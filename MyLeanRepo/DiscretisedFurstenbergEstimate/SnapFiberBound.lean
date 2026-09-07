module

/-
  Fiber bound for snapToTubeGeneral.

  Proves that for a δ-separated set of AffineLines, all δ-close to a point p
  with ‖p‖ ≤ 2 and |slope| ≤ 1, the fiber of snapToTubeGeneral n · p over
  any DyadicTube has cardinality at most a constant M.

  Key steps:
  1. Same fiber ⟹ same slope bin ⟹ |m1-m2| ≤ δ
  2. Near p ⟹ |c1-c2| ≤ 6δ
  3. dist ≤ 32(|m1-m2| + |c1-c2|)
  4. Grid (m,c) with cell δ/65 ⟹ at most 66×391 ≤ 65000 per fiber

  Whiteprint node: improved_incidence_general / snap_fiber_bound
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.TubesAndSlopes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineParams
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ConstructNiceConfiguration
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularSlopeDistance
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CommonTubeEnergyExtraction
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable


namespace DirecretisedFurstenbergEstimate

open DiscretisedFurstenbergEstimate
open LemmaE
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

/-- Coordinate absolute value ≤ norm. -/
lemma coord_abs_le_norm' (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  have h1 : (x i)^2 ≤ ‖x‖^2 := by
    have h2 : ‖x‖^2 = ∑ j : Fin 2, (x j)^2 := by
      rw [EuclideanSpace.real_norm_sq_eq] <;> rfl
    rw [h2]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have h4 : 0 ≤ |x i| := by positivity
  have h5 : 0 ≤ ‖x‖ := by positivity
  nlinarith [sq_abs (x i), sq_abs ‖x‖]

/-- Same grid cell implies absolute difference < cell_size. -/
lemma same_cell_abs_lt_gen {x y : ℝ} {cell_size : ℝ} (h_pos : 0 < cell_size)
    (h : Int.floor (x / cell_size) = Int.floor (y / cell_size)) :
    |x - y| < cell_size := by
  let k := Int.floor (x / cell_size)
  have hky : k = Int.floor (y / cell_size) := h
  set a := x / cell_size with ha_def
  set b := y / cell_size with hb_def
  have h1 : (k : ℝ) ≤ a := Int.floor_le a
  have h2 : a < (k : ℝ) + 1 := Int.lt_floor_add_one a
  have h3 : (k : ℝ) ≤ b := by rw [hky] <;> exact Int.floor_le b
  have h4 : b < (k : ℝ) + 1 := by rw [hky] <;> exact Int.lt_floor_add_one b
  have h5 : |a - b| < 1 := by
    by_cases h6 : a ≤ b
    · have h7 : b - a < 1 := by linarith
      have h8 : |a - b| = b - a := by
        rw [abs_of_nonpos (show a - b ≤ 0 by linarith)] <;> linarith
      rw [h8] <;> linarith
    · have h7 : a - b < 1 := by linarith
      have h8 : |a - b| = a - b := by
        rw [abs_of_nonneg (show 0 ≤ a - b by linarith)]
      rw [h8] <;> linarith
  have h9 : a - b = (x - y) / cell_size := by
    simp only [ha_def, hb_def] <;> ring
  have h10 : |(x - y) / cell_size| < 1 := by rw [←h9] <;> exact h5
  have h11 : |(x - y) / cell_size| = |x - y| / cell_size := by
    rw [abs_div, abs_of_pos h_pos]
  rw [h11] at h10
  have h12 : |x - y| / cell_size < 1 := h10
  calc |x - y|
    = (|x - y| / cell_size) * cell_size := by field_simp [h_pos.ne'] <;> ring
  _ < 1 * cell_size := by gcongr
  _ = cell_size := by ring

/-- For a nonempty finite set of reals with diameter ≤ N*cell_size,
    the floor image has at most N+2 elements. -/
lemma floor_image_card_of_diam {s : Finset ℝ} {cell_size : ℝ} {N : ℕ}
    (h_pos : 0 < cell_size) (hN_pos : 0 < N)
    (h_nonempty : s.Nonempty)
    (h_diam : ∀ x ∈ s, ∀ y ∈ s, |x - y| ≤ (N : ℝ) * cell_size) :
    (s.image (fun x : ℝ => Int.floor (x / cell_size))).card ≤ N + 2 := by
  let x_min := s.min' h_nonempty
  let x_max := s.max' h_nonempty
  have h_min_mem : x_min ∈ s := Finset.min'_mem s h_nonempty
  have h_max_mem : x_max ∈ s := Finset.max'_mem s h_nonempty
  have h_min_le_max : x_min ≤ x_max := Finset.min'_le s x_max h_max_mem
  have h_diam' : x_max - x_min ≤ (N : ℝ) * cell_size := by
    have h : |x_max - x_min| ≤ (N : ℝ) * cell_size := h_diam x_max h_max_mem x_min h_min_mem
    have h' : 0 ≤ x_max - x_min := by linarith
    have h'' : |x_max - x_min| = x_max - x_min := abs_of_nonneg h'
    rw [h''] at h
    exact h
  let k_min := Int.floor (x_min / cell_size)
  let k_max := Int.floor (x_max / cell_size)
  have h1 : ∀ x ∈ s, k_min ≤ Int.floor (x / cell_size) := by
    intro x hx
    have h2 : x_min ≤ x := Finset.min'_le s x hx
    have h3 : x_min / cell_size ≤ x / cell_size := by gcongr
    exact Int.floor_le_floor h3
  have h2 : ∀ x ∈ s, Int.floor (x / cell_size) ≤ k_max := by
    intro x hx
    have h3 : x ≤ x_max := Finset.le_max' s x hx
    have h4 : x / cell_size ≤ x_max / cell_size := by gcongr
    exact Int.floor_le_floor h4
  have h_k_min_le_max : k_min ≤ k_max := by
    have h71 : x_min ≤ x_max := h_min_le_max
    have h72 : x_min / cell_size ≤ x_max / cell_size := by gcongr
    exact Int.floor_le_floor h72
  have h_k_diff : k_max - k_min ≤ (N : ℤ) := by
    have h4 : (k_max : ℝ) ≤ x_max / cell_size := Int.floor_le _
    have h5 : x_min / cell_size < (k_min : ℝ) + 1 := Int.lt_floor_add_one _
    have h6 : x_max / cell_size - x_min / cell_size ≤ (N : ℝ) := by
      have h7 : (x_max - x_min) / cell_size ≤ (N : ℝ) := by
        have h8 : x_max - x_min ≤ (N : ℝ) * cell_size := h_diam'
        have h9 : (x_max - x_min) / cell_size ≤ ((N : ℝ) * cell_size) / cell_size := by gcongr
        have h10 : ((N : ℝ) * cell_size) / cell_size = (N : ℝ) := by
          field_simp [h_pos.ne'] <;> ring
        rw [h10] at h9
        exact h9
      have h10 : (x_max - x_min) / cell_size = x_max / cell_size - x_min / cell_size := by
        field_simp [h_pos.ne'] <;> ring
      rw [h10] at h7
      exact h7
    by_contra h8
    have h9 : k_max - k_min ≥ (N : ℤ) + 1 := by omega
    have h10 : (k_max : ℝ) - (k_min : ℝ) ≥ ((N : ℝ) + 1) := by exact_mod_cast h9
    have h11 : (k_max : ℝ) - (k_min : ℝ) - 1 < x_max / cell_size - x_min / cell_size := by
      linarith [h4, h5]
    linarith
  have h4 : (s.image (fun x : ℝ => Int.floor (x / cell_size))) ⊆ Finset.Icc k_min k_max := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    exact Finset.mem_Icc.mpr ⟨h1 x hx, h2 x hx⟩
  have h5 : (s.image (fun x : ℝ => Int.floor (x / cell_size))).card ≤ (Finset.Icc k_min k_max).card :=
    Finset.card_le_card h4
  have h_nonneg : 0 ≤ k_max - k_min := by linarith
  have h6 : (Finset.Icc k_min k_max).card ≤ (k_max - k_min).toNat + 1 := by
    have h7 : (Finset.Icc k_min k_max).card = (k_max + 1 - k_min).toNat := by simp
    rw [h7]
    have h8 : k_max + 1 - k_min = k_max - k_min + 1 := by omega
    rw [h8]
    have h9 : 0 ≤ k_max - k_min := by omega
    let n : ℕ := (k_max - k_min).toNat
    have hn : (n : ℤ) = k_max - k_min := Int.toNat_of_nonneg h9
    have h10 : (k_max - k_min + 1 : ℤ) = (n : ℤ) + 1 := by rw [←hn] <;> omega
    rw [h10]
    simp <;> norm_cast
  have h7 : (k_max - k_min).toNat ≤ N := by
    have h71 : k_max - k_min ≤ (N : ℤ) := h_k_diff
    have h72 : 0 ≤ k_max - k_min := h_nonneg
    have h73 : ((k_max - k_min).toNat : ℤ) = k_max - k_min := Int.toNat_of_nonneg h72
    have h74 : ((k_max - k_min).toNat : ℤ) ≤ (N : ℤ) := by
      rw [h73] <;> exact h71
    exact_mod_cast h74
  have h8 : (k_max - k_min).toNat + 1 ≤ N + 2 := by omega
  exact le_trans (le_trans h5 h6) h8

/-! ### Regular slope offset formula -/

/-- Offset formula for lines with regular slope y = m*x + c.
    offset = (-m*c/(1+m²), c/(1+m²)). -/
lemma regular_slope_offset_formula (ℓ : AffineLine)
    (hv0 : (getDirV ℓ) 0 ≠ 0) :
    ℓ.offset 0 = -(affineLineSlopeIntercept ℓ).1 * (affineLineSlopeIntercept ℓ).2 / (1 + (affineLineSlopeIntercept ℓ).1^2) ∧
    ℓ.offset 1 = (affineLineSlopeIntercept ℓ).2 / (1 + (affineLineSlopeIntercept ℓ).1^2) := by
  set v := getDirV ℓ with hv_def
  set m := (affineLineSlopeIntercept ℓ).1 with hm_def
  set c := (affineLineSlopeIntercept ℓ).2 with hc_def
  have h_params : affineLineSlopeIntercept ℓ = (v 1 / v 0, ℓ.offset 1 - (v 1 / v 0) * ℓ.offset 0) := by
    unfold affineLineSlopeIntercept
    dsimp only
    rw [dif_neg hv0] <;> rfl
  have h_m : m = v 1 / v 0 := by
    rw [hm_def, h_params] <;> rfl
  have h_c : c = ℓ.offset 1 - m * ℓ.offset 0 := by
    rw [hc_def, h_params, h_m] <;> ring
  have h_v1 : v 1 = m * v 0 := by
    rw [h_m] <;> field_simp [hv0] <;> ring
  have h_pos : 0 < 1 + m^2 := by positivity
  let off_cand : EuclideanSpace ℝ (Fin 2) :=
    EuclideanSpace.single 0 (-m * c / (1 + m^2)) +
    EuclideanSpace.single 1 (c / (1 + m^2))
  have hcand0 : off_cand 0 = -m * c / (1 + m^2) := by
    simp [off_cand, EuclideanSpace.single_apply] <;> ring
  have hcand1 : off_cand 1 = c / (1 + m^2) := by
    simp [off_cand, EuclideanSpace.single_apply] <;> ring
  have hcand_line : off_cand 1 = m * off_cand 0 + c := by
    rw [hcand0, hcand1] <;> field_simp [h_pos.ne'] <;> ring
  have hoff_line : ℓ.offset 1 = m * ℓ.offset 0 + c := by
    linarith [h_c]
  have h_diff_parallel : ∃ (t : ℝ), off_cand - ℓ.offset = t • v := by
    have h_eq0 : (off_cand - ℓ.offset) 1 = m * (off_cand - ℓ.offset) 0 := by
      simp [hcand_line, hoff_line] <;> ring
    let t : ℝ := (off_cand - ℓ.offset) 0 / v 0
    have h_comp0 : (t • v) 0 = (off_cand - ℓ.offset) 0 := by
      have h_smul : (t • v) 0 = t * v 0 := by simp [smul_eq_mul]
      rw [h_smul]
      dsimp only [t]
      field_simp [hv0] <;> ring
    have h_comp1 : (t • v) 1 = (off_cand - ℓ.offset) 1 := by
      have h_smul : (t • v) 1 = t * v 1 := by simp [smul_eq_mul]
      rw [h_smul]
      dsimp only [t]
      rw [h_eq0, h_v1]
      field_simp [hv0] <;> ring
    have ht_eq : off_cand - ℓ.offset = t • v := by
      ext i
      fin_cases i
      · exact h_comp0.symm
      · exact h_comp1.symm
    exact ⟨t, ht_eq⟩
  rcases h_diff_parallel with ⟨t, ht⟩
  have h_dir_eq : ℓ.1.direction = Submodule.span ℝ {v} := by
    have h_span' : Submodule.span ℝ {v} ≤ ℓ.1.direction := by
      apply Submodule.span_le.mpr; intro x hx
      have h_x_eq : x = v := by simpa [Set.mem_singleton_iff] using hx
      rw [h_x_eq]; exact (getDirV_spec ℓ).1
    have h_ne : v ≠ 0 := (getDirV_spec ℓ).2
    have h_finrank1 : Module.finrank ℝ (Submodule.span ℝ {v}) = 1 := finrank_span_singleton h_ne
    have h2 : Module.finrank ℝ (Submodule.span ℝ {v}) = Module.finrank ℝ ℓ.1.direction := by
      rw [h_finrank1, ℓ.2]
    exact (Submodule.eq_of_le_of_finrank_eq h_span' h2).symm
  have h_diff_dir : off_cand - ℓ.offset ∈ ℓ.1.direction := by
    rw [h_dir_eq, ht]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have h_cand_mem : off_cand ∈ ℓ.1 := by
    have h_vsub : (off_cand -ᵥ ℓ.offset) +ᵥ ℓ.offset = off_cand := by
      exact vsub_vadd off_cand ℓ.offset
    rw [←h_vsub]
    exact AffineSubspace.vadd_mem_of_mem_direction h_diff_dir ℓ.offset_mem
  have h_inner_cand : inner ℝ off_cand v = 0 := by
    have h1 : inner ℝ off_cand v = ∑ i : Fin 2, (off_cand i) * (v i) := by
      have h2 : inner ℝ off_cand v = ∑ i : Fin 2, inner ℝ (off_cand i) (v i) := by
        rw [PiLp.inner_apply]
      rw [h2]
      apply Finset.sum_congr rfl
      intro i _
      have h3 : inner ℝ (off_cand i) (v i) = (off_cand i) * (v i) := by
        simp <;> ring
      exact h3
    rw [h1, Fin.sum_univ_two, hcand0, hcand1, h_v1]
    <;> field_simp [h_pos.ne', hv0] <;> ring
  have h_inner_cand' : inner ℝ v off_cand = 0 := by
    have h_comm : inner ℝ v off_cand = inner ℝ off_cand v := by
      simp [PiLp.inner_apply, Fin.sum_univ_two] <;> ring
    rw [h_comm, h_inner_cand]
  have h_cand_orth : off_cand ∈ ℓ.1.directionᗮ := by
    rw [h_dir_eq]
    intro w hw
    rcases Submodule.mem_span_singleton.mp hw with ⟨s, rfl⟩
    have h : inner ℝ (s • v) off_cand = 0 := by
      rw [inner_smul_left, h_inner_cand'] <;> ring
    exact h
  have h_neg_cand_orth : (0 : EuclideanSpace ℝ (Fin 2)) -ᵥ off_cand ∈ ℓ.1.directionᗮ := by
    have h : (0 : EuclideanSpace ℝ (Fin 2)) -ᵥ off_cand = -off_cand := by simp
    rw [h]
    exact Submodule.neg_mem ℓ.1.directionᗮ h_cand_orth
  have h_main : EuclideanGeometry.orthogonalProjection ℓ.1 (0 : EuclideanSpace ℝ (Fin 2)) = off_cand := by
    rw [EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem]
    exact ⟨h_cand_mem, h_neg_cand_orth⟩
  have h_offset_eq : ℓ.offset = off_cand := by
    have h : ℓ.offset = EuclideanGeometry.orthogonalProjection ℓ.1 0 := by rfl
    rw [h, h_main]
  have h7 : ℓ.offset 1 = c / (1 + m^2) := by
    rw [h_offset_eq, hcand1]
  have h8 : ℓ.offset 0 = -m * c / (1 + m^2) := by
    rw [h_offset_eq, hcand0]
  exact ⟨h8, h7⟩

/-- Triangle inequality for real absolute values. -/
lemma real_abs_add (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  have h : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  simpa [Real.norm_eq_abs] using h

/-- Triangle inequality helper: |a - b| ≤ |a| + |b|. -/
lemma abs_sub_triangle (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h : |a + (-b)| ≤ |a| + |(-b)| := real_abs_add a (-b)
  calc |a - b| = |a + (-b)| := by ring_nf
       _ ≤ |a| + |(-b)| := h
       _ = |a| + |b| := by simp

/-- If p is δ-close to line y = m*x + c with |m| ≤ 1,
    then |c - (p 1 - m * p 0)| ≤ 2δ. -/
lemma regular_slope_near_point_intercept_bound {ℓ : AffineLine} {p : EuclideanSpace ℝ (Fin 2)} {δ : ℝ}
    (hδ_pos : 0 < δ)
    (hv0 : (getDirV ℓ) 0 ≠ 0)
    (h_slope : |(affineLineSlopeIntercept ℓ).1| ≤ 1)
    (h_near : p ∈ Metric.cthickening δ (ℓ.1 : Set (EuclideanSpace ℝ (Fin 2)))) :
    |(affineLineSlopeIntercept ℓ).2 - (p 1 - (affineLineSlopeIntercept ℓ).1 * p 0)| ≤ 2 * δ := by
  set m := (affineLineSlopeIntercept ℓ).1 with hm
  set c := (affineLineSlopeIntercept ℓ).2 with hc
  have h_closed : IsClosed (ℓ.1 : Set (EuclideanSpace ℝ (Fin 2))) :=
    AffineSubspace.closed_of_finiteDimensional (ℓ.1)
  have h_nonempty : (ℓ.1 : Set (EuclideanSpace ℝ (Fin 2))).Nonempty := ℓ.nonempty
  have h_ne_top : Metric.infEDist p (ℓ.1 : Set (EuclideanSpace ℝ (Fin 2))) ≠ ⊤ :=
    Metric.infEDist_ne_top h_nonempty
  have h_infDist : Metric.infDist p (ℓ.1 : Set (EuclideanSpace ℝ (Fin 2))) ≤ δ := by
    have h : Metric.infEDist p (ℓ.1 : Set (EuclideanSpace ℝ (Fin 2))) ≤ ENNReal.ofReal δ := h_near
    have h' : (Metric.infEDist p (ℓ.1 : Set (EuclideanSpace ℝ (Fin 2)))).toReal ≤ δ := by
      rw [ENNReal.le_ofReal_iff_toReal_le h_ne_top (by linarith)] at h
      exact h
    simpa [Metric.infDist] using h'
  rcases h_closed.exists_infDist_eq_dist h_nonempty p with ⟨q, hq, h_eq⟩
  have hdist : dist p q ≤ δ := by rw [←h_eq]; exact h_infDist
  have hq_line : q 1 = m * q 0 + c := by
    have h1 : ∃ (t : ℝ), q = ℓ.offset + t • (getDirV ℓ) := by
      have h_dir : q - ℓ.offset ∈ ℓ.1.direction := by
        exact AffineSubspace.vsub_mem_direction hq ℓ.offset_mem
      have h_span : ℓ.1.direction = Submodule.span ℝ {getDirV ℓ} := by
        have h_span' : Submodule.span ℝ {getDirV ℓ} ≤ ℓ.1.direction := by
          apply Submodule.span_le.mpr; intro x hx
          have h_x_eq : x = getDirV ℓ := by simpa [Set.mem_singleton_iff] using hx
          rw [h_x_eq]; exact (getDirV_spec ℓ).1
        have h_ne : (getDirV ℓ) ≠ 0 := (getDirV_spec ℓ).2
        have h_finrank1 : Module.finrank ℝ (Submodule.span ℝ {getDirV ℓ}) = 1 :=
          finrank_span_singleton h_ne
        have h2 : Module.finrank ℝ (Submodule.span ℝ {getDirV ℓ}) =
            Module.finrank ℝ ℓ.1.direction := by rw [h_finrank1, ℓ.2]
        exact (Submodule.eq_of_le_of_finrank_eq h_span' h2).symm
      rw [h_span] at h_dir
      rcases Submodule.mem_span_singleton.mp h_dir with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      have h3 : q - ℓ.offset = t • (getDirV ℓ) := ht.symm
      have h4 : q = ℓ.offset + t • (getDirV ℓ) := by
        have h5 : q - ℓ.offset = t • (getDirV ℓ) := h3
        have h6 : q = ℓ.offset + (q - ℓ.offset) := by simp
        rw [h6, h5]
      exact h4
    rcases h1 with ⟨t, htq⟩
    set v := getDirV ℓ with hv_def
    have h_v1 : v 1 = m * v 0 := by
      have h_m2 : m = v 1 / v 0 := by
        have h : affineLineSlopeIntercept ℓ = (v 1 / v 0, ℓ.offset 1 - (v 1 / v 0) * ℓ.offset 0) := by
          unfold affineLineSlopeIntercept; dsimp only; apply Prod.ext <;> split_ifs <;> tauto
        rw [hm, h] <;> rfl
      rw [h_m2] <;> field_simp [hv0] <;> ring
    have h_c' : c = ℓ.offset 1 - m * ℓ.offset 0 := by
      have h : affineLineSlopeIntercept ℓ = (v 1 / v 0, ℓ.offset 1 - (v 1 / v 0) * ℓ.offset 0) := by
        unfold affineLineSlopeIntercept; dsimp only; apply Prod.ext <;> split_ifs <;> tauto
      have h' : (affineLineSlopeIntercept ℓ).2 = ℓ.offset 1 - (v 1 / v 0) * ℓ.offset 0 := by rw [h] <;> rfl
      have h'' : c = (affineLineSlopeIntercept ℓ).2 := by rfl
      rw [h'', h']
      have h_m' : m = v 1 / v 0 := by
        have h2 : (affineLineSlopeIntercept ℓ).1 = v 1 / v 0 := by rw [h] <;> rfl
        exact h2
      rw [h_m'] <;> ring
    have hq0 : q 0 = ℓ.offset 0 + t * v 0 := by
      rw [htq] <;> simp [EuclideanSpace.single_apply, smul_eq_mul] <;> ring
    have hq1 : q 1 = ℓ.offset 1 + t * v 1 := by
      rw [htq] <;> simp [EuclideanSpace.single_apply, smul_eq_mul] <;> ring
    rw [hq1, hq0, h_v1, h_c'] <;> ring
  have h_p1 : |p 1 - q 1| ≤ dist p q := by
    have h : |p 1 - q 1| ≤ ‖p - q‖ := coord_abs_le_norm' (p - q) 1
    simpa [dist_eq_norm] using h
  have h_p0 : |p 0 - q 0| ≤ dist p q := by
    have h : |p 0 - q 0| ≤ ‖p - q‖ := coord_abs_le_norm' (p - q) 0
    simpa [dist_eq_norm] using h
  have h_main : c - (p 1 - m * p 0) = (q 1 - p 1) - m * (q 0 - p 0) := by
    linarith [hq_line]
  rw [h_main]
  set a := q 1 - p 1 with ha
  set b := m * (q 0 - p 0) with hb
  have h_abs : |a - b| ≤ |a| + |b| := abs_sub_triangle a b
  have h_mul : |b| = |m| * |q 0 - p 0| := by
    simp [hb, abs_mul] <;> ring
  have h_result1 : |a - b| ≤ |a| + |m| * |q 0 - p 0| := by
    rw [h_mul] at h_abs
    exact h_abs
  have h_result2 : |a| + |m| * |q 0 - p 0| ≤ (1 + |m|) * dist p q := by
    have h_xa : |a| ≤ dist p q := by
      have h_eq : a = q 1 - p 1 := by simp [ha]
      rw [h_eq]
      have h_abs : |q 1 - p 1| = |p 1 - q 1| := by
        have h : q 1 - p 1 = -(p 1 - q 1) := by ring
        rw [h, abs_neg]
      rw [h_abs]
      exact h_p1
    have h_xb : |q 0 - p 0| ≤ dist p q := by
      have h_abs : |q 0 - p 0| = |p 0 - q 0| := by
        have h : q 0 - p 0 = -(p 0 - q 0) := by ring
        rw [h, abs_neg]
      rw [h_abs]
      exact h_p0
    have h : |a| + |m| * |q 0 - p 0| ≤ dist p q + |m| * dist p q := by
      gcongr <;> linarith
    have h2 : dist p q + |m| * dist p q = (1 + |m|) * dist p q := by ring
    rw [h2] at h
    exact h
  have h_result3 : (1 + |m|) * dist p q ≤ 2 * δ := by
    have h9 : |m| ≤ 1 := h_slope
    gcongr <;> linarith
  exact le_trans h_result1 (le_trans h_result2 h_result3)

/-- If p is δ-close to line with |m| ≤ 1 and ‖p‖ ≤ 2, then |c| ≤ 6. -/
lemma regular_slope_c_bound {ℓ : AffineLine} {p : EuclideanSpace ℝ (Fin 2)} {δ : ℝ}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hv0 : (getDirV ℓ) 0 ≠ 0)
    (h_slope : |(affineLineSlopeIntercept ℓ).1| ≤ 1)
    (h_near : p ∈ Metric.cthickening δ (ℓ.1 : Set (EuclideanSpace ℝ (Fin 2))))
    (hp_norm : ‖p‖ ≤ 2) :
    |(affineLineSlopeIntercept ℓ).2| ≤ 6 := by
  set m := (affineLineSlopeIntercept ℓ).1 with hm
  set c := (affineLineSlopeIntercept ℓ).2 with hc
  set x := p 1 - m * p 0 with hx
  have h1 : |c - x| ≤ 2 * δ :=
    regular_slope_near_point_intercept_bound hδ_pos hv0 h_slope h_near
  have h_p1 : |p 1| ≤ ‖p‖ := coord_abs_le_norm' p 1
  have h_p0 : |p 0| ≤ ‖p‖ := coord_abs_le_norm' p 0
  have h2 : |x| ≤ |p 1| + |m| * |p 0| := by
    have h21 : |x| ≤ |p 1| + |m * p 0| := abs_sub_triangle (p 1) (m * p 0)
    have h22 : |m * p 0| = |m| * |p 0| := by rw [abs_mul]
    rw [h22] at h21
    exact h21
  have h3 : |x| ≤ 4 := by
    have h31 : |p 1| ≤ ‖p‖ := h_p1
    have h32 : |m| * |p 0| ≤ ‖p‖ := by
      have h33 : |m| ≤ 1 := h_slope
      have h34 : |p 0| ≤ ‖p‖ := h_p0
      calc |m| * |p 0| ≤ 1 * |p 0| := by gcongr
           _ ≤ ‖p‖ := by linarith
    have h35 : |x| ≤ |p 1| + |m| * |p 0| := h2
    have h36 : |x| ≤ ‖p‖ + ‖p‖ := by linarith
    have h37 : ‖p‖ ≤ 2 := hp_norm
    linarith
  have h4 : |c| ≤ |c - x| + |x| := by
    have h_tri : |(c - x) + x| ≤ |c - x| + |x| :=
      real_abs_add (c - x) x
    have h_eq : (c - x) + x = c := by ring
    rw [h_eq] at h_tri
    exact h_tri
  have h5 : |c| ≤ 2 * δ + 4 := by linarith
  have h6 : 2 * δ + 4 ≤ 6 := by
    have h7 : 2 * δ ≤ 2 := by linarith
    linarith
  linarith

/-- For two lines both δ-close to p with |m| ≤ 1 and ‖p‖ ≤ 2:
    |c1 - c2| ≤ 4δ + |m1-m2| * ‖p‖. -/
lemma regular_slope_intercept_diff_bound {ℓ₁ ℓ₂ : AffineLine} {p : EuclideanSpace ℝ (Fin 2)} {δ : ℝ}
    (hδ_pos : 0 < δ)
    (hv0_1 : (getDirV ℓ₁) 0 ≠ 0) (hv0_2 : (getDirV ℓ₂) 0 ≠ 0)
    (h_slope1 : |(affineLineSlopeIntercept ℓ₁).1| ≤ 1)
    (h_slope2 : |(affineLineSlopeIntercept ℓ₂).1| ≤ 1)
    (h_near1 : p ∈ Metric.cthickening δ (ℓ₁.1 : Set (EuclideanSpace ℝ (Fin 2))))
    (h_near2 : p ∈ Metric.cthickening δ (ℓ₂.1 : Set (EuclideanSpace ℝ (Fin 2))))
    (hp_norm : ‖p‖ ≤ 2) :
    |(affineLineSlopeIntercept ℓ₁).2 - (affineLineSlopeIntercept ℓ₂).2| ≤
    4 * δ + |(affineLineSlopeIntercept ℓ₁).1 - (affineLineSlopeIntercept ℓ₂).1| * ‖p‖ := by
  set m1 := (affineLineSlopeIntercept ℓ₁).1 with hm1
  set c1 := (affineLineSlopeIntercept ℓ₁).2 with hc1
  set m2 := (affineLineSlopeIntercept ℓ₂).1 with hm2
  set c2 := (affineLineSlopeIntercept ℓ₂).2 with hc2
  have h1 : |c1 - (p 1 - m1 * p 0)| ≤ 2 * δ :=
    regular_slope_near_point_intercept_bound hδ_pos hv0_1 h_slope1 h_near1
  have h2 : |c2 - (p 1 - m2 * p 0)| ≤ 2 * δ :=
    regular_slope_near_point_intercept_bound hδ_pos hv0_2 h_slope2 h_near2
  have h3 : |p 0| ≤ ‖p‖ := coord_abs_le_norm' p 0
  set d1 := c1 - (p 1 - m1 * p 0) with hd1
  set d2 := c2 - (p 1 - m2 * p 0) with hd2
  have h4 : c1 - c2 = d1 - d2 - (m1 - m2) * p 0 := by
    simp [hd1, hd2] <;> ring
  rw [h4]
  have h_tri : ∀ (a b c : ℝ), |a - b - c| ≤ |a| + |b| + |c| := by
    intro a b c
    have h5 : |a - b - c| ≤ |a - b| + |c| := abs_sub_triangle (a - b) c
    have h6 : |a - b| ≤ |a| + |b| := abs_sub_triangle a b
    linarith
  have h5 : |d1 - d2 - (m1 - m2) * p 0| ≤ |d1| + |d2| + |(m1 - m2) * p 0| :=
    h_tri d1 d2 ((m1 - m2) * p 0)
  have h6 : |(m1 - m2) * p 0| = |m1 - m2| * |p 0| := by rw [abs_mul]
  rw [h6] at h5
  exact le_trans h5 (by gcongr <;> linarith)

/-- dist(ℓ1, ℓ2) ≤ 32 * (|m1-m2| + |c1-c2|) for |m| ≤ 1, |c| ≤ 6. -/
lemma regular_slope_dist_lipschitz (ℓ₁ ℓ₂ : AffineLine)
    (hv0_1 : (getDirV ℓ₁) 0 ≠ 0) (hv0_2 : (getDirV ℓ₂) 0 ≠ 0)
    (h_slope1 : |(affineLineSlopeIntercept ℓ₁).1| ≤ 1)
    (h_slope2 : |(affineLineSlopeIntercept ℓ₂).1| ≤ 1)
    (h_c1_bound : |(affineLineSlopeIntercept ℓ₁).2| ≤ 6)
    (h_c2_bound : |(affineLineSlopeIntercept ℓ₂).2| ≤ 6) :
    AffineLine.dist ℓ₁ ℓ₂ ≤
    32 * (|(affineLineSlopeIntercept ℓ₁).1 - (affineLineSlopeIntercept ℓ₂).1| +
          |(affineLineSlopeIntercept ℓ₁).2 - (affineLineSlopeIntercept ℓ₂).2|) := by
  set m1 := (affineLineSlopeIntercept ℓ₁).1 with hm1
  set c1 := (affineLineSlopeIntercept ℓ₁).2 with hc1
  set m2 := (affineLineSlopeIntercept ℓ₂).1 with hm2
  set c2 := (affineLineSlopeIntercept ℓ₂).2 with hc2
  set off1 := ℓ₁.offset with hoff1
  set off2 := ℓ₂.offset with hoff2
  have h_off1 := regular_slope_offset_formula ℓ₁ hv0_1
  have h_off2 := regular_slope_offset_formula ℓ₂ hv0_2
  have h_dir : ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ ≤
      2 * |m1 - m2| :=
    regular_direction_proj_upper_bound ℓ₁ ℓ₂ hv0_1 hv0_2
  have h_pos1 : 0 < 1 + m1^2 := by positivity
  have h_pos2 : 0 < 1 + m2^2 := by positivity
  have h_abs_m1 : |m1| ≤ 1 := h_slope1
  have h_abs_m2 : |m2| ≤ 1 := h_slope2
  have h_abs_c1 : |c1| ≤ 6 := h_c1_bound
  have h_abs_c2 : |c2| ≤ 6 := h_c2_bound
  have h_denom_ge1 : ∀ (m : ℝ), 1 ≤ 1 + m^2 := by intro m; nlinarith
  have h_frac1 : |c1 / (1 + m1^2) - c2 / (1 + m2^2)| ≤ |c1 - c2| + 12 * |m1 - m2| := by
    have h_eq : c1 / (1 + m1^2) - c2 / (1 + m2^2) =
        (c1 - c2) / (1 + m1^2) + c2 * (m2^2 - m1^2) / ((1 + m1^2) * (1 + m2^2)) := by
      field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
    rw [h_eq]
    have h7 : |(c1 - c2) / (1 + m1^2)| ≤ |c1 - c2| := by
      rw [abs_div, abs_of_pos h_pos1]
      have h8 : |c1 - c2| / (1 + m1^2) ≤ |c1 - c2| := by
        apply div_le_self (by positivity)
        have h9 : 0 ≤ m1^2 := by positivity
        linarith
      exact h8
    have h9 : |m1^2 - m2^2| ≤ 2 * |m1 - m2| := by
      have h10 : m1^2 - m2^2 = (m1 - m2) * (m1 + m2) := by ring
      rw [h10, abs_mul]
      have h11 : |m1 + m2| ≤ 2 := by
        calc |m1 + m2| ≤ |m1| + |m2| := real_abs_add m1 m2
             _ ≤ 1 + 1 := by linarith
             _ = 2 := by norm_num
      have h12 : 0 ≤ |m1 - m2| := by positivity
      have h13 : |m1 - m2| * |m1 + m2| ≤ 2 * |m1 - m2| := by
        have h14 : |m1 - m2| * |m1 + m2| ≤ |m1 - m2| * 2 := mul_le_mul_of_nonneg_left h11 h12
        have h15 : |m1 - m2| * 2 = 2 * |m1 - m2| := by ring
        rw [h15] at h14
        exact h14
      exact h13
    have h10 : |c2 * (m2^2 - m1^2) / ((1 + m1^2) * (1 + m2^2))| ≤ |c2| * |m1^2 - m2^2| := by
      have h11 : |c2 * (m2^2 - m1^2) / ((1 + m1^2) * (1 + m2^2))| =
          |c2| * |m2^2 - m1^2| / ((1 + m1^2) * (1 + m2^2)) := by
        rw [abs_div, abs_mul]
        have h12 : |(1 + m1^2) * (1 + m2^2)| = (1 + m1^2) * (1 + m2^2) := by
          rw [abs_of_pos (mul_pos h_pos1 h_pos2)]
        rw [h12] <;> ring
      rw [h11]
      have h13 : |m2^2 - m1^2| = |m1^2 - m2^2| := by
        have h14 : m2^2 - m1^2 = -(m1^2 - m2^2) := by ring
        rw [h14, abs_neg]
      rw [h13]
      have h14 : |c2| * |m1^2 - m2^2| / ((1 + m1^2) * (1 + m2^2)) ≤ |c2| * |m1^2 - m2^2| := by
        have h15 : 1 ≤ (1 + m1^2) * (1 + m2^2) := by
          have h16 : 0 ≤ m1^2 := by positivity
          have h17 : 0 ≤ m2^2 := by positivity
          have h18 : 1 ≤ 1 + m1^2 := by linarith
          have h19 : 1 ≤ 1 + m2^2 := by linarith
          have h20 : 1 ≤ (1 + m1^2) * (1 + m2^2) := by
            calc 1 = 1 * 1 := by ring
                 _ ≤ (1 + m1^2) * (1 + m2^2) := by gcongr
          exact h20
        apply div_le_self (by positivity)
        exact h15
      exact h14
    let u := (c1 - c2) / (1 + m1^2)
    let v := c2 * (m2^2 - m1^2) / ((1 + m1^2) * (1 + m2^2))
    calc |u + v|
      ≤ |u| + |v| := real_abs_add u v
    _ ≤ |c1 - c2| + |c2| * |m1^2 - m2^2| := by gcongr
    _ ≤ |c1 - c2| + 6 * (2 * |m1 - m2|) := by gcongr <;> linarith
    _ = |c1 - c2| + 12 * |m1 - m2| := by ring
  have h_off1_diff : |off1 1 - off2 1| ≤ |c1 - c2| + 12 * |m1 - m2| := by
    rw [h_off1.2, h_off2.2]
    exact h_frac1
  have h_frac2 : |m1 / (1 + m1^2) - m2 / (1 + m2^2)| ≤ 2 * |m1 - m2| := by
    have h_eq : m1 / (1 + m1^2) - m2 / (1 + m2^2) =
        (m1 - m2) * (1 - m1 * m2) / ((1 + m1^2) * (1 + m2^2)) := by
      field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
    rw [h_eq]
    have h_abs : |(m1 - m2) * (1 - m1 * m2) / ((1 + m1^2) * (1 + m2^2))| =
        |m1 - m2| * |1 - m1 * m2| / ((1 + m1^2) * (1 + m2^2)) := by
      rw [abs_div, abs_mul]
      have h12 : |(1 + m1^2) * (1 + m2^2)| = (1 + m1^2) * (1 + m2^2) := by
        rw [abs_of_pos (mul_pos h_pos1 h_pos2)]
      rw [h12] <;> ring
    rw [h_abs]
    have h13 : |1 - m1 * m2| ≤ 2 := by
      have h14 : |m1 * m2| ≤ 1 := by
        rw [abs_mul]
        have h15 : |m1| * |m2| ≤ 1 := by
          calc |m1| * |m2| ≤ 1 * 1 := by gcongr <;> linarith
               _ = 1 := by norm_num
        exact h15
      have h16 : |1 - m1 * m2| ≤ 1 + |m1 * m2| := by
        have h17 : |1 - m1 * m2| = |1 + (-(m1 * m2))| := by ring_nf
        rw [h17]
        have h18 : |1 + (-(m1 * m2))| ≤ |1| + |-(m1 * m2)| := by
          exact real_abs_add 1 (-(m1 * m2))
        simpa using h18
      linarith
    have h17 : |m1 - m2| * |1 - m1 * m2| / ((1 + m1^2) * (1 + m2^2)) ≤ 2 * |m1 - m2| := by
      have h18 : 0 ≤ |m1 - m2| := by positivity
      have h19 : (1 + m1^2) * (1 + m2^2) ≥ 1 := by
        have h20 : 0 ≤ m1^2 := by positivity
        have h21 : 0 ≤ m2^2 := by positivity
        have h22 : 1 ≤ 1 + m1^2 := by linarith
        have h23 : 1 ≤ 1 + m2^2 := by linarith
        have h24 : 1 ≤ (1 + m1^2) * (1 + m2^2) := by
          calc 1 = 1 * 1 := by ring
               _ ≤ (1 + m1^2) * (1 + m2^2) := by gcongr
        exact h24
      have h20 : |m1 - m2| * |1 - m1 * m2| / ((1 + m1^2) * (1 + m2^2)) ≤ |m1 - m2| * |1 - m1 * m2| := by
        apply div_le_self (by positivity)
        exact h19
      have h21 : |m1 - m2| * |1 - m1 * m2| ≤ 2 * |m1 - m2| := by
        have h22 : |1 - m1 * m2| ≤ 2 := h13
        have h23 : 0 ≤ |m1 - m2| := by positivity
        have h24 : |1 - m1 * m2| * |m1 - m2| ≤ 2 * |m1 - m2| :=
          mul_le_mul_of_nonneg_right h22 h23
        have h25 : |m1 - m2| * |1 - m1 * m2| = |1 - m1 * m2| * |m1 - m2| := by ring
        rw [h25]
        exact h24
      linarith
    exact h17
  have h_off0_diff : |off1 0 - off2 0| ≤ |c1 - c2| + 18 * |m1 - m2| := by
    rw [h_off1.1, h_off2.1]
    have h_eq : (-m1 * c1 / (1 + m1^2)) - (-m2 * c2 / (1 + m2^2)) =
        m2 * (c2 / (1 + m2^2) - c1 / (1 + m1^2)) + (m2 - m1) * (c1 / (1 + m1^2)) := by
      field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
    rw [h_eq]
    have h7 : |m2 * (c2 / (1 + m2^2) - c1 / (1 + m1^2))| ≤ |m2| * |c1 / (1 + m1^2) - c2 / (1 + m2^2)| := by
      rw [abs_mul]
      have h8 : |c2 / (1 + m2^2) - c1 / (1 + m1^2)| = |c1 / (1 + m1^2) - c2 / (1 + m2^2)| := by
        have h9 : c2 / (1 + m2^2) - c1 / (1 + m1^2) = -(c1 / (1 + m1^2) - c2 / (1 + m2^2)) := by ring
        rw [h9, abs_neg]
      rw [h8] <;> ring
    have h9 : |(m2 - m1) * (c1 / (1 + m1^2))| ≤ |m1 - m2| * |c1| := by
      rw [abs_mul]
      have h10 : |m2 - m1| = |m1 - m2| := by
        have h11 : m2 - m1 = -(m1 - m2) := by ring
        rw [h11, abs_neg]
      have h11 : |c1 / (1 + m1^2)| ≤ |c1| := by
        rw [abs_div, abs_of_pos h_pos1]
        apply div_le_self (by positivity)
        have h12 : 0 ≤ m1^2 := by positivity
        linarith
      rw [h10]
      have h13 : 0 ≤ |m1 - m2| := by positivity
      exact mul_le_mul_of_nonneg_left h11 h13
    let x := m2 * (c2 / (1 + m2^2) - c1 / (1 + m1^2))
    let y := (m2 - m1) * (c1 / (1 + m1^2))
    calc |x + y|
      ≤ |x| + |y| := real_abs_add x y
    _ ≤ |m2| * |c1 / (1 + m1^2) - c2 / (1 + m2^2)| + |m1 - m2| * |c1| := by gcongr
    _ ≤ 1 * (|c1 - c2| + 12 * |m1 - m2|) + |m1 - m2| * 6 := by gcongr <;> linarith
    _ = |c1 - c2| + 18 * |m1 - m2| := by ring
  set a := |(off1 - off2) 0| with ha
  set b := |(off1 - off2) 1| with hb
  have h_offset_norm : ‖off1 - off2‖ ≤ a + b := by
    have h1 : ‖off1 - off2‖ ^ 2 = a^2 + b^2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      <;> simp [ha, hb, sq_abs] <;> ring
    have h2 : 0 ≤ ‖off1 - off2‖ := by positivity
    have h3 : 0 ≤ a := by positivity
    have h4 : 0 ≤ b := by positivity
    have h5 : 0 ≤ a + b := by positivity
    have h6 : a^2 + b^2 ≤ (a + b)^2 := by
      have h7 : 0 ≤ 2 * a * b := by positivity
      have h8 : (a + b)^2 = a^2 + b^2 + 2 * a * b := by ring
      rw [h8]
      <;> linarith
    have h9 : ‖off1 - off2‖ ^ 2 ≤ (a + b)^2 := by
      rw [h1] <;> exact h6
    have h10 : ‖off1 - off2‖ ≤ a + b := by
      by_contra h14
      have h15 : a + b < ‖off1 - off2‖ := by linarith
      have h16 : 0 < a + b := by
        have h161 : 0 ≤ a := by positivity
        have h162 : 0 ≤ b := by positivity
        by_contra h163
        have h164 : a + b ≤ 0 := by linarith
        have h165 : a = 0 := by linarith
        have h166 : b = 0 := by linarith
        have h167 : ‖off1 - off2‖ ^ 2 = 0 := by
          rw [h1, h165, h166] <;> ring
        have h168 : ‖off1 - off2‖ = 0 := by
          have h169 : ‖off1 - off2‖ ^ 2 = 0 := h167
          have h170 : ‖off1 - off2‖ = 0 := by
            simpa [pow_two] using h169
          exact h170
        rw [h165, h166] at h15
        rw [h168] at h15
        <;> linarith
      have h17 : 0 < ‖off1 - off2‖ := by linarith
      have h18 : (a + b)^2 < ‖off1 - off2‖^2 := by
        have h19 : (a + b) * (a + b) < (a + b) * ‖off1 - off2‖ :=
          mul_lt_mul_of_pos_left h15 h16
        have h20 : (a + b) * ‖off1 - off2‖ < ‖off1 - off2‖ * ‖off1 - off2‖ :=
          mul_lt_mul_of_pos_right h15 h17
        calc (a + b)^2
          = (a + b) * (a + b) := by ring
        _ < (a + b) * ‖off1 - off2‖ := h19
        _ < ‖off1 - off2‖ * ‖off1 - off2‖ := h20
        _ = ‖off1 - off2‖^2 := by ring
      have h21 : ‖off1 - off2‖^2 ≤ (a + b)^2 := h9
      linarith
    exact h10
  have h_total : ‖off1 - off2‖ ≤ 2 * |c1 - c2| + 30 * |m1 - m2| := by
    have h_a : a ≤ |c1 - c2| + 18 * |m1 - m2| := by
      simpa [ha] using h_off0_diff
    have h_b : b ≤ |c1 - c2| + 12 * |m1 - m2| := by
      simpa [hb] using h_off1_diff
    calc ‖off1 - off2‖ ≤ a + b := h_offset_norm
         _ ≤ (|c1 - c2| + 18 * |m1 - m2|) + (|c1 - c2| + 12 * |m1 - m2|) := by gcongr
         _ = 2 * |c1 - c2| + 30 * |m1 - m2| := by ring
  have h_dist : AffineLine.dist ℓ₁ ℓ₂ =
      ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ + ‖off1 - off2‖ := by rfl
  rw [h_dist]
  have h_final1 : ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ + ‖off1 - off2‖ ≤
      2 * |m1 - m2| + (2 * |c1 - c2| + 30 * |m1 - m2|) := by
    gcongr
  have h_final2 : 2 * |m1 - m2| + (2 * |c1 - c2| + 30 * |m1 - m2|) =
      2 * |c1 - c2| + 32 * |m1 - m2| := by ring
  have h_final3 : 2 * |c1 - c2| + 32 * |m1 - m2| ≤
      32 * (|m1 - m2| + |c1 - c2|) := by
    have h' : 0 ≤ |c1 - c2| := by positivity
    have h'' : 0 ≤ |m1 - m2| := by positivity
    have h3 : 32 * (|m1 - m2| + |c1 - c2|) = 32 * |m1 - m2| + 32 * |c1 - c2| := by
      rw [mul_add] <;> ring
    rw [h3]
    have h4 : 2 * |c1 - c2| ≤ 32 * |c1 - c2| := by
      have h5 : (2 : ℝ) ≤ 32 := by norm_num
      exact mul_le_mul_of_nonneg_right h5 h'
    linarith
  calc ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ + ‖off1 - off2‖
    ≤ 2 * |m1 - m2| + (2 * |c1 - c2| + 30 * |m1 - m2|) := h_final1
  _ = 2 * |c1 - c2| + 32 * |m1 - m2| := h_final2
  _ ≤ 32 * (|m1 - m2| + |c1 - c2|) := h_final3

end DirecretisedFurstenbergEstimate

end
