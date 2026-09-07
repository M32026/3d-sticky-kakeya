module

/-
  Covering movement lemma for snapped tube families.

  Given a family of dyadic tubes T₀ where each tube is within C_move*δ of some
  line in an "oriented" family T_oriented, bound |T₀| by K_pack * Ncover(δ, T_oriented).

  Key trick: use swapLine so that affineLineParams(swapLine(toAffineLine T))
  equals (T.slope, T.intercept), matching our |slope|≤1, |intercept|≤3 hypotheses.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineLipschitzTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate

open DiscretisedFurstenbergEstimate
open DyadicCardToNcover (toAffineLine)
open CoordinatePartition (swapLine swapLine_isometry swapLine_params_eq
  point_on_lineOfSlopeIntercept direction_eq_span swapCoords swapLine_set_eq)

/-- Grid counting: integer pairs with pairwise L∞ distance ≤ D have
    cardinality at most (2 * Nat.ceil D + 1)^2. -/
lemma grid_packing_bound {S : Finset (ℤ × ℤ)} {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ (x : ℤ × ℤ), x ∈ S → ∀ (y : ℤ × ℤ), y ∈ S →
      |(x.1 : ℝ) - y.1| ≤ D ∧ |(x.2 : ℝ) - y.2| ≤ D) :
    S.card ≤ (2 * Nat.ceil D + 1)^2 := by
  by_cases hS : S.Nonempty
  · rcases hS with ⟨x0, hx0⟩
    have h1 : ∀ x ∈ S, |(x.1 : ℝ) - x0.1| ≤ D := fun x hx => h x hx x0 hx0 |>.1
    have h2 : ∀ x ∈ S, |(x.2 : ℝ) - x0.2| ≤ D := fun x hx => h x hx x0 hx0 |>.2
    let M : ℕ := Nat.ceil D
    have h_le_D : D ≤ (M : ℝ) := Nat.le_ceil D
    have hM1 : ∀ x ∈ S, x0.1 - (M : ℤ) ≤ x.1 := by
      intro x hx
      have h3 : |(x.1 : ℝ) - x0.1| ≤ D := h1 x hx
      have h4 : (x0.1 : ℝ) - (M : ℝ) ≤ (x.1 : ℝ) := by
        have h5 : -(D : ℝ) ≤ (x.1 : ℝ) - x0.1 := by linarith [abs_le.mp h3]
        linarith [h_le_D]
      exact_mod_cast h4
    have hM2 : ∀ x ∈ S, x.1 ≤ x0.1 + (M : ℤ) := by
      intro x hx
      have h3 : |(x.1 : ℝ) - x0.1| ≤ D := h1 x hx
      have h4 : (x.1 : ℝ) ≤ (x0.1 : ℝ) + (M : ℝ) := by
        have h5 : (x.1 : ℝ) - x0.1 ≤ D := by linarith [abs_le.mp h3]
        linarith [h_le_D]
      exact_mod_cast h4
    have hM3 : ∀ x ∈ S, x0.2 - (M : ℤ) ≤ x.2 := by
      intro x hx
      have h3 : |(x.2 : ℝ) - x0.2| ≤ D := h2 x hx
      have h4 : (x0.2 : ℝ) - (M : ℝ) ≤ (x.2 : ℝ) := by
        have h5 : -(D : ℝ) ≤ (x.2 : ℝ) - x0.2 := by linarith [abs_le.mp h3]
        linarith [h_le_D]
      exact_mod_cast h4
    have hM4 : ∀ x ∈ S, x.2 ≤ x0.2 + (M : ℤ) := by
      intro x hx
      have h3 : |(x.2 : ℝ) - x0.2| ≤ D := h2 x hx
      have h4 : (x.2 : ℝ) ≤ (x0.2 : ℝ) + (M : ℝ) := by
        have h5 : (x.2 : ℝ) - x0.2 ≤ D := by linarith [abs_le.mp h3]
        linarith [h_le_D]
      exact_mod_cast h4
    let I₁ : Finset ℤ := Finset.Icc (x0.1 - (M : ℤ)) (x0.1 + (M : ℤ))
    let I₂ : Finset ℤ := Finset.Icc (x0.2 - (M : ℤ)) (x0.2 + (M : ℤ))
    have h_sub : S ⊆ I₁ ×ˢ I₂ := by
      intro x hx
      have h6 : x.1 ∈ I₁ := by
        simp only [I₁, Finset.mem_Icc]
        exact ⟨hM1 x hx, hM2 x hx⟩
      have h7 : x.2 ∈ I₂ := by
        simp only [I₂, Finset.mem_Icc]
        exact ⟨hM3 x hx, hM4 x hx⟩
      exact Finset.mem_product.mpr ⟨h6, h7⟩
    have h_card : S.card ≤ (I₁ ×ˢ I₂).card := Finset.card_le_card h_sub
    have hI1 : I₁.card = 2 * M + 1 := by
      simp [I₁, Finset.Icc_eq_empty_of_lt] <;> omega
    have hI2 : I₂.card = 2 * M + 1 := by
      simp [I₂, Finset.Icc_eq_empty_of_lt] <;> omega
    have h_prod : (I₁ ×ˢ I₂).card = I₁.card * I₂.card := Finset.card_product _ _
    rw [h_prod, hI1, hI2] at h_card
    have h_sq : (2 * M + 1) * (2 * M + 1) = (2 * M + 1)^2 := by ring
    rw [h_sq] at h_card
    exact h_card
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS] <;> positivity

/-- For swapLine(lineOfSlopeIntercept m b), getDirV has nonzero y-component. -/
lemma swapLine_getDirV_y_ne_zero (m b : ℝ) :
    (LemmaE.getDirV (swapLine (DyadicCardToNcover.lineOfSlopeIntercept m b))) 1 ≠ 0 := by
  let ℓ := DyadicCardToNcover.lineOfSlopeIntercept m b
  let ℓ' := swapLine ℓ
  let p0' := TubesAndSlopes.mkPlane b 0
  let p1' := TubesAndSlopes.mkPlane (m + b) 1
  have h_points_orig := point_on_lineOfSlopeIntercept m b
  have h_set : (ℓ'.1 : Set EuclideanPlane) = swapCoords '' ℓ.1 := swapLine_set_eq ℓ
  have h0' : p0' ∈ ℓ'.1 := by
    have h_goal : p0' ∈ swapCoords '' ℓ.1 := by
      refine ⟨TubesAndSlopes.mkPlane 0 b, h_points_orig.1, ?_⟩
      ext i; fin_cases i <;> simp [p0', swapCoords, TubesAndSlopes.mkPlane] <;> rfl
    have h_in : p0' ∈ (ℓ'.1 : Set EuclideanPlane) := by
      rw [h_set]
      exact h_goal
    exact h_in
  have h1' : p1' ∈ ℓ'.1 := by
    have h_goal : p1' ∈ swapCoords '' ℓ.1 := by
      refine ⟨TubesAndSlopes.mkPlane 1 (m + b), h_points_orig.2, ?_⟩
      ext i; fin_cases i <;> simp [p1', swapCoords, TubesAndSlopes.mkPlane] <;> rfl
    have h_in : p1' ∈ (ℓ'.1 : Set EuclideanPlane) := by
      rw [h_set]
      exact h_goal
    exact h_in
  let v' := LemmaE.getDirV ℓ'
  have hv'_dir : v' ∈ ℓ'.1.direction := (LemmaE.getDirV_spec ℓ').1
  have hv'_ne : v' ≠ 0 := (LemmaE.getDirV_spec ℓ').2
  have h_span_v' : ℓ'.1.direction = ℝ ∙ v' := direction_eq_span ℓ'.2 hv'_dir hv'_ne
  have h_diff_dir : p1' - p0' ∈ ℓ'.1.direction :=
    AffineSubspace.vsub_mem_direction h1' h0'
  rw [h_span_v'] at h_diff_dir
  rcases (Submodule.mem_span_singleton.mp h_diff_dir) with ⟨c, hc⟩
  have h_eq : (p1' - p0') 1 = c * (v' 1) := by
    have h : p1' - p0' = c • v' := hc.symm
    rw [h] <;> simp
  have h_val : (p1' - p0') 1 = 1 := by
    simp [p0', p1', TubesAndSlopes.mkPlane] <;> ring
  rw [h_val] at h_eq
  intro h_contra
  rw [h_contra] at h_eq
  norm_num at h_eq

/-- Global covering movement bound for snapped dyadic tube families. -/
lemma covering_movement_global
    {n : ℕ} {δ : ℝ} {C_move : ℝ}
    (hδ_pos : 0 < δ)
    (hC_move_nonneg : 0 ≤ C_move)
    (h_scale : δ < 2 * dyadicDelta n)
    (T_oriented : Set AffineLine)
    (T₀ : Finset (DyadicTube n))
    (hm : ∀ T ∈ T₀, |T.slope| ≤ 1)
    (hb : ∀ T ∈ T₀, |T.intercept| ≤ 3)
    (h_prov : ∀ U ∈ T₀, ∃ ℓ ∈ T_oriented,
        dist (toAffineLine U) ℓ ≤ C_move * δ) :
    (T₀.card : ENNReal) ≤
      (2 * Nat.ceil (32 * (C_move + 1)) + 1)^2 *
        Metric.externalCoveringNumber δ.toNNReal T_oriented := by
  classical
  set δ_n := dyadicDelta n with hδ_n_def
  have hδ_n_pos : 0 < δ_n := dyadicDelta_pos n
  set R : ℝ := (C_move + 1) * δ with hR_def
  set D_grid : ℝ := 32 * (C_move + 1) with hD_grid_def
  set K1 : ℕ := Nat.ceil D_grid with hK1_def
  set K_pack : ℕ := (2 * K1 + 1)^2 with hK_pack_def

  -- Shorthand for swapped affine lines
  let swapped (U : DyadicTube n) := swapLine (toAffineLine U)

  by_cases h_top : Metric.externalCoveringNumber δ.toNNReal T_oriented = ⊤
  · rw [h_top] <;> simp

  · have h_lt_top : Metric.externalCoveringNumber δ.toNNReal T_oriented < ⊤ := by exact Ne.lt_top' fun a => h_top (id (Eq.symm a))
    let ι := {C : Set AffineLine // Metric.IsCover δ.toNNReal T_oriented C}
    have hι_nonempty : Nonempty ι := by
      refine ⟨⟨T_oriented, ?_⟩⟩
      intro x hx
      exact ⟨x, hx, by simp [Metric.IsCover, edist_dist]⟩
    let f : ι → ℕ∞ := fun C => C.val.encard
    have h_exists : ∃ (C : ι), f C = ⨅ (x : ι), f x := ENat.exists_eq_iInf f
    rcases h_exists with ⟨C_min, hC_min_eq⟩
    have h_ext_def : Metric.externalCoveringNumber δ.toNNReal T_oriented = ⨅ (C : ι), f C := by
      have h : Metric.externalCoveringNumber δ.toNNReal T_oriented =
          ⨅ (C : Set AffineLine) (_ : Metric.IsCover δ.toNNReal T_oriented C), C.encard := by rfl
      rw [h]
      have h2 : (⨅ (C : Set AffineLine) (_ : Metric.IsCover δ.toNNReal T_oriented C), C.encard) =
          ⨅ (C : ι), f C := by rw [iInf_subtype] <;> rfl
      rw [h2]
    have h_encard_eq : (C_min.val).encard = Metric.externalCoveringNumber δ.toNNReal T_oriented := by
      have h10 : f C_min = Metric.externalCoveringNumber δ.toNNReal T_oriented := by
        rw [hC_min_eq, h_ext_def]
      simpa [f] using h10
    have h_fin : (C_min.val).Finite := by
      have h : (C_min.val).encard < ⊤ := by
        rw [h_encard_eq] <;> exact h_lt_top
      exact Set.encard_lt_top_iff.mp h
    let C_finset : Finset AffineLine := h_fin.toFinset
    have hC_coe : (C_finset : Set AffineLine) = C_min.val := by exact Set.Finite.coe_toFinset h_fin
    have h_cover : ∀ ℓ ∈ T_oriented, ∃ c ∈ C_finset, dist ℓ c ≤ δ := by
      intro ℓ hℓ
      have h := C_min.property hℓ
      rcases h with ⟨c, hc, hedist⟩
      have hdist : dist ℓ c ≤ δ := by
        have h_edist : edist ℓ c ≤ ↑δ.toNNReal := hedist
        have h_eq : edist ℓ c = ENNReal.ofReal (dist ℓ c) := by rw [edist_dist]
        rw [h_eq] at h_edist
        exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mp h_edist
      have hcin : c ∈ C_finset := by
        have h : c ∈ (C_finset : Set AffineLine) := by rw [hC_coe] <;> exact hc
        exact h
      exact ⟨c, hcin, hdist⟩

    have h_choose : ∀ (U : DyadicTube n), U ∈ T₀ →
        ∃ (c : AffineLine), c ∈ C_finset ∧ dist (toAffineLine U) c ≤ R := by
      intro U hU
      rcases h_prov U hU with ⟨ℓ, hℓ, hdist1⟩
      rcases h_cover ℓ hℓ with ⟨c, hc, hdist2⟩
      refine ⟨c, hc, ?_⟩
      have h_tri : dist (toAffineLine U) c ≤ dist (toAffineLine U) ℓ + dist ℓ c := dist_triangle _ _ _
      have h_sum : dist (toAffineLine U) ℓ + dist ℓ c ≤ C_move * δ + δ := by
        exact add_le_add hdist1 hdist2
      have h_eq : C_move * δ + δ = (C_move + 1) * δ := by ring
      rw [h_eq] at h_sum
      exact le_trans h_tri h_sum

    have h_affine_nonempty : Nonempty AffineLine :=
      ⟨toAffineLine (DyadicTube.mk (n := n) 0 0)⟩
    let chooseCenter : DyadicTube n → AffineLine := fun U =>
      if hU : U ∈ T₀ then (h_choose U hU).choose else Classical.choice h_affine_nonempty
    have hc1 : ∀ U ∈ T₀, chooseCenter U ∈ C_finset := by
      intro U hU
      have h9 : chooseCenter U = (h_choose U hU).choose := by
        simp [chooseCenter, hU]
      rw [h9]
      exact (h_choose U hU).choose_spec.1
    have hc2 : ∀ U ∈ T₀, dist (toAffineLine U) (chooseCenter U) ≤ R := by
      intro U hU
      have h9 : chooseCenter U = (h_choose U hU).choose := by
        simp [chooseCenter, hU]
      rw [h9]
      exact (h_choose U hU).choose_spec.2

    have h_fiber_bound : ∀ (center : AffineLine), center ∈ C_finset →
        (T₀.filter fun U => chooseCenter U = center).card ≤ K_pack := by
      intro center hc
      let F := T₀.filter fun U => chooseCenter U = center
      have hF_sub : F ⊆ T₀ := Finset.filter_subset _ _
      have h_dist_bound : ∀ U ∈ F, dist (toAffineLine U) center ≤ R := by
        intro U hU
        have hU' : U ∈ T₀ := hF_sub hU
        have h_eq : chooseCenter U = center := (Finset.mem_filter.mp hU).2
        have h : dist (toAffineLine U) (chooseCenter U) ≤ R := hc2 U hU'
        rw [h_eq] at h
        exact h
      have h_int_bound : ∀ (U1 : DyadicTube n), U1 ∈ F →
          ∀ (U2 : DyadicTube n), U2 ∈ F →
          |(U1.a : ℝ) - U2.a| ≤ D_grid ∧ |(U1.b : ℝ) - U2.b| ≤ D_grid := by
        intro U1 hU1 U2 hU2
        have hU1' : U1 ∈ T₀ := hF_sub hU1
        have hU2' : U2 ∈ T₀ := hF_sub hU2
        have h_d1 : dist (toAffineLine U1) center ≤ R := h_dist_bound U1 hU1
        have h_d2 : dist (toAffineLine U2) center ≤ R := h_dist_bound U2 hU2
        have h_dist12 : dist (toAffineLine U1) (toAffineLine U2) ≤ 2 * R := by
          have h_tri : dist (toAffineLine U1) (toAffineLine U2) ≤
              dist (toAffineLine U1) center + dist center (toAffineLine U2) := dist_triangle _ _ _
          have h_comm : dist center (toAffineLine U2) = dist (toAffineLine U2) center := dist_comm _ _
          rw [h_comm] at h_tri
          linarith
        -- swapLine is an isometry
        have h_iso : dist (swapped U1) (swapped U2) = dist (toAffineLine U1) (toAffineLine U2) :=
          swapLine_isometry.dist_eq (toAffineLine U1) (toAffineLine U2)
        -- Lipschitz bound on swapped lines
        have h_dir1 : (LemmaE.getDirV (swapped U1)) 1 ≠ 0 :=
          swapLine_getDirV_y_ne_zero U1.slope U1.intercept
        have h_dir2 : (LemmaE.getDirV (swapped U2)) 1 ≠ 0 :=
          swapLine_getDirV_y_ne_zero U2.slope U2.intercept
        have h_params1 : LemmaE.affineLineParams (swapped U1) = (U1.slope, U1.intercept) :=
          swapLine_params_eq U1.slope U1.intercept
        have h_params2 : LemmaE.affineLineParams (swapped U2) = (U2.slope, U2.intercept) :=
          swapLine_params_eq U2.slope U2.intercept
        have h_ha1 : |(LemmaE.affineLineParams (swapped U1)).1| ≤ 1 := by
          rw [h_params1] <;> exact hm U1 hU1'
        have h_ha2 : |(LemmaE.affineLineParams (swapped U2)).1| ≤ 1 := by
          rw [h_params2] <;> exact hm U2 hU2'
        have h_hb1 : |(LemmaE.affineLineParams (swapped U1)).2| ≤ 3 := by
          rw [h_params1] <;> exact hb U1 hU1'
        have h_hb2 : |(LemmaE.affineLineParams (swapped U2)).2| ≤ 3 := by
          rw [h_params2] <;> exact hb U2 hU2'
        have h_lip : dist (LemmaE.affineLineParams (swapped U1))
            (LemmaE.affineLineParams (swapped U2)) ≤
            8 * dist (swapped U1) (swapped U2) :=
          AffineLineLipschitzTransfer.affineLineParams_lipschitz_upper
            (swapped U1) (swapped U2) h_dir1 h_dir2 h_ha1 h_ha2 h_hb1 h_hb2
        rw [h_iso] at h_lip
        have h_param_dist : dist (LemmaE.affineLineParams (swapped U1))
            (LemmaE.affineLineParams (swapped U2)) ≤ 8 * (2 * R) :=
          calc _ ≤ 8 * dist (toAffineLine U1) (toAffineLine U2) := h_lip
               _ ≤ 8 * (2 * R) := by gcongr
        -- Coordinate bounds from product distance
        have h_slope_abs : |(LemmaE.affineLineParams (swapped U1)).1 -
            (LemmaE.affineLineParams (swapped U2)).1| ≤
            dist (LemmaE.affineLineParams (swapped U1)) (LemmaE.affineLineParams (swapped U2)) := by
          exact le_max_left _ _
        have h_intercept_abs : |(LemmaE.affineLineParams (swapped U1)).2 -
            (LemmaE.affineLineParams (swapped U2)).2| ≤
            dist (LemmaE.affineLineParams (swapped U1)) (LemmaE.affineLineParams (swapped U2)) := by
          exact le_max_right _ _
        have h_slope_real : |U1.slope - U2.slope| ≤ 8 * (2 * R) := by
          have h1 : |(LemmaE.affineLineParams (swapped U1)).1 -
              (LemmaE.affineLineParams (swapped U2)).1| ≤ 8 * (2 * R) :=
            le_trans h_slope_abs h_param_dist
          rw [h_params1, h_params2] at h1
          exact h1
        have h_intercept_real : |U1.intercept - U2.intercept| ≤ 8 * (2 * R) := by
          have h1 : |(LemmaE.affineLineParams (swapped U1)).2 -
              (LemmaE.affineLineParams (swapped U2)).2| ≤ 8 * (2 * R) :=
            le_trans h_intercept_abs h_param_dist
          rw [h_params1, h_params2] at h1
          exact h1
        have h_slope_def : U1.slope - U2.slope = δ_n * ((U1.a : ℝ) - U2.a) := by
          simp [DyadicTube.slope, hδ_n_def] <;> ring
        have h_intercept_def : U1.intercept - U2.intercept = δ_n * ((U1.b : ℝ) - U2.b) := by
          simp [DyadicTube.intercept, hδ_n_def] <;> ring
        rw [h_slope_def] at h_slope_real
        rw [h_intercept_def] at h_intercept_real
        have h_pos : 0 < δ_n := hδ_n_pos
        have h_a : |(U1.a : ℝ) - U2.a| ≤ (8 * (2 * R)) / δ_n := by
          have h : δ_n * |(U1.a : ℝ) - U2.a| ≤ 8 * (2 * R) := by
            have h3 : |δ_n * ((U1.a : ℝ) - U2.a)| = δ_n * |(U1.a : ℝ) - U2.a| := by
              rw [abs_mul, abs_of_pos h_pos]
            rw [h3] at h_slope_real
            exact h_slope_real
          calc |(U1.a : ℝ) - U2.a|
            = (δ_n * |(U1.a : ℝ) - U2.a|) / δ_n := by field_simp [h_pos.ne'] <;> ring
          _ ≤ (8 * (2 * R)) / δ_n := by gcongr
        have h_b : |(U1.b : ℝ) - U2.b| ≤ (8 * (2 * R)) / δ_n := by
          have h : δ_n * |(U1.b : ℝ) - U2.b| ≤ 8 * (2 * R) := by
            have h3 : |δ_n * ((U1.b : ℝ) - U2.b)| = δ_n * |(U1.b : ℝ) - U2.b| := by
              rw [abs_mul, abs_of_pos h_pos]
            rw [h3] at h_intercept_real
            exact h_intercept_real
          calc |(U1.b : ℝ) - U2.b|
            = (δ_n * |(U1.b : ℝ) - U2.b|) / δ_n := by field_simp [h_pos.ne'] <;> ring
          _ ≤ (8 * (2 * R)) / δ_n := by gcongr
        have h_bound : (8 * (2 * R)) / δ_n ≤ D_grid := by
          have hR : R = (C_move + 1) * δ := by rfl
          rw [hR, hD_grid_def]
          have h_pos2 : 0 < δ_n := hδ_n_pos
          have h9 : δ / δ_n < 2 := by
            have h10 : δ < 2 * δ_n := h_scale
            have h11 : δ / δ_n < (2 * δ_n) / δ_n := by gcongr
            have h12 : (2 * δ_n) / δ_n = 2 := by
              field_simp [h_pos2.ne'] <;> ring
            rw [h12] at h11
            exact h11
          have h11 : 0 ≤ C_move + 1 := by linarith
          calc (8 * (2 * ((C_move + 1) * δ))) / δ_n
            = 16 * (C_move + 1) * (δ / δ_n) := by ring_nf
          _ ≤ 16 * (C_move + 1) * 2 := by gcongr <;> linarith
          _ = 32 * (C_move + 1) := by ring
        exact ⟨le_trans h_a h_bound, le_trans h_b h_bound⟩
      let S : Finset (ℤ × ℤ) := F.image (fun U => (U.a, U.b))
      have h_inj : Set.InjOn (fun U : DyadicTube n => (U.a, U.b)) F := by
        intro U1 _ U2 _ h
        have h_all : U1.a = U2.a ∧ U1.b = U2.b := by
          simpa [Prod.ext_iff] using h
        rcases U1 with ⟨a1, b1⟩
        rcases U2 with ⟨a2, b2⟩
        have h_a : a1 = a2 := by simpa using h_all.1
        have h_b : b1 = b2 := by simpa using h_all.2
        congr
      have hS_card : S.card = F.card := by
        rw [Finset.card_image_of_injOn h_inj]
      have hS_bound : ∀ (x : ℤ × ℤ), x ∈ S → ∀ (y : ℤ × ℤ), y ∈ S →
          |(x.1 : ℝ) - y.1| ≤ D_grid ∧ |(x.2 : ℝ) - y.2| ≤ D_grid := by
        intro x hx y hy
        rcases Finset.mem_image.mp hx with ⟨U1, hU1, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨U2, hU2, rfl⟩
        exact h_int_bound U1 hU1 U2 hU2
      have h_grid : S.card ≤ K_pack := by
        have h : S.card ≤ (2 * Nat.ceil D_grid + 1)^2 :=
          grid_packing_bound (by positivity) hS_bound
        have h9 : Nat.ceil D_grid = K1 := by
          rw [hK1_def] <;> rfl
        rw [h9] at h
        exact h
      rw [hS_card] at h_grid
      exact h_grid

    have h_main : T₀.card ≤ K_pack * C_finset.card := by
      have h_union : T₀ = C_finset.biUnion (fun center => T₀.filter fun U => chooseCenter U = center) := by
        ext U
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        constructor
        · intro hU
          exact ⟨chooseCenter U, hc1 U hU, hU, rfl⟩
        · rintro ⟨center, _, hU, _⟩
          exact hU
      rw [h_union]
      have h_sum : (C_finset.biUnion (fun center => T₀.filter fun U => chooseCenter U = center)).card ≤
          ∑ center ∈ C_finset, (T₀.filter fun U => chooseCenter U = center).card :=
        Finset.card_biUnion_le
      calc _ ≤ ∑ center ∈ C_finset, (T₀.filter fun U => chooseCenter U = center).card := h_sum
           _ ≤ ∑ center ∈ C_finset, K_pack := by
             gcongr with center hc
             exact h_fiber_bound center hc
           _ = K_pack * C_finset.card := by
             rw [Finset.sum_const] <;> ring

    have h_final : (T₀.card : ENNReal) ≤ (K_pack : ENNReal) * (C_finset.card : ENNReal) := by
      exact_mod_cast h_main
    have hC_card : (C_finset.card : ENNReal) = Metric.externalCoveringNumber δ.toNNReal T_oriented := by
      have h1 : (C_min.val).encard = ↑C_finset.card := by
        rw [← hC_coe]
        simp [Set.encard]
      have h2 : (C_finset.card : ENNReal) = (C_min.val).encard := by
        exact_mod_cast h1.symm
      rw [h2, h_encard_eq]
    rw [hC_card] at h_final
    simpa [hK_pack_def] using h_final

end DirecretisedFurstenbergEstimate
