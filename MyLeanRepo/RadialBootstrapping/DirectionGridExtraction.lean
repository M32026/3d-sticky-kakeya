module

/-
  DirectionGridExtraction.lean

  Extract a direction-separated subfamily from concentrated tubes using
  greedy direction bin selection.

  Key results:
  1. tube_containment_general — direction closeness implies enlarged tube containment
  2. tube_containment_2r — specialization to 2r-tube
  3. direction_grid_extraction — main extraction lemma via strong induction

  Whiteprint node: bootstrapping (concentrated case)
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Finset Classical
open scoped ENNReal NNReal


noncomputable section

namespace RadialBootstrapping

/-! ============================================================================
   Geometric lemmas
   ============================================================================ -/

/-- General geometric lemma: if two affine lines through `x` have direction
    distance ≤ `δ`, and `y` is in the `r`-tube of `ℓ₂` with `dist(x,y) ≤ D`,
    then `y` is in the `(r + δ * (D + r))`-tube of `ℓ₁`. -/
lemma tube_containment_general
    (x : Point) (ℓ₁ ℓ₂ : AffineSubspace ℝ Point)
    (hx₁ : x ∈ (ℓ₁ : Set Point)) (hx₂ : x ∈ (ℓ₂ : Set Point))
    (hfin₁ : Module.finrank ℝ ℓ₁.direction = 1)
    (hfin₂ : Module.finrank ℝ ℓ₂.direction = 1)
    (r D δ : ℝ) (hr : 0 < r) (hδ_nonneg : 0 ≤ δ)
    (h_dir : submoduleDirDist ℓ₁.direction ℓ₂.direction ≤ δ)
    (y : Point) (hy_in_tube : y ∈ Metric.thickening r (ℓ₂ : Set Point))
    (hy_dist : dist x y ≤ D) :
    y ∈ Metric.thickening (r + δ * (D + r)) (ℓ₁ : Set Point) := by
  rcases Metric.mem_thickening_iff.mp hy_in_tube with ⟨y', hy'_in, hyy'⟩
  let V1 := ℓ₁.direction
  let V2 := ℓ₂.direction
  have h2 : y' - x ∈ V2 := AffineSubspace.vsub_mem_direction hy'_in hx₂
  have h_proj_id : V2.starProjection (y' - x) = y' - x :=
    Submodule.starProjection_eq_self_iff.mpr h2
  have h3 : ‖y' - x‖ ≤ D + r := by
    have h31 : dist y' x ≤ dist y' y + dist y x := dist_triangle _ _ _
    have h32 : dist y' x = ‖y' - x‖ := by simp [dist_eq_norm]
    have h33 : dist y' y < r := by rwa [dist_comm]
    have h34 : dist y x ≤ D := by rwa [dist_comm]
    rw [←h32]; linarith
  have h_decomp1 : (y' - x) - V1.starProjection (y' - x) =
      (V2.starProjection - V1.starProjection) (y' - x) := by
    have h4 : (V2.starProjection - V1.starProjection) (y' - x) =
        V2.starProjection (y' - x) - V1.starProjection (y' - x) := by
      exact sub_apply V2.starProjection V1.starProjection (y' - x)
    rw [h4, h_proj_id] <;> abel
  have h_perp1 : ‖(y' - x) - V1.starProjection (y' - x)‖ ≤ δ * ‖y' - x‖ := by
    rw [h_decomp1]
    have h5 : ‖(V2.starProjection - V1.starProjection) (y' - x)‖ ≤
        ‖V2.starProjection - V1.starProjection‖ * ‖y' - x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h6 : ‖V2.starProjection - V1.starProjection‖ = submoduleDirDist V1 V2 := by
      have h7 : submoduleDirDist V1 V2 = ‖V1.starProjection - V2.starProjection‖ := by
        simp [submoduleDirDist, submoduleProj_eq_starProjection] <;> rfl
      have h8 : ‖V2.starProjection - V1.starProjection‖ = ‖V1.starProjection - V2.starProjection‖ := by
        rw [show V2.starProjection - V1.starProjection = -(V1.starProjection - V2.starProjection) by
          ext z; simp <;> abel]
        rw [norm_neg]
      rw [h8, h7]
    rw [h6] at h5
    exact le_trans h5 (mul_le_mul_of_nonneg_right h_dir (by positivity))
  set q := (y - y') - V1.starProjection (y - y') with hq_def
  have h_norm_sq : ‖y - y'‖ ^ 2 = ‖q‖ ^ 2 + ‖V1.starProjection (y - y')‖ ^ 2 := by
    have h := V1.orthogonalProjectionFn_norm_sq (y - y')
    have h' : ‖y - y'‖ * ‖y - y'‖ = ‖q‖ * ‖q‖ + ‖V1.starProjection (y - y')‖ * ‖V1.starProjection (y - y')‖ := by
      simpa [hq_def] using h
    have h1 : ‖y - y'‖ * ‖y - y'‖ = ‖y - y'‖ ^ 2 := by ring
    have h2 : ‖q‖ * ‖q‖ = ‖q‖ ^ 2 := by ring
    have h3 : ‖V1.starProjection (y - y')‖ * ‖V1.starProjection (y - y')‖ = ‖V1.starProjection (y - y')‖ ^ 2 := by ring
    rw [h1, h2, h3] at h'; exact h'
  have h_perp2 : ‖q‖ ≤ ‖y - y'‖ := by
    have h4 : ‖q‖ ^ 2 ≤ ‖y - y'‖ ^ 2 := by rw [h_norm_sq] <;> nlinarith
    nlinarith [norm_nonneg q, norm_nonneg (y - y')]
  have h_yy'_lt_r : ‖y - y'‖ < r := by simpa [dist_eq_norm] using hyy'
  have h_decomp2 : (y - x) - V1.starProjection (y - x) =
      ((y' - x) - V1.starProjection (y' - x)) + q := by
    have h5 : V1.starProjection (y - x) = V1.starProjection (y' - x) + V1.starProjection (y - y') := by
      rw [show y - x = (y' - x) + (y - y') by abel]
      exact V1.starProjection.map_add _ _
    rw [h5, hq_def] <;> abel
  have h_part1 : ‖(y' - x) - V1.starProjection (y' - x)‖ ≤ δ * (D + r) := by
    calc
      ‖(y' - x) - V1.starProjection (y' - x)‖ ≤ δ * ‖y' - x‖ := h_perp1
      _ ≤ δ * (D + r) := by gcongr <;> linarith
  have h_part2 : ‖q‖ < r := by
    calc ‖q‖ ≤ ‖y - y'‖ := h_perp2
         _ < r := h_yy'_lt_r
  have h_main : ‖(y - x) - V1.starProjection (y - x)‖ < r + δ * (D + r) := by
    rw [h_decomp2]
    have h_sum : ‖((y' - x) - V1.starProjection (y' - x)) + q‖ ≤
        ‖(y' - x) - V1.starProjection (y' - x)‖ + ‖q‖ := norm_add_le _ _
    have h_strict : ‖(y' - x) - V1.starProjection (y' - x)‖ + ‖q‖ < r + δ * (D + r) := by
      linarith
    exact lt_of_le_of_lt h_sum h_strict
  let z : Point := x + V1.starProjection (y - x)
  have hz_in : z ∈ (ℓ₁ : Set Point) := by
    have h14 : V1.starProjection (y - x) ∈ V1 := Submodule.starProjection_apply_mem V1 (y - x)
    have h15 : V1.starProjection (y - x) +ᵥ x ∈ (ℓ₁ : Set Point) :=
      AffineSubspace.vadd_mem_of_mem_direction h14 hx₁
    have h16 : V1.starProjection (y - x) +ᵥ x = x + V1.starProjection (y - x) := by
      rw [vadd_eq_add] <;> abel
    rw [h16] at h15
    exact h15
  have h17 : dist y z < r + δ * (D + r) := by
    have h18 : y - z = (y - x) - V1.starProjection (y - x) := by simp [z] <;> abel
    have h19 : dist y z = ‖y - z‖ := by simp [dist_eq_norm]
    rw [h19, h18]; exact h_main
  exact Metric.mem_thickening_iff.mpr ⟨z, hz_in, h17⟩

/-- Specialization: direction distance ≤ r/(4R), dist ≤ 2R+r^κ, r^κ ≤ R
    gives containment in the 2r-tube. -/
lemma tube_containment_2r
    (x : Point) (ℓ₁ ℓ₂ : AffineSubspace ℝ Point)
    (hx₁ : x ∈ (ℓ₁ : Set Point)) (hx₂ : x ∈ (ℓ₂ : Set Point))
    (hfin₁ : Module.finrank ℝ ℓ₁.direction = 1)
    (hfin₂ : Module.finrank ℝ ℓ₂.direction = 1)
    (r R κ : ℝ) (hr : 0 < r) (hR_pos : 0 < R) (hR_ge_r : r ≤ R)
    (hκ_pos : 0 < κ) (hκ_lt_one : κ < 1) (hr_small : r < 1)
    (h_rκ_le_R : Real.rpow r κ ≤ R)
    (h_dir : submoduleDirDist ℓ₁.direction ℓ₂.direction ≤ r / (4 * R))
    (y : Point) (hy_in_tube : y ∈ Metric.thickening r (ℓ₂ : Set Point))
    (hy_dist : dist x y ≤ 2 * R + Real.rpow r κ) :
    y ∈ Metric.thickening (2 * r) (ℓ₁ : Set Point) := by
  let δ : ℝ := r / (4 * R)
  let D : ℝ := 2 * R + Real.rpow r κ
  have hδ_nonneg : 0 ≤ δ := by positivity
  have h_rout_le_2r : r + δ * (D + r) ≤ 2 * r := by
    have h1 : D + r ≤ 4 * R := by simp only [D]; linarith [h_rκ_le_R, hR_ge_r]
    have h2 : δ * (D + r) ≤ r := by
      calc δ * (D + r) ≤ δ * (4 * R) := by gcongr
           _ = r := by simp only [δ]; field_simp [hR_pos.ne'] <;> ring
    linarith
  have h_general := tube_containment_general x ℓ₁ ℓ₂ hx₁ hx₂ hfin₁ hfin₂
    r D δ hr hδ_nonneg h_dir y hy_in_tube hy_dist
  have h_mono : Metric.thickening (r + δ * (D + r)) (ℓ₁ : Set Point) ⊆
      Metric.thickening (2 * r) (ℓ₁ : Set Point) :=
    Metric.thickening_mono h_rout_le_2r (ℓ₁ : Set Point)
  exact h_mono h_general

/-! ============================================================================
   Main extraction lemma (proof uses strong induction with inlined selection)
   ============================================================================ -/

/-- Greedy direction-bin extraction. -/
lemma direction_grid_extraction
    {ν : Measure Point} [IsProbabilityMeasure ν]
    (x : Point)
    (T : Finset (AffineSubspace ℝ Point))
    (P : AffineSubspace ℝ Point → Set Point)
    (G_x : Set Point)
    (r R κ m K σ : ℝ)
    (hr : 0 < r) (hr_small : r < 1)
    (hR_pos : 0 < R) (hR_ge_r : r ≤ R)
    (hκ_pos : 0 < κ) (hκ_lt_one : κ < 1)
    (h_rκ_le_R : Real.rpow r κ ≤ R)
    (hm_pos : 0 < m) (hK_pos : 0 < K) (hσ : 0 ≤ σ)
    (h_lines : ∀ ℓ ∈ T, x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1)
    (hP_sub_tube : ∀ ℓ ∈ T, P ℓ ⊆ Metric.thickening r (ℓ : Set Point))
    (hP_sub_Gx : ∀ ℓ ∈ T, P ℓ ⊆ G_x)
    (hP_meas : ∀ ℓ ∈ T, MeasurableSet (P ℓ))
    (hP_mass : ∀ ℓ ∈ T, ν (P ℓ) ≥ ENNReal.ofReal m)
    (hP_bounded : ∀ ℓ ∈ T, ∀ y ∈ P ℓ, dist x y ≤ 2 * R + Real.rpow r κ)
    (h_forward : ∀ (ℓ : AffineSubspace ℝ Point),
      x ∈ (ℓ : Set Point) → Module.finrank ℝ ℓ.direction = 1 →
      ∀ (r' : ℝ), 0 < r' →
        ν (Metric.thickening r' (ℓ : Set Point) ∩ G_x) ≤
          ENNReal.ofReal (K * Real.rpow r' σ)) :
    ∃ (S : Finset (AffineSubspace ℝ Point)),
      S ⊆ T ∧
      (∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ →
        submoduleDirDist ℓ₁.direction ℓ₂.direction > r / (4 * R)) ∧
      (S.card : ENNReal) * ENNReal.ofReal m ≥
        ν (⋃ ℓ ∈ T, P ℓ) * ENNReal.ofReal m /
          ENNReal.ofReal (K * Real.rpow (2 * r) σ) := by
  classical
  let C : ENNReal := ENNReal.ofReal (K * Real.rpow (2 * r) σ)
  have h_rpow_pos : 0 < Real.rpow (2 * r) σ := Real.rpow_pos_of_pos (by positivity) σ
  have hC_pos_real : 0 < K * Real.rpow (2 * r) σ := mul_pos hK_pos h_rpow_pos
  have hC_ne_zero : C ≠ 0 := (ENNReal.ofReal_pos.mpr hC_pos_real).ne'
  have hC_ne_top : C ≠ ⊤ := ENNReal.ofReal_ne_top
  let m' : ENNReal := ENNReal.ofReal m
  let δ : ℝ := r / (4 * R)

  -- Induction predicate: for any subset T_rem ⊆ T, there exists a good S
  let p : Finset (AffineSubspace ℝ Point) → Prop := fun T_rem =>
    T_rem ⊆ T →
      ∃ (S : Finset (AffineSubspace ℝ Point)),
        S ⊆ T_rem ∧
        (∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ →
          submoduleDirDist ℓ₁.direction ℓ₂.direction > δ) ∧
        ν (⋃ ℓ ∈ T_rem, P ℓ) ≤ (S.card : ENNReal) * C

  have h_step : ∀ (s : Finset (AffineSubspace ℝ Point)),
      (∀ (t : Finset (AffineSubspace ℝ Point)), t ⊂ s → p t) → p s := by
    intro s ih hT_sub
    by_cases hne : s.Nonempty
    · -- Nonempty case: pick ℓ, remove bin, recurse on T' = s \ bin
      let ℓ : AffineSubspace ℝ Point := Classical.choose hne
      have hℓ : ℓ ∈ s := Classical.choose_spec hne
      have hℓ_T : ℓ ∈ T := hT_sub hℓ
      let bin := s.filter (fun ℓ' => submoduleDirDist ℓ'.direction ℓ.direction ≤ δ)
      have hbin_sub : bin ⊆ s := filter_subset _ _
      have hℓ_in_bin : ℓ ∈ bin := by
        simp [bin, hℓ, submoduleDirDist_self] <;> linarith [show (0 : ℝ) ≤ δ from by positivity]
      let T' := s \ bin
      have hT'_sub_s : T' ⊆ s := by intro z hz; exact (Finset.mem_sdiff.mp hz).1
      have hT'_sub_T : T' ⊆ T := subset_trans hT'_sub_s hT_sub
      have hT'_ssub : T' ⊂ s := by
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · exact hT'_sub_s
        · intro h_eq
          have h : ℓ ∈ T' := by rw [h_eq] <;> exact hℓ
          have h' : ℓ ∉ T' := by simp [T', hℓ_in_bin]
          exact h' h
      rcases ih T' hT'_ssub hT'_sub_T with ⟨S', hS'_sub, hS'_sep, hS'_mass⟩
      let S := insert ℓ S'
      have hℓ_not_in_S' : ℓ ∉ S' := by
        have hℓ_not_in_T' : ℓ ∉ T' := by simp [T', hℓ_in_bin]
        exact fun h => hℓ_not_in_T' (hS'_sub h)
      have h_card : S.card = S'.card + 1 := by
        rw [Finset.card_insert_of_notMem hℓ_not_in_S'] <;> rfl
      have h_card' : (S.card : ENNReal) = (S'.card : ENNReal) + 1 := by exact_mod_cast h_card
      have hS_sub_s : S ⊆ s := by
        intro z hz
        simp only [S, Finset.mem_insert] at hz
        rcases hz with (rfl | hz)
        · exact hℓ
        · exact hT'_sub_s (hS'_sub hz)
      have hS_sep : ∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ →
          submoduleDirDist ℓ₁.direction ℓ₂.direction > δ := by
        intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ hneq
        simp only [S, Finset.mem_insert] at hℓ₁ hℓ₂
        rcases hℓ₁ with (rfl | hℓ₁)
        · rcases hℓ₂ with (rfl | hℓ₂)
          · exfalso; exact hneq rfl
          · have h_not_in_bin : ℓ₂ ∉ bin := (Finset.mem_sdiff.mp (hS'_sub hℓ₂)).2
            have h_gt : submoduleDirDist ℓ₂.direction ℓ.direction > δ := by
              by_contra h
              have h_le : submoduleDirDist ℓ₂.direction ℓ.direction ≤ δ := by linarith
              exact h_not_in_bin (Finset.mem_filter.mpr ⟨hT'_sub_s (hS'_sub hℓ₂), h_le⟩)
            simpa [submoduleDirDist_comm] using h_gt
        · rcases hℓ₂ with (rfl | hℓ₂)
          · have h_not_in_bin : ℓ₁ ∉ bin := (Finset.mem_sdiff.mp (hS'_sub hℓ₁)).2
            have h_gt : submoduleDirDist ℓ₁.direction ℓ.direction > δ := by
              by_contra h
              have h_le : submoduleDirDist ℓ₁.direction ℓ.direction ≤ δ := by linarith
              exact h_not_in_bin (Finset.mem_filter.mpr ⟨hT'_sub_s (hS'_sub hℓ₁), h_le⟩)
            exact h_gt
          · exact hS'_sep ℓ₁ hℓ₁ ℓ₂ hℓ₂ hneq
      have h_bin_cover : (⋃ ℓ' ∈ bin, P ℓ') ⊆
          Metric.thickening (2 * r) (ℓ : Set Point) ∩ G_x := by
        intro y hy
        have h_ty : ∃ (ℓ' : AffineSubspace ℝ Point), ℓ' ∈ bin ∧ y ∈ P ℓ' := by
          simpa [Finset.mem_biUnion] using hy
        rcases h_ty with ⟨ℓ', hℓ'_bin, hy_P⟩
        have hℓ'_s : ℓ' ∈ s := hbin_sub hℓ'_bin
        have hℓ'_T : ℓ' ∈ T := hT_sub hℓ'_s
        have h_lines' := h_lines ℓ' hℓ'_T
        have h_dir' : submoduleDirDist ℓ'.direction ℓ.direction ≤ δ :=
          (Finset.mem_filter.mp hℓ'_bin).2
        have h_in_tube : y ∈ Metric.thickening r (ℓ' : Set Point) := hP_sub_tube ℓ' hℓ'_T hy_P
        have h_dist : dist x y ≤ 2 * R + Real.rpow r κ := hP_bounded ℓ' hℓ'_T y hy_P
        have h_in_2r : y ∈ Metric.thickening (2 * r) (ℓ : Set Point) :=
          tube_containment_2r x ℓ ℓ'
            (h_lines ℓ hℓ_T).1 h_lines'.1
            (h_lines ℓ hℓ_T).2 h_lines'.2
            r R κ hr hR_pos hR_ge_r hκ_pos hκ_lt_one hr_small h_rκ_le_R
            (by simpa [submoduleDirDist_comm] using h_dir')
            y h_in_tube h_dist
        have h_in_Gx : y ∈ G_x := hP_sub_Gx ℓ' hℓ'_T hy_P
        exact ⟨h_in_2r, h_in_Gx⟩
      have h_bin_mass : ν (⋃ ℓ' ∈ bin, P ℓ') ≤ C := by
        have h1 : ν (⋃ ℓ' ∈ bin, P ℓ') ≤ ν (Metric.thickening (2 * r) (ℓ : Set Point) ∩ G_x) :=
          measure_mono h_bin_cover
        have h2 := h_forward ℓ (h_lines ℓ hℓ_T).1 (h_lines ℓ hℓ_T).2 (2 * r) (by linarith)
        exact le_trans h1 h2
      have h_decomp : s = bin ∪ T' := by
        ext z; simp [T', bin] <;> tauto
      have h_union : (⋃ ℓ' ∈ s, P ℓ') = (⋃ ℓ' ∈ bin, P ℓ') ∪ (⋃ ℓ' ∈ T', P ℓ') := by
        rw [h_decomp]
        exact Finset.set_biUnion_union bin T' P
      have h_mass : ν (⋃ ℓ' ∈ s, P ℓ') ≤ (S.card : ENNReal) * C := by
        rw [h_union]
        have h3 : ν ((⋃ ℓ' ∈ bin, P ℓ') ∪ (⋃ ℓ' ∈ T', P ℓ')) ≤
            ν (⋃ ℓ' ∈ bin, P ℓ') + ν (⋃ ℓ' ∈ T', P ℓ') := measure_union_le _ _
        have h4 : ν (⋃ ℓ' ∈ T', P ℓ') ≤ (S'.card : ENNReal) * C := hS'_mass
        calc
          ν ((⋃ ℓ' ∈ bin, P ℓ') ∪ (⋃ ℓ' ∈ T', P ℓ'))
            ≤ ν (⋃ ℓ' ∈ bin, P ℓ') + ν (⋃ ℓ' ∈ T', P ℓ') := h3
          _ ≤ C + (S'.card : ENNReal) * C := by gcongr
          _ = (S.card : ENNReal) * C := by
            rw [h_card']; simp [add_mul, one_mul] <;> abel
      exact ⟨S, hS_sub_s, hS_sep, h_mass⟩
    · -- Empty case
      have h_empty : s = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using hne
      rw [h_empty]
      simpa [p] using show (∅ ⊆ T → ∃ (S : Finset (AffineSubspace ℝ Point)),
          S ⊆ (∅ : Finset (AffineSubspace ℝ Point)) ∧
          (∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ → submoduleDirDist ℓ₁.direction ℓ₂.direction > δ) ∧
          ν (⋃ ℓ ∈ (∅ : Finset (AffineSubspace ℝ Point)), P ℓ) ≤ (S.card : ENNReal) * C) from
        intro _
        exact ⟨∅, by simp, by simp, by simp⟩

  have h_ind : ∀ (T_rem : Finset (AffineSubspace ℝ Point)), p T_rem :=
    fun T_rem => Finset.strongInductionOn T_rem h_step
  rcases h_ind T (by rfl) with ⟨S, hS_sub, hS_sep, hS_mass⟩
  have h_final : ν (⋃ ℓ ∈ T, P ℓ) * m' / C ≤ (S.card : ENNReal) * m' := by
    have h9 : ν (⋃ ℓ ∈ T, P ℓ) ≤ (S.card : ENNReal) * C := hS_mass
    have h10 : ν (⋃ ℓ ∈ T, P ℓ) * (m' / C) ≤ ((S.card : ENNReal) * C) * (m' / C) := by gcongr
    have h11 : C * (m' / C) = m' := ENNReal.mul_div_cancel hC_ne_zero hC_ne_top
    have h12 : ((S.card : ENNReal) * C) * (m' / C) = (S.card : ENNReal) * m' := by
      rw [mul_assoc, h11] <;> ring
    have h13 : ν (⋃ ℓ ∈ T, P ℓ) * m' / C = ν (⋃ ℓ ∈ T, P ℓ) * (m' / C) := by
      simp [div_eq_mul_inv, mul_assoc] <;> ring
    rw [h13]; rw [h12] at h10; exact h10
  exact ⟨S, hS_sub, hS_sep, by simpa [m', C] using h_final⟩

/-- Variant of `direction_grid_extraction` without per-piece mass lower bound.

    Concludes the union mass bound `ν(⋃ P ℓ) ≤ |S| · K · (2r)^σ`
    and direction separation. Useful when pieces have unknown or variable mass. -/
lemma direction_grid_extraction_card
    {ν : Measure Point} [IsProbabilityMeasure ν]
    (x : Point)
    (T : Finset (AffineSubspace ℝ Point))
    (P : AffineSubspace ℝ Point → Set Point)
    (G_x : Set Point)
    (r R κ K σ : ℝ)
    (hr : 0 < r) (hr_small : r < 1)
    (hR_pos : 0 < R) (hR_ge_r : r ≤ R)
    (hκ_pos : 0 < κ) (hκ_lt_one : κ < 1)
    (h_rκ_le_R : Real.rpow r κ ≤ R)
    (hK_pos : 0 < K) (hσ : 0 ≤ σ)
    (h_lines : ∀ ℓ ∈ T, x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1)
    (hP_sub_tube : ∀ ℓ ∈ T, P ℓ ⊆ Metric.thickening r (ℓ : Set Point))
    (hP_sub_Gx : ∀ ℓ ∈ T, P ℓ ⊆ G_x)
    (hP_meas : ∀ ℓ ∈ T, MeasurableSet (P ℓ))
    (hP_bounded : ∀ ℓ ∈ T, ∀ y ∈ P ℓ, dist x y ≤ 2 * R + Real.rpow r κ)
    (h_forward : ∀ (ℓ : AffineSubspace ℝ Point),
      x ∈ (ℓ : Set Point) → Module.finrank ℝ ℓ.direction = 1 →
      ∀ (r' : ℝ), 0 < r' →
        ν (Metric.thickening r' (ℓ : Set Point) ∩ G_x) ≤
          ENNReal.ofReal (K * Real.rpow r' σ)) :
    ∃ (S : Finset (AffineSubspace ℝ Point)),
      S ⊆ T ∧
      (∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ →
        submoduleDirDist ℓ₁.direction ℓ₂.direction > r / (4 * R)) ∧
      ν (⋃ ℓ ∈ T, P ℓ) ≤
        (S.card : ENNReal) * ENNReal.ofReal (K * Real.rpow (2 * r) σ) := by
  classical
  let C : ENNReal := ENNReal.ofReal (K * Real.rpow (2 * r) σ)
  have h_rpow_pos : 0 < Real.rpow (2 * r) σ := Real.rpow_pos_of_pos (by positivity) σ
  have hC_pos_real : 0 < K * Real.rpow (2 * r) σ := mul_pos hK_pos h_rpow_pos
  have hC_ne_zero : C ≠ 0 := (ENNReal.ofReal_pos.mpr hC_pos_real).ne'
  have hC_ne_top : C ≠ ⊤ := ENNReal.ofReal_ne_top
  let δ : ℝ := r / (4 * R)
  let p : Finset (AffineSubspace ℝ Point) → Prop := fun T_rem =>
    T_rem ⊆ T →
      ∃ (S : Finset (AffineSubspace ℝ Point)),
        S ⊆ T_rem ∧
        (∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ →
          submoduleDirDist ℓ₁.direction ℓ₂.direction > δ) ∧
        ν (⋃ ℓ ∈ T_rem, P ℓ) ≤ (S.card : ENNReal) * C
  have h_step : ∀ (s : Finset (AffineSubspace ℝ Point)),
      (∀ (t : Finset (AffineSubspace ℝ Point)), t ⊂ s → p t) → p s := by
    intro s ih hT_sub
    by_cases hne : s.Nonempty
    · let ℓ : AffineSubspace ℝ Point := Classical.choose hne
      have hℓ : ℓ ∈ s := Classical.choose_spec hne
      have hℓ_T : ℓ ∈ T := hT_sub hℓ
      let bin := s.filter (fun ℓ' => submoduleDirDist ℓ'.direction ℓ.direction ≤ δ)
      have hbin_sub : bin ⊆ s := filter_subset _ _
      have hℓ_in_bin : ℓ ∈ bin := by
        simp [bin, hℓ, submoduleDirDist_self] <;> linarith [show (0 : ℝ) ≤ δ from by positivity]
      let T' := s \ bin
      have hT'_sub_s : T' ⊆ s := by intro z hz; exact (Finset.mem_sdiff.mp hz).1
      have hT'_sub_T : T' ⊆ T := subset_trans hT'_sub_s hT_sub
      have hT'_ssub : T' ⊂ s := by
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · exact hT'_sub_s
        · intro h_eq
          have h : ℓ ∈ T' := by rw [h_eq] <;> exact hℓ
          have h' : ℓ ∉ T' := by simp [T', hℓ_in_bin]
          exact h' h
      rcases ih T' hT'_ssub hT'_sub_T with ⟨S', hS'_sub, hS'_sep, hS'_mass⟩
      let S := insert ℓ S'
      have hℓ_not_in_S' : ℓ ∉ S' := by
        have hℓ_not_in_T' : ℓ ∉ T' := by simp [T', hℓ_in_bin]
        exact fun h => hℓ_not_in_T' (hS'_sub h)
      have h_card : S.card = S'.card + 1 := by
        rw [Finset.card_insert_of_notMem hℓ_not_in_S'] <;> rfl
      have h_card' : (S.card : ENNReal) = (S'.card : ENNReal) + 1 := by exact_mod_cast h_card
      have hS_sub_s : S ⊆ s := by
        intro z hz
        simp only [S, Finset.mem_insert] at hz
        rcases hz with (rfl | hz)
        · exact hℓ
        · exact hT'_sub_s (hS'_sub hz)
      have hS_sep : ∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ →
          submoduleDirDist ℓ₁.direction ℓ₂.direction > δ := by
        intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ hneq
        simp only [S, Finset.mem_insert] at hℓ₁ hℓ₂
        rcases hℓ₁ with (rfl | hℓ₁)
        · rcases hℓ₂ with (rfl | hℓ₂)
          · exfalso; exact hneq rfl
          · have h_not_in_bin : ℓ₂ ∉ bin := (Finset.mem_sdiff.mp (hS'_sub hℓ₂)).2
            have h_gt : submoduleDirDist ℓ₂.direction ℓ.direction > δ := by
              by_contra h
              have h_le : submoduleDirDist ℓ₂.direction ℓ.direction ≤ δ := by linarith
              exact h_not_in_bin (Finset.mem_filter.mpr ⟨hT'_sub_s (hS'_sub hℓ₂), h_le⟩)
            simpa [submoduleDirDist_comm] using h_gt
        · rcases hℓ₂ with (rfl | hℓ₂)
          · have h_not_in_bin : ℓ₁ ∉ bin := (Finset.mem_sdiff.mp (hS'_sub hℓ₁)).2
            have h_gt : submoduleDirDist ℓ₁.direction ℓ.direction > δ := by
              by_contra h
              have h_le : submoduleDirDist ℓ₁.direction ℓ.direction ≤ δ := by linarith
              exact h_not_in_bin (Finset.mem_filter.mpr ⟨hT'_sub_s (hS'_sub hℓ₁), h_le⟩)
            exact h_gt
          · exact hS'_sep ℓ₁ hℓ₁ ℓ₂ hℓ₂ hneq
      have h_bin_cover : (⋃ ℓ' ∈ bin, P ℓ') ⊆
          Metric.thickening (2 * r) (ℓ : Set Point) ∩ G_x := by
        intro y hy
        have h_ty : ∃ (ℓ' : AffineSubspace ℝ Point), ℓ' ∈ bin ∧ y ∈ P ℓ' := by
          simpa [Finset.mem_biUnion] using hy
        rcases h_ty with ⟨ℓ', hℓ'_bin, hy_P⟩
        have hℓ'_s : ℓ' ∈ s := hbin_sub hℓ'_bin
        have hℓ'_T : ℓ' ∈ T := hT_sub hℓ'_s
        have h_lines' := h_lines ℓ' hℓ'_T
        have h_dir' : submoduleDirDist ℓ'.direction ℓ.direction ≤ δ :=
          (Finset.mem_filter.mp hℓ'_bin).2
        have h_in_tube : y ∈ Metric.thickening r (ℓ' : Set Point) := hP_sub_tube ℓ' hℓ'_T hy_P
        have h_dist : dist x y ≤ 2 * R + Real.rpow r κ := hP_bounded ℓ' hℓ'_T y hy_P
        have h_in_2r : y ∈ Metric.thickening (2 * r) (ℓ : Set Point) :=
          tube_containment_2r x ℓ ℓ'
            (h_lines ℓ hℓ_T).1 h_lines'.1
            (h_lines ℓ hℓ_T).2 h_lines'.2
            r R κ hr hR_pos hR_ge_r hκ_pos hκ_lt_one hr_small h_rκ_le_R
            (by simpa [submoduleDirDist_comm] using h_dir')
            y h_in_tube h_dist
        have h_in_Gx : y ∈ G_x := hP_sub_Gx ℓ' hℓ'_T hy_P
        exact ⟨h_in_2r, h_in_Gx⟩
      have h_bin_mass : ν (⋃ ℓ' ∈ bin, P ℓ') ≤ C := by
        have h1 : ν (⋃ ℓ' ∈ bin, P ℓ') ≤ ν (Metric.thickening (2 * r) (ℓ : Set Point) ∩ G_x) :=
          measure_mono h_bin_cover
        have h2 := h_forward ℓ (h_lines ℓ hℓ_T).1 (h_lines ℓ hℓ_T).2 (2 * r) (by linarith)
        exact le_trans h1 h2
      have h_decomp : s = bin ∪ T' := by
        ext z; simp [T', bin] <;> tauto
      have h_union : (⋃ ℓ' ∈ s, P ℓ') = (⋃ ℓ' ∈ bin, P ℓ') ∪ (⋃ ℓ' ∈ T', P ℓ') := by
        rw [h_decomp]
        exact Finset.set_biUnion_union bin T' P
      have h_mass : ν (⋃ ℓ' ∈ s, P ℓ') ≤ (S.card : ENNReal) * C := by
        rw [h_union]
        have h3 : ν ((⋃ ℓ' ∈ bin, P ℓ') ∪ (⋃ ℓ' ∈ T', P ℓ')) ≤
            ν (⋃ ℓ' ∈ bin, P ℓ') + ν (⋃ ℓ' ∈ T', P ℓ') := measure_union_le _ _
        have h4 : ν (⋃ ℓ' ∈ T', P ℓ') ≤ (S'.card : ENNReal) * C := hS'_mass
        calc
          ν ((⋃ ℓ' ∈ bin, P ℓ') ∪ (⋃ ℓ' ∈ T', P ℓ'))
            ≤ ν (⋃ ℓ' ∈ bin, P ℓ') + ν (⋃ ℓ' ∈ T', P ℓ') := h3
          _ ≤ C + (S'.card : ENNReal) * C := by gcongr
          _ = (S.card : ENNReal) * C := by
            rw [h_card']; simp [add_mul, one_mul] <;> abel
      exact ⟨S, hS_sub_s, hS_sep, h_mass⟩
    · have h_empty : s = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using hne
      rw [h_empty]
      simpa [p] using show (∅ ⊆ T → ∃ (S : Finset (AffineSubspace ℝ Point)),
          S ⊆ (∅ : Finset (AffineSubspace ℝ Point)) ∧
          (∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ → submoduleDirDist ℓ₁.direction ℓ₂.direction > δ) ∧
          ν (⋃ ℓ ∈ (∅ : Finset (AffineSubspace ℝ Point)), P ℓ) ≤ (S.card : ENNReal) * C) from
        intro _
        exact ⟨∅, by simp, by simp, by simp⟩
  have h_ind : ∀ (T_rem : Finset (AffineSubspace ℝ Point)), p T_rem :=
    fun T_rem => Finset.strongInductionOn T_rem h_step
  exact h_ind T (by rfl)

end RadialBootstrapping
