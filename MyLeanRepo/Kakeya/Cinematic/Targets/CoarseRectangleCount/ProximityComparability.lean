import MyLeanRepo.Kakeya.Cinematic.Geometry

namespace Kakeya.Cinematic

/--
If two `(δ,t)`-curvilinear rectangles have close functions and nearby midpoints,
they are `λ`-comparable: both fit inside a common `(λδ,t)`-rectangle whose
defining function belongs to the same cinematic family.

The central-quarter hypotheses are not needed for this lemma but are retained
to match the calling context in PYZ Lemma 25.
-/
lemma proximity_implies_comparability
    {δ t lambda : ℝ} (hδ : 0 < δ) (ht : 0 < t) (hlambda : 100 ≤ lambda)
    (hadm : IsAdmissibleComparisonScale δ t lambda)
    {family : Set C2Function}
    {I : ParameterInterval}
    {R S : CurvilinearRectangle δ t}
    (hRf : R.function ∈ family)
    (hSf : S.function ∈ family)
    (hRq : R.IsOverCentralQuarterOf I)
    (hSq : S.IsOverCentralQuarterOf I)
    (hdist : c2Distance R.function S.function ≤ δ)
    (hmid : |R.interval.midpoint - S.interval.midpoint| ≤
            (Real.sqrt lambda - 1) * Real.sqrt (δ / t)) :
    R.AreLambdaComparable S family lambda := by
  set L : ℝ := Real.sqrt (δ / t) with hL_def
  have hL_pos : 0 < L := Real.sqrt_pos.mpr (div_pos hδ ht)
  have hR_len : R.interval.length = L := R.interval_length
  have hS_len : S.interval.length = L := S.interval_length

  set target_len : ℝ := Real.sqrt (lambda * δ / t) with htarget_def
  have hlambda_pos : 0 < lambda := by linarith
  have hlam1 : 1 ≤ lambda := hadm.1
  have hlam2 : lambda * δ ≤ t := hadm.2

  have htarget_eq : target_len = Real.sqrt lambda * L := by
    simp only [htarget_def, hL_def]
    have h3 : lambda * δ / t = lambda * (δ / t) := by ring
    rw [h3, Real.sqrt_mul] <;> linarith

  have htarget_pos : 0 < target_len := by
    rw [htarget_eq]
    positivity

  have htarget_le_one : target_len ≤ 1 := by
    rw [htarget_eq]
    have h4 : lambda * (δ / t) ≤ 1 := by
      calc lambda * (δ / t) = lambda * δ / t := by ring
        _ ≤ t / t := by gcongr
        _ = 1 := by field_simp [ht.ne']
    have h5 : Real.sqrt (lambda * (δ / t)) ≤ 1 := by
      rw [Real.sqrt_le_one] <;> linarith
    have h6 : Real.sqrt (lambda * (δ / t)) = Real.sqrt lambda * L := by
      rw [Real.sqrt_mul] <;> linarith
    linarith

  -- Unfold length definitions
  have hR_len' : R.interval.right - R.interval.left = L := by
    simpa [ParameterInterval.length] using hR_len
  have hS_len' : S.interval.right - S.interval.left = L := by
    simpa [ParameterInterval.length] using hS_len

  -- Express endpoints in terms of midpoint and length
  have hR_left_eq : R.interval.left = R.interval.midpoint - L / 2 := by
    have hmid : R.interval.midpoint = (R.interval.left + R.interval.right) / 2 := rfl
    linarith
  have hR_right_eq : R.interval.right = R.interval.midpoint + L / 2 := by
    linarith [hR_left_eq, hR_len']
  have hS_left_eq : S.interval.left = S.interval.midpoint - L / 2 := by
    have hmid : S.interval.midpoint = (S.interval.left + S.interval.right) / 2 := rfl
    linarith
  have hS_right_eq : S.interval.right = S.interval.midpoint + L / 2 := by
    linarith [hS_left_eq, hS_len']

  set hull_left : ℝ := min R.interval.left S.interval.left with hhull_left_def
  set hull_right : ℝ := max R.interval.right S.interval.right with hhull_right_def
  set hull_len : ℝ := hull_right - hull_left with hhull_len_def

  have hhull_left_nonneg : 0 ≤ hull_left := by
    have h1 : 0 ≤ R.interval.left := R.interval.left_mem.1
    have h2 : 0 ≤ S.interval.left := S.interval.left_mem.1
    exact le_min h1 h2

  have hhull_right_le_one : hull_right ≤ 1 := by
    have h1 : R.interval.right ≤ 1 := R.interval.right_mem.2
    have h2 : S.interval.right ≤ 1 := S.interval.right_mem.2
    exact max_le h1 h2

  have hhull_len_le_target : hull_len ≤ target_len := by
    by_cases hcase : R.interval.midpoint ≤ S.interval.midpoint
    · -- mR ≤ mS
      have hleft : R.interval.left ≤ S.interval.left := by
        rw [hR_left_eq, hS_left_eq] <;> linarith
      have hright : R.interval.right ≤ S.interval.right := by
        rw [hR_right_eq, hS_right_eq] <;> linarith
      have hhl : hull_left = R.interval.left := by
        rw [hhull_left_def, min_eq_left hleft]
      have hhr : hull_right = S.interval.right := by
        rw [hhull_right_def, max_eq_right hright]
      rw [hhull_len_def, hhl, hhr, hS_right_eq, hR_left_eq]
      have habs : |R.interval.midpoint - S.interval.midpoint| =
            S.interval.midpoint - R.interval.midpoint := by
        rw [abs_of_nonpos] <;> linarith
      rw [htarget_eq]
      linarith [hmid, habs]
    · -- mS < mR
      have hcase' : S.interval.midpoint < R.interval.midpoint := by linarith
      have hleft : S.interval.left ≤ R.interval.left := by
        rw [hR_left_eq, hS_left_eq] <;> linarith
      have hright : S.interval.right ≤ R.interval.right := by
        rw [hR_right_eq, hS_right_eq] <;> linarith
      have hhl : hull_left = S.interval.left := by
        rw [hhull_left_def, min_eq_right hleft]
      have hhr : hull_right = R.interval.right := by
        rw [hhull_right_def, max_eq_left hright]
      rw [hhull_len_def, hhl, hhr, hR_right_eq, hS_left_eq]
      have habs : |R.interval.midpoint - S.interval.midpoint| =
            R.interval.midpoint - S.interval.midpoint := by
        rw [abs_of_nonneg] <;> linarith
      rw [htarget_eq]
      linarith [hmid, habs]

  set slack : ℝ := target_len - hull_len with hslack_def
  have hslack_nonneg : 0 ≤ slack := by
    linarith [hhull_len_le_target]

  set ext_left : ℝ := min hull_left slack with hext_left_def
  set ext_right : ℝ := slack - ext_left with hext_right_def

  have hext_left_nonneg : 0 ≤ ext_left := by positivity
  have hext_right_nonneg : 0 ≤ ext_right := by
    simp only [hext_right_def]
    exact sub_nonneg.mpr (min_le_right _ _)
  have hext_left_le : ext_left ≤ hull_left := min_le_left _ _

  have hext_right_le : ext_right ≤ 1 - hull_right := by
    simp only [hext_right_def, hext_left_def]
    by_cases h : slack ≤ hull_left
    · -- slack ≤ hull_left, so min = slack
      have hmin : min hull_left slack = slack := by
        apply min_eq_right
        exact h
      rw [hmin]
      have h' : slack - slack = 0 := by ring
      rw [h']
      linarith [hhull_right_le_one]
    · -- hull_left < slack, so min = hull_left
      have h' : hull_left < slack := by linarith
      have hmin : min hull_left slack = hull_left := by
        apply min_eq_left
        linarith
      rw [hmin]
      have h9 : slack - hull_left ≤ 1 - hull_right := by
        have h10 : target_len ≤ 1 := htarget_le_one
        simp only [hslack_def, hhull_len_def] at *
        <;> linarith
      exact h9

  set J_left : ℝ := hull_left - ext_left with hJ_left_def
  set J_right : ℝ := hull_right + ext_right with hJ_right_def

  have hJ_left_nonneg : 0 ≤ J_left := by
    linarith [hext_left_le]
  have hJ_right_le_one : J_right ≤ 1 := by
    linarith [hext_right_le]
  have hJ_left_le_right : J_left ≤ J_right := by
    have h : J_right - J_left = target_len := by
      simp only [hJ_left_def, hJ_right_def, hext_right_def, hslack_def] <;> linarith
    have h' : 0 < target_len := htarget_pos
    linarith

  let J : ParameterInterval :=
    { left := J_left
      right := J_right
      left_mem := ⟨hJ_left_nonneg, by linarith⟩
      right_mem := ⟨by linarith, hJ_right_le_one⟩
      left_le_right := hJ_left_le_right }

  have hJ_len : J.length = target_len := by
    have h : J.right - J.left = target_len := by
      simp only [J, hJ_left_def, hJ_right_def, hext_right_def, hslack_def] <;> linarith
    exact h

  have hJ_contains_R : R.interval.carrier ⊆ J.carrier := by
    intro x hx
    have h1 : R.interval.left ≤ (x : ℝ) := hx.1
    have h2 : (x : ℝ) ≤ R.interval.right := hx.2
    have h3 : J.left ≤ R.interval.left := by
      have h4 : J.left = hull_left - ext_left := by rfl
      rw [h4]
      have h5 : hull_left ≤ R.interval.left := min_le_left _ _
      linarith [hext_left_nonneg]
    have h5 : R.interval.right ≤ J.right := by
      have h6 : J.right = hull_right + ext_right := by rfl
      rw [h6]
      have h7 : R.interval.right ≤ hull_right := le_max_left _ _
      linarith [hext_right_nonneg]
    exact ⟨by linarith, by linarith⟩

  have hJ_contains_S : S.interval.carrier ⊆ J.carrier := by
    intro x hx
    have h1 : S.interval.left ≤ (x : ℝ) := hx.1
    have h2 : (x : ℝ) ≤ S.interval.right := hx.2
    have h3 : J.left ≤ S.interval.left := by
      have h4 : J.left = hull_left - ext_left := by rfl
      rw [h4]
      have h5 : hull_left ≤ S.interval.left := min_le_right _ _
      linarith [hext_left_nonneg]
    have h5 : S.interval.right ≤ J.right := by
      have h6 : J.right = hull_right + ext_right := by rfl
      rw [h6]
      have h7 : S.interval.right ≤ hull_right := le_max_right _ _
      linarith [hext_right_nonneg]
    exact ⟨by linarith, by linarith⟩

  let U : CurvilinearRectangle (lambda * δ) t :=
    { function := R.function
      interval := J
      interval_length := by
        have h : J.length = Real.sqrt ((lambda * δ) / t) := by
          calc J.length = target_len := hJ_len
            _ = Real.sqrt (lambda * δ / t) := by rw [htarget_def]
            _ = Real.sqrt ((lambda * δ) / t) := by rfl
        exact h }

  have hU_family : U.function ∈ family := hRf

  have hR_sub : R.carrier ⊆ U.carrier := by
    intro p hp
    have h1 : p.1 ∈ R.interval.carrier := hp.1
    have h2 : |p.2 - R.function p.1| ≤ δ := hp.2
    have h3 : p.1 ∈ J.carrier := hJ_contains_R h1
    have h4 : |p.2 - R.function p.1| ≤ lambda * δ := by
      calc |p.2 - R.function p.1| ≤ δ := h2
        _ ≤ lambda * δ := by
          have h5 : 1 ≤ lambda := hlam1
          have h6 : 0 ≤ δ := by linarith
          nlinarith
    exact ⟨h3, h4⟩

  have hS_sub : S.carrier ⊆ U.carrier := by
    intro p hp
    have h1 : p.1 ∈ S.interval.carrier := hp.1
    have h2 : |p.2 - S.function p.1| ≤ δ := hp.2
    have h3 : p.1 ∈ J.carrier := hJ_contains_S h1
    have h4 : |S.function p.1 - R.function p.1| ≤ c2Distance S.function R.function :=
      abs_value_sub_le_c2Distance S.function R.function p.1
    have h5 : c2Distance S.function R.function ≤ δ := by
      have h6 : c2Distance S.function R.function = c2Distance R.function S.function := by
        exact dist_comm _ _
      rw [h6]
      exact hdist
    have h_triangle : |p.2 - R.function p.1| ≤
        |p.2 - S.function p.1| + |S.function p.1 - R.function p.1| := by
      have h_eq : p.2 - R.function p.1 =
          (p.2 - S.function p.1) + (S.function p.1 - R.function p.1) := by ring
      rw [h_eq]
      have h21 : -(|p.2 - S.function p.1| + |S.function p.1 - R.function p.1|) ≤
          (p.2 - S.function p.1) + (S.function p.1 - R.function p.1) := by
        have h21a : -|p.2 - S.function p.1| ≤ p.2 - S.function p.1 := neg_abs_le _
        have h21b : -|S.function p.1 - R.function p.1| ≤ S.function p.1 - R.function p.1 := neg_abs_le _
        linarith
      have h22 : (p.2 - S.function p.1) + (S.function p.1 - R.function p.1) ≤
          |p.2 - S.function p.1| + |S.function p.1 - R.function p.1| := by
        have h22a : p.2 - S.function p.1 ≤ |p.2 - S.function p.1| := le_abs_self _
        have h22b : S.function p.1 - R.function p.1 ≤ |S.function p.1 - R.function p.1| := le_abs_self _
        linarith
      exact abs_le.mpr ⟨h21, h22⟩
    have h7 : |p.2 - R.function p.1| ≤ lambda * δ := by
      calc |p.2 - R.function p.1|
        ≤ |p.2 - S.function p.1| + |S.function p.1 - R.function p.1| := h_triangle
      _ ≤ δ + c2Distance S.function R.function := by gcongr
      _ ≤ δ + δ := by gcongr
      _ = 2 * δ := by ring
      _ ≤ lambda * δ := by
        have h8 : 2 ≤ lambda := by linarith
        have h9 : 0 ≤ δ := by linarith
        nlinarith
    exact ⟨h3, h7⟩

  have h_main : R.carrier ∪ S.carrier ⊆ U.carrier := by
    intro p hp
    cases hp with
    | inl hR => exact hR_sub hR
    | inr hS => exact hS_sub hS

  exact ⟨U, hU_family, h_main⟩

end Kakeya.Cinematic
