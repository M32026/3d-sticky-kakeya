module

/-
  Thickening Absorption Bounds and Good Scale Property

  Standalone lemmas extracted from ThickeningTransfer.lean to reduce
  the context size of `multiscaleToCombining_thickened`.

  - `thickening_absorption_bounds`: proves C_between constant absorption
    inequalities for normal and good scale classes.
  - `thickening_good_property`: proves t ≤ t_j' for good scales.

  Whiteprint node: section9 / thickening_transfer
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem

/-- Absorption bounds for C_between constants, extracted to reduce context size. -/
lemma thickening_absorption_bounds
    {n : ℕ} (j : Fin n)
    (S : Finset (Fin n)) (t_j : ℕ → ℝ)
    (t ε_G ε_N C_P ε_bad Δ : ℝ)
    (k : ℕ)
    (C_uniform_j ratio_j rhs_val : ℝ)
    (C_between_j : ℝ)
    (scaleClass_j : ScaleClass)
    (h_ratio : ratio_j = rhs_val)
    (h_scale_bad : j ∉ S → scaleClass_j = ScaleClass.bad)
    (h_scale_normal : j ∈ S → t_j j.val < t - ε_G / 2 → scaleClass_j = ScaleClass.normal)
    (h_scale_good_high : j ∈ S → t_j j.val ≥ t → scaleClass_j = ScaleClass.good (t_j j.val))
    (h_scale_good_low : j ∈ S → t - ε_G / 2 ≤ t_j j.val → t_j j.val < t → scaleClass_j = ScaleClass.good t)
    (h_C_uniform : ¬(j ∈ S ∧ t_j j.val ≥ t - ε_G / 2 ∧ t_j j.val < t) → C_between_j = C_uniform_j)
    (h_C_boosted : (j ∈ S ∧ t_j j.val ≥ t - ε_G / 2 ∧ t_j j.val < t) →
        C_between_j = C_uniform_j * ratio_j ^ (ε_G / 2))
    (h_C_uniform_eq : C_uniform_j = (72900 : ℝ) * Real.rpow Δ (-4) * ratio_j ^ ε_bad)
    (h_absorb_normal : j ∈ S → t_j j.val < t - ε_G / 2 →
        (72900 : ℝ) * Real.rpow Δ (-4) * ratio_j ^ ε_bad ≤
        Real.log (1 / dyadicDelta k) ^ C_P * ratio_j ^ ε_N)
    (h_absorb_good_high : j ∈ S → t_j j.val ≥ t →
        (72900 : ℝ) * Real.rpow Δ (-4) * ratio_j ^ ε_bad ≤
        Real.log (1 / dyadicDelta k) ^ C_P * ratio_j ^ ε_G)
    (h_absorb_good_low : j ∈ S → t - ε_G / 2 ≤ t_j j.val → t_j j.val < t →
        ((72900 : ℝ) * Real.rpow Δ (-4) * ratio_j ^ ε_bad) * ratio_j ^ (ε_G / 2) ≤
        Real.log (1 / dyadicDelta k) ^ C_P * ratio_j ^ ε_G)
    :
    (scaleClass_j = ScaleClass.normal →
        C_between_j ≤ Real.log (1 / dyadicDelta k) ^ C_P * rhs_val ^ ε_N) ∧
    (∀ (t_j' : ℝ), scaleClass_j = ScaleClass.good t_j' →
        C_between_j ≤ Real.log (1 / dyadicDelta k) ^ C_P * rhs_val ^ ε_G) := by
  have h_normal : scaleClass_j = ScaleClass.normal →
      C_between_j ≤ Real.log (1 / dyadicDelta k) ^ C_P * rhs_val ^ ε_N := by
    intro hj
    have h_j_in_S : j ∈ S := by
      by_cases h : j ∈ S
      · exact h
      · have h_bad := h_scale_bad h
        rw [h_bad] at hj; contradiction
    have h_tj_low : t_j j.val < t - ε_G / 2 := by
      by_cases h : t_j j.val ≥ t - ε_G / 2
      · by_cases h2 : t_j j.val ≥ t
        · have h_sc2 := h_scale_good_high h_j_in_S h2
          rw [h_sc2] at hj; contradiction
        · have h_sc2 := h_scale_good_low h_j_in_S h (by linarith)
          rw [h_sc2] at hj; contradiction
      · linarith
    have h_condition : ¬(j ∈ S ∧ t_j j.val ≥ t - ε_G / 2 ∧ t_j j.val < t) := by
      intro h_cont; linarith [h_tj_low]
    have h_C_eq : C_between_j = C_uniform_j := h_C_uniform h_condition
    rw [h_C_eq]
    have h_abs := h_absorb_normal h_j_in_S h_tj_low
    rw [h_C_uniform_eq] at *
    <;> rw [h_ratio] at * <;> exact h_abs
  have h_good : ∀ (t_j' : ℝ), scaleClass_j = ScaleClass.good t_j' →
      C_between_j ≤ Real.log (1 / dyadicDelta k) ^ C_P * rhs_val ^ ε_G := by
    intro t_j' hsc
    by_cases h_high : t_j j.val ≥ t
    · have h_j_in_S : j ∈ S := by
        by_cases h : j ∈ S
        · exact h
        · have h_bad := h_scale_bad h
          rw [h_bad] at hsc; contradiction
      have h_condition : ¬(j ∈ S ∧ t_j j.val ≥ t - ε_G / 2 ∧ t_j j.val < t) := by
        intro h_cont; linarith [h_high]
      have h_C_eq : C_between_j = C_uniform_j := h_C_uniform h_condition
      rw [h_C_eq]
      have h_abs := h_absorb_good_high h_j_in_S h_high
      rw [h_C_uniform_eq] at *
      <;> rw [h_ratio] at * <;> exact h_abs
    · have h_j_in_S : j ∈ S := by
        by_cases h : j ∈ S
        · exact h
        · have h_bad := h_scale_bad h
          rw [h_bad] at hsc; contradiction
      have h_low : t_j j.val ≥ t - ε_G / 2 := by
        by_cases h2 : t_j j.val ≥ t - ε_G / 2
        · exact h2
        · have h_normal := h_scale_normal h_j_in_S (by linarith)
          rw [h_normal] at hsc; contradiction
      have h_high2 : t_j j.val < t := by linarith
      have h_condition : j ∈ S ∧ t_j j.val ≥ t - ε_G / 2 ∧ t_j j.val < t :=
        ⟨h_j_in_S, h_low, h_high2⟩
      have h_C_eq : C_between_j = C_uniform_j * ratio_j ^ (ε_G / 2) := h_C_boosted h_condition
      rw [h_C_eq]
      have h_abs := h_absorb_good_low h_j_in_S h_low h_high2
      have h_C_boosted_eq : C_uniform_j * ratio_j ^ (ε_G / 2) =
          ((72900 : ℝ) * Real.rpow Δ (-4) * ratio_j ^ ε_bad) * ratio_j ^ (ε_G / 2) := by
        rw [h_C_uniform_eq] <;> ring
      rw [h_C_boosted_eq]
      rw [h_ratio] at * <;> exact h_abs
  exact ⟨h_normal, h_good⟩

/-- Good scale property: if scaleClass j = good t_j', then t ≤ t_j'. -/
lemma thickening_good_property
    {n : ℕ} (j : Fin n)
    (S : Finset (Fin n)) (t_j : ℕ → ℝ)
    (t ε_G : ℝ)
    (scaleClass_j : ScaleClass)
    (t_j' : ℝ)
    (hsc : scaleClass_j = ScaleClass.good t_j')
    (h_scale_bad : j ∉ S → scaleClass_j = ScaleClass.bad)
    (h_scale_normal : j ∈ S → t_j j.val < t - ε_G / 2 → scaleClass_j = ScaleClass.normal)
    (h_scale_good_high : j ∈ S → t_j j.val ≥ t → scaleClass_j = ScaleClass.good (t_j j.val))
    (h_scale_good_low : j ∈ S → t - ε_G / 2 ≤ t_j j.val → t_j j.val < t → scaleClass_j = ScaleClass.good t)
    : t ≤ t_j' := by
  by_cases h_high : t_j j.val ≥ t
  · have h_j_in_S : j ∈ S := by
      by_cases h : j ∈ S
      · exact h
      · have h_bad := h_scale_bad h
        rw [h_bad] at hsc; cases hsc
    have h_eq : t_j' = t_j j.val := by
      have h_sc2 := h_scale_good_high h_j_in_S h_high
      rw [h_sc2] at hsc
      injection hsc with h_inj
      exact h_inj.symm
    exact h_high.trans (le_of_eq h_eq.symm)
  · have h_j_in_S : j ∈ S := by
      by_cases h : j ∈ S
      · exact h
      · have h_bad := h_scale_bad h
        rw [h_bad] at hsc; cases hsc
    have h_low : t_j j.val ≥ t - ε_G / 2 := by
      by_cases h2 : t_j j.val ≥ t - ε_G / 2
      · exact h2
      · have h_normal := h_scale_normal h_j_in_S (by linarith)
        rw [h_normal] at hsc; cases hsc
    have h_eq : t_j' = t := by
      have h_sc2 := h_scale_good_low h_j_in_S h_low (by linarith)
      rw [h_sc2] at hsc
      injection hsc with h_inj
      exact h_inj.symm
    exact le_of_eq h_eq.symm

end DirecretisedFurstenbergEstimate.Section9
