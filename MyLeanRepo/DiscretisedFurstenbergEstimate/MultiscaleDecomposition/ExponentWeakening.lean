module

/-
  Exponent weakening for IsDeltaSSet.

  Generalizes `IsDeltaSSet.cap_exponent1d` to any pseudo-metric space.
  If `A` is a `(δ, s, C)`-set with `C ≥ 1` and `s' ≤ s`, then `A` is also a
  `(δ, s', C)`-set. For `r ≤ 1`, `r^s ≤ r^{s'}`; for `r > 1`, use `C * r^{s'} ≥ 1`.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open DirecretisedFurstenbergEstimate

namespace IsDeltaSSet

/-- Exponent weakening: if `A` is a `(δ, s, C)`-set with `C ≥ 1` and `s' ≤ s`,
    then `A` is also a `(δ, s', C)`-set. Works in any pseudo-metric space. -/
lemma cap_exponent {X : Type*} [PseudoMetricSpace X] {δ s s' C : ℝ} {A : Set X}
    (h : IsDeltaSSet δ s C A) (hs' : 0 ≤ s') (h_le : s' ≤ s)
    (hC_one : 1 ≤ C) :
    IsDeltaSSet δ s' C A := by
  have hA_nonempty : A.Nonempty := h.1
  have hδ_pos : 0 < δ := h.2.1
  have hC_pos : 0 < C := h.2.2.1
  have hs_nonneg : 0 ≤ s := h.2.2.2.1
  refine ⟨hA_nonempty, hδ_pos, hC_pos, hs', ?_⟩
  intro x r hr
  by_cases h_r_le_one : r ≤ 1
  · -- Case r ≤ 1: use original bound and r^s ≤ r^s'
    have h_r_pos : 0 < r := by linarith
    have h_rpow_real : r ^ s ≤ r ^ s' :=
      Real.rpow_le_rpow_of_exponent_ge h_r_pos h_r_le_one h_le
    have h_rpow_enn : (ENNReal.ofReal r) ^ s ≤ (ENNReal.ofReal r) ^ s' := by
      rw [ENNReal.ofReal_rpow_of_pos h_r_pos, ENNReal.ofReal_rpow_of_pos h_r_pos]
      exact ENNReal.ofReal_le_ofReal h_rpow_real
    have h_orig := h.2.2.2.2 x r hr
    have h_mul : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s' * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by
      gcongr
    exact h_orig.trans h_mul
  · -- Case r > 1: A ∩ B(x,r) ⊆ A, and C * r^s' ≥ 1
    have h_r_gt_one : 1 < r := by linarith
    have h_sub : A ∩ Metric.closedBall x r ⊆ A := by simp
    have h1 : (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) ≤
        (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by
      have h1' : Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r) ≤
          Metric.externalCoveringNumber δ.toNNReal A :=
        Metric.externalCoveringNumber_mono_set h_sub
      exact_mod_cast h1'
    have hC1 : (1 : ENNReal) ≤ ENNReal.ofReal C := by
      have h : (1 : ℝ) ≤ C := hC_one
      have h' : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
      rw [h']
      exact ENNReal.ofReal_le_ofReal h
    have hr1 : (1 : ENNReal) ≤ (ENNReal.ofReal r) ^ s' := by
      have h3 : (1 : ENNReal) ≤ ENNReal.ofReal r := by
        have h4 : (1 : ℝ) ≤ r := by linarith
        have h5 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
        rw [h5]
        exact ENNReal.ofReal_le_ofReal h4
      have h4 : (ENNReal.ofReal r) ^ (0 : ℝ) ≤ (ENNReal.ofReal r) ^ s' :=
        ENNReal.rpow_le_rpow_of_exponent_le h3 hs'
      simpa using h4
    have h2 : (1 : ENNReal) ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s' := by
      calc (1 : ENNReal)
        = (1 : ENNReal) * (1 : ENNReal) := by simp
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s' := mul_le_mul' hC1 hr1
    have h3 : (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s' *
          (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by
      have h4 : (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) =
          (1 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by simp
      rw [h4]
      have h5 : (1 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≤
          (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s') * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      simpa [mul_assoc] using h5
    exact h1.trans h3

end IsDeltaSSet
