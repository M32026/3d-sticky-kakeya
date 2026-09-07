import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Slope variation lemma

The grain direction `globalGrainDirection (f z)` varies Lipschitz-continuously
in `z` with constant at most 1, by the normalized slope condition `|f'| ≤ 1`.

Whiteprint node: `main.slope_variation`.
-/

noncomputable section

open Metric Set

namespace Kakeya.Assouad

/--
The grain direction `globalGrainDirection (f z)` is 1-Lipschitz in `z` on `[-1,1]`.
-/
lemma slope_variation_lipschitz
    {f : SlopeFunction} (h_norm : f.IsNormalized) :
    LipschitzOnWith (1 : NNReal)
      (fun z : ℝ => globalGrainDirection (f z)) (Set.Icc (-1 : ℝ) 1) := by
  have h_diff : Differentiable ℝ f := f.contDiff.differentiable (by norm_num)
  have h1 : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |deriv f z| ≤ 1 := by
    intro z hz
    exact (h_norm z hz).2.1
  have h_deriv_norm : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ‖deriv f z‖ ≤ (1 : ℝ) := by
    intro z hz
    have h : ‖deriv f z‖ = |deriv f z| := by
      simp [Real.norm_eq_abs]
    rw [h]
    exact h1 z hz
  have h2 : ∀ (z1 z2 : ℝ), z1 ∈ Set.Icc (-1 : ℝ) 1 → z2 ∈ Set.Icc (-1 : ℝ) 1 →
      |f z1 - f z2| ≤ |z1 - z2| := by
    intro z1 z2 hz1 hz2
    have h_main : ‖f z2 - f z1‖ ≤ (1 : ℝ) * ‖z2 - z1‖ :=
      Convex.norm_image_sub_le_of_norm_deriv_le
        (fun x _ => h_diff.differentiableAt)
        h_deriv_norm (convex_Icc _ _) hz1 hz2
    have h_abs1 : |f z1 - f z2| = |f z2 - f z1| := by
      rw [show f z1 - f z2 = -(f z2 - f z1) by ring, abs_neg]
    have h_abs2 : |z1 - z2| = |z2 - z1| := by
      rw [show z1 - z2 = -(z2 - z1) by ring, abs_neg]
    rw [h_abs1, h_abs2]
    simpa [Real.norm_eq_abs] using h_main
  intro z1 hz1 z2 hz2
  have h_dist : dist (globalGrainDirection (f z1)) (globalGrainDirection (f z2)) ≤
      (1 : ℝ) * dist z1 z2 := by
    have h3 : dist (globalGrainDirection (f z1)) (globalGrainDirection (f z2)) =
        |f z1 - f z2| := by
      have h4 : ‖globalGrainDirection (f z1) - globalGrainDirection (f z2)‖ = |f z1 - f z2| := by
        have h5 : globalGrainDirection (f z1) - globalGrainDirection (f z2) =
            (f z1 - f z2) • EuclideanSpace.single (1 : Fin 3) 1 := by
          ext i
          fin_cases i <;> simp [globalGrainDirection] <;> ring
        rw [h5]
        simp [norm_smul, Real.norm_eq_abs]
        <;> rw [Real.sqrt_sq (show 0 ≤ (f z1 - f z2) ^ 2 by positivity)]
        <;> rfl
      simpa [dist_eq_norm] using h4
    rw [h3]
    have h4 : |f z1 - f z2| ≤ |z1 - z2| := h2 z1 z2 hz1 hz2
    have h5 : dist z1 z2 = |z1 - z2| := by simp [Real.dist_eq] <;> rfl
    rw [h5]
    simpa using h4
  have h_edist : edist (globalGrainDirection (f z1)) (globalGrainDirection (f z2)) ≤
      (1 : NNReal) * edist z1 z2 := by
    have h6 : edist (globalGrainDirection (f z1)) (globalGrainDirection (f z2)) =
        ENNReal.ofReal (dist (globalGrainDirection (f z1)) (globalGrainDirection (f z2))) := by
      exact edist_dist (globalGrainDirection (f z1)) (globalGrainDirection (f z2))
    have h7 : edist z1 z2 = ENNReal.ofReal (dist z1 z2) := by
      exact edist_dist z1 z2
    rw [h6, h7]
    have h8 : dist (globalGrainDirection (f z1)) (globalGrainDirection (f z2)) ≤ (1 : ℝ) * dist z1 z2 := h_dist
    have h9 : ENNReal.ofReal (dist (globalGrainDirection (f z1)) (globalGrainDirection (f z2))) ≤
        ENNReal.ofReal ((1 : ℝ) * dist z1 z2) := ENNReal.ofReal_le_ofReal h8
    have h10 : ENNReal.ofReal ((1 : ℝ) * dist z1 z2) =
        (1 : NNReal) * ENNReal.ofReal (dist z1 z2) := by
      simp [NNReal.coe_one]
      <;> ring
    rw [h10] at h9
    exact h9
  exact h_edist

end Kakeya.Assouad
