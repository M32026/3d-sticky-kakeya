import MyLeanRepo.Kakeya.Cinematic.Statements
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Critical image measure zero

For a C² function `f : ℝ → ℝ`, the image of the critical set on a compact
interval has Lebesgue measure zero.
-/

namespace Kakeya.Cinematic

/-- The image of the critical set of a C² function on a compact interval has measure zero. -/
lemma critical_image_measure_zero {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (a b : ℝ) (_hab : a ≤ b) :
    MeasureTheory.volume (f '' {x ∈ Set.Icc a b | deriv f x = 0}) = 0 := by
  let s : Set ℝ := {x ∈ Set.Icc a b | deriv f x = 0}
  have h1 : ∀ x ∈ s, HasFDerivWithinAt f (fderiv ℝ f x) s x := by
    intro x hx
    have h_diff : DifferentiableAt ℝ f x :=
      hf.differentiable (by norm_num) x
    exact h_diff.hasFDerivAt.hasFDerivWithinAt
  have h2 : ∀ x ∈ s, (fderiv ℝ f x).det = 0 := by
    intro x hx
    have hderiv : deriv f x = 0 := hx.2
    have h3 : (fderiv ℝ f x).det = deriv f x := by
      have h4 : fderiv ℝ f x = ContinuousLinearMap.toSpanSingleton ℝ (deriv f x) := by
        ext
        simp [ContinuousLinearMap.toSpanSingleton_apply]
      rw [h4]
      simp
    rw [h3, hderiv]
  exact MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (MeasureTheory.volume : MeasureTheory.Measure ℝ) h1 h2

end Kakeya.Cinematic
