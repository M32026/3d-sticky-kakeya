import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.VisibilityDegreeBound.Helpers

/-!
# Homogeneity of mollified directional area

This file proves positive homogeneity of the concrete mollified directional area
as a function of the direction `u`. Convexity follows via the Minkowski functional
of the visibility body.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Kakeya.CV

/-- Positive homogeneity of `coefficientSurfaceFunctional` in the direction. -/
lemma coefficientSurfaceFunctional_homogeneous
    {k : ℕ} (P : PolynomialParameterization k)
    (c : ℝ) (u : Point 3) (U : Set (Point 3)) (x : CoefficientSpace P.dim)
    (hc : 0 ≤ c) :
    coefficientSurfaceFunctional P (c • u) U x =
      c * coefficientSurfaceFunctional P u U x := by
  simp only [coefficientSurfaceFunctional]
  set p := parameterPolynomial P x with hp
  set s := polynomialZeroSet p ∩ U with hs
  have h := directionalSurfaceArea_homogeneity c hc u p s
  rw [h]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]

/-- Positive homogeneity of `concreteMollifiedDirectionalArea` in the direction. -/
lemma concreteMollifiedDirectionalArea_homogeneous
    {k : ℕ} (P : PolynomialParameterization k)
    (ε : ℝ) (x : CoefficientSpace P.dim) (c : ℝ) (u : Point 3) (U : Set (Point 3))
    (hc : 0 ≤ c) :
    concreteMollifiedDirectionalArea P ε x (c • u) U =
      c * concreteMollifiedDirectionalArea P ε x u U := by
  simp only [concreteMollifiedDirectionalArea, ballAverage]
  have h1 : ∀ (y : CoefficientSpace P.dim),
      coefficientSurfaceFunctional P (c • u) U y =
        c * coefficientSurfaceFunctional P u U y := by
    intro y
    exact coefficientSurfaceFunctional_homogeneous P c u U y hc
  have h2 : (fun y : CoefficientSpace P.dim => coefficientSurfaceFunctional P (c • u) U y) =
      fun y : CoefficientSpace P.dim => c * coefficientSurfaceFunctional P u U y := by
    funext y
    exact h1 y
  rw [h2]
  have h3 : ∫ y in Metric.ball x ε, c * coefficientSurfaceFunctional P u U y =
      c * ∫ y in Metric.ball x ε, coefficientSurfaceFunctional P u U y := by
    rw [MeasureTheory.integral_const_mul]
  rw [h3]
  ring

/-- Non-negativity of concrete mollified directional area. -/
lemma concreteMollifiedDirectionalArea_nonneg
    {k : ℕ} (P : PolynomialParameterization k)
    (ε : ℝ) (x : CoefficientSpace P.dim) (u : Point 3)
    (U : Set (Point 3)) :
    0 ≤ concreteMollifiedDirectionalArea P ε x u U := by
  simp only [concreteMollifiedDirectionalArea, ballAverage]
  have h1 : 0 ≤ ∫ y in Metric.ball x ε,
      coefficientSurfaceFunctional P u U y := by
    apply integral_nonneg
    intro y
    simp only [coefficientSurfaceFunctional]
    exact ENNReal.toReal_nonneg
  have h2 : 0 ≤ (volume (Metric.ball (0 : CoefficientSpace P.dim) ε)).toReal⁻¹ := by
    apply inv_nonneg.mpr
    exact ENNReal.toReal_nonneg
  exact mul_nonneg h2 h1

end Kakeya.CV
