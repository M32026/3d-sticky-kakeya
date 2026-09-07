import MyLeanRepo.Kakeya.CV.VisibilityDegreeBound.Helpers
import MyLeanRepo.Kakeya.CV.PolynomialMollification
import MyLeanRepo.Kakeya.CV.Mollification
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar


/-!
# Homogeneity and evenness of concrete mollified directional area
-/

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace Kakeya.CV

/-- Homogeneity of `concreteMollifiedDirectionalArea` for nonnegative scalars. -/
lemma concreteMollifiedDirectionalArea_hom
    {k : ℕ} {P : PolynomialParameterization k} {U : Set (Point 3)}
    {ε : ℝ} {x : CoefficientSpace P.dim} {c : Point 3}
    {hU_meas : MeasurableSet U}
    {hU : U ⊆ Metric.closedBall c 1} {hε : 0 < ε}
    (hSurface : ConcreteMollifiedSurfaceStatement)
    (c' : ℝ) (u : Point 3) (hc : 0 ≤ c') :
    concreteMollifiedDirectionalArea P ε x (c' • u) U =
      c' * concreteMollifiedDirectionalArea P ε x u U := by
  let ball : Set (CoefficientSpace P.dim) := Metric.ball x ε
  let mass : CoefficientSpace P.dim → Point 3 → ℝ≥0∞ := fun y w =>
    directionalSurfaceArea w (parameterPolynomial P y)
      (polynomialZeroSet (parameterPolynomial P y) ∩ U)
  have h_surface_data := hSurface k P U c ε hU_meas hU hε
  have h1 : ∀ y, coefficientSurfaceFunctional P (c' • u) U y = c' * coefficientSurfaceFunctional P u U y := by
    intro y
    have h2 : mass y (c' • u) = ENNReal.ofReal c' * mass y u :=
      directionalSurfaceArea_homogeneity c' hc u (parameterPolynomial P y) _
    have h3 : (mass y (c' • u)).toReal = (ENNReal.ofReal c' * mass y u).toReal := by rw [h2]
    have h4 : (ENNReal.ofReal c' * mass y u).toReal = c' * (mass y u).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] <;> ring
    have h5 : (mass y (c' • u)).toReal = c' * (mass y u).toReal := by rw [h3, h4]
    simpa [coefficientSurfaceFunctional] using h5
  have h_int_u : IntegrableOn (coefficientSurfaceFunctional P u U) ball volume := by
    have h_loc_int : LocallyIntegrable (coefficientSurfaceFunctional P u U) volume := h_surface_data.1 u
    have h_compact : IsCompact (Metric.closedBall x ε) := by
      exact isCompact_closedBall x ε
    exact (h_loc_int.integrableOn_isCompact h_compact).mono_set Metric.ball_subset_closedBall
  have h5 : ∫ y in ball, coefficientSurfaceFunctional P (c' • u) U y =
      c' * ∫ y in ball, coefficientSurfaceFunctional P u U y := by
    have h51 : ∫ y in ball, coefficientSurfaceFunctional P (c' • u) U y =
        ∫ y in ball, c' * coefficientSurfaceFunctional P u U y := by
      congr with y; exact h1 y
    rw [h51]
    exact integral_const_mul c' (coefficientSurfaceFunctional P u U)
  simp only [concreteMollifiedDirectionalArea, ballAverage]
  rw [h5] <;> ring

/-- Evenness of `concreteMollifiedDirectionalArea`. -/
lemma concreteMollifiedDirectionalArea_even
    {k : ℕ} {P : PolynomialParameterization k} {U : Set (Point 3)}
    {ε : ℝ} {x : CoefficientSpace P.dim} {c : Point 3}
    {hU : U ⊆ Metric.closedBall c 1} {hε : 0 < ε}
    (u : Point 3) :
    concreteMollifiedDirectionalArea P ε x (-u) U =
    concreteMollifiedDirectionalArea P ε x u U := by
  let mass : CoefficientSpace P.dim → Point 3 → ℝ≥0∞ := fun y w =>
    directionalSurfaceArea w (parameterPolynomial P y)
      (polynomialZeroSet (parameterPolynomial P y) ∩ U)
  have h1 : ∀ y, coefficientSurfaceFunctional P (-u) U y = coefficientSurfaceFunctional P u U y := by
    intro y
    have h2 : mass y (-u) = mass y u :=
      directionalSurfaceArea_evenness u (parameterPolynomial P y) _
    have h3 : (mass y (-u)).toReal = (mass y u).toReal := by rw [h2]
    simpa [coefficientSurfaceFunctional] using h3
  have h4 : (coefficientSurfaceFunctional P (-u) U) = coefficientSurfaceFunctional P u U := funext h1
  simp only [concreteMollifiedDirectionalArea, ballAverage]
  rw [h4]

end Kakeya.CV
