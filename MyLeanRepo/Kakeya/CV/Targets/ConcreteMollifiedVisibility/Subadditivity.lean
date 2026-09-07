import MyLeanRepo.Kakeya.CV.VisibilityDegreeBound.Helpers
import MyLeanRepo.Kakeya.CV.PolynomialMollification
import MyLeanRepo.Kakeya.CV.Mollification
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Analytic properties of concrete mollified directional area

Standalone lemmas for subadditivity of `concreteMollifiedDirectionalArea`,
extracted to reduce elaboration pressure.
-/

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace Kakeya.CV

/-- Subadditivity of `concreteMollifiedDirectionalArea` in the direction argument.

Takes `h_finite` as an explicit hypothesis to avoid expensive searches during elaboration. -/
lemma concreteMollifiedDirectionalArea_subadd
    {k : ℕ} {P : PolynomialParameterization k} {U : Set (Point 3)}
    {ε : ℝ} {x : CoefficientSpace P.dim} {c : Point 3}
    {hU_meas : MeasurableSet U}
    {hU : U ⊆ Metric.closedBall c 1} {hε : 0 < ε}
    (hSurface : ConcreteMollifiedSurfaceStatement)
    (h_finite : ∀ (y : CoefficientSpace P.dim) (w : Point 3),
      directionalSurfaceArea w (parameterPolynomial P y)
        (polynomialZeroSet (parameterPolynomial P y) ∩ U) ≠ ⊤)
    (u v : Point 3) :
    concreteMollifiedDirectionalArea P ε x (u + v) U ≤
      concreteMollifiedDirectionalArea P ε x u U +
      concreteMollifiedDirectionalArea P ε x v U := by
  let ball : Set (CoefficientSpace P.dim) := Metric.ball x ε
  let mass : CoefficientSpace P.dim → Point 3 → ℝ≥0∞ := fun y w =>
    directionalSurfaceArea w (parameterPolynomial P y)
      (polynomialZeroSet (parameterPolynomial P y) ∩ U)
  let f_uv := coefficientSurfaceFunctional P (u + v) U
  let f_u := coefficientSurfaceFunctional P u U
  let f_v := coefficientSurfaceFunctional P v U
  have h_surface_data := hSurface k P U c ε hU_meas hU hε

  have h1 : ∀ y, f_uv y ≤ f_u y + f_v y := by
    intro y
    have h2 : mass y (u + v) ≤ mass y u + mass y v :=
      directionalSurfaceArea_subadditivity u v (parameterPolynomial P y) _
    have hfin_u : mass y u ≠ ⊤ := h_finite y u
    have hfin_v : mass y v ≠ ⊤ := h_finite y v
    have hfin_sum : mass y u + mass y v ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hfin_u, hfin_v⟩
    have h3 : (mass y (u + v)).toReal ≤ (mass y u + mass y v).toReal :=
      ENNReal.toReal_mono hfin_sum h2
    have h4 : (mass y u + mass y v).toReal = (mass y u).toReal + (mass y v).toReal :=
      ENNReal.toReal_add hfin_u hfin_v
    rw [h4] at h3
    simpa [coefficientSurfaceFunctional, f_uv, f_u, f_v] using h3

  have h_loc_int_uv : LocallyIntegrable f_uv volume := h_surface_data.1 (u + v)
  have h_loc_int_u : LocallyIntegrable f_u volume := h_surface_data.1 u
  have h_loc_int_v : LocallyIntegrable f_v volume := h_surface_data.1 v
  have h_compact : IsCompact (Metric.closedBall x ε) := isCompact_closedBall x ε
  have h_int_uv : IntegrableOn f_uv ball volume :=
    (h_loc_int_uv.integrableOn_isCompact h_compact).mono_set Metric.ball_subset_closedBall
  have h_int_u : IntegrableOn f_u ball volume :=
    (h_loc_int_u.integrableOn_isCompact h_compact).mono_set Metric.ball_subset_closedBall
  have h_int_v : IntegrableOn f_v ball volume :=
    (h_loc_int_v.integrableOn_isCompact h_compact).mono_set Metric.ball_subset_closedBall
  have h_int_sum : IntegrableOn (fun y => f_u y + f_v y) ball volume :=
    h_int_u.add h_int_v

  have h_ae : ∀ᵐ y ∂(volume.restrict ball), f_uv y ≤ f_u y + f_v y := by
    filter_upwards with y
    exact h1 y

  let I_uv := ∫ y in ball, f_uv y
  let I_u := ∫ y in ball, f_u y
  let I_v := ∫ y in ball, f_v y

  have h5 : I_uv ≤ I_u + I_v := by
    have h51 : I_uv ≤ ∫ y in ball, (f_u y + f_v y) :=
      integral_mono_ae h_int_uv h_int_sum h_ae
    have h52 : (∫ y in ball, (f_u y + f_v y)) = I_u + I_v :=
      integral_add h_int_u h_int_v
    rw [h52] at h51
    exact h51

  let cvol : ℝ := (volume (Metric.ball (0 : CoefficientSpace P.dim) ε)).toReal⁻¹
  have hvol_pos : 0 ≤ cvol := by positivity

  have h_main : cvol * I_uv ≤ cvol * I_u + cvol * I_v := by
    have h : cvol * I_uv ≤ cvol * (I_u + I_v) := mul_le_mul_of_nonneg_left h5 hvol_pos
    have h2 : cvol * (I_u + I_v) = cvol * I_u + cvol * I_v := by
      exact mul_add cvol I_u I_v
    rw [h2] at h
    exact h

  have h_goal1 : concreteMollifiedDirectionalArea P ε x (u + v) U = cvol * I_uv := by rfl
  have h_goal2 : concreteMollifiedDirectionalArea P ε x u U = cvol * I_u := by rfl
  have h_goal3 : concreteMollifiedDirectionalArea P ε x v U = cvol * I_v := by rfl
  rw [h_goal1, h_goal2, h_goal3]
  exact h_main

end Kakeya.CV
