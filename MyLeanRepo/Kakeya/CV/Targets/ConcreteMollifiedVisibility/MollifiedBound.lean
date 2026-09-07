import MyLeanRepo.Kakeya.CV.VisibilityDegreeBound.Helpers
import MyLeanRepo.Kakeya.CV.PolynomialMollification
import MyLeanRepo.Kakeya.CV.Mollification
import MyLeanRepo.Kakeya.CV.Targets.ConcreteMollifiedVisibility.DirectionalAreaBounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar


/-!
# Linear bound and continuity of concrete mollified directional area
-/

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace Kakeya.CV

/-- Linear bound `concreteMollifiedDirectionalArea P ε x u U ≤ B * ‖u‖`. -/
lemma concreteMollifiedDirectionalArea_bound
    {k : ℕ} {P : PolynomialParameterization k} {U : Set (Point 3)} {c : Point 3}
    {ε : ℝ} {x : CoefficientSpace P.dim}
    {hU_meas : MeasurableSet U}
    {hU : U ⊆ Metric.closedBall c 1} {hε : 0 < ε}
    (hSurface : ConcreteMollifiedSurfaceStatement)
    (B_ennreal : ENNReal)
    (hB_ne_top : B_ennreal ≠ ⊤)
    (h_bound_all : ∀ (y : CoefficientSpace P.dim) (u : Point 3),
      directionalSurfaceArea u (parameterPolynomial P y)
        (polynomialZeroSet (parameterPolynomial P y) ∩ U) ≤ B_ennreal * ENNReal.ofReal ‖u‖)
    (h_finite : ∀ (y : CoefficientSpace P.dim) (u : Point 3),
      directionalSurfaceArea u (parameterPolynomial P y)
        (polynomialZeroSet (parameterPolynomial P y) ∩ U) ≠ ⊤)
    (u : Point 3) :
    concreteMollifiedDirectionalArea P ε x u U ≤ B_ennreal.toReal * ‖u‖ := by
  let ball : Set (CoefficientSpace P.dim) := Metric.ball x ε
  let mass : CoefficientSpace P.dim → Point 3 → ℝ≥0∞ := fun y w =>
    directionalSurfaceArea w (parameterPolynomial P y)
      (polynomialZeroSet (parameterPolynomial P y) ∩ U)
  let B_real : ℝ := B_ennreal.toReal
  have hB_eq : B_ennreal = ENNReal.ofReal B_real := (ENNReal.ofReal_toReal hB_ne_top).symm
  have h_surface_data := hSurface k P U c ε hU_meas hU hε

  have h1 : ∀ y, coefficientSurfaceFunctional P u U y ≤ B_real * ‖u‖ := by
    intro y
    have h2 : mass y u ≤ B_ennreal * ENNReal.ofReal ‖u‖ := h_bound_all y u
    have h_b_fin : (B_ennreal * ENNReal.ofReal ‖u‖) ≠ ⊤ := ENNReal.mul_ne_top hB_ne_top (by simp)
    have h3 : (mass y u).toReal ≤ (B_ennreal * ENNReal.ofReal ‖u‖).toReal :=
      (ENNReal.toReal_le_toReal (h_finite y u) h_b_fin).mpr h2
    have h4 : (B_ennreal * ENNReal.ofReal ‖u‖).toReal = B_real * ‖u‖ := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg u)]
      <;> simp [hB_eq]
    rw [h4] at h3
    exact h3

  have h_compact : IsCompact (Metric.closedBall x ε) := by
    exact isCompact_closedBall x ε
  have h_int_on : IntegrableOn (coefficientSurfaceFunctional P u U) ball volume := by
    have h_loc_int : LocallyIntegrable (coefficientSurfaceFunctional P u U) volume := h_surface_data.1 u
    exact (h_loc_int.integrableOn_isCompact h_compact).mono_set Metric.ball_subset_closedBall
  have h_int_const : IntegrableOn (fun _ : CoefficientSpace P.dim => B_real * ‖u‖) ball volume := by
    have h_cont : Continuous (fun _ : CoefficientSpace P.dim => B_real * ‖u‖) := continuous_const
    have h_loc : LocallyIntegrable (fun _ => B_real * ‖u‖) volume := h_cont.locallyIntegrable
    exact (h_loc.integrableOn_isCompact h_compact).mono_set Metric.ball_subset_closedBall
  have h_ae : ∀ᵐ y ∂(volume.restrict ball), coefficientSurfaceFunctional P u U y ≤ B_real * ‖u‖ := by
    filter_upwards with y
    exact h1 y
  have h5 : ∫ y in ball, coefficientSurfaceFunctional P u U y ≤ ∫ y in ball, (B_real * ‖u‖) :=
    integral_mono_ae h_int_on h_int_const h_ae
  have hvol_pos : 0 < volume ball := by
    have h_open : IsOpen ball := Metric.isOpen_ball
    have hne : ball.Nonempty := Metric.nonempty_ball.mpr hε
    exact h_open.measure_pos volume hne
  have hvol_ne_top : volume ball ≠ ⊤ := Metric.isBounded_ball.measure_lt_top.ne
  have hvol_toReal_pos : 0 < (volume ball).toReal := by
    rw [ENNReal.toReal_pos_iff] <;> exact ⟨hvol_pos, hvol_ne_top.lt_top⟩
  have h6 : ∫ y in ball, (B_real * ‖u‖) = (B_real * ‖u‖) * (volume ball).toReal := by
    haveI : IsFiniteMeasure (volume.restrict ball) := by
      exact isFiniteMeasure_restrict.mpr hvol_ne_top
    have h_const : ∫ y, (B_real * ‖u‖) ∂(volume.restrict ball) =
        (volume.restrict ball).real Set.univ • (B_real * ‖u‖) :=
      integral_const (μ := volume.restrict ball) (B_real * ‖u‖)
    have h9 : (volume.restrict ball).real Set.univ • (B_real * ‖u‖) =
        (B_real * ‖u‖) * (volume.restrict ball Set.univ).toReal := by
      have h_real : (volume.restrict ball).real Set.univ = ((volume.restrict ball) Set.univ).toReal := by rfl
      rw [h_real, smul_eq_mul, mul_comm]
    have h10 : (volume.restrict ball Set.univ) = volume ball := by simp
    have h11 : ∫ y, (B_real * ‖u‖) ∂(volume.restrict ball) = (B_real * ‖u‖) * (volume ball).toReal := by
      rw [h_const, h9, h10]
    exact h11
  rw [h6] at h5
  have hvol_translate : volume (Metric.ball x ε) =
      volume (Metric.ball (0 : CoefficientSpace P.dim) ε) := by
    exact Measure.addHaar_ball_center volume x ε
  simp only [concreteMollifiedDirectionalArea, ballAverage]
  have h7 : (volume (Metric.ball (0 : CoefficientSpace P.dim) ε)).toReal = (volume ball).toReal := by rw [hvol_translate]
  rw [h7]
  have h8 : 0 < (volume ball).toReal := hvol_toReal_pos
  have h9 : (volume ball).toReal⁻¹ * ∫ y in ball, coefficientSurfaceFunctional P u U y ≤
      (volume ball).toReal⁻¹ * (B_real * ‖u‖ * (volume ball).toReal) := by gcongr
  have h10 : (volume ball).toReal⁻¹ * (B_real * ‖u‖ * (volume ball).toReal) = B_real * ‖u‖ := by
    field_simp [h8.ne'] <;> ring
  rw [h10] at h9
  exact h9

end Kakeya.CV
