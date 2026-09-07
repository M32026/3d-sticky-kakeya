import MyLeanRepo.Kakeya.CV.GeometricMeasure.GraphAreaWeightedOnOpen
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.DirectionalGraphWeight
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.MeasurabilitySetup
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.RotationTransfer

/-!
# Directional surface area on measurable graph subpieces

The direction-two surface area on a measurable subpiece of a regular graph
equals the plane normalization constant times the volume of its base.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal Real

namespace Kakeya.CV

/-- The z-directional surface area of a measurable subpiece of a regular
z-graph equals the normalized area of its base. -/
lemma directionalSurfaceArea_zGraph_projection_meas
    {p : MvPolynomial (Fin 3) ℝ} {U : Set R2} {g : R2 → ℝ} {B : Set R2}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U)
    (hB : MeasurableSet B) (hB_sub : B ⊆ U)
    (h_zero : ∀ y ∈ U, polynomialValue p (graphMap g y) = 0)
    (h_reg : ∀ y ∈ U, (polynomialGradient p (graphMap g y)) 2 ≠ 0) :
    directionalSurfaceArea (eBasis 2) p (graphMap g '' B) =
      planeConstant * volume B := by
  have he3 : eBasis 2 = e3 := by
    ext i
    fin_cases i <;> simp [e3, eBasis]
  have hweight_meas : Measurable (graphAreaW p) := by
    have hnormal : Measurable (polynomialUnitNormal p) :=
      measurable_polynomialUnitNormal p
    have hinner :
        Measurable
          (fun x : R3 =>
            inner ℝ e3 (polynomialUnitNormal p x)) :=
      measurable_const.inner hnormal
    exact ENNReal.measurable_ofReal.comp hinner.norm
  have harea :=
    graph_area_formula_weighted_on_open hU hg hB hB_sub hweight_meas
  have hintegrand : ∀ y ∈ B,
      graphAreaW p (graphMap g y) * areaFactor g y =
        planeConstant := by
    intro y hy
    have hyU : y ∈ U := hB_sub hy
    have hg_diff : DifferentiableAt ℝ g y :=
      (hg.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by norm_num)
    have hlocal :
        ∀ᶠ w : R2 in nhds y,
          polynomialValue p (graphMap g w) = 0 := by
      filter_upwards [hU.mem_nhds hyU] with w hw
      exact h_zero w hw
    have hreal :=
      graph_weight_identity_z (p := p) (g := g) (y := y) (u := e3)
        (h_zero y hyU) hlocal (h_reg y hyU) hg_diff
    have hcomponent :
        inner ℝ e3 (polynomialGradient p (graphMap g y)) =
          (polynomialGradient p (graphMap g y)) 2 := by
      simp [e3, PiLp.inner_apply]
    have hratio :
        ‖inner ℝ e3 (polynomialGradient p (graphMap g y))‖ /
            |(polynomialGradient p (graphMap g y)) 2| = 1 := by
      rw [hcomponent, Real.norm_eq_abs]
      exact div_self (abs_ne_zero.mpr (h_reg y hyU))
    rw [hratio] at hreal
    have hnonneg :
        0 ≤ ‖inner ℝ e3
          (polynomialUnitNormal p (graphMap g y))‖ :=
      norm_nonneg _
    calc
      graphAreaW p (graphMap g y) * areaFactor g y =
          ENNReal.ofReal
              ‖inner ℝ e3
                (polynomialUnitNormal p (graphMap g y))‖ *
            (planeConstant *
              ENNReal.ofReal
                (Real.sqrt (1 + ‖fderiv ℝ g y‖ ^ 2))) := by
          rfl
      _ = planeConstant *
          (ENNReal.ofReal
              ‖inner ℝ e3
                (polynomialUnitNormal p (graphMap g y))‖ *
            ENNReal.ofReal
              (Real.sqrt (1 + ‖fderiv ℝ g y‖ ^ 2))) := by
          ac_rfl
      _ = planeConstant *
          ENNReal.ofReal
            (‖inner ℝ e3
                (polynomialUnitNormal p (graphMap g y))‖ *
              Real.sqrt (1 + ‖fderiv ℝ g y‖ ^ 2)) := by
          rw [ENNReal.ofReal_mul hnonneg]
      _ = planeConstant := by
          rw [hreal]
          simp
  rw [he3]
  change (∫⁻ x in graphMap g '' B, graphAreaW p x ∂μH[2]) =
    planeConstant * volume B
  rw [harea]
  have hcongr :
      (∫⁻ y in B,
          graphAreaW p (graphMap g y) * areaFactor g y ∂volume) =
        ∫⁻ _ in B, planeConstant ∂volume := by
    exact setLIntegral_congr_fun hB hintegrand
  rw [hcongr]
  rw [setLIntegral_const]

end Kakeya.CV
