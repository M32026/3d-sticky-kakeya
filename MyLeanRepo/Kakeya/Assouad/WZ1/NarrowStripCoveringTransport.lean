import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremLocalizationStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49OutsideActiveStripCore
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Covering transport for the narrow branch of WZ1 Proposition 8.9

Separated dot-difference values inside one interval give the localized long
projection conclusion once their cardinality supplies the required covering
power.
-/

namespace Kakeya.Assouad

noncomputable section

open scoped ENNReal

attribute [local instance] Classical.propDecidable

/--
Convert a finite set of `2 * rho`-separated real values, contained in the
dot-difference set and one closed ball, to the long-projection conclusion.
-/
lemma separated_dot_values_to_long_projection
    {delta epsilon eta rho center radius : ℝ}
    {H : Finset (Point2 × Point2 × Point2)}
    {values : Finset ℝ}
    (hdelta : 0 < delta)
    (hrho : delta ≤ rho)
    (hrhoOne : rho ≤ 1)
    (hradius : 0 < radius)
    (hlength : Real.rpow delta (-eta) * rho ≤ 2 * radius)
    (hseparated :
      ∀ first ∈ values, ∀ second ∈ values,
        first ≠ second → 2 * rho < |first - second|)
    (hvaluesDot :
      (values : Set ℝ) ⊆ wz1DotDifferenceSet H)
    (hvaluesBall :
      (values : Set ℝ) ⊆ Metric.closedBall center radius)
    (hcard :
      Kakeya.realRpowENN
          (2 * radius / rho) (1 - epsilon) ≤
        (values.card : ENNReal)) :
    WZ1StripLocalizationLongProjection
      delta epsilon eta H := by
  have hrhoPos : 0 < rho := hdelta.trans_le hrho
  have hcoverValues :
      (values.card : ENNReal) ≤
        Metric.externalCoveringNumber
          (Real.toNNReal rho) (values : Set ℝ) :=
    wz1Lemma49_separated_real_covering_lower_bound
      hrhoPos hseparated
  have hvaluesInter :
      (values : Set ℝ) ⊆
        wz1DotDifferenceSet H ∩
          Metric.closedBall center radius :=
    fun _ hvalue =>
      ⟨hvaluesDot hvalue, hvaluesBall hvalue⟩
  have hcoverMono :
      Metric.externalCoveringNumber
          (Real.toNNReal rho) (values : Set ℝ) ≤
        Metric.externalCoveringNumber
          (Real.toNNReal rho)
          (wz1DotDifferenceSet H ∩
            Metric.closedBall center radius) :=
    Metric.externalCoveringNumber_mono_set hvaluesInter
  exact
    ⟨rho, center, radius, hrho, hrhoOne, hradius,
      hlength,
      hcard.trans
        (hcoverValues.trans (by exact_mod_cast hcoverMono))⟩

/--
Use the extreme values of a finite set to place all values in a centered
closed ball.  The radius is enlarged, if necessary, to meet the interval
length condition in the long-projection conclusion.
-/
lemma separated_dot_values_interval_to_long_projection
    {delta epsilon eta : ℝ}
    {H : Finset (Point2 × Point2 × Point2)}
    {values : Finset ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hseparated :
      ∀ first ∈ values, ∀ second ∈ values,
        first ≠ second → 2 * delta < |first - second|)
    (hvaluesDot :
      (values : Set ℝ) ⊆ wz1DotDifferenceSet H)
    (lower upper : ℝ)
    (hlower : lower ∈ values)
    (hupper : upper ∈ values)
    (hbetween :
      ∀ value ∈ values, lower ≤ value ∧ value ≤ upper)
    (hcard :
      Kakeya.realRpowENN
          (2 *
              max ((upper - lower) / 2)
                (Real.rpow delta (1 - eta) / 2) /
            delta)
          (1 - epsilon) ≤
        (values.card : ENNReal)) :
    WZ1StripLocalizationLongProjection
      delta epsilon eta H := by
  let center := (lower + upper) / 2
  let radius :=
    max ((upper - lower) / 2)
      (Real.rpow delta (1 - eta) / 2)
  have hradius : 0 < radius := by
    have hpositive :
        0 < Real.rpow delta (1 - eta) / 2 :=
      div_pos (Real.rpow_pos_of_pos hdelta _) (by norm_num)
    exact hpositive.trans_le (le_max_right _ _)
  have hpower :
      Real.rpow delta (-eta) * delta =
        Real.rpow delta (1 - eta) := by
    have hadd := Real.rpow_add hdelta (-eta) 1
    have hexponent : -eta + 1 = 1 - eta := by ring
    have hone : Real.rpow delta 1 = delta := by simp
    calc
      Real.rpow delta (-eta) * delta =
          Real.rpow delta (-eta) *
            Real.rpow delta 1 := by rw [hone]
      _ = Real.rpow delta (-eta + 1) := hadd.symm
      _ = Real.rpow delta (1 - eta) := by rw [hexponent]
  have hlength :
      Real.rpow delta (-eta) * delta ≤
        2 * radius := by
    rw [hpower]
    calc
      Real.rpow delta (1 - eta) =
          2 * (Real.rpow delta (1 - eta) / 2) := by ring
      _ ≤
          2 *
            max ((upper - lower) / 2)
              (Real.rpow delta (1 - eta) / 2) := by
        gcongr
        exact le_max_right _ _
  have hvaluesBall :
      (values : Set ℝ) ⊆
        Metric.closedBall center radius := by
    intro value hvalue
    have hlowerValue := (hbetween value hvalue).1
    have hvalueUpper := (hbetween value hvalue).2
    have hdistance :
        |value - center| ≤ (upper - lower) / 2 := by
      dsimp only [center]
      rw [abs_le]
      constructor <;> linarith
    have hleRadius : |value - center| ≤ radius :=
      hdistance.trans (le_max_left _ _)
    simpa [Metric.mem_closedBall, Real.dist_eq] using hleRadius
  exact
    separated_dot_values_to_long_projection
      hdelta (le_refl delta) hdeltaOne hradius hlength
      hseparated hvaluesDot hvaluesBall hcard

end

end Kakeya.Assouad
