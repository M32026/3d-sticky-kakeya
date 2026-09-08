import MyLeanRepo.Kakeya.Streamlined.Section5CubicalRepair.DilatedFullFiberFactoringAdapter
import MyLeanRepo.Kakeya.Streamlined.GeneralizedKatzTao.DegreeBoundFromDeltaMax
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.DilatedTubeContainment

/-!
# Geometry of the actual dilated parent bodies

These are the body-family properties available to the corrected Section 6
interface.  They keep the fixed dilation explicit and do not assert the false
strict-parent or `10 * rho` halo geometry used by the legacy adapter.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/-- A positive-dilation tube body has a measurable carrier. -/
lemma dilatedTubeBody_measurable
    {rho A : ℝ} (hA : 0 < A) (hrho : 0 ≤ rho)
    (tube : Kakeya.DeltaTube rho) :
    (dilatedTubeBody A tube).IsMeasurable := by
  change MeasurableSet (dilatedTubeCarrier A tube)
  rw [show dilatedTubeCarrier A tube =
      Metric.cthickening (A * rho)
        (GeometricLemmas.extendedSegment A tube) by
    exact GeometricLemmas.dilatedTubeCarrier_eq_cthickening
      hA hrho tube]
  exact Metric.isClosed_cthickening.measurableSet

/-- A positive-dilation tube body is convex. -/
lemma dilatedTubeBody_convex
    {rho A : ℝ} (hA : 0 < A) (hrho : 0 ≤ rho)
    (tube : Kakeya.DeltaTube rho) :
    Convex ℝ (dilatedTubeBody A tube).carrier :=
  convex_dilatedTubeCarrier hA hrho tube

/-- Exact volume of one positive-dilation tube body. -/
lemma dilatedTubeBody_volume
    {rho A : ℝ} (hrho : 0 < rho) (hA : 0 < A)
    (tube : Kakeya.DeltaTube rho) :
    (dilatedTubeBody A tube).volume =
      ENNReal.ofReal (A ^ 3) * tube.volume :=
  volume_dilatedTubeCarrier_of_pos hrho hA tube

/-- The actual dilated parent body family is measurable. -/
lemma dilatedTubeBodyFamily_measurable
    {rho A : ℝ} (hA : 0 < A) (hrho : 0 ≤ rho)
    (coarse : TubeFamily rho) :
    (dilatedTubeBodyFamily A coarse).IsMeasurable := by
  intro j
  exact dilatedTubeBody_measurable hA hrho (coarse.tube j)

/-- The actual dilated parent body family is convex. -/
lemma dilatedTubeBodyFamily_convex
    {rho A : ℝ} (hA : 0 < A) (hrho : 0 ≤ rho)
    (coarse : TubeFamily rho) :
    (dilatedTubeBodyFamily A coarse).IsConvex := by
  intro j
  exact dilatedTubeBody_convex hA hrho (coarse.tube j)

/-- All actual dilated parents at one radius have equal volume. -/
lemma dilatedTubeBodyFamily_equal_volume
    {rho A : ℝ} (hrho : 0 < rho) (hA : 0 < A)
    (coarse : TubeFamily rho)
    (j k : Fin coarse.card) :
    ((dilatedTubeBodyFamily A coarse).body j).volume =
      ((dilatedTubeBodyFamily A coarse).body k).volume := by
  change
    (dilatedTubeBody A (coarse.tube j)).volume =
      (dilatedTubeBody A (coarse.tube k)).volume
  rw [dilatedTubeBody_volume hrho hA,
    dilatedTubeBody_volume hrho hA]
  congr 1
  exact tube_volume_eq (coarse.tube j) (coarse.tube k)

end Kakeya.Streamlined
