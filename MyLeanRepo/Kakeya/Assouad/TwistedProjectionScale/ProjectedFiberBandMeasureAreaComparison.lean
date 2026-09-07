import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberBandMeasureAreaComparisonStatement

/-!
# Projected measure versus area inside one fiber-multiplicity band

Integrate the pointwise dyadic-band bounds over an arbitrary measurable
subset of the selected projected-fiber band.
-/

open MeasureTheory

namespace Kakeya.Assouad

theorem projected_fiber_band_measure_area_comparison :
    ProjectedFiberBandMeasureAreaComparisonStatement := by
  intro delta F Y f threshold levelCount bandData X hX_meas hX_subset
  set lambda : ENNReal :=
    projectedFiberBandValue Y f bandData with hlambda_def
  have h_measure_eq :
      projectedFiberMeasure Y f X =
        ∫⁻ q in X, projectedFiberMultiplicity Y f q :=
    MeasureTheory.withDensity_apply
      (projectedFiberMultiplicity Y f) hX_meas
  have h_lower :
      ∀ q ∈ X, lambda ≤ projectedFiberMultiplicity Y f q := by
    intro q hq
    exact bandData.fiber_lower q (hX_subset hq)
  have h_band_upper_eq :
      threshold *
          (2 ^ (bandData.bandIndex + 1) : ENNReal) =
        2 * lambda := by
    have h_pow :
        (2 ^ (bandData.bandIndex + 1) : ENNReal) =
          2 * (2 ^ bandData.bandIndex : ENNReal) := by
      rw [pow_succ']
    calc
      threshold *
            (2 ^ (bandData.bandIndex + 1) : ENNReal)
          = threshold *
              (2 * (2 ^ bandData.bandIndex : ENNReal)) := by
              rw [h_pow]
      _ = 2 *
            (threshold *
              (2 ^ bandData.bandIndex : ENNReal)) := by
          rw [← mul_assoc, mul_comm threshold (2 : ENNReal),
            mul_assoc]
      _ = 2 * lambda := by
          simp [hlambda_def, projectedFiberBandValue]
  have h_upper :
      ∀ q ∈ X, projectedFiberMultiplicity Y f q ≤ 2 * lambda := by
    intro q hq
    have h1 :
        projectedFiberMultiplicity Y f q <
          threshold *
            (2 ^ (bandData.bandIndex + 1) : ENNReal) :=
      bandData.fiber_upper q (hX_subset hq)
    rw [h_band_upper_eq] at h1
    exact h1.le
  have h1 :
      lambda * volume X ≤ projectedFiberMeasure Y f X := by
    rw [h_measure_eq]
    calc
      lambda * volume X
          = ∫⁻ q in X, lambda :=
            (MeasureTheory.setLIntegral_const X lambda).symm
      _ ≤ ∫⁻ q in X, projectedFiberMultiplicity Y f q :=
        MeasureTheory.setLIntegral_mono' hX_meas h_lower
  have h2 :
      projectedFiberMeasure Y f X ≤
        2 * lambda * volume X := by
    rw [h_measure_eq]
    calc
      ∫⁻ q in X, projectedFiberMultiplicity Y f q
          ≤ ∫⁻ q in X, (2 * lambda) :=
            MeasureTheory.setLIntegral_mono' hX_meas h_upper
      _ = (2 * lambda) * volume X :=
        MeasureTheory.setLIntegral_const X (2 * lambda)
      _ = 2 * lambda * volume X := by
        rw [mul_assoc]
  exact ⟨h1, h2⟩

end Kakeya.Assouad
