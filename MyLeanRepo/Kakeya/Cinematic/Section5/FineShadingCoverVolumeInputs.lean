import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredRectangleEnlargementInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.FineAssignmentEnlargement
import MyLeanRepo.Kakeya.Cinematic.Section5.ShadingInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.ShadingVolume
import MyLeanRepo.Kakeya.Cinematic.Section5.PolynomialScaleCoarseCountInputs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Fine-shading cover and volume assembly

This is the scale-cap-free covering part of PYZ Lemma 43. The fixed fine
scale constant may be enlarged before the small-scale threshold is chosen.
Polynomial-scale rectangle counting supplies the finite bound needed by the
maximal selection; callers do not provide an arbitrary cardinality bound.
The counting, shading, and carrier-volume constants are chosen uniformly
before the variable family, scale, level set, and assignment data.
-/

open MeasureTheory

namespace Kakeya.Cinematic

def FineShadingCoverVolumeStatement : Prop :=
  CenteredRectangleEnlargementStatement →
    FineShadingComparisonStatement →
    MaximalFineRectangleSelectionStatement →
    PolynomialScaleCoarseRectangleCountStatement →
    ComparableRectanglesStatement →
    ComparabilityTransitivityStatement →
    ∀ K D T C_R₀ : ℝ,
      1 ≤ K →
      1 ≤ D →
      1 ≤ T →
      0 < C_R₀ →
      ∃ C_R C_count C_shading C_volume : ℝ,
        C_R₀ ≤ C_R ∧
        100 ≤ C_R ∧
        0 < C_count ∧
        100 ≤ C_shading ∧
        100 ≤ C_volume ∧
        ∃ delta₀ : ℝ,
          0 < delta₀ ∧
          delta₀ ≤ 1 ∧
          ∀ {family : Set C2Function} {E₂ : Set (ℝ × ℝ)}
            {delta t Delta : ℝ},
            IsCinematicFamily family K D →
            E₂.Nonempty →
            0 < delta →
            delta ≤ delta₀ →
            delta ≤ Delta →
            Delta ≤ t →
            t ≤ T →
            ∀ data₀ :
                FineRectangleAssignmentData
                  family E₂ K delta t Delta C_R₀,
              ∃ data :
                  FineRectangleAssignmentData
                    family E₂ K delta t Delta C_R,
                data.interval = data₀.interval ∧
                (∀ p : E₂, data.center p = data₀.center p) ∧
                (∀ p : E₂, data.fiber p = data₀.fiber p) ∧
                ∃ R : RectangleFamily
                    delta (C_R * t * Delta / delta),
                  ∃ source : Fin R.card → E₂,
                    R.Nonempty ∧
                    (∀ i, R.rectangle i = data.rectangle (source i)) ∧
                    R.CentersIn family ∧
                    R.IsOverCentralQuarterOf data.interval ∧
                    R.IsPairwiseIncomparable family 100 ∧
                    (R.card : ℝ) ≤
                      Real.rpow delta (-C_count) ∧
                    ∃ U_enlarged : Fin R.card →
                        CurvilinearRectangle
                          (C_shading * delta)
                          (C_R * t * Delta / delta),
                      (∀ i,
                        (U_enlarged i).function =
                          (R.rectangle i).function) ∧
                      (∀ i,
                        (U_enlarged i).interval.midpoint =
                          (R.rectangle i).interval.midpoint) ∧
                      E₂ ⊆ ⋃ i, (U_enlarged i).realCarrier ∧
                    volume E₂ ≤
                      (R.card : ENNReal) *
                        ENNReal.ofReal
                          (2 * C_volume * delta ^ 2 /
                            Real.sqrt (C_R * t * Delta))

end Kakeya.Cinematic
