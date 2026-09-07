import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRelativeMultiplicityHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyStatements

/-!
# Union-volume upper bound from a multiplicity floor

The integral of point multiplicity is the total shaded mass.  Therefore a
uniform multiplicity floor on the shaded union converts any mass upper bound
into an upper bound for the union volume.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

def WZ2PaperMultiplicityFloorVolumeStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ {family : Kakeya.Streamlined.TubeFamily delta},
      ∀ (shading : WZ1PaperTubeShading family),
        ∀ (multiplicityFloor massUpper volumeUpper : ENNReal),
          (∀ point ∈ shading.union,
            multiplicityFloor ≤
              (shading.pointMultiplicity point : ENNReal)) →
          shading.mass ≤ massUpper →
          massUpper ≤ multiplicityFloor * volumeUpper →
            volume shading.union ≤ volumeUpper

end Kakeya.Assouad

end
