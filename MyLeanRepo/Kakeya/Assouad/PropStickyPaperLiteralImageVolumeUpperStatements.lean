import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageMultiplicityFloorStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolumeStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpperStatements

/-!
# Union-volume upper bound for a literal cubical image

Transfer a source multiplicity floor to the full target cubical image, bound
the target shaded mass by the quadratic paper-tube estimate, and divide by
the multiplicity floor.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

def WZ2PaperLiteralImageVolumeUpperStatement : Prop :=
  WZ2PaperLiteralImageMultiplicityFloorStatement →
  WZ2PaperShadingMassUpperStatement →
  WZ2PaperMultiplicityFloorVolumeStatement →
  ∀ {delta rho : ℝ},
    0 < delta →
    ∀ (hrho : 0 < rho),
      delta / rho ≤ 1 / 24 →
      ∀ {sourceFamily :
          Kakeya.Streamlined.TubeFamily delta},
        ∀ {anchor : Kakeya.DeltaTube rho},
          ∀ (familyData :
              WZ2PaperLiteralUnitRescaledFamilyData
                sourceFamily anchor hrho),
            ∀ (sourceShading :
                WZ1PaperTubeShading sourceFamily),
              ∀ (shadingData :
                  WZ2PaperLiteralUnitRescaledShadingData
                    familyData sourceShading),
                ∀ (multiplicityFloor volumeUpper : ENNReal),
                  (∀ point ∈ sourceShading.union,
                    multiplicityFloor ≤
                      (sourceShading.pointMultiplicity point :
                        ENNReal)) →
                  (55296 * Kakeya.deltaTubeVolume 1) *
                        Kakeya.realRpowENN (delta / rho) 2 *
                      familyData.targetFamily.enncard ≤
                    multiplicityFloor * volumeUpper →
                  volume shadingData.targetShading.union ≤
                    volumeUpper

end Kakeya.Assouad

end
