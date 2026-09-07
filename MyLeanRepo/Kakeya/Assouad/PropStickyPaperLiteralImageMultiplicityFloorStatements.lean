import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageTransportStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperCubicalRefinement

/-!
# Multiplicity floor on a literal cubical image

If the source shading has point multiplicity at least `m` on its union, then
every point of the target cubical image shading also has multiplicity at
least `m`.  A target point and its source-image witness lie in the same target
grid cube, so cubicality makes their target multiplicities equal.
-/

noncomputable section

namespace Kakeya.Assouad

def WZ2PaperLiteralImageMultiplicityFloorStatement : Prop :=
  WZ2PaperLiteralImageMultiplicityStatement →
  ∀ {delta rho : ℝ},
    ∀ {sourceFamily :
        Kakeya.Streamlined.TubeFamily delta},
      ∀ {anchor : Kakeya.DeltaTube rho},
        ∀ {hrho : 0 < rho},
          ∀ (familyData :
              WZ2PaperLiteralUnitRescaledFamilyData
                sourceFamily anchor hrho),
            ∀ (sourceShading :
                WZ1PaperTubeShading sourceFamily),
              ∀ (shadingData :
                  WZ2PaperLiteralUnitRescaledShadingData
                    familyData sourceShading),
                ∀ (multiplicityFloor : ENNReal),
                  (∀ point ∈ sourceShading.union,
                    multiplicityFloor ≤
                      (sourceShading.pointMultiplicity point :
                        ENNReal)) →
                  ∀ targetPoint ∈ shadingData.targetShading.union,
                    multiplicityFloor ≤
                      (shadingData.targetShading.pointMultiplicity
                        targetPoint : ENNReal)

end Kakeya.Assouad

end
