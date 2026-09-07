import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Relative source multiplicity after external-weight selection

The packed source shading lies in one dyadic multiplicity band.  Its old
literal image has the same lower multiplicity floor.  A critical lower bound
for the final selected literal union, containment in the old literal union,
and the old target quadratic mass upper bound control the absolute dyadic
level.  Weighted cardinality retention then replaces packed source
cardinality by the final selected source cardinality.

Source and target scales are kept distinct throughout.
-/

noncomputable section

namespace Kakeya.Assouad

def WZ2PaperExternalWeightRelativeMultiplicityStatement : Prop :=
  ∀ {sourceScale targetScale sigma floorLoss strongLoss : ℝ},
    0 < targetScale →
    targetScale ≤ 1 →
    floorLoss < strongLoss →
    ∀ {packedSource selectedSource :
        Kakeya.Streamlined.TubeFamily sourceScale},
      ∀ (packedShading :
          WZ1PaperTubeShading packedSource),
        ∀ (selectedShading :
            WZ1PaperTubeShading selectedSource),
          ∀ {oldTarget finalTarget :
              Kakeya.Streamlined.TubeFamily targetScale},
            ∀ (oldTargetShading :
                WZ1PaperTubeShading oldTarget),
              ∀ (finalTargetShading :
                  WZ1PaperTubeShading finalTarget),
                ∀ (multiplicity : ℕ),
                  (∀ point,
                    (selectedShading.pointMultiplicity point : ENNReal) ≤
                      (packedShading.pointMultiplicity point : ENNReal)) →
                  (∀ point,
                    (packedShading.pointMultiplicity point : ENNReal) ≤
                      (2 * multiplicity : ENNReal)) →
                  (∀ point ∈ oldTargetShading.union,
                    (multiplicity : ENNReal) ≤
                      (oldTargetShading.pointMultiplicity point :
                        ENNReal)) →
                  finalTargetShading.union ⊆
                    oldTargetShading.union →
                  Kakeya.realRpowENN targetScale
                      (sigma + floorLoss) ≤
                    MeasureTheory.volume finalTargetShading.union →
                  ∀ (massConstant weight cardinalityLoss : ENNReal),
                    oldTargetShading.mass ≤
                      massConstant *
                        Kakeya.realRpowENN targetScale 2 *
                        packedSource.enncard →
                    weight ≠ 0 →
                    weight ≠ ⊤ →
                    weight * packedSource.enncard ≤
                      cardinalityLoss * selectedSource.enncard →
                    2 * massConstant *
                          (weight⁻¹ * cardinalityLoss) ≤
                      Kakeya.realRpowENN targetScale
                        (-(strongLoss - floorLoss)) →
                    ∀ point,
                      (selectedShading.pointMultiplicity point :
                          ENNReal) ≤
                        Kakeya.realRpowENN targetScale
                            (2 - sigma - strongLoss) *
                          selectedSource.enncard

end Kakeya.Assouad

end
