import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralHistoricalCorrespondenceStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralCWATransferStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralDistinctnessTransferStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageMeasureStatements

/-!
# Selected literal-paper image package

This package records the non-recursive conclusions needed from one selected
source fiber in WZ Lemma 3.3:

* the literal Definition 5 target family and cubical image shading;
* exact correspondence with the historical stable-CWA target subfamily;
* top-level normalized Convex-Wolff, essential-distinctness, measure, and
  pullback-multiplicity conclusions.

It deliberately does not assert hereditary nearby-scale CWA. That recursive
field is supplied separately by the literal fiber-tree route.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperLiteralSelectedImageData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {ambientConstant selectedConstant : ENNReal}
    (historical :
      WZ2PaperUnitRescaledFamilyData
        cover parent hrho ambientConstant)
    (sourceSelected :
      Kakeya.Streamlined.TubeSubfamily
        (cover.fullFiberSubfamily parent).family)
    (sourceShading : WZ1PaperTubeShading sourceSelected.family) where
  literalFamily :
    WZ2PaperLiteralUnitRescaledFamilyData
      sourceSelected.family (coarse.tube parent) hrho
  literalShading :
    WZ2PaperLiteralUnitRescaledShadingData
      literalFamily sourceShading
  correspondence :
    WZ2PaperLiteralHistoricalCorrespondenceData
      historical sourceSelected literalFamily
  target_essentially_distinct :
    WZ1PaperIsEssentiallyDistinct literalFamily.targetFamily
  target_convex_wolff :
    WZ2PaperConvexWolffBound
      literalFamily.targetFamily
      ((100 : ENNReal) * selectedConstant)
  image_measure :
    WZ2PaperLiteralImageMeasureData
      literalFamily sourceShading literalShading
  target_cubical :
    WZ1PaperIsCubicalShading literalShading.targetShading
  source_cardinality_eq :
    literalFamily.targetFamily.enncard =
      sourceSelected.family.enncard
  source_multiplicity_le :
    ∀ point,
      (sourceShading.pointMultiplicity point : ENNReal) ≤
        (literalShading.targetShading.pointMultiplicity
          (wz2PaperLiteralUnitRescalingMap
            (coarse.tube parent) hrho point) : ENNReal)

def WZ2PaperLiteralSelectedImageStatement : Prop :=
  WZ2PaperLiteralUnitRescaledFamilyStatement →
  WZ2PaperLiteralUnitRescaledShadingStatement →
  WZ2PaperLiteralHistoricalCorrespondenceStatement →
  WZ2PaperHistoricalToLiteralCWAStatement →
  WZ2PaperLongitudinalCompressionLineDistanceStatement →
  WZ2PaperLiteralEssentialDistinctnessTransferStatement →
  WZ2PaperLiteralImageMeasureStatement →
  WZ2PaperLiteralImageMultiplicityStatement →
  ∀ {delta rho : ℝ},
    0 < delta →
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ {cover : WZ2PaperPartitioningCover fine coarse},
          ∀ {parent : Fin coarse.card},
            ∀ {hrho : 0 < rho},
              rho ≤ 1 →
              delta / rho ≤ 1 / 24 →
              ∀ {ambientConstant selectedConstant : ENNReal},
                ∀ (historical :
                    WZ2PaperUnitRescaledFamilyData
                      cover parent hrho ambientConstant),
                  ∀ (sourceSelected :
                      Kakeya.Streamlined.TubeSubfamily
                        (cover.fullFiberSubfamily parent).family),
                    ∀ (sourceShading :
                        WZ1PaperTubeShading sourceSelected.family),
                      WZ1PaperIsLineClass sourceSelected.family →
                      WZ1PaperTubeInLineClass (coarse.tube parent) →
                      (∀ source,
                        WZ1PaperTubeCovers
                          (sourceSelected.family.tube source)
                          (coarse.tube parent)) →
                      WZ1PaperIsEssentiallyDistinct
                        (historical.targetSubfamilyForSource
                          sourceSelected).family →
                      WZ2PaperConvexWolffBound
                        (historical.targetSubfamilyForSource
                          sourceSelected).family
                        selectedConstant →
                        Nonempty
                          (WZ2PaperLiteralSelectedImageData
                            (ambientConstant := ambientConstant)
                            (selectedConstant := selectedConstant)
                            historical sourceSelected sourceShading)

end Kakeya.Assouad

end
