import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescaledFamily
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralMapRelationStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers

/-!
# Correspondence between historical and literal selected target families

Both target families are indexed by the same selected source tubes.  The
historical target uses `wz1PaperUnitRescalingMap`; the literal target uses
WZ Definition 5's map.  Their axes therefore differ exactly by the fixed
longitudinal compression.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperLiteralHistoricalCorrespondenceData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C : ENNReal}
    (historical :
      WZ2PaperUnitRescaledFamilyData
        cover parent hrho C)
    (sourceSelected :
      Kakeya.Streamlined.TubeSubfamily
        (cover.fullFiberSubfamily parent).family)
    (literal :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceSelected.family (coarse.tube parent) hrho) where
  indexEquiv :
    Fin literal.targetFamily.card ≃
      Fin (historical.targetSubfamilyForSource
        sourceSelected).family.card
  indexEquiv_source :
    ∀ target,
      indexEquiv target = literal.sourceIndex target
  axis_compression :
    ∀ target,
      tubeAxisLine (literal.targetFamily.tube target) =
        wz2PaperLongitudinalCompression ''
          tubeAxisLine
            ((historical.targetSubfamilyForSource
              sourceSelected).family.tube (indexEquiv target))

def WZ2PaperLiteralHistoricalCorrespondenceStatement : Prop :=
  WZ2PaperLiteralMapImageRelationStatement →
    ∀ {delta rho : ℝ},
      ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
        ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
          ∀ {cover : WZ2PaperPartitioningCover fine coarse},
            ∀ {parent : Fin coarse.card},
              ∀ {hrho : 0 < rho},
                ∀ {C : ENNReal},
                  ∀ (historical :
                      WZ2PaperUnitRescaledFamilyData
                        cover parent hrho C),
                    ∀ (sourceSelected :
                        Kakeya.Streamlined.TubeSubfamily
                          (cover.fullFiberSubfamily parent).family),
                      ∀ (literal :
                          WZ2PaperLiteralUnitRescaledFamilyData
                            sourceSelected.family
                            (coarse.tube parent) hrho),
                        Nonempty
                          (WZ2PaperLiteralHistoricalCorrespondenceData
                            historical sourceSelected literal)

end Kakeya.Assouad

end
