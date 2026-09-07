import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSelectedAnchorRootStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSelectedAnchorRootReindex
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralHistoricalCorrespondenceStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralCWATransferStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRootScaleStatements

/-!
# Fixed literal family and its actual unit-scale root

Starting from one nonempty selected subfamily of a fixed source `sigma`-fiber:

* retain the original anchor as a singleton source root;
* construct the literal Definition 5 image family once;
* transfer the supplied historical selected-family CWA to that literal family;
* construct the vertical unit root and the actual scale-one recursive witness.

The output constant is `1000000 * C`: factor `100` comes from the
historical-to-literal longitudinal compression and factor `10000` from the
vertical-root transverse inverse Jacobian.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperLiteralFixedRootSetupData
    {delta sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {rootCoarse : Kakeya.Streamlined.TubeFamily sigma}
    {rootCover : WZ2PaperPartitioningCover fine rootCoarse}
    {anchor : Fin rootCoarse.card}
    {hsigma : 0 < sigma}
    {ambientConstant selectedConstant : ENNReal}
    (historical :
      WZ2PaperUnitRescaledFamilyData
        rootCover anchor hsigma ambientConstant)
    (selected :
      Kakeya.Streamlined.TubeSubfamily
        (rootCover.fullFiberSubfamily anchor).family)
    (htargetScale :
      delta / sigma ≤ 1 ∧ (1 : ℝ) ≤ 1) where
  selectedRoot :
    WZ2PaperSelectedAnchorRootData
      rootCover anchor selected
  selectedLiteralFamily :
    WZ2PaperLiteralUnitRescaledFamilyData
      selected.family (rootCoarse.tube anchor) hsigma
  literalFamily :
    WZ2PaperLiteralUnitRescaledFamilyData
      (selectedRoot.cover.fullFiberSubfamily
        (wz2PaperSelectedAnchorRootIndex
          (rootCoarse.tube anchor))).family
      (rootCoarse.tube anchor) hsigma
  literalFamily_eq :
    literalFamily =
      selectedRoot.reindexLiteralFamily selectedLiteralFamily
  correspondence :
    WZ2PaperLiteralHistoricalCorrespondenceData
      historical selected selectedLiteralFamily
  literal_convex_wolff :
    WZ2PaperConvexWolffBound
      selectedLiteralFamily.targetFamily
      ((100 : ENNReal) * selectedConstant)
  unitRootFamily :
    WZ2PaperLiteralUnitRootFamilyData literalFamily
  unitRootScale :
    WZ2PaperLiteralUnitRootScaleData
      unitRootFamily htargetScale
      ((1000000 : ENNReal) * selectedConstant)

def WZ2PaperLiteralFixedRootSetupStatement : Prop :=
  WZ2PaperSelectedAnchorRootStatement →
  WZ2PaperLiteralUnitRescaledFamilyStatement →
  WZ2PaperLiteralHistoricalCorrespondenceStatement →
  WZ2PaperHistoricalToLiteralCWAStatement →
  WZ2PaperLiteralUnitRootFamilyStatement →
  WZ2PaperLiteralUnitRootScaleStatement →
  ∀ {delta sigma : ℝ},
    0 < delta →
    ∀ (hsigma : 0 < sigma),
      ∀ (hdeltaSigma : delta ≤ sigma),
        sigma ≤ 1 →
        ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
          WZ1PaperIsLineClass fine →
          ∀ {rootCoarse :
              Kakeya.Streamlined.TubeFamily sigma},
            WZ1PaperIsLineClass rootCoarse →
            ∀ {rootCover :
                WZ2PaperPartitioningCover fine rootCoarse},
              ∀ (anchor : Fin rootCoarse.card),
                ∀ {ambientConstant selectedConstant : ENNReal},
                  ∀ (historical :
                      WZ2PaperUnitRescaledFamilyData
                        rootCover anchor hsigma ambientConstant),
                    ∀ (selected :
                        Kakeya.Streamlined.TubeSubfamily
                          (rootCover.fullFiberSubfamily anchor).family),
                      0 < selected.family.card →
                      1 ≤ selectedConstant →
                      WZ2PaperConvexWolffBound
                        (historical.targetSubfamilyForSource
                          selected).family
                        selectedConstant →
                        Nonempty
                          (WZ2PaperLiteralFixedRootSetupData
                            (selectedConstant := selectedConstant)
                            historical selected
                            ⟨(div_le_one hsigma).mpr hdeltaSigma,
                              le_rfl⟩)

end Kakeya.Assouad

end
