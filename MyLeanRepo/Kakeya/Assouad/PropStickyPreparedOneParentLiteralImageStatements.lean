import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentLiteralCWAStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageMeasureStatements

/-! # Literal image shading for one prepared selected caller fiber -/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperPreparedOneParentLiteralImageData
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (parent : Fin prepared.callerStrict.coarse.card)
    (selection :
      WZ2PaperPreparedOneParentSelectionData prepared parent)
    (quantitative :
      WZ2PaperPreparedOneParentQuantitativeData
        prepared parent selection)
    {restrictedConstant targetConstant : ENNReal}
    (literalCWA :
      WZ2PaperPreparedOneParentLiteralCWAData
        prepared parent selection quantitative
        restrictedConstant targetConstant) where
  literalShading :
    WZ2PaperLiteralUnitRescaledShadingData
      literalCWA.rootSetup.selectedLiteralFamily
      selection.refinement.refined
  imageMeasure :
    WZ2PaperLiteralImageMeasureData
      literalCWA.rootSetup.selectedLiteralFamily
      selection.refinement.refined literalShading
  source_cardinality_eq :
    literalCWA.rootSetup.selectedLiteralFamily.targetFamily.enncard =
      selection.refinement.selected.family.enncard

def WZ2PropStickyPreparedOneParentLiteralImageStatement : Prop :=
  ∀ {delta sourceLoss stableLoss : ℝ},
    ∀ {source : Kakeya.Streamlined.TubeFamily delta},
      ∀ {shading : WZ1PaperTubeShading source},
        ∀ {caller : Kakeya.Streamlined.AdmissibleScale delta},
          ∀ {preparationExponent : ℕ},
            ∀ (prepared :
                WZ2PaperCallerStrictPreparationData
                  (sourceLoss := sourceLoss)
                  (stableLoss := stableLoss)
                  shading caller preparationExponent),
              ∀ parent : Fin prepared.callerStrict.coarse.card,
                ∀ (selection :
                    WZ2PaperPreparedOneParentSelectionData
                      prepared parent),
                  ∀ (quantitative :
                      WZ2PaperPreparedOneParentQuantitativeData
                        prepared parent selection),
                    ∀ {restrictedConstant targetConstant : ENNReal},
                      ∀ (literalCWA :
                          WZ2PaperPreparedOneParentLiteralCWAData
                            prepared parent selection quantitative
                            restrictedConstant targetConstant),
                        delta / caller.1 ≤ 1 / 24 →
                        Nonempty
                          (WZ2PaperPreparedOneParentLiteralImageData
                            prepared parent selection quantitative
                            literalCWA)

end Kakeya.Assouad

end
