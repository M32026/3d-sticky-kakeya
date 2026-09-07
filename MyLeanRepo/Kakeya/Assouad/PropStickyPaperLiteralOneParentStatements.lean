import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageAssemblyStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyStatements

/-!
# Literal-paper one-parent output for WZ2 `prop: sticky`

This is the paper-faithful replacement for the historical one-parent output
whose image field used `wz1PaperUnitRescalingMap`.  The target family and
shading here are explicitly the literal Definition 2 image built using
`wz2PaperLiteralUnitRescalingMap`.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperLiteralLemma3_3Data
    {delta rho sigma strongLoss outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (coarse : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (logExponent : ℕ) where
  refinement :
    WZ1PaperRefinement shading logExponent
  refined_cubical :
    WZ1PaperIsCubicalShading refinement.refined
  refined_nonempty :
    ∀ index, (refinement.refined.carrier index).Nonempty
  familyData :
    WZ2PaperLiteralUnitRescaledFamilyData
      refinement.selected.family coarse hrho
  literalShading :
    WZ2PaperLiteralUnitRescaledShadingData
      familyData refinement.refined
  strongLoss_pos : 0 < strongLoss
  strongLoss_budget : 3 * strongLoss ≤ outputLoss
  extremal_strong :
    WZ2PaperIsExtremal
      sigma strongLoss
      familyData.targetFamily
      literalShading.targetShading
  extremal :
    WZ2PaperIsExtremal
      sigma outputLoss
      familyData.targetFamily
      literalShading.targetShading
  target_cardinality_lower :
    Kakeya.realRpowENN (delta / rho)
        (-2 + 2 * strongLoss) ≤
      familyData.targetFamily.enncard
  source_cardinality_eq :
    familyData.targetFamily.enncard =
      refinement.selected.family.enncard
  source_multiplicity_upper_strong :
    ∀ point,
      (refinement.refined.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - strongLoss) *
          refinement.selected.family.enncard
  source_cardinality_lower :
    Kakeya.realRpowENN (delta / rho)
        (-2 + 2 * strongLoss) ≤
      refinement.selected.family.enncard

def WZ2PaperLiteralOneParentAssemblyStatement : Prop :=
  ∀ {delta rho sigma strongLoss outputLoss : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ (shading : WZ1PaperTubeShading fine),
        ∀ (coarse : Kakeya.DeltaTube rho),
          ∀ (hrho : 0 < rho),
            ∀ (logExponent : ℕ),
              ∀ (refinement :
                  WZ1PaperRefinement shading logExponent),
                WZ1PaperIsCubicalShading refinement.refined →
                (∀ index,
                  (refinement.refined.carrier index).Nonempty) →
                ∀ (familyData :
                    WZ2PaperLiteralUnitRescaledFamilyData
                      refinement.selected.family coarse hrho),
                  ∀ (literalShading :
                      WZ2PaperLiteralUnitRescaledShadingData
                        familyData refinement.refined),
                    0 < strongLoss →
                    3 * strongLoss ≤ outputLoss →
                    WZ2PaperIsExtremal
                      sigma strongLoss
                      familyData.targetFamily
                      literalShading.targetShading →
                    WZ2PaperIsExtremal
                      sigma outputLoss
                      familyData.targetFamily
                      literalShading.targetShading →
                    Kakeya.realRpowENN (delta / rho)
                        (-2 + 2 * strongLoss) ≤
                      familyData.targetFamily.enncard →
                    familyData.targetFamily.enncard =
                      refinement.selected.family.enncard →
                    (∀ point,
                      (refinement.refined.pointMultiplicity point :
                          ENNReal) ≤
                        Kakeya.realRpowENN (delta / rho)
                            (2 - sigma - strongLoss) *
                          refinement.selected.family.enncard) →
                    Nonempty
                      (WZ2PaperLiteralLemma3_3Data
                        (sigma := sigma)
                        (strongLoss := strongLoss)
                        (outputLoss := outputLoss)
                        shading coarse hrho logExponent)

end Kakeya.Assouad

end
