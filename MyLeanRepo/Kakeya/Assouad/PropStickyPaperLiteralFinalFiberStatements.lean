import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralAggregateDensityStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralOneParentStatements

/-!
# Literal unit rescaling of a final full fiber

Item (ii) of `prop: sticky` concerns the final full fiber itself.  Unlike the
one-parent Lemma 3.3 package, this record has no further source refinement.
It records the literal Definition 2 image of the supplied final fiber
shading, together with its extremality and the source-side multiplicity
conclusion.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperLiteralFinalFiberData
    {delta rho sigma strongLoss outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (coarse : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) where
  familyData :
    WZ2PaperLiteralUnitRescaledFamilyData
      sourceFamily coarse hrho
  literalShading :
    WZ2PaperLiteralUnitRescaledShadingData
      familyData sourceShading
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
      sourceFamily.enncard
  source_multiplicity_upper_strong :
    ∀ point,
      (sourceShading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - strongLoss) *
          sourceFamily.enncard
  source_cardinality_lower :
    Kakeya.realRpowENN (delta / rho)
        (-2 + 2 * strongLoss) ≤
      sourceFamily.enncard

def WZ2PaperLiteralFinalFiberRefreshStatement : Prop :=
  WZ2PaperLiteralUnitRescaledShadingStatement →
  WZ2PaperLiteralImageMeasureStatement →
  WZ2PaperLiteralAggregateDensityStatement →
  ∀ {delta rho sigma strongLoss outputLoss : ℝ},
    0 < delta →
    ∀ (hrho : 0 < rho),
      rho ≤ 1 →
      delta / rho ≤ 1 / 24 →
      ∀ {ambientFamily :
          Kakeya.Streamlined.TubeFamily delta},
        ∀ (ambientShading :
            WZ1PaperTubeShading ambientFamily),
          ∀ (coarse : Kakeya.DeltaTube rho),
            ∀ (logExponent : ℕ),
              ∀ (oldData :
                  WZ2PaperLiteralLemma3_3Data
                    (sigma := sigma)
                    (strongLoss := strongLoss)
                    (outputLoss := outputLoss)
                    ambientShading coarse hrho logExponent),
                ∀ (finalShading :
                    WZ1PaperTubeShading
                      oldData.refinement.selected.family),
                  (∀ index,
                    finalShading.carrier index ⊆
                      oldData.refinement.refined.carrier index) →
                  WZ1PaperIsLineClass
                    oldData.refinement.selected.family →
                  WZ1PaperTubeInLineClass coarse →
                  (∀ source,
                    WZ1PaperTubeCovers
                      (oldData.refinement.selected.family.tube source)
                      coarse) →
                  ∀ (sourceDensity : ENNReal),
                    sourceDensity *
                          oldData.refinement.selected.family.enncard *
                          Kakeya.realRpowENN delta 2 ≤
                        finalShading.mass →
                    Kakeya.realRpowENN (delta / rho) strongLoss *
                          (55296 * Kakeya.deltaTubeVolume 1) ≤
                        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
                          sourceDensity →
                    Nonempty
                      (WZ2PaperLiteralFinalFiberData
                        (sigma := sigma)
                        (strongLoss := strongLoss)
                        (outputLoss := outputLoss)
                        finalShading coarse hrho)

end Kakeya.Assouad

end
