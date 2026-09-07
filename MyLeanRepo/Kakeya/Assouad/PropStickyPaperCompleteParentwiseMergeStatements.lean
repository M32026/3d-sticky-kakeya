import MyLeanRepo.Kakeya.Assouad.PropStickyPaperHeavyParentSelection
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralMergedFiberOutputsStatements

/-!
# Parentwise merge over complete heavy fibers

The heavy-parent selection retains every ambient fine tube over each selected
coarse parent.  Reindex one-parent outputs from the ambient full fibers onto
the corresponding full fibers of the selected cover, then run the closed
parentwise merge and merged-fiber output pipeline.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperCompleteParentwiseMergeData
    {delta rho sigma strongLoss outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (heavy : WZ2PaperHeavyParentSelectionData cover shading)
    (hrho : 0 < rho)
    (logExponent : ℕ)
    (ambientFiberData :
      ∀ parent :
          Fin (cover.hitParentSubfamily heavy.selected).family.card,
        WZ2PaperLiteralLemma3_3Data
          (sigma := sigma)
          (strongLoss := strongLoss)
          (outputLoss := outputLoss)
          (restrictPaperShading
            (cover.fullFiberSubfamily
              ((cover.hitParentSubfamily heavy.selected).embedding
                parent))
            shading)
          ((cover.hitParentSubfamily heavy.selected).family.tube parent)
          hrho logExponent) where
  selectedFiberData :
    ∀ parent :
        Fin (cover.hitParentSubfamily heavy.selected).family.card,
      WZ2PaperLiteralLemma3_3Data
        (sigma := sigma)
        (strongLoss := strongLoss)
        (outputLoss := outputLoss)
        (restrictPaperShading
          ((cover.restrictToHitParents heavy.selected).fullFiberSubfamily
            parent)
          heavy.selectedShading)
        ((cover.hitParentSubfamily heavy.selected).family.tube parent)
        hrho logExponent
  parentwise :
    WZ2PaperLiteralParentwiseMergeData
      (cover.restrictToHitParents heavy.selected)
      heavy.selectedShading hrho logExponent selectedFiberData
  fiberReindex :
    ∀ parent :
        Fin (cover.hitParentSubfamily heavy.selected).family.card,
      WZ2PaperLiteralMergedFiberReindexData
        (cover.restrictToHitParents heavy.selected)
        heavy.selectedShading hrho logExponent
        selectedFiberData parentwise parent
  fiberOutputs :
    WZ2PaperLiteralMergedFiberOutputsData
      (cover.restrictToHitParents heavy.selected)
      heavy.selectedShading hrho logExponent
      selectedFiberData parentwise fiberReindex

def WZ2PaperCompleteParentwiseMergeStatement : Prop :=
  ∀ {delta rho sigma strongLoss outputLoss : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ (cover : WZ2PaperPartitioningCover fine coarse),
          ∀ (shading : WZ1PaperTubeShading fine),
            ∀ (heavy :
                WZ2PaperHeavyParentSelectionData cover shading),
              ∀ (hrho : 0 < rho),
                ∀ (logExponent : ℕ),
                  ∀ (ambientFiberData :
                      ∀ parent :
                          Fin
                            (cover.hitParentSubfamily
                              heavy.selected).family.card,
                        WZ2PaperLiteralLemma3_3Data
                          (sigma := sigma)
                          (strongLoss := strongLoss)
                          (outputLoss := outputLoss)
                          (restrictPaperShading
                            (cover.fullFiberSubfamily
                              ((cover.hitParentSubfamily
                                heavy.selected).embedding parent))
                            shading)
                          ((cover.hitParentSubfamily
                            heavy.selected).family.tube parent)
                          hrho logExponent),
                    Nonempty
                      (WZ2PaperCompleteParentwiseMergeData
                        cover shading heavy hrho logExponent
                        ambientFiberData)

end Kakeya.Assouad

end
