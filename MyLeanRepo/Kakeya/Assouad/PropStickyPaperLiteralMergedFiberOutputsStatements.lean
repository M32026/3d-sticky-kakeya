import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralMergedFiberReindexStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralOneParentReindexStatements

/-!
# Literal one-parent outputs on the merged global cover

For each retained parent, reindex its local literal one-parent output onto the
exact full fiber of the globally merged and restricted cover.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperLiteralMergedFiberOutputsData
    {delta rho sigma strongLoss outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (hrho : 0 < rho)
    (logExponent : ℕ)
    (fiberData :
      ∀ parent : Fin coarse.card,
        WZ2PaperLiteralLemma3_3Data
          (sigma := sigma)
          (strongLoss := strongLoss)
          (outputLoss := outputLoss)
          (restrictPaperShading
            (cover.fullFiberSubfamily parent) shading)
          (coarse.tube parent)
          hrho
          logExponent)
    (merged :
      WZ2PaperLiteralParentwiseMergeData
        cover shading hrho logExponent fiberData)
    (fiberReindex :
      ∀ parent : Fin coarse.card,
        WZ2PaperLiteralMergedFiberReindexData
          cover shading hrho logExponent
          fiberData merged parent) where
  globalFiberData :
    ∀ parent : Fin coarse.card,
      WZ2PaperLiteralLemma3_3Data
        (sigma := sigma)
        (strongLoss := strongLoss)
        (outputLoss := outputLoss)
        (restrictPaperShading
          (merged.restrictedCover.fullFiberSubfamily parent)
          merged.merged.refinement.refined)
        (coarse.tube parent)
        hrho
        logExponent

def WZ2PaperLiteralMergedFiberOutputsStatement : Prop :=
  WZ2PaperLiteralOneParentReindexStatement →
  ∀ {delta rho sigma strongLoss outputLoss : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ (cover : WZ2PaperPartitioningCover fine coarse),
          ∀ (shading : WZ1PaperTubeShading fine),
            ∀ (hrho : 0 < rho),
              ∀ (logExponent : ℕ),
                ∀ (fiberData :
                    ∀ parent : Fin coarse.card,
                      WZ2PaperLiteralLemma3_3Data
                        (sigma := sigma)
                        (strongLoss := strongLoss)
                        (outputLoss := outputLoss)
                        (restrictPaperShading
                          (cover.fullFiberSubfamily parent) shading)
                        (coarse.tube parent)
                        hrho
                        logExponent),
                  ∀ (merged :
                      WZ2PaperLiteralParentwiseMergeData
                        cover shading hrho logExponent fiberData),
                    ∀ (fiberReindex :
                        ∀ parent : Fin coarse.card,
                          WZ2PaperLiteralMergedFiberReindexData
                            cover shading hrho logExponent
                            fiberData merged parent),
                      Nonempty
                        (WZ2PaperLiteralMergedFiberOutputsData
                          cover shading hrho logExponent
                          fiberData merged fiberReindex)

end Kakeya.Assouad

end
