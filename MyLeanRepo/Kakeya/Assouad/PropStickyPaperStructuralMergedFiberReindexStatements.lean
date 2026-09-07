import MyLeanRepo.Kakeya.Assouad.PropStickyPaperStructuralParentwiseMergeStatements

/-!
# Reindex one structurally merged full fiber

After merging all structural one-parent refinements, the complete full fiber
of the restricted merged cover is a finite reindexing of the corresponding
local selected family.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperStructuralMergedFiberReindexData
    {delta rho sigma strongLoss outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (hrho : 0 < rho)
    (logExponent : ℕ)
    (fiberData :
      ∀ parent : Fin coarse.card,
        WZ2PaperLiteralLemma3_3StructuralData
          (sigma := sigma)
          (strongLoss := strongLoss)
          (outputLoss := outputLoss)
          (restrictPaperShading
            (cover.fullFiberSubfamily parent) shading)
          (coarse.tube parent) hrho logExponent)
    (merged :
      WZ2PaperStructuralParentwiseMergeData
        cover shading hrho logExponent fiberData)
    (parent : Fin coarse.card) where
  localIndex :
    Fin (merged.restrictedCover.fullFiberSubfamily parent).family.card →
      Fin (fiberData parent).refinement.selected.family.card
  localIndex_bijective :
    Function.Bijective localIndex
  tube_eq :
    ∀ index,
      (merged.restrictedCover.fullFiberSubfamily parent).family.tube
          index =
        (fiberData parent).refinement.selected.family.tube
          (localIndex index)
  carrier_eq :
    ∀ index,
      (restrictPaperShading
        (merged.restrictedCover.fullFiberSubfamily parent)
        merged.merged.refinement.refined).carrier index =
        (fiberData parent).refinement.refined.carrier
          (localIndex index)

def WZ2PaperStructuralMergedFiberReindexStatement : Prop :=
  ∀ {delta rho sigma strongLoss outputLoss : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ (cover : WZ2PaperPartitioningCover fine coarse),
          ∀ (shading : WZ1PaperTubeShading fine),
            ∀ (hrho : 0 < rho),
              ∀ (logExponent : ℕ),
                ∀ (fiberData :
                    ∀ parent : Fin coarse.card,
                      WZ2PaperLiteralLemma3_3StructuralData
                        (sigma := sigma)
                        (strongLoss := strongLoss)
                        (outputLoss := outputLoss)
                        (restrictPaperShading
                          (cover.fullFiberSubfamily parent) shading)
                        (coarse.tube parent) hrho logExponent),
                  ∀ (merged :
                      WZ2PaperStructuralParentwiseMergeData
                        cover shading hrho logExponent fiberData),
                    ∀ parent : Fin coarse.card,
                      Nonempty
                        (WZ2PaperStructuralMergedFiberReindexData
                          cover shading hrho logExponent
                          fiberData merged parent)

end Kakeya.Assouad

end
