import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralParentwiseMergeStatements

/-!
# Reindex one merged full fiber to its local refinement

After merging all parentwise source refinements, the exact full fiber of the
restricted global cover over a parent is a finite reindexing of that parent's
local selected family.  This record exposes the bijection together with exact
tube and shaded-carrier equalities.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperLiteralMergedFiberReindexData
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

def WZ2PaperLiteralMergedFiberReindexStatement : Prop :=
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
                    ∀ parent : Fin coarse.card,
                      Nonempty
                        (WZ2PaperLiteralMergedFiberReindexData
                          cover shading hrho logExponent
                          fiberData merged parent)

end Kakeya.Assouad

end
