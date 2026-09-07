import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFiberwiseRefinementMergeStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralOneParentStructuralStatements

/-!
# Parentwise merge of structural one-parent outputs

Every complete geometric parent supplies the paper-faithful structural half
of Lemma 3.3.  Merge those source refinements before any global balancing or
multiplicity comparison.  No parent is assumed extremal at this stage.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperStructuralParentwiseMergeData
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
          (coarse.tube parent) hrho logExponent) where
  merged :
    WZ2PaperFiberwiseRefinementMergeData
      cover shading logExponent
      (fun parent => (fiberData parent).refinement)
  restrictedCover :
    WZ2PaperPartitioningCover
      merged.refinement.selected.family coarse
  restricted_parent_eq :
    ∀ index,
      restrictedCover.parent index =
        cover.parent (merged.refinement.selected.embedding index)
  refined_cubical :
    WZ1PaperIsCubicalShading merged.refinement.refined
  selected_embedding_eq :
    ∀ index,
      merged.refinement.selected.embedding index =
        (cover.fullFiberSubfamily (merged.indexEquiv index).1).embedding
          ((fiberData
              (merged.indexEquiv index).1).refinement.selected.embedding
            (merged.indexEquiv index).2)
  refined_carrier_eq :
    ∀ index,
      merged.refinement.refined.carrier index =
        (fiberData
            (merged.indexEquiv index).1).refinement.refined.carrier
          (merged.indexEquiv index).2

def WZ2PaperStructuralParentwiseMergeStatement : Prop :=
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
                  Nonempty
                    (WZ2PaperStructuralParentwiseMergeData
                      cover shading hrho logExponent fiberData)

end Kakeya.Assouad

end
