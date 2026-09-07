import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFiberwiseRefinementMergeStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralOneParentStatements

/-!
# Merge literal one-parent outputs over all retained parents

Each retained coarse parent supplies a literal one-parent output whose source
is the exact full fiber of the same geometric cover.  Merge the source
refinements and restrict the geometric cover to the globally selected fine
family.  Nonemptiness of every local refinement makes the restricted parent
map surjective.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperLiteralParentwiseMergeData
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
          logExponent) where
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
        cover.parent
          (merged.refinement.selected.embedding index)
  refined_cubical :
    WZ1PaperIsCubicalShading merged.refinement.refined
  refined_nonempty :
    ∀ index, (merged.refinement.refined.carrier index).Nonempty
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

def WZ2PaperLiteralParentwiseMergeStatement : Prop :=
  WZ2PaperFiberwiseRefinementMergeStatement →
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
                Nonempty
                  (WZ2PaperLiteralParentwiseMergeData
                    cover shading hrho logExponent fiberData)

end Kakeya.Assouad

end
