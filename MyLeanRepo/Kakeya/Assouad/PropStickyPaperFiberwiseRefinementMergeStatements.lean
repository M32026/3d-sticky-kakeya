import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers

/-!
# Merge refinements selected independently in every full parent fiber

Paper step:

> “After refining the shadings `Y(T)`, we may suppose that for each collection
> `𝕋[Ṫ]`, the same number of tubes pass through each `δ`-cube ...”

The one-parent argument selects a genuine refinement inside each full
geometric fiber.  This finite assembly packages all of those selections as
one global paper refinement.  Its index equivalence records the parent and
local index of every globally selected tube, so later consumers can recover
the exact parentwise outputs rather than merely their union.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperFiberwiseRefinementMergeData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (logExponent : ℕ)
    (fiberRefinement :
      ∀ parent : Fin coarse.card,
        WZ1PaperRefinement
          (restrictPaperShading
            (cover.fullFiberSubfamily parent) shading)
          logExponent) where
  refinement : WZ1PaperRefinement shading logExponent
  indexEquiv :
    Fin refinement.selected.family.card ≃
      Σ parent : Fin coarse.card,
        Fin (fiberRefinement parent).selected.family.card
  selected_embedding_eq :
    ∀ index,
      refinement.selected.embedding index =
        (cover.fullFiberSubfamily (indexEquiv index).1).embedding
          ((fiberRefinement (indexEquiv index).1).selected.embedding
            (indexEquiv index).2)
  refined_carrier_eq :
    ∀ index,
      refinement.refined.carrier index =
        (fiberRefinement (indexEquiv index).1).refined.carrier
          (indexEquiv index).2
  selected_card_eq :
    refinement.selected.family.card =
      ∑ parent : Fin coarse.card,
        (fiberRefinement parent).selected.family.card
  refined_mass_eq :
    refinement.refined.mass =
      ∑ parent : Fin coarse.card,
        (fiberRefinement parent).refined.mass
  refined_cubical :
    (∀ parent,
      WZ1PaperIsCubicalShading (fiberRefinement parent).refined) →
      WZ1PaperIsCubicalShading refinement.refined
  refined_nonempty :
    (∀ parent index,
      ((fiberRefinement parent).refined.carrier index).Nonempty) →
      ∀ index, (refinement.refined.carrier index).Nonempty

def WZ2PaperFiberwiseRefinementMergeStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ (cover : WZ2PaperPartitioningCover fine coarse),
          ∀ (shading : WZ1PaperTubeShading fine),
            ∀ (logExponent : ℕ),
              ∀ (fiberRefinement :
                ∀ parent : Fin coarse.card,
                  WZ1PaperRefinement
                    (restrictPaperShading
                      (cover.fullFiberSubfamily parent) shading)
                    logExponent),
                Nonempty
                  (WZ2PaperFiberwiseRefinementMergeData
                    cover shading logExponent fiberRefinement)

end Kakeya.Assouad

end
