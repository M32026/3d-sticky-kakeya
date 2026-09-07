import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers

/-!
# Singleton anchor root for one selected full-fiber subfamily

After the simultaneous finite-scale selection, every retained source tube is
still contained in the same original `sigma`-fiber.  Package that fact as a
literal partitioning cover whose unique coarse tube is the original anchor.

This is finite provenance only.  It does not assert Convex-Wolff inheritance.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The singleton indexed family containing one supplied paper anchor. -/
def wz2PaperSelectedAnchorRootFamily
    {sigma : ℝ} (anchor : Kakeya.DeltaTube sigma) :
    Kakeya.Streamlined.TubeFamily sigma where
  card := 1
  tube := fun _ => anchor

/-- The unique index of a selected-anchor singleton family. -/
def wz2PaperSelectedAnchorRootIndex
    {sigma : ℝ} (anchor : Kakeya.DeltaTube sigma) :
    Fin (wz2PaperSelectedAnchorRootFamily anchor).card :=
  ⟨0, by
    change 0 < 1
    norm_num⟩

structure WZ2PaperSelectedAnchorRootData
    {delta sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {rootCoarse : Kakeya.Streamlined.TubeFamily sigma}
    (rootCover : WZ2PaperPartitioningCover fine rootCoarse)
    (anchor : Fin rootCoarse.card)
    (selected :
      Kakeya.Streamlined.TubeSubfamily
        (rootCover.fullFiberSubfamily anchor).family) where
  cover :
    WZ2PaperPartitioningCover
      selected.family
      (wz2PaperSelectedAnchorRootFamily
        (rootCoarse.tube anchor))
  all_parent :
    ∀ source,
      cover.parent source =
        wz2PaperSelectedAnchorRootIndex
          (rootCoarse.tube anchor)
  fiber_all :
    wz2PaperFullFiberIndices
        selected.family
        (wz2PaperSelectedAnchorRootFamily
          (rootCoarse.tube anchor))
        (wz2PaperSelectedAnchorRootIndex
          (rootCoarse.tube anchor)) =
      Finset.univ
  sourceEquiv :
    Fin
        ((cover.fullFiberSubfamily
          (wz2PaperSelectedAnchorRootIndex
            (rootCoarse.tube anchor))).family.card) ≃
      Fin selected.family.card
  sourceEquiv_ambient :
    ∀ source,
      (cover.fullFiberSubfamily
          (wz2PaperSelectedAnchorRootIndex
            (rootCoarse.tube anchor))).embedding source =
        sourceEquiv source
  coarse_line_class :
    WZ1PaperIsLineClass
      (wz2PaperSelectedAnchorRootFamily
        (rootCoarse.tube anchor))
  coarse_essentially_distinct :
    WZ1PaperIsEssentiallyDistinct
      (wz2PaperSelectedAnchorRootFamily
        (rootCoarse.tube anchor))

def WZ2PaperSelectedAnchorRootStatement : Prop :=
  ∀ {delta sigma : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {rootCoarse :
          Kakeya.Streamlined.TubeFamily sigma},
        ∀ (rootCover :
            WZ2PaperPartitioningCover fine rootCoarse),
          ∀ (anchor : Fin rootCoarse.card),
            WZ1PaperIsLineClass rootCoarse →
            ∀ (selected :
                Kakeya.Streamlined.TubeSubfamily
                  (rootCover.fullFiberSubfamily anchor).family),
              0 < selected.family.card →
                Nonempty
                  (WZ2PaperSelectedAnchorRootData
                    rootCover anchor selected)

end Kakeya.Assouad

end
