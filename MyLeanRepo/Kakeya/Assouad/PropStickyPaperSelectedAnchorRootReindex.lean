import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSelectedAnchorRootStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageAssemblyStatements

/-!
# Reindex one literal family by the selected-anchor full fiber

The unique full fiber of the singleton selected-anchor cover is merely a
finite reindexing of the selected source family.  Reindex the source map of a
literal unit-rescaled family while keeping its target family definitionally
unchanged.
-/

noncomputable section

namespace Kakeya.Assouad

noncomputable def
    WZ2PaperSelectedAnchorRootData.reindexLiteralFamily
    {delta sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {rootCoarse : Kakeya.Streamlined.TubeFamily sigma}
    {rootCover : WZ2PaperPartitioningCover fine rootCoarse}
    {anchor : Fin rootCoarse.card}
    {selected :
      Kakeya.Streamlined.TubeSubfamily
        (rootCover.fullFiberSubfamily anchor).family}
    (root : WZ2PaperSelectedAnchorRootData
      rootCover anchor selected)
    {hsigma : 0 < sigma}
    (literal :
      WZ2PaperLiteralUnitRescaledFamilyData
        selected.family (rootCoarse.tube anchor) hsigma) :
    WZ2PaperLiteralUnitRescaledFamilyData
      (root.cover.fullFiberSubfamily
        (wz2PaperSelectedAnchorRootIndex
          (rootCoarse.tube anchor))).family
      (rootCoarse.tube anchor) hsigma where
  targetFamily := literal.targetFamily
  sourceIndex := fun target =>
    root.sourceEquiv.symm (literal.sourceIndex target)
  sourceIndex_bijective := by
    constructor
    · intro first second heq
      apply literal.sourceIndex_bijective.1
      exact root.sourceEquiv.symm.injective heq
    · intro source
      rcases literal.sourceIndex_bijective.2
          (root.sourceEquiv source) with
        ⟨target, htarget⟩
      refine ⟨target, ?_⟩
      change root.sourceEquiv.symm (literal.sourceIndex target) = source
      rw [htarget]
      exact root.sourceEquiv.symm_apply_apply source
  target_line_class := literal.target_line_class
  target_axis := by
    intro target
    rw [literal.target_axis target]
    congr 2
    rw [
      (root.cover.fullFiberSubfamily
        (wz2PaperSelectedAnchorRootIndex
          (rootCoarse.tube anchor))).tube_eq,
      root.sourceEquiv_ambient
    ]
    simp

@[simp] theorem
    WZ2PaperSelectedAnchorRootData.reindexLiteralFamily_targetFamily
    {delta sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {rootCoarse : Kakeya.Streamlined.TubeFamily sigma}
    {rootCover : WZ2PaperPartitioningCover fine rootCoarse}
    {anchor : Fin rootCoarse.card}
    {selected :
      Kakeya.Streamlined.TubeSubfamily
        (rootCover.fullFiberSubfamily anchor).family}
    (root : WZ2PaperSelectedAnchorRootData
      rootCover anchor selected)
    {hsigma : 0 < sigma}
    (literal :
      WZ2PaperLiteralUnitRescaledFamilyData
        selected.family (rootCoarse.tube anchor) hsigma) :
    (root.reindexLiteralFamily literal).targetFamily =
      literal.targetFamily :=
  rfl

end Kakeya.Assouad

end
