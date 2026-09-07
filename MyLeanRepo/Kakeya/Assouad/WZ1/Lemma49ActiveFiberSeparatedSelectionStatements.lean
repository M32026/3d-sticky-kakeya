import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49ActiveViewpoint

/-!
# Separated actual-fiber selection for WZ1 Lemma 49

The paper selects a separated subset of one actual active `G₁` fiber before
forming radial directions.  This interface keeps the viewpoint, source fiber,
and source triples fixed.
-/

namespace Kakeya.Assouad

/-- Output of maximal separated selection on the actual active fiber. -/
structure WZ1Lemma49ActiveFiberSeparatedSelectionData
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {density C : ENNReal}
    {base direction : Point2}
    {width activeWidth u : ℝ}
    (viewpoint :
      WZ1Lemma49ActiveViewpointData
        F G₁ G₂ H density base direction width activeWidth) where
  selected : DiscreteSet 2
  selected_subset : selected ⊆ viewpoint.source
  selected_nonempty : selected.Nonempty
  separated : selected.IsDeltaSeparated u
  covers_source :
    ∀ point ∈ viewpoint.source,
      ∃ selectedPoint ∈ selected, dist point selectedPoint < u
  actual :
    ∀ second ∈ selected,
      (viewpoint.sourceEdge.1, second, viewpoint.viewpoint) ∈ H
  cardinality :
    density ≤
      C * Kakeya.realRpowENN u 1 * selected.enncard

/--
Extract a separated subset from the supplied actual active fiber.

The cardinality estimate is the normalized form of
`#source ≤ #selected * C * u * #G₁`, combined with the active-fiber density
lower bound.  No radial direction set is introduced at this stage.
-/
def WZ1Lemma49ActiveFiberSeparatedSelectionStatement : Prop :=
  ∀ {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {density C : ENNReal}
    {base direction : Point2}
    {width activeWidth delta u : ℝ},
    ∀ viewpoint :
      WZ1Lemma49ActiveViewpointData
        F G₁ G₂ H density base direction width activeWidth,
      0 < delta →
      delta ≤ u →
      u ≤ 1 →
      G₁.IsFrostman delta 1 C →
        Nonempty
          (WZ1Lemma49ActiveFiberSeparatedSelectionData
            (C := C) (u := u) viewpoint)

end Kakeya.Assouad
