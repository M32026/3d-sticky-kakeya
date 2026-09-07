import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricCoreUniformity

/-!
# Proposition 6.2 metric parents: saturated exact-scale restriction

A finite leaf set which is saturated for one strict parent map is exactly a
union of complete strict fibers.  Therefore the corresponding exact-scale
Definition 2.12 witness restricts with no CWA loss.  This is the only
restriction principle used for the old descendant schedule inside one metric
fiber.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

def pureWZ2Prop62SaturatedParents
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperPureScaleCoverData fine scale C)
    (indices : Finset (Fin fine.card)) :
    Finset (Fin data.coarse.card) :=
  indices.image data.cover.parent

theorem pureWZ2Prop62SaturatedParents_nonempty
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperPureScaleCoverData fine scale C)
    {indices : Finset (Fin fine.card)}
    (indicesNonempty : indices.Nonempty) :
    (pureWZ2Prop62SaturatedParents data indices).Nonempty := by
  rcases indicesNonempty with ⟨source, sourceMem⟩
  exact
    ⟨data.cover.parent source,
      Finset.mem_image.mpr ⟨source, sourceMem, rfl⟩⟩

noncomputable def pureWZ2Prop62SaturatedCompleteRestriction
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperPureScaleCoverData fine scale C)
    (indices : Finset (Fin fine.card))
    (indicesNonempty : indices.Nonempty) :
    PureWZ2CompleteParentRestrictionData
      data.cover (pureWZ2Prop62SaturatedParents data indices) :=
  PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
    data.cover (pureWZ2Prop62SaturatedParents data indices)
    (pureWZ2Prop62SaturatedParents_nonempty data indicesNonempty)

theorem pureWZ2Prop62SaturatedCompleteRestriction_indices_eq
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperPureScaleCoverData fine scale C)
    {indices : Finset (Fin fine.card)}
    (indicesNonempty : indices.Nonempty)
    (saturated :
      ∀ first second,
        data.cover.parent first = data.cover.parent second →
          (first ∈ indices ↔ second ∈ indices)) :
    (pureWZ2Prop62SaturatedCompleteRestriction
      data indices indicesNonempty).selectedFineIndices = indices := by
  ext source
  simp only [
    pureWZ2Prop62SaturatedCompleteRestriction,
    PureWZ2CompleteParentRestrictionData.selectedFineIndices,
    pureWZ2Prop62SaturatedParents,
    Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image
  ]
  constructor
  · rintro ⟨witness, witnessMem, parentEq⟩
    exact (saturated witness source parentEq).mp witnessMem
  · intro sourceMem
    exact ⟨source, sourceMem, rfl⟩

noncomputable def pureWZ2_prop62_restrictScaleToSaturated
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperPureScaleCoverData fine scale C)
    (indices : Finset (Fin fine.card))
    (indicesNonempty : indices.Nonempty)
    (saturated :
      ∀ first second,
        data.cover.parent first = data.cover.parent second →
          (first ∈ indices ↔ second ∈ indices)) :
    WZ2PaperPureScaleCoverData
      (WZ2PaperPureTubeSubfamily.fromFinset fine indices).family
      scale C := by
  let parents := pureWZ2Prop62SaturatedParents data indices
  let complete :=
    pureWZ2Prop62SaturatedCompleteRestriction
      data indices indicesNonempty
  let raw :=
    pureWZ2_prop62_completeParent_sameScale
      data parents
        (pureWZ2Prop62SaturatedParents_nonempty data indicesNonempty)
  have indicesEq :
      complete.selectedFineIndices = indices :=
    pureWZ2Prop62SaturatedCompleteRestriction_indices_eq
      data indicesNonempty saturated
  have familyEq :
      complete.selectedFine.family =
        (WZ2PaperPureTubeSubfamily.fromFinset fine indices).family := by
    change
      (WZ2PaperPureTubeSubfamily.fromFinset
        fine complete.selectedFineIndices).family =
        (WZ2PaperPureTubeSubfamily.fromFinset fine indices).family
    rw [indicesEq]
  exact familyEq ▸ raw

private theorem pureWZ2Prop62_parentCovers_cast
    {delta scale : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (familyEq : source = target)
    (data : WZ2PaperPureScaleCoverData source scale C)
    (parentCovers :
      ∀ index,
        WZ1PaperTubeCovers
          (source.tube index)
          (data.coarse.tube (data.cover.parent index))) :
    ∀ index : Fin target.card,
      WZ1PaperTubeCovers
        (target.tube index)
        ((familyEq ▸ data).coarse.tube
          ((familyEq ▸ data).cover.parent index)) := by
  subst target
  exact parentCovers

private theorem pureWZ2Prop62_coarseLine_cast
    {delta scale : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (familyEq : source = target)
    (data : WZ2PaperPureScaleCoverData source scale C)
    (coarseLine : WZ1PaperIsLineClass data.coarse) :
    WZ1PaperIsLineClass (familyEq ▸ data).coarse := by
  subst target
  exact coarseLine

private theorem pureWZ2Prop62_coarseSeparated_cast
    {delta scale : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (familyEq : source = target)
    (data : WZ2PaperPureScaleCoverData source scale C)
    (coarseSeparated :
      ∀ first second, first ≠ second →
        wz2PaperLiteralSourceSeparationFactor * scale <
          wz1PaperLineDistance
            (data.coarse.tube first) (data.coarse.tube second)) :
    ∀ first second, first ≠ second →
      wz2PaperLiteralSourceSeparationFactor * scale <
        wz1PaperLineDistance
          ((familyEq ▸ data).coarse.tube first)
          ((familyEq ▸ data).coarse.tube second) := by
  subst target
  exact coarseSeparated

/--
The synchronized strict line cover is preserved by a saturated exact-scale
restriction.
-/
theorem pureWZ2_prop62_restrictScaleToSaturated_parent_covers
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperPureScaleCoverData fine scale C)
    (indices : Finset (Fin fine.card))
    (indicesNonempty : indices.Nonempty)
    (saturated :
      ∀ first second,
        data.cover.parent first = data.cover.parent second →
          (first ∈ indices ↔ second ∈ indices))
    (parentCovers :
      ∀ source,
        WZ1PaperTubeCovers
          (fine.tube source)
          (data.coarse.tube (data.cover.parent source)))
    (source :
      Fin (WZ2PaperPureTubeSubfamily.fromFinset fine indices).family.card) :
    WZ1PaperTubeCovers
      ((WZ2PaperPureTubeSubfamily.fromFinset fine indices).family.tube
        source)
      ((pureWZ2_prop62_restrictScaleToSaturated
          data indices indicesNonempty saturated).coarse.tube
        ((pureWZ2_prop62_restrictScaleToSaturated
          data indices indicesNonempty saturated).cover.parent source)) := by
  let parents := pureWZ2Prop62SaturatedParents data indices
  let complete :=
    pureWZ2Prop62SaturatedCompleteRestriction
      data indices indicesNonempty
  let raw :=
    pureWZ2_prop62_completeParent_sameScale
      data parents
        (pureWZ2Prop62SaturatedParents_nonempty data indicesNonempty)
  have indicesEq :
      complete.selectedFineIndices = indices :=
    pureWZ2Prop62SaturatedCompleteRestriction_indices_eq
      data indicesNonempty saturated
  have familyEq :
      complete.selectedFine.family =
        (WZ2PaperPureTubeSubfamily.fromFinset fine indices).family := by
    change
      (WZ2PaperPureTubeSubfamily.fromFinset
        fine complete.selectedFineIndices).family =
        (WZ2PaperPureTubeSubfamily.fromFinset fine indices).family
    rw [indicesEq]
  have rawCovers :
      ∀ rawSource : Fin complete.selectedFine.family.card,
        WZ1PaperTubeCovers
          (complete.selectedFine.family.tube rawSource)
          (raw.coarse.tube (raw.cover.parent rawSource)) :=
    pureWZ2_prop62_completeParent_sameScale_parent_covers
      data parents
      (pureWZ2Prop62SaturatedParents_nonempty data indicesNonempty)
      parentCovers
  have finalEq :
      pureWZ2_prop62_restrictScaleToSaturated
          data indices indicesNonempty saturated =
        familyEq ▸ raw := by
    rfl
  rw [finalEq]
  exact
    pureWZ2Prop62_parentCovers_cast
      familyEq raw rawCovers source

/-- Coarse line class is preserved by a saturated restriction. -/
theorem pureWZ2_prop62_restrictScaleToSaturated_coarse_line_class
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperPureScaleCoverData fine scale C)
    (indices : Finset (Fin fine.card))
    (indicesNonempty : indices.Nonempty)
    (saturated :
      ∀ first second,
        data.cover.parent first = data.cover.parent second →
          (first ∈ indices ↔ second ∈ indices))
    (coarseLine : WZ1PaperIsLineClass data.coarse) :
    WZ1PaperIsLineClass
      (pureWZ2_prop62_restrictScaleToSaturated
        data indices indicesNonempty saturated).coarse := by
  let parents := pureWZ2Prop62SaturatedParents data indices
  let complete :=
    pureWZ2Prop62SaturatedCompleteRestriction
      data indices indicesNonempty
  let raw :=
    pureWZ2_prop62_completeParent_sameScale
      data parents
        (pureWZ2Prop62SaturatedParents_nonempty data indicesNonempty)
  have indicesEq :
      complete.selectedFineIndices = indices :=
    pureWZ2Prop62SaturatedCompleteRestriction_indices_eq
      data indicesNonempty saturated
  have familyEq :
      complete.selectedFine.family =
        (WZ2PaperPureTubeSubfamily.fromFinset fine indices).family := by
    change
      (WZ2PaperPureTubeSubfamily.fromFinset
        fine complete.selectedFineIndices).family =
        (WZ2PaperPureTubeSubfamily.fromFinset fine indices).family
    rw [indicesEq]
  have rawLine : WZ1PaperIsLineClass raw.coarse := by
    change
      WZ1PaperIsLineClass
        (data.cover.hitParentSubfamily complete.selectedFine).family
    exact coarseLine.subfamily
      (data.cover.hitParentSubfamily complete.selectedFine).toTubeSubfamily
  have finalEq :
      pureWZ2_prop62_restrictScaleToSaturated
          data indices indicesNonempty saturated =
        familyEq ▸ raw := by
    rfl
  rw [finalEq]
  exact pureWZ2Prop62_coarseLine_cast familyEq raw rawLine

/-- Fixed-factor coarse separation is preserved by a saturated restriction. -/
theorem pureWZ2_prop62_restrictScaleToSaturated_coarse_separated
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperPureScaleCoverData fine scale C)
    (indices : Finset (Fin fine.card))
    (indicesNonempty : indices.Nonempty)
    (saturated :
      ∀ first second,
        data.cover.parent first = data.cover.parent second →
          (first ∈ indices ↔ second ∈ indices))
    (coarseSeparated :
      ∀ first second, first ≠ second →
        wz2PaperLiteralSourceSeparationFactor * scale <
          wz1PaperLineDistance
            (data.coarse.tube first) (data.coarse.tube second)) :
    ∀ first second, first ≠ second →
      wz2PaperLiteralSourceSeparationFactor * scale <
        wz1PaperLineDistance
          ((pureWZ2_prop62_restrictScaleToSaturated
            data indices indicesNonempty saturated).coarse.tube first)
          ((pureWZ2_prop62_restrictScaleToSaturated
            data indices indicesNonempty saturated).coarse.tube second) := by
  let parents := pureWZ2Prop62SaturatedParents data indices
  let complete :=
    pureWZ2Prop62SaturatedCompleteRestriction
      data indices indicesNonempty
  let raw :=
    pureWZ2_prop62_completeParent_sameScale
      data parents
        (pureWZ2Prop62SaturatedParents_nonempty data indicesNonempty)
  have indicesEq :
      complete.selectedFineIndices = indices :=
    pureWZ2Prop62SaturatedCompleteRestriction_indices_eq
      data indicesNonempty saturated
  have familyEq :
      complete.selectedFine.family =
        (WZ2PaperPureTubeSubfamily.fromFinset fine indices).family := by
    change
      (WZ2PaperPureTubeSubfamily.fromFinset
        fine complete.selectedFineIndices).family =
        (WZ2PaperPureTubeSubfamily.fromFinset fine indices).family
    rw [indicesEq]
  let selectedCoarse :=
    data.cover.hitParentSubfamily complete.selectedFine
  have rawSeparated :
      ∀ first second : Fin raw.coarse.card, first ≠ second →
        wz2PaperLiteralSourceSeparationFactor * scale <
          wz1PaperLineDistance
            (raw.coarse.tube first) (raw.coarse.tube second) := by
    intro first second indexNe
    change
      wz2PaperLiteralSourceSeparationFactor * scale <
        wz1PaperLineDistance
          (selectedCoarse.family.tube first)
          (selectedCoarse.family.tube second)
    rw [selectedCoarse.tube_eq, selectedCoarse.tube_eq]
    exact coarseSeparated
      (selectedCoarse.embedding first)
      (selectedCoarse.embedding second)
      (selectedCoarse.embedding.injective.ne indexNe)
  have finalEq :
      pureWZ2_prop62_restrictScaleToSaturated
          data indices indicesNonempty saturated =
        familyEq ▸ raw := by
    rfl
  rw [finalEq]
  exact
    pureWZ2Prop62_coarseSeparated_cast
      familyEq raw rawSeparated

end Kakeya.Assouad

end
