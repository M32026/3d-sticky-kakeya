import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CompleteParentScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PreliminaryCoreRetention

/-!
# Proposition 6.2 metric parents: complete structural color class

The structural color vector is chosen before the leaf-weight dyadic bin.  If
every structural coordinate is constant on each old strict packet, then its
full color class is exactly a union of complete old packets.  This module
identifies that color class with the canonical complete-parent restriction.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62PreliminarySelectionData

variable
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData fine scale C}
    {coordinateCount : ℕ}
    {Color : Fin coordinateCount → Type*}
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    {color : ∀ coordinate, Fin fine.card → Color coordinate}
    {weight : Fin fine.card → ENNReal}
    (preliminary :
      PureWZ2Prop62PreliminarySelectionData
        coordinateCount Color color weight)

theorem colorClass_nonempty :
    preliminary.colorClass.Nonempty := by
  rcases preliminary.selected_nonempty with ⟨source, sourceMem⟩
  exact ⟨source, preliminary.selected_subset_colorClass sourceMem⟩

def selectedOldParents : Finset (Fin oldData.coarse.card) :=
  preliminary.colorClass.image oldData.cover.parent

theorem selectedOldParents_nonempty :
    preliminary.selectedOldParents (oldData := oldData) |>.Nonempty := by
  rcases preliminary.colorClass_nonempty with ⟨source, sourceMem⟩
  exact
    ⟨oldData.cover.parent source,
      Finset.mem_image.mpr ⟨source, sourceMem, rfl⟩⟩

theorem colorClass_parent_saturated
    (color_parent_invariant :
      ∀ coordinate first second,
        oldData.cover.parent first = oldData.cover.parent second →
          color coordinate first = color coordinate second) :
    ∀ first second,
      oldData.cover.parent first = oldData.cover.parent second →
        (first ∈ preliminary.colorClass ↔
          second ∈ preliminary.colorClass) := by
  intro first second parentEq
  rw [preliminary.colorClass_eq]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro firstColor coordinate
    exact
      (color_parent_invariant coordinate first second parentEq).symm.trans
        (firstColor coordinate)
  · intro secondColor coordinate
    exact
      (color_parent_invariant coordinate first second parentEq).trans
        (secondColor coordinate)

noncomputable def completeColorClass :
    PureWZ2CompleteParentRestrictionData
      oldData.cover
      (preliminary.selectedOldParents (oldData := oldData)) :=
  PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
    oldData.cover
    (preliminary.selectedOldParents (oldData := oldData))
    preliminary.selectedOldParents_nonempty

theorem completeColorClass_selectedFineIndices_eq
    (color_parent_invariant :
      ∀ coordinate first second,
        oldData.cover.parent first = oldData.cover.parent second →
          color coordinate first = color coordinate second) :
    (preliminary.completeColorClass
      (oldData := oldData)).selectedFineIndices =
        preliminary.colorClass := by
  ext source
  simp only [
    PureWZ2CompleteParentRestrictionData.selectedFineIndices,
    Finset.mem_filter, Finset.mem_univ, true_and,
    selectedOldParents, Finset.mem_image
  ]
  constructor
  · rintro ⟨witness, witnessMem, parentEq⟩
    exact
      (preliminary.colorClass_parent_saturated
        color_parent_invariant witness source parentEq).mp witnessMem
  · intro sourceMem
    exact ⟨source, sourceMem, rfl⟩

theorem completeColorClass_selectedFine_card_eq
    (color_parent_invariant :
      ∀ coordinate first second,
        oldData.cover.parent first = oldData.cover.parent second →
          color coordinate first = color coordinate second) :
    (preliminary.completeColorClass
        (oldData := oldData)).selectedFine.family.card =
      preliminary.colorClass.card := by
  change
    (preliminary.completeColorClass
      (oldData := oldData)).selectedFineIndices.card =
        preliminary.colorClass.card
  rw [preliminary.completeColorClass_selectedFineIndices_eq
    color_parent_invariant]

end PureWZ2Prop62PreliminarySelectionData

end Kakeya.Assouad

end
