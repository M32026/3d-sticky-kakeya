import MyLeanRepo.Kakeya.Assouad.WZ1.AnisotropicSelectedImageFrostman

/-!
# Balanced-fiber counting for Proposition 8.9

This module isolates the finite counting step used when transferring a source
strip estimate to the balanced coarse cells of an anisotropic rescaling.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/--
If every selected source in the fiber over a coarse point satisfying
`coarsePredicate` satisfies `sourcePredicate`, then the number of such coarse
points, weighted by the common lower fiber multiplicity, is bounded by the
number of selected sources satisfying `sourcePredicate`.
-/
lemma anisotropic_coarse_filter_card_le_selected_filter
    {E : DiscreteSet 2}
    {phi : Point2 ≃ᵃ[ℝ] Point2}
    {delta width epsilon_r : ℝ}
    {C : ENNReal}
    (rescale :
      WZ1AnisotropicFrostmanRescalingData
        E phi delta width epsilon_r C)
    (coarsePredicate sourcePredicate : Point2 → Prop)
    [DecidablePred coarsePredicate]
    [DecidablePred sourcePredicate]
    (hpullback :
      ∀ coarsePoint ∈ rescale.coarse,
        coarsePredicate coarsePoint →
          ∀ sourcePoint ∈ rescale.selected,
            rescale.assignment sourcePoint = coarsePoint →
              sourcePredicate sourcePoint) :
    (rescale.fiberMultiplicity : ENNReal) *
        ((rescale.coarse.filter coarsePredicate).card : ENNReal) ≤
      ((rescale.selected.filter sourcePredicate).card : ENNReal) := by
  classical
  let coarseFiltered : DiscreteSet 2 :=
    rescale.coarse.filter coarsePredicate
  let sourceFiltered : DiscreteSet 2 :=
    rescale.selected.filter sourcePredicate
  let fiber (coarsePoint : Point2) : DiscreteSet 2 :=
    rescale.selected.filter
      (fun sourcePoint =>
        rescale.assignment sourcePoint = coarsePoint)
  have hfiberSubset :
      ∀ coarsePoint ∈ coarseFiltered,
        fiber coarsePoint ⊆ sourceFiltered := by
    intro coarsePoint hcoarse sourcePoint hsource
    have hcoarse' := Finset.mem_filter.mp hcoarse
    have hsource' := Finset.mem_filter.mp hsource
    exact
      Finset.mem_filter.mpr
        ⟨hsource'.1,
          hpullback coarsePoint hcoarse'.1 hcoarse'.2
            sourcePoint hsource'.1 hsource'.2⟩
  have hfiberDisjoint :
      Set.PairwiseDisjoint
        (↑coarseFiltered : Set Point2) fiber := by
    intro first _ second _ hne
    change Disjoint (fiber first) (fiber second)
    rw [Finset.disjoint_left]
    intro source hfirst hsecond
    have hfirstAssignment :
        rescale.assignment source = first :=
      (Finset.mem_filter.mp hfirst).2
    have hsecondAssignment :
        rescale.assignment source = second :=
      (Finset.mem_filter.mp hsecond).2
    exact hne (hfirstAssignment.symm.trans hsecondAssignment)
  have hbiUnionSubset :
      coarseFiltered.biUnion fiber ⊆ sourceFiltered := by
    intro source hsource
    rcases Finset.mem_biUnion.mp hsource with
      ⟨coarsePoint, hcoarse, hsourceFiber⟩
    exact hfiberSubset coarsePoint hcoarse hsourceFiber
  have hcardUnion :
      (coarseFiltered.biUnion fiber).card =
        ∑ coarsePoint ∈ coarseFiltered,
          (fiber coarsePoint).card := by
    rw [Finset.card_biUnion hfiberDisjoint]
  calc
    (rescale.fiberMultiplicity : ENNReal) *
          ((rescale.coarse.filter coarsePredicate).card : ENNReal) =
        ∑ _coarsePoint ∈ coarseFiltered,
          (rescale.fiberMultiplicity : ENNReal) := by
      simp [coarseFiltered, mul_comm]
    _ ≤
        ∑ coarsePoint ∈ coarseFiltered,
          ((fiber coarsePoint).card : ENNReal) := by
      apply Finset.sum_le_sum
      intro coarsePoint hcoarse
      exact_mod_cast
        (rescale.fiber_comparable coarsePoint
          (Finset.mem_filter.mp hcoarse).1).1
    _ = ((coarseFiltered.biUnion fiber).card : ENNReal) := by
      exact_mod_cast hcardUnion.symm
    _ ≤ (sourceFiltered.card : ENNReal) := by
      exact_mod_cast Finset.card_le_card hbiUnionSubset
    _ =
        ((rescale.selected.filter sourcePredicate).card :
          ENNReal) := by
      rfl

end Kakeya.Assouad
