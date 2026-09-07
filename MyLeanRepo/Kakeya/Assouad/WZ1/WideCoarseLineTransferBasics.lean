import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseSplitStatements

/-!
# Basic cardinality and provenance for wide coarse line transfer

These are the paper-faithful parts of the #3121 checkpoint that remain useful
independently of the failed raw-only exponent absorption:

* balanced source cardinality is at most twice the common fiber multiplicity
  times the number of occupied coarse cells;
* the two sequentially selected endpoint classes remain subsets of the
  endpoint classes in the common-strip package.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/--
The upper half of balanced-cell comparability, summed over all occupied
coarse cells.
-/
lemma anisotropic_selected_card_le_two_fiber_coarse
    {E : DiscreteSet 2}
    {phi : Point2 ≃ᵃ[ℝ] Point2}
    {delta width epsilon_r : ℝ}
    {constant : ENNReal}
    (rescale :
      WZ1AnisotropicFrostmanRescalingData
        E phi delta width epsilon_r constant) :
    rescale.selected.enncard ≤
      (2 : ENNReal) *
        (rescale.fiberMultiplicity : ENNReal) *
        rescale.coarse.enncard := by
  classical
  let fiber (coarsePoint : Point2) : DiscreteSet 2 :=
    rescale.selected.filter
      (fun sourcePoint =>
        rescale.assignment sourcePoint = coarsePoint)
  have hcover :
      rescale.selected =
        rescale.coarse.biUnion fiber := by
    ext sourcePoint
    simp only [Finset.mem_biUnion, fiber, Finset.mem_filter]
    constructor
    · intro hsource
      exact
        ⟨rescale.assignment sourcePoint,
          rescale.assignment_mem sourcePoint hsource,
          hsource, rfl⟩
    · rintro ⟨_coarsePoint, _hcoarse, hsource, _⟩
      exact hsource
  have hdisjoint :
      Set.PairwiseDisjoint
        (↑rescale.coarse : Set Point2) fiber := by
    intro first _ second _ hne
    simp only [Finset.disjoint_left, fiber, Finset.mem_filter]
    intro source hfirst hsecond
    exact
      hne
        (hfirst.2.symm.trans hsecond.2)
  have hcard :
      rescale.selected.card =
        ∑ coarsePoint ∈ rescale.coarse,
          (fiber coarsePoint).card := by
    rw [hcover, Finset.card_biUnion hdisjoint]
  calc
    rescale.selected.enncard =
        ∑ coarsePoint ∈ rescale.coarse,
          ((fiber coarsePoint).card : ENNReal) := by
      rw [show rescale.selected.enncard =
        (rescale.selected.card : ENNReal) by rfl, hcard,
        Nat.cast_sum]
    _ ≤
        ∑ _coarsePoint ∈ rescale.coarse,
          ((2 * rescale.fiberMultiplicity : ℕ) : ENNReal) := by
      apply Finset.sum_le_sum
      intro coarsePoint hcoarsePoint
      exact_mod_cast
        (rescale.fiber_comparable
          coarsePoint hcoarsePoint).2
    _ =
        (2 : ENNReal) *
          (rescale.fiberMultiplicity : ENNReal) *
          rescale.coarse.enncard := by
      simp [Finset.sum_const, DiscreteSet.enncard,
        mul_assoc, mul_comm, mul_left_comm]

/-- The first sequential endpoint selection retains original `G₁` provenance. -/
lemma first_rescale_selected_subset_selectedG1
    {delta epsilon eta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {sequential :
      WZ1Proposition8_9WideSequentialRescalingData
        delta epsilon eta parameters F G₁ G₂ H data} :
    sequential.firstRescale.selected ⊆ data.selectedG₁ := by
  exact
    sequential.firstRescale.selected_subset.trans
      (active_triple_projection_subset data.uniform 1)

/-- The second sequential endpoint selection retains original `G₂` provenance. -/
lemma second_rescale_selected_subset_selectedG2
    {delta epsilon eta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {sequential :
      WZ1Proposition8_9WideSequentialRescalingData
        delta epsilon eta parameters F G₁ G₂ H data} :
    sequential.secondRescale.selected ⊆ data.selectedG₂ := by
  exact
    sequential.secondRescale.selected_subset.trans
      (active_triple_projection_subset
        sequential.firstUniform 2)

end Kakeya.Assouad
