import MyLeanRepo.Kakeya.Streamlined.FlatPrismFactoring.FromSection5AndPlankEstimates.UniformFiberOccupancy

/-!
# Helper lemmas for uniform fiber-occupancy selection

Elementary facts about factoring fibers: nonemptiness, cardinality bounds,
mass partition, and selected preimage mass identity.
-/

noncomputable section

open MeasureTheory Set Finset
open scoped Classical

namespace Kakeya.Streamlined

/-- Every factoring fiber is nonempty because `P.parent` is surjective. -/
lemma factoring_fiber_nonempty {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (j : Fin coarse.card) :
    (P.fiberIndices j).Nonempty := by
  have hsurj : ∃ i : Fin fine.card, P.parent i = j :=
    P.parent_surjective j
  rcases hsurj with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  simp only [Factoring.fiberIndices, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact hi

/-- Every factoring fiber has cardinality between 1 and `fine.card`. -/
lemma factoring_fiber_card_bounds {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (j : Fin coarse.card) :
    1 ≤ (P.fiberIndices j).card ∧
      (P.fiberIndices j).card ≤ fine.card := by
  have h_nonempty : (P.fiberIndices j).Nonempty :=
    factoring_fiber_nonempty P j
  have h1 : 1 ≤ (P.fiberIndices j).card :=
    Finset.Nonempty.card_pos h_nonempty
  have h2 : (P.fiberIndices j).card ≤ fine.card := by
    have h_sub :
        P.fiberIndices j ⊆
          (Finset.univ : Finset (Fin fine.card)) :=
      Finset.subset_univ _
    have h :
        (P.fiberIndices j).card ≤
          (Finset.univ : Finset (Fin fine.card)).card :=
      Finset.card_le_card h_sub
    simpa using h
  exact ⟨h1, h2⟩

/-- The fiber masses partition the total fine mass. -/
lemma factoring_mass_partition {fine coarse : BodyFamily}
    (P : Factoring fine coarse) :
    ∑ j : Fin coarse.card, P.fiberMass j = fine.mass := by
  have h_disj :
      Set.Pairwise (Finset.univ : Finset (Fin coarse.card))
        (fun j1 j2 =>
          Disjoint (P.fiberIndices j1) (P.fiberIndices j2)) := by
    intro j1 _ j2 _ hne
    simp only [Factoring.fiberIndices, Finset.disjoint_left,
      Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi1 hi2
    have h1 : P.parent i = j1 := hi1
    have h2 : P.parent i = j2 := hi2
    rw [h1] at h2
    exact hne h2
  have h_bij :
      ∀ i : Fin fine.card, i ∈ P.fiberIndices (P.parent i) := by
    intro i
    simp [Factoring.fiberIndices]
  have h_univ :
      Finset.biUnion
          (Finset.univ : Finset (Fin coarse.card))
          P.fiberIndices =
        (Finset.univ : Finset (Fin fine.card)) := by
    apply Finset.eq_univ_of_forall
    intro i
    exact Finset.mem_biUnion.mpr
      ⟨P.parent i, by simp, h_bij i⟩
  calc
    ∑ j : Fin coarse.card, P.fiberMass j =
        ∑ j : Fin coarse.card,
          ∑ i ∈ P.fiberIndices j, (fine.body i).volume := by
      rfl
    _ =
        ∑ i ∈ Finset.biUnion
            (Finset.univ : Finset (Fin coarse.card))
            P.fiberIndices,
          (fine.body i).volume := by
      rw [Finset.sum_biUnion h_disj]
    _ =
        ∑ i ∈ (Finset.univ : Finset (Fin fine.card)),
          (fine.body i).volume := by
      rw [h_univ]
    _ = fine.mass := by
      simp [BodyFamily.mass]

/--
The mass of the full preimage of a selected coarse set equals the sum of
the selected fiber masses.
-/
lemma selected_fine_mass_eq_sum_fiber_mass
    {fine coarse : BodyFamily}
    (P : Factoring fine coarse)
    (selected : Finset (Fin coarse.card)) :
    ∑ i ∈ P.selectedFineIndices selected, (fine.body i).volume =
      ∑ j ∈ selected, P.fiberMass j := by
  have h_disj :
      Set.Pairwise selected
        (fun j1 j2 =>
          Disjoint (P.fiberIndices j1) (P.fiberIndices j2)) := by
    intro j1 _ j2 _ hne
    simp only [Factoring.fiberIndices, Finset.disjoint_left,
      Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi1 hi2
    have h1 : P.parent i = j1 := hi1
    have h2 : P.parent i = j2 := hi2
    rw [h1] at h2
    exact hne h2
  have h_eq :
      P.selectedFineIndices selected =
        Finset.biUnion selected P.fiberIndices := by
    ext i
    simp only [Factoring.selectedFineIndices, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro h
      exact ⟨P.parent i, h, by simp [Factoring.fiberIndices]⟩
    · rintro ⟨j, hj, hji⟩
      have h : P.parent i = j := by
        simpa [Factoring.fiberIndices, Finset.mem_filter] using hji
      rw [h]
      exact hj
  rw [h_eq, Finset.sum_biUnion h_disj]
  rfl

/-- Arbitrary weights on a full selected parent preimage partition fiberwise.
This is the weighted form used when zero-shaded complete fibers are removed
after an occupancy selection. -/
lemma selected_fine_weight_eq_sum_fiber_weight
    {fine coarse : BodyFamily}
    (P : Factoring fine coarse)
    (selected : Finset (Fin coarse.card))
    (weight : Fin fine.card → ENNReal) :
    ∑ i ∈ P.selectedFineIndices selected, weight i =
      ∑ j ∈ selected, ∑ i ∈ P.fiberIndices j, weight i := by
  have h_disj :
      Set.Pairwise selected
        (fun first second =>
          Disjoint (P.fiberIndices first) (P.fiberIndices second)) := by
    intro first _ second _ hne
    rw [Finset.disjoint_left]
    intro i hfirst hsecond
    have h1 : P.parent i = first := by
      simpa [Factoring.fiberIndices] using hfirst
    have h2 : P.parent i = second := by
      simpa [Factoring.fiberIndices] using hsecond
    exact hne (h1.symm.trans h2)
  have h_union : P.selectedFineIndices selected =
      selected.biUnion P.fiberIndices := by
    ext i
    simp [Factoring.selectedFineIndices, Factoring.fiberIndices]
  rw [h_union, Finset.sum_biUnion h_disj]

end Kakeya.Streamlined
