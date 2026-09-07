import MyLeanRepo.Kakeya.Assouad.WZ1.PaperPackingRefinement

/-!
# Finite complete-parent selection for Proposition 6.3

At each of finitely many nearby scales we discard whole assigned parent
fibers until the retained parent set is separated.  This is the standard
weighted greedy step in the proof of stability of the Convex Wolff axioms;
it never replaces a fiber by a singleton.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open scoped ENNReal

attribute [local instance] Classical.propDecidable

structure Proposition63FiniteStrongParentSelectionData
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (weight : Index → ENNReal)
    (scaleCount : ℕ)
    (Parent : Fin scaleCount → Type*)
    [∀ coordinate, Fintype (Parent coordinate)]
    [∀ coordinate, DecidableEq (Parent coordinate)]
    (parent : ∀ coordinate, Index → Parent coordinate)
    (conflict : ∀ coordinate, Parent coordinate → Parent coordinate → Prop)
    (degree : ℕ) where
  selected : Finset Index
  retained_weight :
    (∑ index : Index, weight index) ≤
      (degree : ENNReal) ^ scaleCount *
        ∑ index ∈ selected, weight index
  hit_parent_separated :
    ∀ coordinate,
      ∀ first second : Parent coordinate,
        first ≠ second →
        (∃ index ∈ selected, parent coordinate index = first) →
        (∃ index ∈ selected, parent coordinate index = second) →
        ¬ conflict coordinate first second

private lemma proposition63_one_step_complete_parent_selection
    {Index Parent : Type*}
    [Fintype Index] [DecidableEq Index]
    [Fintype Parent] [DecidableEq Parent]
    (weight : Index → ENNReal)
    (selected : Finset Index)
    (parent : Index → Parent)
    (conflict : Parent → Parent → Prop)
    (degree : ℕ)
    (hrefl : ∀ value, conflict value value)
    (hsymm : ∀ first second, conflict first second → conflict second first)
    (hdegree : ∀ value,
      ((Finset.univ : Finset Parent).filter
        (conflict value)).card ≤ degree) :
    ∃ further : Finset Index,
      further ⊆ selected ∧
      (∑ index ∈ selected, weight index) ≤
        (degree : ENNReal) * ∑ index ∈ further, weight index ∧
      ∀ first second : Parent,
        first ≠ second →
        (∃ index ∈ further, parent index = first) →
        (∃ index ∈ further, parent index = second) →
        ¬ conflict first second := by
  let parentWeight : Parent → ENNReal := fun value =>
    ∑ index ∈ selected.filter (fun index => parent index = value),
      weight index
  rcases exists_independent_set_mass_retention
      parentWeight conflict hrefl hsymm degree hdegree with
    ⟨independent, hindependent, hmass⟩
  let further := selected.filter fun index => parent index ∈ independent
  have hfurtherSubset : further ⊆ selected := by
    intro index hindex
    exact (Finset.mem_filter.mp hindex).1
  have htotal :
      (∑ value : Parent, parentWeight value) =
        ∑ index ∈ selected, weight index := by
    simpa [parentWeight] using
      (Finset.sum_fiberwise selected parent weight)
  have hselected :
      (∑ value ∈ independent, parentWeight value) =
        ∑ index ∈ further, weight index := by
    dsimp only [parentWeight, further]
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro index hindex
    by_cases hmem : parent index ∈ independent
    · rw [if_pos hmem]
      rw [Finset.sum_eq_single (parent index)]
      · exact if_pos rfl
      · intro value hvalue hne
        exact if_neg (Ne.symm hne)
      · exact fun hnot => (hnot hmem).elim
    · rw [if_neg hmem]
      apply Finset.sum_eq_zero
      intro value hvalue
      rw [if_neg]
      intro heq
      exact hmem (heq ▸ hvalue)
  have hretained :
      (∑ index ∈ selected, weight index) ≤
        (degree : ENNReal) * ∑ index ∈ further, weight index := by
    rw [← htotal, ← hselected]
    exact hmass
  refine ⟨further, hfurtherSubset, hretained, ?_⟩
  intro first second hne hfirst hsecond
  rcases hfirst with ⟨firstIndex, hfirstIndex, hfirstParent⟩
  rcases hsecond with ⟨secondIndex, hsecondIndex, hsecondParent⟩
  have hfirstMem : first ∈ independent := by
    have h := (Finset.mem_filter.mp hfirstIndex).2
    simpa [hfirstParent] using h
  have hsecondMem : second ∈ independent := by
    have h := (Finset.mem_filter.mp hsecondIndex).2
    simpa [hsecondParent] using h
  exact hindependent first hfirstMem second hsecondMem hne

universe u in
private lemma proposition63_finite_complete_parent_selection_induction
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (weight : Index → ENNReal) (initial : Finset Index) :
    ∀ (scaleCount : ℕ),
      ∀ (Parent : Fin scaleCount → Type u),
        ∀ [hParentFintype : ∀ coordinate, Fintype (Parent coordinate)],
          ∀ [hParentDecidableEq :
              ∀ coordinate, DecidableEq (Parent coordinate)],
            ∀ (parent : ∀ coordinate, Index → Parent coordinate),
              ∀ (conflict : ∀ coordinate,
                  Parent coordinate → Parent coordinate → Prop),
                ∀ (degree : ℕ),
                  (∀ coordinate value,
                    conflict coordinate value value) →
                  (∀ coordinate first second,
                    conflict coordinate first second →
                      conflict coordinate second first) →
                  (∀ coordinate value,
                    ((Finset.univ : Finset (Parent coordinate)).filter
                      (conflict coordinate value)).card ≤ degree) →
                  ∃ selected : Finset Index,
                    selected ⊆ initial ∧
                    (∑ index ∈ initial, weight index) ≤
                      (degree : ENNReal) ^ scaleCount *
                        ∑ index ∈ selected, weight index ∧
                    ∀ coordinate,
                      ∀ first second : Parent coordinate,
                        first ≠ second →
                        (∃ index ∈ selected,
                          parent coordinate index = first) →
                        (∃ index ∈ selected,
                          parent coordinate index = second) →
                        ¬ conflict coordinate first second := by
  intro scaleCount
  induction scaleCount with
  | zero =>
      intro Parent _ _ parent conflict degree hrefl hsymm hdegree
      refine ⟨initial, Finset.Subset.rfl, ?_, ?_⟩
      · simp
      · intro coordinate
        exact Fin.elim0 coordinate
  | succ scaleCount inductionHypothesis =>
      intro Parent hParentFintype hParentDecidableEq parent conflict degree
        hrefl hsymm hdegree
      let PreviousParent : Fin scaleCount → Type u := fun coordinate =>
        Parent (Fin.castSucc coordinate)
      let previousParent :
          ∀ coordinate, Index → PreviousParent coordinate :=
        fun coordinate => parent (Fin.castSucc coordinate)
      let previousConflict : ∀ coordinate,
          PreviousParent coordinate → PreviousParent coordinate → Prop :=
        fun coordinate => conflict (Fin.castSucc coordinate)
      rcases inductionHypothesis PreviousParent previousParent previousConflict
          degree
          (fun coordinate => hrefl (Fin.castSucc coordinate))
          (fun coordinate => hsymm (Fin.castSucc coordinate))
          (fun coordinate => hdegree (Fin.castSucc coordinate)) with
        ⟨selected, hselectedSubset, hselectedWeight, hselectedSeparated⟩
      let last := Fin.last scaleCount
      rcases proposition63_one_step_complete_parent_selection
          weight selected (parent last) (conflict last) degree
          (hrefl last) (hsymm last) (hdegree last) with
        ⟨further, hfurtherSubset, hfurtherWeight, hfurtherSeparated⟩
      have hweight :
          (∑ index ∈ initial, weight index) ≤
            (degree : ENNReal) ^ (scaleCount + 1) *
              ∑ index ∈ further, weight index := by
        calc
          (∑ index ∈ initial, weight index) ≤
              (degree : ENNReal) ^ scaleCount *
                ∑ index ∈ selected, weight index := hselectedWeight
          _ ≤ (degree : ENNReal) ^ scaleCount *
                ((degree : ENNReal) *
                  ∑ index ∈ further, weight index) := by gcongr
          _ = (degree : ENNReal) ^ (scaleCount + 1) *
                ∑ index ∈ further, weight index := by
            rw [pow_succ]
            ring
      refine ⟨further, hfurtherSubset.trans hselectedSubset, hweight, ?_⟩
      apply Fin.lastCases
      · exact hfurtherSeparated
      · intro previousCoordinate first second hne hfirst hsecond
        apply hselectedSeparated previousCoordinate first second hne
        · rcases hfirst with ⟨index, hindex, hparent⟩
          exact ⟨index, hfurtherSubset hindex, hparent⟩
        · rcases hsecond with ⟨index, hindex, hparent⟩
          exact ⟨index, hfurtherSubset hindex, hparent⟩

/-- Simultaneously retain complete parent groups which are separated at each
coordinate of a finite schedule. -/
theorem proposition63_finite_strong_parent_selection
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (weight : Index → ENNReal)
    (scaleCount : ℕ)
    (Parent : Fin scaleCount → Type*)
    [∀ coordinate, Fintype (Parent coordinate)]
    [∀ coordinate, DecidableEq (Parent coordinate)]
    (parent : ∀ coordinate, Index → Parent coordinate)
    (conflict : ∀ coordinate, Parent coordinate → Parent coordinate → Prop)
    (degree : ℕ)
    (hrefl : ∀ coordinate value, conflict coordinate value value)
    (hsymm : ∀ coordinate first second,
      conflict coordinate first second → conflict coordinate second first)
    (hdegree : ∀ coordinate value,
      ((Finset.univ : Finset (Parent coordinate)).filter
        (conflict coordinate value)).card ≤ degree) :
    Nonempty (Proposition63FiniteStrongParentSelectionData
      weight scaleCount Parent parent conflict degree) := by
  rcases proposition63_finite_complete_parent_selection_induction
      weight Finset.univ scaleCount Parent parent conflict degree
      hrefl hsymm hdegree with
    ⟨selected, _hselectedSubset, hweight, hseparated⟩
  exact ⟨{
    selected := selected
    retained_weight := hweight
    hit_parent_separated := hseparated
  }⟩

/-- Simultaneous complete-parent selection starting from a prescribed set of
indices.  This is the form needed after the ordinary-distinctness cleanup in
the final mild rescaling. -/
theorem proposition63_finite_strong_parent_selection_from
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (weight : Index → ENNReal)
    (initial : Finset Index)
    (scaleCount : ℕ)
    (Parent : Fin scaleCount → Type*)
    [∀ coordinate, Fintype (Parent coordinate)]
    [∀ coordinate, DecidableEq (Parent coordinate)]
    (parent : ∀ coordinate, Index → Parent coordinate)
    (conflict : ∀ coordinate, Parent coordinate → Parent coordinate → Prop)
    (degree : ℕ)
    (hrefl : ∀ coordinate value, conflict coordinate value value)
    (hsymm : ∀ coordinate first second,
      conflict coordinate first second → conflict coordinate second first)
    (hdegree : ∀ coordinate value,
      ((Finset.univ : Finset (Parent coordinate)).filter
        (conflict coordinate value)).card ≤ degree) :
    let restrictedWeight : Index → ENNReal := fun index =>
      if index ∈ initial then weight index else 0
    ∃ selection : Proposition63FiniteStrongParentSelectionData
        restrictedWeight scaleCount Parent parent conflict degree,
      selection.selected ⊆ initial ∧
      (∑ index ∈ initial, weight index) ≤
        (degree : ENNReal) ^ scaleCount *
          ∑ index ∈ selection.selected, weight index := by
  let restrictedWeight : Index → ENNReal := fun index =>
    if index ∈ initial then weight index else 0
  rcases proposition63_finite_complete_parent_selection_induction
      restrictedWeight initial scaleCount Parent parent conflict degree
      hrefl hsymm hdegree with
    ⟨selected, hsubset, hweight, hseparated⟩
  have htotal : (∑ index : Index, restrictedWeight index) =
      ∑ index ∈ initial, weight index := by
    rw [← Finset.sum_subset (Finset.subset_univ initial)]
    · apply Finset.sum_congr rfl
      intro index hindex
      simp [restrictedWeight, hindex]
    · intro index _ hindex
      simp [restrictedWeight, hindex]
  have hselected : (∑ index ∈ selected, restrictedWeight index) =
      ∑ index ∈ selected, weight index := by
    apply Finset.sum_congr rfl
    intro index hindex
    simp [restrictedWeight, hsubset hindex]
  have hretainedAll : (∑ index : Index, restrictedWeight index) ≤
      (degree : ENNReal) ^ scaleCount *
        ∑ index ∈ selected, restrictedWeight index := by
    calc
      (∑ index : Index, restrictedWeight index) =
          ∑ index ∈ initial, weight index := htotal
      _ = ∑ index ∈ initial, restrictedWeight index := by
        apply Finset.sum_congr rfl
        intro index hindex
        simp [restrictedWeight, hindex]
      _ ≤ (degree : ENNReal) ^ scaleCount *
          ∑ index ∈ selected, restrictedWeight index := hweight
      _ = (degree : ENNReal) ^ scaleCount *
          ∑ index ∈ selected, restrictedWeight index := by rw [hselected]
  exact ⟨{
    selected := selected
    retained_weight := hretainedAll
    hit_parent_separated := hseparated
  }, hsubset, by
    calc
      (∑ index ∈ initial, weight index) =
          ∑ index ∈ initial, restrictedWeight index := by
        apply Finset.sum_congr rfl
        intro index hindex
        simp [restrictedWeight, hindex]
      _ ≤ (degree : ENNReal) ^ scaleCount *
          ∑ index ∈ selected, restrictedWeight index := hweight
      _ = (degree : ENNReal) ^ scaleCount *
          ∑ index ∈ selected, weight index := by rw [hselected]
  ⟩

end Kakeya.Assouad.PureWZ2

end
