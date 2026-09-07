import MyLeanRepo.Kakeya.Assouad.WZ1.PaperPackingRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalizedAssignedParentCover

/-!
# Finite weighted selection of complete parent fibers

This is the model-independent combinatorial core used by the public
large-slope nearby-scale construction.  At each one of finitely many parent
maps, it selects an independent set of parents and keeps *all* currently
retained children of those parents.  Hence no assigned subfiber or singleton
replacement is introduced.

The theorem is deliberately stated for arbitrary finite parent types.  The
large-slope application instantiates the parent maps with the uniquely derived
strict-parent maps of `WZ2PaperPurePartitioningCover`.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal

attribute [local instance] Classical.propDecidable

structure PureWZ2FiniteStrongParentSelectionData
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

private lemma pureWZ2_one_step_complete_parent_fiber_selection
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
    have := (Finset.mem_filter.mp hfirstIndex).2
    simpa [hfirstParent] using this
  have hsecondMem : second ∈ independent := by
    have := (Finset.mem_filter.mp hsecondIndex).2
    simpa [hsecondParent] using this
  exact hindependent first hfirstMem second hsecondMem hne

universe u in
private lemma pureWZ2_finite_complete_parent_fiber_selection_induction
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (weight : Index → ENNReal) :
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
                    (∑ index : Index, weight index) ≤
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
      refine ⟨Finset.univ, ?_, ?_⟩
      · simp
      · intro coordinate
        exact Fin.elim0 coordinate
  | succ scaleCount inductionHypothesis =>
      intro Parent hParentFintype hParentDecidableEq parent conflict degree
        hrefl hsymm hdegree
      let PreviousParent : Fin scaleCount → Type u := fun coordinate =>
        Parent (Fin.castSucc coordinate)
      let previousParent : ∀ coordinate, Index → PreviousParent coordinate :=
        fun coordinate => parent (Fin.castSucc coordinate)
      let previousConflict : ∀ coordinate,
          PreviousParent coordinate → PreviousParent coordinate → Prop :=
        fun coordinate => conflict (Fin.castSucc coordinate)
      rcases inductionHypothesis PreviousParent previousParent previousConflict
          degree
          (fun coordinate => hrefl (Fin.castSucc coordinate))
          (fun coordinate => hsymm (Fin.castSucc coordinate))
          (fun coordinate => hdegree (Fin.castSucc coordinate)) with
        ⟨selected, hselectedWeight, hselectedSeparated⟩
      let last := Fin.last scaleCount
      rcases pureWZ2_one_step_complete_parent_fiber_selection
          weight selected (parent last) (conflict last) degree
          (hrefl last) (hsymm last) (hdegree last) with
        ⟨further, hfurtherSubset, hfurtherWeight, hfurtherSeparated⟩
      have hweight :
          (∑ index : Index, weight index) ≤
            (degree : ENNReal) ^ (scaleCount + 1) *
              ∑ index ∈ further, weight index := by
        calc
          (∑ index : Index, weight index) ≤
              (degree : ENNReal) ^ scaleCount *
                ∑ index ∈ selected, weight index := hselectedWeight
          _ ≤ (degree : ENNReal) ^ scaleCount *
                ((degree : ENNReal) *
                  ∑ index ∈ further, weight index) := by
            gcongr
          _ = (degree : ENNReal) ^ (scaleCount + 1) *
                ∑ index ∈ further, weight index := by
            rw [pow_succ]
            ring
      refine ⟨further, hweight, ?_⟩
      apply Fin.lastCases
      · exact hfurtherSeparated
      · intro previousCoordinate first second hne hfirst hsecond
        apply hselectedSeparated previousCoordinate first second hne
        · rcases hfirst with ⟨index, hindex, hparent⟩
          exact ⟨index, hfurtherSubset hindex, hparent⟩
        · rcases hsecond with ⟨index, hindex, hparent⟩
          exact ⟨index, hfurtherSubset hindex, hparent⟩

theorem pureWZ2_finite_strong_parent_selection
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
    Nonempty (PureWZ2FiniteStrongParentSelectionData
      weight scaleCount Parent parent conflict degree) := by
  rcases pureWZ2_finite_complete_parent_fiber_selection_induction
      weight scaleCount Parent parent conflict degree hrefl hsymm hdegree with
    ⟨selected, hweight, hseparated⟩
  exact ⟨{
    selected := selected
    retained_weight := hweight
    hit_parent_separated := hseparated
  }⟩

namespace PureWZ2FiniteLocalizedPreAssignedParentScheduleData

/-- Apply the generic complete-fiber independent-set argument to a finite
schedule of preliminary geometric parent assignments. -/
theorem simultaneouslySeparate
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {scaleCount : ℕ}
    (schedule : PureWZ2FiniteLocalizedPreAssignedParentScheduleData
      fine scaleCount)
    (weight : Fin fine.card → ENNReal)
    (conflict : ∀ coordinate,
      schedule.Parent coordinate → schedule.Parent coordinate → Prop)
    (degree : ℕ)
    (hrefl : ∀ coordinate parent, conflict coordinate parent parent)
    (hsymm : ∀ coordinate first second,
      conflict coordinate first second → conflict coordinate second first)
    (hdegree : ∀ coordinate parent,
      ((Finset.univ : Finset (schedule.Parent coordinate)).filter
        (conflict coordinate parent)).card ≤ degree) :
    Nonempty (PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate source =>
        (schedule.cover coordinate).assignedParent source)
      conflict degree) :=
  pureWZ2_finite_strong_parent_selection
    weight scaleCount schedule.Parent
    (fun coordinate source =>
      (schedule.cover coordinate).assignedParent source)
    conflict degree hrefl hsymm hdegree

/-- Convert every coordinate of a preliminary schedule into a genuine public
cover after one common strong-parent selection. -/
noncomputable def selectedCover
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {scaleCount : ℕ}
    (schedule : PureWZ2FiniteLocalizedPreAssignedParentScheduleData
      fine scaleCount)
    (weight : Fin fine.card → ENNReal)
    (conflict : ∀ coordinate,
      schedule.Parent coordinate → schedule.Parent coordinate → Prop)
    (degree : ℕ)
    (selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate source =>
        (schedule.cover coordinate).assignedParent source)
      conflict degree)
    (conflict_of_not_separated : ∀ coordinate first second,
      ¬ 2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
          schedule.rho coordinate <
          wz1PaperLineDistance
            ((schedule.coarse coordinate).tube first)
            ((schedule.coarse coordinate).tube second) →
        conflict coordinate first second)
    (coordinate : Fin scaleCount) :
    let selected := WZ2PaperPureTubeSubfamily.fromFinset
      fine selection.selected
    PureWZ2LocalizedAssignedParentCoverData
      selected.family
      (((schedule.cover coordinate).hitParentSubfamily selected).family) := by
  dsimp only
  let selected := WZ2PaperPureTubeSubfamily.fromFinset
    fine selection.selected
  let pre := schedule.cover coordinate
  apply pre.restrictToSeparatedHitParents selected
  intro first second hne
  have hambientNe :
      (pre.hitParentSubfamily selected).embedding first ≠
        (pre.hitParentSubfamily selected).embedding second :=
    (pre.hitParentSubfamily selected).embedding.injective.ne hne
  have hfirst : ∃ source ∈ selection.selected,
      pre.assignedParent source =
        (pre.hitParentSubfamily selected).embedding first := by
    rcases pre.hitParent_surjective selected first with ⟨source, hsource⟩
    refine ⟨selected.embedding source, ?_, ?_⟩
    · exact Finset.orderEmbOfFin_mem selection.selected rfl source
    · rw [← pre.hitParent_ambient selected source, hsource]
  have hsecond : ∃ source ∈ selection.selected,
      pre.assignedParent source =
        (pre.hitParentSubfamily selected).embedding second := by
    rcases pre.hitParent_surjective selected second with ⟨source, hsource⟩
    refine ⟨selected.embedding source, ?_, ?_⟩
    · exact Finset.orderEmbOfFin_mem selection.selected rfl source
    · rw [← pre.hitParent_ambient selected source, hsource]
  have hnotConflict := selection.hit_parent_separated coordinate
    ((pre.hitParentSubfamily selected).embedding first)
    ((pre.hitParentSubfamily selected).embedding second)
    hambientNe hfirst hsecond
  by_contra hnot
  exact hnotConflict
    (conflict_of_not_separated coordinate _ _ hnot)

end PureWZ2FiniteLocalizedPreAssignedParentScheduleData

end Kakeya.Assouad

end
