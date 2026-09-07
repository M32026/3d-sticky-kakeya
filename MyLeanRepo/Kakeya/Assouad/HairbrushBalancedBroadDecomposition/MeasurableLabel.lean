import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Measurable piecewise label function

Given a finite family of measurable sets and a mapping to a finite label type,
construct a measurable function that labels each point by the first set containing it.
-/

noncomputable section

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

section MeasurableLabel

/-- Active set for a point: indices i with x ∈ A i. -/
private def activeSet {ι : Type*} [Fintype ι]
    (A : ι → Set Point3) (x : Point3) : Finset ι :=
  Finset.univ.filter (fun i => x ∈ A i)

/-- Set of points with a specific active set. -/
private def setOfActive {ι : Type*} [Fintype ι]
    (A : ι → Set Point3) (s : Finset ι) : Set Point3 :=
  {x | activeSet A x = s}

private lemma setOfActive_measurable {ι : Type*} [Fintype ι]
    (A : ι → Set Point3) (hA : ∀ i, MeasurableSet (A i)) (s : Finset ι) :
    MeasurableSet (setOfActive A s) := by
  have h_eq : setOfActive A s =
      (⋂ i ∈ s, A i) ∩ (⋂ i ∈ (Finset.univ \ s), (A i)ᶜ) := by
    ext x
    simp only [setOfActive, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro h_active
      constructor
      · intro i hi
        have h_i_in : i ∈ activeSet A x := by rw [h_active]; exact hi
        exact (Finset.mem_filter.mp h_i_in).2
      · intro i hi
        have h_i_notin_s : i ∉ s := (Finset.mem_sdiff.mp hi).2
        have h_i_notin_active : i ∉ activeSet A x := by
          rw [h_active]; exact h_i_notin_s
        intro h_contra
        have h_goal : i ∈ activeSet A x := by
          simp only [activeSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact h_contra
        exact h_i_notin_active h_goal
    · rintro ⟨h1, h2⟩
      apply Finset.ext
      intro i
      have h_iff : i ∈ activeSet A x ↔ x ∈ A i := by
        simp only [activeSet, Finset.mem_filter, Finset.mem_univ, true_and]
        <;> rfl
      rw [h_iff]
      constructor
      · intro hi
        by_cases h_i_in : i ∈ s
        · exact h_i_in
        · have h_i_in_diff : i ∈ Finset.univ \ s := by
            apply Finset.mem_sdiff.mpr
            exact ⟨Finset.mem_univ i, h_i_in⟩
          have h_contra : x ∉ A i := h2 i h_i_in_diff
          exact False.elim (h_contra hi)
      · intro hi
        exact h1 i hi
  rw [h_eq]
  apply MeasurableSet.inter
  · apply Finset.measurableSet_biInter
    intro i _
    exact hA i
  · apply Finset.measurableSet_biInter
    intro i _
    exact (hA i).compl

/-- Measurable label function. -/
def measurableLabel {ι : Type*} [Fintype ι] [LinearOrder ι]
    {L : Type*} [Fintype L]
    (A : ι → Set Point3) (lab : ι → L) (default : L) : Point3 → L :=
  fun x =>
    if h : (activeSet A x).Nonempty
    then lab (Finset.min' (activeSet A x) h)
    else default

lemma measurableLabel_measurable {ι : Type*} [Fintype ι] [LinearOrder ι]
    {L : Type*} [Fintype L] [MeasurableSpace L]
    (A : ι → Set Point3) (hA : ∀ i, MeasurableSet (A i))
    (lab : ι → L) (default : L) :
    Measurable (measurableLabel A lab default) := by
  apply measurable_to_countable'
  intro j
  let contributing : Finset (Finset ι) :=
    (Finset.univ : Finset (Finset ι)).filter (fun s =>
      if h : s.Nonempty then lab (Finset.min' s h) = j else default = j)
  let fiber : Set Point3 := ⋃ s ∈ contributing, setOfActive A s
  have h_fiber_meas : MeasurableSet fiber := by
    apply Finset.measurableSet_biUnion
    intro s _
    exact setOfActive_measurable A hA s
  have h_main : {x | measurableLabel A lab default x = j} = fiber := by
    ext x
    simp only [Set.mem_setOf_eq, fiber, Set.mem_iUnion]
    constructor
    · -- Forward: label = j → ∃ s ∈ contributing, x ∈ setOfActive A s
      intro h_eq
      let s := activeSet A x
      have hs : s ∈ (Finset.univ : Finset (Finset ι)) := Finset.mem_univ s
      have h_x_in : x ∈ setOfActive A s := by
        simp only [setOfActive, Set.mem_setOf_eq]
        <;> rfl
      have h_s_in_contrib : s ∈ contributing := by
        simp only [contributing, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases h : s.Nonempty
        · have h_val : measurableLabel A lab default x = lab (Finset.min' s h) := by
            unfold measurableLabel
            rw [dif_pos h]
          have h_lab_eq : lab (Finset.min' s h) = j := by
            rw [←h_val]; exact h_eq
          simpa [h] using h_lab_eq
        · have h_val : measurableLabel A lab default x = default := by
            unfold measurableLabel
            rw [dif_neg h]
          have h_default_eq : default = j := by
            rw [←h_val]; exact h_eq
          simpa [h] using h_default_eq
      exact ⟨s, h_s_in_contrib, h_x_in⟩
    · -- Backward: ∃ s ∈ contributing, x ∈ setOfActive A s → label = j
      rintro ⟨s, hs_in, h_x_in⟩
      have h_active_eq : activeSet A x = s := by
        simpa [setOfActive, Set.mem_setOf_eq] using h_x_in
      have h_condition : (if h : s.Nonempty then lab (Finset.min' s h) = j else default = j) := by
        simp only [contributing, Finset.mem_filter, Finset.mem_univ, true_and] at hs_in
        exact hs_in
      by_cases h : s.Nonempty
      · have h_lab_eq : lab (Finset.min' s h) = j := by
          simpa [h] using h_condition
        have h_val : measurableLabel A lab default x = lab (Finset.min' s h) := by
          unfold measurableLabel
          rw [h_active_eq, dif_pos h]
        rw [h_val, h_lab_eq]
      · have h_default_eq : default = j := by
          simpa [h] using h_condition
        have h_val : measurableLabel A lab default x = default := by
          unfold measurableLabel
          rw [h_active_eq, dif_neg h]
        rw [h_val, h_default_eq]
  have h_preimage : (measurableLabel A lab default ⁻¹' {j}) = {x | measurableLabel A lab default x = j} := by
    ext y
    simp
  rw [h_preimage, h_main]
  exact h_fiber_meas

/-- If the family A is pairwise disjoint and x ∈ A i, then the label is lab i. -/
lemma measurableLabel_at_disjoint {ι : Type*} [Fintype ι] [LinearOrder ι]
    {L : Type*} [Fintype L]
    (A : ι → Set Point3) (lab : ι → L) (default : L)
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    {i : ι} {x : Point3} (hx : x ∈ A i) :
    measurableLabel A lab default x = lab i := by
  have h1 : ∀ j, x ∈ A j ↔ j = i := by
    intro j
    constructor
    · intro hj
      by_contra hne
      have h_disj : Disjoint (A i) (A j) := hdisj i j (Ne.symm hne)
      have h_inter : (A i) ∩ (A j) = ∅ := h_disj.eq_bot
      have h_contra : x ∈ (A i) ∩ (A j) := ⟨hx, hj⟩
      rw [h_inter] at h_contra
      simpa using h_contra
    · rintro rfl; exact hx
  have h_active_eq : activeSet A x = {i} := by
    ext j
    simp only [activeSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact h1 j
  unfold measurableLabel
  rw [h_active_eq]
  have h_ne : ({i} : Finset ι).Nonempty := Finset.singleton_nonempty i
  rw [dif_pos h_ne]
  have h_min : Finset.min' ({i} : Finset ι) h_ne = i := by simp
  rw [h_min] <;> rfl

end MeasurableLabel

end Kakeya.Assouad
