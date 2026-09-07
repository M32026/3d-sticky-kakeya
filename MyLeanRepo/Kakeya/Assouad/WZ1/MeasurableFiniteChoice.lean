import Mathlib.Tactic
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Measurable finite choice

A measurable selector for pointwise nonempty predicates with finite ordered
codomain and measurable sections.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- A finite-valued function is measurable when all singleton fibers are. -/
lemma measurable_of_measurable_fibers {X β : Type*}
    [MeasurableSpace X] [Fintype β] [MeasurableSpace β]
    [MeasurableSingletonClass β] {f : X → β}
    (hfib : ∀ b : β, MeasurableSet (f ⁻¹' {b})) :
    Measurable f := by
  classical
  intro s hs
  have h1 :
      f ⁻¹' s =
        ⋃ b : β, if b ∈ s then f ⁻¹' {b} else (∅ : Set X) := by
    ext x
    simp [Set.mem_preimage]
  rw [h1]
  apply MeasurableSet.iUnion
  intro b
  by_cases hbs : b ∈ s
  · simpa [hbs] using hfib b
  · simp [hbs]

/-- Select the least satisfying value from a finite ordered codomain. -/
lemma measurableFiniteChoice {X α : Type*}
    [MeasurableSpace X] [Fintype α] [DecidableEq α] [LinearOrder α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {P : X → α → Prop}
    (hP_meas : ∀ a : α, MeasurableSet {x : X | P x a})
    (hP_nonempty : ∀ x : X, ∃ a : α, P x a) :
    ∃ f : X → α, Measurable f ∧ (∀ x, P x (f x)) ∧
      ∀ x a, P x a → f x ≤ a := by
  classical
  let S : X → Finset α := fun x =>
    Finset.univ.filter fun a => P x a
  have hS_nonempty : ∀ x, (S x).Nonempty := by
    intro x
    rcases hP_nonempty x with ⟨a, ha⟩
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  let f : X → α := fun x =>
    (S x).min' (hS_nonempty x)
  have hf_mem : ∀ x, f x ∈ S x := by
    intro x
    exact Finset.min'_mem (S x) (hS_nonempty x)
  have hf_P : ∀ x, P x (f x) := by
    intro x
    exact (Finset.mem_filter.mp (hf_mem x)).2
  let less : α → Finset α := fun a =>
    Finset.univ.filter (fun b => b < a)
  have hfib : ∀ a : α, MeasurableSet (f ⁻¹' {a}) := by
    intro a
    have h_fiber :
        f ⁻¹' {a} =
          {x : X | P x a} ∩
            {x : X | ∀ b : α, b < a → ¬P x b} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff]
      constructor
      · intro h
        have hfa : f x = a := h
        have h1 : P x a := by
          rw [← hfa]
          exact hf_P x
        have h2 : ∀ b : α, b < a → ¬P x b := by
          intro b hbl
          by_contra h3
          have h4 : b ∈ S x :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ b, h3⟩
          have h5 : f x ≤ b := Finset.min'_le (S x) b h4
          have h6 : b < f x := by
            rw [hfa]
            exact hbl
          exact (Std.not_le.mpr h6) h5
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        have h_a_in : a ∈ S x :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ a, h1⟩
        have h_min : f x ≤ a := Finset.min'_le (S x) a h_a_in
        by_contra h
        have h' : f x < a := lt_of_le_of_ne h_min h
        exact (h2 (f x) h') (hf_P x)
    rw [h_fiber]
    have h_second :
        MeasurableSet {x : X | ∀ b : α, b < a → ¬P x b} := by
      have h_eq :
          {x : X | ∀ b : α, b < a → ¬P x b} =
            ⋂ b ∈ less a, {x : X | ¬P x b} := by
        ext x
        simp [less, Finset.mem_filter, Finset.mem_univ]
      rw [h_eq]
      exact Finset.measurableSet_biInter (less a)
        fun b _ => (hP_meas b).compl
    exact MeasurableSet.inter (hP_meas a) h_second
  exact ⟨f, measurable_of_measurable_fibers hfib, hf_P, by
    intro x a ha
    exact Finset.min'_le (S x) a
      (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩)⟩

end Kakeya.Assouad
