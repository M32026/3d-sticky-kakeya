import Mathlib.Tactic

/-!
# Maximal separated set existence

Given a predicate `P`, a symmetric separation relation `sep`, and a uniform
cardinality bound `N` on every `P`-separated finite set, there exists a maximal
such set: every `P`-element is either in the set or fails to be separated from
some member of it.

Proof: greedy extension by well-founded recursion on `N - s.card`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
Existence of a maximal `P`-separated finite set under a uniform cardinality bound.

Given:
- `P : α → Prop` (the "eligible" elements)
- `sep : α → α → Prop` (a symmetric separation relation)
- `N : ℕ` such that every finite set of pairwise separated `P`-elements has
  cardinality at most `N`

There exists `L : Finset α` such that:
1. Every element of `L` satisfies `P`.
2. Distinct elements of `L` are pairwise separated.
3. Every `x` satisfying `P` is either in `L` or is not separated from some
   element of `L`.

Proof by greedy extension: start with `∅` and repeatedly insert an eligible
element separated from all current members. The cardinality increases by one
each step and is bounded by `N`, so the process terminates.
-/
lemma exists_maximal_separated
    {α : Type*} [DecidableEq α]
    (P : α → Prop) [DecidablePred P]
    (sep : α → α → Prop) [DecidableRel sep]
    (h_symm : ∀ {x y}, sep x y → sep y x)
    (N : ℕ)
    (h_bound : ∀ (s : Finset α),
        (∀ x ∈ s, P x) →
        (∀ x ∈ s, ∀ y ∈ s, x ≠ y → sep x y) →
        s.card ≤ N) :
    ∃ (L : Finset α),
        (∀ x ∈ L, P x) ∧
        (∀ x ∈ L, ∀ y ∈ L, x ≠ y → sep x y) ∧
        (∀ x, P x → ∃ y ∈ L, x = y ∨ ¬ sep x y) := by
  let valid : Finset α → Prop := fun s =>
    (∀ x ∈ s, P x) ∧ (∀ x ∈ s, ∀ y ∈ s, x ≠ y → sep x y)
  have h_valid_empty : valid ∅ := by
    simp [valid]
  have h_insert_valid : ∀ (s : Finset α) (x : α),
      valid s → P x → x ∉ s → (∀ y ∈ s, sep x y) → valid (insert x s) := by
    intro s x hs hPx hxns hsep
    constructor
    · -- All elements of insert x s satisfy P
      intro z hz
      have h : z = x ∨ z ∈ s := Finset.mem_insert.mp hz
      rcases h with (rfl | hzs)
      · exact hPx
      · exact hs.1 z hzs
    · -- Pairwise separation
      intro z hz w hw hne
      have hz' : z = x ∨ z ∈ s := Finset.mem_insert.mp hz
      have hw' : w = x ∨ w ∈ s := Finset.mem_insert.mp hw
      rcases hz' with (rfl | hz_in_s)
      · -- z = x
        rcases hw' with (rfl | hw_in_s)
        · -- w = x
          exfalso; exact hne rfl
        · -- w ∈ s
          exact hsep w hw_in_s
      · -- z ∈ s
        rcases hw' with (rfl | hw_in_s)
        · -- w = x
          exact h_symm (hsep z hz_in_s)
        · -- w ∈ s
          exact hs.2 z hz_in_s w hw_in_s hne
  have h_not_extendable_implies_maximal : ∀ (s : Finset α), valid s →
      (¬ ∃ (x : α), P x ∧ x ∉ s ∧ (∀ y ∈ s, sep x y)) →
      (∀ x, P x → ∃ y ∈ s, x = y ∨ ¬ sep x y) := by
    intro s hs h_not_ext x hPx
    by_cases h_x_in : x ∈ s
    · exact ⟨x, h_x_in, Or.inl rfl⟩
    · -- x ∉ s
      by_cases h_all_sep : ∀ y ∈ s, sep x y
      · exfalso
        exact h_not_ext ⟨x, hPx, h_x_in, h_all_sep⟩
      · -- ¬ (∀ y ∈ s, sep x y)
        have h_exists : ∃ y ∈ s, ¬ sep x y := by
          simpa [not_forall] using h_all_sep
        rcases h_exists with ⟨y, hy_in_s, h_not_sep⟩
        exact ⟨y, hy_in_s, Or.inr h_not_sep⟩
  have h_main : ∀ (k : ℕ), ∀ (s : Finset α),
      N - s.card = k → valid s →
      ∃ (L : Finset α), valid L ∧ s ⊆ L ∧
        (∀ x, P x → ∃ y ∈ L, x = y ∨ ¬ sep x y) := by
    intro k
    induction k with
    | zero =>
      -- Base case: N - s.card = 0, so s.card ≥ N. By h_bound, s.card = N.
      intro s hk hs_valid
      have h_card_le : s.card ≤ N := h_bound s hs_valid.1 hs_valid.2
      have h_card_eq : s.card = N := by omega
      have h_not_ext : ¬ ∃ (x : α), P x ∧ x ∉ s ∧ (∀ y ∈ s, sep x y) := by
        intro h_ext
        rcases h_ext with ⟨x, hPx, hxns, hsep⟩
        let s' := insert x s
        have h_valid' : valid s' := h_insert_valid s x hs_valid hPx hxns hsep
        have h4 : s'.card ≤ N := h_bound s' h_valid'.1 h_valid'.2
        have h5 : s'.card = s.card + 1 := by
          have h6 : x ∉ s := hxns
          exact Finset.card_insert_of_notMem h6
        rw [h5, h_card_eq] at h4
        omega
      refine ⟨s, hs_valid, subset_refl s, h_not_extendable_implies_maximal s hs_valid h_not_ext⟩
    | succ k ih =>
      intro s hk hs_valid
      by_cases h_ext :
          ∃ (x : α), P x ∧ x ∉ s ∧ (∀ y ∈ s, sep x y)
      · -- Extend s by one element and recurse
        rcases h_ext with ⟨x, hPx, hxns, hsep⟩
        let s' := insert x s
        have h_valid' : valid s' := h_insert_valid s x hs_valid hPx hxns hsep
        have h_card' : s'.card = s.card + 1 := by
          have h6 : x ∉ s := hxns
          exact Finset.card_insert_of_notMem h6
        have h_bound' : s'.card ≤ N := h_bound s' h_valid'.1 h_valid'.2
        have h_rem : N - s'.card = k := by omega
        have ih' := ih s' h_rem h_valid'
        rcases ih' with ⟨L, hL_valid, hL_sub, hL_max⟩
        have h_s_sub_s' : s ⊆ s' := by
          exact Finset.subset_insert x s
        refine ⟨L, hL_valid, subset_trans h_s_sub_s' hL_sub, hL_max⟩
      · -- s is already maximal
        refine ⟨s, hs_valid, subset_refl s, h_not_extendable_implies_maximal s hs_valid h_ext⟩
  have h0 : N - (∅ : Finset α).card = N := by simp
  have h_result := h_main N (∅ : Finset α) h0 h_valid_empty
  rcases h_result with ⟨L, hL1, hL2, hL3⟩
  exact ⟨L, hL1.1, hL1.2, hL3⟩

end Kakeya.Assouad
