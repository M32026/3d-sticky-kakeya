module

public import MyLeanRepo.OSWPrelude
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.Definitions

@[expose] public section

/-!
# Fin n Conversion Utilities

Utilities for converting between `List (ℝ × ℝ)` and `Fin n → ℝ × ℝ`,
and transferring properties (sums, pairwise disjointness, forall properties)
between the two representations.

This supports the Combinatorial Kaufman Decomposition proof, where intervals
are constructed as a list and then presented to the theorem as a `Fin n`-indexed
family.
-/

noncomputable section

namespace CombinatorialKaufman

/-- Convert a list to a `Fin l.length`-indexed function. -/
def listToFin {α : Type*} (l : List α) : Fin l.length → α :=
  fun i => l.get i

/-- The sum over `Fin l.length` of `g (l.get i)` equals the sum of `g` over the list. -/
lemma sum_fin_eq_sum_map {α M : Type*} [AddCommMonoid M] (l : List α) (g : α → M) :
    ∑ i : Fin l.length, g (l.get i) = (l.map g).sum := by
  have h1 : List.ofFn (fun i : Fin l.length => g (l.get i)) = l.map g :=
    List.ofFn_getElem_eq_map l g
  have h2 : (List.ofFn (fun i : Fin l.length => g (l.get i))).sum = ∑ i : Fin l.length, g (l.get i) :=
    List.sum_ofFn
  rw [← h2, h1]

/-- Transfer a universal property from a list to its `Fin`-indexed representation. -/
lemma forall_list_to_fin {α : Type*} {l : List α} {P : α → Prop}
    (h : ∀ x ∈ l, P x) : ∀ i : Fin l.length, P (l.get i) := by
  intro i
  exact h (l.get i) (List.get_mem l i)

/-- A nonempty list has positive length. -/
lemma nonempty_list_pos_length {α : Type*} {l : List α} (h : l ≠ []) :
    0 < l.length := by
  simpa [List.length_pos_iff_ne_nil] using h

/-- Transfer `List.Pairwise` disjoint-interior property to `PairwiseInteriorDisjoint`. -/
lemma pairwise_disjoint_list_to_fin (l : List (ℝ × ℝ))
    (h : l.Pairwise (fun p q : ℝ × ℝ =>
      Disjoint (Set.Ioo p.1 p.2) (Set.Ioo q.1 q.2))) :
    PairwiseInteriorDisjoint (listToFin l) := by
  intro i j hne
  have hlt : i < j ∨ j < i := Fin.lt_or_lt_of_ne hne
  cases hlt with
  | inl hlt =>
    exact h.rel_get_of_lt hlt
  | inr hlt =>
    have h' := h.rel_get_of_lt hlt
    exact Disjoint.symm h'

/-- Given a `Finset`, convert to `Fin n → α` via `toList`.
Returns a sigma type with the length and the function. -/
def finsetToFin {α : Type*} [DecidableEq α] (s : Finset α) :
    Σ n : ℕ, Fin n → α :=
  ⟨s.toList.length, fun i => s.toList.get i⟩

/-- Sum over a `Finset` equals sum over the corresponding `Fin` family. -/
lemma finset_sum_eq_fin_sum {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (g : α → M) :
    ∑ x ∈ s, g x = ∑ i : Fin s.toList.length, g (s.toList.get i) := by
  have h1 : ∑ x ∈ s, g x = (s.toList.map g).sum := by
    exact (Finset.sum_map_toList s g).symm
  rw [h1]
  exact (sum_fin_eq_sum_map s.toList g).symm

/-- If all elements of a list satisfy a conjunction of properties,
so does every element of the `Fin` family. -/
lemma forall_and_list_to_fin {α : Type*} {l : List α} {P Q : α → Prop}
    (h : ∀ x ∈ l, P x ∧ Q x) :
    (∀ i : Fin l.length, P (l.get i)) ∧ (∀ i : Fin l.length, Q (l.get i)) := by
  have hP : ∀ i, P (l.get i) := by
    intro i
    exact (h (l.get i) (List.get_mem l i)).1
  have hQ : ∀ i, Q (l.get i) := by
    intro i
    exact (h (l.get i) (List.get_mem l i)).2
  exact ⟨hP, hQ⟩

/-- Transfer a symmetric `List.Pairwise` relation to all distinct `Fin` indices. -/
lemma pairwise_symmetric_list_to_fin {α : Type*} {R : α → α → Prop}
    [Std.Symm R] {l : List α} (h : l.Pairwise R) :
    ∀ (i j : Fin l.length), i ≠ j → R (l.get i) (l.get j) := by
  intro i j hne
  have hlt : i < j ∨ j < i := Fin.lt_or_lt_of_ne hne
  cases hlt with
  | inl hlt =>
    exact h.rel_get_of_lt hlt
  | inr hlt =>
    have h' := h.rel_get_of_lt hlt
    exact symm h'

/-- Cast version: if `l.length = n`, transfer a sum over `Fin l.length` to `Fin n`. -/
lemma sum_fin_cast {α M : Type*} [AddCommMonoid M] {l : List α} {n : ℕ} (hn : l.length = n)
    (g : α → M) :
    ∑ i : Fin n, g (l.get (Fin.cast hn.symm i)) = (l.map g).sum := by
  subst hn
  exact sum_fin_eq_sum_map l g

/-- Cast version of `listToFin` when `l.length = n`. -/
def listToFinCast {α : Type*} (l : List α) {n : ℕ} (hn : l.length = n) : Fin n → α :=
  fun i => l.get (Fin.cast hn.symm i)

end CombinatorialKaufman

end
