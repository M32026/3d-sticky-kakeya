module

public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Interval list utility lemmas

Utilities for lists of real intervals `(a, b)` with `a < b`, used in the
Combinatorial Kaufman Decomposition.

Main results:
- `sorted_disjoint_consecutive`: for two valid intervals sorted by left
  endpoint with disjoint interiors, `p.2 ≤ q.1`.
- `intervalList_sum_length_le`: sum of lengths of pairwise disjoint, sorted
  intervals contained in `[a, b]` is at most `b - a`.
- `sorted_left_get`, `sorted_left_first_min`, `sorted_left_consecutive`:
  consequences of `SortedByLeft`.
-/

namespace CombinatorialKaufman

/-- A list of intervals is sorted by left endpoint. -/
def SortedByLeft (l : List (ℝ × ℝ)) : Prop :=
  List.Pairwise (fun p q => p.1 < q.1) l

/-- A list of intervals has pairwise disjoint interiors. -/
def PairwiseInteriorDisjointList (l : List (ℝ × ℝ)) : Prop :=
  List.Pairwise (fun p q => Disjoint (Set.Ioo p.1 p.2) (Set.Ioo q.1 q.2)) l

/-- For two valid intervals sorted by left endpoint with disjoint interiors,
the right endpoint of the first is at most the left endpoint of the second. -/
lemma sorted_disjoint_consecutive {p q : ℝ × ℝ}
    (_hp : p.1 < p.2) (hq : q.1 < q.2)
    (h_left : p.1 < q.1)
    (h_disj : Disjoint (Set.Ioo p.1 p.2) (Set.Ioo q.1 q.2)) :
    p.2 ≤ q.1 := by
  by_contra h
  have h' : q.1 < p.2 := by linarith
  set y := min p.2 q.2 with hy_def
  have hmin : q.1 < y := by
    rw [hy_def]
    exact lt_min h' hq
  set x := (q.1 + y) / 2 with hx_def
  have hx1 : q.1 < x := by
    rw [hx_def]
    linarith
  have hx2 : x < y := by
    rw [hx_def]
    linarith
  have hx3 : x < p.2 := by
    have h_y_le : y ≤ p.2 := by
      rw [hy_def]
      exact min_le_left _ _
    linarith
  have hx4 : x < q.2 := by
    have h_y_le : y ≤ q.2 := by
      rw [hy_def]
      exact min_le_right _ _
    linarith
  have h_in_p : x ∈ Set.Ioo p.1 p.2 := by
    exact ⟨by linarith, hx3⟩
  have h_in_q : x ∈ Set.Ioo q.1 q.2 := by
    exact ⟨hx1, hx4⟩
  exact Set.not_disjoint_iff.mpr ⟨x, h_in_p, h_in_q⟩ h_disj

/-- If a list of valid intervals is sorted by left endpoint and has pairwise
disjoint interiors, then every interval in the tail starts after the head ends. -/
lemma sorted_disjoint_tail_after_head {p : ℝ × ℝ} {t : List (ℝ × ℝ)}
    (hp : p.1 < p.2)
    (h_valid_t : ∀ q ∈ t, q.1 < q.2)
    (h_sorted : SortedByLeft (p :: t))
    (h_disj : PairwiseInteriorDisjointList (p :: t)) :
    ∀ q ∈ t, p.2 ≤ q.1 := by
  have h_left : ∀ q ∈ t, p.1 < q.1 := by
    have h := List.pairwise_cons.mp h_sorted
    exact h.1
  have h_disj' : ∀ q ∈ t, Disjoint (Set.Ioo p.1 p.2) (Set.Ioo q.1 q.2) := by
    have h := List.pairwise_cons.mp h_disj
    exact h.1
  intro q hq
  exact sorted_disjoint_consecutive hp (h_valid_t q hq) (h_left q hq) (h_disj' q hq)

/-- Sum of lengths of pairwise disjoint, sorted intervals contained in `[a, b]`
is at most `b - a`. -/
lemma intervalList_sum_length_le {l : List (ℝ × ℝ)} {a b : ℝ}
    (h_valid : ∀ p ∈ l, p.1 < p.2)
    (h_sorted : SortedByLeft l)
    (h_disj : PairwiseInteriorDisjointList l)
    (ha : ∀ p ∈ l, a ≤ p.1)
    (hb : ∀ p ∈ l, p.2 ≤ b)
    (hab : a ≤ b) :
    (l.map (fun p : ℝ × ℝ => p.2 - p.1)).sum ≤ b - a := by
  have h_main : ∀ (l : List (ℝ × ℝ)) (c d : ℝ),
      (∀ p ∈ l, p.1 < p.2) →
      SortedByLeft l →
      PairwiseInteriorDisjointList l →
      (∀ p ∈ l, c ≤ p.1) →
      (∀ p ∈ l, p.2 ≤ d) →
      c ≤ d →
      (l.map (fun p : ℝ × ℝ => p.2 - p.1)).sum ≤ d - c := by
    intro l
    induction l with
    | nil =>
      intro c d _ _ _ _ _ hcd
      simpa using sub_nonneg.mpr hcd
    | cons p t ih =>
      intro c d h_valid h_sorted h_disj ha hb hcd
      have hp_valid : p.1 < p.2 := h_valid p (by simp)
      have h_sorted_t : SortedByLeft t := by
        have h := List.pairwise_cons.mp h_sorted
        exact h.2
      have h_disj_t : PairwiseInteriorDisjointList t := by
        have h := List.pairwise_cons.mp h_disj
        exact h.2
      have h_valid_t : ∀ q ∈ t, q.1 < q.2 :=
        fun q hq => h_valid q (by simp [hq])
      have h_tail_after : ∀ q ∈ t, p.2 ≤ q.1 :=
        sorted_disjoint_tail_after_head hp_valid h_valid_t h_sorted h_disj
      have hb_t : ∀ q ∈ t, q.2 ≤ d :=
        fun q hq => hb q (by simp [hq])
      have hp_b : p.2 ≤ d := hb p (by simp)
      have ih' := ih p.2 d h_valid_t h_sorted_t h_disj_t h_tail_after hb_t hp_b
      have h_sum : ((p :: t).map (fun p : ℝ × ℝ => p.2 - p.1)).sum =
          (p.2 - p.1) + (t.map (fun p : ℝ × ℝ => p.2 - p.1)).sum := by
        simp
      rw [h_sum]
      have h_ca : c ≤ p.1 := ha p (by simp)
      linarith [ih']
  exact h_main l a b h_valid h_sorted h_disj ha hb hab

/-- Specialization of `intervalList_sum_length_le` to intervals in `[0, m]`. -/
lemma intervalList_sum_length_le_zero {l : List (ℝ × ℝ)} {m : ℝ}
    (hm : 0 ≤ m)
    (h_valid : ∀ p ∈ l, p.1 < p.2)
    (h_sorted : SortedByLeft l)
    (h_disj : PairwiseInteriorDisjointList l)
    (h_in : ∀ p ∈ l, 0 ≤ p.1 ∧ p.2 ≤ m) :
    (l.map (fun p : ℝ × ℝ => p.2 - p.1)).sum ≤ m := by
  have ha : ∀ p ∈ l, (0 : ℝ) ≤ p.1 := fun p hp => (h_in p hp).1
  have hb : ∀ p ∈ l, p.2 ≤ m := fun p hp => (h_in p hp).2
  have h := intervalList_sum_length_le h_valid h_sorted h_disj ha hb hm
  simpa using h

/-- For a nonempty list sorted by left endpoint, the head has strictly smaller
left endpoint than every element of the tail. -/
lemma sorted_left_first_min {p : ℝ × ℝ} {t : List (ℝ × ℝ)}
    (h : SortedByLeft (p :: t)) :
    ∀ q ∈ t, p.1 < q.1 := by
  have h' := List.pairwise_cons.mp h
  exact h'.1

/-- For a list sorted by left endpoint, consecutive elements satisfy
`p.1 < q.1`. -/
lemma sorted_left_consecutive {p q : ℝ × ℝ} {t : List (ℝ × ℝ)}
    (h : SortedByLeft (p :: q :: t)) :
    p.1 < q.1 := by
  have h1 : ∀ r ∈ (q :: t), p.1 < r.1 := by
    have h' := List.pairwise_cons.mp h
    exact h'.1
  exact h1 q (by simp)

/-- If a list is `SortedByLeft`, then for any `i < j` as `Fin l.length`,
the element at `i` has strictly smaller left endpoint than the element at `j`. -/
lemma sorted_left_get {l : List (ℝ × ℝ)} (h : SortedByLeft l)
    {i j : Fin l.length} (hij : i < j) :
    (l.get i).1 < (l.get j).1 := by
  exact List.pairwise_iff_get.mp h i j hij

end CombinatorialKaufman
