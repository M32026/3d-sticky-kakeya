module

/-
# Pigeonhole lemmas for induction on scales

Provides basic, dyadic, and uniformization pigeonhole principles used in the
proof of OS Proposition 5.1.

## Main results
- `exists_large_fiber`: a fiber of a map has at least average cardinality
- `exists_dyadic_level_count`: some dyadic weight level contains many elements
- `exists_dyadic_level_weighted`: some dyadic level has large total weight
- `uniformize_by_dyadic_level`: select a subset with weights in one dyadic interval
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Auxiliary: if every element of a finite sum is strictly less than `q`,
then the sum is strictly less than `card * q`. -/
lemma sum_lt_card_mul {s : Finset β} {f : β → ℕ} {q : ℕ}
    (h_nonempty : s.Nonempty) (h : ∀ y ∈ s, f y < q) :
    ∑ y ∈ s, f y < s.card * q := by
  calc
    ∑ y ∈ s, f y < ∑ y ∈ s, q := sum_lt_sum_of_nonempty h_nonempty (fun y hy => h y hy)
    _ = s.card * q := by simp [mul_comm]

/-- Number of dyadic levels needed to cover weights up to `N`.
Levels are `0, 1, ..., Nat.log 2 N + 1`, so there are `Nat.log 2 N + 2` levels.
Level 0 is for weight 0; level `j ≥ 1` is for `2^(j-1) ≤ w < 2^j`. -/
def numDyadicLevels (N : ℕ) : ℕ := Nat.log 2 N + 2

/-- Dyadic level of a weight: 0 for zero, `Nat.log 2 w + 1` for positive. -/
def dyadicLevel (w : ℕ) : ℕ :=
  if w = 0 then 0 else Nat.log 2 w + 1

/-- The dyadic level of `w ≤ N` is `< numDyadicLevels N`. -/
lemma dyadicLevel_lt {w N : ℕ} (hw : w ≤ N) :
    dyadicLevel w < numDyadicLevels N := by
  have h : dyadicLevel w ≤ Nat.log 2 N + 1 := by
    simp only [dyadicLevel]
    by_cases h0 : w = 0
    · rw [if_pos h0] <;> simp [numDyadicLevels] <;> omega
    · have h_log : Nat.log 2 w ≤ Nat.log 2 N := Nat.log_mono_right hw
      rw [if_neg h0] <;> simp [numDyadicLevels] <;> omega
  simp [numDyadicLevels] at h ⊢ <;> omega

/-- Characterization: if `dyadicLevel w = j` with `j ≥ 1`,
then `2^(j-1) ≤ w < 2^j`. -/
lemma dyadicLevel_spec {w j : ℕ} (hw_pos : 0 < w)
    (h : dyadicLevel w = j) : 2^(j-1) ≤ w ∧ w < 2^j := by
  have h0 : w ≠ 0 := by omega
  have h1 : Nat.log 2 w + 1 = j := by
    simpa [dyadicLevel, h0] using h
  have h2 : Nat.log 2 w = j - 1 := by omega
  have h3 : 2 ^ (j - 1) ≤ w := by
    have h4 : 2 ^ Nat.log 2 w ≤ w := Nat.pow_log_le_self 2 h0
    rw [h2] at h4; exact h4
  have h5 : w < 2 ^ j := by
    have h6 : w < 2 ^ (Nat.log 2 w + 1) := Nat.lt_pow_succ_log_self (by norm_num) w
    rw [h1] at h6; exact h6
  exact ⟨h3, h5⟩

/-- If `2^(j-1) ≤ w < 2^j` and `j ≥ 1`, then `dyadicLevel w = j`. -/
lemma dyadicLevel_eq {w j : ℕ} (h_j_pos : 0 < j)
    (h1 : 2^(j-1) ≤ w) (h2 : w < 2^j) : dyadicLevel w = j := by
  have h0 : w ≠ 0 := by
    by_contra h
    rw [h] at h1
    cases j with
    | zero => omega
    | succ j' => simp [pow_succ] at h1 <;> omega
  have h7 : Nat.log 2 w = j - 1 := by
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · exact h1
    · have h8 : w < 2 ^ ((j - 1) + 1) := by
        have h9 : (j - 1) + 1 = j := by omega
        rw [h9]; exact h2
      exact h8
  have h10 : dyadicLevel w = Nat.log 2 w + 1 := by
    simp [dyadicLevel, h0]
  rw [h10, h7] <;> omega

/-- Basic pigeonhole: some fiber of a map on a nonempty finite set has
cardinality at least the average `s.card / (s.image f).card`. -/
theorem exists_large_fiber (s : Finset α) (f : α → β) (hs : s.Nonempty) :
    ∃ y ∈ s.image f, (s.filter (fun x => f x = y)).card ≥
      s.card / (s.image f).card := by
  let fiber (y : β) := s.filter (fun x => f x = y)
  have h_sum : ∑ y ∈ s.image f, (fiber y).card = s.card := by
    have h1 : ∀ (y : β), (fiber y).card = ∑ x ∈ s, if f x = y then 1 else 0 := by
      intro y
      rw [Finset.card_filter]
      <;> rfl
    calc
      ∑ y ∈ s.image f, (fiber y).card
        = ∑ y ∈ s.image f, ∑ x ∈ s, if f x = y then 1 else 0 := by
          apply Finset.sum_congr rfl; intro y _; exact h1 y
      _ = ∑ x ∈ s, ∑ y ∈ s.image f, if f x = y then 1 else 0 := by rw [Finset.sum_comm]
      _ = ∑ x ∈ s, 1 := by
          apply Finset.sum_congr rfl; intro x hx
          have h2 : f x ∈ s.image f := Finset.mem_image_of_mem f hx
          simp [h2]
      _ = s.card := by simp
  have h_img_nonempty : (s.image f).Nonempty := s.image_nonempty.mpr hs
  have h_img_pos : 0 < (s.image f).card := Finset.card_pos.mpr h_img_nonempty
  by_contra! h_contra
  set q := s.card / (s.image f).card with hq
  have h_lt : ∑ y ∈ s.image f, (fiber y).card < (s.image f).card * q :=
    sum_lt_card_mul h_img_nonempty (fun y hy => h_contra y hy)
  have h_le : (s.image f).card * q ≤ s.card := Nat.mul_div_le _ _
  rw [h_sum] at h_lt
  exact not_le.mpr h_lt h_le

/-- Pigeonhole with bounded codomain: if `f : α → ℕ` takes values in `{0, ..., N-1}`,
some fiber has at least `s.card / N` elements. -/
theorem exists_large_fiber_bounded (s : Finset α) (f : α → ℕ) {N : ℕ} (hN : 0 < N)
    (h_bound : ∀ x ∈ s, f x < N) :
    ∃ k < N, (s.filter (fun x => f x = k)).card ≥ s.card / N := by
  by_cases hs : s.Nonempty
  · have h_img : (s.image f) ⊆ Finset.range N := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      exact Finset.mem_range.mpr (h_bound x hx)
    have h_card : (s.image f).card ≤ N := (Finset.card_le_card h_img).trans (by simp)
    have h_img_nonempty : (s.image f).Nonempty := s.image_nonempty.mpr hs
    have h_img_pos : 0 < (s.image f).card := Finset.card_pos.mpr h_img_nonempty
    have h_div : s.card / N ≤ s.card / (s.image f).card := by
      exact Nat.div_le_div_left h_card h_img_pos
    rcases exists_large_fiber s f hs with ⟨y, hy_mem, h_y⟩
    have h_y_lt_N : y < N := Finset.mem_range.mp (h_img hy_mem)
    exact ⟨y, h_y_lt_N, h_div.trans h_y⟩
  · exact ⟨0, hN, by simp [not_nonempty_iff_eq_empty.mp hs]⟩

/-- The level sets partition `s`. -/
lemma levelSets_partition (s : Finset α) (w : α → ℕ) {N : ℕ}
    (h_bound : ∀ x ∈ s, w x ≤ N) :
    let L := numDyadicLevels N
    let levelSet := fun j : ℕ => s.filter (fun x => dyadicLevel (w x) = j)
    (∀ j ∈ Finset.range L, True) ∧
    ((Finset.range L).biUnion levelSet = s) := by
  let L := numDyadicLevels N
  let levelSet := fun j : ℕ => s.filter (fun x => dyadicLevel (w x) = j)
  have h_union : (Finset.range L).biUnion levelSet = s := by
    ext x
    simp only [Finset.mem_biUnion, levelSet, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨j, _, hx, _⟩
      exact hx
    · intro hx
      exact ⟨dyadicLevel (w x), dyadicLevel_lt (h_bound x hx), hx, rfl⟩
  exact ⟨fun _ _ => trivial, h_union⟩

/-- Dyadic pigeonhole (count version): given weights `w : α → ℕ` bounded by `N > 0`,
there exists a dyadic level `j` such that the set of elements with weight in
that level has at least `s.card / numDyadicLevels N` elements.
Level 0: weight = 0; level j ≥ 1: `2^(j-1) ≤ weight < 2^j`. -/
theorem exists_dyadic_level_count (s : Finset α) (w : α → ℕ) {N : ℕ} (hN : 0 < N)
    (h_bound : ∀ x ∈ s, w x ≤ N) :
    ∃ j : ℕ, j ≤ Nat.log 2 N + 1 ∧
      (s.filter (fun x => dyadicLevel (w x) = j)).card ≥
      s.card / numDyadicLevels N := by
  let L := numDyadicLevels N
  let levelSet := fun j : ℕ => s.filter (fun x => dyadicLevel (w x) = j)
  have h_disj : (Finset.range L : Set ℕ).PairwiseDisjoint levelSet := by
    intro j _ k _ hjk
    simp only [Finset.disjoint_left, levelSet, Finset.mem_filter]
    intro x hx1 hx2
    have h1 : dyadicLevel (w x) = j := hx1.2
    have h2 : dyadicLevel (w x) = k := hx2.2
    have h3 : j = k := h1.symm.trans h2
    exact hjk h3
  have h_union : (Finset.range L).biUnion levelSet = s :=
    (levelSets_partition s w h_bound).2
  have h_sum : ∑ j ∈ Finset.range L, (levelSet j).card = s.card := by
    rw [← Finset.card_biUnion h_disj, h_union]
  have h_nonempty : (Finset.range L).Nonempty := by
    simp [L, numDyadicLevels] <;> omega
  by_contra! h_contra
  set q := s.card / L with hq
  have h_card_range : (Finset.range L).card = L := by simp
  have h_lt : ∑ j ∈ Finset.range L, (levelSet j).card < (Finset.range L).card * q :=
    sum_lt_card_mul h_nonempty (fun j hj =>
      have h_j_le : j ≤ Nat.log 2 N + 1 := by
        have h_j_lt : j < L := Finset.mem_range.mp hj
        have h_eq : L = Nat.log 2 N + 2 := by simp [L, numDyadicLevels]
        rw [h_eq] at h_j_lt; omega
      h_contra j h_j_le)
  rw [h_card_range] at h_lt
  have h_le : L * q ≤ s.card := Nat.mul_div_le _ _
  rw [h_sum] at h_lt
  exact not_le.mpr h_lt h_le

/-- Dyadic pigeonhole (weighted sum version): given weights `w : α → ℕ` bounded
by `N > 0`, there exists a dyadic level `j` such that the total weight of elements
in that level is at least `(∑ x ∈ s, w x) / numDyadicLevels N`. -/
theorem exists_dyadic_level_weighted (s : Finset α) (w : α → ℕ) {N : ℕ} (hN : 0 < N)
    (h_bound : ∀ x ∈ s, w x ≤ N) :
    ∃ j : ℕ, j ≤ Nat.log 2 N + 1 ∧
      ∑ x ∈ (s.filter (fun x => dyadicLevel (w x) = j)), w x ≥
      (∑ x ∈ s, w x) / numDyadicLevels N := by
  let L := numDyadicLevels N
  let levelSet := fun j : ℕ => s.filter (fun x => dyadicLevel (w x) = j)
  have h_disj : (Finset.range L : Set ℕ).PairwiseDisjoint levelSet := by
    intro j _ k _ hjk
    simp only [Finset.disjoint_left, levelSet, Finset.mem_filter]
    intro x hx1 hx2
    have h1 : dyadicLevel (w x) = j := hx1.2
    have h2 : dyadicLevel (w x) = k := hx2.2
    have h3 : j = k := h1.symm.trans h2
    exact hjk h3
  have h_union : (Finset.range L).biUnion levelSet = s :=
    (levelSets_partition s w h_bound).2
  have h_sum : ∑ j ∈ Finset.range L, ∑ x ∈ levelSet j, w x = ∑ x ∈ s, w x := by
    rw [← Finset.sum_biUnion h_disj, h_union]
  have h_nonempty : (Finset.range L).Nonempty := by
    simp [L, numDyadicLevels] <;> omega
  by_contra! h_contra
  set q := (∑ x ∈ s, w x) / L with hq
  let g : ℕ → ℕ := fun j => ∑ x ∈ levelSet j, w x
  have h_card_range : (Finset.range L).card = L := by simp
  have h_lt : ∑ j ∈ Finset.range L, g j < (Finset.range L).card * q :=
    sum_lt_card_mul h_nonempty (fun j hj =>
      have h_j_le : j ≤ Nat.log 2 N + 1 := by
        have h_j_lt : j < L := Finset.mem_range.mp hj
        have h_eq : L = Nat.log 2 N + 2 := by simp [L, numDyadicLevels]
        rw [h_eq] at h_j_lt; omega
      h_contra j h_j_le)
  rw [h_card_range] at h_lt
  have h_le : L * q ≤ ∑ x ∈ s, w x := Nat.mul_div_le _ _
  rw [h_sum] at h_lt
  exact not_le.mpr h_lt h_le

/-- Uniformization: given a function `w : α → ℕ` bounded by `N`, select a
subset `s' ⊆ s` such that all values of `w` on `s'` lie in a single dyadic level,
and `s'.card ≥ s.card / numDyadicLevels N`. -/
theorem uniformize_by_dyadic_level (s : Finset α) (w : α → ℕ) {N : ℕ} (hN : 0 < N)
    (h_bound : ∀ x ∈ s, w x ≤ N) :
    ∃ (s' : Finset α) (j : ℕ), s' ⊆ s ∧ j ≤ Nat.log 2 N + 1 ∧
      (∀ x ∈ s', dyadicLevel (w x) = j) ∧
      s'.card ≥ s.card / numDyadicLevels N := by
  rcases exists_dyadic_level_count s w hN h_bound with ⟨j, hj_le, h_card⟩
  let s' := s.filter (fun x => dyadicLevel (w x) = j)
  refine ⟨s', j, Finset.filter_subset _ _, hj_le, ?_, h_card⟩
  intro x hx
  exact (Finset.mem_filter.mp hx).2

/-- Uniformization with explicit interval condition: same as above but states
the dyadic interval condition directly. -/
theorem uniformize_by_dyadic_level' (s : Finset α) (w : α → ℕ) {N : ℕ} (hN : 0 < N)
    (h_bound : ∀ x ∈ s, w x ≤ N) :
    ∃ (s' : Finset α) (j : ℕ), s' ⊆ s ∧ j ≤ Nat.log 2 N + 1 ∧
      (∀ x ∈ s', if j = 0 then w x = 0 else 2^(j-1) ≤ w x ∧ w x < 2^j) ∧
      s'.card ≥ s.card / numDyadicLevels N := by
  rcases uniformize_by_dyadic_level s w hN h_bound with ⟨s', j, h_sub, hj_le, h_level, h_card⟩
  refine ⟨s', j, h_sub, hj_le, ?_, h_card⟩
  intro x hx
  have h_eq : dyadicLevel (w x) = j := h_level x hx
  by_cases hj : j = 0
  · simp [hj, dyadicLevel] at h_eq ⊢ <;> tauto
  · have h_j_pos : 0 < j := by omega
    have h_pos : 0 < w x := by
      by_cases h0 : w x = 0
      · simp [h0, dyadicLevel] at h_eq <;> omega
      · omega
    have h_spec := dyadicLevel_spec h_pos h_eq
    simp [hj, h_spec] <;> tauto

/-- Uniformization with positive weights: requires `w x > 0` for all `x ∈ s`.
Selects `s' ⊆ s` and `j ≥ 1` such that all weights in `s'` are in `[2^(j-1), 2^j)`,
and `s'.card ≥ s.card / numDyadicLevels N`. -/
theorem uniformize_positive_by_dyadic_level (s : Finset α) (w : α → ℕ) {N : ℕ} (hN : 0 < N)
    (h_bound : ∀ x ∈ s, w x ≤ N) (h_pos : ∀ x ∈ s, 0 < w x) :
    ∃ (s' : Finset α) (j : ℕ), s' ⊆ s ∧ 1 ≤ j ∧ j ≤ Nat.log 2 N + 1 ∧
      (∀ x ∈ s', 2^(j-1) ≤ w x ∧ w x < 2^j) ∧
      s'.card ≥ s.card / numDyadicLevels N := by
  by_cases h_s : s.Nonempty
  · rcases uniformize_by_dyadic_level s w hN h_bound with ⟨s', j, h_sub, hj_le, h_level, h_card⟩
    by_cases h_j0 : j = 0
    · -- Level 0 would mean w x = 0, but h_pos says w x > 0, so s' is empty.
      -- Thus s.card / L = 0, meaning s.card < L. Pick any single element.
      have h1 : ∀ x ∈ s', dyadicLevel (w x) = 0 := by
        intro x hx
        have h2 : dyadicLevel (w x) = j := h_level x hx
        rw [h_j0] at h2
        exact h2
      have h2 : ∀ x, x ∉ s' := by
        intro x
        intro hx
        have h3 : dyadicLevel (w x) = 0 := h1 x hx
        have h4 : w x = 0 := by
          simp [dyadicLevel] at h3 <;> omega
        have h5 : 0 < w x := h_pos x (h_sub hx)
        omega
      have h_s'_empty : s' = ∅ := Finset.eq_empty_iff_forall_notMem.mpr h2
      rw [h_s'_empty] at h_card
      have h_div : s.card / numDyadicLevels N = 0 := by
        have h : 0 ≥ s.card / numDyadicLevels N := by simpa using h_card
        exact le_antisymm h (by positivity)
      have h_small : s.card < numDyadicLevels N := by
        have h_posL : 0 < numDyadicLevels N := by simp [numDyadicLevels] <;> omega
        have h_iff : s.card / numDyadicLevels N = 0 ↔ numDyadicLevels N = 0 ∨ s.card < numDyadicLevels N :=
          Nat.div_eq_zero_iff
        rcases h_iff.mp h_div with (h | h)
        · omega
        · exact h
      rcases h_s with ⟨x, hx⟩
      let j' := dyadicLevel (w x)
      have h_j'_pos : 1 ≤ j' := by
        have hwx : w x ≠ 0 := by linarith [h_pos x hx]
        have h : dyadicLevel (w x) = Nat.log 2 (w x) + 1 := by
          simp [dyadicLevel, hwx]
        have h' : j' = Nat.log 2 (w x) + 1 := by
          exact h
        rw [h'] <;> omega
      have h_j'_le : j' ≤ Nat.log 2 N + 1 := by
        have h : dyadicLevel (w x) ≤ Nat.log 2 N + 1 := by
          have h2 := dyadicLevel_lt (h_bound x hx)
          simp [numDyadicLevels] at h2 ⊢ <;> omega
        exact h
      let s'' : Finset α := {x}
      refine ⟨s'', j', Finset.singleton_subset_iff.mpr hx, h_j'_pos, h_j'_le, ?_, ?_⟩
      · intro y hy
        have hy_eq : y = x := Finset.mem_singleton.mp hy
        rw [hy_eq]
        exact dyadicLevel_spec (h_pos x hx) rfl
      · have h : s''.card = 1 := by simp [s'']
        rw [h]
        have h9 : s.card / numDyadicLevels N = 0 := by
          have h_posL : 0 < numDyadicLevels N := by simp [numDyadicLevels] <;> omega
          have h_iff : s.card / numDyadicLevels N = 0 ↔ numDyadicLevels N = 0 ∨ s.card < numDyadicLevels N := Nat.div_eq_zero_iff
          exact h_iff.mpr (Or.inr h_small)
        rw [h9] <;> omega
    · have h_j_pos : 1 ≤ j := by omega
      refine ⟨s', j, h_sub, h_j_pos, by omega, ?_, h_card⟩
      intro x hx
      have h_eq : dyadicLevel (w x) = j := h_level x hx
      have h_posx : 0 < w x := h_pos x (h_sub hx)
      exact dyadicLevel_spec h_posx h_eq
  · have h_s_empty : s = ∅ := not_nonempty_iff_eq_empty.mp h_s
    refine ⟨∅, 1, by simp, by omega, by omega, (by simp), ?_⟩
    rw [h_s_empty]
    <;> simp

/-- Given a finite family of positive natural numbers bounded by `N`,
find a dyadic size range `[M, 2*M)` containing a `1 / numDyadicLevels N` fraction.
This is the combinatorial core of the pigeonholing in OS Proposition 5.1. -/
theorem exists_dyadic_size_subfamily {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) {N : ℕ} (hN : 0 < N)
    (h_bound : ∀ i ∈ s, f i ≤ N) (h_pos : ∀ i ∈ s, 0 < f i) :
    ∃ (M : ℕ) (s' : Finset ι), s' ⊆ s ∧
      (∀ i ∈ s', M ≤ f i ∧ f i < 2 * M) ∧
      s'.card ≥ s.card / numDyadicLevels N := by
  rcases uniformize_positive_by_dyadic_level s f hN h_bound h_pos with
    ⟨s', j, h_sub, h_j1, h_j2, h_range, h_card⟩
  let M := 2^(j-1)
  refine ⟨M, s', h_sub, ?_, h_card⟩
  intro i hi
  have h := h_range i hi
  have h1 : M ≤ f i := h.1
  have h2 : f i < 2 * M := by
    have h3 : f i < 2 ^ j := h.2
    have h4 : 2 ^ j = 2 * M := by
      cases j with
      | zero => omega
      | succ j' =>
        simp [M, pow_succ] <;> ring
    rw [h4] at h3
    exact h3
  exact ⟨h1, h2⟩
