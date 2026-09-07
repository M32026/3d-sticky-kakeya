import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.BasicProperties
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.DyadicDecomposition
import Mathlib.Tactic

/-!
# Block structure analysis for Marcus--Tardos

This module proves structural properties of blocks in cyclic
intersection-reverse sequences.

## Key results

- `posOf_sublist_lt`: relative order of `posOf` is preserved under sublists
- `IsIntersectionReverse.sublist`: sub-segments of IR sequences are IR
- `block_eq_drop_take`: dyadic blocks are drop-take segments
- `at_most_one_block_crosses_cut`: at most one block crosses a rotation cut
- `block_sublist_of_not_crossing`: non-crossing blocks are sublists of rotation
-/

namespace MarcusTardos

variable {α : Type*} [DecidableEq α]

/-! ### posOf and sublists -/

/-- The element at `Fin` position corresponding to `posOf a A` is `a`. -/
lemma finGet_posOf {a : α} {A : List α} (ha : a ∈ A) :
    A.get ⟨posOf a A, posOf_lt_length ha⟩ = a := by
  induction A with
  | nil => contradiction
  | cons x xs ih =>
    by_cases hx : x = a
    · have hpos : posOf a (x :: xs) = 0 := by simp [posOf, hx]
      have hlt : posOf a (x :: xs) < (x :: xs).length := posOf_lt_length ha
      have hfin : (⟨posOf a (x :: xs), hlt⟩ : Fin (x :: xs).length) = 0 := by
        apply Fin.ext
        simp [hpos]
      rw [hfin]
      simp [hx]
    · have ha' : a ∈ xs := by
        simp only [List.mem_cons] at ha
        tauto
      have hpos : posOf a (x :: xs) = 1 + posOf a xs := by
        simp [posOf, hx]
      have hlt : posOf a (x :: xs) < (x :: xs).length := posOf_lt_length ha
      let i : Fin xs.length := ⟨posOf a xs, posOf_lt_length ha'⟩
      have hlt2 : 1 + posOf a xs < (x :: xs).length := by
        rw [←hpos]; exact hlt
      have hfin : (⟨posOf a (x :: xs), hlt⟩ : Fin (x :: xs).length) = i.succ := by
        apply Fin.ext
        simp [hpos, i, add_comm]
      rw [hfin]
      have h_get : (x :: xs).get i.succ = xs.get i := List.get_cons_succ
      rw [h_get]
      exact ih ha'

/-- For nodup lists, if `A.get i = a` then `posOf a A = i.val`. -/
lemma posOf_unique {a : α} {A : List α} (hA : A.Nodup) {i : Fin A.length}
    (h : A.get i = a) : posOf a A = i.val := by
  have ha : a ∈ A := by
    have hmem : A.get i ∈ A := List.get_mem A i
    rwa [h] at hmem
  have h1 : A.get ⟨posOf a A, posOf_lt_length ha⟩ = a := finGet_posOf ha
  have h2 : A.get ⟨posOf a A, posOf_lt_length ha⟩ = A.get i := by rw [h1, h]
  have h3 : (⟨posOf a A, posOf_lt_length ha⟩ : Fin A.length) = i := by
    exact hA.injective_get h2
  exact congr_arg Fin.val h3

/--
For a nodup list `A` and a sublist `C`, the relative order of `posOf`
is preserved: `posOf a C < posOf b C ↔ posOf a A < posOf b A`.
-/
lemma posOf_sublist_lt {A C : List α} (hC : C.Sublist A) (hA : A.Nodup)
    {a b : α} (ha : a ∈ C) (hb : b ∈ C) (hne : a ≠ b) :
    posOf a C < posOf b C ↔ posOf a A < posOf b A := by
  rcases List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hC with ⟨f, hf⟩
  let ia : Fin C.length := ⟨posOf a C, posOf_lt_length ha⟩
  let ib : Fin C.length := ⟨posOf b C, posOf_lt_length hb⟩
  have h1 : C.get ia = a := finGet_posOf ha
  have h2 : C.get ib = b := finGet_posOf hb
  have h3 : A.get (f ia) = a := by rw [←hf ia, h1]
  have h4 : A.get (f ib) = b := by rw [←hf ib, h2]
  have h5 : posOf a A = (f ia).val := posOf_unique hA h3
  have h6 : posOf b A = (f ib).val := posOf_unique hA h4
  rw [h5, h6]
  have h7 : (ia : ℕ) < (ib : ℕ) ↔ (f ia : ℕ) < (f ib : ℕ) := by
    have h71 : (ia : ℕ) < (ib : ℕ) ↔ ia < ib := by rfl
    have h72 : (f ia : ℕ) < (f ib : ℕ) ↔ f ia < f ib := by rfl
    have h73 : ia < ib ↔ f ia < f ib := by
      constructor
      · intro h; exact f.strictMono h
      · intro h
        by_cases h' : ia < ib
        · exact h'
        · by_cases h'' : ia = ib
          · rw [h''] at h; exact False.elim (lt_irrefl _ h)
          · have h3 : ib < ia := by omega
            have h4 : f ib < f ia := f.strictMono h3
            exact False.elim (lt_asymm h h4)
    exact h71.trans (h73.trans h72.symm)
  simpa [ia, ib] using h7

/-!
### Intersection-reverse is preserved under sublists
-/
lemma IsIntersectionReverse.sublist {A B C D : List α}
    (h : IsIntersectionReverse A B)
    (hA : A.Nodup) (hB : B.Nodup)
    (hC : C.Sublist A) (hD : D.Sublist B) :
    IsIntersectionReverse C D := by
  intro a ha b hb hne haD hbD
  have haA : a ∈ A := hC.subset ha
  have hbA : b ∈ A := hC.subset hb
  have haB : a ∈ B := hD.subset haD
  have hbB : b ∈ B := hD.subset hbD
  have h1 : posOf a C < posOf b C ↔ posOf a A < posOf b A :=
    posOf_sublist_lt hC hA ha hb hne
  have h2 : posOf b D < posOf a D ↔ posOf b B < posOf a B :=
    posOf_sublist_lt hD hB hbD haD hne.symm
  have h_main : posOf a A < posOf b A ↔ posOf b B < posOf a B :=
    h a haA b hbA hne haB hbB
  rw [h1, h2]
  exact h_main

/-!
### Dyadic blocks and rotation cuts
-/

/-- Helper: `(A.take k).drop n |>.take m = A.drop n |>.take m` when `n + m ≤ k`. -/
private lemma take_drop_take_bound (A : List α) {k n m : ℕ} (h : n + m ≤ k) :
    List.take m (List.drop n (List.take k A)) = List.take m (List.drop n A) := by
  have h1 : n ≤ k := by omega
  have h2 : m ≤ k - n := by omega
  have h3 : List.drop n (List.take k A) = List.take (k - n) (List.drop n A) := by
    rw [List.drop_take]
  rw [h3, List.take_take]
  have h4 : min m (k - n) = m := by apply min_eq_left; omega
  rw [h4]

/-- Every dyadic block is a drop-take segment of the original list. -/
lemma block_eq_drop_take (A : List α) (s : List Bool) :
    ∃ (n m : ℕ), block A s = List.take m (List.drop n A) ∧ n + m ≤ A.length := by
  induction s generalizing A with
  | nil =>
    refine' ⟨0, A.length, _ , _⟩
    · have h : List.take A.length A = A := by simp
      simpa [block] using h
    · omega
  | cons b s ih =>
    let k := A.length / 2
    by_cases hb : b
    · -- b = true
      subst hb
      rcases ih (List.drop k A) with ⟨n, m, h_eq, h_bound⟩
      refine' ⟨k + n, m, _ , _⟩
      · have h1 : block A (true :: s) = block (List.drop k A) s := by
          change block A (true :: s) = block (rightHalf A) s
          rfl
        rw [h1, h_eq, List.drop_drop] <;> rfl
      · have h_len : (List.drop k A).length = A.length - k := by simp
        rw [h_len] at h_bound
        omega
    · -- b = false
      have hbf : b = false := by simp_all
      rw [hbf]
      rcases ih (List.take k A) with ⟨n, m, h_eq, h_bound⟩
      have h_len : (List.take k A).length = min k A.length := by simp
      have h_nmk : n + m ≤ k := by
        rw [h_len] at h_bound
        have h : min k A.length ≤ k := by apply min_le_left
        omega
      refine' ⟨n, m, _ , _⟩
      · have h1 : block A (false :: s) = block (List.take k A) s := by
          change block A (false :: s) = block (leftHalf A) s
          rfl
        rw [h1, h_eq]
        exact take_drop_take_bound A h_nmk
      · omega

/-- Helper: if n < m and n < A.length, then A.get ⟨n, hk⟩ ∈ take m A. -/
private lemma mem_take_at_index_aux : ∀ (n : ℕ),
    ∀ (A : List α) (m : ℕ) (hkm : n < m) (hk : n < A.length),
      A.get ⟨n, hk⟩ ∈ List.take m A := by
  intro n
  induction n with
  | zero =>
    intro A m hkm hk
    cases A with
    | nil =>
      simp at hk <;> omega
    | cons x xs =>
      cases m with
      | zero => omega
      | succ m =>
        have h : x ∈ List.take (m + 1) (x :: xs) := by
          simp [List.take] <;> tauto
        have h2 : (x :: xs).get ⟨0, hk⟩ = x := by simp
        rw [h2] <;> exact h
  | succ n ih =>
    intro A m hkm hk
    cases A with
    | nil =>
      simp at hk <;> omega
    | cons x xs =>
      cases m with
      | zero => omega
      | succ m =>
        have h_n_lt_xs : n < xs.length := by
          have h2 : (x :: xs).length = xs.length + 1 := by simp
          rw [h2] at hk
          omega
        have h_ih' := ih xs m (by omega) h_n_lt_xs
        have h_take_eq : List.take (m + 1) (x :: xs) = x :: List.take m xs := by
          simp [List.take]
        have h_main : xs.get ⟨n, h_n_lt_xs⟩ ∈ List.take (m + 1) (x :: xs) := by
          rw [h_take_eq]
          have h : xs.get ⟨n, h_n_lt_xs⟩ ∈ (x :: List.take m xs) := by
            apply List.mem_cons.mpr
            exact Or.inr h_ih'
          exact h
        have h_eq : (x :: xs).get ⟨n + 1, hk⟩ = xs.get ⟨n, h_n_lt_xs⟩ := by rfl
        rw [h_eq]
        exact h_main

/-- Helper: if n ≤ k < n+m and k < A.length, then A.get ⟨k, hk⟩ ∈ take m (drop n A). -/
private lemma elem_in_drop_take_aux : ∀ (n : ℕ),
    ∀ (A : List α) (m k : ℕ) (hn : n ≤ k) (hkm : k < n + m) (hk : k < A.length),
      A.get ⟨k, hk⟩ ∈ List.take m (List.drop n A) := by
  intro n
  induction n with
  | zero =>
    intro A m k hn hkm hk
    exact mem_take_at_index_aux k A m (by omega) hk
  | succ n ih =>
    intro A m k hn hkm hk
    cases A with
    | nil =>
      simp at hk <;> omega
    | cons x xs =>
      have h_k_pos : 0 < k := by omega
      have h_k'_lt : k - 1 < xs.length := by
        have h2 : (x :: xs).length = xs.length + 1 := by simp
        rw [h2] at hk
        omega
      have h_ih' := ih xs m (k - 1) (by omega) (by omega) h_k'_lt
      have h_drop_eq : List.drop (n + 1) (x :: xs) = List.drop n xs := by
        simp [List.drop]
      let k_fin : Fin (x :: xs).length := ⟨k, hk⟩
      let k'_fin : Fin xs.length := ⟨k - 1, h_k'_lt⟩
      have h_fin_eq : k_fin = Fin.succ k'_fin := by
        apply Fin.ext
        simp [k_fin, k'_fin] <;> omega
      have h_get_eq : (x :: xs).get k_fin = xs.get k'_fin := by
        rw [h_fin_eq] <;> rfl
      rw [h_drop_eq, h_get_eq]
      exact h_ih'

/-- Helper: if n ≤ k < n+m and k < A.length, then A[k] ∈ take m (drop n A). -/
private lemma elem_in_drop_take (A : List α) {n m k : ℕ}
    (hn : n ≤ k) (hkm : k < n + m) (hk : k < A.length) :
    A[k] ∈ List.take m (List.drop n A) :=
  elem_in_drop_take_aux n A m k hn hkm hk

/-- A block crosses position k if its interval contains k in its interior. -/
def BlockCrossesCut (A : List α) (s : List Bool) (k : ℕ) : Prop :=
  ∃ (n m : ℕ), block A s = List.take m (List.drop n A) ∧ n < k ∧ k < n + m

/-- At most one dyadic block at level l crosses position k. -/
lemma at_most_one_block_crosses_cut (A : List α) (hA : A.Nodup) (l k : ℕ)
    (hk : k < A.length) :
    ∃ (s0 : List Bool), ∀ (s : List Bool), s.length = l →
      BlockCrossesCut A s k → s = s0 := by
  classical
  by_cases h_exists : ∃ (s : List Bool), s.length = l ∧ BlockCrossesCut A s k
  · rcases h_exists with ⟨s0, hsl, hcross⟩
    refine' ⟨s0, _⟩
    intro s hsl' hcross'
    by_cases h_eq_s : s0 = s
    · exact h_eq_s.symm
    · rcases hcross with ⟨n, m, h_eq, hn, hnm⟩
      rcases hcross' with ⟨n', m', h_eq', hn', hnm'⟩
      have h_in1 : A[k] ∈ block A s0 := by
        rw [h_eq]
        exact elem_in_drop_take A (by omega) (by omega) hk
      have h_in2 : A[k] ∈ block A s := by
        rw [h_eq']
        exact elem_in_drop_take A (by omega) (by omega) hk
      have hlen : s0.length = s.length := by rw [hsl, hsl']
      have h_disj : Disjoint (block A s0 : Multiset α) (block A s : Multiset α) :=
        block_disjoint hA hlen h_eq_s
      have h_contra : A[k] ∉ (block A s : Multiset α) :=
        Multiset.disjoint_left.mp h_disj h_in1
      exact False.elim (h_contra (Multiset.mem_coe.mpr h_in2))
  · refine' ⟨[], _⟩
    intro s hsl hcross
    exact False.elim (h_exists ⟨s, hsl, hcross⟩)

/-- If a block does not cross cut k, it is a sublist of `A.drop k ++ A.take k`. -/
lemma block_sublist_of_not_crossing (A : List α) (s : List Bool) (k : ℕ)
    (h_not_cross : ¬BlockCrossesCut A s k) :
    (block A s).Sublist (List.drop k A ++ List.take k A) := by
  rcases block_eq_drop_take A s with ⟨n, m, h_eq, h_bound⟩
  have h_case : n + m ≤ k ∨ k ≤ n := by
    by_contra h
    push Not at h
    have h' : BlockCrossesCut A s k := ⟨n, m, h_eq, h.2, h.1⟩
    exact h_not_cross h'
  rw [h_eq]
  rcases h_case with (h_case | h_case)
  · -- n + m ≤ k: block is within A.take k
    have h_eq2 : List.take m (List.drop n A) = List.take m (List.drop n (List.take k A)) := by
      exact (take_drop_take_bound A h_case).symm
    rw [h_eq2]
    have h1a : (List.take m (List.drop n (List.take k A))).Sublist (List.drop n (List.take k A)) :=
      List.take_sublist m (List.drop n (List.take k A))
    have h1b : (List.drop n (List.take k A)).Sublist (List.take k A) :=
      List.drop_sublist n (List.take k A)
    have h1 : (List.take m (List.drop n (List.take k A))).Sublist (List.take k A) :=
      h1a.trans h1b
    have h3 : (List.take k A).Sublist (List.drop k A ++ List.take k A) := List.sublist_append_right _ _
    exact h1.trans h3
  · -- k ≤ n: block is within A.drop k
    have h2 : List.drop n A = List.drop (n - k) (List.drop k A) := by
      have h_sum2 : k + (n - k) = n := by omega
      have h4 : List.drop (n - k) (List.drop k A) = List.drop n A := by
        calc
          List.drop (n - k) (List.drop k A)
            = List.drop (k + (n - k)) A := by rw [List.drop_drop]
          _ = List.drop n A := by rw [h_sum2]
      exact h4.symm
    rw [h2]
    have h1a : (List.take m (List.drop (n - k) (List.drop k A))).Sublist (List.drop (n - k) (List.drop k A)) :=
      List.take_sublist m (List.drop (n - k) (List.drop k A))
    have h1b : (List.drop (n - k) (List.drop k A)).Sublist (List.drop k A) :=
      List.drop_sublist (n - k) (List.drop k A)
    have h1 : (List.take m (List.drop (n - k) (List.drop k A))).Sublist (List.drop k A) :=
      h1a.trans h1b
    have h3 : (List.drop k A).Sublist (List.drop k A ++ List.take k A) := List.sublist_append_left _ _
    exact h1.trans h3

end MarcusTardos
