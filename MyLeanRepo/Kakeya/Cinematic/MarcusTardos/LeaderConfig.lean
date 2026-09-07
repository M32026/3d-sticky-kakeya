import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.BlockStructure
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.OrderFunction
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.DyadicDecomposition
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Definitions
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.BlockLemma
import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Leader pair configuration for Marcus-Tardos Theorem 1
-/

namespace MarcusTardos.LeaderConfig

open BigOperators Finset

variable {α : Type*} [DecidableEq α]

/-! ### posOf and take/drop helpers -/

/-- If the head is not the search element, `posOf` shifts by 1. -/
lemma posOf_cons_of_ne {a x : α} {xs : List α} (h : a ≠ x) :
    posOf x (a :: xs) = 1 + posOf x xs := by
  simp [posOf, h]

/-- If `x ∈ take k A` (nodup), then `posOf x A < k`. -/
lemma posOf_lt_of_mem_take {A : List α} (hA : A.Nodup) {k : ℕ} {x : α}
    (hx : x ∈ List.take k A) : posOf x A < k := by
  have h_main : ∀ (L : List α), L.Nodup → ∀ (n : ℕ), x ∈ List.take n L → posOf x L < n := by
    intro L hL
    induction L with
    | nil => intro n hn; simp at hn
    | cons a xs ih =>
      intro n hn
      cases n with
      | zero => simp at hn
      | succ n' =>
        simp [List.take] at hn
        rcases hn with (rfl | hn)
        · simp [posOf] <;> omega
        · by_cases hxa : x = a
          · simp [posOf, hxa] <;> omega
          · have hne : a ≠ x := by intro h; exact hxa h.symm
            have h_ih : posOf x xs < n' := ih (List.nodup_cons.mp hL).2 n' hn
            have h_pos : posOf x (a :: xs) = 1 + posOf x xs := posOf_cons_of_ne hne
            rw [h_pos]
            omega
  exact h_main A hA k hx

/-- If `x ∈ drop k A` (nodup), then `k ≤ posOf x A`. -/
lemma posOf_ge_of_mem_drop {A : List α} (hA : A.Nodup) {k : ℕ} {x : α}
    (hx : x ∈ List.drop k A) : k ≤ posOf x A := by
  have h_main : ∀ (L : List α), L.Nodup → ∀ (n : ℕ), x ∈ List.drop n L → n ≤ posOf x L := by
    intro L hL
    induction L with
    | nil => intro n hn; simp at hn
    | cons a xs ih =>
      intro n hn
      cases n with
      | zero => simp [List.drop] at hn ⊢ <;> omega
      | succ n' =>
        simp [List.drop] at hn
        have hxa : x ≠ a := by
          intro h
          have h2 : x ∈ xs := List.mem_of_mem_drop hn
          have h1 : a ∉ xs := (List.nodup_cons.mp hL).1
          exact h1 (h ▸ h2)
        have hne : a ≠ x := by intro h; exact hxa h.symm
        have h_ih : n' ≤ posOf x xs := ih (List.nodup_cons.mp hL).2 n' hn
        have h_pos : posOf x (a :: xs) = 1 + posOf x xs := posOf_cons_of_ne hne
        rw [h_pos]
        omega
  exact h_main A hA k hx

/-- For `x ∈ take k A`, `posOf x (take k A) = posOf x A`. -/
lemma posOf_take_eq {A : List α} (hA : A.Nodup) {k : ℕ} {x : α}
    (hx : x ∈ List.take k A) : posOf x (List.take k A) = posOf x A := by
  have h_main : ∀ (L : List α), L.Nodup → ∀ (n : ℕ), x ∈ List.take n L →
      posOf x (List.take n L) = posOf x L := by
    intro L hL
    induction L with
    | nil => intro n hn; simp at hn
    | cons a xs ih =>
      intro n hn
      cases n with
      | zero => simp at hn
      | succ n' =>
        have h_take : List.take (n' + 1) (a :: xs) = a :: List.take n' xs := by
          simp [List.take]
        rw [h_take]
        have hn' : x = a ∨ x ∈ List.take n' xs := by
          simpa [List.take] using hn
        rcases hn' with (rfl | hn')
        · simp [posOf]
        · have hne : a ≠ x := by
            intro h
            have h2 : x ∈ xs := List.mem_of_mem_take hn'
            have h3 : a ∉ xs := (List.nodup_cons.mp hL).1
            exact h3 (h ▸ h2)
          have h_ih : posOf x (List.take n' xs) = posOf x xs :=
            ih (List.nodup_cons.mp hL).2 n' hn'
          rw [posOf_cons_of_ne hne, posOf_cons_of_ne hne, h_ih]
  exact h_main A hA k hx

/-- For `x ∈ drop k A`, `posOf x A = k + posOf x (drop k A)`. -/
lemma posOf_drop_eq {A : List α} (hA : A.Nodup) {k : ℕ} {x : α}
    (hx : x ∈ List.drop k A) : posOf x A = k + posOf x (List.drop k A) := by
  have h_main : ∀ (L : List α), L.Nodup → ∀ (n : ℕ), x ∈ List.drop n L →
      posOf x L = n + posOf x (List.drop n L) := by
    intro L hL
    induction L with
    | nil => intro n hn; simp at hn
    | cons a xs ih =>
      intro n hn
      cases n with
      | zero =>
        have h_drop : List.drop 0 (a :: xs) = a :: xs := by simp
        calc
          posOf x (a :: xs)
            = 0 + posOf x (a :: xs) := by simp
          _ = 0 + posOf x (List.drop 0 (a :: xs)) := by rw [h_drop]
      | succ n' =>
        have h_drop : List.drop (n' + 1) (a :: xs) = List.drop n' xs := by
          simp [List.drop]
        have hn' : x ∈ List.drop n' xs := by simpa [List.drop] using hn
        have hxa : x ≠ a := by
          intro h
          have h2 : x ∈ xs := List.mem_of_mem_drop hn'
          have h1 : a ∉ xs := (List.nodup_cons.mp hL).1
          exact h1 (h ▸ h2)
        have hne : a ≠ x := by intro h; exact hxa h.symm
        have h_ih : posOf x xs = n' + posOf x (List.drop n' xs) :=
          ih (List.nodup_cons.mp hL).2 n' hn'
        have h_pos : posOf x (a :: xs) = 1 + posOf x xs := posOf_cons_of_ne hne
        rw [h_pos, h_ih, h_drop]
        <;> ring
  exact h_main A hA k hx

/-- For `x ∈ leftHalf A`, `posOf x A = posOf x (leftHalf A)`. -/
lemma posOf_leftHalf {A : List α} (hA : A.Nodup) {x : α} (hx : x ∈ leftHalf A) :
    posOf x A = posOf x (leftHalf A) :=
  (posOf_take_eq hA hx).symm

/-- For `x ∈ rightHalf A`, `posOf x A = A.length / 2 + posOf x (rightHalf A)`. -/
lemma posOf_rightHalf {A : List α} (hA : A.Nodup) {x : α} (hx : x ∈ rightHalf A) :
    posOf x A = A.length / 2 + posOf x (rightHalf A) :=
  posOf_drop_eq hA hx

/-! ### Ordering of dyadic blocks -/

/--
For two distinct dyadic blocks at the same level, all elements of one
precede all elements of the other.
-/
lemma blocks_ordered {A : List α} (hA : A.Nodup) {l : ℕ}
    {s t : List Bool} (hsl : s.length = l) (htl : t.length = l) (hne : s ≠ t) :
    (∀ x ∈ block A s, ∀ y ∈ block A t, posOf x A < posOf y A) ∨
    (∀ x ∈ block A t, ∀ y ∈ block A s, posOf x A < posOf y A) := by
  induction l generalizing A s t with
  | zero =>
    have hsl0 : s.length = 0 := by simpa using hsl
    have htl0 : t.length = 0 := by simpa using htl
    have hs' : s = [] := by simpa [List.length_eq_zero_iff] using hsl0
    have ht' : t = [] := by simpa [List.length_eq_zero_iff] using htl0
    subst hs' ht'
    contradiction
  | succ l ih =>
    cases s with
    | nil => simp at hsl
    | cons b s' =>
      cases t with
      | nil => simp at htl
      | cons c t' =>
        have hsl' : s'.length = l := by simp [List.length] at hsl <;> omega
        have htl' : t'.length = l := by simp [List.length] at htl <;> omega
        by_cases hbc : b = c
        · subst hbc
          cases b with
          | false =>
            have hA2 : (leftHalf A).Nodup := hA.sublist (List.take_sublist _ _)
            have h_ih := ih hA2 hsl' htl' (by intro h; apply hne; simp [h])
            rcases h_ih with (h_ih | h_ih)
            · left
              intro x hx y hy
              have hx' : x ∈ block (leftHalf A) s' := by simpa [block] using hx
              have hy' : y ∈ block (leftHalf A) t' := by simpa [block] using hy
              have h1 : posOf x (leftHalf A) < posOf y (leftHalf A) := h_ih x hx' y hy'
              have hsubx : x ∈ leftHalf A := (block_sublist (leftHalf A) s').subset hx'
              have hsuby : y ∈ leftHalf A := (block_sublist (leftHalf A) t').subset hy'
              rw [posOf_leftHalf hA hsubx, posOf_leftHalf hA hsuby]; exact h1
            · right
              intro x hx y hy
              have hx' : x ∈ block (leftHalf A) t' := by simpa [block] using hx
              have hy' : y ∈ block (leftHalf A) s' := by simpa [block] using hy
              have h1 : posOf x (leftHalf A) < posOf y (leftHalf A) := h_ih x hx' y hy'
              have hsubx : x ∈ leftHalf A := (block_sublist (leftHalf A) t').subset hx'
              have hsuby : y ∈ leftHalf A := (block_sublist (leftHalf A) s').subset hy'
              rw [posOf_leftHalf hA hsubx, posOf_leftHalf hA hsuby]; exact h1
          | true =>
            have hA2 : (rightHalf A).Nodup := hA.sublist (List.drop_sublist _ _)
            have h_ih := ih hA2 hsl' htl' (by intro h; apply hne; simp [h])
            rcases h_ih with (h_ih | h_ih)
            · left
              intro x hx y hy
              have hx' : x ∈ block (rightHalf A) s' := by simpa [block] using hx
              have hy' : y ∈ block (rightHalf A) t' := by simpa [block] using hy
              have h1 : posOf x (rightHalf A) < posOf y (rightHalf A) := h_ih x hx' y hy'
              have hsubx : x ∈ rightHalf A := (block_sublist (rightHalf A) s').subset hx'
              have hsuby : y ∈ rightHalf A := (block_sublist (rightHalf A) t').subset hy'
              rw [posOf_rightHalf hA hsubx, posOf_rightHalf hA hsuby] <;> omega
            · right
              intro x hx y hy
              have hx' : x ∈ block (rightHalf A) t' := by simpa [block] using hx
              have hy' : y ∈ block (rightHalf A) s' := by simpa [block] using hy
              have h1 : posOf x (rightHalf A) < posOf y (rightHalf A) := h_ih x hx' y hy'
              have hsubx : x ∈ rightHalf A := (block_sublist (rightHalf A) t').subset hx'
              have hsuby : y ∈ rightHalf A := (block_sublist (rightHalf A) s').subset hy'
              rw [posOf_rightHalf hA hsubx, posOf_rightHalf hA hsuby] <;> omega
        · -- b ≠ c
          by_cases hbf : b = false
          · -- b = false, so c = true
            have hc : c = true := by
              by_cases h : c = false
              · exfalso; exact hbc (by rw [hbf, h])
              · simpa using h
            have hbs : block A (b :: s') = block (leftHalf A) s' := by simp [block, hbf]
            have hbt : block A (c :: t') = block (rightHalf A) t' := by simp [block, hc]
            left
            intro x hx y hy
            have hxL : x ∈ leftHalf A := by
              rw [hbs] at hx; exact (block_sublist (leftHalf A) s').subset hx
            have hyR : y ∈ rightHalf A := by
              rw [hbt] at hy; exact (block_sublist (rightHalf A) t').subset hy
            have h1 : posOf x A < A.length / 2 := posOf_lt_of_mem_take hA hxL
            have h2 : A.length / 2 ≤ posOf y A := posOf_ge_of_mem_drop hA hyR
            omega
          · -- b ≠ false, so b = true, hence c = false
            have hbt : b = true := by
              by_cases h : b = true
              · exact h
              · exfalso; exact hbf (by simpa using h)
            have hc : c = false := by
              by_cases h : c = true
              · exfalso; exact hbc (by rw [hbt, h])
              · simpa using h
            have hbs : block A (b :: s') = block (rightHalf A) s' := by simp [block, hbt]
            have hbt' : block A (c :: t') = block (leftHalf A) t' := by simp [block, hc]
            right
            intro x hx y hy
            have hxL : x ∈ leftHalf A := by
              rw [hbt'] at hx; exact (block_sublist (leftHalf A) t').subset hx
            have hyR : y ∈ rightHalf A := by
              rw [hbs] at hy; exact (block_sublist (rightHalf A) s').subset hy
            have h1 : posOf x A < A.length / 2 := posOf_lt_of_mem_take hA hxL
            have h2 : A.length / 2 ≤ posOf y A := posOf_ge_of_mem_drop hA hyR
            omega

/-! ### Boundary-straddling lemma -/

/--
At most one dyadic block at level `l` intersects both `S` and `T`,
when every element of `S` precedes every element of `T` in `A`.
-/
lemma at_most_one_intersects_both {A : List α} (hA : A.Nodup) (l : ℕ)
    (S T : Finset α)
    (h_sep : ∀ s ∈ S, ∀ t ∈ T, posOf s A < posOf t A) :
    ∀ (s t : List Bool), s.length = l → t.length = l →
      (∃ x, x ∈ S ∧ x ∈ block A s) → (∃ x, x ∈ T ∧ x ∈ block A s) →
      (∃ x, x ∈ S ∧ x ∈ block A t) → (∃ x, x ∈ T ∧ x ∈ block A t) →
      s = t := by
  intro s t hsl htl hSs hTs hSt hTt
  by_contra hne
  have h_order := blocks_ordered hA hsl htl hne
  rcases h_order with (h_before | h_after)
  · -- s before t
    rcases hTs with ⟨t_s, ht_s, hts_in⟩
    rcases hSt with ⟨s_t, hs_t, hst_in⟩
    have h1 : posOf t_s A < posOf s_t A := h_before t_s hts_in s_t hst_in
    have h2 : posOf s_t A < posOf t_s A := h_sep s_t hs_t t_s ht_s
    omega
  · -- t before s
    rcases hTt with ⟨t_t, ht_t, htt_in⟩
    rcases hSs with ⟨s_s, hs_s, hss_in⟩
    have h1 : posOf t_t A < posOf s_s A := h_after t_t htt_in s_s hss_in
    have h2 : posOf s_s A < posOf t_t A := h_sep s_s hs_s t_t ht_t
    omega

end MarcusTardos.LeaderConfig
