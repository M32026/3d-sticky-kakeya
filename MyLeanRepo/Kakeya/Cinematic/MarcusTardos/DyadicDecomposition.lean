import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.BasicProperties
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Dyadic decomposition of a list

Recursive binary block splitting for the Marcus-Tardos proof.
Each list is recursively split into two almost-equal halves.

## Whiteprint node
- `DyadicDecomposition`
-/

namespace MarcusTardos

variable {α : Type*} [DecidableEq α]

/-! ### Definitions -/

/-- The left (first) half of a list. -/
def leftHalf (A : List α) : List α :=
  A.take (A.length / 2)

/-- The right (second) half of a list. -/
def rightHalf (A : List α) : List α :=
  A.drop (A.length / 2)

/-- Recursive binary block indexed by a path of Bools.
    The head of the path is the first (shallowest) split:
    `false` = left/first half, `true` = right/second half. -/
def block (A : List α) : List Bool → List α
  | [] => A
  | false :: s => block (leftHalf A) s
  | true :: s => block (rightHalf A) s

/-- All binary strings of length `l`. -/
def binaryStrings : ℕ → Finset (List Bool)
  | 0 => {[]}
  | l+1 => Finset.image (false :: ·) (binaryStrings l) ∪ Finset.image (true :: ·) (binaryStrings l)

/-! ### Basic block properties -/

/-- The empty path gives the whole list. -/
lemma block_nil (A : List α) : block A [] = A := by
  simp [block]

/-- The two halves concatenate to the original. -/
lemma left_append_right (A : List α) : leftHalf A ++ rightHalf A = A := by
  simp [leftHalf, rightHalf, List.take_append_drop]

/-- A block and its children: the two child blocks concatenate to the parent. -/
lemma block_append (A : List α) (s : List Bool) :
    block A (s ++ [false]) ++ block A (s ++ [true]) = block A s := by
  induction s generalizing A with
  | nil =>
    simp [block, leftHalf, rightHalf, List.take_append_drop]
  | cons b s ih =>
    let C := if b = false then leftHalf A else rightHalf A
    have h1 : block A (b :: s ++ [false]) = block C (s ++ [false]) := by
      cases b <;> simp [block, C] <;> rfl
    have h2 : block A (b :: s ++ [true]) = block C (s ++ [true]) := by
      cases b <;> simp [block, C] <;> rfl
    have h3 : block A (b :: s) = block C s := by
      cases b <;> simp [block, C] <;> rfl
    rw [h1, h2, h3]
    exact ih C

/-- Blocks inherit the nodup property. -/
lemma block_nodup {A : List α} (hA : A.Nodup) (s : List Bool) :
    (block A s).Nodup := by
  induction s generalizing A with
  | nil => exact hA
  | cons b s ih =>
    cases b with
    | false =>
      have h : (leftHalf A).Nodup := by
        have hsub : List.Sublist (leftHalf A) A := List.take_sublist _ _
        exact hA.sublist hsub
      exact ih h
    | true =>
      have h : (rightHalf A).Nodup := by
        have hsub : List.Sublist (rightHalf A) A := List.drop_sublist _ _
        exact hA.sublist hsub
      exact ih h

/-- Every block is a sublist of the original list. -/
lemma block_sublist (A : List α) (s : List Bool) : List.Sublist (block A s) A := by
  induction s generalizing A with
  | nil => simp [block]
  | cons b s ih =>
    cases b with
    | false =>
      have h1 : List.Sublist (block (leftHalf A) s) (leftHalf A) := ih (leftHalf A)
      have h2 : List.Sublist (leftHalf A) A := List.take_sublist _ _
      exact h1.trans h2
    | true =>
      have h1 : List.Sublist (block (rightHalf A) s) (rightHalf A) := ih (rightHalf A)
      have h2 : List.Sublist (rightHalf A) A := List.drop_sublist _ _
      exact h1.trans h2

/-- A sublist lifts to a multiset inequality. -/
private lemma sublist_multiset_le {l1 l2 : List α} (h : List.Sublist l1 l2) :
    (l1 : Multiset α) ≤ (l2 : Multiset α) := by
  have h_perm : List.Subperm l1 l2 := h.subperm
  exact Multiset.coe_le.mpr h_perm

/-- Monotonicity of multiset disjointness. -/
private lemma disjoint_mono {s1 s2 t1 t2 : Multiset α}
    (h : Disjoint s1 t1) (hs : s2 ≤ s1) (ht : t2 ≤ t1) : Disjoint s2 t2 := by
  rw [Multiset.disjoint_left] at h ⊢
  intro x hx2
  have hxs : x ∈ s1 := Multiset.mem_of_le hs hx2
  have hnt : x ∉ t1 := h hxs
  intro hxt2
  exact hnt (Multiset.mem_of_le ht hxt2)

/-! ### Size bounds -/

private lemma half_length_max (A : List α) (b : Bool) :
    (if b = false then leftHalf A else rightHalf A).length ≤ (A.length + 1) / 2 := by
  cases b <;> simp [leftHalf, rightHalf, List.length_take, List.length_drop] <;> omega

/-- Ceiling bound: block size at level l is at most ceil(A.length / 2^l). -/
lemma block_length_le_ceiling (A : List α) (s : List Bool) :
    (block A s).length ≤ (A.length + 2^s.length - 1) / 2^s.length := by
  induction s generalizing A with
  | nil =>
    simp [block] <;> omega
  | cons b s ih =>
    let C := if b = false then leftHalf A else rightHalf A
    have hC : C.length ≤ (A.length + 1) / 2 := half_length_max A b
    have h_ih : (block C s).length ≤ (C.length + 2^s.length - 1) / 2^s.length := ih C
    set y := 2^s.length with hy
    have hpos : 0 < y := by positivity
    have h1 : 2 * C.length ≤ A.length + 1 := by omega
    have h4 : 2 * y = 2^(s.length + 1) := by
      simp [hy, pow_succ] <;> ring
    have h2 : 2 * (C.length + y - 1) ≤ A.length + 2^(s.length + 1) - 1 := by omega
    have h3 : (C.length + y - 1) / y = (2 * (C.length + y - 1)) / (2 * y) := by
      exact (Nat.mul_div_mul_left _ _ (by norm_num)).symm
    have h_main : (C.length + y - 1) / y ≤ (A.length + 2^(s.length + 1) - 1) / 2^(s.length + 1) := by
      rw [h3, h4]
      exact Nat.div_le_div_right h2
    have h_eq : block A (b :: s) = block C s := by
      cases b <;> simp [block, C] <;> rfl
    rw [h_eq]
    exact le_trans h_ih h_main

/-- Division helper: `(a + b - 1) / b ≤ a / b + 1` for `b > 0`. -/
private lemma div_bound (a b : ℕ) (hpos : 0 < b) :
    (a + b - 1) / b ≤ a / b + 1 := by
  by_cases ha : a = 0
  · rw [ha]
    have h1 : (0 + b - 1) / b = 0 := by
      apply Nat.div_eq_of_lt
      omega
    rw [h1]
    exact Nat.zero_le _
  · have ha_pos : 0 < a := by omega
    have h1 : a + b - 1 ≤ a + b := by omega
    have h2 : (a + b - 1) / b ≤ (a + b) / b := by
      apply Nat.div_le_div
      <;> omega
    have h3 : (a + b) / b = a / b + 1 := by
      have h4 : b ∣ b := by simp
      have h5 : (a + b) / b = a / b + b / b := Nat.add_div_of_dvd_left h4
      rw [h5]
      have h6 : b / b = 1 := by
        apply Nat.div_self
        exact hpos
      rw [h6] <;> omega
    rw [h3] at h2
    exact h2

/-- Simple size bound: block size at level l is at most A.length / 2^l + 1. -/
lemma block_length_le (A : List α) (s : List Bool) :
    (block A s).length ≤ A.length / 2^s.length + 1 := by
  have h_ceiling := block_length_le_ceiling A s
  set b := 2^s.length with hb
  have hpos : 0 < b := by positivity
  have h4 : (A.length + b - 1) / b ≤ A.length / b + 1 := div_bound A.length b hpos
  exact le_trans h_ceiling h4

/-- If `2^k ≥ A.length`, every block at level `k` has length at most 1. -/
lemma block_length_le_one {A : List α} {k : ℕ} (h : 2^k ≥ A.length) :
    ∀ s : List Bool, s.length = k → (block A s).length ≤ 1 := by
  intro s hsk
  have h5 := block_length_le_ceiling A s
  rw [hsk] at h5
  have h8 : 0 < 2^k := by positivity
  have h9 : A.length + 2^k - 1 < 2 * 2^k := by omega
  have h10 : (A.length + 2^k - 1) / 2^k < 2 := by
    rw [Nat.div_lt_iff_lt_mul h8] <;> exact h9
  have h6 : (A.length + 2^k - 1) / 2^k ≤ 1 := by omega
  exact le_trans h5 h6

/-! ### binaryStrings properties -/

/-- Membership in binaryStrings: exactly the lists of length l. -/
lemma binaryStrings_mem {l : ℕ} {s : List Bool} :
    s ∈ binaryStrings l ↔ s.length = l := by
  have h_main : ∀ (l : ℕ), ∀ (t : List Bool), t ∈ binaryStrings l ↔ t.length = l := by
    intro l
    induction l with
    | zero =>
      intro t
      simp [binaryStrings] <;> omega
    | succ l ih =>
      intro t
      constructor
      · intro h
        rcases Finset.mem_union.mp h with (h1 | h2)
        · rcases Finset.mem_image.mp h1 with ⟨u, hu, rfl⟩
          have hul : u.length = l := (ih u).mp hu
          simp [hul, List.length_cons]
        · rcases Finset.mem_image.mp h2 with ⟨u, hu, rfl⟩
          have hul : u.length = l := (ih u).mp hu
          simp [hul, List.length_cons]
      · intro hlen
        cases t with
        | nil =>
          simp [List.length] at hlen <;> omega
        | cons b u =>
          have hul : u.length = l := by simp [List.length] at hlen <;> omega
          have hu : u ∈ binaryStrings l := (ih u).mpr hul
          by_cases hbf : b = false
          · rw [hbf]
            exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
          · have hbt : b = true := by
              have hbf' : b ≠ false := hbf
              cases b with
              | false => contradiction
              | true => rfl
            rw [hbt]
            exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
  exact h_main l s

/-- The two images in binaryStrings are disjoint. -/
private lemma binaryStrings_disjoint (l : ℕ) :
    Disjoint ((binaryStrings l).image (false :: ·))
        ((binaryStrings l).image (true :: ·)) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  rcases Finset.mem_image.mp hx1 with ⟨s, _, rfl⟩
  rcases Finset.mem_image.mp hx2 with ⟨t, _, h⟩
  simp [List.cons_eq_cons] at h
  <;> tauto

/-- Cardinality of binaryStrings is 2^l. -/
lemma binaryStrings_card (l : ℕ) : (binaryStrings l).card = 2^l := by
  induction l with
  | zero =>
    simp [binaryStrings] <;> norm_num
  | succ l ih =>
    have h_inj1 : Function.Injective (false :: ·) := fun x y h => by
      injection h <;> contradiction
    have h_inj2 : Function.Injective (true :: ·) := fun x y h => by
      injection h <;> contradiction
    have h_card1 : ((binaryStrings l).image (false :: ·)).card = (binaryStrings l).card :=
      Finset.card_image_of_injective (binaryStrings l) h_inj1
    have h_card2 : ((binaryStrings l).image (true :: ·)).card = (binaryStrings l).card :=
      Finset.card_image_of_injective (binaryStrings l) h_inj2
    have h_main : (binaryStrings (l + 1)).card =
        ((binaryStrings l).image (false :: ·)).card + ((binaryStrings l).image (true :: ·)).card := by
      rw [binaryStrings, Finset.card_union_of_disjoint (binaryStrings_disjoint l)] <;> rfl
    rw [h_main, h_card1, h_card2, ih] <;> ring

/-! ### Disjointness and partition -/

/-- Two halves of a nodup list are disjoint (as multisets). -/
private lemma halves_disjoint {A : List α} (hA : A.Nodup) :
    Disjoint (leftHalf A : Multiset α) (rightHalf A) := by
  have h : (leftHalf A ++ rightHalf A).Nodup := by
    rw [left_append_right] <;> exact hA
  have h_all : (leftHalf A).Nodup ∧ (rightHalf A).Nodup ∧ List.Disjoint (leftHalf A) (rightHalf A) :=
    (List.nodup_append').mp h
  have h_disj_list : List.Disjoint (leftHalf A) (rightHalf A) := h_all.2.2
  rw [Multiset.disjoint_left]
  intro x hx1 hx2
  have h1 : x ∈ leftHalf A := by simpa [Multiset.mem_coe] using hx1
  have h2 : x ∈ rightHalf A := by simpa [Multiset.mem_coe] using hx2
  exact h_disj_list h1 h2

/-- Helper: blocks from different halves are disjoint. -/
private lemma different_halves_disjoint {A : List α} (hA : A.Nodup)
    {s t : List Bool} {b c : Bool} (hne : b ≠ c) :
    Disjoint (block A (b :: s) : Multiset α) (block A (c :: t)) := by
  have hbf : b = false ∨ b = true := by fin_cases b <;> tauto
  rcases hbf with (hbf | hbf)
  · -- b = false, so c = true
    have hct : c = true := by
      have h : c = false ∨ c = true := by fin_cases c <;> tauto
      rcases h with (h | h)
      · exfalso; exact hne (by simp [h, hbf])
      · exact h
    rw [hbf, hct]
    have h1 : (block (leftHalf A) s : Multiset α) ≤ (leftHalf A : Multiset α) :=
      sublist_multiset_le (block_sublist (leftHalf A) s)
    have h2 : (block (rightHalf A) t : Multiset α) ≤ (rightHalf A : Multiset α) :=
      sublist_multiset_le (block_sublist (rightHalf A) t)
    simpa [block] using (halves_disjoint hA).mono h1 h2
  · -- b = true, so c = false
    have hcf : c = false := by
      have h : c = false ∨ c = true := by fin_cases c <;> tauto
      rcases h with (h | h)
      · exact h
      · exfalso; exact hne (by simp [h, hbf])
    rw [hbf, hcf]
    have h1 : (block (rightHalf A) s : Multiset α) ≤ (rightHalf A : Multiset α) :=
      sublist_multiset_le (block_sublist (rightHalf A) s)
    have h2 : (block (leftHalf A) t : Multiset α) ≤ (leftHalf A : Multiset α) :=
      sublist_multiset_le (block_sublist (leftHalf A) t)
    simpa [block] using (halves_disjoint hA).symm.mono h1 h2

/-- Blocks at the same level with different paths are disjoint (for nodup A). -/
lemma block_disjoint {A : List α} (hA : A.Nodup) {s t : List Bool}
    (hlen : s.length = t.length) (hne : s ≠ t) :
    Disjoint (block A s : Multiset α) (block A t) := by
  induction s generalizing A t with
  | nil =>
    have htl : t.length = 0 := by
      simpa [List.length] using hlen.symm
    have ht : t = [] := by
      cases t with
      | nil => rfl
      | cons _ _ => simp [List.length] at htl <;> omega
    rw [ht] at hne
    contradiction
  | cons b s ih =>
    cases t with
    | nil =>
      simp [List.length] at hlen <;> omega
    | cons c t' =>
      have hlen' : s.length = t'.length := by
        simp [List.length] at hlen <;> omega
      by_cases hbc : b = c
      · -- b = c: apply induction hypothesis to the appropriate half
        subst hbc
        have hne' : s ≠ t' := by
          intro h
          apply hne
          rw [h]
        have hbf : b = false ∨ b = true := by fin_cases b <;> tauto
        rcases hbf with (hbf | hbf)
        · -- b = false
          rw [hbf]
          have hC : (leftHalf A).Nodup := by
            have hsub : List.Sublist (leftHalf A) A := List.take_sublist _ _
            exact hA.sublist hsub
          have h_ih := ih hC hlen' hne'
          have h_eq1 : block A (false :: s) = block (leftHalf A) s := by simp [block]
          have h_eq2 : block A (false :: t') = block (leftHalf A) t' := by simp [block]
          rw [h_eq1, h_eq2]
          exact h_ih
        · -- b = true
          rw [hbf]
          have hC : (rightHalf A).Nodup := by
            have hsub : List.Sublist (rightHalf A) A := List.drop_sublist _ _
            exact hA.sublist hsub
          have h_ih := ih hC hlen' hne'
          have h_eq1 : block A (true :: s) = block (rightHalf A) s := by simp [block]
          have h_eq2 : block A (true :: t') = block (rightHalf A) t' := by simp [block]
          rw [h_eq1, h_eq2]
          exact h_ih
      · -- b ≠ c: blocks live in different halves
        exact different_halves_disjoint hA hbc

/-- Every element of A belongs to some block at each level. -/
lemma block_exists {A : List α} {a : α} (ha : a ∈ A) (l : ℕ) :
    ∃ s : List Bool, s.length = l ∧ a ∈ block A s := by
  induction l generalizing A with
  | zero =>
    refine' ⟨[], by simp, _⟩
    simpa [block] using ha
  | succ l ih =>
    have h_split : a ∈ leftHalf A ∨ a ∈ rightHalf A := by
      have h_mem : a ∈ leftHalf A ++ rightHalf A := by
        rw [left_append_right] <;> exact ha
      rw [List.mem_append] at h_mem
      exact h_mem
    cases h_split with
    | inl hL =>
      rcases ih hL with ⟨s, hsl, hs⟩
      refine' ⟨false :: s, by simp [hsl], _⟩
      simpa [block] using hs
    | inr hR =>
      rcases ih hR with ⟨s, hsl, hs⟩
      refine' ⟨true :: s, by simp [hsl], _⟩
      simpa [block] using hs

/-- The sum of block lengths at level l equals A.length. -/
lemma sum_block_lengths (A : List α) (l : ℕ) :
    Finset.sum (binaryStrings l) (fun s => (block A s).length) = A.length := by
  induction l generalizing A with
  | zero =>
    have h0 : binaryStrings 0 = ({[]} : Finset (List Bool)) := by
      rw [binaryStrings] <;> rfl
    rw [h0]
    rw [Finset.sum_singleton]
    <;> simp [block]
  | succ l ih =>
    have h_disj := binaryStrings_disjoint l
    have h_inj1 : Function.Injective (fun s : List Bool => false :: s) := by
      intro s t h
      simpa using h
    have h_inj2 : Function.Injective (fun s : List Bool => true :: s) := by
      intro s t h
      simpa using h
    have h_eq1 : Finset.sum (binaryStrings (l + 1)) (fun s => (block A s).length) =
        Finset.sum (binaryStrings l) (fun s => (block (leftHalf A) s).length) +
        Finset.sum (binaryStrings l) (fun s => (block (rightHalf A) s).length) := by
      rw [binaryStrings, Finset.sum_union h_disj,
          Finset.sum_image (fun x _ y _ h => h_inj1 h),
          Finset.sum_image (fun x _ y _ h => h_inj2 h)]
      <;> rfl
    rw [h_eq1]
    have hL := ih (leftHalf A)
    have hR := ih (rightHalf A)
    rw [hL, hR]
    have h_len : (leftHalf A).length + (rightHalf A).length = A.length := by
      rw [← List.length_append, left_append_right]
    exact h_len

end MarcusTardos
