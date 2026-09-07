module

/-
  Combinatorial block conversion for the multiscale decomposition.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.MultiscaleDecomposition

namespace MultiscaleBlockConversion

def buildBlocks (f : ℝ → ℝ) (s : ℝ) (m : ℕ) : List (ℝ × ℝ) → ℕ → List (ℕ × ℕ × Bool × ℝ)
  | [], pos =>
    if pos < m then [(pos, m, false, (s : ℝ))] else []
  | p :: rest, pos =>
    let l := Nat.ceil p.1
    let r := Nat.floor p.2
    let sl := chordSlope f p.1 p.2
    if pos < l then
      (pos, l, false, (s : ℝ)) :: (l, r, true, sl) :: buildBlocks f s m rest r
    else
      (l, r, true, sl) :: buildBlocks f s m rest r

def blockLen (b : ℕ × ℕ × Bool × ℝ) : ℕ := b.2.1 - b.1
def isStruct (b : ℕ × ℕ × Bool × ℝ) : Bool := b.2.2.1
def slopeLen (b : ℕ × ℕ × Bool × ℝ) : ℝ :=
  if isStruct b then b.2.2.2 * (b.2.1 - b.1 : ℝ) else 0

/-- Sum of block lengths. -/
def sumBlockLen (blocks : List (ℕ × ℕ × Bool × ℝ)) : ℕ :=
  (blocks.map blockLen).sum

/-- Sum of structured block lengths. -/
def sumStructLen (blocks : List (ℕ × ℕ × Bool × ℝ)) : ℕ :=
  ((blocks.filter isStruct).map blockLen).sum

/-- Sum of slope-weighted lengths. -/
def sumSlopeLen (blocks : List (ℕ × ℕ × Bool × ℝ)) : ℝ :=
  (blocks.map slopeLen).sum

/-- Rounded length of an interval. -/
def roundedLength (p : ℝ × ℝ) : ℕ := Nat.floor p.2 - Nat.ceil p.1

/-- Slope-weighted rounded length of an interval. -/
def slopeWeightedLength (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  chordSlope f p.1 p.2 * ((roundedLength p : ℝ))

/-- Comprehensive induction lemma for `buildBlocks`. -/
lemma buildBlocks_correct (f : ℝ → ℝ) (s : ℝ) (m : ℕ) :
    ∀ (ints : List (ℝ × ℝ)) (pos : ℕ), pos ≤ m →
      List.Pairwise (fun p q : ℝ × ℝ => p.2 ≤ q.1) ints →
      (∀ p ∈ ints, (pos : ℝ) ≤ p.1 ∧ p.2 ≤ (m : ℝ)) →
      (∀ p ∈ ints, Nat.ceil p.1 < Nat.floor p.2) →
      let blocks := buildBlocks f s m ints pos
      (pos < m → 0 < blocks.length) ∧
      (∀ (h : 0 < blocks.length), (blocks.get ⟨0, h⟩).1 = pos) ∧
      (∀ b ∈ blocks, b.1 < b.2.1) ∧
      (sumBlockLen blocks = m - pos) ∧
      (sumStructLen blocks = (ints.map roundedLength).sum) ∧
      (sumSlopeLen blocks = (ints.map (slopeWeightedLength f)).sum) := by
  intro ints
  induction ints with
  | nil =>
    intro pos h_pos h_disj h_bound h_round
    simp only [buildBlocks]
    split_ifs with h
    · -- pos < m
      simp [sumBlockLen, sumStructLen, sumSlopeLen, blockLen, isStruct, slopeLen, h]
      <;> omega
    · -- pos ≥ m
      simp [sumBlockLen, sumStructLen, sumSlopeLen, h]
      <;> omega
  | cons p rest ih =>
    intro pos h_pos h_disj h_bound h_round
    let l := Nat.ceil p.1
    let r := Nat.floor p.2
    let sl := chordSlope f p.1 p.2
    have h_l_lt_r : l < r := h_round p (by simp)
    have h_r_pos : 0 < r := by omega
    have h_one_le_r : 1 ≤ r := by omega
    have h_one_le_p2 : (1 : ℝ) ≤ p.2 := by
      exact_mod_cast (Nat.le_floor_iff' (hn := by norm_num)).mp h_one_le_r
    have h_p2_nonneg : 0 ≤ p.2 := by linarith
    have h_p1_nonneg : 0 ≤ p.1 := by
      have h : (0 : ℝ) ≤ (pos : ℝ) := by positivity
      have h' : (pos : ℝ) ≤ p.1 := (h_bound p (by simp)).1
      linarith
    have h1 : p.1 < p.2 := by
      have h2 : (p.1 : ℝ) ≤ ↑l := Nat.le_ceil p.1
      have h3 : (↑r : ℝ) ≤ p.2 := Nat.floor_le h_p2_nonneg
      have h4 : (↑l : ℝ) < (↑r : ℝ) := by exact_mod_cast h_l_lt_r
      linarith
    have h_pos_le_l : pos ≤ l := by
      have h1 : (pos : ℝ) ≤ p.1 := (h_bound p (by simp)).1
      have h2 : p.1 ≤ (l : ℝ) := Nat.le_ceil p.1
      have h3 : (pos : ℝ) ≤ (l : ℝ) := by linarith
      exact_mod_cast h3
    have h_r_le_m : r ≤ m := by
      have h1 : p.2 ≤ (m : ℝ) := (h_bound p (by simp)).2
      have h2 : (r : ℝ) ≤ p.2 := Nat.floor_le h_p2_nonneg
      have h3 : (r : ℝ) ≤ (m : ℝ) := by linarith
      exact_mod_cast h3
    have h_disj1 : ∀ q ∈ rest, p.2 ≤ q.1 := by
      cases h_disj with
      | cons h _ => exact h
    have h_disj_rest : List.Pairwise (fun p q : ℝ × ℝ => p.2 ≤ q.1) rest := by
      cases h_disj with
      | cons _ h => exact h
    have h_bound_rest : ∀ q ∈ rest, (r : ℝ) ≤ q.1 ∧ q.2 ≤ (m : ℝ) := by
      intro q hq
      have h1 : p.2 ≤ q.1 := h_disj1 q hq
      have h2 : (r : ℝ) ≤ p.2 := Nat.floor_le h_p2_nonneg
      have h3 : (r : ℝ) ≤ q.1 := by linarith
      have hq' : q ∈ p :: rest := by simp [hq]
      have h4 : q.2 ≤ (m : ℝ) := (h_bound q hq').2
      exact ⟨h3, h4⟩
    have h_round_rest : ∀ q ∈ rest, Nat.ceil q.1 < Nat.floor q.2 :=
      fun q hq =>
        have hq' : q ∈ p :: rest := by simp [hq]
        h_round q hq'
    have h_ih' := ih r h_r_le_m h_disj_rest h_bound_rest h_round_rest
    let blocks' := buildBlocks f s m rest r
    rcases h_ih' with ⟨h_ne', h_first', h_pos_len', h_sum', h_struct', h_slope'⟩
    have h_sl_eq : sl * ↑(r - l) = slopeWeightedLength f p := by
      simp [sl, l, r, slopeWeightedLength, roundedLength] <;> rfl
    have h_sl_false : slopeLen (pos, l, false, s) = 0 := by
      simp [slopeLen, isStruct] <;> rfl
    have h_sl_true : slopeLen (l, r, true, sl) = slopeWeightedLength f p := by
      have h_cast : (↑(r - l) : ℝ) = ↑r - ↑l := by
        exact Nat.cast_sub (show l ≤ r from le_of_lt h_l_lt_r)
      have h : sl * (↑r - ↑l) = slopeWeightedLength f p := by
        rw [← h_cast]
        exact h_sl_eq
      simpa [slopeLen, isStruct] using h
    have h_sl_cast : sl * (↑r - ↑l) = slopeWeightedLength f p := by
      have h_cast : (↑(r - l) : ℝ) = ↑r - ↑l := by
        exact Nat.cast_sub (show l ≤ r from le_of_lt h_l_lt_r)
      rw [← h_cast]
      exact h_sl_eq
    have h_rl : r - l = roundedLength p := by
      simp [roundedLength, l, r] <;> rfl
    have h_sumSlope_cons : ∀ (x : ℕ × ℕ × Bool × ℝ) (xs : List (ℕ × ℕ × Bool × ℝ)),
        sumSlopeLen (x :: xs) = slopeLen x + sumSlopeLen xs := by
      intro x xs
      simp [sumSlopeLen, List.map_cons, List.sum_cons]
    have h_slope'_sum : (blocks'.map slopeLen).sum = (List.map (slopeWeightedLength f) rest).sum := by
      simpa [sumSlopeLen] using h_slope'
    have h_struct'_sum : (List.map blockLen (List.filter isStruct blocks')).sum = (List.map roundedLength rest).sum := by
      simpa [sumStructLen] using h_struct'
    have h_sum'_sum : (List.map blockLen blocks').sum = m - r := by
      simpa [sumBlockLen] using h_sum'
    have h_pos'_split : ∀ (a a_1 : ℕ),
        ((∀ (b : ℝ), (a, a_1, false, b) ∈ blocks' → a < a_1) ∧
         (∀ (b : ℝ), (a, a_1, true, b) ∈ blocks' → a < a_1)) := by
      intro a a_1
      constructor
      · intro b h
        exact h_pos_len' (a, a_1, false, b) h
      · intro b h
        exact h_pos_len' (a, a_1, true, b) h
    by_cases h_case : pos < l
    · -- Case 1: pos < l
      have h_main : buildBlocks f s m (p :: rest) pos =
          (pos, l, false, s) :: (l, r, true, sl) :: blocks' := by
        simp [buildBlocks, h_case, l, r, sl, blocks'] <;> rfl
      have h_sum1 : (l - pos) + (r - l) + (m - r) = m - pos := by omega
      rw [h_main]
      simp [sumBlockLen, sumStructLen, sumSlopeLen, blockLen, isStruct, slopeLen,
        h_sum'_sum, h_struct'_sum, h_slope'_sum, h_sl_false, h_sl_cast, h_rl, h_sumSlope_cons,
        h_pos'_split, h_sum1, List.map_cons, List.sum_cons]
      <;> constructor <;> (try omega) <;> (try { tauto }) <;> (try { intro b hb; simp only [List.mem_cons] at hb; rcases hb with (rfl | rfl | hb); omega })
    · -- Case 2: pos ≥ l, so pos = l
      have h_pos_eq_l : pos = l := by omega
      have h_main : buildBlocks f s m (p :: rest) pos =
          (l, r, true, sl) :: blocks' := by
        simp [buildBlocks, h_case, h_pos_eq_l, l, r, sl, blocks'] <;> rfl
      have h_sum2 : (r - l) + (m - r) = m - pos := by
        rw [h_pos_eq_l] <;> omega
      rw [h_main]
      simp [sumBlockLen, sumStructLen, sumSlopeLen, blockLen, isStruct, slopeLen,
        h_sum'_sum, h_struct'_sum, h_slope'_sum, h_sl_cast, h_rl, h_sumSlope_cons,
        h_pos'_split, h_sum2, h_pos_eq_l, List.map_cons, List.sum_cons]
      <;> constructor <;> (try omega) <;> (try { tauto }) <;> (try { intro b hb; simp only [List.mem_cons] at hb; rcases hb with (rfl | hb); omega })

end MultiscaleBlockConversion
