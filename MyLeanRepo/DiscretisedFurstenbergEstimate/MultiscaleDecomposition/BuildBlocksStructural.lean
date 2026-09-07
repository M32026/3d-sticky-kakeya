module

/-
  Supplementary structural lemmas for buildBlocks.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.BlockConversion
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.MultiscaleDecomposition

namespace MultiscaleBlockConversion

/-- get ⟨0, h⟩ equals headI for nonempty lists. -/
lemma get_zero_eq_headI {α : Type*} [Inhabited α] {l : List α} (h : 0 < l.length) :
    l.get ⟨0, h⟩ = l.headI := by
  cases l with
  | nil => contradiction
  | cons a t => rfl

/-- Adjacency, last-block, empty, and first-block properties. -/
lemma buildBlocks_adjacent (f : ℝ → ℝ) (s : ℝ) (m : ℕ) :
    ∀ (ints : List (ℝ × ℝ)) (pos : ℕ), pos ≤ m →
      List.Pairwise (fun p q : ℝ × ℝ => p.2 ≤ q.1) ints →
      (∀ p ∈ ints, (pos : ℝ) ≤ p.1 ∧ p.2 ≤ (m : ℝ)) →
      (∀ p ∈ ints, Nat.ceil p.1 < Nat.floor p.2) →
      let blocks := buildBlocks f s m ints pos
      (blocks = [] ↔ pos = m) ∧
      (blocks ≠ [] → (blocks.headI).1 = pos) ∧
      (∀ (j : ℕ) (hj : j + 1 < blocks.length),
         (blocks.get ⟨j, Nat.lt_of_succ_lt hj⟩).2.1 =
         (blocks.get ⟨j + 1, hj⟩).1) ∧
      (∀ (h : blocks ≠ []), (blocks.getLast h).2.1 = m) := by
  intro ints
  induction ints with
  | nil =>
    intro pos h_pos h_disj h_bound h_round
    dsimp only [buildBlocks]
    split_ifs with h
    · simp [h, List.getLast_cons] <;> omega
    · have h_pos_eq : pos = m := by omega
      simp [h, h_pos_eq] <;> omega
  | cons p rest ih =>
    intro pos h_pos h_disj h_bound h_round
    let l := Nat.ceil p.1
    let r := Nat.floor p.2
    have h_lr : l < r := h_round p (by simp)
    have h_p2_nonneg : 0 ≤ p.2 := by
      by_contra h
      have h5 : p.2 < 0 := by linarith
      have h6 : Nat.floor p.2 = 0 := by
        rw [Nat.floor_eq_zero.mpr] <;> linarith
      have h7 : l < Nat.floor p.2 := by simpa [r] using h_lr
      rw [h6] at h7
      exact Nat.not_lt_zero _ h7
    have h_p1_lt_p2 : p.1 < p.2 := by
      have h1 : (p.1 : ℝ) ≤ (l : ℝ) := Nat.le_ceil p.1
      have h2 : (r : ℝ) ≤ (p.2 : ℝ) := Nat.floor_le h_p2_nonneg
      have h3 : (l : ℝ) < (r : ℝ) := by exact_mod_cast h_lr
      linarith
    have h_r_le_m : r ≤ m := by
      have h1 : p.2 ≤ (m : ℝ) := (h_bound p (by simp)).2
      have h2 : (r : ℝ) ≤ p.2 := Nat.floor_le h_p2_nonneg
      have h3 : (r : ℝ) ≤ (m : ℝ) := by linarith
      exact_mod_cast h3
    have h_disj_rest : List.Pairwise (fun p q => p.2 ≤ q.1) rest :=
      (List.pairwise_cons.mp h_disj).2
    have h_bound_rest : ∀ q ∈ rest, (r : ℝ) ≤ q.1 ∧ q.2 ≤ (m : ℝ) := by
      intro q hq
      have h1 : p.2 ≤ q.1 := (List.pairwise_cons.mp h_disj).1 q hq
      have h2 : (r : ℝ) ≤ p.2 := Nat.floor_le h_p2_nonneg
      have h3 : (r : ℝ) ≤ q.1 := by linarith
      have h4 : q.2 ≤ (m : ℝ) := (h_bound q (by simp [hq])).2
      exact ⟨h3, h4⟩
    have h_round_rest : ∀ q ∈ rest, Nat.ceil q.1 < Nat.floor q.2 :=
      fun q hq => h_round q (by simp [hq])
    rcases ih r h_r_le_m h_disj_rest h_bound_rest h_round_rest
      with ⟨h_empty_rest, h_first_rest, h_adj_rest, h_last_rest⟩
    by_cases h_case : pos < l
    · -- Case pos < l
      let rest_blocks := buildBlocks f s m rest r
      let sl := chordSlope f p.1 p.2
      have h_main : buildBlocks f s m (p :: rest) pos =
          (pos, l, false, s) :: (l, r, true, sl) :: rest_blocks := by
        simp [buildBlocks, h_case, l, r, sl] <;> rfl
      have h_ne : pos ≠ m := by
        have h1 : l ≤ r := le_of_lt h_lr
        have h2 : r ≤ m := h_r_le_m
        omega
      rw [h_main]
      constructor
      · simp [h_empty_rest, h_ne]
      constructor
      · intro h; simp [h_first_rest]
      constructor
      · intro j hj
        induction j with
        | zero => simp
        | succ j' =>
          cases j' with
          | zero =>
            have h_rest_ne : rest_blocks ≠ [] := by
              by_contra he2; rw [he2] at hj; simp at hj <;> omega
            have h_len : 0 < rest_blocks.length := by
              simpa [List.length_pos_iff_ne_nil] using h_rest_ne
            have h_fr : (rest_blocks.headI).1 = r := h_first_rest h_rest_ne
            have h_get : rest_blocks.get ⟨0, h_len⟩ = rest_blocks.headI :=
              get_zero_eq_headI h_len
            have h_goal : (rest_blocks.get ⟨0, h_len⟩).1 = r := by
              rw [h_get]
              exact h_fr
            exact h_goal.symm
          | succ j'' =>
            have h_jr : j'' + 1 < rest_blocks.length := by simpa using hj
            simpa using h_adj_rest j'' h_jr
      · intro h
        by_cases he : rest_blocks = []
        · have h_rm : r = m := h_empty_rest.mp he
          have h_goal : (((pos, l, false, s) :: (l, r, true, sl) :: rest_blocks).getLast h).2.1 = m := by
            have h9 : ((pos, l, false, s) :: (l, r, true, sl) :: rest_blocks).getLast h = (l, r, true, sl) := by
              simp [List.getLast_cons, he]
              <;> aesop
            rw [h9]
            <;> simp [h_rm]
          exact h_goal
        · simp [List.getLast_cons, he]
          exact h_last_rest he
    · -- Case pos ≥ l, so pos = l
      have h_pos_le_l : pos ≤ l := by
        have h1 : (pos : ℝ) ≤ p.1 := (h_bound p (by simp)).1
        have h2 : p.1 ≤ (l : ℝ) := Nat.le_ceil p.1
        have h3 : (pos : ℝ) ≤ (l : ℝ) := by linarith
        exact_mod_cast h3
      have h_pos_eq : pos = l := by
        have h4 : l ≤ pos := by omega
        exact le_antisymm h_pos_le_l h4
      let rest_blocks := buildBlocks f s m rest r
      let sl := chordSlope f p.1 p.2
      have h_main : buildBlocks f s m (p :: rest) pos =
          (l, r, true, sl) :: rest_blocks := by
        simp [buildBlocks, h_case, h_pos_eq, l, r, sl] <;> rfl
      have h_ne : pos ≠ m := by
        have h1 : l < r := h_lr
        have h2 : r ≤ m := h_r_le_m
        omega
      rw [h_main]
      constructor
      · simp [h_empty_rest, h_ne]
      constructor
      · intro h; simp [h_first_rest, h_pos_eq]
      constructor
      · intro j hj
        induction j with
        | zero =>
          have h_rest_ne : rest_blocks ≠ [] := by
            by_contra he2; rw [he2] at hj; simp at hj <;> omega
          have h_len : 0 < rest_blocks.length := by
            simpa [List.length_pos_iff_ne_nil] using h_rest_ne
          have h_fr : (rest_blocks.headI).1 = r := h_first_rest h_rest_ne
          have h_get : rest_blocks.get ⟨0, h_len⟩ = rest_blocks.headI :=
            get_zero_eq_headI h_len
          have h_goal : (rest_blocks.get ⟨0, h_len⟩).1 = r := by
            rw [h_get]; exact h_fr
          exact h_goal.symm
        | succ j' =>
          have h_jr : j' + 1 < rest_blocks.length := by simpa using hj
          simpa using h_adj_rest j' h_jr
      · intro h
        by_cases he : rest_blocks = []
        · have h_rm : r = m := h_empty_rest.mp he
          have h_goal : (((l, r, true, sl) :: rest_blocks).getLast h).2.1 = m := by
            have h9 : ((l, r, true, sl) :: rest_blocks).getLast h = (l, r, true, sl) := by
              simp [List.getLast_cons, he] <;> aesop
            rw [h9] <;> simp [h_rm]
          exact h_goal
        · simp [List.getLast_cons, he]
          exact h_last_rest he

/-- No consecutive bad blocks: for any two consecutive blocks, at least one is structured. -/
lemma buildBlocks_no_consecutive_bad (f : ℝ → ℝ) (s : ℝ) (m : ℕ) :
    ∀ (ints : List (ℝ × ℝ)) (pos : ℕ), pos ≤ m →
      List.Pairwise (fun p q : ℝ × ℝ => p.2 ≤ q.1) ints →
      (∀ p ∈ ints, (pos : ℝ) ≤ p.1 ∧ p.2 ≤ (m : ℝ)) →
      (∀ p ∈ ints, Nat.ceil p.1 < Nat.floor p.2) →
      ∀ (j : ℕ) (hj : j + 1 < (buildBlocks f s m ints pos).length),
        isStruct ((buildBlocks f s m ints pos).get ⟨j, Nat.lt_of_succ_lt hj⟩) ∨
        isStruct ((buildBlocks f s m ints pos).get ⟨j + 1, hj⟩) := by
  intro ints
  induction ints with
  | nil =>
    intro pos h_pos h_disj h_bound h_round
    dsimp only [buildBlocks]
    split_ifs with h
    · intro j hj
      exfalso; simpa using hj
    · have h_pos_eq : pos = m := by omega
      simp [h, h_pos_eq] <;> omega
  | cons p rest ih =>
    intro pos h_pos h_disj h_bound h_round
    let l := Nat.ceil p.1
    let r := Nat.floor p.2
    have h_lr : l < r := h_round p (by simp)
    have h_p2_nonneg : 0 ≤ p.2 := by
      by_contra h
      have h5 : p.2 < 0 := by linarith
      have h6 : Nat.floor p.2 = 0 := by
        rw [Nat.floor_eq_zero.mpr] <;> linarith
      have h7 : l < Nat.floor p.2 := by simpa [r] using h_lr
      rw [h6] at h7
      exact Nat.not_lt_zero _ h7
    have h_r_le_m : r ≤ m := by
      have h1 : p.2 ≤ (m : ℝ) := (h_bound p (by simp)).2
      have h2 : (r : ℝ) ≤ p.2 := Nat.floor_le h_p2_nonneg
      have h3 : (r : ℝ) ≤ (m : ℝ) := by linarith
      exact_mod_cast h3
    have h_disj_rest : List.Pairwise (fun p q => p.2 ≤ q.1) rest :=
      (List.pairwise_cons.mp h_disj).2
    have h_bound_rest : ∀ q ∈ rest, (r : ℝ) ≤ q.1 ∧ q.2 ≤ (m : ℝ) := by
      intro q hq
      have h1 : p.2 ≤ q.1 := (List.pairwise_cons.mp h_disj).1 q hq
      have h2 : (r : ℝ) ≤ p.2 := Nat.floor_le h_p2_nonneg
      have h3 : (r : ℝ) ≤ q.1 := by linarith
      have h4 : q.2 ≤ (m : ℝ) := (h_bound q (by simp [hq])).2
      exact ⟨h3, h4⟩
    have h_round_rest : ∀ q ∈ rest, Nat.ceil q.1 < Nat.floor q.2 :=
      fun q hq => h_round q (by simp [hq])
    have h_ih := ih r h_r_le_m h_disj_rest h_bound_rest h_round_rest
    by_cases h_case : pos < l
    · let rest_blocks := buildBlocks f s m rest r
      have h_main : buildBlocks f s m (p :: rest) pos =
          (pos, l, false, s) :: (l, r, true, chordSlope f p.1 p.2) :: rest_blocks := by
        simp [buildBlocks, h_case, l, r] <;> rfl
      have h_goal : ∀ (j : ℕ) (hj : j + 1 < ((pos, l, false, s) :: (l, r, true, chordSlope f p.1 p.2) :: rest_blocks).length),
          isStruct (((pos, l, false, s) :: (l, r, true, chordSlope f p.1 p.2) :: rest_blocks).get ⟨j, Nat.lt_of_succ_lt hj⟩) ∨
          isStruct (((pos, l, false, s) :: (l, r, true, chordSlope f p.1 p.2) :: rest_blocks).get ⟨j + 1, hj⟩) := by
        intro j hj
        by_cases h0 : j = 0
        · simp [h0, isStruct]
        · by_cases h1 : j = 1
          · simp [h1, isStruct]
          · have h_j_ge2 : j ≥ 2 := by omega
            let j'' : ℕ := j - 2
            have h_eq : j = j'' + 2 := by omega
            have h_list_len : ((pos, l, false, s) :: (l, r, true, chordSlope f p.1 p.2) :: rest_blocks).length = 2 + rest_blocks.length := by
              simp
              <;> omega
            rw [h_list_len] at hj
            have h_jr : j'' + 1 < rest_blocks.length := by
              rw [h_eq] at hj
              omega
            simpa [isStruct, h_eq] using h_ih j'' h_jr
      simpa [h_main] using h_goal
    · have h_pos_le_l : pos ≤ l := by
        have h1 : (pos : ℝ) ≤ p.1 := (h_bound p (by simp)).1
        have h2 : p.1 ≤ (l : ℝ) := Nat.le_ceil p.1
        have h3 : (pos : ℝ) ≤ (l : ℝ) := by linarith
        exact_mod_cast h3
      have h_pos_eq : pos = l := by
        have h4 : l ≤ pos := by omega
        exact le_antisymm h_pos_le_l h4
      let rest_blocks := buildBlocks f s m rest r
      let sl := chordSlope f p.1 p.2
      have h_main : buildBlocks f s m (p :: rest) pos =
          (l, r, true, sl) :: rest_blocks := by
        simp [buildBlocks, h_case, h_pos_eq, l, r, sl] <;> rfl
      have h_goal : ∀ (j : ℕ) (hj : j + 1 < ((l, r, true, sl) :: rest_blocks).length),
          isStruct (((l, r, true, sl) :: rest_blocks).get ⟨j, Nat.lt_of_succ_lt hj⟩) ∨
          isStruct (((l, r, true, sl) :: rest_blocks).get ⟨j + 1, hj⟩) := by
        intro j hj
        by_cases h0 : j = 0
        · simp [h0, isStruct]
        · have h_j_ge1 : j ≥ 1 := by omega
          let j' : ℕ := j - 1
          have h_eq : j = j' + 1 := by omega
          have h_list_len : ((l, r, true, sl) :: rest_blocks).length = 1 + rest_blocks.length := by
            simp
            <;> omega
          rw [h_list_len] at hj
          have h_jr : j' + 1 < rest_blocks.length := by
            rw [h_eq] at hj
            omega
          simpa [isStruct, h_eq] using h_ih j' h_jr
      simpa [h_main] using h_goal

/-- Slope bounds: every structured block has slope in [s, 2]. -/
lemma buildBlocks_slope_bounds (f : ℝ → ℝ) (s : ℝ) (m : ℕ) :
    ∀ (ints : List (ℝ × ℝ)) (pos : ℕ), pos ≤ m →
      List.Pairwise (fun p q : ℝ × ℝ => p.2 ≤ q.1) ints →
      (∀ p ∈ ints, (pos : ℝ) ≤ p.1 ∧ p.2 ≤ (m : ℝ)) →
      (∀ p ∈ ints, Nat.ceil p.1 < Nat.floor p.2) →
      (∀ p ∈ ints, s ≤ chordSlope f p.1 p.2 ∧ chordSlope f p.1 p.2 ≤ 2) →
      ∀ b ∈ buildBlocks f s m ints pos, isStruct b → s ≤ b.2.2.2 ∧ b.2.2.2 ≤ 2 := by
  intro ints
  induction ints with
  | nil =>
    intro pos h_pos h_disj h_bound h_round h_slopes
    dsimp only [buildBlocks]
    split_ifs with h
    · intro b hb h_struct
      simp only [List.mem_singleton] at hb
      rw [hb] at h_struct
      simp [isStruct] at h_struct <;> tauto
    · simp [h]
  | cons p rest ih =>
    intro pos h_pos h_disj h_bound h_round h_slopes
    let l := Nat.ceil p.1
    let r := Nat.floor p.2
    let sl := chordSlope f p.1 p.2
    have h_lr : l < r := h_round p (by simp)
    have h_p2_nonneg : 0 ≤ p.2 := by
      by_contra h
      have h5 : p.2 < 0 := by linarith
      have h6 : Nat.floor p.2 = 0 := by
        rw [Nat.floor_eq_zero.mpr] <;> linarith
      have h7 : l < Nat.floor p.2 := by simpa [r] using h_lr
      rw [h6] at h7
      exact Nat.not_lt_zero _ h7
    have h_r_le_m : r ≤ m := by
      have h1 : p.2 ≤ (m : ℝ) := (h_bound p (by simp)).2
      have h2 : (r : ℝ) ≤ p.2 := Nat.floor_le h_p2_nonneg
      have h3 : (r : ℝ) ≤ (m : ℝ) := by linarith
      exact_mod_cast h3
    have h_disj_rest : List.Pairwise (fun p q => p.2 ≤ q.1) rest :=
      (List.pairwise_cons.mp h_disj).2
    have h_bound_rest : ∀ q ∈ rest, (r : ℝ) ≤ q.1 ∧ q.2 ≤ (m : ℝ) := by
      intro q hq
      have h1 : p.2 ≤ q.1 := (List.pairwise_cons.mp h_disj).1 q hq
      have h2 : (r : ℝ) ≤ p.2 := Nat.floor_le h_p2_nonneg
      have h3 : (r : ℝ) ≤ q.1 := by linarith
      have h4 : q.2 ≤ (m : ℝ) := (h_bound q (by simp [hq])).2
      exact ⟨h3, h4⟩
    have h_round_rest : ∀ q ∈ rest, Nat.ceil q.1 < Nat.floor q.2 :=
      fun q hq => h_round q (by simp [hq])
    have h_slopes_rest : ∀ q ∈ rest, s ≤ chordSlope f q.1 q.2 ∧ chordSlope f q.1 q.2 ≤ 2 :=
      fun q hq => h_slopes q (by simp [hq])
    have h_sl_p : s ≤ sl ∧ sl ≤ 2 := h_slopes p (by simp)
    have h_ih := ih r h_r_le_m h_disj_rest h_bound_rest h_round_rest h_slopes_rest
    by_cases h_case : pos < l
    · -- Case pos < l
      let rest_blocks := buildBlocks f s m rest r
      have h_main : buildBlocks f s m (p :: rest) pos =
          (pos, l, false, s) :: (l, r, true, sl) :: rest_blocks := by
        simp [buildBlocks, h_case, l, r, sl] <;> rfl
      rw [h_main]
      intro b hb h_struct
      simp only [List.mem_cons] at hb
      rcases hb with (rfl | rfl | hb)
      · simp [isStruct] at h_struct <;> tauto
      · exact h_sl_p
      · exact h_ih b hb h_struct
    · -- Case pos ≥ l, so pos = l
      have h_pos_le_l : pos ≤ l := by
        have h1 : (pos : ℝ) ≤ p.1 := (h_bound p (by simp)).1
        have h2 : p.1 ≤ (l : ℝ) := Nat.le_ceil p.1
        have h3 : (pos : ℝ) ≤ (l : ℝ) := by linarith
        exact_mod_cast h3
      have h_pos_eq : pos = l := by
        have h4 : l ≤ pos := by omega
        exact le_antisymm h_pos_le_l h4
      let rest_blocks := buildBlocks f s m rest r
      have h_main : buildBlocks f s m (p :: rest) pos =
          (l, r, true, sl) :: rest_blocks := by
        simp [buildBlocks, h_case, h_pos_eq, l, r, sl] <;> rfl
      rw [h_main]
      intro b hb h_struct
      simp only [List.mem_cons] at hb
      rcases hb with (rfl | hb)
      · exact h_sl_p
      · exact h_ih b hb h_struct

/-- Combined structural properties of buildBlocks. -/
lemma buildBlocks_structural (f : ℝ → ℝ) (s : ℝ) (m : ℕ)
    (ints : List (ℝ × ℝ)) (pos : ℕ) (h_pos : pos ≤ m)
    (h_disj : List.Pairwise (fun p q : ℝ × ℝ => p.2 ≤ q.1) ints)
    (h_bound : ∀ p ∈ ints, (pos : ℝ) ≤ p.1 ∧ p.2 ≤ (m : ℝ))
    (h_round : ∀ p ∈ ints, Nat.ceil p.1 < Nat.floor p.2)
    (h_slopes : ∀ p ∈ ints, s ≤ chordSlope f p.1 p.2 ∧ chordSlope f p.1 p.2 ≤ 2) :
    let blocks := buildBlocks f s m ints pos
    (blocks = [] ↔ pos = m) ∧
    (blocks ≠ [] → (blocks.headI).1 = pos) ∧
    (∀ b ∈ blocks, b.1 < b.2.1) ∧
    (∀ (j : ℕ) (hj : j + 1 < blocks.length),
       (blocks.get ⟨j, Nat.lt_of_succ_lt hj⟩).2.1 = (blocks.get ⟨j + 1, hj⟩).1) ∧
    (∀ (j : ℕ) (hj : j + 1 < blocks.length),
       isStruct (blocks.get ⟨j, Nat.lt_of_succ_lt hj⟩) ∨
       isStruct (blocks.get ⟨j + 1, hj⟩)) ∧
    (∀ (h : blocks ≠ []), (blocks.getLast h).2.1 = m) ∧
    (∀ b ∈ blocks, isStruct b → s ≤ b.2.2.2 ∧ b.2.2.2 ≤ 2) := by
  let blocks := buildBlocks f s m ints pos
  have h1 := buildBlocks_adjacent f s m ints pos h_pos h_disj h_bound h_round
  have h2 := buildBlocks_no_consecutive_bad f s m ints pos h_pos h_disj h_bound h_round
  have h3 := buildBlocks_slope_bounds f s m ints pos h_pos h_disj h_bound h_round h_slopes
  have h4 := buildBlocks_correct f s m ints pos h_pos h_disj h_bound h_round
  exact ⟨h1.1, h1.2.1, h4.2.2.1, h1.2.2.1, h2, h1.2.2.2, h3⟩

end MultiscaleBlockConversion
