module

/-
  Per-block correspondence lemma for buildBlocks.

  Every structured block in the output of `buildBlocks` corresponds to an
  interval in the input, with exact endpoint and slope correspondence.
  Also provides structured block length lower bounds.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.BlockConversion
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.MultiscaleDecomposition

namespace MultiscaleBlockConversion

/-- Every structured block in the output corresponds to an interval in the input. -/
lemma buildBlocks_per_block_correspondence (f : ℝ → ℝ) (s : ℝ) (m : ℕ) :
    ∀ (ints : List (ℝ × ℝ)) (pos : ℕ), pos ≤ m →
      (∀ p ∈ ints, (pos : ℝ) ≤ p.1 ∧ p.2 ≤ (m : ℝ)) →
      (∀ p ∈ ints, p.1 < p.2) →
      List.Pairwise (fun p q : ℝ × ℝ => p.2 ≤ q.1) ints →
      ∀ (b : ℕ × ℕ × Bool × ℝ),
        b ∈ buildBlocks f s m ints pos → isStruct b →
        ∃ (p : ℝ × ℝ), p ∈ ints ∧
          b.1 = Nat.ceil p.1 ∧
          b.2.1 = Nat.floor p.2 ∧
          b.2.2.2 = chordSlope f p.1 p.2 := by
  intro ints
  induction ints with
  | nil =>
    intro pos h_pos h_bound h_valid h_disj b hb hstruct
    by_cases h : pos < m
    · have h_blocks : buildBlocks f s m [] pos = [(pos, m, false, s)] := by
        simp [buildBlocks, h]
      rw [h_blocks] at hb
      have h_b_eq : b = (pos, m, false, s) := by simpa using hb
      rw [h_b_eq] at hstruct
      simp [isStruct] at hstruct
    · have h_blocks : buildBlocks f s m [] pos = [] := by
        simp [buildBlocks, h]
      rw [h_blocks] at hb
      simp at hb
  | cons p rest ih =>
    intro pos h_pos h_bound h_valid h_disj b hb hstruct
    let l := Nat.ceil p.1
    let r := Nat.floor p.2
    let sl := chordSlope f p.1 p.2
    have hpb : (pos : ℝ) ≤ p.1 ∧ p.2 ≤ (m : ℝ) := h_bound p (by simp)
    have h_p1_nonneg : 0 ≤ p.1 := by
      have h_pos0 : (0 : ℝ) ≤ (pos : ℝ) := by positivity
      linarith [hpb.1]
    have h_p1_lt_p2 : p.1 < p.2 := h_valid p (by simp)
    have h_p2_nonneg : 0 ≤ p.2 := by linarith
    have h_pos_le_l : pos ≤ l := by
      have h1 : (pos : ℝ) ≤ p.1 := hpb.1
      have h2 : p.1 ≤ (l : ℝ) := Nat.le_ceil p.1
      have h3 : (pos : ℝ) ≤ (l : ℝ) := by linarith
      exact_mod_cast h3
    have h_r_le_m : r ≤ m := by
      have h2 : (r : ℝ) ≤ p.2 := Nat.floor_le h_p2_nonneg
      have h3 : (r : ℝ) ≤ (m : ℝ) := by linarith [hpb.2]
      exact_mod_cast h3
    have h_disj_rest : List.Pairwise (fun p q : ℝ × ℝ => p.2 ≤ q.1) rest := by
      cases h_disj with | cons _ h => exact h
    have h_bound_rest : ∀ q ∈ rest, (r : ℝ) ≤ q.1 ∧ q.2 ≤ (m : ℝ) := by
      intro q hq
      have h1 : p.2 ≤ q.1 := by
        cases h_disj with | cons h _ => exact h q hq
      have h2 : (r : ℝ) ≤ p.2 := Nat.floor_le h_p2_nonneg
      have h3 : (r : ℝ) ≤ q.1 := by linarith
      have h4 : q.2 ≤ (m : ℝ) := (h_bound q (by simp [hq])).2
      exact ⟨h3, h4⟩
    have h_valid_rest : ∀ q ∈ rest, q.1 < q.2 := fun q hq => h_valid q (by simp [hq])
    by_cases h_case : pos < l
    · -- Case pos < l
      have h_main : buildBlocks f s m (p :: rest) pos =
          (pos, l, false, s) :: (l, r, true, sl) :: buildBlocks f s m rest r := by
        simp [buildBlocks, h_case, l, r, sl] <;> rfl
      rw [h_main] at hb
      simp only [List.mem_cons] at hb
      rcases hb with (h_b1 | h_b2 | h_in_rest)
      · -- b = (pos,l,false,s)
        rw [h_b1] at hstruct
        simp [isStruct] at hstruct
      · -- b = (l,r,true,sl)
        rw [h_b2]
        exact ⟨p, by simp, by simp [l], by simp [r], by simp [sl]⟩
      · -- b in rest blocks
        rcases ih r h_r_le_m h_bound_rest h_valid_rest h_disj_rest b h_in_rest hstruct with ⟨q, hq_in, hq1, hq2, hq3⟩
        exact ⟨q, List.Mem.tail p hq_in, hq1, hq2, hq3⟩
    · -- Case pos ≥ l, so pos = l
      have h_l_le_pos : l ≤ pos := by omega
      have h_pos_eq_l : pos = l := le_antisymm h_pos_le_l h_l_le_pos
      have h_main : buildBlocks f s m (p :: rest) pos =
          (l, r, true, sl) :: buildBlocks f s m rest r := by
        simp [buildBlocks, h_case, h_pos_eq_l, l, r, sl] <;> rfl
      rw [h_main] at hb
      simp only [List.mem_cons] at hb
      rcases hb with (h_b1 | h_in_rest)
      · -- b = (l,r,true,sl)
        rw [h_b1]
        exact ⟨p, by simp, by simp [l], by simp [r], by simp [sl]⟩
      · -- b in rest blocks
        rcases ih r h_r_le_m h_bound_rest h_valid_rest h_disj_rest b h_in_rest hstruct with ⟨q, hq_in, hq1, hq2, hq3⟩
        exact ⟨q, List.Mem.tail p hq_in, hq1, hq2, hq3⟩

/-- Rounded length lower bound: floor(p.2) - ceil(p.1) ≥ p.2 - p.1 - 2. -/
lemma rounded_len_ge (p : ℝ × ℝ) (hp1_nonneg : 0 ≤ p.1) (hp2_nonneg : 0 ≤ p.2) :
    (Nat.floor p.2 - Nat.ceil p.1 : ℝ) ≥ p.2 - p.1 - 2 := by
  have h1 : (Nat.ceil p.1 : ℝ) ≤ p.1 + 1 := by
    have h : (Nat.ceil p.1 : ℝ) < p.1 + 1 := Nat.ceil_lt_add_one hp1_nonneg
    linarith
  have h2 : (Nat.floor p.2 : ℝ) ≥ p.2 - 1 := by
    have h : p.2 - 1 < (Nat.floor p.2 : ℝ) := by exact Nat.sub_one_lt_floor p.2
    linarith
  linarith

/-- Structured block length ≥ τ*m when interval length ≥ τ₀*m and m ≥ 4/τ₀. -/
lemma struct_block_len_ge_tau (p : ℝ × ℝ) {τ₀ τ m : ℝ} (hm_pos : 0 < m)
    (hτ₀_pos : 0 < τ₀) (hτ_le_half : τ ≤ τ₀ / 2)
    (hm0_τ₀ : 4 / τ₀ ≤ m)
    (hp1_nonneg : 0 ≤ p.1) (hp2_nonneg : 0 ≤ p.2)
    (h_interval_len : p.2 - p.1 ≥ τ₀ * m) :
    (Nat.floor p.2 - Nat.ceil p.1 : ℝ) ≥ τ * m := by
  have h3 := rounded_len_ge p hp1_nonneg hp2_nonneg
  have h4 : p.2 - p.1 - 2 ≥ τ₀ * m - 2 := by linarith
  have h5 : τ₀ * m ≥ 4 := by
    have h6 : 4 / τ₀ ≤ m := hm0_τ₀
    have h7 : 4 ≤ τ₀ * m := by
      calc 4 = (4 / τ₀) * τ₀ := by field_simp [hτ₀_pos.ne'] <;> ring
        _ ≤ m * τ₀ := by gcongr
        _ = τ₀ * m := by ring
    exact h7
  have h6 : τ₀ * m - 2 ≥ τ₀ * m / 2 := by linarith
  have h7 : τ₀ * m / 2 ≥ τ * m := by
    have h8 : τ ≤ τ₀ / 2 := hτ_le_half
    have h9 : τ * m ≤ (τ₀ / 2) * m := by gcongr <;> linarith
    linarith
  linarith

end MultiscaleBlockConversion
