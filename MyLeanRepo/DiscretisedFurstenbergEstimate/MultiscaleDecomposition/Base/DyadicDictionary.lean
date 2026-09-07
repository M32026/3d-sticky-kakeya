module

/-
  Dictionary lemmas for dyadic uniformity.

  Provides bounds on N(i) and code function slope for `IsDyadicUniform`.

  Key results:
  - `dyadicN_i_le_delta_inv2`: N(i) ≤ Δ^{-2} when 1/Δ is an integer
  - `dyadicSlope_le_2`: code function slope ≤ 2 when 1/Δ is an integer
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.DyadicUniform

@[expose] public section

noncomputable section

namespace DirecretisedFurstenbergEstimate
namespace MultiscaleDecomposition

/-! # Bounds on N(i) for dyadic uniformity -/

/-- For dyadic uniformity with 1/Δ a positive integer, N(i) ≤ (1/Δ)^2.
    The fine grid is an exact refinement of the coarse grid. -/
lemma dyadicN_i_le_delta_inv2 {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N)
    {n : ℕ} (hn_pos : 0 < n) (hΔ_int : (n : ℝ) = 1 / Δ)
    {i : ℕ} (hi : i < m) : N i ≤ n ^ 2 := by
  have hΔ : 0 < Δ := h_uniform.1
  have hP_ne : P.Nonempty := h_uniform.2.2.1
  rcases hP_ne with ⟨x, hx⟩
  let a : ℤ := ⌊x 0 / (Δ ^ i)⌋
  let b : ℤ := ⌊x 1 / (Δ ^ i)⌋
  have hΔi_pos : 0 < Δ ^ i := by positivity
  have h_x_in_square : x ∈ dyadicSquare (Δ ^ i) a b := by
    simp only [dyadicSquare]
    have h1a : (a : ℝ) ≤ x 0 / (Δ ^ i) := Int.floor_le (x 0 / (Δ ^ i))
    have h2a : x 0 / (Δ ^ i) < (a : ℝ) + 1 := Int.lt_floor_add_one (x 0 / (Δ ^ i))
    have h1b : (b : ℝ) ≤ x 1 / (Δ ^ i) := Int.floor_le (x 1 / (Δ ^ i))
    have h2b : x 1 / (Δ ^ i) < (b : ℝ) + 1 := Int.lt_floor_add_one (x 1 / (Δ ^ i))
    constructor
    · constructor
      · calc (a : ℝ) * (Δ ^ i) ≤ (x 0 / (Δ ^ i)) * (Δ ^ i) := by gcongr
        _ = x 0 := by field_simp [hΔi_pos.ne'] <;> ring
      · calc x 0 = (x 0 / (Δ ^ i)) * (Δ ^ i) := by field_simp [hΔi_pos.ne'] <;> ring
        _ < ((a : ℝ) + 1) * (Δ ^ i) := by gcongr
    · constructor
      · calc (b : ℝ) * (Δ ^ i) ≤ (x 1 / (Δ ^ i)) * (Δ ^ i) := by gcongr
        _ = x 1 := by field_simp [hΔi_pos.ne'] <;> ring
      · calc x 1 = (x 1 / (Δ ^ i)) * (Δ ^ i) := by field_simp [hΔi_pos.ne'] <;> ring
        _ < ((b : ℝ) + 1) * (Δ ^ i) := by gcongr
  have hQ_nonempty : (P ∩ dyadicSquare (Δ ^ i) a b).Nonempty := ⟨x, hx, h_x_in_square⟩
  have h_count : (dyadicSquareCount (Δ ^ (i + 1)) (P ∩ dyadicSquare (Δ ^ i) a b) : ENNReal) =
      (↑(N i) : ENNReal) := h_uniform.2.2.2.2 i hi a b hQ_nonempty
  let Q := P ∩ dyadicSquare (Δ ^ i) a b
  let S_set : Set (ℤ × ℤ) := {p | (Q ∩ dyadicSquare (Δ ^ (i + 1)) p.1 p.2).Nonempty}
  have hS_finite : S_set.Finite := by
    have h'' : dyadicSquareCount (Δ ^ (i + 1)) Q = ↑(N i) := by
      exact_mod_cast h_count
    exact Set.finite_of_encard_eq_coe h''
  let S : Finset (ℤ × ℤ) := hS_finite.toFinset
  have hS_card : S.card = N i := by
    have h2 : S.card = S_set.ncard := by exact Eq.symm (Set.ncard_eq_toFinset_card S_set hS_finite)
    have h3 : (S_set.ncard : ENat) = ↑(N i) := by
      letI : Fintype S_set := hS_finite.fintype
      have h42 : (S_set.ncard : ENat) = S_set.encard := by exact Set.coe_ncard_eq_encard S_set
      have h43 : S_set.encard = ↑(N i) := by
        have h44 : S_set.encard = dyadicSquareCount (Δ ^ (i + 1)) Q := by rfl
        rw [h44]
        exact_mod_cast h_count
      rw [h42, h43]
    have h5 : S_set.ncard = N i := by exact_mod_cast h3
    rw [h2, h5]
  -- Key: since 1/Δ = n, Δ^i = n * Δ^(i+1), so coarse square boundaries align with fine grid.
  -- Coarse square is [a*n*Δ^(i+1), (a*n+n)*Δ^(i+1)) × [b*n*Δ^(i+1), (b*n+n)*Δ^(i+1))
  -- Any fine square intersecting Q must have index in {a*n, ..., a*n+n-1} × {b*n, ..., b*n+n-1}
  let I : Finset ℤ := Finset.Ico (a * (n : ℤ)) (a * (n : ℤ) + (n : ℤ))
  let J : Finset ℤ := Finset.Ico (b * (n : ℤ)) (b * (n : ℤ) + (n : ℤ))
  have hI_card : I.card = n := by simp [I]
  have hJ_card : J.card = n := by simp [J]
  have hI_elems : ∀ (k : ℤ), k ∈ I ↔ a * (n : ℤ) ≤ k ∧ k < a * (n : ℤ) + (n : ℤ) := by
    intro k
    simp [I, Finset.mem_range]
    <;> omega
  have hJ_elems : ∀ (k : ℤ), k ∈ J ↔ b * (n : ℤ) ≤ k ∧ k < b * (n : ℤ) + (n : ℤ) := by
    intro k
    simp [J, Finset.mem_range]
    <;> omega
  have h_subset : S ⊆ I ×ˢ J := by
    intro p hp
    have hmem : p ∈ S_set := by
      simp only [S, hS_finite.mem_toFinset] at hp; exact hp
    rcases hmem with ⟨y, hyQ, hyfine⟩
    have h_y_in_Q : y ∈ Q := hyQ
    have h_y_in_coarse : y ∈ dyadicSquare (Δ ^ i) a b := h_y_in_Q.2
    have h_y_in_fine : y ∈ dyadicSquare (Δ ^ (i + 1)) p.1 p.2 := hyfine
    -- p.1 * Δ^(i+1) ≤ y.0 < (p.1+1) * Δ^(i+1)
    -- a * Δ^i ≤ y.0 < (a+1) * Δ^i
    -- Since Δ^i = n * Δ^(i+1):
    -- a * n * Δ^(i+1) ≤ y.0 < (a*n+n) * Δ^(i+1)
    -- So p.1 ≥ a*n and p.1 < a*n+n
    have h1 : (p.1 : ℝ) * Δ ^ (i + 1) ≤ y 0 := h_y_in_fine.1.1
    have h2 : y 0 < ((p.1 : ℝ) + 1) * Δ ^ (i + 1) := h_y_in_fine.1.2
    have h3 : (a : ℝ) * Δ ^ i ≤ y 0 := h_y_in_coarse.1.1
    have h4 : y 0 < ((a : ℝ) + 1) * Δ ^ i := h_y_in_coarse.1.2
    have h_ratio : (n : ℝ) * Δ ^ (i + 1) = Δ ^ i := by
      have h5 : (n : ℝ) = 1 / Δ := hΔ_int
      calc (n : ℝ) * Δ ^ (i + 1)
        = (1 / Δ) * Δ ^ (i + 1) := by rw [h5]
      _ = (1 / Δ) * (Δ * Δ ^ i) := by ring
      _ = Δ ^ i := by field_simp [hΔ.ne'] <;> ring
    have h_pos : 0 < Δ ^ (i + 1) := by positivity
    have h_p1_lower : a * (n : ℤ) ≤ p.1 := by
      have h6 : (a : ℝ) * Δ ^ i < ((p.1 : ℝ) + 1) * Δ ^ (i + 1) := by
        calc (a : ℝ) * Δ ^ i ≤ y 0 := h3
          _ < ((p.1 : ℝ) + 1) * Δ ^ (i + 1) := h2
      have h7 : (a : ℝ) * ((n : ℝ) * Δ ^ (i + 1)) < ((p.1 : ℝ) + 1) * Δ ^ (i + 1) := by
        have h_rew : (a : ℝ) * Δ ^ i = (a : ℝ) * ((n : ℝ) * Δ ^ (i + 1)) := by rw [h_ratio]
        rw [h_rew] at h6
        exact h6
      have h8 : (a : ℝ) * (n : ℝ) < (p.1 : ℝ) + 1 := by
        have h9 : ((a : ℝ) * (n : ℝ) - ((p.1 : ℝ) + 1)) * Δ ^ (i + 1) < 0 := by linarith
        have h10 : (a : ℝ) * (n : ℝ) - ((p.1 : ℝ) + 1) < 0 := by
          nlinarith [h_pos]
        linarith
      have h9 : (a * (n : ℤ) : ℝ) < (p.1 : ℝ) + 1 := by
        simpa [mul_comm] using h8
      have h10 : a * (n : ℤ) < p.1 + 1 := by exact_mod_cast h9
      omega
    have h_p1_upper : p.1 < a * (n : ℤ) + (n : ℤ) := by
      have h6 : (p.1 : ℝ) * Δ ^ (i + 1) < ((a : ℝ) + 1) * Δ ^ i := by
        calc (p.1 : ℝ) * Δ ^ (i + 1) ≤ y 0 := h1
          _ < ((a : ℝ) + 1) * Δ ^ i := h4
      have h7 : (p.1 : ℝ) * Δ ^ (i + 1) < (((a : ℝ) + 1) * (n : ℝ)) * Δ ^ (i + 1) := by
        have h_rew : ((a : ℝ) + 1) * Δ ^ i = (((a : ℝ) + 1) * (n : ℝ)) * Δ ^ (i + 1) := by
          rw [←h_ratio] <;> ring
        rw [h_rew] at h6
        exact h6
      have h8 : (p.1 : ℝ) < ((a : ℝ) + 1) * (n : ℝ) := by
        have h9 : ((p.1 : ℝ) - (((a : ℝ) + 1) * (n : ℝ))) * Δ ^ (i + 1) < 0 := by linarith
        nlinarith [h_pos]
      have h10 : (p.1 : ℝ) < (a : ℝ) * (n : ℝ) + (n : ℝ) := by linarith
      have h11 : (p.1 : ℝ) < ((a * (n : ℤ) + (n : ℤ)) : ℝ) := by
        simpa [mul_add] using h10
      exact_mod_cast h11
    have h_p2_lower : b * (n : ℤ) ≤ p.2 := by
      have h6 : (b : ℝ) * Δ ^ i < ((p.2 : ℝ) + 1) * Δ ^ (i + 1) := by
        calc (b : ℝ) * Δ ^ i ≤ y 1 := h_y_in_coarse.2.1
          _ < ((p.2 : ℝ) + 1) * Δ ^ (i + 1) := h_y_in_fine.2.2
      have h7 : ((b : ℝ) * (n : ℝ)) * Δ ^ (i + 1) < ((p.2 : ℝ) + 1) * Δ ^ (i + 1) := by
        have h_rew : (b : ℝ) * Δ ^ i = ((b : ℝ) * (n : ℝ)) * Δ ^ (i + 1) := by
          rw [←h_ratio] <;> ring
        rw [h_rew] at h6
        exact h6
      have h8 : (b : ℝ) * (n : ℝ) < (p.2 : ℝ) + 1 := by
        have h9 : (((b : ℝ) * (n : ℝ)) - ((p.2 : ℝ) + 1)) * Δ ^ (i + 1) < 0 := by linarith
        nlinarith [h_pos]
      have h9 : (b * (n : ℤ) : ℝ) < (p.2 : ℝ) + 1 := by
        simpa [mul_comm] using h8
      have h10 : b * (n : ℤ) < p.2 + 1 := by exact_mod_cast h9
      omega
    have h_p2_upper : p.2 < b * (n : ℤ) + (n : ℤ) := by
      have h6 : (p.2 : ℝ) * Δ ^ (i + 1) < ((b : ℝ) + 1) * Δ ^ i := by
        calc (p.2 : ℝ) * Δ ^ (i + 1) ≤ y 1 := h_y_in_fine.2.1
          _ < ((b : ℝ) + 1) * Δ ^ i := h_y_in_coarse.2.2
      have h7 : (p.2 : ℝ) * Δ ^ (i + 1) < (((b : ℝ) + 1) * (n : ℝ)) * Δ ^ (i + 1) := by
        have h_rew : ((b : ℝ) + 1) * Δ ^ i = (((b : ℝ) + 1) * (n : ℝ)) * Δ ^ (i + 1) := by
          rw [←h_ratio] <;> ring
        rw [h_rew] at h6
        exact h6
      have h8 : (p.2 : ℝ) < ((b : ℝ) + 1) * (n : ℝ) := by
        have h9 : ((p.2 : ℝ) - (((b : ℝ) + 1) * (n : ℝ))) * Δ ^ (i + 1) < 0 := by linarith
        nlinarith [h_pos]
      have h10 : (p.2 : ℝ) < (b : ℝ) * (n : ℝ) + (n : ℝ) := by linarith
      have h11 : (p.2 : ℝ) < ((b * (n : ℤ) + (n : ℤ)) : ℝ) := by
        simpa [mul_add] using h10
      exact_mod_cast h11
    have h_p1_in : p.1 ∈ I := (hI_elems p.1).mpr ⟨h_p1_lower, h_p1_upper⟩
    have h_p2_in : p.2 ∈ J := (hJ_elems p.2).mpr ⟨h_p2_lower, h_p2_upper⟩
    exact Finset.mem_product.mpr ⟨h_p1_in, h_p2_in⟩
  have h_card_le : S.card ≤ (I ×ˢ J).card := Finset.card_le_card h_subset
  have h_prod_card : (I ×ˢ J).card = I.card * J.card := by rw [Finset.card_product]
  have h1 : S.card ≤ n ^ 2 := by
    rw [h_prod_card, hI_card, hJ_card] at h_card_le
    have h_eq : n * n = n ^ 2 := by ring
    rw [h_eq] at h_card_le
    exact h_card_le
  have h2 : N i ≤ n ^ 2 := by
    rw [←hS_card]
    exact h1
  exact h2

/-- The slope of the code function for a dyadic-uniform set is at most 2
    when 1/Δ is a positive integer, since N(i) ≤ Δ^{-2}. -/
lemma dyadicSlope_le_2 {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    {n : ℕ} (hn_pos : 0 < n) (hΔ_int : (n : ℝ) = 1 / Δ) :
    slope (codeFunction m Δ N) 0 (m : ℝ) ≤ 2 := by
  by_cases hm : m = 0
  · subst hm
    simp [slope] <;> norm_num
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
  let f := codeFunction m Δ N
  have hlog_pos : 0 < Real.log (1 / Δ) := by
    have h2 : 1 < 1 / Δ := by apply one_lt_one_div <;> linarith
    exact Real.log_pos h2
  have hN_pos : ∀ i < m, 0 < (N i : ℝ) := by
    intro i hi
    have h3 : N i ≥ 1 := h_uniform.2.2.2.1 i hi
    exact_mod_cast (by linarith)
  have h_N_bound : ∀ i < m, (N i : ℝ) ≤ (1 / Δ) ^ 2 := by
    intro i hi
    have h1 : N i ≤ n ^ 2 := dyadicN_i_le_delta_inv2 h_uniform hn_pos hΔ_int hi
    have h2 : (N i : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast h1
    have h3 : (n : ℝ) ^ 2 = (1 / Δ) ^ 2 := by rw [hΔ_int]
    rw [h3] at h2
    exact h2
  have h_log_bound : ∀ i ∈ Finset.range m, Real.log (N i) ≤ 2 * Real.log (1 / Δ) := by
    intro i hi
    have h_i_lt_m : i < m := Finset.mem_range.mp hi
    have h3 : (N i : ℝ) ≤ (1 / Δ) ^ 2 := h_N_bound i h_i_lt_m
    have h4 : 0 < (N i : ℝ) := hN_pos i h_i_lt_m
    have h5 : Real.log (N i) ≤ Real.log ((1 / Δ) ^ 2) := Real.log_le_log h4 h3
    have h6 : Real.log ((1 / Δ) ^ 2) = 2 * Real.log (1 / Δ) := by
      rw [Real.log_pow] <;> norm_num
    rw [h6] at h5
    exact h5
  have h_f0 : f 0 = 0 := by
    unfold f codeFunction; simp
  have h_fm : f (m : ℝ) = codeFunctionPartialSum m Δ N m := by
    unfold f codeFunction
    have h1 : ¬(m : ℝ) ≤ 0 := by
      have h_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
      linarith
    rw [if_neg h1]
    have h2 : (m : ℝ) ≥ (m : ℝ) := by linarith
    rw [if_pos h2]
  have h_sum : codeFunctionPartialSum m Δ N m ≤ (m : ℝ) * 2 := by
    dsimp only [codeFunctionPartialSum]
    have h_div : ∀ i ∈ Finset.range m, Real.log (N i) / Real.log (1 / Δ) ≤ 2 := by
      intro i hi
      have h7 : Real.log (N i) ≤ 2 * Real.log (1 / Δ) := h_log_bound i hi
      calc Real.log (N i) / Real.log (1 / Δ)
        ≤ (2 * Real.log (1 / Δ)) / Real.log (1 / Δ) := by gcongr
      _ = 2 := by field_simp [hlog_pos.ne'] <;> ring
    have h8 : ∑ i ∈ Finset.range m, Real.log (N i) / Real.log (1 / Δ) ≤ ∑ i ∈ Finset.range m, (2 : ℝ) := by
      apply Finset.sum_le_sum; exact h_div
    have h9 : ∑ i ∈ Finset.range m, (2 : ℝ) = (m : ℝ) * 2 := by
      simp [Finset.sum_const] <;> ring
    exact le_trans h8 (le_of_eq h9)
  have h_slope : slope f 0 (m : ℝ) = (f (m : ℝ) - f 0) / (m : ℝ) := by simp [slope]
  rw [h_slope, h_fm]
  have h7 : (m : ℝ) > 0 := by exact_mod_cast hm_pos
  have h10 : codeFunctionPartialSum m Δ N m - f 0 ≤ (m : ℝ) * 2 := by
    rw [h_f0]
    <;> linarith
  have h11 : (codeFunctionPartialSum m Δ N m - f 0) / (m : ℝ) ≤ 2 := by
    calc (codeFunctionPartialSum m Δ N m - f 0) / (m : ℝ)
      ≤ ((m : ℝ) * 2) / (m : ℝ) := by gcongr
    _ = 2 := by field_simp [h7.ne'] <;> ring
  exact h11

end MultiscaleDecomposition
end DirecretisedFurstenbergEstimate

end
