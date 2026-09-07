module

/-
  Code function 2-Lipschitz bound for dyadic Δ.

  When 1/Δ ∈ ℕ, each dyadic square of side Δ^i can be covered by
  (1/Δ)^2 balls of radius Δ^{i+1}, so N(i) ≤ (1/Δ)^2.
  This implies the code function has step slope ≤ 2, hence is 2-Lipschitz.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.Core
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.GridHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.DyadicDictionary
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.MultiscaleDecomposition

namespace CodeFunctionLipschitz

/-- When `1/Δ = n` for some `n : ℕ`, a dyadic square of side `Δ^i` can be
    covered by `n^2` balls of radius `Δ^{i+1}`. -/
lemma square_covered_by_n2_balls {Δ : ℝ} {n : ℕ} (hn_pos : 0 < n)
    (h1 : (1 : ℝ) = (n : ℝ) * Δ) {i : ℕ} (a b : ℤ) :
    ∃ (c : Finset EuclideanPlane),
      (dyadicSquare (Δ ^ i) a b) ⊆ ⋃ x ∈ c, Metric.closedBall x (Δ ^ (i + 1)) ∧
      c.card ≤ n ^ 2 := by
  have hΔ_pos : 0 < Δ := by
    have h : (n : ℝ) * Δ = 1 := by linarith
    have h' : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    nlinarith
  have hL_pos : 0 < Δ ^ i := by positivity
  have hr_pos : 0 < Δ ^ (i + 1) := by positivity
  have hk : (n : ℝ) ≥ (Δ ^ i) * Real.sqrt 2 / (2 * (Δ ^ (i + 1))) := by
    have h_eq : (Δ ^ i) * Real.sqrt 2 / (2 * (Δ ^ (i + 1))) = Real.sqrt 2 / (2 * Δ) := by
      field_simp [hΔ_pos.ne'] <;> ring
    rw [h_eq]
    have h4 : (1 : ℝ) / Δ = (n : ℝ) := by field_simp [hΔ_pos.ne'] <;> linarith
    have h5 : Real.sqrt 2 / (2 * Δ) = (Real.sqrt 2 / 2) * (1 / Δ) := by ring
    rw [h5, h4]
    have h6 : Real.sqrt 2 / 2 ≤ 1 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h7 : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    nlinarith
  exact grid_cover_square (Δ ^ i) (Δ ^ (i + 1)) hL_pos hr_pos n hk a b

/-- For dyadic Δ with `1/Δ ∈ ℕ`, `N(i) ≤ (1/Δ)^2`. -/
lemma N_i_le_square {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N) {n : ℕ} (hn_pos : 0 < n)
    (h1 : (1 : ℝ) = (n : ℝ) * Δ) {i : ℕ} (hi : i < m) :
    N i ≤ n ^ 2 := by
  have hΔ_int : (n : ℝ) = 1 / Δ := by
    have hΔ_pos : 0 < Δ := h_uniform.1
    have h : (n : ℝ) * Δ = 1 := by linarith
    field_simp [hΔ_pos.ne'] <;> linarith
  exact dyadicN_i_le_delta_inv2 h_uniform hn_pos hΔ_int hi

/-- The code function is 2-Lipschitz and monotone when `1/Δ ∈ ℕ`. -/
lemma codeFunction_two_lipschitz {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N) {n : ℕ} (hn_pos : 0 < n)
    (h1 : (1 : ℝ) = (n : ℝ) * Δ) :
    ∀ (x y : ℝ), x ∈ Set.Icc 0 (m : ℝ) → y ∈ Set.Icc 0 (m : ℝ) →
      |codeFunction m Δ N x - codeFunction m Δ N y| ≤ 2 * |x - y| := by
  have hΔ : 0 < Δ := h_uniform.1
  have hΔ1 : Δ < 1 := h_uniform.2.1
  have hN_pos : ∀ i < m, N i ≥ 1 := h_uniform.2.2.2.1
  have hN_le : ∀ i < m, (N i : ℝ) ≤ (n : ℝ) ^ 2 := by
    intro i hi
    have h : N i ≤ n ^ 2 := N_i_le_square h_uniform hn_pos h1 hi
    exact_mod_cast h
  have hlog_pos : 0 < Real.log (1 / Δ) := by
    have h2 : 1 < 1 / Δ := by apply one_lt_one_div <;> linarith
    exact Real.log_pos h2
  have h_step_le_2 : ∀ i < m,
      Real.log (N i) / Real.log (1 / Δ) ≤ 2 := by
    intro i hi
    have hNi_pos : 0 < (N i : ℝ) := by
      have h3 : N i ≥ 1 := hN_pos i hi
      exact_mod_cast h3
    have h4 : (N i : ℝ) ≤ (n : ℝ) ^ 2 := hN_le i hi
    have h_n_eq : (n : ℝ) = 1 / Δ := by field_simp [hΔ.ne'] <;> linarith
    have h5 : Real.log (N i) ≤ 2 * Real.log (1 / Δ) := by
      calc Real.log (N i)
        ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log hNi_pos h4
      _ = 2 * Real.log (n : ℝ) := by rw [Real.log_pow] <;> norm_num
      _ = 2 * Real.log (1 / Δ) := by rw [h_n_eq]
    calc Real.log (N i) / Real.log (1 / Δ)
      ≤ (2 * Real.log (1 / Δ)) / Real.log (1 / Δ) := by gcongr
    _ = 2 := by field_simp [hlog_pos.ne'] <;> ring
  have h_step_nonneg : ∀ i < m, 0 ≤ Real.log (N i) / Real.log (1 / Δ) := by
    intro i hi
    have hNi_pos : 0 < (N i : ℝ) := by
      have h3 : N i ≥ 1 := hN_pos i hi
      exact_mod_cast h3
    have h4 : 0 ≤ Real.log (N i) := Real.log_nonneg (by exact_mod_cast hN_pos i hi)
    positivity
  have h_step_eq : ∀ i < m, codeFunctionPartialSum m Δ N (i + 1) - codeFunctionPartialSum m Δ N i =
      Real.log (N i) / Real.log (1 / Δ) := by
    intro i hi
    simp [codeFunctionPartialSum, Finset.sum_range_succ] <;> ring
  have h_ps_mono : ∀ (i j : ℕ), i ≤ j → j ≤ m →
      codeFunctionPartialSum m Δ N i ≤ codeFunctionPartialSum m Δ N j := by
    intro i j hij hj_m
    have h_diff : codeFunctionPartialSum m Δ N j - codeFunctionPartialSum m Δ N i =
        ∑ k ∈ Finset.Ico i j, Real.log (N k) / Real.log (1 / Δ) := by
      rw [Finset.sum_Ico_eq_sub _ hij] <;> rfl
    have h_nonneg : ∀ k ∈ Finset.Ico i j, 0 ≤ Real.log (N k) / Real.log (1 / Δ) := by
      intro k hk
      have h_k_lt_m : k < m := by
        have h2 : k < j := (Finset.mem_Ico.mp hk).2
        omega
      have h4 : N k ≥ 1 := hN_pos k h_k_lt_m
      have h5 : 0 ≤ Real.log (N k) := Real.log_nonneg (by exact_mod_cast h4)
      positivity
    have h_sum_nonneg : 0 ≤ ∑ k ∈ Finset.Ico i j, Real.log (N k) / Real.log (1 / Δ) :=
      Finset.sum_nonneg h_nonneg
    linarith [h_diff]
  have h_ps_nonneg : ∀ (k : ℕ), k ≤ m → 0 ≤ codeFunctionPartialSum m Δ N k :=
    fun k hk => h_ps_mono 0 k (Nat.zero_le k) hk
  let slope (i : ℕ) : ℝ := codeFunctionPartialSum m Δ N (i + 1) - codeFunctionPartialSum m Δ N i
  have h_slope_nonneg : ∀ i < m, 0 ≤ slope i := by
    intro i hi
    have h : slope i = Real.log (N i) / Real.log (1 / Δ) := h_step_eq i hi
    rw [h]
    exact h_step_nonneg i hi
  have h_slope_le2 : ∀ i < m, slope i ≤ 2 := by
    intro i hi
    have h : slope i = Real.log (N i) / Real.log (1 / Δ) := h_step_eq i hi
    rw [h]
    exact h_step_le_2 i hi

  -- Formula for f(z) on [0, m]
  have h_formula : ∀ (z : ℝ), 0 ≤ z → z ≤ (m : ℝ) →
      codeFunction m Δ N z = codeFunctionPartialSum m Δ N (Nat.floor z) +
        (z - (Nat.floor z : ℝ)) * slope (Nat.floor z) := by
    intro z hz0 hzm
    by_cases hz0' : z = 0
    · simp [hz0', codeFunction, codeFunctionPartialSum, slope]
    · by_cases hzm' : z = (m : ℝ)
      · have h_pos : 0 < m := by
          by_contra h
          have h' : m = 0 := by omega
          have hz : z = 0 := by
            have hz1 : z = (m : ℝ) := hzm'
            rw [h'] at hz1
            simpa using hz1
          exact hz0' hz
        have h_floor : Nat.floor z = m := by
          rw [hzm'] <;> simp
        have h_zdiff : z - (m : ℝ) = 0 := by
          rw [hzm'] <;> ring
        rw [h_floor, h_zdiff]
        have h_f : codeFunction m Δ N z = codeFunctionPartialSum m Δ N m := by
          rw [hzm']
          unfold codeFunction
          have h1 : (m : ℝ) > 0 := by exact_mod_cast h_pos
          have h2 : ¬(m : ℝ) ≤ 0 := by linarith
          simp [h2, codeFunctionPartialSum]
        rw [h_f] <;> ring
      · have hz_pos : 0 < z := by exact lt_of_le_of_ne hz0 (Ne.symm hz0')
        have hz_lt_m : z < (m : ℝ) := by exact lt_of_le_of_ne hzm hzm'
        unfold codeFunction
        have h1 : ¬z ≤ 0 := by linarith
        have h2 : ¬z ≥ (m : ℝ) := by linarith
        simp [h1, h2, slope, codeFunctionPartialSum] <;> ring

  -- Telescoping sum via direct sum manipulation
  have h_telescoping : ∀ (a b : ℕ), a ≤ b → b ≤ m →
      codeFunctionPartialSum m Δ N b - codeFunctionPartialSum m Δ N a =
        ∑ i ∈ Finset.Ico a b, slope i := by
    intro a b hab hbm
    have h_slope_eq : ∀ i, slope i = Real.log (N i) / Real.log (1 / Δ) := by
      intro i
      simp [slope, codeFunctionPartialSum, Finset.sum_range_succ] <;> ring
    have h_sum_slope : ∑ i ∈ Finset.Ico a b, slope i =
        ∑ i ∈ Finset.Ico a b, (Real.log (N i) / Real.log (1 / Δ)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact h_slope_eq i
    have h2 : codeFunctionPartialSum m Δ N b - codeFunctionPartialSum m Δ N a =
        ∑ i ∈ Finset.Ico a b, (Real.log (N i) / Real.log (1 / Δ)) := by
      have h_eq1 : codeFunctionPartialSum m Δ N b =
          ∑ i ∈ Finset.range b, (Real.log (N i) / Real.log (1 / Δ)) := by rfl
      have h_eq2 : codeFunctionPartialSum m Δ N a =
          ∑ i ∈ Finset.range a, (Real.log (N i) / Real.log (1 / Δ)) := by rfl
      rw [h_eq1, h_eq2]
      exact Eq.symm (Finset.sum_Ico_eq_sub (fun k => Real.log ↑(N k) / Real.log (1 / Δ)) hab)
    rw [h_sum_slope, h2]

  -- Main bound for 0 ≤ x ≤ y ≤ m
  have h_main : ∀ (x y : ℝ), 0 ≤ x → x ≤ y → y ≤ (m : ℝ) →
      0 ≤ codeFunction m Δ N y - codeFunction m Δ N x ∧
      codeFunction m Δ N y - codeFunction m Δ N x ≤ 2 * (y - x) := by
    intro x y hx0 hxy hym
    set a : ℕ := Nat.floor x with ha_def
    set b : ℕ := Nat.floor y with hb_def
    have ha_le : (a : ℝ) ≤ x := Nat.floor_le hx0
    have hx_lt : x < (a : ℝ) + 1 := Nat.lt_floor_add_one x
    have hb_le : (b : ℝ) ≤ y := Nat.floor_le (by linarith)
    have hy_lt : y < (b : ℝ) + 1 := Nat.lt_floor_add_one y
    have ha_le_m : a ≤ m := by exact_mod_cast (show (a : ℝ) ≤ (m : ℝ) from by linarith)
    have hb_le_m : b ≤ m := by exact_mod_cast (show (b : ℝ) ≤ (m : ℝ) from by linarith)

    have h_fx : codeFunction m Δ N x = codeFunctionPartialSum m Δ N a + (x - (a : ℝ)) * slope a :=
      h_formula x hx0 (by linarith)
    have h_fy : codeFunction m Δ N y = codeFunctionPartialSum m Δ N b + (y - (b : ℝ)) * slope b :=
      h_formula y (by linarith) hym
    rw [h_fx, h_fy]

    have ha_le_b : a ≤ b := Nat.floor_mono hxy
    by_cases hab : a = b
    · -- Same segment
      have h_ab : a = b := hab
      have h_goal : codeFunctionPartialSum m Δ N b + (y - (b : ℝ)) * slope b -
          (codeFunctionPartialSum m Δ N a + (x - (a : ℝ)) * slope a) =
          (y - x) * slope b := by
        rw [h_ab]
        <;> ring
      rw [h_goal]
      by_cases hbm : b < m
      · have h_sn : 0 ≤ slope b := h_slope_nonneg b hbm
        have h_s2 : slope b ≤ 2 := h_slope_le2 b hbm
        have h_ydiff : 0 ≤ y - x := by linarith
        constructor
        · exact mul_nonneg h_ydiff h_sn
        · nlinarith
      · have hbm' : b = m := by omega
        have h1 : (a : ℝ) ≤ x := ha_le
        have h2 : a = b := h_ab
        have h3 : (b : ℝ) ≤ x := by rw [←h2]; exact h1
        have h4 : (b : ℝ) = (m : ℝ) := by exact_mod_cast hbm'
        have h5 : (m : ℝ) ≤ x := by rw [←h4]; exact h3
        have hxy_eq : x = y := by linarith
        rw [hxy_eq]
        <;> simp
    · -- a < b
      have hab' : a < b := Nat.lt_of_le_of_ne ha_le_b hab
      have ha_lt_m : a < m := by omega

      have h_decomp : codeFunctionPartialSum m Δ N b + (y - (b : ℝ)) * slope b -
          (codeFunctionPartialSum m Δ N a + (x - (a : ℝ)) * slope a) =
          slope a * ((a : ℝ) + 1 - x) +
          (∑ i ∈ Finset.Ico (a + 1) b, slope i) +
          slope b * (y - (b : ℝ)) := by
        have h_tel : codeFunctionPartialSum m Δ N b - codeFunctionPartialSum m Δ N a =
            ∑ i ∈ Finset.Ico a b, slope i := h_telescoping a b (by omega) hb_le_m
        have h_sum_split : ∑ i ∈ Finset.Ico a b, slope i =
            slope a + ∑ i ∈ Finset.Ico (a + 1) b, slope i := by
          have h_set : Finset.Ico a b = insert a (Finset.Ico (a + 1) b) := by
            ext k
            simp only [Finset.mem_insert, Finset.mem_Ico]
            <;> omega
          rw [h_set]
          rw [Finset.sum_insert] <;> simp [Finset.mem_Ico] <;> omega
        linarith
      rw [h_decomp]

      -- Term 1: slope a * (a+1-x)
      have h1_coeff : 0 ≤ (a : ℝ) + 1 - x := by linarith
      have h1_nonneg : 0 ≤ slope a * ((a : ℝ) + 1 - x) :=
        mul_nonneg (h_slope_nonneg a ha_lt_m) h1_coeff
      have h1_le : slope a * ((a : ℝ) + 1 - x) ≤ 2 * ((a : ℝ) + 1 - x) := by
        nlinarith [h_slope_le2 a ha_lt_m]

      -- Term 2: sum over full segments
      have h2_nonneg : 0 ≤ ∑ i ∈ Finset.Ico (a + 1) b, slope i := by
        apply Finset.sum_nonneg
        intro i hi
        have hi_lt_m : i < m := by
          have h3 : i < b := (Finset.mem_Ico.mp hi).2
          omega
        exact h_slope_nonneg i hi_lt_m
      have h_a1_lt_b : a + 1 ≤ b := by omega
      have h2_le : ∑ i ∈ Finset.Ico (a + 1) b, slope i ≤ 2 * ((b : ℝ) - ((a : ℝ) + 1)) := by
        have h3 : ∑ i ∈ Finset.Ico (a + 1) b, slope i ≤ ∑ i ∈ Finset.Ico (a + 1) b, (2 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi_lt_m : i < m := by
            have h4 : i < b := (Finset.mem_Ico.mp hi).2
            omega
          exact h_slope_le2 i hi_lt_m
        have h4 : ∑ i ∈ Finset.Ico (a + 1) b, (2 : ℝ) = 2 * ((Finset.Ico (a + 1) b).card : ℝ) := by
          rw [Finset.sum_const] <;> ring
        have h5 : (Finset.Ico (a + 1) b).card = b - (a + 1) := by
          simp [Finset.Ico_eq_empty_of_le, h_a1_lt_b] <;> omega
        have h6 : (2 * ((Finset.Ico (a + 1) b).card : ℝ)) = 2 * ((b : ℝ) - ((a : ℝ) + 1)) := by
          rw [h5]
          have h7 : (b - (a + 1) : ℕ) = b - (a + 1) := rfl
          simp [h7, Nat.cast_sub h_a1_lt_b] <;> ring
        rw [h4, h6] at h3
        exact h3

      -- Term 3: slope b * (y-b)
      have h_b_cases : b < m ∨ b = m := by omega
      have hy_eq_m : b = m → y = (m : ℝ) := by
        intro hbm
        have h1 : (m : ℝ) ≤ y := by
          have h2 : (b : ℝ) ≤ y := hb_le
          rw [hbm] at h2
          exact h2
        linarith
      have h3_coeff : 0 ≤ y - (b : ℝ) := by linarith
      have h3_nonneg : 0 ≤ slope b * (y - (b : ℝ)) := by
        cases h_b_cases with
        | inl h => exact mul_nonneg (h_slope_nonneg b h) h3_coeff
        | inr h =>
          have hy_eq : y = (m : ℝ) := hy_eq_m h
          have h9 : y - (b : ℝ) = 0 := by
            rw [h, hy_eq] <;> norm_num
          rw [h9] <;> norm_num
      have h3_le : slope b * (y - (b : ℝ)) ≤ 2 * (y - (b : ℝ)) := by
        cases h_b_cases with
        | inl h => nlinarith [h_slope_le2 b h]
        | inr h =>
          have hy_eq : y = (m : ℝ) := hy_eq_m h
          have h9 : y - (b : ℝ) = 0 := by
            rw [h, hy_eq] <;> norm_num
          rw [h9] <;> norm_num

      constructor
      · linarith
      · have h_sum_coeff : ((a : ℝ) + 1 - x) + ((b : ℝ) - ((a : ℝ) + 1)) + (y - (b : ℝ)) = y - x := by ring
        nlinarith

  intro x y hx hy
  by_cases hxy : x ≤ y
  · have h := h_main x y hx.1 hxy hy.2
    have h6 : 0 ≤ codeFunction m Δ N y - codeFunction m Δ N x := by linarith [h.1]
    have h7 : 0 ≤ y - x := by linarith
    have h4 : |codeFunction m Δ N x - codeFunction m Δ N y| = codeFunction m Δ N y - codeFunction m Δ N x := by
      have h8 : codeFunction m Δ N x - codeFunction m Δ N y = -(codeFunction m Δ N y - codeFunction m Δ N x) := by ring
      rw [h8, abs_neg, abs_of_nonneg h6]
    have h5 : |x - y| = y - x := by
      have h8 : x - y = -(y - x) := by ring
      rw [h8, abs_neg, abs_of_nonneg h7]
    rw [h4, h5]
    exact h.2
  · have hyx : y ≤ x := by linarith
    have h := h_main y x hy.1 hyx hx.2
    have h6 : 0 ≤ codeFunction m Δ N x - codeFunction m Δ N y := by linarith [h.1]
    have h7 : 0 ≤ x - y := by linarith
    have h4 : |codeFunction m Δ N x - codeFunction m Δ N y| = codeFunction m Δ N x - codeFunction m Δ N y := by
      rw [abs_of_nonneg h6]
    have h5 : |x - y| = x - y := by
      rw [abs_of_nonneg h7]
    rw [h4, h5]
    exact h.2

/-- The code function is monotone on `[0, m]`. -/
lemma codeFunction_monotone {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N) :
    MonotoneOn (codeFunction m Δ N) (Set.Icc 0 (m : ℝ)) := by
  have hΔ : 0 < Δ := h_uniform.1
  have hΔ1 : Δ < 1 := h_uniform.2.1
  have hN_pos : ∀ i < m, N i ≥ 1 := h_uniform.2.2.2.1
  have hlog_pos : 0 < Real.log (1 / Δ) := by
    have h2 : 1 < 1 / Δ := by apply one_lt_one_div <;> linarith
    exact Real.log_pos h2
  let f_int : ℕ → ℝ := codeFunctionPartialSum m Δ N
  have h_int_mono : ∀ (j k : ℕ), j ≤ k → k ≤ m → f_int j ≤ f_int k := by
    intro j k hj hkm
    have h : f_int k = f_int j + ∑ i ∈ Finset.Ico j k, Real.log (N i) / Real.log (1 / Δ) := by
      simp [f_int, codeFunctionPartialSum, Finset.sum_range_add_sum_Ico _ hj] <;> ring
    rw [h]
    have h2 : 0 ≤ ∑ i ∈ Finset.Ico j k, Real.log (N i) / Real.log (1 / Δ) := by
      apply Finset.sum_nonneg
      intro i hi
      have h3 : i < m := by
        simp only [Finset.mem_Ico] at hi
        omega
      have h4 : N i ≥ 1 := hN_pos i h3
      have h5 : 0 ≤ Real.log (N i) := Real.log_nonneg (by exact_mod_cast h4)
      exact div_nonneg h5 (by linarith)
    linarith
  have h_slope_nonneg : ∀ (k : ℕ), k < m → f_int k ≤ f_int (k + 1) := by
    intro k hk
    exact h_int_mono k (k + 1) (by linarith) (by linarith)
  have h_val : ∀ (z : ℝ), 0 ≤ z → z ≤ (m : ℝ) →
      codeFunction m Δ N z =
        let j : ℕ := ⌊z⌋₊
        let t : ℝ := z - j
        f_int j + t * (f_int (j + 1) - f_int j) := by
    intro z hz0 hzm
    by_cases hz0' : z ≤ 0
    · have hz : z = 0 := by linarith
      rw [hz]
      simp [codeFunction, f_int, codeFunctionPartialSum]
    · have hz_pos : 0 < z := by linarith
      by_cases hzm' : (m : ℝ) ≤ z
      · have hz_eq : z = (m : ℝ) := by linarith
        rw [hz_eq]
        by_cases hm : m = 0
        · simp [codeFunction, hm, f_int, codeFunctionPartialSum]
        · have h_m_pos : 0 < m := by omega
          simp [codeFunction, hz_pos.ne', h_m_pos.ne', f_int] <;> ring
      · have hz_between : ¬(z ≤ 0) ∧ ¬((m : ℝ) ≤ z) := ⟨hz0', hzm'⟩
        simp [codeFunction, hz_between.1, hz_between.2, f_int] <;> ring
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx.1
  have hxm : x ≤ (m : ℝ) := hx.2
  have hy0 : 0 ≤ y := hy.1
  have hym : y ≤ (m : ℝ) := hy.2
  rw [h_val x hx0 hxm, h_val y hy0 hym]
  let jx : ℕ := ⌊x⌋₊
  let jy : ℕ := ⌊y⌋₊
  have hjx_le : jx ≤ m := by
    have h : (jx : ℝ) ≤ x := Nat.floor_le hx0
    have h2 : (jx : ℝ) ≤ (m : ℝ) := by linarith
    exact_mod_cast h2
  have hjy_le : jy ≤ m := by
    have h : (jy : ℝ) ≤ y := Nat.floor_le hy0
    have h2 : (jy : ℝ) ≤ (m : ℝ) := by linarith
    exact_mod_cast h2
  by_cases h_eq : jx = jy
  · -- Same integer part
    have h_goal' : f_int jx + (x - (jx : ℝ)) * (f_int (jx + 1) - f_int jx) ≤
        f_int jy + (y - (jy : ℝ)) * (f_int (jy + 1) - f_int jy) := by
      rw [←h_eq]
      by_cases h_jx_eq_m : jx = m
      · have h_jy_eq_jx : jy = jx := h_eq.symm
        have h_x_eq_m : x = (m : ℝ) := by
          have h1 : (jx : ℝ) ≤ x := Nat.floor_le hx0
          rw [h_jx_eq_m] at h1
          have h2 : x ≤ (m : ℝ) := hxm
          exact le_antisymm h2 h1
        have h_y_eq_m : y = (m : ℝ) := by
          have h1 : (jy : ℝ) ≤ y := Nat.floor_le hy0
          rw [h_jy_eq_jx] at h1
          rw [h_jx_eq_m] at h1
          have h2 : y ≤ (m : ℝ) := hym
          exact le_antisymm h2 h1
        rw [h_x_eq_m, h_y_eq_m] <;> simp
      · have h_jx_lt_m : jx < m := by omega
        have h_slope : f_int jx ≤ f_int (jx + 1) := h_slope_nonneg jx h_jx_lt_m
        have h_d : 0 ≤ f_int (jx + 1) - f_int jx := by linarith
        have h_tx_le_ty : x - (jx : ℝ) ≤ y - (jx : ℝ) := by linarith
        have h_mul : (x - (jx : ℝ)) * (f_int (jx + 1) - f_int jx) ≤
            (y - (jx : ℝ)) * (f_int (jx + 1) - f_int jx) := by
          exact mul_le_mul_of_nonneg_right h_tx_le_ty h_d
        exact add_le_add_right h_mul (f_int jx)
    exact h_goal'
  · -- Different integer parts
    have h_jx_lt_jy : jx < jy := by
      by_contra h
      have h' : jy ≤ jx := by omega
      have h1 : (jx : ℝ) ≤ x := Nat.floor_le hx0
      have h2 : y < (jy : ℝ) + 1 := Nat.lt_floor_add_one y
      have h3 : (jy : ℝ) ≤ (jx : ℝ) := by exact_mod_cast h'
      have h4 : x ≤ y := hxy
      have h5 : (jx : ℝ) - (jy : ℝ) < 1 := by linarith
      have h6 : 0 ≤ (jx : ℝ) - (jy : ℝ) := by linarith
      have h7 : jx - jy < 1 := by exact_mod_cast h5
      have h8 : jx - jy = 0 := by omega
      have h9 : jx = jy := by omega
      exact h_eq h9
    have h_jx_lt_m : jx < m := by omega
    have h_fx_le : f_int jx + (x - (jx : ℝ)) * (f_int (jx + 1) - f_int jx) ≤ f_int (jx + 1) := by
      have h_slope : f_int jx ≤ f_int (jx + 1) := h_slope_nonneg jx h_jx_lt_m
      have h_d : 0 ≤ f_int (jx + 1) - f_int jx := by linarith
      have h_tx_le_one : x - (jx : ℝ) ≤ 1 := by
        have h : x < (jx : ℝ) + 1 := Nat.lt_floor_add_one x
        linarith
      have h_tx_nonneg : 0 ≤ x - (jx : ℝ) := by
        have h : (jx : ℝ) ≤ x := Nat.floor_le hx0
        linarith
      nlinarith
    have h_mid : f_int (jx + 1) ≤ f_int jy := h_int_mono (jx + 1) jy (by omega) hjy_le
    have h_fy_ge : f_int jy ≤ f_int jy + (y - (jy : ℝ)) * (f_int (jy + 1) - f_int jy) := by
      by_cases h_jy_eq_m : jy = m
      · have h_y_eq_m : y = (m : ℝ) := by
          have h1 : (jy : ℝ) ≤ y := Nat.floor_le hy0
          have h2 : y ≤ (m : ℝ) := hym
          rw [h_jy_eq_m] at h1
          exact le_antisymm h2 h1
        simp [h_y_eq_m, h_jy_eq_m]
      · have h_jy_lt_m : jy < m := by omega
        have h_slope : f_int jy ≤ f_int (jy + 1) := h_slope_nonneg jy h_jy_lt_m
        have h_d : 0 ≤ f_int (jy + 1) - f_int jy := by linarith
        have h_ty_nonneg : 0 ≤ y - (jy : ℝ) := by have h := Nat.floor_le hy0; linarith
        have h : 0 ≤ (y - (jy : ℝ)) * (f_int (jy + 1) - f_int jy) := by
          exact mul_nonneg h_ty_nonneg h_d
        exact le_add_of_nonneg_right h
    calc f_int jx + (x - (jx : ℝ)) * (f_int (jx + 1) - f_int jx)
      ≤ f_int (jx + 1) := h_fx_le
    _ ≤ f_int jy := h_mid
    _ ≤ f_int jy + (y - (jy : ℝ)) * (f_int (jy + 1) - f_int jy) := h_fy_ge

end CodeFunctionLipschitz
