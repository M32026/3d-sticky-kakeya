module

/-
Copyright (c) 2024 The Discretised Furstenberg Estimate Team.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raven Team
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.CoveringProducts
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.Dictionary

@[expose] public section

noncomputable section

namespace DirecretisedFurstenbergEstimate

namespace MultiscaleDecomposition

/-! # Superlinear to Delta-S-Set conversion

This module contains the first part of the dictionary lemma:
- `superlinear_constant_check`: the key constant inequality
- `superlinearToDeltaSSet`: ε-superlinear code function implies IsDeltaSSet
-/

/-- Helper: constant inequality for superlinearToDeltaSSet. -/
lemma superlinear_constant_check (m : ℕ) (Δ r ε s : ℝ) (j : ℕ)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hε : 0 < ε) (hs_nonneg : 0 ≤ s) (hs_le_4 : s ≤ 4)
    (hm_pos : 0 < m) (h_j_lt_m : j < m)
    (h_j1 : Δ ^ (j + 1) ≤ r)
    (C : ℝ) (hC_def : C = Δ^(-4 : ℝ) * (324 : ℝ) ^ m * Real.rpow (Δ ^ m) (-ε)) :
    (9 : ℝ) ^ (m - j + 1) * Real.rpow Δ (-s * ((m : ℝ) - (j : ℝ)) - ε * (m : ℝ)) ≤
    C * r ^ s * Real.rpow Δ (-s * (m : ℝ)) / (4 : ℝ) ^ m := by
  have h_nat_rpow : ∀ n : ℕ, Real.rpow Δ (n : ℝ) = Δ ^ n := by
    intro n; simp [Real.rpow_natCast]
  have h_rpow_mul : ∀ (y z : ℝ), (Real.rpow Δ y) ^ z = Real.rpow Δ (y * z) := by
    intro y z
    have h := Real.rpow_mul hΔ.le y z
    simpa using h.symm
  have hC_expand : C = Real.rpow Δ (-4) * (324 : ℝ) ^ m * Real.rpow Δ (-ε * (m : ℝ)) := by
    rw [hC_def]
    have h2 : (Δ ^ m : ℝ) = Real.rpow Δ (m : ℝ) := (h_nat_rpow m).symm
    have h3 : Real.rpow (Δ ^ m) (-ε) = Real.rpow Δ (-ε * (m : ℝ)) := by
      rw [h2]
      have h4 : (Real.rpow Δ (m : ℝ)) ^ (-ε) = Real.rpow Δ ((m : ℝ) * (-ε)) := h_rpow_mul (m : ℝ) (-ε)
      simpa [mul_comm] using h4
    have h5 : (Δ ^ (-4 : ℝ)) = Real.rpow Δ (-4) := by rfl
    rw [h5, h3] <;> ring

  -- Step 1: Δ^(s*j) ≤ Δ^(-4) * r^s
  have h_j1' : (j : ℝ) + 1 = ↑(j + 1) := by simp [Nat.cast_add] <;> norm_num
  have h1_rpow_nat : Real.rpow Δ ((j : ℝ) + 1) = Δ ^ (j + 1) := by
    rw [h_j1']
    exact h_nat_rpow (j + 1)
  have h1a : Real.rpow Δ ((j : ℝ) + 1) ≤ r := by
    rw [h1_rpow_nat] <;> exact h_j1
  have h1b : 0 ≤ Real.rpow Δ ((j : ℝ) + 1) := Real.rpow_nonneg hΔ.le _
  have h1c : (Real.rpow Δ ((j : ℝ) + 1)) ^ s ≤ r ^ s := by
    gcongr <;> linarith
  have h1d : (Real.rpow Δ ((j : ℝ) + 1)) ^ s = Real.rpow Δ (s * ((j : ℝ) + 1)) := by
    have h := h_rpow_mul ((j : ℝ) + 1) s
    rw [h] <;> ring_nf
  have h1e : Real.rpow Δ (s * ((j : ℝ) + 1)) ≤ r ^ s := by
    rw [← h1d] <;> exact h1c
  have h1f : Real.rpow Δ (s * (j : ℝ)) = Real.rpow Δ (-s) * Real.rpow Δ (s * ((j : ℝ) + 1)) := by
    have h_eq : s * (j : ℝ) = -s + s * ((j : ℝ) + 1) := by ring
    rw [h_eq]
    exact Real.rpow_add hΔ (-s) (s * ((j : ℝ) + 1))
  have h1g : Real.rpow Δ (-s) ≤ Real.rpow Δ (-4) := by
    have h : -s ≥ -4 := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1.le h
  have h_step1 : Real.rpow Δ (s * (j : ℝ)) ≤ Real.rpow Δ (-4) * r ^ s := by
    rw [h1f]
    exact mul_le_mul h1g h1e (Real.rpow_nonneg hΔ.le _) (Real.rpow_nonneg hΔ.le _)

  -- Step 2: 4^m * 9^(m-j+1) ≤ 324^m
  have h2a : (9 : ℝ) ^ (m - j + 1) ≤ (9 : ℝ) ^ (m + 1) := by
    have h : m - j + 1 ≤ m + 1 := by omega
    gcongr <;> norm_num
  have h2b : (4 : ℝ) ^ m * (9 : ℝ) ^ (m + 1) = (9 : ℝ) * (36 : ℝ) ^ m := by
    have h : (36 : ℝ) ^ m = (4 : ℝ) ^ m * (9 : ℝ) ^ m := by
      have h' : (36 : ℝ) = 4 * 9 := by norm_num
      rw [h', mul_pow] <;> ring
    calc
      (4 : ℝ) ^ m * (9 : ℝ) ^ (m + 1)
        = (4 : ℝ) ^ m * ((9 : ℝ) * (9 : ℝ) ^ m) := by ring
      _ = (9 : ℝ) * ((4 : ℝ) ^ m * (9 : ℝ) ^ m) := by ring
      _ = (9 : ℝ) * (36 : ℝ) ^ m := by rw [h]
  have h2c : (9 : ℝ) * (36 : ℝ) ^ m ≤ (324 : ℝ) ^ m := by
    have h_eq : (324 : ℝ) ^ m = (9 : ℝ) ^ m * (36 : ℝ) ^ m := by
      have h : (324 : ℝ) = 9 * 36 := by norm_num
      rw [h, mul_pow] <;> ring
    rw [h_eq]
    have h : (9 : ℝ) ≤ (9 : ℝ) ^ m := by
      have h' : m ≥ 1 := by omega
      have h'' : (9 : ℝ) ^ m ≥ (9 : ℝ) ^ 1 := by
        gcongr <;> norm_num
      simpa using h''
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 36 by norm_num) m]
  have h_step2 : (4 : ℝ) ^ m * (9 : ℝ) ^ (m - j + 1) ≤ (324 : ℝ) ^ m := by
    calc
      (4 : ℝ) ^ m * (9 : ℝ) ^ (m - j + 1)
        ≤ (4 : ℝ) ^ m * (9 : ℝ) ^ (m + 1) := by gcongr
      _ = (9 : ℝ) * (36 : ℝ) ^ m := h2b
      _ ≤ (324 : ℝ) ^ m := h2c

  -- Step 3: 4^m * 9^(m-j+1) * Δ^(s*j - ε*m) ≤ C * r^s
  have h3a : Real.rpow Δ (s * (j : ℝ) - ε * (m : ℝ)) =
      Real.rpow Δ (s * (j : ℝ)) * Real.rpow Δ (-ε * (m : ℝ)) := by
    have h_eq : s * (j : ℝ) - ε * (m : ℝ) = s * (j : ℝ) + (-ε * (m : ℝ)) := by ring
    rw [h_eq]
    exact Real.rpow_add hΔ (s * (j : ℝ)) (-ε * (m : ℝ))
  have h_step3 : (4 : ℝ) ^ m * (9 : ℝ) ^ (m - j + 1) *
      Real.rpow Δ (s * (j : ℝ) - ε * (m : ℝ)) ≤ C * r ^ s := by
    rw [h3a, hC_expand]
    have h : (4 : ℝ) ^ m * (9 : ℝ) ^ (m - j + 1) *
        (Real.rpow Δ (s * (j : ℝ)) * Real.rpow Δ (-ε * (m : ℝ))) ≤
        (Real.rpow Δ (-4) * (324 : ℝ) ^ m * Real.rpow Δ (-ε * (m : ℝ))) * r ^ s := by
      have h_pos_eps : 0 ≤ Real.rpow Δ (-ε * (m : ℝ)) := Real.rpow_nonneg hΔ.le _
      have h_pos_sj : 0 ≤ Real.rpow Δ (s * (j : ℝ)) := Real.rpow_nonneg hΔ.le _
      have h_mul2 : Real.rpow Δ (s * (j : ℝ)) * Real.rpow Δ (-ε * (m : ℝ)) ≤
          (Real.rpow Δ (-4) * r ^ s) * Real.rpow Δ (-ε * (m : ℝ)) :=
        mul_le_mul_of_nonneg_right h_step1 h_pos_eps
      have h_pos_b : 0 ≤ Real.rpow Δ (s * (j : ℝ)) * Real.rpow Δ (-ε * (m : ℝ)) := by
        exact mul_nonneg h_pos_sj h_pos_eps
      have h_pos_c : 0 ≤ (324 : ℝ) ^ m := by positivity
      calc
        (4 : ℝ) ^ m * (9 : ℝ) ^ (m - j + 1) *
            (Real.rpow Δ (s * (j : ℝ)) * Real.rpow Δ (-ε * (m : ℝ)))
          = ((4 : ℝ) ^ m * (9 : ℝ) ^ (m - j + 1)) *
            (Real.rpow Δ (s * (j : ℝ)) * Real.rpow Δ (-ε * (m : ℝ))) := by ring
        _ ≤ (324 : ℝ) ^ m *
            ((Real.rpow Δ (-4) * r ^ s) * Real.rpow Δ (-ε * (m : ℝ))) := by
          exact mul_le_mul h_step2 h_mul2 h_pos_b h_pos_c
        _ = (Real.rpow Δ (-4) * (324 : ℝ) ^ m * Real.rpow Δ (-ε * (m : ℝ))) * r ^ s := by ring
    simpa [mul_assoc] using h

  -- Step 4: Derive the goal
  have h4a : Real.rpow Δ (-s * ((m : ℝ) - (j : ℝ)) - ε * (m : ℝ)) =
      Real.rpow Δ (s * (j : ℝ) - ε * (m : ℝ)) * Real.rpow Δ (-s * (m : ℝ)) := by
    have h_eq1 : -s * ((m : ℝ) - (j : ℝ)) - ε * (m : ℝ) =
        (s * (j : ℝ) - ε * (m : ℝ)) + (-s * (m : ℝ)) := by ring
    rw [h_eq1]
    exact Real.rpow_add hΔ (s * (j : ℝ) - ε * (m : ℝ)) (-s * (m : ℝ))
  have h_pos4 : 0 < (4 : ℝ) ^ m := by positivity
  have h_pos_sm : 0 ≤ Real.rpow Δ (-s * (m : ℝ)) := Real.rpow_nonneg hΔ.le _
  have h4b : (4 : ℝ) ^ m * (9 : ℝ) ^ (m - j + 1) *
      Real.rpow Δ (-s * ((m : ℝ) - (j : ℝ)) - ε * (m : ℝ)) ≤
      (4 : ℝ) ^ m * (C * r ^ s * Real.rpow Δ (-s * (m : ℝ)) / (4 : ℝ) ^ m) := by
    have h_eq2 : (4 : ℝ) ^ m * (C * r ^ s * Real.rpow Δ (-s * (m : ℝ)) / (4 : ℝ) ^ m) =
        C * r ^ s * Real.rpow Δ (-s * (m : ℝ)) := by
      field_simp [h_pos4.ne'] <;> ring
    rw [h_eq2]
    rw [h4a]
    have h : (4 : ℝ) ^ m * (9 : ℝ) ^ (m - j + 1) *
        (Real.rpow Δ (s * (j : ℝ) - ε * (m : ℝ)) * Real.rpow Δ (-s * (m : ℝ))) =
        ((4 : ℝ) ^ m * (9 : ℝ) ^ (m - j + 1) * Real.rpow Δ (s * (j : ℝ) - ε * (m : ℝ))) *
        Real.rpow Δ (-s * (m : ℝ)) := by ring
    rw [h]
    exact mul_le_mul_of_nonneg_right h_step3 h_pos_sm
  have h_goal : (9 : ℝ) ^ (m - j + 1) * Real.rpow Δ (-s * ((m : ℝ) - (j : ℝ)) - ε * (m : ℝ)) ≤
      C * r ^ s * Real.rpow Δ (-s * (m : ℝ)) / (4 : ℝ) ^ m := by
    have h : (4 : ℝ) ^ m * ((9 : ℝ) ^ (m - j + 1) * Real.rpow Δ (-s * ((m : ℝ) - (j : ℝ)) - ε * (m : ℝ))) ≤
        (4 : ℝ) ^ m * (C * r ^ s * Real.rpow Δ (-s * (m : ℝ)) / (4 : ℝ) ^ m) := by
      ring_nf at h4b ⊢ <;> exact h4b
    have h_div : (4 : ℝ) ^ m * (C * r ^ s * Real.rpow Δ (-s * (m : ℝ)) / (4 : ℝ) ^ m) =
        C * r ^ s * Real.rpow Δ (-s * (m : ℝ)) := by
      field_simp [h_pos4.ne'] <;> ring
    rw [h_div] at h
    have h_final : (9 : ℝ) ^ (m - j + 1) * Real.rpow Δ (-s * ((m : ℝ) - (j : ℝ)) - ε * (m : ℝ)) ≤
        C * r ^ s * Real.rpow Δ (-s * (m : ℝ)) / (4 : ℝ) ^ m := by
      calc
        (9 : ℝ) ^ (m - j + 1) * Real.rpow Δ (-s * ((m : ℝ) - (j : ℝ)) - ε * (m : ℝ))
          = ((4 : ℝ) ^ m * ((9 : ℝ) ^ (m - j + 1) * Real.rpow Δ (-s * ((m : ℝ) - (j : ℝ)) - ε * (m : ℝ)))) / (4 : ℝ) ^ m := by
            field_simp [h_pos4.ne'] <;> ring
        _ ≤ (C * r ^ s * Real.rpow Δ (-s * (m : ℝ))) / (4 : ℝ) ^ m := by gcongr
        _ = C * r ^ s * Real.rpow Δ (-s * (m : ℝ)) / (4 : ℝ) ^ m := by ring
    exact h_final
  exact h_goal

/-- Part 1 of dictionary lemma: ε-superlinear → IsDeltaSSet. -/
lemma superlinearToDeltaSSet {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hΔ2 : Δ ≤ 1 / 2)
    {ε : ℝ} (hε : 0 < ε)
    (h_super : EpsSuperlinear (codeFunction m Δ N) 0 (m : ℝ) ε) :
    IsDeltaSSet (Δ ^ m) (slope (codeFunction m Δ N) 0 (m : ℝ))
      ((9 : ℝ)^m * dictionaryConstant m Δ * Real.rpow (Δ ^ m) (-ε)) P := by
  set f : ℝ → ℝ := codeFunction m Δ N with hf_def
  set s : ℝ := slope f 0 (m : ℝ) with hs_def
  set δ : ℝ := Δ ^ m with hδ_def
  set C : ℝ := (9 : ℝ)^m * dictionaryConstant m Δ * Real.rpow (Δ ^ m) (-ε) with hC_def
  let C_old : ℝ := dictionaryConstant m Δ * Real.rpow (Δ ^ m) (-ε)
  have hC_old_def : C_old = Δ^(-4 : ℝ) * (324 : ℝ) ^ m * Real.rpow (Δ ^ m) (-ε) := by
    simp [C_old, dictionaryConstant] <;> ring
  have hC_eq : C = (9 : ℝ)^m * C_old := by
    rw [hC_def] <;> simp [C_old] <;> ring
  have hfm_pos : 0 < m := by
    have h : (0 : ℝ) < (m : ℝ) := h_super.1
    exact_mod_cast h
  have hP_nonempty : P.Nonempty := h_uniform.2.2.1
  have hN_pos : ∀ i < m, N i ≥ 1 := h_uniform.2.2.2.1
  have hδ_pos : 0 < δ := by positivity
  have hC_pos : 0 < C := by
    rw [hC_def]
    have h1 : 0 < (9 : ℝ)^m := by positivity
    have h2 : 0 < dictionaryConstant m Δ := by
      dsimp only [dictionaryConstant]
      have h21 : 0 < Δ^(-4 : ℝ) := by positivity
      have h22 : 0 < (324 : ℝ) ^ m := by positivity
      exact mul_pos h21 h22
    have h4 : 0 < Real.rpow (Δ ^ m) (-ε) := Real.rpow_pos_of_pos (by positivity) _
    exact mul_pos (mul_pos h1 h2) h4
  have hf0 : f 0 = 0 := by
    simp [hf_def, codeFunction] <;> norm_num
  have hfm : f (m : ℝ) = codeFunctionPartialSum m Δ N m := codeFunction_value (by linarith)
  have h_slope_eq : f (m : ℝ) = s * (m : ℝ) := by
    have h_pos : (m : ℝ) > 0 := by exact_mod_cast hfm_pos
    have h : s = (f (m : ℝ) - f 0) / (m : ℝ) := by
      simp only [hs_def, slope] <;> ring
    rw [h, hf0] <;> field_simp [h_pos.ne'] <;> ring
  have hs_nonneg : 0 ≤ s := by
    have h1 : 0 ≤ f (m : ℝ) := by
      rw [hfm]
      dsimp only [codeFunctionPartialSum]
      have h_log_pos : 0 < Real.log (1 / Δ) := by
        have h2 : 1 < 1 / Δ := by apply one_lt_one_div <;> linarith
        exact Real.log_pos h2
      have h_sum_nonneg : 0 ≤ ∑ i ∈ Finset.range m, Real.log (N i) := by
        apply Finset.sum_nonneg
        intro i hi
        have h_i_lt_m : i < m := Finset.mem_range.mp hi
        have h3 : N i ≥ 1 := hN_pos i h_i_lt_m
        have h4 : 0 ≤ Real.log (N i) := by
          apply Real.log_nonneg
          exact_mod_cast h3
        exact h4
      positivity
    have h2 : s = f (m : ℝ) / (m : ℝ) := by
      have h_pos : (m : ℝ) > 0 := by exact_mod_cast hfm_pos
      rw [h_slope_eq] <;> field_simp [h_pos.ne'] <;> ring
    rw [h2] <;> positivity
  have hs_le_4 : s ≤ 4 := by
    have h := slope_le_4_dyadic h_uniform hΔ hΔ1 hΔ2
    simpa [hs_def] using h
  have h_main_goal : ∀ (x : EuclideanPlane) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
    intro x r hδ_le_r
    by_cases h_r_ge_one : 1 ≤ r
    · -- Case r ≥ 1
      have h1 : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
        exact_mod_cast Metric.externalCoveringNumber_mono_set (Set.inter_subset_left)
      have h4a : (1 : ℝ) ≤ Δ^(-4 : ℝ) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hΔ (by linarith) (by norm_num)
      have h7 : (1 : ℝ) ≤ (324 : ℝ) ^ m := by
        have h71 : (1 : ℝ) ≤ (324 : ℝ) := by norm_num
        exact one_le_pow₀ h71
      have h9 : Δ ^ m ≤ 1 := by
        have h10 : Δ ^ m ≤ 1 ^ m := by gcongr
        simpa using h10
      have h8 : (1 : ℝ) ≤ Real.rpow (Δ ^ m) (-ε) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity) h9 (by linarith)
      have hC_ge_one : (1 : ℝ) ≤ C := by
        rw [hC_def]
        have h1 : 1 ≤ (9 : ℝ)^m := by
          have h11 : 1 ≤ (9 : ℝ) := by norm_num
          exact one_le_pow₀ h11
        have h2 : (1 : ℝ) ≤ dictionaryConstant m Δ * Real.rpow (Δ ^ m) (-ε) := by
          dsimp only [dictionaryConstant]
          have h : (1 : ℝ) ≤ Δ^(-4 : ℝ) * (324 : ℝ) ^ m := by
            calc (1 : ℝ)
              = (1 : ℝ) * (1 : ℝ) := by ring
            _ ≤ Δ^(-4 : ℝ) * (324 : ℝ) ^ m := by gcongr
          calc (1 : ℝ)
            = (1 : ℝ) * (1 : ℝ) := by ring
          _ ≤ (Δ^(-4 : ℝ) * (324 : ℝ) ^ m) * Real.rpow (Δ ^ m) (-ε) := by gcongr
        have h3 : (1 : ℝ) ≤ (9 : ℝ)^m * (dictionaryConstant m Δ * Real.rpow (Δ ^ m) (-ε)) := by
          calc (1 : ℝ)
            = (1 : ℝ) * (1 : ℝ) := by ring
          _ ≤ (9 : ℝ)^m * (dictionaryConstant m Δ * Real.rpow (Δ ^ m) (-ε)) := by gcongr
        simpa [mul_assoc] using h3
      have h2 : (1 : ENNReal) ≤ ENNReal.ofReal C := ENNReal.one_le_ofReal.mpr hC_ge_one
      have h31 : (1 : ℝ) ≤ r ^ s := Real.one_le_rpow h_r_ge_one hs_nonneg
      have h_rpow_s : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) :=
        ENNReal.ofReal_rpow_of_nonneg (by linarith) hs_nonneg
      have h3 : (1 : ENNReal) ≤ (ENNReal.ofReal r) ^ s := by
        rw [h_rpow_s]
        exact ENNReal.one_le_ofReal.mpr h31
      have h4 : (1 : ENNReal) ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s := by
        calc (1 : ENNReal)
          = (1 : ENNReal) * (1 : ENNReal) := by simp
        _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s := by gcongr
      calc (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal)
        ≤ (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := h1
      _ = (1 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by simp
      _ ≤ (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
          gcongr
      _ = ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by ring
    · -- Case δ ≤ r < 1
      have h_r_lt_one : r < 1 := by linarith
      have h_r_pos : 0 < r := lt_of_lt_of_le hδ_pos hδ_le_r
      let S_j : Finset ℕ := Finset.filter (fun k => Δ ^ k > r) (Finset.range m)
      have hSj_nonempty : S_j.Nonempty := by
        have h0 : 0 ∈ S_j := by
          simp [S_j, hfm_pos, hΔ1, h_r_lt_one] <;> norm_num
        exact ⟨0, h0⟩
      let j : ℕ := S_j.max' hSj_nonempty
      have hj_mem : j ∈ S_j := Finset.max'_mem S_j hSj_nonempty
      have hj_in_range : j ∈ Finset.range m := (Finset.mem_filter.mp hj_mem).1
      have hj_lt_m : j < m := Finset.mem_range.mp hj_in_range
      have hj_le_m : j ≤ m := by linarith
      have h_gt : Δ ^ j > r := (Finset.mem_filter.mp hj_mem).2
      have h_le : Δ ^ (j + 1) ≤ r := by
        by_cases h : j + 1 < m
        · have h4 : j + 1 ∉ S_j := by
            intro h5
            have h6 : j + 1 ≤ j := Finset.le_max' S_j (j + 1) h5
            omega
          have h5 : ¬(Δ ^ (j + 1) > r) := by
            simpa [S_j, Finset.mem_filter, h] using h4
          linarith
        · have h6 : j + 1 = m := by omega
          rw [h6]
          exact hδ_le_r
      have hΔj_pos : 0 < Δ ^ j := by positivity
      rcases ball_dyadic_squares_bound (Δ ^ j) hΔj_pos x with ⟨Sq, hSq_prop, hSq_card⟩
      have h_ball_sub : Metric.closedBall x r ⊆ Metric.closedBall x (Δ ^ j) := by
        intro y hy
        have h_dist : dist y x ≤ r := by simpa [Metric.mem_closedBall] using hy
        have h : dist y x ≤ Δ ^ j := by linarith
        simpa [Metric.mem_closedBall] using h
      have h_cover : P ∩ Metric.closedBall x r ⊆
          ⋃ p ∈ Sq, P ∩ dyadicSquare (Δ ^ j) p.1 p.2 := by
        intro y hy
        have hyP : y ∈ P := hy.1
        have hyB : y ∈ Metric.closedBall x r := hy.2
        let a : ℤ := ⌊y 0 / (Δ ^ j)⌋
        let b : ℤ := ⌊y 1 / (Δ ^ j)⌋
        have ha1 : (a : ℝ) ≤ y 0 / (Δ ^ j) := Int.floor_le _
        have ha2 : y 0 / (Δ ^ j) < (a : ℝ) + 1 := Int.lt_floor_add_one _
        have hb1 : (b : ℝ) ≤ y 1 / (Δ ^ j) := Int.floor_le _
        have hb2 : y 1 / (Δ ^ j) < (b : ℝ) + 1 := Int.lt_floor_add_one _
        have hy_sq : y ∈ dyadicSquare (Δ ^ j) a b := by
          simp only [dyadicSquare]
          constructor
          · constructor
            · calc (a : ℝ) * (Δ ^ j) ≤ (y 0 / (Δ ^ j)) * (Δ ^ j) := by gcongr
              _ = y 0 := by field_simp [hΔj_pos.ne'] <;> ring
            · calc y 0 = (y 0 / (Δ ^ j)) * (Δ ^ j) := by field_simp [hΔj_pos.ne'] <;> ring
              _ < ((a : ℝ) + 1) * (Δ ^ j) := by gcongr
          · constructor
            · calc (b : ℝ) * (Δ ^ j) ≤ (y 1 / (Δ ^ j)) * (Δ ^ j) := by gcongr
              _ = y 1 := by field_simp [hΔj_pos.ne'] <;> ring
            · calc y 1 = (y 1 / (Δ ^ j)) * (Δ ^ j) := by field_simp [hΔj_pos.ne'] <;> ring
              _ < ((b : ℝ) + 1) * (Δ ^ j) := by gcongr
        have h_intersect : (Metric.closedBall x (Δ ^ j) ∩ dyadicSquare (Δ ^ j) a b).Nonempty :=
          ⟨y, h_ball_sub hyB, hy_sq⟩
        have h_in_Sq : (a, b) ∈ Sq := hSq_prop a b h_intersect
        exact Set.mem_iUnion₂.mpr ⟨(a, b), h_in_Sq, ⟨hyP, hy_sq⟩⟩
      let B_enat : ENNReal := (9 : ENNReal) ^ (m - j) * ∏ i ∈ Finset.range (m - j), (↑(N (j + i)) : ENNReal)
      have h_each : ∀ (p : ℤ × ℤ), p ∈ Sq →
          (Metric.externalCoveringNumber δ.toNNReal (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) ≤ B_enat := by
        intro p _
        by_cases hne : (P ∩ dyadicSquare (Δ ^ j) p.1 p.2).Nonempty
        · exact dyadicCovering_product_upper h_uniform hj_le_m p.1 p.2 hne
        · have h_empty : P ∩ dyadicSquare (Δ ^ j) p.1 p.2 = ∅ := by
            simpa [Set.not_nonempty_iff_eq_empty] using hne
          rw [h_empty]
          simp [Metric.externalCoveringNumber_empty] <;> positivity
      let A : {p : ℤ × ℤ // p ∈ Sq} → Set EuclideanPlane :=
        fun p => P ∩ dyadicSquare (Δ ^ j) p.val.1 p.val.2
      have h_sum : (Metric.externalCoveringNumber δ.toNNReal
            (⋃ p ∈ Sq, P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) ≤
          ∑ p ∈ Sq, (Metric.externalCoveringNumber δ.toNNReal (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) := by
        have h_iUnion : (⋃ p ∈ Sq, P ∩ dyadicSquare (Δ ^ j) p.1 p.2) = ⋃ (i : {p // p ∈ Sq}), A i := by
          ext z
          simp [A, Set.mem_iUnion] <;> aesop
        rw [h_iUnion]
        have h_enat := externalCoveringNumber_iUnion_le (ε := δ.toNNReal) (A := A)
        let coeHom : ENat →+ ENNReal :=
          { toFun := fun x => ↑x
            map_zero' := by simp
            map_add' := by intro a b; exact ENat.toENNReal_add a b }
        have h_sum_coe : (↑(∑ i : {p // p ∈ Sq}, Metric.externalCoveringNumber δ.toNNReal (A i)) : ENNReal) =
            ∑ i : {p // p ∈ Sq}, (Metric.externalCoveringNumber δ.toNNReal (A i) : ENNReal) := by
          exact map_sum coeHom (fun i => Metric.externalCoveringNumber δ.toNNReal (A i)) Finset.univ
        have h_coerced : (Metric.externalCoveringNumber δ.toNNReal (⋃ (i : {p // p ∈ Sq}), A i) : ENNReal) ≤
            (↑(∑ i : {p // p ∈ Sq}, Metric.externalCoveringNumber δ.toNNReal (A i)) : ENNReal) :=
          enat_to_ennreal_mono h_enat
        rw [h_sum_coe] at h_coerced
        have h_univ : (Finset.univ : Finset {p // p ∈ Sq}) = Finset.attach Sq := by
          ext x; simp
        have h_attach : ∑ (i : {p // p ∈ Sq}), (Metric.externalCoveringNumber δ.toNNReal (A i) : ENNReal) =
            ∑ p ∈ Sq, (Metric.externalCoveringNumber δ.toNNReal (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) := by
          have h1 : ∑ (i : {p // p ∈ Sq}), (Metric.externalCoveringNumber δ.toNNReal (A i) : ENNReal) =
              ∑ i ∈ Finset.attach Sq, (Metric.externalCoveringNumber δ.toNNReal (A i) : ENNReal) := by
            rw [h_univ]
          rw [h1]
          have h2 : ∑ i ∈ Finset.attach Sq, (Metric.externalCoveringNumber δ.toNNReal (A i) : ENNReal) =
              ∑ p ∈ Sq, (Metric.externalCoveringNumber δ.toNNReal (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) := by
            apply Finset.sum_bij' (fun (x : {p // p ∈ Sq}) _ => x.val) (fun (p : ℤ × ℤ) hp => ⟨p, hp⟩)
            <;> simp [A, Subtype.ext_iff] <;> tauto
          exact h2
        rw [h_attach] at h_coerced
        exact h_coerced
      have h_upper1 : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
          ∑ p ∈ Sq, (Metric.externalCoveringNumber δ.toNNReal (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) := by
        have h_mono : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
            (Metric.externalCoveringNumber δ.toNNReal (⋃ p ∈ Sq, P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) := by
          exact_mod_cast Metric.externalCoveringNumber_mono_set h_cover
        calc _ ≤ _ := h_mono
             _ ≤ _ := h_sum
      have h_upper2 : ∑ p ∈ Sq, (Metric.externalCoveringNumber δ.toNNReal (P ∩ dyadicSquare (Δ ^ j) p.1 p.2) : ENNReal) ≤
          (9 : ENNReal) * B_enat := by
        calc ∑ p ∈ Sq, _
          ≤ ∑ p ∈ Sq, B_enat := Finset.sum_le_sum fun i _ => h_each i ‹_›
        _ = (Sq.card : ENNReal) * B_enat := by
          simp [Finset.sum_const] <;> ring
        _ ≤ (9 : ENNReal) * B_enat := by
          have h_card : (Sq.card : ENNReal) ≤ (9 : ENNReal) := by exact_mod_cast hSq_card
          gcongr <;> positivity
      let Prod_N : ℝ := ∏ i ∈ Finset.range (m - j), (N (j + i) : ℝ)
      let B_real : ℝ := (9 : ℝ) ^ (m - j) * Prod_N
      have h_prod_coe : (∏ i ∈ Finset.range (m - j), (↑(N (j + i)) : ENNReal)) =
          ENNReal.ofReal Prod_N := by
        have h1 : (∏ i ∈ Finset.range (m - j), (↑(N (j + i)) : ENNReal)) =
            ↑(∏ i ∈ Finset.range (m - j), N (j + i)) := by
          rw [← Nat.cast_prod] <;> rfl
        rw [h1]
        have h2 : (↑(∏ i ∈ Finset.range (m - j), N (j + i)) : ENNReal) =
            ENNReal.ofReal ((↑(∏ i ∈ Finset.range (m - j), N (j + i)) : ℝ)) := by exact Eq.symm (ENNReal.ofReal_natCast (∏ i ∈ Finset.range (m - j), N (j + i)))
        rw [h2]
        have h3 : ((↑(∏ i ∈ Finset.range (m - j), N (j + i)) : ℝ)) = Prod_N := by
          simp [Prod_N] <;> norm_cast
        rw [h3]
      have hB_enat : B_enat = ENNReal.ofReal B_real := by
        simp [B_enat, B_real, Prod_N, h_prod_coe] <;> ring
      have h_upper3 : (9 : ENNReal) * B_enat = ENNReal.ofReal ((9 : ℝ) * B_real) := by
        rw [hB_enat]
        have h9 : (9 : ENNReal) = ENNReal.ofReal (9 : ℝ) := by simp
        rw [h9]
        rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
      have h_upper4 : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
          ENNReal.ofReal ((9 : ℝ) * B_real) := by
        calc _ ≤ (9 : ENNReal) * B_enat := le_trans h_upper1 h_upper2
             _ = ENNReal.ofReal ((9 : ℝ) * B_real) := h_upper3
      have h_prod1 : Prod_N = (∏ i ∈ Finset.range m, (N i : ℝ)) / (∏ i ∈ Finset.range j, (N i : ℝ)) := by
        have h2 : Finset.range m = Finset.range j ∪ Finset.Ico j m := by
          ext x; simp [Finset.mem_range, Finset.mem_Ico] <;> omega
        have h3 : Disjoint (Finset.range j) (Finset.Ico j m) := by
          simp [Finset.disjoint_left, Finset.mem_range, Finset.mem_Ico] <;> omega
        have h4 : ∏ i ∈ Finset.range m, (N i : ℝ) =
            (∏ i ∈ Finset.range j, (N i : ℝ)) * ∏ i ∈ Finset.Ico j m, (N i : ℝ) := by
          rw [h2, Finset.prod_union h3] <;> ring
        have h5 : ∏ i ∈ Finset.Ico j m, (N i : ℝ) = ∏ i ∈ Finset.range (m - j), (N (j + i) : ℝ) := by
          rw [Finset.prod_Ico_eq_prod_range] <;> rfl
        have h_pos_j : (∏ i ∈ Finset.range j, (N i : ℝ)) ≠ 0 := by
          apply (Finset.prod_pos _).ne'
          intro i hi
          have h_i_lt_j : i < j := Finset.mem_range.mp hi
          have h_i_lt_m : i < m := by linarith
          have h6 : N i ≥ 1 := hN_pos i h_i_lt_m
          exact_mod_cast (by linarith)
        have h_eq : (∏ i ∈ Finset.range j, (N i : ℝ)) * ∏ i ∈ Finset.range (m - j), (N (j + i) : ℝ) =
            ∏ i ∈ Finset.range m, (N i : ℝ) := by
          have h6 : (∏ i ∈ Finset.range j, (N i : ℝ)) * ∏ i ∈ Finset.Ico j m, (N i : ℝ) =
              ∏ i ∈ Finset.range m, (N i : ℝ) := h4.symm
          rw [h5] at h6
          exact h6
        have h_final_product : ∏ i ∈ Finset.range (m - j), (N (j + i) : ℝ) =
            (∏ i ∈ Finset.range m, (N i : ℝ)) / (∏ i ∈ Finset.range j, (N i : ℝ)) := by
          rw [← h_eq] <;> field_simp [h_pos_j] <;> ring
        simpa [Prod_N] using h_final_product
      have h_cf_m : (∏ i ∈ Finset.range m, (N i : ℝ)) = Real.rpow Δ (-(f (m : ℝ))) :=
        codeFunction_product_dyadic h_uniform hΔ hΔ1 (by linarith)
      have h_cf_j : (∏ i ∈ Finset.range j, (N i : ℝ)) = Real.rpow Δ (-(f (j : ℝ))) :=
        codeFunction_product_dyadic h_uniform hΔ hΔ1 (by linarith)
      have h_f_m : f (m : ℝ) = s * (m : ℝ) := h_slope_eq
      have h_super_j : f (j : ℝ) ≥ s * (j : ℝ) - ε * (m : ℝ) :=
        superlinear_lower_bound h_super hs_def hf0
          (by exact ⟨by exact_mod_cast (show 0 ≤ j from by omega), by exact_mod_cast hj_le_m⟩)
      have h_exp_ineq : -(f (m : ℝ)) + f (j : ℝ) ≥ -s * ((m : ℝ) - (j : ℝ)) - ε * (m : ℝ) := by
        linarith [h_f_m, h_super_j]
      have h_rpow_ineq : Real.rpow Δ (-(f (m : ℝ)) + f (j : ℝ)) ≤
          Real.rpow Δ (-s * ((m : ℝ) - (j : ℝ)) - ε * (m : ℝ)) := by
        exact Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1.le h_exp_ineq
      have h_Prod_N_ineq : Prod_N ≤ Real.rpow Δ (-s * ((m : ℝ) - (j : ℝ)) - ε * (m : ℝ)) := by
        rw [h_prod1, h_cf_m, h_cf_j]
        have h_div : Real.rpow Δ (-(f (m : ℝ))) / Real.rpow Δ (-(f (j : ℝ))) =
            Real.rpow Δ (-(f (m : ℝ)) + f (j : ℝ)) := by
          have h_pos : 0 < Real.rpow Δ (-(f (j : ℝ))) := Real.rpow_pos_of_pos hΔ _
          have h_sum : (-(f (m : ℝ)) + f (j : ℝ)) + (-(f (j : ℝ))) = -(f (m : ℝ)) := by ring
          have h_rpow : Real.rpow Δ ((-(f (m : ℝ)) + f (j : ℝ)) + (-(f (j : ℝ)))) =
              Real.rpow Δ (-(f (m : ℝ)) + f (j : ℝ)) * Real.rpow Δ (-(f (j : ℝ))) :=
            Real.rpow_add hΔ (-(f (m : ℝ)) + f (j : ℝ)) (-(f (j : ℝ)))
          have h_eq : Real.rpow Δ (-(f (m : ℝ))) =
              Real.rpow Δ (-(f (m : ℝ)) + f (j : ℝ)) * Real.rpow Δ (-(f (j : ℝ))) := by
            rw [h_sum] at h_rpow
            exact h_rpow
          rw [h_eq] <;> field_simp [h_pos.ne'] <;> ring
        rw [h_div]
        exact h_rpow_ineq
      have h_9B : (9 : ℝ) * B_real = (9 : ℝ) ^ (m - j + 1) * Prod_N := by
        dsimp only [B_real] <;> ring
      have h_final_real : (9 : ℝ) * B_real ≤
          (9 : ℝ) ^ (m - j + 1) * Real.rpow Δ (-s * ((m : ℝ) - (j : ℝ)) - ε * (m : ℝ)) := by
        rw [h_9B] <;> gcongr
      have h_lower : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≥
          ENNReal.ofReal (Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m) := by
        have h1 : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≥
            (↑(∏ i ∈ Finset.range m, N i) : ENNReal) / (36 : ENNReal) ^ m :=
          dyadic_covering_product_lower h_uniform hΔ hΔ1 hΔ2
        have h2 : (↑(∏ i ∈ Finset.range m, N i) : ENNReal) =
            ENNReal.ofReal (∏ i ∈ Finset.range m, (N i : ℝ)) := by
          have h21 : (↑(∏ i ∈ Finset.range m, N i) : ENNReal) =
              ENNReal.ofReal ((↑(∏ i ∈ Finset.range m, N i) : ℝ)) := by exact Eq.symm (ENNReal.ofReal_natCast (∏ i ∈ Finset.range m, N i))
          rw [h21]
          have h22 : ((↑(∏ i ∈ Finset.range m, N i) : ℝ)) = (∏ i ∈ Finset.range m, (N i : ℝ)) := by
            simp <;> norm_cast
          rw [h22]
        rw [h2] at h1
        have h3 : ENNReal.ofReal (∏ i ∈ Finset.range m, (N i : ℝ)) / (36 : ENNReal) ^ m =
            ENNReal.ofReal ((∏ i ∈ Finset.range m, (N i : ℝ)) / (36 : ℝ) ^ m) := by
          have h4 : (36 : ENNReal) ^ m = ENNReal.ofReal ((36 : ℝ) ^ m) := by simp <;> rfl
          rw [h4]
          rw [← ENNReal.ofReal_div_of_pos (show (0 : ℝ) < (36 : ℝ) ^ m by positivity)] <;> rfl
        rw [h3] at h1
        have h5 : (∏ i ∈ Finset.range m, (N i : ℝ)) / (36 : ℝ) ^ m =
            Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m := by
          rw [h_cf_m, h_f_m] <;> ring_nf
        rw [h5] at h1
        exact h1
      have h_const_old : (9 : ℝ) ^ (m - j + 1) * Real.rpow Δ (-s * ((m : ℝ) - (j : ℝ)) - ε * (m : ℝ)) ≤
          C_old * r ^ s * Real.rpow Δ (-s * (m : ℝ)) / (4 : ℝ) ^ m :=
        superlinear_constant_check m Δ r ε s j hΔ hΔ1 hε hs_nonneg hs_le_4 hfm_pos hj_lt_m h_le C_old hC_old_def
      have h_eq_const : C * r ^ s * Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m =
          C_old * r ^ s * Real.rpow Δ (-s * (m : ℝ)) / (4 : ℝ) ^ m := by
        rw [hC_eq]
        have h : (9 : ℝ)^m * C_old * r ^ s * Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m =
            C_old * r ^ s * Real.rpow Δ (-s * (m : ℝ)) / (4 : ℝ) ^ m := by
          have h4 : (36 : ℝ) ^ m = (4 : ℝ) ^ m * (9 : ℝ) ^ m := by
            have h5 : (36 : ℝ) = (4 : ℝ) * (9 : ℝ) := by norm_num
            rw [h5, mul_pow] <;> ring
          rw [h4] <;> field_simp <;> ring
        exact h
      have h_const : (9 : ℝ) ^ (m - j + 1) * Real.rpow Δ (-s * ((m : ℝ) - (j : ℝ)) - ε * (m : ℝ)) ≤
          C * r ^ s * Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m := by
        rw [h_eq_const] <;> exact h_const_old
      have h_final_real2 : (9 : ℝ) * B_real ≤
          C * r ^ s * Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m := by
        calc _ ≤ (9 : ℝ) ^ (m - j + 1) * Real.rpow Δ (-s * ((m : ℝ) - (j : ℝ)) - ε * (m : ℝ)) := h_final_real
             _ ≤ C * r ^ s * Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m := h_const
      have h_rpow_s : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) :=
        ENNReal.ofReal_rpow_of_nonneg (by linarith) hs_nonneg
      have h_goal : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
          ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
        have h6 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
              (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≥
            ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
              ENNReal.ofReal (Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m) := by
          gcongr <;> exact h_lower
        have h_step1 : ENNReal.ofReal C * ENNReal.ofReal (r ^ s) = ENNReal.ofReal (C * r ^ s) := by
          rw [← ENNReal.ofReal_mul (show 0 ≤ C by positivity)]
        have h_step2 : ENNReal.ofReal (C * r ^ s) * ENNReal.ofReal (Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m) =
            ENNReal.ofReal ((C * r ^ s) * (Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m)) := by
          rw [← ENNReal.ofReal_mul (show 0 ≤ C * r ^ s by positivity)]
        have h7 : ENNReal.ofReal C * ENNReal.ofReal (r ^ s) * ENNReal.ofReal (Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m) =
            ENNReal.ofReal (C * (r ^ s) * (Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m)) := by
          have h_assoc : ENNReal.ofReal C * ENNReal.ofReal (r ^ s) * ENNReal.ofReal (Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m) =
              (ENNReal.ofReal C * ENNReal.ofReal (r ^ s)) * ENNReal.ofReal (Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m) := by ring
          rw [h_assoc, h_step1, h_step2] <;> rfl
        have h_final_real3 : (9 : ℝ) * B_real ≤
            C * (r ^ s) * (Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m) := by
          have h_eq : C * r ^ s * Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m =
              C * (r ^ s) * (Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m) := by ring
          rw [h_eq] at h_final_real2
          exact h_final_real2
        have h8 : ENNReal.ofReal ((9 : ℝ) * B_real) ≤
            ENNReal.ofReal (C * (r ^ s) * (Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m)) := by
          apply ENNReal.ofReal_le_ofReal
          exact h_final_real3
        have h6' : ENNReal.ofReal (C * (r ^ s) * (Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m)) ≤
            ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
          have h_temp : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≥
              ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * ENNReal.ofReal (Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m) := h6
          have h_temp2 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * ENNReal.ofReal (Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m) =
              ENNReal.ofReal (C * (r ^ s) * (Real.rpow Δ (-s * (m : ℝ)) / (36 : ℝ) ^ m)) := by
            rw [h_rpow_s, h7]
          rw [h_temp2] at h_temp
          exact h_temp
        exact le_trans h_upper4 (le_trans h8 h6')
      exact h_goal
  exact ⟨hP_nonempty, hδ_pos, hC_pos, hs_nonneg, h_main_goal⟩

end MultiscaleDecomposition

end DirecretisedFurstenbergEstimate

end
