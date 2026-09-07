module

/-
  Explicit fine ratio scale conversion with uniform threshold.

  Replaces the data-dependent polylog threshold in fine_cor25_producer
  with explicit power bounds on C_ret and C_Q.

  Given:
  - C_ret ≤ δ_n^{-a}, C_Q ≤ δ_n^{-b} (explicit power bounds)
  - polylogLoss > 0 (cost of absorbing the polylog factor)

  Produces a uniform threshold δ₀ (depending only on s, a, b, polylogLoss, K)
  such that for even scales n=2m with δ_n ≤ δ₀:

    (1/K) · log(1/δ')^{-K} · 1/(C_P · 13 · C_Q · 2^s) · δ'^{-s}
      ≥ δ_n^{-(s/2 - (a + b + polylogLoss))}

  where δ' = δ_{n-m} = √δ_n, C_P = 81·max(C_ret,1)·(2√2)^s.

  In the application, set b = lambda + loss_K so that
  localLoss = a + lambda + loss_K + polylogLoss.

  Whiteprint node: section6 / fine_ratio_explicit
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.PolylogAbsorption
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section6

open DiscretisedFurstenbergEstimate

/-- Uniform scale conversion for the fine normalized ratio.

    Takes explicit power bounds C_ret ≤ δ_n^{-a}, C_Q ≤ δ_n^{-b},
    and a polylog absorption cost polylogLoss > 0.

    Returns a uniform threshold δ₀ such that the fine ratio inequality holds
    with localLoss = a + b + polylogLoss.

    Both C_ret and C_Q must be positive (they are S-set constants in practice). -/
lemma fine_ratio_explicit_uniform
    {s a b polylogLoss K : ℝ}
    (ha_nonneg : 0 ≤ a) (hb_nonneg : 0 ≤ b)
    (hpolylogLoss_pos : 0 < polylogLoss) (hK_pos : 0 < K) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (n m : ℕ) (hnm : m ≤ n) (h_even : n = 2 * m)
        (C_ret C_Q : ℝ),
        (0 < C_ret) → (0 < C_Q) →
        C_ret ≤ (dyadicDelta n) ^ (-a) →
        C_Q ≤ (dyadicDelta n) ^ (-b) →
        (dyadicDelta n) ≤ δ₀ →
        (1 / K) * Real.log (1 / (dyadicDelta (n - m))) ^ (-K) *
          (1 / ((81 * max C_ret 1 * (2 * Real.sqrt 2) ^ s) *
            (13 * C_Q * Real.rpow 2 s))) *
          (dyadicDelta (n - m)) ^ (-s) ≥
        (dyadicDelta n) ^ (-(s / 2 - (a + b + polylogLoss))) := by
  let const_s : ℝ := 81 * 13 * (2 * Real.sqrt 2) ^ s * Real.rpow 2 s
  have h_base1_pos : 0 < (2 * Real.sqrt 2) := by positivity
  have h_rpow1_pos : 0 < (2 * Real.sqrt 2) ^ s := Real.rpow_pos_of_pos h_base1_pos s
  have h_rpow2_pos : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
  have h_const_s_pos : 0 < const_s := by
    dsimp only [const_s]
    have h : 0 < (81 : ℝ) * 13 * ((2 * Real.sqrt 2) ^ s) * Real.rpow 2 s := by positivity
    exact h
  let C_poly : ℝ := (2 : ℝ) ^ K / (K * const_s)
  have hC_poly_pos : 0 < C_poly := by
    have h1 : 0 < (2 : ℝ) ^ K := Real.rpow_pos_of_pos (by norm_num) K
    have h2 : 0 < K * const_s := mul_pos hK_pos h_const_s_pos
    exact div_pos h1 h2

  rcases polylog_absorption_core polylogLoss K C_poly hpolylogLoss_pos hK_pos hC_poly_pos with
    ⟨δ_core, hδ_core_pos, hcore⟩

  let δ₀ : ℝ := min (δ_core / 2) (1 / 2)
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_le_one : δ₀ ≤ 1 := by
    have h : δ₀ ≤ 1 / 2 := min_le_right _ _
    linarith

  refine ⟨δ₀, hδ₀_pos, hδ₀_le_one, ?_⟩

  intro n m hnm h_even C_ret C_Q hC_ret_pos hCQ_pos hC_ret_bound hC_Q_bound hδ_small

  set δ : ℝ := dyadicDelta n with hδ_def
  set δ' : ℝ := dyadicDelta (n - m) with hδ'_def

  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ'_pos : 0 < δ' := dyadicDelta_pos (n - m)
  have hδ_lt_one : δ < 1 := by
    have h1 : δ ≤ δ₀ := hδ_small
    have h2 : δ₀ ≤ 1 / 2 := min_le_right _ _
    linarith
  have hδ_lt_core : δ < δ_core := by
    have h1 : δ ≤ δ₀ := hδ_small
    have h2 : δ₀ ≤ δ_core / 2 := min_le_left _ _
    linarith

  -- δ' = √δ (since n = 2m)
  have h1 : n - m = m := by omega
  have h2 : dyadicDelta n = (dyadicDelta m) ^ 2 := by
    simp only [dyadicDelta, h_even]
    <;> ring
  have hδ'_eq : δ' = Real.sqrt δ := by
    have hδ'm : δ' = dyadicDelta m := by
      rw [hδ'_def, h1]
    rw [hδ'm]
    have h3 : 0 < dyadicDelta m := dyadicDelta_pos m
    have h4 : Real.sqrt (dyadicDelta n) = dyadicDelta m := by
      rw [h2]
      rw [Real.sqrt_sq (by linarith)]
    exact h4.symm

  -- Polylog bound: δ^{polylogLoss} * |log δ|^K ≤ C_poly
  have h_poly : δ ^ polylogLoss * |Real.log δ| ^ K ≤ C_poly :=
    hcore δ hδ_pos hδ_lt_core

  have h_log_abs : |Real.log δ| = Real.log (1 / δ) := by
    have h6 : Real.log δ < 0 := Real.log_neg hδ_pos (by linarith)
    have h7 : Real.log (1 / δ) = -Real.log δ := by
      rw [Real.log_div (by norm_num) hδ_pos.ne', Real.log_one]
      <;> ring
    rw [abs_of_neg h6, h7]

  have h_log_pos : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    apply one_lt_one_div <;> linarith

  set L : ℝ := Real.log (1 / δ) with hL_def
  have hL_pos : 0 < L := h_log_pos
  have hL_K_pos : 0 < L ^ K := by positivity

  -- C_poly * L^{-K} ≥ δ^{polylogLoss}
  have h_poly2 : C_poly * L ^ (-K) ≥ δ ^ polylogLoss := by
    have h8 : δ ^ polylogLoss * L ^ K ≤ C_poly := by
      rw [h_log_abs] at h_poly
      exact h_poly
    have h9 : (δ ^ polylogLoss * L ^ K) / L ^ K = δ ^ polylogLoss := by
      field_simp [hL_K_pos.ne'] <;> ring
    have h10 : (δ ^ polylogLoss * L ^ K) / L ^ K ≤ C_poly / L ^ K := by gcongr
    have h11 : δ ^ polylogLoss ≤ C_poly / L ^ K := by
      rw [h9] at h10
      exact h10
    have h12 : C_poly / L ^ K = C_poly * L ^ (-K) := by
      rw [Real.rpow_neg (by linarith)] <;> field_simp
    rw [h12] at h11
    exact h11

  -- Bound max(C_ret, 1) ≤ δ^{-a}
  have h_max_bound : max C_ret 1 ≤ δ ^ (-a) := by
    have h1 : C_ret ≤ δ ^ (-a) := hC_ret_bound
    have h21 : 0 ≤ a := ha_nonneg
    have h22 : δ ^ a ≤ 1 := by
      apply Real.rpow_le_one
      <;> linarith
    have h23 : δ ^ (-a) = 1 / (δ ^ a) := by
      rw [Real.rpow_neg (by linarith)] <;> field_simp
    have h24 : 0 < δ ^ a := by positivity
    have h2 : (1 : ℝ) ≤ δ ^ (-a) := by
      rw [h23]
      exact one_le_one_div h24 h22
    exact max_le h1 h2

  let C_P := 81 * max C_ret 1 * (2 * Real.sqrt 2) ^ s

  have h_CP_bound : C_P ≤ 81 * δ ^ (-a) * (2 * Real.sqrt 2) ^ s := by
    dsimp only [C_P]
    gcongr
    <;> linarith

  have h_denom_bound :
      C_P * (13 * C_Q * Real.rpow 2 s) ≤ const_s * δ ^ (-(a + b)) := by
    calc C_P * (13 * C_Q * Real.rpow 2 s)
      ≤ (81 * δ ^ (-a) * (2 * Real.sqrt 2) ^ s) *
          (13 * δ ^ (-b) * Real.rpow 2 s) := by gcongr
    _ = const_s * (δ ^ (-a) * δ ^ (-b)) := by
        dsimp only [const_s] <;> ring
    _ = const_s * δ ^ (-(a + b)) := by
        rw [←Real.rpow_add (by linarith)]
        <;> ring_nf

  have h_denom_pos : 0 < C_P * (13 * C_Q * Real.rpow 2 s) := by
    have h1 : 0 < C_P := by
      dsimp only [C_P]
      have h2 : 0 < max C_ret 1 := by positivity
      positivity
    have h3 : 0 < C_Q := hCQ_pos
    positivity

  have h_inv_bound :
      1 / (C_P * (13 * C_Q * Real.rpow 2 s)) ≥ (1 / const_s) * δ ^ (a + b) := by
    have h1 : 0 < const_s * δ ^ (-(a + b)) := by positivity
    have h2 : 1 / (C_P * (13 * C_Q * Real.rpow 2 s)) ≥
        1 / (const_s * δ ^ (-(a + b))) := by gcongr
    have h4 : 0 < δ ^ (-(a + b)) := by positivity
    have h3 : 1 / (const_s * δ ^ (-(a + b))) = (1 / const_s) * δ ^ (a + b) := by
      calc 1 / (const_s * δ ^ (-(a + b)))
        = (1 / const_s) * (1 / δ ^ (-(a + b))) := by ring
      _ = (1 / const_s) * δ ^ (a + b) := by
        have h5 : 1 / δ ^ (-(a + b)) = δ ^ (a + b) := by
          rw [Real.rpow_neg (by linarith)] <;> field_simp
        rw [h5]
    rw [h3] at h2
    exact h2

  -- log(1/δ') = (1/2) * log(1/δ)
  have h_logδ' : Real.log (1 / δ') = (1 / 2 : ℝ) * L := by
    rw [hδ'_eq, hL_def]
    have h5 : Real.log (1 / Real.sqrt δ) = -Real.log (Real.sqrt δ) := by
      rw [Real.log_div (by norm_num) (Real.sqrt_pos.mpr hδ_pos).ne', Real.log_one]
      <;> ring
    rw [h5]
    have h6 : Real.log (Real.sqrt δ) = (1 / 2 : ℝ) * Real.log δ := by
      rw [Real.log_sqrt (by linarith)] <;> ring
    rw [h6]
    have h7 : Real.log (1 / δ) = -Real.log δ := by
      rw [Real.log_div (by norm_num) hδ_pos.ne', Real.log_one] <;> ring
    linarith

  have h_logδ'_rpow :
      (Real.log (1 / δ')) ^ (-K) = (2 : ℝ) ^ K * L ^ (-K) := by
    rw [h_logδ']
    have h_pos : 0 < (1 / 2 : ℝ) * L := by positivity
    have h : ((1 / 2 : ℝ) * L) ^ (-K) =
        (1 / 2 : ℝ) ^ (-K) * L ^ (-K) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [h]
    have h2 : (1 / 2 : ℝ) ^ (-K) = (2 : ℝ) ^ K := by
      have h_pos1 : 0 < (1 / 2 : ℝ) := by norm_num
      have h_eq : (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
      rw [h_eq]
      have h3 : ((2 : ℝ) ^ (-1 : ℝ)) ^ (-K) = (2 : ℝ) ^ ((-1 : ℝ) * (-K)) := by
        rw [←Real.rpow_mul (by norm_num)]
        <;> rfl
      rw [h3]
      have h4 : (-1 : ℝ) * (-K) = K := by ring
      rw [h4]
    rw [h2] <;> ring

  -- δ'^{-s} = δ^{-s/2}
  have hδ'_rpow : δ' ^ (-s) = δ ^ (-s / 2) := by
    rw [hδ'_eq]
    have h_sqrt : Real.sqrt δ = δ ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    rw [h_sqrt]
    have h3 : (δ ^ (1 / 2 : ℝ)) ^ (-s) = δ ^ ((1 / 2 : ℝ) * (-s)) := by
      rw [←Real.rpow_mul (by linarith)] <;> rfl
    rw [h3]
    have h4 : (1 / 2 : ℝ) * (-s) = -s / 2 := by ring
    rw [h4]

  let localLoss : ℝ := a + b + polylogLoss

  -- Main calculation
  have h_main : (1 / K) * (Real.log (1 / δ')) ^ (-K) *
      (1 / (C_P * (13 * C_Q * Real.rpow 2 s))) * δ' ^ (-s) ≥
      δ ^ (-(s / 2 - localLoss)) := by
    calc (1 / K) * (Real.log (1 / δ')) ^ (-K) *
        (1 / (C_P * (13 * C_Q * Real.rpow 2 s))) * δ' ^ (-s)
      = (1 / K) * ((2 : ℝ) ^ K * L ^ (-K)) *
        (1 / (C_P * (13 * C_Q * Real.rpow 2 s))) * δ ^ (-s / 2) := by
          rw [h_logδ'_rpow, hδ'_rpow] <;> ring
    _ ≥ (1 / K) * ((2 : ℝ) ^ K * L ^ (-K)) *
        ((1 / const_s) * δ ^ (a + b)) * δ ^ (-s / 2) := by gcongr
    _ = ((2 : ℝ) ^ K / (K * const_s)) * L ^ (-K) * (δ ^ (a + b) * δ ^ (-s / 2)) := by ring
    _ = ((2 : ℝ) ^ K / (K * const_s)) * L ^ (-K) * δ ^ (a + b - s / 2) := by
      have h_exp : δ ^ (a + b) * δ ^ (-s / 2) = δ ^ (a + b - s / 2) := by
        rw [←Real.rpow_add (by linarith)]
        have h_sum : a + b + (-s / 2) = a + b - s / 2 := by ring
        rw [h_sum]
      rw [h_exp]
    _ = C_poly * L ^ (-K) * δ ^ (a + b - s / 2) := by rfl
    _ ≥ δ ^ polylogLoss * δ ^ (a + b - s / 2) := by
          gcongr
          <;> exact h_poly2
    _ = δ ^ (a + b + polylogLoss - s / 2) := by
          rw [←Real.rpow_add (by linarith)]
          have h_sum : polylogLoss + (a + b - s / 2) = a + b + polylogLoss - s / 2 := by ring
          rw [h_sum]
    _ = δ ^ (-(s / 2 - localLoss)) := by
          have h9 : a + b + polylogLoss - s / 2 = -(s / 2 - localLoss) := by
            dsimp only [localLoss] <;> ring
          rw [h9]

  simpa [C_P, localLoss] using h_main

end DirecretisedFurstenbergEstimate.Section6

end
