module

/-
  Polynomial absorption threshold lemma

  General fact: for any C > 0 and α > 0, there exists δ₀ > 0 such that
  for all n : ℕ with (1/2)^n ≤ δ₀, we have C * (2n + 5) ≤ 2^{αn}.

  Whiteprint node: polynomial_absorption_threshold
  Status: COMPLETE
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontendQuantBounds

/-- Exponential beats linear: for any C > 0 and α > 0, there exists N
    such that for all n ≥ N, C * (2n + 5) ≤ 2^{αn}. -/
lemma exists_N_linear_absorbed (C α : ℝ) (hC_pos : 0 < C) (hα_pos : 0 < α) :
    ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N →
      C * (2 * (n : ℝ) + 5) ≤ (2 : ℝ)^(α * (n : ℝ)) := by
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set y : ℝ := α * Real.log 2 with hy_def
  have hy_pos : 0 < y := by positivity
  -- exp(y*x) ≥ (y*x)^2 / 4 for x ≥ 0
  have h_exp_lower : ∀ (x : ℝ), 0 ≤ x → Real.exp (y * x) ≥ (y * x)^2 / 4 := by
    intro x hx
    have h1 : 0 ≤ y * x / 2 := by positivity
    have h2 : Real.exp (y * x / 2) ≥ 1 + y * x / 2 := by
      linarith [Real.add_one_le_exp (y * x / 2)]
    have h3 : Real.exp (y * x) = (Real.exp (y * x / 2)) ^ 2 := by
      have h4 : Real.exp (y * x) = Real.exp (y * x / 2 + y * x / 2) := by ring_nf
      rw [h4, Real.exp_add] <;> ring
    rw [h3]
    have h5 : (Real.exp (y * x / 2)) ^ 2 ≥ (1 + y * x / 2) ^ 2 := by gcongr
    have h6 : (1 + y * x / 2) ^ 2 ≥ (y * x)^2 / 4 := by nlinarith [h1]
    linarith
  set c : ℝ := y^2 / 4 with hc_def
  have hc_pos : 0 < c := by positivity
  -- For n ≥ max(1, ceil(7C/c)), c*n^2 ≥ C*(2n+5)
  have h_quad : ∀ (n : ℕ), (n : ℝ) ≥ 1 → (n : ℝ) ≥ 7 * C / c →
      C * (2 * (n : ℝ) + 5) ≤ c * (n : ℝ)^2 := by
    intro n hn1 hn7
    have h5 : c * (n : ℝ) ≥ 7 * C := by
      have h7 : 0 < c := hc_pos
      calc c * (n : ℝ)
        ≥ c * (7 * C / c) := by gcongr
      _ = 7 * C := by field_simp [h7.ne'] <;> ring
    have h8 : c * (n : ℝ)^2 ≥ 7 * C * (n : ℝ) := by
      calc c * (n : ℝ)^2
        = (c * (n : ℝ)) * (n : ℝ) := by ring
      _ ≥ (7 * C) * (n : ℝ) := by gcongr
      _ = 7 * C * (n : ℝ) := by ring
    have h9 : 7 * C * (n : ℝ) ≥ C * (2 * (n : ℝ) + 5) := by
      have h10 : 0 ≤ C := by linarith
      have h11 : 0 ≤ (n : ℝ) - 1 := by linarith
      have h12 : 7 * C * (n : ℝ) - C * (2 * (n : ℝ) + 5) = 5 * C * ((n : ℝ) - 1) := by ring
      have h13 : 0 ≤ 5 * C * ((n : ℝ) - 1) := by positivity
      linarith
    linarith
  let N : ℕ := Nat.ceil (7 * C / c)
  have hN7 : (N : ℝ) ≥ 7 * C / c := Nat.le_ceil _
  have hN1 : (N : ℝ) ≥ 1 := by
    have h_pos : 0 < 7 * C / c := by positivity
    have h : (N : ℝ) ≥ 7 * C / c := hN7
    have h' : 7 * C / c > 0 := h_pos
    by_contra h''
    have h''' : (N : ℝ) < 1 := by linarith
    have h4 : N = 0 := by
      have h5 : N < 1 := by exact_mod_cast h'''
      omega
    rw [h4] at h
    simp at h <;> linarith
  refine ⟨N, fun n hn => ?_⟩
  have h2 : (n : ℝ) ≥ (N : ℝ) := by exact_mod_cast hn
  have h3 : (n : ℝ) ≥ 7 * C / c := by linarith
  have h4 : (n : ℝ) ≥ 1 := by linarith
  have h5 : C * (2 * (n : ℝ) + 5) ≤ c * (n : ℝ)^2 := h_quad n h4 h3
  have h6 : Real.exp (y * (n : ℝ)) ≥ (y * (n : ℝ))^2 / 4 := h_exp_lower (n : ℝ) (by positivity)
  have h7 : (y * (n : ℝ))^2 / 4 = c * (n : ℝ)^2 := by
    simp only [hc_def] <;> ring
  have h8 : c * (n : ℝ)^2 ≤ Real.exp (y * (n : ℝ)) := by
    rw [←h7]; exact h6
  have h9 : (2 : ℝ)^(α * (n : ℝ)) = Real.exp (y * (n : ℝ)) := by
    have h10 : (2 : ℝ)^(α * (n : ℝ)) = Real.exp (Real.log 2 * (α * (n : ℝ))) := by
      rw [Real.rpow_def_of_pos (by norm_num)] <;> ring
    rw [h10]
    have h11 : Real.log 2 * (α * (n : ℝ)) = y * (n : ℝ) := by
      simp only [hy_def] <;> ring
    rw [h11]
  rw [h9]
  exact le_trans h5 h8

/-- Threshold form: for any C > 0 and α > 0, there exists δ₀ > 0 such that
    for all n : ℕ, if (1/2 : ℝ)^n ≤ δ₀ then C * (2n + 5) ≤ 2^{αn}. -/
lemma exists_delta_poly_absorption (C α : ℝ) (hC_pos : 0 < C) (hα_pos : 0 < α) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧
      ∀ (n : ℕ), (1 / 2 : ℝ)^n ≤ δ₀ →
        C * (2 * (n : ℝ) + 5) ≤ (2 : ℝ)^(α * (n : ℝ)) := by
  rcases exists_N_linear_absorbed C α hC_pos hα_pos with ⟨N, hN⟩
  let δ₀ : ℝ := (1 / 2 : ℝ)^N
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine ⟨δ₀, hδ₀_pos, fun n hle => ?_⟩
  have h_ge_n : n ≥ N := by
    by_contra h
    have h' : n < N := by omega
    have h1 : (1 / 2 : ℝ)^n > (1 / 2 : ℝ)^N := by
      have h_pow : (2 : ℕ)^n < (2 : ℕ)^N := by
        have h2 : n < N := h'
        have h3 : (2 : ℕ)^n < (2 : ℕ)^N := Nat.pow_lt_pow_right (by norm_num) h2
        exact h3
      have h_eq1 : (1 / 2 : ℝ)^n = 1 / (2 : ℝ)^n := by
        rw [one_div_pow]
        <;> norm_cast
      have h_eq2 : (1 / 2 : ℝ)^N = 1 / (2 : ℝ)^N := by
        rw [one_div_pow] <;> norm_cast
      rw [h_eq1, h_eq2]
      have h4 : (2 : ℝ)^n < (2 : ℝ)^N := by exact_mod_cast h_pow
      have h5 : 0 < (2 : ℝ)^n := by positivity
      have h6 : 0 < (2 : ℝ)^N := by positivity
      exact one_div_lt_one_div_of_lt h5 h4
    have h_contra : (1 / 2 : ℝ)^n ≤ δ₀ := hle
    simp only [δ₀] at h_contra
    exact False.elim (not_le.mpr h1 h_contra)
  exact hN n h_ge_n

/-- Instantiation for hCP_bound: C = 1024, α = pointLoss/2.
    This stronger threshold (smaller δ_front) still implies full pointLoss
    absorption since δ_n^{-pointLoss/2} ≤ δ_n^{-pointLoss} for δ_n ≤ 1. -/
lemma exists_delta_C_P_absorption (pointLoss : ℝ) (hpointLoss_pos : 0 < pointLoss) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧
      ∀ (n : ℕ), (1 / 2 : ℝ)^n ≤ δ₀ →
        (1024 : ℝ) * (2 * (n : ℝ) + 5) ≤ (2 : ℝ)^((pointLoss / 2) * (n : ℝ)) :=
  exists_delta_poly_absorption 1024 (pointLoss / 2) (by norm_num) (by linarith)

end DirecretisedFurstenbergEstimate.FrontendQuantBounds

end
