module

public import MyLeanRepo.robust_kaufman_projection.Arithmetic
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Polynomial absorption lemma

Absorbs a constant times a negative power of δ times a log factor into a
more negative power of δ.  Used to show that refinement energy losses are
polynomially negligible compared to the allowed budget δ^(-A*ρ).

Key lemma: `delta_pow_absorb_log4` — for any C > 0, a > 0, ε > 0,
there exists δ₀ > 0 such that for all 0 < δ ≤ δ₀:
  C * δ^(-a) * log(4/δ) ≤ δ^(-(a+ε)) / 100
-/

noncomputable section

open scoped ENNReal NNReal

namespace RobustKaufmanProjection.PolynomialAbsorption

/-- For any C > 0, a > 0, ε > 0, there exists δ₀ ∈ (0,1] such that
    for all 0 < δ ≤ δ₀:
    C * δ^(-a) * Real.log (4 / δ) ≤ δ^(-(a + ε)) / 100. -/
lemma delta_pow_absorb_log4 (C a ε : ℝ) (hC : 0 < C) (ha : 0 < a) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        C * δ ^ (-a) * Real.log (4 / δ) ≤ δ ^ (-(a + ε)) / 100 := by
  -- We need: 100 * C * δ^(-a) * log(4/δ) ≤ δ^(-(a+ε))
  -- Step 1: for δ ≤ 1/4, log(4/δ) ≤ 2 * log(1/δ)
  -- Step 2: use delta_pow_absorb_const_log with C' = 200*C, ε' = ε
  let C' : ℝ := 200 * C
  have hC'_pos : 0 < C' := by positivity
  rcases RobustKaufmanProjection.Arithmetic.delta_pow_absorb_const_log C' ε hC'_pos hε
    with ⟨δ₁, hδ₁_pos, h1⟩
  let δ₀ : ℝ := min (1 / 4 : ℝ) δ₁
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_le_one : δ₀ ≤ 1 := by
    calc δ₀ ≤ (1 / 4 : ℝ) := min_le_left _ _
         _ ≤ 1 := by norm_num
  have hδ₀_le_quarter : δ₀ ≤ 1 / 4 := min_le_left _ _
  have hδ₀_le_δ₁ : δ₀ ≤ δ₁ := min_le_right _ _
  refine ⟨δ₀, hδ₀_pos, hδ₀_le_one, fun δ hδ hδ_le => ?_⟩
  have hδ_le_quarter : δ ≤ 1 / 4 :=
    le_trans hδ_le hδ₀_le_quarter
  have hδ_le_δ₁ : δ ≤ δ₁ :=
    le_trans hδ_le hδ₀_le_δ₁
  have hδ_le_one : δ ≤ 1 := by linarith
  -- log(4/δ) = log 4 + log(1/δ) ≤ 2 * log(1/δ) for δ ≤ 1/4
  have hlog4 : Real.log (4 / δ) ≤ 2 * Real.log (1 / δ) := by
    have h1 : Real.log (4 / δ) = Real.log 4 + Real.log (1 / δ) := by
      have h2 : 4 / δ = 4 * (1 / δ) := by ring
      rw [h2, Real.log_mul (by positivity) (by positivity)]
      <;> ring
    rw [h1]
    have h3 : Real.log (1 / δ) ≥ Real.log 4 := by
      have h4 : 1 / δ ≥ 4 := by
        calc 1 / δ ≥ 1 / (1 / 4 : ℝ) := by gcongr
             _ = 4 := by norm_num
      exact Real.log_le_log (by positivity) h4
    linarith
  have hlog_nonneg : 0 ≤ Real.log (1 / δ) := by
    have h5 : 1 ≤ 1 / δ := by
      apply one_le_one_div <;> linarith
    exact Real.log_nonneg h5
  -- C' * log(1/δ) ≤ δ^(-ε)
  have h_absorb : C' * Real.log (1 / δ) ≤ δ ^ (-ε) := h1 δ hδ hδ_le_δ₁
  -- Main calculation
  have h_main : 100 * C * δ ^ (-a) * Real.log (4 / δ) ≤ δ ^ (-(a + ε)) := by
    calc
      100 * C * δ ^ (-a) * Real.log (4 / δ)
        ≤ 100 * C * δ ^ (-a) * (2 * Real.log (1 / δ)) := by
          gcongr <;> positivity
      _ = C' * δ ^ (-a) * Real.log (1 / δ) := by
          dsimp only [C'] <;> ring
      _ ≤ δ ^ (-ε) * δ ^ (-a) := by
          have h6 : C' * Real.log (1 / δ) ≤ δ ^ (-ε) := h_absorb
          have h7 : 0 ≤ δ ^ (-a) := by positivity
          have h8 : C' * δ ^ (-a) * Real.log (1 / δ) = C' * Real.log (1 / δ) * δ ^ (-a) := by ring
          rw [h8]
          exact mul_le_mul_of_nonneg_right h6 h7
      _ = δ ^ (-(a + ε)) := by
          rw [← Real.rpow_add hδ]
          have h8 : -ε + (-a) = -(a + ε) := by ring
          rw [h8]
  have h_final : C * δ ^ (-a) * Real.log (4 / δ) ≤ δ ^ (-(a + ε)) / 100 := by
    have h9 : 0 < (100 : ℝ) := by norm_num
    have h10 : 100 * (C * δ ^ (-a) * Real.log (4 / δ)) ≤ δ ^ (-(a + ε)) := by
      linarith
    calc
      C * δ ^ (-a) * Real.log (4 / δ)
        = (100 * (C * δ ^ (-a) * Real.log (4 / δ))) / 100 := by ring
      _ ≤ δ ^ (-(a + ε)) / 100 := by gcongr
  exact h_final

/-- Product version: absorb C1 * C2 * δ^(-(e1+e2)*ρ) * log(4/δ) into δ^(-A*ρ) / 100,
    provided e1 + e2 < A and ρ > 0. -/
lemma polynomial_absorption_product (C1 C2 e1 e2 A ρ : ℝ)
    (hC1 : 0 < C1) (hC2 : 0 < C2) (hρ : 0 < ρ)
    (h_sum_pos : 0 < e1 + e2) (h_sum_lt_A : e1 + e2 < A) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        C1 * C2 * δ ^ (-(e1 + e2) * ρ) * Real.log (4 / δ) ≤ δ ^ (-A * ρ) / 100 := by
  let a : ℝ := (e1 + e2) * ρ
  let ε : ℝ := (A - (e1 + e2)) * ρ
  have ha_pos : 0 < a := by
    dsimp only [a]
    exact mul_pos h_sum_pos hρ
  have hε_pos : 0 < ε := by
    dsimp only [ε]
    have h1 : 0 < A - (e1 + e2) := by linarith
    positivity
  have h_a_plus_ε : a + ε = A * ρ := by
    dsimp only [a, ε] <;> ring
  rcases delta_pow_absorb_log4 (C1 * C2) a ε (by positivity) ha_pos hε_pos
    with ⟨δ₀, hδ₀_pos, hδ₀_le_one, h⟩
  refine ⟨δ₀, hδ₀_pos, hδ₀_le_one, fun δ hδ hδ_le => ?_⟩
  have h1 := h δ hδ hδ_le
  have h_a_def : δ ^ (-a) = δ ^ (-(e1 + e2) * ρ) := by
    dsimp only [a]
    have h9 : -((e1 + e2) * ρ) = -(e1 + e2) * ρ := by ring
    rw [h9]
  rw [h_a_def] at h1
  have h_A_def : δ ^ (-(a + ε)) = δ ^ (-A * ρ) := by
    have h10 : a + ε = A * ρ := h_a_plus_ε
    rw [h10]
    have h11 : -(A * ρ) = -A * ρ := by ring
    rw [h11]
  rw [h_A_def] at h1
  exact h1

end RobustKaufmanProjection.PolynomialAbsorption
