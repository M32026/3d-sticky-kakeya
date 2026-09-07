module

/-
  Parameter budget lemmas for the discretised Furstenberg estimate.

  These lemmas establish the existence of positive exponents satisfying all
  constraints in the integration chain:
  - RKP feasibility (12ρ < t-s)
  - Combinatorial Kaufman feasibility (A_CK · ε_G < t-s)
  - Product axiom absorption (36·ε_N ≤ η and 36·ε_N < τ)
  - Final target exponent construction (ε_target = ε_G · η / 16)
  - Polylogarithmic loss absorption (log(1/δ)^C ≤ δ^{-ε})

  Whiteprint node: parameter_budget
  Dependencies: none (pure real analysis)
-/
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

namespace ParameterBudget

/-- Lemma 1: RKP feasibility.
Given τ = t-s > 0, there exists ρ > 0 such that 12 * ρ < τ. -/
lemma rkp_feasibility (τ : ℝ) (hτ : 0 < τ) :
    ∃ ρ : ℝ, 0 < ρ ∧ 12 * ρ < τ := by
  use τ / 24
  constructor
  · positivity
  · linarith

/-- Lemma 2: Combinatorial Kaufman feasibility.
Given τ = t-s > 0, there exists ε_G > 0 such that
(1 + 6/τ) * ε_G < τ. -/
lemma ck_feasibility (τ : ℝ) (hτ : 0 < τ) :
    ∃ ε_G : ℝ, 0 < ε_G ∧ (1 + 6 / τ) * ε_G < τ := by
  let A_CK : ℝ := 1 + 6 / τ
  have hA_pos : 0 < A_CK := by positivity
  use τ / (2 * A_CK)
  constructor
  · positivity
  · have hA_eq : τ * A_CK = τ + 6 := by
      dsimp only [A_CK]
      field_simp [hτ.ne'] <;> ring
    have h : (1 + 6 / τ) * (τ / (2 * A_CK)) = τ / 2 := by
      have h5 : (1 + 6 / τ) = A_CK := by simp [A_CK]
      rw [h5]
      field_simp [hA_pos.ne'] <;> linarith
    rw [h]
    <;> linarith

/-- Lemma 3: Product axiom absorption (RKP output constant fits).
Given η > 0, there exists ε_N > 0 such that 36 * ε_N ≤ η.
Here c = 3 absorbs QTTC polylog losses, so 12 * c = 36. -/
lemma product_axiom_absorption (η : ℝ) (hη : 0 < η) :
    ∃ ε_N : ℝ, 0 < ε_N ∧ 36 * ε_N ≤ η := by
  use η / 36
  constructor
  · positivity
  · linarith

/-- Lemma 3b: Both RKP constraints simultaneously.
Given τ > 0 and η > 0, there exists ε_N > 0 such that
36 * ε_N ≤ η AND 36 * ε_N < τ. -/
lemma rkp_both_constraints (τ η : ℝ) (hτ : 0 < τ) (hη : 0 < η) :
    ∃ ε_N : ℝ, 0 < ε_N ∧ 36 * ε_N ≤ η ∧ 36 * ε_N < τ := by
  let ε_N : ℝ := min (η / 72) (τ / 72)
  have h_pos : 0 < ε_N := by positivity
  have h1 : 36 * ε_N ≤ η := by
    dsimp only [ε_N]
    have h2 : 36 * min (η / 72) (τ / 72) ≤ 36 * (η / 72) := by
      gcongr
      exact min_le_left _ _
    have h3 : 36 * (η / 72) = η / 2 := by ring
    linarith
  have h4 : 36 * ε_N < τ := by
    dsimp only [ε_N]
    have h5 : 36 * min (η / 72) (τ / 72) ≤ 36 * (τ / 72) := by
      gcongr
      exact min_le_right _ _
    have h6 : 36 * (τ / 72) = τ / 2 := by ring
    linarith
  exact ⟨ε_N, h_pos, h1, h4⟩

/-- Lemma 4: Final target exponent is positive.
Given ε_G > 0 and η > 0, ε_target = ε_G * η / 16 > 0. -/
lemma target_eps_positive (ε_G η : ℝ) (hεG : 0 < ε_G) (hη : 0 < η) :
    0 < ε_G * η / 16 := by
  positivity

/-- Lemma 5: Combined budget construction.
Given τ > 0 and η > 0, construct ε_G, ε_target, ε_N simultaneously:
  - A_CK · ε_G < τ
  - ε_target = ε_G · η / 16 > 0
  - 36 · ε_N ≤ η
  - 36 · ε_N < τ
-/
lemma combined_budget (τ η : ℝ) (hτ : 0 < τ) (hη : 0 < η) :
    ∃ (ε_G ε_target ε_N : ℝ),
      0 < ε_G ∧
      (1 + 6 / τ) * ε_G < τ ∧
      0 < ε_target ∧
      ε_target = ε_G * η / 16 ∧
      0 < ε_N ∧
      36 * ε_N ≤ η ∧
      36 * ε_N < τ := by
  rcases ck_feasibility τ hτ with ⟨ε_G, hεG_pos, hεG_ck⟩
  let ε_target : ℝ := ε_G * η / 16
  have hεt_pos : 0 < ε_target := target_eps_positive ε_G η hεG_pos hη
  rcases rkp_both_constraints τ η hτ hη with ⟨ε_N, hεN_pos, hεN_η, hεN_τ⟩
  exact ⟨ε_G, ε_target, ε_N, hεG_pos, hεG_ck, hεt_pos, rfl, hεN_pos, hεN_η, hεN_τ⟩

/-- Lemma 6: Polylogarithmic absorption.
For any real C > 0 and ε > 0, there exists δ₀ > 0 such that
for all 0 < δ ≤ δ₀:
  (log(1/δ))^C ≤ δ^{-ε}.

This is the standard fact that logarithmic growth is slower than any
polynomial decay. -/
lemma polylog_absorption (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      Real.rpow (Real.log (1 / δ)) C ≤ Real.rpow δ (-ε) := by
  -- Key intermediate: for all x > 0, log x < 2 * sqrt x
  have h_log_sqrt : ∀ (x : ℝ), 0 < x → Real.log x < 2 * Real.sqrt x := by
    intro x hx
    have h1 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    have h_exp : ∀ (y : ℝ), y + 1 ≤ Real.exp y := Real.add_one_le_exp
    have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := by
      have h3 := h_exp (Real.log (Real.sqrt x))
      have h4 : Real.exp (Real.log (Real.sqrt x)) = Real.sqrt x := by
        rw [Real.exp_log] <;> positivity
      linarith
    have h3 : Real.log (Real.sqrt x) = (1 / 2 : ℝ) * Real.log x := by
      rw [Real.log_sqrt (by linarith)] <;> ring
    linarith
  -- Choose X large enough
  let X : ℝ := max 1 ((2 * C / ε)^2)
  have hX1 : 1 ≤ X := le_max_left _ _
  have hX2 : (2 * C / ε)^2 ≤ X := le_max_right _ _
  let δ₀ : ℝ := Real.exp (-X)
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine' ⟨δ₀, hδ₀_pos, _⟩
  intro δ hδ_pos hδ_le
  have h1 : 1 / δ ≥ 1 / δ₀ := by
    gcongr
    <;> linarith
  have h2 : Real.log (1 / δ) ≥ X := by
    have h3 : Real.log (1 / δ) ≥ Real.log (1 / δ₀) := Real.log_le_log (by positivity) h1
    have h4 : Real.log (1 / δ₀) = X := by
      dsimp only [δ₀]
      have h5 : 1 / Real.exp (-X) = Real.exp X := by
        have h_pos : 0 < Real.exp (-X) := by positivity
        have h6 : Real.exp (-X) * Real.exp X = 1 := by
          have h7 : Real.exp (-X) * Real.exp X = Real.exp ((-X) + X) := by
            rw [← Real.exp_add]
          rw [h7]
          have h8 : (-X) + X = 0 := by ring
          rw [h8, Real.exp_zero]
        have h9 : Real.exp X = 1 / Real.exp (-X) := by
          have h6' : Real.exp X * Real.exp (-X) = 1 := by
            rw [mul_comm]
            exact h6
          exact (eq_div_iff h_pos.ne').mpr h6'
        exact h9.symm
      rw [h5, Real.log_exp]
    linarith
  set x : ℝ := Real.log (1 / δ) with hx_def
  have hx_pos : 0 < x := by linarith [hX1]
  have hx_ge_X : x ≥ X := h2
  -- log x < 2 * sqrt x
  have h5 : Real.log x < 2 * Real.sqrt x := h_log_sqrt x hx_pos
  -- x ≥ (2C/ε)^2 implies sqrt x ≥ 2C/ε, so 2C * sqrt x ≤ ε * x
  have h6 : Real.sqrt x ≥ 2 * C / ε := by
    have h7 : x ≥ (2 * C / ε)^2 := by linarith [hX2]
    have h8 : 0 ≤ 2 * C / ε := by positivity
    nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith)]
  have h9 : 2 * C * Real.sqrt x ≤ ε * x := by
    have h91 : ε * Real.sqrt x ≥ 2 * C := by
      calc ε * Real.sqrt x
        ≥ ε * (2 * C / ε) := by gcongr
        _ = 2 * C := by field_simp [hε.ne'] <;> ring
    have h92 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have h93 : ε * x = ε * (Real.sqrt x)^2 := by
      have h94 : (Real.sqrt x)^2 = x := Real.sq_sqrt (by linarith)
      rw [h94] <;> ring
    rw [h93]
    calc ε * (Real.sqrt x)^2
      = (ε * Real.sqrt x) * Real.sqrt x := by ring
    _ ≥ (2 * C) * Real.sqrt x := by gcongr
    _ = 2 * C * Real.sqrt x := by ring
  have h10 : C * Real.log x < ε * x := by
    have h101 : C * Real.log x < 2 * C * Real.sqrt x := by
      have h : C * Real.log x < C * (2 * Real.sqrt x) := mul_lt_mul_of_pos_left h5 hC
      have h2 : C * (2 * Real.sqrt x) = 2 * C * Real.sqrt x := by ring
      rw [h2] at h
      exact h
    linarith
  -- x^C = exp(C * log x) < exp(ε * x) = δ^{-ε}
  have h11 : Real.rpow x C = Real.exp (C * Real.log x) := by
    have h111 : x ^ C = Real.exp (C * Real.log x) := by
      have h := Real.rpow_def_of_pos hx_pos C
      rw [h]
      <;> ring_nf
    exact h111
  have h12 : Real.rpow δ (-ε) = Real.exp (ε * x) := by
    have h13 : Real.rpow δ (-ε) = Real.exp ((-ε) * Real.log δ) := by
      have h131 : δ ^ (-ε) = Real.exp ((-ε) * Real.log δ) := by
        have h := Real.rpow_def_of_pos hδ_pos (-ε)
        rw [h]
        <;> ring_nf
      exact h131
    rw [h13]
    have h14 : x = -Real.log δ := by
      rw [hx_def]
      have h15 : Real.log (1 / δ) = -Real.log δ := by
        rw [Real.log_div (by norm_num) hδ_pos.ne', Real.log_one] <;> ring
      exact h15
    rw [h14] <;> ring_nf
  rw [h11, h12]
  exact le_of_lt (Real.exp_strictMono h10)

end ParameterBudget
