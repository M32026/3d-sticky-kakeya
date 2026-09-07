module

/-
  K Polynomial Bound — Extract from InductiveStepCore_v2.

  Proves K ≤ A * log(1/δ)^α and 1 ≤ log(1/δ) using the B1 bridge bound
  K ≤ Poly(k) and the identity Poly(k) ≤ A * log(1/δ)^7.

  Whiteprint node: combining_theorem_genuine / inductive_step_core_v2
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure

/-- dyadicDelta is strictly antitone: larger n gives smaller delta. -/
lemma dyadicDelta_strict_anti' {a b : ℕ} (h : dyadicDelta a > dyadicDelta b) : a < b := by
  dsimp only [dyadicDelta] at h
  have h6 : (2 : ℝ)^a < (2 : ℝ)^b :=
    lt_of_one_div_lt_one_div (by positivity) h
  by_contra h10
  have h11 : b ≤ a := by omega
  have h12 : (2 : ℝ)^b ≤ (2 : ℝ)^a := pow_le_pow_right₀ (by norm_num) h11
  linarith

/-- Helper: polynomial bound (4k+7)^7 ≤ (8k)^7 for k≥2. -/
lemma poly_bound_helper' (k : ℕ) (hk : 2 ≤ k) :
    (4 * (k : ℝ) + 7)^7 ≤ (8 * (k : ℝ))^7 := by
  have h : (k : ℝ) ≥ 2 := by exact_mod_cast hk
  have h4k : 4 * (k : ℝ) + 7 ≤ 8 * (k : ℝ) := by
    have h2 : 4 * (k : ℝ) ≥ 8 := by
      have h3 : 4 * (2 : ℝ) ≤ 4 * (k : ℝ) := mul_le_mul_of_nonneg_left h (by norm_num)
      norm_num at h3; exact h3
    linarith
  have h_pos : 0 ≤ 4 * (k : ℝ) + 7 := by positivity
  gcongr

/-- Helper: polynomial log simplification (mixed natural/real powers). -/
lemma log_poly_simplification_mixed' (k : ℕ) (hk : 2 ≤ k) {α : ℝ} (hα7 : α = (7 : ℝ)) :
    2700 * 3145728 * (8 / Real.log 2)^7 * ((k : ℝ) * Real.log 2)^α =
    2700 * 3145728 * (8 * (k : ℝ))^7 := by
  have h_cast2 : ((k : ℝ) * Real.log 2)^α = ((k : ℝ) * Real.log 2)^7 := by
    have h10 : ((k : ℝ) * Real.log 2)^α = ((k : ℝ) * Real.log 2)^(7 : ℝ) := by rw [hα7]
    have h11 : ((k : ℝ) * Real.log 2)^(7 : ℝ) = ((k : ℝ) * Real.log 2)^7 := Real.rpow_natCast _ 7
    exact Eq.trans h10 h11
  rw [h_cast2]
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (8 / Real.log 2) * ((k : ℝ) * Real.log 2) = 8 * (k : ℝ) := by
    field_simp [h_log2_pos.ne'] <;> ring
  have h2 : (8 / Real.log 2)^7 * ((k : ℝ) * Real.log 2)^7 = (8 * (k : ℝ))^7 := by
    rw [←mul_pow, h1]
  have h3 : 2700 * 3145728 * (8 / Real.log 2)^7 * ((k : ℝ) * Real.log 2)^7 =
      2700 * 3145728 * ((8 / Real.log 2)^7 * ((k : ℝ) * Real.log 2)^7) := by ring
  rw [h3, h2]

/-- Polynomial bound: K ≤ A * log(1/dyadicDelta k)^α, given α=7. -/
lemma k_polynomial_bound
    {k m : ℕ} {K A α : ℝ} {Δ_coarse : ℝ}
    (hK_bound : K ≤ (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7)
    (hA_eq : A = 2700 * 3145728 * (8 / Real.log 2)^7)
    (hα7 : α = (7 : ℝ))
    (hm_eq2 : Δ_coarse = dyadicDelta m)
    (hΔ_lt_one : Δ_coarse < 1)
    (hΔk_lt_Δm : dyadicDelta k < dyadicDelta m) :
    K ≤ A * (Real.log (1 / dyadicDelta k)) ^ α := by
  have h_logδ : Real.log (1 / dyadicDelta k) = (k : ℝ) * Real.log 2 := by
    have h1 : 1 / dyadicDelta k = (2 : ℝ)^k := by
      dsimp only [dyadicDelta]
      field_simp <;> ring
    rw [h1, Real.log_pow] <;> norm_num
  have h_k_ge2 : 2 ≤ k := by
    have h_m_ge1 : 1 ≤ m := by
      by_contra h; have h' : m = 0 := by omega
      have h_eq1 : dyadicDelta m = 1 := by
        rw [h']; dsimp only [dyadicDelta]; norm_num
      have h_contra : Δ_coarse = 1 := by
        calc Δ_coarse = dyadicDelta m := hm_eq2
          _ = 1 := h_eq1
      have h : Δ_coarse < 1 := hΔ_lt_one
      rw [h_contra] at h
      exact lt_irrefl 1 h
    have hmk : m < k := dyadicDelta_strict_anti' hΔk_lt_Δm
    omega
  have h_main : (4 * (k : ℝ) + 7)^7 ≤ (8 * (k : ℝ))^7 :=
    poly_bound_helper' k h_k_ge2
  have h_RHS : A * (Real.log (1 / dyadicDelta k)) ^ α =
      2700 * 3145728 * (8 * (k : ℝ))^7 := by
    rw [hA_eq, h_logδ]
    exact log_poly_simplification_mixed' k h_k_ge2 hα7
  rw [h_RHS]
  have h_mul : 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 ≤
      2700 * 3145728 * (8 * (k : ℝ))^7 := by
    apply mul_le_mul_of_nonneg_left h_main; positivity
  calc K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 := hK_bound
    _ ≤ 2700 * 3145728 * (8 * (k : ℝ))^7 := h_mul

/-- Log bound: 1 ≤ log(1/dyadicDelta k) from dyadicDelta k ≤ exp(-1). -/
lemma log_one_over_dyadic_ge_one
    {k : ℕ}
    (hk_exp1 : dyadicDelta k ≤ Real.exp (-1)) :
    1 ≤ Real.log (1 / dyadicDelta k) := by
  have h3 : 0 < dyadicDelta k := dyadicDelta_pos k
  have h1 : dyadicDelta k ≤ Real.exp (-1) := hk_exp1
  have h2 : 0 < Real.exp 1 := Real.exp_pos 1
  have h3' : dyadicDelta k ≤ (Real.exp 1)⁻¹ := by
    have h4 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    rw [h4] at h1; exact h1
  have h4 : 1 / dyadicDelta k ≥ 1 / (Real.exp 1)⁻¹ :=
    one_div_le_one_div_of_le h3 h3'
  have h5 : 1 / (Real.exp 1)⁻¹ = Real.exp 1 := by
    simpa [one_div] using inv_inv h2
  have h6 : 1 / dyadicDelta k ≥ Real.exp 1 := by
    rw [h5] at h4; exact h4
  have h7 : Real.log (1 / dyadicDelta k) ≥ Real.log (Real.exp 1) :=
    Real.log_le_log (by positivity) h6
  have h8 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
  rw [h8] at h7; exact h7

end Prop73Restructure

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
