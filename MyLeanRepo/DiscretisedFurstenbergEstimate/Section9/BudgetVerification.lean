module

/-
  Budget verification for Section 9 exponent absorption.

  Proves that with the parameter schedule in section9_main, the good gain
  ε_G*η/8 dominates all losses:
    ε_G*η/8 ≥ (1+C')*lam + ρ_M + ρ_T + ε_N + ε_bad + ε_log_loss + ε_final

  The key parameter relationships:
  - ε_N = ε_G*η/100
  - ε_bad < ε_N
  - ε_K = ε_N/(2*B_K), B_K ≥ 3
  - ε_Root = ε_K/2
  - ε_final = ε_Root/4 = ε_N/(16*B_K)

  We choose lam, ρ_M, ρ_T, ε_log_loss as fractions of ε_G*η:
  - lam = ε_G*η / (800 * max(1, C'))
  - ρ_M = ε_G*η / 800
  - ρ_T = ε_G*η / 800
  - ε_log_loss = ε_G*η / 800

  Then total losses < ε_G*η * (1/100 + 1/100 + 1/4800 + 4/800)
                     = ε_G*η * (0.02 + 0.000208 + 0.005)
                     < ε_G*η * 0.125 = ε_G*η/8

  Whiteprint node: section9 / budget_verification
  Status: DRAFT
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9

/-- Verify the absorption budget given the parameter schedule.

    Given the relationships between ε_N, ε_bad, ε_final and ε_G*η,
    and choosing lam, ρ_M, ρ_T, ε_log_loss sufficiently small,
    prove the budget inequality. -/
lemma absorption_budget_verification
    (ε_G η ε_N ε_bad ε_final : ℝ)
    (hεG_pos : 0 < ε_G) (hη_pos : 0 < η)
    (hεN_pos : 0 < ε_N) (hε_bad_pos : 0 < ε_bad) (hε_final_pos : 0 < ε_final)
    -- Parameter relationships
    (hεN_eq : ε_N = ε_G * η / 100)
    (hε_bad_lt : ε_bad < ε_N)
    (B_K : ℝ) (hBK_ge3 : B_K ≥ 3)
    (hε_final_eq : ε_final = ε_N / (16 * B_K))
    -- Chosen loss parameters
    (C' lam ρ_M ρ_T ε_log_loss : ℝ)
    (hC'_nonneg : 0 ≤ C')
    (hlam_pos : 0 < lam)
    (hρM_nonneg : 0 ≤ ρ_M) (hρT_nonneg : 0 ≤ ρ_T) (hεlog_nonneg : 0 ≤ ε_log_loss)
    -- Bounds on chosen parameters
    (hlam_bound : (1 + C') * lam ≤ ε_G * η / 800)
    (hρM_bound : ρ_M ≤ ε_G * η / 800)
    (hρT_bound : ρ_T ≤ ε_G * η / 800)
    (hεlog_bound : ε_log_loss ≤ ε_G * η / 800) :
    ε_G * η / 8 ≥ (1 + C') * lam + ρ_M + ρ_T + ε_N + ε_bad + ε_log_loss + ε_final := by
  have h1 : ε_N ≤ ε_G * η / 100 := by
    rw [hεN_eq] <;> linarith
  have h2 : ε_bad < ε_G * η / 100 := by
    rw [hεN_eq] at hε_bad_lt <;> linarith
  have h3 : ε_final ≤ ε_G * η / 4800 := by
    rw [hε_final_eq, hεN_eq]
    have h41 : ε_G * η / 100 / (16 * B_K) = ε_G * η / (100 * 16 * B_K) := by ring
    rw [h41]
    have h42 : 100 * 16 * B_K ≥ 4800 := by
      have h43 : B_K ≥ 3 := hBK_ge3
      nlinarith
    have h_pos : 0 < ε_G * η := mul_pos hεG_pos hη_pos
    exact div_le_div_of_nonneg_left h_pos.le (by positivity) h42
  have h4 : (1 + C') * lam + ρ_M + ρ_T + ε_N + ε_bad + ε_log_loss + ε_final ≤
      ε_G * η / 800 + ε_G * η / 800 + ε_G * η / 800 + ε_G * η / 100 + ε_G * η / 100 + ε_G * η / 800 + ε_G * η / 4800 := by
    gcongr <;> linarith
  have h5 : ε_G * η / 800 + ε_G * η / 800 + ε_G * η / 800 + ε_G * η / 100 + ε_G * η / 100 + ε_G * η / 800 + ε_G * η / 4800 ≤ ε_G * η / 8 := by
    have h_pos : 0 < ε_G * η := mul_pos hεG_pos hη_pos
    linarith
  linarith

end DirecretisedFurstenbergEstimate.Section9
