module

/-
  Scale Conversion Helpers for Fine Ratio Chain

  Provides elementary identities for the n=2m scale conversion:
  1. dyadicDelta m = Real.sqrt (dyadicDelta n)
  2. log(1/δ_m) = (1/2) * log(1/δ_n)
  3. δ_m^(-s) = δ_n^(-s/2)

  Also provides `fine_ratio_convert_for_chain`, a convenience wrapper
  around `fine_ratio_explicit_uniform` that directly produces the
  `h_convert` hypothesis needed by `clean_fine_cor25_chain`.

  Whiteprint node: scale_conversion_helpers
  Status: IMPLEMENTED
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.FineRatioExplicit
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section6

open DiscretisedFurstenbergEstimate

/-- For n = 2*m, dyadicDelta n = (dyadicDelta m)^2. -/
lemma dyadicDelta_square {n m : ℕ} (h_even : n = 2 * m) :
    dyadicDelta n = (dyadicDelta m) ^ 2 := by
  simp only [dyadicDelta, h_even]
  <;> ring

/-- For n = 2*m, dyadicDelta m = Real.sqrt (dyadicDelta n). -/
lemma dyadicDelta_sqrt {n m : ℕ} (h_even : n = 2 * m) :
    dyadicDelta m = Real.sqrt (dyadicDelta n) := by
  have h2 : dyadicDelta n = (dyadicDelta m) ^ 2 := dyadicDelta_square h_even
  have h3 : 0 < dyadicDelta m := dyadicDelta_pos m
  have h4 : Real.sqrt (dyadicDelta n) = dyadicDelta m := by
    rw [h2]
    rw [Real.sqrt_sq (by linarith)]
  exact h4.symm

/-- For n = 2*m, n - m = m. -/
lemma dyadicDelta_half_diff {n m : ℕ} (h_even : n = 2 * m) (hnm : m ≤ n) :
    n - m = m := by omega

/-- For n = 2*m, log(1/dyadicDelta (n-m)) = (1/2) * log(1/dyadicDelta n). -/
lemma log_dyadicDelta_half {n m : ℕ} (h_even : n = 2 * m) (hnm : m ≤ n) :
    Real.log (1 / dyadicDelta (n - m)) = (1 / 2 : ℝ) * Real.log (1 / dyadicDelta n) := by
  set δ : ℝ := dyadicDelta n with hδ_def
  set δ' : ℝ := dyadicDelta (n - m) with hδ'_def
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ'_eq : δ' = Real.sqrt δ := by
    have h1 : n - m = m := dyadicDelta_half_diff h_even hnm
    rw [hδ'_def, h1]
    exact dyadicDelta_sqrt h_even
  rw [hδ'_eq]
  have h5 : Real.log (1 / Real.sqrt δ) = -Real.log (Real.sqrt δ) := by
    rw [Real.log_div (by norm_num) (Real.sqrt_pos.mpr hδ_pos).ne', Real.log_one] <;> ring
  rw [h5]
  have h6 : Real.log (Real.sqrt δ) = (1 / 2 : ℝ) * Real.log δ := by
    rw [Real.log_sqrt (by linarith)] <;> ring
  rw [h6]
  have h7 : Real.log (1 / δ) = -Real.log δ := by
    rw [Real.log_div (by norm_num) hδ_pos.ne', Real.log_one] <;> ring
  linarith

/-- For n = 2*m, (dyadicDelta (n-m))^(-s) = (dyadicDelta n)^(-s/2). -/
lemma rpow_dyadicDelta_half {n m : ℕ} (h_even : n = 2 * m) (hnm : m ≤ n) (s : ℝ) :
    (dyadicDelta (n - m)) ^ (-s) = (dyadicDelta n) ^ (-s / 2) := by
  set δ : ℝ := dyadicDelta n with hδ_def
  set δ' : ℝ := dyadicDelta (n - m) with hδ'_def
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ'_eq : δ' = Real.sqrt δ := by
    have h1 : n - m = m := dyadicDelta_half_diff h_even hnm
    rw [hδ'_def, h1]
    exact dyadicDelta_sqrt h_even
  rw [hδ'_eq]
  have h_sqrt : Real.sqrt δ = δ ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
  rw [h_sqrt]
  have h3 : (δ ^ (1 / 2 : ℝ)) ^ (-s) = δ ^ ((1 / 2 : ℝ) * (-s)) := by
    rw [←Real.rpow_mul (by linarith)] <;> rfl
  rw [h3]
  have h4 : (1 / 2 : ℝ) * (-s) = -s / 2 := by ring
  rw [h4]

/-- Convenience wrapper: produce h_convert for clean_fine_cor25_chain.

    Given power bounds on C_ret (expressed via the formula) and C_Q,
    use `fine_ratio_explicit_uniform` to obtain a threshold δ₀ such that
    for δ_n ≤ δ₀, the scale conversion inequality holds.

    The caller must supply C_ret directly (typically the formula
    `C_point * 9 * K_global * |coarseConfig.P₀| * δ_m^u`). -/
lemma fine_ratio_convert_for_chain
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
        (1 / K) * Real.log (1 / dyadicDelta (n - m)) ^ (-K) *
          (1 / ((81 * max C_ret 1 * (2 * Real.sqrt 2) ^ s) *
            (13 * C_Q * Real.rpow 2 s))) *
          (dyadicDelta (n - m)) ^ (-s) ≥
        (dyadicDelta n) ^ (-(s / 2 - (a + b + polylogLoss))) :=
  fine_ratio_explicit_uniform ha_nonneg hb_nonneg hpolylogLoss_pos hK_pos

end DirecretisedFurstenbergEstimate.Section6

end
