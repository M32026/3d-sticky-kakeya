module

/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Automated extraction from InductiveStepCore_v2
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.KPolynomialBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Arithmetic sub-proofs extracted from the non-all-bad branch

This module contains self-contained arithmetic lemmas extracted from
the non-all-bad branch of `inductive_step_core_v2` to reduce elaboration
time in the main proof.
-/

open scoped ENNReal NNReal

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M2

/-- Prove `K * δ^(-lam) ≤ δ^(-2*lam)` and `δbar^(-lam_tail) ≥ δ^(-2*lam)`,
given `K ≤ δ^(-lam)`, `δbar ≤ δ^τ`, and `τ * lam_tail = 2 * lam`. -/
lemma fine_tail_rpow_bound
    {δ δbar K lam lam_tail τ : ℝ}
    (hδ_pos : 0 < δ) (hδbar_pos : 0 < δbar)
    (hK_le : K ≤ Real.rpow δ (-lam))
    (hδbar_le_δτ : δbar ≤ Real.rpow δ τ)
    (hτ_lam_tail : τ * lam_tail = 2 * lam)
    (hlam : 0 < lam) (hlam_tail_pos : 0 < lam_tail) :
    K * Real.rpow δ (-lam) ≤ Real.rpow δ (-2 * lam) ∧
    Real.rpow δbar (-lam_tail) ≥ Real.rpow δ (-2 * lam) := by
  have hKδ : K * Real.rpow δ (-lam) ≤ Real.rpow δ (-2 * lam) := by
    have h2 : Real.rpow δ (-2 * lam) = Real.rpow δ (-lam) * Real.rpow δ (-lam) := by
      have h_sum : (-2 * lam) = (-lam) + (-lam) := by ring
      rw [h_sum]; exact Real.rpow_add hδ_pos (-lam) (-lam)
    rw [h2]; exact mul_le_mul_of_nonneg_right hK_le (Real.rpow_nonneg hδ_pos.le _)
  have hδτ_rpow : Real.rpow (Real.rpow δ τ) (-lam_tail) = Real.rpow δ (-2 * lam) := by
    have h3 : Real.rpow (Real.rpow δ τ) (-lam_tail) = Real.rpow δ (τ * (-lam_tail)) :=
      (Real.rpow_mul hδ_pos.le τ (-lam_tail)).symm
    have h4 : τ * (-lam_tail) = -2 * lam := by linarith
    rw [h3, h4]
  have hδbar_tail : Real.rpow δbar (-lam_tail) ≥ Real.rpow δ (-2 * lam) := by
    have h1 : Real.rpow δbar (-lam_tail) ≥ Real.rpow (Real.rpow δ τ) (-lam_tail) :=
      Real.rpow_le_rpow_of_nonpos hδbar_pos hδbar_le_δτ (by linarith)
    rw [hδτ_rpow] at h1; exact h1
  exact ⟨hKδ, hδbar_tail⟩

/-- Log bound for the fine scale: if `δbar ≤ δ^τ` and
`log(1/δ) ≥ τ^(-C_P_fine)`, then `log(1/δbar) ≥ τ^(-(C_P + C_n))`. -/
lemma small_log_bound
    {δbar δ τ C_P C_n C_P_fine : ℝ}
    (hδbar_pos : 0 < δbar) (hδ_pos : 0 < δ) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hδbar_le_δτ : δbar ≤ Real.rpow δ τ)
    (h_logδ_ge : Real.log (1 / δ) ≥ Real.rpow τ (-(C_P_fine : ℝ)))
    (hCn_ge1 : 1 ≤ C_n)
    (hCP_fine_eq : C_P_fine = C_P + 2 * C_n) :
    Real.log (1 / δbar) ≥ Real.rpow τ (-(C_P + C_n)) := by
  have h1 : Real.log (1 / δbar) ≥ τ * Real.log (1 / δ) := by
    have h2 : δbar ≤ Real.rpow δ τ := hδbar_le_δτ
    have h4 : 0 < Real.rpow δ τ := Real.rpow_pos_of_pos hδ_pos _
    have h5 : Real.log (1 / δbar) ≥ Real.log (1 / Real.rpow δ τ) :=
      Real.log_le_log (by positivity) (one_div_le_one_div_of_le (by positivity) h2)
    have h6 : Real.log (1 / Real.rpow δ τ) = τ * Real.log (1 / δ) := by
      have h7 : Real.log (1 / Real.rpow δ τ) = -Real.log (Real.rpow δ τ) := by
        rw [show (1 / Real.rpow δ τ) = (Real.rpow δ τ)⁻¹ by ring]
        rw [Real.log_inv]
      rw [h7]
      have h8 : Real.log (Real.rpow δ τ) = τ * Real.log δ := Real.log_rpow hδ_pos τ
      rw [h8]
      have h9 : Real.log (1 / δ) = -Real.log δ := by
        rw [Real.log_div (by norm_num) hδ_pos.ne', Real.log_one, zero_sub]
      rw [h9] <;> ring
    rw [h6] at h5; exact h5
  have h_mult : τ * Real.log (1 / δ) ≥ τ * Real.rpow τ (-(C_P_fine : ℝ)) := by
    gcongr <;> linarith
  have h6 : Real.log (1 / δbar) ≥ τ * Real.rpow τ (-(C_P_fine : ℝ)) :=
    le_trans h_mult h1
  have h7 : τ * Real.rpow τ (-(C_P_fine : ℝ)) = Real.rpow τ (1 - (C_P_fine : ℝ)) := by
    have h9 : Real.rpow τ (1 + (-(C_P_fine : ℝ))) = Real.rpow τ 1 * Real.rpow τ (-(C_P_fine : ℝ)) :=
      Real.rpow_add hτ 1 (-(C_P_fine : ℝ))
    have h10 : 1 + (-(C_P_fine : ℝ)) = 1 - (C_P_fine : ℝ) := by ring
    have h11 : Real.rpow τ 1 = τ := by simp
    rw [h10] at h9; rw [h11] at h9; exact h9.symm
  rw [h7] at h6
  have h9 : 1 - (C_P_fine : ℝ) ≤ -(C_P + C_n) := by
    rw [hCP_fine_eq] <;> linarith
  have h10 : Real.rpow τ (1 - (C_P_fine : ℝ)) ≥ Real.rpow τ (-(C_P + C_n)) :=
    Real.rpow_le_rpow_of_exponent_ge hτ (by linarith) h9
  exact le_trans h10 h6

/-- Positivity and ordering facts for `m`, `k` in the inductive step. -/
lemma fine_scale_positivity
    {m k : ℕ} {Δ1 : ℝ}
    (hm_eq2 : Δ1 = dyadicDelta m)
    (hΔ_lt_one : Δ1 < 1)
    (hk_exp1 : dyadicDelta k ≤ Real.exp (-1))
    (hΔk_lt_Δm : dyadicDelta k < dyadicDelta m) :
    0 < m ∧ 0 < k ∧ m < k := by
  have hm_pos : 0 < m := by
    by_contra h; have h' : m = 0 := by omega
    have h_eq1 : dyadicDelta m = 1 := by rw [h']; dsimp only [dyadicDelta]; norm_num
    have h_contra : Δ1 = 1 := Eq.trans hm_eq2 h_eq1
    rw [h_contra] at hΔ_lt_one; exact lt_irrefl 1 hΔ_lt_one
  have hk_pos : 0 < k := by
    have h1 : dyadicDelta k < 1 := by
      have h2 : Real.exp (-1) < 1 := by
        have h4 : Real.exp (-1 : ℝ) < Real.exp 0 := Real.exp_strictMono (by norm_num)
        simpa using h4
      exact lt_of_le_of_lt hk_exp1 h2
    by_contra h5; have h6 : k = 0 := by omega
    rw [h6] at h1; simp [dyadicDelta] at h1 <;> norm_num at h1 <;> linarith
  have hm_lt_k : m < k := dyadicDelta_strict_anti' hΔk_lt_Δm
  exact ⟨hm_pos, hk_pos, hm_lt_k⟩

/-- Slope bound for fine configuration tubes: `|T.slope| ≤ 1`. -/
lemma fine_slope_bound {k m : ℕ} {s C : ℝ} {M' : ℕ}
    {config'' : CTNiceConfiguration (k - m) s C M'}
    (hB1_fine : B1BridgeHypotheses (k - m) config'')
    (T : DyadicTube (k - m)) (hT : T ∈ config''.T₀) :
    |T.slope| ≤ 1 := by
  have h_strip : -(2 ^ (k - m) : ℤ) ≤ T.a ∧ T.a < (2 ^ (k - m) : ℤ) :=
    hB1_fine.h_tubes_strip T hT
  have h1 : (T.a : ℝ) ≥ -(2 ^ (k - m) : ℝ) := by exact_mod_cast h_strip.1
  have h2 : (T.a : ℝ) < (2 ^ (k - m) : ℝ) := by exact_mod_cast h_strip.2
  have h3 : |(T.a : ℝ)| ≤ (2 ^ (k - m) : ℝ) := by rw [abs_le]; constructor <;> linarith
  have h4 : T.slope = (T.a : ℝ) * dyadicDelta (k - m) := by simp [DyadicTube.slope]
  rw [h4]
  have h5 : |(T.a : ℝ) * dyadicDelta (k - m)| = |(T.a : ℝ)| * dyadicDelta (k - m) := by
    rw [abs_mul, abs_of_pos (dyadicDelta_pos (k - m))]
  rw [h5]
  have h6 : dyadicDelta (k - m) = 1 / (2 : ℝ) ^ (k - m) := by simp [dyadicDelta] <;> field_simp
  rw [h6]
  have h7 : |(T.a : ℝ)| * (1 / (2 : ℝ) ^ (k - m)) ≤ 1 := by
    calc |(T.a : ℝ)| * (1 / (2 : ℝ) ^ (k - m))
      ≤ (2 ^ (k - m) : ℝ) * (1 / (2 : ℝ) ^ (k - m)) := by gcongr
    _ = 1 := by field_simp <;> ring
  exact h7

end DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure
