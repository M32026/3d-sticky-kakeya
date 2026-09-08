/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic.Positivity

/-!
# Sub-polynomial growth of exponentials and logarithms

Elementary real-analysis bounds saying that `exp ((log a⁻¹) ^ α)` with `α < 1`, and any linear or
logarithmic function of `log δ⁻¹`, is dominated by `δ ^ (-ε)` for every `ε > 0`.
-/

@[expose] public section

noncomputable section

namespace Kakeya

lemma log_inv_pos {a : NNReal} (ha : 0 < a) (ha1 : a < 1) : 0 < Real.log (a : ℝ)⁻¹ := by
  rw [Real.log_inv]
  have hapos : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have ha1' : (a:ℝ) < 1 := by exact_mod_cast ha1
  have := Real.log_neg hapos ha1'
  linarith

/-- **Sub-polynomial growth.** Fix `0 ≤ α < 1`. For every `ε > 0` there is a constant `C_ε` such
that, for all `0 < a < 1`, `exp((log a⁻¹) ^ α) ≤ C_ε · a ^ (-ε)`. -/
lemma subpolyExp {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → a < 1 →
      Real.exp ((Real.log a⁻¹) ^ α) ≤ C * a ^ (-ε) := by
  -- Reduce to a uniform linear bound on the exponent: `t ^ α ≤ ε * t + K` for `t ≥ 0`.
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ t : ℝ, 0 ≤ t → t ^ α ≤ ε * t + K := by
    rcases eq_or_lt_of_le hα0 with hα | hα
    · -- `α = 0`: `t ^ 0 = 1 ≤ ε t + 1`.
      refine ⟨1, fun t ht => ?_⟩
      rw [← hα, Real.rpow_zero]
      linarith [mul_nonneg hε.le ht]
    · -- `0 < α < 1`: weighted AM-GM `x ^ α ≤ α x + (1 - α)` applied at `x = c t`,
      -- with `c = (ε / α) ^ (1 / (1 - α))` chosen so the `t`-coefficient is exactly `ε`.
      set c : ℝ := (ε / α) ^ (1 / (1 - α)) with hc
      have hα1' : 0 < 1 - α := by linarith
      have hcpos : 0 < c := Real.rpow_pos_of_pos (div_pos hε hα) _
      have hαne : α ≠ 0 := hα.ne'
      have hc1 : c ^ (1 - α) = ε / α := by
        rw [hc, ← Real.rpow_mul (div_pos hε hα).le, one_div_mul_cancel hα1'.ne', Real.rpow_one]
      have hAB : c ^ α * c ^ (-α) = 1 := by
        rw [← Real.rpow_add hcpos, add_neg_cancel, Real.rpow_zero]
      have hcB : c * c ^ (-α) = ε / α := by
        rw [← hc1, show (1:ℝ) - α = 1 + (-α) by ring, Real.rpow_add hcpos, Real.rpow_one]
      refine ⟨(1 - α) * c ^ (-α), fun t ht => ?_⟩
      have hmul : c ^ α * t ^ α ≤ α * (c * t) + (1 - α) := by
        have h := Real.geom_mean_le_arith_mean2_weighted hα0 hα1'.le
          (mul_nonneg hcpos.le ht) zero_le_one (by ring)
        rwa [Real.one_rpow, mul_one, mul_one, Real.mul_rpow hcpos.le ht] at h
      have step := mul_le_mul_of_nonneg_left hmul (Real.rpow_pos_of_pos hcpos (-α)).le
      rw [show c ^ (-α) * (c ^ α * t ^ α) = t ^ α by
            rw [← mul_assoc, mul_comm (c ^ (-α)) (c ^ α), hAB, one_mul],
        show c ^ (-α) * (α * (c * t) + (1 - α)) = ε * t + (1 - α) * c ^ (-α) by
            rw [show c ^ (-α) * (α * (c * t) + (1 - α))
                  = α * t * (c * c ^ (-α)) + (1 - α) * c ^ (-α) by ring, hcB]
            field_simp] at step
      exact step
  -- Assemble: with `t = log a⁻¹ ≥ 0`, `a ^ (-ε) = exp (ε t)`, so `C = exp K` works.
  refine ⟨Real.exp K, Real.exp_pos K, fun a ha ha1 => ?_⟩
  have ht : 0 ≤ Real.log a⁻¹ := by
    rw [Real.log_inv]; linarith [Real.log_nonpos ha.le ha1.le]
  rw [show a ^ (-ε) = Real.exp (ε * Real.log a⁻¹) by
        rw [Real.rpow_def_of_pos ha, Real.log_inv]; congr 1; ring,
    ← Real.exp_add, Real.exp_le_exp]
  linarith [hK _ ht]

/-- A linear function of `log δ⁻¹` is sub-polynomial: for `δ ∈ (0,1]` it is bounded by
`(c + d/ε) · δ^(-ε)`. -/
lemma linlog_le {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    c + d * Real.log δ⁻¹ ≤ (c + d / ε) * δ ^ (-ε) := by
  have ht : 0 ≤ Real.log δ⁻¹ := by
    rw [Real.log_inv]; linarith [Real.log_nonpos hδ0.le hδ1]
  have hexp : δ ^ (-ε) = Real.exp (ε * Real.log δ⁻¹) := by
    rw [Real.rpow_def_of_pos hδ0, Real.log_inv]; congr 1; ring
  rw [hexp]
  set t := Real.log δ⁻¹
  have h1 : (1:ℝ) ≤ Real.exp (ε * t) := Real.one_le_exp_iff.mpr (by positivity)
  have h2 : ε * t ≤ Real.exp (ε * t) := le_trans (by linarith) (Real.add_one_le_exp (ε * t))
  have hct : c ≤ c * Real.exp (ε * t) := le_mul_of_one_le_right hc h1
  have hdt : d * t ≤ (d / ε) * Real.exp (ε * t) := by
    rw [show d * t = (d / ε) * (ε * t) by field_simp]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

/-- **The constant of `Kakeya.logarg_subpoly`, named.**

`logargConst M N r ε = r + log⁺M / log 2 + (N⁺ / log 2) / ε`, where `x⁺ = max x 0`.

Naming it is the whole point of `Kakeya.logarg_subpoly_le` below: the constant is
**logarithmic in `M`**, which is what lets a consumer that feeds a `δ`-dependent `M` — such as
`Kakeya.VeryNotSticky.CaseScale.typicalAngle_const`, whose plank count carries `δ^{-2ϱ}` —
see that the growth is polylogarithmic in `δ⁻¹` and hence beaten by any fixed positive power
of `δ⁻¹`.  The existential form `Kakeya.logarg_subpoly` hides exactly that. -/
noncomputable def logargConst (M N r ε : ℝ) : ℝ :=
  (r + max (Real.log M) 0 / Real.log 2) + (max N 0 / Real.log 2) / ε

/-- `logargConst` is nonnegative for `0 ≤ r`, `0 < ε`, and at least `r`. -/
lemma le_logargConst {M N r ε : ℝ} (hε : 0 < ε) : r ≤ logargConst M N r ε := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : 0 ≤ max (Real.log M) 0 / Real.log 2 :=
    div_nonneg (le_max_right _ _) hlog2.le
  have h2 : 0 ≤ (max N 0 / Real.log 2) / ε :=
    div_nonneg (div_nonneg (le_max_right _ _) hlog2.le) hε.le
  rw [logargConst]; linarith

/-- `logargConst` is nonnegative for `0 ≤ r` and `0 < ε`. -/
lemma logargConst_nonneg {M N r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    0 ≤ logargConst M N r ε :=
  hr.trans (le_logargConst hε)

/-- **The `M`-free part of `Kakeya.logargConst`.**

`logargBase N r ε = r + (log 2)⁻¹ + (N⁺ / log 2) / ε`.  It depends on `N`, `r` and `ε` only,
and `Kakeya.logargConst_le_logargBase_mul` says
`logargConst M N r ε ≤ logargBase N r ε · (log⁺M + 1)`: the constant grows **logarithmically**
in `M`, uniformly in `M`. -/
noncomputable def logargBase (N r ε : ℝ) : ℝ :=
  r + (Real.log 2)⁻¹ + (max N 0 / Real.log 2) / ε

lemma logargBase_nonneg {N r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) : 0 ≤ logargBase N r ε := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (0:ℝ) ≤ (Real.log 2)⁻¹ := by positivity
  have h2 : 0 ≤ (max N 0 / Real.log 2) / ε :=
    div_nonneg (div_nonneg (le_max_right _ _) hlog2.le) hε.le
  rw [logargBase]; linarith

/-- **The constant of `Kakeya.logarg_subpoly` grows at most logarithmically in `M`.** -/
lemma logargConst_le_logargBase_mul {M N r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    logargConst M N r ε ≤ logargBase N r ε * (max (Real.log M) 0 + 1) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLM : (0:ℝ) ≤ max (Real.log M) 0 := le_max_right _ _
  have hinv : (0:ℝ) ≤ (Real.log 2)⁻¹ := by positivity
  have hNt : 0 ≤ (max N 0 / Real.log 2) / ε :=
    div_nonneg (div_nonneg (le_max_right _ _) hlog2.le) hε.le
  have hkey : max (Real.log M) 0 / Real.log 2
      ≤ logargBase N r ε * max (Real.log M) 0 := by
    rw [div_eq_mul_inv, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ hLM
    rw [logargBase]; linarith
  have hrest : r + (max N 0 / Real.log 2) / ε ≤ logargBase N r ε := by
    rw [logargBase]; linarith
  rw [logargConst, mul_add, mul_one]
  linarith

/-- **`Kakeya.logarg_subpoly` at the named constant.**  This is the statement with the witness
exposed; `Kakeya.logarg_subpoly` is the immediate consequence. -/
lemma logarg_subpoly_le {M N r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    ∀ (δ x : ℝ), 0 < δ → δ ≤ 1 → 0 ≤ x → x ≤ M * δ ^ (-N) →
      Real.log x / Real.log 2 + r ≤ logargConst M N r ε * δ ^ (-ε) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [logargConst]
  intro δ x hδ0 hδ1 hx0 hxle
  have hnl : (0:ℝ) ≤ -Real.log δ := by linarith [Real.log_nonpos hδ0.le hδ1]
  -- `log x ≤ max(log M, 0) + max(N, 0) · log δ⁻¹`.
  have hlogx : Real.log x ≤ max (Real.log M) 0 + max N 0 * Real.log δ⁻¹ := by
    rw [Real.log_inv]
    have hB : N * -Real.log δ ≤ max N 0 * -Real.log δ :=
      mul_le_mul_of_nonneg_right (le_max_left N 0) hnl
    rcases eq_or_lt_of_le hx0 with hx | hx
    · rw [← hx, Real.log_zero]
      linarith [le_max_right (Real.log M) 0, mul_nonneg (le_max_right N 0) hnl]
    · have hM : 0 < M := by
        rcases mul_pos_iff.mp (hx.trans_le hxle) with ⟨h, -⟩ | ⟨-, h⟩
        · exact h
        · exact absurd h (Real.rpow_pos_of_pos hδ0 _).asymm
      have h1 : Real.log x ≤ Real.log (M * δ ^ (-N)) := Real.log_le_log hx hxle
      rw [Real.log_mul hM.ne' (Real.rpow_pos_of_pos hδ0 _).ne', Real.log_rpow hδ0] at h1
      linarith [le_max_left (Real.log M) 0]
  -- divide by `log 2`, add `r`, then apply `linlog_le`.
  refine le_trans ?_ (linlog_le ?_ ?_ hε hδ0 hδ1)
  · simp only [div_eq_mul_inv]
    linarith [mul_le_mul_of_nonneg_right hlogx (inv_pos.mpr hlog2).le]
  · positivity
  · positivity

/-- A logarithm of a polynomially-bounded quantity is sub-polynomial. If `0 ≤ x ≤ M · δ^(-N)`
then `log x / log 2 + r ≤ K · δ^(-ε)` for a `δ`-independent `K`.  The witness is
`Kakeya.logargConst M N r ε`; use `Kakeya.logarg_subpoly_le` when the value matters. -/
lemma logarg_subpoly {M N r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    ∃ K : ℝ, ∀ (δ x : ℝ), 0 < δ → δ ≤ 1 → 0 ≤ x → x ≤ M * δ ^ (-N) →
      Real.log x / Real.log 2 + r ≤ K * δ ^ (-ε) :=
  ⟨logargConst M N r ε, logarg_subpoly_le hr hε⟩

/-- Every fixed power of `log a⁻¹` is eventually dominated by `exp ((log a⁻¹) ^ (1/4))`. -/
lemma logloss_ge_Ainv (k : ℕ) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ a₀ < 1 ∧ ∀ a : ℝ, 0 < a → a < a₀ →
      (Real.log a⁻¹) ^ k ≤ Real.exp ((Real.log a⁻¹) ^ (1/4 : ℝ)) := by
  -- Threshold `a₀ = exp (-exp (32k))`, i.e. `u := log t ≥ 32k` where `t = log a⁻¹`.
  refine ⟨Real.exp (-Real.exp (32 * k)), Real.exp_pos _, ?_, fun a ha ha0 => ?_⟩
  · rw [Real.exp_lt_one_iff, neg_lt_zero]
    exact Real.exp_pos _
  · have hT : Real.exp (32 * (k : ℝ)) < Real.log a⁻¹ := by
      have h := Real.log_lt_log ha ha0
      rw [Real.log_exp] at h
      rw [Real.log_inv]
      linarith
    set t : ℝ := Real.log a⁻¹ with ht
    have htpos : 0 < t := (Real.exp_pos _).trans hT
    -- `u = log t ≥ 32k ≥ 0`, and `exp (u / 4) ≥ 1 + u/4 + u²/32 ≥ k * u` by `u ≥ 32k`.
    have hu : 32 * (k : ℝ) ≤ Real.log t := by
      have h := Real.log_lt_log (Real.exp_pos _) hT
      rw [Real.log_exp] at h
      linarith
    have hun : (0 : ℝ) ≤ Real.log t := le_trans (by positivity) hu
    have key : (k : ℝ) * Real.log t ≤ Real.exp (Real.log t * (1 / 4)) := by
      have hsq : 0 ≤ (Real.log t - 32 * (k : ℝ)) * Real.log t :=
        mul_nonneg (by linarith) hun
      linarith [Real.quadratic_le_exp_of_nonneg (by linarith : (0:ℝ) ≤ Real.log t * (1/4))]
    rw [Real.rpow_def_of_pos htpos, ← Real.exp_log (pow_pos htpos k), Real.log_pow]
    exact Real.exp_le_exp.mpr key

end Kakeya

end

end
