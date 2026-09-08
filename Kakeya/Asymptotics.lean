/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Asymptotic helpers

Small analytic helpers shared by the partial estimates: an `eventually`-form of
`δ ^ ρ → 0`, and a transfer of a real product bound into a negative `ℝ≥0∞`-power bound.

The abstract infimum argument driving the two bootstraps is in `Kakeya/Bootstrap.lean`.
-/

@[expose] public section

open Filter Topology

namespace ENNReal

/-- For positive `ρ` and any positive `C : ℝ≥0∞`, eventually `(δ : ℝ≥0∞) ^ ρ ≤ C`
as `δ → 0+` in `ℝ≥0`. -/
lemma eventually_coe_rpow_le_of_pos {ρ : ℝ} (hρ : 0 < ρ) {C : ENNReal} (hC : 0 < C) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), (δ : ENNReal) ^ ρ ≤ C := by
  have h_lim : Tendsto (fun δ : NNReal => (δ : ENNReal) ^ ρ) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun δ : NNReal => (δ : ENNReal)) (𝓝[>] 0) (𝓝 0) :=
      ENNReal.continuous_coe.continuousAt.tendsto.comp nhdsWithin_le_nhds
    simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hρ] using
      (ENNReal.continuous_rpow_const (y := ρ)).continuousAt.tendsto.comp h1
  exact h_lim.eventually <| eventually_le_nhds hC

/-- **The dyadic-pigeonholing loss is subpolynomial** (blueprint `lem:eventuallyPolylogLeRpow`).

For every `ε > 0` and every `k : ℕ`, eventually as `δ → 0⁺` in `ℝ≥0` we have
`(1 + log₂ (1/δ)) ^ k ≤ δ ^ (-ε)`.

This is the arithmetic step that absorbs a polylogarithmic pigeonholing loss into an
arbitrarily small negative power of the scale.  Its shape is chosen to match the losses that
actually occur: the factor `ENNReal.ofReal (1 + Real.logb 2 (1 / δ)) ^ dim` of
`Kakeya.nonempty_factorization.C`, and one factor per dyadic pigeonhole.

A cardinality factor `1 + log₂ N` with `N ≤ δ ^ (-m)` needs no separate statement: for
`δ ≤ 1/2` one has `1 + Real.logb 2 N ≤ (1 + Real.logb 2 (1 / δ)) ^ m`, so it is covered by
the same lemma with `k` enlarged by `m`. -/
lemma eventually_ofReal_one_add_logb_pow_le_rpow_neg {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal),
      ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : ℝ))) ^ k ≤ (δ : ENNReal) ^ (-ε) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  let C : ℝ := (1 + 1 / Real.log 2) ^ k
  have hC_pos : 0 < C := by
    dsimp [C]
    exact pow_pos (by positivity) k
  -- Eventually in `t`: `(1 + t / log 2) ^ k ≤ exp (ε * t)`.
  have h_poly_exp : ∀ᶠ t : ℝ in atTop, (1 + t / Real.log 2) ^ k ≤ Real.exp (ε * t) := by
    have h_lo : (fun t : ℝ => t ^ k) =o[atTop] fun t => Real.exp (ε * t) :=
      isLittleO_pow_exp_pos_mul_atTop k hε
    have h_main : ∀ᶠ t : ℝ in atTop, C * t ^ k ≤ Real.exp (ε * t) := by
      have hb' : ∀ᶠ t in atTop, ‖t ^ k‖ ≤ C⁻¹ * ‖Real.exp (ε * t)‖ :=
        h_lo.def (inv_pos.mpr hC_pos)
      filter_upwards [hb', (eventually_ge_atTop (0 : ℝ))] with t ht hnonneg
      have hnorm₁ : ‖t ^ k‖ = t ^ k := by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hnonneg k)]
      have hnorm₂ : ‖Real.exp (ε * t)‖ = Real.exp (ε * t) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      calc
        C * t ^ k ≤ C * (C⁻¹ * Real.exp (ε * t)) := by
          exact mul_le_mul_of_nonneg_left (by simpa [hnorm₁, hnorm₂] using ht) hC_pos.le
        _ = Real.exp (ε * t) := by rw [← mul_assoc, mul_inv_cancel₀ hC_pos.ne', one_mul]
    filter_upwards [h_main, (eventually_ge_atTop (1 : ℝ))] with t hmain ht1
    calc
      (1 + t / Real.log 2) ^ k ≤ (t + t / Real.log 2) ^ k := by
        exact pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = (t * (1 + 1 / Real.log 2)) ^ k := by ring
      _ = C * t ^ k := by
        rw [mul_pow]
        ring
      _ ≤ Real.exp (ε * t) := hmain
  -- Eventually in `x`: `(1 + logb 2 x) ^ k ≤ x ^ ε`.
  have h_x : ∀ᶠ x : ℝ in atTop, (1 + Real.logb 2 x) ^ k ≤ x ^ ε := by
    filter_upwards [(Real.tendsto_log_atTop : Tendsto Real.log atTop atTop).eventually h_poly_exp,
      (eventually_gt_atTop (0 : ℝ))] with x ht hx0
    calc
      (1 + Real.logb 2 x) ^ k = (1 + Real.log x / Real.log 2) ^ k := by rw [Real.logb]
      _ ≤ Real.exp (ε * Real.log x) := ht
      _ = Real.exp (Real.log x * ε) := by rw [mul_comm]
      _ = x ^ ε := (Real.rpow_def_of_pos hx0 ε).symm
  -- `δ ↦ (δ : ℝ)` maps `𝓝[>] 0` in `ℝ≥0` to `𝓝[>] 0` in `ℝ`.
  have h_coe_nhds : Tendsto (fun δ : NNReal => (δ : ℝ)) (𝓝[>] (0 : NNReal)) (𝓝 (0 : ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h_coe : Tendsto (fun δ : NNReal => (δ : ℝ)) (𝓝[>] (0 : NNReal)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact h_coe_nhds
    · have hδ0 : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal), 0 < δ := by
        simpa [Set.Ioi] using
          (eventually_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : NNReal), δ ∈ Set.Ioi (0 : NNReal))
      filter_upwards [hδ0] with δ hδ
      exact_mod_cast hδ
  -- `δ ↦ 1 / (δ : ℝ)` maps `𝓝[>] 0` to `atTop`.
  have h_inv : Tendsto (fun δ : NNReal => (δ : ℝ)⁻¹) (𝓝[>] (0 : NNReal)) atTop := by
    exact (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).comp h_coe
  have h_lt_one : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal), (δ : ℝ) < 1 := by
    exact h_coe_nhds.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have h_pos : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal), 0 < (δ : ℝ) := by
    have hδ0 : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal), 0 < δ := by
      simpa [Set.Ioi] using
        (eventually_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : NNReal), δ ∈ Set.Ioi (0 : NNReal))
    filter_upwards [hδ0] with δ hδ
    exact_mod_cast hδ
  filter_upwards [h_inv.eventually h_x, h_lt_one, h_pos] with δ hδx hδlt hδpos
  have hx_gt_one : 1 < (δ : ℝ)⁻¹ := (one_lt_inv₀ hδpos).mpr hδlt
  have hbase_nonneg : 0 ≤ 1 + Real.logb 2 ((δ : ℝ)⁻¹) := by
    have hlogx : 0 < Real.log ((δ : ℝ)⁻¹) := Real.log_pos hx_gt_one
    have hlogb : 0 < Real.logb 2 ((δ : ℝ)⁻¹) := by
      dsimp [Real.logb]
      exact div_pos hlogx hlog2
    linarith
  have h_real : (1 + Real.logb 2 ((δ : ℝ)⁻¹)) ^ k ≤ (δ : ℝ) ^ (-ε) := by
    calc
      (1 + Real.logb 2 ((δ : ℝ)⁻¹)) ^ k ≤ ((δ : ℝ)⁻¹) ^ ε := hδx
      _ = (δ : ℝ) ^ (-ε) := (Real.rpow_neg_eq_inv_rpow (δ : ℝ) ε).symm
  calc
    ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : ℝ))) ^ k
        = ENNReal.ofReal (1 + Real.logb 2 ((δ : ℝ)⁻¹)) ^ k := by rw [one_div]
    _ = ENNReal.ofReal ((1 + Real.logb 2 ((δ : ℝ)⁻¹)) ^ k) := by
        rw [ENNReal.ofReal_pow hbase_nonneg]
    _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ε)) := ENNReal.ofReal_le_ofReal h_real
    _ = (δ : ENNReal) ^ (-ε) := by
        rw [← ENNReal.ofReal_coe_nnreal (p := δ), ENNReal.ofReal_rpow_of_pos hδpos]
/-- Transfer of a real bound `n * δ ^ 2 ≤ C` into the `ℝ≥0∞` form `n ≤ C * δ ^ (-2)`. -/
lemma natCast_le_coe_mul_rpow_neg_two {δ : NNReal} (hδ : 0 < δ) {n : ℕ} {C : NNReal}
    (h : (n : ℝ) * (δ : ℝ) ^ (2 : ℕ) ≤ (C : ℝ)) :
    (n : ENNReal) ≤ (C : ENNReal) * (δ : ENNReal) ^ (-2 : ℝ) := by
  have hδsq_ne_zero : ((δ ^ 2 : NNReal) : ENNReal) ≠ 0 := by
    simpa [ENNReal.coe_eq_zero] using pow_ne_zero 2 hδ.ne.symm
  have hδsq_ne_top : ((δ ^ 2 : NNReal) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h_mul_nnreal : (n : NNReal) * (δ ^ 2 : NNReal) ≤ C := by
    apply NNReal.coe_le_coe.mp
    calc
      ((n : NNReal) * (δ ^ 2 : NNReal) : ℝ) = (n : ℝ) * ((δ ^ 2 : NNReal) : ℝ) := by simp
      _ = (n : ℝ) * ((δ : ℝ) ^ (2 : ℕ)) := by simp
      _ ≤ (C : ℝ) := h
  have h_mul_ennreal : (n : ENNReal) * ((δ ^ 2 : NNReal) : ENNReal) ≤ (C : ENNReal) := by
    calc
      (n : ENNReal) * ((δ ^ 2 : NNReal) : ENNReal)
          = ((n : NNReal) * (δ ^ 2 : NNReal) : ENNReal) := by simp
      _ ≤ (C : ENNReal) := ENNReal.coe_le_coe.mpr h_mul_nnreal
  have h_div : (n : ENNReal) ≤ (C : ENNReal) / ((δ ^ 2 : NNReal) : ENNReal) :=
    (ENNReal.le_div_iff_mul_le (Or.inl hδsq_ne_zero) (Or.inl hδsq_ne_top)).mpr h_mul_ennreal
  calc
    (n : ENNReal) ≤ (C : ENNReal) / ((δ ^ 2 : NNReal) : ENNReal) := h_div
    _ = (C : ENNReal) * ((δ ^ 2 : NNReal) : ENNReal)⁻¹ := by rw [div_eq_mul_inv]
    _ = (C : ENNReal) * ((δ : ENNReal) ^ (2 : ℕ))⁻¹ := by simp
    _ = (C : ENNReal) * ((δ : ENNReal) ^ (2 : ℝ))⁻¹ := by simp
    _ = (C : ENNReal) * (δ : ENNReal) ^ (-(2 : ℝ)) := by simp [ENNReal.rpow_neg]
    _ = (C : ENNReal) * (δ : ENNReal) ^ (-2 : ℝ) := by simp

end ENNReal

namespace Kakeya

/-- Bridge: an ℝ-eventually statement near `0⁺` transports to NNReal. -/
lemma nnreal_eventually_of_real_eventually {p : ℝ → Prop}
    (h : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), p δ) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), p (δ : ℝ) := by
  have htendsto : Filter.Tendsto (fun δ : NNReal => (δ : ℝ))
      (𝓝[>] (0 : NNReal)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ((NNReal.continuous_coe).tendsto 0).mono_left nhdsWithin_le_nhds |>.congr
        (fun _ => rfl) |>.trans (by simp [NNReal.coe_zero])
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact_mod_cast hδ
  exact htendsto.eventually h

/-- For any positive constant `C` and exponent `η > 0`, eventually `C ≤ δ ^ (-η)`
as `δ → 0⁺`. -/
lemma absorb_const_le_rpow_neg {C η : ℝ} (hC : 0 < C) (hη : 0 < η) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), C ≤ δ ^ (-η) := by
  apply Filter.eventually_of_mem (Ioo_mem_nhdsGT (Real.rpow_pos_of_pos hC (-1 / η)))
  intro δ hδ; simp only [Set.mem_Ioo] at hδ
  calc C = (C ^ (-1 / η)) ^ (-η) := by
          rw [← Real.rpow_mul hC.le,
              show (-1 / η) * (-η) = 1 from by field_simp, Real.rpow_one]
    _ ≤ δ ^ (-η) := by
          rw [Real.rpow_neg (Real.rpow_pos_of_pos hC _).le, Real.rpow_neg hδ.1.le]
          exact inv_anti₀ (Real.rpow_pos_of_pos hδ.1 _)
            (Real.rpow_le_rpow hδ.1.le hδ.2.le hη.le)

/-- Eventually, a positive constant times a logarithm is bounded by a negative power:
`C * (M * log (1 / δ)) ≤ δ ^ (-(2 * η))` as `δ → 0⁺`. -/
lemma absorb_log_le_rpow_neg {C M η : ℝ}
    (hC : 0 < C) (hM : 0 < M) (hη : 0 < η) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), C * (M * Real.log (1 / δ)) ≤ δ ^ (-(2 * η)) := by
  filter_upwards [absorb_const_le_rpow_neg
      (show (0 : ℝ) < C * M / η by positivity) hη,
    self_mem_nhdsWithin] with δ hB_le (hδ_pos : 0 < δ)
  calc C * (M * Real.log (1 / δ))
      ≤ C * (M * (δ ^ (-η) / η)) := by
        have h1 := Real.log_le_rpow_div (show (0 : ℝ) ≤ 1 / δ by positivity) hη
        rw [show (1 / δ) ^ η = δ ^ (-η) from by
          rw [Real.rpow_neg hδ_pos.le, one_div, Real.inv_rpow hδ_pos.le]] at h1
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h1 hM.le) hC.le
    _ = (C * M / η) * δ ^ (-η) := by ring
    _ ≤ δ ^ (-η) * δ ^ (-η) :=
        mul_le_mul_of_nonneg_right hB_le (Real.rpow_nonneg hδ_pos.le _)
    _ = δ ^ (-(2 * η)) := by rw [← Real.rpow_add hδ_pos]; congr 1; ring

/-- Rewrite an `ENNReal` power of a positive `NNReal` as `ENNReal.ofReal`. -/
lemma ennreal_coe_nnreal_rpow {δ : NNReal} (hδ : 0 < (δ : ℝ)) (x : ℝ) :
    ((δ : ENNReal) ^ x : ENNReal) = ENNReal.ofReal ((δ : ℝ) ^ x) := by
  rw [show ((δ : ENNReal) : ENNReal) = ENNReal.ofReal (δ : ℝ) from
        ENNReal.ofReal_coe_nnreal.symm,
      ← ENNReal.ofReal_rpow_of_pos hδ]

/-- Rewrite the `toReal` of an `ENNReal` power of a positive `NNReal`. -/
lemma ennreal_coe_nnreal_rpow_toReal {δ : NNReal} (hδ : 0 < (δ : ℝ)) (x : ℝ) :
    (((δ : ENNReal) ^ x : ENNReal)).toReal = (δ : ℝ) ^ x := by
  rw [ennreal_coe_nnreal_rpow hδ, ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le _)]

/-- For any natural `M` and `α > 0`, eventually `(M : ℝ) ≤ δ ^ (-α)` as `δ → 0⁺`. -/
lemma cast_eventually_le_rpow_neg (M : ℕ) (α : ℝ) (hα : 0 < α) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), (M : ℝ) ≤ δ ^ (-α) := by
  by_cases hM : M = 0
  · refine Filter.eventually_of_mem self_mem_nhdsWithin (fun δ (hδ : 0 < δ) => ?_)
    simp [hM, Real.rpow_nonneg hδ.le]
  · exact absorb_const_le_rpow_neg (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM)) hα

/-- For `x ∈ (0,1]` and `C ≥ 1`: `exp(-C · log(1/x)) ≤ x`, i.e. `x^C ≤ x`. -/
lemma exp_neg_mul_log_inv_le_self
    {x C : ℝ} (hx_pos : 0 < x) (hx_le_one : x ≤ 1) (hC_ge_one : 1 ≤ C) :
    Real.exp (-C * Real.log (1 / x)) ≤ x := by
  have hlog_inv_eq : Real.log (1 / x) = -Real.log x := by
    rw [Real.log_div one_ne_zero (ne_of_gt hx_pos), Real.log_one, zero_sub]
  rw [hlog_inv_eq]
  ring_nf
  have hexp_eq : Real.exp (C * Real.log x) = x ^ C := by
    rw [← Real.exp_log hx_pos, ← Real.exp_mul, Real.exp_log hx_pos, mul_comm,
        ← Real.rpow_def_of_pos hx_pos]
  rw [hexp_eq]
  calc x ^ C ≤ x ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hx_pos hx_le_one hC_ge_one
    _ = x := Real.rpow_one _

/-- For `δ ∈ (0,1]`, `ε > 0`, and `M ≥ 0`: `M · (-log δ) ≤ (M/ε) · δ^(-ε)`.
Derived from the elementary `1 + y ≤ exp y` applied at `y = -ε · log δ ≥ 0`. -/
lemma neglog_le_rpow_div
    {δ ε M : ℝ} (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hε_pos : 0 < ε) (hM_nn : 0 ≤ M) :
    M * (-Real.log δ) ≤ M / ε * δ ^ (-ε) := by
  have h_neg_log : 0 ≤ -Real.log δ := by
    rw [neg_nonneg]; exact Real.log_nonpos hδ_pos.le hδ_le_one
  have hrpow_eq : δ ^ (-ε) = Real.exp (-ε * Real.log δ) := by
    rw [Real.rpow_def_of_pos hδ_pos]; congr 1; ring
  have h_ε_log : ε * (-Real.log δ) ≤ δ ^ (-ε) := by
    rw [hrpow_eq]
    have h_exp_ge : -ε * Real.log δ + 1 ≤ Real.exp (-ε * Real.log δ) :=
      Real.add_one_le_exp _
    nlinarith [h_exp_ge, mul_nonneg hε_pos.le h_neg_log]
  have h_neglog_le : -Real.log δ ≤ δ ^ (-ε) / ε := by
    rw [le_div_iff₀ hε_pos]; linarith
  calc M * (-Real.log δ)
      ≤ M * (δ ^ (-ε) / ε) := mul_le_mul_of_nonneg_left h_neglog_le hM_nn
    _ = M / ε * δ ^ (-ε) := by ring

/-- From `1 ≤ x`, `0 ≤ y`, `0 ≤ c` and `c · (x + y) ≤ A`, conclude `c ≤ A`.
Stated separately so that `linarith` never has to look inside `c`. -/
lemma le_of_mul_add_le_of_one_le
    (c A : ℝ) (hc_nn : 0 ≤ c)
    {x y : ℝ} (hx_ge_one : 1 ≤ x) (hy_nn : 0 ≤ y)
    (h_A : c * (x + y) ≤ A) :
    c ≤ A := by
  have hsum_ge_one : (1 : ℝ) ≤ x + y := by linarith
  have hmul : c * 1 ≤ c * (x + y) :=
    mul_le_mul_of_nonneg_left hsum_ge_one hc_nn
  linarith

end Kakeya
