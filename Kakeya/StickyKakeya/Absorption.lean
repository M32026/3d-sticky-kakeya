/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Sticky
public import Kakeya.StickyKakeya.Constants
public import Kakeya.StickyKakeya.Counting

/-!
# Theorem 7.3(A) ⇒ (B): absorbing the losses

The arithmetic that shows every loss the deduction accumulates — polylog factors, the bundling
loss, the shade-refinement loss `Kpoly`, the fixed constants — is subpolynomial, hence absorbed by
a positive power of `1/δ` once `δ` is small enough.  These are the `∀ᶠ δ` thresholds that the
main theorem instantiates.
-/

@[expose] public section

open MeasureTheory
open Tube

namespace Kakeya

open MultiScaleFac

namespace StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

section stickyKatzTaoOfStickyFrostman

/-- **Polylog is subpolynomial.**  For any `c ≥ 0`, `k`, and `ε' > 0`, eventually
`(c·log x + 1)^k ≤ x^ε'`.  This is the analytic core of E2: the `s↔s₂` cardinality
loss `(log₂|s|)^(M-1)` is absorbed by `δ^(-ε')` for `δ` small. -/
private lemma poly_log_le_rpow (c : ℝ) (k : ℕ) (ε' : ℝ) (hc : 0 ≤ c) (hε' : 0 < ε') :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → (c * Real.log x + 1) ^ k ≤ x ^ ε' := by
  set η : ℝ := ε' / (2 * ((k : ℝ) + 1)) with hη_def
  have hη_pos : 0 < η := by rw [hη_def]; positivity
  have hηk : (k : ℝ) * η ≤ ε' / 2 := by
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [hη_def]
    have hrw : (k : ℝ) * (ε' / (2 * ((k : ℝ) + 1))) = (ε' / 2) * ((k : ℝ) / ((k : ℝ) + 1)) := by
      field_simp
    rw [hrw]
    have hfrac : (k : ℝ) / ((k : ℝ) + 1) ≤ 1 := by rw [div_le_one hk1]; linarith
    calc (ε' / 2) * ((k : ℝ) / ((k : ℝ) + 1))
        ≤ (ε' / 2) * 1 := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = ε' / 2 := mul_one _
  have hlog : ∀ x : ℝ, 1 ≤ x → Real.log x ≤ x ^ η / η := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le one_pos hx
    have h1 : η * Real.log x = Real.log (x ^ η) := (Real.log_rpow hxpos η).symm
    have h2 : Real.log (x ^ η) ≤ x ^ η - 1 :=
      Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hxpos η)
    rw [le_div_iff₀ hη_pos, mul_comm, h1]; linarith
  set B : ℝ := c / η + 1 with hB_def
  have hB_pos : 0 < B := by rw [hB_def]; positivity
  refine ⟨max 1 (B ^ (2 * (k : ℝ) / ε')), le_max_left _ _, ?_⟩
  intro x hx
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx1
  have hxη_ge1 : 1 ≤ x ^ η := Real.one_le_rpow hx1 hη_pos.le
  have hstep1 : c * Real.log x + 1 ≤ B * x ^ η := by
    have hl : c * Real.log x ≤ c * (x ^ η / η) :=
      mul_le_mul_of_nonneg_left (hlog x hx1) hc
    have heq : c * (x ^ η / η) = (c / η) * x ^ η := by field_simp
    rw [heq] at hl
    calc c * Real.log x + 1 ≤ (c / η) * x ^ η + 1 := by linarith
      _ ≤ (c / η) * x ^ η + x ^ η := by linarith [hxη_ge1]
      _ = B * x ^ η := by rw [hB_def]; ring
  have hLHS_nn : 0 ≤ c * Real.log x + 1 := by
    have : 0 ≤ Real.log x := Real.log_nonneg hx1
    positivity
  have hpow : (c * Real.log x + 1) ^ k ≤ (B * x ^ η) ^ k :=
    pow_le_pow_left₀ hLHS_nn hstep1 k
  have hrpow_k : (x ^ η) ^ k = x ^ ((k : ℝ) * η) := by
    rw [← Real.rpow_natCast (x ^ η) k, ← Real.rpow_mul hxpos.le, mul_comm]
  have hBxk : (B * x ^ η) ^ k = B ^ k * x ^ ((k : ℝ) * η) := by rw [mul_pow, hrpow_k]
  rw [hBxk] at hpow
  have hxmono : x ^ ((k : ℝ) * η) ≤ x ^ (ε' / 2) :=
    Real.rpow_le_rpow_of_exponent_le hx1 hηk
  have hstep2 : (c * Real.log x + 1) ^ k ≤ B ^ k * x ^ (ε' / 2) :=
    le_trans hpow (mul_le_mul_of_nonneg_left hxmono (pow_pos hB_pos k).le)
  have hBk_le : B ^ k ≤ x ^ (ε' / 2) := by
    have hx0 : B ^ (2 * (k : ℝ) / ε') ≤ x := le_trans (le_max_right _ _) hx
    have hmono : (B ^ (2 * (k : ℝ) / ε')) ^ (ε' / 2) ≤ x ^ (ε' / 2) :=
      Real.rpow_le_rpow (by positivity) hx0 (by positivity)
    have heq : (B ^ (2 * (k : ℝ) / ε')) ^ (ε' / 2) = B ^ k := by
      rw [← Real.rpow_natCast B k, ← Real.rpow_mul hB_pos.le]
      congr 1
      field_simp
    rwa [heq] at hmono
  calc (c * Real.log x + 1) ^ k ≤ B ^ k * x ^ (ε' / 2) := hstep2
    _ ≤ x ^ (ε' / 2) * x ^ (ε' / 2) :=
        mul_le_mul_of_nonneg_right hBk_le (Real.rpow_nonneg hxpos.le _)
    _ = x ^ ε' := by rw [← Real.rpow_add hxpos]; ring_nf

/-- **Poly-log absorption for E2.**  The E2 bound carries a `Cdim·(⌊log₂|s|⌋+1)^k` factor.
Although `|s|` is δ-independent, a Katz–Tao cardinality bound `|s| ≤ δ^(-B)·C` forces
`log₂|s| ≲ log(1/δ)`, so the polylog is polynomial in `log(1/δ)`; `poly_log_le_rpow` then
dominates it (and the dimensional `Cdim`) by `δ^(-ζ)` for any `ζ > 0`, once `δ` is small. -/
private lemma e2_polylog_absorb (Cdim B C ζ : ℝ) (k : ℕ)
    (hCdim : 0 ≤ Cdim) (hB : 0 ≤ B) (hC : 0 < C) (hζ : 0 < ζ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : NNReal, 0 < δ → (δ : ℝ) ≤ δ₀ →
      ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ (δ : ℝ) ^ (-B) * C →
        Cdim * ((⌊Real.logb 2 (N : ℝ)⌋₊ : ℝ) + 1) ^ k ≤ (δ : ℝ) ^ (-ζ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := B / Real.log 2 + |Real.log C / Real.log 2| + 1 with hc_def
  have hc_nn : 0 ≤ c :=
    add_nonneg (add_nonneg (div_nonneg hB hlog2.le) (abs_nonneg _)) zero_le_one
  obtain ⟨x₀, hx₀_ge1, hx₀_bound⟩ := poly_log_le_rpow c k (ζ / 2) hc_nn (by positivity)
  have hx₀_pos : 0 < x₀ := lt_of_lt_of_le one_pos hx₀_ge1
  set Cm : ℝ := max Cdim 1 with hCm_def
  have hCm_ge1 : 1 ≤ Cm := le_max_right _ _
  have hCm_pos : 0 < Cm := lt_of_lt_of_le one_pos hCm_ge1
  have hCm_rpow_pos : 0 < Cm ^ (2 / ζ) := Real.rpow_pos_of_pos hCm_pos _
  refine ⟨min (min (1 / x₀) (Real.exp (-1))) (Cm ^ (-(2 / ζ))), ?_, ?_⟩
  · exact lt_min (lt_min (by positivity) (Real.exp_pos _)) (Real.rpow_pos_of_pos hCm_pos _)
  intro δ hδ_pos hδ_le N hN hN_bound
  have hδ_pos_real : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
  have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hN_ge1
  set x : ℝ := 1 / (δ : ℝ) with hx_def
  have hx_pos : 0 < x := by rw [hx_def]; positivity
  have hδ_le_x0 : (δ : ℝ) ≤ 1 / x₀ :=
    le_trans hδ_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ_le_em1 : (δ : ℝ) ≤ Real.exp (-1) :=
    le_trans hδ_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδ_le_Cm : (δ : ℝ) ≤ Cm ^ (-(2 / ζ)) := le_trans hδ_le (min_le_right _ _)
  have hx_ge_x0 : x₀ ≤ x := by
    rw [hx_def, le_div_iff₀ hδ_pos_real]
    have h := mul_le_mul_of_nonneg_right hδ_le_x0 hx₀_pos.le
    rw [one_div, inv_mul_cancel₀ hx₀_pos.ne'] at h
    linarith [h]
  have hlogx_eq : Real.log x = -Real.log (δ : ℝ) := by
    rw [hx_def, Real.log_div one_ne_zero hδ_pos_real.ne', Real.log_one, zero_sub]
  have hlogδ_le : Real.log (δ : ℝ) ≤ -1 := by
    have h := Real.log_le_log hδ_pos_real hδ_le_em1
    rwa [Real.log_exp] at h
  have hlogx_ge1 : 1 ≤ Real.log x := by rw [hlogx_eq]; linarith
  have h3 : Real.log (N : ℝ) ≤ B * Real.log x + Real.log C := by
    have hle : Real.log (N : ℝ) ≤ Real.log ((δ : ℝ) ^ (-B) * C) :=
      Real.log_le_log hN_pos hN_bound
    rw [Real.log_mul (by positivity) hC.ne', Real.log_rpow hδ_pos_real] at hle
    rw [hlogx_eq]; linarith [hle]
  have hlogbN_le : Real.logb 2 (N : ℝ) ≤ c * Real.log x := by
    rw [Real.logb]
    have hdiv : Real.log (N : ℝ) / Real.log 2
        ≤ (B * Real.log x + Real.log C) / Real.log 2 := by gcongr
    refine le_trans hdiv ?_
    rw [add_div, hc_def]
    have habs : Real.log C / Real.log 2 ≤ |Real.log C / Real.log 2| := le_abs_self _
    have hmul : |Real.log C / Real.log 2|
        ≤ |Real.log C / Real.log 2| * Real.log x :=
      le_mul_of_one_le_right (abs_nonneg _) hlogx_ge1
    have hBrw : B * Real.log x / Real.log 2 = B / Real.log 2 * Real.log x := by ring
    rw [hBrw]; nlinarith [habs, hmul, hlogx_ge1]
  have hbase_le : (⌊Real.logb 2 (N : ℝ)⌋₊ : ℝ) + 1 ≤ c * Real.log x + 1 := by
    have h1 : (⌊Real.logb 2 (N : ℝ)⌋₊ : ℝ) ≤ Real.logb 2 (N : ℝ) :=
      Nat.floor_le (Real.logb_nonneg (by norm_num) hN_ge1)
    linarith [hlogbN_le, h1]
  have hpow : ((⌊Real.logb 2 (N : ℝ)⌋₊ : ℝ) + 1) ^ k ≤ x ^ (ζ / 2) := by
    have hb_nn : 0 ≤ (⌊Real.logb 2 (N : ℝ)⌋₊ : ℝ) + 1 := by positivity
    exact le_trans (pow_le_pow_left₀ hb_nn hbase_le k) (hx₀_bound x hx_ge_x0)
  have hx_ge_Cm : Cm ^ (2 / ζ) ≤ x := by
    rw [Real.rpow_neg hCm_pos.le] at hδ_le_Cm
    rw [hx_def, le_div_iff₀ hδ_pos_real]
    have h := mul_le_mul_of_nonneg_left hδ_le_Cm hCm_rpow_pos.le
    rwa [mul_inv_cancel₀ hCm_rpow_pos.ne'] at h
  have hCm_eq : (Cm ^ (2 / ζ)) ^ (ζ / 2) = Cm := by
    rw [← Real.rpow_mul hCm_pos.le, show 2 / ζ * (ζ / 2) = 1 by field_simp, Real.rpow_one]
  have hCdim_abs : Cdim ≤ x ^ (ζ / 2) :=
    calc Cdim ≤ Cm := le_max_left _ _
      _ = (Cm ^ (2 / ζ)) ^ (ζ / 2) := hCm_eq.symm
      _ ≤ x ^ (ζ / 2) := Real.rpow_le_rpow hCm_rpow_pos.le hx_ge_Cm (by positivity)
  have hδpow_eq : (δ : ℝ) ^ (-ζ) = x ^ ζ := by
    rw [hx_def, one_div, Real.inv_rpow hδ_pos_real.le, Real.rpow_neg hδ_pos_real.le]
  rw [hδpow_eq]
  calc Cdim * ((⌊Real.logb 2 (N : ℝ)⌋₊ : ℝ) + 1) ^ k
      ≤ Cdim * x ^ (ζ / 2) := mul_le_mul_of_nonneg_left hpow hCdim
    _ ≤ x ^ (ζ / 2) * x ^ (ζ / 2) :=
        mul_le_mul_of_nonneg_right hCdim_abs (Real.rpow_nonneg hx_pos.le _)
    _ = x ^ ζ := by rw [← Real.rpow_add hx_pos]; ring_nf

/-- Reads a cardinality bound off the E2 product bracket.  The bracket bounds `m · Cv · δ^{n₁}` by
the E2 quantity `D`, and the absorption hypothesis bounds `D` by `δ^{ε_A - ε}`; one further power of
`δ` pays for `Cv⁻¹` (this is the only role of `δ ≤ Cv`).  Purely real arithmetic, and the shape in
which `assembly_helper` needs the cardinality of the translated family. -/
lemma card_le_of_prod_bracket {δ : NNReal} (hδ_pos : 0 < δ)
    (D Cv n₁ ε ε_A m : ℝ) (hCv_pos : 0 < Cv) (hδ_le_Cv : (δ : ℝ) ≤ Cv)
    (_hm_nonneg : 0 ≤ m)
    (hUB : m * Cv * (δ : ℝ) ^ n₁ ≤ D)
    (habs : (δ : ℝ) ^ (-ε_A) * D ≤ (δ : ℝ) ^ (-ε)) :
    m ≤ (δ : ℝ) ^ (-(n₁ + 1 + ε - ε_A)) := by
  have hx_pos : 0 < (δ : ℝ) := by exact_mod_cast hδ_pos
  have hx_nonneg : 0 ≤ (δ : ℝ) := le_of_lt hx_pos
  have h1 : m * ((δ : ℝ) ^ (-ε_A) * Cv * (δ : ℝ) ^ n₁) ≤ (δ : ℝ) ^ (-ε) := by
    calc
      m * ((δ : ℝ) ^ (-ε_A) * Cv * (δ : ℝ) ^ n₁)
          = (δ : ℝ) ^ (-ε_A) * (m * Cv * (δ : ℝ) ^ n₁) := by ring
      _ ≤ (δ : ℝ) ^ (-ε_A) * D := by
        exact mul_le_mul_of_nonneg_left hUB (Real.rpow_nonneg hx_nonneg (-ε_A))
      _ ≤ (δ : ℝ) ^ (-ε) := habs
  have hrec : (Cv : ℝ)⁻¹ ≤ (δ : ℝ)⁻¹ := (inv_le_inv₀ hCv_pos hx_pos).2 hδ_le_Cv
  have hle : m ≤ (δ : ℝ) ^ (-ε) * (δ : ℝ) ^ ε_A * (δ : ℝ) ^ (-n₁) * (Cv : ℝ)⁻¹ := by
    have hd_pos : 0 < (δ : ℝ) ^ (-ε_A) * Cv * (δ : ℝ) ^ n₁ := by positivity
    have hstep : m ≤ (δ : ℝ) ^ (-ε) / ((δ : ℝ) ^ (-ε_A) * Cv * (δ : ℝ) ^ n₁) := by
      exact (le_div_iff₀ hd_pos).2 h1
    calc
      m ≤ (δ : ℝ) ^ (-ε) / ((δ : ℝ) ^ (-ε_A) * Cv * (δ : ℝ) ^ n₁) := hstep
      _ = (δ : ℝ) ^ (-ε) * (δ : ℝ) ^ ε_A * (δ : ℝ) ^ (-n₁) * (Cv : ℝ)⁻¹ := by
        rw [div_eq_mul_inv]
        rw [mul_inv, mul_inv]
        rw [← Real.rpow_neg hx_nonneg (-ε_A)]
        rw [← Real.rpow_neg hx_nonneg n₁]
        ring_nf
  calc
    m ≤ (δ : ℝ) ^ (-ε) * (δ : ℝ) ^ ε_A * (δ : ℝ) ^ (-n₁) * (Cv : ℝ)⁻¹ := hle
    _ ≤ (δ : ℝ) ^ (-ε) * (δ : ℝ) ^ ε_A * (δ : ℝ) ^ (-n₁) * (δ : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_left hrec (by positivity)
    _ = (δ : ℝ) ^ (-ε) * (δ : ℝ) ^ ε_A * (δ : ℝ) ^ (-n₁) * (δ : ℝ) ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_neg_one]
    _ = (δ : ℝ) ^ (-(n₁ + 1 + ε - ε_A)) := by
      rw [← Real.rpow_add hx_pos, ← Real.rpow_add hx_pos, ← Real.rpow_add hx_pos]
      congr 1
      ring

/-- **E6 loglog≪log threshold**: for `A, B ≥ 1`, `δ^η₁·A·B^⌈loglog(1/δ)⌉ ≤ 1` for all small `δ`.
Key step: `B^(loglog(1/δ)) = (log(1/δ))^(log B)` turns the `B^⌈loglog⌉` factor into a polylog in
`1/δ`, which (with the constant `A·B`) `poly_log_le_rpow` absorbs into `δ^(-η₁)`.  Discharges the
threshold hypothesis of `exists_frostman_translation_family` (the E6 `h_disc` `hthr`). -/
private lemma e6_threshold_le (η₁ : ℝ) (hη₁ : 0 < η₁) (A B : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : NNReal, 0 < δ → (δ : ℝ) ≤ δ₀ →
      (δ : ℝ) ^ η₁ * A * B ^ (⌈Real.log (Real.log (1 / (δ : ℝ)))⌉₊) ≤ 1 := by
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA
  have hB0 : 0 < B := lt_of_lt_of_le one_pos hB
  set k : ℕ := ⌈Real.log B⌉₊ with hk_def
  obtain ⟨x₀, hx₀_ge1, hx₀_bound⟩ := poly_log_le_rpow 1 k (η₁ / 2) (by norm_num) (by positivity)
  have hx₀_pos : 0 < x₀ := lt_of_lt_of_le one_pos hx₀_ge1
  set Cm : ℝ := max (A * B) 1 with hCm_def
  have hCm_ge1 : 1 ≤ Cm := le_max_right _ _
  have hCm_pos : 0 < Cm := lt_of_lt_of_le one_pos hCm_ge1
  have hCm_rpow_pos : 0 < Cm ^ (2 / η₁) := Real.rpow_pos_of_pos hCm_pos _
  refine ⟨min (min (1 / x₀) (Real.exp (-1))) (Cm ^ (-(2 / η₁))), ?_, ?_⟩
  · exact lt_min (lt_min (by positivity) (Real.exp_pos _)) (Real.rpow_pos_of_pos hCm_pos _)
  intro δ hδ_pos hδ_le
  have hδ_pos_real : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
  set x : ℝ := 1 / (δ : ℝ) with hx_def
  have hx_pos : 0 < x := by rw [hx_def]; positivity
  have hδ_le_x0 : (δ : ℝ) ≤ 1 / x₀ :=
    le_trans hδ_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ_le_em1 : (δ : ℝ) ≤ Real.exp (-1) :=
    le_trans hδ_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδ_le_Cm : (δ : ℝ) ≤ Cm ^ (-(2 / η₁)) := le_trans hδ_le (min_le_right _ _)
  have hx_ge_x0 : x₀ ≤ x := by
    rw [hx_def, le_div_iff₀ hδ_pos_real]
    have h := mul_le_mul_of_nonneg_right hδ_le_x0 hx₀_pos.le
    rw [one_div, inv_mul_cancel₀ hx₀_pos.ne'] at h
    linarith [h]
  have hlogx_eq : Real.log x = -Real.log (δ : ℝ) := by
    rw [hx_def, Real.log_div one_ne_zero hδ_pos_real.ne', Real.log_one, zero_sub]
  have hlogδ_le : Real.log (δ : ℝ) ≤ -1 := by
    have h := Real.log_le_log hδ_pos_real hδ_le_em1
    rwa [Real.log_exp] at h
  have hL_ge1 : 1 ≤ Real.log x := by rw [hlogx_eq]; linarith
  set L : ℝ := Real.log x with hL_def
  have hL_pos : 0 < L := lt_of_lt_of_le one_pos hL_ge1
  have hlogL_nn : 0 ≤ Real.log L := Real.log_nonneg hL_ge1
  have hMout_le : ((⌈Real.log L⌉₊ : ℝ)) ≤ Real.log L + 1 := (Nat.ceil_lt_add_one hlogL_nn).le
  have hBident : B ^ (Real.log L) = L ^ (Real.log B) := by
    rw [Real.rpow_def_of_pos hB0, Real.rpow_def_of_pos hL_pos]; congr 1; ring
  have hBMout : B ^ (⌈Real.log L⌉₊) ≤ B * L ^ (Real.log B) := by
    rw [← Real.rpow_natCast B (⌈Real.log L⌉₊)]
    calc B ^ ((⌈Real.log L⌉₊ : ℝ))
        ≤ B ^ (Real.log L + 1) := Real.rpow_le_rpow_of_exponent_le hB hMout_le
      _ = B ^ (Real.log L) * B ^ (1 : ℝ) := Real.rpow_add hB0 _ _
      _ = B * L ^ (Real.log B) := by rw [hBident, Real.rpow_one, mul_comm]
  have hLk : L ^ (Real.log B) ≤ (L + 1) ^ k := by
    rw [← Real.rpow_natCast (L + 1) k]
    calc L ^ (Real.log B)
        ≤ (L + 1) ^ (Real.log B) :=
          Real.rpow_le_rpow hL_pos.le (by linarith) (Real.log_nonneg hB)
      _ ≤ (L + 1) ^ ((k : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil _)
  have hpoly : (L + 1) ^ k ≤ x ^ (η₁ / 2) := by
    have h := hx₀_bound x hx_ge_x0
    rw [← hL_def] at h
    simpa [one_mul] using h
  have hx_ge_Cm : Cm ^ (2 / η₁) ≤ x := by
    rw [Real.rpow_neg hCm_pos.le] at hδ_le_Cm
    rw [hx_def, le_div_iff₀ hδ_pos_real]
    have h := mul_le_mul_of_nonneg_left hδ_le_Cm hCm_rpow_pos.le
    rwa [mul_inv_cancel₀ hCm_rpow_pos.ne'] at h
  have hCm_eq : (Cm ^ (2 / η₁)) ^ (η₁ / 2) = Cm := by
    rw [← Real.rpow_mul hCm_pos.le, show 2 / η₁ * (η₁ / 2) = 1 by field_simp, Real.rpow_one]
  have hCm_abs : Cm ≤ x ^ (η₁ / 2) :=
    calc Cm = (Cm ^ (2 / η₁)) ^ (η₁ / 2) := hCm_eq.symm
      _ ≤ x ^ (η₁ / 2) := Real.rpow_le_rpow hCm_rpow_pos.le hx_ge_Cm (by positivity)
  have hmain : A * B ^ (⌈Real.log L⌉₊) ≤ x ^ η₁ := by
    calc A * B ^ (⌈Real.log L⌉₊)
        ≤ A * (B * L ^ (Real.log B)) := mul_le_mul_of_nonneg_left hBMout hA0.le
      _ = (A * B) * L ^ (Real.log B) := by ring
      _ ≤ Cm * (L + 1) ^ k :=
          mul_le_mul (le_max_left _ _) hLk (Real.rpow_nonneg hL_pos.le _) hCm_pos.le
      _ ≤ x ^ (η₁ / 2) * x ^ (η₁ / 2) :=
          mul_le_mul hCm_abs hpoly (by positivity) (Real.rpow_nonneg hx_pos.le _)
      _ = x ^ η₁ := by rw [← Real.rpow_add hx_pos]; ring_nf
  have hxη : (δ : ℝ) ^ η₁ * x ^ η₁ = 1 := by
    rw [hx_def, ← Real.mul_rpow hδ_pos_real.le (by positivity), mul_one_div,
      div_self hδ_pos_real.ne', Real.one_rpow]
  calc (δ : ℝ) ^ η₁ * A * B ^ (⌈Real.log L⌉₊)
      = (δ : ℝ) ^ η₁ * (A * B ^ (⌈Real.log L⌉₊)) := by ring
    _ ≤ (δ : ℝ) ^ η₁ * x ^ η₁ := mul_le_mul_of_nonneg_left hmain (Real.rpow_nonneg hδ_pos_real.le _)
    _ = 1 := hxη

omit [MeasurableSpace E] [BorelSpace E] in
/-- **All three E6 thresholds at once**, at the slack exponent `β = sfBeta η₁`: the `h_disc`
loglog≪log threshold, the `h_ratio` budget `δ^(β/2) ≤ Kic²/Cuni^(2(n-1))`, and `(n-1)/Mout ≤ β/4`.
Bundled into a single existential so that the main theorem's context grows by three hypotheses
instead of a dozen. -/
lemma e6_thresholds (η₁ : ℝ) (hη₁ : 0 < η₁) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : NNReal, 0 < δ → (δ : ℝ) ≤ δ₀ →
      ((δ : ℝ) ^ (sfBeta (E := E) η₁)
          * ((2 * (Tube.overlapConstBO (Module.finrank ℝ E) : NNReal)) : ℝ) ^ 3
          * (2 * ((2 * (Tube.overlapConstBO (Module.finrank ℝ E) : NNReal)) : ℝ) ^ 3)
              ^ (⌈Real.log (Real.log (1 / (δ : ℝ)))⌉₊) ≤ 1)
        ∧ ((δ : ℝ) ^ (sfBeta (E := E) η₁ / 2)
            ≤ ((Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
                  / (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)) ^ 2
                / ((2 * (Tube.overlapConstBO (Module.finrank ℝ E) : NNReal)) : ℝ)
                    ^ (2 * (Module.finrank ℝ E - 1)))
        ∧ (((Module.finrank ℝ E : ℝ) - 1)
              / ((⌈Real.log (Real.log (1 / (δ : ℝ)))⌉₊ : ℕ) : ℝ)
            ≤ sfBeta (E := E) η₁ / 4) := by
  have hβ_pos : 0 < sfBeta (E := E) η₁ := sfBeta_pos (E := E) η₁ hη₁
  set Cuni := ((2 * (Tube.overlapConstBO (Module.finrank ℝ E) : NNReal)) : ℝ) with hCuni_def
  have hCu1 : (1 : ℝ) ≤ Cuni := by
    have hx : (1 : NNReal) ≤ (Tube.overlapConstBO (Module.finrank ℝ E) : NNReal) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by simp [Tube.overlapConstBO])
    have hx' : (1 : ℝ) ≤ ((Tube.overlapConstBO (Module.finrank ℝ E) : NNReal) : ℝ) := by
      exact_mod_cast hx
    dsimp [Cuni]
    nlinarith
  have hCu3 : (1 : ℝ) ≤ Cuni ^ 3 := one_le_pow₀ hCu1
  have hB : (1 : ℝ) ≤ 2 * Cuni ^ 3 := by
    nlinarith
  obtain ⟨δ₀₁, hδ₀₁_pos, hδ₀₁_spec⟩ :=
    e6_threshold_le (sfBeta (E := E) η₁) hβ_pos
      (A := (((2 * (Tube.overlapConstBO (Module.finrank ℝ E) : NNReal)) : ℝ) ^ 3))
      (B := 2 * (((2 * (Tube.overlapConstBO (Module.finrank ℝ E) : NNReal)) : ℝ) ^ 3)) hCu3 hB
  set Kic := ((Tube.le_volume.c (Module.finrank ℝ E) : ℝ) /
    (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)) with hKic_def
  have hKic_pos : 0 < Kic := by
    have hlc_pos : 0 < (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) := by
      exact_mod_cast Tube.le_volume.c_pos (Module.finrank ℝ E)
    have hvc_pos : 0 < (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) := by
      unfold Tube.volume_le.C; positivity
    dsimp [Kic]
    positivity
  have hCuni_pos : 0 < Cuni := by
    have hx : (0 : ℝ) < ((Tube.overlapConstBO (Module.finrank ℝ E) : NNReal) : ℝ) := by
      have hpos : 1 ≤ Tube.overlapConstBO (Module.finrank ℝ E) :=
        Nat.one_le_iff_ne_zero.mpr (by simp [Tube.overlapConstBO])
      have hpos' : 0 < Tube.overlapConstBO (Module.finrank ℝ E) :=
        Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hpos)
      exact_mod_cast hpos'
    positivity
  have hc_pos : 0 < Kic ^ 2 / Cuni ^ (2 * (Module.finrank ℝ E - 1)) := by
    positivity
  obtain ⟨δ₀₂, hδ₀₂_pos, hδ₀₂_spec⟩ :=
    rpow_le_const_eventually (sfBeta (E := E) η₁ / 2)
      (Kic ^ 2 / Cuni ^ (2 * (Module.finrank ℝ E - 1)))
      (by nlinarith) hc_pos
  obtain ⟨δ₀₃, hδ₀₃_pos, hδ₀₃_spec⟩ :=
    loglog_div_le_eventually ((Module.finrank ℝ E : ℝ) - 1) (sfBeta (E := E) η₁ / 4) (by nlinarith)
  refine ⟨min δ₀₁ (min δ₀₂ δ₀₃), lt_min hδ₀₁_pos (lt_min hδ₀₂_pos hδ₀₃_pos), ?_⟩
  intro δ hδ_pos hδ_le
  have hδ_le₁ : (δ : ℝ) ≤ δ₀₁ := hδ_le.trans (min_le_left _ _)
  have hδ_le₂ : (δ : ℝ) ≤ δ₀₂ := hδ_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ_le₃ : (δ : ℝ) ≤ δ₀₃ := hδ_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h1 : (δ : ℝ) ^ (sfBeta (E := E) η₁) *
    (((2 * (Tube.overlapConstBO (Module.finrank ℝ E) : NNReal)) : ℝ) ^ 3)
      * (2 * (((2 * (Tube.overlapConstBO (Module.finrank ℝ E) : NNReal)) : ℝ) ^ 3))
          ^ (⌈Real.log (Real.log (1 / (δ : ℝ)))⌉₊) ≤ 1 :=
    hδ₀₁_spec δ hδ_pos hδ_le₁
  have h2 : (δ : ℝ) ^ (sfBeta (E := E) η₁ / 2) ≤ Kic ^ 2 / Cuni ^ (2 * (Module.finrank ℝ E - 1)) :=
    hδ₀₂_spec δ hδ_pos hδ_le₂
  have h3 : ((Module.finrank ℝ E : ℝ) - 1) / ((⌈Real.log (Real.log (1 / (δ : ℝ)))⌉₊ : ℕ) : ℝ) ≤
    sfBeta (E := E) η₁ / 4 :=
    hδ₀₃_spec δ hδ_pos hδ_le₃
  exact ⟨h1, h2, h3⟩

/-- Assembles the E2 absorption inequality `δ^(-εA)·(δ^(-ηKT)·Cdim·Pl) ≤ δ^(-ε)` from the
poly-log absorption `Cdim·Pl ≤ δ^(-ζ)`, where `εA + ηKT + ζ = ε`. -/
private lemma e2_habsorb {δ : NNReal} (hδ_pos : 0 < δ)
    (εA ηKT Cdim Pl ζ ε : ℝ) (hCdimPl : Cdim * Pl ≤ (δ : ℝ) ^ (-ζ))
    (hsum : εA + ηKT + ζ = ε) :
    (δ : ℝ) ^ (-εA) * ((δ : ℝ) ^ (-ηKT) * Cdim * Pl) ≤ (δ : ℝ) ^ (-ε) := by
  have hδr : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
  have hpos : (0 : ℝ) ≤ (δ : ℝ) ^ (-εA) * (δ : ℝ) ^ (-ηKT) := by positivity
  calc (δ : ℝ) ^ (-εA) * ((δ : ℝ) ^ (-ηKT) * Cdim * Pl)
      = (δ : ℝ) ^ (-εA) * (δ : ℝ) ^ (-ηKT) * (Cdim * Pl) := by ring
    _ ≤ (δ : ℝ) ^ (-εA) * (δ : ℝ) ^ (-ηKT) * (δ : ℝ) ^ (-ζ) :=
        mul_le_mul_of_nonneg_left hCdimPl hpos
    _ = (δ : ℝ) ^ (-ε) := by
        rw [← Real.rpow_add hδr, ← Real.rpow_add hδr]
        congr 1; linarith [hsum]

/-- Threshold form of the E2 absorption used by `main`: for `δ` below a fixed `δ₀`, any
`δ^(-η_KT)`-Katz–Tao family `s` satisfies `δ^(-ε/2)·D(|s|) ≤ δ^(-ε)`, where `D` is the E2
conjunct's RHS.  Combines `katzTao_card_volume_bound` (|s|-bound), `e2_polylog_absorb`
(poly-log absorption) and `e2_habsorb`.  Holds for empty `s` too (via `N := max |s| 1`). -/
lemma e2_absorb_threshold (ε η_KT η₁ : ℝ) (hε : 0 < ε)
    (hη_KT_pos : 0 < η_KT) (hη_KT_lt : 2 * η_KT +
      1 / ((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ) < ε / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ δ₀ → δ < 1 →
      ∀ {ι : Type} (s : Finset ι) (T : ι → Tube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        ConvexSpaceBody.IsKatzTao s (fun i => (T i).toConvexSpaceBody)
          (ENNReal.ofReal ((δ : ℝ) ^ (-η_KT))) →
        (δ : ℝ) ^ (-(ε / 2))
          * ((641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
              * edRefineC (E := E) * (δ : ℝ) ^ (-2 * η_KT)
              * (e2Const (Module.finrank ℝ E) η₁ ε δ *
                (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
                  * (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
                        / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
                      + (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
                        / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)))
              * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1)
                  ^ (gridLen (Module.finrank ℝ E) η₁ ε - 1))
          ≤ (δ : ℝ) ^ (-ε) := by
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn_pos : 0 < n := Module.finrank_pos
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
  have hc_pos : (0 : ℝ) < (Tube.le_volume.c n : ℝ) := by exact_mod_cast Tube.le_volume.c_pos n
  set M_inner : ℕ := gridLen n η₁ ε with hM_inner_def
  set ε_inner : ℝ := 1 / (M_inner : ℝ) with hε_inner_def
  have hM_inner_pos : 1 ≤ M_inner := by
    rw [hM_inner_def]; exact one_le_gridLen _ _ _
  have hε_inner_nonneg : 0 ≤ ε_inner := by
    rw [hε_inner_def]; positivity
  have hε_inner_pos : 0 < ε_inner := by
    rw [hε_inner_def]; positivity
  have hM_inner_ge_ceil4 : (⌈(4 : ℝ) / ε⌉₊ + 1 : ℕ) ≤ M_inner := by
    rw [hM_inner_def, gridLen_eq]; exact le_max_right _ _
  have h_ε_inner_bound : ε_inner < ε / 4 := by
    have hceil_pos_real : (0 : ℝ) < ((⌈(4 : ℝ) / ε⌉₊ + 1 : ℕ) : ℝ) := by
      have : 0 < (⌈(4 : ℝ) / ε⌉₊ + 1 : ℕ) := by omega
      exact_mod_cast this
    have hM_pos_real : (0 : ℝ) < (M_inner : ℝ) := by
      have : 0 < M_inner := by omega
      exact_mod_cast this
    have h_ceil_ge_4div : ((⌈(4 : ℝ) / ε⌉₊ + 1 : ℕ) : ℝ) ≥ (4 : ℝ) / ε := by
      have : (⌈(4 : ℝ) / ε⌉₊ : ℝ) ≥ (4 : ℝ) / ε := Nat.le_ceil _
      push_cast
      linarith
    have hM_ge_ceil : (M_inner : ℝ) ≥ ((⌈(4 : ℝ) / ε⌉₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast hM_inner_ge_ceil4
    have h4_lt : (4 : ℝ) < ε * ((⌈(4 : ℝ) / ε⌉₊ + 1 : ℕ) : ℝ) := by
      have hlt : (4 : ℝ) / ε < ((⌈(4 : ℝ) / ε⌉₊ + 1 : ℕ) : ℝ) := by
        have h := Nat.le_ceil ((4 : ℝ) / ε)
        push_cast
        linarith
      have := (div_lt_iff₀ hε).mp hlt
      linarith
    have h1_div : 1 / ((⌈(4 : ℝ) / ε⌉₊ + 1 : ℕ) : ℝ) < ε / 4 := by
      rw [div_lt_div_iff₀ hceil_pos_real (by norm_num : (0 : ℝ) < 4)]
      linarith
    calc
      ε_inner = 1 / (M_inner : ℝ) := hε_inner_def
      _ ≤ 1 / ((⌈(4 : ℝ) / ε⌉₊ + 1 : ℕ) : ℝ) :=
        (one_div_le_one_div hM_pos_real hceil_pos_real).mpr hM_ge_ceil
      _ < ε / 4 := h1_div
  set qCq : ℝ := qCardConst n M_inner (cnEff n) (prodConst n M_inner) with hqCq_def
  have hqCq_pos : 0 < qCq := qCardConst_pos n M_inner (cnEff n) (prodConst n M_inner)
  set Cdim : ℝ := (641 : ℝ) ^ (2 * n) * (4 : ℝ) ^ (2 * n) * edRefineC (E := E)
      * (qCq * (Tube.volume_le.C n : ℝ)
      * (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2) / (Tube.le_volume.c n : ℝ)
        + (Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ))) with hCdim_def
  have hCdim_nn : 0 ≤ Cdim := by
    rw [hCdim_def]
    have h1 : (0 : ℝ) ≤ edRefineC (E := E) := by linarith [one_le_edRefineC (E := E)]
    have h2 : (0 : ℝ) ≤ qCq * (Tube.volume_le.C n : ℝ)
        * (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2) / (Tube.le_volume.c n : ℝ)
          + (Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ)) := by positivity
    exact mul_nonneg (mul_nonneg (by positivity) h1) h2
  set Ckt0 : ℝ := MeasureTheory.volume.real (Metric.closedBall (0 : E) 2) / (Tube.le_volume.c n : ℝ)
    with hCkt0_def
  have hCkt0_nn : 0 ≤ Ckt0 := by rw [hCkt0_def]; positivity
  set Ckt : ℝ := Ckt0 + 1 with hCkt_def
  have hCkt_pos : 0 < Ckt := by rw [hCkt_def]; linarith
  set ζ : ℝ := ε / 2 - 2 * η_KT - ε_inner with hζ_def
  have hζ_pos : 0 < ζ := by
    rw [hζ_def]
    have hεi : ε_inner = 1 / ((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ) := by
      rw [hε_inner_def, hM_inner_def, hn_def]
    rw [hεi]
    linarith [hη_KT_lt]
  set B : ℝ := η_KT + ((n : ℝ) - 1) with hB_def
  have hB_nn : 0 ≤ B := by rw [hB_def]; linarith
  obtain ⟨δ₀, hδ₀_pos, hδ₀_spec⟩ :=
    e2_polylog_absorb Cdim B Ckt ζ (gridLen n η₁ ε - 1) hCdim_nn hB_nn hCkt_pos hζ_pos
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro δ hδ_pos hδ_le hδ_lt1 ι s T hT hKT
  have hδ_pos_real : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
  have hδ_lt1_real : (δ : ℝ) < 1 := by exact_mod_cast hδ_lt1
  have hexp : (δ : ℝ) ^ (n - 1) = (δ : ℝ) ^ ((n : ℝ) - 1) := by
    rw [← Real.rpow_natCast (δ : ℝ) (n - 1), Nat.cast_sub hn_pos, Nat.cast_one]
  have hsB : (s.card : ℝ) * (δ : ℝ) ^ B ≤ Ckt0 := by
    have hkt := katzTao_card_volume_bound hδ_pos hδ_lt1 s T hT η_KT hKT
    rw [hexp, mul_div_assoc] at hkt
    have hBexp : (δ : ℝ) ^ B = (δ : ℝ) ^ η_KT * (δ : ℝ) ^ ((n : ℝ) - 1) := by
      rw [← Real.rpow_add hδ_pos_real, hB_def]
    calc (s.card : ℝ) * (δ : ℝ) ^ B
        = (δ : ℝ) ^ η_KT * ((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1)) := by rw [hBexp]; ring
      _ ≤ (δ : ℝ) ^ η_KT * ((δ : ℝ) ^ (-η_KT) * Ckt0) :=
          mul_le_mul_of_nonneg_left hkt (Real.rpow_nonneg hδ_pos_real.le _)
      _ = Ckt0 := by
          rw [← mul_assoc, ← Real.rpow_add hδ_pos_real, add_neg_cancel, Real.rpow_zero, one_mul]
  have hδB_pos : (0 : ℝ) < (δ : ℝ) ^ B := Real.rpow_pos_of_pos hδ_pos_real _
  have hcard_bound : (s.card : ℝ) ≤ (δ : ℝ) ^ (-B) * Ckt := by
    rw [Real.rpow_neg hδ_pos_real.le, mul_comm, ← div_eq_mul_inv]
    exact (le_div_iff₀ hδB_pos).mpr (le_trans hsB (by linarith))
  have hδnegB_ge1 : (1 : ℝ) ≤ (δ : ℝ) ^ (-B) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ_pos_real hδ_lt1_real.le (by linarith)
  set Nn : ℕ := max s.card 1 with hNn_def
  have hNn_ge1 : 1 ≤ Nn := le_max_right _ _
  have hNn_bound : (Nn : ℝ) ≤ (δ : ℝ) ^ (-B) * Ckt := by
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [hNn_def, h0]; norm_num; nlinarith [hδnegB_ge1, hCkt_pos]
    · rw [hNn_def, Nat.max_eq_left hpos]; exact hcard_bound
  have hpl := hδ₀_spec δ hδ_pos hδ_le Nn hNn_ge1 hNn_bound
  have hfloor_eq : (⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) = (⌊Real.logb 2 (Nn : ℝ)⌋₊ : ℝ) := by
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [hNn_def, h0]; norm_num
    · rw [hNn_def, Nat.max_eq_left hpos]
  have hCdimPl : Cdim * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1) ^ (gridLen n η₁ ε - 1)
      ≤ (δ : ℝ) ^ (-ζ) := by rw [hfloor_eq]; exact hpl
  have hbase := e2_habsorb hδ_pos (ε / 2) (2 * η_KT + ε_inner) Cdim
    (((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1) ^ (gridLen n η₁ ε - 1)) ζ ε hCdimPl
    (by
      rw [hζ_def]
      ring)
  have hδexp_merge : (δ : ℝ) ^ (-2 * η_KT) * (δ : ℝ) ^ (-ε_inner) =
    (δ : ℝ) ^ (-(2 * η_KT + ε_inner)) := by
    rw [← Real.rpow_add hδ_pos_real, add_comm, neg_add, add_comm]
    ring_nf
  have h_e2Const_unfold : e2Const n η₁ ε δ = qCq * (δ : ℝ) ^ (-ε_inner) := by
    unfold e2Const
    rw [hqCq_def, hε_inner_def, ← hM_inner_def]
  calc
    (δ : ℝ) ^ (-(ε / 2))
      * ((641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
          * edRefineC (E := E) * (δ : ℝ) ^ (-2 * η_KT)
          * (e2Const (Module.finrank ℝ E) η₁ ε δ *
            (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
              * (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
                    / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
                  + (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
                    / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)))
          * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1) ^ (gridLen (Module.finrank ℝ E) η₁ ε - 1))
    = (δ : ℝ) ^ (-(ε / 2)) * ((δ : ℝ) ^ (-(2 * η_KT + ε_inner)) * Cdim
        * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1) ^ (gridLen n η₁ ε - 1)) := by
      rw [h_e2Const_unfold, hCdim_def, ← hn_def]
      calc
        (δ : ℝ) ^ (-(ε / 2)) * ((641 : ℝ) ^ (2 * n) * (4 : ℝ) ^ (2 * n) * edRefineC (E := E)
            * (δ : ℝ) ^ (-2 * η_KT)
            * (qCq * (δ : ℝ) ^ (-ε_inner) * (Tube.volume_le.C n : ℝ)
              * (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2) / (Tube.le_volume.c n : ℝ)
                + (Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ)))
            * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1) ^ (gridLen n η₁ ε - 1))
          = (δ : ℝ) ^ (-(ε / 2)) * (((δ : ℝ) ^ (-2 * η_KT) * (δ : ℝ) ^ (-ε_inner))
            * ((641 : ℝ) ^ (2 * n) * (4 : ℝ) ^ (2 * n) * edRefineC (E := E) * qCq
              * (Tube.volume_le.C n : ℝ)
              * (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2) / (Tube.le_volume.c n : ℝ)
                + (Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ)))
            * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1) ^ (gridLen n η₁ ε - 1)) := by ring
        _ = (δ : ℝ) ^ (-(ε / 2)) * ((δ : ℝ) ^ (-(2 * η_KT + ε_inner))
            * ((641 : ℝ) ^ (2 * n) * (4 : ℝ) ^ (2 * n) * edRefineC (E := E) * qCq
              * (Tube.volume_le.C n : ℝ)
              * (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2) / (Tube.le_volume.c n : ℝ)
                + (Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ)))
            * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1) ^ (gridLen n η₁ ε - 1)) := by
          rw [hδexp_merge]
        _ = (δ : ℝ) ^ (-(ε / 2)) * ((δ : ℝ) ^ (-(2 * η_KT + ε_inner)) * Cdim
            * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1) ^ (gridLen n η₁ ε - 1)) := by
          rw [hCdim_def]; ring
    _ ≤ (δ : ℝ) ^ (-ε) := hbase

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Threshold form of the `:1466` constant absorption used by `main`: for `δ` below a fixed
`δ₀ > 0` (depending only on `η_KT`, `η₁`, `n`), the dimensional constant `Cc` in the
leaf→parent `maxDensity` transfer (`uniform_parent_maxDensity_le`) is absorbed into the strict
gap `ε_inner² - η_KT`, giving `Cc · δ^(-η_KT) ≤ δ^(-ε_inner²)`.  Requires STRICT
`η_KT < ε_inner²`.  Mirrors `e2_absorb_threshold`; `Cc` is dimensional so `main` can name it. -/
lemma dmax_absorb_threshold (η_KT η₁ ε : ℝ) (_hη₁_pos : 0 < η₁)
    (_hη_KT_pos : 0 < η_KT)
    (hη_KT_lt : η_KT <
        (1 / ((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ)) ^ 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ δ₀ → (δ : ℝ) < 1 →
      (↑(Tube.volume_le.C (Module.finrank ℝ E))
            / ↑(Tube.le_volume.c (Module.finrank ℝ E))
          * ↑(2 * (Tube.overlapConstBOTight (Module.finrank ℝ E) : NNReal))
          * (2 : ENNReal) ^ Module.finrank ℝ E)
          * ENNReal.ofReal ((δ : ℝ) ^ (-η_KT))
        ≤ ENNReal.ofReal ((δ : ℝ) ^
            (-((1 / ((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ)) ^ 2))) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set εsq : ℝ := (1 / ((gridLen n η₁ ε : ℕ) : ℝ)) ^ 2 with hεsq_def
  have hc_pos : (0 : ℝ) < (Tube.le_volume.c n : ℝ) := by exact_mod_cast Tube.le_volume.c_pos n
  have hcne : (Tube.le_volume.c n : NNReal) ≠ 0 := by exact_mod_cast (Tube.le_volume.c_pos n).ne'
  set Q : NNReal := Tube.volume_le.C n / Tube.le_volume.c n
      * (2 * Tube.overlapConstBOTight n) * 2 ^ n with hQ_def
  set c : ℝ := max (Q : ℝ) 1 with hc_def
  have hc1 : (1 : ℝ) ≤ c := le_max_right _ _
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc1
  set ζ : ℝ := εsq - η_KT with hζ_def
  have hζ_pos : 0 < ζ := by rw [hζ_def]; linarith
  have hζ_ne : ζ ≠ 0 := hζ_pos.ne'
  refine ⟨c ^ (-(1 / ζ)), Real.rpow_pos_of_pos hc0 _, ?_⟩
  intro δ hδ_pos hδ_le hδ_lt1
  have hδ_pos_real : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
  have hkey : c ≤ (δ : ℝ) ^ (-ζ) := by
    have h1 : (c ^ (-(1 / ζ))) ^ (-ζ) ≤ (δ : ℝ) ^ (-ζ) :=
      Real.rpow_le_rpow_of_nonpos hδ_pos_real hδ_le (by linarith)
    have h2 : (c ^ (-(1 / ζ))) ^ (-ζ) = c := by
      rw [← Real.rpow_mul hc0.le,
        show (-(1 / ζ)) * (-ζ) = 1 by field_simp, Real.rpow_one]
    linarith [h2 ▸ h1]
  have hconst_eq :
      (↑(Tube.volume_le.C n) / ↑(Tube.le_volume.c n)
          * ↑(2 * (Tube.overlapConstBOTight n : NNReal)) * (2 : ENNReal) ^ n : ENNReal)
        = (↑Q : ENNReal) := by
    rw [hQ_def]
    simp only [ENNReal.coe_mul, ENNReal.coe_div hcne, ENNReal.coe_pow]
    norm_num
  rw [hconst_eq, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hQc : (Q : ℝ) ≤ (δ : ℝ) ^ (-ζ) := le_trans (le_max_left _ _) hkey
  have hpow : (δ : ℝ) ^ (-ζ) * (δ : ℝ) ^ (-η_KT) = (δ : ℝ) ^ (-εsq) := by
    rw [← Real.rpow_add hδ_pos_real]; congr 1; rw [hζ_def]; ring
  calc (Q : ℝ) * (δ : ℝ) ^ (-η_KT)
      ≤ (δ : ℝ) ^ (-ζ) * (δ : ℝ) ^ (-η_KT) :=
        mul_le_mul_of_nonneg_right hQc (Real.rpow_nonneg hδ_pos_real.le _)
    _ = (δ : ℝ) ^ (-εsq) := hpow

/-- **Generic constant absorption.**  A fixed constant `Q` is absorbed into any strictly positive
gap between two exponents: for `δ` below a threshold determined by `Q` and `σ - θ`, one has
`Q · δ^(-θ) ≤ δ^(-σ)`.  This is `dmax_absorb_threshold` with the constant abstracted. -/
lemma const_absorb_threshold (Q : NNReal) (θ σ : ℝ) (hθσ : θ < σ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ δ₀ → (δ : ℝ) < 1 →
      (Q : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-θ))
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-σ)) := by
  set c : ℝ := max (Q : ℝ) 1 with hc_def
  have hc1 : (1 : ℝ) ≤ c := le_max_right _ _
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc1
  set ζ : ℝ := σ - θ with hζ_def
  have hζ_pos : 0 < ζ := by rw [hζ_def]; linarith
  have hζ_ne : ζ ≠ 0 := hζ_pos.ne'
  refine ⟨c ^ (-(1 / ζ)), Real.rpow_pos_of_pos hc0 _, ?_⟩
  intro δ hδ_pos hδ_le _hδ_lt1
  have hδ_pos_real : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
  have hkey : c ≤ (δ : ℝ) ^ (-ζ) := by
    have h1 : (c ^ (-(1 / ζ))) ^ (-ζ) ≤ (δ : ℝ) ^ (-ζ) :=
      Real.rpow_le_rpow_of_nonpos hδ_pos_real hδ_le (by linarith)
    have h2 : (c ^ (-(1 / ζ))) ^ (-ζ) = c := by
      rw [← Real.rpow_mul hc0.le,
        show (-(1 / ζ)) * (-ζ) = 1 by field_simp, Real.rpow_one]
    linarith [h2 ▸ h1]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hQc : (Q : ℝ) ≤ (δ : ℝ) ^ (-ζ) := le_trans (le_max_left _ _) hkey
  have hpow : (δ : ℝ) ^ (-ζ) * (δ : ℝ) ^ (-θ) = (δ : ℝ) ^ (-σ) := by
    rw [← Real.rpow_add hδ_pos_real]; congr 1; rw [hζ_def]; ring
  calc (Q : ℝ) * (δ : ℝ) ^ (-θ)
      ≤ (δ : ℝ) ^ (-ζ) * (δ : ℝ) ^ (-θ) :=
        mul_le_mul_of_nonneg_right hQc (Real.rpow_nonneg hδ_pos_real.le _)
    _ = (δ : ℝ) ^ (-σ) := hpow

/-- **Kpoly is subpolynomial** (E5 `s_heavy` crux): the shade-refinement loss
`Kpoly = (Nat.log₂ B + 1)^(2⌈log log(1/δ)⌉)` with `B ≤ δ^(-A)` satisfies, for `δ` small,
`δ^η₁ · Kpoly ≤ δ^η_full / 2` whenever `η_full < η₁`.  The exponent is `loglog(1/δ)` and the
base is `polylog(1/δ)`, so `log Kpoly = O((loglog)²) = o(log(1/δ))`; the strict gap `η₁-η_full`
then absorbs it.  This is the genuine analytic remainder of E5 (no construction change). -/
lemma kpoly_subpoly (η₁ η_full A C₀ : ℝ) (hζ : η_full < η₁) (hA : 0 < A)
    (hC₀ : 1 ≤ C₀) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ δ₀ → (δ : ℝ) < 1 →
      ∀ (B : ℕ), (B : ℝ) ≤ C₀ * (δ : ℝ) ^ (-A) →
        (δ : ℝ) ^ η₁ *
            ((Nat.log 2 B + 1 : ℕ) : ℝ) ^ (2 * ⌈Real.log (Real.log (1 / (δ : ℝ)))⌉₊)
          ≤ (δ : ℝ) ^ η_full / 2 := by
  set ζ : ℝ := η₁ - η_full with hζ_def
  have hζ_pos : 0 < ζ := by rw [hζ_def]; linarith
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogC₀_nonneg : 0 ≤ Real.log C₀ := Real.log_nonneg hC₀
  set c₁ : ℝ := (A + Real.log C₀) / Real.log 2 + 1 with hc₁_def
  have hc₁_pos : 0 < c₁ := by rw [hc₁_def]; positivity
  have h1 : (fun u : ℝ => 2 * Real.log u ^ 2) =o[Filter.atTop] (id : ℝ → ℝ) :=
    (Real.isLittleO_pow_log_id_atTop (n := 2)).const_mul_left 2
  have h2 : (fun u : ℝ => 2 * (1 + Real.log c₁) * Real.log u) =o[Filter.atTop] (id : ℝ → ℝ) := by
    have := (Real.isLittleO_pow_log_id_atTop (n := 1)).const_mul_left (2 * (1 + Real.log c₁))
    simpa [pow_one] using this
  have h3 : (fun _ : ℝ => 2 * Real.log c₁ + Real.log 2) =o[Filter.atTop] (id : ℝ → ℝ) :=
    Asymptotics.isLittleO_const_id_atTop _
  have hpoly_o := (h1.add h2).add h3
  have hev : ∀ᶠ u : ℝ in Filter.atTop,
      2 * (Real.log u + 1) * Real.log (c₁ * u) + Real.log 2 ≤ ζ * u := by
    have hdef := hpoly_o.def hζ_pos
    filter_upwards [hdef, Filter.eventually_gt_atTop (0 : ℝ)] with u hu hu0
    have hlogmul : Real.log (c₁ * u) = Real.log c₁ + Real.log u :=
      Real.log_mul hc₁_pos.ne' hu0.ne'
    rw [id_eq, Real.norm_of_nonneg hu0.le] at hu
    have hpoly_eq :
        2 * Real.log u ^ 2 + 2 * (1 + Real.log c₁) * Real.log u + (2 * Real.log c₁ + Real.log 2)
          = 2 * (Real.log u + 1) * Real.log (c₁ * u) + Real.log 2 := by
      rw [hlogmul]; ring
    calc 2 * (Real.log u + 1) * Real.log (c₁ * u) + Real.log 2
        = 2 * Real.log u ^ 2 + 2 * (1 + Real.log c₁) * Real.log u
            + (2 * Real.log c₁ + Real.log 2) := hpoly_eq.symm
      _ ≤ ‖2 * Real.log u ^ 2 + 2 * (1 + Real.log c₁) * Real.log u
            + (2 * Real.log c₁ + Real.log 2)‖ := by
            rw [Real.norm_eq_abs]; exact le_abs_self _
      _ ≤ ζ * u := hu
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.mp hev
  set U₀ : ℝ := max (max U 1) (Real.log 2 / ζ + 1) with hU₀_def
  refine ⟨Real.exp (-U₀), Real.exp_pos _, ?_⟩
  intro δ hδ_pos hδ_le hδ_lt1 B hB
  have hδ_pos_real : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
  set u : ℝ := Real.log (1 / (δ : ℝ)) with hu_def
  have hu_ge : U₀ ≤ u := by
    have hlogδ : Real.log (δ : ℝ) ≤ -U₀ := by
      have := Real.log_le_log hδ_pos_real hδ_le
      rwa [Real.log_exp] at this
    have : u = -Real.log (δ : ℝ) := by rw [hu_def, one_div, Real.log_inv]
    rw [this]; linarith
  have hU₀_ge1 : (1 : ℝ) ≤ U₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hu_ge1 : (1 : ℝ) ≤ u := le_trans hU₀_ge1 hu_ge
  have hu_pos : 0 < u := lt_of_lt_of_le one_pos hu_ge1
  have hlogu_nonneg : 0 ≤ Real.log u := Real.log_nonneg hu_ge1
  set K : ℕ := Nat.log 2 B + 1 with hK_def
  have hKr_ge1 : (1 : ℝ) ≤ (K : ℝ) := by
    rw [hK_def]; push_cast
    have : (0 : ℝ) ≤ (Nat.log 2 B : ℝ) := Nat.cast_nonneg _
    linarith
  have hKr_pos : 0 < (K : ℝ) := lt_of_lt_of_le one_pos hKr_ge1
  have hu_neg : u = -Real.log (δ : ℝ) := by rw [hu_def, one_div, Real.log_inv]
  have hNatlog_le : (Nat.log 2 B : ℝ) ≤ (Real.log C₀ + A * u) / Real.log 2 := by
    rw [le_div_iff₀ hlog2_pos]
    rcases Nat.eq_zero_or_pos B with hB0 | hBpos
    · subst hB0
      simp only [Nat.log_zero_right, Nat.cast_zero, zero_mul]
      exact add_nonneg hlogC₀_nonneg (mul_nonneg hA.le hu_pos.le)
    · have hpr : ((2 : ℝ)) ^ Nat.log 2 B ≤ (B : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 hBpos.ne'
      have h := Real.log_le_log (by positivity) hpr
      rw [Real.log_pow] at h
      have hBr_pos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hBpos
      have hlogB : Real.log (B : ℝ) ≤ Real.log C₀ + A * u := by
        have h2 := Real.log_le_log hBr_pos hB
        rw [Real.log_mul (lt_of_lt_of_le one_pos hC₀).ne'
              (Real.rpow_pos_of_pos hδ_pos_real _).ne', Real.log_rpow hδ_pos_real] at h2
        rw [hu_neg]; linarith [h2]
      linarith [h, hlogB]
  have hKr_le : (K : ℝ) ≤ c₁ * u := by
    have hL_ne : Real.log 2 ≠ 0 := hlog2_pos.ne'
    rw [hK_def]; push_cast; rw [hc₁_def]
    have hgoal : ((A + Real.log C₀) / Real.log 2 + 1) * u
        = (Real.log C₀ + A * u) / Real.log 2 + (Real.log C₀ * (u - 1)) / Real.log 2 + u := by
      field_simp; ring
    rw [hgoal]
    have hpos1 : 0 ≤ (Real.log C₀ * (u - 1)) / Real.log 2 :=
      div_nonneg (mul_nonneg hlogC₀_nonneg (by linarith [hu_ge1])) hlog2_pos.le
    linarith [hNatlog_le, hu_ge1, hpos1]
  have hlogK_le : Real.log (K : ℝ) ≤ Real.log (c₁ * u) :=
    Real.log_le_log hKr_pos hKr_le
  set M : ℕ := ⌈Real.log u⌉₊ with hM_def
  have hMr_le : (M : ℝ) ≤ Real.log u + 1 := by
    rw [hM_def]; exact (Nat.ceil_lt_add_one hlogu_nonneg).le
  have hkey : 2 * (M : ℝ) * Real.log (K : ℝ) ≤ ζ * u - Real.log 2 := by
    have hA1 : (M : ℝ) * Real.log (K : ℝ) ≤ (Real.log u + 1) * Real.log (c₁ * u) :=
      mul_le_mul hMr_le hlogK_le (Real.log_nonneg hKr_ge1) (by linarith [hlogu_nonneg])
    have hstep : 2 * (M : ℝ) * Real.log (K : ℝ)
        ≤ 2 * (Real.log u + 1) * Real.log (c₁ * u) := by linarith [hA1]
    have huU : U ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu_ge
    have hpoly := hU u huU
    linarith [hstep, hpoly]
  have hKpow_eq : (K : ℝ) ^ (2 * M) = Real.exp ((2 * (M : ℝ)) * Real.log (K : ℝ)) := by
    rw [← Real.rpow_natCast (K : ℝ) (2 * M), Real.rpow_def_of_pos hKr_pos]
    congr 1; push_cast; ring
  have hexp_ζu : Real.exp (ζ * u) = (δ : ℝ) ^ (-ζ) := by
    rw [Real.rpow_def_of_pos hδ_pos_real, hu_neg]
    congr 1; ring
  have hKpow_le : (K : ℝ) ^ (2 * M) ≤ (δ : ℝ) ^ (-ζ) / 2 := by
    rw [hKpow_eq]
    calc Real.exp ((2 * (M : ℝ)) * Real.log (K : ℝ))
        ≤ Real.exp (ζ * u - Real.log 2) := Real.exp_le_exp.mpr hkey
      _ = Real.exp (ζ * u) * Real.exp (-Real.log 2) := by rw [sub_eq_add_neg, Real.exp_add]
      _ = (δ : ℝ) ^ (-ζ) * (1 / 2) := by
          rw [hexp_ζu, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]; norm_num
      _ = (δ : ℝ) ^ (-ζ) / 2 := by ring
  calc (δ : ℝ) ^ η₁ * ((K : ℝ)) ^ (2 * M)
      ≤ (δ : ℝ) ^ η₁ * ((δ : ℝ) ^ (-ζ) / 2) :=
        mul_le_mul_of_nonneg_left hKpow_le (Real.rpow_nonneg hδ_pos_real.le _)
    _ = (δ : ℝ) ^ (η₁ + -ζ) / 2 := by rw [Real.rpow_add hδ_pos_real]; ring
    _ = (δ : ℝ) ^ η_full / 2 := by
        rw [show η₁ + -ζ = η_full by rw [hζ_def]; ring]

/-- Pure-arithmetic core of the E2 regime split (kept context-free so the heavy
algebra does not run inside the huge `exists_frostman_translation_family` context).
Given the sharp `R`-bound, the Katz–Tao density bound on `s`, the carrier-multiplicity
bound, and the `s₁→s₂` refinement loss, the packing product is `≤ δ^(-η)·C·P`. -/
lemma e2_regime_arith {R Sc S1 S2 Cn Cq Dn Dη A Bb P : ℝ}
    (hCn : 0 < Cn) (hCq : 0 < Cq) (hDn : 0 < Dn) (hS2 : 0 < S2) (hP : 1 ≤ P) (hDη : 0 < Dη)
    (hA : 0 ≤ A) (hB : 0 ≤ Bb) (hSc : 0 ≤ Sc)
    (hR : R ≤ Cq * max 1 (S2 * Dn)⁻¹)
    (hkt : Sc * Dn ≤ Dη * A)
    (hmult : Sc ≤ Dη * Bb * S1)
    (hs12 : S1 ≤ S2 * P) :
    R * Sc * Cn * Dn ≤ Dη * (Cq * Cn * (A + Bb)) * P := by
  have hP0 : (0 : ℝ) ≤ P := le_trans zero_le_one hP
  have hsmul_ub : Sc ≤ Dη * Bb * (S2 * P) :=
    le_trans hmult (mul_le_mul_of_nonneg_left hs12 (mul_nonneg hDη.le hB))
  by_cases hY : S2 * Dn ≤ 1
  · have hY_pos : 0 < S2 * Dn := mul_pos hS2 hDn
    have hmaxeq : max 1 (S2 * Dn)⁻¹ = (S2 * Dn)⁻¹ :=
      max_eq_right ((one_le_inv₀ hY_pos).mpr hY)
    rw [hmaxeq] at hR
    have hRs2 : R * (S2 * Dn) ≤ Cq := by
      have := mul_le_mul_of_nonneg_right hR hY_pos.le
      rwa [mul_assoc, inv_mul_cancel₀ hY_pos.ne', mul_one] at this
    apply le_of_mul_le_mul_right _ hS2
    calc R * Sc * Cn * Dn * S2 = (R * (S2 * Dn)) * (Sc * Cn) := by ring
      _ ≤ Cq * (Sc * Cn) := mul_le_mul_of_nonneg_right hRs2 (mul_nonneg hSc hCn.le)
      _ ≤ Cq * ((Dη * Bb * (S2 * P)) * Cn) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsmul_ub hCn.le) hCq.le
      _ ≤ (Dη * (Cq * Cn * (A + Bb)) * P) * S2 := by
          have hle : Bb ≤ A + Bb := by linarith
          have h1 : (0 : ℝ) ≤ Cq * Dη * Cn * P * S2 :=
            mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCq.le hDη.le) hCn.le) hP0) hS2.le
          nlinarith [mul_le_mul_of_nonneg_left hle h1]
  · push Not at hY
    have hmaxeq : max 1 (S2 * Dn)⁻¹ = 1 := by
      apply max_eq_left; rw [inv_le_one_iff₀]; right; exact hY.le
    rw [hmaxeq, mul_one] at hR
    calc R * Sc * Cn * Dn = (R * Cn) * (Sc * Dn) := by ring
      _ ≤ (Cq * Cn) * (Dη * A) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hR hCn.le) hkt
            (mul_nonneg hSc hDn.le) (mul_nonneg hCq.le hCn.le)
      _ ≤ Dη * (Cq * Cn * (A + Bb)) * P := by
          have h2 : (0 : ℝ) ≤ Cq * Cn * Dη :=
            mul_nonneg (mul_nonneg hCq.le hCn.le) hDη.le
          nlinarith [mul_nonneg (mul_nonneg h2 hA) (by linarith : (0 : ℝ) ≤ P - 1),
            mul_nonneg (mul_nonneg h2 hB) hP0]
end stickyKatzTaoOfStickyFrostman

end StickyKakeya

end Kakeya
