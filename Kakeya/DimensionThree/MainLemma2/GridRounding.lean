/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Uniform

/-!
# Rounding an arbitrary radius up to a scale of the multiscale grid

The multiscale grid of GWZ Definition 2.1 (`Tube.gridScale`) consists of the
`N + 1` scales `δ^{k/N}`, `0 ≤ k ≤ N`.  A radius that arises from the geometry — the radius
`r = θ b` at which the transverse branch of Main Lemma 2 invokes the scale-`r` interface, say —
is not of that form.  This file records that this is not an obstruction, for an entirely
elementary reason: consecutive grid scales differ by the factor `δ^{1/N}`, so rounding an
arbitrary radius `r ∈ [δ, 1]` *up* to the nearest grid scale costs at most that one factor.

* `Kakeya.StickyKakeya.exists_gridScale_ge` is the rounding statement: there is a grid index
  `k ≤ N` with `r ≤ ρ_k ≤ δ^{-1/N} r`.
* `Kakeya.StickyKakeya.rpow_neg_div_le_rpow_neg` is the accounting: a loss `δ^{-c/N}` is at
  most a prescribed `δ^{-α}` as soon as `c ≤ α N`.
* `Kakeya.StickyKakeya.le_ssfGridLen` and
  `Kakeya.StickyKakeya.exists_ssfGridLen_rpow_threshold` combine the two at the grid length
  `N = ⌈log log 1/δ⌉` of GWZ Definition 2.1, where the loss is *sub-polynomial*: `1/N → 0` as
  `δ → 0⁺`, so `δ^{-c/N} ≤ δ^{-α}` for every fixed `α > 0` once `δ` is small enough.  This is
  the design intent of the grid length `log log 1/δ`, and the same computation is already
  recorded in the docstrings of `Tube.exists_uniformTubeSet_subfamily`,
  `Tube.exists_uniformTubeSet_subfamily_ssf` and, for shaded families, of
  `Kakeya.ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`.

GWZ perform this rounding themselves (p. 41: "we choose a radius `r` of the form `r = δ^{ηj}`
with `θ b ≤ r ≤ δ^{-η} θ b"), paying `δ^{3η}` for it in the ball estimate.  Rounding to the
Definition 2.1 grid instead costs `δ^{3/N}` with `N = ⌈log log 1/δ⌉`, which is strictly
cheaper, since `1/N ≤ η` for every fixed `η > 0` at small `δ`.

Nothing here mentions tubes, a configuration, or a measure: it is arithmetic of real powers.
-/

@[expose] public section

namespace StickyKakeya

open Set
open Tube

/-! ### Monotonicity along the grid -/

/-- The grid scales decrease as the index grows: `ρ_l ≤ ρ_k` for `k ≤ l`, since `δ ≤ 1`. -/
theorem gridScale_le_gridScale {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (N : ℕ) {k l : ℕ}
    (hkl : k ≤ l) : gridScale δ N l ≤ gridScale δ N k := by
  simp only [gridScale]
  refine NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 ?_
  have hk : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  gcongr

/-! ### Rounding up -/

/-- **Rounding a radius up to a grid scale.**

For `0 < δ ≤ 1`, a positive grid length `N` and any radius `r` in the range `[δ, 1]` spanned by
the grid, there is a grid index `k ≤ N` whose scale `ρ_k = δ^{k/N}` dominates `r` by at most the
single grid step `δ^{-1/N}`:

`r ≤ ρ_k ≤ δ^{-1/N} r`.

The index is `k = ⌊N log r / log δ⌋`, the largest one whose scale still dominates `r`; the upper
bound is the failure of the next index. -/
theorem exists_gridScale_ge {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ} (hN : 0 < N)
    {r : NNReal} (hr : r ∈ Set.Icc δ 1) :
    ∃ k ≤ N, r ≤ gridScale δ N k ∧
      gridScale δ N k ≤ δ ^ (-(1 : ℝ) / (N : ℝ)) * r := by
  by_cases hδeq : δ = 1
  · -- δ = 1 : every grid scale is 1, and r = 1
    subst hδeq
    have hr1' : r = 1 := le_antisymm hr.2 hr.1
    subst hr1'
    refine ⟨0, Nat.zero_le N, ?_, ?_⟩
    · simp [gridScale]
    · simp [gridScale]
  · -- δ < 1 : round the exponent up
    have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ
    have hδ1Rle : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
    have hδ1Rlt : (δ : ℝ) < 1 := by
      have hne : (δ : ℝ) ≠ 1 := by
        intro h
        exact hδeq (by exact_mod_cast h)
      exact lt_of_le_of_ne hδ1Rle hne
    have hδrR : (δ : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.1
    have hr1R : (r : ℝ) ≤ 1 := by exact_mod_cast hr.2
    have hrposR : 0 < (r : ℝ) := lt_of_lt_of_le hδR hδrR
    have hlogδneg : Real.log (δ : ℝ) < 0 := Real.log_neg hδR hδ1Rlt
    have hlogδ_le_logr : Real.log (δ : ℝ) ≤ Real.log (r : ℝ) := Real.log_le_log hδR hδrR
    have hlogr_le0 : Real.log (r : ℝ) ≤ 0 := Real.log_nonpos (le_of_lt hrposR) hr1R
    let θ : ℝ := Real.log (r : ℝ) / Real.log (δ : ℝ)
    have hθ_nonneg : 0 ≤ θ := by
      dsimp [θ]
      exact div_nonneg_of_nonpos hlogr_le0 hlogδneg.le
    have hθ_le_one : θ ≤ 1 := by
      dsimp [θ]
      exact (div_le_iff_of_neg hlogδneg).2 (by simpa using hlogδ_le_logr)
    have hNnonnegR : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
    have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hθN_le_N : θ * (N : ℝ) ≤ (N : ℝ) := by
      calc
        θ * (N : ℝ) ≤ (1 : ℝ) * (N : ℝ) := mul_le_mul_of_nonneg_right hθ_le_one hNnonnegR
        _ = (N : ℝ) := by ring
    let k : ℕ := Nat.floor (θ * (N : ℝ))
    have hkN : k ≤ N := by
      dsimp [k]
      have hf := Nat.floor_le_floor hθN_le_N
      simpa [Nat.floor_natCast] using hf
    have hθN_nonneg : 0 ≤ θ * (N : ℝ) := mul_nonneg hθ_nonneg hNnonnegR
    have hk_le_θN : (k : ℝ) ≤ θ * (N : ℝ) := by
      dsimp [k]
      exact Nat.floor_le hθN_nonneg
    have hktheta : (k : ℝ) / (N : ℝ) ≤ θ := (div_le_iff₀ hNposR).2 hk_le_θN
    have heq_theta : (δ : ℝ) ^ θ = (r : ℝ) := by
      dsimp [θ]
      rw [Real.rpow_def_of_pos hδR]
      calc
        Real.exp (Real.log (δ : ℝ) * (Real.log (r : ℝ) / Real.log (δ : ℝ)))
            = Real.exp (Real.log (r : ℝ)) := by
              congr 1
              rw [← mul_div_assoc]
              rw [mul_div_cancel_left₀ (Real.log (r : ℝ)) hlogδneg.ne]
        _ = (r : ℝ) := Real.exp_log hrposR
    have hA_real : (r : ℝ) ≤ (gridScale δ N k : NNReal) := by
      rw [← heq_theta]
      simp only [gridScale, NNReal.coe_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge hδR hδ1Rle hktheta
    have heqNN : δ ^ θ = r := by
      apply NNReal.eq
      rw [NNReal.coe_rpow]
      exact heq_theta
    have hθN_lt_k1 : θ * (N : ℝ) < (k : ℝ) + 1 := by
      dsimp [k]
      exact Nat.lt_floor_add_one (θ * (N : ℝ))
    have hθ_le_k1N : θ ≤ ((k : ℝ) + 1) / (N : ℝ) := by
      have hlt : θ < ((k : ℝ) + 1) / (N : ℝ) := (lt_div_iff₀ hNposR).2 hθN_lt_k1
      exact le_of_lt hlt
    have hB1 : δ ^ (((k : ℝ) + 1) / (N : ℝ)) ≤ δ ^ θ :=
      NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 hθ_le_k1N
    have hB1' : δ ^ (((k : ℝ) + 1) / (N : ℝ)) ≤ r := by
      simpa [heqNN] using hB1
    have hB2 : δ ^ ((k : ℝ) / (N : ℝ)) * δ ^ ((1 : ℝ) / (N : ℝ)) ≤ r := by
      rw [add_div] at hB1'
      rw [NNReal.rpow_add hδ.ne'] at hB1'
      exact hB1'
    have hB3 :
        δ ^ ((k : ℝ) / (N : ℝ)) * δ ^ ((1 : ℝ) / (N : ℝ)) * δ ^ (-(1 : ℝ) / (N : ℝ)) ≤
          r * δ ^ (-(1 : ℝ) / (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hB2 (by positivity)
    have hB4 : δ ^ ((k : ℝ) / (N : ℝ)) ≤ δ ^ (-(1 : ℝ) / (N : ℝ)) * r := by
      rw [mul_assoc, ← NNReal.rpow_add hδ.ne'] at hB3
      have he0 : (1 : ℝ) / (N : ℝ) + (-(1 : ℝ) / (N : ℝ)) = 0 := by ring
      rw [he0, NNReal.rpow_zero] at hB3
      rw [mul_one] at hB3
      rw [mul_comm] at hB3
      exact hB3
    refine ⟨k, hkN, ?_, ?_⟩
    · exact (NNReal.coe_le_coe).mp hA_real
    · simpa [gridScale] using hB4

/-! ### The cost of one grid step -/

/-- **One grid step is cheaper than a prescribed power.**

For `0 < δ ≤ 1` the map `s ↦ δ^s` is antitone, so `δ^{-c/N} ≤ δ^{-α}` as soon as `c ≤ α N`.
This is the whole of the accounting: the loss incurred by rounding is `δ^{-c/N}` for a fixed
small integer `c`, and the budget it is charged against is a fixed power `δ^{-α}` with `α > 0`
chosen before `δ`. -/
theorem rpow_neg_div_le_rpow_neg {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {c α : ℝ} {N : ℕ}
    (hN : 0 < N) (h : c ≤ α * (N : ℝ)) :
    δ ^ (-c / (N : ℝ)) ≤ δ ^ (-α) := by
  apply NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1
  have hNp : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdiv : c / (N : ℝ) ≤ α := (div_le_iff₀ hNp).2 h
  rw [neg_div]
  linarith

/-! ### The grid length of GWZ Definition 2.1 -/

/-- Below the explicit threshold `exp(-exp n)` the grid length `⌈log log 1/δ⌉` of GWZ
Definition 2.1 is at least `n`.

Indeed `δ ≤ exp(-exp n)` reads `log (1/δ) ≥ exp n`, hence `log log (1/δ) ≥ n`, and the ceiling
only increases it. -/
theorem le_ssfGridLen {δ : NNReal} (hδ : 0 < δ) {n : ℕ}
    (h : (δ : ℝ) ≤ Real.exp (-Real.exp (n : ℝ))) : n ≤ ssfGridLen δ := by
  have hd : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hd_ne : (δ : ℝ) ≠ 0 := ne_of_gt hd
  have h1 : Real.log (δ : ℝ) ≤ -Real.exp (n : ℝ) := by
    simpa using Real.log_le_log hd h
  have hld : Real.log (1 / (δ : ℝ)) = -Real.log (δ : ℝ) := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hd_ne]
    simp
  have h2 : Real.exp (n : ℝ) ≤ Real.log (1 / (δ : ℝ)) := by
    rw [hld]
    linarith
  have h3 : (n : ℝ) ≤ Real.log (Real.log (1 / (δ : ℝ))) := by
    simpa using Real.log_le_log (Real.exp_pos (n : ℝ)) h2
  have h4 : (⌈(n : ℝ)⌉₊ : ℕ) ≤ ⌈Real.log (Real.log (1 / (δ : ℝ)))⌉₊ := Nat.ceil_mono h3
  simpa [ssfGridLen, Nat.ceil_natCast] using h4

/-- **The grid length beats every fixed reciprocal.**

For a prescribed `α > 0` and a prescribed loss exponent `c`, there is a threshold
`δ₀ ∈ (0, 1]` below which `c ≤ α ⌈log log 1/δ⌉`.  This is the statement that
`1/⌈log log 1/δ⌉ → 0`, made quantitative through `Kakeya.StickyKakeya.le_ssfGridLen`.

The quantifier order is the one the consumers need: `α` and `c` are fixed *before* `δ`, which
is what makes the threshold a condition on `δ` alone. -/
theorem exists_ssfGridLen_threshold (c α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : NNReal, 0 < δ → δ ≤ δ₀ → c ≤ α * (ssfGridLen δ : ℝ) := by
  let n : ℕ := ⌈c / α⌉₊
  have hdivle : c / α ≤ (n : ℝ) := Nat.le_ceil (c / α)
  have hcα : c ≤ α * (n : ℝ) := by
    have hc : c ≤ (n : ℝ) * α := (div_le_iff₀ hα).1 hdivle
    rwa [mul_comm]
  let δ₀ : NNReal := ⟨Real.exp (-Real.exp (n : ℝ)), (Real.exp_pos _).le⟩
  have hδ₀ : (δ₀ : ℝ) = Real.exp (-Real.exp (n : ℝ)) := by rfl
  refine ⟨δ₀, ?_, ?_, ?_⟩
  · rw [← NNReal.coe_pos]
    rw [hδ₀]
    exact Real.exp_pos _
  · change (δ₀ : ℝ) ≤ 1
    rw [hδ₀]
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Real.exp_pos _).le
  · intro δ hδ hδδ₀
    have hδle : (δ : ℝ) ≤ Real.exp (-Real.exp (n : ℝ)) := by
      rw [← hδ₀]
      exact NNReal.coe_le_coe.mp hδδ₀
    have hlen : n ≤ ssfGridLen δ := le_ssfGridLen hδ hδle
    have hmain : (n : ℝ) ≤ (ssfGridLen δ : ℝ) := by exact_mod_cast hlen
    exact hcα.trans (mul_le_mul_of_nonneg_left hmain hα.le)

/-- **Sub-polynomiality of the grid step at the Definition 2.1 grid length.**

Combining `Kakeya.StickyKakeya.exists_ssfGridLen_threshold` with
`Kakeya.StickyKakeya.rpow_neg_div_le_rpow_neg`: for a prescribed `α > 0` and a prescribed loss
exponent `c`, below a threshold `δ₀ ∈ (0, 1]` the `c`-fold grid step `δ^{-c/⌈log log 1/δ⌉}` is
at most `δ^{-α}`.

This is the form in which the scale-`r` layer of Main Lemma 2 charges the rounding of an
arbitrary radius to the grid: `α` is a fraction of the gain `ν`, fixed before `δ`, and `c` is
`3` for the ball estimate and `2` for the multiplicity bound. -/
theorem exists_ssfGridLen_rpow_threshold (c α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : NNReal, 0 < δ → δ ≤ δ₀ →
        δ ^ (-c / (ssfGridLen δ : ℝ)) ≤ δ ^ (-α) := by
  rcases exists_ssfGridLen_threshold (max c α) α hα with ⟨δ₀, hδ0, hδ01, hthr⟩
  refine ⟨δ₀, hδ0, hδ01, ?_⟩
  intro δ hδ hδle
  have hδ1 : δ ≤ 1 := le_trans hδle hδ01
  have hm : max c α ≤ α * (ssfGridLen δ : ℝ) := hthr δ hδ hδle
  have ha : α ≤ α * (ssfGridLen δ : ℝ) := le_trans (le_max_right c α) hm
  have hlenposN : 0 < ssfGridLen δ := by
    have hone : (1 : ℝ) ≤ (ssfGridLen δ : ℝ) := by
      nlinarith
    have h1n : (1 : ℕ) ≤ ssfGridLen δ := by exact_mod_cast hone
    omega
  have hc : c ≤ α * (ssfGridLen δ : ℝ) := le_trans (le_max_left c α) hm
  exact rpow_neg_div_le_rpow_neg hδ hδ1 (N := ssfGridLen δ) hlenposN hc

/-- The filter form of `Kakeya.StickyKakeya.exists_ssfGridLen_rpow_threshold`: for every fixed
`α > 0` the grid step is eventually, as `δ → 0⁺`, cheaper than `δ^{-α}`. -/
theorem eventually_ssfGridLen_rpow_le (c α : ℝ) (hα : 0 < α) :
    ∀ᶠ δ : NNReal in nhdsWithin 0 (Set.Ioi 0),
      δ ^ (-c / (ssfGridLen δ : ℝ)) ≤ δ ^ (-α) := by
  obtain ⟨δ₀, hδ₀, _, hmain⟩ := exists_ssfGridLen_rpow_threshold c α hα
  filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hδ₀)] with δ hδpos hδlt
  exact hmain δ hδpos (le_of_lt hδlt)

end StickyKakeya
