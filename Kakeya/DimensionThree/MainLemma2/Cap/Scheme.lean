/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Cap.CapLemma

/-!
# The cap level scheme, and the Cap Lemma modulo the seam (band item A7, part 1)

This file is the **producer of `Kakeya.ML2Cap.CapScheme`** that band item A6
(`Cap/CapLemma.lean`) left open, and with it the Cap Lemma `L(γ) ⇒ K_KT(γ)`
 modulo one named hypothesis.

## The four obligations A6 enumerated

A6's module docstring lists exactly what a scheme producer must still supply.  Three of the four
are discharged here:

1. **the scale sequence `δ_k`** — `Kakeya.ML2Cap.capLevelScale`, band item A5's
   `Kakeya.CapRescale.capScale` iterated: `δ_{k+1} = δ_k / (K_c δ_k^c)`, which at `K_c = 16` is
   A5's `capScale (4 θ_ang) δ_k = δ_k / (16 θ_ang)` at `θ_ang = δ_k^c`, i.e. the plan's
   `δ_k^{1-c}/16` (`Kakeya.ML2Cap.capScaleStep_eq_rpow`).  The two bounds `δ ≤ δ_k ≤ δ^{(1-c)^k}`
   are `Kakeya.ML2Cap.le_capLevelScale` and `Kakeya.ML2Cap.capLevelScale_le_rpow`.  The upper one
   is free (each step divides by `K_c ≥ 1`); the lower one is **not** — it needs the single
   eventual absorption `K_c δ^t ≤ 1` at `t = c (1-c)^{k*}`, and it is proved through the exponent
   sequence `Kakeya.ML2Cap.capLevelExp`, `b_0 = 1`, `b_{k+1} = b_k(1-c) + t`, whose two bounds
   `b_k ≤ 1` (`Kakeya.ML2Cap.capLevelExp_le_one`) and `b_k ≤ (1-c)^k + t/c`
   (`Kakeya.ML2Cap.capLevelExp_le_add`) are exactly the two places the scale sequence is read:
   `b_k ≤ 1` gives `δ ≤ δ_k`, which `Kakeya.ML2Cap.capFactor_large` demands, and
   `b_{k*} ≤ 2 (1-c)^{k*}` gives the bottom level's `δ^{2(1-c)^{k*}} ≤ δ_{k*}`, which
   `Kakeya.ML2Cap.capBottom_cond` demands at `a = 2(1-c)^{k*}`.  **The factor `2` there is why the
   depth is taken at `ε/4` and not at `ε/2`**: the `1/K_c` per level costs the bottom level one
   doubling of its exponent, and nothing else in the accounting notices.
2. **the Katz--Tao and fullness sequences** `C₁^k δ^{-η}` and `c₁^k δ^{η}`
   (`Kakeya.ML2Cap.capLevel`), with the eventual absorptions `C₁^{k*} ≤ δ^{-η}` and
   `c₁^{-k*} ≤ δ^{-η}` — both instances of the one threshold lemma
   `Kakeya.ML2Cap.eventually_mul_rpow_le_one`, as is the third absorption
   `C₃ c₁^{-2k*} ≤ δ^{-η}` that the broad case needs.  The drift condition
   (`Kakeya.ML2Cap.Arith.drift`'s inequality, in the form `2η ≤ (1-c)^k η_L`) is
   `Kakeya.ML2Cap.two_capEta_le`, and the accuracy condition `3η ≤ ε/2` is
   `Kakeya.ML2Cap.three_capEta_le`; both are read at A6's own
   `η = Kakeya.ML2Cap.capEta γ η_L k*` and neither needs any hypothesis on `η_L` beyond
   positivity, because `min η_L (3γ/4) ≤ 3/4`.
3. **the availability of `L(γ) at every level scale`** —
   `Kakeya.StickyKakeya.exists_threshold_of_eventually_nhdsGT` turns A6's
   `∀ᶠ d, LargeOneAt E d (ε/2) γ η_L` into a threshold `d₀`, and
   `δ_k ≤ δ^{(1-c)^k} ≤ δ^{(1-c)^{k*}} ≤ d₀` puts every level inside it.

The fourth, **the seam**, is `Kakeya.ML2Cap.CapSeamOn`, assumed.  It is the composite of band
item A5 (`Kakeya.CapRescale.exists_capRescaledFamily`) with the A4-to-A5 column bridge; the exact
statement assumed is the definition below.

## What is *not* spent

Following A6's finding, the positive power `δ_k^{γ-c}` of the broad bound is used only through
`Kakeya.ML2Cap.capFactor_broad`, i.e. only as `≤ 1`; the `ε/2` half of the outer budget pays for
`C₃` and `λ_k^{-2}` on its own.  Nothing here moves the per-level fullness or `Δ_max` losses out
of the seam, so the slack A6 recorded stays slack.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Cap

universe u v

/-! ## 1. The one eventual-threshold lemma -/

/-- **The eventual threshold the scheme producer runs on.**  For every positive exponent `p` and
every real `M`, `M · δ^p ≤ 1` for all small `δ`, together with `0 < δ ≤ 1`. -/
theorem eventually_mul_rpow_le_one {p : ℝ} (hp : 0 < p) (M : ℝ) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), 0 < δ ∧ (δ : ℝ) ≤ 1 ∧ M * (δ : ℝ) ^ p ≤ 1 := by
  set A : ℝ := max M 1 with hA
  have hA1 : (1 : ℝ) ≤ A := le_max_right _ _
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA1
  have hAi0 : (0 : ℝ) ≤ A⁻¹ := by positivity
  set r : ℝ := min ((A⁻¹) ^ (1 / p)) 1 with hr
  have hrp0 : (0 : ℝ) < (A⁻¹) ^ (1 / p) := Real.rpow_pos_of_pos (by positivity) _
  have hr0 : 0 < r := lt_min hrp0 zero_lt_one
  have hr1 : r ≤ 1 := min_le_right _ _
  have hrn0 : (0 : NNReal) < r.toNNReal := Real.toNNReal_pos.mpr hr0
  filter_upwards [Ioo_mem_nhdsGT hrn0] with δ hδ
  obtain ⟨hδ0, hδr⟩ := hδ
  have hδr' : (δ : ℝ) ≤ r := by
    have h := NNReal.coe_le_coe.mpr hδr.le
    rwa [Real.coe_toNNReal r hr0.le] at h
  refine ⟨hδ0, le_trans hδr' hr1, ?_⟩
  have hpow : (δ : ℝ) ^ p ≤ A⁻¹ := by
    refine (Real.rpow_le_rpow (by positivity) hδr' hp.le).trans ?_
    calc r ^ p ≤ ((A⁻¹) ^ (1 / p)) ^ p := Real.rpow_le_rpow hr0.le (min_le_left _ _) hp.le
      _ = A⁻¹ := by
          rw [← Real.rpow_mul hAi0, one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]
  have hMA : M ≤ A := le_max_left _ _
  have hpow0 : (0 : ℝ) ≤ (δ : ℝ) ^ p := Real.rpow_nonneg (by positivity) _
  calc M * (δ : ℝ) ^ p ≤ A * (δ : ℝ) ^ p := by nlinarith
    _ ≤ A * A⁻¹ := by nlinarith
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hA0)

/-! ## 2. The scale sequence -/

/-- **One step of the cap scale sequence**, in the form band item A5 delivers it:
`Kakeya.CapRescale.capScale (4 θ) d = d / (16 θ)` at angular scale `θ = d^c`, i.e.
`d ↦ d / (K_c · d^c)` with `K_c = 16`. -/
noncomputable def capScaleStep (Kc : NNReal) (c : ℝ) (d : NNReal) : NNReal := d / (Kc * d ^ c)

/-- The power form of the step, `d^{1-c} / K_c` — 's
`δ_{k+1} = δ_k^{1-c}/16`. -/
theorem capScaleStep_eq_rpow {Kc : NNReal} {c : ℝ} {d : NNReal} (hd : d ≠ 0) :
    capScaleStep Kc c d = d ^ (1 - c) / Kc := by
  rw [capScaleStep, NNReal.rpow_sub hd, NNReal.rpow_one, div_div, mul_comm (d ^ c) Kc]

/-- **The scale sequence of the cap induction**, `δ_0 = δ` and `δ_{k+1} = δ_k / (K_c δ_k^c)`. -/
noncomputable def capLevelScale (Kc : NNReal) (c : ℝ) (δ : NNReal) : ℕ → NNReal
  | 0 => δ
  | (k + 1) => capScaleStep Kc c (capLevelScale Kc c δ k)

@[simp] theorem capLevelScale_zero (Kc : NNReal) (c : ℝ) (δ : NNReal) :
    capLevelScale Kc c δ 0 = δ := rfl

theorem capLevelScale_succ (Kc : NNReal) (c : ℝ) (δ : NNReal) (k : ℕ) :
    capLevelScale Kc c δ (k + 1) = capScaleStep Kc c (capLevelScale Kc c δ k) := rfl

/-- Every level scale is positive. -/
theorem capLevelScale_pos {Kc : NNReal} {c : ℝ} {δ : NNReal} (hKc : 1 ≤ Kc) (hδ0 : 0 < δ) :
    ∀ k : ℕ, 0 < capLevelScale Kc c δ k := by
  intro k
  induction k with
  | zero => simpa using hδ0
  | succ j ihj =>
    rw [capLevelScale_succ, capScaleStep_eq_rpow (ne_of_gt ihj)]
    exact div_pos (NNReal.rpow_pos ihj) (lt_of_lt_of_le zero_lt_one hKc)

/-- **The upper bound on the scale sequence**, `δ_k ≤ δ^{(1-c)^k}`: each step raises to the
power `1-c` and then *divides* by `K_c ≥ 1`. -/
theorem capLevelScale_le_rpow {Kc : NNReal} {c : ℝ} {δ : NNReal} (hKc : 1 ≤ Kc)
    (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1) (_hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∀ k : ℕ, capLevelScale Kc c δ k ≤ δ ^ ((1 - c) ^ k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hd0 : (0 : NNReal) < capLevelScale Kc c δ k := capLevelScale_pos hKc hδ0 k
    rw [capLevelScale_succ, capScaleStep_eq_rpow (ne_of_gt hd0)]
    have h1c : (0 : ℝ) ≤ 1 - c := by linarith
    calc capLevelScale Kc c δ k ^ (1 - c) / Kc
        ≤ capLevelScale Kc c δ k ^ (1 - c) / 1 := by gcongr
      _ = capLevelScale Kc c δ k ^ (1 - c) := by rw [div_one]
      _ ≤ (δ ^ ((1 - c) ^ k)) ^ (1 - c) := NNReal.rpow_le_rpow ih h1c
      _ = δ ^ ((1 - c) ^ (k + 1)) := by
          rw [← NNReal.rpow_mul, pow_succ]

/-! ## 3. The exponent sequence that bounds the scales from below -/

/-- **The exponent sequence of the lower bound**, `b_0 = 1`, `b_{k+1} = b_k (1-c) + t`, where `t`
is the exponent the eventual absorption `K_c δ^t ≤ 1` is read at. -/
noncomputable def capLevelExp (c t : ℝ) : ℕ → ℝ
  | 0 => 1
  | (k + 1) => capLevelExp c t k * (1 - c) + t

@[simp] theorem capLevelExp_zero (c t : ℝ) : capLevelExp c t 0 = 1 := rfl

theorem capLevelExp_succ (c t : ℝ) (k : ℕ) :
    capLevelExp c t (k + 1) = capLevelExp c t k * (1 - c) + t := rfl

/-- `b_k ≤ 1` whenever `t ≤ c`: this is what gives `δ ≤ δ_k`, the hypothesis
`Kakeya.ML2Cap.capFactor_large` reads. -/
theorem capLevelExp_le_one {c t : ℝ} (hc1 : c ≤ 1) (ht : t ≤ c) :
    ∀ k : ℕ, capLevelExp c t k ≤ 1 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [capLevelExp_succ]
    nlinarith [sub_nonneg.mpr hc1]

/-- `b_k ≤ (1-c)^k + t/c`, the closed-form bound; at `t = c (1-c)^{k*}` it gives
`b_{k*} ≤ 2 (1-c)^{k*}`, which is what the bottom level needs. -/
theorem capLevelExp_le_add {c t : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) :
    ∀ k : ℕ, capLevelExp c t k ≤ (1 - c) ^ k + t / c := by
  intro k
  induction k with
  | zero =>
    have : (0 : ℝ) ≤ t / c := by positivity
    simpa using this
  | succ k ih =>
    have h1c : (0 : ℝ) ≤ 1 - c := by linarith
    have hid : ((1 - c) ^ k + t / c) * (1 - c) + t = (1 - c) ^ (k + 1) + t / c := by
      field_simp
      ring
    calc capLevelExp c t (k + 1) = capLevelExp c t k * (1 - c) + t := capLevelExp_succ c t k
      _ ≤ ((1 - c) ^ k + t / c) * (1 - c) + t := by nlinarith
      _ = (1 - c) ^ (k + 1) + t / c := hid

/-- **The lower bound on the scale sequence**, `δ^{b_k} ≤ δ_k`, under the single eventual
absorption `K_c · δ^t ≤ 1`. -/
theorem rpow_capLevelExp_le {Kc : NNReal} {c t : ℝ} {δ : NNReal} (hKc : 1 ≤ Kc)
    (hδ0 : 0 < δ) (hc1 : c ≤ 1) (habs : Kc * δ ^ t ≤ 1) :
    ∀ k : ℕ, δ ^ (capLevelExp c t k) ≤ capLevelScale Kc c δ k := by
  have hKc0 : Kc ≠ 0 := by
    intro h; rw [h] at hKc; simp at hKc
  have h1c : (0 : ℝ) ≤ 1 - c := by linarith
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hd0 : (0 : NNReal) < capLevelScale Kc c δ k := capLevelScale_pos hKc hδ0 k
    have hKcpos : (0 : NNReal) < Kc := lt_of_lt_of_le zero_lt_one hKc
    rw [capLevelScale_succ, capScaleStep_eq_rpow (ne_of_gt hd0), le_div_iff₀ hKcpos,
      capLevelExp_succ, NNReal.rpow_add (ne_of_gt hδ0)]
    calc δ ^ (capLevelExp c t k * (1 - c)) * δ ^ t * Kc
        = δ ^ (capLevelExp c t k * (1 - c)) * (Kc * δ ^ t) := by ring
      _ ≤ δ ^ (capLevelExp c t k * (1 - c)) * 1 := by gcongr
      _ = (δ ^ (capLevelExp c t k)) ^ (1 - c) := by rw [mul_one, NNReal.rpow_mul]
      _ ≤ capLevelScale Kc c δ k ^ (1 - c) := NNReal.rpow_le_rpow ih h1c

/-- `δ ≤ δ_k` for every level: the hypothesis of `Kakeya.ML2Cap.capFactor_large`. -/
theorem le_capLevelScale {Kc : NNReal} {c t : ℝ} {δ : NNReal} (hKc : 1 ≤ Kc)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : c ≤ 1) (ht : t ≤ c) (habs : Kc * δ ^ t ≤ 1) (k : ℕ) :
    δ ≤ capLevelScale Kc c δ k := by
  refine le_trans ?_ (rpow_capLevelExp_le hKc hδ0 hc1 habs k)
  have h := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (capLevelExp_le_one hc1 ht k)
  simpa using h

/-! ## 4. The `capEta` budget inequalities -/

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `2 η ≤ (1-c)^k η_L` for every level `k ≤ k*`, at `η = capEta γ η_L k*`: this is the drift
condition 's `Kakeya.ML2Cap.Arith.drift`, in the form the level's
Katz--Tao and fullness bounds need. -/
theorem two_capEta_le {γ ηL : ℝ} {K k : ℕ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hηL : 0 < ηL)
    (hk : k ≤ K) : 2 * capEta γ ηL K ≤ (1 - γ / 4) ^ k * ηL := by
  have h1 : (0 : ℝ) ≤ 1 - γ / 4 := by nlinarith
  have h1' : (1 - γ / 4) ≤ 1 := by nlinarith
  have hmono : (1 - γ / 4) ^ K ≤ (1 - γ / 4) ^ k := pow_le_pow_of_le_one h1 h1' hk
  have hmin : min ηL (3 * γ / 4) ≤ ηL := min_le_left _ _
  have hminpos : (0 : ℝ) < min ηL (3 * γ / 4) := lt_min hηL (by nlinarith)
  have hKpos : (0 : ℝ) ≤ (1 - γ / 4) ^ K := pow_nonneg h1 K
  have hkpos : (0 : ℝ) ≤ (1 - γ / 4) ^ k := pow_nonneg h1 k
  rw [capEta]
  have hstep : (1 - γ / 4) ^ K * min ηL (3 * γ / 4) ≤ (1 - γ / 4) ^ k * ηL := by
    calc (1 - γ / 4) ^ K * min ηL (3 * γ / 4) ≤ (1 - γ / 4) ^ k * min ηL (3 * γ / 4) := by
          exact mul_le_mul_of_nonneg_right hmono hminpos.le
      _ ≤ (1 - γ / 4) ^ k * ηL := by exact mul_le_mul_of_nonneg_left hmin hkpos
  have hX : (0 : ℝ) ≤ (1 - γ / 4) ^ K * min ηL (3 * γ / 4) := by positivity
  linarith

/-- `3 η ≤ ε/2` at `η = capEta γ η_L k*` and depth `(1-γ/4)^{k*} ≤ ε/4`: the accuracy budget of
the broad case, where the level's fullness floor `λ_k^{-2}` is paid.  The bound uses
`min η_L (3γ/4) ≤ 3/4` only, so it is independent of `η_L`. -/
theorem three_capEta_le {γ ε ηL : ℝ} {K : ℕ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hηL : 0 < ηL)
    (hdepth : (1 - γ / 4) ^ K ≤ ε / 4) : 3 * capEta γ ηL K ≤ ε / 2 := by
  have h1 : (0 : ℝ) ≤ 1 - γ / 4 := by nlinarith
  have hKpos : (0 : ℝ) ≤ (1 - γ / 4) ^ K := pow_nonneg h1 K
  have hminpos : (0 : ℝ) < min ηL (3 * γ / 4) := lt_min hηL (by nlinarith)
  have hmin : min ηL (3 * γ / 4) ≤ 3 / 4 := le_trans (min_le_right _ _) (by nlinarith)
  have hstep : (1 - γ / 4) ^ K * min ηL (3 * γ / 4) ≤ (ε / 4) * (3 / 4) := by
    calc (1 - γ / 4) ^ K * min ηL (3 * γ / 4) ≤ (ε / 4) * min ηL (3 * γ / 4) :=
          mul_le_mul_of_nonneg_right hdepth hminpos.le
      _ ≤ (ε / 4) * (3 / 4) := by
          have hε4 : (0 : ℝ) ≤ ε / 4 := le_trans hKpos hdepth
          exact mul_le_mul_of_nonneg_left hmin hε4
  rw [capEta]
  linarith

/-! ## 5. The level data of the scheme -/

/-- **The level data of the cap induction.**  The scale is `Kakeya.ML2Cap.capLevelScale`; the
Katz--Tao bound and fullness floor drift by the fixed absolute constants `C₁` and `c₁` per level
(band item A5's `Kakeya.CapRescale.capLoss` and A4's `8 C_P` times it); the budget is band item
A6's canonical `Kakeya.ML2Cap.capFactor`. -/
noncomputable def capLevel (Kc C₁ c₁ : NNReal) (c ε η : ℝ) (K : ℕ) (δ : NNReal) (k : ℕ) :
    LevelData where
  scale := capLevelScale Kc c δ k
  ktBound := (C₁ : ENNReal) ^ k * (δ : ENNReal) ^ (-η)
  full := c₁ ^ k * δ ^ η
  factor := capFactor δ ε K k

@[simp] theorem capLevel_scale (Kc C₁ c₁ : NNReal) (c ε η : ℝ) (K : ℕ) (δ : NNReal) (k : ℕ) :
    (capLevel Kc C₁ c₁ c ε η K δ k).scale = capLevelScale Kc c δ k := rfl

@[simp] theorem capLevel_ktBound (Kc C₁ c₁ : NNReal) (c ε η : ℝ) (K : ℕ) (δ : NNReal) (k : ℕ) :
    (capLevel Kc C₁ c₁ c ε η K δ k).ktBound = (C₁ : ENNReal) ^ k * (δ : ENNReal) ^ (-η) := rfl

@[simp] theorem capLevel_full (Kc C₁ c₁ : NNReal) (c ε η : ℝ) (K : ℕ) (δ : NNReal) (k : ℕ) :
    (capLevel Kc C₁ c₁ c ε η K δ k).full = c₁ ^ k * δ ^ η := rfl

@[simp] theorem capLevel_factor (Kc C₁ c₁ : NNReal) (c ε η : ℝ) (K : ℕ) (δ : NNReal) (k : ℕ) :
    (capLevel Kc C₁ c₁ c ε η K δ k).factor = capFactor δ ε K k := rfl

/-! ## 6. The seam, as a hypothesis on consecutive levels -/

/-- **The cap-rescaling seam of band item A6, read on the consecutive levels of a scheme.**

`Kakeya.ML2Cap.CapSeam` is A6's named `Prop`; this is the statement that it holds for *every*
pair of levels related as the scheme relates them — the scale by one `Kakeya.ML2Cap.capScaleStep`,
the Katz--Tao bound up by `C₁` and the fullness floor down by `c₁`.  It is the composite of band
item A5 (`Kakeya.CapRescale.exists_capRescaledFamily`, whose losses are `C₁ = capLoss` on both
`Δ_max` and fullness) with the A4-to-A5 column bridge (`Kakeya.CapColumn`, whose fullness cost is
the factor `18 = 2 · 9` and whose multiplicity cost is the factor `2` that
`Kakeya.ML2Cap.CapSeam`'s conclusion already carries).  At the existing constants,
`Kc = 16`, `C₁ = capLoss` and `c₁ = (8 · C_P · 18 · capLoss)⁻¹`.

The side condition `4 δ_k^c ≤ 1` is **not decoration**: it is A5's `hθ1 : θ ≤ 1` read at the cap
radius `θ = 4 δ_k^c`, and at cap radius `4 θ_ang` it is genuinely a condition on the scale rather
than a consequence of `δ_k ≤ 1`.  `Kakeya.ML2Cap.exists_capScheme` discharges it from the same
eventual absorption that carries the scale sequence's lower bound, so it costs a call site
nothing. -/
def CapSeamOn (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (γ c : ℝ) (Kc C₁ c₁ : NNReal) : Prop :=
  ∀ L L' : LevelData, 0 < L.scale → L.scale ≤ 1 → 0 < L.full →
    4 * ((L.scale : NNReal) : ℝ) ^ c ≤ 1 →
    L'.scale = capScaleStep Kc c L.scale →
    L'.ktBound = (C₁ : ENNReal) * L.ktBound →
    L'.full = c₁ * L.full →
    CapSeam.{u} E L L' γ c

/-! ## 7. The scheme producer -/

set_option maxHeartbeats 1000000 in
-- The `whnf`/`isDefEq` cost is concentrated in the `factor_broad` field, whose goal carries
-- three `Real.rpow`s of compound exponents at once; the budget is raised rather than the proof
-- restructured, since every step of it is already a named lemma application.
/-- **The producer of cap level schemes** — the four obligations band item A6 left open, with the
seam as the single named hypothesis.

* the **scale sequence** is `Kakeya.ML2Cap.capLevelScale`, and
  `Kakeya.ML2Cap.le_capLevelScale` / `Kakeya.ML2Cap.capLevelScale_le_rpow` are the two bounds
  `δ ≤ δ_k ≤ δ^{(1-c)^k}`;
* the **Katz--Tao and fullness sequences** are `C₁^k δ^{-η}` and `c₁^k δ^{η}`, and the two
  eventual absorptions `C₁^{k*} ≤ δ^{-η}` and `c₁^{-k*} ≤ δ^{-η}` are instances of
  `Kakeya.ML2Cap.eventually_mul_rpow_le_one`;
* the **availability of `L(γ)` at every level scale** comes from
  `Kakeya.StickyKakeya.exists_threshold_of_eventually_nhdsGT` together with
  `δ_k ≤ δ^{(1-c)^{k*}} ≤ d₀`;
* the **seam** is `Kakeya.ML2Cap.CapSeamOn`, assumed. -/
theorem exists_capScheme {γ ε ηL C₃ : ℝ} {Kc C₁ c₁ : NNReal}
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) (hηL : 0 < ηL) (hC₃ : 0 < C₃)
    (hKc : 1 ≤ Kc) (hC₁ : 1 ≤ C₁) (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1)
    (hseam : CapSeamOn.{u} E γ (γ / 4) Kc C₁ c₁)
    (hev : ∀ᶠ (d : NNReal) in 𝓝[>] 0, LargeOneAt.{u} E d (ε / 2) γ ηL) :
    ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      Nonempty (CapScheme.{u} E γ ε η ηL C₃ δ) := by
  classical
  have hc0 : (0 : ℝ) < γ / 4 := by linarith
  have hcγ : γ / 4 ≤ γ := by linarith
  have hc1 : γ / 4 ≤ 1 := by linarith
  have h1c0 : (0 : ℝ) < 1 - γ / 4 := by linarith
  obtain ⟨K, hdep⟩ := exists_capDepth (γ := γ) (ε := ε / 2) hγ0 hγ1 (by linarith)
  have hdepth : (1 - γ / 4) ^ K ≤ ε / 4 := by linarith
  have hcK0 : (0 : ℝ) < (1 - γ / 4) ^ K := pow_pos h1c0 K
  have hcK1 : (1 - γ / 4) ^ K ≤ 1 := pow_le_one₀ h1c0.le (by linarith)
  obtain ⟨η, hη0, hηtwo, hηthree⟩ :
      ∃ η : ℝ, 0 < η ∧ (∀ k : ℕ, k ≤ K → 2 * η ≤ (1 - γ / 4) ^ k * ηL) ∧ 3 * η ≤ ε / 2 :=
    ⟨capEta γ ηL K, capEta_pos hγ0 hγ1 hηL,
      fun k hk => two_capEta_le hγ0 hγ1 hηL hk, three_capEta_le hγ0 hγ1 hηL hdepth⟩
  refine ⟨η, hη0, ?_⟩
  have ht0 : (0 : ℝ) < γ / 4 * (1 - γ / 4) ^ K := by positivity
  have htc : γ / 4 * (1 - γ / 4) ^ K ≤ γ / 4 := by nlinarith
  obtain ⟨d₀, hd₀0, hd₀⟩ := Kakeya.StickyKakeya.exists_threshold_of_eventually_nhdsGT hev
  have hd₀r : (0 : ℝ) < (d₀ : ℝ) := by exact_mod_cast hd₀0
  have hr16 : (0 : NNReal) < Real.toNNReal ((16 : ℝ) ^ (-(2 * (K : ℝ) / ε))) :=
    Real.toNNReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)
  filter_upwards [eventually_mul_rpow_le_one ht0 ((Kc : ℝ)),
    eventually_mul_rpow_le_one ht0 (4 : ℝ),
    eventually_mul_rpow_le_one hcK0 ((d₀ : ℝ)⁻¹),
    eventually_mul_rpow_le_one hη0 ((C₁ : ℝ) ^ K),
    eventually_mul_rpow_le_one hη0 (((c₁ : ℝ) ^ K)⁻¹),
    eventually_mul_rpow_le_one hη0 (C₃ * (((c₁ : ℝ) ^ K) ^ 2)⁻¹),
    Ioo_mem_nhdsGT hr16] with δ hA hA4 hB hC hD hF hG
  obtain ⟨hδ0, hδ1r, hAbs⟩ := hA
  have hδ0r : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδ1 : δ ≤ 1 := by exact_mod_cast hδ1r
  have hδη0 : (0 : ℝ) < (δ : ℝ) ^ η := Real.rpow_pos_of_pos hδ0r η
  -- the NNReal form of the scale absorption
  have hAbsN : Kc * δ ^ (γ / 4 * (1 - γ / 4) ^ K) ≤ 1 := by
    have h : ((Kc * δ ^ (γ / 4 * (1 - γ / 4) ^ K) : NNReal) : ℝ) ≤ ((1 : NNReal) : ℝ) := by
      simpa [NNReal.coe_rpow] using hAbs
    exact_mod_cast h
  -- the three basic scale bounds
  have hspos : ∀ k : ℕ, 0 < capLevelScale Kc (γ / 4) δ k :=
    fun k => capLevelScale_pos hKc hδ0 k
  have hsposr : ∀ k : ℕ, (0 : ℝ) < ((capLevelScale Kc (γ / 4) δ k : NNReal) : ℝ) :=
    fun k => by exact_mod_cast hspos k
  have hsup : ∀ k : ℕ, capLevelScale Kc (γ / 4) δ k ≤ δ ^ ((1 - γ / 4) ^ k) :=
    fun k => capLevelScale_le_rpow hKc hδ0 hδ1 hc0.le hc1 k
  have hslo : ∀ k : ℕ, δ ≤ capLevelScale Kc (γ / 4) δ k :=
    fun k => le_capLevelScale hKc hδ0 hδ1 hc1 htc hAbsN k
  have hsle1 : ∀ k : ℕ, capLevelScale Kc (γ / 4) δ k ≤ 1 := fun k =>
    le_trans (hsup k) (NNReal.rpow_le_one hδ1 (pow_nonneg h1c0.le k))
  have hexpmono : ∀ k : ℕ, k ≤ K → ((1 : ℝ) - γ / 4) ^ K ≤ (1 - γ / 4) ^ k :=
    fun k hk => pow_le_pow_of_le_one h1c0.le (by linarith) hk
  -- the cap-radius side condition of A5, at every level
  have hrad : ∀ k : ℕ, k ≤ K →
      4 * ((capLevelScale Kc (γ / 4) δ k : NNReal) : ℝ) ^ (γ / 4) ≤ 1 := by
    intro k hk
    refine le_trans ?_ hA4.2.2
    have hzu : ((capLevelScale Kc (γ / 4) δ k : NNReal) : ℝ)
        ≤ (δ : ℝ) ^ ((1 - γ / 4) ^ k) := by
      have h := NNReal.coe_le_coe.mpr (hsup k)
      simpa [NNReal.coe_rpow] using h
    have h1 : ((capLevelScale Kc (γ / 4) δ k : NNReal) : ℝ) ^ (γ / 4)
        ≤ ((δ : ℝ) ^ ((1 - γ / 4) ^ k)) ^ (γ / 4) :=
      Real.rpow_le_rpow (hsposr k).le hzu hc0.le
    have h2 : ((δ : ℝ) ^ ((1 - γ / 4) ^ k)) ^ (γ / 4)
        ≤ (δ : ℝ) ^ (γ / 4 * (1 - γ / 4) ^ K) := by
      rw [← Real.rpow_mul hδ0r.le]
      refine Real.rpow_le_rpow_of_exponent_ge hδ0r hδ1r ?_
      have := hexpmono k hk
      nlinarith
    have := le_trans h1 h2
    nlinarith [Real.rpow_nonneg hδ0r.le (γ / 4 * (1 - γ / 4) ^ K)]
  -- the inversion helper
  have hinv : ∀ M : ℝ, M * (δ : ℝ) ^ η ≤ 1 → M ≤ (δ : ℝ) ^ (-η) := by
    intro M h
    rw [Real.rpow_neg hδ0r.le, inv_eq_one_div, le_div_iff₀ hδη0]
    simpa using h
  have hmulinv : ∀ M p : ℝ, M * (δ : ℝ) ^ η ≤ 1 →
      M * (δ : ℝ) ^ (-p) ≤ (δ : ℝ) ^ (-(η + p)) := by
    intro M p h
    have h2 : (δ : ℝ) ^ (-(η + p)) = (δ : ℝ) ^ (-η) * (δ : ℝ) ^ (-p) := by
      rw [← Real.rpow_add hδ0r]; ring_nf
    rw [h2]
    exact mul_le_mul_of_nonneg_right (hinv M h) (Real.rpow_nonneg hδ0r.le _)
  -- `L(γ)` at every level scale
  have hd₀le : ∀ k : ℕ, k ≤ K → capLevelScale Kc (γ / 4) δ k ≤ d₀ := by
    intro k hk
    refine le_trans (hsup k) (le_trans
      (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (hexpmono k hk)) ?_)
    have h := hB.2.2
    have h2 := mul_le_mul_of_nonneg_left h hd₀r.le
    rw [mul_one, ← mul_assoc, mul_inv_cancel₀ hd₀r.ne', one_mul] at h2
    have : ((δ ^ ((1 - γ / 4) ^ K) : NNReal) : ℝ) ≤ ((d₀ : NNReal) : ℝ) := by
      simpa [NNReal.coe_rpow] using h2
    exact_mod_cast this
  have hlarge : ∀ k : ℕ, k ≤ K →
      LargeOneAt.{u} E (capLevelScale Kc (γ / 4) δ k) (ε / 2) γ ηL :=
    fun k hk => hd₀ (hspos k) (hd₀le k hk)
  -- the drift bound, in `ℝ`, that both `kt_le` and `full_ge` run on
  have hdriftR : ∀ k : ℕ, k ≤ K →
      ((capLevelScale Kc (γ / 4) δ k : NNReal) : ℝ) ^ ηL ≤ (δ : ℝ) ^ (2 * η) := by
    intro k hk
    have hzu : ((capLevelScale Kc (γ / 4) δ k : NNReal) : ℝ) ≤ (δ : ℝ) ^ ((1 - γ / 4) ^ k) := by
      have := NNReal.coe_le_coe.mpr (hsup k)
      simpa [NNReal.coe_rpow] using this
    have h1 : ((capLevelScale Kc (γ / 4) δ k : NNReal) : ℝ) ^ ηL
        ≤ ((δ : ℝ) ^ ((1 - γ / 4) ^ k)) ^ ηL :=
      Real.rpow_le_rpow (hsposr k).le hzu hηL.le
    refine h1.trans ?_
    rw [← Real.rpow_mul hδ0r.le]
    exact Real.rpow_le_rpow_of_exponent_ge hδ0r hδ1r
      (by have h := hηtwo k hk
          nlinarith)
  refine Nonempty.intro ?_
  refine
    { depth := K
      cexp := γ / 4
      level := capLevel Kc C₁ c₁ (γ / 4) ε η K δ
      cexp_nonneg := hc0.le
      cexp_le := hcγ
      scale_pos := fun k _ => hspos k
      scale_le_one := fun k _ => hsle1 k
      full_pos := ?_
      large := fun k hk => hlarge k hk
      kt_le := ?_
      full_ge := ?_
      factor_large := fun k _ => capFactor_large (hslo k) hε.le
      factor_broad := ?_
      seam := ?_
      factor_narrow := fun k hk => capFactor_narrow δ ε hk
      factor_bottom := ?_
      entry_scale := by simp
      entry_kt := by simp
      entry_full := by simp
      entry_factor := ?_ }
  · intro k _
    simp only [capLevel_full]
    have : (0 : NNReal) < c₁ ^ k * δ ^ η := by
      exact mul_pos (pow_pos hc₁0 k) (NNReal.rpow_pos hδ0)
    exact this
  · -- kt_le
    intro k hk
    simp only [capLevel_scale, capLevel_ktBound]
    have hC₁r : (1 : ℝ) ≤ (C₁ : ℝ) := by exact_mod_cast hC₁
    have hpowk : ((C₁ : ℝ)) ^ k ≤ ((C₁ : ℝ)) ^ K := pow_le_pow_right₀ hC₁r hk
    have hstep : ((C₁ : ℝ)) ^ k * (δ : ℝ) ^ (-η) ≤ (δ : ℝ) ^ (-(η + η)) := by
      refine le_trans ?_ (hmulinv (((C₁ : ℝ)) ^ K) η hC.2.2)
      exact mul_le_mul_of_nonneg_right hpowk (Real.rpow_nonneg hδ0r.le _)
    have hlast : (δ : ℝ) ^ (-(η + η))
        ≤ ((capLevelScale Kc (γ / 4) δ k : NNReal) : ℝ) ^ (-ηL) := by
      have hy0 : (0 : ℝ) < ((capLevelScale Kc (γ / 4) δ k : NNReal) : ℝ) := hsposr k
      have hd : ((capLevelScale Kc (γ / 4) δ k : NNReal) : ℝ) ^ ηL ≤ (δ : ℝ) ^ (η + η) := by
        have h := hdriftR k hk
        rwa [show (2 : ℝ) * η = η + η by ring] at h
      rw [Real.rpow_neg hy0.le, Real.rpow_neg hδ0r.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hy0 ηL) hd
    have hcoeC : ((C₁ : ENNReal)) ^ k = ENNReal.ofReal (((C₁ : ℝ)) ^ k) := by
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_coe_nnreal]
    rw [hcoeC, coe_rpow_eq_ofReal hδ0, coe_rpow_eq_ofReal (hspos k),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (le_trans hstep hlast)
  · -- full_ge
    intro k hk
    simp only [capLevel_scale, capLevel_full]
    have hpc : (δ : ℝ) ^ η ≤ ((c₁ : ℝ)) ^ k := by
      have h := hD.2.2
      have hcK : (0 : ℝ) < ((c₁ : ℝ)) ^ K := by
        have : (0 : ℝ) < (c₁ : ℝ) := by exact_mod_cast hc₁0
        positivity
      have h2 := mul_le_mul_of_nonneg_left h hcK.le
      rw [mul_one, ← mul_assoc, mul_inv_cancel₀ hcK.ne', one_mul] at h2
      refine h2.trans ?_
      have hc₁r : (0 : ℝ) ≤ (c₁ : ℝ) := by positivity
      have hc₁r1 : (c₁ : ℝ) ≤ 1 := by exact_mod_cast hc₁1
      exact pow_le_pow_of_le_one hc₁r hc₁r1 hk
    have hgoalR : ((capLevelScale Kc (γ / 4) δ k : NNReal) : ℝ) ^ ηL
        ≤ ((c₁ : ℝ)) ^ k * (δ : ℝ) ^ η := by
      refine (hdriftR k hk).trans ?_
      have hsplit : (δ : ℝ) ^ (2 * η) = (δ : ℝ) ^ η * (δ : ℝ) ^ η := by
        rw [← Real.rpow_add hδ0r]; ring_nf
      rw [hsplit]
      exact mul_le_mul_of_nonneg_right hpc hδη0.le
    have : ((capLevelScale Kc (γ / 4) δ k ^ ηL : NNReal) : ℝ)
        ≤ ((c₁ ^ k * δ ^ η : NNReal) : ℝ) := by
      simpa [NNReal.coe_rpow] using hgoalR
    exact_mod_cast this
  · -- factor_broad
    intro k hk
    simp only [capLevel_scale, capLevel_full, capLevel_factor]
    refine capFactor_broad (hspos k) (hsle1 k) hcγ hC₃.le hδ0 ?_
    have hc₁r : (0 : ℝ) < (c₁ : ℝ) := by exact_mod_cast hc₁0
    have hc₁r1 : (c₁ : ℝ) ≤ 1 := by exact_mod_cast hc₁1
    have hcoe : (((c₁ ^ k * δ ^ η : NNReal)) : ℝ) = ((c₁ : ℝ)) ^ k * (δ : ℝ) ^ η := by
      simp [NNReal.coe_rpow]
    rw [hcoe]
    have hδ2 : ((δ : ℝ) ^ η) ^ 2 = (δ : ℝ) ^ (2 * η) := by
      rw [← Real.rpow_natCast ((δ : ℝ) ^ η) 2, ← Real.rpow_mul hδ0r.le]
      congr 1
      push_cast
      ring
    have hkey : C₃ * ((((c₁ : ℝ)) ^ k * (δ : ℝ) ^ η) ^ 2)⁻¹
        = (C₃ * ((((c₁ : ℝ)) ^ k) ^ 2)⁻¹) * (δ : ℝ) ^ (-(2 * η)) := by
      rw [mul_pow, mul_inv, hδ2, ← Real.rpow_neg hδ0r.le]
      ring
    rw [hkey]
    have hmono : C₃ * ((((c₁ : ℝ)) ^ k) ^ 2)⁻¹ ≤ C₃ * ((((c₁ : ℝ)) ^ K) ^ 2)⁻¹ := by
      have h1 : ((c₁ : ℝ)) ^ K ≤ ((c₁ : ℝ)) ^ k := pow_le_pow_of_le_one hc₁r.le hc₁r1 hk
      have h2 : (0 : ℝ) < ((c₁ : ℝ)) ^ K := by positivity
      gcongr
    refine le_trans (mul_le_mul_of_nonneg_right hmono
      (Real.rpow_nonneg hδ0r.le (-(2 * η)))) ?_
    refine le_trans (hmulinv (C₃ * ((((c₁ : ℝ)) ^ K) ^ 2)⁻¹) (2 * η) hF.2.2) ?_
    exact Real.rpow_le_rpow_of_exponent_ge hδ0r hδ1r
      (by linarith)
  · -- seam
    intro k hk
    refine hseam _ _ (hspos k) (hsle1 k) ?_ ?_ ?_ ?_ ?_
    · simp only [capLevel_full]
      exact mul_pos (pow_pos hc₁0 k) (NNReal.rpow_pos hδ0)
    · simp only [capLevel_scale]
      exact hrad k hk.le
    · simp only [capLevel_scale]
      exact capLevelScale_succ Kc (γ / 4) δ k
    · simp only [capLevel_ktBound, pow_succ]
      ring
    · simp only [capLevel_full, pow_succ]
      ring
  · -- factor_bottom
    simp only [capLevel_scale, capLevel_factor]
    refine capFactor_bottom K hδ0 ?_
    refine capBottom_cond (a := 2 * (1 - γ / 4) ^ K) hδ0 hδ1r hγ1 ?_ ?_
    · have hb := rpow_capLevelExp_le (Kc := Kc) (c := γ / 4)
        (t := γ / 4 * (1 - γ / 4) ^ K) hKc hδ0 hc1 hAbsN K
      have hexp : capLevelExp (γ / 4) (γ / 4 * (1 - γ / 4) ^ K) K ≤ 2 * (1 - γ / 4) ^ K := by
        have h := capLevelExp_le_add (c := γ / 4) (t := γ / 4 * (1 - γ / 4) ^ K)
          hc0 hc1 ht0.le K
        have hid : γ / 4 * (1 - γ / 4) ^ K / (γ / 4) = (1 - γ / 4) ^ K := by
          field_simp
        rw [hid] at h
        linarith
      have hmono := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hexp
      have hfin : δ ^ (2 * (1 - γ / 4) ^ K) ≤ capLevelScale Kc (γ / 4) δ K :=
        le_trans hmono hb
      have := NNReal.coe_le_coe.mpr hfin
      simpa [NNReal.coe_rpow] using this
    · nlinarith
  · -- entry_factor
    simp only [capLevel_factor]
    refine capFactor_entry_of_le hδ0 hε ?_
    have h := NNReal.coe_le_coe.mpr hG.2.le
    rwa [Real.coe_toNNReal _ (Real.rpow_pos_of_pos (by norm_num) _).le] at h

/-! ## 8. The Cap Lemma, modulo the seam -/

/-- **The Cap Lemma `L(γ) ⇒ K_KT(γ)`, modulo the cap-rescaling seam.**

`Kakeya.ML2Cap.katzTaoEstimate_of_largeOne_of_scheme` reduces the Cap Lemma to a
*producer* of level schemes; `Kakeya.ML2Cap.exists_capScheme` is that producer.  The only
hypothesis neither file discharges is `Kakeya.ML2Cap.CapSeamOn`. -/
theorem katzTaoEstimate_of_largeOne_of_seam {γ : ℝ} {Kc C₁ c₁ : NNReal}
    (hn : 1 < Module.finrank ℝ E) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hKc : 1 ≤ Kc) (hC₁ : 1 ≤ C₁) (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1)
    (hseam : CapSeamOn.{u} E γ (γ / 4) Kc C₁ c₁)
    (hL : KatzTaoEstimateLargeOne.{u} E γ) : KatzTaoEstimate.{u} E γ :=
  katzTaoEstimate_of_largeOne_of_scheme hn hγ1 hL
    (fun _ε hε _ηL _C₃ hηL hC₃ _hB hev =>
      exists_capScheme hγ0 hγ1 hε hηL hC₃ hKc hC₁ hc₁0 hc₁1 hseam hev)

end Kakeya.ML2Cap

end
