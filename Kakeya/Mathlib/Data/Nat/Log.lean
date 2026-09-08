/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Comparing `Nat.log 2` with the real logarithm

Bridging lemmas between the dyadic `Nat.log 2` used by pigeonholing arguments and the real
logarithm used by the analytic estimates.

Also the *dyadic band* itself: a positive quantity is bracketed between `2 ^ k` and `2 ^ (k + 1)`
for `k` its base-`2` logarithm.  Both halves are wanted together at every use, so they are stated
as one conjunction rather than as the two Mathlib facts `Nat.pow_log_le_self` and
`Nat.lt_pow_succ_log_self` they are proved from.
-/

@[expose] public section

/-- A positive natural number lies in the dyadic band cut out by its base-`2` logarithm. -/
theorem Nat.dyadic_band {c : ℕ} (hc : 0 < c) :
    2 ^ Nat.log 2 c ≤ c ∧ c ≤ 2 * 2 ^ Nat.log 2 c := by
  constructor
  · exact Nat.pow_log_le_self 2 hc.ne'
  · calc
      c ≤ 2 ^ (Nat.log 2 c + 1) := le_of_lt (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) c)
      _ = 2 * 2 ^ Nat.log 2 c := by rw [pow_succ, mul_comm]

/-- An extended real in `[1, ∞)` lies in the dyadic band cut out by the base-`2` logarithm of its
integer part. -/
theorem ENNReal.dyadic_band {x : ENNReal} (hx : 1 ≤ x) (hx' : x ≠ ⊤) :
    (2 : ENNReal) ^ Nat.log 2 ⌊x.toReal⌋₊ ≤ x ∧
      x ≤ 2 * (2 : ENNReal) ^ Nat.log 2 ⌊x.toReal⌋₊ := by
  have hr : 0 ≤ x.toReal := ENNReal.toReal_nonneg
  have h1r : (1 : ℝ) ≤ x.toReal := by
    have h1 : (1 : ℝ) = (1 : ENNReal).toReal := by simp
    calc
      (1 : ℝ) = (1 : ENNReal).toReal := h1
      _ ≤ x.toReal := ENNReal.toReal_mono hx' hx
  have h1c : (1 : ℕ) ≤ ⌊x.toReal⌋₊ := Nat.le_floor (by simpa using h1r)
  have hpowle : (2 : ℝ) ^ Nat.log 2 ⌊x.toReal⌋₊ ≤ x.toReal := by
    calc
      (2 : ℝ) ^ Nat.log 2 ⌊x.toReal⌋₊ ≤ (⌊x.toReal⌋₊ : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega : ⌊x.toReal⌋₊ ≠ 0)
      _ ≤ x.toReal := Nat.floor_le hr
  have hsumle : (⌊x.toReal⌋₊ : ℝ) + 1 ≤ 2 * (2 : ℝ) ^ Nat.log 2 ⌊x.toReal⌋₊ := by
    have hlt : ⌊x.toReal⌋₊ < 2 ^ (Nat.log 2 ⌊x.toReal⌋₊ + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊x.toReal⌋₊
    have hs : ⌊x.toReal⌋₊ + 1 ≤ 2 * 2 ^ Nat.log 2 ⌊x.toReal⌋₊ := by
      calc
        ⌊x.toReal⌋₊ + 1 ≤ 2 ^ (Nat.log 2 ⌊x.toReal⌋₊ + 1) := Nat.succ_le_of_lt hlt
        _ = 2 * 2 ^ Nat.log 2 ⌊x.toReal⌋₊ := by rw [pow_succ, mul_comm]
    exact_mod_cast hs
  constructor
  · calc
      (2 : ENNReal) ^ Nat.log 2 ⌊x.toReal⌋₊
          = ENNReal.ofReal ((2 : ℝ) ^ Nat.log 2 ⌊x.toReal⌋₊) := by
        rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num]
        rw [← ENNReal.ofReal_pow (by norm_num : 0 ≤ (2 : ℝ))]
      _ ≤ ENNReal.ofReal x.toReal := ENNReal.ofReal_le_ofReal hpowle
      _ = x := ENNReal.ofReal_toReal hx'
  · calc
      x = ENNReal.ofReal x.toReal := (ENNReal.ofReal_toReal hx').symm
      _ ≤ ENNReal.ofReal ((⌊x.toReal⌋₊ : ℝ) + 1) :=
          ENNReal.ofReal_le_ofReal (le_of_lt (Nat.lt_floor_add_one x.toReal))
      _ ≤ ENNReal.ofReal (2 * (2 : ℝ) ^ Nat.log 2 ⌊x.toReal⌋₊) :=
          ENNReal.ofReal_le_ofReal hsumle
      _ = 2 * (2 : ENNReal) ^ Nat.log 2 ⌊x.toReal⌋₊ := by
        rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
        rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ (2 : ℝ))]
        rw [show ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) by norm_num]

/-- A dyadic band on a natural number, read in `NNReal` (blueprint `lem:nnrealDyadicBandCast`).
The dyadic pigeonhole produces its band on cardinalities; consumers that inflate constants need it
on their `NNReal` casts. -/
theorem NNReal.dyadic_band {m c : ℕ} (h1 : 2 ^ m ≤ c) (h2 : c ≤ 2 * 2 ^ m) :
    (2 : NNReal) ^ m ≤ (c : NNReal) ∧ (c : NNReal) ≤ 2 * (2 : NNReal) ^ m := by
  exact_mod_cast And.intro h1 h2

noncomputable section

namespace Kakeya

/-- Two naturals lying in the same dyadic band, the larger one nonzero, differ by at most a
factor `2`. -/
lemma le_two_mul_of_log_two_eq {a b : ℕ} (hb : b ≠ 0)
    (hab : Nat.log 2 a = Nat.log 2 b) : a ≤ 2 * b :=
  ((hab ▸ Nat.lt_pow_succ_log_self Nat.one_lt_two a).trans_le <|
    (pow_succ' 2 (Nat.log 2 b)).le.trans <|
      Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hb)).le

/-- `⌊log₂ n⌋ ≤ log n / log 2` for every natural `n`, including the degenerate case `n = 0`
(where both sides vanish). -/
lemma natLog_le_log_div_log_two (n : ℕ) :
    (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · simp [h0]
  · rw [le_div_iff₀ hlog2, ← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.pow_log_le_self 2 hn.ne')

/-- **A polynomial cap on `K` makes `⌊log₂ K⌋ + 1` affine in `log a⁻¹`.**
Taking logarithms in `K ≤ C₁ · a ^ (-D)` and dividing by `log 2`. The `K = 0` case is where the
normalisation `1 ≤ C₁` is used. -/
lemma natLog_succ_le_affine_log_inv_of_cap {C1 : ℝ} (hC1 : 1 ≤ C1) (D : ℕ)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {K : ℕ} (hK : (K : ℝ) ≤ C1 * a ^ (-(D : ℝ))) :
    (Nat.log 2 K : ℝ) + 1
      ≤ (Real.log C1 / Real.log 2 + 1) + ((D : ℝ) / Real.log 2) * Real.log a⁻¹ := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hC1pos : 0 < C1 := by linarith
  have htpos : 0 ≤ Real.log a⁻¹ := by
    rw [Real.log_inv]; linarith [Real.log_neg ha ha1]
  -- The whole content: `⌊log₂ K⌋ · log 2 ≤ log C1 + D · log a⁻¹`.
  have key : (Nat.log 2 K : ℝ) * Real.log 2 ≤ Real.log C1 + (D : ℝ) * Real.log a⁻¹ := by
    rcases eq_or_ne K 0 with hK0 | hK0
    · have h0 : (Nat.log 2 K : ℝ) = 0 := by simp [hK0]
      rw [h0, zero_mul]
      have := mul_nonneg (Nat.cast_nonneg (α := ℝ) D) htpos
      linarith [Real.log_nonneg hC1]
    · have h1 : (Nat.log 2 K : ℝ) * Real.log 2 ≤ Real.log (K : ℝ) := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by positivity)
          (by exact_mod_cast Nat.pow_log_le_self 2 hK0)
      refine h1.trans ?_
      have h2 := Real.log_le_log (by positivity : (0:ℝ) < (K : ℝ)) hK
      rw [Real.log_mul hC1pos.ne' (by positivity), Real.log_rpow ha] at h2
      rw [Real.log_inv]
      linarith
  -- Divide by `log 2`.
  have hgoal : (Real.log C1 / Real.log 2 + 1) + ((D : ℝ) / Real.log 2) * Real.log a⁻¹
      = (Real.log C1 + (D : ℝ) * Real.log a⁻¹) / Real.log 2 + 1 := by
    field_simp
    ring
  rw [hgoal]
  linarith [(le_div_iff₀ hlog2pos).mpr key]

end Kakeya

end

end
