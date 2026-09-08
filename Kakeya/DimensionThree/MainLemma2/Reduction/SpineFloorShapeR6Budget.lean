/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeParent
public import Kakeya.DimensionThree.MainLemma2.ShadedDividingScales

/-!
# `R6`'s budget is a `δ`-threshold once the site hoists `Cu₀` — the consumer check

`Kakeya.ML2Core.crossing_lt_window` (`R6`, existing the estimate) carries

```
    hbudget : Cstar * ENNReal.ofReal (2 * 100 ^ (2 * finrank ℝ E) * (Cu : ℝ))
                < ENNReal.ofReal ((δ : ℝ) ^ (-(ε_div ^ 2 * τ)))
```

and  recorded that the site's **old** row 3 — `Cu` quantified *inside*
`∀ᶠ δ` with only `(Cu : ℝ) ≤ δ^{-1}` retained — could not supply it
(`Kakeya.ML2Core.hbudget_fails_at_polynomial_Cu`, existing, is the refutation of that row).
 specified `Cu` `δ`-free and the estimate hoists `∃ Cu₀` before the filter, with `Cu ≤ Cu₀`
**primitive** and `(Cu : ℝ) ≤ δ^{-1}` **derived**
(`Kakeya.ML2Core.exists_threshold_const_le_rpow_neg_one`).

**This file is the consumer check: with the hoisted row, `hbudget` is a `δ`-threshold and nothing
more.**

## The two lines

`Kakeya.ML2Core.hbudget_of_absorb` splits the budget into the two things the site supplies and the
one thing a threshold buys:

```
 Cstar · K  ≤  δ^{-a} · δ^{-b}  =  δ^{-(a+b)}  <  δ^{-e}      whenever a + b < e
```

with `a` the window constant's exponent (`ν/20`, the floor block's existing binder) and `δ^{-b}` the
room the threshold gives the **`δ`-free** constant `2 · 100^{2n} · Cu₀`.  Since `e = ε_div² τ` is a
fixed positive exponent, `b := (e − a)/2` works and
`Kakeya.ML2Core.exists_threshold_hbudget` produces the threshold.

**The whole check is that `Cu₀` is `δ`-free.**  Had the site kept only `Cu ≤ δ^{-1}`, `b` would have
had to exceed `1`, and `a + b < e` with `e = ε_div² τ ≪ 1` is then impossible — which is exactly
what `hbudget_fails_at_polynomial_Cu` says.  With row the constant is `2·100^{2n}·Cu₀`, a
number, and every number is `≤ δ^{-b}` below a threshold.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section R6Budget

/-- **`R6`'s budget from two absorptions.**  The window constant is absorbed at exponent `a`, the
`δ`-free geometric constant at exponent `b`, and any `a + b < e` leaves the budget strict. -/
theorem hbudget_of_absorb {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {Cstar : ℝ≥0∞} {a b e K : ℝ} (hab : a + b < e) (_hK0 : 0 ≤ K)
    (hCstar : Cstar ≤ ENNReal.ofReal ((δ : ℝ) ^ (-a)))
    (hK : K ≤ (δ : ℝ) ^ (-b)) :
    Cstar * ENNReal.ofReal K < ENNReal.ofReal ((δ : ℝ) ^ (-e)) := by
  have hδr : (0 : ℝ) < (δ : ℝ) := hδ0
  have hδr1 : (δ : ℝ) < 1 := hδ1
  have hstep : Cstar * ENNReal.ofReal K
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(a + b))) := by
    calc Cstar * ENNReal.ofReal K
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-a)) * ENNReal.ofReal ((δ : ℝ) ^ (-b)) := by
          exact mul_le_mul' hCstar (ENNReal.ofReal_le_ofReal hK)
      _ = ENNReal.ofReal ((δ : ℝ) ^ (-a) * (δ : ℝ) ^ (-b)) :=
          (ENNReal.ofReal_mul (Real.rpow_nonneg hδr.le _)).symm
      _ = ENNReal.ofReal ((δ : ℝ) ^ (-(a + b))) := by
          rw [← Real.rpow_add hδr]; ring_nf
  refine lt_of_le_of_lt hstep ?_
  refine (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hδr _)).mpr ?_
  exact Real.rpow_lt_rpow_of_exponent_gt hδr hδr1 (by linarith)

/-- **The consumer check, : `R6`'s budget is a `δ`-threshold once `Cu₀` is `δ`-free.**

Given the site's hoisted row — `Cu₀` bound **before** `∀ᶠ δ`, `Cu ≤ Cu₀` primitive — and the floor
block's existing window binder `Cstar ≤ δ^{-a}`, there is a threshold below which
`Kakeya.ML2Core.crossing_lt_window`'s `hbudget` holds for **every** `Cu ≤ Cu₀`, at the geometric
constant `2 · 100^{2n}` of `Kakeya.ML2Core.card_nodesUnder_le_coverCount'`.

`0 < e - a` is the floor block's own margin: `e = ε_div² τ` and `a = ν/20` with
`ν ≤ ε_div² β τ / 1024`, so `e - a ≥ (1023/1024) ε_div² τ > 0`. -/
theorem exists_threshold_hbudget (n : ℕ) (Cu₀ : NNReal) {a e : ℝ} (hae : a < e) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → δ < 1 → δ ≤ δ₀ →
      ∀ Cu : NNReal, Cu ≤ Cu₀ →
      ∀ Cstar : ℝ≥0∞, Cstar ≤ ENNReal.ofReal ((δ : ℝ) ^ (-a)) →
        Cstar * ENNReal.ofReal (2 * (100 : ℝ) ^ (2 * n) * (Cu : ℝ))
          < ENNReal.ofReal ((δ : ℝ) ^ (-e)) := by
  obtain ⟨d, hd0, hd1, hd⟩ :=
    ML2Shaded.exists_threshold_const_le_rpow_neg'
      (2 * (100 : ℝ) ^ (2 * n) * (Cu₀ : ℝ)) (β := (e - a) / 2) (by linarith)
  refine ⟨d, hd0, hd1, ?_⟩
  intro δ hδ0 hδ1 hδd Cu hCu Cstar hCstar
  refine hbudget_of_absorb hδ0 hδ1 (b := (e - a) / 2) (by linarith) (by positivity) hCstar ?_
  refine le_trans ?_ (hd hδ0 hδd)
  have : (Cu : ℝ) ≤ (Cu₀ : ℝ) := by exact_mod_cast hCu
  have h100 : (0 : ℝ) ≤ 2 * (100 : ℝ) ^ (2 * n) := by positivity
  nlinarith [NNReal.coe_nonneg Cu]

/-- **The control that the check is about `Cu₀` and nothing else.**  At the site's *old* row — only
`(Cu : ℝ) ≤ δ^{-1}` — the exponent `b` would have to exceed `1`, and `a + b < e` with
`e = ε_div² τ ≤ 1` is then impossible.  `Kakeya.ML2Core.hbudget_fails_at_polynomial_Cu` (existing,
the estimate) is the refutation; this records the arithmetic side of it. -/
theorem hbudget_absorb_needs_delta_free {a b e : ℝ} (he1 : e ≤ 1) (hb1 : 1 ≤ b) (ha0 : 0 ≤ a) :
    ¬ (a + b < e) := by
  intro h
  linarith

end R6Budget

end Kakeya.ML2Core
