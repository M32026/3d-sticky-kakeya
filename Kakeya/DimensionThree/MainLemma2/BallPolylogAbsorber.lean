/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallMarginLoss

/-!
# The degree-`k` polylogarithmic absorber

Both reviews measured the same gap:

* `ConvexSpaceBody.nonempty_biasedFactorization.L` (`Kakeya/Factorization.lean`) is a
  **product** of `dim + 1` polylogarithmic factors,
  `ofReal (1 + logb 2 (card · (2^dim/(c·d^dim))^ϖ)) * ofReal (1 + logb 2 (1/d)) ^ dim`
  — at `dim = 3` a degree-4 polylog product;
* the existing absorber `Kakeya.VeryNotSticky.eventually_le_rpow_neg_of_polylog`
  (`M/BallGeneralGlue.lean`) takes an **additive** hypothesis
  `(f d : ℝ) ≤ A + B · logb 2 (1/d)` — degree 1.

So `Cg ≤ δ^{-ε}` had no route, for **any** `ε > 0`: the defect is exponent-independent.

This file supplies the missing degree-`k` absorber and the reduction that makes it usable on
Lemma 9.2's loss. Nothing existing changes; every declaration here is new.

## Contents

* `Kakeya.VeryNotSticky.polylog_pow_rpow_atTop` — the degree-`k` generalisation of the existing
  `Kakeya.VeryNotSticky.polylog_rpow_atTop`, which hard-wires the exponent `2`.
* `Kakeya.VeryNotSticky.eventually_le_rpow_neg_of_polylog_pow` — **the absorber**. A
  `NNReal`-valued function of the scale bounded by `(A + B · logb 2 (1/d)) ^ k` is eventually
  below `δ^{-ε}`, for every `ε > 0` and every `k`. It sits **beside** the existing additive
  absorber and **subsumes** it: `eventually_le_rpow_neg_of_polylog_of_pow` is the `k = 1`
  instance, and it reproves the existing statement verbatim.
* `Kakeya.VeryNotSticky.eventually_le_rpow_neg_of_polylog_prod` — the same for a function
  bounded by a `Finset.prod` of `k` individually-polylog factors, which is the shape `L` has.
* `ConvexSpaceBody.nonempty_biasedFactorization.L_le_polylog_pow` — the reduction of `L` at
  general `dim` to a degree-`(dim + 1)` polylog power. **Every constant is forced**: see the
  docstring for which hypothesis pins which.
* `Kakeya.VeryNotSticky.eventually_uniformLossBound_le_rpow_neg` and its `dim = 3` instance
  `…_three_le_rpow_neg` — the payoff:
  `Kakeya.VeryNotSticky.uniformLossBound 3 (N δ) δ ϱ ≤ δ^{-ε}` eventually, for every `ε > 0`,
  whenever the cardinality bound `N` is polynomially bounded in `1/δ`. The existing
  `Kakeya.VeryNotSticky.eventually_card_segs_le` supplies exactly that, at `p = 4`.
* `Kakeya.VeryNotSticky.exists_threshold_of_eventually_nhdsGT` and
  `Kakeya.VeryNotSticky.le_rpow_neg_of_le_coarser` — the two shape adapters, kept separate from
  the absorber: Lemma 9.2's retention is read at the *relative* scale `δ/r₁` while the `Cg`
  obligation is stated at `δ`.

## What this does **not** do

A product of polylogarithmic losses is absorbed by any fixed negative power of `δ`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Asymptotics
open scoped NNReal ENNReal Topology

universe u

namespace Kakeya.VeryNotSticky

/-! ### The degree-`k` polylogarithmic growth bound -/

/-- **`(1 + logb ρ x) ^ k = o(x^ε)` for every `k` and every `ε > 0`.** The existing
`Kakeya.VeryNotSticky.polylog_rpow_atTop` is the `k = 2` case; it hard-wires the exponent `2`
because its only consumer squared. The reduction to it is monotonicity of `t ↦ t ^ n` at a base
`t = 1 + logb ρ x ≥ 1`, valid for `x ≥ 1`, together with `k ≤ 2 · max k 1`.

The hypothesis `1 < ρ` is what forces `0 ≤ logb ρ x` for `x ≥ 1` (`Real.logb_nonneg`), hence
`1 ≤ 1 + logb ρ x`, without which `pow_le_pow_right₀` is unavailable and the statement is false
(at `ρ < 1` the polylog is negative and odd powers flip). -/
theorem polylog_pow_rpow_atTop {ρ : ℝ} (hρ : 1 < ρ) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, (1 + Real.logb ρ x) ^ k ≤ x ^ ε := by
  set m : ℕ := max k 1 with hm
  have hm0 : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hkm : k ≤ 2 * m := le_trans (le_max_left _ _) (Nat.le_mul_of_pos_left m Nat.zero_lt_two)
  have hεm : 0 < ε / (m : ℝ) := div_pos hε hmR
  filter_upwards [polylog_rpow_atTop hρ hεm, eventually_ge_atTop (1 : ℝ)] with x hx1 hx3
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx3
  have hL : 0 ≤ Real.logb ρ x := Real.logb_nonneg hρ hx3
  have hbase : (1 : ℝ) ≤ 1 + Real.logb ρ x := by linarith
  calc (1 + Real.logb ρ x) ^ k
      ≤ (1 + Real.logb ρ x) ^ (2 * m) := pow_le_pow_right₀ hbase hkm
    _ = ((1 + Real.logb ρ x) ^ 2) ^ m := by rw [pow_mul]
    _ ≤ (x ^ (ε / (m : ℝ))) ^ m := by
        exact pow_le_pow_left₀ (by positivity) hx1 m
    _ = x ^ ε := by
        rw [← Real.rpow_natCast (x ^ (ε / (m : ℝ))) m, ← Real.rpow_mul hx0.le,
          div_mul_cancel₀ _ (ne_of_gt hmR)]

/-- **The degree-`k` polylogarithmic growth bound in the `A + B · logb` normal form.** For every
`k` and every `ε > 0`, `(A + B · logb 2 x) ^ k ≤ x ^ ε` for all large `x`.

`0 ≤ A` and `0 ≤ B` are what force the linearisation `A + B · logb 2 x ≤ (A + B)(1 + logb 2 x)`
(valid for `x ≥ 1`, where the polylog is nonnegative); without them the left side can be
negative and the `k`-th power uncontrolled in sign. -/
theorem polylog_normal_pow_rpow_atTop {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (k : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, (A + B * Real.logb 2 x) ^ k ≤ x ^ ε := by
  have hε2 : 0 < ε / 2 := by linarith
  have hconst : ∀ᶠ x : ℝ in atTop, (A + B) ^ k ≤ x ^ (ε / 2) :=
    (tendsto_rpow_atTop (y := ε / 2) hε2).eventually_ge_atTop ((A + B) ^ k)
  filter_upwards [polylog_pow_rpow_atTop (ρ := (2 : ℝ)) (by norm_num) k hε2, hconst,
    eventually_ge_atTop (1 : ℝ)] with x hx1 hx2 hx3
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx3
  have hL : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx3
  have hlin : A + B * Real.logb 2 x ≤ (A + B) * (1 + Real.logb 2 x) := by
    nlinarith [mul_nonneg hA hL]
  have hlin0 : 0 ≤ A + B * Real.logb 2 x := by positivity
  calc (A + B * Real.logb 2 x) ^ k
      ≤ ((A + B) * (1 + Real.logb 2 x)) ^ k := pow_le_pow_left₀ hlin0 hlin k
    _ = (A + B) ^ k * (1 + Real.logb 2 x) ^ k := by rw [mul_pow]
    _ ≤ x ^ (ε / 2) * x ^ (ε / 2) := by
        refine mul_le_mul hx2 hx1 (by positivity) (by positivity)
    _ = x ^ ε := by rw [← Real.rpow_add hx0]; ring_nf

/-! ### The scale-side transfer, factored out -/

/-- **The `𝓝[>] 0` ⇄ `atTop` transfer of the absorber, with the growth bound abstracted.** This
is verbatim the tail of the existing `Kakeya.VeryNotSticky.eventually_le_rpow_neg_of_polylog`,
extracted so that every polylogarithmic shape — additive, `k`-th power, or product — reaches
`δ^{-ε}` through one bridge instead of its own copy.

`hf` is asked only on `0 < d ≤ 1` because that is all the filter supplies: the threshold
`x₀` produced by `hg` is raised to `max x₀ 1 ≥ 1`, which forces `d ≤ 1` on the selected
neighbourhood. No sign hypothesis on `ε` is needed here; positivity of `ε` is what the *growth
bound* `hg` needs, not the transfer. -/
theorem eventually_le_rpow_neg_of_atTop {f : NNReal → NNReal} {g : ℝ → ℝ} {ε : ℝ}
    (hf : ∀ d : NNReal, 0 < d → d ≤ 1 → (f d : ℝ) ≤ g ((d : ℝ))⁻¹)
    (hg : ∀ᶠ x : ℝ in atTop, g x ≤ x ^ ε) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ((f d : NNReal) : ENNReal) ≤ (d : ENNReal) ^ (-ε) := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hg
  have hmax : (0 : ℝ) < max x₀ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have ht0 : (0 : ℝ≥0) < ((max x₀ 1)⁻¹).toNNReal := Real.toNNReal_pos.2 (inv_pos.2 hmax)
  have htc : (((max x₀ 1)⁻¹).toNNReal : ℝ) = (max x₀ 1)⁻¹ :=
    Real.coe_toNNReal _ (le_of_lt (inv_pos.2 hmax))
  filter_upwards [Ioo_mem_nhdsGT ht0] with d hd
  have hd0 : 0 < d := hd.1
  have hd0R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hdt : (d : ℝ) < (max x₀ 1)⁻¹ := by
    have h := NNReal.coe_lt_coe.2 hd.2
    rwa [htc] at h
  have hx : max x₀ 1 ≤ ((d : ℝ))⁻¹ := by
    rw [le_inv_comm₀ hmax hd0R]
    exact hdt.le
  have hd1 : d ≤ 1 := by
    have h1 : (d : ℝ) ≤ 1 := by
      have : (max x₀ 1)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        exact Or.inr (le_max_right _ _)
      linarith
    exact_mod_cast h1
  have key := hx₀ ((d : ℝ))⁻¹ (le_trans (le_max_left _ _) hx)
  have hreal : (f d : ℝ) ≤ ((d : ℝ))⁻¹ ^ ε := le_trans (hf d hd0 hd1) key
  have hnn : (f d : ℝ≥0) ≤ d ^ (-ε) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_rpow, Real.rpow_neg hd0R.le,
      ← Real.inv_rpow hd0R.le]
    simpa using hreal
  calc ((f d : NNReal) : ENNReal) ≤ ((d ^ (-ε) : ℝ≥0) : ENNReal) := by exact_mod_cast hnn
    _ = (d : ENNReal) ^ (-ε) := ENNReal.coe_rpow_of_ne_zero hd0.ne' _

/-! ### The degree-`k` absorber -/

/-- **THE DEGREE-`k` ABSORBER.** A `NNReal`-valued function of the scale bounded by the `k`-th
power of a polylogarithm, `(f d : ℝ) ≤ (A + B · logb 2 (1/d)) ^ k`, is eventually below
`δ^{-ε}` — for **every** `ε > 0` and **every** `k`.

This is what `Kakeya.VeryNotSticky.BallData`'s `Cg` field needs and what the existing additive
absorber `Kakeya.VeryNotSticky.eventually_le_rpow_neg_of_polylog` could not deliver: Lemma 9.2's
retention `ConvexSpaceBody.nonempty_biasedFactorization.L` is a *product* of `dim + 1`
polylogarithmic factors, so at `dim = 3` the consumer needs `k = 4`.

Which hypothesis forces which constant:

* `hA : 0 ≤ A`, `hB : 0 ≤ B` force the linearisation inside
  `Kakeya.VeryNotSticky.polylog_normal_pow_rpow_atTop`. They are not cosmetic: for `A < 0` the
  bracket is negative near `d = 1` and an even `k` turns the bound the wrong way round.
* `hε : 0 < ε` is what makes `x ^ ε` beat every fixed power of a logarithm; at `ε = 0` the
  statement is false for any `B > 0`, `k ≥ 1`.
* `k` is unconstrained — in particular `k = 0` is allowed and gives `f d ≤ 1` absorbed trivially.
* `hf` is asked only on `0 < d ≤ 1`, all the filter supplies. -/
theorem eventually_le_rpow_neg_of_polylog_pow {f : NNReal → NNReal} {A B : ℝ} {k : ℕ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ d : NNReal, 0 < d → d ≤ 1 → (f d : ℝ) ≤ (A + B * Real.logb 2 ((d : ℝ))⁻¹) ^ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ((f d : NNReal) : ENNReal) ≤ (d : ENNReal) ^ (-ε) :=
  eventually_le_rpow_neg_of_atTop (g := fun x => (A + B * Real.logb 2 x) ^ k) hf
    (polylog_normal_pow_rpow_atTop hA hB k hε)

/-- **The degree-`k` absorber subsumes the existing additive one.** This is the `k = 1` instance,
and its statement is verbatim that of `Kakeya.VeryNotSticky.eventually_le_rpow_neg_of_polylog`;
the two therefore sit beside each other, the existing one being an instance rather than a
competitor. Nothing existing is deleted or re-proved in place. -/
theorem eventually_le_rpow_neg_of_polylog_of_pow {f : NNReal → NNReal} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ d : NNReal, 0 < d → d ≤ 1 → (f d : ℝ) ≤ A + B * Real.logb 2 ((d : ℝ))⁻¹)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ((f d : NNReal) : ENNReal) ≤ (d : ENNReal) ^ (-ε) :=
  eventually_le_rpow_neg_of_polylog_pow (k := 1) hA hB
    (fun d hd hd1 => by simpa using hf d hd hd1) hε

/-- The existing additive absorber really is the `k = 1` instance: same statement, up to the
implicit-argument order. A tripwire, not a dependency — if either statement moves, this stops
typechecking. -/
example : @eventually_le_rpow_neg_of_polylog = @eventually_le_rpow_neg_of_polylog_of_pow := rfl

/-- **The absorber in product form**, which is the shape the general branch's `Cg` actually has:
a *product* of loss factors — the tier retention, the dims-class loss, the heavy-ball factor,
Lemma 9.2's pigeonholing retention — each individually polylogarithmic. The degree is the number
of factors, `t.card`, so no consumer has to count them by hand.

`hu` is the whole content: each factor is below one common affine polylog. `hA`, `hB` force that
polylog's constants, exactly as in `Kakeya.VeryNotSticky.eventually_le_rpow_neg_of_polylog_pow`.
No hypothesis on `t` beyond finiteness, and none on `f` beyond `hf`. -/
theorem eventually_le_rpow_neg_of_polylog_prod {ι : Type*} (t : Finset ι)
    {f : NNReal → NNReal} {u : ι → NNReal → NNReal} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ d : NNReal, 0 < d → d ≤ 1 → f d ≤ ∏ i ∈ t, u i d)
    (hu : ∀ i ∈ t, ∀ d : NNReal, 0 < d → d ≤ 1 →
      (u i d : ℝ) ≤ A + B * Real.logb 2 ((d : ℝ))⁻¹)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ((f d : NNReal) : ENNReal) ≤ (d : ENNReal) ^ (-ε) := by
  refine eventually_le_rpow_neg_of_polylog_pow (k := t.card) hA hB (fun d hd hd1 => ?_) hε
  have hΛ : 0 ≤ Real.logb 2 ((d : ℝ))⁻¹ := by
    refine Real.logb_nonneg (by norm_num) ?_
    rw [one_le_inv_iff₀]
    exact ⟨hd, hd1⟩
  calc (f d : ℝ) ≤ ((∏ i ∈ t, u i d : NNReal) : ℝ) := by exact_mod_cast hf d hd hd1
    _ = ∏ i ∈ t, ((u i d : NNReal) : ℝ) := by push_cast; ring
    _ ≤ ∏ _i ∈ t, (A + B * Real.logb 2 ((d : ℝ))⁻¹) :=
        Finset.prod_le_prod (fun i _ => (u i d).coe_nonneg)
          (fun i hi => hu i hi d hd hd1)
    _ = (A + B * Real.logb 2 ((d : ℝ))⁻¹) ^ t.card := by
        rw [Finset.prod_const]

end Kakeya.VeryNotSticky

/-! ### Lemma 9.2's loss is a degree-`(dim + 1)` polylogarithmic power -/

namespace ConvexSpaceBody.nonempty_biasedFactorization

/-- **The reduction of Lemma 9.2's retention to the absorber's normal form.**
`ConvexSpaceBody.nonempty_biasedFactorization.L dim card d ϖ` is a product of `dim + 1`
polylogarithmic factors; each of them is below one common affine polylog `A + B · logb 2 (1/d)`,
so the whole product is below its `(dim + 1)`-st power. That is exactly the hypothesis of
`Kakeya.VeryNotSticky.eventually_le_rpow_neg_of_polylog_pow`.

**Which hypothesis forces which constant.** The three factors contributing are
`logb 2 card`, the `δ`-free `ϖ · logb 2 (2^dim / c dim)`, and `ϖ · dim · logb 2 (1/d)`:

* `hcard : (card : ℝ) ≤ (1/d) ^ p` is the *only* control on the cardinality, and it is what
  contributes the `p` in `hB`. Without it `card` is unbounded and no `δ`-free `B` exists —
  the bound is genuinely false, not merely unprovable.
* `hA` pins `A` from the scale-free part of the first factor. `Metric.lt_volume_convexHull.c dim`
  enters through `- logb 2 (c dim)` and `hA1 : 1 ≤ A` is what makes the *second* factor
  `1 + logb 2 (1/d)` fit under the same `A + B · logb 2 (1/d)` (it needs `A ≥ 1`, `B ≥ 1`).
* `hB`, `hB1` pin `B` from `p` (cardinality) plus `ϖ · dim` (the scale part of the first factor)
  and from the second factor's slope `1`.
* there is deliberately **no** sign hypothesis on `ϖ`. One was tried and **deleted**: the whole
  `ϖ`-dependence is carried by `hA` and `hB`, and at `ϖ < 0` the first factor turns negative, so
  `ENNReal.ofReal` truncates it to `0` and the bound holds a fortiori. A `0 ≤ ϖ` binder here did
  no work, and the `unusedVariables` linter said so.
* `hd`, `hd1` force `0 ≤ logb 2 (1/d)`, without which none of the `Λ`-monotonicity steps hold.

At `dim = 3`, the case Lemma 9.2 is read at, this is the required degree-4 statement. -/
theorem L_le_ofReal_polylog_pow {dim card : ℕ} {d : NNReal} {ϖ p A B : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hcard : (card : ℝ) ≤ ((d : ℝ))⁻¹ ^ p)
    (hA : 1 + ϖ * ((dim : ℝ) - Real.logb 2 (Metric.lt_volume_convexHull.c dim)) ≤ A)
    (hA1 : 1 ≤ A) (hB : p + ϖ * (dim : ℝ) ≤ B) (hB1 : 1 ≤ B) :
    L dim card d ϖ ≤
      ENNReal.ofReal ((A + B * Real.logb 2 ((d : ℝ))⁻¹) ^ (dim + 1)) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := hd
  have hd1' : (d : ℝ) ≤ 1 := hd1
  have hinv1 : (1 : ℝ) ≤ ((d : ℝ))⁻¹ := by
    rw [one_le_inv_iff₀]
    exact ⟨hd0, hd1'⟩
  set Λ : ℝ := Real.logb 2 ((d : ℝ))⁻¹ with hΛdef
  have hΛ : 0 ≤ Λ := Real.logb_nonneg (by norm_num) hinv1
  have hlogd : Real.logb 2 (d : ℝ) = -Λ := by
    rw [hΛdef, Real.logb_inv]; ring
  have hM0 : (0 : ℝ) ≤ A + B * Λ := by positivity
  have hM1 : (1 : ℝ) ≤ A + B * Λ := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ B) hΛ]
  -- the constants of the definition
  have hc0 : (0 : ℝ) < (Metric.lt_volume_convexHull.c dim : ℝ) :=
    Metric.lt_volume_convexHull.c_pos dim
  set X : ℝ := ((2 : ℝ) ^ dim / ((Metric.lt_volume_convexHull.c dim : ℝ) * (d : ℝ) ^ dim))
    with hXdef
  have hX0 : (0 : ℝ) < X := by rw [hXdef]; positivity
  have hlogX : Real.logb 2 X =
      (dim : ℝ) - Real.logb 2 (Metric.lt_volume_convexHull.c dim) + (dim : ℝ) * Λ := by
    have hself : Real.logb 2 (2 : ℝ) = 1 := by norm_num [Real.logb_self_eq_one]
    rw [hXdef, Real.logb_div (by positivity) (by positivity), Real.logb_mul (ne_of_gt hc0)
      (by positivity), Real.logb_pow, Real.logb_pow, hself, hlogd]
    ring
  -- the second factor
  have hv : (1 : ℝ) + Real.logb 2 (1 / (d : ℝ)) = 1 + Λ := by rw [one_div, hΛdef]
  have hvle : (1 : ℝ) + Real.logb 2 (1 / (d : ℝ)) ≤ A + B * Λ := by
    rw [hv]
    nlinarith [mul_le_mul_of_nonneg_right hB1 hΛ]
  -- the first factor
  have hule : (1 : ℝ) + Real.logb 2 ((card : ℝ) * X ^ ϖ) ≤ A + B * Λ := by
    rcases Nat.eq_zero_or_pos card with hc | hc
    · subst hc
      simp only [Nat.cast_zero, zero_mul, Real.logb_zero, add_zero]
      linarith [mul_le_mul_of_nonneg_right hB1 hΛ]
    · have hcR : (0 : ℝ) < (card : ℝ) := by exact_mod_cast hc
      have hrp : (0 : ℝ) < X ^ ϖ := Real.rpow_pos_of_pos hX0 ϖ
      have hsplit : Real.logb 2 ((card : ℝ) * X ^ ϖ) =
          Real.logb 2 (card : ℝ) + ϖ * Real.logb 2 X := by
        rw [Real.logb_mul (ne_of_gt hcR) (ne_of_gt hrp),
          Real.logb_rpow_eq_mul_logb_of_pos hX0]
      have hcardlog : Real.logb 2 (card : ℝ) ≤ p * Λ := by
        refine le_trans (Real.logb_le_logb_of_le (by norm_num) hcR hcard) ?_
        rw [Real.logb_rpow_eq_mul_logb_of_pos (lt_of_lt_of_le zero_lt_one hinv1), hΛdef]
      rw [hsplit, hlogX]
      nlinarith [mul_le_mul_of_nonneg_right hB hΛ]
  -- assemble
  calc L dim card d ϖ
      = ENNReal.ofReal (1 + Real.logb 2 ((card : ℝ) * X ^ ϖ)) *
          ENNReal.ofReal (1 + Real.logb 2 (1 / (d : ℝ))) ^ dim := by rw [L, hXdef]
    _ ≤ ENNReal.ofReal (A + B * Λ) * ENNReal.ofReal (A + B * Λ) ^ dim := by
        gcongr
    _ = ENNReal.ofReal (A + B * Λ) ^ (dim + 1) := by rw [pow_succ]; ring
    _ = ENNReal.ofReal ((A + B * Λ) ^ (dim + 1)) := (ENNReal.ofReal_pow hM0 _).symm

end ConvexSpaceBody.nonempty_biasedFactorization

namespace Kakeya.VeryNotSticky

/-! ### The payoff: `Cg`'s Lemma 9.2 factor is absorbed -/

/-- The `A` of the normal form for `ConvexSpaceBody.nonempty_biasedFactorization.L` at ambient
dimension `dim` and bias exponent `ϖ`: the scale-free part of the first pigeonholing factor,
raised to at least `1` so that the *other* `dim` factors `1 + logb 2 (1/d)` fit under the same
affine polylog. -/
noncomputable def lossPolylogConst (dim : ℕ) (ϖ : ℝ) : ℝ :=
  max 1 (1 + ϖ * ((dim : ℝ) - Real.logb 2 (Metric.lt_volume_convexHull.c dim)))

/-- The `B` of the normal form: the slope. `p` is the exponent of the polynomial cardinality
bound `#𝕋_B ≤ (1/δ)^p`, `ϖ · dim` is the scale part of the first pigeonholing factor, and the
`max 1` covers the slope `1` of the remaining `dim` factors. -/
noncomputable def lossPolylogSlope (dim : ℕ) (ϖ p : ℝ) : ℝ := max 1 (p + ϖ * (dim : ℝ))

theorem one_le_lossPolylogConst (dim : ℕ) (ϖ : ℝ) : 1 ≤ lossPolylogConst dim ϖ := le_max_left _ _

theorem one_le_lossPolylogSlope (dim : ℕ) (ϖ p : ℝ) : 1 ≤ lossPolylogSlope dim ϖ p :=
  le_max_left _ _

/-- **The uniformised Lemma 9.2 loss is a degree-`(dim + 1)` polylog, in the absorber's normal
form.** `Kakeya.VeryNotSticky.uniformLossBound` is `max 1 (L …).toNNReal`, and the `max 1` costs
nothing because the normal form is already `≥ 1`. -/
theorem uniformLossBound_le_polylog_pow {dim n : ℕ} {d : NNReal} {ϖ p : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hn : (n : ℝ) ≤ ((d : ℝ))⁻¹ ^ p) :
    ((uniformLossBound dim n d ϖ : NNReal) : ℝ) ≤
      (lossPolylogConst dim ϖ + lossPolylogSlope dim ϖ p * Real.logb 2 ((d : ℝ))⁻¹) ^
        (dim + 1) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := hd
  have hd1' : (d : ℝ) ≤ 1 := hd1
  have hinv1 : (1 : ℝ) ≤ ((d : ℝ))⁻¹ := by
    rw [one_le_inv_iff₀]
    exact ⟨hd0, hd1'⟩
  have hΛ : 0 ≤ Real.logb 2 ((d : ℝ))⁻¹ := Real.logb_nonneg (by norm_num) hinv1
  set A : ℝ := lossPolylogConst dim ϖ with hAdef
  set B : ℝ := lossPolylogSlope dim ϖ p with hBdef
  have hA1 : (1 : ℝ) ≤ A := one_le_lossPolylogConst dim ϖ
  have hB1 : (1 : ℝ) ≤ B := one_le_lossPolylogSlope dim ϖ p
  have hM1 : (1 : ℝ) ≤ A + B * Real.logb 2 ((d : ℝ))⁻¹ := by
    nlinarith [mul_le_mul_of_nonneg_right hB1 hΛ]
  have hMpow : (1 : ℝ) ≤ (A + B * Real.logb 2 ((d : ℝ))⁻¹) ^ (dim + 1) :=
    one_le_pow₀ hM1
  have hL := ConvexSpaceBody.nonempty_biasedFactorization.L_le_ofReal_polylog_pow
    (dim := dim) (card := n) (ϖ := ϖ) (p := p) (A := A) (B := B) hd hd1 hn
    (le_max_right _ _) hA1 (le_max_right _ _) hB1
  have hreal : (ConvexSpaceBody.nonempty_biasedFactorization.L dim n d ϖ).toReal ≤
      (A + B * Real.logb 2 ((d : ℝ))⁻¹) ^ (dim + 1) :=
    ENNReal.toReal_le_of_le_ofReal (by linarith) hL
  rw [uniformLossBound, NNReal.coe_max]
  exact max_le (by exact_mod_cast hMpow) hreal

/-- **THE PAYOFF.** Lemma 9.2's pigeonholing loss, read at a ball-independent cardinality bound
`N δ` that is polynomially bounded in `1/δ`, is eventually below `δ^{-ε}` for **every** `ε > 0`.

This is the `Cg` obligation of the general branch, and the additive absorber alone does not suffice: `L` at `dim = 3`
is a degree-4 polylog product, so this is `k = 4` in
`Kakeya.VeryNotSticky.eventually_le_rpow_neg_of_polylog_pow`.

Which hypothesis forces what: `hN` is the *only* control on the cardinality and supplies the `p`
in the slope; `hε : 0 < ε` is what makes `δ^{-ε}` beat a fixed power of a logarithm. `ϖ` needs no
sign hypothesis (see `ConvexSpaceBody.nonempty_biasedFactorization.L_le_ofReal_polylog_pow`), and
`N` needs no monotonicity — the uniformisation already happened in
`Kakeya.VeryNotSticky.L_le_uniformLossBound`. -/
theorem eventually_uniformLossBound_le_rpow_neg (dim : ℕ) {N : NNReal → ℕ} {ϖ p : ℝ}
    (hN : ∀ d : NNReal, 0 < d → d ≤ 1 → ((N d : ℕ) : ℝ) ≤ ((d : ℝ))⁻¹ ^ p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ((uniformLossBound dim (N d) d ϖ : NNReal) : ENNReal) ≤ (d : ENNReal) ^ (-ε) :=
  eventually_le_rpow_neg_of_polylog_pow (f := fun d => uniformLossBound dim (N d) d ϖ)
    (k := dim + 1) (le_trans zero_le_one (one_le_lossPolylogConst dim ϖ))
    (le_trans zero_le_one (one_le_lossPolylogSlope dim ϖ p))
    (fun d hd hd1 => uniformLossBound_le_polylog_pow hd hd1 (hN d hd hd1)) hε

/-- The `dim = 3` instance, which is the one Lemma 9.2 is read at: a **degree-4** polylog
product absorbed into `δ^{-ε}`. -/
theorem eventually_uniformLossBound_three_le_rpow_neg {N : NNReal → ℕ} {ϖ p : ℝ}
    (hN : ∀ d : NNReal, 0 < d → d ≤ 1 → ((N d : ℕ) : ℝ) ≤ ((d : ℝ))⁻¹ ^ p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ((uniformLossBound 3 (N d) d ϖ : NNReal) : ENNReal) ≤ (d : ENNReal) ^ (-ε) :=
  eventually_uniformLossBound_le_rpow_neg 3 hN hε

/-! ### Two shape adapters the consumer needs

Lemma 9.2's retention is read at the **relative** scale `d = δ/r₁`, not at `δ`, while the `Cg`
obligation is stated at `δ`. The two lemmas below are the change of variable, kept separate from
the absorber so that neither hides inside the other.
-/

/-- **Threshold form of the absorber.** `∀ᶠ d in 𝓝[>] 0` is the wrong shape when the argument is
a *derived* scale `δ/r₁`: one then needs an explicit threshold to compare against. `hd₀1 : d₀ ≤ 1`
is part of the output because every polylog bound here is only claimed on `d ≤ 1`.

*Short-name duplicate, deliberate.* Two other declarations carry this short name —
`Kakeya.StickyKakeya.exists_threshold_of_eventually_nhdsGT` (`StickyKakeya/Constants.lean`) and
`Kakeya.ML2Reduction.exists_threshold_of_eventually_nhdsGT`
(`MainLemma2/Reduction/SpineOuterTubes.lean`) — and the full names differ. They are **not**
interchangeable with this one: neither concludes `d₀ ≤ 1`, and the `StickyKakeya` copy binds `δ`
strict-implicitly. -/
theorem exists_threshold_of_eventually_nhdsGT {P : NNReal → Prop}
    (h : ∀ᶠ d : NNReal in 𝓝[>] 0, P d) :
    ∃ d₀ : NNReal, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ d : NNReal, 0 < d → d ≤ d₀ → P d := by
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨r, hr0, hr⟩ := h
  refine ⟨min (Real.toNNReal (r / 2)) 1, ?_, min_le_right _ _, fun d hd hdle => ?_⟩
  · exact lt_min (Real.toNNReal_pos.2 (by linarith)) zero_lt_one
  · have hdr : (d : ℝ) ≤ r / 2 := by
      have h1 : d ≤ Real.toNNReal (r / 2) := le_trans hdle (min_le_left _ _)
      have h2 : (d : ℝ) ≤ ((Real.toNNReal (r / 2) : NNReal) : ℝ) := h1
      rwa [Real.coe_toNNReal _ (by linarith)] at h2
    refine hr ?_ hd
    have : dist d (0 : NNReal) = (d : ℝ) := by
      simp [NNReal.dist_eq, abs_of_nonneg d.coe_nonneg]
    rw [this]
    linarith

/-- **Passing a `δ^{-ε}`-bound from a coarser scale to a finer one.** If a quantity is below
`c^{-ε}` and `d ≤ c ≤ 1`, it is below `d^{-ε}`: the map `t ↦ t^{-ε}` is *antitone*, so the bound
at the *larger* scale is the *stronger* one. This is why the absorber applied at the relative
scale `c = δ/r₁ ≥ δ` still delivers the `Cg` obligation, which is stated at `d = δ`.

`hε : 0 ≤ ε` is what makes the map antitone; at `ε < 0` the implication reverses. `hdc` is the
only other hypothesis: a `0 < d` binder was tried and **deleted**, because at `d = 0` and `ε > 0`
the right-hand side is `⊤` and the statement is vacuously true, so the binder did no work. -/
theorem le_rpow_neg_of_le_coarser {c d : NNReal} {ε : ℝ} (hε : 0 ≤ ε)
    (hdc : d ≤ c) {x : ENNReal} (hx : x ≤ (c : ENNReal) ^ (-ε)) :
    x ≤ (d : ENNReal) ^ (-ε) := by
  refine le_trans hx ?_
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow (by exact_mod_cast hdc) hε)

end Kakeya.VeryNotSticky
