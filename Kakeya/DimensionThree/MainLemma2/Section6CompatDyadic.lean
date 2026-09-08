/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Section6CompatAScale

/-!
# The finite dyadic split of `ShadedPlank.reduction_to_slab_atTypicalAngle`

`ShadedPlank.reduction_to_slab_atTypicalAngle_of_aScaleConstant` reduces the leaf to the regime in
which the comparability constant is an `a`-power, `C ≤ 2 * a ^ (-(1 - 3η - ε)/127)`.  That is not
enough to run the slab layer, and `ShadedPlank.slabRoute_exponents_incompatible_at_small_eta`
records why: `Plank.localAngleConcentration_of_preassemblyData` binds its exponent `εs` **before**
the configuration, so a single `εs` must be chosen for the *worst* configuration in the regime,
while `Plank.slabwiseDensity_of_preassembly`'s `3 * ηL ≤ 4 * η + εwork` and the Item-1 budget cap
`ηL` at `O(η + ε)`.  At `η = 1/1000`, `ε = η/256` the two are incompatible.

This file removes that obstruction, by splitting the regime into **finitely many blocks** and
giving each block its own `εs`.

## The ladder

Write `δ = a ^ t`; the leaf's `δ ≤ a` is `t ≥ 1`.  Block `j` is

```
a ^ (2 ^ (j+1))  ≤  δ  ≤  a ^ (2 ^ j),        i.e.   t ∈ [2 ^ j, 2 ^ (j+1)].
```

Consecutive blocks abut exactly, so `⋃_{j < J} block j` is the contiguous range
`t ∈ [1, 2 ^ J]`, and `Plank.exists_blockCount` picks `J` with `2 ^ J` above the top of the regime.
Since the top is `(2 - 3η - ε)/(127 ε)`, `J = O(log (1/ε))`.

## Where each block's loss is charged — and why nothing sums

**The blocks are a case split, not an induction.**  A given configuration lies in exactly one
block, and that block's loss is charged to *that configuration's own* budget.  No block's loss is
ever charged to another block's budget, so there is no accumulation and no `κ`-dependence: the
budget is the `c1 = δ ^ ε'` the leaf statement itself provides at that `δ`, which is fixed before
any constant the slab layer names.  This is exactly the point at which a narrow *induction* would
be circular — it would charge block `j`'s loss to block `j+1`'s budget — and the split avoids it by
never composing two blocks.

Concretely, in block `j`:

* the **loss** is the angular exponent the slab layer must be run at,
  `εs_j = 2 ^ (j+1) * ε`, forced by the *lower* end `a ^ (2 ^ (j+1)) ≤ δ`, which gives
  `C ≤ δ ^ (-ε) ≤ a ^ (-(2 ^ (j+1) * ε))` — an `a`-power with the block's own exponent, and no
  constant at all;
* the **budget** is `c1 = δ ^ ε' ≤ a ^ (2 ^ j * ε')= a ^ (128 * 2 ^ j * ε)`, forced by the *upper*
  end `δ ≤ a ^ (2 ^ j)`;
* the ledger constraint is `εs_j < ηL_j` with `ηL_j ≤ 4 * η + (budget exponent) + ε`, i.e.
  `2 ^ (j+1) * ε < 4 * η + 128 * 2 ^ j * ε + ε`, which is
  `Plank.blockLedger_margin` — true for **every** `j` with a factor-`64` margin, because the
  loss grows by `2` per block while the budget grows by `128`.

The only quantity that has to be finite is the **number** of blocks, and it is needed for exactly
one thing: the leaf must name a single threshold `δthr` before seeing the configuration, and the
split takes the minimum of the `J` block thresholds.  A minimum of finitely many positive reals is
positive; that is the whole use of `J < ∞`.

## What is proved here

`ShadedPlank.reduction_to_slab_atTypicalAngle_of_dyadicBlocks`: the target *verbatim*, from `J`
instances of the target restricted to one block, each instance additionally handed the `a`-scale
bound `C ≤ a ^ (-(2 ^ (j+1) * ε))` that its block supplies.  Nothing geometric is used; the two
ingredients are `ShadedPlank.reduction_to_slab_atTypicalAngle_of_smallRadius` for everything
outside the regime and `ShadedPlank.rpow_le_mul_rpow_of_budgetExcess` for the top of the ladder.
-/

@[expose] public section

open MeasureTheory Metric
open scoped NNReal Real ENNReal

noncomputable section

namespace ShadedPlank

/-! ## The regime is an interval of exponents -/

/-- **The scalar core of the residual regime, exposed.**

The intermediate step of `ShadedPlank.le_two_mul_rpow_of_budgetExcess`: failure of the small-radius
budget bounds `a ^ (1 - 3η - ε)` by `432 * δ ^ (127 ε)`.  Stated separately because the dyadic
split needs the bound on `δ`, not the bound on `C` that lemma returns. -/
theorem rpow_le_mul_rpow_of_budgetExcess {η ε ε' : ℝ} (hgap : 128 * ε ≤ ε')
    {δ a b θ C : ℝ≥0} (hδ : 0 < δ) (hδa : δ ≤ a) (ha1 : a < 1) (hθ1 : θ ≤ 1) (hb1 : b ≤ 1)
    (hCδ : C ≤ δ ^ (-ε))
    (hres : a ^ η * a < 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C * (θ * b)) :
    a ^ (1 - 3 * η - ε) ≤ 432 * (δ : ℝ≥0) ^ (127 * ε) := by
  have ha : (0 : ℝ≥0) < a := lt_of_lt_of_le hδ hδa
  have hane : (a : ℝ≥0) ≠ 0 := ha.ne'
  have hδne : (δ : ℝ≥0) ≠ 0 := hδ.ne'
  have hδ1 : (δ : ℝ≥0) ≤ 1 := le_trans hδa ha1.le
  have hθb : (θ : ℝ≥0) * b ≤ 1 := by
    calc (θ : ℝ≥0) * b ≤ 1 * 1 := by gcongr
      _ = 1 := by ring
  have hstep1 : a ^ η * a < 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C := by
    refine lt_of_lt_of_le hres ?_
    calc 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C * (θ * b)
        ≤ 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C * 1 := by gcongr
      _ = 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C := by ring
  have hδC : (δ : ℝ≥0) ^ ε' * C ≤ δ ^ (127 * ε) := by
    have h1 : (δ : ℝ≥0) ^ ε' * C ≤ δ ^ ε' * δ ^ (-ε) := by gcongr
    have h2 : (δ : ℝ≥0) ^ ε' * δ ^ (-ε) = δ ^ (ε' - ε) := by
      rw [← NNReal.rpow_add hδne]; ring_nf
    have h3 : (δ : ℝ≥0) ^ (ε' - ε) ≤ δ ^ (127 * ε) :=
      NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    exact le_trans h1 (h2 ▸ h3)
  have hrw : a ^ η * a = a ^ (1 - 3 * η - ε) * (a ^ (4 * η) * a ^ ε) := by
    have h1 : a ^ (1 - 3 * η - ε) * (a ^ (4 * η) * a ^ ε) = a ^ (1 + η) := by
      rw [← NNReal.rpow_add hane, ← NNReal.rpow_add hane]
      congr 1
      ring
    have h2 : a ^ η * a = a ^ (1 + η) := by
      rw [show (1 + η) = η + 1 by ring, NNReal.rpow_add hane, NNReal.rpow_one]
    rw [h1, h2]
  have hrw2 : 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C
      = 432 * ((δ : ℝ≥0) ^ ε' * C) * (a ^ (4 * η) * a ^ ε) := by ring
  have hpos : (0 : ℝ≥0) < a ^ (4 * η) * a ^ ε :=
    mul_pos (NNReal.rpow_pos ha) (NNReal.rpow_pos ha)
  rw [hrw, hrw2] at hstep1
  have hcancel : a ^ (1 - 3 * η - ε) < 432 * ((δ : ℝ≥0) ^ ε' * C) :=
    lt_of_mul_lt_mul_right hstep1 (le_of_lt hpos)
  calc a ^ (1 - 3 * η - ε) ≤ 432 * ((δ : ℝ≥0) ^ ε' * C) := hcancel.le
    _ ≤ 432 * (δ : ℝ≥0) ^ (127 * ε) := by gcongr

/-- **The bottom of the ladder: in the residual regime `δ` is at least a fixed power of `a`.**

For `a ≤ 432⁻¹` the numeric constant of `ShadedPlank.rpow_le_mul_rpow_of_budgetExcess` is absorbed
by one further factor of `a`, and taking `127 ε`-th roots gives

`δ ≥ a ^ ((2 - 3η - ε) / (127 ε))`.

So the residual regime is the *bounded* exponent interval `t ∈ [1, (2 - 3η - ε)/(127 ε)]`, which is
what makes the number of blocks finite. -/
theorem rpow_le_of_budgetExcess {η ε ε' : ℝ} (hε : 0 < ε) (hgap : 128 * ε ≤ ε')
    {δ a b θ C : ℝ≥0} (hδ : 0 < δ) (hδa : δ ≤ a) (ha1 : a < 1) (hasmall : a ≤ 432⁻¹)
    (hθ1 : θ ≤ 1) (hb1 : b ≤ 1) (hCδ : C ≤ δ ^ (-ε))
    (hres : a ^ η * a < 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C * (θ * b)) :
    a ^ ((2 - 3 * η - ε) / (127 * ε)) ≤ δ := by
  have ha : (0 : ℝ≥0) < a := lt_of_lt_of_le hδ hδa
  have hane : (a : ℝ≥0) ≠ 0 := ha.ne'
  have hcore := rpow_le_mul_rpow_of_budgetExcess hgap hδ hδa ha1 hθ1 hb1 hCδ hres
  -- absorb the constant `432` into one factor of `a`
  have h432 : (432 : ℝ≥0) * a ≤ 1 := by
    calc (432 : ℝ≥0) * a ≤ 432 * 432⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ (by norm_num)
  have hstep : a ^ (2 - 3 * η - ε) ≤ (δ : ℝ≥0) ^ (127 * ε) := by
    have hsplit : a ^ (2 - 3 * η - ε) = a ^ (1 - 3 * η - ε) * a := by
      have h1 : a ^ (1 - 3 * η - ε) * a = a ^ (1 - 3 * η - ε) * a ^ (1 : ℝ) := by
        rw [NNReal.rpow_one]
      rw [h1, ← NNReal.rpow_add hane]
      congr 1
      ring
    rw [hsplit]
    calc a ^ (1 - 3 * η - ε) * a ≤ (432 * (δ : ℝ≥0) ^ (127 * ε)) * a := by gcongr
      _ = (δ : ℝ≥0) ^ (127 * ε) * (432 * a) := by ring
      _ ≤ (δ : ℝ≥0) ^ (127 * ε) * 1 := by gcongr
      _ = (δ : ℝ≥0) ^ (127 * ε) := by ring
  -- take `127 ε`-th roots
  have hne : (127 : ℝ) * ε ≠ 0 := by positivity
  have hmono : (a ^ (2 - 3 * η - ε)) ^ ((127 * ε)⁻¹)
      ≤ ((δ : ℝ≥0) ^ (127 * ε)) ^ ((127 * ε)⁻¹) :=
    NNReal.rpow_le_rpow hstep (by positivity)
  have hL : (a ^ (2 - 3 * η - ε)) ^ ((127 * ε)⁻¹) = a ^ ((2 - 3 * η - ε) / (127 * ε)) := by
    rw [← NNReal.rpow_mul, div_eq_mul_inv]
  have hR : ((δ : ℝ≥0) ^ (127 * ε)) ^ ((127 * ε)⁻¹) = δ := by
    rw [← NNReal.rpow_mul, mul_inv_cancel₀ hne, NNReal.rpow_one]
  rw [hL, hR] at hmono
  exact hmono

/-! ## The ladder is finite -/

/-- **The number of blocks is finite**, and it is `O(log (1/ε))`: the top of the exponent range is
`(2 - 3η - ε)/(127 ε)`, and `2 ^ J` passes it as soon as `J` exceeds its binary logarithm. -/
theorem exists_blockCount (η ε : ℝ) : ∃ J : ℕ, 1 ≤ J ∧ (2 - 3 * η - ε) / (127 * ε) ≤ 2 ^ J := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((2 - 3 * η - ε) / (127 * ε))
  refine ⟨n + 1, Nat.le_add_left 1 n, ?_⟩
  have h1 : ((n : ℝ)) ≤ 2 ^ n := by
    exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have h2 : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := by
    apply pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
  linarith

/-- **The blocks cover the exponent range.**

If `a ^ (2 ^ J) ≤ δ ≤ a` with `0 < a < 1`, then `δ` lies in one of the `J` blocks
`[a ^ (2 ^ (j+1)), a ^ (2 ^ j)]`.  Consecutive blocks abut exactly — the upper end of block `j+1`
is the lower end of block `j` — so the cover has no gap. -/
theorem exists_dyadicBlock {a δ : ℝ≥0} {J : ℕ} (hJ : 1 ≤ J)
    (hlo : a ^ ((2 : ℝ) ^ J) ≤ δ) (hhi : δ ≤ a) :
    ∃ j : ℕ, j < J ∧ a ^ ((2 : ℝ) ^ (j + 1)) ≤ δ ∧ δ ≤ a ^ ((2 : ℝ) ^ j) := by
  classical
  have hex : ∃ j : ℕ, a ^ ((2 : ℝ) ^ (j + 1)) ≤ δ := by
    refine ⟨J - 1, ?_⟩
    rwa [Nat.sub_add_cancel hJ]
  set j := Nat.find hex with hj
  have hjspec : a ^ ((2 : ℝ) ^ (j + 1)) ≤ δ := Nat.find_spec hex
  have hjlt : j < J := by
    by_contra hcon
    have : j ≤ J - 1 := Nat.find_min' hex (by rwa [Nat.sub_add_cancel hJ])
    omega
  refine ⟨j, hjlt, hjspec, ?_⟩
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · simpa [h0] using hhi
  · have hprev : ¬ a ^ ((2 : ℝ) ^ ((j - 1) + 1)) ≤ δ := Nat.find_min hex (by omega)
    rw [Nat.sub_add_cancel hpos] at hprev
    exact (not_le.mp hprev).le

/-! ## The per-block ledger -/

/-- **A block's loss, isolated: the lower end of the block bounds `C` by an `a`-power, with no
constant.**

`a ^ (2 ^ (j+1)) ≤ δ` together with the leaf's own `C ≤ δ ^ (-ε)` gives
`C ≤ a ^ (-(2 ^ (j+1) * ε))`.  This is the *only* place a block's angular exponent
`εs_j = 2 ^ (j+1) * ε` comes from, and it is charged to the configuration, not to a neighbouring
block. -/
theorem blockLoss {j : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {a δ C : ℝ≥0} (ha : 0 < a)
    (hlo : a ^ ((2 : ℝ) ^ (j + 1)) ≤ δ) (hC : C ≤ δ ^ (-ε)) :
    C ≤ a ^ (-((2 : ℝ) ^ (j + 1) * ε)) := by
  refine le_trans hC ?_
  have h1 : (δ : ℝ≥0) ^ (-ε) ≤ (a ^ ((2 : ℝ) ^ (j + 1))) ^ (-ε) := by
    rw [NNReal.rpow_neg, NNReal.rpow_neg]
    gcongr
  refine le_trans h1 (le_of_eq ?_)
  rw [← NNReal.rpow_mul]
  congr 1
  ring

/-- **A block's budget, isolated: the upper end of the block makes `c1 = δ ^ ε'` at least as small
as `a ^ (128 * 2 ^ j * ε)`.**

`δ ≤ a ^ (2 ^ j)` and `128 * ε ≤ ε'` give `δ ^ ε' ≤ a ^ (128 * 2 ^ j * ε)`.  The budget is a
quantity of the *statement* — `c1` is what the leaf's own conclusion allows — so it is independent
of every constant the slab layer later names.  That independence is what makes the split
non-circular: block `j`'s loss is paid here, and never out of another block's budget. -/
theorem blockBudget {j : ℕ} {ε ε' : ℝ} (hε : 0 < ε) (hgap : 128 * ε ≤ ε')
    {a δ : ℝ≥0} (ha : 0 < a) (ha1 : a ≤ 1) (hδ : δ ≤ a ^ ((2 : ℝ) ^ j)) :
    (δ : ℝ≥0) ^ ε' ≤ a ^ (128 * (2 : ℝ) ^ j * ε) := by
  have hε' : (0 : ℝ) < ε' := lt_of_lt_of_le (by positivity) hgap
  have hpow : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have h1 : (δ : ℝ≥0) ^ ε' ≤ (a ^ ((2 : ℝ) ^ j)) ^ ε' := NNReal.rpow_le_rpow hδ hε'.le
  have h2 : (a ^ ((2 : ℝ) ^ j)) ^ ε' = a ^ ((2 : ℝ) ^ j * ε') := (NNReal.rpow_mul _ _ _).symm
  have h3 : a ^ ((2 : ℝ) ^ j * ε') ≤ a ^ (128 * (2 : ℝ) ^ j * ε) :=
    NNReal.rpow_le_rpow_of_exponent_ge ha ha1 (by nlinarith)
  exact le_trans h1 (h2 ▸ h3)


/-- **Each block's loss is inside its own budget, with a factor-`64` margin.**

In block `j` the angular exponent the slab layer must be run at is `εs_j = 2 ^ (j+1) * ε`, forced
by the lower end of the block; the Item-1 budget exponent is `2 ^ j * ε' ≥ 128 * 2 ^ j * ε`, forced
by the upper end; and `Plank.slabwiseDensity_of_preassembly`'s `3 * ηL ≤ 4 * η + εwork` together
with that budget allows `ηL_j` up to `4 * η + 128 * 2 ^ j * ε + ε`.  The requirement
`εs_j < ηL_j` of `Plank.localAngleConcentration_of_preassemblyData` is therefore

```
2 ^ (j+1) * ε  <  4 * η + 128 * 2 ^ j * ε + ε ,
```

and it holds for every `j`, uniformly, because the loss doubles per block while the budget
multiplies by `128`.  **This is a per-block statement and nothing is summed**: a configuration lies
in one block and pays once.

Contrast `ShadedPlank.slabRoute_exponents_incompatible_at_small_eta`, which shows that a *single*
`εs` covering the whole regime cannot satisfy the same three constraints. -/
theorem blockLedger_margin (j : ℕ) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    (2 : ℝ) ^ (j + 1) * ε < 4 * η + 128 * (2 : ℝ) ^ j * ε + ε := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
  nlinarith [hpow, hε, hη]

/-- **The ladder has 12 blocks at the transverse branch's own exponents.**

At `η = 1/1000` and `ε = η/256` the top of the residual regime is
`(2 - 3η - ε)/(127 ε) ≈ 4026`, so `J = 12` blocks suffice — the concrete instance of the
`O(log (1/ε))` bound.

The contrast with `ShadedPlank.slabRoute_exponents_incompatible_at_small_eta` is worth stating at
these numbers.  A single instance had to run at `εs ≈ 0.0079` against a budget allowing only
`ηL ≤ 0.0045`.  Block `11`, the top of the ladder, runs at the comparable `εs = 2 ^ 12 * ε ≈ 0.016`
— but against `ηL ≤ 4η + 128 * 2 ^ 11 * ε + ε ≈ 1.03`, because at the top of the ladder `δ` is a
very high power of `a` and `c1 = δ ^ ε'` is correspondingly tiny.  **That is the whole mechanism:
the single-instance argument was forced to pair the worst-case loss with the best-case budget,
and the split pairs each loss with its own block's budget.** -/
theorem blockCount_at_consumer_exponents :
    (2 - 3 * (1 / 1000 : ℝ) - (1 / 256000 : ℝ)) / (127 * (1 / 256000 : ℝ)) ≤ 2 ^ (12 : ℕ) := by
  norm_num


/-! ## The reduction -/

/-- **The target, from `O(log (1/ε))` block-restricted instances.**

`H` is the target statement restricted to one dyadic block: it may assume, in addition to every
hypothesis of the target,

```
a ^ (2 ^ (j+1)) ≤ δ ,      δ ≤ a ^ (2 ^ j) ,      C ≤ a ^ (-(2 ^ (j+1) * ε)) ,
```

the third being the `a`-scale bound on the comparability constant that the block's *lower* end
supplies, with **no constant in front of it**.  The conclusion is the target *verbatim*.

Only `O(log (1/ε))` of the blocks are used: `ShadedPlank.exists_blockCount` picks `J` with
`2 ^ J` above `(2 - 3η - ε)/(127 ε)`, which
`ShadedPlank.rpow_le_of_budgetExcess` shows is the top of the residual regime.

**Where the finiteness of `J` is used, and where it is not.**  It is used in exactly one place: the
target must name a single `δthr` before seeing the configuration, and this proof takes the minimum
of the `J` block thresholds, which is positive because the family is finite.  It is *not* used to
sum any loss — the blocks are a case split, each configuration lies in exactly one of them, and its
loss is charged to its own `c1 = δ ^ ε'`.  See `ShadedPlank.blockLedger_margin` for the per-block
ledger and the factor-`64` margin.

Two further thresholds are combined in:
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_smallRadius`'s, for the configurations outside the
regime; and `432 ^ (-((2 + η)/(127 ε)))`, which makes the regime **empty** when `a > 432⁻¹` and so
lets `ShadedPlank.rpow_le_of_budgetExcess` assume `a ≤ 432⁻¹` and absorb its numeric constant into
one factor of `a`. -/
theorem reduction_to_slab_atTypicalAngle_of_dyadicBlocks.{u}
    (H :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (j : ℕ) (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr athr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧ 0 < athr ∧
    ∀ {ι : Type u} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (_hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
      a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
      Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
      (a ^ ((2 : ℝ) ^ (j + 1)) ≤ δ) →
      (δ ≤ a ^ ((2 : ℝ) ^ j)) →
      (C ≤ a ^ (-((2 : ℝ) ^ (j + 1) * ε))) →
      (a ≤ athr) →
    ∃ (s' : Finset ι)
      (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (c1 : ℝ≥0),
      0 < c1 ∧
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s' Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      (∀ x,
        ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε')) :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type u} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (_hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
      a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
      Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
    ∃ (s' : Finset ι)
      (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (c1 : ℝ≥0),
      0 < c1 ∧
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s' Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      (∀ x,
        ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε')  := by
  intro η ε ε' hη hε hε' hgap Ccard D
  classical
  obtain ⟨J, hJ1, hJtop⟩ := exists_blockCount η ε
  obtain ⟨δ0, h0pos, h0le, hnarrow⟩ :=
    reduction_to_slab_atTypicalAngle_of_smallRadius hη hε hε' hgap Ccard D
  have H' := fun (j : ℕ) => H (η := η) (ε := ε) (ε' := ε') hη hε hε' hgap j Ccard D
  choose db ab hdbpos hdble habpos hdb using H'
  -- the threshold that empties the regime when `a > 432⁻¹`
  set δA : ℝ≥0 := (432 : ℝ≥0) ^ (-((2 + η) / (127 * ε))) with hδA
  have hδApos : (0 : ℝ≥0) < δA := NNReal.rpow_pos (by norm_num)
  have hδAone : δA ≤ 1 :=
    NNReal.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.mpr (by positivity : (0 : ℝ) ≤ (2 + η) / (127 * ε)))
  -- the minimum of the `J` block thresholds
  have hne : (Finset.range J).Nonempty := ⟨0, Finset.mem_range.mpr hJ1⟩
  set δB : ℝ≥0 := (Finset.range J).inf' hne db with hδB
  have hδBpos : (0 : ℝ≥0) < δB := by
    rw [hδB, Finset.lt_inf'_iff]
    intro j _
    exact hdbpos j
  have hδBone : δB ≤ 1 := by
    obtain ⟨j, hj⟩ := hne
    exact le_trans (Finset.inf'_le _ hj) (hdble j)
  set aI : ℝ≥0 := (Finset.range J).inf' hne ab with haI
  have haIpos : (0 : ℝ≥0) < aI := by
    rw [haI, Finset.lt_inf'_iff]; intro j _; exact habpos j
  set δC : ℝ≥0 := aI ^ ((2 : ℝ) ^ J) with hδCdef
  have hδCpos : (0 : ℝ≥0) < δC := NNReal.rpow_pos haIpos
  refine ⟨min (min δ0 δA) (min δB δC), lt_min (lt_min h0pos hδApos) (lt_min hδBpos hδCpos),
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) h0le), ?_⟩
  intro ι s δ a b hab hb1 Y θ hθ1 C Y'' hδ hδa ha1 hδthr hwin hfull hma hmd h2 hcard
    hθlb hC1 hCδ hYref hYmult htyp hmaxA
  have hδ0 : δ ≤ δ0 := le_trans hδthr (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδAle : δ ≤ δA := le_trans hδthr (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδBle : δ ≤ δB := le_trans hδthr (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδCle : δ ≤ δC := le_trans hδthr (le_trans (min_le_right _ _) (min_le_right _ _))
  have ha : (0 : ℝ≥0) < a := lt_of_lt_of_le hδ hδa
  have hane : (a : ℝ≥0) ≠ 0 := ha.ne'
  have hδne : (δ : ℝ≥0) ≠ 0 := hδ.ne'
  have hδ1 : (δ : ℝ≥0) ≤ 1 := le_trans hδa ha1.le
  by_cases hcase : 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C * (θ * b) ≤ a ^ η * a
  · exact hnarrow s Y θ hθ1 C Y'' hδ hδa ha1 hδ0 hwin hfull hma hmd h2 hcard hθlb hC1 hCδ
      hYref hYmult htyp hmaxA hcase
  · -- the residual regime
    have hres := not_le.mp hcase
    -- `δ ^ ε' * C ≤ δ ^ (127 * ε)`, used twice
    have hδC : (δ : ℝ≥0) ^ ε' * C ≤ δ ^ (127 * ε) := by
      have h1 : (δ : ℝ≥0) ^ ε' * C ≤ δ ^ ε' * δ ^ (-ε) := by gcongr
      have h2 : (δ : ℝ≥0) ^ ε' * δ ^ (-ε) = δ ^ (ε' - ε) := by
        rw [← NNReal.rpow_add hδne]; ring_nf
      have h3 : (δ : ℝ≥0) ^ (ε' - ε) ≤ δ ^ (127 * ε) :=
        NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      exact le_trans h1 (h2 ▸ h3)
    -- `a > 432⁻¹` is impossible below the threshold `δA`
    have hasmall : a ≤ 432⁻¹ := by
      by_contra hbig
      rw [not_le] at hbig
      have hLHS : 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C * (θ * b)
          ≤ 432 * (δ : ℝ≥0) ^ (127 * ε) := by
        have haη : (a : ℝ≥0) ^ (4 * η) ≤ 1 := NNReal.rpow_le_one ha1.le (by positivity)
        have haε : (a : ℝ≥0) ^ ε ≤ 1 := NNReal.rpow_le_one ha1.le hε.le
        have hθb : (θ : ℝ≥0) * b ≤ 1 := by
          calc (θ : ℝ≥0) * b ≤ 1 * 1 := by gcongr
            _ = 1 := by ring
        calc 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C * (θ * b)
            ≤ 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C * 1 := by gcongr
          _ = 432 * ((δ : ℝ≥0) ^ ε' * C) * (a ^ (4 * η) * a ^ ε) := by ring
          _ ≤ 432 * ((δ : ℝ≥0) ^ ε' * C) * (1 * 1) := by gcongr
          _ = 432 * ((δ : ℝ≥0) ^ ε' * C) := by ring
          _ ≤ 432 * (δ : ℝ≥0) ^ (127 * ε) := by gcongr
      have hδpow : (δ : ℝ≥0) ^ (127 * ε) ≤ (432 : ℝ≥0) ^ (-(2 + η)) := by
        have := NNReal.rpow_le_rpow hδAle (by positivity : (0 : ℝ) ≤ 127 * ε)
        refine le_trans this (le_of_eq ?_)
        rw [hδA, ← NNReal.rpow_mul]
        congr 1
        field_simp
      have hRHS : (432 : ℝ≥0) ^ (-(1 + η)) ≤ a ^ η * a := by
        have h1 : ((432 : ℝ≥0)⁻¹) ^ η ≤ a ^ η := NNReal.rpow_le_rpow hbig.le hη.le
        have h2 : ((432 : ℝ≥0)⁻¹) ^ η * 432⁻¹ ≤ a ^ η * a := mul_le_mul' h1 hbig.le
        refine le_trans (le_of_eq ?_) h2
        rw [NNReal.inv_rpow, ← NNReal.rpow_neg]
        rw [show ((432 : ℝ≥0))⁻¹ = (432 : ℝ≥0) ^ (-(1 : ℝ)) by
          rw [NNReal.rpow_neg, NNReal.rpow_one]]
        rw [← NNReal.rpow_add (by norm_num : (432 : ℝ≥0) ≠ 0)]
        congr 1
        ring
      have hchain : 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C * (θ * b) ≤ a ^ η * a := by
        refine le_trans hLHS (le_trans ?_ hRHS)
        have key : (432 : ℝ≥0) * (432 : ℝ≥0) ^ (-(2 + η)) = (432 : ℝ≥0) ^ (-(1 + η)) := by
          have h : (432 : ℝ≥0) ^ (1 : ℝ) * (432 : ℝ≥0) ^ (-(2 + η))
              = (432 : ℝ≥0) ^ ((1 : ℝ) + (-(2 + η))) :=
            (NNReal.rpow_add (by norm_num) _ _).symm
          rw [NNReal.rpow_one] at h
          rw [h]
          congr 1
          ring
        calc 432 * (δ : ℝ≥0) ^ (127 * ε) ≤ 432 * (432 : ℝ≥0) ^ (-(2 + η)) := by gcongr
          _ = (432 : ℝ≥0) ^ (-(1 + η)) := key
      exact absurd hchain hcase
    -- the bottom of the ladder
    have hlow : a ^ ((2 - 3 * η - ε) / (127 * ε)) ≤ δ :=
      rpow_le_of_budgetExcess hε hgap hδ hδa ha1 hasmall hθ1 hb1 hCδ hres
    have hlow' : a ^ ((2 : ℝ) ^ J) ≤ δ :=
      le_trans (NNReal.rpow_le_rpow_of_exponent_ge ha ha1.le hJtop) hlow
    obtain ⟨j, hjJ, hjlo, hjhi⟩ := exists_dyadicBlock hJ1 hlow' hδa
    -- the block's `a`-scale bound on `C`
    have hCa : C ≤ a ^ (-((2 : ℝ) ^ (j + 1) * ε)) := by
      refine le_trans hCδ ?_
      have h1 : (δ : ℝ≥0) ^ (-ε) ≤ (a ^ ((2 : ℝ) ^ (j + 1))) ^ (-ε) := by
        rw [NNReal.rpow_neg, NNReal.rpow_neg]
        gcongr
      refine le_trans h1 (le_of_eq ?_)
      rw [← NNReal.rpow_mul]
      congr 1
      ring
    have haathr : a ≤ ab j := by
      have hpow : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
      have h1 : a ^ ((2 : ℝ) ^ J) ≤ aI ^ ((2 : ℝ) ^ J) :=
        le_trans hlow' (le_trans hδCle (le_of_eq hδCdef))
      have h2 : a ≤ aI := by
        by_contra hcon
        rw [not_le] at hcon
        exact absurd h1 (not_le.mpr (NNReal.rpow_lt_rpow hcon hpow))
      exact le_trans h2 (Finset.inf'_le _ (Finset.mem_range.mpr hjJ))
    exact hdb j s Y θ hθ1 C Y'' hδ hδa ha1 (le_trans hδBle (Finset.inf'_le _
      (Finset.mem_range.mpr hjJ))) hwin hfull hma hmd h2 hcard hθlb hC1 hCδ hYref hYmult
      htyp hmaxA hjlo hjhi hCa haathr

/-! ## Fidelity pin for the 2026-09 threading -/

/-- **Tripwire / fidelity check for the absolute plank-angle binder.**

Granting `Kakeya.HasMaxPlankAngleBound … θ 1` universally and for free, the *threaded*
`ShadedPlank.reduction_to_slab_atTypicalAngle` **is** the pre-threading statement: every other
binder, every hypothesis and the whole conclusion are passed through verbatim.  So the new binder is
the only thing added, and an edit that quietly weakened something else as well would break this pin.

`hmaxUniv` is of course false — a fibre containing two planks at a large mutual angle violates it —
so combining this with anything refuting the old statement would merely reprove `¬ hmaxUniv`, which
is sound.  This is the `Kakeya.ThinCase.Refute.statement_of_universal_loc` device, applied at the
Section-6 interface, and it is what a plain same-type tripwire cannot carry across a new binder. -/
theorem statement_of_universal_hmaxAbs.{u}
    (hmaxUniv : ∀ {ι : Type u} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (s : Finset ι) (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (P : ι → Plank a b hab hb1) (θ : ℝ≥0),
      Kakeya.HasMaxPlankAngleBound s Y'' P θ 1)
    (H :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type u} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (_hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
      a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
      Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
    ∃ (s' : Finset ι)
      (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (c1 : ℝ≥0),
      0 < c1 ∧
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s' Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      (∀ x,
        ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (c1 : ENNReal) * a ^ (4 * η) * a ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε')) :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type u} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (_hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
      a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
    ∃ (s' : Finset ι)
      (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (c1 : ℝ≥0),
      0 < c1 ∧
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s' Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      (∀ x,
        ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (c1 : ENNReal) * a ^ (4 * η) * a ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε') := by
  intro η ε ε' hη hε hε' hgap Ccard D
  obtain ⟨δthr, hpos, hone, hH⟩ := H hη hε hε' hgap Ccard D
  refine ⟨δthr, hpos, hone, ?_⟩
  intro ι s δ a b hab hb1 Y θ hθ1 C Y'' hδ hδa ha1 hδthr hwin hfull hma hmd h2 hcard
    hθlb hC1 hCδ hYref hYmult htyp
  exact hH s Y θ hθ1 C Y'' hδ hδa ha1 hδthr hwin hfull hma hmd h2 hcard hθlb hC1 hCδ
    hYref hYmult htyp (hmaxUniv s Y'' (ShadedPlank.planks Y) θ)


end ShadedPlank

end
