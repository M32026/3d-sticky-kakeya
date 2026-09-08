/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallPolylogAbsorber
public import Kakeya.DimensionThree.MainLemma2.ThinConstantProducer

/-!
# Wiring the polylog absorber: the cardinality discharge and the relative-scale change of variable

What that payoff still carries is

* a **cardinality hypothesis** `hN : ∀ d, 0 < d → d ≤ 1 → (N d : ℝ) ≤ (1/d)^p`, which
   measured to be *half the blocker* rather than a detail: `L`'s first factor is
  `1 + logb 2 (card · X^ϖ)`, so with `card` unbounded there is no `δ`-free slope and **no absorber
  of any degree can work**;
* a **scale mismatch**: Lemma 9.2's retention is read at the relative scale `d = δ/r₁`, while the
  `Cg` obligation is stated at `δ`.

## O2 — the cardinality discharge

The existing `Kakeya.VeryNotSticky.eventually_card_segs_le`
(`M/ThinConstantProducer.lean`) proves `#(bd.segs B) ≤ 1 · δ⁻¹^4` eventually, i.e. `p = 4`. It is
**eventual in `δ` and quantified over `cfg`, `bd`, `B` inside the filter**, whereas `hN` is a
*pointwise, `cfg`-free* hypothesis on a single function `N : NNReal → ℕ`. The two shapes do not
meet, and no choice of `N` bridges them, because `#(bd.segs B)` is not a function of `δ` alone.

The fix is to move the `∀ n` inside the filter. Nothing in the absorber's eventual step mentions
the cardinality: `Kakeya.VeryNotSticky.uniformLossBound_le_polylog_pow` is *pointwise* in `d`, and
only `(A + B · logb 2 (1/d))^k ≤ d^{-ε}` is eventual. Factoring at that seam gives
`Kakeya.VeryNotSticky.eventually_uniformLossBound_le_rpow_neg_of_card`, which is **uniform in the
cardinality** and therefore composes with the existing count by `filter_upwards`.

## O3 — the change of variable `d = δ/r₁ → δ`

 supplied **both** adapters and this file uses **exactly those two**, writing no
third:

* `Kakeya.VeryNotSticky.exists_threshold_of_eventually_nhdsGT` turns the absorber's `∀ᶠ` into an
  explicit threshold, which is what a *derived* scale needs — used inside
  `Kakeya.VeryNotSticky.eventually_of_relScale`;
* `Kakeya.VeryNotSticky.le_rpow_neg_of_le_coarser` transports a `c^{-ε}` bound to `d^{-ε}` for
  `d ≤ c`, applied at `c = δ/r₁ ≥ δ` — used inside
  `Kakeya.VeryNotSticky.eventually_uniformLossBound_relScale_le_rpow_neg`.

What  item 3 left as "a `cfg`-level fact, not an analytic one" is
`Kakeya.VeryNotSticky.eventually_relScale_le`: with `r₁ = δ^{exscal}` and `exscal < 1`,
`δ/r₁ = δ^{1 - exscal} → 0`, which the existing
`Kakeya.VeryNotSticky.eventually_nnreal_mul_rpow_le_rpow` supplies at `p = 1 - exscal`, `q = 0`.

One further piece the obligation list did not name: the count is known **at `δ`** while the loss
is read **at `δ/r₁`**, and `δ/r₁ ≥ δ` makes `δ^{-4}` the *weaker* bound in the relative variable.
The honest relative exponent is therefore `4/(1 - exscal)`, and
`Kakeya.VeryNotSticky.inv_rpow_relScale` is the exact identity
`((δ/r₁)⁻¹)^{p/(1-exscal)} = (δ⁻¹)^p`, not an inequality — no slack is spent.

## What this does **not** do

It does **not** close `bd.Cg ≤ δ^{-εg}`, and cannot: `Kakeya.VeryNotSticky.exists_ballData_general`
does not exist,
and the existing conjunct 1 of `Kakeya.VeryNotSticky.SideDataObligations` still reads `bd.Cg = Cg`
at a `δ`-free `Cg`. There is no consumer to close against. See
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped NNReal ENNReal Topology

universe u

namespace Kakeya.VeryNotSticky

/-! ### O2: the absorber's eventual step, separated from the cardinality -/

/-- **The absorber's eventual step, with no cardinality in sight.** A degree-`k` polylog in the
normal form `A + B · logb 2 (1/d)` is eventually below `d^{-ε}`, as an `ENNReal.ofReal`.

This is `Kakeya.VeryNotSticky.eventually_le_rpow_neg_of_polylog_pow` at the *maximal* admissible
`f`, namely `f d = ((A + B · logb 2 (1/d))^k).toNNReal`; the hypothesis `hf` of the absorber then
holds with **equality** on `(0, 1]`, because `hA`, `hB` and `d ≤ 1` force the bracket
non-negative, so `Real.toNNReal` truncates nothing. Every later consumer factors through this and
therefore never has to re-run the `𝓝[>]0 ⇄ atTop` transfer.

`hA : 0 ≤ A` and `hB : 0 ≤ B` are the absorber's own hypotheses and are load-bearing twice over:
they license the linearisation inside the absorber, and here they are what makes the truncation
vacuous. `hε : 0 < ε` is what makes `d^{-ε}` beat a fixed power of a logarithm. -/
theorem eventually_ofReal_polylog_pow_le_rpow_neg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ENNReal.ofReal ((A + B * Real.logb 2 ((d : ℝ))⁻¹) ^ k) ≤ (d : ENNReal) ^ (-ε) := by
  have h := eventually_le_rpow_neg_of_polylog_pow
    (f := fun d : NNReal => ((A + B * Real.logb 2 ((d : ℝ))⁻¹) ^ k).toNNReal)
    (A := A) (B := B) (k := k) hA hB ?_ hε
  · filter_upwards [h] with d hd
    simpa [ENNReal.ofReal] using hd
  · intro d hd hd1
    have hd0 : (0 : ℝ) < (d : ℝ) := hd
    have hd1' : (d : ℝ) ≤ 1 := hd1
    have hinv1 : (1 : ℝ) ≤ ((d : ℝ))⁻¹ := by
      rw [one_le_inv_iff₀]; exact ⟨hd0, hd1'⟩
    have hΛ : 0 ≤ Real.logb 2 ((d : ℝ))⁻¹ := Real.logb_nonneg (by norm_num) hinv1
    have hx : (0 : ℝ) ≤ (A + B * Real.logb 2 ((d : ℝ))⁻¹) ^ k :=
      pow_nonneg (by have := mul_nonneg hB hΛ; linarith) k
    rw [Real.coe_toNNReal']
    exact max_le le_rfl hx

/-- **O2, the reusable half: the loss bound is absorbed uniformly in the cardinality.**

`Kakeya.VeryNotSticky.eventually_uniformLossBound_le_rpow_neg` takes the cardinality control as a
*pointwise* hypothesis on a function `N : NNReal → ℕ` of the scale alone. The existing count
`Kakeya.VeryNotSticky.eventually_card_segs_le` is not of that shape and cannot be made so:
`#(bd.segs B)` depends on `cfg`, `bd` and `B`, all of which the existing statement quantifies
*inside* the filter. Here the `∀ n` is moved inside the filter instead, which is sound precisely
because the absorber's eventual step
(`Kakeya.VeryNotSticky.eventually_ofReal_polylog_pow_le_rpow_neg`) does not mention `n` at all:
the `n`-dependence is entirely inside the pointwise
`Kakeya.VeryNotSticky.uniformLossBound_le_polylog_pow`.

Which hypothesis forces what. `hε : 0 < ε` is the only hypothesis, and it is exactly the
absorber's. `p` is free: it is *not* a hypothesis but a parameter of the conclusion, and it is
where the caller's cardinality exponent enters (`p = 4` from the existing count, at the absolute
scale). `dim` is free. No sign condition on `ϖ` is needed —  deleted that binder
rather than renaming it, and this lemma inherits the generality. -/
theorem eventually_uniformLossBound_le_rpow_neg_of_card (dim : ℕ) {ϖ p ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ∀ n : ℕ, ((n : ℝ) ≤ ((d : ℝ))⁻¹ ^ p) →
      ((uniformLossBound dim n d ϖ : NNReal) : ENNReal) ≤ (d : ENNReal) ^ (-ε) := by
  -- `∀ᶠ d in 𝓝[>] 0, d ≤ 1`, inlined exactly as the four existing `MainLemma2` sites do
  -- (`SetupAssembly.lean:123`, `SetupCarrierIsland.lean:554`, `SetupProduce.lean:781`,
  -- `Reduction/Envelope.lean:178`) rather than adding a fifth named near-duplicate of
  -- `Kakeya.ml1Boot.eventually_le_one_nhdsGT`, which lives in the `MainLemma1` module tree.
  have hle1 : ∀ᶠ d : NNReal in 𝓝[>] 0, d ≤ 1 :=
    Filter.eventually_of_mem
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : NNReal) < 1 by norm_num)))
      (fun _ hd => le_of_lt hd)
  filter_upwards [eventually_ofReal_polylog_pow_le_rpow_neg
      (A := lossPolylogConst dim ϖ) (B := lossPolylogSlope dim ϖ p) (k := dim + 1)
      (le_trans zero_le_one (one_le_lossPolylogConst dim ϖ))
      (le_trans zero_le_one (one_le_lossPolylogSlope dim ϖ p)) hε,
    self_mem_nhdsWithin, hle1] with d hpoly hd0 hd1
  intro n hn
  have hreal := uniformLossBound_le_polylog_pow (dim := dim) (n := n) (d := d) (ϖ := ϖ) (p := p)
    (by simpa using hd0) hd1 hn
  calc ((uniformLossBound dim n d ϖ : NNReal) : ENNReal)
      = ENNReal.ofReal ((uniformLossBound dim n d ϖ : NNReal) : ℝ) :=
        ENNReal.ofReal_coe_nnreal.symm
    _ ≤ ENNReal.ofReal ((lossPolylogConst dim ϖ +
          lossPolylogSlope dim ϖ p * Real.logb 2 ((d : ℝ))⁻¹) ^ (dim + 1)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ ≤ (d : ENNReal) ^ (-ε) := hpoly

/-- **O2 at the absolute scale, wired to the existing count at `p = 4`.**

`Kakeya.VeryNotSticky.eventually_card_segs_le` gives `#(bd.segs B) ≤ 1 · δ⁻¹^4` for every `cfg` at
density exponent `η ≤ 1`; that is `p = 4`, and `hη1 : η ≤ 1` is the *only* hypothesis forcing the
constant `4` — it is the existing count's own side condition, discharged at any real call site from
`Kakeya.VeryNotSticky.CaseParams` (`6η < exscal` with `exscal < 1/2` gives `η < 1/12`), exactly as
`Kakeya.VeryNotSticky.thinConstantObligation_of_card_bodies` does.

The cast is the only content: the existing bound is an `NNReal` inequality against the *natural*
power `cfg.δ⁻¹ ^ (4 : ℕ)` with a redundant `1 *`, while the absorber reads a *real* `rpow`
`(δ⁻¹) ^ (4 : ℝ)`. -/
theorem eventually_card_segs_le_rpow {η : ℝ} (hη1 : η ≤ 1) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → ∀ B ∈ bd.bs,
        (((bd.segs B).card : ℕ) : ℝ) ≤ ((cfg.δ : ℝ))⁻¹ ^ (4 : ℝ) := by
  filter_upwards [eventually_card_segs_le (η := η) hη1] with δ hseg
  intro cfg bd hδ hη B hB
  have h := hseg cfg bd hδ hη B hB
  have h' : (((bd.segs B).card : ℕ) : ℝ) ≤ ((1 : NNReal) * cfg.δ⁻¹ ^ 4 : NNReal) := by
    exact_mod_cast h
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  push_cast at h' ⊢
  simpa using h'

/-- **O2, complete, at the absolute scale.** The uniformised Lemma 9.2 loss of every ball of every
`cfg` at density exponent `η ≤ 1`, read at the *absolute* scale `δ`, is eventually below `δ^{-ε}`
for every `ε > 0`. This is  obligation **O2** discharged: no cardinality
hypothesis survives. -/
theorem eventually_uniformLossBound_segs_le_rpow_neg {η : ℝ} (hη1 : η ≤ 1) {ϖ ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → ∀ B ∈ bd.bs,
        ((uniformLossBound 3 ((bd.segs B).card) cfg.δ ϖ : NNReal) : ENNReal) ≤
          (cfg.δ : ENNReal) ^ (-ε) := by
  filter_upwards [eventually_card_segs_le_rpow (η := η) hη1,
    eventually_uniformLossBound_le_rpow_neg_of_card 3 (ϖ := ϖ) (p := (4 : ℝ)) hε] with δ hseg habs
  intro cfg bd hδ hη B hB
  subst hδ
  exact habs _ (hseg cfg bd rfl hη B hB)

/-! ### O3: the relative scale `δ/r₁` -/

/-- `δ/r₁ = δ^{1 - exscal}` for `r₁ = δ^{exscal}` and `δ > 0`. `hδ` is what licenses
`NNReal.rpow_sub`; at `δ = 0` the left side is `0/0 = 0` and the right side is `0`, so the
identity happens to survive, but the *proof* does not, and no consumer needs `δ = 0`. -/
theorem relScale_eq {δ : NNReal} (hδ : 0 < δ) (exscal : ℝ) :
    δ / δ ^ exscal = δ ^ (1 - exscal) := by
  rw [NNReal.rpow_sub hδ.ne', NNReal.rpow_one]

/-- **The relative scale tends to `0`.**  item 3 named this as the one remaining
piece of the change of variable and classified it correctly as `cfg`-level rather than analytic:
`δ/r₁ = δ^{1-exscal}`, and `exscal < 1` makes the exponent positive, so the existing
`Kakeya.VeryNotSticky.eventually_nnreal_mul_rpow_le_rpow` applies at `p = 1 - exscal`, `q = 0`
with the constant `d₀⁻¹`.

`hex1 : exscal < 1` is the hypothesis forcing everything: at `exscal = 1` the relative scale is
identically `1` and the statement is false for `d₀ < 1`; at `exscal > 1` it diverges. `hd₀`
forces `d₀ ≠ 0` for the final division. -/
theorem eventually_relScale_le {exscal : ℝ} (hex1 : exscal < 1) {d₀ : NNReal} (hd₀ : 0 < d₀) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, δ / δ ^ exscal ≤ d₀ := by
  filter_upwards [eventually_nnreal_mul_rpow_le_rpow d₀⁻¹ (p := 1 - exscal) (q := 0)
      (by linarith), self_mem_nhdsWithin] with δ h hδ0
  have hδ : (0 : NNReal) < δ := by simpa using hδ0
  rw [NNReal.rpow_zero] at h
  rw [← div_eq_inv_mul] at h
  rw [relScale_eq hδ]
  exact (div_le_one hd₀).mp h

/-- The relative scale is positive, so it lies in the punctured neighbourhood the absorber's
threshold is stated on. -/
theorem eventually_relScale_pos {exscal : ℝ} :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, (0 : NNReal) < δ / δ ^ exscal := by
  filter_upwards [self_mem_nhdsWithin] with δ hδ0
  have hδ : (0 : NNReal) < δ := by simpa using hδ0
  exact div_pos hδ (NNReal.rpow_pos hδ)

/-- **The change of variable `δ ↦ δ/r₁`, as a filter statement.** Anything that holds eventually
in the punctured neighbourhood of `0` holds eventually at the *relative* scale.

This is where 's first adapter
`Kakeya.VeryNotSticky.exists_threshold_of_eventually_nhdsGT` is used, and it is used for the
reason its docstring gives: `∀ᶠ c in 𝓝[>] 0` is the wrong shape for a *derived* scale, since one
cannot `filter_upwards` along a substitution. Converting to an explicit threshold `d₀` first, and
then reaching `d₀` with `Kakeya.VeryNotSticky.eventually_relScale_le`, is the whole proof.

`hex1 : exscal < 1` is inherited from `Kakeya.VeryNotSticky.eventually_relScale_le` and is the
only hypothesis; note in particular that `0 ≤ exscal` is **not** needed here (it is needed only by
`Kakeya.VeryNotSticky.le_relScale`, for the transport back). -/
theorem eventually_of_relScale {exscal : ℝ} (hex1 : exscal < 1) {P : NNReal → Prop}
    (h : ∀ᶠ c : NNReal in 𝓝[>] 0, P c) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, P (δ / δ ^ exscal) := by
  obtain ⟨d₀, hd₀0, _, hP⟩ := exists_threshold_of_eventually_nhdsGT h
  filter_upwards [eventually_relScale_le hex1 hd₀0, eventually_relScale_pos (exscal := exscal)]
    with δ hle hpos
  exact hP _ hpos hle

/-- `δ ≤ δ/r₁`: the relative scale is the **coarser** one, which is what makes
`Kakeya.VeryNotSticky.le_rpow_neg_of_le_coarser` applicable in the direction needed.

`hδ1 : δ ≤ 1` and `hex0 : 0 ≤ exscal` together give `r₁ = δ^{exscal} ≤ 1`; both do work, since at
`δ > 1` or `exscal < 0` one has `r₁ > 1` and the inequality reverses. `hδ` licenses the division.
For an actual `cfg` these are `cfg.hδ1` and `cfg.hexscal.le`. -/
theorem le_relScale {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {exscal : ℝ} (hex0 : 0 ≤ exscal) :
    δ ≤ δ / δ ^ exscal := by
  rw [le_div_iff₀ (NNReal.rpow_pos hδ)]
  calc δ * δ ^ exscal ≤ δ * 1 := by
        gcongr
        exact NNReal.rpow_le_one hδ1 hex0
    _ = δ := mul_one δ

/-- **The exact exponent identity behind the change of variable.**
`((δ/r₁)⁻¹)^{p/(1-exscal)} = (δ⁻¹)^p`, an *equality*, not an inequality: passing the cardinality
bound from the absolute scale to the relative one costs nothing, provided the exponent is
rescaled by `1/(1 - exscal)`.

This is the piece 's obligation list did not name. The count is known at `δ`
(`#segs B ≤ δ^{-4}`) while the loss is read at `δ/r₁ ≥ δ`, so `δ^{-4}` is the *weaker* bound in
the relative variable and the honest relative exponent is `4/(1 - exscal)`, not `4`.

`hex1 : exscal < 1` forces `1 - exscal ≠ 0`, without which the rescaled exponent does not exist;
`hδ` is needed for `relScale_eq`. -/
theorem inv_rpow_relScale {δ : NNReal} (hδ : 0 < δ) {exscal p : ℝ} (hex1 : exscal < 1) :
    (((δ / δ ^ exscal : NNReal) : ℝ))⁻¹ ^ (p / (1 - exscal)) = ((δ : ℝ))⁻¹ ^ p := by
  have hne : (1 : ℝ) - exscal ≠ 0 := by linarith
  have ht : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  have hcast : (((δ / δ ^ exscal : NNReal) : ℝ)) = ((δ : ℝ)) ^ (1 - exscal) := by
    rw [relScale_eq hδ, NNReal.coe_rpow]
  rw [hcast, ← Real.rpow_neg_one ((δ : ℝ) ^ (1 - exscal)), ← Real.rpow_mul ht,
    ← Real.rpow_mul ht, ← Real.rpow_neg_one (δ : ℝ), ← Real.rpow_mul ht]
  congr 1
  field_simp

/-- **O2 + O3 composed, at general `dim` and general cardinality exponent.** The uniformised
Lemma 9.2 loss read at the **relative** scale `δ/r₁`, under a cardinality bound stated at the
**absolute** scale `δ`, is eventually below `δ^{-ε}` for every `ε > 0`.

Both of 's adapters are used here and no third was written: the change of variable
is `Kakeya.VeryNotSticky.eventually_of_relScale` (built on adapter 1,
`exists_threshold_of_eventually_nhdsGT`), and the transport of the conclusion from `(δ/r₁)^{-ε}`
back to `δ^{-ε}` is adapter 2, `Kakeya.VeryNotSticky.le_rpow_neg_of_le_coarser`, applied at
`c = δ/r₁`, `d = δ` — legitimate exactly because `δ ≤ δ/r₁`
(`Kakeya.VeryNotSticky.le_relScale`).

Which hypothesis forces what.

* `hex0 : 0 ≤ exscal` is used **only** by `Kakeya.VeryNotSticky.le_relScale`, i.e. only to know
  that the relative scale is the coarser one. It cannot be dropped: at `exscal < 0` the ball
  radius exceeds `1`, `δ/r₁ < δ`, and adapter 2 runs the wrong way.
* `hex1 : exscal < 1` is used **twice**: by `eventually_of_relScale` (the relative scale must tend
  to `0`) and by `inv_rpow_relScale` (the rescaled exponent must exist).
* `hε : 0 < ε` is the absorber's.
* `p` is a free parameter of the conclusion, not a hypothesis. It appears in the *absolute*
  variable; the lemma rescales it to `p/(1 - exscal)` internally.

For an actual `cfg` with `cfg.exscal = exscal`, `hex0` is `cfg.hexscal.le`; `hex1` is the
`Kakeya.VeryNotSticky.CaseParams` field `scale : exscal < 1/2`. The `exscal` binder must sit
*outside* the filter because `cfg` is quantified *inside* it — that quantifier order is the
existing convention (`Kakeya.VeryNotSticky.thinConstantObligation_of_card_bodies`,
`Kakeya.VeryNotSticky.eventually_C₀_mul_le_half_r₁`), which is why `hex0` cannot simply be read
off `cfg`. -/
theorem eventually_uniformLossBound_relScale_le_rpow_neg (dim : ℕ) {exscal ϖ p ε : ℝ}
    (hex0 : 0 ≤ exscal) (hex1 : exscal < 1) (hε : 0 < ε) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ n : ℕ, ((n : ℝ) ≤ ((δ : ℝ))⁻¹ ^ p) →
      ((uniformLossBound dim n (δ / δ ^ exscal) ϖ : NNReal) : ENNReal) ≤
        (δ : ENNReal) ^ (-ε) := by
  have hle1 : ∀ᶠ δ : NNReal in 𝓝[>] 0, δ ≤ 1 :=
    Filter.eventually_of_mem
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : NNReal) < 1 by norm_num)))
      (fun _ hd => le_of_lt hd)
  filter_upwards [eventually_of_relScale (exscal := exscal) hex1
      (eventually_uniformLossBound_le_rpow_neg_of_card dim (ϖ := ϖ)
        (p := p / (1 - exscal)) hε),
    self_mem_nhdsWithin, hle1] with δ habs hδ0 hδ1
  intro n hn
  have hδ : (0 : NNReal) < δ := by simpa using hδ0
  refine le_rpow_neg_of_le_coarser hε.le (le_relScale hδ hδ1 hex0) (habs n ?_)
  rw [inv_rpow_relScale hδ hex1]
  exact hn

/-- **O2 + O3, complete, at `dim = 3` and the existing count's `p = 4`.** For every `cfg` at
density exponent `η ≤ 1` and coarse-scale exponent `exscal`, every ball's uniformised Lemma 9.2
loss — read at the relative scale `cfg.δ / cfg.r₁` where Lemma 9.2's retention actually lives —
is eventually below `cfg.δ^{-ε}` for every `ε > 0`, with **no cardinality hypothesis and no
scale mismatch left**.

The relative cardinality exponent is `4/(1 - exscal)` internally
(`Kakeya.VeryNotSticky.inv_rpow_relScale`); nothing here fixes `ϖ`, so this holds at the bias
exponent Lemma 9.2 is applied at, whatever it is. -/
theorem eventually_uniformLossBound_segs_relScale_le_rpow_neg {η exscal : ℝ}
    (hη1 : η ≤ 1) (hex0 : 0 ≤ exscal) (hex1 : exscal < 1) {ϖ ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → ∀ B ∈ bd.bs,
        ((uniformLossBound 3 ((bd.segs B).card) (cfg.δ / cfg.r₁) ϖ : NNReal) : ENNReal) ≤
          (cfg.δ : ENNReal) ^ (-ε) := by
  filter_upwards [eventually_card_segs_le_rpow (η := η) hη1,
    eventually_uniformLossBound_relScale_le_rpow_neg 3 (ϖ := ϖ) (p := (4 : ℝ))
      hex0 hex1 hε] with δ hseg habs
  intro cfg bd hδ hη hex B hB
  have hr : cfg.r₁ = cfg.δ ^ exscal := by rw [VeryNotSticky.r₁, hex]
  rw [hr]
  subst hδ
  exact habs _ (hseg cfg bd rfl hη B hB)

end Kakeya.VeryNotSticky
