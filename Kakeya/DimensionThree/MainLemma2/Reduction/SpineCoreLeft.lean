/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCorePrelim

/-!
# Branch (i) of a `Kakeya.ML2Assembly.GeometricCoreAt` producer: the left disjunct

Rows **GC-L1** – **GC-L5** of the Section-9 geometric-core plan, i.e. GWZ `section9.tex` lines
55–61: *"if the dividing-scales dichotomy returns alternative (i), then by Theorem 7.3(B) the
multiplicity is already `δ^{-ε}` and we are done."*

Everything here sits on top of `Kakeya.ML2Core.eventually_dividingScalesPackage_dim3` and
`Kakeya.ML2Core.losses_of_dividingScalesOutput` (rows GC-P1/GC-P2).  Nothing here builds a
hierarchy, a spine, or a shading; all of that is the package's.

## The four steps, and the exponent each spends

Write `ν = η 0 = Kakeya.ML2Spine.spineNu β ϖ ε₁ gain dens`, `c₃`, `C₃` for the two dimensional
tube-volume constants, `P = (log₂ #𝕋 + 1)^{2 ssfGridLen δ + 2}` for the shaded-uniformization
polylogarithm and `λ ≥ δ^ν/2` for the dense-shading level.

1. **GC-L1**, `Kakeya.ML2Core.exists_multiplicity_quarter` — GWZ Theorem 7.3(B) read at the
   absolute accuracy `β/4`.  The one input the package does not hand over directly is the
   *fullness floor* `δ^{2ν} ≤ λ'(u', W)` that
   `Kakeya.ML2Reduction.exists_everyScale_multiplicity_le` consumes; it is manufactured here from
   the package's `λ ≤ P · λ'(u', W)` and `δ^ν ≤ 2 λ` against the threshold `2 P ≤ δ^{-ν}`
   (`Tube.exists_threshold_polylog_pow_ssfGridLen_le` at `A = 2`, `m = 2`, `K₀ = 4`).  Reading the
   hypotheses at `2ν` rather than at `ν` is what buys that threshold, and `2ν ≤ ε₁` is free from
   `Kakeya.ML2Spine.IsSpine` (`rung_mono`, `rung_top`, `div_le`, `eps₂_le_everyScale` give
   `ν ≤ ε₁/25`).  **Spends `ν`.**
2. **GC-L2**, `Kakeya.ML2Core.sum_shade_le_shadingBridgeLoss` — the mass chain, in exactly the
   shape `Kakeya.ML2Shading.shadingBridgeLoss · M` that
   `Kakeya.ML2Shading.exists_threshold_shadingBridgeLoss_le` absorbs, **at `K = 2`**.  The `2` is
   *not* the mass-banding constant of `Kakeya.ML2Shaded.exists_massBanded_shadeRefinement`; it is
   the dense-shading discard of `Kakeya.ML2Shaded.exists_denseShading_refinement`, which GC-P1
   already paid.  See "why not the banded route" below.  **Spends nothing new.**
3. **GC-L3**, `Kakeya.ML2Core.sum_shade_le_rpow_of_chain` — the absorption.  Three factors are
   cleared: the shading-bridge loss at `a` (its own threshold), the multiplicity `M ≤ δ^{-κ}`, and
   the two `ν`'s that division by `λ ≥ δ^ν/2` costs (one for `λ⁻¹`, one for the `2`).  Output
   exponent `a + κ + ν + ν`.  **Spends `2ν`.**
4. **GC-L4**, `Kakeya.ML2Core.dichotomyLeft_of_rpow_bound` —
   `Kakeya.ML2Shading.dichotomyLeft_of_bridge` at `ε₀ = β/2`, plus the one arithmetic
   `b ≤ ε₀`.  **Spends nothing.**
5. **GC-L5**, `Kakeya.ML2Core.exists_dichotomyLeft_or_window_dim3` — the four composed on the
   package, with the pushback to `(𝕋, Y)` being GC-P1's three loss clauses and nothing else.

The whole left branch therefore costs

`β/4` (7.3(B)) `+ 2ν` (the package's cardinality loss at `α = ν`) `+ ν` (`totalLoss`)
`+ ν` (the shading bridge's own budget) `+ 2ν` (division by `λ`) `= β/4 + 6ν`,

and `Kakeya.ML2Inputs.spineNu_le_div_48000` (`ν ≤ β/48000`) closes it inside `β/2` with a margin of
`β/4 − β/8000`.

## Why this file does *not* take the banded route

The plan's row GC-L2 asks for the `hbr` binder of
`Kakeya.ML2Shading.sum_shade_le_of_everyScale_banded` to be discharged.  That binder is
`∀ u ⊆ 𝕋, HasComparableDensities 2 u Y → ∃ u' ⊆ u, …, μ(u', Y') ≤ M`, with `A`, `B`, `M` bound
**before** `u`.  Its `M` is the output of GWZ Theorem 7.3(B), whose fullness hypothesis
`δ^{2ν} ≤ λ'(u', W)` is derived (step 1 above) from the dense-shading level of the family it is run
on — and for an `hbr`-supplied `u` that level is `λ(u, Y)/2`, which comparability at the absolute
constant `2` does not bound below by any power of `δ`.  So no `δ`-free-in-`u` `M` better than the
trivial `μ ≤ #u ≤ δ^{-4}` is available from the existing toolkit, and `δ^{-4}` is far outside `β/2`.

The banded route is also **unnecessary**, and that is the substantive point: the cardinality → mass
conversion it exists to condition is already performed by GC-P1, through
`Kakeya.ML2Shaded.sum_shade_le_of_card_le` against the *one-sided pointwise*
`Kakeya.ML2Shaded.HasDenseShading` rather than against two-sided comparability.  So the aggregate-
versus-pointwise trap that `Kakeya.ML2Shaded.not_hasComparableDensities_of_aggregate_retention`
records is avoided upstream, at the absolute cost `2`, and no logarithm
(`Kakeya.ML2Shaded.massBandLoss`) is charged at all.  The loss this file absorbs is nevertheless
literally `Kakeya.ML2Shading.shadingBridgeLoss n A 2 (log₂ #𝕋) (ssfGridLen δ)` — the banded shape
at `K = 2` — so the threshold lemma the plan names is the one used.

## `ε`-discipline

No statement here has an `ε` binder.  `ε₁` is the exponent
`Kakeya.ML2Reduction.exists_everyScale_multiplicity_le` returns at the accuracy `β/4`, a `β`-only
number, and every other exponent is `β`, `ν` or a sum of them.
`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy` and
`Kakeya.ML2Reduction.no_epsFree_drop_of_outer_everyScale` are untouched: `ε₁` is not driven to `0`.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ShadedBody ConvexSpaceBody
open Tube ShadedTube

universe u w

namespace Kakeya.ML2Core

variable
  {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-! ### An `ENNReal` bookkeeping lemma for `δ`-powers -/

omit [Nontrivial E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- `δ`-powers multiply, inside `ENNReal.ofReal`.  Used four times below and nowhere else; the
hypothesis `0 < δ` is what `Real.rpow_add` needs. -/
theorem ofReal_rpow_mul {δ : NNReal} (hδ0 : 0 < δ) (x y : ℝ) :
    ENNReal.ofReal ((δ : ℝ) ^ x) * ENNReal.ofReal ((δ : ℝ) ^ y)
      = ENNReal.ofReal ((δ : ℝ) ^ (x + y)) := by
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδR.le _), ← Real.rpow_add hδR]

/-! ### GC-L1: GWZ Theorem 7.3(B) at the absolute accuracy `β/4` -/

/-- **GC-L1 — the left alternative of GWZ Lemma 7.7(B) fed to GWZ Theorem 7.3(B) at `β/4`.**

The exponent `ε₁` is bound **first**, before the drop `ν`, before the threshold and before the
family: it is what `Kakeya.ML2Reduction.exists_everyScale_multiplicity_le` returns at the accuracy
`β/4`, and it is the `ε₁` a producer must feed to
`Kakeya.ML2Core.eventually_dividingScalesPackage_dim3` so that the package's alternative (i) is
Katz--Tao at every scale *at exactly this* `δ^{-ε₁}`.  Reading 7.3(B) at `β/4` rather than at
`β/2` is condition-free — `Kakeya.ML2Assembly.GeometricCoreAt` only asks for *some* `ε₁ > 0`, and
`Kakeya.ML2Spine.exists_ml2SpineParams` takes the exponent map as a parameter.

**The one input that is manufactured here** is 7.3(B)'s fullness hypothesis.  The package hands
over `λ ≤ P · λ'(u', W)` with `P` the shaded-uniformization polylogarithm and `δ^ν ≤ 2 λ`; what
7.3(B) wants is `δ^{2ν} ≤ λ'(u', W)`.  The gap is exactly `2 P ≤ δ^{-ν}`, a threshold on `δ` alone
supplied by `Tube.exists_threshold_polylog_pow_ssfGridLen_le` once the crude cardinality bound
`#𝕋 ≤ δ^{-4}` (`Kakeya.ML2Assembly.card_le_rpow_neg_four`) is available.  This is why the
hypotheses are read at the level `2ν` and not at `ν`, and `2ν ≤ ε₁` costs nothing.

The Katz--Tao input is read on the **outer** family `𝕋` and transported to `u'` by
`Kakeya.maxDensity_mono`, since `W` has the same tubes as `T` (`htube`); likewise the unit-ball
containment.  Neither is a new hypothesis. -/
theorem exists_multiplicity_quarter (hdim : Module.finrank ℝ E = 3)
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{u, u} (E := E))
    {β : ℝ} (hβ : 0 < β) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ {ν : ℝ}, 0 < ν → 2 * ν ≤ ε₁ →
      ∃ d : NNReal, 0 < d ∧ d ≤ 1 ∧
        ∀ {δ : NNReal}, 0 < δ → δ ≤ d →
        ∀ {ι : Type w} (s u : Finset ι) (T W : ι → ShadedTube δ E) (lam : NNReal),
          u ⊆ s →
          (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
          (∀ i, (W i).toTube = (T i).toTube) →
          Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)
              ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ν)) →
          (s.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) →
          ENNReal.ofReal ((δ : ℝ) ^ ν) ≤ 2 * (lam : ENNReal) →
          (lam : ENNReal) ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
              * ShadedBody.fullness' u (fun i => (W i).toShadedBody) →
          ∀ {Cu : NNReal} (𝒲 : ShadedUniformTubeSet u W (ssfGridLen δ) Cu),
            𝒲.tubeUniform.IsKatzTaoAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-ε₁))) →
            ShadedBody.multiplicity u (fun i => (W i).toShadedBody)
              ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(β / 4))) := by
  obtain ⟨ε₁, δ₁, hε₁, hδ₁0, hδ₁1, hmain⟩ :=
    ML2Reduction.exists_everyScale_multiplicity_le.{u, w} (E := E) hdim hSFE
      (ε₀ := β / 4) (by linarith)
  refine ⟨ε₁, hε₁, ?_⟩
  intro ν hν hνε
  obtain ⟨d₂, hd₂0, hd₂1, hd₂⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le 2 (by norm_num) 4 2 ν hν
  refine ⟨min d₂ (Real.toNNReal δ₁), lt_min hd₂0 (Real.toNNReal_pos.mpr hδ₁0),
    (min_le_left _ _).trans hd₂1, ?_⟩
  intro δ hδ0 hδd ι s u T W lam hus hball htube hmax hcard hlam hfullpoly Cu 𝒲 hevery
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδ1 : δ ≤ 1 := hδd.trans ((min_le_left _ _).trans hd₂1)
  have hδR1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hδδ₁ : (δ : ℝ) ≤ δ₁ := by
    have h1 := hδd.trans (min_le_right _ _)
    have h2 : (δ : ℝ) ≤ ((Real.toNNReal δ₁ : NNReal) : ℝ) := by exact_mod_cast h1
    rwa [Real.coe_toNNReal δ₁ hδ₁0.le] at h2
  set k : ℕ := 2 * ssfGridLen δ + 2 with hk
  set L : ℕ := Nat.log 2 s.card with hL
  set P : ENNReal := ((L + 1 : ℕ) : ENNReal) ^ k with hP
  have hPcast : P = ENNReal.ofReal (((L : ℝ) + 1) ^ k) := by
    rw [hP, ENNReal.ofReal_pow (by positivity)]
    norm_cast
  have h2P : (2 : ENNReal) * P ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ν)) := by
    have hreal := (hd₂ hδ0 (hδd.trans (min_le_left _ _))).2.2 ((s.card : ℝ))
      (by positivity) hcard
    have hfl : ⌊Real.logb 2 (s.card : ℝ)⌋₊ = L := by
      simpa [hL] using Real.natFloor_logb_natCast 2 s.card
    rw [hfl] at hreal
    have hstep : 2 * (((L : ℝ) + 1) ^ k) ≤ (2 * ((L : ℝ) + 1)) ^ k := by
      rw [mul_pow]
      have h1 : (0 : ℝ) ≤ ((L : ℝ) + 1) ^ k := by positivity
      have h2 : (2 : ℝ) ≤ 2 ^ k := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := by
              refine pow_le_pow_right₀ (by norm_num) ?_
              omega
      exact mul_le_mul_of_nonneg_right h2 h1
    have hcombine : 2 * (((L : ℝ) + 1) ^ k) ≤ (δ : ℝ) ^ (-ν) := hstep.trans hreal
    have hmulcast : (2 : ENNReal) * P = ENNReal.ofReal (2 * ((L : ℝ) + 1) ^ k) := by
      rw [hPcast, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [hmulcast]
    exact ENNReal.ofReal_le_ofReal hcombine
  have hP0 : P ≠ 0 := by
    rw [hP]; exact pow_ne_zero _ (by exact_mod_cast Nat.succ_ne_zero L)
  have hPT : P ≠ ⊤ := by rw [hP]; exact ENNReal.pow_ne_top (by simp)
  have h2P0 : (2 : ENNReal) * P ≠ 0 := mul_ne_zero two_ne_zero hP0
  have h2PT : (2 : ENNReal) * P ≠ ⊤ := ENNReal.mul_ne_top (by simp) hPT
  have hfull : ENNReal.ofReal ((δ : ℝ) ^ (2 * ν))
      ≤ ShadedBody.fullness' u (fun i => (W i).toShadedBody) := by
    refine (ENNReal.mul_le_mul_iff_right h2P0 h2PT).mp ?_
    calc ((2 : ENNReal) * P) * ENNReal.ofReal ((δ : ℝ) ^ (2 * ν))
        = ENNReal.ofReal ((δ : ℝ) ^ (2 * ν)) * ((2 : ENNReal) * P) := by ring
      _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (2 * ν)) * ENNReal.ofReal ((δ : ℝ) ^ (-ν)) := by gcongr
      _ = ENNReal.ofReal ((δ : ℝ) ^ ν) := by
            rw [ofReal_rpow_mul hδ0]
            ring_nf
      _ ≤ 2 * (lam : ENNReal) := hlam
      _ ≤ 2 * (P * ShadedBody.fullness' u (fun i => (W i).toShadedBody)) := by gcongr
      _ = ((2 : ENNReal) * P) * ShadedBody.fullness' u (fun i => (W i).toShadedBody) := by ring
  have hbody : ∀ i, (W i).toConvexSpaceBody = (T i).toConvexSpaceBody := fun i => by
    rw [show (W i).toConvexSpaceBody = (W i).toTube.toConvexSpaceBody from rfl, htube i]
  have hballW : ∀ i ∈ u, (W i).carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro i hi
    have hc : (W i).carrier = (T i).carrier := by
      rw [show (W i).carrier = (W i).toTube.carrier from rfl, htube i]
    rw [hc]
    exact hball i (hus hi)
  have hmaxW : Kakeya.maxDensity u (fun i => (W i).toConvexSpaceBody)
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(2 * ν))) := by
    have hfun : (fun i => (W i).toConvexSpaceBody) = (fun i => (T i).toConvexSpaceBody) :=
      funext hbody
    rw [hfun]
    refine le_trans (Kakeya.maxDensity_mono (fun i => (T i).toConvexSpaceBody) hus) ?_
    refine hmax.trans (ENNReal.ofReal_le_ofReal ?_)
    exact Real.rpow_le_rpow_of_exponent_ge hδR hδR1 (by linarith)
  exact hmain hδ0 hδδ₁ (η := 2 * ν) hνε u W hballW 𝒲 hfull hmaxW hevery

/-! ### GC-L2: the mass chain, in the `shadingBridgeLoss` shape at `K = 2` -/

omit [Nontrivial E] in
/-- **GC-L2 — the package's three mass clauses composed with the multiplicity bound.**

Input: GC-P1's mass loss back to `(𝕋, Y)` (the dense-shading discard `2`, the package's
cardinality loss `A`, and the two dimensional constants), its shaded-uniformization mass loss `P`,
its union monotonicity, and any multiplicity bound `M` on `(u', W)`.  Output: the single
inequality `λ c₃ ∑_{i ∈ 𝕋} |Y_i| ≤ shadingBridgeLoss · M · |⋃_{i ∈ 𝕋} Y_i|`, with the loss written
*exactly* as `Kakeya.ML2Shading.shadingBridgeLoss n A 2 (log₂ #𝕋) (ssfGridLen δ)` so that
`Kakeya.ML2Shading.exists_threshold_shadingBridgeLoss_le` absorbs it verbatim.

**The comparability slot is `K = 2`, and the `2` is real.**  It is the absolute mass-retention
factor of `Kakeya.ML2Shaded.exists_denseShading_refinement`, already spent by GC-P1 — *not* the
constant of `Kakeya.ML2Shaded.exists_massBanded_shadeRefinement`, which this route never calls, and
whose `Kakeya.ML2Shaded.massBandLoss` logarithm is therefore never charged.  See the module
docstring.

No hypothesis is added to make anything typecheck: every input is a clause of
`Kakeya.ML2Core.losses_of_dividingScalesOutput`, and `hmult` is GC-L1's conclusion. -/
theorem sum_shade_le_shadingBridgeLoss {δ : NNReal}
    {s u : Finset ι} {T W : ι → ShadedTube δ E} {lam : NNReal} {A M : ENNReal}
    (hmassloss : (lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
          * (∑ i ∈ s, volume (T i).shade)
        ≤ 2 * A * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
          * ∑ i ∈ u, volume (T i).shade)
    (hpoly : (∑ i ∈ u, volume (T i).shade)
        ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
          * ∑ i ∈ u, volume (W i).shade)
    (hunion : volume (⋃ i ∈ u, (W i).shade) ≤ volume (⋃ i ∈ s, (T i).shade))
    (hmult : ShadedBody.multiplicity u (fun i => (W i).toShadedBody) ≤ M) :
    (lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
        * (∑ i ∈ s, volume (T i).shade)
      ≤ ML2Shading.shadingBridgeLoss (Module.finrank ℝ E) A 2 (Nat.log 2 s.card)
            (ssfGridLen δ) * M * volume (⋃ i ∈ s, (T i).shade) := by
  have hmw : (∑ i ∈ u, volume (W i).shade) ≤ M * volume (⋃ i ∈ u, (W i).shade) :=
    (ShadedBody.multiplicity_le_iff u (fun i => (W i).toShadedBody)).mp hmult
  calc (lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
          * (∑ i ∈ s, volume (T i).shade)
      ≤ 2 * A * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
          * ∑ i ∈ u, volume (T i).shade := hmassloss
    _ ≤ 2 * A * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
          * (((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
              * (M * volume (⋃ i ∈ s, (T i).shade))) := by
        gcongr
        exact hpoly.trans (mul_le_mul' le_rfl (hmw.trans (mul_le_mul' le_rfl hunion)))
    _ = ML2Shading.shadingBridgeLoss (Module.finrank ℝ E) A 2 (Nat.log 2 s.card)
            (ssfGridLen δ) * M * volume (⋃ i ∈ s, (T i).shade) := by
        rw [ML2Shading.shadingBridgeLoss]
        push_cast
        ring

/-! ### GC-L3: absorbing the whole loss into one `δ`-power -/

omit [Nontrivial E] in
/-- **GC-L3 — the absorption, and the whole loss ledger of branch (i) in one statement.**

Three inputs are cleared, and the exponent each costs is visible in the conclusion
`a + κ + ν + ν`:

* `a` — the shading-bridge loss, i.e. the package's cardinality loss `A` together with the
  comparability `2`, the dimensional ratio `C₃/c₃` and the shaded-uniformization polylogarithm.
  Forced by `hSBL`, which is `Kakeya.ML2Shading.exists_threshold_shadingBridgeLoss_le` at
  `K = 2`, `K₀ = 4`;
* `κ` — the multiplicity, i.e. GWZ Theorem 7.3(B)'s accuracy.  Forced by `hM`;
* `ν + ν` — division by the dense-shading level.  One `ν` is `λ⁻¹` itself (`hlam`, i.e. GC-P1's
  `δ^ν ≤ 2 λ`); the other is the absolute factor `2` in it (`htwo`).  Neither is avoidable: the
  package's mass loss is stated with `λ` on the left, which is what makes it a *mass* and not a
  cardinality statement.

`hδ0` is what makes `δ^{-ν} · δ^{ν} = 1`; `δ ≤ 1` is *not* needed here (every step is a product
inequality), which is why it is absent from the binder list. -/
theorem sum_shade_le_rpow_of_chain {δ : NNReal} (hδ0 : 0 < δ)
    {s : Finset ι} {T : ι → ShadedTube δ E} {lam : NNReal} {A M : ENNReal} {a κ ν : ℝ}
    (hchain : (lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
          * (∑ i ∈ s, volume (T i).shade)
        ≤ ML2Shading.shadingBridgeLoss (Module.finrank ℝ E) A 2 (Nat.log 2 s.card)
            (ssfGridLen δ) * M * volume (⋃ i ∈ s, (T i).shade))
    (hSBL : ML2Shading.shadingBridgeLoss (Module.finrank ℝ E) A 2 (Nat.log 2 s.card)
            (ssfGridLen δ)
        ≤ (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
          * ENNReal.ofReal ((δ : ℝ) ^ (-a)))
    (hM : M ≤ ENNReal.ofReal ((δ : ℝ) ^ (-κ)))
    (hlam : ENNReal.ofReal ((δ : ℝ) ^ ν) ≤ 2 * (lam : ENNReal))
    (htwo : (2 : ENNReal) ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ν))) :
    (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) * (∑ i ∈ s, volume (T i).shade)
      ≤ ((Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
          * ENNReal.ofReal ((δ : ℝ) ^ (-(a + κ + ν + ν)))) * volume (⋃ i ∈ s, (T i).shade) := by
  set c : ENNReal := (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) with hc
  set U : ENNReal := volume (⋃ i ∈ s, (T i).shade) with hU
  set S : ENNReal := ∑ i ∈ s, volume (T i).shade with hS
  have hcancel : ENNReal.ofReal ((δ : ℝ) ^ (-ν)) * ENNReal.ofReal ((δ : ℝ) ^ ν) = 1 := by
    rw [ofReal_rpow_mul hδ0]
    norm_num
  have hstep : ENNReal.ofReal ((δ : ℝ) ^ ν) * (c * S)
      ≤ c * (ENNReal.ofReal ((δ : ℝ) ^ (-ν)) * ENNReal.ofReal ((δ : ℝ) ^ (-a))
          * ENNReal.ofReal ((δ : ℝ) ^ (-κ))) * U := by
    calc ENNReal.ofReal ((δ : ℝ) ^ ν) * (c * S)
        ≤ (2 * (lam : ENNReal)) * (c * S) := by gcongr
      _ = 2 * ((lam : ENNReal) * c * S) := by ring
      _ ≤ 2 * (ML2Shading.shadingBridgeLoss (Module.finrank ℝ E) A 2 (Nat.log 2 s.card)
              (ssfGridLen δ) * M * U) := by gcongr
      _ ≤ 2 * ((c * ENNReal.ofReal ((δ : ℝ) ^ (-a)))
              * ENNReal.ofReal ((δ : ℝ) ^ (-κ)) * U) := by gcongr
      _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ν)) * ((c * ENNReal.ofReal ((δ : ℝ) ^ (-a)))
              * ENNReal.ofReal ((δ : ℝ) ^ (-κ)) * U) := by gcongr
      _ = c * (ENNReal.ofReal ((δ : ℝ) ^ (-ν)) * ENNReal.ofReal ((δ : ℝ) ^ (-a))
              * ENNReal.ofReal ((δ : ℝ) ^ (-κ))) * U := by ring
  calc c * S = (ENNReal.ofReal ((δ : ℝ) ^ (-ν)) * ENNReal.ofReal ((δ : ℝ) ^ ν)) * (c * S) := by
        rw [hcancel, one_mul]
    _ = ENNReal.ofReal ((δ : ℝ) ^ (-ν)) * (ENNReal.ofReal ((δ : ℝ) ^ ν) * (c * S)) := by ring
    _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ν))
          * (c * (ENNReal.ofReal ((δ : ℝ) ^ (-ν)) * ENNReal.ofReal ((δ : ℝ) ^ (-a))
              * ENNReal.ofReal ((δ : ℝ) ^ (-κ))) * U) := by gcongr
    _ = c * (ENNReal.ofReal ((δ : ℝ) ^ (-ν)) * ENNReal.ofReal ((δ : ℝ) ^ (-ν))
          * ENNReal.ofReal ((δ : ℝ) ^ (-a)) * ENNReal.ofReal ((δ : ℝ) ^ (-κ))) * U := by ring
    _ = (c * ENNReal.ofReal ((δ : ℝ) ^ (-(a + κ + ν + ν)))) * U := by
        rw [ofReal_rpow_mul hδ0, ofReal_rpow_mul hδ0,
          ofReal_rpow_mul hδ0]
        ring_nf

/-! ### GC-L4: landing on the left disjunct -/

omit [Nontrivial E] in
/-- **GC-L4 — `Kakeya.ML2Shading.dichotomyLeft_of_bridge` at `ε₀ = β/2`.**

The only content beyond the existing bridge lemma is the exponent comparison `b ≤ ε₀` read against
`δ ≤ 1`, and the `ENNReal.ofReal`/`ENNReal.rpow` bridge
`Kakeya.ML2Reduction.ofReal_rpow_coe`.  `hδ1` is what makes `δ^{-b} ≤ δ^{-ε₀}`; `hδ0` is what makes
`δ^{-ε₀}` in `ENNReal` agree with the real power. -/
theorem dichotomyLeft_of_rpow_bound {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → ShadedTube δ E} {b ε₀ : ℝ}
    (hbound : (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) * (∑ i ∈ s, volume (T i).shade)
        ≤ ((Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
            * ENNReal.ofReal ((δ : ℝ) ^ (-b))) * volume (⋃ i ∈ s, (T i).shade))
    (hbud : b ≤ ε₀) :
    ML2Shading.DichotomyLeft ε₀ s T := by
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδR1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  refine ML2Shading.dichotomyLeft_of_bridge hbound (mul_le_mul' le_rfl ?_)
  rw [← ML2Reduction.ofReal_rpow_coe hδ0]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδR hδR1 (by linarith))

/-! ### GC-L5: the capstone — the left disjunct on the original family -/

/-- **GC-L5 — branch (i) of a `Kakeya.ML2Assembly.GeometricCoreAt` producer, assembled.**

From `Kakeya.ML2Assembly.Dichotomy`'s hypotheses (a)–(d) at `η = ν` and nothing else: either the
**left disjunct of the dichotomy on the original family `(𝕋, Y)`**, at the absolute accuracy
`ε₀ = β/2`, or the package of GC-P1 with GWZ Lemma 7.7(B)'s alternative (ii) — the
`Kakeya.ML2Reduction.IsKatzTaoDividingWindow` datum — pinned, which is exactly what branch (ii)
(rows the estimate onwards) consumes.  Nothing is left in between: the two alternatives of
`Kakeya.ML2Inputs.DividingScalesOutput` are cased on here, once.

**The pushback to `(𝕋, Y)` is GC-P1's three loss clauses and nothing else.**  There is no separate
pushback step: `Kakeya.ML2Core.losses_of_dividingScalesOutput` already states the mass loss with
`∑_{i ∈ 𝕋} |Y_i|` on the left and the union with `⋃_{i ∈ 𝕋} Y_i` on the right, so `dichotomyLeft`
lands on `(𝕋, T)` directly.  The two selections (the dense-shading discard `𝕋 ⊇ 𝕋'` and 7.7(B)'s
`u' ⊆ 𝕋'`) cost the absolute `2` and the package's `δ^{-2ν} · totalLoss`; the shaded uniformization
`Y ⇝ W` costs the polylogarithm; the union costs nothing.  Total: `2ν + ν` on top of
`β/4 + ν + 2ν`.

**The exponent, and the hypothesis forcing each term** (`ν = η 0`):

| term | value | forced by |
|---|---|---|
| GWZ Theorem 7.3(B)'s accuracy | `β/4` | free choice of `ε₀` in `exists_multiplicity_quarter` |
| the package's cardinality loss, `α = ν` | `2ν` | the own clause of
  `Kakeya.ML2Core.eventually_dividingScalesPackage_dim3` |
| `StickyKakeya.totalLoss` | `ν` | `StickyKakeya.exists_threshold_totalLoss_le`, needs `1 ≤ C` |
| the shading bridge (`K = 2`, `K₀ = 4`) | `ν` |
  `Kakeya.ML2Shading.exists_threshold_shadingBridgeLoss_le` |
| `λ⁻¹` and the `2` in `δ^ν ≤ 2 λ` | `2ν` | GC-P1's `δ^ν/2 ≤ lam`, and
  `Kakeya.ML2Shaded.exists_threshold_const_le_rpow_neg'` |
| **total** | `β/4 + 6ν ≤ β/2` | `Kakeya.ML2Inputs.spineNu_le_div_48000` (`ν ≤ β/48000`) |

The margin is `β/4 − β/8000`.  Note that this is **six** `ν`'s, not the three of
`Kakeya.ML2Core.eventually_coreThresholds_dim3`'s branch-(i) clause `β/4 + 3ν ≤ β/2`: that clause
prices the shading bridge at `a = 2ν`, which cannot absorb the package's own cardinality loss
`δ^{-2ν} · totalLoss` because `1 ≤ totalLoss`.  The arithmetic is re-derived here from
`spineNu_le_div_48000` and costs nothing.

`hβ1` is consumed by `spineNu_le_div_48000` and by the package; `hϖ`, `hgain`, `hdens` by
`Kakeya.ML2Spine.spineNu_pos` inside the package.  `2ν ≤ ε₁`, which GWZ Theorem 7.3(B) needs, is
free from `Kakeya.ML2Spine.IsSpine` (`rung_mono`, `rung_top`, `div_le`, `eps₂_le_everyScale`). -/
theorem exists_dichotomyLeft_or_window_dim3
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3)))
    {β ϖ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∃ (C : NNReal) (Kl cl : ℕ) (ε₂ e : ℝ) (N : ℕ) (η : ℕ → ℝ),
        1 ≤ C ∧ 4096 ≤ N ∧ e = 1 / Real.sqrt (N : ℝ) ∧
        η 0 = ML2Spine.spineNu β ϖ ε₁ gain dens ∧ 0 < η 0 ∧ η 0 ≤ 1 ∧
        ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η ∧
        ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
          0 < δ ∧ δ ≤ 1 ∧
          ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
            (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
            IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-(η 0))) →
            ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ (η 0) →
            (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
            s.Nonempty ∧
            (ML2Shading.DichotomyLeft (β / 2) s T
              ∨ ∃ u' ⊆ s, ∃ W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)), ∃ lam : NNReal,
                  δ ^ (η 0) / 2 ≤ lam ∧ 0 < lam ∧ u'.Nonempty ∧
                  (∀ i, (W i).toTube = (T i).toTube) ∧
                  (∀ i, (W i).shade ⊆ (T i).shade) ∧
                  ML2Shaded.HasDenseShading lam u' (fun i ↦ (T i).toShadedBody) ∧
                  ML2Shaded.HasComparableDensities lam⁻¹ u'
                      (fun i ↦ (T i).toShadedBody) ∧
                  (lam : ENNReal)
                        * (Tube.le_volume.c
                            (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
                        * (∑ i ∈ s, volume (T i).shade)
                      ≤ 2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + η 0)))
                          * StickyKakeya.totalLoss C Kl cl δ)
                        * (Tube.volume_le.C
                            (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal)
                        * ∑ i ∈ u', volume (T i).shade ∧
                  (∑ i ∈ u', volume (T i).shade)
                      ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
                        * ∑ i ∈ u', volume (W i).shade ∧
                  volume (⋃ i ∈ u', (W i).shade) ≤ volume (⋃ i ∈ s, (T i).shade) ∧
                  (lam : ENNReal)
                      ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
                        * ShadedBody.fullness' u' (fun i ↦ (W i).toShadedBody) ∧
                  ∃ 𝒲 : ShadedUniformTubeSet u' W (ssfGridLen δ) (max C 4),
                    ∃ a b m : ℕ, ML2Reduction.IsKatzTaoDividingWindow 𝒲.tubeUniform
                        ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) η e N a b m) := by
  classical
  obtain ⟨ε₁, hε₁, hL1⟩ :=
    exists_multiplicity_quarter.{0, u} (E := EuclideanSpace ℝ (Fin 3))
      finrank_euclideanSpace_fin hSFE hβ
  obtain ⟨C, Kl, cl, ε₂, e, N, η, hC, hN, he, hη0nu, hη00, hη01, hspine, hev⟩ :=
    eventually_dividingScalesPackage_dim3.{u} hβ hβ1 hϖ hε₁ hgain hdens
  refine ⟨ε₁, hε₁, C, Kl, cl, ε₂, e, N, η, hC, hN, he, hη0nu, hη00, hη01, hspine, ?_⟩
  have hνε₁ : 2 * η 0 ≤ ε₁ := by
    have h1 : η 0 ≤ η N := hspine.rung_mono (Nat.zero_le N)
    have h2 : η N = e := hspine.rung_top
    have h3 : e ≤ ε₂ / 5 := hspine.div_le
    have h4 : ε₂ ≤ ε₁ / 5 := hspine.eps₂_le_everyScale
    have h5 : 0 < ε₂ := hspine.eps₂_pos
    rw [h2] at h1
    linarith
  have hν48 : η 0 ≤ β / 48000 := by
    rw [hη0nu]
    exact ML2Inputs.spineNu_le_div_48000 hβ hβ1 hϖ hε₁ hgain hdens
  have hbud : η 0 + η 0 + η 0 + η 0 + β / 4 + η 0 + η 0 ≤ β / 2 := by linarith
  obtain ⟨d1, hd10, hd11, hL1d⟩ := hL1 hη00 hνε₁
  obtain ⟨dT, hdT0, hdT1, hdT⟩ :=
    StickyKakeya.exists_threshold_totalLoss_le C hC Kl cl (η 0) hη00
  obtain ⟨dS, hdS0, hdS1, hdS⟩ :=
    ML2Shading.exists_threshold_shadingBridgeLoss_le
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) 2 4
      (a := η 0 + η 0 + η 0) (α := η 0) hη00
  obtain ⟨d2, hd20, hd21, hd2⟩ := ML2Shaded.exists_threshold_const_le_rpow_neg' 2 hη00
  filter_upwards [hev, ML2Assembly.eventually_card_thresholds,
    Ioc_mem_nhdsGT hd10, Ioc_mem_nhdsGT hdT0, Ioc_mem_nhdsGT hdS0, Ioc_mem_nhdsGT hd20]
    with δ hpkg hthr hm1 hmT hmS hm2
  obtain ⟨hδ0, hδ1, hpkgbody⟩ := hpkg
  obtain ⟨-, -, hδC⟩ := hthr
  refine ⟨hδ0, hδ1, ?_⟩
  intro ι s T hball hKT hfull hcard
  obtain ⟨hsne, s', hs's, lam, hlamlow, hlam0, hs'ne, hmass, hdense, hout⟩ :=
    hpkgbody s T hball hKT hfull hcard
  refine ⟨hsne, ?_⟩
  obtain ⟨u', hu's, W, htube, hshade, hu'ne, hdenseu, hcompu, hmassloss, hpoly, hunion,
    hfullpoly, 𝒲, halt⟩ :=
    losses_of_dividingScalesOutput (E := EuclideanSpace ℝ (Fin 3)) hδ1 hs's hmass hout
  rcases halt with hevery | hwindow
  · -- alternative (i): GWZ `section9.tex` lines 55–61
    refine Or.inl ?_
    have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
    have hmaxs : Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0))) := by
      rw [ML2Reduction.ofReal_rpow_coe hδ0]
      exact hKT
    have hcard4 : (s.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) := by
      simpa using ML2Assembly.card_le_rpow_neg_four hδ0 hδ1 hδC s T hball hη01 hKT
    have hlamE : ENNReal.ofReal ((δ : ℝ) ^ (η 0)) ≤ 2 * (lam : ENNReal) := by
      have hnn : (δ : NNReal) ^ (η 0) ≤ 2 * lam := by
        rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 2)] at hlamlow
        calc (δ : NNReal) ^ (η 0) ≤ lam * 2 := hlamlow
          _ = 2 * lam := by ring
      have hcoe : ENNReal.ofReal ((δ : ℝ) ^ (η 0))
          = (((δ : NNReal) ^ (η 0) : NNReal) : ENNReal) := by
        rw [← NNReal.coe_rpow, ENNReal.ofReal_coe_nnreal]
      rw [hcoe]
      calc (((δ : NNReal) ^ (η 0) : NNReal) : ENNReal) ≤ ((2 * lam : NNReal) : ENNReal) :=
            ENNReal.coe_le_coe.mpr hnn
        _ = 2 * (lam : ENNReal) := by push_cast; ring
    have hmult := hL1d hδ0 hm1.2 s u' T W lam hu's hball htube hmaxs hcard4 hlamE hfullpoly
      𝒲 hevery
    have hA : ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + η 0))) * StickyKakeya.totalLoss C Kl cl δ
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + η 0 + η 0))) := by
      calc ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + η 0))) * StickyKakeya.totalLoss C Kl cl δ
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + η 0)))
              * ENNReal.ofReal ((δ : ℝ) ^ (-(η 0))) := by
            gcongr
            exact hdT hδ0 hmT.2
        _ = ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + η 0 + η 0))) := by
            rw [ofReal_rpow_mul hδ0]
            ring_nf
    have hSBL := hdS hδ0 hmS.2 hA s.card (by simpa using hcard4)
    have htwo : (2 : ENNReal) ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0))) := by
      have hr := hd2 hδ0 hm2.2
      calc (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by simp
        _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0))) := ENNReal.ofReal_le_ofReal hr
    have hchain := sum_shade_le_shadingBridgeLoss hmassloss hpoly hunion hmult
    have hbound := sum_shade_le_rpow_of_chain hδ0 hchain hSBL le_rfl hlamE htwo
    exact dichotomyLeft_of_rpow_bound hδ0 hδ1 hbound hbud
  · exact Or.inr ⟨u', hu's, W, lam, hlamlow, hlam0, hu'ne, htube, hshade, hdenseu, hcompu,
      hmassloss, hpoly, hunion, hfullpoly, 𝒲, hwindow⟩

/-! ### The glue to `Kakeya.ML2Assembly.Dichotomy`, and non-vacuity -/

/-- **compatibility, and the exact glue row the estimate needs.**

`Kakeya.ML2Shading.DichotomyLeft ε₀ s T` on the left and the dichotomy's own gain disjunct on the
right, under `Kakeya.ML2Assembly.Dichotomy`'s hypothesis block written out verbatim, *is*
`Kakeya.ML2Assembly.Dichotomy`.  Named rather than an `example`, so `#print axioms` checks it, and
so that a later edit to `Dichotomy` or to `DichotomyLeft` breaks this theorem instead of silently
decoupling branch (i) from its consumer.

Nothing is proved here: the two `Or` constructors and one `filter_upwards`. -/
theorem dichotomy_of_dichotomyLeft_or_gain {β ε₀ g η : ℝ}
    (h : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
        ML2Shading.DichotomyLeft ε₀ s T
          ∨ (∑ i ∈ s, volume (T i).shade
              ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β
                  * volume (⋃ i ∈ s, (T i).shade))) :
    ML2Assembly.Dichotomy.{u} β ε₀ g η := by
  filter_upwards [h] with δ hδ
  intro ι s T hball hKT hfull hcardge
  rcases hδ s T hball hKT hfull hcardge with hleft | hright
  · exact Or.inl hleft
  · exact Or.inr hright

/-- **Non-vacuity of branch (i) and of its exponent budget.**

At the concrete data `β = ϖ = 1`, `gain = dens = id` the producer of
`Kakeya.ML2Core.exists_dichotomyLeft_or_window_dim3` exists, its `ε₁` is positive, its spine is a
genuine `Kakeya.ML2Spine.IsSpine`, and the branch-(i) budget `β/4 + 6ν ≤ β/2` holds on it.  So
neither the statement nor the budget is a consequence of `False`, and in particular the six `ν`'s
of the ledger are affordable at a `ν` the development actually produces. -/
theorem exists_dichotomyLeft_budget_at_one
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3))) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ (ε₂ e : ℝ) (N : ℕ) (η : ℕ → ℝ),
      ML2Spine.IsSpine 1 1 ε₁ (fun x => x) (fun x => x) ε₂ e N η ∧
        0 < η 0 ∧ η 0 + η 0 + η 0 + η 0 + (1 : ℝ) / 4 + η 0 + η 0 ≤ 1 / 2 := by
  obtain ⟨ε₁, hε₁, C, Kl, cl, ε₂, e, N, η, -, -, -, hη0nu, hη00, -, hspine, -⟩ :=
    exists_dichotomyLeft_or_window_dim3.{0} hSFE (β := 1) (ϖ := 1) (gain := fun x => x)
      (dens := fun x => x) one_pos le_rfl one_pos (fun _ h => h) (fun _ h => h)
  refine ⟨ε₁, hε₁, ε₂, e, N, η, hspine, hη00, ?_⟩
  have hν48 : η 0 ≤ (1 : ℝ) / 48000 := by
    rw [hη0nu]
    simpa using ML2Inputs.spineNu_le_div_48000 (β := 1) (ϖ := 1) (ε₁ := ε₁)
      (gain := fun x => x) (dens := fun x => x) one_pos le_rfl one_pos hε₁
      (fun _ h => h) (fun _ h => h)
  linarith

end Kakeya.ML2Core

end
