/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ShadedDividingScales
public import Kakeya.DimensionThree.MainLemma2.Reduction.Assembly

/-!
# The shading bridge — component G2d of `Kakeya.ML2Assembly.GeometricCore`

The GWZ reduction of Main Lemma 2 moves between **unshaded** statements — the dividing-scales
lemma, Katz--Tao-at-every-scale, the tube hierarchy — and **shaded** ones — multiplicity, fullness
`λ`, the `ShadedTube.ShadedUniformTubeSet` that GWZ Theorem 7.3(B) consumes.  This file carries a
shading across that boundary and accounts for the loss.

## The gap this file closes

`StickyKakeya.dividingScalesKatzTao` (GWZ Lemma 7.7(B), proved) is handed a family of `δ`-tubes and
a `Tube.UniformTubeSet` on them, and returns a **subfamily** `𝕋' ⊆ 𝕋` carrying a *new* tube
hierarchy `𝒰'` and a **cardinality** retention `#𝕋 ≤ StickyKakeya.totalLoss · #𝕋'`.  It never looks
at the shading.

`Kakeya.ML2Reduction.exists_everyScale_multiplicity_le` (GWZ Theorem 7.3(B), proved from Sticky
Kakeya 7.3(A)) wants three things the dichotomy does not give: a
`ShadedTube.ShadedUniformTubeSet` read on *that* hierarchy, a **fullness lower bound**
`δ^η ≤ λ(𝕋', Y')` on the refined pair, and — after it fires — a way back from `(𝕋', Y')` to the
original `(𝕋, Y)`.  The module docstring of `Reduction/SpineEveryScale.lean` names exactly this as
what is *not* proved there, and names `Kakeya.ML2Reduction.isKatzTaoAtEveryScale_of_cover_eq` as the
one piece of it that is.

`Kakeya.ML2Shading.exists_shadingBridge` is the rest of it.  Given the dichotomy's `𝕋'` and `𝒰'`
it produces, in one statement,

1. the sub-shading `Y' ⊆ Y` on the *same* tubes and the
   `ShadedTube.ShadedUniformTubeSet s' V' N (max C 4)` built over the given hierarchy
   (`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet`);
2. the transport of the every-scale hypothesis onto it, which is free because that lemma pins
   `cover.{indexSet, assign, tube}` and `branchingN` to `𝒰'`'s;
3. **the fullness input `δ^η ≤ λ(𝕋', Y')` of Theorem 7.3(B)** — produced, not assumed; and
4. the transport of Theorem 7.3(B)'s conclusion back to `(𝕋, Y)`, in the shape of the left disjunct
   of `Kakeya.ML2Assembly.Dichotomy`.

## The loss it charges

`Kakeya.ML2Shading.shadingBridgeLoss n A K clamp N = A · K · C_n · (clamp + 1)^{2N+2}`, read against
the constant `c_n` of `Tube.le_volume` that sits on the left of every inequality below.  At the call
site, with `n = 3`, `clamp = log₂ #𝕋` and `N = Tube.ssfGridLen δ = ⌈log log (1/δ)⌉`:

* `A` — the cardinality loss of GWZ 7.7(B), `StickyKakeya.totalLoss C K c δ`; absorbed by
  `StickyKakeya.exists_threshold_totalLoss_le`.
* `K` — the comparability constant of the shading densities, the absolute `2`.
* `C_n / c_n` — the dimensional tube-volume ratio; absorbed by
  `Kakeya.ML2Shaded.exists_threshold_const_le_rpow_neg'`.
* `(log₂ #𝕋 + 1)^{2N+2}` — the shaded-uniformization loss; absorbed by
  `Tube.exists_threshold_polylog_pow_ssfGridLen_le`.
* `Kakeya.ML2Shaded.massBandLoss λ` — the mass banding, charged only in the banded form; absorbed
  by `Kakeya.ML2Shaded.exists_threshold_massBandLoss_le`.

`Kakeya.ML2Shading.exists_threshold_shadingBridgeLoss_le` proves the whole thing subpolynomial:
below an explicit threshold depending on `(n, K, K₀, a, α)` only, and given `A ≤ δ^{-a}` and
`#𝕋 ≤ δ^{-K₀}`, the loss is at most `c_n δ^{-(a+α)}`.  So the bridge costs `a + α` in the exponent
and nothing else.  Note that the shaded-uniformization factor is *not* bounded — with
`#𝕋 ≤ δ^{-4}` (`Kakeya.ML2Assembly.card_le_rpow_neg_four`) it is `exp(Θ((log log 1/δ)^2))` — it is
only subpolynomial, which is why a threshold appears at all.

## Why comparability of the densities is the crux, and where it comes from

Step 4 is a **cardinality-to-mass** conversion, and no such conversion exists without a pointwise
hypothesis: `𝕋'` is chosen by a lemma blind to `Y`, so `𝕋'` can consist entirely of *unshaded*
tubes while `#𝕋 ≤ A · #𝕋'` still holds, and then no bound `∑_{𝕋} |Y_i| ≤ L ∑_{𝕋'} |Y_i|` is true at
any finite `L`.  The missing information is exactly
`Kakeya.ML2Shaded.HasComparableDensities`, and
`Kakeya.ML2Shading.sum_shade_le_of_card_le_of_comparableDensities` is the conversion —
the converse of `Kakeya.ML2Shaded.card_le_of_sum_shade_le`, whose docstring names it
`exists_massShare_of_comparableDensities`, a lemma that does not exist in the tree.

Comparability is supplied, at the absolute constant `2`, by
`Kakeya.ML2Shaded.exists_massBanded_shadeRefinement`, which pays for it by **discarding indices**
(`Kakeya.ML2Shaded.not_hasComparableDensities_of_aggregate_retention` shows discarding is forced).
`Kakeya.ML2Shading.sum_shade_le_of_everyScale_banded` is the form in which the hypothesis has been
discharged and its loss charged; because the banding must happen *before* the dichotomy — a
subfamily is not a `Tube.UniformTubeSet` — its remaining hypothesis is quantified over subfamilies.

This is the one place where the recurring "an aggregate bound consumed as a pointwise one" defect
of this development could have entered, and it is where it is paid for.

The one-sided `Kakeya.ML2Shaded.HasDenseShading` works just as well and is charged separately by
`Kakeya.ML2Shading.sum_shade_le_of_card_le_of_denseShading` and
`Kakeya.ML2Shading.sum_shade_le_of_everyScale_dense`: it costs only a factor `2` to establish, but
`lam⁻¹ ≈ δ^{-η}` to spend, where comparability costs `O(η log (1/δ))` to establish and `2` to
spend.  Neither dominates; the assembled bridge uses the comparability route because its total is
the smaller one, and the dense route is carried so that the bridge is not tied to one way of
manufacturing the pointwise hypothesis.  Nothing here reads an
aggregate as a pointwise bound: `hcomp` is pointwise and is consumed pointwise; `hcard`, `hrefine`
and `hmult` are aggregate and are consumed as aggregates.

## The `ε`-discipline

No statement in this file has an `ε` binder.  The two levels that appear are `θ`, the level at
which the standing hypotheses of Main Lemma 2 are read, and `η`, the level at which GWZ Theorem
7.3(B) is read; the hypothesis `habs` of `Kakeya.ML2Shading.exists_shadingBridge` is precisely the
statement that the loss fits between them, and
`Kakeya.ML2Shading.exists_threshold_shadingBridgeLoss_le` shows the budget `η ≥ θ + a + α` is met
below a threshold that depends on the constants alone.  In the intended instantiation `θ` is Lemma
9.1's own density exponent and `η` is `ε₁ = Eexp (β₀/2)` — Theorem 7.3(B) read at the **threshold**
accuracy `β₀/2`, never at `β/2` and never at the outer `ε`, per Prof. Hong Wang's clarification of
2026-08-30.  `Kakeya.ML2Spine.not_epsFree_of_outerAccuracy` is untouched by anything here.

## Non-vacuity, checked by the compiler

* a singleton family satisfies every hypothesis of `Kakeya.ML2Shading.sum_shade_le_of_everyScale`;
* `Kakeya.ML2Shading.sum_shade_le_of_everyScale_banded`'s hypothesis `hbr` is met, for *every*
  family, at `𝕋' = 𝕋`, `A = B = 1`, `M = #𝕋` (`ShadedBody.multiplicity_le_card`), producing a true
  bound — so the banded statement neither presupposes the dichotomy nor asks for something no call
  site can supply;
* the absorption hypothesis `habs` is met below an explicit threshold.

Three `example`s at the end of the file carry these, and a fourth pins
`Kakeya.ML2Shading.DichotomyLeft` to the left disjunct of `Kakeya.ML2Assembly.Dichotomy`.

## What is deliberately *not* here

The essential-distinctness hypothesis of GWZ Lemma 7.7(B) and the `4096 ≤ N` side condition, both
of which belong to component G2a; the window branch (G2c); and the actual invocation of Theorem
7.3(B), which lives in `Reduction/SpineEveryScale.lean`.  This file imports
`Reduction/Assembly.lean` only for the fidelity compatibility; if the discharge of
`Kakeya.ML2Assembly.GeometricCore` is ever placed inside `Assembly.lean` itself, drop that import
and the compatibility together.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ShadedBody ConvexSpaceBody
open Tube ShadedTube

universe u

namespace Kakeya.ML2Shading

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-! ### Two `ENNReal` book-keeping lemmas -/

/-- **Cancelling a nonzero finite factor.** -/
theorem le_of_mul_le_mul_left' {L y z : ENNReal} (hL0 : L ≠ 0) (hLT : L ≠ ⊤)
    (h : L * y ≤ L * z) : y ≤ z :=
  (ENNReal.mul_le_mul_iff_right hL0 hLT).mp h

/-- **The absorption step.**  If a bridge charges the loss `L` against the gain `a`, if `x` is a
lower bound for the source quantity `f`, and if `L * y ≤ a * x`, then `y` is a lower bound for the
target quantity `f'`. -/
theorem le_of_absorb {L a x y f f' : ENNReal} (hL0 : L ≠ 0) (hLT : L ≠ ⊤)
    (hbridge : a * f ≤ L * f') (hx : x ≤ f) (habs : L * y ≤ a * x) : y ≤ f' :=
  le_of_mul_le_mul_left' hL0 hLT
    (habs.trans ((mul_le_mul' le_rfl hx).trans hbridge))

/-! ### From a share of the index set to a share of the shaded mass -/

/-- **A cardinality share is a mass share, under comparable densities.**

If the shading densities of `(𝕋, Y)` are pairwise comparable at the constant `K` and the subfamily
`𝕋' ⊆ 𝕋` retains all but a factor `A` of the *indices*, then it retains all but a factor
`A · K · C_n / c_n` of the *shaded mass*, where `c_n ≤ |T| / δ^{n-1} ≤ C_n` are the two dimensional
tube-volume constants (`Tube.le_volume`, `Tube.volume_le`).

This is the converse of `Kakeya.ML2Shaded.card_le_of_sum_shade_le`, and it is the step the shading
bridge cannot do without: `StickyKakeya.dividingScalesKatzTao` retains a share of the *indices*
only, while every consumer of the shading needs a share of the *mass*.  Comparability is not a
technical convenience here — without it the retained subfamily can be entirely unshaded, and no
bound of this shape holds; it is supplied by `Kakeya.ML2Shaded.exists_massBanded_shadeRefinement`,
whose loss is charged in `Kakeya.ML2Shading.sum_shade_le_of_everyScale_banded`. -/
theorem sum_shade_le_of_card_le_of_comparableDensities {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {s s' : Finset ι} (hsub : s' ⊆ s) {V : ι → ShadedTube δ E} {K : NNReal}
    (hcomp : ML2Shaded.HasComparableDensities K s (fun i => (V i).toShadedBody))
    {A : ENNReal} (hcard : (s.card : ENNReal) ≤ A * (s'.card : ENNReal)) :
    (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) * ∑ i ∈ s, volume (V i).shade
      ≤ A * (K : ENNReal) * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
          * ∑ i ∈ s', volume (V i).shade := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set p : ENNReal := (δ : ENNReal) ^ (n - 1) with hp
  have hp0 : p ≠ 0 := by
    rw [hp]; exact pow_ne_zero _ (by simpa using hδ0.ne')
  have hpT : p ≠ ⊤ := by
    rw [hp]; exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  rcases Finset.eq_empty_or_nonempty s' with rfl | hne
  · have hs0 : (s.card : ENNReal) ≤ 0 := by simpa using hcard
    have hcard0 : s.card = 0 := by
      have h0 : (s.card : ENNReal) = 0 := le_antisymm hs0 (by simp)
      exact_mod_cast h0
    rw [Finset.card_eq_zero.mp hcard0]
    simp
  · have hdouble : (∑ i ∈ s, volume (V i).shade) * (∑ j ∈ s', volume (V j).carrier)
        ≤ (K : ENNReal)
            * ((∑ j ∈ s', volume (V j).shade) * (∑ i ∈ s, volume (V i).carrier)) := by
      calc (∑ i ∈ s, volume (V i).shade) * (∑ j ∈ s', volume (V j).carrier)
          = ∑ i ∈ s, ∑ j ∈ s', volume (V i).shade * volume (V j).carrier :=
            Finset.sum_mul_sum _ _ _ _
        _ ≤ ∑ i ∈ s, ∑ j ∈ s', (K : ENNReal) * (volume (V j).shade * volume (V i).carrier) :=
            Finset.sum_le_sum fun i hi =>
              Finset.sum_le_sum fun j hj => hcomp i hi j (hsub hj)
        _ = (K : ENNReal) * ∑ i ∈ s, ∑ j ∈ s', volume (V j).shade * volume (V i).carrier := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
        _ = (K : ENNReal)
              * ((∑ j ∈ s', volume (V j).shade) * (∑ i ∈ s, volume (V i).carrier)) := by
            congr 1
            rw [Finset.sum_mul_sum]
            exact Finset.sum_comm
    have hlow : (s'.card : ENNReal) * ((Tube.le_volume.c n : ENNReal) * p)
        ≤ ∑ j ∈ s', volume (V j).carrier := by
      have := Finset.card_nsmul_le_sum s' (fun j => volume (V j).carrier)
        ((Tube.le_volume.c n : ENNReal) * p) (fun j _ => by
          simpa [hn, hp] using Tube.le_volume (E := E) (V j).toTube)
      simpa [nsmul_eq_mul] using this
    have hup : (∑ i ∈ s, volume (V i).carrier)
        ≤ (s.card : ENNReal) * ((Tube.volume_le.C n : ENNReal) * p) := by
      have := Finset.sum_le_card_nsmul s (fun i => volume (V i).carrier)
        ((Tube.volume_le.C n : ENNReal) * p) (fun i _ => by
          simpa [hn, hp] using Tube.volume_le (E := E) hδ1 (V i).toTube)
      simpa [nsmul_eq_mul] using this
    have hchain : ((s'.card : ENNReal) * p)
          * ((Tube.le_volume.c n : ENNReal) * ∑ i ∈ s, volume (V i).shade)
        ≤ ((s'.card : ENNReal) * p)
          * (A * (K : ENNReal) * (Tube.volume_le.C n : ENNReal)
              * ∑ i ∈ s', volume (V i).shade) := by
      calc ((s'.card : ENNReal) * p)
            * ((Tube.le_volume.c n : ENNReal) * ∑ i ∈ s, volume (V i).shade)
          = (∑ i ∈ s, volume (V i).shade)
              * ((s'.card : ENNReal) * ((Tube.le_volume.c n : ENNReal) * p)) := by ring
        _ ≤ (∑ i ∈ s, volume (V i).shade) * (∑ j ∈ s', volume (V j).carrier) :=
            mul_le_mul' le_rfl hlow
        _ ≤ (K : ENNReal)
              * ((∑ j ∈ s', volume (V j).shade) * (∑ i ∈ s, volume (V i).carrier)) := hdouble
        _ ≤ (K : ENNReal)
              * ((∑ j ∈ s', volume (V j).shade)
                  * ((s.card : ENNReal) * ((Tube.volume_le.C n : ENNReal) * p))) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl hup)
        _ ≤ (K : ENNReal)
              * ((∑ j ∈ s', volume (V j).shade)
                  * ((A * (s'.card : ENNReal)) * ((Tube.volume_le.C n : ENNReal) * p))) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' hcard le_rfl))
        _ = ((s'.card : ENNReal) * p)
              * (A * (K : ENNReal) * (Tube.volume_le.C n : ENNReal)
                  * ∑ i ∈ s', volume (V i).shade) := by ring
    have hc0 : ((s'.card : ENNReal) * p) ≠ 0 := by
      refine mul_ne_zero ?_ hp0
      simpa using (Finset.card_pos.mpr hne).ne'
    have hcT : ((s'.card : ENNReal) * p) ≠ ⊤ := ENNReal.mul_ne_top (by simp) hpT
    exact (ENNReal.mul_le_mul_iff_right hc0 hcT).mp hchain

/-- **A cardinality share is a mass share, under a dense shading** — the second route.

`Kakeya.ML2Shaded.HasDenseShading lam 𝕋 Y` is the *one-sided* pointwise hypothesis
`lam · |T_i| ≤ |Y_i|`, which `Kakeya.ML2Shaded.exists_denseShading_refinement` produces at the
absolute cost `2` of the shaded mass — no logarithm, no dyadic pigeonhole.  It converts a
cardinality share into a mass share just as well, at the loss `A · C_n / (lam · c_n)`.

The two routes price the same conversion differently and neither dominates:

* comparability costs `Kakeya.ML2Shaded.massBandLoss λ = O(η log (1/δ))` to establish and then
  `K = 2` to spend;
* density costs `2` to establish and then `lam⁻¹`, i.e. `≈ 2 δ^{-η}` under the standing
  `δ^η ≤ λ`, to spend.

The comparability route is the smaller of the two, which is why it is the one the assembled
`Kakeya.ML2Shading.exists_shadingBridge` uses; this variant exists so that the bridge is not tied
to one way of manufacturing the pointwise hypothesis, and because
`Kakeya.ML2Shaded.HasDenseShading` is the form that
`Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao_dense` hands back. -/
theorem sum_shade_le_of_card_le_of_denseShading {δ : NNReal} (hδ1 : δ ≤ 1)
    {s s' : Finset ι} (hsub : s' ⊆ s) {V : ι → ShadedTube δ E} {lam : NNReal}
    (hdense : ML2Shaded.HasDenseShading lam s (fun i => (V i).toShadedBody))
    {A : ENNReal} (hcard : (s.card : ENNReal) ≤ A * (s'.card : ENNReal)) :
    (lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
        * ∑ i ∈ s, volume (V i).shade
      ≤ A * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
          * ∑ i ∈ s', volume (V i).shade := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set p : ENNReal := (δ : ENNReal) ^ (n - 1) with hp
  have hlow : (s'.card : ENNReal) * ((lam : ENNReal) * ((Tube.le_volume.c n : ENNReal) * p))
      ≤ ∑ j ∈ s', volume (V j).shade := by
    have := Finset.card_nsmul_le_sum s' (fun j => volume (V j).shade)
      ((lam : ENNReal) * ((Tube.le_volume.c n : ENNReal) * p)) (fun j hj => by
        refine le_trans (mul_le_mul' le_rfl ?_) (hdense j (hsub hj))
        simpa [hn, hp] using Tube.le_volume (E := E) (V j).toTube)
    simpa [nsmul_eq_mul] using this
  have hup : (∑ i ∈ s, volume (V i).shade)
      ≤ (s.card : ENNReal) * ((Tube.volume_le.C n : ENNReal) * p) := by
    have := Finset.sum_le_card_nsmul s (fun i => volume (V i).shade)
      ((Tube.volume_le.C n : ENNReal) * p) (fun i _ => by
        refine le_trans (measure_mono ((V i).toShadedBody).shade_subset) ?_
        simpa [hn, hp] using Tube.volume_le (E := E) hδ1 (V i).toTube)
    simpa [nsmul_eq_mul] using this
  calc (lam : ENNReal) * (Tube.le_volume.c n : ENNReal) * ∑ i ∈ s, volume (V i).shade
      ≤ (lam : ENNReal) * (Tube.le_volume.c n : ENNReal)
          * ((s.card : ENNReal) * ((Tube.volume_le.C n : ENNReal) * p)) :=
        mul_le_mul' le_rfl hup
    _ ≤ (lam : ENNReal) * (Tube.le_volume.c n : ENNReal)
          * ((A * (s'.card : ENNReal)) * ((Tube.volume_le.C n : ENNReal) * p)) :=
        mul_le_mul' le_rfl (mul_le_mul' hcard le_rfl)
    _ = A * (Tube.volume_le.C n : ENNReal)
          * ((s'.card : ENNReal)
              * ((lam : ENNReal) * ((Tube.le_volume.c n : ENNReal) * p))) := by ring
    _ ≤ A * (Tube.volume_le.C n : ENNReal) * ∑ i ∈ s', volume (V i).shade :=
        mul_le_mul' le_rfl hlow

/-! ### From a share of the shaded mass to a share of the fullness -/

omit [Nontrivial E] in
/-- **A mass share is a fullness share.**

The exact converse of `Kakeya.ML2Shaded.sum_shade_le_of_fullness_le`: passing to a subfamily can
only shrink the total carrier mass, so a mass retention on `𝕋' ⊆ 𝕋` with the same tubes is a
fullness retention with the same constant.  The scalar `a` is carried so that the statement can be
applied with the dimensional constant `c_n` of
`Kakeya.ML2Shading.sum_shade_le_of_card_le_of_comparableDensities` already in place.

This is the clause that lets the bridge *produce* the fullness hypothesis
`δ^η ≤ λ(𝕋', Y')` of `Kakeya.ML2Reduction.exists_everyScale_multiplicity_le`, rather than assume
it.  Producing it is the whole point: `λ(𝕋', Y')` is a hypothesis no consumer of the dichotomy can
supply directly, since the dichotomy chooses `𝕋'` and is blind to the shading. -/
theorem mul_fullness'_le_of_mul_sum_shade_le {δ : NNReal}
    {s s' : Finset ι} (hsub : s' ⊆ s) {V V' : ι → ShadedTube δ E}
    (htube : ∀ i, (V' i).toTube = (V i).toTube) {a L : ENNReal}
    (hmass : a * ∑ i ∈ s, volume (V i).shade ≤ L * ∑ i ∈ s', volume (V' i).shade) :
    a * ShadedBody.fullness' s (fun i => (V i).toShadedBody)
      ≤ L * ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) := by
  have hcar : (∑ i ∈ s', volume (V' i).carrier) ≤ ∑ i ∈ s, volume (V i).carrier := by
    have hEq : ∀ i ∈ s', volume (V' i).carrier = volume (V i).carrier := by
      intro i _
      congr 1
      calc (V' i).carrier = (V' i).toTube.carrier := rfl
        _ = (V i).toTube.carrier := by rw [htube i]
        _ = (V i).carrier := rfl
    calc (∑ i ∈ s', volume (V' i).carrier) = ∑ i ∈ s', volume (V i).carrier :=
          Finset.sum_congr rfl hEq
      _ ≤ ∑ i ∈ s, volume (V i).carrier :=
          Finset.sum_le_sum_of_subset hsub
  calc a * ShadedBody.fullness' s (fun i => (V i).toShadedBody)
      = (a * ∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier) :=
        (mul_div_assoc _ _ _).symm
    _ ≤ (L * ∑ i ∈ s', volume (V' i).shade) / (∑ i ∈ s', volume (V' i).carrier) :=
        ENNReal.div_le_div hmass hcar
    _ = L * ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) :=
        mul_div_assoc _ _ _

/-! ### From the multiplicity of the refined subfamily back to the original union -/

omit [Nontrivial E] in
/-- **The union of the refined shading sits inside the original union.**

`𝕋' ⊆ 𝕋` and `Y' ⊆ Y`, so `|U(𝕋', Y')| ≤ |U(𝕋, Y)|`; this is the *favourable* direction, and it is
the reason the shading bridge is possible at all.  Shrinking a shading moves the numerator
`∑ |Y_i|` and the denominator `|⋃ Y_i|` of the multiplicity the same way, so neither
`μ(𝕋', Y') ≤ μ(𝕋, Y)` nor its converse holds in general; what does hold is that the *denominator*
only shrinks, which is exactly what a bound of the form `∑ |Y_i| ≤ C · |⋃ Y_i|` needs. -/
theorem sum_shade_le_mul_volume_iUnion {δ : NNReal}
    {s s' : Finset ι} (hsub : s' ⊆ s) {V V' : ι → ShadedTube δ E}
    (hshade : ∀ i, (V' i).shade ⊆ (V i).shade) {M : ENNReal}
    (hmult : ShadedBody.multiplicity s' (fun i => (V' i).toShadedBody) ≤ M) :
    ∑ i ∈ s', volume (V' i).shade ≤ M * volume (⋃ i ∈ s, (V i).shade) := by
  refine ((ShadedBody.multiplicity_le_iff s' (fun i => (V' i).toShadedBody)).mp hmult).trans ?_
  refine mul_le_mul' le_rfl (measure_mono ?_)
  exact Set.iUnion₂_subset fun i hi x hx => Set.mem_biUnion (hsub hi) (hshade i hx)

/-! ### The shading bridge, in hypothesis form -/

/-- **The shading bridge, with its three losses handed in.**

`c_n · ∑_{i ∈ 𝕋} |Y_i| ≤ A · K · C_n · B · M · |U(𝕋, Y)|`, where

* `A` is the **cardinality loss** of GWZ Lemma 7.7(B) (`StickyKakeya.totalLoss`),
* `K` is the **comparability constant** of the shading densities on `𝕋`
  (the absolute `2` of `Kakeya.ML2Shaded.exists_massBanded_shadeRefinement`),
* `C_n / c_n` is the **dimensional tube-volume ratio**,
* `B` is the **shaded-uniformization loss** `(log₂ #𝕋 + 1)^{2N+2}` of
  `ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet`, and
* `M` is whatever multiplicity bound GWZ Theorem 7.3(B) delivers on the refined subfamily.

No hypothesis is aggregate-read-as-pointwise: `hcomp` is pointwise and is *consumed* pointwise;
`hcard`, `hrefine` and `hmult` are aggregate and are consumed as aggregates. -/
theorem sum_shade_le_of_everyScale {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {s s' : Finset ι} (hsub : s' ⊆ s) {V V' : ι → ShadedTube δ E}
    (htube : ∀ i, (V' i).toTube = (V i).toTube)
    (hshade : ∀ i, (V' i).shade ⊆ (V i).shade) {K : NNReal}
    (hcomp : ML2Shaded.HasComparableDensities K s (fun i => (V i).toShadedBody))
    {A : ENNReal} (hcard : (s.card : ENNReal) ≤ A * (s'.card : ENNReal))
    {B : ENNReal} (hrefine : ShadedBody.fullness' s' (fun i => (V i).toShadedBody)
        ≤ B * ShadedBody.fullness' s' (fun i => (V' i).toShadedBody))
    {M : ENNReal} (hmult : ShadedBody.multiplicity s' (fun i => (V' i).toShadedBody) ≤ M) :
    (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) * ∑ i ∈ s, volume (V i).shade
      ≤ A * (K : ENNReal) * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * B * M
          * volume (⋃ i ∈ s, (V i).shade) := by
  have h1 := sum_shade_le_of_card_le_of_comparableDensities hδ0 hδ1 hsub hcomp hcard
  have h2 := ML2Shaded.sum_shade_le_of_fullness_le (V := V) (V' := V') hδ0 htube hrefine
  have h3 := sum_shade_le_mul_volume_iUnion hsub hshade hmult
  calc (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) * ∑ i ∈ s, volume (V i).shade
      ≤ A * (K : ENNReal) * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
          * ∑ i ∈ s', volume (V i).shade := h1
    _ ≤ A * (K : ENNReal) * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
          * (B * ∑ i ∈ s', volume (V' i).shade) := mul_le_mul' le_rfl h2
    _ = A * (K : ENNReal) * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * B
          * ∑ i ∈ s', volume (V' i).shade := by ring
    _ ≤ A * (K : ENNReal) * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * B
          * (M * volume (⋃ i ∈ s, (V i).shade)) := mul_le_mul' le_rfl h3
    _ = A * (K : ENNReal) * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * B * M
          * volume (⋃ i ∈ s, (V i).shade) := by ring

/-- **The shading bridge along the dense-shading route.**

`Kakeya.ML2Shading.sum_shade_le_of_everyScale` with
`Kakeya.ML2Shaded.HasComparableDensities K` replaced by
`Kakeya.ML2Shaded.HasDenseShading lam`, and the factor `K` on the right replaced by the factor
`lam` on the left.  Nothing else changes: the shaded-uniformization loss `B` and the multiplicity
bound `M` are consumed exactly as before. -/
theorem sum_shade_le_of_everyScale_dense {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {s s' : Finset ι} (hsub : s' ⊆ s) {V V' : ι → ShadedTube δ E}
    (htube : ∀ i, (V' i).toTube = (V i).toTube)
    (hshade : ∀ i, (V' i).shade ⊆ (V i).shade) {lam : NNReal}
    (hdense : ML2Shaded.HasDenseShading lam s (fun i => (V i).toShadedBody))
    {A : ENNReal} (hcard : (s.card : ENNReal) ≤ A * (s'.card : ENNReal))
    {B : ENNReal} (hrefine : ShadedBody.fullness' s' (fun i => (V i).toShadedBody)
        ≤ B * ShadedBody.fullness' s' (fun i => (V' i).toShadedBody))
    {M : ENNReal} (hmult : ShadedBody.multiplicity s' (fun i => (V' i).toShadedBody) ≤ M) :
    (lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
        * ∑ i ∈ s, volume (V i).shade
      ≤ A * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * B * M
          * volume (⋃ i ∈ s, (V i).shade) := by
  have h1 := sum_shade_le_of_card_le_of_denseShading hδ1 hsub hdense hcard
  have h2 := ML2Shaded.sum_shade_le_of_fullness_le (V := V) (V' := V') hδ0 htube hrefine
  have h3 := sum_shade_le_mul_volume_iUnion hsub hshade hmult
  calc (lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
        * ∑ i ∈ s, volume (V i).shade
      ≤ A * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
          * ∑ i ∈ s', volume (V i).shade := h1
    _ ≤ A * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
          * (B * ∑ i ∈ s', volume (V' i).shade) := mul_le_mul' le_rfl h2
    _ = A * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * B
          * ∑ i ∈ s', volume (V' i).shade := by ring
    _ ≤ A * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * B
          * (M * volume (⋃ i ∈ s, (V i).shade)) := mul_le_mul' le_rfl h3
    _ = A * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * B * M
          * volume (⋃ i ∈ s, (V i).shade) := by ring

/-- **The fullness input of GWZ Theorem 7.3(B), produced rather than assumed.** -/
theorem mul_fullness'_le_of_card_le {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {s s' : Finset ι} (hsub : s' ⊆ s) {V V' : ι → ShadedTube δ E}
    (htube : ∀ i, (V' i).toTube = (V i).toTube) {K : NNReal}
    (hcomp : ML2Shaded.HasComparableDensities K s (fun i => (V i).toShadedBody))
    {A : ENNReal} (hcard : (s.card : ENNReal) ≤ A * (s'.card : ENNReal))
    {B : ENNReal} (hrefine : ShadedBody.fullness' s' (fun i => (V i).toShadedBody)
        ≤ B * ShadedBody.fullness' s' (fun i => (V' i).toShadedBody)) :
    (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
        * ShadedBody.fullness' s (fun i => (V i).toShadedBody)
      ≤ A * (K : ENNReal) * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * B
          * ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) := by
  refine mul_fullness'_le_of_mul_sum_shade_le hsub htube ?_
  have h1 := sum_shade_le_of_card_le_of_comparableDensities hδ0 hδ1 hsub hcomp hcard
  have h2 := ML2Shaded.sum_shade_le_of_fullness_le (V := V) (V' := V') hδ0 htube hrefine
  calc (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) * ∑ i ∈ s, volume (V i).shade
      ≤ A * (K : ENNReal) * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
          * ∑ i ∈ s', volume (V i).shade := h1
    _ ≤ A * (K : ENNReal) * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
          * (B * ∑ i ∈ s', volume (V' i).shade) := mul_le_mul' le_rfl h2
    _ = A * (K : ENNReal) * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * B
          * ∑ i ∈ s', volume (V' i).shade := by ring

/-! ### The loss the bridge charges -/

/-- **The loss charged by the shading bridge**, as a single expression:

`shadingBridgeLoss n A K clamp N = A · K · C_n · (clamp + 1)^{2N+2}`,

read against the denominator `c_n` of `Tube.le_volume` that every statement below carries on the
left.  The four factors are, in order,

* `A`  — the **cardinality loss** of GWZ Lemma 7.7(B); at the call site this is
  `StickyKakeya.totalLoss C K c δ`, absorbed by `StickyKakeya.exists_threshold_totalLoss_le`;
* `K`  — the **comparability constant** of the shading densities, the absolute `2` of
  `Kakeya.ML2Shaded.exists_massBanded_shadeRefinement`;
* `C_n / c_n` — the **dimensional tube-volume ratio** `Tube.volume_le.C n / Tube.le_volume.c n`,
  a constant;
* `(clamp + 1)^{2N+2}` — the **shaded-uniformization loss** of
  `ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet` at `clamp = log₂ #𝕋`,
  `N = Tube.ssfGridLen δ`.  This one is subpolynomial but not bounded: with
  `#𝕋 ≤ δ^{-4}` (`Kakeya.ML2Assembly.card_le_rpow_neg_four`) and
  `Tube.ssfGridLen δ = ⌈log log (1/δ)⌉` it is `exp(O((log log 1/δ)^2))`, absorbed by
  `Tube.exists_threshold_polylog_pow_ssfGridLen_le`.

The bridge does **not** additionally charge the mass-banding loss
`Kakeya.ML2Shaded.massBandLoss`; that one is charged separately, and only where the comparability
constant `K` is actually manufactured, by
`Kakeya.ML2Shading.sum_shade_le_of_everyScale_banded`. -/
noncomputable def shadingBridgeLoss (n : ℕ) (A : ENNReal) (K : NNReal) (clamp N : ℕ) : ENNReal :=
  A * (K : ENNReal) * (Tube.volume_le.C n : ENNReal) * ((clamp + 1 : ℕ) : ENNReal) ^ (2 * N + 2)

theorem shadingBridgeLoss_ne_zero {n : ℕ} {A : ENNReal} {K : NNReal} {clamp N : ℕ}
    (hA0 : A ≠ 0) (hK0 : K ≠ 0) : shadingBridgeLoss n A K clamp N ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero hA0 (ENNReal.coe_ne_zero.mpr hK0)) ?_) ?_
  · exact ENNReal.coe_ne_zero.mpr (Tube.volume_le.C_pos n).ne'
  · exact pow_ne_zero _ (by exact_mod_cast Nat.succ_ne_zero clamp)

theorem shadingBridgeLoss_ne_top {n : ℕ} {A : ENNReal} {K : NNReal} {clamp N : ℕ}
    (hAT : A ≠ ⊤) : shadingBridgeLoss n A K clamp N ≠ ⊤ := by
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hAT ENNReal.coe_ne_top)
    ENNReal.coe_ne_top) ?_
  exact ENNReal.pow_ne_top (by simp)

/-! ### The shading bridge -/

/-- **The shading bridge (component G2d of `Kakeya.ML2Assembly.GeometricCore`).**

`StickyKakeya.dividingScalesKatzTao` — GWZ Lemma 7.7(B) — hands back a subfamily `𝕋' ⊆ 𝕋`
carrying a *tube* hierarchy `𝒰` and a **cardinality** retention `#𝕋 ≤ A · #𝕋'`, and it is blind to
the shading.  GWZ Theorem 7.3(B), as
`Kakeya.ML2Reduction.exists_everyScale_multiplicity_le` states it, consumes a
`ShadedTube.ShadedUniformTubeSet` on the very hierarchy the every-scale hypothesis is read on,
together with a **fullness lower bound** `δ^η ≤ λ(𝕋', Y')` on the refined pair, and returns a
multiplicity bound on `(𝕋', Y')`.  This theorem is the bridge between the two, and it discharges
all three obligations:

1. it **builds the shading** — `ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet` refines
   `Y` to `Y' ⊆ Y` over the *given* hierarchy, so the returned `𝒱` has
   `cover.{indexSet, assign, tube}` and `branchingN` equal to `𝒰`'s and the every-scale hypothesis
   transports verbatim (third clause, via
   `Kakeya.ML2Reduction.isKatzTaoAtEveryScale_of_cover_eq`);
2. it **produces the fullness input** (fourth clause) rather than assuming it — this is the clause
   no consumer can supply by itself, because the dichotomy chooses `𝕋'` without looking at `Y`;
3. it **transports the conclusion back** from `(𝕋', Y')` to `(𝕋, Y)` (fifth clause), which is the
   step that needs the cardinality retention converted into a mass retention.

**Where the comparability hypothesis comes from, and why it is not optional.**  Step 3 is a
cardinality-to-mass conversion, and no such conversion exists without a pointwise hypothesis:
`𝕋'` is chosen by a lemma that never looks at `Y`, so it may consist entirely of unshaded tubes
while `#𝕋 ≤ A · #𝕋'` still holds.  `hcomp` is exactly the missing pointwise information, it is
supplied by `Kakeya.ML2Shaded.exists_massBanded_shadeRefinement` at the absolute constant `K = 2`,
and `Kakeya.ML2Shading.sum_shade_le_of_everyScale_banded` is the version in which it has been
discharged and its loss charged.  This is the one place in the bridge where the recurring
"aggregate bound consumed as a pointwise one" defect could have entered, and it is where it is
paid for.

**The `ε`-discipline.**  Neither `θ` nor `η` is the outer accuracy `ε`.  `θ` is the level at which
the standing hypotheses of Main Lemma 2 are read, `η` is the level at which GWZ Theorem 7.3(B) is
read, and `habs` is the exact statement that the loss fits between them:
`shadingBridgeLoss · δ^η ≤ c_n · δ^θ`.  Since the loss is subpolynomial, any `η > θ` works below a
threshold that depends on `(θ, η)` and on the constants only — never on `ε`.  The bridge therefore
adds no `ε`-dependence to the chain `ε → ε₁ → ε₂ → (N, η_i) → ν`;
`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy` remains untouched. -/
theorem exists_shadingBridge {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {s s' : Finset ι} (hsub : s' ⊆ s) {V : ι → ShadedTube δ E}
    {N : ℕ} (hN : 0 < N) {C : NNReal}
    (𝒰 : UniformTubeSet s' (fun i => (V i).toTube) N C)
    {K : NNReal} (hK0 : K ≠ 0)
    (hcomp : ML2Shaded.HasComparableDensities K s (fun i => (V i).toShadedBody))
    {A : ENNReal} (hA0 : A ≠ 0) (hAT : A ≠ ⊤)
    (hcard : (s.card : ENNReal) ≤ A * (s'.card : ENNReal))
    {θ η : ℝ}
    (hθ : ENNReal.ofReal ((δ : ℝ) ^ θ)
        ≤ ShadedBody.fullness' s (fun i => (V i).toShadedBody))
    (habs : shadingBridgeLoss (Module.finrank ℝ E) A K (Nat.log 2 s.card) N
              * ENNReal.ofReal ((δ : ℝ) ^ η)
            ≤ (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
              * ENNReal.ofReal ((δ : ℝ) ^ θ)) :
    ∃ V' : ι → ShadedTube δ E, ∃ 𝒱 : ShadedUniformTubeSet s' V' N (max C 4),
      (∀ i, (V' i).toTube = (V i).toTube) ∧
      (∀ i, (V' i).shade ⊆ (V i).shade) ∧
      (∀ Aes : ENNReal, 𝒰.IsKatzTaoAtEveryScale Aes →
        𝒱.tubeUniform.IsKatzTaoAtEveryScale Aes) ∧
      ENNReal.ofReal ((δ : ℝ) ^ η)
        ≤ ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) ∧
      ∀ M : ENNReal, ShadedBody.multiplicity s' (fun i => (V' i).toShadedBody) ≤ M →
        (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) * ∑ i ∈ s, volume (V i).shade
          ≤ shadingBridgeLoss (Module.finrank ℝ E) A K (Nat.log 2 s.card) N * M
              * volume (⋃ i ∈ s, (V i).shade) := by
  classical
  have hclamp : ∀ t : Finset ι, t ⊆ s' → Nat.log 2 t.card ≤ Nat.log 2 s.card :=
    fun t ht => Nat.log_mono_right (Finset.card_le_card (ht.trans hsub))
  obtain ⟨V', htube, hshade, hfull, 𝒱, hIdx, hAss, hTube, hBr⟩ :=
    ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet (V := V) (𝒰 := 𝒰) hN
      (Nat.log 2 s.card) hclamp
  refine ⟨V', 𝒱, htube, hshade, ?_, ?_, ?_⟩
  · exact fun Aes h => ML2Reduction.isKatzTaoAtEveryScale_of_cover_eq hIdx hTube h
  · refine le_of_absorb (shadingBridgeLoss_ne_zero hA0 hK0)
      (shadingBridgeLoss_ne_top hAT) ?_ hθ habs
    simpa [shadingBridgeLoss, mul_assoc] using
      mul_fullness'_le_of_card_le hδ0 hδ1 hsub htube hcomp hcard hfull
  · intro M hM
    simpa [shadingBridgeLoss, mul_assoc] using
      sum_shade_le_of_everyScale hδ0 hδ1 hsub htube hshade hcomp hcard hfull hM

/-! ### The bridge with the comparability hypothesis discharged -/

/-- **The shading bridge with the mass banding folded in.**

The same statement as `Kakeya.ML2Shading.exists_shadingBridge`, with the pointwise comparability
hypothesis removed and its price — `Kakeya.ML2Shaded.massBandLoss λ`, i.e.
`2(1 + log₂(2/λ))`, which is `O(η log(1/δ))` under the standing `δ^η ≤ λ` — charged explicitly.

The hypothesis `hbr` is "GWZ Lemma 7.7(B) followed by the shaded uniformization and by GWZ Theorem
7.3(B), applied to an arbitrary subfamily of `𝕋`".  It is quantified over subfamilies because the
banding has to happen **before** the dichotomy: `Kakeya.ML2Shaded.HasComparableDensities` is
two-sided and pointwise, so it cannot be produced on a family the dichotomy has already chosen
(`Kakeya.ML2Shaded.not_hasComparableDensities_of_aggregate_retention`), and the uniformization
`ShadedTube.exists_shadedUniformTubeSet_subfamily` that the dichotomy's `Tube.UniformTubeSet` input
comes from is itself applied to a subfamily.  Its three losses `A`, `B`, `M` are bound before the
subfamily, which is legitimate because each of them is a function of `δ` and of a cardinality bound
for `𝕋` alone, both of which the outer family already fixes. -/
theorem sum_shade_le_of_everyScale_banded {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (s : Finset ι) (V : ι → ShadedTube δ E) {A B M : ENNReal}
    (hbr : ∀ u ⊆ s, ML2Shaded.HasComparableDensities 2 u (fun i => (V i).toShadedBody) →
      ∃ u' ⊆ u, ∃ V' : ι → ShadedTube δ E,
        (∀ i, (V' i).toTube = (V i).toTube) ∧
        (∀ i, (V' i).shade ⊆ (V i).shade) ∧
        (u.card : ENNReal) ≤ A * (u'.card : ENNReal) ∧
        ShadedBody.fullness' u' (fun i => (V i).toShadedBody)
            ≤ B * ShadedBody.fullness' u' (fun i => (V' i).toShadedBody) ∧
        ShadedBody.multiplicity u' (fun i => (V' i).toShadedBody) ≤ M) :
    (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) * ∑ i ∈ s, volume (V i).shade
      ≤ ML2Shaded.massBandLoss (ShadedBody.fullness s (fun i => (V i).toShadedBody))
          * (A * 2 * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * B * M)
          * volume (⋃ i ∈ s, (V i).shade) := by
  classical
  obtain ⟨u, hus, hband, hcomp⟩ := ML2Shaded.exists_massBanded_shadeRefinement hδ0 s V
  obtain ⟨u', hu'u, V', htube, hshade, hcard, hrefine, hmult⟩ := hbr u hus hcomp
  have hb := sum_shade_le_of_everyScale hδ0 hδ1 hu'u htube hshade hcomp hcard hrefine hmult
  have hU : volume (⋃ i ∈ u, (V i).shade) ≤ volume (⋃ i ∈ s, (V i).shade) :=
    measure_mono (Set.iUnion₂_subset fun i hi x hx => Set.mem_biUnion (hus hi) hx)
  calc (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) * ∑ i ∈ s, volume (V i).shade
      ≤ (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
          * (ML2Shaded.massBandLoss (ShadedBody.fullness s (fun i => (V i).toShadedBody))
              * ∑ i ∈ u, volume (V i).shade) := mul_le_mul' le_rfl hband
    _ = ML2Shaded.massBandLoss (ShadedBody.fullness s (fun i => (V i).toShadedBody))
          * ((Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
              * ∑ i ∈ u, volume (V i).shade) := by ring
    _ ≤ ML2Shaded.massBandLoss (ShadedBody.fullness s (fun i => (V i).toShadedBody))
          * (A * ((2 : NNReal) : ENNReal)
              * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * B * M
              * volume (⋃ i ∈ u, (V i).shade)) := mul_le_mul' le_rfl hb
    _ ≤ ML2Shaded.massBandLoss (ShadedBody.fullness s (fun i => (V i).toShadedBody))
          * (A * ((2 : NNReal) : ENNReal)
              * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * B * M
              * volume (⋃ i ∈ s, (V i).shade)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hU)
    _ = ML2Shaded.massBandLoss (ShadedBody.fullness s (fun i => (V i).toShadedBody))
          * (A * 2 * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * B * M)
          * volume (⋃ i ∈ s, (V i).shade) := by
        push_cast
        ring

/-- **The mass-banded subfamily inherits the fullness, up to `Kakeya.ML2Shaded.massBandLoss`.**

The missing link of the banded route.  `Kakeya.ML2Shaded.exists_massBanded_shadeRefinement`
returns a *mass* retention on `u ⊆ 𝕋`; what
`Kakeya.ML2Shading.exists_shadingBridge` then wants on `u` is a *fullness* lower bound, since it is
`λ(u, Y)` and not `λ(𝕋, Y)` that it propagates to `(𝕋', Y')`.  The carriers are untouched and `u`
is a subfamily, so `Kakeya.ML2Shading.mul_fullness'_le_of_mul_sum_shade_le` converts one into the
other with the same constant, and the standing hypothesis `δ^θ ≤ λ(𝕋, Y)` of Main Lemma 2 becomes
`δ^θ ≤ massBandLoss λ · λ(u, Y)` — a fullness bound on `u` at the level `θ` plus the banding loss,
which is subpolynomial by `Kakeya.ML2Shaded.exists_threshold_massBandLoss_le`.

Without this the banded route would be a shell game: the comparability hypothesis would have been
discharged at the price of a hypothesis that the next step could no longer meet. -/
theorem le_fullness'_massBanded {δ : NNReal} (hδ0 : 0 < δ)
    (s : Finset ι) (V : ι → ShadedTube δ E) :
    ∃ u ⊆ s,
      ML2Shaded.HasComparableDensities 2 u (fun i => (V i).toShadedBody) ∧
      (∑ i ∈ s, volume (V i).shade)
          ≤ ML2Shaded.massBandLoss (ShadedBody.fullness s (fun i => (V i).toShadedBody))
              * ∑ i ∈ u, volume (V i).shade ∧
      ShadedBody.fullness' s (fun i => (V i).toShadedBody)
          ≤ ML2Shaded.massBandLoss (ShadedBody.fullness s (fun i => (V i).toShadedBody))
              * ShadedBody.fullness' u (fun i => (V i).toShadedBody) := by
  obtain ⟨u, hus, hband, hcomp⟩ := ML2Shaded.exists_massBanded_shadeRefinement hδ0 s V
  refine ⟨u, hus, hcomp, hband, ?_⟩
  simpa using
    mul_fullness'_le_of_mul_sum_shade_le (a := 1) (V := V) (V' := V) hus (fun _ => rfl)
      (by simpa using hband)

/-! ### Landing on the left disjunct of `Kakeya.ML2Assembly.Dichotomy` -/

/-- The **left disjunct** of `Kakeya.ML2Assembly.Dichotomy`, copied verbatim.  The compatibility
`example` below pins it to the real thing. -/
def DichotomyLeft {δ : NNReal} {ι : Type*} (ε₀ : ℝ) (s : Finset ι)
    (T : ι → ShadedTube δ E) : Prop :=
  ∑ i ∈ s, volume (T i).shade
    ≤ (δ : ENNReal) ^ (-ε₀) * volume (⋃ i ∈ s, (T i).shade)

omit [Nontrivial E] in
/-- **The bridge, once its loss is absorbed, is the left disjunct of the dichotomy.**

The absorption hypothesis `habs` is the only thing between
`Kakeya.ML2Shading.exists_shadingBridge` and `Kakeya.ML2Assembly.Dichotomy`: the whole loss,
including the multiplicity bound `M = δ^{-ε₁}` that GWZ Theorem 7.3(B) returns at the absolute
accuracy `ε₁`, must fit under `c_n · δ^{-ε₀}`.  With `ε₀ = β₀/2` read at the **threshold** and the
loss subpolynomial, this is a threshold condition on `δ` alone. -/
theorem dichotomyLeft_of_bridge {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E}
    {Loss : ENNReal} {ε₀ : ℝ}
    (hbound : (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) * ∑ i ∈ s, volume (V i).shade
        ≤ Loss * volume (⋃ i ∈ s, (V i).shade))
    (habs : Loss ≤ (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) * (δ : ENNReal) ^ (-ε₀)) :
    DichotomyLeft ε₀ s V := by
  have hc0 : (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos _).ne'
  have hcT : (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  refine le_of_mul_le_mul_left' hc0 hcT ?_
  calc (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) * ∑ i ∈ s, volume (V i).shade
      ≤ Loss * volume (⋃ i ∈ s, (V i).shade) := hbound
    _ ≤ ((Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) * (δ : ENNReal) ^ (-ε₀))
          * volume (⋃ i ∈ s, (V i).shade) := mul_le_mul' habs le_rfl
    _ = (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
          * ((δ : ENNReal) ^ (-ε₀) * volume (⋃ i ∈ s, (V i).shade)) := by ring

/-- **Fidelity compatibility.**  `Kakeya.ML2Shading.DichotomyLeft` is the *left disjunct* of
`Kakeya.ML2Assembly.Dichotomy`, with every binder written out: supplying it under the dichotomy's
own hypotheses supplies the dichotomy.  If the two ever drift apart, this `example` stops
compiling. -/
example {β ε₀ g η : ℝ}
    (h : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
        DichotomyLeft ε₀ s T) :
    ML2Assembly.Dichotomy.{u} β ε₀ g η := by
  filter_upwards [h] with δ hδ
  intro ι s T hball hKT hfull hcardge
  exact Or.inl (hδ s T hball hKT hfull hcardge)

/-! ### Non-vacuity -/

/-- **Non-vacuity of `Kakeya.ML2Shading.sum_shade_le_of_everyScale`.**

Every hypothesis of the bridge is simultaneously satisfiable, and on a singleton family at
`𝕋' = 𝕋`, `Y' = Y`, `A = B = K = 1` the conclusion is the (nontrivial) statement
`c_n |Y| ≤ C_n μ({i₀}, Y) |Y|`.  The bridge is therefore not vacuous, and its hypotheses do not
silently force the family to be empty or unshaded. -/
example {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (i₀ : ι) (V : ι → ShadedTube δ E) :
    (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
        * ∑ i ∈ ({i₀} : Finset ι), volume (V i).shade
      ≤ 1 * ((1 : NNReal) : ENNReal) * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * 1
          * ShadedBody.multiplicity ({i₀} : Finset ι) (fun i => (V i).toShadedBody)
          * volume (⋃ i ∈ ({i₀} : Finset ι), (V i).shade) := by
  classical
  refine sum_shade_le_of_everyScale hδ0 hδ1 (le_refl ({i₀} : Finset ι)) (fun _ => rfl)
    (fun _ => subset_rfl) ?_ ?_ ?_ le_rfl
  · intro i hi j hj
    simp only [Finset.mem_singleton] at hi hj
    subst hi; subst hj
    simp
  · simp
  · simp


/-- **Non-vacuity of `Kakeya.ML2Shading.sum_shade_le_of_everyScale_banded`.**

The hypothesis `hbr` is satisfiable, and not only by a degenerate choice: taking `𝕋' = 𝕋`,
`Y' = Y`, `A = B = 1` and `M = #𝕋` (`ShadedBody.multiplicity_le_card`) turns the banded bridge into
the true bound `c_n ∑ |Y_i| ≤ massBandLoss λ · 2 C_n #𝕋 · |U(𝕋, Y)|`, for *every* family.  So the
banded statement neither presupposes the dichotomy nor asks for a hypothesis that no call site can
meet; the dichotomy's job is only to replace `#𝕋` by `δ^{-ε₁}`. -/
example {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (s : Finset ι) (V : ι → ShadedTube δ E) :
    (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) * ∑ i ∈ s, volume (V i).shade
      ≤ ML2Shaded.massBandLoss (ShadedBody.fullness s (fun i => (V i).toShadedBody))
          * (1 * 2 * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * 1 * (s.card : ENNReal))
          * volume (⋃ i ∈ s, (V i).shade) := by
  refine sum_shade_le_of_everyScale_banded hδ0 hδ1 s V ?_
  intro u hu _hcomp
  refine ⟨u, subset_rfl, V, fun _ => rfl, fun _ => subset_rfl, by simp, by simp, ?_⟩
  refine (ShadedBody.multiplicity_le_card u (fun i => (V i).toShadedBody)).trans ?_
  exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hu)


/-! ### The bridge loss is subpolynomial: the explicit threshold -/

omit [Nontrivial E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- **The absorption `habs` of `Kakeya.ML2Shading.exists_shadingBridge`, from a budget.** -/
theorem shadingBridge_absorb {n : ℕ} {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {L : ENNReal} {b θ η : ℝ}
    (hL : L ≤ (Tube.le_volume.c n : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-b)))
    (hbud : θ + b ≤ η) :
    L * ENNReal.ofReal ((δ : ℝ) ^ η)
      ≤ (Tube.le_volume.c n : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ θ) := by
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδR1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  calc L * ENNReal.ofReal ((δ : ℝ) ^ η)
      ≤ ((Tube.le_volume.c n : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-b)))
          * ENNReal.ofReal ((δ : ℝ) ^ η) := mul_le_mul' hL le_rfl
    _ = (Tube.le_volume.c n : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-b + η)) := by
        rw [mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδR.le _), ← Real.rpow_add hδR]
    _ ≤ (Tube.le_volume.c n : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ θ) := by
        refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
        exact Real.rpow_le_rpow_of_exponent_ge hδR hδR1 (by linarith)

omit [Nontrivial E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- **The loss charged by the shading bridge is subpolynomial.**

For every ambient dimension `n`, comparability constant `K`, cardinality exponent `K₀`,
cardinality-loss exponent `a ≥ 0` and every gain `α > 0` there is a threshold `d > 0`, *bound
before the scale and before the family*, below which

`shadingBridgeLoss n A K (log₂ #𝕋) (ssfGridLen δ) ≤ c_n · δ^{-(a+α)}`

whenever the cardinality loss `A` is at most `δ^{-a}` and `#𝕋 ≤ δ^{-K₀}`.

This is the statement that the hypothesis `habs` of
`Kakeya.ML2Shading.exists_shadingBridge` is satisfiable, and that it is satisfiable at an
`ε`-free budget: neither `d` nor `α` sees the outer accuracy.  Combined with
`Kakeya.ML2Shading.shadingBridge_absorb` it says that the bridge costs `a + α` in the exponent, so
that reading GWZ Theorem 7.3(B) at any level `η ≥ θ + a + α` suffices.

The two ingredients are `Tube.exists_threshold_polylog_pow_ssfGridLen_le` for the
shaded-uniformization factor `(log₂ #𝕋 + 1)^{2 ssfGridLen δ + 2}` — which is *not* bounded, only
subpolynomial, since `ssfGridLen δ = ⌈log log (1/δ)⌉` grows — and
`Kakeya.ML2Shaded.exists_threshold_const_le_rpow_neg'` for the constant `K C_n / c_n`. -/
theorem exists_threshold_shadingBridgeLoss_le (n : ℕ) (K : NNReal) (K₀ : ℕ) {a α : ℝ}
    (hα : 0 < α) :
    ∃ d : NNReal, 0 < d ∧ d ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ d →
        ∀ {A : ENNReal}, A ≤ ENNReal.ofReal ((δ : ℝ) ^ (-a)) →
        ∀ m : ℕ, (m : ℝ) ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) →
          shadingBridgeLoss n A K (Nat.log 2 m) (Tube.ssfGridLen δ)
            ≤ (Tube.le_volume.c n : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-(a + α))) := by
  have hα2 : (0 : ℝ) < α / 2 := by linarith
  obtain ⟨d₁, hd₁0, hd₁1, hd₁⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le 1 le_rfl K₀ 2 (α / 2) hα2
  obtain ⟨d₂, hd₂0, hd₂1, hd₂⟩ :=
    ML2Shaded.exists_threshold_const_le_rpow_neg'
      ((K : ℝ) * (Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ)) hα2
  refine ⟨min d₁ d₂, lt_min hd₁0 hd₂0, (min_le_left _ _).trans hd₁1, ?_⟩
  intro δ hδ0 hδle A hA m hm
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hcpos : (0 : ℝ) < (Tube.le_volume.c n : ℝ) := by
    exact_mod_cast Tube.le_volume.c_pos n
  -- the shaded-uniformization factor
  have hP : ((Nat.log 2 m + 1 : ℕ) : ENNReal) ^ (2 * Tube.ssfGridLen δ + 2)
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(α / 2))) := by
    have hreal := (hd₁ hδ0 (hδle.trans (min_le_left _ _))).2.2 (m : ℝ)
      (by positivity) hm
    have hfl : ⌊Real.logb 2 (m : ℝ)⌋₊ = Nat.log 2 m := by
      simpa using Real.natFloor_logb_natCast 2 m
    rw [hfl] at hreal
    have hcast : ((Nat.log 2 m + 1 : ℕ) : ENNReal) ^ (2 * Tube.ssfGridLen δ + 2)
        = ENNReal.ofReal (((Nat.log 2 m : ℝ) + 1) ^ (2 * Tube.ssfGridLen δ + 2)) := by
      rw [ENNReal.ofReal_pow (by positivity)]
      norm_cast
    rw [hcast]
    refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) hreal)
    ring
  -- the constant
  have hKC : (K : ENNReal) * (Tube.volume_le.C n : ENNReal)
      ≤ (Tube.le_volume.c n : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-(α / 2))) := by
    have hreal := hd₂ hδ0 (hδle.trans (min_le_right _ _))
    have hmul : (K : ℝ) * (Tube.volume_le.C n : ℝ)
        ≤ (Tube.le_volume.c n : ℝ) * (δ : ℝ) ^ (-(α / 2)) := by
      rw [div_le_iff₀ hcpos] at hreal
      linarith [hreal]
    have h1 : (K : ENNReal) * (Tube.volume_le.C n : ENNReal)
        = ENNReal.ofReal ((K : ℝ) * (Tube.volume_le.C n : ℝ)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      simp [ENNReal.ofReal_coe_nnreal]
    have h2 : (Tube.le_volume.c n : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-(α / 2)))
        = ENNReal.ofReal ((Tube.le_volume.c n : ℝ) * (δ : ℝ) ^ (-(α / 2))) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      simp [ENNReal.ofReal_coe_nnreal]
    rw [h1, h2]
    exact ENNReal.ofReal_le_ofReal hmul
  -- assemble
  calc shadingBridgeLoss n A K (Nat.log 2 m) (Tube.ssfGridLen δ)
      = A * ((K : ENNReal) * (Tube.volume_le.C n : ENNReal))
          * ((Nat.log 2 m + 1 : ℕ) : ENNReal) ^ (2 * Tube.ssfGridLen δ + 2) := by
        rw [shadingBridgeLoss]; ring
    _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-a))
          * ((Tube.le_volume.c n : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-(α / 2))))
          * ENNReal.ofReal ((δ : ℝ) ^ (-(α / 2))) :=
        mul_le_mul' (mul_le_mul' hA hKC) hP
    _ = (Tube.le_volume.c n : ENNReal)
          * (ENNReal.ofReal ((δ : ℝ) ^ (-a)) * ENNReal.ofReal ((δ : ℝ) ^ (-(α / 2)))
              * ENNReal.ofReal ((δ : ℝ) ^ (-(α / 2)))) := by ring
    _ = (Tube.le_volume.c n : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-(a + α))) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδR.le _),
          ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hδR, ← Real.rpow_add hδR]
        ring_nf


/-- **Non-vacuity of the hypothesis `habs` of `Kakeya.ML2Shading.exists_shadingBridge`.**

For every exponent budget `θ + a + α ≤ η` there is a threshold below which `habs` holds, uniformly
in the family and in the cardinality loss `A ≤ δ^{-a}`.  So `habs` is not a hypothesis that only an
empty configuration can meet, and it is met at a threshold that never sees the outer accuracy. -/
example (n : ℕ) (K : NNReal) (K₀ : ℕ) {a α θ η : ℝ} (hα : 0 < α) (hbud : θ + (a + α) ≤ η) :
    ∃ d : NNReal, 0 < d ∧ d ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ d →
        ∀ {A : ENNReal}, A ≤ ENNReal.ofReal ((δ : ℝ) ^ (-a)) →
        ∀ m : ℕ, (m : ℝ) ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) →
          shadingBridgeLoss n A K (Nat.log 2 m) (Tube.ssfGridLen δ)
              * ENNReal.ofReal ((δ : ℝ) ^ η)
            ≤ (Tube.le_volume.c n : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ θ) := by
  obtain ⟨d, hd0, hd1, hd⟩ := exists_threshold_shadingBridgeLoss_le n K K₀ hα
  refine ⟨d, hd0, hd1, ?_⟩
  intro δ hδ0 hδle A hA m hm
  exact shadingBridge_absorb hδ0 (hδle.trans hd1) (hd hδ0 hδle hA m hm) hbud


end Kakeya.ML2Shading
