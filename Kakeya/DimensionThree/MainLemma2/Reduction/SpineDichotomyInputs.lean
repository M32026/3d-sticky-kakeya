/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Uniform
public import Kakeya.Tube.EssentiallyDistinctReduction
public import Kakeya.DimensionThree.MainLemma2.ShadedDividingScales
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEveryScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.Assembly

/-!
# Component G2a: the missing inputs of GWZ Lemma 7.7(B)

`Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao` and its one-sided companion
`Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao_dense` — GWZ Lemma 7.7(B) in shaded form —
carry three hypotheses that `Kakeya.ML2Assembly.Dichotomy`'s hypotheses do **not** supply:

1. `(𝕋 : Set ι).Pairwise IsEssentiallyDistinct` — a *geometric* condition on the retained tubes;
2. `Tube.UniformTubeSet 𝕋 T (Tube.ssfGridLen δ) C` — a uniform hierarchy on the grid of `δ`;
3. `4096 ≤ N`, the stopping-step threshold of `StickyKakeya.dividingScalesKatzTao`.

This file supplies all three, and prices them.  Nothing here touches a shading.

## The answers

* **`4096 ≤ N` is free.**  The `N` of 7.7(B) is the *stopping-step count*, not the grid length, and
  the parameter spine already commits to `N = Kakeya.ML2Spine.spineCount ϖ ε₁ = ⌈25/ε₂²⌉` with
  `ε₂ ≤ 1/64`, so `Kakeya.ML2Spine.four_thousand_le_spineCount` gives `N ≥ 4096` from `0 < ϖ` and
  `0 < ε₁` alone — both of which the `GeometricCore` context has (the window exponent of GWZ Lemma
  9.1, and the exponent `Kakeya.ML2Reduction.exists_everyScale_exponent` returns at the absolute
  accuracy).  Packaged as `Kakeya.ML2Inputs.exists_dividingScalesLadder`, which hands over the
  whole non-family hypothesis block of 7.7(B) — `4096 ≤ N`, `e = 1/√N`, `0 ≤ η 0`,
  `η k ≤ e η_{k+1}`, `η N ≤ e` — from `(β, ϖ, ε₁, gain, dens)` and nothing else.  So the answer to
  "can the `Dichotomy` context hand you an `IsSpine`?" is **yes**, and this is the theorem that
  does it.

* **`Pairwise IsEssentiallyDistinct` is not free, and banding is the wrong place to look for it.**
  Banding is a *mass* selection and says nothing about geometry.  What supplies it is
  `Kakeya.Tube.refineToEssDistinctLeaves`: **every** finite family of `δ`-tubes has a pairwise
  essentially distinct subfamily, at the cardinality loss `C_n · Δ_max(𝕋)`, and
  `Kakeya.ML2Assembly.Dichotomy`'s Katz--Tao hypothesis is *exactly* a bound on `Δ_max(𝕋)`
  (`Kakeya.IsKatzTao` unfolds to `Kakeya.maxDensity … ≤ …`).  So the loss the extra selection costs
  is the one the dichotomy's own hypothesis already pays for
  (`Kakeya.ML2Inputs.exists_essDistinct_subfamily` at `D = δ^{-θ}`, absorbed into `δ^{-(θ+α)}` by
  `Kakeya.ML2Inputs.exists_threshold_edLoss_le`).

* **The uniform hierarchy comes from the *tube-level* uniformization**,
  `Tube.exists_uniformTubeSet_subfamily_ssf`, not from
  `ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`.  That is not a stylistic preference: the
  tube-level version keeps the family `T` *literally the same function*, so essential distinctness
  and any pointwise datum about the shading — `Kakeya.ML2Shaded.HasDenseShading` in particular —
  restrict to the selected subfamily for free and at **zero** loss, and no shade refinement and no
  fullness loss are incurred before the dichotomy.  Inside the loop the dichotomy never looks at a
  shading, so the shaded uniformization belongs at the GWZ 7.3(B) leaf, not here.

## The order of the two selections is forced

Essential distinctness is chosen **first** and the uniformization **second**.

The reason is not convenience.  `Tube.UniformTubeSet` does **not** restrict to an arbitrary
subfamily: every field restricts except `Tube.UniformTubeSet.le_card_class`, which fails at every
node whose class the discard empties, and repairing it by flattening the branching count breaks
`Tube.UniformTubeSet.card_class_le` at any constant.  The proved obstruction in the tree is
`Kakeya.ML2Shaded.coverClass_nonempty_of_uniformTubeSet`.  So a hierarchy must be built on the
index set that is going to carry it, i.e. after every discard — which is also why
`Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao` puts its mass-banded subfamily `s''`
*outside* the hierarchy it returns.

Essential distinctness, by contrast, is hereditary (`Kakeya.ML2Inputs.pairwise_essDistinct_subset`),
so choosing it before the uniformization costs nothing.  The composite order
**ED → uniformize → 7.7(B)** therefore works, and the reverse does not even typecheck.

## The trap, and how it is avoided here

`Kakeya.Tube.refineToEssDistinctLeaves` is **blind to the shading**: it selects by geometry, so the
retained subfamily can be entirely unshaded while `#𝕋 ≤ C_n D #𝕋'` still holds, and then no bound
`∑_𝕋 |Y_i| ≤ L ∑_{𝕋'} |Y_i|` holds at any finite `L`
(`Kakeya.ML2Inputs.no_mass_share_of_essDistinct_refinement` is the refutation).  The
cardinality-to-mass conversion therefore needs a *pointwise* datum, and the cheapest one is the
one-sided `Kakeya.ML2Shaded.HasDenseShading`: `Kakeya.ML2Shaded.sum_shade_le_of_card_le` reads it on
the **retained** set, where the ED selection hands it over for free, and its constant carries no
comparability factor and no logarithm.
`Kakeya.ML2Inputs.sum_shade_le_of_essDistinct_refinement` is that conversion at the ED loss.

**Direction check of every hypothesis in this file.**  `hED` (pairwise), `hdense`
(`HasDenseShading`) and `hball` are pointwise and are consumed pointwise; `hD` (`maxDensity`),
`hcard` and the mass inequalities are aggregate and are consumed as aggregates.  No aggregate
quantity is read at a point, and no pointwise quantity is summed without a matching per-index
bound.

## What is here

* `pairwise_essDistinct_subset`, `pairwise_essDistinct_of_tube_eq` — heredity of the geometric
  hypothesis under the two operations the pipeline performs.
* `exists_dividingScalesLadder` — the `(N, e, η)` block of 7.7(B), `4096 ≤ N` included.
* `spineNu_le_div_48000` — `ν ≤ β/48000`, the quantitative statement that the loss charged below is
  affordable against the absolute accuracy `β/2` (a fact three docstrings assert; here proved).
* `edLoss`, `exists_essDistinct_subfamily`, `exists_threshold_edLoss_le` — the geometric hypothesis,
  produced, with its loss and the threshold that absorbs it.
* `sum_shade_le_of_essDistinct_refinement`, `no_mass_share_of_essDistinct_refinement` — the mass
  side of the ED discard, and the refutation of doing it with no pointwise datum.
* `exists_dividingScalesInputs` — **the input package**, on unshaded tubes: from exactly
  `Kakeya.ML2Assembly.Dichotomy`'s Katz--Tao and containment hypotheses plus the crude cardinality
  bound, a subfamily carrying essential distinctness, the same density bound and a uniform
  hierarchy, at the single cardinality loss `δ^{-(θ+α)}`.
* `exists_shaded_dividingScales_of_dichotomyHypotheses` — **the capstone**: GWZ Lemma 7.7(B) in its
  one-sided shaded form actually run on the `Dichotomy` context, with the essential-distinctness
  hypothesis, the uniformity hypothesis and the `4096 ≤ N` side condition all gone from the
  statement, and with alternative (i) already absorbed to `δ^{-ε₁}`.
* `DividingScalesOutput` — the output of the capstone, named once so that its threshold form and
  its `∀ᶠ δ` form state the same thing.
* `eventually_dividingScalesInputs_dim3` and `eventually_shaded_dividingScales_dim3` — the package
  and the capstone in the `∀ᶠ δ` form of `Dichotomy`, with the crude cardinality bound discharged
  from the dichotomy's own hypotheses by `Kakeya.ML2Assembly.card_le_rpow_neg_four` (its `η ≤ 1`
  side condition met by `spineNu_le_div_48000`), so that hypothesis is not a new demand either.
  `eventually_shaded_dividingScales_dim3` is the theorem the assembly of the first disjunct calls.
* `maxDensity_le_of_card_le` — with `Kakeya.ML2Shaded.exists_fullShading_of_tubes`, the consistency
  of the whole hypothesis set.

## `ε`-discipline

No statement in this file has an `ε` binder.  The only exponents are `β`, the window exponent `ϖ`,
the Katz--Tao exponent `ε₁` of Theorem 7.3(B) read at an absolute accuracy, the spine's own
`ε₂, e, (η_k)`, and the free absorption budget `α > 0`.  Nothing here can reintroduce a dependence
of `ν` on the outer accuracy; `Kakeya.ML2Spine.not_epsFree_of_outerAccuracy` is untouched.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ShadedBody ConvexSpaceBody
open Tube ShadedTube

universe u

namespace Kakeya.ML2Inputs

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-! ### Heredity of the geometric hypothesis -/

omit [Nontrivial E] in
/-- **Essential distinctness is hereditary.**  Any selection step — mass banding included — that
returns a *subfamily* preserves it, so the question "can the banding be made to preserve pairwise
essential distinctness?" is answered by this one line: it cannot destroy it.

Stated for an arbitrary carrier map `f`, so that it applies verbatim to `fun i => (T i).carrier`
and to `fun i => (V i).carrier` for a shaded family, with no coercion dance. -/
theorem pairwise_essDistinct_subset {s u : Finset ι} (hsub : u ⊆ s) {f : ι → Set E}
    (hED : (s : Set ι).Pairwise fun i j => IsEssentiallyDistinct (f i) (f j)) :
    (u : Set ι).Pairwise fun i j => IsEssentiallyDistinct (f i) (f j) :=
  hED.mono (Finset.coe_subset.mpr hsub)

omit [Nontrivial E] in
/-- **Essential distinctness does not see the shading.**  Every shade-refinement step keeps the
tubes and shrinks only the shadings, so the geometric hypothesis transports for free across the
shaded uniformization at the GWZ 7.3(B) leaf. -/
theorem pairwise_essDistinct_of_tube_eq {δ : NNReal} {s : Finset ι} {V V' : ι → ShadedTube δ E}
    (htube : ∀ i, (V' i).toTube = (V i).toTube)
    (hED : (s : Set ι).Pairwise fun i j =>
      IsEssentiallyDistinct ((V i).carrier) ((V j).carrier)) :
    (s : Set ι).Pairwise fun i j =>
      IsEssentiallyDistinct ((V' i).carrier) ((V' j).carrier) := by
  intro i hi j hj hne
  have hi' : (V' i).carrier = (V i).carrier := by
    show (V' i).toTube.carrier = (V i).toTube.carrier
    rw [htube i]
  have hj' : (V' j).carrier = (V j).carrier := by
    show (V' j).toTube.carrier = (V j).toTube.carrier
    rw [htube j]
  rw [hi', hj']
  exact hED hi hj hne

/-! ### The `4096 ≤ N` side condition -/

/-- **`4096 ≤ N` at the spine's own stopping-step count.**  `Kakeya.ML2Spine.spineEps₂` is capped at
`1/64`, so `⌈25/ε₂²⌉ ≥ 102400`.  Nothing beyond positivity of `ϖ` and `ε₁` is used. -/
theorem four_thousand_le_spineCount {ϖ ε₁ : ℝ} (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁) :
    4096 ≤ ML2Spine.spineCount ϖ ε₁ :=
  ML2Spine.four_thousand_le_spineCount hϖ hε₁

/-- **`ν ≤ β/48000`.**

Three docstrings in the reduction assert this ("In fact `ν ≤ β/48000`") and none proves it;
`Kakeya.ML2Spine.two_spineNu_le` proves only `2ν ≤ β`.  It matters here, and quantitatively: the
essential-distinctness selection below charges `δ^{-ν}` on the way to alternative (i) of the
dichotomy, whose budget is the absolute accuracy `Kakeya.ML2Spine.absAccuracy β = β/2`.  With
`2ν ≤ β` alone the charge would consume the entire budget and the composition would be tight to the
point of failing; with `ν ≤ β/48000` all but `1/24000` of the budget is left for the ED loss, the
uniformization loss and the free `α`.

The proof is the one already inside `Kakeya.ML2Spine.two_spineNu_le`, stopped one step earlier:
`ν ≤ η₁ ≤ e² β e/48` and `e ≤ 1/10`, so `ν ≤ β/(1000 · 48)`. -/
theorem spineNu_le_div_48000 {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    ML2Spine.spineNu β ϖ ε₁ gain dens ≤ β / 48000 := by
  have he : 0 < ML2Spine.spineDiv ϖ ε₁ := ML2Spine.spineDiv_pos hϖ hε₁
  have he10 : ML2Spine.spineDiv ϖ ε₁ ≤ 1 / 10 := ML2Spine.spineDiv_le_one hϖ hε₁
  have hanti : Antitone (ML2Spine.spineAux β ϖ ε₁ gain dens) :=
    ML2Spine.spineAux_antitone hβ hβ1 hϖ hε₁ hgain hdens
  have hN : 1 ≤ ML2Spine.spineCount ϖ ε₁ := ML2Spine.one_le_spineCount hϖ hε₁
  have hstep : ML2Spine.spineNu β ϖ ε₁ gain dens ≤ ML2Spine.spineAux β ϖ ε₁ gain dens 1 := by
    unfold ML2Spine.spineNu ML2Spine.spineRung
    rw [Nat.sub_zero]
    exact hanti hN
  have hone : ML2Spine.spineAux β ϖ ε₁ gain dens 1
      ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2 * β * ML2Spine.spineDiv ϖ ε₁ / 48 := by
    rw [ML2Spine.spineAux, ML2Spine.spineAux]
    exact ML2Spine.spineStep_le_div_48 hβ he.le
  have he2 : ML2Spine.spineDiv ϖ ε₁ ^ 2 ≤ 1 / 100 := by nlinarith [he.le, he10]
  have hcube : ML2Spine.spineDiv ϖ ε₁ ^ 2 * ML2Spine.spineDiv ϖ ε₁ ≤ 1 / 1000 := by
    nlinarith [he2, he.le, he10, sq_nonneg (ML2Spine.spineDiv ϖ ε₁)]
  have hfin : ML2Spine.spineDiv ϖ ε₁ ^ 2 * β * ML2Spine.spineDiv ϖ ε₁ / 48 ≤ β / 48000 := by
    nlinarith [hcube, hβ.le,
      mul_nonneg (by linarith :
        (0 : ℝ) ≤ 1 / 1000 - ML2Spine.spineDiv ϖ ε₁ ^ 2 * ML2Spine.spineDiv ϖ ε₁) hβ.le]
  linarith [hstep, hone, hfin]

/-- **The whole non-family hypothesis block of GWZ Lemma 7.7(B), supplied.**

`Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao` asks for `N` with `4096 ≤ N`, an
`ε = 1/√N`, and a ladder `η : ℕ → ℝ` with `0 ≤ η 0`, `η k ≤ ε η_{k+1}` for `k < N` and `η N ≤ ε`.
All five come from the parameter spine, and the bottom rung is the gain `ν` of Main Lemma 2 — so
the density level at which the dichotomy is read is exactly the one
`Kakeya.ML2Assembly.GeometricCore` gets to choose.  The last three conjuncts are the `ε₂` data that
`Kakeya.ML2Reduction.exists_threshold_katzTaoError_le` spends to absorb alternative (i) to
`δ^{-ε₁}`.

There is no `ε` binder: the whole block is a function of `(β, ϖ, ε₁, gain, dens)`. -/
theorem exists_dividingScalesLadder {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    ∃ (ε₂ e : ℝ) (N : ℕ) (η : ℕ → ℝ),
      ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η ∧
        4096 ≤ N ∧ e = 1 / Real.sqrt (N : ℝ) ∧
        η 0 = ML2Spine.spineNu β ϖ ε₁ gain dens ∧
        0 ≤ η 0 ∧ (∀ k < N, η k ≤ e * η (k + 1)) ∧ η N ≤ e ∧
        0 < ε₂ ∧ 5 * e ≤ ε₂ ∧ ε₂ ≤ ε₁ / 5 := by
  refine ⟨ML2Spine.spineEps₂ ϖ ε₁, ML2Spine.spineDiv ϖ ε₁, ML2Spine.spineCount ϖ ε₁,
    ML2Spine.spineRung β ϖ ε₁ gain dens, ?_⟩
  have hspine := ML2Spine.spineRung_isSpine hβ hβ1 hϖ hε₁ hgain hdens
  refine ⟨hspine, hspine.four_thousand_le_stepCount, hspine.div_eq, rfl,
    (hspine.rung_pos 0).le,
    fun k hk => ML2Reduction.rung_le_div_mul_rung_succ hspine hβ hβ1 hk,
    le_of_eq hspine.rung_top, hspine.eps₂_pos, ?_, hspine.eps₂_le_everyScale⟩
  have := hspine.div_le
  linarith

/-! ### The essential-distinctness hypothesis, produced -/

/-- **The loss of the essential-distinctness selection**: `C_n · D`, where `D` bounds the maximal
density of the family and `C_n = Tube.refineToEssDistinctLeaves.C n` is dimensional.  Under
`Kakeya.ML2Assembly.Dichotomy`'s own Katz--Tao hypothesis `D = δ^{-η}`, so the selection is paid
for by a hypothesis the dichotomy already has. -/
noncomputable def edLoss (n : ℕ) (D : ENNReal) : ENNReal :=
  Tube.refineToEssDistinctLeaves.C n * D

/-- **The geometric hypothesis of GWZ Lemma 7.7(B), supplied for every family.**

`Kakeya.Tube.refineToEssDistinctLeaves`, restated at the loss `Kakeya.ML2Inputs.edLoss`.  Nothing
is assumed about the family beyond the Katz--Tao bound that `Kakeya.ML2Assembly.Dichotomy` supplies:
`Kakeya.IsKatzTao s W C` **is** `Kakeya.maxDensity s W ≤ C` by definition, so `hD` is that
hypothesis verbatim.  No shading appears. -/
theorem exists_essDistinct_subfamily {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (s : Finset ι) (T : ι → Tube δ E) {D : ENNReal}
    (hD : Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody) ≤ D) :
    ∃ u ⊆ s,
      (u : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) ∧
        (s.card : ENNReal) ≤ edLoss (Module.finrank ℝ E) D * (u.card : ENNReal) := by
  obtain ⟨u, hus, hED, hcard⟩ := Tube.refineToEssDistinctLeaves hδ0 hδ1 s T hD
  refine ⟨u, hus, hED, ?_⟩
  unfold edLoss
  exact hcard

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The essential-distinctness loss is absorbed by any positive budget above the density level.**

`C_n · δ^{-θ} ≤ δ^{-(θ+α)}` below a threshold depending only on `α` and the dimension — in
particular not on the scale and not on the family, which is what the assembly needs. -/
theorem exists_threshold_edLoss_le {θ α : ℝ} (hα : 0 < α) :
    ∃ d : NNReal, 0 < d ∧ d ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ d →
        edLoss (Module.finrank ℝ E) (ENNReal.ofReal ((δ : ℝ) ^ (-θ)))
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(θ + α))) := by
  obtain ⟨d, hd0, hd1, h⟩ :=
    ML2Shaded.exists_threshold_const_le_rpow_neg' (StickyKakeya.edRefineC (E := E)) hα
  refine ⟨d, hd0, hd1, ?_⟩
  intro δ hδ0 hδd
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hC : Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E)
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-α)) := by
    rw [← StickyKakeya.ofReal_edRefineC (E := E)]
    exact ENNReal.ofReal_le_ofReal (h hδ0 hδd)
  calc edLoss (Module.finrank ℝ E) (ENNReal.ofReal ((δ : ℝ) ^ (-θ)))
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-α)) * ENNReal.ofReal ((δ : ℝ) ^ (-θ)) :=
        mul_le_mul' hC le_rfl
    _ = ENNReal.ofReal ((δ : ℝ) ^ (-α) * (δ : ℝ) ^ (-θ)) :=
        (ENNReal.ofReal_mul (Real.rpow_nonneg hδR.le _)).symm
    _ = ENNReal.ofReal ((δ : ℝ) ^ (-(θ + α))) := by
        rw [← Real.rpow_add hδR]; ring_nf

/-! ### The mass side of the essential-distinctness discard -/

/-- **The essential-distinctness discard, priced on the shaded mass.**

`Kakeya.Tube.refineToEssDistinctLeaves` is blind to the shading, so its conclusion is a share of
the *indices* only.  Turning that into a share of the shaded *mass* needs a pointwise datum, and
the cheapest is the one-sided `Kakeya.ML2Shaded.HasDenseShading`, read on the **retained** set — the
one the ED selection hands over for free by heredity
(`Kakeya.ML2Shaded.HasDenseShading.subset`).  The constant is
`edLoss · C_n / (lam · c_n)`: no comparability constant and no logarithm.

This is `Kakeya.ML2Shaded.sum_shade_le_of_card_le` at the ED loss; nothing new is proved, and that
is the point — the conversion has a single owner. -/
theorem sum_shade_le_of_essDistinct_refinement {δ : NNReal} (hδ1 : δ ≤ 1)
    {s u : Finset ι} {V : ι → ShadedTube δ E} {lam : NNReal}
    (hdense : ML2Shaded.HasDenseShading lam u (fun i => (V i).toShadedBody))
    {D : ENNReal}
    (hcard : (s.card : ENNReal) ≤ edLoss (Module.finrank ℝ E) D * (u.card : ENNReal)) :
    (lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
        * (∑ i ∈ s, volume (V i).shade)
      ≤ edLoss (Module.finrank ℝ E) D * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
          * ∑ i ∈ u, volume (V i).shade :=
  ML2Shaded.sum_shade_le_of_card_le hδ1 hdense hcard

omit [Nontrivial E] in
/-- **Without a pointwise datum there is no mass share at any loss.**

The refutation of the cardinality-only reading of the previous lemma, in the house pattern.  On a
two-element family whose first tube is fully shaded and whose second is unshaded, the subfamily
`u = {i₂}` retains half the indices — so `#s ≤ 2 · #u` — and *none* of the mass.  Hence

  `∑_{i ∈ s} |Y_i| ≤ L · ∑_{i ∈ u} |Y_i|`

is false for **every** `L : ENNReal`, `L = ⊤` included, since the right-hand side is `0`.  So
`Kakeya.ML2Inputs.sum_shade_le_of_essDistinct_refinement` cannot drop `hdense`, and the ED
selection is subject to the same trap as 7.7(B)'s own retention. -/
theorem no_mass_share_of_essDistinct_refinement [DecidableEq ι] {δ : NNReal} {i₁ i₂ : ι}
    (hne : i₁ ≠ i₂) (V : ι → ShadedTube δ E)
    (hV₁ : volume (V i₁).shade ≠ 0) (hV₂ : volume (V i₂).shade = 0) :
    ∀ L : ENNReal, ¬ (∑ i ∈ ({i₁, i₂} : Finset ι), volume (V i).shade
      ≤ L * ∑ i ∈ ({i₂} : Finset ι), volume (V i).shade) := by
  intro L hL
  rw [Finset.sum_pair hne, Finset.sum_singleton, hV₂, mul_zero, add_zero] at hL
  exact hV₁ (le_antisymm hL (by simp))

/-! ### The input package -/

/-- **The two geometric inputs of GWZ Lemma 7.7(B), on one subfamily, from
`Kakeya.ML2Assembly.Dichotomy`'s own hypotheses.**

Given a family of `δ`-tubes in `B_1` whose maximal density is at most `δ^{-θ}` and whose cardinality
is at most `δ^{-K₀}`, there is a subfamily `u` carrying

* **`hball`** — containment in `B_1`, inherited;
* **`hED`** — pairwise essential distinctness, *produced*;
* **`hDens`** — the same density bound `δ^{-θ}`, since `Kakeya.maxDensity` is monotone in the index
  set;
* **`hU`** — a `Tube.UniformTubeSet` on the grid `Tube.ssfGridLen δ`;

at the single cardinality loss `δ^{-(θ+α)}` for **any** positive budget `α`, below a threshold fixed
before the scale and before the family.

**No shading appears anywhere in this statement.**  That is deliberate and it is what makes the
package cheap: both selections are subfamily selections that keep the tube map `T` *literally the
same function*, so any pointwise datum about a shading of these tubes — `HasDenseShading`,
`HasComparableDensities`, fullness read pointwise — restricts to `u` for free, and no shade
refinement, no fullness loss and no polylogarithm are incurred before the dichotomy. -/
theorem exists_dividingScalesInputs (K₀ : ℕ) (θ : ℝ) {α : ℝ} (hα : 0 < α) :
    ∃ d : NNReal, 0 < d ∧ d ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ d →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)
            ≤ ENNReal.ofReal ((δ : ℝ) ^ (-θ)) →
        (s.card : ℝ) ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) →
        ∃ u ⊆ s,
          (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (u : Set ι).Pairwise
            (fun i j => IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) ∧
          Kakeya.maxDensity u (fun i => (T i).toConvexSpaceBody)
              ≤ ENNReal.ofReal ((δ : ℝ) ^ (-θ)) ∧
          Nonempty (UniformTubeSet u T (ssfGridLen δ) (uniformConst (Module.finrank ℝ E))) ∧
          (s.card : ENNReal)
              ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(θ + α))) * (u.card : ENNReal) := by
  classical
  obtain ⟨d₁, hd₁0, hd₁1, hd₁⟩ :=
    exists_threshold_edLoss_le (E := E) (θ := θ) (α := α / 2) (by linarith)
  obtain ⟨d₂, hd₂0, hd₂1, hd₂⟩ :=
    Tube.exists_uniformTubeSet_subfamily_ssf.{u} (E := E) K₀ (α / 2) (by linarith)
  refine ⟨min d₁ d₂, lt_min hd₁0 hd₂0, (min_le_left _ _).trans hd₁1, ?_⟩
  intro ι δ hδ0 hδd s T hball hD hcardK
  have hδ1 : δ ≤ 1 := hδd.trans ((min_le_left _ _).trans hd₁1)
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  -- Step 1: the geometric selection.
  obtain ⟨u₀, hu₀s, hED₀, hcard₀⟩ := exists_essDistinct_subfamily hδ0 hδ1 s T hD
  -- Step 2: the tube-level uniformization, on the essentially distinct subfamily.
  have hballu₀ : ∀ i ∈ u₀, (T i).carrier ⊆ Metric.closedBall (0 : E) 1 :=
    fun i hi => hball i (hu₀s hi)
  have hcardu₀ : (u₀.card : ℝ) ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) :=
    le_trans (by exact_mod_cast Finset.card_le_card hu₀s) hcardK
  obtain ⟨u, huu₀, hcardu, hstruct⟩ :=
    hd₂ hδ0 (hδd.trans (min_le_right _ _)) u₀ T hballu₀ hcardu₀
  have hus : u ⊆ s := huu₀.trans hu₀s
  refine ⟨u, hus, fun i hi => hball i (hus hi),
    pairwise_essDistinct_subset (E := E) huu₀ hED₀,
    le_trans (Kakeya.maxDensity_mono (fun i => (T i).toConvexSpaceBody) hus) hD, hstruct, ?_⟩
  -- the two cardinality losses compose
  have hED' : (s.card : ENNReal)
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(θ + α / 2))) * (u₀.card : ENNReal) :=
    hcard₀.trans (mul_le_mul' (hd₁ hδ0 (hδd.trans (min_le_left _ _))) le_rfl)
  have hUn : (u₀.card : ENNReal)
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(α / 2))) * (u.card : ENNReal) := by
    have h1 : ENNReal.ofReal ((u₀.card : ℝ))
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(α / 2)) * (u.card : ℝ)) :=
      ENNReal.ofReal_le_ofReal hcardu
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hδR.le _)] at h1
    simpa using h1
  calc (s.card : ENNReal)
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(θ + α / 2))) * (u₀.card : ENNReal) := hED'
    _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(θ + α / 2)))
          * (ENNReal.ofReal ((δ : ℝ) ^ (-(α / 2))) * (u.card : ENNReal)) :=
        mul_le_mul' le_rfl hUn
    _ = (ENNReal.ofReal ((δ : ℝ) ^ (-(θ + α / 2)))
          * ENNReal.ofReal ((δ : ℝ) ^ (-(α / 2)))) * (u.card : ENNReal) := by ring
    _ = ENNReal.ofReal ((δ : ℝ) ^ (-(θ + α))) * (u.card : ENNReal) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδR.le _), ← Real.rpow_add hδR]
        ring_nf

/-! ### The capstone: GWZ Lemma 7.7(B) run on the dichotomy's context -/

/-- **The output of GWZ Lemma 7.7(B) as this file delivers it**, named so that the threshold form
and the `∀ᶠ δ` form of the capstone state the same thing and a consumer can `unfold` once.

Read the clauses in order: the two nested subfamilies `u' ⊆ u ⊆ 𝕋` produced by the input package and
by the dichotomy; the refined shading `Y'` on the same tubes; nonemptiness; the **single**
cardinality loss `δ^{-(η₀+α)} · totalLoss`; the shaded-uniformization mass loss; the density
invariant `HasDenseShading lam` and its consequence `HasComparableDensities lam⁻¹`, both on `u'` and
both for the *original* shading `Y`; the fullness of the refined shading, which is what
`Kakeya.ML2Reduction.exists_everyScale_multiplicity_le` consumes; and the dichotomy itself, with
alternative (i) already at `δ^{-ε₁}`.

Every clause is one of `Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao_dense`'s, except that
the cardinality loss also carries the price of the two selections this file performs and that
alternative (i) has been absorbed. -/
def DividingScalesOutput {ι : Type*} {δ : NNReal} (C : NNReal) (Kl cl : ℕ) (ε₁ α : ℝ)
    (e : ℝ) (N : ℕ) (η : ℕ → ℝ) (s : Finset ι) (V : ι → ShadedTube δ E) (lam : NNReal) : Prop :=
  ∃ u ⊆ s, ∃ u' ⊆ u, ∃ W : ι → ShadedTube δ E,
    u'.Nonempty ∧
    (∀ i, (W i).toTube = (V i).toTube) ∧
    (∀ i, (W i).shade ⊆ (V i).shade) ∧
    (s.card : ENNReal)
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + α)))
          * StickyKakeya.totalLoss C Kl cl δ * (u'.card : ENNReal) ∧
    (∑ i ∈ u', volume (V i).shade)
        ≤ ((Nat.log 2 u.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
          * ∑ i ∈ u', volume (W i).shade ∧
    ML2Shaded.HasDenseShading lam u' (fun i => (V i).toShadedBody) ∧
    ML2Shaded.HasComparableDensities lam⁻¹ u' (fun i => (V i).toShadedBody) ∧
    (lam : ENNReal)
        ≤ ((Nat.log 2 u.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
          * ShadedBody.fullness' u' (fun i => (W i).toShadedBody) ∧
    ∃ 𝒲 : ShadedUniformTubeSet u' W (ssfGridLen δ) (max C 4),
      (𝒲.tubeUniform.IsKatzTaoAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-ε₁)))
        ∨ ∃ a b m : ℕ, ML2Reduction.IsKatzTaoDividingWindow 𝒲.tubeUniform
            ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) η e N a b m)

/-- **`DividingScalesOutput` with the window read as `IsKatzTaoDividingWindowLevels`.**  Same
clauses, same losses; only the bundled window carries the two extra fields of
`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels`.  The producers below return this; the existing
consumers of `DividingScalesOutput` read it through
`DividingScalesOutputLevels.toDividingScalesOutput`. -/
def DividingScalesOutputLevels {ι : Type*} {δ : NNReal} (C : NNReal) (Kl cl : ℕ) (ε₁ α : ℝ)
    (e : ℝ) (N : ℕ) (η : ℕ → ℝ) (s : Finset ι) (V : ι → ShadedTube δ E) (lam : NNReal) : Prop :=
  ∃ u ⊆ s, ∃ u' ⊆ u, ∃ W : ι → ShadedTube δ E,
    u'.Nonempty ∧
    (∀ i, (W i).toTube = (V i).toTube) ∧
    (∀ i, (W i).shade ⊆ (V i).shade) ∧
    (s.card : ENNReal)
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + α)))
          * StickyKakeya.totalLoss C Kl cl δ * (u'.card : ENNReal) ∧
    (∑ i ∈ u', volume (V i).shade)
        ≤ ((Nat.log 2 u.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
          * ∑ i ∈ u', volume (W i).shade ∧
    ML2Shaded.HasDenseShading lam u' (fun i => (V i).toShadedBody) ∧
    ML2Shaded.HasComparableDensities lam⁻¹ u' (fun i => (V i).toShadedBody) ∧
    (lam : ENNReal)
        ≤ ((Nat.log 2 u.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
          * ShadedBody.fullness' u' (fun i => (W i).toShadedBody) ∧
    ∃ 𝒲 : ShadedUniformTubeSet u' W (ssfGridLen δ) (max C 4),
      (𝒲.tubeUniform.IsKatzTaoAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-ε₁)))
        ∨ ∃ a b m : ℕ, ML2Reduction.IsKatzTaoDividingWindowLevels 𝒲.tubeUniform
            ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) η e N a b m)

omit [Nontrivial E] in
/-- The twin projects onto the existing output: drop the two extra window fields. -/
theorem DividingScalesOutputLevels.toDividingScalesOutput {ι : Type*} {δ : NNReal} {C : NNReal}
    {Kl cl : ℕ} {ε₁ α e : ℝ} {N : ℕ} {η : ℕ → ℝ} {s : Finset ι} {V : ι → ShadedTube δ E}
    {lam : NNReal} (h : DividingScalesOutputLevels C Kl cl ε₁ α e N η s V lam) :
    DividingScalesOutput C Kl cl ε₁ α e N η s V lam := by
  obtain ⟨u, hus, u', hu'u, W, hu'ne, htube, hshade, hcard, hmass, hdense, hcomp, hfull, 𝒲,
    halt⟩ := h
  refine ⟨u, hus, u', hu'u, W, hu'ne, htube, hshade, hcard, hmass, hdense, hcomp, hfull, 𝒲, ?_⟩
  rcases halt with hKT | ⟨a, b, m, hw⟩
  · exact Or.inl hKT
  · exact Or.inr ⟨a, b, m, hw.toIsKatzTaoDividingWindow⟩

/-- **GWZ Lemma 7.7(B) in its one-sided shaded form, returning the level twin.**
`exists_shaded_dividingScales_of_dichotomyHypotheses` with the conclusion
`DividingScalesOutputLevels`: the bundled window is
`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels`,
carrying the source's multiplicity-free level clause and the two-level density band that
`Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao_dense` now returns.  The existing statement is
the corollary below, through `DividingScalesOutputLevels.toDividingScalesOutput`; its proof is the
one that used to sit here, verbatim. -/
theorem exists_shaded_dividingScales_of_dichotomyHypotheses_levels
    (hn : Module.finrank ℝ E = 3) (K₀ : ℕ)
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {α : ℝ} (hα : 0 < α) :
    ∃ (C d : NNReal) (Kl cl : ℕ) (ε₂ e : ℝ) (N : ℕ) (η : ℕ → ℝ),
      1 ≤ C ∧ 0 < d ∧ d ≤ 1 ∧ 4096 ≤ N ∧ e = 1 / Real.sqrt (N : ℝ) ∧
      η 0 = ML2Spine.spineNu β ϖ ε₁ gain dens ∧
      ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ d →
      ∀ (s : Finset ι) (V : ι → ShadedTube δ E), s.Nonempty →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody)
            ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0))) →
        (s.card : ℝ) ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) →
        ∀ lam : NNReal, 0 < lam →
        ML2Shaded.HasDenseShading lam s (fun i => (V i).toShadedBody) →
        DividingScalesOutputLevels C Kl cl ε₁ α e N η s V lam := by
  classical
  obtain ⟨ε₂, e, N, η, hspine, hN, he, hη0nu, hη0, hηstep, hηN, hε₂0, h5e, hε₂₁⟩ :=
    exists_dividingScalesLadder hβ hβ1 hϖ hε₁ hgain hdens
  obtain ⟨C, δ₀, Kl, cl, hC, hδ₀0, hδ₀1, hmain⟩ :=
    ML2Shaded.exists_shaded_dividingScalesKatzTao_dense.{u} (E := E) hn N hN he
      (uniformConst (Module.finrank ℝ E))
  have h5e₁ : 5 * e ≤ ε₁ / 5 := by linarith
  obtain ⟨δ₁, hδ₁0, hδ₁1, habs⟩ :=
    ML2Reduction.exists_threshold_katzTaoError_le C hC Kl cl hε₁ h5e₁
  obtain ⟨δ₂, hδ₂0, hδ₂1, hinputs⟩ :=
    exists_dividingScalesInputs.{u} (E := E) K₀ (η 0) hα
  refine ⟨C, min (min δ₀ δ₁) δ₂, Kl, cl, ε₂, e, N, η, hC,
    lt_min (lt_min hδ₀0 hδ₁0) hδ₂0, ((min_le_left _ _).trans (min_le_left _ _)).trans hδ₀1,
    hN, he, hη0nu, hspine, ?_⟩
  intro ι δ hδ0 hδd s V hsne hball hD hcardK lam hlam hdense
  have hδδ₀ : δ ≤ δ₀ := hδd.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδδ₁ : δ ≤ δ₁ := hδd.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδδ₂ : δ ≤ δ₂ := hδd.trans (min_le_right _ _)
  -- the input package, on the underlying tubes
  have hball' : ∀ i ∈ s, ((V i).toTube).carrier ⊆ Metric.closedBall (0 : E) 1 := hball
  have hD' : Kakeya.maxDensity s (fun i => ((V i).toTube).toConvexSpaceBody)
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0))) :=
    le_trans (le_of_eq (Kakeya.maxDensity_congr (fun i _ => rfl))) hD
  obtain ⟨u, hus, hballu, hED, hDens, hstruct, hcard1⟩ :=
    hinputs hδ0 hδδ₂ s (fun i => (V i).toTube) hball' hD' hcardK
  have hune : u.Nonempty := ML2Shaded.nonempty_of_card_le_mul hsne hcard1
  have hballu' : ∀ i ∈ u, (V i).carrier ⊆ Metric.closedBall (0 : E) 1 := hballu
  have hED' : (u : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct ((V i).carrier) ((V j).carrier)) := by
    intro i hi j hj hne
    exact hED hi hj hne
  have hDens' : Kakeya.maxDensity u (fun i => (V i).toConvexSpaceBody)
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0))) :=
    le_trans (le_of_eq (Kakeya.maxDensity_congr (fun i _ => rfl))) hDens
  -- GWZ 7.7(B), one-sided form, on the package
  obtain ⟨u', hu'u, W, hu'ne, htube, hshade, hcard2, hmass, hdense', hcomp', hfull, -,
      𝒲, halt⟩ :=
    hmain (ι := ι) (δ := δ) hδ0 hδδ₀ η hη0 hηstep hηN u V hune hballu' hED' hstruct.some hDens'
      lam hlam (hdense.subset hus)
  refine ⟨u, hus, u', hu'u, W, hu'ne, htube, hshade, ?_, hmass, hdense', hcomp', hfull,
    𝒲, ?_⟩
  · calc (s.card : ENNReal)
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + α))) * (u.card : ENNReal) := hcard1
      _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + α)))
            * (StickyKakeya.totalLoss C Kl cl δ * (u'.card : ENNReal)) :=
          mul_le_mul' le_rfl hcard2
      _ = ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + α)))
            * StickyKakeya.totalLoss C Kl cl δ * (u'.card : ENNReal) := by ring
  · rcases halt with hKT | ⟨a, b, m, hm, hab, hb, hsep, h1, h2, h3, hlev, hband⟩
    · exact Or.inl (hKT.mono (habs hδ0 hδδ₁))
    · exact Or.inr ⟨a, b, m, ⟨⟨hm, hab, hb, hsep, h1, h2, h3⟩, hlev, hband⟩⟩

/-- **GWZ Lemma 7.7(B) in its one-sided shaded form, with all three missing inputs discharged.**

`Kakeya.ML2Shaded.exists_shaded_dividingScalesKatzTao_dense` composed with
`Kakeya.ML2Inputs.exists_dividingScalesInputs` and
`Kakeya.ML2Inputs.exists_dividingScalesLadder`.  The hypotheses on the family are now exactly

* nonemptiness and containment in `B_1`,
* `Δ_max(𝕋) ≤ δ^{-η₀}` at the spine's bottom rung `η₀ = ν`,
* the crude cardinality bound `|𝕋| ≤ δ^{-K₀}` (itself derivable — see
  `Kakeya.ML2Inputs.eventually_dividingScalesInputs_dim3`), and
* the pointwise density invariant `HasDenseShading lam 𝕋 Y`;

**no essential distinctness, no uniform hierarchy, and no `4096 ≤ N`.**  Alternative (i) is already
absorbed to `δ^{-ε₁}`, so `Kakeya.ML2Reduction.exists_everyScale_multiplicity_le` (GWZ Theorem
7.3(B)) applies to it directly, and alternative (ii) is packaged as
`Kakeya.ML2Reduction.IsKatzTaoDividingWindow` on the returned hierarchy.

`HasDenseShading lam 𝕋 Y` survives both selections at **zero** loss, so it comes out on `u'` as
well — which is why it, and not two-sided comparability, is the right invariant to carry through
the loop.

The chain of losses back to `𝕋` is `δ^{-(ν+α)}` for the two selections of the input package and
`StickyKakeya.totalLoss` for 7.7(B), both subpolynomial;
`Kakeya.ML2Inputs.spineNu_le_div_48000` is what says the first one, the only one carrying a genuine
`δ`-power, fits inside the absolute accuracy `β/2` with room to spare.

`ε₁` is a parameter, to be instantiated at the exponent
`Kakeya.ML2Reduction.exists_everyScale_exponent` returns at the absolute accuracy
`Kakeya.ML2Spine.absAccuracy β = β/2`.  There is no `ε` binder. -/
theorem exists_shaded_dividingScales_of_dichotomyHypotheses
    (hn : Module.finrank ℝ E = 3) (K₀ : ℕ)
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {α : ℝ} (hα : 0 < α) :
    ∃ (C d : NNReal) (Kl cl : ℕ) (ε₂ e : ℝ) (N : ℕ) (η : ℕ → ℝ),
      1 ≤ C ∧ 0 < d ∧ d ≤ 1 ∧ 4096 ≤ N ∧ e = 1 / Real.sqrt (N : ℝ) ∧
      η 0 = ML2Spine.spineNu β ϖ ε₁ gain dens ∧
      ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ d →
      ∀ (s : Finset ι) (V : ι → ShadedTube δ E), s.Nonempty →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody)
            ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0))) →
        (s.card : ℝ) ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) →
        ∀ lam : NNReal, 0 < lam →
        ML2Shaded.HasDenseShading lam s (fun i => (V i).toShadedBody) →
        DividingScalesOutput C Kl cl ε₁ α e N η s V lam := by
  obtain ⟨C, d, Kl, cl, ε₂, e, N, η, hC, hd0, hd1, hN, he, hη0nu, hspine, hmain⟩ :=
    exists_shaded_dividingScales_of_dichotomyHypotheses_levels.{u} hn K₀ hβ hβ1 hϖ hε₁ hgain
      hdens hα
  exact ⟨C, d, Kl, cl, ε₂, e, N, η, hC, hd0, hd1, hN, he, hη0nu, hspine,
    fun hδ0 hδd s V hsne hball hKT hcard lam hlam hdense =>
      (hmain hδ0 hδd s V hsne hball hKT hcard lam hlam hdense).toDividingScalesOutput⟩


/-! ### Non-vacuity, and the cardinality hypothesis is not a new demand -/

/-- **The ladder exists unconditionally.**  Every hypothesis of
`Kakeya.ML2Inputs.exists_dividingScalesLadder` is discharged at concrete data, so the `4096 ≤ N`
it delivers is not a consequence of `False`. -/
example :
    ∃ (ε₂ e : ℝ) (N : ℕ) (η : ℕ → ℝ),
      ML2Spine.IsSpine 1 1 1 (fun x => x) (fun x => x) ε₂ e N η ∧
        4096 ≤ N ∧ e = 1 / Real.sqrt (N : ℝ) ∧
        η 0 = ML2Spine.spineNu 1 1 1 (fun x => x) (fun x => x) ∧
        0 ≤ η 0 ∧ (∀ k < N, η k ≤ e * η (k + 1)) ∧ η N ≤ e ∧
        0 < ε₂ ∧ 5 * e ≤ ε₂ ∧ ε₂ ≤ 1 / 5 :=
  exists_dividingScalesLadder (β := 1) (ϖ := 1) (ε₁ := 1) (gain := fun x => x)
    (dens := fun x => x) one_pos le_rfl one_pos one_pos (fun _ h => h) (fun _ h => h)

omit [Nontrivial E] in
/-- **The Katz--Tao hypothesis of the input package is not an obstruction on a small family.**

`Kakeya.maxDensity s W ≤ #s` always, so any family whose cardinality already obeys the crude bound
satisfies the density hypothesis at the same exponent.  Together with
`Kakeya.ML2Shaded.exists_fullShading_of_tubes` — which re-shades *any* witness of the unshaded
hypotheses fully, hence keeps the same tubes and the same witnesses, and satisfies
`HasDenseShading 1` on the nose — this settles that the hypothesis set of
`Kakeya.ML2Inputs.exists_dividingScalesInputs` and of the capstone is consistent: it is met by every
family of at most `δ^{-θ}` tubes in `B₁`, fully shaded. -/
theorem maxDensity_le_of_card_le {δ : NNReal} {θ : ℝ} (s : Finset ι) (T : ι → Tube δ E)
    (hcard : (s.card : ENNReal) ≤ ENNReal.ofReal ((δ : ℝ) ^ (-θ))) :
    Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-θ)) :=
  le_trans (Kakeya.maxDensity_le_card s _) hcard

/-- **The crude cardinality bound is derivable from the dichotomy's own hypotheses**, so the
hypothesis `|𝕋| ≤ δ^{-K₀}` of `Kakeya.ML2Inputs.exists_dividingScalesInputs` adds nothing at
`K₀ = 4`: `Kakeya.ML2Assembly.card_le_rpow_neg_four` derives it in `ℝ³` from containment in `B_1`,
`θ ≤ 1` and the Katz--Tao bound, below the threshold
`Kakeya.ML2Assembly.eventually_card_thresholds`.

This is the statement that the input package is available in the `∀ᶠ δ` form and under
literally the hypotheses of `Kakeya.ML2Assembly.Dichotomy` — `Kakeya.IsKatzTao` written exactly as
the dichotomy writes it, no cardinality side condition, and nothing about essential distinctness or
uniformity. -/
theorem eventually_dividingScalesInputs_dim3 {θ α : ℝ} (hθ1 : θ ≤ 1) (hα : 0 < α) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i => (V i).toConvexSpaceBody) ((δ : ENNReal) ^ (-θ)) →
        ∃ u ⊆ s,
          (∀ i ∈ u, (V i).carrier ⊆ Metric.closedBall 0 1) ∧
          (u : Set ι).Pairwise
            (fun i j => IsEssentiallyDistinct ((V i).carrier) ((V j).carrier)) ∧
          Kakeya.maxDensity u (fun i => (V i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-θ) ∧
          Nonempty (UniformTubeSet u (fun i => (V i).toTube) (ssfGridLen δ) (uniformConst 3)) ∧
          (s.card : ENNReal)
              ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(θ + α))) * (u.card : ENNReal) := by
  classical
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  obtain ⟨d, hd0, hd1, hpack⟩ :=
    exists_dividingScalesInputs.{u} (E := EuclideanSpace ℝ (Fin 3)) 4 θ hα
  filter_upwards [ML2Assembly.eventually_card_thresholds, Ioc_mem_nhdsGT hd0]
    with δ hthr hδmem
  obtain ⟨hδ0, hδ1, hδC⟩ := hthr
  obtain ⟨-, hδd⟩ := hδmem
  intro ι s V hball hKT
  have hDens : Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody)
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-θ)) := by
    rw [ML2Reduction.ofReal_rpow_coe hδ0]
    exact hKT
  have hcardK : (s.card : ℝ) ≤ (δ : ℝ) ^ (-((4 : ℕ) : ℝ)) := by
    have h := ML2Assembly.card_le_rpow_neg_four hδ0 hδ1 hδC s V hball hθ1 hKT
    simpa using h
  have hball' : ∀ i ∈ s, ((V i).toTube).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := hball
  have hDens' : Kakeya.maxDensity s (fun i => ((V i).toTube).toConvexSpaceBody)
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-θ)) :=
    le_trans (le_of_eq (Kakeya.maxDensity_congr (fun i _ => rfl))) hDens
  obtain ⟨u, hus, hballu, hED, hDensu, hstruct, hcard⟩ :=
    hpack hδ0 hδd s (fun i => (V i).toTube) hball' hDens' hcardK
  have hballu' : ∀ i ∈ u, (V i).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := hballu
  have hED' : (u : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct ((V i).carrier) ((V j).carrier)) := by
    intro i hi j hj hne
    exact hED hi hj hne
  refine ⟨u, hus, hballu', hED', ?_, ?_, hcard⟩
  · rw [← ML2Reduction.ofReal_rpow_coe hδ0]
    exact le_trans (le_of_eq (Kakeya.maxDensity_congr (fun i _ => rfl))) hDensu
  · rw [hE] at hstruct
    exact hstruct

/-- `eventually_shaded_dividingScales_dim3`, returning the level twin
`DividingScalesOutputLevels`.  The existing statement is the corollary below. -/
theorem eventually_shaded_dividingScales_dim3_levels
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {α : ℝ} (hα : 0 < α) :
    ∃ (C : NNReal) (Kl cl : ℕ) (ε₂ e : ℝ) (N : ℕ) (η : ℕ → ℝ),
      1 ≤ C ∧ 4096 ≤ N ∧ e = 1 / Real.sqrt (N : ℝ) ∧
      η 0 = ML2Spine.spineNu β ϖ ε₁ gain dens ∧ 0 < η 0 ∧ η 0 ≤ 1 ∧
      ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η ∧
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
        ∀ {ι : Type u} (s : Finset ι) (V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          s.Nonempty →
          (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
          IsKatzTao s (fun i => (V i).toConvexSpaceBody) ((δ : ENNReal) ^ (-(η 0))) →
          ∀ lam : NNReal, 0 < lam →
          ML2Shaded.HasDenseShading lam s (fun i => (V i).toShadedBody) →
          DividingScalesOutputLevels C Kl cl ε₁ α e N η s V lam := by
  classical
  obtain ⟨C, d, Kl, cl, ε₂, e, N, η, hC, hd0, hd1, hN, he, hη0nu, hspine, hmain⟩ :=
    exists_shaded_dividingScales_of_dichotomyHypotheses_levels.{u}
      (E := EuclideanSpace ℝ (Fin 3)) (by simp) 4 hβ hβ1 hϖ hε₁ hgain hdens hα
  have hν0 : 0 < ML2Spine.spineNu β ϖ ε₁ gain dens :=
    ML2Spine.spineNu_pos hβ hϖ hε₁ hgain hdens
  have hν1 : ML2Spine.spineNu β ϖ ε₁ gain dens ≤ 1 := by
    have h := spineNu_le_div_48000 hβ hβ1 hϖ hε₁ hgain hdens
    linarith
  have hη00 : 0 < η 0 := by rw [hη0nu]; exact hν0
  have hη01 : η 0 ≤ 1 := by rw [hη0nu]; exact hν1
  refine ⟨C, Kl, cl, ε₂, e, N, η, hC, hN, he, hη0nu, hη00, hη01, hspine, ?_⟩
  filter_upwards [ML2Assembly.eventually_card_thresholds, Ioc_mem_nhdsGT hd0]
    with δ hthr hδmem
  obtain ⟨hδ0, hδ1, hδC⟩ := hthr
  obtain ⟨-, hδd⟩ := hδmem
  intro ι s V hsne hball hKT lam hlam hdense
  have hDens : Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody)
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0))) := by
    rw [ML2Reduction.ofReal_rpow_coe hδ0]
    exact hKT
  have hcardK : (s.card : ℝ) ≤ (δ : ℝ) ^ (-((4 : ℕ) : ℝ)) := by
    have h := ML2Assembly.card_le_rpow_neg_four hδ0 hδ1 hδC s V hball hη01 hKT
    simpa using h
  exact hmain hδ0 hδd s V hsne hball hDens hcardK lam hlam hdense

/-- **The capstone in the `∀ᶠ δ` form of `Kakeya.ML2Assembly.Dichotomy`, in `ℝ³`** — the form the
assembly of the first disjunct calls.

Every hypothesis is either one of `Kakeya.ML2Assembly.Dichotomy`'s own, written exactly as the
dichotomy writes it (`Kakeya.IsKatzTao … ((δ : ENNReal) ^ (-(η 0)))`, containment in `B₁`), or the
one-sided density invariant `Kakeya.ML2Shaded.HasDenseShading lam 𝕋 Y` that
`Kakeya.ML2Shaded.exists_denseShading_refinement` produces from the dichotomy's fullness hypothesis
at the absolute cost `2`, or nonemptiness, which `δ⁻¹ ≤ |𝕋|` gives.

In particular the crude cardinality bound `|𝕋| ≤ δ^{-4}` has been discharged — by
`Kakeya.ML2Assembly.card_le_rpow_neg_four`, whose `η ≤ 1` side condition is met by
`Kakeya.ML2Inputs.spineNu_le_div_48000` — and **no essential distinctness, no uniform hierarchy and
no `4096 ≤ N` appear anywhere in the statement**.

`ν = η 0`, `ε₂`, `e`, `N` and the whole ladder are bound *before* the filter, hence before the
scale and before the family, and none of them sees an outer accuracy. -/
theorem eventually_shaded_dividingScales_dim3
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {α : ℝ} (hα : 0 < α) :
    ∃ (C : NNReal) (Kl cl : ℕ) (ε₂ e : ℝ) (N : ℕ) (η : ℕ → ℝ),
      1 ≤ C ∧ 4096 ≤ N ∧ e = 1 / Real.sqrt (N : ℝ) ∧
      η 0 = ML2Spine.spineNu β ϖ ε₁ gain dens ∧ 0 < η 0 ∧ η 0 ≤ 1 ∧
      ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η ∧
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
        ∀ {ι : Type u} (s : Finset ι) (V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          s.Nonempty →
          (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
          IsKatzTao s (fun i => (V i).toConvexSpaceBody) ((δ : ENNReal) ^ (-(η 0))) →
          ∀ lam : NNReal, 0 < lam →
          ML2Shaded.HasDenseShading lam s (fun i => (V i).toShadedBody) →
          DividingScalesOutput C Kl cl ε₁ α e N η s V lam := by
  obtain ⟨C, Kl, cl, ε₂, e, N, η, hC, hN, he, hη0nu, hη00, hη01, hspine, hev⟩ :=
    eventually_shaded_dividingScales_dim3_levels.{u} hβ hβ1 hϖ hε₁ hgain hdens hα
  exact ⟨C, Kl, cl, ε₂, e, N, η, hC, hN, he, hη0nu, hη00, hη01, hspine,
    hev.mono fun δ hδ => fun s V hsne hball hKT lam hlam hdense =>
      (hδ s V hsne hball hKT lam hlam hdense).toDividingScalesOutput⟩


end Kakeya.ML2Inputs

end
