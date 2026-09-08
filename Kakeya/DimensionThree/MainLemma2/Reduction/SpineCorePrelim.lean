/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDichotomyInputs
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineShadingBridge

/-!
# The shared preliminaries of a `Kakeya.ML2Assembly.GeometricCoreAt` producer

Rows **GC-P1** and **GC-P2** of the Section-9 geometric-core plan.  Everything below `Dichotomy`'s
hypothesis block and above the two branches lives here, and nothing here is specific to either
branch.

## What is missing between `Dichotomy` and GWZ Lemma 7.7(B)

`Kakeya.ML2Inputs.eventually_shaded_dividingScales_dim3` already runs GWZ Lemma 7.7(B) on the
`Kakeya.ML2Assembly.Dichotomy` context — essential distinctness, the uniform hierarchy, `4096 ≤ N`
and the crude cardinality bound are all discharged there.  Two of its hypotheses are still *not*
`Dichotomy`'s:

1. **nonemptiness** of the family.  `Dichotomy` grants `δ⁻¹ ≤ #𝕋`; with `δ ≤ 1` that forces
   `#𝕋 ≥ 1`.  `Kakeya.ML2Core.nonempty_of_inv_le_card`.
2. **`Kakeya.ML2Shaded.HasDenseShading lam`**, the *pointwise* density invariant.  `Dichotomy`
   grants only the *aggregate* `δ^ν ≤ λ(𝕋, Y)`.  The conversion is
   `Kakeya.ML2Shaded.exists_denseShading_refinement`, and it is not free: it returns a
   **subfamily** `𝕋' ⊆ 𝕋`, at the absolute mass loss `2`.
   `Kakeya.ML2Core.exists_denseShading_dichotomy`.

Item 2 is the only place in this file where a hypothesis of the target is not literally a
hypothesis of the source, and it is paid for by a named loss rather than by an added hypothesis:
the price is the factor `2` in `∑_{i ∈ 𝕋} |Y_i| ≤ 2 ∑_{i ∈ 𝕋'} |Y_i|`, which is carried in the
conclusion of `Kakeya.ML2Core.eventually_dividingScalesPackage_dim3` and is what the pushback of
either disjunct to the original family spends.

## The direction check

`HasDenseShading` is pointwise and is consumed pointwise; the fullness bound of `Dichotomy` is an
aggregate and is consumed as an aggregate, exactly once, to manufacture the pointwise datum at the
cost of the subfamily.  No aggregate quantity is read at a point.  The cardinality retention that
GWZ Lemma 7.7(B) returns is a *cardinality* statement and is converted to mass only through
`Kakeya.ML2Shaded.sum_shade_le_of_card_le`, i.e. only against the pointwise datum — the trap
`Kakeya.ML2Inputs.no_mass_share_of_essDistinct_refinement` refutes.

## The three losses back to `(𝕋, Y)`, named

`Kakeya.ML2Core.losses_of_dividingScalesOutput` is the whole accounting, in one statement.  With
`u'` the family GWZ Lemma 7.7(B) returns and `W` its refined shading:

* the **mass loss** `2 · δ^{-(ν+ν)} · totalLoss C Kl cl δ · C₃ / (lam · c₃)`, from the
  dense-shading discard (`2`) composed with the cardinality-to-mass conversion at the single
  cardinality loss of `Kakeya.ML2Inputs.DividingScalesOutput`;
* the **shaded-uniformization mass loss** `(log₂ #𝕋 + 1)^{2 ssfGridLen δ + 2}` from `Y` to `W`
  on `u'`, monotonised from the intermediate family's cardinality up to `#𝕋` so that the consumer
  never has to name the intermediate family;
* the **fullness loss**: the same polylogarithm, carrying `lam ≥ δ^ν/2` down to
  `λ'(u', W)`.

The union is monotone (`u' ⊆ 𝕋`), so no loss is charged there; that clause is stated so a consumer
of either disjunct does not have to re-derive it.

## `ε`-discipline

No statement in this file has an `ε` binder.  The absorption budget of
`Kakeya.ML2Core.eventually_coreThresholds_dim3` is `α := ν`, a `β`-only quantity, and both budget
clauses are inequalities between `β`, `ν` and the spine's own `ε₂`.
`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy` is untouched.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ShadedBody ConvexSpaceBody
open Tube ShadedTube

universe u

namespace Kakeya.ML2Core

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-! ### GC-P1, step 1: nonemptiness -/

/-- **`Kakeya.ML2Assembly.Dichotomy`'s cardinality hypothesis gives nonemptiness.**

`δ ≤ 1` makes `δ⁻¹ ≥ 1`, so `δ⁻¹ ≤ #𝕋` forces `#𝕋 ≥ 1`.  This is the whole content of
statement-mismatch risk 1 of the plan: `Kakeya.ML2Inputs.eventually_shaded_dividingScales_dim3`
demands `s.Nonempty`, `Dichotomy` does not grant it, and no hypothesis has to be added.

`hδ0` is what makes `δ⁻¹` finite and the inversion order-reversing; `hδ1` is what puts `δ⁻¹` above
`1`. -/
theorem nonempty_of_inv_le_card {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {s : Finset ι}
    (hcard : (δ : ℝ)⁻¹ ≤ (s.card : ℝ)) : s.Nonempty := by
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδR1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have h1 : (1 : ℝ) ≤ (δ : ℝ)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hδR]; simpa using hδR1
  have h2 : (1 : ℝ) ≤ (s.card : ℝ) := le_trans h1 hcard
  have h3 : 1 ≤ s.card := by exact_mod_cast h2
  exact Finset.card_pos.mp h3

/-! ### GC-P1, step 2: the pointwise density invariant, at a named mass loss -/

omit [Nontrivial E] in
/-- **`Kakeya.ML2Assembly.Dichotomy`'s fullness hypothesis gives a dense shading**, on a subfamily,
at the absolute mass loss `2`, and the level is `δ^θ/2`.

This is statement-mismatch risk 2 of the plan, discharged.  The three outputs a consumer needs are
all here and all named:

* `δ^θ/2 ≤ lam` — the level, forced by `hfull` alone (`lam` is `λ(𝕋, Y)/2` and `λ(𝕋, Y) ≥ δ^θ`);
* `0 < lam` — forced by `hδ0`, since `δ^θ > 0`; this is what
  `Kakeya.ML2Inputs.eventually_shaded_dividingScales_dim3` consumes as `hlam`;
* `s'.Nonempty` — forced by `hfull` *again*, through the mass retention: a positive fullness makes
  the total shade mass nonzero (`ShadedBody.sum_volume_shade_ne_zero_of_fullness_pos`), and the
  retention `∑_𝕋 ≤ 2 ∑_{𝕋'}` then forbids `𝕋' = ∅`.  Note that this is *not* available from
  `Kakeya.ML2Core.nonempty_of_inv_le_card`, which speaks about `𝕋` and not about `𝕋'`.

The loss is the factor `2`, and it is the only loss: `Kakeya.ML2Shaded.HasDenseShading` restricts to
subfamilies at zero cost, so nothing further is charged downstream. -/
theorem exists_denseShading_dichotomy {δ : NNReal} (hδ0 : 0 < δ) {θ : ℝ} (s : Finset ι)
    (T : ι → ShadedTube δ E)
    (hfull : ShadedBody.fullness s (fun i => (T i).toShadedBody) ≥ δ ^ θ) :
    ∃ s' ⊆ s, ∃ lam : NNReal, δ ^ θ / 2 ≤ lam ∧ 0 < lam ∧ s'.Nonempty ∧
      (∑ i ∈ s, volume (T i).shade) ≤ 2 * ∑ i ∈ s', volume (T i).shade ∧
      ML2Shaded.HasDenseShading lam s' (fun i => (T i).toShadedBody) := by
  classical
  have hpow : (0 : NNReal) < δ ^ θ := NNReal.rpow_pos hδ0
  have hfullpos : 0 < ShadedBody.fullness s (fun i => (T i).toShadedBody) :=
    lt_of_lt_of_le hpow hfull
  obtain ⟨s', hs's, hmass, hdense⟩ :=
    ML2Shaded.exists_denseShading_refinement (E := E) s (fun i => (T i).toShadedBody)
  refine ⟨s', hs's, ShadedBody.fullness s (fun i => (T i).toShadedBody) / 2, ?_, ?_, ?_,
    hmass, hdense⟩
  · exact div_le_div_of_nonneg_right hfull (by norm_num)
  · positivity
  · rw [Finset.nonempty_iff_ne_empty]
    intro h0
    rw [h0] at hmass
    simp only [Finset.sum_empty, mul_zero, nonpos_iff_eq_zero] at hmass
    exact ShadedBody.sum_volume_shade_ne_zero_of_fullness_pos s _ hfullpos hmass

/-! ### GC-P1: the package, in the `∀ᶠ δ` form of `Kakeya.ML2Assembly.Dichotomy` -/

/-- **GC-P1 — `Kakeya.ML2Inputs.DividingScalesOutput` produced from literally
`Kakeya.ML2Assembly.Dichotomy`'s hypotheses, at `α := ν`.**

The four hypotheses of the inner statement are `Dichotomy`'s (a)–(d) verbatim, at `η := ν = η 0`
(the compatibility `example` below pins that by `id`), and the two hypotheses of
`Kakeya.ML2Inputs.eventually_shaded_dividingScales_dim3` that `Dichotomy` does not grant are
produced, not assumed:

* `s.Nonempty` by `Kakeya.ML2Core.nonempty_of_inv_le_card` from (d) and `δ ≤ 1`;
* `Kakeya.ML2Shaded.HasDenseShading lam` by `Kakeya.ML2Core.exists_denseShading_dichotomy` from
  (c), at the mass loss `2` and on the subfamily `s'`.

Hypotheses (a) and (b) are then read on `s'` for free — containment is pointwise, and the Katz--Tao
bound is `Kakeya.maxDensity_mono`.

**The absorption budget is `α := ν`.**  It is bound before the scale and before the family, and it
is a `β`-only quantity (`ν = Kakeya.ML2Spine.spineNu β ϖ ε₁ gain dens`), so the single cardinality
loss of `Kakeya.ML2Inputs.DividingScalesOutput` is `δ^{-(ν+ν)} · totalLoss C Kl cl δ`.  That is the
`a = 2ν` the shading bridge is charged at in
`Kakeya.ML2Core.eventually_coreThresholds_dim3`.

**The losses back to `(s, T)`** are the two conclusions `∑_s ≤ 2 ∑_{s'}` and `s' ⊆ s`, together
with everything `Kakeya.ML2Core.losses_of_dividingScalesOutput` reads off the package.  Nothing
else is spent between `Dichotomy`'s hypotheses and GWZ Lemma 7.7(B)'s output. -/
theorem eventually_dividingScalesPackage_dim3
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
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
          ∃ s' ⊆ s, ∃ lam : NNReal,
            δ ^ (η 0) / 2 ≤ lam ∧ 0 < lam ∧ s'.Nonempty ∧
            (∑ i ∈ s, volume (T i).shade) ≤ 2 * ∑ i ∈ s', volume (T i).shade ∧
            ML2Shaded.HasDenseShading lam s' (fun i ↦ (T i).toShadedBody) ∧
            ML2Inputs.DividingScalesOutput C Kl cl ε₁ (η 0) e N η s' T lam := by
  classical
  have hν0 : 0 < ML2Spine.spineNu β ϖ ε₁ gain dens :=
    ML2Spine.spineNu_pos hβ hϖ hε₁ hgain hdens
  obtain ⟨C, Kl, cl, ε₂, e, N, η, hC, hN, he, hη0nu, hη00, hη01, hspine, hev⟩ :=
    ML2Inputs.eventually_shaded_dividingScales_dim3.{u}
      hβ hβ1 hϖ hε₁ hgain hdens (α := ML2Spine.spineNu β ϖ ε₁ gain dens) hν0
  refine ⟨C, Kl, cl, ε₂, e, N, η, hC, hN, he, hη0nu, hη00, hη01, hspine, ?_⟩
  filter_upwards [hev, Ioc_mem_nhdsGT (zero_lt_one' NNReal)] with δ hδmain hδmem
  obtain ⟨hδ0, hδ1⟩ := hδmem
  refine ⟨hδ0, hδ1, ?_⟩
  intro ι s T hball hKT hfull hcard
  have hsne : s.Nonempty := nonempty_of_inv_le_card hδ0 hδ1 hcard
  obtain ⟨s', hs's, lam, hlamlow, hlam0, hs'ne, hmass, hdense⟩ :=
    exists_denseShading_dichotomy (E := EuclideanSpace ℝ (Fin 3)) hδ0 s T hfull
  have hballs' : ∀ i ∈ s', (T i).carrier ⊆ Metric.closedBall 0 1 :=
    fun i hi => hball i (hs's hi)
  have hKTs' : IsKatzTao s' (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-(η 0))) :=
    le_trans (Kakeya.maxDensity_mono (fun i ↦ (T i).toConvexSpaceBody) hs's) hKT
  have hout := hδmain s' T hs'ne hballs' hKTs' lam hlam0 hdense
  rw [← hη0nu] at hout
  exact ⟨hsne, s', hs's, lam, hlamlow, hlam0, hs'ne, hmass, hdense, hout⟩

/-- **compatibility.**  The hypothesis block of
`Kakeya.ML2Core.eventually_dividingScalesPackage_dim3` is `Kakeya.ML2Assembly.Dichotomy`'s,
verbatim: the two are pinned by `id`, so a later edit to either one breaks this theorem.  It is a
*named* declaration and not an `example` so that `#print axioms` can check it. -/
theorem dichotomy_of_dichotomyBody {β ε₀ g η : ℝ}
    (h : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
        (∑ i ∈ s, volume (T i).shade
              ≤ (δ : ENNReal) ^ (-ε₀) * volume (⋃ i ∈ s, (T i).shade))
          ∨ (∑ i ∈ s, volume (T i).shade
              ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β
                  * volume (⋃ i ∈ s, (T i).shade))) :
    ML2Assembly.Dichotomy.{u} β ε₀ g η := h

/-! ### GC-P1: the losses back to `(s, T)`, named -/

/-- **Every loss `Kakeya.ML2Core.eventually_dividingScalesPackage_dim3` charges, read off the
package in one statement.**

Input: the dense-shading mass retention `∑_s ≤ 2 ∑_{s'}` and the
`Kakeya.ML2Inputs.DividingScalesOutput` on `s'`.  Output: the family `u'` that GWZ Lemma 7.7(B)
returns, presented **as a subfamily of `s`** (the intermediate family the dichotomy interposes is
existentially discharged), with

1. the **mass loss** — `lam · c₃ · ∑_{i ∈ s} |Y_i| ≤ 2 · A · C₃ · ∑_{i ∈ u'} |Y_i|` with
   `A = δ^{-(η₀+α)} · totalLoss C Kl cl δ`.  The `2` is the dense-shading discard; `A` is the
   single cardinality loss of the package; `lam`, `c₃`, `C₃` are what
   `Kakeya.ML2Shaded.sum_shade_le_of_card_le` charges to turn a cardinality retention into a mass
   retention.  `hδ1` is what that conversion needs (`Tube.volume_le`);
2. the **shaded-uniformization mass loss** from `Y` to `W` on `u'`, at the polylogarithm
   `(log₂ #s + 1)^{2 ssfGridLen δ + 2}`.  The package states it at the *intermediate* family's
   cardinality; it is monotonised up to `#s` here (`Nat.log_mono_right` along `u' ⊆ v ⊆ s' ⊆ s`) so
   that no consumer has to name the intermediate family, and so that the polylogarithm matches the
   `m ≤ δ^{-4}` slot of `Kakeya.ML2Core.eventually_coreThresholds_dim3`;
3. **union monotonicity**, `|⋃_{u'} W| ≤ |⋃_s Y|`, at no loss — `u' ⊆ s` and `W_i ⊆ Y_i`;
4. the **fullness loss**, `lam ≤ (log₂ #s + 1)^{2 ssfGridLen δ + 2} · λ'(u', W)`, the same
   polylogarithm.  Composed with `δ^ν/2 ≤ lam` from GC-P1 this is the fullness input of GWZ
   Theorem 7.3(B).

Also carried through unchanged: the pointwise `Kakeya.ML2Shaded.HasDenseShading lam` and
`Kakeya.ML2Shaded.HasComparableDensities lam⁻¹` on `u'` for the *original* shading, the tube/shade
relations of `W`, nonemptiness, and the two-way alternative on the returned hierarchy.

Nothing here is a new obligation: every clause is a clause of
`Kakeya.ML2Inputs.DividingScalesOutput` or of `hmass`, composed. -/
theorem losses_of_dividingScalesOutput {δ : NNReal} (hδ1 : δ ≤ 1)
    {C : NNReal} {Kl cl : ℕ} {ε₁ α e : ℝ} {N : ℕ} {η : ℕ → ℝ}
    {s s' : Finset ι} (hs's : s' ⊆ s) {T : ι → ShadedTube δ E} {lam : NNReal}
    (hmass : (∑ i ∈ s, volume (T i).shade) ≤ 2 * ∑ i ∈ s', volume (T i).shade)
    (hout : ML2Inputs.DividingScalesOutput C Kl cl ε₁ α e N η s' T lam) :
    ∃ u' ⊆ s, ∃ W : ι → ShadedTube δ E,
      (∀ i, (W i).toTube = (T i).toTube) ∧
      (∀ i, (W i).shade ⊆ (T i).shade) ∧
      u'.Nonempty ∧
      ML2Shaded.HasDenseShading lam u' (fun i => (T i).toShadedBody) ∧
      ML2Shaded.HasComparableDensities lam⁻¹ u' (fun i => (T i).toShadedBody) ∧
      (lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
            * (∑ i ∈ s, volume (T i).shade)
          ≤ 2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + α)))
              * StickyKakeya.totalLoss C Kl cl δ)
            * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
            * ∑ i ∈ u', volume (T i).shade ∧
      (∑ i ∈ u', volume (T i).shade)
          ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
            * ∑ i ∈ u', volume (W i).shade ∧
      volume (⋃ i ∈ u', (W i).shade) ≤ volume (⋃ i ∈ s, (T i).shade) ∧
      (lam : ENNReal)
          ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
            * ShadedBody.fullness' u' (fun i => (W i).toShadedBody) ∧
      ∃ 𝒲 : ShadedUniformTubeSet u' W (ssfGridLen δ) (max C 4),
        (𝒲.tubeUniform.IsKatzTaoAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-ε₁)))
          ∨ ∃ a b m : ℕ, ML2Reduction.IsKatzTaoDividingWindow 𝒲.tubeUniform
              ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) η e N a b m) := by
  classical
  obtain ⟨v, hvs', u', hu'v, W, hu'ne, htube, hshade, hcard, hpolymass, hdense, hcomp,
    hfull, 𝒲, halt⟩ := hout
  have hu's : u' ⊆ s := (hu'v.trans hvs').trans hs's
  have hlog : Nat.log 2 v.card ≤ Nat.log 2 s.card :=
    Nat.log_mono_right (Finset.card_le_card (hvs'.trans hs's))
  have hP : ((Nat.log 2 v.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
      ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2) := by
    gcongr
  refine ⟨u', hu's, W, htube, hshade, hu'ne, hdense, hcomp, ?_, ?_, ?_, ?_, 𝒲, halt⟩
  · -- the mass loss back to `(s, T)`
    have hconv := ML2Shaded.sum_shade_le_of_card_le (E := E) hδ1 (s := s') (s' := u') (V := T)
      hdense hcard
    calc (lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
            * (∑ i ∈ s, volume (T i).shade)
        ≤ (lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
            * (2 * ∑ i ∈ s', volume (T i).shade) := by gcongr
      _ = 2 * ((lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
            * ∑ i ∈ s', volume (T i).shade) := by ring
      _ ≤ 2 * ((ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + α)))
              * StickyKakeya.totalLoss C Kl cl δ)
            * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
            * ∑ i ∈ u', volume (T i).shade) := by
          gcongr
      _ = 2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + α)))
              * StickyKakeya.totalLoss C Kl cl δ)
            * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
            * ∑ i ∈ u', volume (T i).shade := by ring
  · exact hpolymass.trans (mul_le_mul' hP le_rfl)
  · refine measure_mono (Set.iUnion₂_subset fun i hi x hx => ?_)
    exact Set.mem_biUnion (hu's hi) (hshade i hx)
  · exact hfull.trans (mul_le_mul' hP le_rfl)

/-- `Kakeya.ML2Core.losses_of_dividingScalesOutput` on
`Kakeya.ML2Inputs.DividingScalesOutputLevels`:
the same clauses, with the window carrying the two extra fields of
`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels`.  The proof is that theorem's, verbatim. -/
theorem losses_of_dividingScalesOutputLevels {δ : NNReal} (hδ1 : δ ≤ 1)
    {C : NNReal} {Kl cl : ℕ} {ε₁ α e : ℝ} {N : ℕ} {η : ℕ → ℝ}
    {s s' : Finset ι} (hs's : s' ⊆ s) {T : ι → ShadedTube δ E} {lam : NNReal}
    (hmass : (∑ i ∈ s, volume (T i).shade) ≤ 2 * ∑ i ∈ s', volume (T i).shade)
    (hout : ML2Inputs.DividingScalesOutputLevels C Kl cl ε₁ α e N η s' T lam) :
    ∃ u' ⊆ s, ∃ W : ι → ShadedTube δ E,
      (∀ i, (W i).toTube = (T i).toTube) ∧
      (∀ i, (W i).shade ⊆ (T i).shade) ∧
      u'.Nonempty ∧
      ML2Shaded.HasDenseShading lam u' (fun i => (T i).toShadedBody) ∧
      ML2Shaded.HasComparableDensities lam⁻¹ u' (fun i => (T i).toShadedBody) ∧
      (lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
            * (∑ i ∈ s, volume (T i).shade)
          ≤ 2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + α)))
              * StickyKakeya.totalLoss C Kl cl δ)
            * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
            * ∑ i ∈ u', volume (T i).shade ∧
      (∑ i ∈ u', volume (T i).shade)
          ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
            * ∑ i ∈ u', volume (W i).shade ∧
      volume (⋃ i ∈ u', (W i).shade) ≤ volume (⋃ i ∈ s, (T i).shade) ∧
      (lam : ENNReal)
          ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
            * ShadedBody.fullness' u' (fun i => (W i).toShadedBody) ∧
      ∃ 𝒲 : ShadedUniformTubeSet u' W (ssfGridLen δ) (max C 4),
        (𝒲.tubeUniform.IsKatzTaoAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-ε₁)))
          ∨ ∃ a b m : ℕ, ML2Reduction.IsKatzTaoDividingWindowLevels 𝒲.tubeUniform
              ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) η e N a b m) := by
  classical
  obtain ⟨v, hvs', u', hu'v, W, hu'ne, htube, hshade, hcard, hpolymass, hdense, hcomp,
    hfull, 𝒲, halt⟩ := hout
  have hu's : u' ⊆ s := (hu'v.trans hvs').trans hs's
  have hlog : Nat.log 2 v.card ≤ Nat.log 2 s.card :=
    Nat.log_mono_right (Finset.card_le_card (hvs'.trans hs's))
  have hP : ((Nat.log 2 v.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2)
      ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) ^ (2 * ssfGridLen δ + 2) := by
    gcongr
  refine ⟨u', hu's, W, htube, hshade, hu'ne, hdense, hcomp, ?_, ?_, ?_, ?_, 𝒲, halt⟩
  · -- the mass loss back to `(s, T)`
    have hconv := ML2Shaded.sum_shade_le_of_card_le (E := E) hδ1 (s := s') (s' := u') (V := T)
      hdense hcard
    calc (lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
            * (∑ i ∈ s, volume (T i).shade)
        ≤ (lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
            * (2 * ∑ i ∈ s', volume (T i).shade) := by gcongr
      _ = 2 * ((lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
            * ∑ i ∈ s', volume (T i).shade) := by ring
      _ ≤ 2 * ((ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + α)))
              * StickyKakeya.totalLoss C Kl cl δ)
            * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
            * ∑ i ∈ u', volume (T i).shade) := by
          gcongr
      _ = 2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + α)))
              * StickyKakeya.totalLoss C Kl cl δ)
            * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
            * ∑ i ∈ u', volume (T i).shade := by ring
  · exact hpolymass.trans (mul_le_mul' hP le_rfl)
  · refine measure_mono (Set.iUnion₂_subset fun i hi x hx => ?_)
    exact Set.mem_biUnion (hu's hi) (hshade i hx)
  · exact hfull.trans (mul_le_mul' hP le_rfl)

/-! ### GC-P2: the four thresholds, fused, and the exponent budget stated once -/

/-- **GC-P2 — the four thresholds of the geometric core, in a single `∀ᶠ δ` statement, and the
exponent budget stated exactly once.**

The thresholds are `Kakeya.ML2Assembly.eventually_card_thresholds`,
`Kakeya.ML2Reduction.exists_threshold_katzTaoError_le`,
`Kakeya.ML2Inputs.exists_threshold_edLoss_le` and
`Kakeya.ML2Shading.exists_threshold_shadingBridgeLoss_le`, all instantiated at the *one* absorption
budget `α := ν = η 0` that `Kakeya.ML2Core.eventually_dividingScalesPackage_dim3` uses, plus
`Kakeya.ML2Shaded.exists_threshold_massBandLoss_le` — see "the fifth threshold" below.  Each is
bound before the scale and before the family; the fusion is a single `filter_upwards`, so a
consumer instantiates one `∀ᶠ` and not five.

**The budget, stated once.**  Two `δ`-free clauses, both proved from
`Kakeya.ML2Inputs.spineNu_le_div_48000` (`ν ≤ β/48000`) and the spine's own fields:

* **branch (i)**: `β/4 + (ν + ν + ν) ≤ β/2`.  The `β/4` is where GWZ Theorem 7.3(B) is read
  (`ε₁ := E (β/4)`, legitimate because `Kakeya.ML2Spine.exists_ml2SpineParams` takes the exponent
  map as a parameter); the `ν + ν` is the single cardinality loss of the package at `α = ν`; the
  third `ν` is the shading bridge's own budget.  The sum is the absolute accuracy
  `Kakeya.ML2Spine.absAccuracy β = β/2`, so branch (i) closes with `β/4` to spare.
  Forced by: `hβ`, `hβ1`, `hϖ`, `hε₁`, `hgain`, `hdens`, `hη0`.
* **branch (ii)**: `ν + ν + ν ≤ 40 · η k / ε₂` for **every** rung `k`, which is exactly the
  hypothesis `hκ` of `Kakeya.ML2Spine.spine_gainBudget_of_loss`.  Forced by
  `IsSpine.rung_mono` (`η 0 ≤ η k`), `IsSpine.rung_pos`, `IsSpine.eps₂_pos` and
  `IsSpine.eps₂_le_half`; the margin is a factor `80/3`, so the whole subpolynomial-loss chain of
  the gain branch fits with room.

**The fifth threshold, and why it is here.**  The plan names four.  The banded route the left
disjunct takes — `Kakeya.ML2Shading.sum_shade_le_of_everyScale_banded` — charges
`Kakeya.ML2Shaded.massBandLoss λ` *in addition* to `shadingBridgeLoss`, and that factor is not
covered by any of the four.  It is `Θ(ν log (1/δ))` under `δ^ν ≤ λ`, hence subpolynomial, and it is
absorbed here at the same budget `ν`.  A consumer that only needs the four may ignore the last
clause.

**The comparability constant is `2`, and it cannot be `lam⁻¹`.**
`Kakeya.ML2Shading.exists_threshold_shadingBridgeLoss_le` binds `K` *before* the scale, so `K`
must be `δ`-free; `Kakeya.ML2Inputs.DividingScalesOutput`'s
`Kakeya.ML2Shaded.HasComparableDensities lam⁻¹` has `lam⁻¹ ≈ δ^{-ν}` and is therefore **not** an
admissible `K` here.  `K = 2` is the constant the mass banding
(`Kakeya.ML2Shaded.exists_massBanded_shadeRefinement`, absolute) manufactures, and it is the one
this clause is stated at.  `K₀ = 4` is the crude cardinality exponent
`Kakeya.ML2Assembly.card_le_rpow_neg_four` delivers.

No clause of this statement mentions the outer accuracy, and `α = ν` is a `β`-only quantity. -/
theorem eventually_coreThresholds_dim3
    {β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    {C : NNReal} (Kl cl : ℕ)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hC : 1 ≤ C)
    (hη0 : η 0 = ML2Spine.spineNu β ϖ ε₁ gain dens)
    (hspine : ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η) :
    (β / 4 + (η 0 + η 0 + η 0) ≤ β / 2) ∧
    (∀ k, η 0 + η 0 + η 0 ≤ 40 * η k / ε₂) ∧
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      0 < δ ∧ δ ≤ 1 ∧
      (Tube.card_le_of_densityIn_le.C 3 : ENNReal) ≤ (δ : ENNReal) ^ (-1 : ℝ) ∧
      ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ
          * ENNReal.ofReal ((δ : ℝ) ^ (-ε₂)) ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ε₁))) ∧
      (ML2Inputs.edLoss 3 (ENNReal.ofReal ((δ : ℝ) ^ (-(η 0))))
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + η 0)))) ∧
      (∀ {A : ENNReal}, A ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + η 0))) →
        ∀ m : ℕ, (m : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) →
          ML2Shading.shadingBridgeLoss 3 A 2 (Nat.log 2 m) (Tube.ssfGridLen δ)
            ≤ (Tube.le_volume.c 3 : ENNReal)
              * ENNReal.ofReal ((δ : ℝ) ^ (-(η 0 + η 0 + η 0)))) ∧
      (∀ lam : NNReal, ENNReal.ofReal ((δ : ℝ) ^ (η 0)) ≤ (lam : ENNReal) →
          ML2Shaded.massBandLoss lam ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η 0)))) := by
  classical
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hη00 : 0 < η 0 := hspine.rung_pos 0
  have hν48 : η 0 ≤ β / 48000 := by
    rw [hη0]; exact ML2Inputs.spineNu_le_div_48000 hβ hβ1 hϖ hε₁ hgain hdens
  -- the exponent budget, stated once
  have hbudgetL : β / 4 + (η 0 + η 0 + η 0) ≤ β / 2 := by linarith
  have hbudgetG : ∀ k, η 0 + η 0 + η 0 ≤ 40 * η k / ε₂ := by
    intro k
    have hk : η 0 ≤ η k := hspine.rung_mono (Nat.zero_le k)
    have hε₂0 : 0 < ε₂ := hspine.eps₂_pos
    have hε₂h : ε₂ ≤ 1 / 2 := hspine.eps₂_le_half
    rw [le_div_iff₀ hε₂0]
    nlinarith
  refine ⟨hbudgetL, hbudgetG, ?_⟩
  -- the four thresholds, and the banding loss
  obtain ⟨d₁, hd₁0, hd₁1, hd₁⟩ :=
    ML2Reduction.exists_threshold_katzTaoError_le C hC Kl cl hε₁ hspine.eps₂_le_everyScale
  obtain ⟨d₂, hd₂0, hd₂1, hd₂⟩ :=
    ML2Inputs.exists_threshold_edLoss_le (E := EuclideanSpace ℝ (Fin 3))
      (θ := η 0) (α := η 0) hη00
  obtain ⟨d₃, hd₃0, hd₃1, hd₃⟩ :=
    ML2Shading.exists_threshold_shadingBridgeLoss_le 3 2 4
      (a := η 0 + η 0) (α := η 0) hη00
  obtain ⟨d₄, hd₄0, hd₄1, hd₄⟩ :=
    ML2Shaded.exists_threshold_massBandLoss_le (η := η 0) (α := η 0) hη00.le hη00
  filter_upwards [ML2Assembly.eventually_card_thresholds,
    Ioc_mem_nhdsGT hd₁0, Ioc_mem_nhdsGT hd₂0, Ioc_mem_nhdsGT hd₃0, Ioc_mem_nhdsGT hd₄0]
    with δ hthr h₁ h₂ h₃ h₄
  obtain ⟨hδ0, hδ1, hδC⟩ := hthr
  refine ⟨hδ0, hδ1, hδC, hd₁ hδ0 h₁.2, ?_, ?_, hd₄ hδ0 h₄.2⟩
  · have h := hd₂ hδ0 h₂.2
    rw [hE] at h
    exact h
  · intro A hA m hm
    exact hd₃ hδ0 h₃.2 hA m hm

/-- **Non-vacuity of GC-P2, and of the budget.**  At concrete data a spine exists and both budget
clauses hold on it, so neither is a consequence of `False`.  Named, so `#print axioms` sees it. -/
theorem exists_spine_budget_at_one : ∃ (ε₂ e : ℝ) (N : ℕ) (η : ℕ → ℝ),
    ML2Spine.IsSpine 1 1 1 (fun x => x) (fun x => x) ε₂ e N η ∧
      (1 : ℝ) / 4 + (η 0 + η 0 + η 0) ≤ 1 / 2 ∧
      ∀ k, η 0 + η 0 + η 0 ≤ 40 * η k / ε₂ := by
  obtain ⟨ε₂, e, N, η, hspine, -, -, hη0nu, -, -, -, -, -, -⟩ :=
    ML2Inputs.exists_dividingScalesLadder (β := 1) (ϖ := 1) (ε₁ := 1)
      (gain := fun x => x) (dens := fun x => x)
      one_pos le_rfl one_pos one_pos (fun _ h => h) (fun _ h => h)
  obtain ⟨hL, hG, -⟩ :=
    eventually_coreThresholds_dim3 (C := 1) 0 0 one_pos le_rfl one_pos one_pos
      (fun _ h => h) (fun _ h => h) le_rfl hη0nu hspine
  exact ⟨ε₂, e, N, η, hspine, hL, hG⟩

end Kakeya.ML2Core

end
