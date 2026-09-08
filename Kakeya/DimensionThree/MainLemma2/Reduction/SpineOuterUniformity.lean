/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineOuterTubes

/-!
# The uniformity witness that GWZ Lemma 9.1 asks for, at the grid of the outer scale

Blueprint `blueprint/src/GWZAdapted/section9.tex`, step 10 of the non-eccentric case.  This file
supplies the `huni` binder of `Kakeya.ML2Reduction.Lemma91At` — equivalently of
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer` — namely

```
∃ C : ℝ≥0, 1 ≤ C ∧ (C : ENNReal) ≤ (σ : ENNReal) ^ (-ηd) ∧
  Nonempty (ShadedTube.ShadedUniformTubeSet s U (Tube.ssfGridLen σ) C)
```

`Reduction/SpineOuterTubes.lean` records why this is not transported from upstairs: *"the
tube-level hierarchy on the outer family at the grid of `δ'` is a fresh object — the upstairs
hierarchy lives on the grid of `δ̃` — so it has to be built, not transported"*.

## What builds it, and what it costs

The tree already has the *composed* builder at exactly the grid length the binder names:
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`, which chains
`Tube.exists_uniformTubeSet_subfamily` and the balanced shade refinement and lands on
`ShadedTube.ShadedUniformTubeSet s' V' (Tube.ssfGridLen σ) (ShadedTube.ssfUniformConst n)`.  So the
two-step route through `Tube.exists_uniformTubeSet_subfamily_ssf` followed by
`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet` is redundant; the composed form is used
here.

Its price is **not** zero, and this is the one thing a consumer must plan for: the builder
*refines*, so the witness is produced

* on a **subfamily** `s' ⊆ s`, at count retention `|s| ≤ σ^{-α} |s'|`, and
* against a **shrunk shading** `U'` with `(U' i).toTube = (U i).toTube` and
  `(U' i).shade ⊆ (U i).shade`, at fullness retention `λ'(s', U) ≤ σ^{-α'} λ'(s', U')`.

Both are subpolynomial and both fit `Kakeya.ML2Spine.spine_gainBudget_of_loss`.  What they mean for
the interface is recorded in the docstring of
`Kakeya.ML2Reduction.exists_outerShadedUniformTubeSet`.

## Which hypothesis forces `C ≤ σ^{-ηd}`

Only two: `hηd : 0 < ηd`, and the threshold `σ ≤ σ₀` produced by the statement.  The constant the
builder returns is `ShadedTube.ssfUniformConst (Module.finrank ℝ E)` — a *fixed* number depending
on the ambient dimension alone, chosen before any scale — so `1 ≤ C` is
`ShadedTube.one_le_ssfUniformConst` and `C ≤ σ^{-ηd}` is pure absorption of a constant into a
negative power, `Kakeya.ML2Reduction.exists_threshold_const_le_rpow_neg`.  No hypothesis about
`β`, `ϖ`, the window, the hierarchy upstairs, or the geometry of the family enters.  In particular
the bound is *not* forced by any relation between `ηd` and the dimension: it is forced by
smallness of `σ`, and if `ηd` were allowed to be `0` the binder would demand `C ≤ 1`, which
`ssfUniformConst n ≥ 4` refutes.  `hηd : 0 < ηd` is therefore load-bearing and cannot be dropped.
-/

@[expose] public section

open MeasureTheory Metric Set Topology Filter ShadedBody ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Reduction

universe u

/-! ## Absorbing a fixed constant into a negative power of the scale -/

/-- **A constant fixed before the scale is below `σ^{-κ}` for all small `σ`.**  The general form of
`Kakeya.ML2Reduction.exists_threshold_outerLoss`, whose proof this is verbatim with `outerLoss R`
replaced by an arbitrary `C ≥ 1`. -/
theorem exists_threshold_const_le_rpow_neg {C : ℝ≥0} (hC : 1 ≤ C) {κ : ℝ} (hκ : 0 < κ) :
    ∃ σ₀ : ℝ≥0, 0 < σ₀ ∧ ∀ σ : ℝ≥0, 0 < σ → σ ≤ σ₀ → C ≤ σ ^ (-κ) := by
  have hC0 : C ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hC)
  have hinv0 : (0 : ℝ≥0) < C⁻¹ := pos_of_ne_zero (inv_ne_zero hC0)
  refine ⟨(C⁻¹) ^ (1 / κ), NNReal.rpow_pos hinv0, ?_⟩
  intro σ hσ0 hσle
  have hpow : σ ^ κ ≤ C⁻¹ := by
    calc σ ^ κ ≤ ((C⁻¹) ^ (1 / κ)) ^ κ := NNReal.rpow_le_rpow hσle hκ.le
      _ = C⁻¹ ^ (1 / κ * κ) := (NNReal.rpow_mul _ _ _).symm
      _ = C⁻¹ := by rw [one_div, inv_mul_cancel₀ (ne_of_gt hκ), NNReal.rpow_one]
  have hmul : σ ^ κ * C ≤ 1 := by
    calc σ ^ κ * C ≤ C⁻¹ * C := mul_le_mul_left hpow _
      _ = 1 := inv_mul_cancel₀ hC0
  rw [NNReal.rpow_neg]
  exact le_inv_of_mul_le_one (ne_of_gt (NNReal.rpow_pos hσ0)) hmul

/-- The `ENNReal` reading of `Kakeya.ML2Reduction.exists_threshold_const_le_rpow_neg`, which is the
form the `huni` binder of `Kakeya.ML2Reduction.Lemma91At` states. -/
theorem exists_threshold_coe_const_le_rpow_neg {C : ℝ≥0} (hC : 1 ≤ C) {κ : ℝ} (hκ : 0 < κ) :
    ∃ σ₀ : ℝ≥0, 0 < σ₀ ∧ ∀ σ : ℝ≥0, 0 < σ → σ ≤ σ₀ →
      (C : ENNReal) ≤ (σ : ENNReal) ^ (-κ) := by
  obtain ⟨σ₀, hσ₀, h⟩ := exists_threshold_const_le_rpow_neg hC hκ
  refine ⟨σ₀, hσ₀, fun σ hσ0 hσle => ?_⟩
  have h' := ENNReal.coe_le_coe.mpr (h σ hσ0 hσle)
  rwa [ENNReal.coe_rpow_of_ne_zero (ne_of_gt hσ0)] at h'

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]

/-! ## The uniformity witness on an arbitrary family of shaded tubes -/

/-- **The `huni` binder of GWZ Lemma 9.1, built at a threshold.**

Below a threshold depending only on `(K₀, α, α', ηd)` — not on the family, the index type or the
scale — every finite family `U` of `σ`-shaded tubes in `B₁` of cardinality at most `σ^{-K₀}` has a
subfamily `s' ⊆ s` and a shade refinement `U'` carrying a
`ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen σ) C` with `1 ≤ C ≤ σ^{-ηd}`, at count loss
`σ^{-α}` and fullness loss `σ^{-α'}`.

This is `ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` with its fixed constant
`ShadedTube.ssfUniformConst (Module.finrank ℝ E)` absorbed into `σ^{-ηd}`.  The three positivity
hypotheses are each load-bearing and for different reasons: `hα` and `hα'` are the two exponents
the builder's polylogarithmic losses are absorbed into (they are separate budgets, one for the
count and one for the fullness), and `hηd` is what makes the constant absorbable at all — see the
module docstring.

The conclusion is stated with the `∃ C, 1 ≤ C ∧ … ∧ Nonempty …` conjunction spelled out rather
than as a named predicate: it is the binder of `Kakeya.ML2Reduction.Lemma91At` character for
character, so a consumer discharges that binder by `exact`. -/
theorem exists_threshold_shadedUniformTubeSet_ssf (K₀ : ℕ) (α α' ηd : ℝ)
    (hα : 0 < α) (hα' : 0 < α') (hηd : 0 < ηd) :
    ∃ σ₀ : ℝ≥0, 0 < σ₀ ∧ σ₀ ≤ 1 ∧
      ∀ {ι : Type u} {σ : ℝ≥0}, 0 < σ → σ ≤ σ₀ →
      ∀ (s : Finset ι) (U : ι → ShadedTube σ E),
      (∀ i ∈ s, (U i).carrier ⊆ closedBall (0 : E) 1) →
      (s.card : ℝ) ≤ (σ : ℝ) ^ (-(K₀ : ℝ)) →
      ∃ s' ⊆ s, ∃ U' : ι → ShadedTube σ E,
        (∀ i, (U' i).toTube = (U i).toTube) ∧
        (∀ i, (U' i).shade ⊆ (U i).shade) ∧
        (s.card : ℝ) ≤ (σ : ℝ) ^ (-α) * (s'.card : ℝ) ∧
        ShadedBody.fullness' s' (fun i => (U i).toShadedBody)
            ≤ ENNReal.ofReal ((σ : ℝ) ^ (-α'))
              * ShadedBody.fullness' s' (fun i => (U' i).toShadedBody) ∧
        (∃ C : ℝ≥0, 1 ≤ C ∧ (C : ENNReal) ≤ (σ : ENNReal) ^ (-ηd) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen σ) C)) := by
  obtain ⟨σ₁, hσ₁pos, hσ₁le1, hbuild⟩ :=
    ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf (E := E) K₀ α α' hα hα'
  obtain ⟨σ₂, hσ₂pos, habs⟩ :=
    exists_threshold_coe_const_le_rpow_neg
      (ShadedTube.one_le_ssfUniformConst (Module.finrank ℝ E)) hηd
  refine ⟨min (min σ₁ σ₂) 1, lt_min (lt_min hσ₁pos hσ₂pos) one_pos, min_le_right _ _, ?_⟩
  intro ι σ hσ0 hσle s U hball hcard
  have hσ₁ : σ ≤ σ₁ := le_trans hσle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hσ₂ : σ ≤ σ₂ := le_trans hσle (le_trans (min_le_left _ _) (min_le_right _ _))
  obtain ⟨s', hs'sub, U', hUto, hUshade, hUcard, hUfull, hUstruct⟩ :=
    hbuild (ι := ι) (δ := σ) hσ0 hσ₁ s U hball hcard
  exact ⟨s', hs'sub, U', hUto, hUshade, hUcard, hUfull,
    ShadedTube.ssfUniformConst (Module.finrank ℝ E),
    ShadedTube.one_le_ssfUniformConst _, habs σ hσ0 hσ₂, hUstruct⟩

/-! ## What a tube-preserving shade refinement transports for free

The builder above shrinks shades and keeps tubes.  Every hypothesis of
`Kakeya.ML2Reduction.Lemma91At` that reads only the *carrier* is therefore unchanged, and these
three one-line lemmas are the ones a consumer needs in order to say so.  They are separated out
because each is used at a different hypothesis of Lemma 9.1 and because stating them keeps the
interface note of `Kakeya.ML2Reduction.exists_outerShadedUniformTubeSet` checkable rather than
merely asserted. -/

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- A shade refinement that keeps the tubes keeps the convex bodies. -/
theorem toConvexSpaceBody_eq_of_toTube_eq {ι : Type*} {σ : ℝ≥0} {U U' : ι → ShadedTube σ E}
    (h : ∀ i, (U' i).toTube = (U i).toTube) (i : ι) :
    (U' i).toConvexSpaceBody = (U i).toConvexSpaceBody := by
  rw [show (U' i).toConvexSpaceBody = ((U' i).toTube).toConvexSpaceBody from rfl,
    show (U i).toConvexSpaceBody = ((U i).toTube).toConvexSpaceBody from rfl, h i]

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- …and the carriers, hence the unit-ball containment of Lemma 9.1's first hypothesis, on any
subfamily. -/
theorem carrier_subset_closedBall_of_toTube_eq {ι : Type*} {σ : ℝ≥0} {U U' : ι → ShadedTube σ E}
    (h : ∀ i, (U' i).toTube = (U i).toTube) {s s' : Finset ι} (hs : s' ⊆ s)
    (hball : ∀ i ∈ s, (U i).carrier ⊆ closedBall (0 : E) 1) :
    ∀ i ∈ s', (U' i).carrier ⊆ closedBall (0 : E) 1 := by
  intro i hi
  rw [show (U' i).carrier = ((U' i).toTube).carrier from rfl, h i]
  exact hball i (hs hi)

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- …and therefore `Δ_max`, which reads carriers only.  With `Kakeya.maxDensity_mono` this is what
carries Lemma 9.1's `Δ_max` hypothesis from `(s, U)` to `(s', U')` with **no** loss. -/
theorem maxDensity_eq_of_toTube_eq {ι : Type*} {σ : ℝ≥0} {U U' : ι → ShadedTube σ E}
    (h : ∀ i, (U' i).toTube = (U i).toTube) (s : Finset ι) :
    Kakeya.maxDensity s (fun i => (U' i).toConvexSpaceBody)
      = Kakeya.maxDensity s (fun i => (U i).toConvexSpaceBody) := by
  have : (fun i => (U' i).toConvexSpaceBody) = fun i => (U i).toConvexSpaceBody := by
    funext i
    exact toConvexSpaceBody_eq_of_toTube_eq h i
  rw [this]

/-! ## The instance on the outer family of step 10 -/

/-- **The outer uniformiser at its OWN constant**.

Additive sibling of `Kakeya.ML2Reduction.exists_outerShadedUniformTubeSet`, which is byte-untouched
below.  The difference is one step: the existing form absorbs the builder's fixed constant into
`σ^{-ηd}` (its own docstring, "with its fixed constant `ShadedTube.ssfUniformConst
(Module.finrank ℝ E)` absorbed into `σ^{-ηd}`"), and this one does not, so it has **no `ηd`
parameter at all**.

That absorption is the root cause the centring line spent a reading gap on: the builder
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` returns
`ShadedTube.ssfUniformConst (Module.finrank ℝ E)` **by name and unquantified**, a number in the
ambient dimension alone (`Kakeya/Uniform.lean:439`, `Kakeya/ShadedUniform.lean:895`), and the
`δ`-dependence of the whole statement is confined to the threshold `σ₀`.  A consumer that names the
constant pays nothing; a consumer that reads `∃ C ≤ σ^{-ηd}` pays `ηd` for a fact it already had.

The existing theorem is this one with the constant re-absorbed by
`ShadedTube.one_le_ssfUniformConst` and `hηd`; it is not re-proved through this sibling. -/
theorem exists_outerShadedUniformTubeSet_ssf (K₀ : ℕ) (α α' : ℝ)
    (hα : 0 < α) (hα' : 0 < α') :
    ∃ σ₀ : ℝ≥0, 0 < σ₀ ∧ σ₀ ≤ 1 ∧
      ∀ {ι : Type u} {θ τ σ : ℝ≥0} {R : ℝ}, 0 < σ → σ ≤ σ₀ →
      Module.finrank ℝ E = 3 →
      ∀ (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R),
      (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ) →
      ∀ (T₀ : Tube θ E) (s : Finset ι) (𝕋 : ι → ShadedTube τ E),
      (∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier) →
      (s.card : ℝ) ≤ (σ : ℝ) ^ (-(K₀ : ℝ)) →
      ∃ s' ⊆ s, ∃ U' : ι → ShadedTube σ E,
        (∀ i, (U' i).toTube = (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toTube) ∧
        (∀ i, (U' i).shade ⊆ (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).shade) ∧
        (s.card : ℝ) ≤ (σ : ℝ) ^ (-α) * (s'.card : ℝ) ∧
        ShadedBody.fullness' s'
              (fun i => (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toShadedBody)
            ≤ ENNReal.ofReal ((σ : ℝ) ^ (-α'))
              * ShadedBody.fullness' s' (fun i => (U' i).toShadedBody) ∧
        Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen σ)
          (ShadedTube.ssfUniformConst (Module.finrank ℝ E))) := by
  obtain ⟨σ₀, hσ₀pos, hσ₀le1, hbuild⟩ :=
    ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf (E := E) K₀ α α' hα hα'
  refine ⟨σ₀, hσ₀pos, hσ₀le1, ?_⟩
  intro ι θ τ σ R hσ0 hσle hn hsit hR hτσ T₀ s 𝕋 hsub hcard
  exact hbuild (ι := ι) (δ := σ) hσ0 hσle s (outerFamily hsit.pos_ambient T₀ hR σ 𝕋)
    (outerFamily_carrier_subset_closedBall hn hsit hR hτσ hsub) hcard

/-- **The uniformity witness on the outer family** (blueprint step 10, the `huni` binder of
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer`).

`Kakeya.ML2Reduction.exists_threshold_shadedUniformTubeSet_ssf` applied to
`Kakeya.ML2Reduction.outerFamily`, whose unit-ball hypothesis is
`Kakeya.ML2Reduction.outerFamily_carrier_subset_closedBall` — and that is the *only* place `hsub`
enters this file.

**Interface note for the consuming rows (this is the statement mismatch to plan for).**  The
witness produced here lives on `(s', U')`, a subfamily with a shrunk shading, and **not** on
`(s, outerFamily … 𝕋)`.  So it does *not* discharge the `huni` binder of
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer`, whose binder is pinned to
`outerFamily hsit.pos_ambient T₀ hR σ 𝕋` on the whole of `s`.  A consumer must instead apply
`Kakeya.ML2Reduction.Lemma91At` — which quantifies over an *arbitrary* family of `σ`-shaded tubes,
so `(s', U')` is a legal argument — and transport the conclusion back across the two retentions.
Three of Lemma 9.1's five hypotheses transport to `(s', U')` for free, because `U'` has the *same
tubes*: the unit-ball containment
(`Kakeya.ML2Reduction.carrier_subset_closedBall_of_toTube_eq`), the `Δ_max` bound
(`Kakeya.ML2Reduction.maxDensity_eq_of_toTube_eq`, an equality, and `Δ_max` is monotone under
passing to `s' ⊆ s`), and the `ρ`-tube count clause
(`Kakeya.ML2Reduction.toConvexSpaceBody_eq_of_toTube_eq`, since "used" is a statement about
carriers).  Only the fullness floor and the multiplicity conclusion read shades, and those are
exactly the two the retentions above are for. -/
theorem exists_outerShadedUniformTubeSet (K₀ : ℕ) (α α' ηd : ℝ)
    (hα : 0 < α) (hα' : 0 < α') (hηd : 0 < ηd) :
    ∃ σ₀ : ℝ≥0, 0 < σ₀ ∧ σ₀ ≤ 1 ∧
      ∀ {ι : Type u} {θ τ σ : ℝ≥0} {R : ℝ}, 0 < σ → σ ≤ σ₀ →
      Module.finrank ℝ E = 3 →
      ∀ (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R),
      (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ) →
      ∀ (T₀ : Tube θ E) (s : Finset ι) (𝕋 : ι → ShadedTube τ E),
      (∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier) →
      (s.card : ℝ) ≤ (σ : ℝ) ^ (-(K₀ : ℝ)) →
      ∃ s' ⊆ s, ∃ U' : ι → ShadedTube σ E,
        (∀ i, (U' i).toTube = (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toTube) ∧
        (∀ i, (U' i).shade ⊆ (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).shade) ∧
        (s.card : ℝ) ≤ (σ : ℝ) ^ (-α) * (s'.card : ℝ) ∧
        ShadedBody.fullness' s'
              (fun i => (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toShadedBody)
            ≤ ENNReal.ofReal ((σ : ℝ) ^ (-α'))
              * ShadedBody.fullness' s' (fun i => (U' i).toShadedBody) ∧
        (∃ C : ℝ≥0, 1 ≤ C ∧ (C : ENNReal) ≤ (σ : ENNReal) ^ (-ηd) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen σ) C)) := by
  obtain ⟨σ₀, hσ₀pos, hσ₀le1, hmain⟩ :=
    exists_threshold_shadedUniformTubeSet_ssf (E := E) K₀ α α' ηd hα hα' hηd
  refine ⟨σ₀, hσ₀pos, hσ₀le1, ?_⟩
  intro ι θ τ σ R hσ0 hσle hn hsit hR hτσ T₀ s 𝕋 hsub hcard
  exact hmain (ι := ι) (σ := σ) hσ0 hσle s (outerFamily hsit.pos_ambient T₀ hR σ 𝕋)
    (outerFamily_carrier_subset_closedBall hn hsit hR hτσ hsub) hcard

/-! ## The site supplier: the folded `huni` and the grid threshold, at `∀ params, ∀ᶠ δ`

 R1/R3.  The six middle-factor sites now name their uniformity
constant, and the two facts they cannot carry themselves — the absorption
`ssfUniformConst 3 ≤ δ'^{-ηd}` and the uniformiser's grid threshold `δ' ≤ 16^{-N}` — are both
**thresholds in the scale at fixed parameters**.  This section supplies both, together with the
subfamily, under one `∀ᶠ σ`.

**and it is the whole point of the shape.**  The parameters are theorem binders and the
scale is quantified *inside* the conclusion, i.e. `∀ β, ∀ᶠ δ`.  The reverse reading `∀ᶠ δ, ∀ β`
is not a stylistic variant: it is **false**, and
`Kakeya.ML2Reduction.not_eventually_forall_etad` below compiles that refutation, so a future
re-cut that swaps the two quantifiers cannot pass unnoticed. -/

/-- **firing control: the swapped quantifier order is FALSE.**

No single threshold on the scale serves *every* `ηd > 0`: at any fixed `σ ∈ (0,1)` the value
`σ^{-ηd}` tends to `1` as `ηd → 0⁺`, while `ShadedTube.ssfUniformConst 3 ≥ 4`.  The witness is
explicit — `ηd := log 2 / log(1/σ)` makes `σ^{-ηd} = 2` on the nose — so this is a refutation, not
a non-constructive limit argument.

This is the statement `Kakeya.ML2Reduction.eventually_outerHuni_ssf` would have if its `ηd`
binder were pushed inside the `∀ᶠ`; it is recorded here so that the order in that theorem is
*checked* rather than merely intended. -/
theorem not_eventually_forall_etad :
    ¬ (∀ᶠ σ : ℝ≥0 in 𝓝[>] 0, ∀ ηd : ℝ, 0 < ηd →
        ((ShadedTube.ssfUniformConst 3 : ℝ≥0) : ENNReal) ≤ (σ : ENNReal) ^ (-ηd)) := by
  intro h
  obtain ⟨σ, hσ, hσmem⟩ := (h.and (Ioc_mem_nhdsGT (show (0:ℝ≥0) < 1/2 by norm_num))).exists
  obtain ⟨hσ0, hσhalf⟩ := hσmem
  have hσ0' : (0:ℝ) < (σ:ℝ) := by exact_mod_cast hσ0
  have hσlt1 : (σ:ℝ) < 1 := by
    have : (σ:ℝ) ≤ 1/2 := by exact_mod_cast hσhalf
    linarith
  set L : ℝ := Real.log (σ:ℝ) with hL
  have hLneg : L < 0 := Real.log_neg hσ0' hσlt1
  set ηd : ℝ := Real.log 2 / (-L) with hηd
  have hηd0 : 0 < ηd := by
    apply div_pos (Real.log_pos (by norm_num)) (by linarith)
  have hval : (σ:ℝ) ^ (-ηd) = 2 := by
    rw [Real.rpow_def_of_pos hσ0']
    have hLne : L ≠ 0 := ne_of_lt hLneg
    have : L * (-ηd) = Real.log 2 := by
      rw [hηd]; field_simp
    rw [← hL, this, Real.exp_log (by norm_num)]
  have hk := hσ ηd hηd0
  rw [show ((σ : ENNReal) ^ (-ηd)) = ENNReal.ofReal ((σ:ℝ) ^ (-ηd)) from ?_] at hk
  · rw [hval] at hk
    have h4 : (4:ℝ≥0) ≤ ShadedTube.ssfUniformConst 3 := by
      unfold ShadedTube.ssfUniformConst; exact le_max_right _ _
    have : ((4:ℝ≥0) : ENNReal) ≤ ENNReal.ofReal (2:ℝ) := le_trans (by exact_mod_cast h4) hk
    rw [show ENNReal.ofReal (2:ℝ) = (2:ENNReal) by simp [ENNReal.ofReal_ofNat]] at this
    norm_num at this
  · rw [← ENNReal.coe_rpow_of_ne_zero (ne_of_gt hσ0)]
    rw [ENNReal.ofReal]
    congr 1
    ext
    simp [NNReal.coe_rpow]
    positivity

/-- **The site's uniformity supplier**.

Below a threshold that depends only on `(K₀, α, α', ηd)`, the outer family of step 10 admits a
subfamily `s'` and a shade refinement `U'` carrying

* the two retention rows (count `σ^{-α}`, fullness `σ^{-α'}`), unchanged;
* the **folded `huni` conjunct** of the six middle-factor sites, at the *named* absolute constant
  `ShadedTube.ssfUniformConst 3` — the form  specified;
* the uniformiser's own grid threshold `σ ≤ 16^{-ssfGridLen σ}`, which is the one input of the
  levels datum (`Kakeya.VeryNotSticky.lineEDLevelsAt_C3_of_huni`) that no site carries.

Both thresholds live under **one** `∀ᶠ σ`, so a site pays a single threshold for the pair.

**Why the two facts travel together.**   folded the absorption into `huni`
precisely so that the two halves cannot be separated and then re-paired at different scales
(V-3/); the same argument applies to the grid threshold, which is read at the *same* `σ` by
the same witness.  Splitting them into two `∀ᶠ`s would be sound but would re-open the pairing
hazard at the wiring site, so they are one conjunction here. -/
theorem eventually_outerHuni_ssf (K₀ : ℕ) (α α' ηd : ℝ)
    (hα : 0 < α) (hα' : 0 < α') (hηd : 0 < ηd) :
    ∀ᶠ σ : ℝ≥0 in 𝓝[>] 0,
      0 < σ ∧
      σ ≤ (16 : ℝ≥0) ^ (-(Tube.ssfGridLen σ : ℝ)) ∧
      ∀ {ι : Type u} {θ τ : ℝ≥0} {R : ℝ},
      Module.finrank ℝ E = 3 →
      ∀ (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R),
      (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ) →
      ∀ (T₀ : Tube θ E) (s : Finset ι) (𝕋 : ι → ShadedTube τ E),
      (∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier) →
      (s.card : ℝ) ≤ (σ : ℝ) ^ (-(K₀ : ℝ)) →
      ∃ s' ⊆ s, ∃ U' : ι → ShadedTube σ E,
        (∀ i, (U' i).toTube = (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toTube) ∧
        (∀ i, (U' i).shade ⊆ (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).shade) ∧
        (s.card : ℝ) ≤ (σ : ℝ) ^ (-α) * (s'.card : ℝ) ∧
        ShadedBody.fullness' s'
              (fun i => (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toShadedBody)
            ≤ ENNReal.ofReal ((σ : ℝ) ^ (-α'))
              * ShadedBody.fullness' s' (fun i => (U' i).toShadedBody) ∧
        (((ShadedTube.ssfUniformConst 3 : ℝ≥0) : ENNReal) ≤ (σ : ENNReal) ^ (-ηd) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen σ)
            (ShadedTube.ssfUniformConst 3))) := by
  obtain ⟨σ₁, hσ₁0, hσ₁1, hbuild⟩ :=
    exists_outerShadedUniformTubeSet_ssf.{u} (E := E) K₀ α α' hα hα'
  obtain ⟨σ₂, hσ₂0, habs⟩ :=
    exists_threshold_coe_const_le_rpow_neg (ShadedTube.one_le_ssfUniformConst 3) hηd
  obtain ⟨σ₃, hσ₃0, hσ₃1, hgrid⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le 1 le_rfl 0 1 1 one_pos
  filter_upwards [Ioc_mem_nhdsGT hσ₁0, Ioc_mem_nhdsGT hσ₂0, Ioc_mem_nhdsGT hσ₃0]
    with σ h1 h2 h3
  obtain ⟨hσ0, hσ₁le⟩ := h1
  obtain ⟨-, hσ₂le⟩ := h2
  obtain ⟨-, hσ₃le⟩ := h3
  refine ⟨hσ0, (hgrid hσ0 hσ₃le).2.1, ?_⟩
  intro ι θ τ R hn hsit hR hτσ T₀ s 𝕋 hsub hcard
  obtain ⟨s', hs', U', hto, hshade, hcardle, hfull, huni⟩ :=
    hbuild (ι := ι) hσ0 hσ₁le hn hsit hR hτσ T₀ s 𝕋 hsub hcard
  rw [hn] at huni
  exact ⟨s', hs', U', hto, hshade, hcardle, hfull, habs σ hσ0 hσ₂le, huni⟩

/-- **The supplier's filter is not trivial**, so `Filter.Eventually.exists` applies to
`Kakeya.ML2Reduction.eventually_outerHuni_ssf` and it really does produce a scale.  Recorded
because a `∀ᶠ` over `⊥` would make the whole section content-free — the same V-2 question the run
asks of every new Prop, asked of a filter. -/
theorem nhdsGT_zero_neBot : (𝓝[>] (0 : ℝ≥0)).NeBot := by infer_instance

/-- **…and the grid-threshold half is realised at an explicit scale**, so neither conjunct of the
supplier's conclusion is vacuously carried.  (The `huni` half is realised by the same `σ`; it is
not restated here because its statement is the supplier's own conclusion.) -/
theorem exists_scale_grid_threshold :
    ∃ σ : ℝ≥0, 0 < σ ∧ σ ≤ (16 : ℝ≥0) ^ (-(Tube.ssfGridLen σ : ℝ)) := by
  obtain ⟨σ₀, hσ₀0, -, hgrid⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le 1 le_rfl 0 1 1 one_pos
  exact ⟨σ₀, hσ₀0, (hgrid hσ₀0 le_rfl).2.1⟩

end General

end Kakeya.ML2Reduction

end
