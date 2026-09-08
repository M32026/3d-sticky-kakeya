/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.PartialEstimates
public import Kakeya.Sticky
public import Kakeya.DimensionThree.CardBound
public import Kakeya.DimensionThree.MainLemma1.FrostmanAtEveryScaleCase

/-!
# Main Lemma 1: the parameter package and the sticky case

This file sets up Section 8 of the adapted blueprint
(`GWZAdapted/section8_setup.tex`).  It contains

* the reduction to a strictly positive Katz–Tao exponent
  `β'(γ) = max β (γ / 2)` (blueprint `lem:ml1bootBetaPrime`), split into its two
  `E`-free arithmetic clauses `Kakeya.ml1Boot.betaPrime_spec`,
  `Kakeya.ml1Boot.gap_spec` and the monotonicity clause
  `Kakeya.ml1Boot.katzTaoEstimate_betaPrime`;
* the parameter package
  `c_{8.1}(β, γ₀) = (η⋆, δ₀, N, ε, κ, (η_j), ε', η(·), c)`
  (`Kakeya.ml1Boot.params`, blueprint `def:ml1bootParams`) together with its two
  specification lemmas `Kakeya.ml1Boot.params_spec` (blueprint
  `lem:ml1bootParamsSpec`) and `Kakeya.ml1Boot.etaGamma_spec` (blueprint
  `lem:ml1bootEtaGamma`);
* Case (i) of the sticky/non-sticky dichotomy
  (`Kakeya.ml1Boot.multiplicity_le_of_frostmanAtEveryScale`, blueprint
  `lem:ml1bootCaseSticky`).

The sharp count of essentially distinct `δ`-tubes in `B₁ ⊆ ℝ³` that Case (i) consumes
(`Kakeya.ml1Boot.card_le`, blueprint `lem:ml1bootCardBound`) has moved to its own module
`Kakeya.DimensionThree.CardBound`, which this file re-exports.

## The shape of the parameter package

Items (i) and (v) of blueprint Definition `def:ml1bootParams` are *outputs of other
theorems*: `(η⋆, δ₀)` comes from
`StickyKakeya.volume_iUnionShade_ge_of_isFrostmanAtEveryScale`, and the two thresholds
`η♯^{K_F}`, `η♯^{K_KT}` come from `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale`
and `Kakeya.KatzTaoEstimate.multiplicity_bound`. We therefore take them as explicit arguments: `Kakeya.ml1Boot.params` is a genuine
closed-form function of `β`, `γ₀`, `η⋆`, `δ₀` and the two threshold functions, and the
hypotheses that those arguments really are the outputs in question appear in the
specification lemmas that consume them.

Items (ii)–(iv) are then literal formulas: `N` is a ceiling, `ε = 1 / √N`, and the ladder
`(η_j)` is the *geometric* ladder `η_j = κ ^ (N - j + 1)` of item (iii), implemented as the
upward power `Kakeya.ml1Boot.etaLadder` read backwards (`η_j = etaLadder κ (N - j)`).
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

universe u

namespace ml1Boot

/-! ### Reduction to a positive Katz–Tao exponent -/

/-- The shifted Katz–Tao exponent `β'(γ) = max β (γ / 2)` of blueprint
`lem:ml1bootBetaPrime`.  It is strictly positive whenever `γ > 0` and still strictly
below `γ`, and `K_KT(β)` implies `K_KT(β'(γ))`. -/
noncomputable def betaPrime (β γ : ℝ) : ℝ := max β (γ / 2)

/-- The exponent gap `g(γ) = γ - β'(γ) = min (γ - β) (γ / 2)` of blueprint
`lem:ml1bootBetaPrime`(ii).  The whole of Section 8 divides by this quantity, which is why
`β` is replaced by `β'` in the first place. -/
noncomputable def gap (β γ : ℝ) : ℝ := γ - betaPrime β γ

/-- **The shifted exponent is positive and still below `γ`** (blueprint
`lem:ml1bootBetaPrime`(i)).

For `0 ≤ β < 1` and `γ ∈ (β, 1]` one has `0 < β'(γ) < γ`.  This is real arithmetic; it does
not mention the ambient space, which is why it is stated outside the `E`-parameterized
section. -/
theorem betaPrime_spec {β : ℝ} (hβ0 : 0 ≤ β) :
    ∀ γ ∈ Set.Ioc β 1, 0 < betaPrime β γ ∧ betaPrime β γ < γ := by
  intro γ hγ
  have hβγ : β < γ := hγ.1
  have hγ0 : 0 < γ := lt_of_le_of_lt hβ0 hβγ
  refine ⟨?_, ?_⟩
  · dsimp [betaPrime]
    exact lt_of_lt_of_le (by positivity : 0 < γ / 2) (le_max_right β (γ / 2))
  · dsimp [betaPrime]
    exact max_lt hβγ (by nlinarith)

/-- **The exponent gap** (blueprint `lem:ml1bootBetaPrime`(ii)).

The gap `g(γ) = γ - β'(γ)` equals `min (γ - β) (γ / 2)`, is strictly positive on `(β, 1]`,
and is monotone increasing there; in particular `g(γ) ≥ g(γ₀) = gap β γ₀` for every
`γ ∈ [γ₀, 1]`, which is the form in which the whole of Section 8 uses it.  Like
`Kakeya.ml1Boot.betaPrime_spec` this is `E`-free real arithmetic. -/
theorem gap_spec {β : ℝ} (hβ0 : 0 ≤ β) :
    (∀ γ, gap β γ = min (γ - β) (γ / 2)) ∧
      (∀ γ ∈ Set.Ioc β 1, 0 < gap β γ) ∧
      MonotoneOn (gap β) (Set.Ioc β 1) := by
  have hgap : ∀ γ, gap β γ = min (γ - β) (γ / 2) := by
    intro γ
    dsimp [gap, betaPrime]
    by_cases h : β ≤ γ / 2
    · have hmax : max β (γ / 2) = γ / 2 := max_eq_right h
      have hmin : min (γ - β) (γ / 2) = γ / 2 := min_eq_right (by linarith)
      rw [hmax, hmin]
      ring
    · have hβ_le : γ / 2 ≤ β := le_of_not_ge h
      have hmax : max β (γ / 2) = β := max_eq_left hβ_le
      have hmin : min (γ - β) (γ / 2) = γ - β := min_eq_left (by linarith)
      rw [hmax, hmin]
  refine ⟨hgap, ?_, ?_⟩
  · intro γ hγ
    rw [hgap]
    have hβγ : β < γ := hγ.1
    have hγ0 : 0 < γ := lt_of_le_of_lt hβ0 hβγ
    have hgβ : 0 < γ - β := by linarith
    exact (by positivity : 0 < min (γ - β) (γ / 2))
  · intro a ha b hb hab
    rw [hgap, hgap]
    refine min_le_min ?_ ?_
    · linarith
    · nlinarith

section BetaPrime

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Reduction to a positive Katz–Tao exponent** (blueprint `lem:ml1bootBetaPrime`(iii)):
`K_KT(β)` implies `K_KT(β'(γ))` for every `γ ∈ (β, 1]`.

This is the only clause of the blueprint lemma that mentions the ambient space; the two
arithmetic clauses (i) and (ii) are `Kakeya.ml1Boot.betaPrime_spec` and
`Kakeya.ml1Boot.gap_spec`.  It is the monotonicity of `Kakeya.KatzTaoEstimate` in its
exponent applied to `β ≤ β'(γ)`. -/
theorem katzTaoEstimate_betaPrime {β : ℝ} :
    ∀ γ ∈ Set.Ioc β 1,
      KatzTaoEstimate.{u} E β → KatzTaoEstimate.{u} E (betaPrime β γ) := by
  intro γ hγ hK
  apply KatzTaoEstimate.mono
  · dsimp [betaPrime]
    exact le_max_left β (γ / 2)
  · exact hK

end BetaPrime

/-! ### The parameter package -/

/-- The ladder `(η_j)_{j = 0}^{N}` of blueprint `def:ml1bootParams`(iii), read *upwards*:
`etaLadder κ k` is the blueprint's `η_{N - k}`.

The ladder is *geometric* with ratio `κ = ε² β₀ g₀ / 100`: the blueprint prescribes
`η_N = κ` and `η_j = κ ^ (N - j) η_N = κ ^ (N - j + 1)`, so that `η_{j-1} = κ η_j` for
`1 ≤ j ≤ N`.  In the upward indexing this is the bare power `etaLadder κ k = κ ^ (k + 1)`.

This replaces the earlier downward recursion
`η_N = ε / 5`, `η_{j-1} = min (ε² γ₀ η_j / 60) (ε γ₀ g₀ / 400) (η_j)`.  The change is one of
*shape*, not of numerals: the induction proving `Kakeya.ml1Boot.params_spec`(ii) becomes the
antitonicity of `k ↦ κ ^ k` for `0 < κ ≤ 1`, and the two bounds of
`Kakeya.ml1Boot.params_spec`(iii) become one-line computations, because on the geometric
ladder `10 η_{j-1} / (ε β₀) = ε g₀ η_j / 10` exactly rather than up to a case analysis over a
minimum. -/
noncomputable def etaLadder (κ : ℝ) (k : ℕ) : ℝ := κ ^ (k + 1)

/-- The number `N` of scales of blueprint `def:ml1bootParams`(ii): the least integer with
`N ≥ max 4096 ((20 / η⋆) ^ 2) ((96 / g₀) ^ 2)`, so that `ε = 1 / √N` satisfies
`ε ≤ 1 / 64`, `20 ε ≤ η⋆` and `96 ε ≤ g₀`.

* `N ≥ 4096` is the threshold that `StickyKakeya.dividingScalesFrostman` imposes.  In that
  statement `N` no longer indexes the grid — the hierarchy lives on the grid of length
  `Tube.ssfGridLen δ` — and bounds the exponent index alone.
* `N ≥ (20 / η⋆) ^ 2` delivers GWZ's `5 ε ≤ η⋆ / 4`; the earlier `N ≥ 25 / η⋆ ^ 2` gave only
  `5 ε ≤ η⋆`.
* `N ≥ (96 / g₀) ^ 2` was `32 ε ≤ g₀` in earlier versions.  It is tripled because the middle
  factor now factors at the parent scale `δ̃ ^ (6 ε)` rather than `δ̃ ^ (2 ε)`, which triples
  the density exponent of `Kakeya.ml1Boot.maxDensity_coarse_le_rpow`, which is now
  `30 ε + η'_{j-1}`: that lemma reads the parent count at `ρ ^ (-5)`, so the exponent is `5`
  times the parent scale's `6 ε`.  See blueprint `note:ml1bootWindowConsumers`(3).  Since
  `g₀ ≤ 1/2` this forces `N ≥ 192 ^ 2 = 36864`.

The gap here is `g₀ = γ₀ - β'(γ₀)` and not `γ₀ - β`; see blueprint
`note:ml1bootBetaZeroFixed`. -/
noncomputable def paramsN (β γ₀ ηStar : ℝ) : ℕ :=
  max 4096 ⌈max ((20 / ηStar) ^ 2) ((96 / gap β γ₀) ^ 2)⌉₊

/-- **The parameter package** `c_{8.1}(β, γ₀)` of blueprint `def:ml1bootParams`: the
threshold `η⋆` and scale `δ₀` of the sticky Kakeya theorem, the number `N` of scales, the
loss exponent `ε = 1 / √N`, the ladder `(η_j)_{j ≤ N}` and the `γ`-dependent fullness
threshold `η(·)`.

The fields carry no proofs; the properties asserted by the blueprint definition are the
content of `Kakeya.ml1Boot.params_spec` and `Kakeya.ml1Boot.etaGamma_spec`. -/
structure Params where
  /-- The fullness / Frostman-at-every-scale threshold `η⋆` of the sticky Kakeya theorem. -/
  ηStar : ℝ
  /-- The scale threshold `δ₀` of the sticky Kakeya theorem. -/
  δ₀ : NNReal
  /-- The number `N` of scales. -/
  N : ℕ
  /-- The loss exponent `ε = 1 / √N`. -/
  ε : ℝ
  /-- The ladder ratio `κ = ε² β₀ g₀ / 100` of blueprint `def:ml1bootParams`(iii), where
  `β₀ = β'(γ₀)` and `g₀ = γ₀ - β₀`.  It is positive because `β₀ > 0`, and it is far below `ε`;
  the blueprint's geometric ladder is `η_j = κ ^ (N - j + 1)`.  See
  `Kakeya.ml1Boot.Params.Spec` for what the present package asserts about it. -/
  κ : ℝ
  /-- The ladder `(η_j)_{j ≤ N}`; the values at `j > N` are irrelevant. -/
  η : ℕ → ℝ
  /-- The bookkeeping accuracy `ε' = η₀ / 16` of blueprint `def:ml1bootParams`(iv): the
  exponent at which `Kakeya.ml1Boot.exists_caseTwoData` and
  `Kakeya.ml1Boot.exists_factorTwoScales` are chained. -/
  ε' : ℝ
  /-- The `γ`-dependent fullness threshold `η(γ)`. -/
  ηGamma : ℝ → ℝ
  /-- The **step** `c = min (γ₀ / 2) (η₀ / 4)` of blueprint `def:ml1bootParams`(vi).

  This is the field that closes blueprint `note:auditUniformStep`: the step is read off the
  *bottom* rung `η₀` of the ladder and off `γ₀`, it depends on `(β, γ₀)` alone, and it is fixed
  *before* the accuracy at which `K_F(γ - c)` is subsequently asked for, which is what
  `Kakeya.frostmanStepSet` demands.  The earlier route stepped by the ladder entry `η 1`
  against a loss allowance `δ ^ (-ε)` drawn from the package itself, coupling the step to the
  accuracy. -/
  c : ℝ

/-- The **eccentricity exponent** `η'_j = 10 η_j / (ε β₀)` of blueprint
`def:ml1bootParams`(iv), where `β₀ = β'(γ₀) = Kakeya.ml1Boot.betaPrime β γ₀` is the fixed
shifted exponent of blueprint `note:ml1bootBetaZeroFixed`.  The blueprint writes `η'_{j-1}`;
here the index is the one of the `η` used, so the blueprint's `η'_{j-1}` is
`p.etaPrime β γ₀ (j - 1)`.

The denominator is the *fixed* `ε β₀` and not `ε γ` or `ε β'(γ)`: item (iv) makes `η'`
`γ`-free, which is what lets the whole parameter package — and with it the step `c` and the
uniform statement `Kakeya.ml1Boot.exists_uniform_step` — be fixed before `γ` is chosen.  On
the geometric ladder of item (iii) it has the closed form
`η'_{j-1} = 10 κ η_j / (ε β₀) = ε g₀ η_j / 10`, which is what turns the bounds recorded in
`Kakeya.ml1Boot.Params.Spec` into one-line computations.

Since `β₀ ≤ β'(γ)` for `γ ∈ [γ₀, 1]`, this quantity *dominates* the `γ`-dependent form
`10 η_{j-1} / (ε β'(γ))` that the dichotomy actually delivers; that domination is the clause
`Kakeya.ml1Boot.Params.Spec.etaPrimeDominates`, so a caller holding only the `γ`-dependent
quantity still inherits every bound proved here. -/
noncomputable def Params.etaPrime (p : Params) (β γ₀ : ℝ) (j : ℕ) : ℝ :=
  10 * p.η j / (p.ε * betaPrime β γ₀)

/-- **The parameter package of blueprint `def:ml1bootParams`.**

`η⋆` and `δ₀` are the output of
`StickyKakeya.volume_iUnionShade_ge_of_isFrostmanAtEveryScale`
applied with `γ₀ / 2` in place of `ε`, and `ηKF`, `ηKKT` are the fullness thresholds
supplied by `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale` and
`Kakeya.KatzTaoEstimate.multiplicity_bound` at the loss exponent `η₀`, as functions of the
exponent at which each of those lemmas is applied.  They are arguments rather than internal
choices so that this is a genuine closed-form definition; the specification lemmas record
what has to be true of them.

Absorbing the loss-exponent slot `ε♯ = η₀` into `ηKF` and `ηKKT`, so that they are functions
of the *exponent* alone, is not circular: `N`, `ε`, `κ` and the whole ladder `(η_j)` — hence
`η₀` itself — are built from `β`, `γ₀` and `η⋆` only, and `ηKF`, `ηKKT` enter the definition
nowhere but in `ηGamma`.  A caller therefore computes `η₀ = (params β γ₀ η⋆ δ₀ f g).η 0` for
*any* pair `f`, `g` (for instance the constant `0` functions), applies
`Kakeya.FrostmanEstimate.multiplicity_bound_auxScale` and
`Kakeya.KatzTaoEstimate.multiplicity_bound` at that `η₀` to obtain the genuine thresholds
`ηKF`, `ηKKT`, and only then forms `params β γ₀ η⋆ δ₀ ηKF ηKKT`; the ladder it gets back is
the one the thresholds were chosen against.

Note the arguments at which the two thresholds are read, matching blueprint
`def:ml1bootParams`(v):

* the Frostman threshold is read at `γ` itself, since
  `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale` is applied at the exponent `γ`;
* the Katz–Tao threshold is read at the *shifted* exponent `β'(γ) = Kakeya.ml1Boot.betaPrime β γ`,
  since `Kakeya.KatzTaoEstimate.multiplicity_bound` is applied at that exponent and not at `γ`
  (see blueprint `lem:ml1bootTbKatzTao`), and it enters weighted by the factor `1 - 5 ε`.  The
  weight is `1 - 5 ε` and not `1 - ε` because the honest `b`-tube scale of
  `Kakeya.ml1Boot.plankWidth_le` is now only known to satisfy `b♯ ≤ δ̃ ^ (1 - 5 ε)`, so the
  fullness hypothesis of `Kakeya.ml1Boot.multiplicity_coarse_le` reads `λ ≥ δ̃ ^ ((1 - 5 ε) η♯)`;
  see blueprint `note:ml1bootWindowConsumers`(3).

The clause `ε η₀ / 2` in the minimum is what makes the fullness hypothesis
`δ ^ η(γ) ≤ λ` of `Kakeya.ml1Boot.multiplicity_le_middle` survive the rescaling to the
middle scale `δ̃ = τ / θ ≤ δ ^ ε`: it gives `δ ^ η(γ) ≤ δ̃ ^ (η(γ) / ε) ≤ δ̃ ^ (η₀ / 2)`, hence
the hypotheses `δ̃ ^ η_{j-1} ≤ λ` of `Kakeya.ml1Boot.flatPrism_dichotomy` and
`Kakeya.ml1Boot.normalized_le_of_coarse`(b) at `j = 1`, where `η_{j-1} = η₀`.  Without it the
case `j = 1` would be unprovable. -/
noncomputable def params (β γ₀ ηStar : ℝ) (δ₀ : NNReal) (ηKF ηKKT : ℝ → ℝ) : Params :=
  let N := paramsN β γ₀ ηStar
  let ε := 1 / Real.sqrt N
  let κ := ε ^ 2 * betaPrime β γ₀ * gap β γ₀ / 100
  let η : ℕ → ℝ := fun j => etaLadder κ (N - j)
  { ηStar := ηStar
    δ₀ := δ₀
    N := N
    ε := ε
    κ := κ
    η := η
    ε' := η 0 / 16
    ηGamma := fun γ =>
      min (min (min (η 0) ηStar) (ε * η 0 / 4))
        (min (ηKF γ) ((1 - 5 * ε) * ηKKT (betaPrime β γ)))
    c := min (γ₀ / 2) (η 0 / 4) }

/-- **What it means for a parameter package to be admissible for `(β, γ₀)`** (blueprint
`lem:ml1bootParamsSpec`), one field per clause of items (i)–(iii).

The clauses depend on none of `δ₀`, `ηKF`, `ηKKT`, and on `η⋆` only through
`fiveEpsLe`, which is why `η⋆` is read off the package itself as `p.ηStar` rather than
carried as a separate parameter.

`etaPrimeLossLe` is item (iii) in its *loss-corrected* form: besides
`η'_{j-1} ≤ ε η_j / 2` (`etaPrimeLe`) it asserts the stronger
`η'_{j-1} + η₀ / ε ≤ ε η_j / 2`.  This is what `Kakeya.ml1Boot.plankWidth_le` needs, since
the lower Frostman bounds fed into it carry the loss `δ ^ (η₀)` in the *outer* scale `δ`,
whereas `Kakeya.ml1Boot.plankWidth_le` is stated at the rescaled scale `δ̃ = τ / θ`, of which
only `δ̃ ≤ δ ^ ε` is known; so the loss exponent available there is `e = η₀ / ε`, not `η₀`.
On the geometric ladder the corrected form costs nothing: `η'_{j-1} ≤ ε η_j / 20` and
`η₀ / ε ≤ ε η_j / 200`, whose sum is `11 ε η_j / 200 ≤ ε η_j / 2`.

The four `η'` clauses are `γ`-free, matching blueprint `def:ml1bootParams`(iv); the fifth,
`etaPrimeDominates`, is the only one to quantify over `γ`, and it is what transports those
bounds to the `γ`-dependent quantity `10 η_{j-1} / (ε β'(γ))`.

Bundling these clauses is what lets the Case (ii) lemmas take a package together with
its specification instead of re-deriving `Kakeya.ml1Boot.params β γ₀ η⋆ δ₀ ηKF ηKKT` from
seven separate binders at every call site. -/
structure Params.Spec (p : Params) (β γ₀ : ℝ) : Prop where
  /-- (i) The loss exponent `ε = 1 / √N` is positive. -/
  epsPos : 0 < p.ε
  /-- (i) `ε ≤ 1`. -/
  epsLeOne : p.ε ≤ 1
  /-- (i) `N ≥ 4096`, the threshold `StickyKakeya.dividingScalesFrostman` imposes. -/
  nGeFourThousandNinetySix : 4096 ≤ p.N
  /-- (i) `ε ≤ 1 / 64`, which is what `N ≥ 4096` buys. -/
  epsLeInvSixtyFour : p.ε ≤ 1 / 64
  /-- (i) `20 ε ≤ η⋆`, which is what `N ≥ (20 / η⋆) ^ 2` buys; this is GWZ's
  `5 ε ≤ η⋆ / 4`. -/
  twentyEpsLe : 20 * p.ε ≤ p.ηStar
  /-- (i) `5 ε ≤ η⋆`, the weakening of `twentyEpsLe` that Case (i)
  (`Kakeya.ml1Boot.multiplicity_le_of_frostmanAtEveryScale`) consumes. -/
  fiveEpsLe : 5 * p.ε ≤ p.ηStar
  /-- (i) `96 ε ≤ g₀ = gap β γ₀`, which is what `N ≥ (96 / g₀) ^ 2` buys.  Together with
  `g₀ ≤ 1/2` it gives `ε ≤ 1/192`, which is where the strict positivity of `1 - 5 ε` in
  `Kakeya.ml1Boot.params` comes from (blueprint `note:ml1bootEtaGammaPositivity`).

  The tightest consumer of the bound is `Kakeya.ml1Boot.numerics_strong`, which charges
  `72 ε + 2 η'_{j-1}` against `g(γ)`; with `etaPrimeLeGap` that is at most
  `72 g₀ / 96 + 2 g₀ / 40 = 4 g₀ / 5`, so `96` still leaves room. -/
  ninetySixEpsLe : 96 * p.ε ≤ gap β γ₀
  /-- (ii) The bottom rung of the ladder is positive. -/
  etaZeroPos : 0 < p.η 0
  /-- (ii) The ladder is nondecreasing on `[0, N]`. -/
  etaMono : MonotoneOn p.η (Set.Iic p.N)
  /-- (ii) The top rung is the ratio itself, `η_N = κ`.  Together with `etaStep` this pins the
  ladder down completely: `η_j = κ ^ (N - j + 1)`. -/
  etaTopEq : p.η p.N = p.κ
  /-- (ii) The top rung `η_N = κ` is at most `ε / 5`.  The blueprint's geometric ladder makes
  this an *inequality*: the earlier recursion started at the exact value `η_N = ε / 5`, whereas
  item (iii) of `def:ml1bootParams` starts at `η_N = κ ≤ ε² / 200 ≤ ε / 5`. -/
  etaTop : p.η p.N ≤ p.ε / 5
  /-- (ii) **The ladder descends at the ratio `κ`**: `η_{j-1} = κ η_j` for `1 ≤ j ≤ N`.  This
  is the defining relation of the geometric ladder of blueprint `def:ml1bootParams`(iii); it is
  what makes `κ` a ratio rather than a bare number, and together with `kappaLeEps` it gives the
  ladder condition `η_{j-1} ≤ ε η_j` of `StickyKakeya.dividingScalesFrostman`. -/
  etaStep : ∀ j, 1 ≤ j → j ≤ p.N → p.η (j - 1) = p.κ * p.η j
  /-- (iii) `η'_{j-1} ≤ ε η_j / 2`.  The bound is `γ`-free, as blueprint
  `def:ml1bootParams`(iv) requires of `η'`. -/
  etaPrimeLe : ∀ j, 1 ≤ j → j ≤ p.N → p.etaPrime β γ₀ (j - 1) ≤ p.ε * p.η j / 2
  /-- (iii) The loss-corrected form `η'_{j-1} + η₀ / ε ≤ ε η_j / 2`, the first half of
  blueprint `eq:ml1bootEtaPrimeBounds`. -/
  etaPrimeLossLe : ∀ j, 1 ≤ j → j ≤ p.N →
    p.etaPrime β γ₀ (j - 1) + p.η 0 / p.ε ≤ p.ε * p.η j / 2
  /-- (iii) `η'_{j-1} ≤ g₀ / 40`, the second half of blueprint
  `eq:ml1bootEtaPrimeBounds`. -/
  etaPrimeLeGap : ∀ j, 1 ≤ j → j ≤ p.N → p.etaPrime β γ₀ (j - 1) ≤ gap β γ₀ / 40
  /-- (iii) `η_{j-1} ≤ η'_{j-1}`, which holds because `ε β₀ ≤ 1 ≤ 10`. -/
  etaLeEtaPrime : ∀ j, 1 ≤ j → j ≤ p.N → p.η (j - 1) ≤ p.etaPrime β γ₀ (j - 1)
  /-- (iii) **The `γ`-free exponent dominates the `γ`-dependent one**: for every
  `γ ∈ [γ₀, 1]`, `10 η_{j-1} / (ε β'(γ)) ≤ η'_{j-1}`.

  This is the clause that makes the four `γ`-free bounds above usable by a caller that holds
  only the `γ`-dependent quantity `10 η_{j-1} / (ε β'(γ))` — which is what the Katz–Tao step
  of Section 8 delivers, since it is applied at the shifted exponent `β'(γ)`.  It holds
  because `β'` is monotone, so `β₀ = β'(γ₀) ≤ β'(γ)` for `γ ≥ γ₀`. -/
  etaPrimeDominates : ∀ j, 1 ≤ j → j ≤ p.N → ∀ γ ∈ Set.Icc γ₀ 1,
    10 * p.η (j - 1) / (p.ε * betaPrime β γ) ≤ p.etaPrime β γ₀ (j - 1)
  /-- (iii) The ladder ratio `κ = ε² β₀ g₀ / 100` is positive; this is exactly the positivity
  of `β₀ = β'(γ₀)`, which is what the substitution of blueprint `note:ml1bootBetaZeroFixed`
  buys and what the raw `β` does not give at `β = 0`. -/
  kappaPos : 0 < p.κ
  /-- (iii) `κ ≤ ε² / 200`, which is `β₀ ≤ 1` and `g₀ ≤ 1/2`.  This is the bound that pays for
  the loss summand `η₀ / ε ≤ ε η_j / 200` in `etaPrimeLossLe`. -/
  kappaLeEpsSq : p.κ ≤ p.ε ^ 2 / 200
  /-- (iii) `κ ≤ ε`, so a ladder descending at the ratio `κ` satisfies the ladder condition
  `η_{j-1} ≤ ε η_j` of `StickyKakeya.dividingScalesFrostman` a fortiori (blueprint
  `note:ml1bootLadderRatio`). -/
  kappaLeEps : p.κ ≤ p.ε
  /-- (iv) The bookkeeping accuracy is `ε' = η₀ / 16`, half the extremal value `η₀ / 8`
  allowed by the exponent contract of blueprint `eq:ml1bootExponentContract`. -/
  epsPrimeEq : p.ε' = p.η 0 / 16
  /-- (vi) The step is positive. -/
  stepPos : 0 < p.c
  /-- (vi) `c ≤ γ₀ / 2`, which is what Case (i)
  (`Kakeya.ml1Boot.multiplicity_le_of_frostmanAtEveryScale`) requires of a step. -/
  stepLeHalfGammaZero : p.c ≤ γ₀ / 2
  /-- (vi) `c ≤ η₀ / 4`, which is what the funding inequality `stepFunding` requires. -/
  stepLeEtaZero : p.c ≤ p.η 0 / 4
  /-- (vi) **The funding inequality** (blueprint `eq:ml1bootStepFunding`).  For every rung
  `1 ≤ j ≤ N` and every fullness exponent `e ∈ [0, η₀]` — the intended value being
  `e = η(γ)`, which satisfies `η(γ) ≤ η₀` by `Kakeya.ml1Boot.Params.EtaGammaSpec` —

  `ε' + 2 c + e c / 2 + 5 η₀ / 16 ≤ 2 η_{j-1} - 16 ε'`,

  whose right-hand side is the gain exponent `10 a - 8 a'` of the exponent contract at
  `a = η_{j-1}`, `a' = η_{j-1} + 2 ε'`.  In words: the linking loss `δ ^ (-ε')` and the
  exponent shift `γ ↦ γ - c`, which costs `δ ^ (-2c - e c / 2)`, are together paid for by the
  gain of the contract, with the strict surplus `δ ^ (5 η₀ / 16)` left over to absorb the fixed
  constants of the assembly into the smallness of `δ`.  This is what decouples the step from
  the package's loss exponent `ε` (blueprint `note:auditUniformStep`). -/
  stepFunding : ∀ j, 1 ≤ j → j ≤ p.N → ∀ e : ℝ, 0 ≤ e → e ≤ p.η 0 →
    p.ε' + 2 * p.c + e * p.c / 2 + 5 * p.η 0 / 16 ≤ 2 * p.η (j - 1) - 16 * p.ε'

set_option maxHeartbeats 800000 in
-- The geometric-ladder inequalities in parts (ii) and (iii) need several
-- `field_simp` / `nlinarith` calls; they push past the default heartbeat budget.
/-- **The parameter package is admissible** (blueprint `lem:ml1bootParamsSpec`): the package
`Kakeya.ml1Boot.params β γ₀ η⋆ δ₀ ηKF ηKKT` satisfies `Kakeya.ml1Boot.Params.Spec`. -/
theorem params_spec {β γ₀ ηStar : ℝ} (hβ0 : 0 ≤ β) (hγ₀ : γ₀ ∈ Set.Ioc β 1)
    (hηStar : 0 < ηStar) (δ₀ : NNReal) (ηKF ηKKT : ℝ → ℝ) :
    (params β γ₀ ηStar δ₀ ηKF ηKKT).Spec β γ₀ := by
  let N : ℕ := paramsN β γ₀ ηStar
  let s : ℝ := Real.sqrt (N : ℝ)
  let ε : ℝ := 1 / s
  let κ : ℝ := ε ^ 2 * betaPrime β γ₀ * gap β γ₀ / 100
  let η : ℕ → ℝ := fun j => etaLadder κ (N - j)
  have hγ0pos : 0 < γ₀ := lt_of_le_of_lt hβ0 hγ₀.1
  have hgap : 0 < gap β γ₀ := by
    dsimp [gap, betaPrime]
    apply sub_pos.mpr
    rw [max_lt_iff]
    exact ⟨hγ₀.1, half_lt_self hγ0pos⟩
  have hN4096 : (4096 : ℕ) ≤ N := by
    dsimp only [N, paramsN]
    exact le_max_left _ _
  have hNOne : (1 : ℕ) ≤ N := le_trans (by norm_num) hN4096
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNOne
  have hN4096R : (4096 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4096
  have hNpos : 0 < (N : ℝ) := by linarith
  have hs0 : 0 < s := by
    dsimp [s]
    rw [Real.sqrt_pos]
    exact hNpos
  have hs1 : 1 ≤ s := by
    dsimp [s]
    rw [Real.one_le_sqrt]
    exact hN1
  have hs2 : s ^ 2 = (N : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (le_of_lt hNpos)
  have hε : ε = 1 / Real.sqrt (N : ℝ) := by simp [ε, s]
  have hε0 : 0 < ε := by
    rw [hε]
    exact one_div_pos.mpr (by rwa [Real.sqrt_pos])
  have hsNsqrt_pos : 0 < Real.sqrt (N : ℝ) := by rwa [Real.sqrt_pos]
  -- `N ≥ 4096` gives `s ≥ 64`, hence `ε ≤ 1/64` (blueprint `lem:ml1bootParamsSpec`(i)).
  have hs64 : (64 : ℝ) ≤ s := by nlinarith [hs2, hs0, hN4096R]
  have hε64 : ε ≤ 1 / 64 := by
    have hεs : ε = 1 / s := rfl
    rw [hεs, div_le_iff₀ hs0]
    linarith
  have hε1 : ε ≤ 1 := by linarith
  have hxN : max ((20 / ηStar) ^ 2) ((96 / gap β γ₀) ^ 2) ≤ (N : ℝ) := by
    let m : ℝ := max ((20 / ηStar) ^ 2) ((96 / (gap β γ₀)) ^ 2)
    have h0 : m ≤ (⌈m⌉₊ : ℝ) := Nat.le_ceil m
    have h1 : (⌈m⌉₊ : ℕ) ≤ N := by
      dsimp only [N, paramsN, m]
      exact le_max_right _ _
    calc
      m ≤ (⌈m⌉₊ : ℝ) := h0
      _ ≤ (N : ℝ) := Nat.cast_le.mpr h1
  have hq1 : (20 / ηStar) ^ 2 ≤ (N : ℝ) := le_trans (le_max_left _ _) hxN
  have hq2 : (96 / gap β γ₀) ^ 2 ≤ (N : ℝ) := le_trans (le_max_right _ _) hxN
  -- `N ≥ (20/η⋆)²` gives `20 ε ≤ η⋆`, and a fortiori `5 ε ≤ η⋆`.
  have h20div : 20 / ηStar ≤ s := by
    have h2 : (0 : ℝ) ≤ 20 / ηStar := by positivity
    calc
      20 / ηStar = Real.sqrt ((20 / ηStar) ^ 2) := (Real.sqrt_sq h2).symm
      _ ≤ Real.sqrt (s ^ 2) := Real.sqrt_le_sqrt (by rw [hs2]; exact hq1)
      _ = s := Real.sqrt_sq hs0.le
  have h20le : (20 : ℝ) ≤ s * ηStar := (div_le_iff₀ hηStar).mp h20div
  have h20eps : 20 * ε ≤ ηStar := by
    have hεs : 20 * ε = 20 / s := by
      have h : ε = 1 / s := rfl
      rw [h]; ring
    rw [hεs, div_le_iff₀ hs0]
    linarith
  have h5eps : 5 * ε ≤ ηStar := by linarith [hε0.le]
  have hg2 : 0 < (gap β γ₀) ^ 2 := sq_pos_of_ne_zero (ne_of_gt hgap)
  have h96le : 96 ≤ gap β γ₀ * s := by
    have hsq : (gap β γ₀ * s) ^ 2 = (gap β γ₀) ^ 2 * (N : ℝ) := by
      calc
        (gap β γ₀ * s) ^ 2 = (gap β γ₀) ^ 2 * s ^ 2 := by ring
        _ = (gap β γ₀) ^ 2 * (N : ℝ) := by rw [hs2]
    have hsi : 96 ^ 2 ≤ (gap β γ₀ * s) ^ 2 := by
      rw [hsq]
      calc
        96 ^ 2 = (96 / gap β γ₀) ^ 2 * (gap β γ₀) ^ 2 := by field_simp [ne_of_gt hgap]
        _ ≤ (N : ℝ) * (gap β γ₀) ^ 2 := mul_le_mul_of_nonneg_right hq2 (sq_nonneg (gap β γ₀))
        _ = (gap β γ₀) ^ 2 * (N : ℝ) := by ring
    have hle_abs : |(96 : ℝ)| ≤ |gap β γ₀ * s| := sq_le_sq.mp hsi
    have hpa : |gap β γ₀ * s| = gap β γ₀ * s :=
      abs_of_nonneg (mul_nonneg (le_of_lt hgap) (le_of_lt hs0))
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 96), hpa] at hle_abs
    exact hle_abs
  have h96eps : 96 * ε ≤ gap β γ₀ := by
    rw [hε]
    rw [show 96 * (1 / Real.sqrt (N : ℝ)) = 96 / Real.sqrt (N : ℝ) by ring]
    rw [div_le_iff₀ (by rwa [Real.sqrt_pos])]
    simpa using h96le
  have hγ0le1 : γ₀ ≤ 1 := hγ₀.2
  -- The two fixed exponents `β₀ = β'(γ₀)` and `g₀ = γ₀ - β₀` of blueprint
  -- `note:ml1bootBetaZeroFixed`.
  have hβ0prime : 0 < betaPrime β γ₀ := (betaPrime_spec hβ0 γ₀ hγ₀).1
  have hb0lt : betaPrime β γ₀ < γ₀ := (betaPrime_spec hβ0 γ₀ hγ₀).2
  have hb0le : betaPrime β γ₀ ≤ 1 := le_trans hb0lt.le hγ0le1
  have hgap_le : gap β γ₀ ≤ 1 / 2 := by
    obtain ⟨hgapEq, -, -⟩ := gap_spec hβ0
    rw [hgapEq γ₀]
    calc
      min (γ₀ - β) (γ₀ / 2) ≤ γ₀ / 2 := min_le_right _ _
      _ ≤ 1 / 2 := by linarith
  -- The ladder ratio `κ = ε² β₀ g₀ / 100` (blueprint `def:ml1bootParams`(iii)).
  have hκdef : κ = ε ^ 2 * betaPrime β γ₀ * gap β γ₀ / 100 := rfl
  have hκ0 : 0 < κ := by rw [hκdef]; positivity
  have hb0g0 : betaPrime β γ₀ * gap β γ₀ ≤ 1 / 2 := by
    nlinarith only [hb0le, hgap, hgap_le, hβ0prime]
  have hκ200 : κ ≤ ε ^ 2 / 200 := by
    rw [hκdef]
    nlinarith only [sq_nonneg ε, hb0g0]
  have hκeps5 : κ ≤ ε / 5 := by nlinarith only [hκ200, hε0, hε1]
  have hκeps : κ ≤ ε := by linarith
  have hκ1 : κ ≤ 1 := by linarith
  -- The geometric ladder `η_j = κ ^ (N - j + 1)`.
  have hηdef : ∀ j : ℕ, η j = κ ^ (N - j + 1) := fun _ => rfl
  have hηpos : ∀ j, 0 < η j := by
    intro j
    rw [hηdef]
    exact pow_pos hκ0 _
  have hηNeq : η N = κ := by
    rw [hηdef]
    simp
  have hηN : η N ≤ ε / 5 := by rw [hηNeq]; exact hκeps5
  have hmono : MonotoneOn η (Set.Iic N) := by
    intro a _ b hb hab
    rw [hηdef, hηdef]
    exact pow_le_pow_of_le_one hκ0.le hκ1 (by omega)
  have hstep : ∀ j : ℕ, 1 ≤ j → j ≤ N → η (j - 1) = κ * η j := by
    intro j hj1 hjN
    rw [hηdef, hηdef, show N - (j - 1) + 1 = N - j + 1 + 1 by omega, pow_succ]
    ring
  -- The eccentricity exponent of blueprint `def:ml1bootParams`(iv), with the *fixed*
  -- denominator `ε β₀`.  Everything below is the blueprint proof of
  -- `lem:ml1bootParamsSpec`(iii) on the geometric ladder.
  have hεb0 : 0 < ε * betaPrime β γ₀ := mul_pos hε0 hβ0prime
  have hmain : ∀ j, 1 ≤ j → j ≤ N →
      10 * η (j - 1) / (ε * betaPrime β γ₀) ≤ ε * η j / 2 ∧
      10 * η (j - 1) / (ε * betaPrime β γ₀) + η 0 / ε ≤ ε * η j / 2 ∧
      10 * η (j - 1) / (ε * betaPrime β γ₀) ≤ gap β γ₀ / 40 ∧
      η (j - 1) ≤ 10 * η (j - 1) / (ε * betaPrime β γ₀) := by
    intro j hj1 hjN
    have hηj_pos : 0 < η j := hηpos j
    have hηjm1_pos : 0 < η (j - 1) := hηpos (j - 1)
    have hηjm1 : η (j - 1) = κ * η j := hstep j hj1 hjN
    -- The closed form of item (iv): `10 κ / (ε β₀) = ε g₀ / 10`.
    have hkey : 10 * η (j - 1) / (ε * betaPrime β γ₀) = ε * gap β γ₀ * η j / 10 := by
      rw [hηjm1, hκdef, div_eq_iff (ne_of_gt hεb0)]
      ring
    have hεηj_nonneg : 0 ≤ ε * η j := (mul_pos hε0 hηj_pos).le
    -- `η'_{j-1} = ε g₀ η_j / 10 ≤ ε η_j / 20`, using `g₀ ≤ 1/2`.
    have hA : 10 * η (j - 1) / (ε * betaPrime β γ₀) ≤ ε * η j / 20 := by
      rw [hkey]
      nlinarith only [mul_nonneg hεηj_nonneg
        (by linarith only [hgap_le] : (0 : ℝ) ≤ 1 / 2 - gap β γ₀)]
    have hprime_le_2 : 10 * η (j - 1) / (ε * betaPrime β γ₀) ≤ ε * η j / 2 := by
      linarith only [hA, hεηj_nonneg]
    -- The loss summand: `η₀ ≤ η_{j-1} = κ η_j ≤ ε² η_j / 200`.
    have hη0le : η 0 ≤ η (j - 1) := by
      refine hmono (Set.mem_Iic.mpr (Nat.zero_le N)) (Set.mem_Iic.mpr ?_) (Nat.zero_le (j - 1))
      omega
    have hη0ε : η 0 / ε ≤ ε * η j / 200 := by
      rw [div_le_iff₀ hε0]
      have h1 : η 0 ≤ κ * η j := by rw [← hηjm1]; exact hη0le
      nlinarith only [h1, hκ200, hηj_pos]
    have hprime2 : 10 * η (j - 1) / (ε * betaPrime β γ₀) + η 0 / ε ≤ ε * η j / 2 := by
      linarith only [hA, hη0ε, hεηj_nonneg]
    -- The gap bound: `ε g₀ η_j / 10 ≤ g₀ / 40` reduces to `ε η_j ≤ 1/4`.
    have hηjle : η j ≤ ε / 5 :=
      le_trans (hmono (Set.mem_Iic.mpr hjN) (Set.mem_Iic.mpr le_rfl) hjN) hηN
    have hεηj : ε * η j ≤ 1 / 4 := by nlinarith only [hε0, hε64, hηjle, hηj_pos]
    have hprime3 : 10 * η (j - 1) / (ε * betaPrime β γ₀) ≤ gap β γ₀ / 40 := by
      rw [hkey]
      nlinarith only [mul_nonneg hgap.le
        (by linarith only [hεηj] : (0 : ℝ) ≤ 1 - 4 * (ε * η j))]
    -- `η_{j-1} ≤ η'_{j-1}`, since `ε β₀ ≤ 1 ≤ 10`.
    have hεb0le1 : ε * betaPrime β γ₀ ≤ 1 := by
      nlinarith only [mul_nonneg (by linarith only [hε1] : (0 : ℝ) ≤ 1 - ε) hβ0prime.le,
        hb0le]
    have h10ge : (1 : ℝ) ≤ 10 / (ε * betaPrime β γ₀) := by
      rw [le_div_iff₀ hεb0]
      linarith only [hεb0le1]
    have hprime4 : η (j - 1) ≤ 10 * η (j - 1) / (ε * betaPrime β γ₀) := by
      calc
        η (j - 1) = η (j - 1) * 1 := by ring
        _ ≤ η (j - 1) * (10 / (ε * betaPrime β γ₀)) :=
          mul_le_mul_of_nonneg_left h10ge hηjm1_pos.le
        _ = 10 * η (j - 1) / (ε * betaPrime β γ₀) := by ring
    exact ⟨hprime_le_2, hprime2, hprime3, hprime4⟩
  -- The domination clause: `β'` is monotone, so `β₀ = β'(γ₀) ≤ β'(γ)` for `γ ≥ γ₀`.
  have hdom : ∀ j, 1 ≤ j → j ≤ N → ∀ γ ∈ Set.Icc γ₀ 1,
      10 * η (j - 1) / (ε * betaPrime β γ) ≤ 10 * η (j - 1) / (ε * betaPrime β γ₀) := by
    intro j _ _ γ hγ
    have hb0mono : betaPrime β γ₀ ≤ betaPrime β γ := by
      dsimp [betaPrime]
      exact max_le_max le_rfl (by linarith only [hγ.1])
    have hnum : (0 : ℝ) ≤ 10 * η (j - 1) := by linarith only [hηpos (j - 1)]
    exact div_le_div_of_nonneg_left hnum hεb0
      (mul_le_mul_of_nonneg_left hb0mono hε0.le)
  have hη0pos : 0 < η 0 := hηpos 0
  have hcpos : 0 < min (γ₀ / 2) (η 0 / 4) :=
    lt_min (half_pos hγ0pos) (by nlinarith [hη0pos])
  exact
    { epsPos := hε0
      epsLeOne := hε1
      nGeFourThousandNinetySix := hN4096
      epsLeInvSixtyFour := hε64
      twentyEpsLe := h20eps
      fiveEpsLe := h5eps
      ninetySixEpsLe := h96eps
      etaZeroPos := hηpos 0
      etaMono := hmono
      etaTopEq := hηNeq
      etaTop := hηN
      etaStep := hstep
      etaPrimeLe := fun j hj1 hjN => (hmain j hj1 hjN).1
      etaPrimeLossLe := fun j hj1 hjN => (hmain j hj1 hjN).2.1
      etaPrimeLeGap := fun j hj1 hjN => (hmain j hj1 hjN).2.2.1
      etaLeEtaPrime := fun j hj1 hjN => (hmain j hj1 hjN).2.2.2
      etaPrimeDominates := hdom
      kappaPos := hκ0
      kappaLeEpsSq := hκ200
      kappaLeEps := hκeps
      epsPrimeEq := by
        rfl
      stepPos := by
        dsimp [params]
        exact hcpos
      stepLeHalfGammaZero := by
        dsimp [params]
        exact min_le_left (γ₀ / 2) (η 0 / 4)
      stepLeEtaZero := by
        dsimp [params]
        exact min_le_right (γ₀ / 2) (η 0 / 4)
      stepFunding := by
        intro j hj1 hjN e he0 heη
        have hη0nn : 0 ≤ η 0 := (hηpos 0).le
        have hη0le1 : η 0 ≤ 1 := by
          have hhη0leN : η 0 ≤ η N :=
            hmono (Set.mem_Iic.mpr (Nat.zero_le N)) (Set.mem_Iic.mpr le_rfl) (Nat.zero_le N)
          calc
            η 0 ≤ η N := hhη0leN
            _ ≤ ε / 5 := hηN
            _ ≤ 1 := by nlinarith [hε1]
        have hhmon : η 0 ≤ η (j - 1) := by
          have hjN' : j ≤ N := by
            simpa [params] using hjN
          exact hmono (Set.mem_Iic.mpr (Nat.zero_le N))
            (Set.mem_Iic.mpr (by omega)) (Nat.zero_le (j - 1))
        have hc_le4 : min (γ₀ / 2) (η 0 / 4) ≤ η 0 / 4 :=
          min_le_right (γ₀ / 2) (η 0 / 4)
        have hhec : e * min (γ₀ / 2) (η 0 / 4) / 2 ≤ η 0 * (η 0 / 4) / 2 := by
          have h1 : e * min (γ₀ / 2) (η 0 / 4) ≤ η 0 * min (γ₀ / 2) (η 0 / 4) :=
            mul_le_mul_of_nonneg_right heη hcpos.le
          have h2 : η 0 * min (γ₀ / 2) (η 0 / 4) ≤ η 0 * (η 0 / 4) :=
            mul_le_mul_of_nonneg_left hc_le4 hη0nn
          calc
            e * min (γ₀ / 2) (η 0 / 4) / 2 ≤ η 0 * min (γ₀ / 2) (η 0 / 4) / 2 :=
              div_le_div_of_nonneg_right h1 (by norm_num)
            _ ≤ η 0 * (η 0 / 4) / 2 := div_le_div_of_nonneg_right h2 (by norm_num)
        have h2c : 2 * min (γ₀ / 2) (η 0 / 4) ≤ 2 * (η 0 / 4) :=
          mul_le_mul_of_nonneg_left hc_le4 (by norm_num)
        have hworst : η 0 / 16 + 2 * (η 0 / 4) + η 0 * (η 0 / 4) / 2 + 5 * η 0 / 16 ≤ η 0 := by
          have hsq0 : η 0 * η 0 ≤ η 0 := by
            calc
              η 0 * η 0 ≤ (1 : ℝ) * η 0 := mul_le_mul_of_nonneg_right hη0le1 hη0nn
              _ = η 0 := by ring
          nlinarith [hsq0, hη0nn, hη0le1]
        have hRHS : η 0 ≤ 2 * η (j - 1) - η 0 := by
          nlinarith [hhmon]
        have h16 : 16 * (η 0 / 16) = η 0 := by ring
        have hfin :
            η 0 / 16 + 2 * min (γ₀ / 2) (η 0 / 4) + e * min (γ₀ / 2) (η 0 / 4) / 2 +
              5 * η 0 / 16 ≤ 2 * η (j - 1) - 16 * (η 0 / 16) := by
          have hpred : η 0 / 16 + 2 * min (γ₀ / 2) (η 0 / 4) + e * min (γ₀ / 2) (η 0 / 4) / 2 +
              5 * η 0 / 16 ≤ η 0 / 16 + 2 * (η 0 / 4) + η 0 * (η 0 / 4) / 2 + 5 * η 0 / 16 := by
            nlinarith [hhec, h2c]
          nlinarith [hpred, hworst, hRHS, h16]
        exact hfin }

/-- **The `γ`-dependent fullness threshold** (blueprint `lem:ml1bootEtaGamma`).

For every `γ ∈ [γ₀, 1]` the threshold `η(γ)` is positive, is below every exponent of the
ladder and below `η⋆`, is below `ε η₀ / 2`, and is below both of the thresholds `ηKF γ` and
`(1 - 5 ε) * ηKKT (β'(γ))` that the fine, coarse and Katz–Tao steps of Section 8 consume.

The clause `η(γ) ≤ ε η₀ / 2` is the one that survives the rescaling to the middle scale: it
turns the fullness hypothesis `δ ^ η(γ) ≤ λ` of `Kakeya.ml1Boot.multiplicity_le_middle` into
`δ̃ ^ (η₀ / 2) ≤ λ` at `δ̃ = τ / θ ≤ δ ^ ε`, hence into the hypotheses
`δ̃ ^ η_{j-1} ≤ λ` of `Kakeya.ml1Boot.flatPrism_dichotomy` and
`Kakeya.ml1Boot.normalized_le_of_coarse`(b), including at `j = 1` where `η_{j-1} = η₀`.

As in `Kakeya.ml1Boot.params`, the Katz–Tao threshold is read at the shifted exponent
`β'(γ) = Kakeya.ml1Boot.betaPrime β γ`, which is the exponent at which
`Kakeya.KatzTaoEstimate.multiplicity_bound` is applied in Section 8.

The hypotheses on `ηKF` and `ηKKT` are only their positivity: that is all the blueprint
uses, and it is what `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale` and
`Kakeya.KatzTaoEstimate.multiplicity_bound` supply. -/
structure Params.EtaGammaSpec (p : Params) (β γ₀ : ℝ) (ηKF ηKKT : ℝ → ℝ) : Prop where
  /-- `η(γ)` is positive. -/
  etaGammaPos : ∀ γ ∈ Set.Icc γ₀ 1, 0 < p.ηGamma γ
  /-- `η(γ)` is below the bottom rung of the ladder. -/
  etaGammaLeEtaZero : ∀ γ ∈ Set.Icc γ₀ 1, p.ηGamma γ ≤ p.η 0
  /-- The bottom two rungs of the ladder are ordered. -/
  etaZeroLeEtaOne : p.η 0 ≤ p.η 1
  /-- The rung `η_1` is below `ε / 5`.  On the geometric ladder this follows from the top
  rung bound `Kakeya.ml1Boot.Params.Spec.etaTop`, `η_N ≤ ε / 5`, together with the
  monotonicity `etaMono` of the ladder on `[0, N]` (note `1 ≤ N` since `N ≥ 4096`). -/
  etaOneLeEps : p.η 1 ≤ p.ε / 5
  /-- `η(γ)` is below the sticky-Kakeya threshold `η⋆`. -/
  etaGammaLeEtaStar : ∀ γ ∈ Set.Icc γ₀ 1, p.ηGamma γ ≤ p.ηStar
  /-- `η(γ) ≤ ε η₀ / 4`, the clause that survives the rescaling to the middle scale.

  The quarter, not the half: this is the strength
  `Kakeya.ml1Boot.multiplicity_le_middle_avg` asks for in its `hηΓ4` hypothesis, and without
  it that theorem carries an undischargeable side condition.  The half is still available,
  a fortiori, as `Kakeya.ml1Boot.Params.EtaGammaSpec.etaGammaLeRescale`. -/
  etaGammaLeRescale4 : ∀ γ ∈ Set.Icc γ₀ 1, p.ηGamma γ ≤ p.ε * p.η 0 / 4
  /-- `η(γ)` is below the Frostman threshold, read at `γ`. -/
  etaGammaLeKF : ∀ γ ∈ Set.Icc γ₀ 1, p.ηGamma γ ≤ ηKF γ
  /-- `η(γ)` is below the Katz–Tao threshold, read at the shifted exponent `β'(γ)` and
  weighted by `1 - 5 ε`.  This is the weight that supplies the fullness hypothesis
  `λ ≥ δ̃ ^ ((1 - 5 ε) η♯)` of `Kakeya.ml1Boot.multiplicity_coarse_le`, the honest `b`-tube
  scale being bounded only by `δ̃ ^ (1 - 5 ε)`. -/
  etaGammaLeKKT : ∀ γ ∈ Set.Icc γ₀ 1, p.ηGamma γ ≤ (1 - 5 * p.ε) * ηKKT (betaPrime β γ)

/-- **The half-strength rescaling clause**, `η(γ) ≤ ε η₀ / 2`.

Kept under its historical name because it is the form the middle-scale numerics of
`Kakeya.ml1Boot.middleFactor_numerics` read.  It is now a *consequence* of the recorded
clause `Kakeya.ml1Boot.Params.EtaGammaSpec.etaGammaLeRescale4`: `η(γ) ≤ ε η₀ / 4` together
with `0 < η(γ)` forces `0 < ε η₀`, and then the quarter is below the half. -/
theorem Params.EtaGammaSpec.etaGammaLeRescale {p : Params} {β γ₀ : ℝ} {ηKF ηKKT : ℝ → ℝ}
    (h : p.EtaGammaSpec β γ₀ ηKF ηKKT) :
    ∀ γ ∈ Set.Icc γ₀ 1, p.ηGamma γ ≤ p.ε * p.η 0 / 2 := by
  intro γ hγ
  have h4 := h.etaGammaLeRescale4 γ hγ
  have hpos := h.etaGammaPos γ hγ
  linarith

/-- **The `γ`-dependent fullness threshold of `Kakeya.ml1Boot.params` is admissible**
(blueprint `lem:ml1bootEtaGamma`): the package `Kakeya.ml1Boot.params β γ₀ η⋆ δ₀ ηKF ηKKT`
satisfies `Kakeya.ml1Boot.Params.EtaGammaSpec`.

The hypotheses on `ηKF` and `ηKKT` are only their positivity: that is all the blueprint
uses, and it is what `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale` and
`Kakeya.KatzTaoEstimate.multiplicity_bound` supply. -/
theorem etaGamma_spec {β γ₀ ηStar : ℝ} (hβ0 : 0 ≤ β) (hγ₀ : γ₀ ∈ Set.Ioc β 1)
    (hηStar : 0 < ηStar) (δ₀ : NNReal) {ηKF ηKKT : ℝ → ℝ}
    (hηKF : ∀ γ ∈ Set.Icc γ₀ 1, 0 < ηKF γ)
    (hηKKT : ∀ γ ∈ Set.Icc γ₀ 1, 0 < ηKKT (betaPrime β γ)) :
    (params β γ₀ ηStar δ₀ ηKF ηKKT).EtaGammaSpec β γ₀ ηKF ηKKT := by
  let p := params β γ₀ ηStar δ₀ ηKF ηKKT
  have hspec := params_spec hβ0 hγ₀ hηStar δ₀ ηKF ηKKT
  have hε0 : 0 < p.ε := hspec.epsPos
  have hε96 : 96 * p.ε ≤ gap β γ₀ := hspec.ninetySixEpsLe
  have hη00 : 0 < p.η 0 := hspec.etaZeroPos
  have hmono : MonotoneOn p.η (Set.Iic p.N) := hspec.etaMono
  have hηN : p.η p.N ≤ p.ε / 5 := hspec.etaTop
  have hγ₀le : γ₀ ≤ 1 := hγ₀.2
  have hgapLeHalf : gap β γ₀ ≤ 1 / 2 := by
    obtain ⟨hgapEqu, -, -⟩ := gap_spec hβ0
    rw [hgapEqu γ₀]
    exact le_trans (min_le_right _ _) (by linarith)
  -- Blueprint `note:ml1bootEtaGammaPositivity`: `96 ε ≤ g₀ ≤ 1/2` gives `ε ≤ 1/192`, so
  -- `1 - 5 ε ≥ 187/192 > 0`.  The weaker `ε ≤ 1` would not give `5 ε < 1`.
  have hε192 : 192 * p.ε ≤ 1 := by nlinarith [hε96, hgapLeHalf]
  have h1mε : 0 < 1 - 5 * p.ε := by nlinarith [hε0]
  have hpN1 : 1 ≤ p.N := le_trans (by norm_num) hspec.nGeFourThousandNinetySix
  have hmem0 : 0 ∈ Set.Iic p.N := Set.mem_Iic.mpr (Nat.zero_le _)
  have hmem1 : 1 ∈ Set.Iic p.N := Set.mem_Iic.mpr hpN1
  have hmemN : p.N ∈ Set.Iic p.N := Set.mem_Iic.mpr le_rfl
  have hpos0 : 0 < min (p.η 0) p.ηStar := lt_min hη00 hηStar
  have hposA : 0 < min (min (p.η 0) p.ηStar) (p.ε * p.η 0 / 4) := by
    exact lt_min hpos0 (by positivity)
  have hmain : ∀ γ ∈ Set.Icc γ₀ 1,
      0 < p.ηGamma γ ∧ p.ηGamma γ ≤ p.η 0 ∧ p.ηGamma γ ≤ p.ηStar ∧
        p.ηGamma γ ≤ p.ε * p.η 0 / 4 ∧ p.ηGamma γ ≤ ηKF γ ∧
        p.ηGamma γ ≤ (1 - 5 * p.ε) * ηKKT (betaPrime β γ) := by
    intro γ hγ
    have hposKF : 0 < ηKF γ := hηKF γ hγ
    have hposKKT : 0 < ηKKT (betaPrime β γ) := hηKKT γ hγ
    have hposB : 0 < min (ηKF γ) ((1 - 5 * p.ε) * ηKKT (betaPrime β γ)) := by
      exact lt_min hposKF (by positivity)
    have hηG : p.ηGamma γ =
        min (min (min (p.η 0) p.ηStar) (p.ε * p.η 0 / 4))
          (min (ηKF γ) ((1 - 5 * p.ε) * ηKKT (betaPrime β γ))) := by
      rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hηG]; exact lt_min hposA hposB
    · rw [hηG]; exact min_le_of_left_le (min_le_of_left_le (min_le_left _ _))
    · rw [hηG]; exact min_le_of_left_le (min_le_of_left_le (min_le_right _ _))
    · rw [hηG]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    · rw [hηG]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    · rw [hηG]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hle01 : p.η 0 ≤ p.η 1 := hmono hmem0 hmem1 (by norm_num)
  have hle1N : p.η 1 ≤ p.ε / 5 := le_trans (hmono hmem1 hmemN hpN1) hηN
  exact
    { etaGammaPos := fun γ hγ => (hmain γ hγ).1
      etaGammaLeEtaZero := fun γ hγ => (hmain γ hγ).2.1
      etaZeroLeEtaOne := hle01
      etaOneLeEps := hle1N
      etaGammaLeEtaStar := fun γ hγ => (hmain γ hγ).2.2.1
      etaGammaLeRescale4 := fun γ hγ => (hmain γ hγ).2.2.2.1
      etaGammaLeKF := fun γ hγ => (hmain γ hγ).2.2.2.2.1
      etaGammaLeKKT := fun γ hγ => (hmain γ hγ).2.2.2.2.2 }

/-! ### Case (i): the sticky case -/

section CaseSticky

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Case (i) of the dichotomy: the Frostman-at-every-scale case** (blueprint
`lem:ml1bootCaseSticky`).

If a uniform family of essentially distinct, shaded `δ`-tubes in `B₁ ⊆ ℝ³` has fullness at
least `δ ^ η(γ)` and is `δ ^ (-5 ε)`-Frostman at every scale, then it satisfies the
multiplicity bound of `K_F(γ - c)` for every `γ ∈ [γ₀, 1]` and every step size
`0 < c ≤ γ₀ / 2`.

The quantifier over `γ` is placed *before* the family, unlike in the blueprint: the
fullness hypothesis is `λ ≥ δ ^ η(γ)` and `η` depends on `γ`, so the two cannot both be
read with `γ` bound after the family.  The uniformity constant `Cunif` is quantified before
`δ`, as in `StickyKakeya.volume_iUnionShade_ge_of_isFrostmanAtEveryScale`.

Sticky Kakeya is a `Prop` definition (`StickyKakeya.StickyFrostmanEstimate`), not a theorem,
so it enters as the hypothesis `hSFE`; and uniformity and the every-scale Frostman bound are
read off one and the same bundle `𝒯 : ShadedTube.ShadedUniformTubeSet s T (ssfGridLen δ)
Cunif`, as they are in that definition.

Following the opening of the proof of [GWZ, Lemma 8.2], the threshold `η⋆` is an *output* of
this lemma rather than a parameter: GWZ takes `η⋆` to be the threshold returned by sticky
Kakeya ([GWZ, Theorem 7.3(A)],
`StickyKakeya.volume_iUnionShade_ge_of_isFrostmanAtEveryScale`) and only then builds the
parameter package on top of it, through `N ≥ (20 / η⋆) ^ 2` (`Kakeya.ml1Boot.paramsN`).  A
universally quantified `η⋆` would be unprovable: enlarging `η⋆` weakens both the fullness
hypothesis `λ ≥ δ ^ η(γ)` and the Frostman error `δ ^ (-5 ε)`, so no single family of
hypotheses can serve every `η⋆`.

The ambient dimension is `3`, so the common volume of a `δ`-tube enters as `δ ^ 2`; as in
`Kakeya/DimensionThree/MainLemma1/Cases.lean` the exponent `2` is written literally rather
than as `Module.finrank ℝ E - 1`, since `hdim` is already in force. -/
theorem multiplicity_le_of_frostmanAtEveryScale
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{_, u} (E := E))
    (hdim : Module.finrank ℝ E = 3)
    {β γ₀ : ℝ} (hβ0 : 0 ≤ β) (hγ₀ : γ₀ ∈ Set.Ioc β 1)
    (δ₀ : NNReal) (ηKF ηKKT : ℝ → ℝ) :
    ∃ ηStar > (0 : ℝ), ∀ (c α : ℝ), 0 < c → c ≤ γ₀ / 2 → 0 < α →
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ γ ∈ Set.Icc γ₀ 1,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
        ∀ {Cunif : NNReal}, Cunif ≤ ShadedTube.ssfUniformConst (Module.finrank ℝ E) →
        ∀ 𝒯 : ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) Cunif,
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (δ : ENNReal) ^ (params β γ₀ ηStar δ₀ ηKF ηKKT).ηGamma γ
          ≤ ShadedBody.fullness s (fun i => (T i).toShadedBody) →
        𝒯.tubeUniform.IsFrostmanAtEveryScale
          ((δ : ENNReal) ^ (-5 * (params β γ₀ ηStar δ₀ ηKF ηKKT).ε)) →
        multiplicity s (fun i => (T i).toShadedBody) ≤
          (δ : ENNReal) ^ (-α) *
            (δ : ENNReal) ^ (-2 * (γ - c)) *
            ((s.card : ENNReal) * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - (γ - c) / 2) := by
  -- The intended witness is the `η` of
  -- `StickyKakeya.volume_iUnionShade_ge_of_isFrostmanAtEveryScale` at `ε := γ₀ / 2`, which
  -- depends only on `γ₀` and `Cunif` and hence not on the parameter package.  Note that the
  -- route through `Kakeya.multiplicity_le_of_isFrostmanAtEveryScale` applies sticky Kakeya at
  -- half the *loss* exponent instead, so its `η` would depend on `p.ε` and the choice would be
  -- circular.  The remaining ingredient is `Kakeya.ml1Boot.card_le`.
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hdim]; norm_num)
  have hγ₀pos : 0 < γ₀ := lt_of_le_of_lt hβ0 hγ₀.1
  have hγ₀half : 0 < γ₀ / 2 := half_pos hγ₀pos
  obtain ⟨ηStar, hηStar_pos, hηStar_ev⟩ :=
    StickyKakeya.volume_iUnionShade_ge_of_isFrostmanAtEveryScale (E := E) hSFE
      (ε := γ₀ / 2) hγ₀half
  refine ⟨ηStar, hηStar_pos, ?_⟩
  intro c α hc0 hc hα
  let p := params β γ₀ ηStar δ₀ ηKF ηKKT
  have hspec := params_spec hβ0 hγ₀ hηStar_pos δ₀ ηKF ηKKT
  have hfiveEps : 5 * p.ε ≤ ηStar := by
    simpa [p, params] using hspec.fiveEpsLe
  let Cvol : ENNReal := (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
  let Ccard : ENNReal := (cardBound.C : ENNReal)
  let A : ENNReal := Cvol * Ccard
  have hA1 : (1 : ENNReal) ≤ A := by
    dsimp [A]
    rw [← one_mul (1 : ENNReal)]
    exact mul_le_mul' (ENNReal.one_le_coe_iff.mpr (one_le_pow₀ one_le_two))
      (ENNReal.one_le_coe_iff.mpr cardBound.one_le_C)
  have hAtop : A ≠ ⊤ := by
    dsimp [A]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hconst_ev : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      0 < δ ∧ δ ≤ 1 ∧ A ≤ (δ : ENNReal) ^ (-α) := by
    have hApos : (0 : ENNReal) < A := zero_lt_one.trans_le hA1
    have htop : A ^ (-1 / α) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg' hApos hAtop
    have hδ₁ : (0 : NNReal) < min 1 (A ^ (-1 / α)).toNNReal :=
      lt_min zero_lt_one (by
        rw [← ENNReal.coe_pos, ENNReal.coe_toNNReal htop]
        exact ENNReal.rpow_pos hApos hAtop)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ₁)]
      with δ (hδ_pos : 0 < δ) hδ_lt
    refine ⟨hδ_pos, hδ_lt.le.trans (min_le_left _ _),
      const_le_rpow_neg hA1 hAtop hα hδ_pos ?_⟩
    calc
      (δ : ENNReal) ≤ ((A ^ (-1 / α)).toNNReal : ENNReal) :=
        ENNReal.coe_le_coe.mpr (hδ_lt.le.trans (min_le_right _ _))
      _ = A ^ (-1 / α) := ENNReal.coe_toNNReal htop
  filter_upwards [hηStar_ev, hconst_ev] with δ hδ_sticky ⟨hδ_pos, hδ_le1, hC_le⟩
  intro γ hγ ι s T Cunif hCunif 𝒯 hB hED hfull hfrost
  have hδ_ne : (δ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hδ_pos).ne'
  -- `η(γ) ≤ η⋆`, so the fullness hypothesis at `η(γ)` implies fullness at `η⋆`
  have hηle : p.ηGamma γ ≤ ηStar := by
    dsimp [p, params]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hfull' : (δ : ENNReal) ^ ηStar ≤ ShadedBody.fullness s (fun i => (T i).toShadedBody) :=
    le_trans (ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ_le1) hηle) hfull
  -- `ShadedBody.fullness` is `NNReal`-valued; the sticky theorem's fullness hypothesis is
  -- stated in `NNReal`, so convert across the coercion.
  have hfull_nn : (δ ^ ηStar : NNReal) ≤ ShadedBody.fullness s (fun i => (T i).toShadedBody) :=
    ENNReal.coe_le_coe.mp
      (by simpa [ENNReal.rpow_ofNNReal hηStar_pos.le] using hfull')
  -- `5 ε ≤ η⋆`, so the `δ ^ (-5 ε)`-Frostman hypothesis implies `δ ^ (-η⋆)`-Frostman
  have hfrost' : 𝒯.tubeUniform.IsFrostmanAtEveryScale ((δ : ENNReal) ^ (-ηStar)) :=
    Tube.UniformTubeSet.IsFrostmanAtEveryScale.mono hfrost
      (ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ_le1) (by linarith [hfiveEps]))
  have hδ_sticky_union : (δ : ENNReal) ^ (γ₀ / 2) ≤ volume (⋃ i ∈ s, (T i).shade) :=
    hδ_sticky s T hB hED hCunif 𝒯 hfull_nn hfrost'
  let X : ENNReal := (s.card : ENNReal) * (δ : ENNReal) ^ (2 : ℕ)
  let a : ℝ := γ - c
  have hbound :=
    Kakeya.multiplicity_le_div_of_le_volume_iUnionShade hδ_le1 s T
      (u := (δ : ENNReal) ^ (γ₀ / 2))
      (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ_pos) ENNReal.coe_ne_top) hδ_sticky_union
  have hαge : γ₀ / 2 ≤ a := by
    dsimp [a]
    nlinarith [hc, hγ.1]
  have hαpos : 0 < a := lt_of_lt_of_le hγ₀half hαge
  have hαle2 : a ≤ 2 := by
    dsimp [a]
    nlinarith [hc0, hγ.2]
  -- the sharp count `|s| ≲ δ ^ (-4)` gives `X = |s| · δ² ≲ δ ^ (-2)`
  have hcard : (s.card : ENNReal) ≤ Ccard * (δ : ENNReal) ^ (-4 : ℝ) := by
    dsimp [Ccard]
    exact card_le hdim hδ_pos hδ_le1 s (fun i => (T i).toTube) hB hED
  have hX_le : X ≤ Ccard * (δ : ENNReal) ^ (-2 : ℝ) := by
    calc
      X ≤ Ccard * (δ : ENNReal) ^ (-4 : ℝ) * (δ : ENNReal) ^ (2 : ℕ) := by
        dsimp [X]
        exact mul_le_mul_left hcard _
      _ = Ccard * (δ : ENNReal) ^ (-2 : ℝ) := by
        rw [mul_assoc, ← ENNReal.rpow_natCast (δ : ENNReal) 2,
          ← ENNReal.rpow_add _ _ hδ_ne ENNReal.coe_ne_top]
        norm_num
  -- split `X = X ^ (α/2) · X ^ (1 - α/2)` and bound the first factor
  have hXsplit : X ≤ Ccard * (δ : ENNReal) ^ (-a) * X ^ (1 - a / 2) := by
    have hα2 : (0 : ℝ) ≤ a / 2 := by linarith
    rcases eq_or_ne X 0 with hX0 | hXne0
    · rw [hX0]
      exact zero_le
    have hδne2 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδ_pos)
    have hXtop : X ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (by simp [hδne2])) hX_le
    have hXα : X ^ (a / 2) ≤ Ccard * (δ : ENNReal) ^ (-a) := by
      calc
        X ^ (a / 2) ≤ (Ccard * (δ : ENNReal) ^ (-2 : ℝ)) ^ (a / 2) :=
          ENNReal.rpow_le_rpow hX_le hα2
        _ = Ccard ^ (a / 2) * (δ : ENNReal) ^ (-a) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hα2, ← ENNReal.rpow_mul,
            show (-2 : ℝ) * (a / 2) = -a by ring]
        _ ≤ Ccard * (δ : ENNReal) ^ (-a) := by
          have hCge1 : (1 : ENNReal) ≤ Ccard := by
            dsimp [Ccard]
            exact ENNReal.one_le_coe_iff.mpr cardBound.one_le_C
          have hCpow : Ccard ^ (a / 2) ≤ Ccard ^ (1 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le hCge1 (by linarith : a / 2 ≤ 1)
          exact mul_le_mul_left (by simpa using hCpow) _
    calc
      X = X ^ (a / 2) * X ^ (1 - a / 2) := by
        rw [← ENNReal.rpow_add _ _ hXne0 hXtop,
          show a / 2 + (1 - a / 2) = (1 : ℝ) by ring, ENNReal.rpow_one]
      _ ≤ Ccard * (δ : ENNReal) ^ (-a) * X ^ (1 - a / 2) := mul_le_mul_left hXα _
  -- absorb `Cvol · Ccard ≤ δ ^ (-ε)` and `δ ^ (-γ₀/2) ≤ δ ^ (-2α)` into `δ ^ (-ε) δ ^ (-2α)`
  have key : ∀ B : ENNReal, B ≤ (δ : ENNReal) ^ (-α) →
      B / (δ : ENNReal) ^ (γ₀ / 2) * (δ : ENNReal) ^ (-a)
        ≤ (δ : ENNReal) ^ (-α) * (δ : ENNReal) ^ (-2 * a) := by
    intro B hB
    calc
      B / (δ : ENNReal) ^ (γ₀ / 2) * (δ : ENNReal) ^ (-a)
          ≤ (δ : ENNReal) ^ (-α) / (δ : ENNReal) ^ (γ₀ / 2) * (δ : ENNReal) ^ (-a) :=
            mul_le_mul_left (ENNReal.div_le_div_right hB _) _
      _ = (δ : ENNReal) ^ (-α - γ₀ / 2) * (δ : ENNReal) ^ (-a) := by
            rw [ENNReal.rpow_sub _ _ hδ_ne ENNReal.coe_ne_top]
      _ = (δ : ENNReal) ^ (-α - a - γ₀ / 2) := by
            rw [← ENNReal.rpow_add _ _ hδ_ne ENNReal.coe_ne_top,
              show (-α - γ₀ / 2) + -a = -α - a - γ₀ / 2 by ring]
      _ ≤ (δ : ENNReal) ^ (-α - 2 * a) :=
            ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ_le1) (by nlinarith [hαge])
      _ = (δ : ENNReal) ^ (-α) * (δ : ENNReal) ^ (-2 * a) := by
            rw [← ENNReal.rpow_add _ _ hδ_ne ENNReal.coe_ne_top,
              show (-α + -2 * a : ℝ) = -α - 2 * a by ring]
  have hfinal : multiplicity s (fun i => (T i).toShadedBody) ≤
      (δ : ENNReal) ^ (-α) * (δ : ENNReal) ^ (-2 * a) * X ^ (1 - a / 2) := by
    calc
      multiplicity s (fun i => (T i).toShadedBody)
          ≤ Cvol * ((s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) /
              (δ : ENNReal) ^ (γ₀ / 2) :=
            hbound
      _ ≤ Cvol * X / (δ : ENNReal) ^ (γ₀ / 2) := by
            dsimp [X]
            rw [show (δ : ENNReal) ^ (Module.finrank ℝ E - 1) = (δ : ENNReal) ^ (2 : ℕ) by
              rw [hdim]]
      _ ≤ Cvol * (Ccard * (δ : ENNReal) ^ (-a) * X ^ (1 - a / 2)) / (δ : ENNReal) ^ (γ₀ / 2) := by
            exact ENNReal.div_le_div_right
              (by simpa [mul_assoc, mul_comm, mul_left_comm] using (mul_le_mul_left hXsplit Cvol)) _
      _ = (Cvol * Ccard) / (δ : ENNReal) ^ (γ₀ / 2) * (δ : ENNReal) ^ (-a) * X ^ (1 - a / 2) := by
            simp only [div_eq_mul_inv]
            ring
      _ ≤ (δ : ENNReal) ^ (-α) * (δ : ENNReal) ^ (-2 * a) * X ^ (1 - a / 2) := by
            exact mul_le_mul_left (key (Cvol * Ccard) hC_le) _
  simpa [p, a, X] using hfinal

end CaseSticky

end ml1Boot

end Kakeya
