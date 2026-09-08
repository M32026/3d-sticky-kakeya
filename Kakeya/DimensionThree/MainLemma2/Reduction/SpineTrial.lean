/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ShadedDividingScales
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTrialOutcome

/-!
# `P7` — one trial 

`Kakeya.ML2Core.TrialOutcomeAt` is the *conclusion* of one trial; this file is the *producer* side.
The binder block is the existing one of `Kakeya.ML2Core.geometricCoreAt_of_rungMiddleFactor` — ball,
nonempty, `Δ_max ≤ δ^{-η_in}`, dense shading, comparable densities, `λ ≥ δ^{η_in}/2` — read **on the
current subfamily `S`, not on the ambient `u`**, because the whole point of the descent is that the
block must be re-runnable on the family the previous trial retained.

## `C-D1` in one line

`𝒰`, `Cu` and `Λ` are **parameters** and never move.  `Kakeya.ML2Core.not_reentry_le` is what the
alternative costs: re-entering `Kakeya.MultiScaleFac.exists_homogenizing_pass_gridUniform` once per
trial accumulates `Cu ^ 2 ^ (Pmax h δ)`, which no `δ`-free ceiling absorbs.  The price of staying on
one hierarchy is the single clause `Kakeya.ML2Core.IsClassHomogeneousOn` — a *loss* paid by the
trial's own dyadic selection (refined l.5860–5940), not a constant — and it appears here as a
**hypothesis** and in `TrialOutcomeAt`'s `(B)` as a **conclusion**.  That pair is what closes the
descent's induction.

## Two absences by design

* `Cstar ≤ δ^{-ν/20}` is absent: `Cstar` belongs to the window, which is produced *inside* the
  trial, not handed to it.
* `Cu ≤ Cu₀` is absent: under `C-D1` it is a parameter-level condition, stated once at the
  descent's own statement rather than at every trial.

The cardinality binder is 's option (a) — `#u ≤ δ^{-4}` alone, with the
`Cu ≤ δ^{-1}` threshold spent at the descent's statement — which is what
`Kakeya.ML2Core.potential_le_potentialCeil_five` consumes.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

/-- **One trial** (refined source `lem:defect-one-trial`, l.5793–5851, with the trichotomy of
`lem:ml2-window-refinement` folded in through `Kakeya.ML2Core.TrialOutcomeAt`).

Read it as the source reads its own lemma: *fixed* tower, *fixed* `(β, ω)` — here `ω = 0`, so the
two inputs are the `KatzTaoEstimate`/`FrostmanEstimate` the block already carries — and a quantifier
over the subfamilies the descent walks.  `𝒰`, `Cu` and `Λ` are parameters and never move: `C-D1`.

`IsClassHomogeneousOn 𝒰 S` is the re-entry clause.  It is a hypothesis here and a **conclusion of
`(B)`**, which is what closes the descent's induction: the trial may only be run on a family whose
classes are two-sidedly banded, and `(B)` hands back exactly that band on the family it retains.

`lam` is quantified **per trial**, not fixed: it is the source's `λ(𝕊,Z)`, which `(B)` decays by at
most `Λ` (l.5836).  The *floor* `δ^{ηin}/2 ≤ lam` stays a binder — the source's fixed
`λ ≥ δ^{2η₀}` (l.5834) — and the ladder `lam ≥ Λ^{P−P_max}·δ^{ηin}/2` that re-establishes it at
every step is `Kakeya.ML2Core.gain_of_trialDescent`'s, not the trial's (l.5949–5962).

The two exits sit one margin `Kakeya.ML2Core.defectMargin` inside `Dichotomy`'s own, because the
descent multiplies **both** by `Λ ^ P` and `Kakeya.ML2Core.absorbL_forces_trivial_loss` shows a
left exit already at `β/2` would force `Λ ^ P ≤ 1`.  The margin is `defectMargin`, **by name**: a
free parameter here could differ from the one the site's absorption hypotheses use, and the two
would compose only by luck ( constraint (4), condition I-3). -/
def IsTrialAt {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (β ϖ ε₁ h ηin : ℝ) (gain dens : ℝ → ℝ)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (Λ : ℝ≥0∞) : Prop :=
  ∀ S ⊆ u, ∀ Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)), ∀ lam : NNReal,
    S.Nonempty →
    (∀ i, (Z i).toTube = (T i).toTube) →
    (∀ i, (Z i).shade ⊆ (T i).shade) →
    IsClassHomogeneousOn 𝒰 S →
    (∀ i ∈ S, (Z i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
    Kakeya.maxDensity S (fun i => (Z i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) →
    ML2Shaded.HasDenseShading lam S (fun i => (Z i).toShadedBody) →
    ML2Shaded.HasComparableDensities lam⁻¹ S (fun i => (Z i).toShadedBody) →
    (δ : NNReal) ^ ηin / 2 ≤ lam →
    (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) →
    TrialOutcomeAtGain h (β / 2 - defectMargin β ϖ ε₁ gain dens)
      (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β 𝒰 Λ lam S Z

/-- **What the floor block's `F7` must deliver after the  re-cut, spelled out.**

`Kakeya.ML2Core.IsTrialAt` unfolded: the per-triple obligation, at the margin-shifted exits.  A
producer that proves this — for every retained family `S ⊆ u`, its shading `Z` and its shading level
`lam`, on the eleven binders — has produced the trial, and `:= hF7` is the whole wiring.

This is the `exact`-matchable form of the floor block's `F7alpha`.  Their conclusion changes from
`TrialOutcomeAt β ϖ ε₁ h gain dens 𝒰 Λ lam S T` to the `TrialOutcomeAtGain` below, and their budget
binder `hexp` from `4ν + θ₂ + η_in ≤ …` to `5ν + θ₂ + η_in ≤ …`, which that
budget allows for both terminal alternatives.  The `(G₁)` side owes nothing:
`Kakeya.ML2Core.stickyExit_pays_defectMargin`. -/
theorem isTrialAt_of_floorRoutes {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {β ϖ ε₁ h ηin : ℝ} {gain dens : ℝ → ℝ}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu} {Λ : ℝ≥0∞}
    (hF7 : ∀ S ⊆ u, ∀ Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)), ∀ lam : NNReal,
      S.Nonempty →
      (∀ i, (Z i).toTube = (T i).toTube) →
      (∀ i, (Z i).shade ⊆ (T i).shade) →
      IsClassHomogeneousOn 𝒰 S →
      (∀ i ∈ S, (Z i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      Kakeya.maxDensity S (fun i => (Z i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) →
      ML2Shaded.HasDenseShading lam S (fun i => (Z i).toShadedBody) →
      ML2Shaded.HasComparableDensities lam⁻¹ S (fun i => (Z i).toShadedBody) →
      (δ : NNReal) ^ ηin / 2 ≤ lam →
      (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) →
      TrialOutcomeAtGain h (β / 2 - defectMargin β ϖ ε₁ gain dens)
        (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β 𝒰 Λ lam S Z) :
    IsTrialAt β ϖ ε₁ h ηin gain dens 𝒰 Λ := hF7

end Kakeya.ML2Core
