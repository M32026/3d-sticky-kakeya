/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Shading
public import Kakeya.DimensionThree.MainLemma2.ShadedDividingScales
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineParams
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectConstantLedger

/-!
# The trial interface 

The defect route splits across two hands: one owns the twin window and the `(F)`/`(P)` terminal
derivation, the other owns the potential, the descent and the `(D)` exit.  They meet on exactly one
statement, and **neither owns it**: `Kakeya.ML2Core.TrialOutcomeAt`, the conclusion of one trial of
the refined source's `lem:defect-one-trial` (l.5793–5851), with alternative `(D)` folded in as the
potential drop of l.4092–4096.

```
 one trial of  (𝕊, Z)  produces one of
 (G₁)  μ(𝕊,Z) ≤ δ^{-β/2} · |⋃ Z|                                   the sticky / absolute exit
 (G₂)  μ(𝕊,Z) ≤ δ^{4ν} · (#𝕊)^β · |⋃ Z|                            the terminal gain
 (B)   ∃ ∅ ≠ 𝕊* ⊆ 𝕊, ∃ Z* ⊆ Z :  μ(𝕊,Z) ≤ Λ μ(𝕊*,Z*),
                                  λ(𝕊,Z)  ≤ Λ λ(𝕊*,Z*),
                                  Φ_h(𝕊*) + 1 ≤ Φ_h(𝕊),
                                  𝕊* is class-homogeneous on the SAME tower
```

`(B)` also hands back the retained pair's own shading level `lam'`, decayed by at most `Λ`: the
refined source's `λ(𝕊*,Z*) ≥ Λ⁻¹ λ(𝕊,Z)` (l.5836), which is what P2's fullness ladder carries across
the `P_max` trials (l.5949–5960).  `ML2Shaded.HasComparableDensities lam'⁻¹` is **not** listed: it
follows from the dense shading and `0 < lam'` by
`Kakeya.ML2Shaded.HasDenseShading.hasComparableDensities`.  The
*floor* `δ^{ηin}/2 ≤ lam` is **not** here either — it stays a binder of the producer and is
re-established at every step by the descent's own ladder (correction 2).

The `IsClassHomogeneousOn` conjunct is, and it is what closes the descent's
induction:
the trial may only be run on a family whose classes are two-sidedly banded
(`Kakeya.ML2Core.IsClassHomogeneousOn`, the hypothesis of `Kakeya.ML2Core.IsTrialAt`), and `(B)`
hands back exactly that band on the family it retains.  The source pays for it with the trial's own
vector-valued dyadic selection (l.5860–5940) at a single loss `Λ₀ ≤ Λ`: **a loss, not a constant**
(`Kakeya.ML2Core.not_reentry_le` is what a constant would cost).

## The three interface conditions, and where each is discharged by the text below

* **I-1 (condition `C-D1`).**  `𝒰` and `Cu` are **parameters**, not existentials.  The descent runs
  on **one** hierarchy for the whole loop and only the index set `S ⊆ u` varies.  This is not a
  convenience: every `GridUniform` restriction in the tree *squares* the uniformity constant
  (`Kakeya.MultiScaleFac.gridUniformBandConst`), so a trial that re-entered the uniformiser would
  accumulate `Cu ^ (2 ^ Pmax h δ)`, which no `δ`-free ceiling and no subpolynomial loss can absorb.  A producer that needs a fresh hierarchy is
  re-cutting this interface and must go back to the source comparison.
* **I-2 (the same family).**  `(B)` hands back a pair `(S', W)`, not a family and a separate
  shading: `W` refines `Z` tube-for-tube (`toTube` equal, `shade` contained), so `(G₁)`, `(G₂)` and
  the window clauses are all readable on the *same* pair at the next round (refined l.4483–4486).
* **I-3 (`h` and `Pmax` are named once).**  `Kakeya.ML2Core.potential` and
  `Kakeya.ML2Core.Pmax` live in `SpineDefectPotential.lean` and are *imported* here, so the two
  hands cannot each choose their own `h`.

## What is deliberately **not** in the statement

`TrialOutcomeAt` is the trial's **conclusion**, not the trial.  The admissibility binders — `S ⊆ u`,
the ball condition, the Katz–Tao bound at `ηin`, the fullness floor at `lam`, the block's
cardinality binder — belong to the *producer* `IsTrialAt` (`P7`), which is why `ηin` and `lam` do
not occur below.  Keeping them out is what lets the descent (`Kakeya.ML2Core.gain_of_trialDescent`)
consume this Prop without knowing how it was produced.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

/-- **The outcome of one trial** (refined source `lem:defect-one-trial`, l.5834–5851, with
alternative `(D)` of `lem:ml2-window-refinement`, l.4092–4096, folded in).

`Λ` is the per-trial loss, fixed once for the whole descent, and is a parameter for the same reason
`𝒰` is: two hands each choosing their own would make the ledgers diverge silently.

The three disjuncts are, in order, `Kakeya.ML2Assembly.Dichotomy`'s left disjunct at
`ε₀ = β/2`, its right disjunct at `g = 4·spineNu`, and the source's `(B)`. -/
def TrialOutcomeAt {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (β ϖ ε₁ h : ℝ) (gain dens : ℝ → ℝ)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (Λ : ℝ≥0∞) (lam : NNReal) (S : Finset ι)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) : Prop :=
  (∑ i ∈ S, volume (Z i).shade
      ≤ (δ : ℝ≥0∞) ^ (-(β / 2)) * volume (⋃ i ∈ S, (Z i).shade))
  ∨ (∑ i ∈ S, volume (Z i).shade
      ≤ (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens)
        * (S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (Z i).shade))
  ∨ (∃ S' ⊆ S, ∃ W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)),
      S'.Nonempty ∧
      (∀ i, (W i).toTube = (Z i).toTube) ∧
      (∀ i, (W i).shade ⊆ (Z i).shade) ∧
      (∑ i ∈ S, volume (Z i).shade) ≤ Λ * ∑ i ∈ S', volume (W i).shade ∧
      ShadedBody.fullness' S (fun i => (Z i).toShadedBody)
        ≤ Λ * ShadedBody.fullness' S' (fun i => (W i).toShadedBody) ∧
      potential h 𝒰 S' + 1 ≤ potential h 𝒰 S ∧
      IsClassHomogeneousOn 𝒰 S' ∧
      ∃ lam' : NNReal, 0 < lam' ∧ lam ≤ Λ * lam' ∧
        ML2Shaded.HasDenseShading lam' S' (fun i => (W i).toShadedBody))

/-! ## The trial outcome at free exit exponents -/

section Gain

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **`Kakeya.ML2Core.TrialOutcomeAt` with its two exit exponents freed.**

`ε₀` is the sticky/absolute exit's accuracy and `g` the terminal exit's gain.  Everything else —
the `(B)` alternative, its ledgers, the potential drop and the class band — is
`TrialOutcomeAt`'s, unchanged; `Kakeya.ML2Core.trialOutcomeAt_eq_gain` is the `rfl` that
witnesses it. -/
def TrialOutcomeAtGain (h ε₀ g β : ℝ)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (Λ : ℝ≥0∞) (lam : NNReal) (S : Finset ι)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) : Prop :=
  (∑ i ∈ S, volume (Z i).shade
      ≤ (δ : ℝ≥0∞) ^ (-ε₀) * volume (⋃ i ∈ S, (Z i).shade))
  ∨ (∑ i ∈ S, volume (Z i).shade
      ≤ (δ : ℝ≥0∞) ^ g * (S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (Z i).shade))
  ∨ (∃ S' ⊆ S, ∃ W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)),
      S'.Nonempty ∧
      (∀ i, (W i).toTube = (Z i).toTube) ∧
      (∀ i, (W i).shade ⊆ (Z i).shade) ∧
      (∑ i ∈ S, volume (Z i).shade) ≤ Λ * ∑ i ∈ S', volume (W i).shade ∧
      ShadedBody.fullness' S (fun i => (Z i).toShadedBody)
        ≤ Λ * ShadedBody.fullness' S' (fun i => (W i).toShadedBody) ∧
      potential h 𝒰 S' + 1 ≤ potential h 𝒰 S ∧
      IsClassHomogeneousOn 𝒰 S' ∧
      ∃ lam' : NNReal, 0 < lam' ∧ lam ≤ Λ * lam' ∧
        ML2Shaded.HasDenseShading lam' S' (fun i => (W i).toShadedBody))

/-- **Zero churn on the floor block's target.**  `TrialOutcomeAt` *is* `TrialOutcomeAtGain` at
`Dichotomy`'s own exponents; the generalisation adds nothing and removes nothing. -/
theorem trialOutcomeAt_eq_gain (β ϖ ε₁ h : ℝ) (gain dens : ℝ → ℝ)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (Λ : ℝ≥0∞) (lam : NNReal) (S : Finset ι)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) :
    TrialOutcomeAt β ϖ ε₁ h gain dens 𝒰 Λ lam S Z
      = TrialOutcomeAtGain h (β / 2) (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) β 𝒰 Λ lam S Z := rfl

end Gain

end Kakeya.ML2Core
