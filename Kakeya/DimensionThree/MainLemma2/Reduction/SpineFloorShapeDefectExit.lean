/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectExit
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShape

/-!
# `R8` — when the refinement destroys the concentration, the trial exits through `(D)`

/§4.1 and (ii)/.  This is the row that **closes the
tetrachotomy** and retires `ParentInsideWindow`.

## The source's order of operations, and why there is no fourth case

l.5896–5905 [the refined source, quoted in (ii)]:

> *All simultaneous factorings and mass-coupled refinements in the middle window are completed
> **before** its asserted lower concentration is tested.  If that concentration is destroyed, there
> is a definite coordinate `(k,l)` for which `D_{k,l}(𝕊*) ≤ δ^{2h} D_{k,l}(𝕊')` … Thus the
> corresponding ceiling in the defect potential falls by at least one.*

**Refine first, then test; and the failure of the test is `(D)` and nothing else.**  So
's "fourth case" — *the fill level lies inside the window* — was never a
mathematical alternative: it is the shadow the missing device cast.  With the refinement performed
*before* the test, the branch in which the parent is not found is exactly the branch in which the
concentration did not survive, and that branch is `(D)`.

## What moves, and what does not

**`(D)`'s exit does not move at all.**  `Kakeya.ML2Core.profileDrop_of_concentration_destroyed`
reads `Kakeya.ML2Core.pairProfile` through `Kakeya.ML2Core.footprint`, i.e. on the **ambient**
hierarchy `𝒰` at the *occupied* nodes of the family — so the refinement's `S'` slots straight into
its `hafter` with no `Tube.UniformTubeSet.restrictOccupied` juggling and no statement change.  That
is the footprint design of  paying off a second time.

**`T-D1″` is preserved.**  `(B)` remains reachable **only** through
`profileDrop_of_concentration_destroyed`: `Kakeya.ML2Core.trialOutcomeAtGain_defect_of_refinement`
takes the potential drop as a hypothesis and never manufactures one, and
`Kakeya.ML2Core.defect_of_refinement_concentration_destroyed` obtains it from that theorem and from
nothing else.  No new route into `(B)` is opened.

## What `Kakeya.ML2Core.IsShadedRefinementOf` supplies, and the two clauses it does not

Of `(B)`'s nine conjuncts the refinement gives six outright — `S' ⊆ S`, `S'.Nonempty`, the tube
equality, the sub-shading, the **mass** retention and `IsClassHomogeneousOn` — and the potential
drop is `(D)`'s.  The remaining two are asked for explicitly rather than smuggled in:

* the **fullness** retention `Λ⁻¹·fullness' S ≤ fullness' S'` (l.4098–4102).  `IsShadedRefinementOf`
  carries the mass retention only — the same gap `M1`'s `(F)` binder had to name, and it is named here for the same reason;
* the density floor `∃ lam', 0 < lam' ∧ lam ≤ Λ·lam' ∧ HasDenseShading lam' S' W` (l.5836's decay of
  `λ(𝕊,Z)` by at most `Λ`).

Both are conclusions of the source's alternatives and neither is free in the tree, so both are
binders.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section DefectExit

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}

/-- **`R8`, the packaging half.**  A refinement that also buys a potential drop, a fullness
retention and a density floor *is* alternative `(B)` — the third disjunct of
`Kakeya.ML2Core.TrialOutcomeAtGain`.

The potential drop is a **hypothesis**: this theorem never manufactures one, which is what keeps
`T-D1″` (`(B)` reachable only through `profileDrop_of_concentration_destroyed`) true. -/
theorem trialOutcomeAtGain_defect_of_refinement {Λ : ℝ≥0∞} {h ε₀ g β : ℝ} {lam : NNReal}
    {S S' : Finset ι} {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (href : IsShadedRefinementOf 𝒰 Λ S Z S' W)
    (hfull : ShadedBody.fullness' S (fun i => (Z i).toShadedBody)
      ≤ Λ * ShadedBody.fullness' S' (fun i => (W i).toShadedBody))
    (hdrop : potential h 𝒰 S' + 1 ≤ potential h 𝒰 S)
    {lam' : NNReal} (hlam'0 : 0 < lam') (hlam' : lam ≤ Λ * lam')
    (hdense : ML2Shaded.HasDenseShading lam' S' (fun i => (W i).toShadedBody)) :
    TrialOutcomeAtGain h ε₀ g β 𝒰 Λ lam S Z :=
  Or.inr (Or.inr ⟨S', href.subset, W, href.nonempty, href.2.2.1, href.shade_subset,
    href.retention, hfull, hdrop, href.classHomogeneous, lam', hlam'0, hlam', hdense⟩)

/-- Destruction of the window's lower concentration after refinement gives a defect exit.
`profileDrop_of_concentration_destroyed` supplies the potential drop, which yields
the trial's `(B)` alternative. The concentration test is applied after refinement,
as in the refined source, lines 5899-5901. -/
theorem defect_of_refinement_concentration_destroyed {Λ : ℝ≥0∞} {ε₀ g β : ℝ} {lam : NNReal}
    {S S' : Finset ι} {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (href : IsShadedRefinementOf 𝒰 Λ S Z S' W)
    (hfull : ShadedBody.fullness' S (fun i => (Z i).toShadedBody)
      ≤ Λ * ShadedBody.fullness' S' (fun i => (W i).toShadedBody))
    {lam' : NNReal} (hlam'0 : 0 < lam') (hlam' : lam ≤ Λ * lam')
    (hdense : ML2Shaded.HasDenseShading lam' S' (fun i => (W i).toShadedBody))
    {h τ Θ : ℝ} (hh : 0 < h) (hΘ0 : 0 < Θ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {a m : ℕ} (ham : a < m) (hm : m ≤ Tube.ssfGridLen δ)
    (hΘ2 : 2 ≤ Θ ^ (τ / 2))
    (hbefore : ENNReal.ofReal (Θ ^ τ / 2) ≤ pairProfile 𝒰 S a m)
    (hafter : pairProfile 𝒰 S' a m ≤ ENNReal.ofReal (Θ ^ (τ / 2) / 2))
    (hgap : 2 * h ≤ (τ / 2) * (Real.log Θ / Real.log (1 / (δ : ℝ)))) :
    TrialOutcomeAtGain h ε₀ g β 𝒰 Λ lam S Z :=
  trialOutcomeAtGain_defect_of_refinement href hfull
    (profileDrop_of_concentration_destroyed 𝒰 href.subset hh hΘ0 hδ0 hδ1 ham hm hΘ2
      hbefore hafter hgap)
    hlam'0 hlam' hdense

/-- **The trichotomy, closed — and the exhaustiveness is a kernel fact.**

(4) requires that *"exhaustive by construction"* mean an `rcases` on a
`le_or_gt`, not a case-split on an assumed disjunction.  It does here: the split is on the
**survival test itself**,

```
    rcases le_or_gt (pairProfile 𝒰 S' a m) (ENNReal.ofReal (Θ ^ (τ / 2) / 2)) with hafter | hsurv
```

which is `le_or_gt` on `ℝ≥0∞` and nothing else.  The two branches are then the source's own two
outcomes of l.5899-5905:

* **the concentration did not survive the refinement** (`hafter`) — `(D)` fires and the trial exits
  through `(B)`;
* **it survived** (`hsurv`) — and *only then* is the floor route's gain available.  That is why
  `hgain` is stated as an **implication from survival** rather than as a bare inequality: the
  `(F)`/`(P)` producer may not be invoked in the branch where the test failed, and a bare hypothesis
  would have let it.

**An earlier cut of this theorem took the disjunction as a hypothesis `hsurvive` and called the
result "exhaustive by construction".  It was not** — the exhaustiveness was assumed.  The claim is
now carried by `le_or_gt` and the docstring says which. -/
theorem trialOutcomeAtGain_of_refinement_dichotomy {Λ : ℝ≥0∞} {h ε₀ g β : ℝ} {lam : NNReal}
    {S S' : Finset ι} {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (href : IsShadedRefinementOf 𝒰 Λ S Z S' W) (hβ : 0 ≤ β)
    (hfull : ShadedBody.fullness' S (fun i => (Z i).toShadedBody)
      ≤ Λ * ShadedBody.fullness' S' (fun i => (W i).toShadedBody))
    {lam' : NNReal} (hlam'0 : 0 < lam') (hlam' : lam ≤ Λ * lam')
    (hdense : ML2Shaded.HasDenseShading lam' S' (fun i => (W i).toShadedBody))
    {g' : ℝ} (habs : Λ * (δ : ℝ≥0∞) ^ g' ≤ (δ : ℝ≥0∞) ^ g)
    {τ Θ : ℝ} {a m : ℕ}
    -- the `(F)`/`(P)` route, available **only** in the branch where the concentration survives
    (hgain : ENNReal.ofReal (Θ ^ (τ / 2) / 2) < pairProfile 𝒰 S' a m →
      ∑ i ∈ S', volume (W i).shade
        ≤ (δ : ℝ≥0∞) ^ g' * (S'.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S', (W i).shade))
    -- `(D)`'s side conditions, unchanged
    (hh : 0 < h) (hΘ0 : 0 < Θ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (ham : a < m) (hm : m ≤ Tube.ssfGridLen δ) (hΘ2 : 2 ≤ Θ ^ (τ / 2))
    (hbefore : ENNReal.ofReal (Θ ^ τ / 2) ≤ pairProfile 𝒰 S a m)
    (hgap : 2 * h ≤ (τ / 2) * (Real.log Θ / Real.log (1 / (δ : ℝ)))) :
    TrialOutcomeAtGain h ε₀ g β 𝒰 Λ lam S Z := by
  rcases le_or_gt (pairProfile 𝒰 S' a m) (ENNReal.ofReal (Θ ^ (τ / 2) / 2)) with hafter | hsurv
  · exact defect_of_refinement_concentration_destroyed href hfull hlam'0 hlam' hdense
      hh hΘ0 hδ0 hδ1 ham hm hΘ2 hbefore hafter hgap
  · exact trialOutcomeAtGain_of_refinement_gain href hβ (hgain hsurv) habs

end DefectExit

/-! ### Controls -/

section Controls

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}

/-- **Control: `T-D1″` holds for this route.**
`Kakeya.ML2Core.trialOutcomeAtGain_defect_of_refinement` consumes a potential drop and never
produces one — witnessed by the fact that the drop is a named
hypothesis which the statement mentions, so no instance of the theorem can be formed without one
already in hand.  Compiled as the trivial re-export, which is the honest form of the claim: the only
way to reach `(B)` here is to supply `hdrop`. -/
theorem defect_route_needs_potential_drop {Λ : ℝ≥0∞} {h ε₀ g β : ℝ} {lam : NNReal}
    {S S' : Finset ι} {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (href : IsShadedRefinementOf 𝒰 Λ S Z S' W)
    (hfull : ShadedBody.fullness' S (fun i => (Z i).toShadedBody)
      ≤ Λ * ShadedBody.fullness' S' (fun i => (W i).toShadedBody))
    {lam' : NNReal} (hlam'0 : 0 < lam') (hlam' : lam ≤ Λ * lam')
    (hdense : ML2Shaded.HasDenseShading lam' S' (fun i => (W i).toShadedBody)) :
    (potential h 𝒰 S' + 1 ≤ potential h 𝒰 S) → TrialOutcomeAtGain h ε₀ g β 𝒰 Λ lam S Z :=
  fun hdrop => trialOutcomeAtGain_defect_of_refinement href hfull hdrop hlam'0 hlam' hdense

end Controls

end Kakeya.ML2Core
