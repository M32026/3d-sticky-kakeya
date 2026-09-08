/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteProducer
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeM1

/-!
# Row 15's two suppliers, made concrete

 the parameter comparison leaves the site discharge with exactly one hypothesis carrying
mathematics: `htrial : IsTrialAtGain ε₀ g β h ηin 𝒰 Λ`.  Two existing theorems conclude in that slot,
**both at the margin-shifted exits** [MEASURED: each ends
`∀ Λ, TrialOutcomeAtGain h (β/2 − defectMargin …) (4·spineNu … + defectMargin …) β 𝒰 Λ lam S T`]:

* `Kakeya.ML2Core.trialOutcome_middle_of_floorFactors_alpha` — the `(F)` route;
* `Kakeya.ML2Core.exists_trialOutcome_of_eccentric_alpha` — the `(P)` route.

This file names their remaining inputs so that the closure is `exact` the day those inputs land.

## The one place M1's swap happens

`Kakeya.ML2Core.FloorDataAt` is the `(F)` alternative at its **current** text
(`SpineFloorTerminal.lean:610–636`).  The floor-shape hand's M1 replaces that binder by
`RefinedFloorHypothesis …`; when it does, **only this `def`'s body changes** and every consumer
below — and every consumer downstream of them — is untouched.  That is why the `(F)` data is
wrapped in a `def` rather than inlined: a one-token retarget at one site instead of at each use.

**Honest label.**  The body below is transcribed from the existing text and is against it
line for line; that the transcription is *definitionally* F7alpha's own binder is
**[TO BE CHECKED AT APPLICATION]** — it is exactly what the `exact` in a future
`htrial_of_floorData ∘ trialOutcome_middle_of_floorFactors_alpha` will check, and it will fail
loudly rather than silently if the transcription drifts.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal Topology

namespace Kakeya.ML2Core

section FloorRoute

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **The `(F)` payload of `trialOutcome_middle_of_floorFactors_alpha`, PER FAMILY.**

`C-D1` put the trial's hierarchy on the ambient `u` with `S ⊆ u` varying,
and the `(F)` alternative moved with it: the refinement is asked of the *retained* family
`(S, Z)` inside the **inherited** tower `(𝒰.restrictOccupied hS hh).retube (funext ht)`, not of
the ambient `(u, T)`.

An ambient
payload cannot feed any `(F)` supplier: `RefinedFloorHypothesis`'s conclusions carry `(#·)^β`
and `|⋃ ·|`, both **monotone increasing** in the family, so a statement about `(u, T)` bounds
the wrong side for `S ⊊ u` and does not specialise down.  The window `(a, b, m)` is per family
for the same reason, and is existential here rather than a parameter.

This `def` is still the single point at which the floor block's `(F)` text is named. -/
def FloorDataAt (β ϖ ε₁ η' : ℝ) (gain dens : ℝ → ℝ) {C : NNReal} {Kl cl : ℕ}
    (Λf : ℝ≥0∞)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu) : Prop :=
  ∀ (S : Finset ι) (hS : S ⊆ u) (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S),
    ∃ a b m : ℕ,
      RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
        η' Λf ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m

/-- **The `(F)` payload over the whole filter.**  `Kakeya.ML2Core.FloorDataAt` at every scale and
every ambient family — the named hypothesis the `(F)` route still owes. -/
def FloorPayload.{w} (β ϖ ε₁ η' : ℝ) (gain dens : ℝ → ℝ) {C : NNReal} {Kl cl : ℕ}
    (Λf : NNReal → ℝ≥0∞) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type w} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu : NNReal)
      (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu),
      FloorDataAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens (Λf δ) 𝒰

/-- **The `(F)` supplier of row 15, at one scale.**

`hF7` is the `C-D1` `trialOutcome_middle_of_floorFactors_alpha`'s per-`δ` conclusion, and `hΛf` its
per-`δ` absorption row.  The proof is one positional application — the floor owner's
`M1PROBE_supplier` check, localised. -/
theorem htrial_of_floorData {β ϖ ε₁ η' h ηin : ℝ} {gain dens : ℝ → ℝ}
    {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu} {Λ : ℝ≥0∞}
    (hF7 : ∀ (a b m : ℕ) (S : Finset ι) (hS : S ⊆ u)
      (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (lam : NNReal),
      S.Nonempty →
      ∀ (ht : ∀ i, (Z i).toTube = (T i).toTube),
      (∀ i, (Z i).shade ⊆ (T i).shade) →
      ∀ (hh : IsClassHomogeneousOn 𝒰 S),
      (∀ i ∈ S, (Z i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      Kakeya.maxDensity S (fun i => (Z i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) →
      ML2Shaded.HasDenseShading lam S (fun i => (Z i).toShadedBody) →
      ML2Shaded.HasComparableDensities lam⁻¹ S (fun i => (Z i).toShadedBody) →
      (δ : NNReal) ^ ηin / 2 ≤ lam →
      (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) →
      Λf * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
            + 2 * defectMargin β ϖ ε₁ gain dens)
          ≤ (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
            + defectMargin β ϖ ε₁ gain dens) →
      RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
        η' Λf ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m →
      ∀ Λ' : ℝ≥0∞, TrialOutcomeAtGain h (β / 2 - defectMargin β ϖ ε₁ gain dens)
        (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β 𝒰 Λ' lam S Z)
    (hΛf : Λf * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
          + 2 * defectMargin β ϖ ε₁ gain dens)
        ≤ (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
          + defectMargin β ϖ ε₁ gain dens))
    (hfloor : FloorDataAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf 𝒰) :
    IsTrialAtGain (β / 2 - defectMargin β ϖ ε₁ gain dens)
      (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β h ηin 𝒰 Λ := by
  intro S hS Z lam hne ht hs hh hb hmx hd hc hl hcard
  obtain ⟨a, b, m, hf⟩ := hfloor S hS Z ht hh
  exact hF7 a b m S hS Z lam hne ht hs hh hb hmx hd hc hl hcard hΛf hf Λ

/-- **The `(P)` supplier of row 15**, from `exists_trialOutcome_of_eccentric_alpha` (F5alpha,
existing the estimate).  `hecc` is its tail once the eccentric plank data is supplied per family. -/
theorem htrial_of_eccentricData {β ϖ ε₁ h ηin : ℝ} {gain dens : ℝ → ℝ}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu} {Λ : ℝ≥0∞}
    {EccData : Prop}
    (hecc : ∀ S ⊆ u, ∀ Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)), ∀ lam : NNReal,
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
      EccData →
      TrialOutcomeAtGain h (β / 2 - defectMargin β ϖ ε₁ gain dens)
        (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β 𝒰 Λ lam S Z)
    (hdata : EccData) :
    IsTrialAtGain (β / 2 - defectMargin β ϖ ε₁ gain dens)
      (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β h ηin 𝒰 Λ :=
  fun S hS Z lam hne ht hs hh hb hmx hd hc hl hcard =>
    hecc S hS Z lam hne ht hs hh hb hmx hd hc hl hcard hdata

end FloorRoute

end Kakeya.ML2Core
