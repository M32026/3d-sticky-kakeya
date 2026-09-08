/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeHwinfloor

/-!
# The `RR1` delta, isolated: the `(F)` payload **with** the nonemptiness binder

`Kakeya.ML2Core.not_floorPayload`  shows
`Kakeya.ML2Core.FloorPayload` is **false as stated**: `Kakeya.ML2Core.FloorDataAt` quantifies over
`S = ∅`, where the `(F)` predicate is unsatisfiable.  `RR1` asks the source comparison to add one binder,
`(hne : S.Nonempty)`, to the existing `def`.

**This file does not edit the existing `def`.**  It carries the repaired predicate under a *new* name
and re-proves the two theorems the repair touches, so that the whole cost of `RR1` is visible in one
place and can be re-cut cheaply if source routes the nonemptiness elsewhere (onto
`Kakeya.ML2Core.RefinedFloorHypothesis`, or onto `Kakeya.ML2Core.IsClassHomogeneousOn`, or onto the
`(F)` predicate itself).  In that case only this file changes.

The delta is **exactly one positional argument**, twice:

* `Kakeya.ML2Core.htrial_of_floorDataNonempty` is `htrial_of_floorData` with `hfloor` applied to the
  `hne` that `IsTrialAtGain` already binds;
* `Kakeya.ML2Core.trialSupplier_of_floorRouteNonempty` is `trialSupplier_of_floorRoute` with `hfl`
  applied to the `hne` that `TrialSupplier` already binds.

Neither proof needs anything new: the nonemptiness is in scope at both call sites already, which is
the evidence that the binder belongs on `FloorDataAt` and costs nothing downstream.

The loop is then closed: `Kakeya.ML2Core.floorPayloadNonempty_of_rows` produces the repaired payload
from `hwinfloor` alone (the estimate removed the line-ED row), and
`trialSupplier_of_floorRouteNonempty` turns it into `Kakeya.ML2Core.TrialSupplier` — the form the
closure consumes.
-/

@[expose] public section

open MeasureTheory Metric Tube Topology Filter
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section Defs

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- `Kakeya.ML2Core.FloorDataAt` with the `RR1` binder `(hne : S.Nonempty)`.  Everything else is
to the existing text. -/
def FloorDataAtNonempty (β ϖ ε₁ η' : ℝ) (gain dens : ℝ → ℝ) {C : NNReal} {Kl cl : ℕ}
    (Λf : ℝ≥0∞)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu) : Prop :=
  ∀ (S : Finset ι) (hS : S ⊆ u), S.Nonempty →
    ∀ (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S),
      ∃ a b m : ℕ,
        RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
          η' Λf ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m

/-- `Kakeya.ML2Core.FloorPayload` over the repaired per-scale predicate. -/
def FloorPayloadNonempty.{w} (β ϖ ε₁ η' : ℝ) (gain dens : ℝ → ℝ)
    {C : NNReal} {Kl cl : ℕ} (Λf : NNReal → ℝ≥0∞) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type w} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu : NNReal)
      (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu),
      FloorDataAtNonempty (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens (Λf δ) 𝒰

/-- **Control: the repair is a genuine weakening.**  The existing predicate implies the repaired one;
the converse fails by `Kakeya.ML2Core.not_floorDataAt`, so `RR1` does not silently strengthen
anything. -/
theorem floorDataAt_toNonempty {β ϖ ε₁ η' : ℝ} {gain dens : ℝ → ℝ}
    {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (h : FloorDataAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf 𝒰) :
    FloorDataAtNonempty (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf 𝒰 :=
  fun S hS _ Z ht hh => h S hS Z ht hh

end Defs

/-! ### The producer: `hwinfloor`, and nothing else -/

section Producer

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **The repaired per-scale payload from its one row.**
`Kakeya.ML2Core.floorDataAt_nonempty_of_rows` packaged into `Kakeya.ML2Core.FloorDataAtNonempty`;
`hdev` is discharged internally by the identity refinement. -/
theorem floorDataAtNonempty_of_rows {β ϖ ε₁ η' : ℝ} {gain dens : ℝ → ℝ}
    {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞} (hΛf : 1 ≤ Λf)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (hwinfloor : ∀ (S : Finset ι) (hS : S ⊆ u)
      (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (ht : ∀ i, (Z i).toTube = (T i).toTube)
      (hh : IsClassHomogeneousOn 𝒰 S)
      (S' : Finset ι) (W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (hS' : S' ⊆ S)
      (hhom' : IsClassHomogeneousOn ((𝒰.restrictOccupied hS hh).retube (funext ht)) S')
      (hW : (fun i => (W i).toTube) = (fun i => (Z i).toTube)),
      IsShadedRefinementOf 𝒰 Λf S Z S' W →
      ∃ a b m : ℕ,
        ML2Reduction.IsKatzTaoDividingWindowLevels
          (refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht)) hS' hhom' hW)
          ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) (ML2Spine.spineRung β ϖ ε₁ gain dens)
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m ∧
        FloorHypothesisAt β ϖ ε₁ gain dens η'
          (refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht)) hS' hhom' hW) a b m) :
    FloorDataAtNonempty (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf 𝒰 :=
  fun S hS hne Z ht hh =>
    floorDataAt_nonempty_of_rows hΛf 𝒰 hwinfloor S hS Z ht hh hne

end Producer

/-! ### The `RR1` delta at the two consumers, and the loop to `TrialSupplier` -/

section Delta

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **Delta 1.**  `Kakeya.ML2Core.htrial_of_floorData` with the repaired payload: the proof is the
existing one plus the `hne` that `Kakeya.ML2Core.IsTrialAtGain` already binds. -/
theorem htrial_of_floorDataNonempty {β ϖ ε₁ η' h ηin : ℝ} {gain dens : ℝ → ℝ}
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
    (hfloor : FloorDataAtNonempty (C := C) (Kl := Kl) (cl := cl)
      β ϖ ε₁ η' gain dens Λf 𝒰) :
    IsTrialAtGain (β / 2 - defectMargin β ϖ ε₁ gain dens)
      (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β h ηin 𝒰 Λ := by
  intro S hS Z lam hne ht hs hh hb hmx hd hc hl hcard
  obtain ⟨a, b, m, hf⟩ := hfloor S hS hne Z ht hh
  exact hF7 a b m S hS Z lam hne ht hs hh hb hmx hd hc hl hcard hΛf hf Λ

end Delta

section Loop

open scoped Classical in
/-- **Delta 2, and the loop closed.**  `Kakeya.ML2Core.trialSupplier_of_floorRoute` with the
repaired payload: again the existing proof plus the `hne` that `Kakeya.ML2Core.TrialSupplier` already binds.

This is the exact form the closure consumes — the descent's
`trialSupplier_of_floorRoute (…_alpha … (polylogLoss K') hexp hfac)
(eventually_hΛf_polylogLoss …) hfloor : TrialSupplier …` with `hfloor` at the repaired predicate. -/
theorem trialSupplier_of_floorRouteNonempty.{w} {β ϖ ε₁ ηin η' h : ℝ} {gain dens : ℝ → ℝ}
    {C : NNReal} {Kl cl : ℕ} {Cu₀ : NNReal} {Λf : NNReal → ℝ≥0∞}
    (hF7 : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type w} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (Cu : NNReal) (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (a b m : ℕ) (S : Finset ι) (hS : S ⊆ u)
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
        Cu ≤ Cu₀ →
        Λf δ * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
              + 2 * defectMargin β ϖ ε₁ gain dens)
            ≤ (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
              + defectMargin β ϖ ε₁ gain dens) →
        RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
          η' (Λf δ) ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m →
        ∀ Λ : ℝ≥0∞, TrialOutcomeAtGain h (β / 2 - defectMargin β ϖ ε₁ gain dens)
          (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β 𝒰 Λ lam S Z)
    (hΛf : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      Λf δ * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
            + 2 * defectMargin β ϖ ε₁ gain dens)
          ≤ (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
            + defectMargin β ϖ ε₁ gain dens))
    (hfloor : FloorPayloadNonempty.{w} (C := C) (Kl := Kl) (cl := cl)
      β ϖ ε₁ η' gain dens Λf) :
    TrialSupplier.{w} β ϖ ε₁ ηin h gain dens Cu₀ Λf := by
  filter_upwards [hF7, hΛf, hfloor] with δ hδ hΛ hfl
  intro ι u T Cu 𝒰 hCu hcard S hS Z lam hne ht hs hh hb hmx hd hc hl hcard'
  obtain ⟨a, b, m, hf⟩ := hfl u T Cu 𝒰 S hS hne Z ht hh
  exact hδ u T Cu 𝒰 a b m S hS Z lam hne ht hs hh hb hmx hd hc hl hcard' hCu hΛ hf (Λf δ)

end Loop

end Kakeya.ML2Core

end
