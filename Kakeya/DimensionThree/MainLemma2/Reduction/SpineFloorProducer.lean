/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorTerminal
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShape

/-!
# The `hfloor` producer — what produces `RefinedFloorHypothesis` per family, field by field

After the C-D1 re-cut the (F) route's single hypothesis is the per-family
payload

`hfloor : ∀ᶠ δ, ∀ u T Cu 𝒰 S (hS : S ⊆ u) Z (ht) (hh), ∃ a b m,
  RefinedFloorHypothesis … (Λf δ) ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m`.

This leaf maps the three fields of `RefinedFloorHypothesis` (`SpineFloorShapeM1.lean`) to what the
tree produces today, compiles the rows the floor block can produce now, and states the assembly
`hfloor_of_producers` with the rows still waiting on other owners as **named hypotheses**.

| field | status |
|---|---|
| refined pair `(S', W)` with `IsShadedRefinementOf` | device `exists_shadedRefinement_of_pass` (R0′, existing) — but at the δ-power `refinementLoss`, needing a pairwise `IsEssentiallyDistinct` row the trial does not carry, and `2 ≤ Cu`: **WAITING** on R0′'s re-cut (floor-shape hand) and on the site (ED row, `2 ≤ Cu`). The transport of the predicate from the ambient `𝒰` to the `S`-restricted, `Z`-retubed hierarchy is **PRODUCIBLE**: `isShadedRefinementOf_restrict_retube_iff`. |
| (former) `fullness S' W ≥ δ^{η_in}` | **DROPPED**: the rate lives in the trial's hereditary `HasDenseShading lam S Z` and `δ^{η_in}/2 ≤ lam`; the engine `_bound` takes mass positivity from the dense shading. A fullness rate on a refinement with untouched shading is one lemma away: `fullness_refinement_of_denseShading` (kept, standalone). |
| twin `IsKatzTaoDividingWindowLevels` on `refinedHierarchy` | **no producer by design** (C-M1c: incomparable with the ambient twin; its failure is (D), `trialOutcomeAtGain_of_refinement_dichotomy`, R8): **WAITING** on the (D) routing.
-/

@[expose] public section

open MeasureTheory Tube Topology Filter
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-! ### PRODUCIBLE rows -/

open Classical in
/-- **The refinement predicate is insensitive to the hierarchy's restriction and retubing.**  The
ambient `𝒰` enters `IsShadedRefinementOf` only through `IsClassHomogeneousOn 𝒰 S'`, which reads
`cover.assign` and `Cu` alone — both unchanged by `restrictOccupied` and `retube`
(`isClassHomogeneousOn_restrictOccupied_iff`, `isClassHomogeneousOn_retube_iff`, both `Iff.rfl`).  So
a refinement of `(S, Z)` produced against the ambient hierarchy is a refinement against the
`S`-restricted, `Z`-retubed one, which is the hierarchy `RefinedFloorHypothesis` is read on. -/
theorem isShadedRefinementOf_restrict_retube_iff
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {S : Finset ι} (hS : S ⊆ u) (hh : IsClassHomogeneousOn 𝒰 S)
    {Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (ht : ∀ i, (Z i).toTube = (T i).toTube)
    (Λ : ℝ≥0∞) (S' : Finset ι) (W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) :
    IsShadedRefinementOf ((𝒰.restrictOccupied hS hh).retube (funext ht)) Λ S Z S' W
      ↔ IsShadedRefinementOf 𝒰 Λ S Z S' W :=
  Iff.rfl

/-- **Fullness of the refinement from the site's dense shading, at `δ^{η_in}/2`.**  When the
refinement leaves the shading untouched (`W = Z`, as `exists_shadedRefinement_of_pass` does),
`IsTrialAtGain`'s two rows `HasDenseShading lam S Z` and `δ^{η_in}/2 ≤ lam` give
`fullness S' Z ≥ δ^{η_in}/2` on every nonempty `S' ⊆ S` — through the existing
`HasDenseShading.le_fullness_tube` (which yields the average `fullness'`) and `coe_fullness`
(`fullness' = ↑fullness`), so the conclusion is the **unprimed**, `NNReal`-valued
`ShadedBody.fullness` that `RefinedFloorHypothesis` and the engine consume.
The payload carries no fullness clause; this is the "one lemma away" rate. -/
theorem fullness_refinement_of_denseShading (hδ0 : 0 < δ) {lam : NNReal} {S S' : Finset ι}
    {Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hdense : ML2Shaded.HasDenseShading lam S (fun i ↦ (Z i).toShadedBody))
    (hS' : S' ⊆ S) (hne : S'.Nonempty) {ηin : ℝ} (hlam : (δ : NNReal) ^ ηin / 2 ≤ lam) :
    (δ : NNReal) ^ ηin / 2 ≤ ShadedBody.fullness S' (fun i ↦ (Z i).toShadedBody) := by
  have h := (hdense.subset hS').le_fullness_tube hδ0 hne
  rw [← ShadedBody.coe_fullness, ENNReal.coe_le_coe] at h
  exact hlam.trans h

/-! ### The assembly, with the WAITING rows as named hypotheses -/

open Classical in
/-- **`hfloor` from its producers, per family and per `δ`.**  Given, at a fixed `δ` and for the
family `(S, Z)` inside the ambient hierarchy `𝒰` on `u`:

* `hdev` — the simultaneous refinement of `(S, Z)` at loss `Λf` (**WAITING**: R0′ re-cut to the
  polylogarithmic loss; the ED row and `2 ≤ Cu` from the site);
* `hwinfloor` — for every refinement, a window `(a, b, m)` at which the twin holds on the refined
  hierarchy **and** the existing floor payload holds there (**WAITING**: the twin is the (D)-routed
  clause, R8; the floor payload is R7 over F4a);

the per-family payload `∃ a b m, RefinedFloorHypothesis … Λf (restricted, retubed hierarchy) a b m`
follows, the refinement predicate transported by `isShadedRefinementOf_restrict_retube_iff`.  There is no fullness row.  No row is
proved that is not condition; every hypothesis below is a row of the ledger with a named owner. -/
theorem hfloor_of_producers {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {η' : ℝ}
    {C : NNReal} {Kl cl : ℕ} (Λf : ℝ≥0∞)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {S : Finset ι} (hS : S ⊆ u) {Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S)
    (hdev : ∃ (S' : Finset ι) (W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      IsShadedRefinementOf 𝒰 Λf S Z S' W)
    (hwinfloor : ∀ (S' : Finset ι) (W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (hS' : S' ⊆ S)
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
    ∃ a b m : ℕ, RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
      η' Λf ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m := by
  obtain ⟨S', W, href⟩ := hdev
  have hS' : S' ⊆ S := href.subset
  have hhom' : IsClassHomogeneousOn ((𝒰.restrictOccupied hS hh).retube (funext ht)) S' :=
    href.classHomogeneous
  have hW : (fun i => (W i).toTube) = (fun i => (Z i).toTube) := funext href.2.2.1
  obtain ⟨a, b, m, hwin, hflo⟩ := hwinfloor S' W hS' hhom' hW href
  exact ⟨a, b, m, S', W, hS', hhom', hW,
    (isShadedRefinementOf_restrict_retube_iff 𝒰 hS hh ht Λf S' W).mpr href, hwin, hflo⟩

end Kakeya.ML2Core

end
