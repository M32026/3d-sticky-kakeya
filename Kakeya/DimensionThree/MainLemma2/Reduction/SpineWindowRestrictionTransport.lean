/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeRoute
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeDichotomyGap

/-!
# `A2`: what complete-cell restriction does and does not keep, and the source's own dichotomy

 The refined source gives the `(F)`/`(P)`/`(D)` producer to the simultaneous refinement of
l.4056-4059, proved at l.4112-4153.

## The measurement, and it is asymmetric

l.4148-4151 says *"complete-cell restriction keeps the factor-two tower statistics"*.  Read against
`ML2Reduction.IsKatzTaoDividingWindowLevels`, that is **half true, and the half that fails is
exactly the source's `(D)`**:

* `level_density_band` is a **two-sided** band `Φ p c ≤ Δ_max(…) ≤ C_⋆ · Φ p c`.  Restriction
  shrinks the class (`Tube.coverClass_subset_of_subset`), and `Kakeya.maxDensity` is **monotone**,
  so the density can only **drop**.  The **upper** half therefore transports to any subfamily,
  unconditionally: `levelDensityBand_upper_of_subset`.
* The **lower** half — and `le_level_maxDensity`, which is also a lower bound on a `maxDensity` —
  points the wrong way and does **not** transport.  `maxDensity_coverClass_image_mono` is the
  witness of the direction.

This is not a gap in the bookkeeping.  It is the source's own case split, l.4121-4123: *"If a
required lower concentration fails after the restrictions, then for one `m ∈ 𝒲` the old value is
larger than `½Θ_m^τ`, while the new value is smaller than `½Θ_m^{τ/2}` … This is (D)."*  The
lower bounds are precisely the "required lower concentration", their survival is precisely the
`(F)` branch, and their failure is precisely `(D)`.  So the tree's note *"the window `(a,b,m)` is
born here"* and 's condition are the same statement from two sides, as the
source comparison said.

Recorded in the idiom the tree already uses for asymmetric transport
(`MainLemma2/JointRefinementObstruction.lean`: upper survives, lower does not, with a witness) rather than as a new convention.

## What this file supplies, and what it does not

It supplies the transport that is true, the named obligation that is not, and the source's
dichotomy skeleton (`floorDataAtTrichotomy_of_lowerConcentrationDichotomy`) which composes an
`(F)` producer and a `(D)` producer into `Kakeya.ML2Core.FloorDataAtTrichotomy` at exactly the case
split of l.4121/l.4133.

It does **not** supply an unconditional producer of `FloorDataAtTrichotomy`: the two branch
producers remain open, and their exact goals are named here.  Nothing is assumed as an axiom and
no existing or guarded statement is touched.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `maxDensity_coverClass_image_mono` | two families `S' ⊆ S`, the **ambient** cover data; no shading | the pair `(p,c)` of `level_density_band`, both free |
| `levelDensityBand_upper_of_subset` | as above | `(p,c)`, both free |
| `LowerConcentrationSurvivesAt` | `S' ⊆ S` under the ambient cover; no shading | `(p,c)`, both free |
| `floorDataAtTrichotomy_of_lowerConcentrationDichotomy` | `𝒰` on `(u,T)`; the branch families are `S ⊆ u` with shading `Z` | the window triple `(a,b,m)` is **existential**, born in the branch producers — not fixed here |

The window triple is deliberately not pinned in the skeleton: l.4133-4136 has the genuine parent
`p` determined *inside* the `(F)` branch, so fixing `(a,b,m)` before the case split would be the
level-pair conflation this column exists to catch.
-/

@[expose] public section

open MeasureTheory Metric Tube Topology Filter
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section RestrictionTransport

variable {ι : Type*} [DecidableEq ι]

/-- **The direction,.**  Restriction can only *decrease* a two-level maximal density,
because the class shrinks and `Kakeya.maxDensity` is monotone.  This single fact is why the
band's upper half transports and its lower half cannot.

**Family:** `S' ⊆ S` read through the ambient cover data.  **Level pair:** `(p,c)`, both free. -/
theorem maxDensity_coverClass_image_mono {S' S : Finset ι} (hS' : S' ⊆ S)
    (assign assignc : ι → ι) (j : ι)
    (Wc : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    Kakeya.maxDensity ((coverClass S' assign j).image assignc) Wc
      ≤ Kakeya.maxDensity ((coverClass S assign j).image assignc) Wc :=
  Kakeya.maxDensity_mono _ (Finset.image_subset_image (coverClass_subset_of_subset hS' assign j))

/-- **The half of l.4148-4151 that is true, unconditionally.**  Any upper bound on a two-level
maximal density survives complete-cell restriction — no hypothesis on the restriction at all.

**Family:** `S' ⊆ S`.  **Level pair:** `(p,c)`, both free. -/
theorem levelDensityBand_upper_of_subset {S' S : Finset ι} (hS' : S' ⊆ S)
    (assign assignc : ι → ι) (j : ι)
    (Wc : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) {Cstar Φpc : ENNReal}
    (hub : Kakeya.maxDensity ((coverClass S assign j).image assignc) Wc ≤ Cstar * Φpc) :
    Kakeya.maxDensity ((coverClass S' assign j).image assignc) Wc ≤ Cstar * Φpc :=
  (maxDensity_coverClass_image_mono hS' assign assignc j Wc).trans hub

/-- **The half that does not transport, named as the source's own condition** (l.4121-4123).

`LowerConcentrationSurvivesAt S' S assign assignc j Wc Φpc` is exactly *"the required lower
concentration survives the restriction"* at one class and one level pair.  It is a **named
obligation, not an axiom**: `(F)` is the branch where it holds, `(D)` the branch where it fails,
and `floorDataAtTrichotomy_of_lowerConcentrationDichotomy` below consumes precisely that split.

**Family:** `S' ⊆ S`.  **Level pair:** `(p,c)`, both free. -/
def LowerConcentrationSurvivesAt (S' : Finset ι) (assign assignc : ι → ι) (j : ι)
    (Wc : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (Φpc : ENNReal) : Prop :=
  Φpc ≤ Kakeya.maxDensity ((coverClass S' assign j).image assignc) Wc

/-- The ambient lower bound alone does **not** give the restricted one; it is the restricted
statement that must be established, and that is what this reduction records.  Stated so the
asymmetry is rather than asserted in prose. -/
theorem lowerConcentration_of_survives {S' : Finset ι} {assign assignc : ι → ι} {j : ι}
    {Wc : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {Φpc : ENNReal}
    (h : LowerConcentrationSurvivesAt S' assign assignc j Wc Φpc) :
    Φpc ≤ Kakeya.maxDensity ((coverClass S' assign j).image assignc) Wc := h

end RestrictionTransport

section Dichotomy

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **The source's dichotomy, composed** (l.4121 for `(D)`, l.4133 for `(F)`).

`Surv` is the run-time reading of *"the required lower concentration survives the restrictions"*.
The source's proof is exactly this case split: where `Surv` fails, one `d_{a,m}` gap of at least
`2h` drops a ceiling and no other ceiling rises — that is `(D)`; where it holds, complete factor
cells are retained and the genuine parent `p` appears — that is `(F)`.

`(P)` is handled separately: the tree routes it through the separate
supplier `Kakeya.ML2Core.htrial_of_eccentricData`, recorded as a faithful rendering choice.

**Family/shading:** `𝒰` on `(u, T)`; each branch runs on `S ⊆ u` with the shading `Z`.
**Level pair:** the window triple `(a,b,m)` is existential and is produced *inside* the `(F)`
branch, per l.4133-4136 — it is not fixed before the split. -/
theorem floorDataAtTrichotomy_of_lowerConcentrationDichotomy
    {β ϖ ε₁ η' h : ℝ} {gain dens : ℝ → ℝ} {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (Surv : Finset ι → (ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) → Prop)
    (hF : ∀ (S : Finset ι) (hS : S ⊆ u), S.Nonempty →
      ∀ (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S),
        Surv S Z →
        ∃ a b m : ℕ, RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
          η' Λf ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m)
    (hD : ∀ (S : Finset ι), S ⊆ u → S.Nonempty →
      ∀ (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (Z i).toTube = (T i).toTube) → IsClassHomogeneousOn 𝒰 S → ∀ lam : NNReal,
        ¬ Surv S Z → DefectBranchAt h Λf lam 𝒰 S Z) :
    FloorDataAtTrichotomy (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' h gain dens Λf 𝒰 := by
  classical
  intro S hS hne Z ht hh lam
  by_cases hs : Surv S Z
  · obtain ⟨a, b, m, hf⟩ := hF S hS hne Z ht hh hs
    exact ⟨a, b, m, Or.inl hf⟩
  · exact ⟨0, 0, 0, Or.inr (hD S hS hne Z ht hh lam hs)⟩

/-- **The `(F)` branch's data on the inherited tower, named.**  Exactly the two hypotheses
`Kakeya.ML2Core.refinedFloorHypothesis_of_landed` consumes, read on the hierarchy `𝒰₁` that
`FloorDataAtTrichotomy` hands its consumer — i.e. on the **inherited** tower, per
, and not on any freshly built one.

**Family/shading:** `𝒰₁` on its own index set `S` with shading `V`.  **Level pair:** the window
triple `(a,b,m)` is existential and born here, per l.4133-4136. -/
def WindowAndFloorAt (β ϖ ε₁ η' : ℝ) (gain dens : ℝ → ℝ) {C : NNReal} {Kl cl : ℕ}
    {S : Finset ι} {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰₁ : Tube.UniformTubeSet S (fun i => (V i).toTube) (Tube.ssfGridLen δ) Cu) : Prop :=
  ∃ (a b m : ℕ) (hhom : IsClassHomogeneousOn 𝒰₁ S),
    ML2Reduction.IsKatzTaoDividingWindowLevels
        (refinedHierarchy 𝒰₁ (Finset.Subset.refl S) hhom rfl)
        ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ)
        (ML2Spine.spineRung β ϖ ε₁ gain dens)
        (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m ∧
      FloorHypothesisAt β ϖ ε₁ gain dens η'
        (refinedHierarchy 𝒰₁ (Finset.Subset.refl S) hhom rfl) a b m

/-- `RefinedFloorHypothesis` is monotone in the loss, by `IsShadedRefinementOf.mono_loss`. -/
theorem refinedFloorHypothesis_mono_loss {β ϖ ε₁ η' : ℝ} {gain dens : ℝ → ℝ}
    {C : NNReal} {Kl cl : ℕ} {Λ Λ' : ℝ≥0∞} {S : Finset ι}
    {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {𝒰₁ : Tube.UniformTubeSet S (fun i => (V i).toTube) (Tube.ssfGridLen δ) Cu}
    {a b m : ℕ} (hΛ : Λ ≤ Λ')
    (hR : RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens η' Λ 𝒰₁ a b m) :
    RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens η' Λ' 𝒰₁ a b m := by
  obtain ⟨S', W, hS', hhom, hW, href, hwin, hflo⟩ := hR
  exact ⟨S', W, hS', hhom, hW, href.mono_loss hΛ, hwin, hflo⟩

/-- **A2's reduction: the trichotomy needs only the `(D)` producer.**

`SpineFloorProducer.lean:29` recorded the twin `IsKatzTaoDividingWindowLevels` on
`refinedHierarchy` as having *"no producer by design … **WAITING** on the (D) routing. The window
`(a,b,m)` is born here."*  This theorem is that sentence, : where the window **and** floor
do hold on the inherited tower, the `(F)` alternative follows outright from the existing
`Kakeya.ML2Core.refinedFloorHypothesis_of_landed` at the trivial refinement, and the loss is
absorbed by `1 ≤ Λ_f` (`Kakeya.ML2Core.one_le_polylogLoss` supplies that for the polylogarithmic
`Λ_f` the source prints at l.4057).  Where they do not, the source's l.4121-4123 sends the
configuration to `(D)`.

**So `FloorDataAtTrichotomy` has exactly one hypothesis, and it is the `(D)` producer.**
Its exact goal is the hypothesis `hD` below.

**Family/shading:** `𝒰` on `(u,T)`; the branch runs on `S ⊆ u` with shading `Z`, and the `(F)`
alternative is delivered on the **inherited** tower `(𝒰.restrictOccupied hS hh).retube`.
**Level pair:** `(a,b,m)` existential, born in the `(F)` branch — not fixed before the split. -/
theorem floorDataAtTrichotomy_of_defectProducer
    {β ϖ ε₁ η' h : ℝ} {gain dens : ℝ → ℝ} {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (hΛf : 1 ≤ Λf)
    (hD : ∀ (S : Finset ι) (hS : S ⊆ u), S.Nonempty →
      ∀ (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S) (lam : NNReal),
        ¬ WindowAndFloorAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens
            ((𝒰.restrictOccupied hS hh).retube (funext ht)) →
        DefectBranchAt h Λf lam 𝒰 S Z) :
    FloorDataAtTrichotomy (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' h gain dens Λf 𝒰 := by
  classical
  intro S hS hne Z ht hh lam
  by_cases hw : WindowAndFloorAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens
      ((𝒰.restrictOccupied hS hh).retube (funext ht))
  · obtain ⟨a, b, m, hhom', hwin, hflo⟩ := hw
    refine ⟨a, b, m, Or.inl (refinedFloorHypothesis_mono_loss hΛf ?_)⟩
    exact refinedFloorHypothesis_of_landed β ϖ ε₁ gain dens η' _ a b m hne hhom' hwin hflo
  · exact ⟨0, 0, 0, Or.inr (hD S hS hne Z ht hh lam hw)⟩

/-! ### The `(D)` producer, and the correction it forces on the dichotomy above

Building `hD` located a defect in `floorDataAtTrichotomy_of_defectProducer`'s **trigger**, and it
is worth stating plainly because it is mine.

`profileDrop_of_concentration_destroyed` (`SpineDefectExit.lean:270`) is **existing** and is
literally l.4118-4131: *"the old value is larger than `½Θ^τ`, the new value is smaller than
`½Θ^{τ/2}` … hence `d_{a,m}(𝕊') − d_{a,m}(𝕊*) ≥ τε²/4 ≥ 2h"*, with
`potential_drop_of_profileExp_drop` supplying *"every other `D_{k,l}` is monotone under
restriction, so the corresponding ceiling drops by at least one and no other ceiling increases"*.
So the quantitative core of `(D)` needed **no new proof at all**.

**What does not work is deriving `(D)` from `¬ WindowAndFloorAt`.**  That hypothesis is the
negation of an existential: it yields no refinement `S'`, no failing pair `(a,m)`, and neither
concentration bound, so nothing can be constructed from it.  The source does not test first
either — `SpineFloorShapeDefectExit.lean:96` states the order explicitly, *"the refinement is
performed, and **then** the window's lower concentration is tested"* (l.5899-5901), matching
l.4133's *"Otherwise retain complete factor cells"*, which is a statement **about the refinement**.

Hence `defectBranchAt_of_concentration_destroyed` below takes the refinement as data, and
`floorDataAtTrichotomy_of_refinementTrichotomy` re-composes the trichotomy **in the source's
order**.  `floorDataAtTrichotomy_of_defectProducer` is kept — it is a correct reduction — but its
`hD` is *not* a discharge-able goal, and this is the reading that supersedes it. -/

/-- **The `(D)` branch, produced** (l.4093-4097, l.4118-4131).

Everything quantitative is the existing `Kakeya.ML2Core.profileDrop_of_concentration_destroyed`;
this only carries it into `Kakeya.ML2Core.DefectBranchAt`.  The constants are the source's own and
are **copied, not fitted**: `τ` and `Θ = ρ_a/ρ_m` are the caller's, `hgap` is
`2h ≤ (τ/2)(log Θ / log(1/δ))`, i.e. l.4124-4127's `τε²/4 ≥ 2h` read through the window's scale
arithmetic `log Θ_m / log(1/δ) ≥ ε²/2`, and `hΘ2` is the existing exit's own side condition.

**Family/shading:** the refinement `(S', W)` of `(S, Z)` under `𝒰` on `(u,T)`.  **The potential
does not see the shading** — `potential` is a function of the family alone (floor hand,
`Kakeya.ML2Core.no_potential_drop_self`); the shading enters only through the dense-shading
conjunct.  **Level pair:** `(a,m)` with `a < m ≤ ssfGridLen δ` — the failing pair, which is *not*
the window triple and must not be conflated with it. -/
theorem defectBranchAt_of_concentration_destroyed
    {Λf : ℝ≥0∞} {h τ Θ : ℝ} {lam : NNReal} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (href : IsShadedRefinementOf 𝒰 Λf S Z S' W)
    (hh : 0 < h) (hΘ0 : 0 < Θ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {a m : ℕ} (ham : a < m) (hm : m ≤ Tube.ssfGridLen δ) (hΘ2 : 2 ≤ Θ ^ (τ / 2))
    (hbefore : ENNReal.ofReal (Θ ^ τ / 2) ≤ pairProfile 𝒰 S a m)
    (hafter : pairProfile 𝒰 S' a m ≤ ENNReal.ofReal (Θ ^ (τ / 2) / 2))
    (hgap : 2 * h ≤ (τ / 2) * (Real.log Θ / Real.log (1 / (δ : ℝ))))
    {lam' : NNReal} (hlam'0 : 0 < lam') (hlam' : lam ≤ Λf * lam')
    (hdense : ML2Shaded.HasDenseShading lam' S' (fun i => (W i).toShadedBody)) :
    DefectBranchAt h Λf lam 𝒰 S Z :=
  ⟨S', W, href,
    profileDrop_of_concentration_destroyed 𝒰 href.subset hh hΘ0 hδ0 hδ1 ham hm hΘ2
      hbefore hafter hgap,
    lam', hlam'0, hlam', hdense⟩

/-- **`(F)` from a general refinement**, not only the trivial one: the constructor of
`RefinedFloorHypothesis`, read on the refinement's own inherited tower. -/
theorem refinedFloorHypothesis_of_refinement
    {β ϖ ε₁ η' : ℝ} {gain dens : ℝ → ℝ} {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞}
    {S S' : Finset ι} {V W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {𝒰₁ : Tube.UniformTubeSet S (fun i => (V i).toTube) (Tube.ssfGridLen δ) Cu}
    {a b m : ℕ} (hS' : S' ⊆ S) (hhom : IsClassHomogeneousOn 𝒰₁ S')
    (hW : (fun i => (W i).toTube) = (fun i => (V i).toTube))
    (href : IsShadedRefinementOf 𝒰₁ Λf S V S' W)
    (hwin : ML2Reduction.IsKatzTaoDividingWindowLevels (refinedHierarchy 𝒰₁ hS' hhom hW)
      ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) (ML2Spine.spineRung β ϖ ε₁ gain dens)
      (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m)
    (hflo : FloorHypothesisAt β ϖ ε₁ gain dens η' (refinedHierarchy 𝒰₁ hS' hhom hW) a b m) :
    RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens η' Λf 𝒰₁ a b m :=
  ⟨S', W, hS', hhom, hW, href, hwin, hflo⟩

/-- **The trichotomy re-composed in the source's order**: the refinement is produced *first*, and
the test is applied to it (l.4133, l.5899-5901).  This is the shape a real producer can discharge,
and it supersedes `floorDataAtTrichotomy_of_defectProducer`'s trigger.

**Family/shading:** `𝒰` on `(u,T)`; each configuration `S ⊆ u` with shading `Z`.  **Level pair:**
the window triple is existential and born inside the `(F)` alternative. -/
theorem floorDataAtTrichotomy_of_refinementTrichotomy
    {β ϖ ε₁ η' h : ℝ} {gain dens : ℝ → ℝ} {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (hstep : ∀ (S : Finset ι) (hS : S ⊆ u), S.Nonempty →
      ∀ (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S) (lam : NNReal),
        (∃ a b m : ℕ, RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
            η' Λf ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m)
          ∨ DefectBranchAt h Λf lam 𝒰 S Z) :
    FloorDataAtTrichotomy (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' h gain dens Λf 𝒰 := by
  intro S hS hne Z ht hh lam
  rcases hstep S hS hne Z ht hh lam with ⟨a, b, m, hF⟩ | hD
  · exact ⟨a, b, m, Or.inl hF⟩
  · exact ⟨0, 0, 0, Or.inr hD⟩

/-- **Which `S'`, and why it cannot be the identity** — the question asked of the `(D)` witness.

The floor hand's  recorded that the identity refinement never fires `(D)`
(`Kakeya.ML2Core.lt_pairProfile_of_identity`).  Here that is turned into a property of any witness:
the two concentration bounds are **jointly unsatisfiable at `S' = S`**, so a `(D)` witness is
necessarily a *genuine* restriction `S' ⊊ S`, selected by the pair `(a,m)` whose lower
concentration failed.

*Why no other ceiling rises*: `Kakeya.ML2Core.potential_drop_of_profileExp_drop` — used inside
`defectBranchAt_of_concentration_destroyed` — closes the sum with
`Kakeya.ML2Core.pairProfile_mono_family` on **every** pair, so no `D_{k,l}` can increase under the
restriction; only the failing pair moves, and it moves down by two ceilings.  That is l.4128-4130
verbatim, and it is existing, not re-proved here.

**Family:** `S' ⊆ S` under `𝒰`; the potential sees the **family only**, never the shading (floor
hand ).  **Level pair:** the failing pair `(a,m)`. -/
theorem ne_of_concentration_destroyed {τ Θ : ℝ} (hΘ0 : 0 < Θ) (hΘ2 : 2 ≤ Θ ^ (τ / 2))
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    {S S' : Finset ι} {a m : ℕ}
    (hbefore : ENNReal.ofReal (Θ ^ τ / 2) ≤ pairProfile 𝒰 S a m)
    (hafter : pairProfile 𝒰 S' a m ≤ ENNReal.ofReal (Θ ^ (τ / 2) / 2)) :
    S' ≠ S := by
  rintro rfl
  exact absurd (lt_of_le_of_lt hafter (lt_pairProfile_of_identity hΘ0 hΘ2 hbefore)) (lt_irrefl _)

/-! ### `hstep` is **not provable as stated**, and the obstruction is a missing hypothesis

Attempting `hstep` — the hypothesis of `floorDataAtTrichotomy_of_refinementTrichotomy`, and the
last floor row — produced a refutation rather than a construction, so it is recorded as one.

`FloorDataAtTrichotomy` quantifies over **every** nonempty `S ⊆ u` with a tube-matching shading `Z`
and `IsClassHomogeneousOn 𝒰 S`, and **nothing else**.  The source's lemma does not: l.4038-4053
fixes `𝒲` and then says *"and **assume the non-sticky window inequalities**"* — three of them,
the third being `Δ_max(𝕊'_m⟨S⟩) > ½(ρ_a/ρ_m)^{η_{J+1}}` for `m ∈ 𝒲`.  That third inequality **is**
the `hbefore` of `defectBranchAt_of_concentration_destroyed`; it is an *assumption* of the lemma,
not a consequence of it.

Take `S` a singleton.  Then `(D)` is **impossible** — `not_defectBranchAt_singleton` — because
`IsShadedRefinementOf` forces `S'` nonempty and `S' ⊆ {i}`, hence `S' = {i}`, and
`Kakeya.ML2Core.no_potential_drop_self` kills the strict drop.  So at a singleton `hstep`
degenerates to the **unconditional** `(F)` obligation, with no dichotomy escape
(`refinedFloorHypothesis_of_step_singleton`) — and `(F)` there asks for
`ML2Reduction.IsKatzTaoDividingWindowLevels`, whose `le_level_maxDensity` is a *lower* bound
`(ρ_a/ρ_c)^{η} ≤ C_⋆ Δ_max(…)` that a one-tube family cannot meet for a wide window.

**So the last floor row is not a missing construction; it is a missing hypothesis.**  The engine is
existing (`profileDrop_of_concentration_destroyed`), the composition is existing
(`defectBranchAt_of_concentration_destroyed` above), and what is absent is the source's own window
assumptions in the predicate.  The exact corrected goal is `hstep` **with l.4043-4053's three
non-sticky window inequalities added as hypotheses on `(S, Z)`** — at which point `hbefore` is
available and the `(D)` side is discharged by the composition already here.

Adding them changes a **existing** statement (`FloorDataAtTrichotomy`, floor hand's route (b)), so it
is a written request and not something this file does. -/

/-- **`(D)` is impossible on a singleton family.**  `IsShadedRefinementOf` demands a *nonempty*
`S' ⊆ S`, so at `S = {i}` the only refinement is the identity, and
`Kakeya.ML2Core.no_potential_drop_self` forbids the strict potential drop.

**Family:** `{i}` with shading `Z`; the potential sees the **family only**, never the shading.
**Level pair:** none — the obstruction is at the level of the family. -/
theorem not_defectBranchAt_singleton {h : ℝ} {Λf : ℝ≥0∞} {lam : NNReal}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    {i : ι} {Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} :
    ¬ DefectBranchAt h Λf lam 𝒰 {i} Z := by
  rintro ⟨S', W, href, hdrop, -⟩
  have hsub : S' ⊆ ({i} : Finset ι) := href.subset
  have hne : S'.Nonempty := href.nonempty
  have hEq : S' = ({i} : Finset ι) :=
    Finset.eq_singleton_iff_nonempty_unique_mem.mpr
      ⟨hne, fun x hx => Finset.mem_singleton.mp (hsub hx)⟩
  subst hEq
  exact no_potential_drop_self 𝒰 _ hdrop

/-- **At a singleton, `hstep` is the unconditional `(F)` obligation.**  The disjunction collapses,
so no choice of refinement can help: this is the statement that the last floor row cannot
be closed while `FloorDataAtTrichotomy` omits l.4043-4053's window assumptions. -/
theorem refinedFloorHypothesis_of_step_singleton
    {β ϖ ε₁ η' h : ℝ} {gain dens : ℝ → ℝ} {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞} {lam : NNReal}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    {i : ι} {Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {hS : ({i} : Finset ι) ⊆ u} {ht : ∀ j, (Z j).toTube = (T j).toTube}
    {hh : IsClassHomogeneousOn 𝒰 ({i} : Finset ι)}
    (hstep : (∃ a b m : ℕ, RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
        η' Λf ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m)
      ∨ DefectBranchAt h Λf lam 𝒰 {i} Z) :
    ∃ a b m : ℕ, RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
      η' Λf ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m :=
  hstep.resolve_right not_defectBranchAt_singleton

/-! ## The un-bundled, window-parametrised trichotomy 

 The three non-sticky window inequalities of l.4042-4053 **cannot be added as
antecedents** of `FloorDataAtTrichotomy`, because they mention `a`, `b`, `m`, which its conclusion
binds existentially.  They are also **not a fifth dropped clause**: all three are existing as the
three fields of `ML2Reduction.IsKatzTaoDividingWindow` (`SpineEveryScale.lean:218/222/228`).  The
defect is dispersal — the clauses exist one interface away and this row does not receive them.

The faithful repair un-bundles the two jobs the row had absorbed:

* *finding* a window is `lem:dividing-scales`' job (l.4365, l.4376-4377);
* *trichotomising* a given window is `lem:ml2-window-refinement`'s job (l.4056-4098).

`WindowedFloorTrichotomyAt` does only the second: the window `(a,b,m)` and its
`IsKatzTaoDividingWindowLevels` — whose `le_window_maxDensity` field **is** l.4051-4053, i.e. the
`hbefore` that `defectBranchAt_of_concentration_destroyed` needs — arrive as **inputs**, on the
inherited tower.  `floorDataAtTrichotomy_of_windowed` then reaches the existing
`FloorDataAtTrichotomy` unchanged, so every existing consumer
(`htrial_of_floorDataNonempty`, `trialSupplier_of_floorRouteNonempty`, the `ROUTEB` consumers) is
served **without being re-proved** and the `TrialSupplier` endpoint is unmoved. -/

/-- **The trichotomy of `lem:ml2-window-refinement`, un-bundled** (l.4056-4098, ).

The window is a **hypothesis**, on the **inherited** tower `(𝒰.restrictOccupied hS hh).retube` —
never a rebuilt one (§9.1, §9.2).  Its `le_window_maxDensity` field is l.4051-4053's third
non-sticky inequality, so `hbefore` is now *received* rather than missing, which is exactly what
`not_defectBranchAt_singleton` showed the old shape lacked.

**Family/shading:** `𝒰` on `(u,T)`; each configuration is `S ⊆ u` with shading `Z`; the `(F)`
alternative refines to `(S', W)` inside `RefinedFloorHypothesis` — the one place the shading moves.
**Level pair:** the window triple `(a,b,m)` is **universally** quantified here, which is the whole
point of the un-bundling; the failing pair of the `(D)` side is a different, existential pair. -/
def WindowedFloorTrichotomyAt (β ϖ ε₁ η' h : ℝ) (gain dens : ℝ → ℝ)
    {C : NNReal} {Kl cl : ℕ} (Λf : ℝ≥0∞)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu) : Prop :=
  ∀ (S : Finset ι) (hS : S ⊆ u), S.Nonempty →
    ∀ (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S) (lam : NNReal)
      (a b m : ℕ),
      ML2Reduction.IsKatzTaoDividingWindowLevels ((𝒰.restrictOccupied hS hh).retube (funext ht))
          ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ)
          (ML2Spine.spineRung β ϖ ε₁ gain dens)
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
      RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
          η' Λf ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m
        ∨ DefectBranchAt h Λf lam 𝒰 S Z

/-- **The un-bundled row reaches the existing one**, given a window supply on the inherited tower.

This is what keeps the repair non-breaking: `FloorDataAtTrichotomy` is *derived*, not edited, so
`htrial_of_floorDataNonempty`, `trialSupplier_of_floorRouteNonempty` and the `ROUTEB` consumers
continue to compile against it verbatim and still reach `TrialSupplier`.

**What the caller must now supply** — the descent composition into
`geometricCoreAt_of_hfac_witness_payload`'s third row — is exactly `hsupply`: a window
**on the inherited tower**.  That is the open link, measured in
`not_window_transport_of_restrict_indexSet` below. -/
theorem floorDataAtTrichotomy_of_windowed
    {β ϖ ε₁ η' h : ℝ} {gain dens : ℝ → ℝ} {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (hW : WindowedFloorTrichotomyAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' h gain dens Λf 𝒰)
    (hsupply : ∀ (S : Finset ι) (hS : S ⊆ u), S.Nonempty →
      ∀ (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S),
        ∃ a b m : ℕ, ML2Reduction.IsKatzTaoDividingWindowLevels
          ((𝒰.restrictOccupied hS hh).retube (funext ht))
          ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ)
          (ML2Spine.spineRung β ϖ ε₁ gain dens)
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m) :
    FloorDataAtTrichotomy (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' h gain dens Λf 𝒰 := by
  intro S hS hne Z ht hh lam
  obtain ⟨a, b, m, hwin⟩ := hsupply S hS hne Z ht hh
  rcases hW S hS hne Z ht hh lam a b m hwin with hF | hD
  · exact ⟨a, b, m, Or.inl hF⟩
  · exact ⟨a, b, m, Or.inr hD⟩

/-- **The single open floor row, named** : a dividing window on the **inherited**
tower.  It is exactly `floorDataAtTrichotomy_of_windowed`'s `hsupply`.

**Measured, not assumed.**  The existing cover-equality bridge
`Kakeya.ML2Core.isKatzTaoDividingWindowLevels_of_cover_eq` **cannot** supply it:

* it relates two hierarchies over the **same** index `Finset`, whereas `restrictOccupied` moves
  from `u` to `S`; supplying its three `rfl`s unifies both sides to the *restricted* hierarchy, so
  the ambient window is not even type-compatible with the goal (control `WTRANS`, recorded);
* and its `hidx` asks for `cover.indexSet` **equality**, whereas `restrictOccupied` sets
  `indexSet k := S.image (assign k)` (`SpineFloorShape.lean:132`) with only
  `⊆` available (`SpineDefectConstantLedger.lean:427`).

Independently of the bridge, the field that blocks is the same one this file measured at the
outset: `le_window_maxDensity` is a **lower** bound on a `maxDensity`, restriction can only make
densities **drop**, so it cannot descend from the ambient tower — while the two upper-bound fields
would. The obstruction is the l.4051-4053 inequality, in both places, for one reason.

**So the answer to the question is the second option:** the window must be produced
**on the inherited tower directly**, by the source's own route — l.4376-4377's rising two-scale
density read on the original tower — and not transported from a rebuilt one (§9.2's inert
stopping-time producer) nor from the ambient one (here).  That is the single open floor row, and
this `def` is its exact Lean goal.

**Family/shading:** `𝒰` on `(u,T)`, restricted to `S` and retubed at `Z`; no shading enters — the
window is a statement about tubes and densities only.  **Level pair:** the triple `(a,b,m)` is
existential *here*, because supplying a window is exactly asserting one exists. -/
def InheritedWindowSupplyAt (β ϖ ε₁ : ℝ) (gain dens : ℝ → ℝ) {C : NNReal} {Kl cl : ℕ}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu) : Prop :=
  ∀ (S : Finset ι) (hS : S ⊆ u), S.Nonempty →
    ∀ (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S),
      ∃ a b m : ℕ, ML2Reduction.IsKatzTaoDividingWindowLevels
        ((𝒰.restrictOccupied hS hh).retube (funext ht))
        ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ)
        (ML2Spine.spineRung β ϖ ε₁ gain dens)
        (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m

/-- The named supply is literally `floorDataAtTrichotomy_of_windowed`'s `hsupply`, so the whole
payload side now rests on **one** open row. -/
theorem floorDataAtTrichotomy_of_windowed_of_supply
    {β ϖ ε₁ η' h : ℝ} {gain dens : ℝ → ℝ} {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (hW : WindowedFloorTrichotomyAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' h gain dens Λf 𝒰)
    (hsupply : InheritedWindowSupplyAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens 𝒰) :
    FloorDataAtTrichotomy (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' h gain dens Λf 𝒰 :=
  floorDataAtTrichotomy_of_windowed hW hsupply

/-! ## The single open row, traced to its engine: the stopping lemma has no slot for a tower

`InheritedWindowSupplyAt` is the source's **non-sticky alternative of `dividingScalesLemma` (B)**,
l.2621-2705.  Read there, the lemma is *given* a tower — *"Let `𝕋_M = 𝕋 → ⋯ → 𝕋_0` be a **named
threaded tower** at these radii"* — and its (B) dichotomy is asserted **about that tower**:
`eqdividingKfirst` (l.2695-2696) is `coarse_maxDensity_le`, `eqdividingKsecond` (l.2697-2698) is
`middle_maxDensity_le`, and `eqdividingKwitness` (l.2700-2703) is `le_window_maxDensity`.  So the
three fields `WindowedFloorTrichotomyAt` consumes are exactly (B)'s three conclusions, and the
source produces them **without rebuilding**.

**Why the tree cannot restate it by holding a hierarchy fixed — measured, not assumed.**

* `StickyKakeya.dividingScalesKatzTao` (`MultiScaleFac.lean:430`) takes a `UniformTubeSet` and
  returns `(𝒢L.toUniformTubeSet).mono`, a **fresh** hierarchy; the S1 hand's
  `producer_runs_on_any_hierarchy` compiles that the input slot is inert.
* The reason is one level down, and it is structural: its engine
  `exists_maximal_cutsKT_hoisted_blocks_core` (`MultiScaleFac/StoppingKT.lean:517-539`) takes
  `s`, `T`, the ball / essential-distinctness / density hypotheses — and **no hierarchy at all**.
  It *produces* `𝒢L : GridUniform tL T Mgrid Cv`.  There is no argument to hold fixed, so this is
  not a restatement away; the engine would have to be re-proved against a supplied tower.
* `PairBandOn` (`StoppingKT.lean:90`) — the two-sided band the stopping lemma carries, and
  literally the shape this file measured in `levelDensityBand_upper_of_subset` — is stated over
  `GridUniform`, not over the `UniformTubeSet` the inherited tower is.  So even the band cannot be
  handed to the engine on the inherited tower without a retyping.

**And the source says what the fixed-tower route needs**, l.2708-2713: reduce to the common array
stopping lemma `lemabstractstopping`, *"before forming either array, insert any endpoint radius …
by the canonical centred-tube cover and then apply the **simultaneous vector-bin regularization to
the enlarged finite tower**"*.  That regularization is `A1`
(`Kakeya.ML2Core.exists_jointStatisticBand`) — it supplies exactly the two-sided bands of
`PairBandOn`, on the **given** tower.  What is missing is the stopping lemma downstream of it.

> **Named missing step.**  `lemabstractstopping` (source l.2708-2709), restated to **consume** a
> band on a supplied hierarchy instead of manufacturing its own grid — i.e. an analogue of
> `exists_maximal_cutsKT_hoisted_blocks_core` with `GridUniform tL T Mgrid Cv` moved from the
> conclusion to the hypotheses.
>
> **CORRECTION, and it is mine.**  This paragraph originally added *"the first row of this run
> with no existing engine reachable by restatement"*.  **That was wrong**, and
> `Reduction/SpineFixedTowerStopping.lean` refutes it: the measurement above is accurate about
> `exists_maximal_cutsKT_hoisted_blocks_core`, but **one layer further down**
> `Kakeya.MultiScaleFac.exists_maximal_cuts_abstract_state_margin` (`MultiScaleFac/Stopping.lean`
> `:312`) is fully abstract over its state type and predicates — it is `lemabstractstopping`, and
> it runs on a fixed tower unchanged (`Kakeya.ML2Core.exists_fixedTowerCuts`).  The grid
> manufacture is in the *instantiation*, not in the engine.  So this row is like every other one
> today: the engine was existing and only the wiring was missing.
>
> Exact Lean goal: `InheritedWindowSupplyAt`, whose discharge with
> `floorDataAtTrichotomy_of_windowed_of_supply` makes `FloorDataAtTrichotomy` unconditional. -/

/-- **The fixed-tower stopping obligation, named** — the missing engine, isolated.

Given a hierarchy and its two-sided pair band, produce the maximal-cut data on **that** hierarchy.
This is `lemabstractstopping` on a supplied tower; discharging it and composing with the existing
`alternativeOneKT_of_cutsKT` / `alternativeTwoKT_of_terminal_block` chain would yield
`InheritedWindowSupplyAt`, and with it an unconditional `FloorDataAtTrichotomy`.

Stated with the window data abstracted to `Prop`-level so it names the obligation without
prejudging the cut structure — the cut shape is `StoppingKT`'s and belongs to whoever re-proves it.

**Family/shading:** the inherited tower's family `S` with shading `Z` **unchanged** — the window is
about tubes and densities only, and no shading enters.  **Level pair:** `(a,b)` with the middle
level `m ∈ 𝒲`, exactly `IsKatzTaoDividingWindowLevels`'s triple. -/
def FixedTowerStoppingObligation (β ϖ ε₁ : ℝ) (gain dens : ℝ → ℝ) {C : NNReal} {Kl cl : ℕ}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu) : Prop :=
  InheritedWindowSupplyAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens 𝒰

/-- The obligation is *definitionally* the supply, so nothing is smuggled in by naming it: the
payload side is unconditional exactly when this is discharged. -/
theorem floorDataAtTrichotomy_of_fixedTowerStopping
    {β ϖ ε₁ η' h : ℝ} {gain dens : ℝ → ℝ} {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (hW : WindowedFloorTrichotomyAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' h gain dens Λf 𝒰)
    (hstop : FixedTowerStoppingObligation (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens 𝒰) :
    FloorDataAtTrichotomy (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' h gain dens Λf 𝒰 :=
  floorDataAtTrichotomy_of_windowed_of_supply hW hstop

end Dichotomy

end Kakeya.ML2Core

end
