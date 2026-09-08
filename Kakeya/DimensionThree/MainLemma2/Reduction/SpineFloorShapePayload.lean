/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteClosure
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeSelfHierarchy
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorGateRed
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorProducer

/-!
# `FloorPayload`: the `hdev` row's one blocking inequality, and the payload's **empty-family**
refutation

 lists `Kakeya.ML2Core.FloorPayload` as row R3 of `GeometricCoreAt`, carried
by the floor hands.  This file measures what that row costs, and the answer is in two halves.

## The `hdev` half — one inequality, named

`Kakeya.ML2Core.hfloor_of_producers`'s `hdev` row is
`∃ S' W, IsShadedRefinementOf 𝒰 Λf S Z S' W`.  The producer is existing
(`Kakeya.ML2Core.exists_shadedRefinement_of_pass`, `R0′`) but returns the loss
`Kakeya.ML2Core.refinementLoss K 3 Cu δ`, while the closure fixes `Λf := polylogLoss K'`.
`Kakeya.ML2Core.IsShadedRefinementOf.mono_loss` below shows the predicate is **monotone in the
loss**, so the whole gap between producer and consumer is the single scalar inequality

```
    refinementLoss K 3 Cu δ ≤ polylogLoss K' δ          -- the `hdev` blocker, in one line
```

and `Kakeya.ML2Core.exists_shadedRefinement_of_le` is the reduction.  That inequality is **false**
in general and the reason is recorded : `refinementLoss`
carries the comparability factor `K` (`= lam⁻¹`, up to `2 δ^{-ηin}` at the trial's floor), a genuine
`δ`-power, and `StickyKakeya.gridLoss Cu 6 δ`, whose exponent
`6 (ssfGridLen δ + 1)^2` grows with `δ → 0`, whereas `polylogLoss K' δ` is `(1 − log δ)^{K'}` at a
**fixed** `K'`.

## The payload half — `FloorPayload` is **FALSE as stated**

`Kakeya.ML2Core.FloorDataAt` quantifies over **every** `S ⊆ u`, including `S = ∅`, and
`IsClassHomogeneousOn 𝒰 ∅` holds (take `bN = 0`; the band is quantified over
`(∅ : Finset ι).image _ = ∅`).  At `S = ∅` the hierarchy handed to
`Kakeya.ML2Core.RefinedFloorHypothesis` is indexed by `∅`, and that predicate's first clause is
`IsShadedRefinementOf … S' W` with `S' ⊆ ∅` **and** `S'.Nonempty` — the explicit anti-vacuity clause
`C-M1a` of   The two are contradictory, so:

* `Kakeya.ML2Core.not_refinedFloorHypothesis_of_empty` — the `(F)` predicate is false on an
  empty-indexed hierarchy, at every window and every loss;
* `Kakeya.ML2Core.not_floorDataAt` — hence `FloorDataAt` is false for **every** hierarchy;
* `Kakeya.ML2Core.not_floorPayload` — hence `FloorPayload` is false, with a witness family
  supplied at every small `δ`.

The nonemptiness clause was added to `IsShadedRefinementOf` ( `C-M1a`) and to
`Kakeya.ML2Core.isShadedRefinementOf_self` (which carries `hne : S.Nonempty`), but never to
`FloorDataAt`'s binder list.  **This is a statement-level defect and is not repaired here**: the
repair is one binder, `(hne : S.Nonempty)`, in a existing `def`, and that is the source comparison's call.
See  for the exact requested text and the consumer check.
-/

@[expose] public section

open MeasureTheory Metric
open scoped NNReal ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace Kakeya.ML2Core

section MonoLoss

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ E3}
  {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}

/-- **The refinement predicate is monotone in the loss.**  Only the retention clause mentions `Λ`,
and it is an upper bound.  This is what turns the gap between `R0′`'s output loss and the closure's
`Λf` into a single scalar inequality. -/
theorem IsShadedRefinementOf.mono_loss {Λ Λ' : ℝ≥0∞} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ E3}
    (h : IsShadedRefinementOf 𝒰 Λ S Z S' W) (hΛ : Λ ≤ Λ') :
    IsShadedRefinementOf 𝒰 Λ' S Z S' W :=
  ⟨h.subset, h.nonempty, h.2.2.1, h.2.2.2.1,
    h.retention.trans (mul_le_mul_left hΛ _), h.classHomogeneous⟩

/-- **The `hdev` row, reduced to one inequality.**  Given `R0′`'s output at its own loss `Λ`, the
row the closure consumes at `Λ'` follows from `Λ ≤ Λ'` and nothing else. -/
theorem exists_shadedRefinement_of_le {Λ Λ' : ℝ≥0∞} {S : Finset ι} {Z : ι → ShadedTube δ E3}
    (h : ∃ S' W, IsShadedRefinementOf 𝒰 Λ S Z S' W) (hΛ : Λ ≤ Λ') :
    ∃ S' W, IsShadedRefinementOf 𝒰 Λ' S Z S' W := by
  obtain ⟨S', W, hSW⟩ := h
  exact ⟨S', W, hSW.mono_loss hΛ⟩

/-- **The `hdev` row, CLOSED.**  `Kakeya.ML2Core.hfloor_of_producers`'s `hdev` is
`∃ S' W, IsShadedRefinementOf 𝒰 Λf S Z S' W`, and the *identity* refinement `S' := S`, `W := Z`
supplies it at loss `1` (`Kakeya.ML2Core.isShadedRefinementOf_self`), hence at every `Λf ≥ 1` by
`Kakeya.ML2Core.IsShadedRefinementOf.mono_loss`.  Since `Kakeya.ML2Core.one_le_polylogLoss` holds
unconditionally, `hdev` at the closure's `Λf := polylogLoss K'` costs **nothing**.

This is  `C-M1d` (*"the re-cut `(F)` is weaker … instantiate at `S' := S`,
`W := Z`, `Λf := 1`"*) turned into the row the closure consumes.  **`R0′` is therefore not needed
for `hdev`**, and `Reduction/SpineFloorProducer.lean:27`'s "WAITING on `R0′`'s re-cut (floor-shape
hand) and on the site (ED row, `2 ≤ Cu`)" is withdrawn: none of the ED row, the ball containment,
the comparable densities or `2 ≤ Cu` is used.  What `R0′` buys — a *proper* subfamily with a
genuine mass retention — is not what this row asks for. -/
theorem exists_shadedRefinement_of_nonempty {Λ : ℝ≥0∞} {S : Finset ι} {Z : ι → ShadedTube δ E3}
    (hne : S.Nonempty) (hhom : IsClassHomogeneousOn 𝒰 S) (hΛ : 1 ≤ Λ) :
    ∃ S' W, IsShadedRefinementOf 𝒰 Λ S Z S' W :=
  ⟨S, Z, (isShadedRefinementOf_self hne hhom).mono_loss hΛ⟩

/-- `hdev` at the closure's own loss, with the only remaining hypothesis being nonemptiness. -/
theorem exists_shadedRefinement_polylogLoss (K' : ℕ) {S : Finset ι} {Z : ι → ShadedTube δ E3}
    (hne : S.Nonempty) (hhom : IsClassHomogeneousOn 𝒰 S) :
    ∃ S' W, IsShadedRefinementOf 𝒰 (polylogLoss K' δ) S Z S' W :=
  exists_shadedRefinement_of_nonempty hne hhom (one_le_polylogLoss K' δ)

end MonoLoss

/-! ### The empty-family refutation -/

section Vacuity

variable {ι : Type*} {δ Cu : NNReal}

/-- `IsClassHomogeneousOn` holds vacuously on the empty family: the band is quantified over
`(∅ : Finset ι).image _`, which is empty. -/
theorem isClassHomogeneousOn_empty {u : Finset ι} {T : ι → Tube δ E3}
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) :
    IsClassHomogeneousOn 𝒰 (∅ : Finset ι) :=
  ⟨fun _ => 0, by simp⟩

/-- **The `(F)` predicate is false on an empty-indexed hierarchy.**  `RefinedFloorHypothesis`'s
first clause is `IsShadedRefinementOf`, whose subfamily must be both a subset of the index set and
**nonempty** (`C-M1a`).  Over `∅` those are contradictory, at every window, every loss and every
parameter. -/
theorem not_refinedFloorHypothesis_of_empty {β ϖ ε₁ η' : ℝ} {gain dens : ℝ → ℝ}
    {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞}
    {T : ι → ShadedTube δ E3}
    (𝒱 : Tube.UniformTubeSet (∅ : Finset ι) (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (a b m : ℕ) :
    ¬ RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
      η' Λf 𝒱 a b m := by
  rintro ⟨S', W, hS', -, -, href, -⟩
  obtain ⟨i, hi⟩ := href.nonempty
  exact absurd (hS' hi) (Finset.notMem_empty i)

/-- **`FloorDataAt` is false for every hierarchy.**  Instantiate its `∀ S ⊆ u` at `S = ∅`, with
`Z := T` so the retube is the identity. -/
theorem not_floorDataAt {β ϖ ε₁ η' : ℝ} {gain dens : ℝ → ℝ}
    {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞} {u : Finset ι}
    {T : ι → ShadedTube δ E3}
    (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu) :
    ¬ FloorDataAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf 𝒰 := by
  intro h
  obtain ⟨a, b, m, hf⟩ :=
    h ∅ (Finset.empty_subset u) T (fun _ => rfl) (isClassHomogeneousOn_empty 𝒰)
  exact not_refinedFloorHypothesis_of_empty _ a b m hf

end Vacuity

section PayloadRefutation

/-- The tube with its whole carrier shaded — the cheapest `ShadedTube`, used only to exhibit a
family at which `FloorPayload`'s inner `∀` bites. -/
noncomputable def fullShade (δ : NNReal) (T : Tube δ E3) : ShadedTube δ E3 where
  toTube := T
  shade := T.carrier
  measurableSet_shade := T.isCompact'.measurableSet
  shade_subset := subset_rfl

@[simp] theorem fullShade_toTube (δ : NNReal) (T : Tube δ E3) :
    (fullShade δ T).toTube = T := rfl

/-- **`FloorPayload` is FALSE as stated.**  Its inner `∀` runs over every ambient family and every
`S ⊆ u`; at `S = ∅` the `(F)` predicate is unsatisfiable
(`Kakeya.ML2Core.not_refinedFloorHypothesis_of_empty`), and a family exists at every `δ ∈ (0, 1]`,
so the `∀ᶠ δ` cannot hold.

The defect is a missing `S.Nonempty` binder in `Kakeya.ML2Core.FloorDataAt`; see the module
docstring.  **Not repaired here** — the `def` is existing. -/
theorem not_floorPayload.{w} {β ϖ ε₁ η' : ℝ} {gain dens : ℝ → ℝ}
    {C : NNReal} {Kl cl : ℕ} {Λf : NNReal → ℝ≥0∞} :
    ¬ FloorPayload.{w} (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf := by
  intro h
  have hbase : ∀ᶠ (δ : NNReal) in nhdsWithin 0 (Set.Ioi 0), (0 : NNReal) < δ ∧ δ ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hδ
    exact ⟨hδ.1, hδ.2.le⟩
  have hfalse : ∀ᶠ (δ : NNReal) in nhdsWithin 0 (Set.Ioi 0), False := by
    filter_upwards [h, hbase] with δ hδ hδ01
    obtain ⟨hδ0, hδ1⟩ := hδ01
    classical
    set ST : PUnit.{w + 1} → ShadedTube δ E3 := fun _ => fullShade δ (redTube δ) with hST
    have hinj : ∀ k ≤ Tube.ssfGridLen δ,
        Set.InjOn (fun i => ((fun i => (ST i).toTube) i).rescale
          (Tube.gridScale δ (Tube.ssfGridLen δ) k)) ((∅ : Finset PUnit.{w + 1}) : Set PUnit) := by
      intro k _
      simp
    exact not_floorDataAt
      (Tube.UniformTubeSet.self hδ0 hδ1 (∅ : Finset PUnit.{w + 1})
        (fun i => (ST i).toTube) hinj)
      (hδ (ι := PUnit.{w + 1}) ∅ ST _ _)
  exact (Filter.eventually_false_iff_eq_bot.mp hfalse ▸
    (inferInstance : (nhdsWithin (0 : NNReal) (Set.Ioi 0)).NeBot).ne') rfl

end PayloadRefutation

/-! ### What is left of the payload once `hdev` is free -/

section Reduction

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ E3}

open scoped Classical in
/-- **`FloorPayload`, post-repair and post-the estimate, reduces to `hwinfloor` ALONE — `hdev` is discharged
here.**

This is `Kakeya.ML2Core.hfloor_of_producers` with its `hdev` row supplied internally by the
identity refinement (`Kakeya.ML2Core.exists_shadedRefinement_of_nonempty`), so the only row left is
the window/floor row.  The `S.Nonempty` binder is the repair
requested for `Kakeya.ML2Core.FloorDataAt` (see the module docstring and
`Kakeya.ML2Core.not_floorPayload`); with it in place the conclusion below *is* `FloorDataAt`.

the estimate removed `hlineED` from `hfloor_of_producers`, so the list is **one row**: `hwinfloor`. -/
theorem floorDataAt_nonempty_of_rows {β ϖ ε₁ η' : ℝ} {gain dens : ℝ → ℝ}
    {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞} (hΛf : 1 ≤ Λf)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (hwinfloor : ∀ (S : Finset ι) (hS : S ⊆ u)
      (Z : ι → ShadedTube δ E3) (ht : ∀ i, (Z i).toTube = (T i).toTube)
      (hh : IsClassHomogeneousOn 𝒰 S)
      (S' : Finset ι) (W : ι → ShadedTube δ E3) (hS' : S' ⊆ S)
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
    ∀ (S : Finset ι) (hS : S ⊆ u) (Z : ι → ShadedTube δ E3)
      (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S), S.Nonempty →
      ∃ a b m : ℕ, RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
        η' Λf ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m := by
  intro S hS Z ht hh hne
  exact hfloor_of_producers Λf 𝒰 hS ht hh
    (exists_shadedRefinement_of_nonempty hne hh hΛf) (hwinfloor S hS Z ht hh)

end Reduction

end Kakeya.ML2Core

end
