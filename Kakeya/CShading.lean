/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FactorFamily.Basic

/-!
# Closed shadings

`ShadedBody` (blueprint `def:shading`) asks of a shading only that it be measurable. Two arguments
of the factoring construction need strictly more: the measurability of the Step 2 level set, whose
defining conditions involve a Minkowski sum rather than a preimage, and the projection step of GWZ
Lemma 5.9, where the shade is pushed forward along an orthogonal projection. Both are rescued by
closedness of the shade, through compactness.

This file collects the declarations of the closed variant of the shaded-body structure
(blueprint `sec:cshading`):

* `CShadedBody`, the shaded-body structure with `measurableSet_shade` strengthened to
  `isClosed_shade`, together with the coercion `CShadedBody.toShadedBody` that forgets closedness
  and the compactness `CShadedBody.isCompact_shade` of its shade;
* `ShadedBody.closureShade`, the closure operation in the other direction, which imposes
  closedness at no cost in shading mass (`ShadedBody.volume_shade_le_volume_shade_closureShade`);
* `ShadedBody.FactorFamily.closureShade`, the same operation applied to the inner bodies of a
  factor family, with the field equations recording that nothing but the shades changes;
* `ShadedBody.shade_inducedShading_closureShade`, that the induced shading of
  `ShadedBody.inducedShading` does not distinguish a shading from its closure.
-/

@[expose] public section

open Metric MeasureTheory Convexity

/-- A **closed shaded body** (blueprint `def:cshading`) is a convex body together with a closed
subset of it, called its shading.

This is the same data as `ShadedBody`, with the field `measurableSet_shade` strengthened to
`isClosed_shade`. The typeclass assumptions are those of `ShadedBody` so that a `CShadedBody`
can eventually be substituted for a `ShadedBody` without changing the ambient context; the
measurable-space structure is used by the coercion `CShadedBody.toShadedBody`, not by the
fields below. -/
structure CShadedBody (E : Type*) [TopologicalSpace E] [MeasurableSpace E]
    [ConvexSpace ℝ E]
    extends ConvexSpaceBody E where
  /-- Shading -/
  shade : Set E
  /-- The shading is closed -/
  isClosed_shade : IsClosed shade
  /-- The shading is a subset of the carrier -/
  shade_subset : shade ⊆ carrier

namespace CShadedBody

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [ConvexSpace ℝ E]

/-- **A closed shading is a shading** (blueprint `def:cshadingToShading`): forget the closedness
of the shade, keeping the carrier and the shade.

Along this map every result proved for `ShadedBody` applies verbatim to a `CShadedBody`, so no
statement has to be duplicated for the closed variant. -/
def toShadedBody [OpensMeasurableSpace E] (W : CShadedBody E) : ShadedBody E where
  toConvexSpaceBody := W.toConvexSpaceBody
  shade := W.shade
  measurableSet_shade := W.isClosed_shade.measurableSet
  shade_subset := W.shade_subset

/-- **The shade of a closed shaded body is compact** (blueprint
`lem:isCompactShadeCShadedBody`): it is a closed subset of the compact carrier.

This, rather than closedness itself, is what the projection construction
`CShadedBody.orthogonalProjectionImage` uses. -/
theorem isCompact_shade (W : CShadedBody E) : IsCompact W.shade := by
  exact W.isCompact'.of_isClosed_subset W.isClosed_shade W.shade_subset

end CShadedBody

namespace ShadedBody

section ClosureShade

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [ConvexSpace ℝ E] [T2Space E]

/-- **Closure of a shading** (blueprint `def:closureShade`): the closed shaded body with the same
carrier as `W` and with shade the closure of the shade of `W`.

This is well formed because the carrier of a convex body is compact, hence closed, so
`shade ⊆ carrier` gives `closure shade ⊆ closure carrier = carrier`. -/
def closureShade (W : ShadedBody E) : CShadedBody E where
  toConvexSpaceBody := W.toConvexSpaceBody
  shade := closure W.shade
  isClosed_shade := isClosed_closure
  shade_subset := by
    rw [← W.isCompact'.isClosed.closure_eq]
    exact closure_mono W.shade_subset

end ClosureShade

section ClosureShadeVolume

variable {E : Type*} [TopologicalSpace E] [MeasureSpace E] [ConvexSpace ℝ E] [T2Space E]

/-- **Closing a shading does not lose mass** (blueprint
`lem:volumeShadeLeVolumeShadeClosureShade`): `|Y| ≤ |closure Y|`. -/
theorem volume_shade_le_volume_shade_closureShade (W : ShadedBody E) :
    volume W.shade ≤ volume W.closureShade.shade := by
  exact measure_mono subset_closure

end ClosureShadeVolume

namespace FactorFamily

section ClosureShade

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [ConvexSpace ℝ E]
  [T2Space E] [OpensMeasurableSpace E]
  {ι κ : Type*}

/-- **Closure of a factor family** (blueprint `def:closureShadeFactorFamily`): the factor family
with the same inner and outer index sets, the same parent map, the same outer bodies and the same
inner carriers, with each inner shade replaced by its closure as in `ShadedBody.closureShade`.

The inner bodies of a `ShadedBody.FactorFamily` are `ShadedBody`s, so each closed shaded body
`ShadedBody.closureShade (F.innerBody i)` is reinserted along `CShadedBody.toShadedBody`; that is
why closedness of the new shades is not recorded in the type, but in
`ShadedBody.FactorFamily.closureShade_isClosed_shade`. -/
def closureShade (F : FactorFamily E ι κ) : FactorFamily E ι κ where
  innerSet := F.innerSet
  innerBody := fun i ↦ (F.innerBody i).closureShade.toShadedBody
  outerSet := F.outerSet
  outerBody := F.outerBody
  parent := F.parent
  parent_mem := F.parent_mem
  inner_le_parent := F.inner_le_parent

/-- Item (i) of blueprint `lem:closureShadeFactorFamilyHypotheses`: every shade of the closure
family is closed. -/
theorem closureShade_isClosed_shade (F : FactorFamily E ι κ) (i : ι) :
    IsClosed (F.closureShade.innerBody i).shade := by
  exact isClosed_closure

/-- The inner bodies of the closure family are the closures of the inner bodies of `F`. -/
theorem closureShade_innerBody (F : FactorFamily E ι κ) (i : ι) :
    F.closureShade.innerBody i = (F.innerBody i).closureShade.toShadedBody := by
  rfl

/-- The closure family has the same inner carriers as `F`. -/
theorem closureShade_innerBody_carrier (F : FactorFamily E ι κ) (i : ι) :
    (F.closureShade.innerBody i).carrier = (F.innerBody i).carrier := by
  rfl

/-- The closure family has the same inner index set as `F`. -/
theorem closureShade_innerSet (F : FactorFamily E ι κ) :
    F.closureShade.innerSet = F.innerSet := by
  rfl

/-- The closure family has the same outer bodies as `F`. -/
theorem closureShade_outerBody (F : FactorFamily E ι κ) :
    F.closureShade.outerBody = F.outerBody := by
  rfl

/-- The closure family has the same outer index set as `F`. -/
theorem closureShade_outerSet (F : FactorFamily E ι κ) :
    F.closureShade.outerSet = F.outerSet := by
  rfl

/-- The closure family has the same parent map as `F`. -/
theorem closureShade_parent (F : FactorFamily E ι κ) :
    F.closureShade.parent = F.parent := by
  rfl

/-- The closure family has the same fibers as `F`. -/
theorem closureShade_fiber (F : FactorFamily E ι κ) (j : κ) :
    F.closureShade.fiber j = F.fiber j := by
  rfl

end ClosureShade

section ClosureShadeVolume

variable {E : Type*} [TopologicalSpace E] [MeasureSpace E] [ConvexSpace ℝ E]
  [T2Space E] [OpensMeasurableSpace E]
  {ι κ : Type*}

/-- Item (iii) of blueprint `lem:closureShadeFactorFamilyHypotheses`: the fullness bound
`(lam / 2) * |V i| ≤ |Y i|` passes from `F` to its closure family, since closing a shade does
not decrease its volume. -/
theorem closureShade_lambda_le {lam : ENNReal} (F : FactorFamily E ι κ)
    (hlam : ∀ i ∈ F.innerSet,
      (2⁻¹ : ENNReal) * lam * volume (F.innerBody i).carrier ≤ volume (F.innerBody i).shade) :
    ∀ i ∈ F.closureShade.innerSet,
      (2⁻¹ : ENNReal) * lam * volume (F.closureShade.innerBody i).carrier ≤
        volume (F.closureShade.innerBody i).shade := by
  intro i hi
  rw [closureShade_innerSet] at hi
  rw [closureShade_innerBody_carrier]
  exact (hlam i hi).trans (volume_shade_le_volume_shade_closureShade (F.innerBody i))

end ClosureShadeVolume

end FactorFamily

section InducedShading

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-- **The induced shading does not see the closure** (blueprint
`lem:shadeInducedShadingClosureShade`): the shading induced on the enlargement of a convex body
`W` by the closure family of `V` coincides with the one induced by `V` itself.

Finiteness of `s` is genuinely used: for an infinite family the union of the closures is in
general a proper subset of the closure of the union. -/
theorem shade_inducedShading_closureShade (s : Finset ι) (V : ι → ShadedBody E)
    (W : ConvexSpaceBody E) :
    (inducedShading s (fun i ↦ (V i).closureShade.toShadedBody) W).shade =
      (inducedShading s V W).shade := by
  rw [shade_inducedShading]
  congr 1
  change Metric.cthickening (2 * W.scale) (⋃ i ∈ s, closure ((V i).shade)) =
    Metric.cthickening (2 * W.scale) (⋃ i ∈ s, (V i).shade)
  rw [← Finset.closure_biUnion, Metric.cthickening_closure]

end InducedShading

end ShadedBody
