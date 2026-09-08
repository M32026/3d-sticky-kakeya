/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Shading
public import Kakeya.ConvexHull
public import Mathlib.Order.Partition.Finpartition

/-!
# Basic API for factored families of convex bodies

For fixed index types, this file bundles a finite inner family, a finite outer family, and a
fixed choice of an outer body containing each inner body. The chosen outer body need not be
the unique outer body containing the inner body.

`ShadedBody.FactorFamily` has shaded inner bodies and unshaded outer bodies.
The fully shaded version additionally requires the shade of each inner body to lie in the shade
of its chosen outer body.
-/

@[expose] public section

open Convexity

namespace ConvexSpaceBody

universe w

open Classical in
/-- A finite family of convex bodies factored through a finite outer family.

The map `parent` fixes, for each member of the inner family, one member of the outer family
that contains it. No uniqueness of the containing outer body is required. -/
structure FactorFamily (E : Type w) [TopologicalSpace E] [ConvexSpace ℝ E]
    (ι κ : Type*) where
  /-- The finite indexing set of the inner family. -/
  innerSet : Finset ι
  /-- The inner family of convex bodies. -/
  innerBody : ι → ConvexSpaceBody E
  /-- The finite indexing set of the outer family. -/
  outerSet : Finset κ
  /-- The outer family of convex bodies. -/
  outerBody : κ → ConvexSpaceBody E
  /-- The chosen outer-body index of each inner body. -/
  parent : ι → κ
  /-- The chosen parent of an inner-family member belongs to the outer family. -/
  parent_mem : ∀ i ∈ innerSet, parent i ∈ outerSet
  /-- Every inner-family member lies in its chosen outer body. -/
  inner_le_parent : ∀ i ∈ innerSet, innerBody i ≤ outerBody (parent i)

namespace FactorFamily

variable {E : Type w} [TopologicalSpace E] [ConvexSpace ℝ E]
  {ι κ : Type*}

open Classical in
/-- The inner bodies whose chosen parent is `j`. -/
noncomputable def fiber (F : FactorFamily E ι κ) (j : κ) : Finset ι :=
  {i ∈ F.innerSet | F.parent i = j}

open Classical in
/-- The partition of the inner family into the fibers of its chosen-parent map. -/
noncomputable def finpartition (F : FactorFamily E ι κ) : Finpartition F.innerSet :=
  Finpartition.ofSetSetoid (Setoid.ker F.parent) F.innerSet

open Classical in
@[simp]
theorem mem_finpartition_part_iff (F : FactorFamily E ι κ) {i k : ι} :
    k ∈ F.finpartition.part i ↔
      i ∈ F.innerSet ∧ k ∈ F.innerSet ∧ F.parent i = F.parent k := by
  change k ∈ (Finpartition.ofSetSetoid (Setoid.ker F.parent) F.innerSet).part i ↔ _
  rw [Finpartition.mem_part_ofSetSetoid_iff_rel]
  rfl

open Classical in
/-- The part containing an inner index is its chosen parent's fiber. -/
theorem finpartition_part_eq_fiber (F : FactorFamily E ι κ) {i : ι}
    (hi : i ∈ F.innerSet) : F.finpartition.part i = F.fiber (F.parent i) := by
  ext k
  simp only [mem_finpartition_part_iff, fiber, Finset.mem_filter]
  tauto

/-- Restrict a factor family to a subset of its inner indexing set. -/
def ofSubset (F : FactorFamily E ι κ) {s : Finset ι} (hs : s ⊆ F.innerSet) :
    FactorFamily E ι κ where
  innerSet := s
  innerBody := F.innerBody
  outerSet := F.outerSet
  outerBody := F.outerBody
  parent := F.parent
  parent_mem i hi := F.parent_mem i (hs hi)
  inner_le_parent i hi := F.inner_le_parent i (hs hi)

/-- Regard a finite partition as a factor family, taking the convex hull of each part as its
outer body. -/
noncomputable def ofFinpartition {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (V : ι → ConvexSpaceBody E) (P : Finpartition s) : FactorFamily E ι (Finset ι) where
  innerSet := s
  innerBody := V
  outerSet := P.parts
  outerBody := fun t ↦ t.convexHull_biUnion V
  parent := P.part
  parent_mem i hi := show P.part i ∈ P.parts from P.part_mem.mpr hi
  inner_le_parent i hi :=
    Finset.le_convexHull_biUnion V (show i ∈ P.part i from P.mem_part hi)

/-- A part of a finite partition is its fiber in the associated factor family. -/
@[simp]
theorem ofFinpartition_fiber {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (V : ι → ConvexSpaceBody E) (P : Finpartition s) {t : Finset ι} (ht : t ∈ P.parts) :
    (ofFinpartition V P).fiber t = t := by
  ext i
  simp [ofFinpartition, fiber, P.part_eq_iff_mem ht, P.subset ht]

end FactorFamily

end ConvexSpaceBody

namespace ShadedBody

universe w

open Classical in
/-- A finite family of shaded convex bodies factored through a finite unshaded outer family. -/
structure FactorFamily (E : Type w) [TopologicalSpace E] [MeasurableSpace E]
    [ConvexSpace ℝ E] (ι κ : Type*) where
  /-- The finite indexing set of the inner family. -/
  innerSet : Finset ι
  /-- The inner family of shaded convex bodies. -/
  innerBody : ι → ShadedBody E
  /-- The finite indexing set of the unshaded outer family. -/
  outerSet : Finset κ
  /-- The unshaded outer family of convex bodies. -/
  outerBody : κ → ConvexSpaceBody E
  /-- The chosen outer-body index of each inner body. -/
  parent : ι → κ
  /-- The chosen parent of an inner-family member belongs to the outer family. -/
  parent_mem : ∀ i ∈ innerSet, parent i ∈ outerSet
  /-- Every inner-family member lies in its chosen outer body. -/
  inner_le_parent : ∀ i ∈ innerSet, (innerBody i).toConvexSpaceBody ≤ outerBody (parent i)

namespace FactorFamily

variable {E : Type w} [TopologicalSpace E] [MeasurableSpace E] [ConvexSpace ℝ E]
  {ι κ : Type*}

/-- Forget the inner shadings of a factor family. -/
def toFactorFamily (F : FactorFamily E ι κ) : ConvexSpaceBody.FactorFamily E ι κ where
  innerSet := F.innerSet
  innerBody := fun i ↦ (F.innerBody i).toConvexSpaceBody
  outerSet := F.outerSet
  outerBody := F.outerBody
  parent := F.parent
  parent_mem := F.parent_mem
  inner_le_parent := F.inner_le_parent

open Classical in
/-- The inner shaded bodies whose chosen parent is `j`. -/
noncomputable def fiber (F : FactorFamily E ι κ) (j : κ) : Finset ι :=
  {i ∈ F.innerSet | F.parent i = j}

open Classical in
/-- The partition of the inner shaded family into the fibers of its chosen-parent map. -/
noncomputable def finpartition (F : FactorFamily E ι κ) : Finpartition F.innerSet :=
  F.toFactorFamily.finpartition

open Classical in
@[simp]
theorem mem_finpartition_part_iff (F : FactorFamily E ι κ) {i k : ι} :
    k ∈ F.finpartition.part i ↔
      i ∈ F.innerSet ∧ k ∈ F.innerSet ∧ F.parent i = F.parent k :=
  F.toFactorFamily.mem_finpartition_part_iff

open Classical in
/-- The part containing an inner shaded index is its chosen parent's fiber. -/
theorem finpartition_part_eq_fiber (F : FactorFamily E ι κ) {i : ι}
    (hi : i ∈ F.innerSet) : F.finpartition.part i = F.fiber (F.parent i) := by
  ext k
  simp only [mem_finpartition_part_iff, fiber, Finset.mem_filter]
  tauto

/-- Restrict a factor family to a subset of its inner indexing set. -/
def ofSubset (F : FactorFamily E ι κ) {s : Finset ι} (hs : s ⊆ F.innerSet) :
    FactorFamily E ι κ where
  innerSet := s
  innerBody := F.innerBody
  outerSet := F.outerSet
  outerBody := F.outerBody
  parent := F.parent
  parent_mem i hi := F.parent_mem i (hs hi)
  inner_le_parent i hi := F.inner_le_parent i (hs hi)

end FactorFamily

open Classical in
/-- A finite family of shaded convex bodies factored through a finite shaded outer family.

Besides containment of the underlying convex bodies, the shade of every inner-family member
is required to lie in the shade of its chosen outer body. -/
structure ShadedFactorFamily (E : Type w) [TopologicalSpace E] [MeasurableSpace E]
    [ConvexSpace ℝ E] (ι κ : Type*) where
  /-- The finite indexing set of the inner family. -/
  innerSet : Finset ι
  /-- The inner family of shaded convex bodies. -/
  innerBody : ι → ShadedBody E
  /-- The finite indexing set of the outer family. -/
  outerSet : Finset κ
  /-- The outer family of shaded convex bodies. -/
  outerBody : κ → ShadedBody E
  /-- The chosen outer-body index of each inner body. -/
  parent : ι → κ
  /-- The chosen parent of an inner-family member belongs to the outer family. -/
  parent_mem : ∀ i ∈ innerSet, parent i ∈ outerSet
  /-- Every inner-family member lies in its chosen outer body. -/
  inner_le_parent : ∀ i ∈ innerSet,
    (innerBody i).toConvexSpaceBody ≤ (outerBody (parent i)).toConvexSpaceBody
  /-- Every inner shade lies in the shade of its chosen outer body. -/
  shade_subset_parent : ∀ i ∈ innerSet, (innerBody i).shade ⊆ (outerBody (parent i)).shade

namespace ShadedFactorFamily

variable {E : Type w} [TopologicalSpace E] [MeasurableSpace E] [ConvexSpace ℝ E]
  {ι κ : Type*}

/-- Forget the outer shadings of a fully shaded factor family. -/
def toFactorFamily (F : ShadedFactorFamily E ι κ) : FactorFamily E ι κ where
  innerSet := F.innerSet
  innerBody := F.innerBody
  outerSet := F.outerSet
  outerBody := fun j ↦ (F.outerBody j).toConvexSpaceBody
  parent := F.parent
  parent_mem := F.parent_mem
  inner_le_parent := F.inner_le_parent

open Classical in
/-- The inner shaded bodies whose chosen parent is `j`. -/
noncomputable def fiber (F : ShadedFactorFamily E ι κ) (j : κ) : Finset ι :=
  {i ∈ F.innerSet | F.parent i = j}

open Classical in
/-- The partition of the inner shaded family into the fibers of its chosen-parent map. -/
noncomputable def finpartition (F : ShadedFactorFamily E ι κ) : Finpartition F.innerSet :=
  F.toFactorFamily.finpartition

open Classical in
@[simp]
theorem mem_finpartition_part_iff (F : ShadedFactorFamily E ι κ) {i k : ι} :
    k ∈ F.finpartition.part i ↔
      i ∈ F.innerSet ∧ k ∈ F.innerSet ∧ F.parent i = F.parent k :=
  F.toFactorFamily.mem_finpartition_part_iff

open Classical in
/-- The part containing an inner shaded index is its chosen parent's fiber. -/
theorem finpartition_part_eq_fiber (F : ShadedFactorFamily E ι κ) {i : ι}
    (hi : i ∈ F.innerSet) : F.finpartition.part i = F.fiber (F.parent i) := by
  ext k
  simp only [mem_finpartition_part_iff, fiber, Finset.mem_filter]
  tauto

/-- Restrict a fully shaded factor family to a subset of its inner indexing set. -/
def ofSubset (F : ShadedFactorFamily E ι κ) {s : Finset ι} (hs : s ⊆ F.innerSet) :
    ShadedFactorFamily E ι κ where
  innerSet := s
  innerBody := F.innerBody
  outerSet := F.outerSet
  outerBody := F.outerBody
  parent := F.parent
  parent_mem i hi := F.parent_mem i (hs hi)
  inner_le_parent i hi := F.inner_le_parent i (hs hi)
  shade_subset_parent i hi := F.shade_subset_parent i (hs hi)

section TrimOuter

variable {E : Type w} [TopologicalSpace E] [T2Space E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [ConvexSpace ℝ E] {ι κ : Type*}

/-- **Trim the outer bodies of a fully shaded factor family.** Given, for every outer index `j`,
a convex body `K j` containing every inner body whose chosen parent is `j`, replace the outer
body at `j` by `K j`, and keep as its shade only the part of the old outer shade that lies in
`K j`.

This is the operation that lets one replace the outer family of a shaded factor family by a
prescribed family of containing bodies (in the Kakeya application: by dilates of tubes) without
losing the two containment fields. -/
noncomputable def trimOuter (G : ShadedFactorFamily E ι κ) (K : κ → ConvexSpaceBody E)
    (hK : ∀ i ∈ G.innerSet, (G.innerBody i).toConvexSpaceBody ≤ K (G.parent i)) :
    ShadedFactorFamily E ι κ where
  innerSet := G.innerSet
  innerBody := G.innerBody
  outerSet := G.outerSet
  outerBody j :=
    { toConvexSpaceBody := K j
      shade := (G.outerBody j).shade ∩ (K j).carrier
      measurableSet_shade := (G.outerBody j).measurableSet_shade.inter
        (K j).isCompact.isClosed.measurableSet
      shade_subset := Set.inter_subset_right }
  parent := G.parent
  parent_mem := G.parent_mem
  inner_le_parent := hK
  shade_subset_parent := by
    intro i hi
    exact Set.subset_inter (G.shade_subset_parent i hi)
      ((G.innerBody i).shade_subset.trans (fun _ hx => hK i hi hx))

variable (G : ShadedFactorFamily E ι κ) (K : κ → ConvexSpaceBody E)
  (hK : ∀ i ∈ G.innerSet, (G.innerBody i).toConvexSpaceBody ≤ K (G.parent i))

@[simp]
theorem trimOuter_innerSet : (G.trimOuter K hK).innerSet = G.innerSet := rfl

@[simp]
theorem trimOuter_innerBody : (G.trimOuter K hK).innerBody = G.innerBody := rfl

@[simp]
theorem trimOuter_outerSet : (G.trimOuter K hK).outerSet = G.outerSet := rfl

@[simp]
theorem trimOuter_parent : (G.trimOuter K hK).parent = G.parent := rfl

@[simp]
theorem trimOuter_outerBody_toConvexSpaceBody (j : κ) :
    ((G.trimOuter K hK).outerBody j).toConvexSpaceBody = K j := rfl

@[simp]
theorem trimOuter_outerBody_carrier (j : κ) :
    ((G.trimOuter K hK).outerBody j).carrier = (K j).carrier := rfl

@[simp]
theorem trimOuter_outerBody_shade (j : κ) :
    ((G.trimOuter K hK).outerBody j).shade = (G.outerBody j).shade ∩ (K j).carrier := rfl

end TrimOuter

end ShadedFactorFamily

end ShadedBody
