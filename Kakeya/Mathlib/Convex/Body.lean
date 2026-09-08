/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Geometry.Convex.Set
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Convex bodies (over convex spaces)

This file is an alternative to `Mathlib.Analysis.Convex.Body`. The definition of `ConvexSpaceBody`
in mathlib relies on the `SMul ℝ V` typeclass (through the `Convex ℝ` predicate), which makes it
impossible to talk about convex bodies in an affine space over the reals.

Here we instead build `ConvexSpaceBody` on top of the `ConvexSpace ℝ M` typeclass. Since every
affine space (in particular every `NormedAddTorsor`) is a `ConvexSpace`, this version applies to
affine spaces as well as to vector spaces.

To make this work we first introduce `IsConvexSet R S`, the statement that a subset `S` of a convex
space is closed under binary convex combinations. When the ambient space is a real vector space,
`IsConvexSet ℝ S` is equivalent to the usual `Convex ℝ S` (see `isConvexSet_iff_convex`), so the
existing mathlib `Convex` API can still be used to construct convex bodies in vector spaces.

## Main definitions

* `IsConvexSet R S`: a subset of a convex space is convex if it is closed under convex combinations.
* `ConvexSpaceBody M`: a convex, compact, nonempty subset of a real convex space `M`.
-/

-- This file defines a `ConvexSpaceBody` that clashes with mathlib's `ConvexBody`,
-- we shoud avoid using the latter until it is updated to work.
assert_not_imported Mathlib.Analysis.Convex.Body

@[expose] public section

open Convexity

/-- Every real affine space (`AddTorsor` over a real vector space) is a convex space, via its
canonical affine combination. In particular every real vector space is one (it is an `AddTorsor`
over itself).

Mathlib intentionally does not register this globally (`AddTorsor.toConvexSpace` and
`ConvexSpace.ofModule` are diamond-prone non-instances). We pick the affine structure as the
canonical one for this project, so that the affine API (e.g. `AddTorsor.convexCombPair_eq_lineMap`)
applies to `ConvexSpaceBody` over both affine spaces and vector spaces. It is given high priority so
that this affine structure is used consistently for `ConvexSpaceBody`, rather than mathlib's other
(propositionally-but-not-definitionally-equal) `ConvexSpace` instances on e.g. `ℝ` or `Pi` types. -/
noncomputable instance (priority := high) instConvexSpaceAddTorsor {V S : Type*}
    [AddCommGroup V] [Module ℝ V] [AddTorsor V S] : ConvexSpace ℝ S :=
  AddTorsor.toConvexSpace

variable {M : Type*}

/-! ### Relation to `Convex` in a vector space

We reuse mathlib's `Convexity.IsConvexSet`, and relate it to the usual `Convex ℝ` predicate. -/

section VectorSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- In a real vector space, a binary convex combination is the expected linear combination. -/
theorem convexCombPair_eq_smul_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : E) :
    convexCombPair s t hs ht h x y = s • x + t • y := by
  have ht' : t = 1 - s := by linarith
  subst ht'
  rw [AddTorsor.convexCombPair_eq_lineMap, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  module

/-- In a real vector space, `IsConvexSet ℝ` agrees with the usual notion of convexity. -/
theorem isConvexSet_iff_convex {S : Set E} : IsConvexSet ℝ S ↔ Convex ℝ S := by
  constructor
  · intro h x hx y hy s t hs ht hst
    rw [← convexCombPair_eq_smul_add hs ht hst]
    exact h.convexCombPair_mem hx hy hs ht hst
  · intro h
    refine IsConvexSet.of_convexCombPair_mem fun s t hs ht hst x hx y hy => ?_
    rw [convexCombPair_eq_smul_add hs ht hst]
    exact h hx hy hs ht hst

alias ⟨Convexity.IsConvexSet.convex, Convex.isConvexSet⟩ := isConvexSet_iff_convex

end VectorSpace

/-! ### Affine images

The image of a convex set under an affine map of real affine spaces is convex. This works at the
level of affine spaces (`AddTorsor`), not just vector spaces, since it only uses that an affine map
commutes with `AffineMap.lineMap`. -/

section AffineSpace

variable
  {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]
  {W Q : Type*} [AddCommGroup W] [Module ℝ W] [AddTorsor W Q]

open Convexity in
/-- The image of a convex set under an affine map of real affine spaces is convex. -/
theorem Convexity.IsConvexSet.affineMap_image (f : P →ᵃ[ℝ] Q) {S : Set P}
    (h : IsConvexSet ℝ S) : IsConvexSet ℝ (f '' S) := by
  refine IsConvexSet.of_convexCombPair_mem fun a b ha hb hab x hx y hy => ?_
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨convexCombPair a b ha hb hab x' y', h.convexCombPair_mem hx' hy' ha hb hab, ?_⟩
  rw [AddTorsor.convexCombPair_eq_lineMap, AddTorsor.convexCombPair_eq_lineMap, f.apply_lineMap]

open Convexity in
/-- The preimage of a convex set under an affine map of real affine spaces is convex. -/
theorem Convexity.IsConvexSet.affineMap_preimage (f : P →ᵃ[ℝ] Q) {S : Set Q}
    (h : IsConvexSet ℝ S) : IsConvexSet ℝ (f ⁻¹' S) := by
  refine IsConvexSet.of_convexCombPair_mem fun a b ha hb hab x hx y hy => ?_
  rw [Set.mem_preimage] at hx hy
  rw [Set.mem_preimage]
  rw [AddTorsor.convexCombPair_eq_lineMap, f.apply_lineMap,
    ← AddTorsor.convexCombPair_eq_lineMap]
  exact h.convexCombPair_mem hx hy ha hb hab

end AffineSpace

/-! ### Convex bodies -/

/-- Let `M` be a real convex space. A subset of `M` is a convex body if and only if it is convex,
compact, and nonempty. -/
structure ConvexSpaceBody (M : Type*) [TopologicalSpace M] [ConvexSpace ℝ M] where
  /-- The **carrier set** underlying a convex body: the set of points contained in it. -/
  carrier : Set M
  /-- A convex body has convex carrier set. -/
  convex' : IsConvexSet ℝ carrier
  /-- A convex body has compact carrier set. -/
  isCompact' : IsCompact carrier
  /-- A convex body has non-empty carrier set. -/
  nonempty' : carrier.Nonempty

-- Initialize the `simps` projections before the `SetLike` instance below is in scope, so that
-- `@[simps]` lemmas are stated in terms of the `carrier` projection rather than the coercion.
initialize_simps_projections ConvexSpaceBody

namespace ConvexSpaceBody

section ConvexSpace

variable [TopologicalSpace M] [ConvexSpace ℝ M]

instance : SetLike (ConvexSpaceBody M) M where
  coe := ConvexSpaceBody.carrier
  coe_injective K L h := by
    cases K
    cases L
    congr

instance : PartialOrder (ConvexSpaceBody M) := .ofSetLike (ConvexSpaceBody M) M

/-- The carrier of a convex body is convex. -/
protected theorem isConvexSet (K : ConvexSpaceBody M) : IsConvexSet ℝ (K : Set M) :=
  K.convex'

protected theorem isCompact (K : ConvexSpaceBody M) : IsCompact (K : Set M) :=
  K.isCompact'

protected theorem nonempty (K : ConvexSpaceBody M) : (K : Set M).Nonempty :=
  K.nonempty'

@[ext]
protected theorem ext {K L : ConvexSpaceBody M} (h : (K : Set M) = L) : K = L :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Set M) (h₁ h₂ h₃) : (mk s h₁ h₂ h₃ : Set M) = s :=
  rfl

instance [Zero M] : Zero (ConvexSpaceBody M) where
  zero := ⟨{0}, IsConvexSet.singleton, isCompact_singleton, Set.singleton_nonempty 0⟩

noncomputable instance [Nonempty M] : Inhabited (ConvexSpaceBody M) :=
  ⟨{Classical.arbitrary M}, IsConvexSet.singleton, isCompact_singleton, Set.singleton_nonempty _⟩

end ConvexSpace

section VectorSpace

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/-- The carrier of a convex body in a real vector space is `Convex`. -/
protected theorem convex (K : ConvexSpaceBody E) : Convex ℝ K.carrier :=
  K.convex'.convex

end VectorSpace

section PseudoMetricSpace

variable [PseudoMetricSpace M] [ConvexSpace ℝ M]

protected theorem isBounded (K : ConvexSpaceBody M) : Bornology.IsBounded (K : Set M) :=
  K.isCompact.isBounded

end PseudoMetricSpace

end ConvexSpaceBody
