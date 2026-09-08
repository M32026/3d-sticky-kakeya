/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineWindowLevelsTripwires
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorRefinement

/-!
# `T-S1(iii)` — the simultaneous refinement does **not** open a back door for the sticky grid family

 and   Re-cutting `(F)` onto a refined pair adds a
hypothesis (`IsShadedRefinementOf` and the tower on `Tube.UniformTubeSet.restrictOccupied`) to a
theorem whose whole purpose is to *exclude* the sticky grid family of
`Reduction/SpineCountFloorObstruction.lean`.  A hypothesis that the grid family satisfies for free
cannot be doing the excluding — so before the re-cut is written, the run has to know **where** the
exclusion lives, and that it is untouched by the refinement.

**It lives entirely in the window twin, and the refinement cannot reach it.**  This file compiles
the two halves.

## (a) The refinement clause is free on the grid family — the back door is real

`Kakeya.ML2Core.gridModel_bottom_coverClass_card_eq_one`: the grid's leaves are pairwise disjoint
(`Kakeya.ML2Core.pairwiseDisjoint_gridShaded`), so by
`Kakeya.ML2Core.card_coverClass_bot_le_one` **every** bottom class of the *ambient* family is a
singleton, and `Tube.coverClass_subset_of_subset` pushes that down to **every** subfamily at once.
On an occupied node the class is nonempty, so its cardinality is exactly `1`, and the two halves of
`Kakeya.ML2Core.IsClassHomogeneousOn` read `1 ≤ Cu * 1` at the bottom level for *any* subfamily and
*any* `1 ≤ Cu` — no pass, no loss, no choice of subfamily.  Together with
`Kakeya.ML2Core.isClassHomogeneousOn_self` (which gives the whole clause, at every level, for the
trivial refinement `S' := s'`), this is the record that

> **the sticky exclusion cannot come from the refinement.**

## (b) The twin still excludes, on the refined hierarchy — the door is shut

`Kakeya.ML2Core.not_levelClause_gridModel_restrictOccupied`: `T1`
(`Kakeya.ML2Core.not_levelClause_gridModel`) is stated at an *arbitrary* hierarchy over an arbitrary
nonempty subfamily of `Kakeya.ML2Core.gridIndex`, and `Tube.UniformTubeSet.restrictOccupied` returns
exactly such a hierarchy.  So the level clause fails on **every** refinement of the grid family, for
's reason — the arithmetic `δ^{-(c/N)η₁} > C²` is a statement about `η 1 > 0` and
the grid, and restriction does not touch it.  In fact restriction makes the refutation *easier*: the
restricted index set is smaller (`Kakeya.ML2Core.restrictOccupied_cover`), so the node count that
caps `Δ_max` only drops.

`Kakeya.ML2Core.not_countFloor_hypothesis` remains the record of why the un-strengthened floor
needed strengthening in the first place; nothing here reopens it.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## (a) The refinement clause is free on the grid family -/

open scoped Classical in
/-- **`T-S1(iii)a` — the back door, exhibited.**  On the sticky grid family every *occupied* bottom
class of **every** subfamily is a singleton, because the leaves are pairwise disjoint.  So the
bottom-level half of `Kakeya.ML2Core.IsClassHomogeneousOn` is satisfied by every subfamily
whatsoever, at every `1 ≤ Cu`, with `bN := 1` — with no pass, no polylogarithmic loss and no choice.

This is the precise sense in which "the pass is trivially satisfiable on the grid family"
( T-S1(iii)), and it is why the sticky exclusion **must** come from the window
twin and not from the refinement. -/
theorem gridModel_bottom_coverClass_card_eq_one {δ : NNReal} (hδ : 0 < δ) {K : ℕ} {C : NNReal}
    {s' : Finset (ULift.{u} ℕ)}
    (𝒰 : Tube.UniformTubeSet s' (fun n => (gridShaded.{u} δ K n).toTube) (Tube.ssfGridLen δ) C)
    (hN : 0 < Tube.ssfGridLen δ) {S : Finset (ULift.{u} ℕ)} (hS : S ⊆ s')
    {j : ULift.{u} ℕ} (hj : j ∈ S.image (𝒰.cover.assign (Tube.ssfGridLen δ))) :
    (Tube.coverClass S (𝒰.cover.assign (Tube.ssfGridLen δ)) j).card = 1 := by
  classical
  refine le_antisymm ?_ ?_
  · refine le_trans (Finset.card_le_card
      (Tube.coverClass_subset_of_subset hS (𝒰.cover.assign (Tube.ssfGridLen δ)) j)) ?_
    exact card_coverClass_bot_le_one 𝒰 hN (pairwiseDisjoint_gridShaded hδ s') j
  · rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
    simp only [Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    exact ⟨i, by simp [Tube.coverClass, hi]⟩

/-- **`T-S1(iii)a`, the level-wise half.**  The refinement clause holds, at *every* level, for the
trivial refinement `S' := s'`: `Kakeya.ML2Core.isClassHomogeneousOn_self`.  So `M1`'s new
`(F)` hypothesis is satisfiable on the grid family with `S' := s'`, `W := Z`, `Λf := 1`, and the
`IsShadedRefinementOf` conjunct adds **nothing** to the exclusion. -/
theorem gridModel_isClassHomogeneousOn_self {δ : NNReal} {K : ℕ} {C : NNReal}
    {s' : Finset (ULift.{u} ℕ)}
    (𝒰 : Tube.UniformTubeSet s' (fun n => (gridShaded.{u} δ K n).toTube) (Tube.ssfGridLen δ) C) :
    IsClassHomogeneousOn 𝒰 s' :=
  isClassHomogeneousOn_self 𝒰

/-! ## (b) The window twin still excludes, on the refined hierarchy -/

/-- **`T-S1(iii)b` — the door is shut.**  For **every** refinement `S ⊆ s'` of the sticky grid
family and every certificate `hhom` that carries it, the window twin's level clause **still fails**
on `Tube.UniformTubeSet.restrictOccupied`, at the same level `c` and by the same arithmetic as
`Kakeya.ML2Core.not_levelClause_gridModel`.

The proof is that `T1` was stated at an arbitrary hierarchy over an arbitrary nonempty subfamily of
`Kakeya.ML2Core.gridIndex`, which is exactly what `restrictOccupied` returns — so the transport is
the instantiation and nothing else.  **This is the control  requires before `M1`
is cut**: whatever the refinement does, the sticky grid family is excluded by the twin. -/
theorem not_levelClause_gridModel_restrictOccupied {δ : NNReal} {K : ℕ}
    {C : NNReal} {s' : Finset (ULift.{u} ℕ)} (hs' : s' ⊆ gridIndex.{u} K)
    (𝒰 : Tube.UniformTubeSet s' (fun n => (gridShaded.{u} δ K n).toTube) (Tube.ssfGridLen δ) C)
    {S : Finset (ULift.{u} ℕ)} (hS : S ⊆ s') (hSne : S.Nonempty)
    (hhom : IsClassHomogeneousOn 𝒰 S)
    {η₁ : ℝ} {c : ℕ} (hc : c ≤ Tube.ssfGridLen δ)
    (hRc : (δ : ℝ) + 6 * δ * K ≤ Tube.gridScale δ (Tube.ssfGridLen δ) c)
    (hbig : (C : ℝ) * C < ((1 : ℝ) / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ η₁) :
    ¬ ∀ j ∈ (𝒰.restrictOccupied hS hhom).cover.indexSet 0,
      ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) 0 : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ η₁)
        ≤ (C : ENNReal) * Kakeya.maxDensity ((𝒰.restrictOccupied hS hhom).nodesUnder c 0 j)
            (fun j' => ((𝒰.restrictOccupied hS hhom).cover.tube c j').toConvexSpaceBody) :=
  not_levelClause_gridModel (hS.trans hs') hSne (𝒰.restrictOccupied hS hhom) hc hRc hbig

/-! ## The record

Reading (a) and (b) together: on the sticky grid family the refinement clause is satisfied by the
trivial refinement and, at the bottom level, by **every** subfamily; and the twin's level clause
fails on **every** refinement.  So the re-cut of `(F)` onto a refined pair
* does **not** weaken the exclusion of the grid family (b), and
* does **not** strengthen it either (a) —

which is exactly the disposition  asks for: the exclusion is the twin's, before
and after `M1`. -/

end Kakeya.ML2Core
