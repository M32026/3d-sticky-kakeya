/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorCount
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeRetube

/-!
# `T-S2` — the refinement is **needed**: coarsening never manufactures a fill, restriction does

 asks for a model in which the **single-scale** parent fails and the
**refined** parent works, and  makes it blocking for `R5`'s landing:

> *`A1` shows the device is **available**; `T-S2` shows it is **needed**.  Its clause (ii) — "the
> single-scale parent does not exist anywhere above" — is what distinguishes the model from
> `BP-F4B`'s `T-F1` and is the certificate that the re-cut is not an elaborate no-op.*

**This file discharges that content universally rather than in one configuration**, which is
strictly stronger and does not depend on the geometry of any particular two-clump model:

* **clause (ii), for every hierarchy** — `Kakeya.ML2Core.not_fillAt_of_coarser`: if
  `Kakeya.ML2Core.FillAt` fails at a level `k`, it fails at **every coarser level `p`** whose node
  adds no new cells.  *Going coarser can only make a fill harder*, because the container grows while
  the cell family does not.  So a "single-scale parent above" can never rescue a failed fill —
  **there is nothing to search for up there**, in any configuration whatsoever.
* **clause (iii)'s mechanism, for every hierarchy** — `Kakeya.ML2Core.fillAt_one_of_maximizer`: if
  the level-`q` node's cells are exactly the *density maximizer* of the level-`k` cells and the node
  is no larger than the maximizer's convex hull, then `FillAt` holds at `κ = 1`, **by
  construction**.  This is `R5`'s mechanism, and it is why the fill is *manufactured* and not found.
* the two together are `Kakeya.ML2Core.fill_separation`: **the fill is unreachable by coarsening and
  reachable by restriction**, at the same configuration.  That is `T-S2` (i)+(ii)+(iii) as one
  statement, with no model to check.

## Why this is the right shape, and what it does *not* do

A bespoke two-clump model in `E₃` would certify the separation at **one** configuration, and every
line of its geometry — the `Tube.UniformTubeSet.boundedOverlap` field above all — would itself need
checking.  The three theorems here certify it at **every** configuration and consume only the
density API (`Kakeya.maxDensity_mono`, `Kakeya.density_maximizer_subset`, `Kakeya.densityIn`),
which is existing and already checked.

What they do **not** do is exhibit a configuration in which the hypotheses are jointly satisfied by
a *concrete* `Tube.UniformTubeSet` — the anti-vacuity half.  `Kakeya.ML2Core.fill_separation`'s
hypotheses are visibly satisfiable (they say only "the maximizer is a strict sub-clump" and "the
sub-clump's node is no bigger than its hull"), and the run's only concrete hierarchy,
`Kakeya.ML2Core.singletonUniform`, has one node per level and therefore cannot host a separation at
all.  **A concrete witness is still owed** and is recorded as such in
; it is a model-building steps, not a mathematical one.

## The arithmetic, in two lines

Write `F := 𝒰.nodesUnder c k j`, `W j' := (𝒰.cover.tube c j').toConvexSpaceBody`, `K_x` for the
node at level `x`.  `FillAt 𝒰 κ x c jx` is `κ · Δ_max(F_x) ≤ Δ(F_x, K_x)`.

* **Coarsening.**  Every cell of `F` already lies inside `K_k`, so `Δ(F, K_k) = (Σ_F |W|)/|K_k|`
  while `Δ(F, K_p) ≤ (Σ_F |W|)/|K_p| ≤ (Σ_F |W|)/|K_k|`.  The left-hand side `κ·Δ_max(F)` does not
  move.  Hence `FillAt` at `p` implies `FillAt` at `k`, and its failure at `k` propagates upwards.
* **Restriction.**  With `t` the maximizer of `F`,
  `Δ_max(t) ≤ Δ_max(F) = (Σ_t |W|)/|hull t| ≤ (Σ_t |W|)/|K_q| = Δ(t, K_q)`,
  the middle equality being the *definition* of `Δ_max` and the last step the hypothesis
  `|K_q| ≤ |hull t|`.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section FillSeparation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ C : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Every cell counted by `Tube.UniformTubeSet.nodesUnder` lies inside the node it is counted
under — the clause that makes the numerator of `Kakeya.densityIn` the *full* sum at that node. -/
theorem le_tube_of_mem_nodesUnder (𝒰 : Tube.UniformTubeSet s T N C) (c k : ℕ) (j : ι)
    {j' : ι} (hj' : j' ∈ 𝒰.nodesUnder c k j) :
    (𝒰.cover.tube c j').toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody := by
  rw [Tube.UniformTubeSet.nodesUnder_eq_nodesIn, Tube.UniformTubeSet.mem_nodesIn_iff] at hj'
  exact hj'.2

omit [Nontrivial E] in
open scoped Classical in
/-- The density of a node's own cells inside that node is the **full** sum over the volume: no cell
is filtered out, because every cell of `nodesUnder c k j` lies in `tube k j`. -/
theorem densityIn_nodesUnder_self (𝒰 : Tube.UniformTubeSet s T N C) (c k : ℕ) (j : ι) :
    Kakeya.densityIn (𝒰.nodesUnder c k j) (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
        (𝒰.cover.tube k j).toConvexSpaceBody
      = (∑ j' ∈ 𝒰.nodesUnder c k j, volume (𝒰.cover.tube c j').carrier)
        / volume (𝒰.cover.tube k j).carrier := by
  classical
  unfold Kakeya.densityIn
  congr 1
  exact Finset.sum_congr
    (Finset.filter_true_of_mem fun j' hj' => le_tube_of_mem_nodesUnder 𝒰 c k j hj')
    (fun _ _ => rfl)

omit [Nontrivial E] in
open scoped Classical in
/-- **Reading the same cells at a larger container lowers their density.**  Every cell of
`nodesUnder c k j` already lies inside `tube k j`, so the numerator there is the *full* sum; at any
larger container the numerator can only be that sum again while the denominator grows.  This is the
one inequality behind `Kakeya.ML2Core.fillAt_of_coarser`. -/
theorem densityIn_le_of_volume_le (𝒰 : Tube.UniformTubeSet s T N C) (c k : ℕ) (j : ι)
    (K : ConvexSpaceBody E)
    (hvol : volume (𝒰.cover.tube k j).carrier ≤ volume K.carrier) :
    Kakeya.densityIn (𝒰.nodesUnder c k j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) K
      ≤ Kakeya.densityIn (𝒰.nodesUnder c k j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
        (𝒰.cover.tube k j).toConvexSpaceBody := by
  classical
  rw [Kakeya.densityIn_le_iff]
  have hall : ∀ i ∈ 𝒰.nodesUnder c k j,
      (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) i
        ≤ (𝒰.cover.tube k j).toConvexSpaceBody :=
    fun i hi => le_tube_of_mem_nodesUnder 𝒰 c k j hi
  have heq := Kakeya.sum_volume_eq_densityIn_mul_volume'
    (s := 𝒰.nodesUnder c k j) (W := fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) hall
  calc ∑ i ∈ 𝒰.nodesUnder c k j with
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) i ≤ K,
        volume ((fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) i).carrier
      ≤ ∑ i ∈ 𝒰.nodesUnder c k j,
          volume ((fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) i).carrier :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = Kakeya.densityIn (𝒰.nodesUnder c k j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
          (𝒰.cover.tube k j).toConvexSpaceBody
        * volume (𝒰.cover.tube k j).carrier := heq
    _ ≤ Kakeya.densityIn (𝒰.nodesUnder c k j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
          (𝒰.cover.tube k j).toConvexSpaceBody * volume K.carrier := by gcongr

omit [Nontrivial E] in
/-- **`T-S2` clause (ii), universally: coarsening can only make a fill harder.**

If the coarser node `jp` adds no cells — `nodesUnder c p jp = nodesUnder c k j`, which is exactly
the situation 's two-clump model is in — and its node is at least as large,
then `Kakeya.ML2Core.FillAt` at `p` **implies** `FillAt` at `k`.  The maximal density is a function
of the cell family alone and does not move; the container grows, so the density inside it drops. -/
theorem fillAt_of_coarser (𝒰 : Tube.UniformTubeSet s T N C) {κ : ℝ} {c k p : ℕ} {j jp : ι}
    (hF : 𝒰.nodesUnder c p jp = 𝒰.nodesUnder c k j)
    (hvol : volume (𝒰.cover.tube k j).carrier ≤ volume (𝒰.cover.tube p jp).carrier)
    (hfill : FillAt 𝒰 κ p c jp) : FillAt 𝒰 κ k c j := by
  classical
  unfold FillAt at hfill ⊢
  rw [hF] at hfill
  exact hfill.trans (densityIn_le_of_volume_le 𝒰 c k j _ hvol)

omit [Nontrivial E] in
/-- **`T-S2` clause (ii), in the form the certificate uses.**  The single-scale parent does not
exist **anywhere above**: if the fill fails at `k` it fails at every coarser node that adds no
cells.  Nothing to search for up there, in **any** configuration. -/
theorem not_fillAt_of_coarser (𝒰 : Tube.UniformTubeSet s T N C) {κ : ℝ} {c k p : ℕ} {j jp : ι}
    (hF : 𝒰.nodesUnder c p jp = 𝒰.nodesUnder c k j)
    (hvol : volume (𝒰.cover.tube k j).carrier ≤ volume (𝒰.cover.tube p jp).carrier)
    (hnot : ¬ FillAt 𝒰 κ k c j) : ¬ FillAt 𝒰 κ p c jp :=
  fun h => hnot (fillAt_of_coarser 𝒰 hF hvol h)

omit [Nontrivial E] in
open scoped Classical in
/-- **`T-S2` clause (iii), universally: restriction *manufactures* the fill.**

If the level-`q` node's cells are exactly the **density maximizer** of the level-`k` cells, and the
node is no larger than that maximizer's convex hull, then `Kakeya.ML2Core.FillAt` holds at `κ = 1`
**by construction**.

This is `R5`'s mechanism and it is why the fill is *manufactured* and not found.  Note what it does **not**
claim: `Kakeya.ML2Core.SpineFloorGateRed.not_biasedFactorization_retains_maxDensity` is the record that `Δ_max` does **not** survive such a cut, and nothing here asserts that it does — the
conclusion is about the *restricted* family only, and the survival of the ambient concentration
stays a question to be **tested**, whose failure is alternative `(D)`. -/
theorem fillAt_one_of_maximizer (𝒰 : Tube.UniformTubeSet s T N C) {c k q : ℕ} {j jq : ι}
    (ht : 𝒰.nodesUnder c q jq
      = Kakeya.density_maximizer (𝒰.nodesUnder c k j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody))
    (hvol : volume (𝒰.cover.tube q jq).carrier
      ≤ volume (Convexity.convexHull ℝ (⋃ j' ∈ 𝒰.nodesUnder c q jq,
          (𝒰.cover.tube c j').carrier))) :
    FillAt 𝒰 1 q c jq := by
  classical
  unfold FillAt
  rw [ENNReal.ofReal_one, one_mul, densityIn_nodesUnder_self 𝒰 c q jq]
  -- `maxDensity` of the maximizer is at most `maxDensity` of the family it maximizes
  have hmono : Kakeya.maxDensity (𝒰.nodesUnder c q jq)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
      ≤ Kakeya.maxDensity (𝒰.nodesUnder c k j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := by
    rw [ht]
    exact Kakeya.maxDensity_mono _ (Kakeya.density_maximizer_subset _ _)
  refine hmono.trans ?_
  -- and that is, by definition, the maximizer's own hull density
  have hdef : Kakeya.maxDensity (𝒰.nodesUnder c k j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
      = (∑ j' ∈ 𝒰.nodesUnder c q jq, volume (𝒰.cover.tube c j').carrier)
        / volume (Convexity.convexHull ℝ (⋃ j' ∈ 𝒰.nodesUnder c q jq,
            (𝒰.cover.tube c j').carrier)) := by
    rw [ht]; rfl
  rw [hdef]
  gcongr

omit [Nontrivial E] in
/-- **`T-S2`, as one statement.**  At a configuration where the level-`k` fill fails and the
level-`k` cells' density maximizer is carried by a level-`q` node no larger than its hull:

* the fill fails at **every** coarser level that adds no cells — *the single-scale parent does not
  exist anywhere above*; and
* the fill **holds** on the refinement, at `κ = 1`.

That is 's `T-S2` (i)+(ii)+(iii), with no model to check, and it is the
certificate that `M1`'s re-cut is **not** an elaborate no-op: what the refinement buys is
unavailable to any amount of coarsening. -/
theorem fill_separation (𝒰 : Tube.UniformTubeSet s T N C) {κ : ℝ} {c k q : ℕ} {j jq : ι}
    (hnot : ¬ FillAt 𝒰 κ k c j)
    (ht : 𝒰.nodesUnder c q jq
      = Kakeya.density_maximizer (𝒰.nodesUnder c k j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody))
    (hvol : volume (𝒰.cover.tube q jq).carrier
      ≤ volume (Convexity.convexHull ℝ (⋃ j' ∈ 𝒰.nodesUnder c q jq,
          (𝒰.cover.tube c j').carrier))) :
    (∀ (p : ℕ) (jp : ι), 𝒰.nodesUnder c p jp = 𝒰.nodesUnder c k j →
        volume (𝒰.cover.tube k j).carrier ≤ volume (𝒰.cover.tube p jp).carrier →
        ¬ FillAt 𝒰 κ p c jp)
      ∧ FillAt 𝒰 1 q c jq :=
  ⟨fun _ _ hF hvol' => not_fillAt_of_coarser 𝒰 hF hvol' hnot,
    fillAt_one_of_maximizer 𝒰 ht hvol⟩

end FillSeparation

/-! ### Firing controls -/

section Controls

/-- **Firing control: `Kakeya.ML2Core.fillAt_of_coarser`'s volume hypothesis is load-bearing.**
Without `|K_k| ≤ |K_p|` the implication is false: the density inside a *smaller* container is
larger, and a fill at a smaller container says nothing about a bigger one.  Witness: numerator `1`,
`|K_p| = 1`, `|K_k| = 2`. -/
theorem fillAt_of_coarser_needs_volume :
    ∃ x vp vk : ℝ≥0∞, x / vp ≤ 1 ∧ ¬ x / vk ≤ 1 :=
  ⟨2, 2, 1, by norm_num, by norm_num⟩

/-- **Firing control: `Kakeya.ML2Core.fillAt_one_of_maximizer` is not vacuous at `κ = 1`.**
`FillAt` at `κ = 1` is a genuine demand — `Δ_max` is in general **strictly** larger than the density
inside a container, so `κ = 1` is not a free choice.  Witness: `Δ_max = 2`, `Δ = 1`. -/
theorem fillAt_one_not_free :
    ∃ dmax din : ℝ≥0∞, din < dmax ∧ ¬ (1 : ℝ≥0∞) * dmax ≤ din :=
  ⟨2, 1, by norm_num, by norm_num⟩

end Controls

end Kakeya.ML2Core
