/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeForcing

/-!
# The `redBody` host does **not** carry the fill-restoration clause — the obstruction

 named `Kakeya.ML2Core.SpineFloorGateRed.redBody` as the host for the `T-S2`
certificate, on the rationale that *"the repeated tube attains the max in both"*: `redBody`'s `inl`
block is one tube repeated, so restricting to it should preserve `Δ_max` exactly (clause 3).

## Why: `FillAt` sees NODES, and nodes never repeat

`Kakeya.ML2Core.FillAt` is a statement about `Tube.UniformTubeSet.nodesUnder` — a family of
**nodes** — and `Tube.UniformTubeSet.tube_injOn` makes distinct node indices carry **distinct**
tubes (`Kakeya.ML2Core.nodesUnder_tube_injOn` below).  `redBody`'s density contrast, by contrast,
lives entirely in repeated **members**: `redBody δ (Sum.inl n) = redTube δ` for *every* `n`, so its
member-level `Δ_max` reaches `⌊1/(24δ)⌋` purely by counting one body many times
(`Kakeya.ML2Core.SpineFloorGateRed.not_biasedFactorization_retains_maxDensity`).

**Repetition among members does not survive the passage to nodes.**  Members sharing a tube share
the *containment* that `Tube.UniformTubeSet.boundedOverlap` counts, so they occupy at most `Cu`
level-`c` nodes — `Kakeya.ML2Core.card_nodes_le_of_common_tube` — and therefore contribute at most
`Cu` to the node-level maximal density
(`Kakeya.ML2Core.maxDensity_nodes_le_of_common_tube`).  `Cu` is `δ`-free.

> **So on `redBody` the node-level contrast available to `FillAt` is `O(Cu)`, not `≈ δ^{-1}`.**  The
> `K`-fold contrast the host was chosen for is invisible to the predicate the certificate is about.

## What this does and does not rule out

* It does **not** say `redBody` cannot host clauses 1 and 2.  Clause 1 needs only a volume deficit
  (`Kakeya.ML2Core.not_fillAt_of_sum_lt`), and clause 2 needs a node at the hull scale; neither
  needs repetition.
* It **does** say clause 3 cannot be obtained from `redBody`'s repetition, which was the stated
  reason for choosing it.  A host for clause 3 must produce its `Δ_max` contrast from **distinct
  overlapping tubes at one radius**, not from a repeated one — and `boundedOverlap` caps *that* at
  `Cu` too, at any single level.

**Consequence, and it is the thing to rule on.**  A node-level `Δ_max` contrast bigger than `Cu` at
a single level is impossible in *any* `Tube.UniformTubeSet`, by
`Kakeya.ML2Core.maxDensity_nodesUnder_le_of_common_tube_cover`.  So clause 3 — an *equality* of
`Δ_max` between a family and a proper restriction — is not the obstacle; the obstacle is that
neither side can be large, so the certificate's force must come from the **volume deficit** of
clause 1 and the **hull-scale reading** of clause 2, with clause 3 read as *"the restriction did not
lower the (already `O(Cu)`) maximum"*.  That is still a meaningful separation and `redBody` may well
host it — but it is a different certificate from the one the rationale describes, and I will not
build it under the old rationale.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section HostObstruction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ C : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Nodes never repeat.**  The level-`c` cells under a node carry pairwise **distinct** tubes, by
`Tube.UniformTubeSet.tube_injOn`.  So a host whose density contrast comes from a repeated *member*
cannot exhibit it in `Kakeya.ML2Core.FillAt`, which sees only nodes. -/
theorem nodesUnder_tube_injOn (𝒰 : Tube.UniformTubeSet s T N C) {c k : ℕ} (hc : c ≤ N) (j : ι) :
    Set.InjOn (𝒰.cover.tube c) (𝒰.nodesUnder c k j : Set ι) := by
  classical
  refine Set.InjOn.mono ?_ (𝒰.tube_injOn c hc)
  intro j' hj'
  simp only [Finset.mem_coe] at hj'
  rw [Tube.UniformTubeSet.nodesUnder_eq_nodesIn, Tube.UniformTubeSet.mem_nodesIn_iff] at hj'
  exact_mod_cast hj'.1

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
open scoped Classical in
/-- **Members sharing a tube occupy at most `Cu` nodes.**  If every member of `A ⊆ s` lies inside
one `ρ_c`-tube `V`, then `A` meets at most `Cu` level-`c` nodes: each such node shares a member of
`s`
with `V`, and `Tube.UniformTubeSet.boundedOverlap` counts exactly those.

This is the obstruction in its sharpest form: **repetition among members buys nothing at node
level.** -/
theorem card_nodes_le_of_common_tube (𝒰 : Tube.UniformTubeSet s T N C) {c : ℕ} (hc : c ≤ N)
    (V : Tube (Tube.gridScale δ N c) E) {A : Finset ι} (hA : A ⊆ s)
    (hV : ∀ i ∈ A, (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) :
    ((A.image (𝒰.cover.assign c)).card : NNReal) ≤ C := by
  classical
  refine le_trans ?_ (𝒰.boundedOverlap c hc V)
  have hsub : A.image (𝒰.cover.assign c)
      ⊆ (𝒰.cover.indexSet c).filter (fun j => ∃ i ∈ s,
          (T i).toConvexSpaceBody ≤ (𝒰.cover.tube c j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) := by
    intro j hj
    simp only [Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    refine Finset.mem_filter.mpr ⟨𝒰.cover.assign_mem c hc i (hA hi), i, hA hi, ?_, hV i hi⟩
    exact 𝒰.cover.le_tube_assign c hc i (hA hi)
  exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hsub)

omit [Nontrivial E] in
open scoped Classical in
/-- **…and therefore contribute at most `Cu` to the node-level maximal density.**  `Cu` is
`δ`-free, so a `≈ δ^{-1}` member-level contrast collapses to `O(Cu)` at node level. -/
theorem maxDensity_nodes_le_of_common_tube (𝒰 : Tube.UniformTubeSet s T N C) {c : ℕ} (hc : c ≤ N)
    (V : Tube (Tube.gridScale δ N c) E) {A : Finset ι} (hA : A ⊆ s)
    (hV : ∀ i ∈ A, (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) :
    Kakeya.maxDensity (A.image (𝒰.cover.assign c))
        (fun j => (𝒰.cover.tube c j).toConvexSpaceBody)
      ≤ (C : ℝ≥0∞) := by
  refine (Kakeya.maxDensity_le_card _ _).trans ?_
  exact_mod_cast (ENNReal.coe_le_coe.mpr (card_nodes_le_of_common_tube 𝒰 hc V hA hV))

omit [Nontrivial E] in
open scoped Classical in
/-- **The general ceiling: at a single level, a node family covered by one `ρ_c`-tube has
`Δ_max ≤ Cu`, in *any* hierarchy.**  So no host can produce a single-level node-density contrast
larger than `Cu` inside one cell — the certificate's force must come from the **volume deficit**
(clause 1) and the **hull-scale reading** (clause 2), not from a large `Δ_max`. -/
theorem maxDensity_nodesUnder_le_of_common_tube_cover (𝒰 : Tube.UniformTubeSet s T N C)
    {c k : ℕ} (hc : c ≤ N) (V : Tube (Tube.gridScale δ N c) E)
    (hcov : 𝒰.nodesUnder c k j ⊆ (𝒰.cover.indexSet c).filter (fun j' => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (𝒰.cover.tube c j').toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)) :
    Kakeya.maxDensity (𝒰.nodesUnder c k j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
      ≤ (C : ℝ≥0∞) := by
  classical
  refine (Kakeya.maxDensity_le_card _ _).trans ?_
  have := 𝒰.boundedOverlap c hc V
  have hcard : ((𝒰.nodesUnder c k j).card : NNReal) ≤ C :=
    le_trans (by exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hcov)) this
  exact_mod_cast ENNReal.coe_le_coe.mpr hcard

end HostObstruction

end Kakeya.ML2Core
