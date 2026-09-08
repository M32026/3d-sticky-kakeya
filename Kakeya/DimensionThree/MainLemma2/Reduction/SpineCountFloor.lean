/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineRefinedFloor

/-!
# GC-2: the assignment fibre, and its place under `nodesUnder`

Helper vocabulary for the count floor   The refined source's
thread cells `𝕊_m⟨T_p⟩` (l.5757–5760) are the **assignment fibres** — the level-`m` nodes
assigned a member of the class of the level-`p` node — while the tree's
`Tube.UniformTubeSet.nodesUnder` is the larger set of level-`m` nodes geometrically inside the
level-`p` node.  : `assignFibre ⊆ nodesUnder`
(`Tube.UniformTubeSet.assignFibre_subset_nodesUnder`), so a floor on the fibre passes to
`nodesUnder` by monotonicity, and the `nodesUnder` form of the floor is the weaker hypothesis.

Also here: iterated node nestedness (`Tube.GridCoverSystem.tube_le_of_le`), a member's fine node
lies under its coarse node (`Tube.UniformTubeSet.assign_mem_nodesUnder`), and the
volume-to-count comparison on the fibre (`Tube.UniformTubeSet.volume_biUnion_le_card_assignFibre`).
The floor itself is **refuted** in `Reduction/SpineCountFloorObstruction.lean`
(`Kakeya.ML2Core.not_countFloor_hypothesis`).
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube
open scoped NNReal ENNReal

namespace Tube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ : NNReal}

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Iterated nestedness of the nodes themselves.**  `GridCoverSystem.tube_nested` one step at a
time: a member's node at a fine index lies inside its node at every coarser index. -/
theorem GridCoverSystem.tube_le_of_le {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    (G : GridCoverSystem s T N) {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ N) {i : ι} (hi : i ∈ s) :
    (G.tube l (G.assign l i)).toConvexSpaceBody ≤ (G.tube k (G.assign k i)).toConvexSpaceBody := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ m hkm ih =>
      exact (G.tube_nested m hl i hi).trans (ih (by omega))

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **A member's fine node lies in the `nodesUnder` set of its coarse node.** -/
theorem UniformTubeSet.assign_mem_nodesUnder {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : UniformTubeSet s T N C) {p m : ℕ} (hpm : p ≤ m) (hm : m ≤ N)
    {i : ι} (hi : i ∈ s) :
    𝒰.cover.assign m i ∈ 𝒰.nodesUnder m p (𝒰.cover.assign p i) := by
  classical
  refine (𝒰.mem_nodesIn_iff m _ _).2 ⟨𝒰.cover.assign_mem m hm i hi, ?_⟩
  exact 𝒰.cover.tube_le_of_le hpm hm hi

/-- **The assignment fibre** `𝕊_m⟨T_p⟩` of the refined text: the level-`m` nodes *assigned* a
member of the class of the level-`p` node `jp`.  The refined proof's thread cells are these; the
tree's `Tube.UniformTubeSet.nodesUnder` is the larger set of level-`m` nodes merely *contained* in
`tube p jp`. -/
noncomputable def UniformTubeSet.assignFibre {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : UniformTubeSet s T N C) (m p : ℕ) (jp : ι) : Finset ι :=
  open scoped Classical in
  (coverClass s (𝒰.cover.assign p) jp).image (𝒰.cover.assign m)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- : the assignment fibre is contained in the
`nodesUnder` cell, so a count floor on the fibre implies the same floor on `nodesUnder`, and the
`nodesUnder` form of the floor is the *weaker* hypothesis. -/
theorem UniformTubeSet.assignFibre_subset_nodesUnder {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : UniformTubeSet s T N C) {p m : ℕ} (hpm : p ≤ m) (hm : m ≤ N) (jp : ι) :
    𝒰.assignFibre m p jp ⊆ 𝒰.nodesUnder m p jp := by
  classical
  intro k hk
  simp only [UniformTubeSet.assignFibre, Finset.mem_image] at hk
  obtain ⟨i, hi, rfl⟩ := hk
  simp only [coverClass, Finset.mem_filter] at hi
  obtain ⟨his, hia⟩ := hi
  have := 𝒰.assign_mem_nodesUnder hpm hm his
  rwa [hia] at this

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The cell's members are covered by the fibre's nodes.** -/
theorem UniformTubeSet.biUnion_carrier_subset {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : UniformTubeSet s T N C) {p m : ℕ} (hm : m ≤ N) (jp : ι) :
    (⋃ i ∈ coverClass s (𝒰.cover.assign p) jp, (T i).carrier)
      ⊆ ⋃ k ∈ 𝒰.assignFibre m p jp, (𝒰.cover.tube m k).carrier := by
  classical
  refine Set.iUnion₂_subset fun i hi => ?_
  have his : i ∈ s := by
    simpa only [coverClass, Finset.mem_filter] using (Finset.mem_filter.mp hi).1
  refine Set.subset_iUnion₂_of_subset (𝒰.cover.assign m i) ?_ ?_
  · exact Finset.mem_image_of_mem _ hi
  · exact 𝒰.cover.le_tube_assign m hm i his

/-- **The volume-to-count comparison, on the fibre.**  The members assigned under a level-`p` node
are covered by the level-`m` nodes of the assignment fibre, each of volume at most
`2^{n+1} ρ_m^{n-1}`; so the volume they fill is at most `#fibre` times that. -/
theorem UniformTubeSet.volume_biUnion_le_card_assignFibre {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C) (hδ1 : δ ≤ 1) {p m : ℕ} (hm : m ≤ N)
    (jp : ι) :
    volume (⋃ i ∈ coverClass s (𝒰.cover.assign p) jp, (T i).carrier)
      ≤ ((𝒰.assignFibre m p jp).card : ENNReal)
          * ((Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
              * (gridScale δ N m : ENNReal) ^ (Module.finrank ℝ E - 1)) := by
  classical
  refine (measure_mono (𝒰.biUnion_carrier_subset hm jp)).trans ?_
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hbound : ∀ k ∈ 𝒰.assignFibre m p jp, volume (𝒰.cover.tube m k).carrier
      ≤ (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
          * (gridScale δ N m : ENNReal) ^ (Module.finrank ℝ E - 1) := by
    intro k _
    have := Tube.volume_le (gridScale_le_one hδ1 N m) (𝒰.cover.tube m k)
    exact this.trans_eq (by push_cast; ring)
  calc ∑ k ∈ 𝒰.assignFibre m p jp, volume (𝒰.cover.tube m k).carrier
      ≤ ∑ _k ∈ 𝒰.assignFibre m p jp, (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
          * (gridScale δ N m : ENNReal) ^ (Module.finrank ℝ E - 1) := Finset.sum_le_sum hbound
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end Tube
