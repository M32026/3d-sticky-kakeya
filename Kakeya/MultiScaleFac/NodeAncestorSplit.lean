/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.FibrePacking
public import Kakeya.Frostman
public import Kakeya.GridScale
public import Kakeya.MultiScaleFac.ScaleGapTransport
public import Kakeya.MultiScaleFac.Stopping
public import Kakeya.Sticky
public import Kakeya.Tube.Basic
public import Kakeya.Uniform
public import Kakeya.MultiScaleFac.UniformBridgeKT

/-!
# The nodes inside a dilated node, split over their ancestors

The geometry of the ancestor split and the node counting it supports, and the spreading of a
node-level lower bound to an arbitrary container.  Nothing here spends a power of `δ`: every
bound is a dimensional constant against a ratio of scales, which is what lets the dichotomy carry
a subpolynomial loss.

Sliced out of the former `DividingScalesA`, merged with the former `NodeDensityBounds`.

## Uniform two-sided density bounds for the nodes inside a dilated node

The third bullet of alternative (ii) of GWZ Lemma 7.7(A) needs, as an input to
`Kakeya.MultiScaleFac.le_frostmanConstant_nodesIn_dilate_of_band`, a bound on the density of the
level-`b` nodes contained in the `8ρ_c`-dilate of a level-`c` node, *inside that dilate*.  The
bound must be uniform in the node and must carry **no power of `δ`**: it is a statement of bounded
overlap of the hierarchy, and the constant has to be fixed before `δ` is chosen.

This section supplies both directions.  The mechanism is the same on both sides and is purely a
volume count.  Write `n = Module.finrank ℝ E` and `p = n - 1`.  A tube of thickness `r` has volume
between
`c_n r ^ p` and `C_n r ^ p`, so:

* the total volume of the level-`b` nodes in the dilate is at most `C_n · (#nodes · ρ_b ^ p)`;
* the volume of the dilate itself is at least `c_n · 8 ^ p · ρ_c ^ p`.

Hence as soon as the *count* obeys the natural comparison `#nodes · ρ_b ^ p ≤ Cv · ρ_c ^ p` -- which
is exactly bounded overlap of the hierarchy, with `Cv` a pure overlap constant -- the density is at
most `C_n / (c_n · 8 ^ p) · Cv`, with no `δ` anywhere.  The mirrored lower bound swaps the two
volume estimates and gives `c_n / (C_n · 8 ^ p) · Cv`.

The two constants are `Kakeya.MultiScaleFac.nodeDensityUBConst` and
`Kakeya.MultiScaleFac.nodeDensityLBConst`; both are explicit functions of the ambient dimension
alone.
-/

@[expose] public section

open MeasureTheory Real Metric
open scoped Topology

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The nodes inside a dilated node, split over their ancestors

The terminal step of the stopping time produces a *leaf-anchored* lower bound, which
`UniformBridge.frostmanConstant_fibre_le_mul_frostmanConstant_nodesIn` converts into a lower bound
for the node Frostman constant on the `8 ρ_a`-dilate of a single level-`a` node.  The third
bullet of alternative (ii), on the other hand, is stated on the *undilated* nodes, and the
homogenizing band is available only there: the Frostman constant of the nodes under a level-`a`
node depends only on what sits inside that node, which is what makes the single homogenizing pass
correct, whereas the same quantity on a dilate sees the neighbouring classes too.

Bridging the two is a covering argument, and the three lemmas below are its pieces: every level-`b`
node lies inside its own level-`a` ancestor, boundedly many ancestors occur inside a dilate, and the
count of them is dimensional.  Nothing here costs a power of `δ`. -/

section AncestorSplit

variable {ι : Type*}

/-- **Boundedly many `ρ_a`-tubes catch every member inside a tube of radius `8 ρ_a`.**

The bound is dimensional: the ratio of the two radii is the absolute constant `32` after the
`Tube.rescale_le_of_le` inflation, so the packing count of `exists_gapFibre_cover_of_ratio` does not
see `δ`.  This is the only geometric input of the split. -/
private theorem exists_gridScale_cover_of_members_in_tube {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N a : ℕ} {r : NNReal} (hδ : 0 < δ) (h2δ : 2 * δ ≤ gridScale δ N a)
    (hr : r ≤ 8 * gridScale δ N a) (K : Tube r E) {i₀ : ι}
    (hi₀K : (T i₀).toConvexSpaceBody ≤ K.toConvexSpaceBody) :
    ∃ A ⊆ s,
      (A.card : ℝ) ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
          * (32 : ℝ) ^ (2 * Module.finrank ℝ E) ∧
      ∀ i ∈ s, (T i).toConvexSpaceBody ≤ K.toConvexSpaceBody →
        ∃ i₂ ∈ A, (T i).toConvexSpaceBody
          ≤ ((T i₂).rescale (gridScale δ N a)).toConvexSpaceBody := by
  classical
  set σa := gridScale δ N a
  have hσa_pos : 0 < σa := gridScale_pos hδ N a
  have hK_le : K.toConvexSpaceBody ≤ ((T i₀).rescale (32 * σa)).toConvexSpaceBody :=
    (Tube.rescale_le_of_le (T i₀) K hi₀K).trans
      (Tube.rescale_le_rescale_of_radius_le (T i₀)
        (by rw [show (32 : NNReal) * σa = 4 * (8 * σa) by ring]; exact mul_le_mul_right hr 4))
  obtain ⟨A, hA_sub, hA_card, hcover⟩ :=
    exists_gapFibre_cover_of_ratio (E := E) (ι := ι) (δ := δ) (σ := δ) (ρ := σa) (ρ' := 32 * σa)
      (s := s) (T := T)
      hσa_pos le_rfl h2δ (le_mul_of_one_le_left hσa_pos.le (by norm_num : (1 : NNReal) ≤ 32)) i₀
  have hratio : ((32 * σa : NNReal) : ℝ) / (σa : ℝ) = 32 := by
    rw [NNReal.coe_mul, mul_div_assoc, div_self (by exact_mod_cast hσa_pos.ne' : (σa : ℝ) ≠ 0),
      mul_one]
    norm_num
  refine ⟨A, hA_sub, by simpa only [hratio] using hA_card, fun i hi_s hiK => ?_⟩
  obtain ⟨i₂, hi₂A, hi₂fib⟩ := hcover i
    (by rw [fibreIndex_self]; exact Finset.mem_filter.mpr ⟨hi_s, hiK.trans hK_le⟩)
  rw [fibreIndex_self] at hi₂fib
  exact ⟨i₂, hi₂A, (Finset.mem_filter.mp hi₂fib).2⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The nodes inside a container are covered by the nodes under their ancestors.**  The `nodesIn`
analogue of `UniformBridge.coverClass_subset_biUnion_nodesUnder`, which states the same
decomposition for a class of *members*; the passage from members to nodes is
`UniformTubeSet.nodeAncestor`.  No hypothesis on `K` is needed. -/
private theorem nodesIn_subset_biUnion_nodesUnder {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} [DecidableEq ι] (𝒰 : UniformTubeSet s T N C) {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ N) (hs : s.Nonempty) (K : ConvexSpaceBody E) :
    𝒰.nodesIn b K
      ⊆ ((𝒰.nodesIn b K).image (𝒰.nodeAncestor b a)).biUnion
          (fun j => 𝒰.nodesUnder b a j) := by
  intro w hw
  have h := ((𝒰.mem_nodesIn_iff b K w).mp hw).1
  refine Finset.mem_biUnion.mpr ⟨𝒰.nodeAncestor b a w, Finset.mem_image_of_mem _ hw, ?_⟩
  rw [UniformTubeSet.nodesUnder_eq_nodesIn, UniformTubeSet.mem_nodesIn_iff]
  exact ⟨h, 𝒰.tube_le_tube_nodeAncestor hab hb hs h⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The ancestor count, given a covering of the members of the container by `ρ_a`-tubes.**  The
shared engine of `Kakeya.MultiScaleFac.card_image_nodeAncestor_le` and its `_ratio` companion: each
ancestor is witnessed by a member of `s` in the container, hence sits in one of the `M` classes cut
out by the covering tubes, and Definition 2.1(ii) allows at most `C` ancestors per class. -/
private theorem card_image_nodeAncestor_le_of_cover {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} [DecidableEq ι] (𝒰 : UniformTubeSet s T N C) {a b : ℕ}
    (ha : a ≤ N) (hb : b ≤ N) (hs : s.Nonempty) {r : NNReal} (K : Tube r E) {M : ℝ} (hM : 0 ≤ M)
    (hcov : ∀ i₀ : ι, (T i₀).toConvexSpaceBody ≤ K.toConvexSpaceBody →
      ∃ A ⊆ s, (A.card : ℝ) ≤ M ∧
        ∀ i ∈ s, (T i).toConvexSpaceBody ≤ K.toConvexSpaceBody →
          ∃ i₂ ∈ A, (T i).toConvexSpaceBody
            ≤ ((T i₂).rescale (gridScale δ N a)).toConvexSpaceBody) :
    (((𝒰.nodesIn b K.toConvexSpaceBody).image (𝒰.nodeAncestor b a)).card : ℝ)
      ≤ M * (C : ℝ) := by
  classical
  set σa : NNReal := gridScale δ N a
  set Anc : Finset ι := (𝒰.nodesIn b K.toConvexSpaceBody).image (𝒰.nodeAncestor b a)
  rcases Finset.eq_empty_or_nonempty (𝒰.nodesIn b K.toConvexSpaceBody) with hempty | ⟨w, hw⟩
  · simpa [Anc, hempty] using mul_nonneg hM (NNReal.coe_nonneg C)
  obtain ⟨hwidx, hwK⟩ := (𝒰.mem_nodesIn_iff b K.toConvexSpaceBody w).mp hw
  obtain ⟨i₀, hi₀, hwi₀, -⟩ := 𝒰.exists_nodeAncestor_witness (a := a) hb hs hwidx
  obtain ⟨A, -, hAcard, hcover⟩ :=
    hcov i₀ ((hwi₀ ▸ 𝒰.cover.le_tube_assign b hb i₀ hi₀).trans hwK)
  set S : ι → Finset ι := fun i₂ => (𝒰.cover.indexSet a).filter (fun j => ∃ i ∈ s,
    (T i).toConvexSpaceBody ≤ (𝒰.cover.tube a j).toConvexSpaceBody ∧
    (T i).toConvexSpaceBody ≤ ((T i₂).rescale σa).toConvexSpaceBody)
  have hAnc_sub : Anc ⊆ A.biUnion S := by
    intro j hj
    obtain ⟨w, hw, hwj⟩ := Finset.mem_image.mp hj
    obtain ⟨hwidx, hwK⟩ := (𝒰.mem_nodesIn_iff b K.toConvexSpaceBody w).mp hw
    obtain ⟨i, his, hwi, hji⟩ := 𝒰.exists_nodeAncestor_witness (a := a) hb hs hwidx
    obtain ⟨i₂, hi₂A, hiV₂⟩ :=
      hcover i his ((hwi ▸ 𝒰.cover.le_tube_assign b hb i his).trans hwK)
    have hji' : j = 𝒰.cover.assign a i := by rw [← hwj, hji]
    exact Finset.mem_biUnion.mpr ⟨i₂, hi₂A, Finset.mem_filter.mpr
      ⟨hji' ▸ 𝒰.cover.assign_mem a ha i his,
        i, his, hji' ▸ 𝒰.cover.le_tube_assign a ha i his, hiV₂⟩⟩
  calc
    (Anc.card : ℝ) ≤ (∑ i₂ ∈ A, ((S i₂).card : ℝ)) := by
        exact_mod_cast (Finset.card_le_card hAnc_sub).trans Finset.card_biUnion_le
    _ ≤ (∑ _i₂ ∈ A, (C : ℝ)) :=
        Finset.sum_le_sum fun i₂ _ =>
          NNReal.coe_le_coe.mpr (𝒰.boundedOverlap a ha ((T i₂).rescale σa))
    _ ≤ M * (C : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hAcard (NNReal.coe_nonneg C)

/-- **Only boundedly many ancestors occur inside a dilated node.**  The ancestors are among the
level-`a` nodes meeting one of the boundedly many `ρ_a`-tubes of
`exists_gridScale_cover_of_members_in_tube`, and Definition 2.1(ii) allows at most `C` of them per
tube.  The constant is dimensional times `C`; in particular it carries no power of `δ`. -/
theorem card_image_nodeAncestor_le {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} [DecidableEq ι] (hδ : 0 < δ) (𝒰 : UniformTubeSet s T N C) {a b : ℕ}
    (ha : a ≤ N) (hb : b ≤ N) (hs : s.Nonempty) (h2δ : 2 * δ ≤ gridScale δ N a)
    {r : NNReal} (hr : r ≤ 8 * gridScale δ N a) (K : Tube r E) :
    (((𝒰.nodesIn b K.toConvexSpaceBody).image (𝒰.nodeAncestor b a)).card : ℝ)
      ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E) * (32 : ℝ) ^ (2 * Module.finrank ℝ E)
          * (C : ℝ) :=
  card_image_nodeAncestor_le_of_cover 𝒰 ha hb hs K (by positivity)
    fun _ hi₀K => exists_gridScale_cover_of_members_in_tube hδ h2δ hr K hi₀K

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The nodes under a node are few**, upper half of the counting band.  The classes of the
level-`b` nodes contained in a level-`c` node are pairwise disjoint and all sit inside the set of
members merely *contained* in that level-`c` node, which `ChainUniformTubeSet.card_filter_le` bounds
by `C ^ 2` times the branching number; each class being `≥ N_{ρ_b} / C`, the third power appears. -/
private theorem card_nodesUnder_mul_branchingN_le {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu) (hCu : 1 ≤ Cu)
    {c b : ℕ} (hc : c ≤ N) (hb : b ≤ N) {j : ι} (hj : j ∈ 𝒰.cover.indexSet c) :
    ((𝒰.nodesUnder b c j).card : NNReal) * 𝒰.branchingN b ≤ Cu ^ 3 * 𝒰.branchingN c := by
  classical
  set u : Finset ι := 𝒰.nodesUnder b c j with hu
  set F : Finset ι := {i ∈ s | (T i).toConvexSpaceBody ≤ (𝒰.cover.tube c j).toConvexSpaceBody}
  have hmem : ∀ w ∈ u, w ∈ 𝒰.cover.indexSet b ∧
      (𝒰.cover.tube b w).toConvexSpaceBody ≤ (𝒰.cover.tube c j).toConvexSpaceBody := by
    intro w hw
    rw [hu, UniformTubeSet.nodesUnder_eq_nodesIn] at hw
    exact (𝒰.mem_nodesIn_iff b (𝒰.cover.tube c j).toConvexSpaceBody w).mp hw
  have hdisj : (u : Set ι).PairwiseDisjoint (fun w => coverClass s (𝒰.cover.assign b) w) := by
    intro w _ w' _ hne
    simp only [Function.onFun, Finset.disjoint_left, coverClass, Finset.mem_filter]
    exact fun i hi hi' => hne (hi.2.symm.trans hi'.2)
  have hsub : u.biUnion (fun w => coverClass s (𝒰.cover.assign b) w) ⊆ F := by
    intro i hi
    obtain ⟨w, hw, hiw⟩ := Finset.mem_biUnion.mp hi
    simp only [coverClass, Finset.mem_filter] at hiw
    exact Finset.mem_filter.mpr ⟨hiw.1,
      (hiw.2 ▸ 𝒰.cover.le_tube_assign b hb i hiw.1).trans (hmem w hw).2⟩
  have hsum_le : (∑ w ∈ u, ((coverClass s (𝒰.cover.assign b) w).card : NNReal)) ≤
      (F.card : NNReal) := by
    exact_mod_cast (Finset.card_biUnion hdisj).symm.trans_le (Finset.card_le_card hsub)
  have hcardF : (F.card : NNReal) ≤ Cu ^ 2 * 𝒰.branchingN c := by
    simpa [F, UniformTubeSet.toChain, GridCoverSystem.toChain] using
      (ChainUniformTubeSet.card_filter_le (𝒰.toChain) hCu hc hj)
  calc
    (u.card : NNReal) * 𝒰.branchingN b = (∑ _w ∈ u, 𝒰.branchingN b : NNReal) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (∑ w ∈ u, Cu * ((coverClass s (𝒰.cover.assign b) w).card : NNReal)) :=
        Finset.sum_le_sum fun w hw => 𝒰.le_card_class b hb w (hmem w hw).1
    _ = Cu * (∑ w ∈ u, ((coverClass s (𝒰.cover.assign b) w).card : NNReal)) := by
        rw [Finset.mul_sum]
    _ ≤ Cu * (Cu ^ 2 * 𝒰.branchingN c) := mul_le_mul_right (hsum_le.trans hcardF) Cu
    _ = Cu ^ 3 * 𝒰.branchingN c := by ring

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Two nodes of the same level carry comparably many nodes of a finer level.**

This is what keeps the ancestor split from losing: the sum over the boundedly many ancestors is
compared with the single node whose dilate is the container, and their `𝕋_b`-counts differ only by a
constant. -/
private theorem card_nodesUnder_le_mul_card_nodesUnder {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu) (hCu : 1 ≤ Cu)
    {c b : ℕ} (hc : c ≤ N) (hb : b ≤ N) (hcb : c ≤ b) (hs : s.Nonempty)
    {j j' : ι} (hj : j ∈ 𝒰.cover.indexSet c) (hj' : j' ∈ 𝒰.cover.indexSet c) :
    ((𝒰.nodesUnder b c j).card : NNReal)
      ≤ Cu ^ 5 * ((𝒰.nodesUnder b c j').card : NNReal) := by
  refine le_of_mul_le_mul_right ?_ (branchingN_pos 𝒰 hCu hs hb)
  calc ((𝒰.nodesUnder b c j).card : NNReal) * 𝒰.branchingN b
      ≤ Cu ^ 3 * 𝒰.branchingN c := card_nodesUnder_mul_branchingN_le 𝒰 hCu hc hb hj
    _ ≤ Cu ^ 3 * (Cu ^ 2 * (((𝒰.nodesUnder b c j').card : NNReal) * 𝒰.branchingN b)) :=
        mul_le_mul_right (branchingN_le_mul_card_nodesUnder 𝒰 hcb hb hc hj') (Cu ^ 3)
    _ = (Cu ^ 5 * ((𝒰.nodesUnder b c j').card : NNReal)) * 𝒰.branchingN b := by ring

omit [Nontrivial E] in
/-- **The numerator of the split.**  `maxDensity` is subadditive along the ancestor decomposition,
which is the only place that decomposition is used. -/
theorem maxDensity_nodesIn_le_sum_nodesUnder {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} [DecidableEq ι] (𝒰 : UniformTubeSet s T N Cu) {c b : ℕ} (hcb : c ≤ b)
    (hb : b ≤ N) (hs : s.Nonempty) (K : ConvexSpaceBody E) :
    Kakeya.maxDensity (𝒰.nodesIn b K) (fun w => (𝒰.cover.tube b w).toConvexSpaceBody)
      ≤ ∑ j ∈ (𝒰.nodesIn b K).image (𝒰.nodeAncestor b c),
          Kakeya.maxDensity (𝒰.nodesUnder b c j)
            (fun w => (𝒰.cover.tube b w).toConvexSpaceBody) :=
  maxDensity_le_sum_of_subset_biUnion _ (nodesIn_subset_biUnion_nodesUnder 𝒰 hcb hb hs K)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **A node's own fine nodes survive inside its dilate.**  This is what keeps the denominator of
the ancestor split from degenerating: the container is a dilate of one of the level-`c` nodes, so it
holds at least that node's entire `𝕋_b[T_c]`. -/
theorem nodesUnder_subset_nodesIn_rescale {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu) {c b : ℕ} (j : ι) {r : NNReal}
    (hr : gridScale δ N c ≤ r) :
    𝒰.nodesUnder b c j ⊆ 𝒰.nodesIn b ((𝒰.cover.tube c j).rescale r).toConvexSpaceBody := by
  rw [UniformTubeSet.nodesUnder_eq_nodesIn]
  intro j' hj'
  obtain ⟨hidx, hle⟩ := (𝒰.mem_nodesIn_iff b _ j').mp hj'
  exact (𝒰.mem_nodesIn_iff b _ j').mpr ⟨hidx, hle.trans ((𝒰.cover.tube c j).le_rescale hr)⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **A node of a nonempty family carries at least one node of any finer level.**  Its class is
nonempty, and the level-`b` node of any member of that class lies under it. -/
private theorem card_nodesUnder_pos {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu) {c b : ℕ} (hcb : c ≤ b) (hb : b ≤ N) (hc : c ≤ N)
    (hs : s.Nonempty) {j : ι} (hj : j ∈ 𝒰.cover.indexSet c) :
    0 < (𝒰.nodesUnder b c j).card :=
  let ⟨i, hi⟩ := coverClass_nonempty_of_mem_parent 𝒰 hc hs hj
  Finset.card_pos.mpr ⟨𝒰.cover.assign b i, assign_mem_nodesUnder 𝒰 hcb hb hi⟩

end AncestorSplit

/-! ### Spreading a node-level lower bound to an arbitrary container

The third bullet of alternative (ii) asks for a *lower* bound on a Frostman constant at every
level-`b` node, dilated to an arbitrary real radius `ρ` of the window.  What the grid produces is a
lower bound at the level-`c` nodes, `c` the grid index of `ρ`.  Unlike `Kakeya.maxDensity`,
`ConvexSpaceBody.frostmanConstant` is *not* monotone in the index set, so enlarging the container
from `𝒰.cover.tube c p` to the `ρ`-dilate of a level-`b` node is not free: the chain estimate
`Kakeya.MultiScaleFac.card_mul_frostmanConstant_nodesIn_le` pays the ratio of the two node counts.
That ratio is bounded with no power of `δ`, by the ancestor split
(`Kakeya.MultiScaleFac.card_image_nodeAncestor_le`) followed by the comparability of node counts
across a level (`Kakeya.MultiScaleFac.card_nodesUnder_le_mul_card_nodesUnder`).  This is the
half-(A) substitute for the monotonicity that half (B) enjoys. -/

section Bullet3Core

variable {ι : Type*}

/-- **The `ρ_a`-tubes catching every member of a tube of arbitrary radius.**  The version of
`Kakeya.MultiScaleFac.exists_gridScale_cover_of_members_in_tube` in which the radius of the
container is not tied to `8 ρ_a`; the packing count of `exists_gapFibre_cover_of_ratio` then
displays the ratio `4r/ρ_a`, and it is the caller's business to bound it. -/
theorem exists_gridScale_cover_of_members_in_tube_ratio {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N a : ℕ} {r : NNReal} (hδ : 0 < δ) (h2δ : 2 * δ ≤ gridScale δ N a)
    (hr : gridScale δ N a ≤ 4 * r) (K : Tube r E) {i₀ : ι}
    (hi₀K : (T i₀).toConvexSpaceBody ≤ K.toConvexSpaceBody) :
    ∃ A ⊆ s,
      (A.card : ℝ) ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
          * (((4 * r : NNReal) : ℝ) / (gridScale δ N a : ℝ)) ^ (2 * Module.finrank ℝ E) ∧
      ∀ i ∈ s, (T i).toConvexSpaceBody ≤ K.toConvexSpaceBody →
        ∃ i₂ ∈ A, (T i).toConvexSpaceBody
          ≤ ((T i₂).rescale (gridScale δ N a)).toConvexSpaceBody := by
  classical
  have hK_le : K.toConvexSpaceBody ≤ ((T i₀).rescale (4 * r)).toConvexSpaceBody :=
    Tube.rescale_le_of_le (T i₀) K hi₀K
  obtain ⟨A, hA_sub, hA_card, hcover⟩ :=
    exists_gapFibre_cover_of_ratio (E := E) (ι := ι) (δ := δ) (σ := δ) (ρ := gridScale δ N a)
      (ρ' := 4 * r) (s := s) (T := T) (gridScale_pos hδ N a) le_rfl h2δ hr i₀
  refine ⟨A, hA_sub, hA_card, fun i hi_s hiK => ?_⟩
  obtain ⟨i2, hi2A, hi2fib⟩ := hcover i
    (by rw [fibreIndex_self]; exact Finset.mem_filter.mpr ⟨hi_s, hiK.trans hK_le⟩)
  rw [fibreIndex_self] at hi2fib
  exact ⟨i2, hi2A, (Finset.mem_filter.mp hi2fib).2⟩

/-- **Only boundedly many ancestors occur inside a container of arbitrary radius.**

`Kakeya.MultiScaleFac.card_image_nodeAncestor_le` with the radius constraint `r ≤ 8 ρ_a` removed and
the ratio `4r/ρ_a` displayed. -/
theorem card_image_nodeAncestor_le_ratio {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} [DecidableEq ι] (hδ : 0 < δ) (𝒰 : UniformTubeSet s T N C) {a b : ℕ}
    (ha : a ≤ N) (hb : b ≤ N) (hs : s.Nonempty) (h2δ : 2 * δ ≤ gridScale δ N a)
    {r : NNReal} (hr : gridScale δ N a ≤ 4 * r) (K : Tube r E) :
    (((𝒰.nodesIn b K.toConvexSpaceBody).image (𝒰.nodeAncestor b a)).card : ℝ)
      ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
          * (((4 * r : NNReal) : ℝ) / (gridScale δ N a : ℝ)) ^ (2 * Module.finrank ℝ E)
          * (C : ℝ) :=
  card_image_nodeAncestor_le_of_cover 𝒰 ha hb hs K (by positivity)
    fun _ hi₀K => exists_gridScale_cover_of_members_in_tube_ratio hδ h2δ hr K hi₀K

/-- **Nodes in a container of arbitrary radius versus nodes under one node of the level.**
`Kakeya.StickyKakeya.card_nodesIn_le_mul_card_nodesUnder` with the radius constraint removed.  The
displayed ratio `4r/ρ_c` is what the third bullet of alternative (ii) pays for reading a real scale
`ρ` of the window against the grid index just below `ρ/4`. -/
theorem card_nodesIn_le_mul_card_nodesUnder_ratio {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (hδ : 0 < δ) (𝒰 : UniformTubeSet s T N Cu)
    (hCu : 1 ≤ Cu) {c b : ℕ} (hc : c ≤ N) (hb : b ≤ N) (hcb : c ≤ b) (hs : s.Nonempty)
    (h2δ : 2 * δ ≤ gridScale δ N c) {r : NNReal} (hr : gridScale δ N c ≤ 4 * r) (K : Tube r E)
    {p : ι} (hp : p ∈ 𝒰.cover.indexSet c) :
    ((𝒰.nodesIn b K.toConvexSpaceBody).card : ℝ)
      ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
          * (((4 * r : NNReal) : ℝ) / (gridScale δ N c : ℝ)) ^ (2 * Module.finrank ℝ E)
          * (Cu : ℝ) * ((Cu : ℝ) ^ 5 * ((𝒰.nodesUnder b c p).card : ℝ)) := by
  classical
  set Anc : Finset ι := (𝒰.nodesIn b K.toConvexSpaceBody).image (𝒰.nodeAncestor b c)
  calc
    ((𝒰.nodesIn b K.toConvexSpaceBody).card : ℝ)
        ≤ ∑ j ∈ Anc, ((𝒰.nodesUnder b c j).card : ℝ) := by
          exact_mod_cast (Finset.card_le_card (nodesIn_subset_biUnion_nodesUnder (a := c) (b := b)
            𝒰 hcb hb hs K.toConvexSpaceBody)).trans Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Anc, ((Cu : ℝ) ^ 5 * ((𝒰.nodesUnder b c p).card : ℝ)) :=
        Finset.sum_le_sum fun j hj => by
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hj
          exact_mod_cast card_nodesUnder_le_mul_card_nodesUnder 𝒰 hCu hc hb hcb hs
            (𝒰.nodeAncestor_mem hc hb hs ((𝒰.mem_nodesIn_iff b K.toConvexSpaceBody w).mp hw).1) hp
    _ = (Anc.card : ℝ) * ((Cu : ℝ) ^ 5 * ((𝒰.nodesUnder b c p).card : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
          * (((4 * r : NNReal) : ℝ) / (gridScale δ N c : ℝ)) ^ (2 * Module.finrank ℝ E)
          * (Cu : ℝ) * ((Cu : ℝ) ^ 5 * ((𝒰.nodesUnder b c p).card : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (card_image_nodeAncestor_le_ratio (a := c) (b := b) hδ 𝒰 hc hb hs h2δ hr K)
          (mul_nonneg (pow_nonneg (NNReal.coe_nonneg Cu) 5) (Nat.cast_nonneg _))

/-- **A lower bound at a container transfers to a larger container, at the price of the node-count
ratio.**  The chain estimate `Kakeya.MultiScaleFac.card_mul_frostmanConstant_nodesIn_le` reads
`c_n |𝕋_b[K₁]| F₁ ≤ C_n |𝕋_b[K₂]| F₂`; cancelling the count of the smaller container leaves
`c_n F₁ ≤ C_n Λ F₂`.  The factor `c_n` is left on the left, keeping the statement division-free. -/
theorem leVolumeConst_mul_le_of_frostmanConstant_nodesIn {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {Cu : NNReal}
    (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu) {b : ℕ} {K₁ K₂ : ConvexSpaceBody E}
    (hK : K₁ ≤ K₂) {Λ : NNReal}
    (hcard : ((𝒰.nodesIn b K₂).card : ENNReal)
        ≤ (Λ : ENNReal) * ((𝒰.nodesIn b K₁).card : ENNReal))
    (hne : (𝒰.nodesIn b K₁).Nonempty) {X D : ENNReal}
    (hX : X ≤ D * ConvexSpaceBody.frostmanConstant (𝒰.nodesIn b K₁)
        (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody) K₁) :
    ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal) * X
      ≤ D * (((Tube.volume_le.C (Module.finrank ℝ E) * Λ : NNReal)) : ENNReal)
        * ConvexSpaceBody.frostmanConstant (𝒰.nodesIn b K₂)
            (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody) K₂ := by
  let F1 : ENNReal := ConvexSpaceBody.frostmanConstant (𝒰.nodesIn b K₁)
    (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody) K₁
  let F2 : ENNReal := ConvexSpaceBody.frostmanConstant (𝒰.nodesIn b K₂)
    (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody) K₂
  let cn : ENNReal := ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
  let Cn : ENNReal := ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
  let n1 : ENNReal := ((𝒰.nodesIn b K₁).card : ENNReal)
  let n2 : ENNReal := ((𝒰.nodesIn b K₂).card : ENNReal)
  have hc : cn * n1 * F1 ≤ Cn * n2 * F2 :=
    card_mul_frostmanConstant_nodesIn_le hδ hδ1 𝒰 hK
  have hn1_ne0 : n1 ≠ 0 := by
    dsimp [n1]; exact_mod_cast (Finset.card_pos.mpr hne).ne'
  have hcancel : cn * F1 ≤ Cn * (Λ : ENNReal) * F2 :=
    (ENNReal.mul_le_mul_iff_right hn1_ne0 (ENNReal.natCast_ne_top _)).mp <| by
      calc
        n1 * (cn * F1) = cn * n1 * F1 := by ring
        _ ≤ Cn * n2 * F2 := hc
        _ ≤ Cn * ((Λ : ENNReal) * n1) * F2 :=
          mul_le_mul_left (mul_le_mul_right hcard Cn) F2
        _ = n1 * (Cn * (Λ : ENNReal) * F2) := by ring
  rw [ENNReal.coe_mul]
  calc
    cn * X ≤ cn * (D * F1) := mul_le_mul_right hX cn
    _ = D * (cn * F1) := by ring
    _ ≤ D * (Cn * (Λ : ENNReal) * F2) := mul_le_mul_right hcancel D
    _ = D * (Cn * (Λ : ENNReal)) * F2 := by ring

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Cancelling the lower volume constant.**

`Tube.le_volume.c` is a strictly positive dimensional constant, so multiplying an `ENNReal`
inequality by it is reversible.  Isolated as a lemma because unfolding the constant inside a larger
proof makes `positivity` expand its definition. -/
theorem le_of_leVolumeConst_mul_le {X Y : ENNReal}
    (h : ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal) * X ≤ Y) :
    X ≤ (((Tube.le_volume.c (Module.finrank ℝ E))⁻¹ : NNReal) : ENNReal) * Y := by
  set cn : NNReal := Tube.le_volume.c (Module.finrank ℝ E)
  have hcn_ne : cn ≠ 0 := (Tube.le_volume.c_pos (Module.finrank ℝ E)).ne'
  calc X = ((cn⁻¹ : NNReal) : ENNReal) * ((cn : ENNReal) * X) := by
        rw [← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hcn_ne, ENNReal.coe_one, one_mul]
    _ ≤ ((cn⁻¹ : NNReal) : ENNReal) * Y := mul_le_mul_right h _

/-- **The node count inside a real dilate, against one node of the rounding level, in `ℝ≥0∞`.**
`Kakeya.MultiScaleFac.card_nodesIn_le_mul_card_nodesUnder_ratio` read at the container
`(𝒰.cover.tube b j).rescale ρ`, with the numeric prefactor absorbed into `Λ` and the conclusion
moved from `ℝ` to `ℝ≥0∞`. -/
theorem card_nodesIn_rescale_le_of_ancestor {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {Cu : NNReal} (hδ : 0 < δ)
    (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu) (hCu : 1 ≤ Cu) (hs : s.Nonempty)
    {c b : ℕ} (hc : c ≤ ssfGridLen δ) (hb : b ≤ ssfGridLen δ) (hcb : c ≤ b)
    (h2δ : 2 * δ ≤ gridScale δ (ssfGridLen δ) c)
    {ρ : NNReal} (hρ : 4 * gridScale δ (ssfGridLen δ) c ≤ ρ)
    {Λ : NNReal}
    (hΛ : 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
          * (((4 * ρ : NNReal) : ℝ)
              / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ (2 * Module.finrank ℝ E)
          * (Cu : ℝ) * ((Cu : ℝ) ^ 5) ≤ (Λ : ℝ))
    {j p : ι} (hp : p ∈ 𝒰.cover.indexSet c) :
    ((𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody).card : ENNReal)
      ≤ (Λ : ENNReal) * ((𝒰.nodesUnder b c p).card : ENNReal) := by
  classical
  letI : ProperSpace E := FiniteDimensional.proper_real E
  have hr : gridScale δ (ssfGridLen δ) c ≤ 4 * ρ :=
    (le_mul_of_one_le_left zero_le (by norm_num : (1 : NNReal) ≤ 4)).trans
      (hρ.trans (le_mul_of_one_le_left zero_le (by norm_num : (1 : NNReal) ≤ 4)))
  have hreal : ((𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody).card : ℝ)
      ≤ (Λ : ℝ) * ((𝒰.nodesUnder b c p).card : ℝ) := by
    calc
      ((𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody).card : ℝ)
          ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
              * (((4 * ρ : NNReal) : ℝ)
                  / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ (2 * Module.finrank ℝ E)
              * (Cu : ℝ) * ((Cu : ℝ) ^ 5 * ((𝒰.nodesUnder b c p).card : ℝ)) :=
            card_nodesIn_le_mul_card_nodesUnder_ratio (N := ssfGridLen δ) (r := ρ)
              (K := (𝒰.cover.tube b j).rescale ρ) hδ 𝒰 hCu hc hb hcb hs h2δ hr hp
      _ = (2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
              * (((4 * ρ : NNReal) : ℝ)
                  / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ (2 * Module.finrank ℝ E)
              * (Cu : ℝ) * ((Cu : ℝ) ^ 5)) * ((𝒰.nodesUnder b c p).card : ℝ) := by
            ring
      _ ≤ (Λ : ℝ) * ((𝒰.nodesUnder b c p).card : ℝ) :=
            mul_le_mul_of_nonneg_right hΛ (Nat.cast_nonneg _)
  have hnn : ((𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody).card : NNReal) ≤
      Λ * ((𝒰.nodesUnder b c p).card : NNReal) := NNReal.coe_le_coe.mpr hreal
  simpa [ENNReal.coe_mul, ENNReal.coe_natCast] using (ENNReal.coe_le_coe.mpr hnn)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The `8 ρ_c`-dilate of a coarse node sits inside the `ρ`-dilate of any of its fine nodes, once
`32 ρ_c ≤ ρ`.**  The `Kakeya.StickyKakeya.tube_le_rescale_of_tube_le` step with the coarse node
replaced by its `8 ρ_c`-dilate, which `Tube.rescale_le_of_le` inflates to `4 * (8 ρ_c) = 32 ρ_c`
around the fine node; this is the sole source of the raised window. -/
theorem tube_rescale_le_rescale_of_tube_le {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu) {c b : ℕ} {j p : ι}
    (hjp : (𝒰.cover.tube b j).toConvexSpaceBody ≤ (𝒰.cover.tube c p).toConvexSpaceBody)
    {ρ : NNReal} (hρ : 32 * gridScale δ N c ≤ ρ) :
    ((𝒰.cover.tube c p).rescale (8 * gridScale δ N c)).toConvexSpaceBody
      ≤ ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody := by
  letI : ProperSpace E := FiniteDimensional.proper_real E
  refine (Tube.rescale_le_of_le (𝒰.cover.tube b j) _ (hjp.trans (Tube.le_rescale _
      (le_mul_of_one_le_left zero_le (by norm_num : (1 : NNReal) ≤ 8))))).trans
    (Tube.rescale_le_rescale_of_radius_le (𝒰.cover.tube b j) ?_)
  rwa [show 4 * (8 * gridScale δ N c) = 32 * gridScale δ N c by ring]

/-- **The node count inside a real dilate, against the nodes of the `8 ρ_c`-dilated rounding node.**

`Kakeya.MultiScaleFac.card_nodesIn_rescale_le_of_ancestor` with the reference family enlarged from
the nodes under `p` to the nodes inside the `8 ρ_c`-dilate of `p`, which only helps: the node family
is monotone in its container. -/
theorem card_nodesIn_rescale_le_of_ancestor_dilate {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {Cu : NNReal} (hδ : 0 < δ)
    (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu) (hCu : 1 ≤ Cu) (hs : s.Nonempty)
    {c b : ℕ} (hc : c ≤ ssfGridLen δ) (hb : b ≤ ssfGridLen δ) (hcb : c ≤ b)
    (h2δ : 2 * δ ≤ gridScale δ (ssfGridLen δ) c)
    {ρ : NNReal} (hρ : 32 * gridScale δ (ssfGridLen δ) c ≤ ρ)
    {Λ : NNReal}
    (hΛ : 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
          * (((4 * ρ : NNReal) : ℝ)
              / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ (2 * Module.finrank ℝ E)
          * (Cu : ℝ) * ((Cu : ℝ) ^ 5) ≤ (Λ : ℝ))
    {j p : ι} (hp : p ∈ 𝒰.cover.indexSet c) :
    ((𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody).card : ENNReal)
      ≤ (Λ : ENNReal) * ((𝒰.nodesIn b (((𝒰.cover.tube c p).rescale
          (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody)).card : ENNReal) := by
  have hρ4 : 4 * gridScale δ (ssfGridLen δ) c ≤ ρ :=
    (mul_le_mul_left (by norm_num : (4 : NNReal) ≤ 32) _).trans hρ
  have h3 : ((𝒰.nodesUnder b c p).card : ENNReal) ≤
      ((𝒰.nodesIn b (((𝒰.cover.tube c p).rescale
        (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody)).card : ENNReal) :=
    Nat.cast_le.mpr (Finset.card_le_card (nodesUnder_subset_nodesIn_rescale 𝒰 p
      (le_mul_of_one_le_left zero_le (by norm_num : (1 : NNReal) ≤ 8))))
  exact (card_nodesIn_rescale_le_of_ancestor hδ 𝒰 hCu hs hc hb hcb h2δ hρ4 hΛ hp).trans
    (mul_le_mul_right h3 (Λ : ENNReal))

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The nodes inside the `8 ρ_c`-dilate of a node of level `c` are nonempty.**

`Kakeya.MultiScaleFac.card_nodesUnder_pos` transported along the inclusion of the node into its
dilate.  Isolated because it is the one nonemptiness side condition of
`Kakeya.MultiScaleFac.leVolumeConst_mul_le_of_frostmanConstant_nodesIn` at the dilated container. -/
theorem nodesIn_rescale_nonempty {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {Cu : NNReal} (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu) (hs : s.Nonempty)
    {c b : ℕ} (hc : c ≤ ssfGridLen δ) (hb : b ≤ ssfGridLen δ) (hcb : c ≤ b)
    {p : ι} (hp : p ∈ 𝒰.cover.indexSet c) :
    (𝒰.nodesIn b (((𝒰.cover.tube c p).rescale
      (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody)).Nonempty :=
  Finset.Nonempty.mono (nodesUnder_subset_nodesIn_rescale 𝒰 p
    (le_mul_of_one_le_left zero_le (by norm_num : (1 : NNReal) ≤ 8)))
    (Finset.card_pos.mp (card_nodesUnder_pos 𝒰 hcb hb hc hs hp))

/-- **The same reduction, with the hypothesis read on the `8 ρ_c`-dilates.**
`Kakeya.StickyKakeya.le_frostmanConstant_nodesIn_rescale_of_grid` in the form the stopping time can
actually feed: the leaf-anchored lower bound reaches the nodes on the `8 ρ_c`-dilate of a level-`c`
node, so asking for the hypothesis there saves a container change, at the cost of raising the
admissible window from `4 ρ_c ≤ ρ` to `32 ρ_c ≤ ρ`. -/
theorem le_frostmanConstant_nodesIn_rescale_of_grid_dilate {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {Cu : NNReal}
    (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu) (hCu : 1 ≤ Cu) (hs : s.Nonempty)
    {c b : ℕ} (hc : c ≤ ssfGridLen δ) (hb : b ≤ ssfGridLen δ) (hcb : c ≤ b)
    (h2δ : 2 * δ ≤ gridScale δ (ssfGridLen δ) c)
    {ρ : NNReal} (hρ : 32 * gridScale δ (ssfGridLen δ) c ≤ ρ)
    {Λ : NNReal}
    (hΛ : 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
          * (((4 * ρ : NNReal) : ℝ)
              / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ (2 * Module.finrank ℝ E)
          * (Cu : ℝ) * ((Cu : ℝ) ^ 5) ≤ (Λ : ℝ))
    {X D : ENNReal}
    (hgrid : ∀ p ∈ 𝒰.cover.indexSet c, X ≤ D * ConvexSpaceBody.frostmanConstant
        (𝒰.nodesIn b (((𝒰.cover.tube c p).rescale
            (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody))
        (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
        (((𝒰.cover.tube c p).rescale
            (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody))
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet b) :
    X ≤ (((Tube.le_volume.c (Module.finrank ℝ E))⁻¹ : NNReal) : ENNReal)
        * (D * (((Tube.volume_le.C (Module.finrank ℝ E) * Λ : NNReal)) : ENNReal)
          * ConvexSpaceBody.frostmanConstant
              (𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody)
              (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
              ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody) := by
  have hqmem : 𝒰.nodeAncestor b c j ∈ 𝒰.cover.indexSet c :=
    𝒰.nodeAncestor_mem (a := c) hc hb hs hj
  exact le_of_leVolumeConst_mul_le (leVolumeConst_mul_le_of_frostmanConstant_nodesIn hδ hδ1 𝒰
    (tube_rescale_le_rescale_of_tube_le 𝒰 (𝒰.tube_le_tube_nodeAncestor (a := c) hcb hb hs hj) hρ)
    (card_nodesIn_rescale_le_of_ancestor_dilate (p := 𝒰.nodeAncestor b c j) (j := j)
      hδ 𝒰 hCu hs hc hb hcb h2δ hρ hΛ hqmem)
    (nodesIn_rescale_nonempty (p := 𝒰.nodeAncestor b c j) 𝒰 hs hc hb hcb hqmem)
    (hgrid (𝒰.nodeAncestor b c j) hqmem))

end Bullet3Core

/-- **The upper density constant of a dilated node**, a function of the ambient dimension `n`
alone.  It is the ratio of the maximal tube volume constant to the minimal tube volume constant,
discounted by the `8 ^ (n - 1)` gained from passing to the `8ρ_c`-dilate. -/
noncomputable def nodeDensityUBConst (n : ℕ) : NNReal :=
  Tube.volume_le.C n / (Tube.le_volume.c n * 8 ^ (n - 1))

/-- **The lower density constant of a dilated node**, the mirror image of
`Kakeya.MultiScaleFac.nodeDensityUBConst`: the ratio of the minimal tube volume constant to the
maximal one, again discounted by `8 ^ (n - 1)`. -/
noncomputable def nodeDensityLBConst (n : ℕ) : NNReal :=
  Tube.le_volume.c n / (Tube.volume_le.C n * 8 ^ (n - 1))

/-- The minimal volume of a rescaled tube, in the `ConvexSpaceBody` packaging used by the density
API. -/
theorem le_volume_rescale_toConvexSpaceBody {r : NNReal} (T : Tube r E) (ρ : NNReal) :
    ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
        * (ρ : ENNReal) ^ (Module.finrank ℝ E - 1)
      ≤ volume (T.rescale ρ).toConvexSpaceBody.carrier :=
  Tube.le_volume (T.rescale ρ)

/-- The maximal volume of a rescaled tube, in the `ConvexSpaceBody` packaging used by the density
API. -/
theorem volume_rescale_toConvexSpaceBody_le {r : NNReal} (T : Tube r E) {ρ : NNReal}
    (hρ : ρ ≤ 1) :
    volume (T.rescale ρ).toConvexSpaceBody.carrier
      ≤ ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
        * (ρ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
  Tube.volume_le hρ (T.rescale ρ)

/-- **The algebraic core of the upper density bound.** -- (extracted by Fuse golfer)

Cancelling the volume `V` of the container from `d * V ≤ C (Cv ρ_c ^ p)` against the lower volume
estimate `c · 8 ^ p · ρ_c ^ p ≤ V`.  Purely a computation in `ℝ≥0∞`, with no geometry. -/
private theorem density_le_of_volume_bounds {cn Cn Cv sc : NNReal} {p : ℕ} {d V : ENNReal}
    (hcn : cn ≠ 0) (hsc : sc ≠ 0)
    (hd : d * V ≤ (Cn : ENNReal) * ((Cv : ENNReal) * (sc : ENNReal) ^ p))
    (hV : ((cn * 8 ^ p * sc ^ p : NNReal) : ENNReal) ≤ V) :
    d ≤ ((Cn / (cn * 8 ^ p) * Cv : NNReal) : ENNReal) := by
  have hden : cn * 8 ^ p ≠ 0 := mul_ne_zero hcn (pow_ne_zero p (by norm_num))
  have hid : cn * 8 ^ p * sc ^ p * (Cn / (cn * 8 ^ p) * Cv) = Cn * (Cv * sc ^ p) := by
    rw [show cn * 8 ^ p * sc ^ p * (Cn / (cn * 8 ^ p) * Cv)
        = Cn / (cn * 8 ^ p) * (cn * 8 ^ p) * (Cv * sc ^ p) by ring, div_mul_cancel₀ _ hden]
  refine (ENNReal.mul_le_mul_iff_right
    (ENNReal.coe_ne_zero.mpr (mul_ne_zero hden (pow_ne_zero p hsc))) ENNReal.coe_ne_top).mp ?_
  calc ((cn * 8 ^ p * sc ^ p : NNReal) : ENNReal) * d
      ≤ d * V := by rw [mul_comm d V]; exact mul_le_mul_left hV d
    _ ≤ (Cn : ENNReal) * ((Cv : ENNReal) * (sc : ENNReal) ^ p) := hd
    _ = ((cn * 8 ^ p * sc ^ p : NNReal) : ENNReal)
          * ((Cn / (cn * 8 ^ p) * Cv : NNReal) : ENNReal) := by
        rw [← ENNReal.coe_mul, hid]; push_cast; ring

/-- **The algebraic core of the lower density bound.** -- (extracted by Fuse golfer)

The mirror of `density_le_of_volume_bounds`: the two volume estimates are exchanged. -/
private theorem le_density_of_volume_bounds {cn Cn Cv sc : NNReal} {p : ℕ} {d V : ENNReal}
    (hCn : Cn ≠ 0) (hsc : sc ≠ 0)
    (hd : (cn : ENNReal) * ((Cv : ENNReal) * (sc : ENNReal) ^ p) ≤ d * V)
    (hV : V ≤ ((Cn * 8 ^ p * sc ^ p : NNReal) : ENNReal)) :
    ((cn / (Cn * 8 ^ p) * Cv : NNReal) : ENNReal) ≤ d := by
  have hden : Cn * 8 ^ p ≠ 0 := mul_ne_zero hCn (pow_ne_zero p (by norm_num))
  have hid : Cn * 8 ^ p * sc ^ p * (cn / (Cn * 8 ^ p) * Cv) = cn * (Cv * sc ^ p) := by
    rw [show Cn * 8 ^ p * sc ^ p * (cn / (Cn * 8 ^ p) * Cv)
        = cn / (Cn * 8 ^ p) * (Cn * 8 ^ p) * (Cv * sc ^ p) by ring, div_mul_cancel₀ _ hden]
  refine (ENNReal.mul_le_mul_iff_right
    (ENNReal.coe_ne_zero.mpr (mul_ne_zero hden (pow_ne_zero p hsc))) ENNReal.coe_ne_top).mp ?_
  calc ((Cn * 8 ^ p * sc ^ p : NNReal) : ENNReal)
        * ((cn / (Cn * 8 ^ p) * Cv : NNReal) : ENNReal)
      = (cn : ENNReal) * ((Cv : ENNReal) * (sc : ENNReal) ^ p) := by
        rw [← ENNReal.coe_mul, hid]; push_cast; ring
    _ ≤ d * V := hd
    _ ≤ d * ((Cn * 8 ^ p * sc ^ p : NNReal) : ENNReal) := mul_le_mul_right hV d
    _ = ((Cn * 8 ^ p * sc ^ p : NNReal) : ENNReal) * d := mul_comm _ _

open scoped Classical in
/-- **The level-`b` nodes of an `8ρ_c`-dilate have bounded density in that dilate.**  The hypothesis
`hcard` is the counting form of bounded overlap of the hierarchy: the number of level-`b` nodes in
the dilate, weighted by `ρ_b ^ (n - 1)`, is at most `Cv · ρ_c ^ (n - 1)`.  The conclusion converts
this into a density bound with constant `nodeDensityUBConst n * Cv` and no power of `δ`. -/
theorem densityIn_nodesIn_rescale_eight_le {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (𝒰 : UniformTubeSet s T N Cu)
    {c b : ℕ} {q : ι} {Cv : NNReal}
    (hcard : ((𝒰.nodesIn b (((𝒰.cover.tube c q).rescale
          (8 * gridScale δ N c)).toConvexSpaceBody)).card : ENNReal)
        * ((gridScale δ N b : ENNReal) ^ (Module.finrank ℝ E - 1))
      ≤ (Cv : ENNReal) * ((gridScale δ N c : ENNReal) ^ (Module.finrank ℝ E - 1))) :
    Kakeya.densityIn
        (𝒰.nodesIn b (((𝒰.cover.tube c q).rescale (8 * gridScale δ N c)).toConvexSpaceBody))
        (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
        (((𝒰.cover.tube c q).rescale (8 * gridScale δ N c)).toConvexSpaceBody)
      ≤ ((nodeDensityUBConst (Module.finrank ℝ E) * Cv : NNReal) : ENNReal) := by
  set n : ℕ := Module.finrank ℝ E with hn
  set p : ℕ := n - 1 with hp
  set cn : NNReal := Tube.le_volume.c n with hcn
  set Cn : NNReal := Tube.volume_le.C n with hCn
  set sc : NNReal := gridScale δ N c with hsc
  set sb : NNReal := gridScale δ N b with hsb
  set K : ConvexSpaceBody E := ((𝒰.cover.tube c q).rescale (8 * sc)).toConvexSpaceBody with hK
  set W : ι → ConvexSpaceBody E := fun j' => (𝒰.cover.tube b j').toConvexSpaceBody with hW
  set nds : Finset ι := 𝒰.nodesIn b K with hnds
  rw [nodeDensityUBConst]
  refine density_le_of_volume_bounds (Tube.le_volume.c_pos n).ne' (gridScale_pos hδ N c).ne'
    (V := volume K.carrier) ?_ ?_
  · calc Kakeya.densityIn nds W K * volume K.carrier
        ≤ (nds.card : ENNReal) * ((Cn : ENNReal) * (sb : ENNReal) ^ p) :=
          densityIn_mul_volume_le_card_mul K fun i _ => by
            rw [show (Cn : ENNReal) * (sb : ENNReal) ^ p = ((Cn * sb ^ p : NNReal) : ENNReal) by
              push_cast; ring]
            exact Tube.volume_le (gridScale_le_one hδ1 N b) (𝒰.cover.tube b i)
      _ = (Cn : ENNReal) * ((nds.card : ENNReal) * (sb : ENNReal) ^ p) := by ring
      _ ≤ (Cn : ENNReal) * ((Cv : ENNReal) * (sc : ENNReal) ^ p) :=
          mul_le_mul_right hcard (Cn : ENNReal)
  · rw [show ((cn * 8 ^ p * sc ^ p : NNReal) : ENNReal)
        = (cn : ENNReal) * ((8 * sc : NNReal) : ENNReal) ^ p by push_cast; ring]
    exact le_volume_rescale_toConvexSpaceBody (𝒰.cover.tube c q) (8 * sc)

open scoped Classical in
/-- **The count of level-`b` nodes inside a rescaled tube, against their density in it.**

The level-`b` nodes of a container lie inside it by definition of `nodesIn`, so their count
weighted by the minimal `ρ_b`-tube volume is at most their density weighted by the volume of the
container.  This is the container-generic engine of the lower bound below. -/
theorem card_nodesIn_rescale_mul_le_densityIn_mul_volume {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu) (b : ℕ)
    {r : NNReal} (T₀ : Tube r E) {ρ : NNReal} (hρ : 0 < ρ) :
    ((𝒰.nodesIn b ((T₀.rescale ρ).toConvexSpaceBody)).card : ENNReal)
        * (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
          * ((gridScale δ N b : ENNReal) ^ (Module.finrank ℝ E - 1)))
      ≤ Kakeya.densityIn (𝒰.nodesIn b ((T₀.rescale ρ).toConvexSpaceBody))
            (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
            ((T₀.rescale ρ).toConvexSpaceBody)
          * volume ((T₀.rescale ρ).toConvexSpaceBody).carrier := by
  let n : ℕ := Module.finrank ℝ E
  let p : ℕ := n - 1
  let cn : NNReal := Tube.le_volume.c n
  let K : ConvexSpaceBody E := (T₀.rescale ρ).toConvexSpaceBody
  let W : ι → ConvexSpaceBody E := fun j' => (𝒰.cover.tube b j').toConvexSpaceBody
  let nds : Finset ι := 𝒰.nodesIn b K
  have hge := densityIn_ge_of_count_volume (s := nds) (W := W) (K := K)
    (Finset.Subset.refl nds) (fun j' hj' => ((𝒰.mem_nodesIn_iff b K j').mp hj').2)
    (fun j' _ => by
      simpa only [ENNReal.coe_mul, ENNReal.coe_pow] using Tube.le_volume (𝒰.cover.tube b j'))
  have hvol_lb : ((cn * ρ ^ p : NNReal) : ENNReal) ≤ volume K.carrier := by
    simpa only [ENNReal.coe_mul, ENNReal.coe_pow] using le_volume_rescale_toConvexSpaceBody T₀ ρ
  rwa [ENNReal.div_le_iff
    ((ENNReal.coe_pos.mpr (mul_pos (Tube.le_volume.c_pos n) (pow_pos hρ p))).trans_le hvol_lb).ne'
    K.isCompact.measure_ne_top] at hge

open scoped Classical in
/-- **The mirrored lower bound on the density of the level-`b` nodes of an `8ρ_c`-dilate.**  Same
shape as `Kakeya.MultiScaleFac.densityIn_nodesIn_rescale_eight_le` with the two volume estimates
exchanged: the hypothesis is now a lower bound on the weighted count, and the constant
`nodeDensityLBConst n * Cv` again carries no power of `δ`. -/
theorem le_densityIn_nodesIn_rescale_eight {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (hδ : 0 < δ) (_hδ1 : δ ≤ 1) (𝒰 : UniformTubeSet s T N Cu)
    {c b : ℕ} {q : ι} {Cv : NNReal} (h8 : 8 * gridScale δ N c ≤ 1)
    (hcard : (Cv : ENNReal) * ((gridScale δ N c : ENNReal) ^ (Module.finrank ℝ E - 1))
      ≤ ((𝒰.nodesIn b (((𝒰.cover.tube c q).rescale
          (8 * gridScale δ N c)).toConvexSpaceBody)).card : ENNReal)
        * ((gridScale δ N b : ENNReal) ^ (Module.finrank ℝ E - 1))) :
    ((nodeDensityLBConst (Module.finrank ℝ E) * Cv : NNReal) : ENNReal)
      ≤ Kakeya.densityIn
          (𝒰.nodesIn b (((𝒰.cover.tube c q).rescale (8 * gridScale δ N c)).toConvexSpaceBody))
          (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
          (((𝒰.cover.tube c q).rescale (8 * gridScale δ N c)).toConvexSpaceBody) := by
  set n : ℕ := Module.finrank ℝ E with hn
  set p : ℕ := n - 1 with hp
  set cn : NNReal := Tube.le_volume.c n with hcn
  set Cn : NNReal := Tube.volume_le.C n with hCn
  set sc : NNReal := gridScale δ N c with hsc
  set sb : NNReal := gridScale δ N b with hsb
  set K : ConvexSpaceBody E := ((𝒰.cover.tube c q).rescale (8 * sc)).toConvexSpaceBody with hK
  set W : ι → ConvexSpaceBody E := fun j' => (𝒰.cover.tube b j').toConvexSpaceBody with hW
  set nds : Finset ι := 𝒰.nodesIn b K with hnds
  have hsc_pos : 0 < sc := gridScale_pos hδ N c
  have hCn_pos : 0 < Cn := by simp [Cn, Tube.volume_le.C]
  rw [nodeDensityLBConst]
  refine le_density_of_volume_bounds hCn_pos.ne' hsc_pos.ne' (V := volume K.carrier) ?_ ?_
  · calc (cn : ENNReal) * ((Cv : ENNReal) * (sc : ENNReal) ^ p)
        ≤ (cn : ENNReal) * ((nds.card : ENNReal) * (sb : ENNReal) ^ p) :=
          mul_le_mul_right hcard (cn : ENNReal)
      _ = (nds.card : ENNReal) * ((cn : ENNReal) * (sb : ENNReal) ^ p) := by ring
      _ ≤ Kakeya.densityIn nds W K * volume K.carrier :=
          card_nodesIn_rescale_mul_le_densityIn_mul_volume (𝒰 := 𝒰) (b := b)
            (T₀ := 𝒰.cover.tube c q) (ρ := 8 * sc)
            (hρ := mul_pos (by norm_num : (0 : NNReal) < 8) hsc_pos)
  · rw [show ((Cn * 8 ^ p * sc ^ p : NNReal) : ENNReal)
        = (Cn : ENNReal) * ((8 * sc : NNReal) : ENNReal) ^ p by push_cast; ring]
    exact volume_rescale_toConvexSpaceBody_le (𝒰.cover.tube c q) (by simpa [sc] using h8)

/-! ### Discharging the counting hypothesis from the hierarchy

The hypothesis `hcard` of the two bounds above is a comparison of a *weighted node count* with a
power of the coarse scale.  It splits into two genuinely different pieces:

* a **node count in branching form** — how many level-`b` nodes sit in the `8ρ_c`-dilate, measured
  against the branching numbers `N_{ρ_b}`, `N_{ρ_c}` of the bundle;
* a **branching-versus-scale comparison** — how `N_{ρ_c} / N_{ρ_b}` compares with
  `(ρ_c / ρ_b) ^ (n - 1)`.

Neither piece involves a power of `δ`.  The first piece is available from the bundle itself on the
*lower* side, where `Kakeya.MultiScaleFac.branchingN_le_mul_card_nodesUnder` is exactly the needed
count; on the upper side it is the ancestor-splitting count and is left as a hypothesis, since the
machinery that produces it (`nodeAncestor` and the ancestor union bound) lives strictly downstream
of this file.  The second piece is a hypothesis on both sides: it is a property of the pair
`(branchingN, gridScale)` of the bundle and nothing in `UniformTubeSet` constrains it. -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
open scoped Classical in
/-- **The level-`b` nodes of the `8ρ_c`-dilate of a level-`c` node are at least
`N_{ρ_c} / (C_u ^ 2 · N_{ρ_b})` many.**  The dilate contains the node itself (`Tube.le_rescale`),
hence every level-`b` node under it, and `branchingN_le_mul_card_nodesUnder` counts those.  No
volume and no power of `δ` enter. -/
theorem branchingN_le_mul_card_nodesIn_rescale_eight {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu) {c b : ℕ}
    (hcb : c ≤ b) (hb : b ≤ N) (hc : c ≤ N) {q : ι} (hq : q ∈ 𝒰.cover.indexSet c) :
    𝒰.branchingN c ≤ (Cu ^ 2 * 𝒰.branchingN b)
      * (((𝒰.nodesIn b (((𝒰.cover.tube c q).rescale
          (8 * gridScale δ N c)).toConvexSpaceBody)).card : NNReal)) := by
  have hcard : ((𝒰.nodesUnder b c q).card : NNReal) ≤
      ((𝒰.nodesIn b (((𝒰.cover.tube c q).rescale
        (8 * gridScale δ N c)).toConvexSpaceBody)).card : NNReal) :=
    Nat.cast_le.mpr (Finset.card_le_card (nodesUnder_subset_nodesIn_rescale 𝒰 q
      (le_mul_of_one_le_left zero_le (by norm_num : (1 : NNReal) ≤ 8))))
  calc
    𝒰.branchingN c ≤ Cu ^ 2 * (((𝒰.nodesUnder b c q).card : NNReal) * 𝒰.branchingN b) :=
      branchingN_le_mul_card_nodesUnder 𝒰 hcb hb hc hq
    _ = (Cu ^ 2 * 𝒰.branchingN b) * ((𝒰.nodesUnder b c q).card : NNReal) := by ring
    _ ≤ _ := mul_le_mul_right hcard (Cu ^ 2 * 𝒰.branchingN b)

open scoped Classical in
/-- **The lower density bound with the counting hypothesis discharged from the hierarchy.**  Same
conclusion as `Kakeya.MultiScaleFac.le_densityIn_nodesIn_rescale_eight`, but `hcard` is replaced by
`hscale`, a comparison between the branching numbers of the bundle and the grid scales; the node
count comes from `branchingN_le_mul_card_nodesIn_rescale_eight`, and no power of `δ` appears. -/
theorem le_densityIn_nodesIn_rescale_eight_of_branchingN {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (𝒰 : UniformTubeSet s T N Cu) {c b : ℕ} {q : ι} {Cv : NNReal}
    (h8 : 8 * gridScale δ N c ≤ 1) (hcb : c ≤ b) (hb : b ≤ N) (hc : c ≤ N)
    (hq : q ∈ 𝒰.cover.indexSet c) (hCu : 0 < Cu) (hbr : 0 < 𝒰.branchingN b)
    (hscale : (Cv : ENNReal) * ((Cu ^ 2 * 𝒰.branchingN b : NNReal) : ENNReal)
          * ((gridScale δ N c : ENNReal) ^ (Module.finrank ℝ E - 1))
        ≤ ((𝒰.branchingN c : NNReal) : ENNReal)
          * ((gridScale δ N b : ENNReal) ^ (Module.finrank ℝ E - 1))) :
    ((nodeDensityLBConst (Module.finrank ℝ E) * Cv : NNReal) : ENNReal)
      ≤ Kakeya.densityIn
          (𝒰.nodesIn b (((𝒰.cover.tube c q).rescale (8 * gridScale δ N c)).toConvexSpaceBody))
          (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
          (((𝒰.cover.tube c q).rescale (8 * gridScale δ N c)).toConvexSpaceBody) := by
  set nds : Finset ι :=
    𝒰.nodesIn b (((𝒰.cover.tube c q).rescale (8 * gridScale δ N c)).toConvexSpaceBody) with hnds
  set p : ℕ := Module.finrank ℝ E - 1 with hp
  have hM0 : ((Cu ^ 2 * 𝒰.branchingN b : NNReal) : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (mul_pos (pow_pos hCu 2) hbr).ne'
  refine le_densityIn_nodesIn_rescale_eight hδ hδ1 𝒰 h8
    ((ENNReal.mul_le_mul_iff_right hM0 ENNReal.coe_ne_top).mp ?_)
  calc ((Cu ^ 2 * 𝒰.branchingN b : NNReal) : ENNReal)
        * ((Cv : ENNReal) * (gridScale δ N c : ENNReal) ^ p)
      = (Cv : ENNReal) * ((Cu ^ 2 * 𝒰.branchingN b : NNReal) : ENNReal)
        * (gridScale δ N c : ENNReal) ^ p := by ring
    _ ≤ ((𝒰.branchingN c : NNReal) : ENNReal) * (gridScale δ N b : ENNReal) ^ p := hscale
    _ ≤ ((Cu ^ 2 * 𝒰.branchingN b : NNReal) : ENNReal) * (nds.card : ENNReal)
        * (gridScale δ N b : ENNReal) ^ p :=
        mul_le_mul_left
          (by exact_mod_cast branchingN_le_mul_card_nodesIn_rescale_eight 𝒰 hcb hb hc hq) _
    _ = ((Cu ^ 2 * 𝒰.branchingN b : NNReal) : ENNReal)
        * ((nds.card : ENNReal) * (gridScale δ N b : ENNReal) ^ p) := by ring

open scoped Classical in
/-- **The upper density bound with the counting hypothesis put in branching form.**  Same conclusion
as `Kakeya.MultiScaleFac.densityIn_nodesIn_rescale_eight_le`, with `hcard` replaced by two
separately available pieces: `hcount`, a bound on the number of level-`b` nodes in the dilate
against the branching numbers, and `hscale`, the branching-versus-scale comparison. -/
theorem densityIn_nodesIn_rescale_eight_le_of_card_mul_branchingN {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (𝒰 : UniformTubeSet s T N Cu) {c b : ℕ} {q : ι} {Cv Cw : NNReal}
    (hbr : 0 < 𝒰.branchingN b)
    (hcount : (((𝒰.nodesIn b (((𝒰.cover.tube c q).rescale
            (8 * gridScale δ N c)).toConvexSpaceBody)).card : NNReal)) * 𝒰.branchingN b
        ≤ Cw * 𝒰.branchingN c)
    (hscale : (Cw : ENNReal) * ((𝒰.branchingN c : NNReal) : ENNReal)
          * ((gridScale δ N b : ENNReal) ^ (Module.finrank ℝ E - 1))
        ≤ (Cv : ENNReal) * ((𝒰.branchingN b : NNReal) : ENNReal)
          * ((gridScale δ N c : ENNReal) ^ (Module.finrank ℝ E - 1))) :
    Kakeya.densityIn
        (𝒰.nodesIn b (((𝒰.cover.tube c q).rescale (8 * gridScale δ N c)).toConvexSpaceBody))
        (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
        (((𝒰.cover.tube c q).rescale (8 * gridScale δ N c)).toConvexSpaceBody)
      ≤ ((nodeDensityUBConst (Module.finrank ℝ E) * Cv : NNReal) : ENNReal) := by
  set nds : Finset ι :=
    𝒰.nodesIn b (((𝒰.cover.tube c q).rescale (8 * gridScale δ N c)).toConvexSpaceBody) with hnds
  set p : ℕ := Module.finrank ℝ E - 1 with hp
  refine densityIn_nodesIn_rescale_eight_le hδ hδ1 𝒰
    ((ENNReal.mul_le_mul_iff_right (by exact_mod_cast hbr.ne' :
      ((𝒰.branchingN b : NNReal) : ENNReal) ≠ 0) ENNReal.coe_ne_top).mp ?_)
  calc ((𝒰.branchingN b : NNReal) : ENNReal)
        * ((nds.card : ENNReal) * (gridScale δ N b : ENNReal) ^ p)
      = (nds.card : ENNReal) * ((𝒰.branchingN b : NNReal) : ENNReal)
        * (gridScale δ N b : ENNReal) ^ p := by ring
    _ ≤ (Cw : ENNReal) * ((𝒰.branchingN c : NNReal) : ENNReal)
        * (gridScale δ N b : ENNReal) ^ p := mul_le_mul_left (by exact_mod_cast hcount) _
    _ ≤ (Cv : ENNReal) * ((𝒰.branchingN b : NNReal) : ENNReal)
        * (gridScale δ N c : ENNReal) ^ p := hscale
    _ = ((𝒰.branchingN b : NNReal) : ENNReal)
        * ((Cv : ENNReal) * (gridScale δ N c : ENNReal) ^ p) := by ring

/-! ### Discharging `hcount` from the hierarchy

The hypothesis `hcount` of
`Kakeya.MultiScaleFac.densityIn_nodesIn_rescale_eight_le_of_card_mul_branchingN` counts the
level-`b` nodes of the `8ρ_c`-dilate against the branching numbers.  It is produced by the
*ancestor split*:
the nodes in the dilate are distributed among the boundedly many level-`c` ancestors that meet the
dilate, and each ancestor carries at most `C_u ^ 3 · N_{ρ_c} / N_{ρ_b}` nodes.

The machinery for the split lives downstream of this file, so the pieces are re-derived here in
primed copies; they use nothing beyond the fields of `UniformTubeSet` and
`Tube.ChainUniformTubeSet.card_filter_le`.  Because the container is exactly the
`8ρ_c`-dilate, the packing ratio is the absolute constant `32` and no power of `δ` appears. -/

/-- **The dimensional constant of the ancestor split of an `8ρ_c`-dilate.**  The packing count
`2 · 25 ^ (2n) · 32 ^ (2n)` of `Kakeya.MultiScaleFac.card_image_nodeAncestor_le` times the fourth
power of the uniformity constant: one power from Definition 2.1(ii) and three from
`card_nodesUnder_mul_branchingN_le`.  It depends only on the dimension and on `C_u`. -/
noncomputable def nodeCountSplitConst (n : ℕ) (Cu : NNReal) : NNReal :=
  2 * 25 ^ (2 * n) * 32 ^ (2 * n) * Cu ^ 4

/-- **The ancestor-split count in `NNReal`.** -/
private theorem card_image_nodeAncestor_le_nnreal' {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} [DecidableEq ι] (hδ : 0 < δ) (𝒰 : UniformTubeSet s T N C) {a b : ℕ}
    (ha : a ≤ N) (hb : b ≤ N) (hs : s.Nonempty) (h2δ : 2 * δ ≤ gridScale δ N a)
    {r : NNReal} (hr : r ≤ 8 * gridScale δ N a) (K : Tube r E) :
    (((𝒰.nodesIn b K.toConvexSpaceBody).image (𝒰.nodeAncestor b a)).card : NNReal)
      ≤ 2 * 25 ^ (2 * Module.finrank ℝ E) * 32 ^ (2 * Module.finrank ℝ E) * C := by
  rw [← NNReal.coe_le_coe]
  push_cast
  exact card_image_nodeAncestor_le hδ 𝒰 ha hb hs h2δ hr K

open scoped Classical in
/-- **The level-`b` nodes of the `8ρ_c`-dilate of a level-`c` node, counted against the branching
numbers.**  This is the `hcount` hypothesis of
`densityIn_nodesIn_rescale_eight_le_of_card_mul_branchingN`, discharged from the hierarchy: the
nodes in the dilate are distributed among their boundedly many level-`c` ancestors, each of which
carries few nodes.  The constant is `Kakeya.MultiScaleFac.nodeCountSplitConst`. -/
private theorem card_nodesIn_rescale_eight_mul_branchingN_le {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (hδ : 0 < δ) (𝒰 : UniformTubeSet s T N Cu)
    (hCu : 1 ≤ Cu) {c b : ℕ} (hc : c ≤ N) (hb : b ≤ N) (hcb : c ≤ b) (hs : s.Nonempty)
    (h2δ : 2 * δ ≤ gridScale δ N c) {q : ι} :
    (((𝒰.nodesIn b (((𝒰.cover.tube c q).rescale
            (8 * gridScale δ N c)).toConvexSpaceBody)).card : NNReal)) * 𝒰.branchingN b
      ≤ nodeCountSplitConst (Module.finrank ℝ E) Cu * 𝒰.branchingN c := by
  set Kd : Tube (8 * gridScale δ N c) E := (𝒰.cover.tube c q).rescale (8 * gridScale δ N c)
    with hKd
  set nds : Finset ι := 𝒰.nodesIn b Kd.toConvexSpaceBody with hnds
  set Anc : Finset ι := nds.image (𝒰.nodeAncestor b c) with hAnc
  have hAncMem : ∀ j ∈ Anc, j ∈ 𝒰.cover.indexSet c := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨w, hw, rfl⟩
    exact 𝒰.nodeAncestor_mem hc hb hs ((𝒰.mem_nodesIn_iff b Kd.toConvexSpaceBody w).mp hw).1
  calc
    (nds.card : NNReal) * 𝒰.branchingN b
        ≤ (∑ j ∈ Anc, ((𝒰.nodesUnder b c j).card : NNReal)) * 𝒰.branchingN b :=
          mul_le_mul_of_nonneg_right (by
            exact_mod_cast (Finset.card_le_card
              (nodesIn_subset_biUnion_nodesUnder 𝒰 hcb hb hs Kd.toConvexSpaceBody)).trans
              Finset.card_biUnion_le) (zero_le : 0 ≤ 𝒰.branchingN b)
    _ = ∑ j ∈ Anc, ((𝒰.nodesUnder b c j).card : NNReal) * 𝒰.branchingN b := by
          rw [Finset.sum_mul]
    _ ≤ ∑ _j ∈ Anc, (Cu ^ 3 * 𝒰.branchingN c) :=
          Finset.sum_le_sum fun j hj =>
            card_nodesUnder_mul_branchingN_le 𝒰 hCu hc hb (hAncMem j hj)
    _ = (Anc.card : NNReal) * (Cu ^ 3 * 𝒰.branchingN c) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * 25 ^ (2 * Module.finrank ℝ E) * 32 ^ (2 * Module.finrank ℝ E) * Cu)
          * (Cu ^ 3 * 𝒰.branchingN c) :=
          mul_le_mul_of_nonneg_right
            (card_image_nodeAncestor_le_nnreal' hδ 𝒰 hc hb hs h2δ le_rfl Kd)
            (zero_le : 0 ≤ Cu ^ 3 * 𝒰.branchingN c)
    _ = nodeCountSplitConst (Module.finrank ℝ E) Cu * 𝒰.branchingN c := by
          rw [nodeCountSplitConst]
          ring

open scoped Classical in
/-- **The upper density bound with the counting hypothesis discharged from the hierarchy.**  Same
conclusion as `Kakeya.MultiScaleFac.densityIn_nodesIn_rescale_eight_le`, with `hcount` now supplied
by `Kakeya.MultiScaleFac.card_nodesIn_rescale_eight_mul_branchingN_le`.  Only `hscale`, the
branching-versus-scale comparison, remains; the constant is `nodeDensityUBConst n * Cv`. -/
theorem densityIn_nodesIn_rescale_eight_le_of_branchingN {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (𝒰 : UniformTubeSet s T N Cu) (hCu : 1 ≤ Cu) {c b : ℕ} {q : ι} {Cv : NNReal}
    (hc : c ≤ N) (hb : b ≤ N) (hcb : c ≤ b) (hs : s.Nonempty)
    (h2δ : 2 * δ ≤ gridScale δ N c) (hbr : 0 < 𝒰.branchingN b)
    (hscale : ((nodeCountSplitConst (Module.finrank ℝ E) Cu : NNReal) : ENNReal)
          * ((𝒰.branchingN c : NNReal) : ENNReal)
          * ((gridScale δ N b : ENNReal) ^ (Module.finrank ℝ E - 1))
        ≤ (Cv : ENNReal) * ((𝒰.branchingN b : NNReal) : ENNReal)
          * ((gridScale δ N c : ENNReal) ^ (Module.finrank ℝ E - 1))) :
    Kakeya.densityIn
        (𝒰.nodesIn b (((𝒰.cover.tube c q).rescale (8 * gridScale δ N c)).toConvexSpaceBody))
        (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
        (((𝒰.cover.tube c q).rescale (8 * gridScale δ N c)).toConvexSpaceBody)
      ≤ ((nodeDensityUBConst (Module.finrank ℝ E) * Cv : NNReal) : ENNReal) :=
  densityIn_nodesIn_rescale_eight_le_of_card_mul_branchingN
    (Cw := nodeCountSplitConst (Module.finrank ℝ E) Cu) hδ hδ1 𝒰 hbr
    (card_nodesIn_rescale_eight_mul_branchingN_le hδ 𝒰 hCu hc hb hcb hs h2δ) hscale

end MultiScaleFac
end Kakeya

end
