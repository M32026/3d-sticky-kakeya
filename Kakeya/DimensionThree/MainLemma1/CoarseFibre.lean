/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.NodeFamilies
public import Kakeya.DimensionThree.MainLemma1.Setup

/-!
# Main Lemma 1, Case (ii): the containment-to-fibre conversion at the coarse parent

Blueprint `note:ml1bootRawMidContainment`.  Alternative (ii) of
`StickyKakeya.dividingScalesFrostman` asserts its middle Frostman bound at the *containment*
family `Tube.UniformTubeSet.nodesIn b (tube a l)` — all level-`b` nodes lying inside the
coarse node — whereas `Kakeya.ml1Boot.IsCaseTwoData.mid`, and behind it
`Kakeya.ml1Boot.exists_factorTwoScales`, asks for the parent-map fibre of `ϖ_{b→a}`, which is in
general a proper subfamily: the `a`-nodes are not disjoint, so a fine node may lie inside several
coarse nodes while `ϖ_{b→a}` is a function and names exactly one of them.

A Frostman constant is a *ratio* — `ConvexSpaceBody.IsFrostmanIn` bounds `densityIn t W K'` by
`C * densityIn t W K` — so passing to a subfamily shrinks numerator and denominator alike and the
bound does **not** transport.  What does transport is a *share*, through
`ConvexSpaceBody.frostmanConstIn_subfamily_le`, and the four declarations of this file produce
that share and cash it in:

* `Kakeya.ml1Boot.branching_mul_card_nodesIn_le` counts the `b`-nodes inside a coarse node;
* `Kakeya.ml1Boot.branching_le_mul_card_coarseFibre` counts those in a coarse parent fibre;
* `Kakeya.ml1Boot.card_nodesIn_le_card_coarseFibre` combines the two into the share `Cu ⁻⁵`;
* `Kakeya.ml1Boot.frostmanConstIn_coarseFibre_le` is the resulting Frostman transfer.

The exponent `5` is what this route costs and is not claimed optimal: nothing downstream reads
its value, only that it is a constant fixed before `δ`.  The `δ`-bookkeeping that turns it into a
factor `δ ^ (-ε')` is `Kakeya.ml1Boot.caseTwoRawMidFibre`, the last declaration of this file,
which is step 0 of `Kakeya.ml1Boot.exists_caseTwoDataRepair`.

Also here is `Kakeya.ml1Boot.hasBoundedOverlap_nodes`, the one-line bridge saying that the node
parent family of a hierarchy satisfies `Kakeya.ml1Boot.HasBoundedOverlap`.  It belongs with the
node bookkeeping and it is what discharges, at every Case (ii) call site, the bounded-overlap
hypothesis without which `Kakeya.ml1Boot.exists_essDistinct_parentFamily` is false.

*Why this is a separate file.*  Every declaration here is about the *nodes* of a hierarchy: none
mentions a shading, a refinement of the leaves, or the Case (ii) conclusion bundles.  They are
the counting layer that `Kakeya/DimensionThree/MainLemma1.lean` cites, and keeping them out of
`Kakeya/DimensionThree/MainLemma1/NodeFamilies.lean` keeps that file inside its size budget.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody StickyKakeya Tube Filter Topology

namespace Kakeya

universe u

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- **The coarse node parent family, as a situation** (blueprint
`lem:ml1bootParentFamiliesFromNodesCoarse`, together with its standing hypothesis).

This bundles the data the containment-to-fibre conversion runs in, and nothing else: a block
`a ≤ b ≤ N` of the hierarchy, the standing hypothesis that every `b`-node carries a leaf, the
induced map `ϖ_{b→a}` on nodes together with the identity `ϖ (assign b i) = assign a i` that
characterizes it there, and the parent-family property of the coarse nodes over the fine ones.

It is exactly the output of `Kakeya.ml1Boot.exists_nodeParentFamilies_coarse` together with the
two hypotheses that lemma itself takes, so a caller that has applied that lemma has this bundle
for free.  It is bundled rather than repeated because the three counting lemmas below each
consume the whole of it and none of them is meaningful without it: the identity `assign_comp` is
what reads a coarse class as the disjoint union of the fine classes over the fibre, and
`nodes_carry_leaf` is what makes the branching number at the index `b` strictly positive, which
is what licenses the division that produces the share. -/
structure IsCoarseNodeParents {ι : Type*} {δ : NNReal} {s' : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu) (a b : ℕ) (pθ : ι → ι) : Prop where
  /-- The coarse index is at or below the fine one. -/
  le_index : a ≤ b
  /-- …and the fine one is a grid index. -/
  le_gridLen : b ≤ N
  /-- Every `b`-node carries a leaf.  `Tube.UniformTubeSet` nowhere requires this, and
  without it the induced map on nodes is undefined at the empty nodes and
  `Kakeya.ml1Boot.card_nodesIn_le_card_coarseFibre` is false. -/
  nodes_carry_leaf : ∀ k ∈ 𝒰'.cover.indexSet b, ∃ i ∈ s', 𝒰'.cover.assign b i = k
  /-- The identity characterizing `ϖ_{b→a}` on the nodes that carry a leaf.  It is this, and not
  any particular construction of `pθ`, that the counting rests on. -/
  assign_comp : ∀ i ∈ s', pθ (𝒰'.cover.assign b i) = 𝒰'.cover.assign a i
  /-- The coarse nodes form a parent family for the fine ones along `pθ`. -/
  parent : IsParentFamily (𝒰'.cover.indexSet b) (𝒰'.cover.tube b)
    (𝒰'.cover.indexSet a) (𝒰'.cover.tube a) pθ

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **The nodes of a hierarchy are a boundedly overlapping parent family.**

`Kakeya.ml1Boot.HasBoundedOverlap` for the node parent family at a grid index is literally the
field `Tube.UniformTubeSet.boundedOverlap` at that index, with `Co = Cu`: same `Finset`,
same bound.  This is the "single field read" by which every consumer of
`Kakeya.ml1Boot.exists_essDistinct_parentFamily` discharges its bounded-overlap hypothesis, and
it is why the repaired form of that proposition costs the Case (ii) chain nothing. -/
theorem hasBoundedOverlap_nodes {ι : Type*} {δ : NNReal} {s' : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu) {k : ℕ} (hk : k ≤ N) :
    HasBoundedOverlap s' T (𝒰'.cover.indexSet k) (𝒰'.cover.tube k) Cu :=
  fun W => 𝒰'.boundedOverlap k hk W

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Counting the `b`-nodes inside a coarse node** (blueprint
`lem:ml1bootContainmentNodeCount`): `N_b · |𝒩_b(P_a(l))| ≤ Cu ³ N_a`.

The classes of the nodes of `𝒩_b(P_a(l))` are pairwise disjoint, being fibres of the single map
`assign b` over distinct values, and each is contained in the contained set of the coarse node.
Bound each of the `|𝒩_b(P_a(l))|` summands from below by the lower class bracket
`Tube.UniformTubeSet.le_card_class` at the index `b`, and the contained set from above by
`Tube.UniformTubeSet.card_familyIn_le` at the index `a`.

No coarse parent map is read, and no membership `l ∈ 𝒰'_a`: the containment bracket at the index
`a` is stated at every node index.  No lower bound on `Cu` is needed either: the two brackets are
used in the directions that survive `Cu = 0`, where the lower bracket forces `N_b = 0` and both
sides vanish. -/
theorem branching_mul_card_nodesIn_le {ι : Type*} [DecidableEq ι] {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal}
    (𝒰' : UniformTubeSet s' T N Cu) (hab : a ≤ b) (hb : b ≤ N) (l : ι) :
    (𝒰'.branchingN b : ℝ) *
        ((𝒰'.nodesIn b (𝒰'.cover.tube a l).toConvexSpaceBody).card : ℝ)
      ≤ (Cu : ℝ) ^ 3 * (𝒰'.branchingN a : ℝ) := by
  classical
  -- The theorem omits `[MeasurableSpace E] [BorelSpace E]`, but the class counts we read off
  -- (`Tube.UniformTubeSet.le_card_class`, `card_familyIn_le`) live in the measurable
  -- context of `Kakeya/Uniform.lean`.  All the operations used below are pure Finset counts,
  -- so instantiating them with the Borel σ-algebra is harmless.
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  let K := 𝒰'.nodesIn b (𝒰'.cover.tube a l).toConvexSpaceBody
  let cls : ι → Finset ι := fun j => coverClass s' (𝒰'.cover.assign b) j
  let S := Kakeya.familyIn s' (fun i => (T i).toConvexSpaceBody)
    (𝒰'.cover.tube a l).toConvexSpaceBody
  have nodesIn_mem : ∀ i, i ∈ 𝒰'.nodesIn b (𝒰'.cover.tube a l).toConvexSpaceBody ↔
      i ∈ 𝒰'.cover.indexSet b ∧
      (𝒰'.cover.tube b i).toConvexSpaceBody ≤ (𝒰'.cover.tube a l).toConvexSpaceBody := by
    intro i
    change i ∈ (𝒰'.cover.indexSet b).filter
        (fun j' => (𝒰'.cover.tube b j').toConvexSpaceBody ≤
          (𝒰'.cover.tube a l).toConvexSpaceBody) ↔ _
    simp
  have hK : K ⊆ 𝒰'.cover.indexSet b := by
    intro j hj
    exact (nodesIn_mem j).mp hj |>.1
  have habN : a ≤ N := le_trans hab hb
  -- The classes over `K` are pairwise disjoint (the assignment is a function).
  have hpd : (K : Set ι).PairwiseDisjoint cls := by
    intro j1 hj1 j2 hj2 hne
    change Disjoint (cls j1) (cls j2)
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have hm1 : i ∈ s' ∧ 𝒰'.cover.assign b i = j1 := by
      simpa [cls, coverClass] using hi1
    have hm2 : i ∈ s' ∧ 𝒰'.cover.assign b i = j2 := by
      simpa [cls, coverClass] using hi2
    exact hne (hm1.2.symm.trans hm2.2)
  -- Each class over `k ∈ K` is contained in the contained set `S` of the coarse node.
  have hcls_sub : ∀ k ∈ K, cls k ⊆ S := by
    intro k hk i hi
    have hki : k ∈ 𝒰'.cover.indexSet b ∧
        (𝒰'.cover.tube b k).toConvexSpaceBody ≤
          (𝒰'.cover.tube a l).toConvexSpaceBody :=
      (nodesIn_mem k).mp hk
    have hmem : i ∈ s' ∧ 𝒰'.cover.assign b i = k := by
      simpa [cls, coverClass] using hi
    have hTk : (T i).toConvexSpaceBody ≤
        (𝒰'.cover.tube b (𝒰'.cover.assign b i)).toConvexSpaceBody :=
      𝒰'.cover.le_tube_assign b hb i hmem.1
    rw [hmem.2] at hTk
    simpa [S, Kakeya.familyIn] using ⟨hmem.1, hTk.trans hki.2⟩
  -- The union of the classes over `K` is contained in `S`, so its cardinality is at most `|S|`.
  have hunion_sub : K.biUnion cls ⊆ S := by
    intro i hi
    rw [Finset.mem_biUnion] at hi
    rcases hi with ⟨k, hk, hik⟩
    exact hcls_sub k hk hik
  have hsum_le : ∑ j ∈ K, ((cls j).card : ℝ) ≤ (S.card : ℝ) := by
    have hc1 : (K.biUnion cls).card ≤ S.card := Finset.card_le_card hunion_sub
    have hc2 : (K.biUnion cls).card = ∑ j ∈ K, (cls j).card :=
      Finset.card_biUnion hpd
    rw [hc2] at hc1
    exact_mod_cast hc1
  -- Lower bound: `|K| · N_b ≤ Cu · Σ_{j ∈ K} |cls j|`.
  have hlower : (K.card : ℝ) * (𝒰'.branchingN b : ℝ) ≤
      (Cu : ℝ) * ∑ j ∈ K, ((cls j).card : ℝ) := by
    calc
      (K.card : ℝ) * (𝒰'.branchingN b : ℝ) = ∑ j ∈ K, (𝒰'.branchingN b : ℝ) := by
        simp
      _ ≤ ∑ j ∈ K, ((Cu : ℝ) * ((cls j).card : ℝ)) := by
        exact Finset.sum_le_sum (by
          intro j hj
          exact_mod_cast 𝒰'.le_card_class b hb j (hK hj))
      _ = (Cu : ℝ) * ∑ j ∈ K, ((cls j).card : ℝ) := by
        rw [← Finset.mul_sum]
  have hCu0 : (0 : ℝ) ≤ (Cu : ℝ) := by positivity
  -- Upper bound on the contained set: `|S| ≤ Cu² · N_a`.
  have hSle : (S.card : ℝ) ≤ (Cu : ℝ) ^ 2 * (𝒰'.branchingN a : ℝ) := by
    exact_mod_cast 𝒰'.card_familyIn_le habN l
  calc
    (𝒰'.branchingN b : ℝ) * (K.card : ℝ) ≤ (Cu : ℝ) * (S.card : ℝ) := by
      have hstep : (K.card : ℝ) * (𝒰'.branchingN b : ℝ) ≤ (Cu : ℝ) * (S.card : ℝ) :=
        (hlower.trans (mul_le_mul_of_nonneg_left hsum_le hCu0))
      nlinarith
    _ ≤ (Cu : ℝ) * ((Cu : ℝ) ^ 2 * (𝒰'.branchingN a : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hSle hCu0
    _ = (Cu : ℝ) ^ 3 * (𝒰'.branchingN a : ℝ) := by
      ring

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **Counting the `b`-nodes in a coarse parent fibre** (blueprint
`lem:ml1bootParentFibreCount`): `N_a ≤ Cu ² N_b · |t_τ[l]|`, where
`t_τ[l] = Kakeya.ml1Boot.fibre (𝒰'_b) ϖ l`.

The coarse class of `l` is the disjoint union of the fine classes over the fibre — that is
`Kakeya.ml1Boot.IsCoarseNodeParents.assign_comp` read in both directions — so the lower class
bracket at the index `a` and the upper class bracket at the index `b` sandwich the count.

As in `Kakeya.ml1Boot.branching_mul_card_nodesIn_le`, no lower bound on `Cu` is needed: both
brackets are used in the direction that stays true at `Cu = 0`. -/
theorem branching_le_mul_card_coarseFibre {ι : Type*} [DecidableEq ι] {δ : NNReal}
    {s' : Finset ι} {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal}
    (𝒰' : UniformTubeSet s' T N Cu) {pθ : ι → ι} (hcnp : IsCoarseNodeParents 𝒰' a b pθ)
    {l : ι} (hl : l ∈ 𝒰'.cover.indexSet a) :
    (𝒰'.branchingN a : ℝ)
      ≤ (Cu : ℝ) ^ 2 * (𝒰'.branchingN b : ℝ) *
          ((fibre (𝒰'.cover.indexSet b) pθ l).card : ℝ) := by
  classical
  set F : Finset ι := fibre (𝒰'.cover.indexSet b) pθ l
  let cls : ι → Finset ι := fun k => coverClass s' (𝒰'.cover.assign b) k
  have hleN : a ≤ N := hcnp.le_index.trans hcnp.le_gridLen
  -- Step 1: the coarse class of `l` is the disjoint union of the fine classes over the fibre.
  have hsplit : coverClass s' (𝒰'.cover.assign a) l = F.biUnion cls := by
    classical
    ext i
    constructor
    · intro h
      have h_mem : i ∈ s' ∧ 𝒰'.cover.assign a i = l := by
        simpa [coverClass, Finset.mem_filter] using h
      rw [Finset.mem_biUnion]
      refine ⟨𝒰'.cover.assign b i, ?_, ?_⟩
      · simpa [F, fibre, Finset.mem_filter] using
          ⟨𝒰'.cover.assign_mem b hcnp.le_gridLen i h_mem.1, by
            rw [hcnp.assign_comp i h_mem.1]
            exact h_mem.2⟩
      · simpa [cls, coverClass, Finset.mem_filter] using (⟨h_mem.1, rfl⟩ :
          i ∈ s' ∧ 𝒰'.cover.assign b i = 𝒰'.cover.assign b i)
    · intro h
      rw [Finset.mem_biUnion] at h
      rcases h with ⟨k, hk, hik⟩
      have hk_mem : k ∈ 𝒰'.cover.indexSet b ∧ pθ k = l := by
        simpa [F, fibre, Finset.mem_filter] using hk
      have hik_mem : i ∈ s' ∧ 𝒰'.cover.assign b i = k := by
        simpa [cls, coverClass, Finset.mem_filter] using hik
      simpa [coverClass, Finset.mem_filter] using ⟨hik_mem.1, by
        calc
          𝒰'.cover.assign a i = pθ (𝒰'.cover.assign b i) := (hcnp.assign_comp i hik_mem.1).symm
          _ = pθ k := by rw [hik_mem.2]
          _ = l := hk_mem.2⟩
  -- Step 2: the classes over the fibre are pairwise disjoint (the assignment is a function).
  have hpd : (F : Set ι).PairwiseDisjoint cls := by
    intro k1 hk1 k2 hk2 hne
    change Disjoint (cls k1) (cls k2)
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have hm1 : i ∈ s' ∧ 𝒰'.cover.assign b i = k1 := by
      simpa [cls, coverClass] using hi1
    have hm2 : i ∈ s' ∧ 𝒰'.cover.assign b i = k2 := by
      simpa [cls, coverClass] using hi2
    exact hne (hm1.2.symm.trans hm2.2)
  -- cardinality of the coarse class as the sum over the fibre
  have hcard : (coverClass s' (𝒰'.cover.assign a) l).card = ∑ k ∈ F, (cls k).card := by
    rw [hsplit]
    exact Finset.card_biUnion hpd
  -- Step 3, in ℝ: the two class brackets.
  have hsumR : ((coverClass s' (𝒰'.cover.assign a) l).card : ℝ)
      = ∑ k ∈ F, ((cls k).card : ℝ) := by
    exact_mod_cast hcard
  -- lower bracket at the index `a`: `N_a ≤ Cu · |class_a l| = Cu · Σ`.
  have hlow : (𝒰'.branchingN a : ℝ) ≤ (Cu : ℝ) * ∑ k ∈ F, ((cls k).card : ℝ) := by
    have h1 : (𝒰'.branchingN a : ℝ) ≤
        (Cu : ℝ) * ((coverClass s' (𝒰'.cover.assign a) l).card : ℝ) := by
      exact_mod_cast 𝒰'.le_card_class a hleN l hl
    calc
      (𝒰'.branchingN a : ℝ) ≤ (Cu : ℝ) * ((coverClass s' (𝒰'.cover.assign a) l).card : ℝ) := h1
      _ = (Cu : ℝ) * (∑ k ∈ F, ((cls k).card : ℝ)) := by
        rw [hsumR]
  -- upper bound on each summand via the upper bracket at the index `b`.
  have hsumle : (∑ k ∈ F, ((cls k).card : ℝ))
      ≤ (F.card : ℝ) * (Cu : ℝ) * (𝒰'.branchingN b : ℝ) := by
    calc
      (∑ k ∈ F, ((cls k).card : ℝ)) ≤ ∑ k ∈ F, ((Cu : ℝ) * (𝒰'.branchingN b : ℝ)) := by
        exact Finset.sum_le_sum (by
          intro k hk
          have hk_index : k ∈ 𝒰'.cover.indexSet b := (Finset.mem_filter.mp hk).1
          exact_mod_cast 𝒰'.card_class_le b hcnp.le_gridLen k hk_index)
      _ = (F.card : ℝ) * (Cu : ℝ) * (𝒰'.branchingN b : ℝ) := by
        rw [Finset.sum_const]
        simp only [nsmul_eq_mul]
        ring
  -- Step 4: assemble.
  calc
    (𝒰'.branchingN a : ℝ) ≤ (Cu : ℝ) * ∑ k ∈ F, ((cls k).card : ℝ) := hlow
    _ ≤ (Cu : ℝ) * ((F.card : ℝ) * (Cu : ℝ) * (𝒰'.branchingN b : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hsumle (by positivity)
    _ = (Cu : ℝ) ^ 2 * (𝒰'.branchingN b : ℝ) * (F.card : ℝ) := by
      ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The coarse parent fibre is a `Cu ⁻⁵`-share of the containment family: the count**
(blueprint `lem:ml1bootFibreShareCount`).

Two conclusions, as in the blueprint.  The fibre is contained in the containment family: that is
the parent-family clause `P_b(k) ⊆ P_a(ϖ k)` of
`Kakeya.ml1Boot.IsCoarseNodeParents.parent`, and the inclusion is in general strict.  And it
carries at least a `Cu ⁻⁵` share of it: chain
`Kakeya.ml1Boot.branching_mul_card_nodesIn_le` with
`Kakeya.ml1Boot.branching_le_mul_card_coarseFibre` and cancel the branching number `N_b`, which
is strictly positive because every `b`-node carries a leaf and the upper class bracket then
forces `1 ≤ Cu · N_b`. -/
theorem card_nodesIn_le_card_coarseFibre {ι : Type*} [DecidableEq ι] {δ : NNReal}
    {s' : Finset ι} {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal} (hCu : 1 ≤ Cu)
    (𝒰' : UniformTubeSet s' T N Cu) {pθ : ι → ι} (hcnp : IsCoarseNodeParents 𝒰' a b pθ)
    {l : ι} (hl : l ∈ 𝒰'.cover.indexSet a) :
    fibre (𝒰'.cover.indexSet b) pθ l
        ⊆ 𝒰'.nodesIn b (𝒰'.cover.tube a l).toConvexSpaceBody ∧
      ((𝒰'.nodesIn b (𝒰'.cover.tube a l).toConvexSpaceBody).card : ℝ)
        ≤ (Cu : ℝ) ^ 5 * ((fibre (𝒰'.cover.indexSet b) pθ l).card : ℝ) := by
  constructor
  · -- containment: the fibre is the parent-map preimage of a single coarse node
    intro k hk
    rw [fibre] at hk
    have hk_index : k ∈ 𝒰'.cover.indexSet b := (Finset.mem_filter.mp hk).1
    have hk_pθ : pθ k = l := (Finset.mem_filter.mp hk).2
    rw [UniformTubeSet.nodesIn]
    rw [Finset.mem_filter]
    constructor
    · exact hk_index
    · have hle := hcnp.parent.le_parent k hk_index
      simpa [hk_pθ] using hle
  · -- the share: `|nodesIn| ≤ Cu ^ 5 · |fibre|`
    classical
    let NI : Finset ι := 𝒰'.nodesIn b (𝒰'.cover.tube a l).toConvexSpaceBody
    let F : Finset ι := fibre (𝒰'.cover.indexSet b) pθ l
    let B : ℝ := (𝒰'.branchingN b : ℝ)
    by_cases hNi : NI.card = 0
    · -- empty: the left side is `0`
      have h0f : (0 : ℝ) ≤ ((fibre (𝒰'.cover.indexSet b) pθ l).card : ℝ) := by
        exact Nat.cast_nonneg (fibre (𝒰'.cover.indexSet b) pθ l).card
      have h0c : (0 : ℝ) ≤ (Cu : ℝ) ^ 5 := pow_nonneg (NNReal.coe_nonneg Cu) 5
      rw [hNi]
      simpa using mul_nonneg h0c h0f
    · -- nonempty: cancel the strictly positive branch number `N_b`
      have hNe : NI.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hNi)
      rcases hNe with ⟨k₀, hk₀⟩
      have hk₀m : k₀ ∈ (𝒰'.cover.indexSet b).filter (fun j =>
          (𝒰'.cover.tube b j).toConvexSpaceBody ≤ (𝒰'.cover.tube a l).toConvexSpaceBody) := by
        simpa [NI, UniformTubeSet.nodesIn] using hk₀
      have hk₀index : k₀ ∈ 𝒰'.cover.indexSet b := (Finset.mem_filter.mp hk₀m).1
      rcases hcnp.nodes_carry_leaf k₀ hk₀index with ⟨i, hi, hassign⟩
      let cls_k : Finset ι := coverClass s' (𝒰'.cover.assign b) k₀
      have hi_c : i ∈ cls_k := by
        simpa [cls_k, coverClass, hassign] using hi
      have hcls_pos : 0 < cls_k.card := Finset.card_pos.mpr ⟨i, hi_c⟩
      -- `1 ≤ Cu · N_b`
      have hOne : (1 : ℝ) ≤ (Cu : ℝ) * B := by
        have hge : (1 : NNReal) ≤ (cls_k.card : NNReal) := by
          exact_mod_cast (Nat.succ_le_of_lt hcls_pos)
        have hle : (cls_k.card : NNReal) ≤ Cu * 𝒰'.branchingN b :=
          𝒰'.card_class_le b hcnp.le_gridLen k₀ hk₀index
        exact_mod_cast (le_trans hge hle)
      have hcu_pos : 0 < (Cu : ℝ) := by
        exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hCu)
      have hBpos : 0 < B := by
        have hcm : 0 < (Cu : ℝ) * B := lt_of_lt_of_le (by norm_num) hOne
        exact pos_of_mul_pos_right hcm (le_of_lt hcu_pos)
      -- chain the two counting lemmas
      have h1 : B * (NI.card : ℝ) ≤ (Cu : ℝ) ^ 3 * (𝒰'.branchingN a : ℝ) := by
        simpa [B, NI] using branching_mul_card_nodesIn_le 𝒰' hcnp.le_index hcnp.le_gridLen l
      have h2 : (𝒰'.branchingN a : ℝ) ≤ (Cu : ℝ) ^ 2 * B * (F.card : ℝ) := by
        simpa [B, F] using branching_le_mul_card_coarseFibre 𝒰' hcnp hl
      have h2' : (Cu : ℝ) ^ 3 * (𝒰'.branchingN a : ℝ)
          ≤ (Cu : ℝ) ^ 5 * B * (F.card : ℝ) := by
        calc
          (Cu : ℝ) ^ 3 * (𝒰'.branchingN a : ℝ)
              ≤ (Cu : ℝ) ^ 3 * ((Cu : ℝ) ^ 2 * B * (F.card : ℝ)) := by
                exact mul_le_mul_of_nonneg_left h2 (pow_nonneg (le_of_lt hcu_pos) 3)
          _ = (Cu : ℝ) ^ 5 * B * (F.card : ℝ) := by
            ring
      have hchain : B * (NI.card : ℝ) ≤ (Cu : ℝ) ^ 5 * B * (F.card : ℝ) :=
        le_trans h1 h2'
      have hbm : B * (NI.card : ℝ) ≤ B * ((Cu : ℝ) ^ 5 * (F.card : ℝ)) := by
        simpa [mul_comm, mul_assoc, mul_left_comm] using hchain
      exact le_of_mul_le_mul_left hbm hBpos

/-- **The coarse parent fibre is a `Cu ⁻⁵`-share of the containment family: the Frostman
transfer** (blueprint `lem:ml1bootFibreShareTransfer`).

`Kakeya.ml1Boot.card_nodesIn_le_card_coarseFibre` fed to
`ConvexSpaceBody.frostmanConstIn_subfamily_le` with `κ = Cu ⁻⁵`.  Both families are read as
families of node tubes at the index `b`, which have the common volume of an exact `ρ_b`-tube and
lie in the coarse node, so the hypotheses of that lemma hold.

The nonemptiness hypothesis is that of `ConvexSpaceBody.frostmanConstIn_subfamily_le`; it is
discharged at the call site by the consumer, which only ever reads the bound at a coarse node
that some fine node lies under. -/
theorem frostmanConstIn_coarseFibre_le {ι : Type*} [DecidableEq ι] {δ : NNReal}
    {s' : Finset ι} {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal} (hCu : 1 ≤ Cu)
    (𝒰' : UniformTubeSet s' T N Cu) {pθ : ι → ι} (hcnp : IsCoarseNodeParents 𝒰' a b pθ)
    {l : ι} (hl : l ∈ 𝒰'.cover.indexSet a)
    (hne : (𝒰'.nodesIn b (𝒰'.cover.tube a l).toConvexSpaceBody).Nonempty) :
    frostmanConstIn (fibre (𝒰'.cover.indexSet b) pθ l)
        (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
        (𝒰'.cover.tube a l).toConvexSpaceBody
      ≤ (Cu : ENNReal) ^ 5 *
          frostmanConstIn (𝒰'.nodesIn b (𝒰'.cover.tube a l).toConvexSpaceBody)
            (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
            (𝒰'.cover.tube a l).toConvexSpaceBody := by
  classical
  set sBase : Finset ι := 𝒰'.nodesIn b (𝒰'.cover.tube a l).toConvexSpaceBody with hBase
  set sFibre : Finset ι := fibre (𝒰'.cover.indexSet b) pθ l with hFibre
  set Wb : ι → ConvexSpaceBody E := fun k => (𝒰'.cover.tube b k).toConvexSpaceBody with hWb
  set Ka : ConvexSpaceBody E := (𝒰'.cover.tube a l).toConvexSpaceBody with hKa
  set κ : ENNReal := ((Cu : ENNReal) ^ 5)⁻¹ with hκ
  let v : ENNReal := volume (𝒰'.cover.tube b hne.choose).carrier
  have hCu5_ne0 : (Cu : ENNReal) ^ 5 ≠ 0 := by
    have hCu0 : (Cu : ENNReal) ≠ 0 := by
      exact ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hCu))
    exact pow_ne_zero 5 hCu0
  have hCu5_ne_top : (Cu : ENNReal) ^ 5 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hκ_ne : κ ≠ 0 := by
    dsimp [κ]
    exact ENNReal.inv_ne_zero.mpr hCu5_ne_top
  have hcount : sFibre ⊆ sBase ∧
      (sBase.card : ℝ) ≤ (Cu : ℝ) ^ 5 * (sFibre.card : ℝ) := by
    simpa [sBase, sFibre] using card_nodesIn_le_card_coarseFibre hCu 𝒰' hcnp hl
  have hs : sBase.Nonempty := hne
  have hvol : ∀ i ∈ sBase, volume (Wb i).carrier = v := by
    intro i hi
    simpa [Wb, v, sBase] using
      (Tube.volume_carrier_eq_volume_carrier (𝒰'.cover.tube b i) (𝒰'.cover.tube b hne.choose))
  have hWK : ∀ i ∈ sBase, Wb i ≤ Ka := by
    intro i hi
    have hmem : i ∈ 𝒰'.cover.indexSet b ∧
        (𝒰'.cover.tube b i).toConvexSpaceBody ≤ Ka := by
      simpa [sBase, UniformTubeSet.nodesIn] using hi
    simpa [Wb] using hmem.2
  have hcard_nn : (sBase.card : NNReal) ≤ (Cu : NNReal) ^ 5 * (sFibre.card : NNReal) := by
    exact_mod_cast hcount.2
  have hcard_enn : (sBase.card : ENNReal) ≤ (Cu : ENNReal) ^ 5 * (sFibre.card : ENNReal) := by
    exact ENNReal.coe_le_coe.mpr hcard_nn
  have hcard : κ * (sBase.card : ENNReal) ≤ (sFibre.card : ENNReal) := by
    calc
      κ * (sBase.card : ENNReal)
          ≤ κ * ((Cu : ENNReal) ^ 5 * (sFibre.card : ENNReal)) := by
            exact mul_le_mul_right hcard_enn κ
      _ = (sFibre.card : ENNReal) := by
        dsimp [κ]
        rw [← mul_assoc, ENNReal.inv_mul_cancel hCu5_ne0 hCu5_ne_top, one_mul]
  have hsub : frostmanConstIn sFibre Wb Ka ≤ κ⁻¹ * frostmanConstIn sBase Wb Ka := by
    apply frostmanConstIn_subfamily_le (s := sBase) (s' := sFibre) (W := Wb) (K := Ka)
      (v := v) (κ := κ)
    · exact hs
    · exact hvol
    · exact hWK
    · exact hcount.1
    · exact hκ_ne
    · exact hcard
  calc
    frostmanConstIn sFibre Wb Ka ≤ κ⁻¹ * frostmanConstIn sBase Wb Ka := hsub
    _ = (Cu : ENNReal) ^ 5 * frostmanConstIn sBase Wb Ka := by
      simp [hκ]

/-- **Case (ii) repair, step 0: the middle bound at the coarse parent fibre** (blueprint
`lem:ml1bootRawMidToFibre`).

The passage from the *containment* family the dichotomy speaks about to the parent-map *fibre*
that `Kakeya.ml1Boot.exists_factorTwoScales` consumes, performed before anything is refined, at a
cost of one further factor `δ ^ (-ε')`.

It is `Kakeya.ml1Boot.frostmanConstIn_coarseFibre_le` composed with the assumed bound at the
containment family — which is item (b) of blueprint `lem:ml1bootCaseIIDataRaw`, i.e. the field
`Kakeya.ml1Boot.IsCaseTwoRawUpper.mid` read through
`Kakeya.ml1Boot.familyIn_indexSet_eq_nodesIn` — the fixed constant `Cu ⁵` being absorbed into a
second `δ ^ (-ε')` for all small `δ`, exactly as in
`Kakeya.ml1Boot.eventually_dichotomyLoss_le`.  Hence the exponent `-2 ε'` in the conclusion.

The Case (ii) input bundle is *not* a hypothesis: the assumed bound is the only thing read off
it, and passing the bundle as well would leave an unused argument.  The exponent index is that
of the blueprint's `η_{j-1}` at `j = m + 1`, namely `p.η m`. -/
theorem caseTwoRawMidFibre (p : Params) {ε' : ℝ} (hε' : 0 < ε') {Cu : NNReal} (hCu : 1 ≤ Cu) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} [DecidableEq ι] {s' : Finset ι} {T : ι → Tube δ E} {N : ℕ}
        (a b m : ℕ) (𝒰' : UniformTubeSet s' T N Cu) (pθ : ι → ι),
        IsCoarseNodeParents 𝒰' a b pθ →
        (∀ l' ∈ 𝒰'.cover.indexSet a,
          frostmanConstIn (𝒰'.nodesIn b (𝒰'.cover.tube a l').toConvexSpaceBody)
              (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
              (𝒰'.cover.tube a l').toConvexSpaceBody
            ≤ (δ : ENNReal) ^ (-ε') *
                ((gridScale δ N a / gridScale δ N b : NNReal) : ENNReal) ^ p.η m) →
        ∀ l' ∈ 𝒰'.cover.indexSet a,
          (𝒰'.nodesIn b (𝒰'.cover.tube a l').toConvexSpaceBody).Nonempty →
          frostmanConstIn (fibre (𝒰'.cover.indexSet b) pθ l')
              (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
              (𝒰'.cover.tube a l').toConvexSpaceBody
            ≤ (δ : ENNReal) ^ (-2 * ε') *
                ((gridScale δ N a / gridScale δ N b : NNReal) : ENNReal) ^ p.η m := by
  -- Step 1: eventually (Cu : ENNReal)^5 ≤ (δ : ENNReal)^(-ε'), as δ → 0⁺
  have hcu_abs : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      (Cu : ENNReal) ^ (5 : ℕ) ≤ (δ : ENNReal) ^ (-ε') := by
    have hCposR : (0 : ℝ) < (Cu : ℝ) ^ (5 : ℕ) := by positivity
    filter_upwards [nnreal_eventually_of_real_eventually
        (Kakeya.absorb_const_le_rpow_neg hCposR hε'), self_mem_nhdsWithin]
      with δ hcst hδ0
    have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
    -- transfer the real inequality (Cu : ℝ)^5 ≤ (δ : ℝ)^(-ε') into ENNReal
    rw [ennreal_coe_nnreal_rpow hδR (-ε')]
    calc
      (Cu : ENNReal) ^ (5 : ℕ) = ENNReal.ofReal ((Cu : ℝ) ^ (5 : ℕ)) := by
        rw [← ENNReal.ofReal_coe_nnreal (p := Cu), ENNReal.ofReal_pow]
        positivity
      _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ε')) := ENNReal.ofReal_le_ofReal hcst
  -- bookkeeping: eventually take δ to be positive, for the rpow-add step
  have hδ0event : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, 0 < δ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hδ
  filter_upwards [hcu_abs, hδ0event] with δ hcu_absδ hδ0
  intro ι _i s' T N a b m 𝒰' pθ hcnp hin l' hl' hne
  have hδne0 : ((δ : NNReal) : ENNReal) ≠ 0 := ne_of_gt (ENNReal.coe_pos.mpr hδ0)
  set ratio : ENNReal := ((gridScale δ N a / gridScale δ N b : NNReal) : ENNReal) ^ p.η m
  -- frostmanConstIn_coarseFibre_le transfers from the fibre to the containment family
  have hfib : frostmanConstIn (fibre (𝒰'.cover.indexSet b) pθ l')
        (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
        (𝒰'.cover.tube a l').toConvexSpaceBody
      ≤ (Cu : ENNReal) ^ (5 : ℕ) *
          frostmanConstIn (𝒰'.nodesIn b (𝒰'.cover.tube a l').toConvexSpaceBody)
            (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
            (𝒰'.cover.tube a l').toConvexSpaceBody :=
    frostmanConstIn_coarseFibre_le hCu 𝒰' hcnp hl' hne
  have hmid : frostmanConstIn (𝒰'.nodesIn b (𝒰'.cover.tube a l').toConvexSpaceBody)
        (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
        (𝒰'.cover.tube a l').toConvexSpaceBody
      ≤ (δ : ENNReal) ^ (-ε') * ratio :=
    hin l' hl'
  -- the fixed constant `Cu ⁵` is absorbed into a second `δ ^ (-ε')`
  have hcoef : (Cu : ENNReal) ^ (5 : ℕ) * (δ : ENNReal) ^ (-ε')
      ≤ (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ (-ε') := by
    exact mul_le_mul_of_nonneg_right hcu_absδ (by positivity)
  calc
    frostmanConstIn (fibre (𝒰'.cover.indexSet b) pθ l')
        (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
        (𝒰'.cover.tube a l').toConvexSpaceBody
        ≤ (Cu : ENNReal) ^ (5 : ℕ) *
            frostmanConstIn (𝒰'.nodesIn b (𝒰'.cover.tube a l').toConvexSpaceBody)
              (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
              (𝒰'.cover.tube a l').toConvexSpaceBody := hfib
    _ ≤ (Cu : ENNReal) ^ (5 : ℕ) * ((δ : ENNReal) ^ (-ε') * ratio) := by
          exact mul_le_mul_of_nonneg_left hmid (by positivity)
    _ = ((Cu : ENNReal) ^ (5 : ℕ) * (δ : ENNReal) ^ (-ε')) * ratio := by ac_rfl
    _ ≤ ((δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ (-ε')) * ratio := by
          exact mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = (δ : ENNReal) ^ (-2 * ε') * ratio := by
          have hpow : (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ (-ε')
              = (δ : ENNReal) ^ (-2 * ε') := by
            rw [← ENNReal.rpow_add (-ε') (-ε') hδne0 ENNReal.coe_ne_top]
            congr 1
            ring
          rw [hpow]

/-- **Fibrewise empty-or-share** (blueprint `def:ml1bootFibrewiseEmptyOrShare`).

Let `pθ` be the coarse node parent map, `sb` the full fine node index set (`𝒰'.cover.indexSet b`),
`sa` the coarse one (`𝒰'.cover.indexSet a`), and `t ⊆ sb` a retained subfamily.  We say `t` is
*fibrewise empty-or-share at `κ`* over `pθ` if over every coarse node `l ∈ sa` either the retained
fibre `Kakeya.ml1Boot.fibre t pθ l` is empty, or it carries at least a `κ`-share of the full fibre
`Kakeya.ml1Boot.fibre sb pθ l`.

That is: the selection may lose a coarse fibre *entirely*, but any fibre it keeps at all it keeps a
`κ`-share of.  Losing a fibre entirely is harmless downstream, the empty family having Frostman
constant `0`; keeping all but a concentrated part of one is not, and that is exactly what the
disjunction excludes.  This dichotomy — and not a global cardinality share — is what
`Kakeya.ml1Boot.frostmanConstIn_retainedFibre_le` consumes.

The subset relation `t ⊆ sb` is *not* part of this definition: it is data the consumers carry
separately, since the definition is meaningful (and the empty branch true) without it. -/
def IsFibrewiseEmptyOrShare {ι : Type*} [DecidableEq ι] (sb sa t : Finset ι) (pθ : ι → ι)
    (κ : ENNReal) : Prop :=
  ∀ l ∈ sa,
    fibre t pθ l = ∅ ∨
      κ * ((fibre sb pθ l).card : ENNReal) ≤ ((fibre t pθ l).card : ENNReal)

/-- **The dichotomy is monotone in the share: a bigger share implies a smaller one**
(blueprint `lem:ml1bootFibrewiseShareMono`).

`Kakeya.ml1Boot.IsFibrewiseEmptyOrShare` at `κ` is a *stronger* statement for *larger* `κ`, the
share branch reading `κ |F_l| ≤ |F_l ∩ t|`.  Since the exponents in play are powers of a `δ ≤ 1`,
where a larger exponent means a smaller number, this is the lemma that lets a supply produced at
one exponent meet a demand declared at a larger one.

It is what connects the two ends of route 3 of blueprint
`note:ml1bootEssDistinctFibrewiseShare`: the post-selection trim
(`Kakeya.ml1Boot.fibrewiseTrim`) produces the dichotomy at whatever share its cost lemma can
afford, while `Kakeya.ml1Boot.frostmanConstIn_retainedFibre_le` is consumed at the share the
exponent budget of `Kakeya.ml1Boot.mid_le_of_share_compose` permits; the two need not be the same
number, and this lemma is the only thing standing between them. -/
theorem IsFibrewiseEmptyOrShare.mono_share {ι : Type*} [DecidableEq ι]
    {sb sa t : Finset ι} {pθ : ι → ι} {κ κ' : ENNReal}
    (h : IsFibrewiseEmptyOrShare sb sa t pθ κ) (hκ : κ' ≤ κ) :
    IsFibrewiseEmptyOrShare sb sa t pθ κ' := by
  intro l hl
  rcases h l hl with hempty | hshare
  · exact Or.inl hempty
  · exact Or.inr (le_trans (mul_le_mul_left hκ _) hshare)

omit [Nontrivial E] in
/-- **The middle bound descends to a retained fibre** (blueprint
`lem:ml1bootRetainedFibreTransfer`).

If the retained node set `t ⊆ 𝒰'.cover.indexSet b` is fibrewise empty-or-share at `κ ≠ 0` over the
coarse parent map `pθ` (`Kakeya.ml1Boot.IsFibrewiseEmptyOrShare`), then over every coarse node the
Frostman constant of the *retained* fibre is at most `κ⁻¹` times that of the *full* fibre.  This is
the descent half of the Case (ii) repair: composed with a bound
`≤ δ ^ (-ε') * (θ/τ) ^ η_m` at the full fibre — which is what
`Kakeya.ml1Boot.caseTwoRawMidFibre` delivers — it gives the same bound at the retained fibre with
the single further factor `κ⁻¹`, i.e. `δ ^ (-ε'')` at `κ = δ ^ ε''`.

The bracket is throughout the *parent-map fibre* of `pθ`, not the containment family
`Tube.UniformTubeSet.nodesIn b (𝒰'.cover.tube a l)` of which it is in general a proper
subfamily (`note:ml1bootRawMidContainment`): the passage between the two is step 0 and is already
paid for by `Kakeya.ml1Boot.caseTwoRawMidFibre`.  The only thing read out of
`Kakeya.ml1Boot.IsCoarseNodeParents` is the one-sided containment `P_b k ⊆ P_a (pθ k)` of its
`parent` clause.

No nonemptiness hypothesis on the full fibre is needed: in the share branch the full fibre is
nonempty because the retained one is, and in the empty branch the left-hand side is `0`.  No lower
bound on `Cu` is needed either — the counting lemmas of this file are not used, the share being a
hypothesis. -/
theorem frostmanConstIn_retainedFibre_le {ι : Type*} [DecidableEq ι] {δ : NNReal}
    {s' : Finset ι} {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal}
    (𝒰' : UniformTubeSet s' T N Cu) {pθ : ι → ι} (hcnp : IsCoarseNodeParents 𝒰' a b pθ)
    {t : Finset ι} (ht : t ⊆ 𝒰'.cover.indexSet b) {κ : ENNReal} (hκ : κ ≠ 0)
    (hshare : IsFibrewiseEmptyOrShare (𝒰'.cover.indexSet b) (𝒰'.cover.indexSet a) t pθ κ)
    {l : ι} (hl : l ∈ 𝒰'.cover.indexSet a) :
    frostmanConstIn (fibre t pθ l)
        (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
        (𝒰'.cover.tube a l).toConvexSpaceBody
      ≤ κ⁻¹ *
          frostmanConstIn (fibre (𝒰'.cover.indexSet b) pθ l)
            (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
            (𝒰'.cover.tube a l).toConvexSpaceBody := by
  classical
  set Wb : ι → ConvexSpaceBody E := fun k => (𝒰'.cover.tube b k).toConvexSpaceBody with hWb
  set Ka : ConvexSpaceBody E := (𝒰'.cover.tube a l).toConvexSpaceBody with hKa
  by_cases hstruct : (fibre t pθ l) = ∅
  · have hle0 : frostmanConstIn (fibre t pθ l) Wb Ka ≤ 0 := by
      rw [hstruct]
      apply ConvexSpaceBody.frostmanConstIn_le
      intro K' hK'
      simp [Kakeya.densityIn]
    have h0 : (0 : ENNReal) ≤ κ⁻¹ * frostmanConstIn (fibre (𝒰'.cover.indexSet b) pθ l) Wb Ka := by
      exact bot_le
    exact le_trans hle0 h0
  · have hnon : (fibre t pθ l).Nonempty := by
      exact Finset.nonempty_iff_ne_empty.mpr hstruct
    rcases hnon with ⟨k₀, hk₀⟩
    have hsub : fibre t pθ l ⊆ fibre (𝒰'.cover.indexSet b) pθ l := by
      intro x hx
      rw [fibre] at hx ⊢
      have hx1 : x ∈ t := (Finset.mem_filter.mp hx).1
      have hx2 : pθ x = l := (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr ⟨ht hx1, hx2⟩
    have hfull_ne : (fibre (𝒰'.cover.indexSet b) pθ l).Nonempty := ⟨k₀, hsub hk₀⟩
    have hshr : κ * ((fibre (𝒰'.cover.indexSet b) pθ l).card : ENNReal)
        ≤ ((fibre t pθ l).card : ENNReal) := by
      rcases hshare l hl with h_empt | hshr
      · exfalso
        have hne0 : (fibre t pθ l).Nonempty := ⟨k₀, hk₀⟩
        rw [h_empt] at hne0
        exact Finset.not_nonempty_empty hne0
      · exact hshr
    let v : ENNReal := volume (Wb k₀).carrier
    have hvol : ∀ i ∈ fibre (𝒰'.cover.indexSet b) pθ l, volume (Wb i).carrier = v := by
      intro i hi
      simpa [v, hWb] using
        (Tube.volume_carrier_eq_volume_carrier (𝒰'.cover.tube b i) (𝒰'.cover.tube b k₀))
    have h_m : ∀ i ∈ fibre (𝒰'.cover.indexSet b) pθ l, Wb i ≤ Ka := by
      intro i hi
      rw [fibre] at hi
      have hi₁ : i ∈ 𝒰'.cover.indexSet b := (Finset.mem_filter.mp hi).1
      have hi₂ : pθ i = l := (Finset.mem_filter.mp hi).2
      have hle : (𝒰'.cover.tube b i).toConvexSpaceBody
          ≤ (𝒰'.cover.tube a (pθ i)).toConvexSpaceBody := hcnp.parent.le_parent i hi₁
      simpa [hWb, hKa, hi₂] using hle
    apply ConvexSpaceBody.frostmanConstIn_subfamily_le (v := v) (κ := κ)
    · exact hfull_ne
    · exact hvol
    · exact h_m
    · exact hsub
    · exact hκ
    · exact hshr

end ml1Boot

end Kakeya
