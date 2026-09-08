/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Factoring
public import Kakeya.MultiScaleFac
public import Kakeya.Asymptotics

/-!
# Main Lemma 1, Case (ii): the named parent families read off the hierarchy

Alternative (ii) of `StickyKakeya.dividingScalesFrostman` is phrased on the *nodes* of the
hierarchy `𝒰'` it returns, while the factoring chain of Case (ii)
(`Kakeya.ml1Boot.exists_factorTwoScales`, `Kakeya.ml1Boot.multiplicity_le_middle`) consumes two
*named* parent families in the sense of `Kakeya.ml1Boot.IsParentFamily`.  This file is the
passage between the two, and it is the whole of it: the nodes at the fine index `b` are a parent
family for the leaves, and the nodes at the coarse index `a` are a parent family for those.

Both statements are blueprint `lem:ml1bootParentFamiliesFromNodesFine` and
`lem:ml1bootParentFamiliesFromNodesCoarse`, split in two because the coarse half needs two
hypotheses the fine half does not and no consumer needs them together.

Two further pieces of bookkeeping live here, for want of a better home and because both
outlived the grid-rounding layer they were first written for:
`Kakeya.ml1Boot.exists_majorityNodeRestriction`, which discards the leaves whose `b`-node lies
outside a majority set, and `Kakeya.ml1Boot.rescale_le_dilate_two`, the containment
`T_σ ⊆ 2 · T_{θ,l}` that `Kakeya.ml1Boot.IsCaseTwoData.lower` used to carry and that a
consumer now applies on the spot (blueprint `lem:ml1bootFreeScaleAnchor`).  The rest of that
layer —
the rounding of a free scale onto the grid, the rounded anchor and its transport — has been
deleted: `StickyKakeya.IsFrostmanDividingBlock.frostman_lower` is asserted at every real scale
of the `ε`-window and at every node of level `b`, so there is nothing left to round.

*Injectivity is a hypothesis.*  `Kakeya.ml1Boot.IsParentFamily` asks the parent tubes to be
pairwise distinct as convex bodies, which `Tube.UniformTubeSet` does not give: two node
indices may carry the same tube.  The caller supplies it, after deduplicating.

*Membership in `B₁` is not a conclusion.*  A node tube may stick out of `B₁` even though every
leaf inside it lies in `B₁`, so the blueprint's clause to that effect is carried by
`Kakeya.ml1Boot.IsCaseTwoData` and established from the geometry of the hierarchy, not here.

*The induced map on nodes.*  The blueprint names the coarse parent map `ϖ_{b→a}`; here it is
produced existentially, together with the identity `ϖ (assign b i) = assign a i` that
characterizes it on the nodes that carry a leaf.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody StickyKakeya Tube Filter Topology
open scoped BigOperators

namespace Kakeya

universe u

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- **The fine named parent family read off the hierarchy** (blueprint
`lem:ml1bootParentFamiliesFromNodes`, first half).

For a grid index `b ≤ N` of a hierarchy `𝒰'` on `𝕋|_{s'}`, the nodes at `b` together with the
assignment `assign b` form a parent family for `𝕋|_{s'}` at the scale `τ = ρ_b`.

`hinjFine` is the injectivity clause of `Kakeya.ml1Boot.IsParentFamily`, which
`Tube.UniformTubeSet.tube_injOn` does not supply (see the module docstring).  The
blueprint's clause "all members of the family are contained in `B₁`" is *not* a conclusion
here, for the reason recorded there as well.

The coarse half of the blueprint lemma is
`Kakeya.ml1Boot.exists_nodeParentFamilies_coarse`; it is a separate declaration because it
needs two hypotheses (`hnodes`, `hinjCoarse`) that this half does not, and no consumer needs
the two halves together. -/
theorem isParentFamily_nodes_fine {ι : Type*} {δ : NNReal} {s' : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu) {b : ℕ} (hb : b ≤ N)
    (hinjFine : Set.InjOn (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
      (𝒰'.cover.indexSet b)) :
    IsParentFamily s' T (𝒰'.cover.indexSet b) (𝒰'.cover.tube b) (𝒰'.cover.assign b) := by
  exact ⟨𝒰'.cover.assign_mem b hb, hinjFine, 𝒰'.cover.le_tube_assign b hb⟩

/-- **The coarse named parent family read off the hierarchy** (blueprint
`lem:ml1bootParentFamiliesFromNodes`, second half).

For a block `a ≤ b ≤ N` of a hierarchy `𝒰'`, the nodes at the coarse index `a` form a parent
family at `θ = ρ_a` for the fine node family of
`Kakeya.ml1Boot.isParentFamily_nodes_fine`, the parent map being the map `ϖ_{b→a}` on nodes
induced by the assignment; it is produced existentially, together with the identity
`ϖ (assign b i) = assign a i` that characterizes it on the nodes carrying a leaf.

`hnodes` says every `b`-node carries a leaf, which is what lets the induced map be defined at
all; `hinjCoarse` is the injectivity clause of `Kakeya.ml1Boot.IsParentFamily`.

`a ≤ b` and not `a < b`: the containment `P_b(k) ⊆ P_a(ϖ k)` is the chain of
`Tube.UniformTubeSet.tube_nested` from `a` up to `b`, which is the identity at
`a = b`. -/
theorem exists_nodeParentFamilies_coarse {ι : Type*} {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu) {a b : ℕ}
    (hab : a ≤ b) (hb : b ≤ N)
    (hnodes : ∀ k ∈ 𝒰'.cover.indexSet b, ∃ i ∈ s', 𝒰'.cover.assign b i = k)
    (hinjCoarse : Set.InjOn (fun k => (𝒰'.cover.tube a k).toConvexSpaceBody)
      (𝒰'.cover.indexSet a)) :
    ∃ pθ : ι → ι,
      (∀ i ∈ s', pθ (𝒰'.cover.assign b i) = 𝒰'.cover.assign a i) ∧
        IsParentFamily (𝒰'.cover.indexSet b) (𝒰'.cover.tube b)
          (𝒰'.cover.indexSet a) (𝒰'.cover.tube a) pθ := by
  classical
  let pθ : ι → ι := fun k =>
    if h : ∃ i, i ∈ s' ∧ 𝒰'.cover.assign b i = k then
      𝒰'.cover.assign a h.choose
    else k
  -- (1) well-definedness: descent along the nested cover, from level `b` down to `m`.
  have hd : ∀ (m d : ℕ), m + d ≤ b → ∀ i ∈ s', ∀ j ∈ s',
      𝒰'.cover.assign (m + d) i = 𝒰'.cover.assign (m + d) j →
      𝒰'.cover.assign m i = 𝒰'.cover.assign m j := by
    intro m d
    induction d with
    | zero =>
        intro h i hi j hj heq
        simpa using heq
    | succ d ih =>
        intro h i hi j hj heq
        have hmN : (m + d) + 1 ≤ N := by
          exact le_trans (by omega) hb
        rw [show m + (d + 1) = (m + d) + 1 by omega] at heq
        have hstep : 𝒰'.cover.assign (m + d) i = 𝒰'.cover.assign (m + d) j :=
          𝒰'.cover.nested (m + d) hmN i hi j hj heq
        exact ih (by omega) i hi j hj hstep
  have hnest : ∀ m : ℕ, m ≤ b → ∀ i ∈ s', ∀ j ∈ s',
      𝒰'.cover.assign b i = 𝒰'.cover.assign b j →
      𝒰'.cover.assign m i = 𝒰'.cover.assign m j := by
    intro m hm i hi j hj heq
    have hle : m + (b - m) ≤ b := by omega
    have heq' : 𝒰'.cover.assign (m + (b - m)) i = 𝒰'.cover.assign (m + (b - m)) j := by
      rw [← Nat.add_sub_cancel' hm] at heq
      exact heq
    exact hd m (b - m) hle i hi j hj heq'
  -- (2) the containing chain of node tubes, from level `b` down to `m`.
  have hcd : ∀ (m d : ℕ), m + d ≤ b → ∀ i ∈ s',
      (𝒰'.cover.tube (m + d) (𝒰'.cover.assign (m + d) i)).toConvexSpaceBody ≤
      (𝒰'.cover.tube m (𝒰'.cover.assign m i)).toConvexSpaceBody := by
    intro m d
    induction d with
    | zero =>
        intro h i hi
        exact le_rfl
    | succ d ih =>
        intro h i hi
        have hmN : (m + d) + 1 ≤ N := by
          exact le_trans (by omega) hb
        rw [show m + (d + 1) = (m + d) + 1 by omega]
        have hstep := 𝒰'.cover.tube_nested (m + d) hmN i hi
        have htail := ih (by omega) i hi
        exact le_trans hstep htail
  have hchain : ∀ m : ℕ, m ≤ b → ∀ i ∈ s',
      (𝒰'.cover.tube b (𝒰'.cover.assign b i)).toConvexSpaceBody ≤
      (𝒰'.cover.tube m (𝒰'.cover.assign m i)).toConvexSpaceBody := by
    intro m hm i hi
    have hle : m + (b - m) ≤ b := by omega
    have h' := hcd m (b - m) hle i hi
    rw [Nat.add_sub_cancel' hm] at h'
    exact h'
  -- the characterizing identity on the nodes that carry a leaf
  have hpres : ∀ i ∈ s', pθ (𝒰'.cover.assign b i) = 𝒰'.cover.assign a i := by
    intro i hi
    unfold pθ
    have h : ∃ j, j ∈ s' ∧ 𝒰'.cover.assign b j = 𝒰'.cover.assign b i := ⟨i, hi, rfl⟩
    rw [dif_pos h]
    exact hnest a hab h.choose h.choose_spec.1 i hi h.choose_spec.2
  -- the three clauses of `IsParentFamily`
  have hspan : ∀ k ∈ 𝒰'.cover.indexSet b, pθ k ∈ 𝒰'.cover.indexSet a := by
    intro k hk
    unfold pθ
    have h := hnodes k hk
    rw [dif_pos h]
    exact 𝒰'.cover.assign_mem a (le_trans hab hb) h.choose h.choose_spec.1
  have hleparent : ∀ k ∈ 𝒰'.cover.indexSet b,
      (𝒰'.cover.tube b k).toConvexSpaceBody ≤
      (𝒰'.cover.tube a (pθ k)).toConvexSpaceBody := by
    intro k hk
    unfold pθ
    have h := hnodes k hk
    rw [dif_pos h]
    have hbc : (𝒰'.cover.tube b (𝒰'.cover.assign b h.choose)).toConvexSpaceBody ≤
        (𝒰'.cover.tube a (𝒰'.cover.assign a h.choose)).toConvexSpaceBody :=
      hchain a hab h.choose h.choose_spec.1
    simpa [h.choose_spec.2] using hbc
  exact ⟨pθ, hpres, ⟨hspan, hinjCoarse, hleparent⟩⟩

/-- **Counting the leaves under a majority set of `b`-nodes** (blueprint
`lem:ml1bootMajorityNodeCount`).

If `F` is a majority set of `b`-nodes of a `Cu`-uniform hierarchy `𝒰'`, in the sense
`|𝒰'_b| ≤ Cds |F|`, then the union `s'' = ⋃_{j ∈ F} s'⟨j⟩` of the classes of `assign b` over
`F` consists of leaves assigned into `F`, and retains a `(Cu ^ 2 Cds)⁻¹` share of `s'`.

Neither `δ` nor any exponent occurs: this is pure counting, and the passage from the fixed
constant `Cu ^ 2 Cds` to a power of `δ` is
`Kakeya.ml1Boot.exists_majorityNodeRestriction` below.  The exponent `2` on `Cu` is forced:
the class bracket `Tube.UniformTubeSet.card_class_le` /
`Tube.UniformTubeSet.le_card_class` is two-sided with the *same* constant on both
sides, so comparing two classes at the same grid index through the branching number costs `Cu`
once on each side.

Both degenerate edges are covered by the statement as it stands: if `F = ∅` then `𝒰'_b = ∅`
and `s' = ∅`, and if the branching number vanishes then every class at index `b` is empty, so
again `s' = ∅`. -/
theorem card_le_majorityNodeCount {ι : Type*} [DecidableEq ι] {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {N b : ℕ} {Cu Cds : NNReal} (hCu : 1 ≤ Cu) (hCds : 1 ≤ Cds)
    (𝒰' : UniformTubeSet s' T N Cu) (hb : b ≤ N) {F : Finset ι}
    (hF : F ⊆ 𝒰'.cover.indexSet b)
    (hmaj : ((𝒰'.cover.indexSet b).card : ℝ) ≤ (Cds : ℝ) * (F.card : ℝ)) :
    (∀ i ∈ F.biUnion fun j => coverClass s' (𝒰'.cover.assign b) j,
        𝒰'.cover.assign b i ∈ F) ∧
      (s'.card : ℝ) ≤ (Cu : ℝ) ^ 2 * (Cds : ℝ) *
        ((F.biUnion fun j => coverClass s' (𝒰'.cover.assign b) j).card : ℝ) := by
  classical
  let J := 𝒰'.cover.indexSet b
  let cls : ι → Finset ι := fun j => coverClass s' (𝒰'.cover.assign b) j
  let s'' : Finset ι := F.biUnion cls
  -- The classes at index `b` are pairwise disjoint (the assignment is a function).
  have hpd : (J : Set ι).PairwiseDisjoint cls := by
    intro j1 hj1 j2 hj2 hne
    change Disjoint (cls j1) (cls j2)
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have hm1 : i ∈ s' ∧ 𝒰'.cover.assign b i = j1 := by
      simpa [cls, coverClass] using hi1
    have hm2 : i ∈ s' ∧ 𝒰'.cover.assign b i = j2 := by
      simpa [cls, coverClass] using hi2
    exact hne (hm1.2.symm.trans hm2.2)
  -- `s'` is the disjoint union of the classes over all nodes at index `b`.
  have hs' : s' = J.biUnion cls := by
    ext i
    constructor
    · intro hi
      rw [Finset.mem_biUnion]
      exact ⟨𝒰'.cover.assign b i, 𝒰'.cover.assign_mem b hb i hi,
        by simpa [cls, coverClass] using hi⟩
    · intro hi
      rw [Finset.mem_biUnion] at hi
      rcases hi with ⟨j, hj, hij⟩
      exact (by simpa [cls, coverClass] using hij : i ∈ s' ∧ 𝒰'.cover.assign b i = j).1
  -- cardinality of `s'` as the sum over the classes.
  have hs'card : (s'.card : ℝ) = ∑ j ∈ J, ((cls j).card : ℝ) := by
    have hc : s'.card = ∑ j ∈ J, (cls j).card := by
      rw [hs']
      exact Finset.card_biUnion hpd
    exact_mod_cast hc
  -- upper bound: each class at index `b` has cardinality at most `Cu * branchingN b`.
  have hs'le : (s'.card : ℝ) ≤ (J.card : ℝ) * (Cu : ℝ) * (𝒰'.branchingN b : ℝ) := by
    calc
      (s'.card : ℝ) = ∑ j ∈ J, ((cls j).card : ℝ) := hs'card
      _ ≤ ∑ j ∈ J, ((Cu : ℝ) * (𝒰'.branchingN b : ℝ)) := by
        exact Finset.sum_le_sum (by
          intro j hj
          exact_mod_cast 𝒰'.card_class_le b hb j hj)
      _ = (J.card : ℝ) * (Cu : ℝ) * (𝒰'.branchingN b : ℝ) := by
        simp; ring
  -- cardinality of `s''` as the sum over `F`.
  have hs''card : (s''.card : ℝ) = ∑ j ∈ F, ((cls j).card : ℝ) := by
    have hpdF : (F : Set ι).PairwiseDisjoint cls := by
      intro j1 hj1 j2 hj2 hne
      exact hpd (hF hj1) (hF hj2) hne
    have hc : s''.card = ∑ j ∈ F, (cls j).card := by
      dsimp [s'']
      exact Finset.card_biUnion hpdF
    exact_mod_cast hc
  -- lower bound: each class over `F` has cardinality at least `branchingN b`.
  have hs''ge : (F.card : ℝ) * (𝒰'.branchingN b : ℝ) ≤ (Cu : ℝ) * (s''.card : ℝ) := by
    calc
      (F.card : ℝ) * (𝒰'.branchingN b : ℝ) = ∑ j ∈ F, (𝒰'.branchingN b : ℝ) := by
        simp
      _ ≤ ∑ j ∈ F, ((Cu : ℝ) * ((cls j).card : ℝ)) := by
        exact Finset.sum_le_sum (by
          intro j hj
          exact_mod_cast 𝒰'.le_card_class b hb j (hF hj))
      _ = (Cu : ℝ) * ∑ j ∈ F, ((cls j).card : ℝ) := by
        rw [← Finset.mul_sum]
      _ = (Cu : ℝ) * (s''.card : ℝ) := by
        rw [hs''card]
  -- combine: `|s'| ≤ |J| Cu N_b ≤ Cds |F| Cu N_b = Cds Cu (|F| N_b) ≤ Cds Cu (Cu |s''|)`.
  have hCu0 : (0 : ℝ) ≤ (Cu : ℝ) := by exact_mod_cast (zero_le_one.trans hCu)
  have hCds0 : (0 : ℝ) ≤ (Cds : ℝ) := by exact_mod_cast (zero_le_one.trans hCds)
  have hb0 : (0 : ℝ) ≤ (𝒰'.branchingN b : ℝ) := by positivity
  constructor
  · intro i hi
    rw [Finset.mem_biUnion] at hi
    rcases hi with ⟨j, hj, hij⟩
    have hmem : i ∈ s' ∧ 𝒰'.cover.assign b i = j := by
      simpa [cls, coverClass] using hij
    rw [hmem.2]
    exact hj
  · calc
      (s'.card : ℝ) ≤ (J.card : ℝ) * (Cu : ℝ) * (𝒰'.branchingN b : ℝ) := hs'le
      _ ≤ (Cds : ℝ) * (F.card : ℝ) * (Cu : ℝ) * (𝒰'.branchingN b : ℝ) := by
        have hnonneg : (0 : ℝ) ≤ (Cu : ℝ) * (𝒰'.branchingN b : ℝ) :=
          mul_nonneg hCu0 hb0
        have hstep := mul_le_mul_of_nonneg_right hmaj hnonneg
        dsimp [J] at hstep ⊢
        ring_nf at hstep ⊢
        exact hstep
      _ = (Cds : ℝ) * (Cu : ℝ) * ((F.card : ℝ) * (𝒰'.branchingN b : ℝ)) := by
        ring
      _ ≤ (Cds : ℝ) * (Cu : ℝ) * ((Cu : ℝ) * (s''.card : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hs''ge (mul_nonneg hCds0 hCu0)
      _ = (Cu : ℝ) ^ 2 * (Cds : ℝ) * (s''.card : ℝ) := by
        ring

/-- **Discarding the `b`-nodes outside a majority set** (blueprint
`lem:ml1bootMajorityNodeDiscard`).

Let `ε' > 0`.  Then for all sufficiently small `δ > 0`: if `F` is a majority set of `b`-nodes of
a `Cu`-uniform hierarchy `𝒰'`, in the sense `|𝒰'_b| ≤ Cds |F|`, then there is `s'' ⊆ s'`
retaining all but a `δ ^ (-ε')` share of `s'` and all of whose members are assigned to a node
of `F`.

The threshold on `δ` depends on `Cu`, `Cds` and `ε'` only, all three of which are fixed before
`δ`; that is what lets the two constants be absorbed into `δ ^ (-ε')`.  "Every `b`-node meeting
`s''` lies in `F`" is rendered as `∀ i ∈ s'', assign b i ∈ F`, which is what taking `s''` to be
the union of the classes over `F` gives.

The majority set of the superseded, `δ`-independent-grid form of alternative (ii) of GWZ
Lemma 7.7(A) is gone — `StickyKakeya.IsFrostmanDividingBlock` asserts its lower bound at every
node — but this is node bookkeeping about an arbitrary majority set and is used in its own
right, in the passage from the retained parent families back to the leaves. -/
theorem exists_majorityNodeRestriction {Cu Cds : NNReal} (hCu : 1 ≤ Cu) (hCds : 1 ≤ Cds)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} {s' : Finset ι} {T : ι → Tube δ E} {N b : ℕ}
        (𝒰' : UniformTubeSet s' T N Cu), b ≤ N →
        ∀ F ⊆ 𝒰'.cover.indexSet b,
          ((𝒰'.cover.indexSet b).card : ℝ) ≤ (Cds : ℝ) * (F.card : ℝ) →
          ∃ s'' ⊆ s', ((s'.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s''.card : ℝ)) ∧
            ∀ i ∈ s'', 𝒰'.cover.assign b i ∈ F := by
  have hCu_pos : (0 : NNReal) < Cu := lt_of_lt_of_le (by norm_num) hCu
  have hCds_pos : (0 : NNReal) < Cds := lt_of_lt_of_le (by norm_num) hCds
  have hC : 0 < (Cu : ℝ)^2 * (Cds : ℝ) := by
    rw [pow_two]
    exact mul_pos (mul_pos (by exact_mod_cast hCu_pos) (by exact_mod_cast hCu_pos))
      (by exact_mod_cast hCds_pos)
  filter_upwards [nnreal_eventually_of_real_eventually
      (absorb_const_le_rpow_neg hC hε')] with δ hδ
  intro ι s' T N b 𝒰' hb F hF hcard
  classical
  let s'' : Finset ι := F.biUnion fun j => coverClass s' (𝒰'.cover.assign b) j
  have hmem := (card_le_majorityNodeCount hCu hCds 𝒰' hb hF hcard).2
  have hassign := (card_le_majorityNodeCount hCu hCds 𝒰' hb hF hcard).1
  refine ⟨s'', ?_, ?_, ?_⟩
  · intro i hi
    dsimp [s''] at hi
    rcases (Finset.mem_biUnion.mp hi) with ⟨j, hjF, hji⟩
    have hji' : i ∈ s' ∧ 𝒰'.cover.assign b i = j := by simpa [coverClass] using hji
    exact hji'.1
  · dsimp [s'']
    calc
      (s'.card : ℝ) ≤ ((Cu : ℝ)^2 * (Cds : ℝ)) *
          ((F.biUnion fun j => coverClass s' (𝒰'.cover.assign b) j).card : ℝ) := by
            exact hmem
      _ ≤ (δ : ℝ) ^ (-ε') *
          ((F.biUnion fun j => coverClass s' (𝒰'.cover.assign b) j).card : ℝ) :=
        mul_le_mul_of_nonneg_right hδ (by positivity)
  · intro i hi
    dsimp [s''] at hi
    exact hassign i hi

/-- **A refinement of the leaves retains a share of the `b`-nodes** (blueprint
`lem:ml1bootNodeShareFromLeafRefinement`).

Let `ε' > 0`.  Then for all sufficiently small `δ`: if `s₀ ⊆ s'` retains all but a `δ ^ (-ε')`
share of `s'`, then the set `G = assign b '' s₀` of `b`-nodes *met* by `s₀` retains all but a
`δ ^ (-2 ε')` share of `𝒰'_b`.

This is the same class-bracket count that `Kakeya.ml1Boot.card_le_majorityNodeCount` performs,
run in the opposite direction: there a subset of the *nodes* is turned into a subset of the
leaves retaining a share, here a subset of the *leaves* is turned into a subset of the nodes
retaining a share.  The proof produces the sharper `|𝒰'_b| ≤ Cu ^ 2 * δ ^ (-ε') * |G|`, valid
for every `δ`; the smallness of `δ` is used only to absorb `Cu ^ 2` — fixed before `δ` — into
the second factor `δ ^ (-ε')`, which is why the stated exponent is `-2 ε'`.  The exponent `2`
on `Cu` is forced, and for the same reason as in
`Kakeya.ml1Boot.card_le_majorityNodeCount`: the class bracket
`Tube.UniformTubeSet.card_class_le` / `.le_card_class` is two-sided with the same
constant on both sides, so comparing two classes at the same grid index through the branching
number costs `Cu` once on each side.

**This lemma is currently unused.**  It was stated as the share hypothesis of the retired
refinement-stability assumption (blueprint `prop:ml1bootLowerFrostmanStable`), whose sole
consumer was `Kakeya.ml1Boot.repairLower`.  That assumption is refuted and undeliverable
(blueprint `note:ml1bootLowerFrostmanRetired`) and has been deleted, and `repairLower` is now a
read-off of `StickyKakeya.IsFrostmanDividingBlock.frostman_lower` at the *unrefined* node
family carrying no share hypothesis, so nothing consumes this bound any more.  It is true and
proved and is kept: it is the only statement in the Case (ii) chain converting a share of the
*leaves* into a share of the *parents*.  Neither
`Kakeya.ml1Boot.exists_essDistinct_parentFamily` nor `Kakeya.ml1Boot.exists_uniformizePair`
says anything about the cardinality of a retained *parent* index set, and a parent-map fibre
carries no share guarantee at all — a refinement of the leaves retaining a `δ ^ ε'` share may
empty an arbitrary fibre.

## The nonemptiness hypothesis on `s₀` is necessary

Without `s₀.Nonempty` the lemma is **false**, and not only at an uninteresting edge.
`Tube.UniformTubeSet` nowhere requires a node to carry a leaf, so take `s' = ∅`, let
`𝒰'.cover.indexSet b` be a single node and let `𝒰'.branchingN b = 0`.  Every clause of that
structure holds: the bounded-overlap clause quantifies over members of `s' = ∅` and is vacuous,
and both halves of the class bracket read `0 ≤ Cu * 0`.  The refinement hypothesis reads
`0 ≤ 0`, while `G = ∅` and the conclusion demands `1 ≤ δ ^ (-2 ε') * 0 = 0`.

Assuming `s₀.Nonempty` excludes this and is exactly enough: from a member of `s₀ ⊆ s'` some
class at index `b` has size at least `1`, and the *upper* half of the bracket
`Tube.UniformTubeSet.card_class_le` forces `𝒰'.branchingN b ≥ 1 / Cu > 0`, which is
what legitimises the division by the branching number.  The consumer supplies the hypothesis:
the Case (ii) chain runs on nonempty families. -/
theorem card_le_nodeShare_of_leafRefinement {Cu : NNReal} (hCu : 1 ≤ Cu) {ε' : ℝ}
    (hε' : 0 < ε') :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} [DecidableEq ι] {s' : Finset ι} {T : ι → Tube δ E} {N b : ℕ}
        (𝒰' : UniformTubeSet s' T N Cu), b ≤ N →
        ∀ s₀ ⊆ s', s₀.Nonempty → (s'.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s₀.card : ℝ) →
          ((𝒰'.cover.indexSet b).card : ℝ)
            ≤ (δ : ℝ) ^ (-2 * ε') * ((s₀.image (𝒰'.cover.assign b)).card : ℝ) := by
  have hCu_pos : (0 : NNReal) < Cu := lt_of_lt_of_le (by norm_num) hCu
  have hC : 0 < (Cu : ℝ)^2 := by
    rw [pow_two]
    exact mul_pos (by exact_mod_cast hCu_pos) (by exact_mod_cast hCu_pos)
  filter_upwards [nnreal_eventually_of_real_eventually
      (absorb_const_le_rpow_neg hC hε'), self_mem_nhdsWithin] with δ hδ hδ0
  have hδpos : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  classical
  intro ι _ s' T N b 𝒰' hb s₀ hss₀ hne hsc
  let J : Finset ι := 𝒰'.cover.indexSet b
  let cls : ι → Finset ι := fun j => coverClass s' (𝒰'.cover.assign b) j
  let G : Finset ι := s₀.image (𝒰'.cover.assign b)
  -- the classes at index `b` are pairwise disjoint and partition `s'`
  have hClose : (J : Set ι).PairwiseDisjoint cls := by
    intro j1 h1 j2 h2_ hn
    change Disjoint (cls j1) (cls j2)
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have hq1 : i ∈ s' ∧ 𝒰'.cover.assign b i = j1 := by
      simpa [cls, coverClass] using hi1
    have hq2 : i ∈ s' ∧ 𝒰'.cover.assign b i = j2 := by
      simpa [cls, coverClass] using hi2
    exact hn (hq1.2.symm.trans hq2.2)
  have hPart : s' = J.biUnion cls := by
    ext i
    constructor
    · intro hi
      rw [Finset.mem_biUnion]
      exact ⟨𝒰'.cover.assign b i, 𝒰'.cover.assign_mem b hb i hi,
        by simp [cls, coverClass, hi]⟩
    · intro hi
      rw [Finset.mem_biUnion] at hi
      rcases hi with ⟨j, hj, hij⟩
      exact (by simpa [cls, coverClass] using hij : i ∈ s' ∧ 𝒰'.cover.assign b i = j).1
  have hScr : (s'.card : ℝ) = ∑ j ∈ J, ((cls j).card : ℝ) := by
    have h0 : s'.card = ∑ j ∈ J, (cls j).card := by
      rw [hPart]
      exact Finset.card_biUnion hClose
    exact_mod_cast h0
  -- strict positivity of the branching number, from an element of `s₀`
  rcases hne with ⟨i, hi₀⟩
  have hi' : i ∈ s' := hss₀ hi₀
  have hjJ : 𝒰'.cover.assign b i ∈ J := 𝒰'.cover.assign_mem b hb i hi'
  have hi_c : i ∈ cls (𝒰'.cover.assign b i) := by
    simp [cls, coverClass, hi']
  have hcls_pos : 0 < (cls (𝒰'.cover.assign b i)).card :=
    Finset.card_pos.mpr ⟨i, hi_c⟩
  have hOne : (1 : ℝ) ≤ (Cu : ℝ) * (𝒰'.branchingN b : ℝ) := by
    have hge : (1 : NNReal) ≤ (cls (𝒰'.cover.assign b i)).card := by
      exact_mod_cast (Nat.succ_le_of_lt hcls_pos)
    have hle : ((cls (𝒰'.cover.assign b i)).card : NNReal) ≤ Cu * 𝒰'.branchingN b :=
      𝒰'.card_class_le b hb (𝒰'.cover.assign b i) hjJ
    exact_mod_cast (le_trans hge hle)
  -- from `1 ≤ Cu * N_b` and `Cu ≥ 1`, the branching number is strictly positive
  have hbN_pos : 0 < (𝒰'.branchingN b : ℝ) := by
    have hcm : 0 < (Cu : ℝ) * (𝒰'.branchingN b : ℝ) := by
      exact lt_of_lt_of_le (by norm_num) hOne
    exact pos_of_mul_pos_right hcm (by positivity)
  -- `G ⊆ J`, and `s₀` is covered by the classes over `G`
  have hGJ : G ⊆ J := by
    intro k hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨i, hi, rfl⟩
    exact 𝒰'.cover.assign_mem b hb i (hss₀ hi)
  have hsubS : s₀ ⊆ G.biUnion cls := by
    intro k hk
    have hkG : 𝒰'.cover.assign b k ∈ G := by
      rw [Finset.mem_image]
      exact ⟨k, hk, rfl⟩
    rw [Finset.mem_biUnion]
    exact ⟨𝒰'.cover.assign b k, hkG, by simp [cls, coverClass, hss₀ hk]⟩
  have hpdG : (G : Set ι).PairwiseDisjoint cls := by
    intro j1 hj1 j2 hj2 hn
    exact hClose (hGJ hj1) (hGJ hj2) hn
  have hs0le : (s₀.card : ℝ) ≤ ∑ k ∈ G, ((cls k).card : ℝ) := by
    have hc : s₀.card ≤ ∑ k ∈ G, (cls k).card := by
      rw [← Finset.card_biUnion hpdG]
      exact Finset.card_le_card hsubS
    exact_mod_cast hc
  -- upper bound: each class over `G` has cardinality at most `Cu * N_b`
  have hsumG : ∑ k ∈ G, ((cls k).card : ℝ) ≤
      (Cu : ℝ) * (𝒰'.branchingN b : ℝ) * (G.card : ℝ) := by
    calc
      ∑ k ∈ G, ((cls k).card : ℝ)
          ≤ ∑ k ∈ G, ((Cu : ℝ) * (𝒰'.branchingN b : ℝ)) := by
        exact Finset.sum_le_sum (by
          intro k hk
          exact_mod_cast 𝒰'.card_class_le b hb k (hGJ hk))
      _ = (Cu : ℝ) * (𝒰'.branchingN b : ℝ) * (G.card : ℝ) := by
        simp
        ring
  -- `|s'| ≤ δ^(-ε') * Cu * N_b * |G|`
  have hchain : (s'.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (Cu : ℝ) * (𝒰'.branchingN b : ℝ)
      * (G.card : ℝ) := by
    calc
      (s'.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s₀.card : ℝ) := hsc
      _ ≤ (δ : ℝ) ^ (-ε') * ∑ k ∈ G, ((cls k).card : ℝ) := by
        exact mul_le_mul_of_nonneg_left hs0le (Real.rpow_nonneg (le_of_lt hδpos) (-ε'))
      _ ≤ (δ : ℝ) ^ (-ε') * ((Cu : ℝ) * (𝒰'.branchingN b : ℝ) * (G.card : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hsumG (Real.rpow_nonneg (le_of_lt hδpos) (-ε'))
      _ = (δ : ℝ) ^ (-ε') * (Cu : ℝ) * (𝒰'.branchingN b : ℝ) * (G.card : ℝ) := by
        ring
  -- lower bound: `|J| * N_b ≤ Cu * |s'|`, then divide by the positive `N_b`
  have hMul : (J.card : ℝ) * (𝒰'.branchingN b : ℝ) ≤ (Cu : ℝ) * (s'.card : ℝ) := by
    calc
      (J.card : ℝ) * (𝒰'.branchingN b : ℝ) = ∑ j ∈ J, (𝒰'.branchingN b : ℝ) := by
        simp
      _ ≤ ∑ j ∈ J, ((Cu : ℝ) * ((cls j).card : ℝ)) := by
        exact Finset.sum_le_sum (by
          intro j hj
          exact_mod_cast 𝒰'.le_card_class b hb j hj)
      _ = (Cu : ℝ) * ∑ j ∈ J, ((cls j).card : ℝ) := by
        rw [← Finset.mul_sum]
      _ = (Cu : ℝ) * (s'.card : ℝ) := by
        rw [hScr]
  have hDiv : (J.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (Cu : ℝ) ^ 2 * (G.card : ℝ) := by
    have h1 : (J.card : ℝ) * (𝒰'.branchingN b : ℝ) ≤
        ((δ : ℝ) ^ (-ε') * (Cu : ℝ) ^ 2 * (G.card : ℝ))
          * (𝒰'.branchingN b : ℝ) := by
      calc
        (J.card : ℝ) * (𝒰'.branchingN b : ℝ) ≤ (Cu : ℝ) * (s'.card : ℝ) := hMul
        _ ≤ (Cu : ℝ) * ((δ : ℝ) ^ (-ε') * (Cu : ℝ) * (𝒰'.branchingN b : ℝ)
            * (G.card : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hchain (by positivity)
        _ = ((δ : ℝ) ^ (-ε') * (Cu : ℝ) ^ 2 * (G.card : ℝ))
            * (𝒰'.branchingN b : ℝ) := by
          ring
    exact le_of_mul_le_mul_right h1 hbN_pos
  -- absorb `(Cu : ℝ) ^ 2 ≤ δ^(-ε')`, then `δ^(-ε') * δ^(-ε') = δ^(-2ε')`
  have hfin : (J.card : ℝ) ≤ (δ : ℝ) ^ (-2 * ε') * (G.card : ℝ) := by
    calc
      (J.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (Cu : ℝ) ^ 2 * (G.card : ℝ) := hDiv
      _ = (Cu : ℝ) ^ 2 * (δ : ℝ) ^ (-ε') * (G.card : ℝ) := by
        ring
      _ ≤ (δ : ℝ) ^ (-ε') * (δ : ℝ) ^ (-ε') * (G.card : ℝ) := by
        have hNonneg1 : 0 ≤ (δ : ℝ) ^ (-ε') := by
          exact Real.rpow_nonneg (le_of_lt hδpos) (-ε')
        have hNonneg2 : 0 ≤ (G.card : ℝ) := by exact_mod_cast (Nat.zero_le (G.card))
        have hm := mul_le_mul_of_nonneg_right hδ (mul_nonneg hNonneg1 hNonneg2)
        calc
          (Cu : ℝ) ^ 2 * (δ : ℝ) ^ (-ε') * (G.card : ℝ)
              = (Cu : ℝ) ^ 2 * ((δ : ℝ) ^ (-ε') * (G.card : ℝ)) := by ring
          _ ≤ (δ : ℝ) ^ (-ε') * ((δ : ℝ) ^ (-ε') * (G.card : ℝ)) := hm
          _ = (δ : ℝ) ^ (-ε') * (δ : ℝ) ^ (-ε') * (G.card : ℝ) := by ring
      _ = (δ : ℝ) ^ (-2 * ε') * (G.card : ℝ) := by
        have hpow : (δ : ℝ) ^ (-ε') * (δ : ℝ) ^ (-ε') =
            (δ : ℝ) ^ (-2 * ε') := by
          rw [← Real.rpow_add hδpos]
          congr 1
          ring
        rw [hpow]
  simpa [J, G] using hfin

/-- **The `σ`-tube sits in the `2`-dilate of the coarse node** (blueprint
`lem:ml1bootAnchorDilateContainment`).

If the core of a tube `V` lies in a tube `W` of radius `ρ_a` and `σ ≤ ρ_a`, then the
`σ`-rescaling of `V` — the `σ`-tube with the same core — lies in the `2`-dilate of `W`.  Every
point of `V.rescale σ` is within `σ` of `core V ⊆ W`, hence within `ρ_a + σ ≤ 2 ρ_a` of
`core W`, and the homothety of ratio `2` enlarges the core as well as the radius.

The containment is in the `2`-dilate and not in `W` itself, because `V` may already touch the
boundary of `W`; this is not an artefact that shrinking `σ` removes.

It is exactly the containment `T_σ ⊆ 2 · T_{θ,l}` that `Kakeya.ml1Boot.IsCaseTwoData.lower`
used to assert alongside its Frostman bound (blueprint `lem:ml1bootFreeScaleAnchor`).  That
field no longer names a coarse index, so the containment is now supplied here on demand; this
is why the lemma outlived both the grid-rounding layer it was first written for and the
restatement of item (iv) at the unrefined node family. -/
theorem rescale_le_dilate_two {ρc ρa σ : NNReal} (V : Tube ρc E) (W : Tube ρa E)
    (hcore : segment ℝ V.x V.y ⊆ W.carrier) (hσ : σ ≤ ρa) :
    (V.rescale σ).toConvexSpaceBody ≤ Tube.dilate W 2 := by
  intro z hz
  change z ∈ (V.rescale σ).carrier at hz
  have hxσ : (V.rescale σ).x = V.x := by simp [Tube.rescale]
  have hyσ : (V.rescale σ).y = V.y := by simp [Tube.rescale]
  rw [(V.rescale σ).carrier_eq] at hz
  rw [Set.mem_iUnion₂] at hz
  rw [hxσ, hyσ] at hz
  obtain ⟨p, hp_seg, h_zp⟩ := hz
  rw [Metric.mem_closedBall] at h_zp
  have hpW : p ∈ W.carrier := hcore hp_seg
  rw [W.carrier_eq] at hpW
  rw [Set.mem_iUnion₂] at hpW
  obtain ⟨q, hq_seg, h_pq⟩ := hpW
  rw [Metric.mem_closedBall] at h_pq
  rw [segment_eq_image'] at hq_seg
  obtain ⟨u, hu, hq_eq⟩ := hq_seg
  let s : ℝ := u - 1 / 2
  have hsq : q = W.center + s • W.direction := by
    rw [← hq_eq]
    dsimp [s]
    have hc : W.center = (1 / 2 : ℝ) • (W.x + W.y) := by
      change midpoint ℝ W.x W.y = (1 / 2 : ℝ) • (W.x + W.y)
      rw [midpoint_eq_smul_add]
      norm_num
    rw [hc]
    module
  have hs : |s| ≤ 1 := by
    dsimp [s]
    rw [abs_le]
    constructor <;> linarith [hu.1, hu.2]
  have hz2 : dist z (W.center + s • W.direction) ≤ 2 * (ρa : ℝ) := by
    rw [← hsq]
    calc
      dist z q ≤ dist z p + dist p q := dist_triangle z p q
      _ ≤ (σ : ℝ) + (ρa : ℝ) := add_le_add h_zp h_pq
      _ ≤ 2 * (ρa : ℝ) := by
        linarith [show (σ : ℝ) ≤ (ρa : ℝ) from by exact_mod_cast hσ]
  exact Tube.mem_dilate_of_dist_axis_le (T := W) (C := 2)
    (hC := (by norm_num : (0 : ℝ) < 2)) (s := s) (hs := (by simpa using hs)) (hz := hz2)

/-- **The `σ`-rescale sits in the `2ρ_a`-rescale of the coarse node** (blueprint
`lem:ml1bootEnlargementRadius`, the radius-rescaling form of enlargement item (b)).

Same hypotheses as `Kakeya.ml1Boot.rescale_le_dilate_two`, and the same proof stopped one line
earlier: every point of `V.rescale σ` is within `σ` of `core V ⊆ W`, hence within
`ρ_a + σ ≤ 2 ρ_a` of `core W`, and `W.rescale (2 * ρ_a)` *is* by definition the set of points
within `2 ρ_a` of `core W`.  No lower bound on either radius, and no relation between `ρ_c` and
`ρ_a`, is used; the radius `ρ_c` of `V` enters only through the fact that a rescaling keeps the
core.

This is the conclusion the Step 5a consumers cite: they need the *concentric radius-rescaling*
`W^{(2ρ_a)}`, whereas `Kakeya.ml1Boot.rescale_le_dilate_two` delivers only the weaker homothety
`Tube.dilate W 2`, which lengthens the core as well.  It is added *beside* that lemma rather than
replacing it, so that its existing consumers continue to typecheck; the homothety form is in any
case recovered from this one. -/
theorem rescale_le_rescale_two {ρc ρa σ : NNReal} (V : Tube ρc E) (W : Tube ρa E)
    (hcore : segment ℝ V.x V.y ⊆ W.carrier) (hσ : σ ≤ ρa) :
    (V.rescale σ).toConvexSpaceBody ≤ (W.rescale (2 * ρa)).toConvexSpaceBody := by
  intro z hz
  change z ∈ (V.rescale σ).carrier at hz
  have hxσ : (V.rescale σ).x = V.x := by simp [Tube.rescale]
  have hyσ : (V.rescale σ).y = V.y := by simp [Tube.rescale]
  rw [(V.rescale σ).carrier_eq] at hz
  rw [Set.mem_iUnion₂] at hz
  rw [hxσ, hyσ] at hz
  obtain ⟨p, hp_seg, h_zp⟩ := hz
  rw [Metric.mem_closedBall] at h_zp
  have hpW : p ∈ W.carrier := hcore hp_seg
  rw [W.carrier_eq] at hpW
  rw [Set.mem_iUnion₂] at hpW
  obtain ⟨q, hq_seg, h_pq⟩ := hpW
  rw [Metric.mem_closedBall] at h_pq
  have hzq : dist z q ≤ 2 * (ρa : ℝ) := by
    calc
      dist z q ≤ dist z p + dist p q := dist_triangle z p q
      _ ≤ (σ : ℝ) + (ρa : ℝ) := add_le_add h_zp h_pq
      _ ≤ 2 * (ρa : ℝ) := by
        linarith [show (σ : ℝ) ≤ (ρa : ℝ) from by exact_mod_cast hσ]
  change z ∈ (W.rescale (2 * ρa)).carrier
  have hxW : (W.rescale (2 * ρa)).x = W.x := by simp [Tube.rescale]
  have hyW : (W.rescale (2 * ρa)).y = W.y := by simp [Tube.rescale]
  rw [(W.rescale (2 * ρa)).carrier_eq]
  rw [Set.mem_iUnion₂]
  rw [hxW, hyW]
  exact ⟨q, hq_seg, Metric.mem_closedBall.mpr hzq⟩

/-! ### The three seams between the dichotomy's spelling and Section 8's -/

/-- **The containment family of the node tubes is the hierarchy's `nodesIn`.**

`StickyKakeya.IsFrostmanDividingBlock` measures the nodes lying in a body with
`Tube.UniformTubeSet.nodesIn`, while `Kakeya.ml1Boot.IsFreeScaleLowerBound` and
`Kakeya.ml1Boot.IsCaseTwoRawUpper.mid` measure them with `Kakeya.familyIn` at the level-`b`
index set.  The two are the same `Finset.filter` and differ only in the decidability instance;
this is the single place where that seam is crossed. -/
theorem familyIn_indexSet_eq_nodesIn {ι : Type*} {δ : NNReal} {s' : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu) (b : ℕ) (K : ConvexSpaceBody E) :
    familyIn (𝒰'.cover.indexSet b) (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K
      = 𝒰'.nodesIn b K := by
  rfl

/-- **The parent-map fibre of an assignment is the cover class of the dichotomy.**

`StickyKakeya.IsFrostmanDividingBlock.frostman_leaves` measures the leaves of a node with
`Tube.coverClass`, while `Kakeya.ml1Boot.IsCaseTwoRawUpper.fine` measures them with the
parent-map fibre `Kakeya.ml1Boot.fibre` of the assignment.  Again one `Finset.filter` under two
decidability instances. -/
theorem fibre_eq_coverClass {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : ι → ι) (k : ι) :
    fibre s q k = coverClass s q k := by
  simp only [fibre, coverClass]
  exact (Finset.filter_congr_decidable s (fun i => q i = k)
    (Classical.decPred fun i => q i = k)).symm

/-- **The loss of the dichotomy is below `δ ^ (-ε')` for all small `δ`** (blueprint
`lem:ml1bootDichotomyLossAbsorb`).

Every bullet of `StickyKakeya.IsFrostmanDividingBlock` carries the factor
`Cds * StickyKakeya.totalLoss Cds Kds cds δ`, with `Cds`, `Kds`, `cds` fixed before `δ`.  The
loss is subpolynomial (`StickyKakeya.exists_threshold_totalLoss_le`) and the constant is fixed,
so their product is below any fixed negative power of `δ` eventually — which is how every Case
(ii) read-off turns the displayed loss into `δ ^ (∓ ε')`.

No lower bound on `Cds` is assumed: `StickyKakeya.gridLoss` is monotone in its constant, so a
`Cds < 1` is handled by comparing against `Cds + 1`. -/
theorem eventually_dichotomyLoss_le (Cds : NNReal) (Kds cds : ℕ) {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      (Cds : ENNReal) * totalLoss Cds Kds cds δ ≤ (δ : ENNReal) ^ (-ε') := by
  have hε2 : 0 < ε' / 2 := by linarith
  have hA : (1 : NNReal) ≤ Cds + 1 := by
    calc
      (1 : NNReal) = (0 : NNReal) + 1 := by simp
      _ ≤ Cds + 1 := by
        exact add_le_add (zero_le (a := Cds)) le_rfl
  obtain ⟨δ₀, hδ₀pos, hδ₀le1, hthr⟩ :=
    StickyKakeya.exists_threshold_totalLoss_le (Cds + 1) hA Kds cds (ε' / 2) hε2
  have hδ₀R : (0 : ℝ) < (δ₀ : ℝ) := by exact_mod_cast hδ₀pos
  have hAposR : (0 : ℝ) < (Cds : ℝ) + 1 := by
    have h : (0 : ℝ) ≤ (Cds : ℝ) := by positivity
    linarith
  -- eventually: 0 < δ, δ ≤ δ₀, and the fixed constant absorbed into δ^(-ε'/2)
  have hδle₀ev : ∀ᶠ δ : NNReal in 𝓝[>] 0, δ ≤ δ₀ := by
    have hℤ : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal), (δ : ℝ) ≤ (δ₀ : ℝ) :=
      NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.eventually
        (eventually_le_nhds hδ₀R)
    filter_upwards [hℤ] with δ hδ
    exact NNReal.coe_le_coe.mp hδ
  filter_upwards [nnreal_eventually_of_real_eventually
      (Kakeya.absorb_const_le_rpow_neg hAposR hε2),
    self_mem_nhdsWithin, hδle₀ev] with δ hcst hδ0 hδle₀
  have hδpos : (0 : NNReal) < δ := hδ0
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδpos
  have hδle1 : δ ≤ 1 := hδle₀.trans hδ₀le1
  have hcst_ℝ : (Cds : ℝ) + 1 ≤ (δ : ℝ) ^ (-(ε' / 2)) := by
    simpa [neg_div, div_neg] using hcst
  -- gridLoss is monotone in its positive constant
  have hgrid : gridLoss Cds Kds δ ≤ gridLoss (Cds + 1) Kds δ := by
    have hδlog : Real.log (δ : ℝ) ≤ 0 := Real.log_nonpos (by positivity) (by exact_mod_cast hδle1)
    unfold gridLoss
    have hpow1 : (Cds : ℝ) ^ (ssfGridLen δ + 1) ≤
        ((Cds + 1 : NNReal) : ℝ) ^ (ssfGridLen δ + 1) := by
      apply pow_le_pow_left₀
      · positivity
      · exact_mod_cast (le_self_add (a := Cds))
    have hpow2 : 0 ≤ (1 - Real.log (δ : ℝ)) ^ (Kds * (ssfGridLen δ + 1) ^ 2) := by
      exact pow_nonneg (by linarith) _
    exact mul_le_mul_of_nonneg_right hpow1 hpow2
  -- scaleGapLoss is nonneg, so totalLoss is monotone in the constant
  have hsnn : (0 : ℝ) ≤ scaleGapLoss cds δ := by
    have h₁ : (1 : ℝ) ≤ scaleGapLoss cds δ := one_le_scaleGapLoss cds hδpos hδle1
    linarith
  have hloss : totalLoss Cds Kds cds δ ≤ totalLoss (Cds + 1) Kds cds δ := by
    unfold totalLoss
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hgrid hsnn)
  -- the loss of the compared-against constant is below δ^(-ε'/2)
  have hloss_b : totalLoss (Cds + 1) Kds cds δ ≤ (δ : ENNReal) ^ (-(ε' / 2)) := by
    have hthr' := hthr hδpos hδle₀
    rw [ennreal_coe_nnreal_rpow hδR (-(ε' / 2))]
    exact hthr'
  -- the fixed constant is below δ^(-ε'/2)
  have hcst_enn : (Cds : ENNReal) ≤ (δ : ENNReal) ^ (-(ε' / 2)) := by
    have hle1 : (Cds : ℝ) ≤ (δ : ℝ) ^ (-(ε' / 2)) := by
      exact le_trans (by exact_mod_cast (le_self_add (a := Cds))) hcst_ℝ
    rw [← ENNReal.ofReal_coe_nnreal,
      show (δ : ENNReal) ^ (-(ε' / 2)) = ENNReal.ofReal ((δ : ℝ) ^ (-(ε' / 2)))
        from (ennreal_coe_nnreal_rpow hδR (-(ε' / 2)))]
    exact ENNReal.ofReal_le_ofReal hle1
  -- the smallness of `δ` for the rpow-addition step
  have hδne0 : ((δ : NNReal) : ENNReal) ≠ 0 := ne_of_gt (ENNReal.coe_pos.mpr hδpos)
  calc
    (Cds : ENNReal) * totalLoss Cds Kds cds δ
        ≤ (Cds : ENNReal) * totalLoss (Cds + 1) Kds cds δ := by
            exact mul_le_mul_of_nonneg_left hloss (by positivity)
    _ ≤ (Cds : ENNReal) * (δ : ENNReal) ^ (-(ε' / 2)) := by
            exact mul_le_mul_of_nonneg_left hloss_b (by positivity)
    _ ≤ (δ : ENNReal) ^ (-(ε' / 2)) * (δ : ENNReal) ^ (-(ε' / 2)) := by
            exact mul_le_mul_of_nonneg_right hcst_enn (by positivity)
    _ = (δ : ENNReal) ^ (-ε') := by
            have hpow : (δ : ENNReal) ^ (-(ε' / 2)) * (δ : ENNReal) ^ (-(ε' / 2))
                = (δ : ENNReal) ^ (-ε') := by
              rw [← ENNReal.rpow_add (-(ε' / 2)) (-(ε' / 2)) hδne0 ENNReal.coe_ne_top]
              congr 1
              ring
            exact hpow

end ml1Boot

end Kakeya
