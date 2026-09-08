/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTwoScale

/-!
# Cardinality multiplicativity across the two levels of the §9 spine hierarchy

Blueprint `blueprint/src/GWZAdapted/section9.tex`, the cardinality bookkeeping of the two-scale
split (lines 63–90): the three factors that
`Kakeya.ML2Reduction.exists_spineTwoScale_ofChain` produces a multiplicity bound against are
indexed by

* `{i ∈ s | 𝒞.assign b i = jτ}` — the *class* of a middle (`τ`) node, the fine fibre;
* `{j ∈ tτ' | coarseNode 𝒞 a b j = jθ}` — the middle nodes whose coarse (`θ`) ancestor is `jθ`;
* `tθ'` — the retained coarse nodes,

and the exponent arithmetic of §9 needs the product of the three cardinalities to be at most a
constant multiple of `|s|`.  That is what this file proves
(`Kakeya.ML2Reduction.card_class_mul_card_coarseFibre_mul_card_le`), with the constant `Cu ^ 5`.

## Why a product bound and not three separate bounds

Individually none of the three factors is bounded by `|s|`: a hierarchy with one coarse node and
one middle node per leaf has `|tθ'| = 1` and middle fibre `|s|`, while a hierarchy with one leaf per
middle node has fine fibre `1` and `|tθ'| = |s|`.  What the hierarchy does control is the *product*,
through the branching numbers, and the two branching numbers cancel telescopically:

```
|class_b(jτ)|              ≤ Cu · N_b                (ChainUniformTubeSet.card_class_le)
N_b · |{j | ancestor = jθ}| ≤ Cu ^ 3 · N_a           (branchingN_mul_card_le_of_tube_le)
N_a · |tθ'|                 ≤ Cu · |s|               (branchingN_mul_card_le_subset_indexSet)
```

Multiplying the three in that order never divides by a branching number, so no positivity of `N_a`
or `N_b` is needed and the bound stays true in the degenerate case `Cu = 0` (where the lower class
bracket forces every branching number to vanish).  This is the three-factor form of the
Main-Lemma-1 counting layer `Kakeya.ml1Boot.branching_mul_card_nodesIn_le` /
`Kakeya.ml1Boot.branchingN_mul_card_indexSet_le` /
`Kakeya.ml1Boot.b3_branch_card_of_hierarchy`, reproved here on
`Tube.ChainUniformTubeSet` — the §9 hierarchy lives on an arbitrary chain `σ`, not on the grid
`Tube.gridScale δ N`, and `Kakeya/DimensionThree/MainLemma1/` is not on the import graph of the
Main Lemma 2 reduction.  Two things change in the port:

* the containment bracket used is `Tube.ChainUniformTubeSet.card_filter_le`, whose contained set is
  the plain filter `{i ∈ s | T i ≤ tube a jθ}` rather than `Kakeya.familyIn`;
* the middle factor is not the containment family `Tube.UniformTubeSet.nodesUnder` but the
  *ancestor fibre* of `Kakeya.ML2Reduction.coarseNode`, which is a subfamily of it — the inclusion
  is `Kakeya.ML2Reduction.tube_le_coarseNode`, and it is the only geometric input.

No coarse parent-map bundle (`Kakeya.ml1Boot.IsCoarseNodeParents`) is needed, because
`Kakeya.ML2Reduction.coarseNode` already *is* the ancestor map and
`Kakeya.ML2Reduction.tube_le_coarseNode` already proves the node containment on the active nodes.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Reduction

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {δ : ℝ≥0} {ι : Type u} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → ℝ≥0} {Cu : ℝ≥0}

/-! ## The two class-bracket counts -/

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
open Classical in
/-- **The containment bracket at a level, with no side condition on the constant or the node.**

`|{i ∈ s | T i ≤ tube a j}| ≤ Cu ² · N_a`: a leaf contained in the node `j` is assigned to one of
the at most `Cu` nodes that the bounded-overlap clause permits to meet `tube a j` through `s`, and
each of those classes has at most `Cu · N_a` members.

This is `Tube.ChainUniformTubeSet.card_filter_le` with its two hypotheses `1 ≤ Cu` and
`j ∈ 𝒰.cover.indexSet a` **deleted**.  Both are inert there — the tree binds them as `_hC` and
`_hj` and never uses them — and carrying them would push two vacuous obligations onto every
consumer of the counting layer below.  Nothing else changes: the proof is the same three steps,
and `Cu ^ 2` is the same constant. -/
theorem card_filter_le_of_chainUniform
    (𝒰 : Tube.ChainUniformTubeSet s T N σ Cu) {a : ℕ} (haN : a ≤ N) (j : ι) :
    (({i ∈ s | (T i).toConvexSpaceBody ≤ (𝒰.cover.tube a j).toConvexSpaceBody}).card : ℝ≥0)
      ≤ Cu ^ 2 * 𝒰.branchingN a := by
  classical
  set F : Finset ι :=
    {i ∈ s | (T i).toConvexSpaceBody ≤ (𝒰.cover.tube a j).toConvexSpaceBody} with hF
  set A : Finset ι := F.image (𝒰.cover.assign a) with hA
  have hFs : F ⊆ s := Finset.filter_subset _ _
  -- every node hit by a contained leaf meets `tube a j` through `s`
  set M : Finset ι := (𝒰.cover.indexSet a).filter (fun v => ∃ i ∈ s,
    (T i).toConvexSpaceBody ≤ (𝒰.cover.tube a v).toConvexSpaceBody ∧
    (T i).toConvexSpaceBody ≤ (𝒰.cover.tube a j).toConvexSpaceBody) with hM
  have hAmeet : A ⊆ M := by
    intro v hv
    obtain ⟨i, hiF, rfl⟩ := Finset.mem_image.mp hv
    have hi : i ∈ s ∧ (T i).toConvexSpaceBody ≤ (𝒰.cover.tube a j).toConvexSpaceBody :=
      Finset.mem_filter.mp hiF
    exact Finset.mem_filter.mpr ⟨𝒰.cover.assign_mem a haN i hi.1,
      i, hi.1, 𝒰.cover.le_tube_assign a haN i hi.1, hi.2⟩
  have hAcard : (A.card : ℝ≥0) ≤ Cu := by
    have hbo := 𝒰.boundedOverlap a haN (𝒰.cover.tube a j)
    have hMC : (M.card : ℝ≥0) ≤ Cu := by convert hbo using 3
    exact le_trans (by exact_mod_cast Finset.card_le_card hAmeet) hMC
  have hAindex : A ⊆ 𝒰.cover.indexSet a := fun v hv => by
    obtain ⟨i, hiF, rfl⟩ := Finset.mem_image.mp hv
    exact 𝒰.cover.assign_mem a haN i (hFs hiF)
  -- the contained set is covered by the classes of those nodes
  have hFcov : F ⊆ A.biUnion (fun v => Tube.coverClass s (𝒰.cover.assign a) v) := by
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨𝒰.cover.assign a i, Finset.mem_image_of_mem _ hi,
      Finset.mem_filter.mpr ⟨hFs hi, rfl⟩⟩
  have hsum : (F.card : ℝ≥0)
      ≤ ∑ v ∈ A, ((Tube.coverClass s (𝒰.cover.assign a) v).card : ℝ≥0) := by
    have h₁ : F.card ≤ ∑ v ∈ A, (Tube.coverClass s (𝒰.cover.assign a) v).card :=
      le_trans (Finset.card_le_card hFcov) Finset.card_biUnion_le
    rw [← Nat.cast_sum]
    exact_mod_cast h₁
  calc (F.card : ℝ≥0)
      ≤ ∑ v ∈ A, ((Tube.coverClass s (𝒰.cover.assign a) v).card : ℝ≥0) := hsum
    _ ≤ ∑ _v ∈ A, Cu * 𝒰.branchingN a :=
        Finset.sum_le_sum (fun v hv => 𝒰.card_class_le a haN v (hAindex hv))
    _ = (A.card : ℝ≥0) * (Cu * 𝒰.branchingN a) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Cu * (Cu * 𝒰.branchingN a) := by exact mul_le_mul' hAcard le_rfl
    _ = Cu ^ 2 * 𝒰.branchingN a := by ring

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **Counting the level-`b` nodes contained in a level-`a` node**: `N_b · |K| ≤ Cu ³ · N_a` for
any set `K` of level-`b` nodes all of whose node tubes sit inside the level-`a` node `jθ`.

The classes of the members of `K` are pairwise disjoint — they are fibres of the single function
`assign b` over distinct values — and each is contained in the set of leaves contained in the
level-`a` node, because a leaf lies in the node it is assigned to.  So the lower class bracket at
level `b` summed over `K` is at most `Cu` times the containment count at level `a`, which
`Kakeya.ML2Reduction.card_filter_le_of_chainUniform` bounds by `Cu ² · N_a`.

Neither `1 ≤ Cu` nor `jθ ∈ 𝒰.cover.indexSet a` is a hypothesis: see
`Kakeya.ML2Reduction.card_filter_le_of_chainUniform`. -/
theorem branchingN_mul_card_le_of_tube_le
    (𝒰 : Tube.ChainUniformTubeSet s T N σ Cu)
    {a b : ℕ} (haN : a ≤ N) (hbN : b ≤ N) {jθ : ι}
    {K : Finset ι} (hK : K ⊆ 𝒰.cover.indexSet b)
    (hKle : ∀ j ∈ K, (𝒰.cover.tube b j).toConvexSpaceBody
      ≤ (𝒰.cover.tube a jθ).toConvexSpaceBody) :
    𝒰.branchingN b * (K.card : ℝ≥0) ≤ Cu ^ 3 * 𝒰.branchingN a := by
  classical
  set cls : ι → Finset ι := fun j => Tube.coverClass s (𝒰.cover.assign b) j with hcls
  set F : Finset ι :=
    {i ∈ s | (T i).toConvexSpaceBody ≤ (𝒰.cover.tube a jθ).toConvexSpaceBody} with hF
  -- the classes over `K` are pairwise disjoint
  have hpd : (K : Set ι).PairwiseDisjoint cls := by
    intro j₁ hj₁ j₂ hj₂ hne
    change Disjoint (cls j₁) (cls j₂)
    rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    have hm₁ : i ∈ s ∧ 𝒰.cover.assign b i = j₁ := by
      simpa [hcls, Tube.coverClass] using hi₁
    have hm₂ : i ∈ s ∧ 𝒰.cover.assign b i = j₂ := by
      simpa [hcls, Tube.coverClass] using hi₂
    exact hne (hm₁.2.symm.trans hm₂.2)
  -- each class over `K` lands in the contained set of the coarse node
  have hsubF : ∀ j ∈ K, cls j ⊆ F := by
    intro j hj i hi
    have hm : i ∈ s ∧ 𝒰.cover.assign b i = j := by
      simpa [hcls, Tube.coverClass] using hi
    have hT : (T i).toConvexSpaceBody
        ≤ (𝒰.cover.tube b (𝒰.cover.assign b i)).toConvexSpaceBody :=
      𝒰.cover.le_tube_assign b hbN i hm.1
    rw [hm.2] at hT
    exact Finset.mem_filter.mpr ⟨hm.1, hT.trans (hKle j hj)⟩
  have hsum_le : (∑ j ∈ K, ((cls j).card : ℝ≥0)) ≤ (F.card : ℝ≥0) := by
    have h₁ : (K.biUnion cls).card ≤ F.card :=
      Finset.card_le_card (fun i hi => by
        obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
        exact hsubF j hj hij)
    rw [Finset.card_biUnion hpd] at h₁
    rw [← Nat.cast_sum]
    exact_mod_cast h₁
  -- lower class bracket at level `b`, summed
  have hlow : 𝒰.branchingN b * (K.card : ℝ≥0) ≤ Cu * ∑ j ∈ K, ((cls j).card : ℝ≥0) := by
    calc 𝒰.branchingN b * (K.card : ℝ≥0)
        = ∑ _j ∈ K, 𝒰.branchingN b := by
          rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
      _ ≤ ∑ j ∈ K, Cu * ((cls j).card : ℝ≥0) :=
          Finset.sum_le_sum (fun j hj => 𝒰.le_card_class b hbN j (hK hj))
      _ = Cu * ∑ j ∈ K, ((cls j).card : ℝ≥0) := by rw [Finset.mul_sum]
  -- containment bracket at level `a`
  have hFle : (F.card : ℝ≥0) ≤ Cu ^ 2 * 𝒰.branchingN a := by
    rw [hF]
    exact card_filter_le_of_chainUniform 𝒰 haN jθ
  calc 𝒰.branchingN b * (K.card : ℝ≥0)
      ≤ Cu * ∑ j ∈ K, ((cls j).card : ℝ≥0) := hlow
    _ ≤ Cu * (F.card : ℝ≥0) := by exact mul_le_mul' le_rfl hsum_le
    _ ≤ Cu * (Cu ^ 2 * 𝒰.branchingN a) := by exact mul_le_mul' le_rfl hFle
    _ = Cu ^ 3 * 𝒰.branchingN a := by ring

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **The classes of a level account for the whole leaf set**: `N_a · |t| ≤ Cu · |s|` for any set
`t` of level-`a` nodes.

Summing the lower class bracket `Tube.ChainUniformTubeSet.le_card_class` over `t`: the classes are
fibres of the function `assign a`, hence pairwise disjoint, and all lie inside `s`, so their
cardinalities sum to at most `|s|`.  The chain version of
`Kakeya.ml1Boot.branchingN_mul_card_indexSet_le`, relativized to a subset `t` of the index set
rather than the whole of it, which is what §9 needs: `tθ'` is a *retained* subfamily. -/
theorem branchingN_mul_card_le_subset_indexSet
    (𝒰 : Tube.ChainUniformTubeSet s T N σ Cu) {a : ℕ} (haN : a ≤ N)
    {t : Finset ι} (ht : t ⊆ 𝒰.cover.indexSet a) :
    𝒰.branchingN a * (t.card : ℝ≥0) ≤ Cu * (s.card : ℝ≥0) := by
  classical
  set cls : ι → Finset ι := fun j => Tube.coverClass s (𝒰.cover.assign a) j with hcls
  have hpd : (t : Set ι).PairwiseDisjoint cls := by
    intro j₁ hj₁ j₂ hj₂ hne
    change Disjoint (cls j₁) (cls j₂)
    rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    have hm₁ : i ∈ s ∧ 𝒰.cover.assign a i = j₁ := by
      simpa [hcls, Tube.coverClass] using hi₁
    have hm₂ : i ∈ s ∧ 𝒰.cover.assign a i = j₂ := by
      simpa [hcls, Tube.coverClass] using hi₂
    exact hne (hm₁.2.symm.trans hm₂.2)
  have hsum_le : (∑ j ∈ t, ((cls j).card : ℝ≥0)) ≤ (s.card : ℝ≥0) := by
    have h₁ : (t.biUnion cls).card ≤ s.card :=
      Finset.card_le_card (fun i hi => by
        obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
        exact (Finset.mem_filter.mp hij).1)
    rw [Finset.card_biUnion hpd] at h₁
    rw [← Nat.cast_sum]
    exact_mod_cast h₁
  calc 𝒰.branchingN a * (t.card : ℝ≥0)
      = ∑ _j ∈ t, 𝒰.branchingN a := by
        rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    _ ≤ ∑ j ∈ t, Cu * ((cls j).card : ℝ≥0) :=
        Finset.sum_le_sum (fun j hj => 𝒰.le_card_class a haN j (ht hj))
    _ = Cu * ∑ j ∈ t, ((cls j).card : ℝ≥0) := by rw [Finset.mul_sum]
    _ ≤ Cu * (s.card : ℝ≥0) := by exact mul_le_mul' le_rfl hsum_le

/-! ## The three-factor product bound -/

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
open Classical in
/-- **Cardinality multiplicativity across the two levels of the §9 hierarchy** (blueprint
`section9.tex`, the cardinality bookkeeping of the two-scale split).

The three index sets of `Kakeya.ML2Reduction.exists_spineTwoScale_ofChain`'s triple product — the
fine fibre `{i ∈ s | assign b i = jτ}`, the ancestor fibre
`{j ∈ tτ' | coarseNode 𝒞 a b j = jθ}` and the retained coarse family `tθ'` — have
cardinalities whose product is at most `Cu ^ 5 · |s|`.

The ancestor fibre is a set of level-`b` nodes whose node tubes lie inside the level-`a` node `jθ`
(`Kakeya.ML2Reduction.tube_le_coarseNode`, available because `tτ'` consists of *active* nodes), so
`Kakeya.ML2Reduction.branchingN_mul_card_le_of_tube_le` applies to it; the remaining two factors are
the upper class bracket at level `b` and
`Kakeya.ML2Reduction.branchingN_mul_card_le_subset_indexSet` at level `a`.

`Cu ^ 5` is not claimed optimal — nothing downstream reads the exponent, only that the constant is
fixed before `δ`. -/
theorem card_class_mul_card_coarseFibre_mul_card_le
    (𝒰 : Tube.ChainUniformTubeSet s T N σ Cu)
    {a b : ℕ} (hab : a ≤ b) (haN : a ≤ N) (hbN : b ≤ N)
    {tτ' tθ' : Finset ι} (htτ : tτ' ⊆ activeNodes 𝒰.cover b)
    (htθ : tθ' ⊆ 𝒰.cover.indexSet a)
    {jτ jθ : ι} (hjτ : jτ ∈ 𝒰.cover.indexSet b) :
    (({i ∈ s | 𝒰.cover.assign b i = jτ}).card : ℝ≥0)
        * (({j ∈ tτ' | coarseNode 𝒰.cover a b j = jθ}).card : ℝ≥0)
        * (tθ'.card : ℝ≥0)
      ≤ Cu ^ 5 * (s.card : ℝ≥0) := by
  classical
  set K : Finset ι := {j ∈ tτ' | coarseNode 𝒰.cover a b j = jθ} with hK
  -- the ancestor fibre consists of level-`b` nodes sitting inside the level-`a` node `jθ`
  have hKsub : K ⊆ 𝒰.cover.indexSet b := by
    intro j hj
    exact activeNodes_subset 𝒰.cover b (htτ (Finset.mem_filter.mp hj).1)
  have hKle : ∀ j ∈ K, (𝒰.cover.tube b j).toConvexSpaceBody
      ≤ (𝒰.cover.tube a jθ).toConvexSpaceBody := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    have := tube_le_coarseNode 𝒰.cover hab hbN (htτ hj'.1)
    rwa [hj'.2] at this
  -- the three brackets
  have h₁ : (({i ∈ s | 𝒰.cover.assign b i = jτ}).card : ℝ≥0) ≤ Cu * 𝒰.branchingN b := by
    have h := 𝒰.card_class_le b hbN jτ hjτ
    simpa [Tube.coverClass] using h
  have h₂ : 𝒰.branchingN b * (K.card : ℝ≥0) ≤ Cu ^ 3 * 𝒰.branchingN a :=
    branchingN_mul_card_le_of_tube_le 𝒰 haN hbN hKsub hKle
  have h₃ : 𝒰.branchingN a * (tθ'.card : ℝ≥0) ≤ Cu * (s.card : ℝ≥0) :=
    branchingN_mul_card_le_subset_indexSet 𝒰 haN htθ
  calc (({i ∈ s | 𝒰.cover.assign b i = jτ}).card : ℝ≥0) * (K.card : ℝ≥0) * (tθ'.card : ℝ≥0)
      ≤ (Cu * 𝒰.branchingN b) * (K.card : ℝ≥0) * (tθ'.card : ℝ≥0) := by
        exact mul_le_mul' (mul_le_mul' h₁ le_rfl) le_rfl
    _ = Cu * (𝒰.branchingN b * (K.card : ℝ≥0)) * (tθ'.card : ℝ≥0) := by ring
    _ ≤ Cu * (Cu ^ 3 * 𝒰.branchingN a) * (tθ'.card : ℝ≥0) := by
        exact mul_le_mul' (mul_le_mul' le_rfl h₂) le_rfl
    _ = Cu ^ 4 * (𝒰.branchingN a * (tθ'.card : ℝ≥0)) := by ring
    _ ≤ Cu ^ 4 * (Cu * (s.card : ℝ≥0)) := by exact mul_le_mul' le_rfl h₃
    _ = Cu ^ 5 * (s.card : ℝ≥0) := by ring

end Kakeya.ML2Reduction

end
