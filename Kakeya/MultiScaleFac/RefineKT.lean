/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.Refine
public import Kakeya.MultiScaleFac.StoppingKTBase

/-!
# The refined stopping time of GWZ Lemma 7.7(B)

The Katz–Tao twin of `Kakeya/MultiScaleFac/Refine.lean`.

What is *not* the same is the price.  In half (A) the block predicate
`MultiScaleFac.BlockFrostmanAt t T N C ζ a b i₀` reads the fibres of the **current pile** `t`, so
shrinking the pile changes the predicate and the descent
`MultiScaleFac.BlockFrostmanAt.of_subfamily` costs a factor; restoring the hypotheses that descent
needs costs a re-uniformization at every level, and that is the origin of the polylogarithmic
factor in half (A).

Here `MultiScaleFac.BlockKatzTaoAt u C ζ a b i₀` reads only the node families of the **fixed**
uniform data `u` and the anchor `i₀`.  It does not mention the pile at all.  So:

* the invariant `∀ i₀ ∈ t, BlockKatzTaoAt u C ζ a b i₀` descends to any subset of `t` by
  restricting a universal quantifier — no constant, no hypotheses to restore;
* the constant never grows along the stopping time, since both halves of a cut carry the constant
  the parent carried (`MultiScaleFac.BlockKatzTaoOn.anchor_le`);
* no level re-uniformizes, so the only loss is the pile shrinkage `2 (N+1)` per level — a factor of
  `N` alone, independent of `δ`.

The state of the abstract engine is therefore just the pile, and the uniform data is a parameter
fixed once and for all before the recursion starts.
-/

@[expose] public section

open MeasureTheory Real Metric ConvexSpaceBody
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

universe u

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

variable {ι : Type*} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {Cu : NNReal} {N : ℕ}

section Invariant

/-- **The block bound of GWZ Lemma 7.7(B) with the anchor set named separately.**  Where
`MultiScaleFac.BlockKatzTao` quantifies over the whole family carrying the uniform data, here the
two roles are separated: `u` is the uniform data on the ambient family `s`, and `t` is the current
pile of anchors.  The predicate `BlockKatzTaoAt u C ζ a b i₀` never mentions `t`. -/
def BlockKatzTaoOn (t : Finset ι)
    (u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu)
    (C : NNReal) (ζ : ℝ) (a b : ℕ) : Prop :=
  ∀ i₀ ∈ t, BlockKatzTaoAt u C ζ a b i₀

omit [Nontrivial E] in
/-- The invariant descends to a smaller pile for free: it is a universal quantifier over the pile
and its body does not mention the pile.  This is the `hdescend` hypothesis of
`MultiScaleFac.exists_maximal_cuts_abstract_state`, and in half (B) it is free where half (A) pays
`MultiScaleFac.BlockFrostmanAt.of_subfamily`. -/
theorem BlockKatzTaoOn.subset {t t' : Finset ι}
    {u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu}
    {C : NNReal} {ζ : ℝ} {a b : ℕ} (h : BlockKatzTaoOn t u C ζ a b) (ht : t' ⊆ t) :
    BlockKatzTaoOn t' u C ζ a b :=
  fun i₀ hi₀ => h i₀ (ht hi₀)

omit [Nontrivial E] in
/-- The pile-relative form of `MultiScaleFac.BlockKatzTaoAt.mono`, quantified over the pile. -/
theorem BlockKatzTaoOn.mono (hδ : 0 < δ) (hδ1 : δ ≤ 1) {t : Finset ι}
    {u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu}
    {C C' : NNReal} {ζ ζ' : ℝ} (hCC' : C ≤ C') (hζ : 0 ≤ ζ) (hζζ' : ζ ≤ ζ')
    {a b : ℕ} (hab : a ≤ b) (h : BlockKatzTaoOn t u C ζ a b) :
    BlockKatzTaoOn t u C' ζ' a b :=
  fun i₀ hi₀ => (h i₀ hi₀).mono hδ hδ1 hCC' hζ hζζ' hab

omit [Nontrivial E] in
/-- The pile-relative form of `MultiScaleFac.BlockKatzTaoAt.anchor_le`, quantified over the pile:
the fine half of a cut is free. -/
theorem BlockKatzTaoOn.anchor_le (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℝ} (hεpos : 0 < ε)
    {t : Finset ι} {u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu}
    {C : NNReal} {ζ ζ' : ℝ} (hζ : 0 ≤ ζ) (hgap : ζ ≤ ε * ζ') {a c b : ℕ} (hac : a ≤ c)
    (hcb : c + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b) (h : BlockKatzTaoOn t u C ζ a b) :
    BlockKatzTaoOn t u C ζ' c b :=
  fun i₀ hi₀ => (h i₀ hi₀).anchor_le hδ hδ1 hεpos hζ hgap hac hcb

omit [Nontrivial E] in
/-- **`Δ_max` compares along a subfamily with the same bodies.**  `Kakeya.maxDensity_mono` needs the
same body map and `Kakeya.maxDensity_congr` needs the same index set; composing them covers the case
where the index set shrinks and the bodies agree on the smaller one. -/
theorem maxDensity_le_of_subset_of_eqOn {ι' : Type*} {S S' : Finset ι'}
    {W W' : ι' → ConvexSpaceBody E} (hS : S ⊆ S') (hW : ∀ i ∈ S, W i = W' i) :
    Kakeya.maxDensity S W ≤ Kakeya.maxDensity S' W' :=
  (Kakeya.maxDensity_congr hW).le.trans (Kakeya.maxDensity_mono W' hS)

omit [Nontrivial E] in
/-- **The block bound of half (B) descends to a sub-cover for free.**  If the uniform data `u'` on a
subfamily has, at every grid scale, a subset of the nodes of `u` and the same node tubes there, then
every block bound for `u` is a block bound for `u'` with the *same* constant — the quantity being a
plain supremum of densities, which can only decrease when the index set shrinks. -/
theorem BlockKatzTaoAt.of_subcover {s' : Finset ι} {Cu' : NNReal}
    {u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu}
    {u' : ∀ k, k ≤ N → Tube.IsUniformAtScale s' T (gridScale δ N k) Cu'}
    (hpar : ∀ k (hk : k ≤ N), (u' k hk).parent ⊆ (u k hk).parent)
    (htub : ∀ k (hk : k ≤ N), ∀ j ∈ (u' k hk).parent,
      (u' k hk).parentTube j = (u k hk).parentTube j)
    {C : NNReal} {ζ : ℝ} {a b : ℕ} {i₀ : ι} (h : BlockKatzTaoAt u C ζ a b i₀) :
    BlockKatzTaoAt u' C ζ a b i₀ := fun hb =>
  (maxDensity_le_of_subset_of_eqOn
    (fun j hj => Finset.mem_filter.mpr
      ⟨hpar b hb (Finset.mem_filter.mp hj).1,
        (congrArg _ (htub b hb j (Finset.mem_filter.mp hj).1).symm).trans_le
          (Finset.mem_filter.mp hj).2⟩)
    (fun j hj => congrArg _ (htub b hb j (Finset.mem_filter.mp hj).1))).trans (h hb)

omit [Nontrivial E] in
/-- The pile-and-anchor form of `MultiScaleFac.BlockKatzTaoAt.of_subcover`: a block bound descends
both in the pile of anchors and along a sub-cover, at no cost. -/
theorem BlockKatzTaoOn.of_subcover {t t' s' : Finset ι} {Cu' : NNReal}
    {u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu}
    {u' : ∀ k, k ≤ N → Tube.IsUniformAtScale s' T (gridScale δ N k) Cu'}
    (hpar : ∀ k (hk : k ≤ N), (u' k hk).parent ⊆ (u k hk).parent)
    (htub : ∀ k (hk : k ≤ N), ∀ j ∈ (u' k hk).parent,
      (u' k hk).parentTube j = (u k hk).parentTube j)
    {C : NNReal} {ζ : ℝ} {a b : ℕ} (ht : t' ⊆ t) (h : BlockKatzTaoOn t u C ζ a b) :
    BlockKatzTaoOn t' u' C ζ a b :=
  fun i₀ hi₀ => (h i₀ (ht hi₀)).of_subcover hpar htub

end Invariant

section PerNode

/-- **The per-anchor split test of GWZ Lemma 7.7(B).**  The anchor `i₀` passes the test on the block
`(a,b)` if *some* cut index at relative depth `ε` from both ends carries the block bound on the
**coarse** half `(a,c)` at `i₀`.  Mirror of `MultiScaleFac.NodeSplitTest`, which tests the fine half
because `C_F` is inherited in the opposite direction. -/
def NodeSplitTestKT (u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu)
    (C : NNReal) (ε ζ : ℝ) (a b : ℕ) (i₀ : ι) : Prop :=
  NodeSplitTestOf (fun c => BlockKatzTaoAt u C ζ a c) ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ a b i₀

/-- The anchors of the pile that pass the per-anchor split test. -/
noncomputable def passingNodesKT (t : Finset ι)
    (u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu)
    (C : NNReal) (ε ζ : ℝ) (a b : ℕ) : Finset ι :=
  passingNodesOf t (fun c => BlockKatzTaoAt u C ζ a c) ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ a b

/-- The anchors of the pile that fail the per-anchor split test.  This is the set that becomes the
majority set `F` of alternative (ii) when the stopping time halts. -/
noncomputable def failingNodesKT (t : Finset ι)
    (u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu)
    (C : NNReal) (ε ζ : ℝ) (a b : ℕ) : Finset ι :=
  failingNodesOf t (fun c => BlockKatzTaoAt u C ζ a c) ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ a b

omit [Nontrivial E] in
theorem passingNodesKT_subset (t : Finset ι)
    (u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu)
    (C : NNReal) (ε ζ : ℝ) (a b : ℕ) : passingNodesKT t u C ε ζ a b ⊆ t :=
  passingNodesOf_subset t (fun c => BlockKatzTaoAt u C ζ a c) ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ a b

omit [Nontrivial E] in
theorem failingNodesKT_subset (t : Finset ι)
    (u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu)
    (C : NNReal) (ε ζ : ℝ) (a b : ℕ) : failingNodesKT t u C ε ζ a b ⊆ t :=
  failingNodesOf_subset t (fun c => BlockKatzTaoAt u C ζ a c) ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ a b

omit [Nontrivial E] in
theorem mem_passingNodesKT {t : Finset ι}
    {u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu}
    {C : NNReal} {ε ζ : ℝ} {a b : ℕ} {i₀ : ι} :
    i₀ ∈ passingNodesKT t u C ε ζ a b ↔ i₀ ∈ t ∧ NodeSplitTestKT u C ε ζ a b i₀ :=
  mem_passingNodesOf

omit [Nontrivial E] in
theorem mem_failingNodesKT {t : Finset ι}
    {u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu}
    {C : NNReal} {ε ζ : ℝ} {a b : ℕ} {i₀ : ι} :
    i₀ ∈ failingNodesKT t u C ε ζ a b ↔ i₀ ∈ t ∧ ¬ NodeSplitTestKT u C ε ζ a b i₀ :=
  mem_failingNodesOf

omit [Nontrivial E] in
/-- **The majority side of a split.**  A finite set is at most twice one of the two blocks of any
two-block partition of it.  This is the sole place in the refined stopping time of half (B) where
anchors are discarded at all, and the property separating the two sides is a property of individual
anchors, so whichever side survives carries that property universally. -/
theorem card_le_two_mul_card_passingNodesKT_or_failingNodesKT (t : Finset ι)
    (u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu)
    (C : NNReal) (ε ζ : ℝ) (a b : ℕ) :
    t.card ≤ 2 * (passingNodesKT t u C ε ζ a b).card ∨
      t.card ≤ 2 * (failingNodesKT t u C ε ζ a b).card :=
  card_le_two_mul_card_passingNodesOf_or_failingNodesOf t
    (fun c => BlockKatzTaoAt u C ζ a c) ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ a b

omit [Nontrivial E] in
/-- **A common cut index for the passing pile.**  If every anchor of `P` passes the per-anchor test
on `(a,b)`, a pigeonhole over the at most `N + 1` admissible grid indices produces a *single* index
`c`, still at relative depth `ε` from both ends, carrying the coarse-half block bound at every
anchor of a subset `P' ⊆ P` with `|P| ≤ (N+1) |P'|`.  The loss `N + 1` is `δ`-independent. -/
theorem exists_common_cut_of_forall_nodeSplitTestKT {P : Finset ι}
    {u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu}
    {C : NNReal} {ε ζ : ℝ} {a b : ℕ} (hb : b ≤ N) (hP : P.Nonempty)
    (h : ∀ i₀ ∈ P, NodeSplitTestKT u C ε ζ a b i₀) :
    ∃ c : ℕ, a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c ∧ c + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b ∧
      ∃ P' ⊆ P, P'.Nonempty ∧ P.card ≤ (N + 1) * P'.card ∧
        BlockKatzTaoOn P' u C ζ a c :=
  exists_common_cut_of_forall_nodeSplitTestOf (Q := fun c => BlockKatzTaoAt u C ζ a c)
    (M := ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊) hb hP h

end PerNode

section GridState

omit [Nontrivial E] in
/-- The sub-cover form of `MultiScaleFac.BlockKatzTaoAt.of_subcover`, stated for two grid-uniform
systems: the node data of a `MultiScaleFac.GridUniform` is reached through `parent_eq` and
`tube_eq`, so a sub-cover relation at the level of the cover systems transports the block bound. -/
theorem BlockKatzTaoAt.of_gridUniformCore_subcover {t t' : Finset ι} {Cv : NNReal}
    (𝒞 : GridUniformCore t T N Cv) (𝒞' : GridUniformCore t' T N Cv)
    (hpar : ∀ n ≤ N, 𝒞'.cover.indexSet n ⊆ 𝒞.cover.indexSet n)
    (htub : ∀ n, 𝒞'.cover.tube n = 𝒞.cover.tube n)
    {C : NNReal} {ζ : ℝ} {a b : ℕ} {i₀ : ι}
    (h : BlockKatzTaoAt 𝒞.uniformAt C ζ a b i₀) :
    BlockKatzTaoAt 𝒞'.uniformAt C ζ a b i₀ := by
  refine BlockKatzTaoAt.of_subcover (fun n hn => ?_) (fun n hn j hj => ?_) h
  · rw [𝒞'.parent_eq n hn, 𝒞.parent_eq n hn]; exact hpar n hn
  · rw [𝒞'.parent_eq n hn] at hj
    rw [𝒞'.tube_eq n hn j hj, 𝒞.tube_eq n hn j (hpar n hn hj), htub n]

omit [Nontrivial E] in
/-- **The original, derived from the core sibling in one line** — the bridge that pins the two
readings together.  The statement is unchanged; only its proof now
routes through `GridUniformCore`, which a bare `Tube.UniformTubeSet` can supply. -/
theorem BlockKatzTaoAt.of_gridUniform_subcover {t t' : Finset ι} {Cv : NNReal}
    (𝒢 : GridUniform t T N Cv) (𝒢' : GridUniform t' T N Cv)
    (hpar : ∀ n ≤ N, 𝒢'.cover.indexSet n ⊆ 𝒢.cover.indexSet n)
    (htub : ∀ n, 𝒢'.cover.tube n = 𝒢.cover.tube n)
    {C : NNReal} {ζ : ℝ} {a b : ℕ} {i₀ : ι}
    (h : BlockKatzTaoAt 𝒢.uniformAt C ζ a b i₀) :
    BlockKatzTaoAt 𝒢'.uniformAt C ζ a b i₀ :=
  BlockKatzTaoAt.of_gridUniformCore_subcover 𝒢.toGridUniformCore 𝒢'.toGridUniformCore hpar htub h

end GridState

end MultiScaleFac

end Kakeya
