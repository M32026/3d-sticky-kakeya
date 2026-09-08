/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineThreeLevelSeam
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorRetention
public import Kakeya.DimensionThree.MainLemma1.CoarseFibre

/-!
# The `Cu ^ 5` containment-to-fibre bracket, restated at the hypotheses it actually uses

 The vehicle carrying the existing count floor from
`Tube.UniformTubeSet.nodesUnder` to the coarse *fibre* is
`Kakeya.ml1Boot.card_nodesIn_le_card_coarseFibre`, composed with retention.
 then measured that the ML1 lemma's bundle
`Kakeya.ml1Boot.IsCoarseNodeParents` is
**not instantiable at Main Lemma 2's hierarchy**: it asks `nodes_carry_leaf` over the whole of
`𝒰.cover.indexSet b`, while Main Lemma 2 only ever has the retained set inside
`Kakeya.ML2Reduction.activeNodes`, and it asks `Kakeya.ml1Boot.IsParentFamily.injOn` — node-body
injectivity at the coarse index — for which the tree has no lemma.  The only constructor of the
bundle, `Kakeya.ml1Boot.exists_coarseNodeParents_of_caseTwoInput`, takes both as extra hypotheses
and says in its own docstring that they are owed.

**This file removes the blocker without asking for either row, by measuring what the ML1 proof
uses rather than what its bundle demands.**  In `Kakeya.ml1Boot.card_nodesIn_le_card_coarseFibre`:

* `Kakeya.ml1Boot.IsParentFamily.injOn` is **never read**.  The bundle's `parent` field is read
  exactly once, as `parent.le_parent`, and only in the *containment* half of the conclusion
  (`fibre ⊆ nodesIn`).  The **counting** half — the half the count floor needs, and the only half
  's Bar 1 route uses — reads no field of `IsParentFamily` at all.
* `nodes_carry_leaf` is read exactly once, and only to produce **one** node with a nonempty class,
  which forces `0 < 𝒰.branchingN b`.  A single leaf `i ∈ s'` does the same job through
  `Tube.ChainCoverSystem.assign_mem`, so `s'.Nonempty` suffices.

So the counting bracket holds under `a ≤ b ≤ N`, the identity `assign_comp`, and `s'.Nonempty`.
The first two are existing for Main Lemma 2 (`Kakeya.ML2Core.coarseNode_assign`), and the third is
free wherever any leaf exists.  **Neither owed hierarchy row is needed.**

Per 's condition on restatements, the restatement is pinned to the
original by the bridge `Kakeya.ML2Core.card_nodesIn_le_card_coarseFibre_bridge`, whose
statement is the ML1 lemma's counting conclusion verbatim and whose proof is the restatement.

**Family / shading / level pair.**  Every declaration here is about the *nodes* of a uniform
hierarchy `𝒰` on `(s, T)`; no shading is read.  The generic pair is `(a, b)` with `a` coarse;
the Main Lemma 2 corollaries are instantiated at the genuine-parent pair `(p, b)`.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section Bracket

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **The coarse class splits over the fibre: `N_a ≤ Cu ² N_b · |t_τ[l]|`, from `assign_comp`
alone.**

`Kakeya.ml1Boot.branching_le_mul_card_coarseFibre` restated at the three hypotheses its proof
uses — `a ≤ b`, `b ≤ N` and the identity `pθ (assign b i) = assign a i` on leaves — instead of at
the bundle `Kakeya.ml1Boot.IsCoarseNodeParents`, whose remaining two fields
(`nodes_carry_leaf`, `parent`) that proof never reads.  The argument is the original's, unchanged.

**Family:** `(s', T)` under `𝒰'`, no shading.  **Level pair:** `(a, b)`. -/
theorem branching_le_mul_card_fibre_of_assignComp {ι : Type*} [DecidableEq ι] {δ : NNReal}
    {s' : Finset ι} {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal}
    (𝒰' : UniformTubeSet s' T N Cu) {pθ : ι → ι} (hab : a ≤ b) (hbN : b ≤ N)
    (hcomp : ∀ i ∈ s', pθ (𝒰'.cover.assign b i) = 𝒰'.cover.assign a i)
    {l : ι} (hl : l ∈ 𝒰'.cover.indexSet a) :
    (𝒰'.branchingN a : ℝ)
      ≤ (Cu : ℝ) ^ 2 * (𝒰'.branchingN b : ℝ) *
          ((ml1Boot.fibre (𝒰'.cover.indexSet b) pθ l).card : ℝ) := by
  classical
  set F : Finset ι := ml1Boot.fibre (𝒰'.cover.indexSet b) pθ l
  let cls : ι → Finset ι := fun k => coverClass s' (𝒰'.cover.assign b) k
  have hleN : a ≤ N := hab.trans hbN
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
      · simpa [F, ml1Boot.fibre, Finset.mem_filter] using
          ⟨𝒰'.cover.assign_mem b hbN i h_mem.1, by
            rw [hcomp i h_mem.1]
            exact h_mem.2⟩
      · simpa [cls, coverClass, Finset.mem_filter] using (⟨h_mem.1, rfl⟩ :
          i ∈ s' ∧ 𝒰'.cover.assign b i = 𝒰'.cover.assign b i)
    · intro h
      rw [Finset.mem_biUnion] at h
      rcases h with ⟨k, hk, hik⟩
      have hk_mem : k ∈ 𝒰'.cover.indexSet b ∧ pθ k = l := by
        simpa [F, ml1Boot.fibre, Finset.mem_filter] using hk
      have hik_mem : i ∈ s' ∧ 𝒰'.cover.assign b i = k := by
        simpa [cls, coverClass, Finset.mem_filter] using hik
      simpa [coverClass, Finset.mem_filter] using ⟨hik_mem.1, by
        calc
          𝒰'.cover.assign a i = pθ (𝒰'.cover.assign b i) := (hcomp i hik_mem.1).symm
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
          exact_mod_cast 𝒰'.card_class_le b hbN k hk_index)
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
/-- **The `Cu ^ 5` bracket, at hypotheses Main Lemma 2 can meet**:
`|nodesIn b (tube a l)| ≤ Cu ^ 5 · |fibre|`.

`Kakeya.ml1Boot.card_nodesIn_le_card_coarseFibre`'s counting half, restated over `a ≤ b ≤ N`,
`assign_comp`, and `s'.Nonempty`.  The strict positivity of `𝒰'.branchingN b` — the one thing
`nodes_carry_leaf` was there to give — comes from a single leaf: `𝒰'.cover.assign b i` is an index
whose class contains `i`, so `1 ≤ Cu · N_b` by the upper class bracket, exactly as in the original
but at a node the caller always has.

**Family:** `(s', T)` under `𝒰'`, no shading.  **Level pair:** `(a, b)`. -/
theorem card_nodesIn_le_card_fibre_of_assignComp {ι : Type*} [DecidableEq ι] {δ : NNReal}
    {s' : Finset ι} {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal} (hCu : 1 ≤ Cu)
    (𝒰' : UniformTubeSet s' T N Cu) {pθ : ι → ι} (hab : a ≤ b) (hbN : b ≤ N)
    (hcomp : ∀ i ∈ s', pθ (𝒰'.cover.assign b i) = 𝒰'.cover.assign a i)
    (hs : s'.Nonempty) {l : ι} (hl : l ∈ 𝒰'.cover.indexSet a) :
    ((𝒰'.nodesIn b (𝒰'.cover.tube a l).toConvexSpaceBody).card : ℝ)
      ≤ (Cu : ℝ) ^ 5 * ((ml1Boot.fibre (𝒰'.cover.indexSet b) pθ l).card : ℝ) := by
  classical
  let NI : Finset ι := 𝒰'.nodesIn b (𝒰'.cover.tube a l).toConvexSpaceBody
  let F : Finset ι := ml1Boot.fibre (𝒰'.cover.indexSet b) pθ l
  let B : ℝ := (𝒰'.branchingN b : ℝ)
  -- `0 < N_b`, from one leaf instead of from `nodes_carry_leaf`.
  obtain ⟨i₀, hi₀⟩ := hs
  have hk₀index : 𝒰'.cover.assign b i₀ ∈ 𝒰'.cover.indexSet b := 𝒰'.cover.assign_mem b hbN i₀ hi₀
  have hcls_pos : 0 < (coverClass s' (𝒰'.cover.assign b) (𝒰'.cover.assign b i₀)).card :=
    Finset.card_pos.mpr ⟨i₀, by simp [coverClass, hi₀]⟩
  have hOne : (1 : ℝ) ≤ (Cu : ℝ) * B := by
    have hge : (1 : NNReal)
        ≤ ((coverClass s' (𝒰'.cover.assign b) (𝒰'.cover.assign b i₀)).card : NNReal) := by
      exact_mod_cast (Nat.succ_le_of_lt hcls_pos)
    have hle : ((coverClass s' (𝒰'.cover.assign b) (𝒰'.cover.assign b i₀)).card : NNReal)
        ≤ Cu * 𝒰'.branchingN b := 𝒰'.card_class_le b hbN _ hk₀index
    exact_mod_cast (le_trans hge hle)
  have hcu_pos : 0 < (Cu : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hCu)
  have hBpos : 0 < B := by
    have hcm : 0 < (Cu : ℝ) * B := lt_of_lt_of_le (by norm_num) hOne
    exact pos_of_mul_pos_right hcm (le_of_lt hcu_pos)
  have h1 : B * (NI.card : ℝ) ≤ (Cu : ℝ) ^ 3 * (𝒰'.branchingN a : ℝ) := by
    simpa [B, NI] using ml1Boot.branching_mul_card_nodesIn_le 𝒰' hab hbN l
  have h2 : (𝒰'.branchingN a : ℝ) ≤ (Cu : ℝ) ^ 2 * B * (F.card : ℝ) := by
    simpa [B, F] using branching_le_mul_card_fibre_of_assignComp 𝒰' hab hbN hcomp hl
  have h2' : (Cu : ℝ) ^ 3 * (𝒰'.branchingN a : ℝ) ≤ (Cu : ℝ) ^ 5 * B * (F.card : ℝ) := by
    calc
      (Cu : ℝ) ^ 3 * (𝒰'.branchingN a : ℝ)
          ≤ (Cu : ℝ) ^ 3 * ((Cu : ℝ) ^ 2 * B * (F.card : ℝ)) :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg (le_of_lt hcu_pos) 3)
      _ = (Cu : ℝ) ^ 5 * B * (F.card : ℝ) := by ring
  have hbm : B * (NI.card : ℝ) ≤ B * ((Cu : ℝ) ^ 5 * (F.card : ℝ)) := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using h1.trans h2'
  exact le_of_mul_le_mul_left hbm hBpos

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The pin, per **: the restatement implies the existing lemma's
counting conclusion, verbatim, on the bundle.

The statement below is the second conjunct of `Kakeya.ml1Boot.card_nodesIn_le_card_coarseFibre`
copied unchanged; the proof is
`Kakeya.ML2Core.card_nodesIn_le_card_fibre_of_assignComp`.  So the restatement is at least as
strong as the original at every site the original applies (a bundle whose `nodes_carry_leaf` is
non-vacuous forces `s'.Nonempty`), and it is strictly weaker in hypotheses: it asks neither
`nodes_carry_leaf` over `indexSet b` nor `Kakeya.ml1Boot.IsParentFamily.injOn`. -/
theorem card_nodesIn_le_card_coarseFibre_bridge {ι : Type*} [DecidableEq ι] {δ : NNReal}
    {s' : Finset ι} {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal} (hCu : 1 ≤ Cu)
    (𝒰' : UniformTubeSet s' T N Cu) {pθ : ι → ι}
    (hcnp : ml1Boot.IsCoarseNodeParents 𝒰' a b pθ) (hs : s'.Nonempty)
    {l : ι} (hl : l ∈ 𝒰'.cover.indexSet a) :
    ((𝒰'.nodesIn b (𝒰'.cover.tube a l).toConvexSpaceBody).card : ℝ)
      ≤ (Cu : ℝ) ^ 5 * ((ml1Boot.fibre (𝒰'.cover.indexSet b) pθ l).card : ℝ) :=
  card_nodesIn_le_card_fibre_of_assignComp hCu 𝒰' hcnp.le_index hcnp.le_gridLen
    hcnp.assign_comp hs hl

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Exactness of the pin.**  The existing lemma's own counting half inhabits the *same* stated
type as `Kakeya.ML2Core.card_nodesIn_le_card_coarseFibre_bridge`.  Written as an `example` proved
from `Kakeya.ml1Boot.card_nodesIn_le_card_coarseFibre` rather than from the bridge, so that the
two proofs of one type witness that the restatement did not drift. -/
example {ι : Type*} [DecidableEq ι] {δ : NNReal}
    {s' : Finset ι} {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal} (hCu : 1 ≤ Cu)
    (𝒰' : UniformTubeSet s' T N Cu) {pθ : ι → ι}
    (hcnp : ml1Boot.IsCoarseNodeParents 𝒰' a b pθ) (_hs : s'.Nonempty)
    {l : ι} (hl : l ∈ 𝒰'.cover.indexSet a) :
    ((𝒰'.nodesIn b (𝒰'.cover.tube a l).toConvexSpaceBody).card : ℝ)
      ≤ (Cu : ℝ) ^ 5 * ((ml1Boot.fibre (𝒰'.cover.indexSet b) pθ l).card : ℝ) :=
  (ml1Boot.card_nodesIn_le_card_coarseFibre hCu 𝒰' hcnp hl).2

end Bracket

section ML2

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {δ Cu : NNReal}

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The bracket at Main Lemma 2's genuine-parent pair `(p, b)`**:
`|nodesUnder b p jp| ≤ Cu ^ 5 · |fibre over indexSet b|`.

`Kakeya.ML2Core.card_nodesIn_le_card_fibre_of_assignComp` with `pθ` the level-`p` ancestor map
`Kakeya.ML2Reduction.coarseNode`, whose `assign_comp` identity is the existing
`Kakeya.ML2Core.coarseNode_assign`.  `Tube.UniformTubeSet.nodesUnder b p jp` is
`nodesIn b (tube p jp)` by definition (`Tube.UniformTubeSet.nodesUnder_eq_nodesIn`).

This is the first leg  Bar 1's route, and it needs **no** row on the
hierarchy beyond nonemptiness of the leaf family.

**Family:** `(u, T)` under `𝒰`, no shading.  **Level pair:** `(p, b)`. -/
theorem card_nodesUnder_le_card_coarseFibre {ι : Type*} [DecidableEq ι] {u : Finset ι}
    {T : ι → Tube δ E} {N p b : ℕ} (hCu : 1 ≤ Cu) (𝒰 : UniformTubeSet u T N Cu)
    (hpb : p ≤ b) (hbN : b ≤ N) (hu : u.Nonempty)
    {jp : ι} (hjp : jp ∈ 𝒰.cover.indexSet p) :
    ((𝒰.nodesUnder b p jp).card : ℝ)
      ≤ (Cu : ℝ) ^ 5
          * ((ml1Boot.fibre (𝒰.cover.indexSet b)
              (ML2Reduction.coarseNode 𝒰.cover.toChain p b) jp).card : ℝ) :=
  card_nodesIn_le_card_fibre_of_assignComp hCu 𝒰 hpb hbN
    (fun _i hi => coarseNode_assign 𝒰.cover.toChain hpb hbN hi) hu hjp

open Classical in
/-- **Retention, stated where it is actually true: on the full coarse fibre.**

`Kakeya.ML2Core.RetentionProportionAt` asks the retained set `t` to hold a `θ₀`-share of
`Tube.UniformTubeSet.nodesUnder`, the *geometric* set.  The source's selection (l.4486-4500) is a
selection inside the *assignment* fibre, and  Trap B records
that the two are different objects.  This is the honest spelling: a `θ₀`-share of the fibre over
`𝒰.cover.indexSet c`.

**Family/shading:** hierarchy `𝒰` on `(s, V)`; `t` the retained level-`c` set.
**Level pair:** `(p, c)`. -/
def FibreRetentionAt {s : Finset ι} {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet s (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu)
    (p c : ℕ) (t : Finset ι) (θ₀ : NNReal) : Prop :=
  ∀ jp ∈ 𝒰.cover.indexSet p,
    (θ₀ : ℝ) * ((ml1Boot.fibre (𝒰.cover.indexSet c)
          (ML2Reduction.coarseNode 𝒰.cover.toChain p c) jp).card : ℝ)
      ≤ ((({j ∈ t | ML2Reduction.coarseNode 𝒰.cover.toChain p c j = jp} : Finset ι)).card : ℝ)

open Classical in
/-- **BRACKET ∘ RETENTION, the composite  rules is the vehicle**, in
that order: the geometric-set retention `Kakeya.ML2Core.RetentionProportionAt` is *derived* from
fibre retention at the cost of the hierarchy's own uniformity constant, `θ₀ ↦ θ₀ / Cu ^ 5`.

**No new constant** in the sense §SPEC required: `Cu` is `𝒰`'s own, and `hfac` brackets it by
`Cu ≤ Cu₀`.

**Family/shading** and **level pair**: as `Kakeya.ML2Core.FibreRetentionAt`. -/
theorem retentionProportionAt_of_fibreRetention {s : Finset ι}
    {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {𝒰 : Tube.UniformTubeSet s (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu}
    {p c : ℕ} {t : Finset ι} {θ₀ : NNReal} (hCu : 1 ≤ Cu)
    (hpc : p ≤ c) (hcN : c ≤ Tube.ssfGridLen δ) (hs : s.Nonempty)
    (hret : FibreRetentionAt 𝒰 p c t θ₀) :
    RetentionProportionAt 𝒰 p c t (θ₀ / Cu ^ 5) := by
  classical
  intro jp hjp
  have hbr := card_nodesUnder_le_card_coarseFibre (E := EuclideanSpace ℝ (Fin 3))
    hCu 𝒰 hpc hcN hs hjp
  have hCu1 : (1 : ℝ) ≤ (Cu : ℝ) := by exact_mod_cast hCu
  have hCu0 : (0 : ℝ) < (Cu : ℝ) := by linarith
  have hpow : (0 : ℝ) < (Cu : ℝ) ^ 5 := by positivity
  have hdiv : ((θ₀ / Cu ^ 5 : NNReal) : ℝ) = (θ₀ : ℝ) / (Cu : ℝ) ^ 5 := by
    rw [NNReal.coe_div, NNReal.coe_pow]
  rw [hdiv, div_mul_eq_mul_div, div_le_iff₀ hpow]
  have hfr := hret jp hjp
  have hmono : (θ₀ : ℝ) * ((𝒰.nodesUnder c p jp).card : ℝ)
      ≤ (θ₀ : ℝ) * ((Cu : ℝ) ^ 5
          * ((ml1Boot.fibre (𝒰.cover.indexSet c)
              (ML2Reduction.coarseNode 𝒰.cover.toChain p c) jp).card : ℝ)) :=
    mul_le_mul_of_nonneg_left hbr (NNReal.coe_nonneg θ₀)
  have h3 := mul_le_mul_of_nonneg_left hfr hpow.le
  have hrw : (θ₀ : ℝ) * ((Cu : ℝ) ^ 5
      * ((ml1Boot.fibre (𝒰.cover.indexSet c)
          (ML2Reduction.coarseNode 𝒰.cover.toChain p c) jp).card : ℝ))
      = (Cu : ℝ) ^ 5 * ((θ₀ : ℝ)
        * ((ml1Boot.fibre (𝒰.cover.indexSet c)
            (ML2Reduction.coarseNode 𝒰.cover.toChain p c) jp).card : ℝ)) := by ring
  rw [hrw] at hmono
  exact (hmono.trans h3).trans (le_of_eq (mul_comm _ _))

end ML2

end Kakeya.ML2Core

end
