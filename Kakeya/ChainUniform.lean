/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ShadedUniform
public import Kakeya.Uniform

/-!
# Uniform hierarchies along an arbitrary chain of scales

`Tube.GridCoverSystem` and `Tube.UniformTubeSet` pin the radius of the
node at level `k` to the geometric grid scale `gridScale δ N k`.  That is a real restriction: the
telescoping engine of the `MultiScale*` files does not run on the grid, it runs on a *cut chain* —
a subsequence `σ m = gridScale δ N (c m)` selected by a stopping time (`cutChain`), whose
consecutive scales are `16`-separated whereas consecutive grid scales are not.  A grid-indexed
bundle can therefore not be handed to that engine, which is why those files consume the unbundled
per-scale predicate `Tube.IsUniformAtScale` instead.

This file removes that restriction.  The node radius becomes a parameter `σ : ℕ → NNReal`, and the
grid structures are recovered as the special case `σ := gridScale δ N` by the wrappers
`GridCoverSystem.toChain` / `ChainCoverSystem.toGrid` and `UniformTubeSet.toChain` /
`ChainUniformTubeSet.toGrid`, which are field-by-field copies: no statement of `Uniform.lean`
or `ShadedUniform.lean` changes, and nothing is re-proved.

The generalization costs nothing because neither `Uniform.lean` nor `ShadedUniform.lean`
uses any property of `gridScale` at all — the grid scale occurs there only as the radius of a node
tube.  In particular antitonicity, the endpoint conditions `σ 0 = 1`, `σ J = δ` and the
`16`-separation are deliberately *not* fields here: the raw grid does not satisfy the separation
condition, so baking it in would break the grid instantiation.  Consumers state those conditions
separately, exactly as `Kakeya.MultiScaleFac.frostmanConstant_fibre_le_prod` already does.

The payoff is `ChainCoverSystem.restrict` / `ChainUniformTubeSet.restrict`: a hierarchy along one
chain restricts to a hierarchy along any monotone reindexing, in particular from the grid to a cut
chain.  Nestedness survives the restriction because `nested` and `tube_nested` compose across a
gap; that is the content of `ChainCoverSystem.assign_eq_of_le` and
`ChainCoverSystem.tube_assign_le`.
-/

@[expose] public section

open MeasureTheory Real Metric

universe u
open ShadedTube

namespace Tube


section Tubes

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-! ### The nested system of covers along an arbitrary chain -/

/-- **A nested system of covers along a prescribed chain of scales**: the scale-parameterized form
of `Tube.GridCoverSystem`, with the node radius at level `k` given by `σ k` instead
of `gridScale δ N k`.  All four clauses are verbatim those of the grid version. -/
structure ChainCoverSystem {δ : NNReal} (t : Finset ι) (T : ι → Tube δ E) (N : ℕ)
    (σ : ℕ → NNReal) where
  /-- The index set of the nodes at each level of the chain. -/
  indexSet : ℕ → Finset ι
  /-- The node of scale `σ k` to which a member of `t` is assigned. -/
  assign : ℕ → ι → ι
  /-- The node itself, a tube of the exact chain radius `σ k`. -/
  tube : (k : ℕ) → ι → Tube (σ k) E
  /-- Every member of `t` is assigned to an actual node. -/
  assign_mem : ∀ k, k ≤ N → ∀ i ∈ t, assign k i ∈ indexSet k
  /-- A member lies inside the node it is assigned to (factor-`1` containment). -/
  le_tube_assign : ∀ k, k ≤ N → ∀ i ∈ t,
    (T i).toConvexSpaceBody ≤ (tube k (assign k i)).toConvexSpaceBody
  /-- The classes refine as the level increases. -/
  nested : ∀ k, k + 1 ≤ N → ∀ i ∈ t, ∀ j ∈ t,
    assign (k + 1) i = assign (k + 1) j → assign k i = assign k j
  /-- …and so do the nodes themselves. -/
  tube_nested : ∀ k, k + 1 ≤ N → ∀ i ∈ t,
    (tube (k + 1) (assign (k + 1) i)).toConvexSpaceBody ≤
      (tube k (assign k i)).toConvexSpaceBody

/-- A grid cover system is a chain cover system along the grid chain `σ = gridScale δ N`. -/
def GridCoverSystem.toChain {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    (𝒞 : GridCoverSystem t T N) : ChainCoverSystem t T N (gridScale δ N) where
  indexSet := 𝒞.indexSet
  assign := 𝒞.assign
  tube := 𝒞.tube
  assign_mem := 𝒞.assign_mem
  le_tube_assign := 𝒞.le_tube_assign
  nested := 𝒞.nested
  tube_nested := 𝒞.tube_nested

/-- …and conversely, so the grid version is exactly the special case `σ := gridScale δ N`. -/
def ChainCoverSystem.toGrid {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    (𝒞 : ChainCoverSystem t T N (gridScale δ N)) : GridCoverSystem t T N where
  indexSet := 𝒞.indexSet
  assign := 𝒞.assign
  tube := 𝒞.tube
  assign_mem := 𝒞.assign_mem
  le_tube_assign := 𝒞.le_tube_assign
  nested := 𝒞.nested
  tube_nested := 𝒞.tube_nested

/-! ### Nestedness composes across a gap -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Nestedness of the classes, iterated over a gap of length `d`: sharing a node at level `a + d`
forces sharing one at level `a`.  This is what makes a cut chain — a monotone reindexing of the
levels — inherit the nestedness of the ambient chain. -/
theorem ChainCoverSystem.assign_eq_of_add {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {σ : ℕ → NNReal} (𝒞 : ChainCoverSystem t T N σ) (a : ℕ) :
    ∀ d : ℕ, a + d ≤ N → ∀ i ∈ t, ∀ j ∈ t,
      𝒞.assign (a + d) i = 𝒞.assign (a + d) j → 𝒞.assign a i = 𝒞.assign a j := by
  intro d
  induction d with
  | zero =>
      intro h i hi j hj heq
      simpa using heq
  | succ d ih =>
      intro h i hi j hj heq
      have h1 : (a + d) + 1 ≤ N := by omega
      exact ih (by omega) i hi j hj (𝒞.nested (a + d) h1 i hi j hj (by
        simpa [Nat.add_assoc] using heq))

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Nestedness of the classes across an arbitrary gap `a ≤ b`. -/
theorem ChainCoverSystem.assign_eq_of_le {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {σ : ℕ → NNReal} (𝒞 : ChainCoverSystem t T N σ) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ N)
    {i j : ι} (hi : i ∈ t) (hj : j ∈ t) (heq : 𝒞.assign b i = 𝒞.assign b j) :
    𝒞.assign a i = 𝒞.assign a j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact 𝒞.assign_eq_of_add a d hb i hi j hj heq

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Nestedness of the nodes, iterated over a gap of length `d`. -/
theorem ChainCoverSystem.tube_assign_le_add {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {σ : ℕ → NNReal} (𝒞 : ChainCoverSystem t T N σ) (a : ℕ) :
    ∀ d : ℕ, a + d ≤ N → ∀ i ∈ t,
      (𝒞.tube (a + d) (𝒞.assign (a + d) i)).toConvexSpaceBody ≤
        (𝒞.tube a (𝒞.assign a i)).toConvexSpaceBody := by
  intro d
  induction d with
  | zero =>
      intro hN i hi
      exact le_rfl
  | succ d ih =>
      intro hN i hi
      exact le_trans (𝒞.tube_nested (a + d) (by omega) i hi) (ih (by omega) i hi)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Nestedness of the nodes across an arbitrary gap `a ≤ b`: the node of a member at the finer
level `b` lies inside its node at the coarser level `a`, with no inflation of the container. -/
theorem ChainCoverSystem.tube_assign_le {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {σ : ℕ → NNReal} (𝒞 : ChainCoverSystem t T N σ) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ N)
    {i : ι} (hi : i ∈ t) :
    (𝒞.tube b (𝒞.assign b i)).toConvexSpaceBody ≤ (𝒞.tube a (𝒞.assign a i)).toConvexSpaceBody := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact 𝒞.tube_assign_le_add a d hb i hi

/-! ### Restriction to a subchain -/

/-- **Restricting a hierarchy to a subchain.**  Given a monotone reindexing `c : ℕ → ℕ` of the
levels, the hierarchy along `σ` restricts to a hierarchy along `σ ∘ c`.  Taking `σ = gridScale δ N`
and `c` the enumeration of a stopping-time cut set turns a grid hierarchy into a hierarchy along the
cut chain, which is the object the telescoping engine of the `MultiScale*` files consumes. -/
def ChainCoverSystem.restrict {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {σ : ℕ → NNReal} (𝒞 : ChainCoverSystem t T N σ) (c : ℕ → ℕ) (M : ℕ)
    (hmono : ∀ m, m + 1 ≤ M → c m ≤ c (m + 1)) (hcN : ∀ m, m ≤ M → c m ≤ N) :
    ChainCoverSystem t T M (fun m => σ (c m)) where
  indexSet m := 𝒞.indexSet (c m)
  assign m := 𝒞.assign (c m)
  tube m := 𝒞.tube (c m)
  assign_mem m hm i hi := 𝒞.assign_mem (c m) (hcN m hm) i hi
  le_tube_assign m hm i hi := 𝒞.le_tube_assign (c m) (hcN m hm) i hi
  nested m hm _i hi _j hj heq :=
    𝒞.assign_eq_of_le (hmono m hm) (hcN (m + 1) hm) hi hj heq
  tube_nested m hm _i hi :=
    𝒞.tube_assign_le (hmono m hm) (hcN (m + 1) hm) hi

/-! ### Uniform sets of tubes along an arbitrary chain -/

/-- **GWZ Definition 2.1 along a prescribed chain of scales**: the scale-parameterized form of
`Tube.UniformTubeSet`.  Every clause is verbatim that of the grid version, with
`gridScale δ N k` replaced by `σ k`. -/
structure ChainUniformTubeSet {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) (N : ℕ)
    (σ : ℕ → NNReal) (C : NNReal) where
  /-- The nested system of covers along the chain `σ`. -/
  cover : ChainCoverSystem s T N σ
  /-- The branching number at each level of the chain. -/
  branchingN : ℕ → NNReal
  /-- Distinct node indices name distinct node tubes. -/
  tube_injOn : ∀ k ≤ N, Set.InjOn (cover.tube k) (cover.indexSet k : Set ι)
  /-- **Definition 2.1(ii) (Bounded overlap)**, read at the chain radius `σ k`. -/
  boundedOverlap : ∀ k ≤ N, ∀ V : Tube (σ k) E,
    (open scoped Classical in
      (cover.indexSet k).filter (fun j => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (cover.tube k j).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤ C
  /-- **Definition 2.1(iii) (Constant branching), upper half**, on the class of a node. -/
  card_class_le : ∀ k ≤ N, ∀ j ∈ cover.indexSet k,
    ((coverClass s (cover.assign k) j).card : NNReal) ≤ C * branchingN k
  /-- **Definition 2.1(iii), lower half**, on the class of a node. -/
  le_card_class : ∀ k ≤ N, ∀ j ∈ cover.indexSet k,
    branchingN k ≤ C * ((coverClass s (cover.assign k) j).card : NNReal)

/-- A uniform set of tubes along the grid is a uniform set of tubes along the grid chain. -/
def UniformTubeSet.toChain {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : UniformTubeSet s T N C) : ChainUniformTubeSet s T N (gridScale δ N) C where
  cover := 𝒰.cover.toChain
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlap := 𝒰.boundedOverlap
  card_class_le := 𝒰.card_class_le
  le_card_class := 𝒰.le_card_class

/-- …and conversely, so `UniformTubeSet` is exactly `ChainUniformTubeSet` at `σ := gridScale δ
N`. -/
def ChainUniformTubeSet.toGrid {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : ChainUniformTubeSet s T N (gridScale δ N) C) : UniformTubeSet s T N C where
  cover := 𝒰.cover.toGrid
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlap := 𝒰.boundedOverlap
  card_class_le := 𝒰.card_class_le
  le_card_class := 𝒰.le_card_class

/-! ### The per-scale reading, recovered along the chain -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Every member of `s` lies in some node of level `k`, with no inflation.  The unbundled form of
`cover.assign_mem` together with `cover.le_tube_assign`. -/
theorem ChainUniformTubeSet.exists_le_node {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {σ : ℕ → NNReal} {C : NNReal} (𝒰 : ChainUniformTubeSet s T N σ C) {k : ℕ} (hk : k ≤ N)
    {i : ι} (hi : i ∈ s) :
    ∃ j ∈ 𝒰.cover.indexSet k, (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody :=
  ⟨𝒰.cover.assign k i, 𝒰.cover.assign_mem k hk i hi, 𝒰.cover.le_tube_assign k hk i hi⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
open Classical in
/-- **The containment bracket, upper half.**  The leaves of `s` merely *contained* in a level-`k`
node number at most `C ^ 2 * 𝒰.branchingN k`: a contained leaf is assigned to one of the at most
`C` nodes that the bounded-overlap clause permits to meet that node. -/
theorem ChainUniformTubeSet.card_filter_le {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {σ : ℕ → NNReal} {C : NNReal} (𝒰 : ChainUniformTubeSet s T N σ C) (_hC : 1 ≤ C)
    {k : ℕ} (hk : k ≤ N) {j : ι} (_hj : j ∈ 𝒰.cover.indexSet k) :
    (({i ∈ s | (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody}).card : NNReal)
      ≤ C ^ 2 * 𝒰.branchingN k := by
  classical
  let F : Finset ι := {i ∈ s | (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody}
  let A : Finset ι := F.image (𝒰.cover.assign k)
  have hF_s : F ⊆ s := by
    dsimp [F]; exact Finset.filter_subset _ _
  have hA_sub_parent : A ⊆ 𝒰.cover.indexSet k := by
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨i, hiF, rfl⟩ := hv
    have hi_s : i ∈ s := by
      dsimp [F] at hiF; exact (Finset.mem_filter.mp hiF).1
    exact 𝒰.cover.assign_mem k hk i hi_s
  have hA_sub_overlap :
      A ⊆ (𝒰.cover.indexSet k).filter (fun v => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k v).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody) := by
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨i, hiF, rfl⟩ := hv
    have hi_s : i ∈ s := by
      dsimp [F] at hiF; exact (Finset.mem_filter.mp hiF).1
    rw [Finset.mem_filter]
    refine ⟨𝒰.cover.assign_mem k hk i hi_s, i, hi_s, ?_, ?_⟩
    · exact 𝒰.cover.le_tube_assign k hk i hi_s
    · dsimp [F] at hiF; exact (Finset.mem_filter.mp hiF).2
  have hAcard : (A.card : NNReal) ≤ C := by
    have hsub : A.card ≤
        ((𝒰.cover.indexSet k).filter (fun v => ∃ i ∈ s,
          (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k v).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody)).card :=
      Finset.card_le_card hA_sub_overlap
    have hle : (A.card : NNReal) ≤
        ((𝒰.cover.indexSet k).filter (fun v => ∃ i ∈ s,
          (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k v).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody)).card := by
      exact_mod_cast hsub
    exact hle.trans (by exact_mod_cast (𝒰.boundedOverlap k hk (𝒰.cover.tube k j)))
  have hF_eq : F = A.biUnion (fun v => coverClass F (𝒰.cover.assign k) v) := by
    apply Finset.ext
    intro i
    constructor
    · intro hi
      have hv : 𝒰.cover.assign k i ∈ A := Finset.mem_image.mpr ⟨i, hi, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨𝒰.cover.assign k i, hv,
        by simp only [coverClass, Finset.mem_filter]; exact ⟨hi, trivial⟩⟩
    · intro hmem
      rw [Finset.mem_biUnion] at hmem
      rcases hmem with ⟨v, hv, hi⟩
      simp only [coverClass, Finset.mem_filter] at hi ⊢
      exact hi.1
  have hF_le_sum : (F.card : NNReal) ≤
      (∑ v ∈ A, (coverClass F (𝒰.cover.assign k) v).card : NNReal) := by
    have hnat : F.card ≤ ∑ v ∈ A, (coverClass F (𝒰.cover.assign k) v).card := by
      calc F.card = (A.biUnion (fun v => coverClass F (𝒰.cover.assign k) v)).card := by
            exact congrArg Finset.card hF_eq
        _ ≤ ∑ v ∈ A, (coverClass F (𝒰.cover.assign k) v).card := Finset.card_biUnion_le
    exact_mod_cast hnat
  have hterm : ∀ v ∈ A, (coverClass F (𝒰.cover.assign k) v).card ≤ C * 𝒰.branchingN k := by
    intro v hvA
    have hv : v ∈ 𝒰.cover.indexSet k := hA_sub_parent hvA
    have hsubcl : coverClass F (𝒰.cover.assign k) v ⊆ coverClass s (𝒰.cover.assign k) v :=
      coverClass_subset_of_subset hF_s (𝒰.cover.assign k) v
    have hcl_le : (coverClass F (𝒰.cover.assign k) v).card ≤
        (coverClass s (𝒰.cover.assign k) v).card := Finset.card_le_card hsubcl
    have hcl_le_c :
        ((coverClass F (𝒰.cover.assign k) v).card : NNReal) ≤
          ((coverClass s (𝒰.cover.assign k) v).card : NNReal) := by
      exact_mod_cast hcl_le
    exact hcl_le_c.trans (𝒰.card_class_le k hk v hv)
  have hsum_le : (∑ v ∈ A, (coverClass F (𝒰.cover.assign k) v).card : NNReal) ≤
      (A.card : NNReal) * (C * 𝒰.branchingN k) := by
    calc (∑ v ∈ A, (coverClass F (𝒰.cover.assign k) v).card : NNReal)
        ≤ (∑ v ∈ A, (C * 𝒰.branchingN k) : NNReal) :=
            Finset.sum_le_sum (fun v hv => hterm v hv)
      _ = (A.card : NNReal) * (C * 𝒰.branchingN k) := by simp
  have hcount : (F.card : NNReal) ≤ (C ^ 2) * 𝒰.branchingN k := by
    calc (F.card : NNReal)
        ≤ (A.card : NNReal) * (C * 𝒰.branchingN k) := hF_le_sum.trans hsum_le
      _ ≤ C * (C * 𝒰.branchingN k) := mul_le_mul_left hAcard (C * 𝒰.branchingN k)
      _ = (C ^ 2) * 𝒰.branchingN k := by ring
  exact hcount

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
open Classical in
/-- **The containment bracket, lower half.**  The class of a node sits inside the set of leaves
contained in it, so the lower class bracket transfers with the same constant, weakened to `C ^ 2` to
match `ChainUniformTubeSet.card_filter_le`. -/
theorem ChainUniformTubeSet.le_mul_card_filter {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {σ : ℕ → NNReal} {C : NNReal} (𝒰 : ChainUniformTubeSet s T N σ C) (hC : 1 ≤ C)
    {k : ℕ} (hk : k ≤ N) {j : ι} (hj : j ∈ 𝒰.cover.indexSet k) :
    𝒰.branchingN k ≤
      C ^ 2 * (({i ∈ s | (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody}).card
        : NNReal) := by
  classical
  have hC_le_Csq : C ≤ C ^ 2 := by
    calc C = C ^ 1 := by rw [pow_one]
      _ ≤ C ^ 2 := pow_le_pow_right₀ hC (by norm_num : (1 : ℕ) ≤ 2)
  have hsubcl : coverClass s (𝒰.cover.assign k) j ⊆
      {i ∈ s | (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody} := by
    intro i hi
    simp only [coverClass, Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, ?_⟩
    have hlt := 𝒰.cover.le_tube_assign k hk i hi.1
    simpa [hi.2] using hlt
  have hclcard : (coverClass s (𝒰.cover.assign k) j).card ≤
      {i ∈ s | (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody}.card :=
    Finset.card_le_card hsubcl
  have hclcard' :
      ((coverClass s (𝒰.cover.assign k) j).card : NNReal) ≤
        ({i ∈ s | (T i).toConvexSpaceBody
            ≤ (𝒰.cover.tube k j).toConvexSpaceBody}.card : NNReal) := by
    exact_mod_cast hclcard
  calc 𝒰.branchingN k ≤ C * (coverClass s (𝒰.cover.assign k) j).card :=
        𝒰.le_card_class k hk j hj
    _ ≤ C * {i ∈ s | (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody}.card :=
        mul_le_mul_right hclcard' C
    _ ≤ (C ^ 2) * {i ∈ s | (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody}.card :=
        mul_le_mul_left hC_le_Csq _

/-- **The per-scale reading of a chain hierarchy.**  At every level `k ≤ N` a
`ChainUniformTubeSet` is uniform at the chain scale `σ k` in the unbundled sense of
`Tube.IsUniformAtScale`, with the constant squared (see `card_filter_le`). -/
def ChainUniformTubeSet.uniformAt {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {σ : ℕ → NNReal} {C : NNReal} (𝒰 : ChainUniformTubeSet s T N σ C) (hC : 1 ≤ C)
    {k : ℕ} (hk : k ≤ N) : Tube.IsUniformAtScale s T (σ k) (C ^ 2) := by
  have hC_le_Csq : C ≤ C ^ 2 := by
    calc C = C ^ 1 := by rw [pow_one]
      _ ≤ C ^ 2 := pow_le_pow_right₀ hC (by norm_num : (1 : ℕ) ≤ 2)
  exact {
    branchingN := 𝒰.branchingN k
    parent := 𝒰.cover.indexSet k
    parentTube := 𝒰.cover.tube k
    exists_le_rescale := by
      intro i hi
      exact ⟨𝒰.cover.assign k i, 𝒰.cover.assign_mem k hk i hi, 𝒰.cover.le_tube_assign k hk i hi⟩
    boundedOverlap := by
      intro V
      exact (𝒰.boundedOverlap k hk V).trans hC_le_Csq
    parentTube_injOn := 𝒰.tube_injOn k hk
    card_filter_le := fun hj => 𝒰.card_filter_le hC hk hj
    le_mul_card_filter := fun hj => 𝒰.le_mul_card_filter hC hk hj
  }

/-- **The tight-net side condition** along a chain: the scale-parameterized form of
`Tube.UniformTubeSet.Nice`. -/
def ChainUniformTubeSet.Nice {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {σ : ℕ → NNReal} {C : NNReal} (𝒰 : ChainUniformTubeSet s T N σ C) : Prop :=
  ∀ k ≤ N, ∀ V : Tube (σ k) E,
    (open scoped Classical in
      (𝒰.cover.indexSet k).filter (fun v => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k v).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
          Tube.overlapConstBOTight (Module.finrank ℝ E)

/-- Weakening the constant, along a chain. -/
def ChainUniformTubeSet.mono {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {σ : ℕ → NNReal} {C C' : NNReal} (𝒰 : ChainUniformTubeSet s T N σ C) (hC : C ≤ C') :
    ChainUniformTubeSet s T N σ C' where
  cover := 𝒰.cover
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlap k hk V := (𝒰.boundedOverlap k hk V).trans hC
  card_class_le k hk j hj := (𝒰.card_class_le k hk j hj).trans (mul_le_mul_left hC _)
  le_card_class k hk j hj := (𝒰.le_card_class k hk j hj).trans (mul_le_mul_left hC _)

/-- **Restricting a uniform set of tubes to a subchain.**  Together with `UniformTubeSet.toChain`
this is what makes a bundled hierarchy available along a cut chain: `𝒰.toChain.restrict c M …` is a
`ChainUniformTubeSet` along `fun m => gridScale δ N (c m)`. -/
def ChainUniformTubeSet.restrict {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {σ : ℕ → NNReal} {C : NNReal} (𝒰 : ChainUniformTubeSet s T N σ C) (c : ℕ → ℕ) (M : ℕ)
    (hmono : ∀ m, m + 1 ≤ M → c m ≤ c (m + 1)) (hcN : ∀ m, m ≤ M → c m ≤ N) :
    ChainUniformTubeSet s T M (fun m => σ (c m)) C where
  cover := 𝒰.cover.restrict c M hmono hcN
  branchingN m := 𝒰.branchingN (c m)
  tube_injOn m hm := 𝒰.tube_injOn (c m) (hcN m hm)
  boundedOverlap m hm V := 𝒰.boundedOverlap (c m) (hcN m hm) V
  card_class_le m hm j hj := 𝒰.card_class_le (c m) (hcN m hm) j hj
  le_card_class m hm j hj := 𝒰.le_card_class (c m) (hcN m hm) j hj

end Tubes

/-! ### Uniform shaded sets of tubes along an arbitrary chain -/

section Shaded

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

/-- **GWZ Definition 2.2 along a prescribed chain of scales**: the scale-parameterized form of
`ShadedTube.ShadedUniformTubeSet`.  Only the ambient tube hierarchy mentions the scale, so
the four branching clauses are verbatim those of the grid version. -/
structure ChainShadedUniformTubeSet {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E) (N : ℕ)
    (σ : ℕ → NNReal) (C : NNReal) where
  /-- The underlying tubes carry a uniform hierarchy along the chain `σ`. -/
  tubeUniform : ChainUniformTubeSet s (fun i => (V i).toTube) N σ C
  /-- The per-scale branching count shared across all points of the shade union. -/
  branchingN : ℕ → NNReal
  /-- The branching count of the fibre at a single point. -/
  localN : E → ℕ → NNReal
  /-- Each node met by the fibre of `x` contributes at most `C · localN x k` of its members. -/
  card_shadeClass_le : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, ∀ i ∈ s, x ∈ (V i).shade →
    ((shadeClass s V (tubeUniform.cover.assign k) (tubeUniform.cover.assign k i) x).card : NNReal)
      ≤ C * localN x k
  /-- …and at least `localN x k / C` of them. -/
  le_card_shadeClass : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, ∀ i ∈ s, x ∈ (V i).shade →
    localN x k ≤
      C * ((shadeClass s V (tubeUniform.cover.assign k)
        (tubeUniform.cover.assign k i) x).card : NNReal)
  /-- The shared count is at most a factor `C` above each local count. -/
  branchingN_le : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, branchingN k ≤ C * localN x k
  /-- Each local count is at most a factor `C` above the shared count. -/
  le_branchingN : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, localN x k ≤ C * branchingN k

/-- A shaded uniform set of tubes along the grid is one along the grid chain. -/
def ShadedUniformTubeSet.toChain {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E} {N : ℕ}
    {C : NNReal} (𝒱 : ShadedUniformTubeSet s V N C) :
    ChainShadedUniformTubeSet s V N (gridScale δ N) C where
  tubeUniform := 𝒱.tubeUniform.toChain
  branchingN := 𝒱.branchingN
  localN := 𝒱.localN
  card_shadeClass_le := 𝒱.card_shadeClass_le
  le_card_shadeClass := 𝒱.le_card_shadeClass
  branchingN_le := 𝒱.branchingN_le
  le_branchingN := 𝒱.le_branchingN

/-- …and conversely, so the grid version is exactly the special case `σ := gridScale δ N`. -/
def ChainShadedUniformTubeSet.toGrid {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E} {N : ℕ}
    {C : NNReal} (𝒱 : ChainShadedUniformTubeSet s V N (gridScale δ N) C) :
    ShadedUniformTubeSet s V N C where
  tubeUniform := 𝒱.tubeUniform.toGrid
  branchingN := 𝒱.branchingN
  localN := 𝒱.localN
  card_shadeClass_le := 𝒱.card_shadeClass_le
  le_card_shadeClass := 𝒱.le_card_shadeClass
  branchingN_le := 𝒱.branchingN_le
  le_branchingN := 𝒱.le_branchingN

end Shaded

end Tube

