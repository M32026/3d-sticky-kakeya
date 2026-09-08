/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Uniform.Tree
public import Kakeya.Density
public import Kakeya.Frostman
public import Kakeya.GridScale
public import Kakeya.Tube.Basic
public import Kakeya.Tube.IsUniformAtScale
public import Kakeya.Uniform.Pruning
public import Kakeya.Uniform.Rescale
public import Kakeya.Tube.EssentiallyDistinctReduction
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
  # Uniform tube properties

  Telescoping volume estimates and density bounds that rely on uniform-tube
  hypotheses at each scale, formulated via `Tube.IsUniformAtScale`.
  Split out of `Kakeya/Sticky.lean` to collect uniform-tube material in one
  place.

  The file collects `Tube.IsUniformAtScale` and its supporting `Tube`-level
  uniformity results. Uniformity of a
  shaded family (GWZ Definition 2.2) is
  `ShadedTube.ShadedUniformTubeSet` in
  `Kakeya/ShadedUniform.lean`, together with the shade-fibre pigeonholing it is
  built on.
-/

@[expose] public section

open MeasureTheory Real Metric ConvexSpaceBody
open scoped ENNReal

universe u

namespace Tube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ : NNReal}

/-!
## Uniform sets of tubes, read as a multiscale hierarchy

This section is the replacement for `Tube.IsUniform`.

### Why the per-scale reading is not enough

`Tube.IsUniform s T scales C` is `∀ ρ ∈ scales, Nonempty (Tube.IsUniformAtScale s T ρ C)`: it
records GWZ Definition 2.1(i)–(iii) independently at each scale and therefore relates the parent
families at different scales in *no way at all*.  The node of `𝕋_{ρ_k}` containing a given leaf need
not sit inside the node of `𝕋_{ρ_{k-1}}` containing it.

That is not the object the multiscale argument uses.  Wang–Zahl need `𝕋_{ρ_j}` to cover
`𝕋_{ρ_{j+1}}`, not merely to cover `𝕋`, and they say so explicitly: see
`blueprint/src/WZ2/250224e_K3.tex:4970`, where the covers obtained scale by scale are *repaired*
into a nested family at the cost of dilating each parent by `2ρ_{j+1}` — and where it is recorded
that after the repair the parents need no longer be essentially distinct nor form a partitioning
cover.  The blueprint's `def:indexedTubeHierarchy` is the nested object.

`UniformTubeSet` is that object: the hierarchy `cover`, together with Definition 2.1(ii)–(iii) read
directly on the *classes* of that hierarchy.  Nothing bundles a per-scale `Tube.IsUniformAtScale`,
because the containment reading of Definition 2.1(iii) cannot supply the lower bound on a class:
a node may contain members of other classes.
-/

/-! ### Classes of a cover -/

/-- The class `u⟨P⟩` of a node `P` in an index set `u` carrying an assignment: the members of `u`
assigned to `P`.  Since the assignment is a *function*, the classes partition `u` — this is what
makes GWZ Definition 2.1's cover a *partitioning* cover, and it is what the nestedness condition
below is stated against. -/
noncomputable def coverClass (u : Finset ι) (assign : ι → ι) (P : ι) : Finset ι :=
  open scoped Classical in
  u.filter (fun i => assign i = P)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Classes are monotone in the index set. -/
theorem coverClass_subset_of_subset {u v : Finset ι} (hvu : v ⊆ u) (assign : ι → ι) (P : ι) :
    coverClass v assign P ⊆ coverClass u assign P := by
  classical
  intro i hi
  simp only [coverClass, Finset.mem_filter] at hi ⊢
  exact ⟨hvu hi.1, hi.2⟩

/-! ### The nested system of covers -/

/-- **A nested system of covers along the grid** (blueprint `def:indexedTubeHierarchy`).

At each grid index `k ≤ N` the members of `t` are *assigned* to nodes, each node is a tube of the
exact grid radius `ρ_k`, and the classes refine as the scale gets finer: if two members share a node
at index `k+1` they share one at index `k`.  That last clause is the content Wang–Zahl have to
repair by hand (`WZ2/250224e_K3.tex:4970`) and is exactly what a per-scale uniformity predicate
cannot supply. -/
structure GridCoverSystem {δ : NNReal} (t : Finset ι) (T : ι → Tube δ E) (N : ℕ) where
  /-- The index set of the nodes at each grid scale. -/
  indexSet : ℕ → Finset ι
  /-- The node of scale `ρ_k` to which a member of `t` is assigned. -/
  assign : ℕ → ι → ι
  /-- The node itself, a tube of the exact grid radius `ρ_k`. -/
  tube : (k : ℕ) → ι → Tube (gridScale δ N k) E
  /-- Every member of `t` is assigned to an actual node. -/
  assign_mem : ∀ k, k ≤ N → ∀ i ∈ t, assign k i ∈ indexSet k
  /-- A member lies inside the node it is assigned to (factor-`1` containment). -/
  le_tube_assign : ∀ k, k ≤ N → ∀ i ∈ t,
    (T i).toConvexSpaceBody ≤ (tube k (assign k i)).toConvexSpaceBody
  /-- The classes refine as the scale gets finer. -/
  nested : ∀ k, k + 1 ≤ N → ∀ i ∈ t, ∀ j ∈ t,
    assign (k + 1) i = assign (k + 1) j → assign k i = assign k j
  /-- …and so do the nodes themselves: a member's node at index `k+1` lies inside its node at index
  `k`.  The tower builder supplies this alongside the index-level clause at no extra cost, and it is
  what makes `Tube.UniformTubeSet.nodesUnder` the faithful `𝕋_b[T_a]`, with no inflation of
  the container. -/
  tube_nested : ∀ k, k + 1 ≤ N → ∀ i ∈ t,
    (tube (k + 1) (assign (k + 1) i)).toConvexSpaceBody ≤
      (tube k (assign k i)).toConvexSpaceBody

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Iterated nestedness.**  Two members sharing a node at a fine grid level share one at every
coarser level. -/
theorem GridCoverSystem.assign_eq_of_le {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    (G : GridCoverSystem s T N) {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ N) {i i' : ι}
    (hi : i ∈ s) (hi' : i' ∈ s) (h : G.assign l i = G.assign l i') :
    G.assign k i = G.assign k i' := by
  revert hl h
  induction l, hkl using Nat.le_induction with
  | base => exact fun _ h => h
  | succ m _ ih => exact fun hm1N h => ih (by omega) (G.nested m hm1N i hi i' hi' h)

/-! ### Uniform sets of tubes -/

/-- **GWZ Definition 2.1, read as a multiscale hierarchy.**  `cover` is the nested system of covers,
carrying Definition 2.1(i); the remaining fields are Definition 2.1(ii) (bounded overlap) and (iii)
(constant branching), both read on the grid range `k ≤ N` only, since below `δ` a nonempty family
admits no uniform structure at all.  A single constant `C` governs both. -/
structure UniformTubeSet {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) (N : ℕ) (C : NNReal) where
  /-- The nested system of covers along the grid `ρ_k = δ^{k/N}`.  This subsumes Definition 2.1(i)
  (Cover): `assign_mem` and `le_tube_assign` say every member lies in the node it is assigned to,
  which is the containment (i) asks for, and more, since the assignment is a function and the
  classes therefore *partition* `s` — WZ's "partitioning cover". -/
  cover : GridCoverSystem s T N
  /-- The branching number at each grid scale. -/
  branchingN : ℕ → NNReal
  /-- Distinct node indices name distinct node tubes: the injective indexing of `𝕋_ρ` required in
  the preamble of Definition 2.1. -/
  tube_injOn : ∀ k ≤ N, Set.InjOn (cover.tube k) (cover.indexSet k : Set ι)
  /-- **Definition 2.1(ii) (Bounded overlap).**  For every `ρ_k`-tube `V`, at most `C` nodes *meet
  `V` through `s`* — share a member of `s` with it.  This is the achievable `∼1`-multiplicity
  content of (ii); it replaces the requirement that the nodes be pairwise essentially distinct,
  which is unsatisfiable while preserving cardinality. -/
  boundedOverlap : ∀ k ≤ N, ∀ V : Tube (gridScale δ N k) E,
    (open scoped Classical in
      (cover.indexSet k).filter (fun j => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (cover.tube k j).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤ C
  /-- **Definition 2.1(iii) (Constant branching), upper half.**  Stated on the *class* of a node —
  the members assigned to it — not on the larger set of members merely contained in it.  That is the
  partitioning-cover reading, and it is the object the two every-scale conditions are stated
  against. -/
  card_class_le : ∀ k ≤ N, ∀ j ∈ cover.indexSet k,
    ((coverClass s (cover.assign k) j).card : NNReal) ≤ C * branchingN k
  /-- **Definition 2.1(iii), lower half.**  This is the direction that the containment reading
  cannot supply: a node may contain members of other classes, so a lower bound on the contained set
  says nothing about the class. -/
  le_card_class : ∀ k ≤ N, ∀ j ∈ cover.indexSet k,
    branchingN k ≤ C * ((coverClass s (cover.assign k) j).card : NNReal)

/-- **The tight-net side condition.**  Split off from `UniformTubeSet` because it is internal to the
re-uniformization machinery: only boundedly many nodes meet a common tube of the same radius, with
the *tight* dimensional constant rather than the ambient `C`.  Every system built in this
development comes from a tight grid net, so the condition costs nothing to supply and is preserved
by restriction.  Node distinctness is not repeated here — it is the `tube_injOn` field. -/
def UniformTubeSet.Nice {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : UniformTubeSet s T N C) : Prop :=
  ∀ k ≤ N, ∀ V : Tube (gridScale δ N k) E,
    (open scoped Classical in
      (𝒰.cover.indexSet k).filter (fun v => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k v).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
          Tube.overlapConstBOTight (Module.finrank ℝ E)

/-- Weakening the constant.  The hierarchy, the nodes and the branching numbers are unchanged, which
matters at the call sites that compare the nodes of two bundles. -/
def UniformTubeSet.mono {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C C' : NNReal} (𝒰 : UniformTubeSet s T N C) (hC : C ≤ C') : UniformTubeSet s T N C' where
  cover := 𝒰.cover
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlap k hk V := (𝒰.boundedOverlap k hk V).trans hC
  card_class_le k hk j hj := (𝒰.card_class_le k hk j hj).trans (mul_le_mul_left hC _)
  le_card_class k hk j hj := (𝒰.le_card_class k hk j hj).trans (mul_le_mul_left hC _)

/-!
### Why the class reading, and not the containment reading

The class bracket implies the containment bracket `{i ∈ s | T i ≤ tube k j}` of the per-scale
reading, with `C ^ 2` in place of `C`, but not conversely.  Upwards is immediate, since
`le_tube_assign` puts each class inside its own node.  Downwards: if `T i` lies in the node `j`,
then the node `j' = assign k i` that `i` is actually assigned to shares the member `i` with
`tube k j`, so `j'` is one of the at most `C` nodes that Definition 2.1(ii) permits to meet
`tube k j` through `s`; summing the class bound over those `C` nodes bounds the contained set by
`C ^ 2 * branchingN k`.  The lower direction needs nothing, the class being a subset of the
contained set.

This is why the class reading is the one stored: it is strictly stronger, it is WZ's
partitioning-cover reading, and the containment reading is recoverable from it whenever some
consumer of the old per-scale API wants it.

### The nodes of one level inside a node of a coarser one
-/

/-- The nodes at grid index `b` lying inside a prescribed container `K`.

The container is an arbitrary convex body rather than a node, because the two consumers need
different ones.  Alternative (ii)-2 of Lemma 7.7(A) uses the node itself, for which
`UniformTubeSet.nodesUnder` below is the specialization.  Alternative (ii)-3 is a *lower* bound and
needs the container inflated: it is deduced from a leaf-anchored bound whose anchor
`T_{i_0}^{(2\rho)}` is twice as thick as the node, so the nodes of the members it counts are only
guaranteed to lie in a bounded dilate of the node, and inflating an anchor is exactly what a lower
bound cannot absorb after the fact. -/
noncomputable def UniformTubeSet.nodesIn {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : UniformTubeSet s T N C) (b : ℕ) (K : ConvexSpaceBody E) : Finset ι :=
  open scoped Classical in
  (𝒰.cover.indexSet b).filter (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody ≤ K)

/-- WZ's `𝕋_b[T_a]`: the nodes at grid index `b` lying inside the node `j` at the coarser index `a`
(`blueprint/src/WZ2/250224e_K3.tex:365`, read on the cover rather than on `𝕋`).

Containment is literal, with no inflation of the container.  That is available because
`GridCoverSystem.tube_nested` carries the nesting of the nodes themselves; it is precisely the
clause Wang–Zahl have to restore by hand at the cost of a `2ρ` dilation (`:4970`). -/
noncomputable def UniformTubeSet.nodesUnder {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : UniformTubeSet s T N C) (b a : ℕ) (j : ι) : Finset ι :=
  𝒰.nodesIn b (𝒰.cover.tube a j).toConvexSpaceBody

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem UniformTubeSet.nodesUnder_eq_nodesIn {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : UniformTubeSet s T N C) (b a : ℕ) (j : ι) :
    𝒰.nodesUnder b a j = 𝒰.nodesIn b (𝒰.cover.tube a j).toConvexSpaceBody := rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem UniformTubeSet.mem_nodesIn_iff {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : UniformTubeSet s T N C) (b : ℕ) (K : ConvexSpaceBody E) (j' : ι) :
    j' ∈ 𝒰.nodesIn b K ↔
      j' ∈ 𝒰.cover.indexSet b ∧ (𝒰.cover.tube b j').toConvexSpaceBody ≤ K := by
  classical
  simp [UniformTubeSet.nodesIn]

/-! Weakening the constant changes nothing a consumer can see.  These are all `rfl`, but they are
stated so that the assembly of Lemma 7.7 can rewrite with them: unfolding
`Tube.UniformTubeSet.mono` with `simp` instead forces the whole structure open and exhausts
the heartbeat budget. -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem UniformTubeSet.mono_cover {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C C' : NNReal} (𝒰 : UniformTubeSet s T N C) (hC : C ≤ C') :
    (𝒰.mono hC).cover = 𝒰.cover := rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem UniformTubeSet.mono_nodesUnder {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C C' : NNReal} (𝒰 : UniformTubeSet s T N C) (hC : C ≤ C') (b a : ℕ) (j : ι) :
    (𝒰.mono hC).nodesUnder b a j = 𝒰.nodesUnder b a j := rfl

/-! ### The contained set of a node, and the containment bracket -/

/-- **The nodes meeting a tube through `s`** (blueprint `def:meetingNodes`).

For a grid index `k` and a `ρ_k`-tube `V`, the set of nodes at index `k` that *meet `V` through
`s`*: those sharing a member of the family with `V`, that is, those `j` for which some `i ∈ s`
has `T i ⊆ tube k j` and `T i ⊆ V`.

This is a name for the object `Tube.UniformTubeSet.boundedOverlap` already quantifies
over — the same `Finset.filter` — so that the field is literally a bound on its cardinality
(`Tube.UniformTubeSet.card_meetingNodes_le`).

The relativization by `s` is essential and not a convenience: bare intersection with `V` is not
a bounded condition, a fixed `ρ_k`-tube being met, as a set, by `ρ_k`-tubes of every direction. -/
noncomputable def UniformTubeSet.meetingNodes {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C) (k : ℕ)
    (V : Tube (gridScale δ N k) E) : Finset ι :=
  open scoped Classical in
  (𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ s,
    (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
    (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Definition 2.1(ii) as a bound on `Tube.UniformTubeSet.meetingNodes`.**

The bounded-overlap field, read at the named object.  It is the same `Finset` on both sides. -/
theorem UniformTubeSet.card_meetingNodes_le {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C) {k : ℕ} (hk : k ≤ N)
    (V : Tube (gridScale δ N k) E) :
    ((𝒰.meetingNodes k V).card : NNReal) ≤ C :=
  𝒰.boundedOverlap k hk V

/-- **Definition 2.1(ii) for a family that is not a hierarchy** (blueprint
`def:ml1bootParentBoundedOverlap`).

A family `𝕍_ρ = (Vρ k)_{k ∈ t}` of `ρ`-tubes has *overlap bounded by `Co` through
`𝕍 = (V i)_{i ∈ s}`* when, for every `ρ`-tube `W`, at most `Co` members of `𝕍_ρ` *meet `W`
through `𝕍`* — share a member of `𝕍` with it.

This is `Tube.UniformTubeSet.boundedOverlap` transcribed off the nodes of a hierarchy
word for word: taking `t` to be a node index set, `Vρ` the node tubes at that grid index and `V`
the leaves recovers the field exactly, which is what
`Kakeya.ml1Boot.hasBoundedOverlap_nodes` records. It lives here rather than downstream because
it is the same condition as the field, and because both a free family and a hierarchy's nodes
have to be able to supply it.

The relativization by `𝕍` is what makes the condition satisfiable at all: bare intersection with
`W` is not a bounded condition, a fixed `ρ`-tube being met, as a set, by `ρ`-tubes of every
direction.

It is the achievable `∼1`-multiplicity content of Definition 2.1(ii), and it is what the nodes
of a hierarchy carry *instead of* pairwise essential distinctness, which they cannot satisfy
while preserving cardinality. -/
def HasBoundedOverlap {κ : Type*} {σ ρ : NNReal} (s : Finset ι) (V : ι → Tube σ E)
    (t : Finset κ) (Vρ : κ → Tube ρ E) (Co : NNReal) : Prop :=
  ∀ W : Tube ρ E,
    ((open scoped Classical in
      t.filter (fun k => ∃ i ∈ s,
        (V i).toConvexSpaceBody ≤ (Vρ k).toConvexSpaceBody ∧
        (V i).toConvexSpaceBody ≤ W.toConvexSpaceBody)).card : NNReal) ≤ Co

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The class of a node lies in its contained set** (blueprint
`lem:classSubsetContainmentSet`).

If `i` is assigned to `j` at the grid index `k` then `T i` lies in the node tube `tube k j`, by
clause (b) of `Tube.GridCoverSystem`; so the class of `j` is contained in the *contained
set* `s[j] = Kakeya.familyIn s _ (tube k j)`.  The reverse inclusion is exactly what fails, and
what `Tube.UniformTubeSet.familyIn_subset_biUnion_meetingNodes` repairs at the cost of a
bounded overlap. -/
theorem coverClass_subset_familyIn {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    (cov : GridCoverSystem t T N) {k : ℕ} (hk : k ≤ N) (j : ι) :
    coverClass t (cov.assign k) j ⊆
      Kakeya.familyIn t (fun i => (T i).toConvexSpaceBody)
        (cov.tube k j).toConvexSpaceBody := by
  classical
  intro i hi
  simp only [coverClass, Kakeya.familyIn, Finset.mem_filter] at hi ⊢
  rcases hi with ⟨hit, hiassign⟩
  constructor
  · exact hit
  · have h := cov.le_tube_assign k hk i hit
    simpa [← hiassign] using h

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The contained set is covered by the classes of the meeting nodes** (blueprint
`lem:containmentSetCoveredByMeetingClasses`).

If `T i ⊆ tube k j` then the node `j' = assign k i` that `i` is actually assigned to shares the
member `i` with `tube k j`, so `j'` meets `tube k j` through `s`; and `i` lies in the class of
`j'`.  The companion bound `|meetingNodes| ≤ C` is
`Tube.UniformTubeSet.card_meetingNodes_le` and is not restated here. -/
theorem UniformTubeSet.familyIn_subset_biUnion_meetingNodes [DecidableEq ι] {δ : NNReal}
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C)
    {k : ℕ} (hk : k ≤ N) (j : ι) :
    Kakeya.familyIn s (fun i => (T i).toConvexSpaceBody)
        (𝒰.cover.tube k j).toConvexSpaceBody
      ⊆ (𝒰.meetingNodes k (𝒰.cover.tube k j)).biUnion
          (fun j' => coverClass s (𝒰.cover.assign k) j') := by
  intro i hi
  rw [Kakeya.familyIn, Finset.mem_filter] at hi
  rw [Finset.mem_biUnion]
  refine ⟨𝒰.cover.assign k i, ?_hnodes, ?_hcls⟩
  · rw [UniformTubeSet.meetingNodes, Finset.mem_filter]
    refine ⟨𝒰.cover.assign_mem k hk i hi.1, ⟨i, hi.1, ?_, hi.2⟩⟩
    exact 𝒰.cover.le_tube_assign k hk i hi.1
  · letI : DecidablePred (fun a : ι => 𝒰.cover.assign k a = 𝒰.cover.assign k i) :=
      fun a => Classical.propDecidable _
    rw [coverClass, Finset.mem_filter]
    exact ⟨hi.1, rfl⟩

/-- **Upper half of the containment bracket** (blueprint `lem:containmentBracketUpper`).

The class bracket of `Tube.UniformTubeSet` implies the containment bracket of the
per-scale reading, with `C ^ 2` in place of `C`: bound the contained set by the union of the
classes of the meeting nodes
(`Tube.UniformTubeSet.familyIn_subset_biUnion_meetingNodes`), each class by
`C * branchingN k` (`Tube.UniformTubeSet.card_class_le`), and the number of meeting
nodes by `C` (`Tube.UniformTubeSet.card_meetingNodes_le`).

The converse fails for every constant; blueprint `note:classVersusContainmentReading` carries
the witness.  This is the form the Case (ii) node counting of
`Kakeya.ml1Boot.branching_mul_card_nodesIn_le` consumes. -/
theorem UniformTubeSet.card_familyIn_le [DecidableEq ι] {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C)
    {k : ℕ} (hk : k ≤ N) (j : ι) :
    ((Kakeya.familyIn s (fun i => (T i).toConvexSpaceBody)
        (𝒰.cover.tube k j).toConvexSpaceBody).card : NNReal)
      ≤ C ^ 2 * 𝒰.branchingN k := by
  let F := 𝒰.meetingNodes k (𝒰.cover.tube k j)
  let cls : ι → Finset ι := fun j' => coverClass s (𝒰.cover.assign k) j'
  calc
    ((Kakeya.familyIn s (fun i => (T i).toConvexSpaceBody)
        (𝒰.cover.tube k j).toConvexSpaceBody).card : NNReal)
      ≤ ((F.biUnion cls).card : NNReal) := by
        exact_mod_cast
          (Finset.card_le_card (𝒰.familyIn_subset_biUnion_meetingNodes hk j))
    _ ≤ ((∑ x ∈ F, (cls x).card : ℕ) : NNReal) := by
        exact_mod_cast
          (show (F.biUnion cls).card ≤ ∑ x ∈ F, (cls x).card
            from Finset.card_biUnion_le)
    _ = ∑ x ∈ F, ((cls x).card : NNReal) := by
        simp [Nat.cast_sum]
    _ ≤ ∑ x ∈ F, (C * 𝒰.branchingN k : NNReal) := by
        refine Finset.sum_le_sum ?_
        intro x hx
        exact 𝒰.card_class_le k hk x (by
          have hmem : x ∈ (𝒰.cover.indexSet k).filter
              (fun j' => ∃ i ∈ s,
                (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j').toConvexSpaceBody ∧
                (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody) := by
            simpa [F, UniformTubeSet.meetingNodes] using hx
          exact (Finset.mem_filter.mp hmem).1)
    _ = (F.card : NNReal) * (C * 𝒰.branchingN k) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ C * (C * 𝒰.branchingN k) := by
        exact mul_le_mul'
          (by simpa [F] using 𝒰.card_meetingNodes_le hk (𝒰.cover.tube k j))
          (le_rfl : (C * 𝒰.branchingN k) ≤ (C * 𝒰.branchingN k))
    _ = C ^ 2 * 𝒰.branchingN k := by ring

/-! ### The refinement lemma -/

/-- The uniformity constant produced by multiscale uniformization: it depends only on the
ambient dimension. -/
def uniformConst (n : ℕ) : NNReal := max 2 ((Tube.overlapConstBOTight n : ℕ) : NNReal)

theorem one_le_uniformConst (n : ℕ) : 1 ≤ uniformConst n := by
  rw [uniformConst]
  exact le_trans (by norm_num : (1 : NNReal) ≤ 2) (le_max_left 2 _)

/-- **Every family of `δ`-tubes in `B_1` has a uniform subfamily** (the replacement of
`Tube.refineToEssDistinctUniform`, strengthened to produce the *nested* object).  Nothing is assumed
beyond containment in `B_1` — no essential distinctness and no carrier injectivity — and the
retained share is a polylogarithm in `#s`.  Both `A` and the uniformity constant
`uniformConst (Module.finrank ℝ E)` are fixed before `N` and `δ`. -/
theorem exists_uniformTubeSet_subfamily :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ {ι : Type u} {δ : NNReal} (N : ℕ), 0 < δ → 0 < N →
      δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∃ s' ⊆ s,
        (s.card : ℝ)
            ≤ (A * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1)) ^ N * (s'.card : ℝ) ∧
          Nonempty (UniformTubeSet s' T N (uniformConst (Module.finrank ℝ E))) := by
  classical
  set n := Module.finrank ℝ E with hn
  set C₀ : ℝ := (641 : ℝ) ^ (2 * n) * (4 : ℝ) ^ (2 * n) with hC₀_def
  set Cu : NNReal := uniformConst n with hCu_def
  have hA : (1 : ℝ) ≤ C₀ := by
    rw [hC₀_def]
    calc
      (1 : ℝ) ≤ (641 : ℝ) ^ (2 * n) := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 641)
      _ ≤ (641 : ℝ) ^ (2 * n) * (4 : ℝ) ^ (2 * n) := by
        calc
          (641 : ℝ) ^ (2 * n) = (641 : ℝ) ^ (2 * n) * 1 := by rw [mul_one]
          _ ≤ (641 : ℝ) ^ (2 * n) * (4 : ℝ) ^ (2 * n) :=
            mul_le_mul_of_nonneg_left
              (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4))
              (by positivity : (0 : ℝ) ≤ (641 : ℝ) ^ (2 * n))
  have hCu1 : (1 : NNReal) ≤ Cu := by
    rw [hCu_def]
    exact le_trans (by norm_num : (1 : NNReal) ≤ 2) (le_max_left _ _)
  refine ⟨C₀, hA, ?_⟩
  intro ι δ N hδ hN hδ0 s T hs_B1
  by_cases hs_empty : s = ∅
  · subst s
    refine ⟨∅, by simp, ?_, ?_⟩
    · simp
    · exact ⟨{
        cover := {
          indexSet := fun _ => ∅
          assign := fun _ => id
          tube := fun k i => (T i).rescale (gridScale δ N k)
          assign_mem := by intro k hk i hi; exact False.elim (Finset.notMem_empty i hi)
          le_tube_assign := by intro k hk i hi; exact False.elim (Finset.notMem_empty i hi)
          nested := by intro k hk i hi j hj h; exact False.elim (Finset.notMem_empty i hi)
          tube_nested := by intro k hk i hi; exact False.elim (Finset.notMem_empty i hi)
        }
        branchingN := fun _ => 0
        tube_injOn := by intro k hk a ha; simp at ha
        boundedOverlap := by intro k hk V; simp
        card_class_le := by intro k hk j hj; exact False.elim (Finset.notMem_empty j hj)
        le_card_class := by intro k hk j hj; exact False.elim (Finset.notMem_empty j hj)
      }⟩
  · have hs_ne : s.Nonempty := (Finset.nonempty_iff_ne_empty).mpr hs_empty
    have hδ1 : δ < 1 := by
      have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : (1 : ℕ) ≤ N)
      have h16le : (16 : NNReal) ^ (-(N : ℝ)) ≤ (16 : NNReal) ^ (-(1 : ℝ)) := by
        exact NNReal.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : NNReal) ≤ 16) (neg_le_neg hNge1)
      have h16inv : (16 : NNReal) ^ (-(1 : ℝ)) = (1 : NNReal) / 16 := by
        rw [NNReal.rpow_neg, NNReal.rpow_one]
        norm_num
      have hδle16 : (δ : NNReal) ≤ (1 : NNReal) / 16 := by
        calc
          δ ≤ (16 : NNReal) ^ (-(N : ℝ)) := hδ0
          _ ≤ (16 : NNReal) ^ (-(1 : ℝ)) := h16le
          _ = (1 : NNReal) / 16 := h16inv
      have h16lt : (1 : NNReal) / 16 < 1 := by norm_num
      exact lt_of_le_of_lt hδle16 h16lt
    have hδnonneg : (0 : ℝ) ≤ (δ : ℝ) := le_of_lt (by exact_mod_cast hδ)
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
    have hgap : (δ : ℝ) ^ ((1 : ℝ) / (N : ℝ)) ≤ 1 / 2 := by
      have hδle16R : (δ : ℝ) ≤ (16 : ℝ) ^ (-(N : ℝ)) := by
        have hcast : (δ : ℝ) ≤ (((16 : NNReal) ^ (-(N : ℝ)) : NNReal) : ℝ) :=
          NNReal.coe_le_coe.mpr hδ0
        simpa [NNReal.coe_rpow] using hcast
      have h16exp : (16 : ℝ) ^ ((-(N : ℝ)) * ((1 : ℝ) / (N : ℝ))) = (1 : ℝ) / 16 := by
        have hprod : (-(N : ℝ)) * ((1 : ℝ) / (N : ℝ)) = -1 := by
          field_simp [hNne]
        rw [hprod]
        norm_num
      have hstep1 : (δ : ℝ) ^ ((1 : ℝ) / (N : ℝ)) ≤
          ((16 : ℝ) ^ (-(N : ℝ))) ^ ((1 : ℝ) / (N : ℝ)) :=
        Real.rpow_le_rpow hδnonneg hδle16R (by positivity : 0 ≤ (1 : ℝ) / (N : ℝ))
      have hstep2 : ((16 : ℝ) ^ (-(N : ℝ))) ^ ((1 : ℝ) / (N : ℝ)) = (1 : ℝ) / 16 := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 16) (-(N : ℝ)) ((1 : ℝ) / (N : ℝ))]
        exact h16exp
      calc
        (δ : ℝ) ^ ((1 : ℝ) / (N : ℝ)) ≤ ((16 : ℝ) ^ (-(N : ℝ))) ^ ((1 : ℝ) / (N : ℝ)) := hstep1
        _ = (1 : ℝ) / 16 := hstep2
        _ ≤ 1 / 2 := by norm_num
    set ρ : ℕ → NNReal := fun k => δ ^ ((k : ℝ) / (N : ℝ)) with hρ_def
    obtain ⟨parent, assign, W, h_assign_mem, h_nested, h_cover, h_injOn, h_overlap, hPcard,
        h_body_nest⟩ :=
      Tube.exists_multiscale_tube_tree_bo_tight_dup hδ hδ1 s T N hN hgap hs_B1 hs_ne
    have hC₀_pos : (0 : ℝ) < C₀ := by rw [hC₀_def]; positivity
    have hC₀ : ((parent 0).card : ℝ) ≤ C₀ := by
      rw [hC₀_def]
      have h := hPcard 0 hN
      have hρ0 : ((ρ 0 : NNReal) : ℝ) = 1 := by
        rw [hρ_def]
        simp
      have hfour : ((4 : ℝ) / ((ρ 0 : NNReal) : ℝ)) ^ (2 * n) = (4 : ℝ) ^ (2 * n) := by
        rw [hρ0]
        norm_num
      rwa [hfour] at h
    obtain ⟨s', N₂, parent', hs'_sub, hs'_card, h_parent'_sub, h_assign'_mem, h_active, h_band⟩ :=
      Tube.exists_pruned_subset_noroot_notop s N hs_ne parent assign h_assign_mem h_nested C₀
        hC₀_pos hC₀
    set B : ℝ := (⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1 with hB_def
    have hBpos : (0 : ℝ) < B := by
      rw [hB_def]
      positivity
    have hcard_step : (s.card : ℝ) ≤ C₀ * (B ^ N) * (s'.card : ℝ) := by
      have hd : (0 : ℝ) < C₀ * (B ^ N) := mul_pos hC₀_pos (pow_pos hBpos N)
      have hadiv := (div_le_iff₀ hd).mp hs'_card
      calc
        (s.card : ℝ) ≤ (s'.card : ℝ) * (C₀ * (B ^ N)) := hadiv
        _ = C₀ * (B ^ N) * (s'.card : ℝ) := by ring
    have hcard_final : (s.card : ℝ) ≤ (C₀ * B) ^ N * (s'.card : ℝ) := by
      have hCN : C₀ ≤ C₀ ^ N := by
        have h1N : (1 : ℕ) ≤ N := by omega
        calc
          C₀ = C₀ ^ 1 := by rw [pow_one]
          _ ≤ C₀ ^ N := pow_le_pow_right₀ hA h1N
      have hBN : 0 ≤ B ^ N := (pow_pos hBpos N).le
      have hmul : C₀ * B ^ N ≤ (C₀ * B) ^ N := by
        calc
          C₀ * B ^ N ≤ C₀ ^ N * B ^ N := mul_le_mul_of_nonneg_right hCN hBN
          _ = (C₀ * B) ^ N := (mul_pow C₀ B N).symm
      calc
        (s.card : ℝ) ≤ C₀ * (B ^ N) * (s'.card : ℝ) := hcard_step
        _ ≤ (C₀ * B) ^ N * (s'.card : ℝ) :=
          mul_le_mul_of_nonneg_right hmul (by positivity : 0 ≤ (s'.card : ℝ))
    have hC2 : (2 : NNReal) ≤ Cu := by rw [hCu_def]; exact le_max_left 2 _
    have hCop : (Tube.overlapConstBOTight n : NNReal) ≤ Cu := by
      rw [hCu_def]
      exact le_max_right 2 ((Tube.overlapConstBOTight n : ℕ) : NNReal)
    let gcs : GridCoverSystem s' T N := {
      indexSet := parent'
      assign := assign
      tube := W
      assign_mem := by intro k hk i hi; exact h_assign'_mem k hk hi
      le_tube_assign := by intro k hk i hi; exact h_cover k hk (hs'_sub hi)
      nested := by
        intro k hk i hi j hj hij
        exact h_nested k (by omega) (hs'_sub hi) (hs'_sub hj) hij
      tube_nested := by intro k hk i hi; exact h_body_nest k (by omega) (hs'_sub hi)
    }
    refine ⟨s', hs'_sub, hcard_final, ⟨{
      cover := gcs
      branchingN := fun k => (N₂ k : NNReal)
      tube_injOn := by
        intro k hk
        exact Set.InjOn.mono (Finset.coe_subset.mpr (h_parent'_sub k hk)) (h_injOn k hk)
      boundedOverlap := by
        intro k hk V
        have hsub : ((parent' k).filter (fun j => ∃ i ∈ s',
              (T i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody ∧
              (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)) ⊆
            ((parent k).filter (fun j => ∃ i ∈ s,
              (T i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody ∧
              (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)) := by
          intro v hv
          rw [Finset.mem_filter] at hv ⊢
          obtain ⟨hv_par, i, hi_s', hPV⟩ := hv
          exact ⟨h_parent'_sub k hk hv_par, i, hs'_sub hi_s', hPV⟩
        have hlecard : ((parent' k).filter (fun j => ∃ i ∈ s',
              (T i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody ∧
              (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
            Tube.overlapConstBOTight n :=
          le_trans (Finset.card_le_card hsub) (h_overlap k hk V)
        calc
          ((parent' k).filter (fun j => ∃ i ∈ s',
              (T i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody ∧
              (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card
            ≤ (Tube.overlapConstBOTight n : NNReal) := by exact_mod_cast hlecard
          _ ≤ Cu := hCop
      card_class_le := by
        intro k hk j hj
        have hband := h_band k hk j hj
        have hle : ((coverClass s' (assign k) j).card : NNReal) ≤ 2 * (N₂ k : NNReal) := by
          have h : (coverClass s' (assign k) j).card ≤ 2 * N₂ k := by
            simpa [coverClass] using (le_of_lt hband.2)
          exact_mod_cast h
        exact le_trans hle (mul_le_mul_of_nonneg_right hC2 (by positivity : 0 ≤ (N₂ k : NNReal)))
      le_card_class := by
        intro k hk j hj
        have hband := h_band k hk j hj
        have hNle : (N₂ k : NNReal) ≤ ((coverClass s' (assign k) j).card : NNReal) := by
          have h : N₂ k ≤ (coverClass s' (assign k) j).card := by
            simpa [coverClass] using hband.1
          exact_mod_cast h
        have hle1 : ((coverClass s' (assign k) j).card : NNReal) ≤
            Cu * ((coverClass s' (assign k) j).card : NNReal) := by
          calc
            ((coverClass s' (assign k) j).card : NNReal)
                = 1 * ((coverClass s' (assign k) j).card : NNReal) := by rw [one_mul]
            _ ≤ Cu * ((coverClass s' (assign k) j).card : NNReal) :=
              mul_le_mul_of_nonneg_right hCu1 (by positivity)
        exact le_trans hNle hle1
    }⟩⟩

/-! ### The grid length of GWZ Definition 2.1 -/

/-- The grid length `⌈log log 1/δ⌉` at which GWZ Definition 2.1 is stated.  Spelled exactly as in
`StickyKakeya.StickyFrostmanEstimate`, so that `gridScales δ (ssfGridLen δ)` is *literally* the
scale set appearing there. -/
noncomputable def ssfGridLen (δ : NNReal) : ℕ := ⌈Real.log (Real.log (1 / (δ : ℝ)))⌉₊

/-- **The absorption behind every statement at the grid length `ssfGridLen δ`.**  Below a threshold
depending only on `A, K₀, m, α`: the grid length is positive, the separation `δ ≤ 16^{-N}` demanded
by `exists_uniformTubeSet_subfamily` holds at `N = ssfGridLen δ`, and a polylogarithmic loss raised
to any power linear in `N` is at most `δ^{-α}`, because `(log log x)^2 / log x → 0`. -/
theorem exists_threshold_polylog_pow_ssfGridLen_le (A : ℝ) (hA : 1 ≤ A) (K₀ m : ℕ)
    (α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
        0 < ssfGridLen δ ∧
        δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ)) ∧
        ∀ c : ℝ, 0 ≤ c → c ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) →
          (A * ((⌊Real.logb 2 c⌋₊ : ℝ) + 1)) ^ (m * ssfGridLen δ + m) ≤ (δ : ℝ) ^ (-α) := by
  classical
  set B : ℝ := A * ((K₀ : ℝ) / Real.log 2 + 1) with hB_def
  have hBge1 : (1 : ℝ) ≤ B := by
    rw [hB_def]
    have h2 : (1 : ℝ) ≤ (K₀ : ℝ) / Real.log 2 + 1 := by
      have h0 : 0 ≤ (K₀ : ℝ) / Real.log 2 := by positivity
      linarith
    calc
      (1 : ℝ) = (1 : ℝ) * 1 := by norm_num
      _ ≤ A * ((K₀ : ℝ) / Real.log 2 + 1) :=
        mul_le_mul hA h2 (by linarith) (by linarith)
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hBge1
  have hBlog_nonneg : 0 ≤ Real.log B := (Real.log_nonneg_iff hBpos).mpr hBge1
  have hlog2 : (fun L : ℝ => (Real.log L) ^ 2) =o[Filter.atTop] (fun L : ℝ => L) :=
    Real.isLittleO_pow_log_id_atTop
  have hlog1 : (fun L : ℝ => Real.log L) =o[Filter.atTop] (fun L : ℝ => L) :=
    Real.isLittleO_log_id_atTop
  have hF₂ : (fun L : ℝ => (Real.log L + 1) * Real.log 16) =o[Filter.atTop] (fun L : ℝ => L) := by
    have hb : (fun L : ℝ => Real.log 16 + Real.log 16 * Real.log L)
        =o[Filter.atTop] (fun L : ℝ => L) :=
      (Asymptotics.isLittleO_const_id_atTop (Real.log 16)).add
        (Asymptotics.IsLittleO.const_mul_left hlog1 (Real.log 16))
    have h0 : (fun L : ℝ => (Real.log L + 1) * Real.log 16) =
        (fun L : ℝ => Real.log 16 + Real.log 16 * Real.log L) := by
      funext L
      ring
    simpa [h0.symm] using hb
  have hF₃ : (fun L : ℝ => ((m : ℝ) * (Real.log L + 1) + m) * (Real.log B + Real.log L))
      =o[Filter.atTop] (fun L : ℝ => L) := by
    have hA1 : (fun L : ℝ => (m : ℝ) * (Real.log L ^ 2)) =o[Filter.atTop] (fun L : ℝ => L) :=
      Asymptotics.IsLittleO.const_mul_left hlog2 (m : ℝ)
    have hA2 : (fun L : ℝ => (m : ℝ) * Real.log B * Real.log L) =o[Filter.atTop] (fun L : ℝ => L) :=
      Asymptotics.IsLittleO.const_mul_left hlog1 ((m : ℝ) * Real.log B)
    have hA3 : (fun L : ℝ => (2 : ℝ) * (m : ℝ) * Real.log L) =o[Filter.atTop] (fun L : ℝ => L) :=
      Asymptotics.IsLittleO.const_mul_left hlog1 ((2 : ℝ) * (m : ℝ))
    have hA4 : (fun L : ℝ => (2 : ℝ) * (m : ℝ) * Real.log B) =o[Filter.atTop] (fun L : ℝ => L) :=
      Asymptotics.isLittleO_const_id_atTop ((2 : ℝ) * (m : ℝ) * Real.log B)
    have hsum : (fun L : ℝ => (m : ℝ) * (Real.log L ^ 2) + (m : ℝ) * Real.log B * Real.log L +
        (2 : ℝ) * (m : ℝ) * Real.log L + (2 : ℝ) * (m : ℝ) * Real.log B) =o[Filter.atTop]
        (fun L : ℝ => L) := by
      exact ((((hA1.add hA2).add hA3).add hA4))
    have h0 : (fun L : ℝ => ((m : ℝ) * (Real.log L + 1) + m) * (Real.log B + Real.log L)) =
        (fun L : ℝ => (m : ℝ) * (Real.log L ^ 2) + (m : ℝ) * Real.log B * Real.log L +
          (2 : ℝ) * (m : ℝ) * Real.log L + (2 : ℝ) * (m : ℝ) * Real.log B) := by
      funext L
      ring
    simpa [h0.symm] using hsum
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℝ, 1 < L₀ ∧ (∀ L : ℝ, L₀ ≤ L → (Real.log L + 1) * Real.log 16 ≤ L) ∧
      (∀ L : ℝ, L₀ ≤ L → ((m : ℝ) * (Real.log L + 1) + m) * (Real.log B + Real.log L) ≤ α * L) := by
    have hev₂ : ∀ᶠ L in Filter.atTop, (Real.log L + 1) * Real.log 16 ≤ L := by
      have h := Asymptotics.isLittleO_iff.mp hF₂ (by norm_num : (0 : ℝ) < 1)
      filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with L hb hL1
      have hLnn : 0 ≤ L := by linarith
      have hlogL_nonneg : 0 ≤ Real.log L := Real.log_nonneg (by linarith : (1 : ℝ) ≤ L)
      have hfn : 0 ≤ (Real.log L + 1) * Real.log 16 :=
        mul_nonneg (by linarith) (Real.log_pos (by norm_num : (1 : ℝ) < 16)).le
      rw [Real.norm_eq_abs, abs_of_nonneg hfn, Real.norm_eq_abs, abs_of_nonneg hLnn] at hb
      simpa using hb
    have hev₃ : ∀ᶠ L in Filter.atTop,
        ((m : ℝ) * (Real.log L + 1) + m) * (Real.log B + Real.log L) ≤ α * L := by
      have h := Asymptotics.isLittleO_iff.mp hF₃ hα
      filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with L hb hL1
      have hLnn : 0 ≤ L := by linarith
      have hlogL_nonneg : 0 ≤ Real.log L := Real.log_nonneg (by linarith : (1 : ℝ) ≤ L)
      have hm : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
      have hfac1 : 0 ≤ (m : ℝ) * (Real.log L + 1) + m :=
        add_nonneg (mul_nonneg hm (by linarith)) hm
      have hfac2 : 0 ≤ Real.log B + Real.log L := by linarith
      have hfn : 0 ≤ ((m : ℝ) * (Real.log L + 1) + m) * (Real.log B + Real.log L) :=
        mul_nonneg hfac1 hfac2
      rw [Real.norm_eq_abs, abs_of_nonneg hfn, Real.norm_eq_abs, abs_of_nonneg hLnn] at hb
      simpa using hb
    have hev : ∀ᶠ L in Filter.atTop, 1 < L ∧ (Real.log L + 1) * Real.log 16 ≤ L ∧
        ((m : ℝ) * (Real.log L + 1) + m) * (Real.log B + Real.log L) ≤ α * L := by
      filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), hev₂, hev₃] with L hgt h₂ h₃
      exact ⟨hgt, h₂, h₃⟩
    rcases Filter.eventually_atTop.mp hev with ⟨L₀, hL₀_all⟩
    refine ⟨L₀, (hL₀_all L₀ le_rfl).1, ?_, ?_⟩
    · intro L hL; exact (hL₀_all L hL).2.1
    · intro L hL; exact (hL₀_all L hL).2.2
  set δ₀ : NNReal := Real.toNNReal (Real.exp (-L₀)) with hδ₀_def
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀_def]
    exact Real.toNNReal_pos.mpr (Real.exp_pos _)
  have hδ₀le1 : δ₀ ≤ 1 := by
    have h : (δ₀ : ℝ) ≤ 1 := by
      rw [hδ₀_def]
      rw [Real.coe_toNNReal (Real.exp (-L₀)) (Real.exp_nonneg _)]
      exact (Real.exp_le_one_iff).mpr (by linarith)
    exact NNReal.coe_le_coe.mp h
  refine ⟨δ₀, hδ₀pos, hδ₀le1, ?_⟩
  intro δ hδ hδle
  set L : ℝ := Real.log (1 / (δ : ℝ)) with hL_def
  set N : ℕ := ssfGridLen δ with hN_def
  have hδRpos : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hL : L = -Real.log (δ : ℝ) := by
    rw [hL_def, one_div]
    exact Real.log_inv (δ : ℝ)
  have hLle : L₀ ≤ L := by
    have hδleexp : (δ : ℝ) ≤ Real.exp (-L₀) := by
      have h1 : (δ : ℝ) ≤ (δ₀ : ℝ) := NNReal.coe_le_coe.mp hδle
      have hδ₀val : (δ₀ : ℝ) = Real.exp (-L₀) := by
        rw [hδ₀_def]
        exact Real.coe_toNNReal (Real.exp (-L₀)) (Real.exp_nonneg _)
      rwa [hδ₀val] at h1
    have hlogδ : Real.log (δ : ℝ) ≤ -L₀ := by
      have h := Real.log_le_log hδRpos hδleexp
      rwa [Real.log_exp] at h
    rw [hL]
    linarith
  have hLgt1 : 1 < L := by linarith
  have hNpos : 0 < ssfGridLen δ := by
    rw [ssfGridLen, ← hL_def]
    exact Nat.ceil_pos.mpr (Real.log_pos (by linarith : (1 : ℝ) < L))
  have hNle : (N : ℝ) ≤ Real.log L + 1 := by
    rw [hN_def, ssfGridLen, ← hL_def]
    have hceil : ((⌈Real.log L⌉₊ : ℕ) : ℝ) ≤ (⌊Real.log L⌋₊ : ℝ) + 1 := by
      exact_mod_cast (Nat.ceil_le_floor_add_one (Real.log L))
    have hfloor : (⌊Real.log L⌋₊ : ℝ) ≤ Real.log L :=
      Nat.floor_le (Real.log_nonneg (by linarith : (1 : ℝ) ≤ L))
    linarith
  have hL162 : (Real.log L + 1) * Real.log 16 ≤ L := hL₀.2.1 L hLle
  have hNlog16 : (N : ℝ) * Real.log 16 ≤ L := by
    calc
      (N : ℝ) * Real.log 16 ≤ (Real.log L + 1) * Real.log 16 := by
        exact mul_le_mul_of_nonneg_right hNle (Real.log_pos (by norm_num : (1 : ℝ) < 16)).le
      _ ≤ L := hL162
  have hδle16R : (δ : ℝ) ≤ (16 : ℝ) ^ (-(N : ℝ)) := by
    have hlog_comp : Real.log (δ : ℝ) ≤ Real.log ((16 : ℝ) ^ (-(N : ℝ))) := by
      rw [Real.log_rpow (by norm_num : (0 : ℝ) < 16) (-(N : ℝ))]
      linarith
    exact (Real.log_le_log_iff hδRpos
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 16) _)).mp hlog_comp
  have hδle16 : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ)) := by
    have hcoer : (δ : ℝ) ≤ (((16 : NNReal) ^ (-(ssfGridLen δ : ℝ)) : NNReal) : ℝ) := by
      simpa [NNReal.coe_rpow] using hδle16R
    exact NNReal.coe_le_coe.mp hcoer
  have h3 : ∀ c : ℝ, 0 ≤ c → c ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) →
      (A * ((⌊Real.logb 2 c⌋₊ : ℝ) + 1)) ^ (m * ssfGridLen δ + m) ≤ (δ : ℝ) ^ (-α) := by
    intro c hc0 hcle
    have hc_le_exp : c ≤ Real.exp ((K₀ : ℝ) * L) := by
      have hδr : (δ : ℝ) ^ (-(K₀ : ℝ)) = Real.exp ((K₀ : ℝ) * L) := by
        rw [Real.rpow_def_of_pos hδRpos (-(K₀ : ℝ))]
        congr 1
        rw [hL]
        ring
      rwa [hδr] at hcle
    have hRHSnonneg : 0 ≤ (K₀ : ℝ) * L / Real.log 2 := by positivity
    have hfloor_bound : (⌊Real.logb 2 c⌋₊ : ℝ) ≤ (K₀ : ℝ) * L / Real.log 2 := by
      by_cases hc1 : c < 1
      · have hfloor0 : (⌊Real.logb 2 c⌋₊ : ℕ) = 0 := by
          rw [Nat.floor_eq_zero]
          have hlogb_le : Real.logb 2 c ≤ 0 := by
            by_cases hc0' : c = 0
            · subst c
              simp [Real.logb]
            · have hcpos' : 0 < c := by
                exact lt_of_le_of_ne hc0 (Ne.symm hc0')
              have hle1 : c ≤ 1 := by linarith
              exact (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hcpos' hle1).trans_eq
                Real.logb_one
          linarith
        have hfl0 : (⌊Real.logb 2 c⌋₊ : ℝ) = 0 := by exact_mod_cast hfloor0
        linarith
      · have hc1le : 1 ≤ c := le_of_not_gt hc1
        have hcpos : 0 < c := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hc1le
        have hfloor : (⌊Real.logb 2 c⌋₊ : ℝ) ≤ Real.logb 2 c :=
          Nat.floor_le (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hc1le)
        have hlogb2 : Real.logb 2 c ≤ (K₀ : ℝ) * L / Real.log 2 := by
          have hlogb_le : Real.logb 2 c ≤ Real.logb 2 (Real.exp ((K₀ : ℝ) * L)) :=
            Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hcpos hc_le_exp
          have hlogue : Real.logb 2 (Real.exp ((K₀ : ℝ) * L)) = (K₀ : ℝ) * L / Real.log 2 := by
            rw [Real.logb, Real.log_exp]
          simpa [hlogue] using hlogb_le
        exact le_trans hfloor hlogb2
    have hA0 : 0 ≤ A := by linarith
    have hbase_le : A * ((⌊Real.logb 2 c⌋₊ : ℝ) + 1) ≤ B * L := by
      have h1 : A * ((⌊Real.logb 2 c⌋₊ : ℝ) + 1) ≤ A * ((K₀ : ℝ) * L / Real.log 2 + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hA0
      have hLge1 : (1 : ℝ) ≤ L := by linarith
      have h2 : A * ((K₀ : ℝ) * L / Real.log 2 + 1) ≤ B * L := by
        have hA_le : A ≤ A * L := by nlinarith [le_mul_of_one_le_left hA0 hLge1]
        calc
          A * ((K₀ : ℝ) * L / Real.log 2 + 1) = A * ((K₀ : ℝ) / Real.log 2 * L) + A := by
            field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
          _ ≤ A * ((K₀ : ℝ) / Real.log 2 * L) + A * L := by nlinarith
          _ = A * ((K₀ : ℝ) / Real.log 2 + 1) * L := by ring
          _ = B * L := by rw [hB_def]
      exact le_trans h1 h2
    have hbase_pos : 0 < A * ((⌊Real.logb 2 c⌋₊ : ℝ) + 1) := by positivity
    have hpow_pos : 0 < (A * ((⌊Real.logb 2 c⌋₊ : ℝ) + 1)) ^ (m * ssfGridLen δ + m) :=
      pow_pos hbase_pos _
    have hBL_pos : 0 < B * L := by positivity
    have hlogbase_le : Real.log (A * ((⌊Real.logb 2 c⌋₊ : ℝ) + 1)) ≤ Real.log (B * L) :=
      Real.log_le_log hbase_pos hbase_le
    have hlog_rpow : Real.log ((δ : ℝ) ^ (-α)) = α * L := by
      rw [Real.rpow_def_of_pos hδRpos (-α), Real.log_exp]
      rw [hL]
      ring
    have hδrpow_pos : 0 < (δ : ℝ) ^ (-α) := Real.rpow_pos_of_pos hδRpos _
    apply (Real.log_le_log_iff hpow_pos hδrpow_pos).mp
    rw [hlog_rpow]
    have hlogLHS : Real.log ((A * ((⌊Real.logb 2 c⌋₊ : ℝ) + 1)) ^ (m * ssfGridLen δ + m))
        ≤ ((m : ℝ) * (N : ℝ) + m) * Real.log (A * ((⌊Real.logb 2 c⌋₊ : ℝ) + 1)) := by
      rw [Real.log_pow, hN_def]
      norm_num
    have e_nonneg : 0 ≤ (m : ℝ) * (N : ℝ) + m := by positivity
    have hchain : ((m : ℝ) * (N : ℝ) + m) *
        Real.log (A * ((⌊Real.logb 2 c⌋₊ : ℝ) + 1)) ≤ α * L := by
      calc
        ((m : ℝ) * (N : ℝ) + m) * Real.log (A * ((⌊Real.logb 2 c⌋₊ : ℝ) + 1))
            ≤ ((m : ℝ) * (N : ℝ) + m) * Real.log (B * L) :=
              mul_le_mul_of_nonneg_left hlogbase_le e_nonneg
        _ = ((m : ℝ) * (N : ℝ) + m) * (Real.log B + Real.log L) := by
          rw [Real.log_mul (ne_of_gt hBpos) (ne_of_gt (by positivity : 0 < L))]
        _ ≤ ((m : ℝ) * (Real.log L + 1) + m) * (Real.log B + Real.log L) := by
          have hmm : (m : ℝ) * (N : ℝ) ≤ (m : ℝ) * (Real.log L + 1) :=
            mul_le_mul_of_nonneg_left hNle (by exact_mod_cast (Nat.zero_le m))
          have hmul2 : 0 ≤ Real.log B + Real.log L :=
            by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ L)]
          exact mul_le_mul_of_nonneg_right (by linarith) hmul2
        _ ≤ α * L := hL₀.2.2 L hLle
    exact le_trans hlogLHS hchain
  exact ⟨hNpos, hδle16, h3⟩

/-- **The faithful form: GWZ Definition 2.1 at its own grid length.**  The same conclusion as
`exists_uniformTubeSet_subfamily`, instantiated at the `δ`-dependent `N = ⌈log log 1/δ⌉` of GWZ
Definition 2.1 and with the loss absorbed into a prescribed `δ^{-α}`.  Two things are paid for: a
cardinality bound `#s ≤ δ^{-K₀}`, which turns the polylogarithm in `#s` into one in `1/δ`, and a
threshold `δ₀(α, K₀, n)` for the absorption, which also secures the side conditions at this `N`. -/
theorem exists_uniformTubeSet_subfamily_ssf (K₀ : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (s.card : ℝ) ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) →
      ∃ s' ⊆ s,
        (s.card : ℝ) ≤ (δ : ℝ) ^ (-α) * (s'.card : ℝ) ∧
          Nonempty (UniformTubeSet s' T (ssfGridLen δ) (uniformConst (Module.finrank ℝ E))) := by
  classical
  obtain ⟨A, hA, hsubfam⟩ := exists_uniformTubeSet_subfamily (E := E)
  obtain ⟨δ₀, hδ₀pos, hδ₀le1, hthr⟩ :=
    exists_threshold_polylog_pow_ssfGridLen_le A hA K₀ 1 α hα
  refine ⟨δ₀, hδ₀pos, hδ₀le1, ?_⟩
  intro ι δ hδ hδδ₀ s T hs_B1 hscard
  have hsAbs := hthr hδ hδδ₀
  have hNpos : 0 < ssfGridLen δ := hsAbs.1
  have hN16 : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ)) := hsAbs.2.1
  obtain ⟨s', hs'_sub, hcard, huniform⟩ :=
    hsubfam (ι := ι) (δ := δ) (ssfGridLen δ) hδ hNpos hN16 s T hs_B1
  set base : ℝ := A * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1) with hbase_def
  have hc_nonneg : (0 : ℝ) ≤ (s.card : ℝ) := by positivity
  have habs := hsAbs.2.2 (s.card : ℝ) hc_nonneg hscard
  have hbase1 : (1 : ℝ) ≤ base := by
    have hfac : (1 : ℝ) ≤ ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1) := by
      have hflr : (0 : ℝ) ≤ (⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) := by
        exact_mod_cast (Nat.zero_le (⌊Real.logb 2 (s.card : ℝ)⌋₊))
      linarith
    rw [hbase_def]
    simpa using mul_le_mul hA hfac (by norm_num) (by linarith [hA])
  have hpow : base ^ ssfGridLen δ ≤ base ^ (1 * ssfGridLen δ + 1) := by
    apply pow_le_pow_right₀ hbase1
    omega
  refine ⟨s', hs'_sub, ?_, huniform⟩
  calc
    (s.card : ℝ) ≤ base ^ ssfGridLen δ * (s'.card : ℝ) := by
      simpa [hbase_def] using hcard
    _ ≤ base ^ (1 * ssfGridLen δ + 1) * (s'.card : ℝ) := by
      exact mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ (s'.card : ℝ))
    _ ≤ (δ : ℝ) ^ (-α) * (s'.card : ℝ) := by
      exact mul_le_mul_of_nonneg_right habs (by positivity : 0 ≤ (s'.card : ℝ))

end Tube
