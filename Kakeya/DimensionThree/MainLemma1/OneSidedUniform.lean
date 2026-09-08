/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ShadedUniform

/-!
# One-sided uniformity, and why it restricts for free

`Tube.UniformTubeSet` and `ShadedTube.ShadedUniformTubeSet` are two-sided: each class bracket
is asserted in both directions.  That is what makes them fail to descend to a subfamily, and
it is the obstruction recorded on `Kakeya.ml1Boot.exists_plankDimensions_uniformSelection`:
every consumer of the plank pigeonhole has to be run at the *refined* index set `u''`, while
the middle-factor data supplies uniformity only at `u'`.

This file splits both predicates along the direction of their inequalities and keeps only the
half that survives restriction.  The resulting predicates,
`Kakeya.ml1Boot.IsOneSidedUniformTubeSet` and `Kakeya.ml1Boot.IsOneSidedUniform`, restrict to an
arbitrary subfamily with the data inherited verbatim, at **no loss in the constant and with no
pigeonholing** (`Kakeya.ml1Boot.IsOneSidedUniformTubeSet.mono_index`,
`Kakeya.ml1Boot.IsOneSidedUniform.mono_index`).  Every two-sided hierarchy projects onto them
(`Kakeya.ml1Boot.IsOneSidedUniform.of_shadedUniformTubeSet`), so the pair
"project, then restrict" replaces a re-uniformization.

## Which half survives, and why

Writing `A` for the cardinality of the class in question, the four inequalities of
`ShadedTube.ShadedUniformTubeSet` split as

| clause                | shape                     | restricts |
|-----------------------|---------------------------|-----------|
| `card_shadeClass_le`  | `A ≤ C · localN x k`      | yes       |
| `le_card_shadeClass`  | `localN x k ≤ C · A`      | no        |
| `branchingN_le`       | `branchingN k ≤ C · localN x k` | no  |
| `le_branchingN`       | `localN x k ≤ C · branchingN k` | yes |

and the three of `Tube.UniformTubeSet` as `boundedOverlap` (yes), `card_class_le` (yes),
`le_card_class` (no).

The two survivors survive for *different* reasons, and both are used below.

* `card_shadeClass_le` and `card_class_le` survive because the class is monotone in the index
  set — `Tube.coverClass_subset_of_subset` and `Kakeya.ml1Boot.shadeClass_subset_of_subset`
  below — and the clause is an *upper* bound on a quantity that shrinks.  `boundedOverlap` is
  of the same kind: its filter predicate `∃ i ∈ s, …` weakens, so the filtered node set shrinks.
* `le_branchingN` survives because it never mentions the index set at all: it relates the two
  inherited counting functions at a point.  `tube_injOn` survives for the same reason — it
  speaks about `indexSet` and the node tubes only.

Two further facts make the inheritance literal rather than approximate.  `branchingN` and
`localN` are *free fields* of the two structures, not quantities derived from the family, so a
subfamily may keep them unchanged; and the domain `⋃ i ∈ s, (V i).shade` of the two pointwise
clauses shrinks under restriction, which is the favourable direction for a `∀ x` hypothesis.

## What is deliberately absent

No lower bracket appears anywhere below, and no constant is enlarged to compensate for one.
A consumer that genuinely needs a lower branching bound is not served by this file; it has to
re-uniformize, or be restated.  In particular nothing here is claimed about
`prop:ml1bootFlatPrismsCorrected`, whose Lean carrier does not exist.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

/-! ### Monotonicity of the shaded class in the index set -/

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- **The shaded class is monotone in the index set.**

`ShadedTube.shadeClass` is a filter of `Tube.coverClass`, so it inherits
`Tube.coverClass_subset_of_subset`.  This is the reason the *upper* class bracket of
`ShadedTube.ShadedUniformTubeSet` survives restriction, and it is not the same statement as
`ShadedTube.shadeClass_subset`, which compares the shaded class with the cover class at a fixed
index set. -/
theorem shadeClass_subset_of_subset {δ : NNReal} {s s' : Finset ι} (hs : s' ⊆ s)
    (V : ι → ShadedTube δ E) (assign : ι → ι) (j : ι) (x : E) :
    ShadedTube.shadeClass s' V assign j x ⊆ ShadedTube.shadeClass s V assign j x := by
  classical
  intro i hi
  simp only [ShadedTube.shadeClass, Finset.mem_filter] at hi ⊢
  exact ⟨Tube.coverClass_subset_of_subset hs assign j hi.1, hi.2⟩

/-! ### Restricting a nested cover system -/

/-- **A nested cover system restricts to a subfamily verbatim.**

Every field of `Tube.GridCoverSystem` is either a free datum (`indexSet`, `assign`, `tube`) or a
statement quantified over the members of the family, so the node data is kept unchanged and each
clause is read on a smaller set.  In particular `indexSet` is *not* shrunk: the nodes that no
longer carry a member of `s'` stay in place, which is harmless because no clause asserts that a
node is inhabited. -/
def gridCoverRestrict {δ : NNReal} {s s' : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    (cover : Tube.GridCoverSystem s T N) (hs : s' ⊆ s) : Tube.GridCoverSystem s' T N where
  indexSet := cover.indexSet
  assign := cover.assign
  tube := cover.tube
  assign_mem k hk i hi := cover.assign_mem k hk i (hs hi)
  le_tube_assign k hk i hi := cover.le_tube_assign k hk i (hs hi)
  nested k hk i hi j hj := cover.nested k hk i (hs hi) j (hs hj)
  tube_nested k hk i hi := cover.tube_nested k hk i (hs hi)

/-! ### One-sided uniformity at the tube level -/

/-- **The half of `Tube.UniformTubeSet` that restricts.**

Definition 2.1 with the *lower* class bracket `le_card_class` deleted.  What remains is the
hierarchy, the injective indexing of the nodes, bounded overlap, and the upper class bracket —
every clause of which is either independent of the index set or an upper bound on a quantity
monotone in it. -/
structure IsOneSidedUniformTubeSet {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) (N : ℕ)
    (C : NNReal) where
  /-- The nested system of covers along the grid `ρ_k = δ^{k/N}`. -/
  cover : Tube.GridCoverSystem s T N
  /-- The branching number at each grid scale, a free datum. -/
  branchingN : ℕ → NNReal
  /-- Distinct node indices name distinct node tubes. -/
  tube_injOn : ∀ k ≤ N, Set.InjOn (cover.tube k) (cover.indexSet k : Set ι)
  /-- **Definition 2.1(ii) (Bounded overlap).** -/
  boundedOverlap : ∀ k ≤ N, ∀ V : Tube (Tube.gridScale δ N k) E,
    (open scoped Classical in
      (cover.indexSet k).filter (fun j => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (cover.tube k j).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤ C
  /-- **Definition 2.1(iii), upper half only.** -/
  card_class_le : ∀ k ≤ N, ∀ j ∈ cover.indexSet k,
    ((Tube.coverClass s (cover.assign k) j).card : NNReal) ≤ C * branchingN k

/-- Every two-sided hierarchy is one-sided: forget `le_card_class`. -/
def IsOneSidedUniformTubeSet.of_uniformTubeSet {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒰 : Tube.UniformTubeSet s T N C) :
    IsOneSidedUniformTubeSet s T N C where
  cover := 𝒰.cover
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlap := 𝒰.boundedOverlap
  card_class_le := 𝒰.card_class_le

/-- **One-sided tube uniformity restricts to an arbitrary subfamily, at the same constant.**

The node data is inherited verbatim by `Kakeya.ml1Boot.gridCoverRestrict`; `boundedOverlap`
descends because its filter predicate weakens, and `card_class_le` because
`Tube.coverClass_subset_of_subset` shrinks the class it bounds.  No pigeonholing and no loss. -/
def IsOneSidedUniformTubeSet.mono_index {δ : NNReal} {s s' : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒰 : IsOneSidedUniformTubeSet s T N C) (hs : s' ⊆ s) :
    IsOneSidedUniformTubeSet s' T N C where
  cover := gridCoverRestrict 𝒰.cover hs
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlap := by
    classical
    intro k hk V
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (𝒰.boundedOverlap k hk V)
    intro j hj
    simp only [gridCoverRestrict, Finset.mem_filter] at hj ⊢
    obtain ⟨hjmem, i, hi, h1, h2⟩ := hj
    exact ⟨hjmem, i, hs hi, h1, h2⟩
  card_class_le := by
    intro k hk j hj
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (𝒰.card_class_le k hk j ?_)
    · exact Tube.coverClass_subset_of_subset hs (𝒰.cover.assign k) j
    · simpa only [gridCoverRestrict] using hj

/-! ### One-sided uniformity at the shaded level -/

/-- **The half of `ShadedTube.ShadedUniformTubeSet` that restricts** (the one-sided reading of
GWZ Definition 2.2).

Definition 2.2 with the two clauses that bound a *shrinking* quantity from below deleted:
`le_card_shadeClass` and `branchingN_le` are gone, `card_shadeClass_le` and `le_branchingN`
remain, and the ambient tube hierarchy is the one-sided
`Kakeya.ml1Boot.IsOneSidedUniformTubeSet`.

What the two survivors still say together is that no node the fibre of `x` meets carries more
than `C · localN x k` members of that fibre, and that `localN x k` is no larger than
`C · branchingN k` — a uniform *upper* bound on the local branching, with `branchingN`
independent of `x`.  That is exactly the content a consumer needs when it uses uniformity to
bound a count from above; a consumer needing a member of every class is not served. -/
structure IsOneSidedUniform {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E) (N : ℕ)
    (C : NNReal) where
  /-- The underlying tubes carry a one-sided uniform hierarchy. -/
  tubeUniform : IsOneSidedUniformTubeSet s (fun i => (V i).toTube) N C
  /-- The per-scale branching count shared across all points of the shade union. -/
  branchingN : ℕ → NNReal
  /-- The branching count of the fibre at a single point. -/
  localN : E → ℕ → NNReal
  /-- Each node met by the fibre of `x` contributes at most `C · localN x k` of its members. -/
  card_shadeClass_le : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, ∀ i ∈ s, x ∈ (V i).shade →
    ((ShadedTube.shadeClass s V (tubeUniform.cover.assign k)
      (tubeUniform.cover.assign k i) x).card : NNReal) ≤ C * localN x k
  /-- Each local count is at most a factor `C` above the shared count. -/
  le_branchingN : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, localN x k ≤ C * branchingN k

/-- **Every two-sided shaded hierarchy is one-sided**: forget `le_card_shadeClass` and
`branchingN_le`.

The two retained clauses transfer verbatim, the ambient hierarchy being projected by
`Kakeya.ml1Boot.IsOneSidedUniformTubeSet.of_uniformTubeSet`, which keeps `cover` unchanged, so
the occurrences of `tubeUniform.cover.assign` on either side are the same function. -/
def IsOneSidedUniform.of_shadedUniformTubeSet {δ : NNReal} {s : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {C : NNReal}
    (𝒱 : ShadedTube.ShadedUniformTubeSet s V N C) : IsOneSidedUniform s V N C where
  tubeUniform := IsOneSidedUniformTubeSet.of_uniformTubeSet 𝒱.tubeUniform
  branchingN := 𝒱.branchingN
  localN := 𝒱.localN
  card_shadeClass_le := 𝒱.card_shadeClass_le
  le_branchingN := 𝒱.le_branchingN

/-- **A one-sided tube hierarchy transports along an equality of tubes on the index set.**

`Tube.GridCoverSystem` and the two retained clauses mention the family only through `T i` for
`i ∈ s`, so an equality there carries the whole structure across.  This is what lets a hierarchy
established for a family be reused after the *shading* is replaced, the tubes being untouched — the
situation every factoring step is in, since `Kakeya.ml1Boot.exists_factorOneScale` returns a
refined shading on the same tubes. -/
def IsOneSidedUniformTubeSet.congr_tubes {δ : NNReal} {s : Finset ι} {T T' : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒰 : IsOneSidedUniformTubeSet s T N C)
    (h : ∀ i ∈ s, T' i = T i) : IsOneSidedUniformTubeSet s T' N C where
  cover :=
    { indexSet := 𝒰.cover.indexSet
      assign := 𝒰.cover.assign
      tube := 𝒰.cover.tube
      assign_mem := 𝒰.cover.assign_mem
      le_tube_assign := by
        intro k hk i hi
        rw [h i hi]
        exact 𝒰.cover.le_tube_assign k hk i hi
      nested := by
        intro k hk i hi j hj
        simpa [h i hi, h j hj] using 𝒰.cover.nested k hk i hi j hj
      tube_nested := 𝒰.cover.tube_nested }
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlap := by
    intro k hk W
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (𝒰.boundedOverlap k hk W)
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    obtain ⟨hjmem, i, hi, h1, h2⟩ := hj
    refine ⟨hjmem, i, hi, ?_, ?_⟩
    · rw [← h i hi]; exact h1
    · rw [← h i hi]; exact h2
  card_class_le := 𝒰.card_class_le

/-- **One-sided shaded uniformity from a bare tube-level hierarchy.**

`Kakeya.ml1Boot.IsOneSidedUniform` imposes only *upper* bounds on its two counting functions, and
both are free data, so taking each to be the constant `s.card` satisfies them with no information
about the shading at all: `card_shadeClass_le` holds because a shade class is a subset of the index
set, and `le_branchingN` because the two functions are equal.

**What this records.**  The shade side of one-sided uniformity carries nothing beyond the
tube-level hierarchy.  For Section 8 the consequence is benign and useful — the factoring bundles
need only a hierarchy on the *tubes*, which an index-set pigeonhole produces without touching the
shading, so a per-tube density band survives it verbatim.  For Section 6 it is a warning: the
weakening of `Kakeya.IsFlatPrismFamily.unif` to the one-sided predicate gave away more than the two
lower brackets it is documented as dropping. -/
def IsOneSidedUniform.of_tubeUniform {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E}
    {N : ℕ} {C : NNReal} (hC : 1 ≤ C)
    (𝒰 : IsOneSidedUniformTubeSet s (fun i => (V i).toTube) N C) :
    IsOneSidedUniform s V N C where
  tubeUniform := 𝒰
  branchingN := fun _ => (s.card : NNReal)
  localN := fun _ _ => (s.card : NNReal)
  card_shadeClass_le := by
    intro x _hx k _hk i _hi _hxi
    have hsub : ShadedTube.shadeClass s V (𝒰.cover.assign k) (𝒰.cover.assign k i) x ⊆ s := by
      intro y hy
      have hy' := ShadedTube.shadeClass_subset s V (𝒰.cover.assign k)
        (𝒰.cover.assign k i) x hy
      simp only [Tube.coverClass, Finset.mem_filter] at hy'
      exact hy'.1
    have hmono : ((ShadedTube.shadeClass s V (𝒰.cover.assign k)
        (𝒰.cover.assign k i) x).card : NNReal) ≤ (s.card : NNReal) := by
      exact_mod_cast Finset.card_le_card hsub
    refine hmono.trans ?_
    calc (s.card : NNReal) = 1 * (s.card : NNReal) := (one_mul _).symm
      _ ≤ C * (s.card : NNReal) := by gcongr
  le_branchingN := by
    intro x _hx k _hk
    calc (s.card : NNReal) = 1 * (s.card : NNReal) := (one_mul _).symm
      _ ≤ C * (s.card : NNReal) := by gcongr

/-- **Weakening the constant, tube level.**  The node data and the branching function are
unchanged; both retained clauses are upper bounds, so they weaken with the constant. -/
def IsOneSidedUniformTubeSet.mono {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C C' : NNReal} (𝒰 : IsOneSidedUniformTubeSet s T N C) (hC : C ≤ C') :
    IsOneSidedUniformTubeSet s T N C' where
  cover := 𝒰.cover
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlap := fun k hk V => (𝒰.boundedOverlap k hk V).trans hC
  card_class_le := fun k hk j hj => (𝒰.card_class_le k hk j hj).trans (by gcongr)

/-- **Weakening the constant.**  The counterpart of `ShadedTube.ShadedUniformTubeSet.mono`; the
hierarchy and both counting functions are unchanged, and both retained clauses are upper bounds. -/
def IsOneSidedUniform.mono {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E} {N : ℕ}
    {C C' : NNReal} (𝒱 : IsOneSidedUniform s V N C) (hC : C ≤ C') :
    IsOneSidedUniform s V N C' where
  tubeUniform := 𝒱.tubeUniform.mono hC
  branchingN := 𝒱.branchingN
  localN := 𝒱.localN
  card_shadeClass_le := fun x hx k hk i hi hxi =>
    (𝒱.card_shadeClass_le x hx k hk i hi hxi).trans (by gcongr)
  le_branchingN := fun x hx k hk => (𝒱.le_branchingN x hx k hk).trans (by gcongr)

/-- **One-sided shaded uniformity restricts to an arbitrary subfamily, at the same constant.**

This is the pivot of the whole file.  The counting functions `branchingN` and `localN` are free
fields and are inherited unchanged; the ambient hierarchy restricts by
`Kakeya.ml1Boot.IsOneSidedUniformTubeSet.mono_index`; the shade union shrinks, which weakens
both `∀ x` clauses; `card_shadeClass_le` descends because
`Kakeya.ml1Boot.shadeClass_subset_of_subset` shrinks the class it bounds; and `le_branchingN`
descends because it does not mention the index set.  No pigeonholing, and the constant is
unchanged. -/
def IsOneSidedUniform.mono_index {δ : NNReal} {s s' : Finset ι} {V : ι → ShadedTube δ E}
    {N : ℕ} {C : NNReal} (𝒱 : IsOneSidedUniform s V N C) (hs : s' ⊆ s) :
    IsOneSidedUniform s' V N C where
  tubeUniform := 𝒱.tubeUniform.mono_index hs
  branchingN := 𝒱.branchingN
  localN := 𝒱.localN
  card_shadeClass_le := by
    intro x hx k hk i hi hxi
    have hxs : x ∈ (⋃ i ∈ s, (V i).shade) := by
      simp only [Set.mem_iUnion, exists_prop] at hx ⊢
      obtain ⟨j, hj, hxj⟩ := hx
      exact ⟨j, hs hj, hxj⟩
    refine le_trans ?_ (𝒱.card_shadeClass_le x hxs k hk i (hs hi) hxi)
    exact Nat.cast_le.mpr (Finset.card_le_card
      (shadeClass_subset_of_subset hs V (𝒱.tubeUniform.cover.assign k)
        (𝒱.tubeUniform.cover.assign k i) x))
  le_branchingN := by
    intro x hx k hk
    have hxs : x ∈ (⋃ i ∈ s, (V i).shade) := by
      simp only [Set.mem_iUnion, exists_prop] at hx ⊢
      obtain ⟨j, hj, hxj⟩ := hx
      exact ⟨j, hs hj, hxj⟩
    exact 𝒱.le_branchingN x hxs k hk

/-- **Project, then restrict**: the composite this file exists to provide.

A two-sided hierarchy at `s` yields one-sided uniformity at every `s' ⊆ s`, at the same
constant and with no loss.  This is what replaces a re-uniformization at the refined index set
in `Kakeya.ml1Boot.exists_plankDimensions_uniformSelection`. -/
def IsOneSidedUniform.of_shadedUniformTubeSet_subset {δ : NNReal} {s s' : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {C : NNReal}
    (𝒱 : ShadedTube.ShadedUniformTubeSet s V N C) (hs : s' ⊆ s) :
    IsOneSidedUniform s' V N C :=
  (IsOneSidedUniform.of_shadedUniformTubeSet 𝒱).mono_index hs

end ml1Boot

end Kakeya
