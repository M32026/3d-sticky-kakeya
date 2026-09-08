/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.BoundedOverlapParents

/-!
# The minimal strengthening of bounded overlap that makes the outer-plank parent count constant

`Kakeya.not_card_assignedParents_le_const_of_boundedOverlap`
(`Kakeya/Factoring/BoundedOverlapParents.lean`) shows that no constant bounds the
assigned-parent count of the outer plank nonconcentration step of GWZ Proposition 6.6(A) under
`Tube.HasBoundedOverlap`.  This file asks what the *weakest* strengthening of that hypothesis is
that restores the constant, answers it, and then shows that the answer is not available to Main
Lemma 1.

## The candidate

`Tube.HasBoundedOverlapAtDilate s V t Vρ L Co` is `Tube.HasBoundedOverlap` with the test body
enlarged from a `ρ`-tube `W` to its `L`-dilate `L · W`.  That is the *entire* gap between the two
statements: given the parent containment `V i ≤ Vρ (p i)`, the set the outer-plank step counts,

    { k ∈ t : ∃ i ∈ s, p i = k ∧ V i ≤ L · W },

is a subset of the set bounded-overlap-at-a-dilate bounds, and nothing else is needed
(`Kakeya.card_assignedParents_le_of_boundedOverlapAtDilate`: no dimension hypothesis, no scale
hypothesis, no `B₁` containment, and the count is `Co`, a constant).

* It is stronger than bounded overlap for `1 ≤ L`
  (`Tube.HasBoundedOverlapAtDilate.hasBoundedOverlap`), and **strictly** stronger:
  `Kakeya.exists_hasBoundedOverlap_not_hasBoundedOverlapAtDilate` exhibits, for every constant,
  a stage of the axial pencil `Kakeya.ml1Boot.essDistinctCex` that has bounded overlap at the
  sharpest constant `1` and fails bounded overlap at the dilate `4`.  So the candidate **kills
  the pencil**, which is the first thing any candidate has to do.
* It is satisfiable: `Tube.hasBoundedOverlapAtDilate_of_card_le` — a coarse family of at most
  `Co` members has it at `Co`, whatever the leaves are.
* It is **minimal**: on families whose parent map is determined by containment — the pencil is
  one, by `Kakeya.ml1Boot.essDistinctCex.eq_of_le_parent` — the hypothesis is *equivalent* to the
  count it is asked to produce (`Kakeya.hasBoundedOverlapAtDilate_of_card_assignedParents_le`).
  No strictly weaker hypothesis can therefore do the job on that class.

## Why the two natural alternatives are not candidates

*Fullness.*  The pencil of `Kakeya.not_card_assignedParents_le_const_of_boundedOverlap` carries
the empty shading, so it violates the `fullness` clause of `Kakeya.IsFlatPrismFamily`, and one
might hope that clause is what rules the configuration out.  It is not:
`Kakeya.not_card_assignedParents_le_const_of_boundedOverlap_of_full` re-runs the refutation with
the pencil shaded by the whole of each leaf (`Kakeya.fullLeaf`, fullness exactly `1` by
`Kakeya.fullness_fullLeaf_eq_one`), against the hypothesis package *nonempty + `B₁` +
leaf-scale essential distinctness + fullness at an arbitrary threshold + parent family + bounded
overlap at `1`* — ship's 6.6(A) package minus its uniformity clause — and the count is still
unbounded.

*A cardinality cap, or anything else at a constant coarse family.*  The Main Lemma 1 call site in
`Kakeya/DimensionThree/MainLemma1/Rescaling/KatzTao.lean` instantiates the coarse family at a
single fixed unit tube.  `Kakeya.card_le_of_hasBoundedOverlap_const` shows that bounded overlap
there degenerates to `#t ≤ Co` — a cap on the number of coarse tubes, which is not a constant.

## The verdict this file records

The configuration that separates `Tube.HasBoundedOverlapAtDilate` from `Tube.HasBoundedOverlap`
is the axial pencil, and the axial pencil is precisely the *longitudinal stack* of the
blueprint's erratum to GWZ Definition 2.1(ii) (`blueprint/src/GWZAdapted/section2.tex:1093--1139`)
— "a longitudinal stack of `∼ δ ^ (-1/2)` parent tubes covered with bounded overlap by `∼ 1`
coarse parent at `ρ = √δ`".  That erratum's whole point is that such stacks *survive* the
uniformization refinement, and that any refinement which removes them collapses the family to
`O(1)` where `|𝕋| ∼ δ ^ (-1/2)`; it is why Definition 2.1(ii) was changed from
essential distinctness of the parents to bounded overlap in the first place.

So a coarse family satisfying `Tube.HasBoundedOverlapAtDilate` is a coarse family with no
longitudinal stacks, which is the parent-scale essential distinctness the erratum declares
unsatisfiable while preserving cardinality.  Main Lemma 1 cannot supply the candidate, and by the
minimality result above it cannot supply anything weaker that would do either.  The material in
this file is therefore a **negative** result about the current architecture: the outer-plank count
step of GWZ Proposition 6.6(A) has to be reached at a coarser `ρ`, not through a stronger
hypothesis on the coarse family at the given `ρ`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Tube

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {ι : Type*}

/-- **Bounded overlap tested against *dilated* `ρ`-tubes.**

`Tube.HasBoundedOverlap` tests the coarse family against `ρ`-tubes `W`; this variant tests it
against the `L`-dilates `L · W`, which are longer (core length `L`) and fatter (radius `L ρ`)
than a `ρ`-tube.

For `1 ≤ L` this implies `Tube.HasBoundedOverlap` at the same constant
(`Tube.HasBoundedOverlapAtDilate.hasBoundedOverlap`), and it is **strictly** stronger
(`Kakeya.not_hasBoundedOverlapAtDilate_of_boundedOverlap`). -/
def HasBoundedOverlapAtDilate {κ : Type*} {σ ρ : NNReal} (s : Finset ι) (V : ι → Tube σ E)
    (t : Finset κ) (Vρ : κ → Tube ρ E) (L : ℝ) (Co : NNReal) : Prop :=
  ∀ W : Tube ρ E,
    ((open scoped Classical in
      t.filter (fun k => ∃ i ∈ s,
        (V i).toConvexSpaceBody ≤ (Vρ k).toConvexSpaceBody ∧
        (V i).toConvexSpaceBody ≤ Kakeya.Tube.dilate W L)).card : NNReal) ≤ Co

/-- **Bounded overlap at a dilate implies bounded overlap**, for any enlargement `1 ≤ L`. -/
theorem HasBoundedOverlapAtDilate.hasBoundedOverlap {κ : Type*} {σ ρ : NNReal} {s : Finset ι}
    {V : ι → Tube σ E} {t : Finset κ} {Vρ : κ → Tube ρ E} {L : ℝ} {Co : NNReal}
    (hL : 1 ≤ L) (h : HasBoundedOverlapAtDilate s V t Vρ L Co) :
    HasBoundedOverlap s V t Vρ Co := by
  classical
  intro W
  refine le_trans ?_ (h W)
  refine Nat.cast_le.mpr (Finset.card_le_card ?_)
  intro k hk
  rcases Finset.mem_filter.mp hk with ⟨hkt, i, his, hiP, hiW⟩
  exact Finset.mem_filter.mpr ⟨hkt, i, his, hiP,
    le_trans hiW (SetLike.coe_subset_coe.mpr (subset_dilate W hL))⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Satisfiability, schematically**: a coarse family with at most `Co` members has bounded
overlap at every dilate, at the constant `Co`, whatever the leaves are. -/
theorem hasBoundedOverlapAtDilate_of_card_le {κ : Type*} {σ ρ : NNReal} {s : Finset ι}
    {V : ι → Tube σ E} {t : Finset κ} {Vρ : κ → Tube ρ E} {L : ℝ} {Co : NNReal}
    (ht : (t.card : NNReal) ≤ Co) :
    HasBoundedOverlapAtDilate s V t Vρ L Co := by
  classical
  intro W
  refine le_trans ?_ ht
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

end Tube

namespace Kakeya

section Count

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The outer-plank parent count from bounded overlap at a dilate.**

This is the replacement, at the outer plank nonconcentration step of GWZ Proposition 6.6(A), for
`Kakeya.edParentCount.card_assignedParents_le_of_subset_dilate`: the same conclusion, with
pairwise essential distinctness of the coarse family replaced by
`Tube.HasBoundedOverlapAtDilate` at the *same* dilation `L` the step tests at.

No hypothesis on the scales, on the dimension, or on containment in `B₁` is used: the counted set
is a subset of the set `Tube.HasBoundedOverlapAtDilate` bounds outright, the only geometric input
being the parent containment `hle`. -/
theorem card_assignedParents_le_of_boundedOverlapAtDilate
    {ι κ : Type*} [DecidableEq κ] {σ ρ Co : NNReal} {L : ℝ}
    {q : Finset ι} {T : ι → Tube σ E} {r : Finset κ} {R : κ → Tube ρ E} {assign : ι → κ}
    (hle : ∀ i ∈ q, (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody)
    (hbo : Tube.HasBoundedOverlapAtDilate q T r R L Co) (W : Tube ρ E) :
    (((r.filter fun k => ∃ i ∈ q, assign i = k ∧
        (T i).toConvexSpaceBody ≤ Tube.dilate W L).card : NNReal)) ≤ Co := by
  classical
  refine le_trans ?_ (hbo W)
  refine Nat.cast_le.mpr (Finset.card_le_card ?_)
  intro k hk
  rcases Finset.mem_filter.mp hk with ⟨hkr, i, hiq, hik, hiW⟩
  refine Finset.mem_filter.mpr ⟨hkr, i, hiq, ?_, hiW⟩
  have := hle i hiq
  rwa [hik] at this


omit [MeasurableSpace E] [BorelSpace E] in
/-- **The candidate hypothesis is not merely sufficient for the count: on the families that
matter it is equivalent to it, which is what makes it *minimal*.**

If the parent map is determined by containment — if a leaf contained in a listed parent is
assigned to it — then the set `Tube.HasBoundedOverlapAtDilate` bounds is exactly the set the
outer-plank step counts, so the count bound at every test tube gives the hypothesis back.  The
axial pencil is such a family: `Kakeya.ml1Boot.essDistinctCex.eq_of_le_parent` says a leaf lies in
no parent but its own.

Consequently no hypothesis strictly weaker than `Tube.HasBoundedOverlapAtDilate` can yield the
constant count on this class: any such hypothesis would already imply
`Tube.HasBoundedOverlapAtDilate` there. -/
theorem hasBoundedOverlapAtDilate_of_card_assignedParents_le
    {ι κ : Type*} [DecidableEq κ] {σ ρ Co : NNReal} {L : ℝ}
    {q : Finset ι} {T : ι → Tube σ E} {r : Finset κ} {R : κ → Tube ρ E} {assign : ι → κ}
    (hsec : ∀ i ∈ q, ∀ k ∈ r, (T i).toConvexSpaceBody ≤ (R k).toConvexSpaceBody → assign i = k)
    (hcount : ∀ W : Tube ρ E,
      (((r.filter fun k => ∃ i ∈ q, assign i = k ∧
          (T i).toConvexSpaceBody ≤ Tube.dilate W L).card : NNReal)) ≤ Co) :
    Tube.HasBoundedOverlapAtDilate q T r R L Co := by
  classical
  intro W
  refine le_trans ?_ (hcount W)
  refine Nat.cast_le.mpr (Finset.card_le_card ?_)
  intro k hk
  rcases Finset.mem_filter.mp hk with ⟨hkr, i, hiq, hiP, hiW⟩
  exact Finset.mem_filter.mpr ⟨hkr, i, hiq, hsec i hiq k hkr hiP, hiW⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- **At a constant coarse family, bounded overlap is a cardinality cap and nothing else.**

`Kakeya/DimensionThree/MainLemma1/Rescaling/KatzTao.lean` instantiates the coarse family of GWZ
Proposition 6.6(A) at a *single* fixed unit tube, `Vρ := fun _ => T1`, with every leaf contained
in `T1`.  There `Tube.HasBoundedOverlap s V t Vρ Co` is not a geometric condition at all: testing
at `W = T1` counts the whole of `t`, so the hypothesis says `#t ≤ Co`.

This is a hard obstruction to *any* bounded-overlap-shaped hypothesis at that call site, the
candidate `Tube.HasBoundedOverlapAtDilate` included (it is stronger still): the coarse index set
there is the family of coarse tubes, whose cardinality is not bounded by a constant. -/
theorem card_le_of_hasBoundedOverlap_const {ι κ : Type*} {σ ρ Co : NNReal}
    {s : Finset ι} {V : ι → Tube σ E} {t : Finset κ} {T1 : Tube ρ E}
    (hs : s.Nonempty) (hle : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ T1.toConvexSpaceBody)
    (h : Tube.HasBoundedOverlap s V t (fun _ => T1) Co) :
    (t.card : NNReal) ≤ Co := by
  classical
  obtain ⟨i₀, hi₀⟩ := hs
  have hkey := h T1
  have hfilter : (t.filter fun k => ∃ i ∈ s,
      (V i).toConvexSpaceBody ≤ T1.toConvexSpaceBody ∧
      (V i).toConvexSpaceBody ≤ T1.toConvexSpaceBody) = t := by
    ext k
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.1, fun hk => ⟨hk, i₀, hi₀, hle i₀ hi₀, hle i₀ hi₀⟩⟩
  rwa [hfilter] at hkey

end Count


section Pencil

open ml1Boot.essDistinctCex

/-- **The axial pencil violates bounded overlap at the dilate `4`, at every constant.**

The pencil `Kakeya.ml1Boot.essDistinctCex.leaf` of `M = 2 ^ (2 n + 1)` leaves under `M` parents
has `Tube.HasBoundedOverlap` at the sharpest constant `1`
(`Kakeya.ml1Boot.essDistinctCex.hasBoundedOverlap`) and yet all `M` of its parents are counted by
the dilated test at `W = ` the `0`-th parent, since every leaf lies in the `4`-dilate of that
parent (`Kakeya.essDistinctCex_leaf_carrier_subset_parentZero_dilate`) and in its own parent
(`Kakeya.ml1Boot.IsParentFamily.le_parent`).

So `Tube.HasBoundedOverlapAtDilate` is **strictly** stronger than `Tube.HasBoundedOverlap`, and
the pencil — the configuration of the blueprint's erratum to GWZ Definition 2.1(ii)
(`blueprint/src/GWZAdapted/section2.tex:1093--1139`), a longitudinal stack of parents covered by
one coarse parent — is exactly what separates them. -/
theorem exists_hasBoundedOverlap_not_hasBoundedOverlapAtDilate (Co : NNReal) :
    ∃ (σ ρ : NNReal) (M : ℕ), 0 < σ ∧ σ ≤ ρ ∧ ρ ≤ 1 ∧
      Tube.HasBoundedOverlap (Finset.range M) (leaf σ ρ) (Finset.range M) (parent σ ρ) 1 ∧
      ¬ Tube.HasBoundedOverlapAtDilate (Finset.range M) (leaf σ ρ) (Finset.range M)
          (parent σ ρ) (4 : ℝ) Co := by
  classical
  obtain ⟨m, hm⟩ := exists_nat_gt (Co : ℝ)
  let n : ℕ := max 5 m
  have hn5 : 5 ≤ n := le_max_left _ _
  have hnm : m ≤ n := le_max_right _ _
  have hn2 : 2 ≤ n := le_trans (by norm_num) hn5
  refine ⟨leafScale n, parentScale n, count n, leafScale_pos n,
    leafScale_le_parentScale hn2, parentScale_le_one n, ?_, ?_⟩
  · exact hasBoundedOverlap (leafScale_le_parentScale hn2) (parentScale_pos n)
      (parentScale_le_inv128 n) (Finset.range (count n)) (Finset.range (count n))
  · intro hbo
    have hσρ : leafScale n ≤ parentScale n := leafScale_le_parentScale hn2
    have hρ128 : (parentScale n : ℝ) ≤ 1 / 128 := parentScale_le_inv128 n
    have hax : 7 * (parentScale n : ℝ) * (count n : ℝ) ≤ 1 / 12 := axial_bound n
    have htr : 3 * (leafScale n : ℝ) * (count n : ℝ) ≤ (parentScale n : ℝ) :=
      essDistinctCex_trans_bound_le_parentScale hn5
    have hpf := isParentFamily hσρ (parentScale_pos n) hρ128 (Finset.range (count n))
    have hkey := hbo (parent (leafScale n) (parentScale n) 0)
    have hfilter :
        ((Finset.range (count n)).filter fun k => ∃ i ∈ Finset.range (count n),
          (leaf (leafScale n) (parentScale n) i).toConvexSpaceBody ≤
            (parent (leafScale n) (parentScale n) k).toConvexSpaceBody ∧
          (leaf (leafScale n) (parentScale n) i).toConvexSpaceBody ≤
            Kakeya.Tube.dilate (parent (leafScale n) (parentScale n) 0) (4 : ℝ))
          = Finset.range (count n) := by
      ext k
      simp only [Finset.mem_filter]
      refine ⟨fun h => h.1, fun hk => ⟨hk, k, hk, ?_, ?_⟩⟩
      · simpa using hpf.le_parent k hk
      · exact SetLike.coe_subset_coe.mpr
          (essDistinctCex_leaf_carrier_subset_parentZero_dilate hσρ hρ128 hax htr
            (le_of_lt (Finset.mem_range.mp hk)))
    rw [hfilter, Finset.card_range] at hkey
    have hCoM : (Co : ℝ) < (count n : ℝ) := by
      have h1 : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnm
      have h2 : (n : ℝ) < (count n : ℝ) := by
        have : n < count n := by
          have hlt : n < 2 ^ n := Nat.lt_two_pow_self
          have hle : (2 : ℕ) ^ n ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          simpa [count] using lt_of_lt_of_le hlt hle
        exact_mod_cast this
      linarith
    have : ((count n : NNReal) : ℝ) ≤ (Co : ℝ) := by exact_mod_cast hkey
    simp at this
    linarith

end Pencil


section Fullness

open ml1Boot.essDistinctCex

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **A family shaded by the whole of its carrier is full.** -/
theorem fullness_eq_one_of_shade_eq_carrier {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E)
    (hsh : ∀ i ∈ s, (V i).shade = (V i).carrier)
    (hpos : 0 < ∑ i ∈ s, volume (V i).carrier)
    (hne : ∑ i ∈ s, volume (V i).carrier ≠ ⊤) :
    ShadedBody.fullness s V = 1 := by
  have hsum : ∑ i ∈ s, volume (V i).shade = ∑ i ∈ s, volume (V i).carrier :=
    Finset.sum_congr rfl fun i hi => by rw [hsh i hi]
  have : ((ShadedBody.fullness s V : NNReal) : ENNReal) = 1 := by
    rw [ShadedBody.fullness_def, hsum, ENNReal.div_self hpos.ne' hne]
  exact_mod_cast this

/-- The `i`-th leaf of the axial pencil, shaded by **the whole of its carrier**.

`Kakeya.ml1Boot.essDistinctCex.shadedLeaf` uses the empty shading, which makes every fullness
hypothesis fail.  This variant makes fullness equal to `1`, its maximum, so that a fullness
clause is satisfied at every threshold.  Everything else about the pencil is unchanged: the
underlying tube is the same. -/
def fullLeaf (σ ρ : NNReal) (i : ℕ) : ShadedTube σ (EuclideanSpace ℝ (Fin 3)) where
  toTube := leaf σ ρ i
  shade := (leaf σ ρ i).carrier
  measurableSet_shade := (leaf σ ρ i).isCompact.measurableSet
  shade_subset := le_rfl

@[simp] theorem fullLeaf_toTube (σ ρ : NNReal) (i : ℕ) :
    (fullLeaf σ ρ i).toTube = leaf σ ρ i := rfl

@[simp] theorem fullLeaf_shade (σ ρ : NNReal) (i : ℕ) :
    (fullLeaf σ ρ i).shade = (leaf σ ρ i).carrier := rfl

/-- **The fully shaded pencil is full at level `1`.** -/
theorem fullness_fullLeaf_eq_one {σ ρ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) {M : ℕ} (hM : 0 < M) :
    ShadedBody.fullness (Finset.range M)
      (fun i => (fullLeaf σ ρ i).toShadedBody) = 1 := by
  have hvol : ∀ i : ℕ, 0 < volume (leaf σ ρ i).carrier ∧ volume (leaf σ ρ i).carrier < ⊤ :=
    fun i => Tube.volume_pos_and_lt_top hσ0 hσ1 (leaf σ ρ i)
  refine fullness_eq_one_of_shade_eq_carrier _ _ (fun i _ => rfl) ?_ ?_
  · refine lt_of_lt_of_le (hvol 0).1 ?_
    exact Finset.single_le_sum (f := fun i => volume (leaf σ ρ i).carrier)
      (fun i _ => bot_le) (Finset.mem_range.mpr hM)
  · refine ne_of_lt ?_
    exact (ENNReal.sum_lt_top).2 (fun i _ => (hvol i).2)


/-- **Fullness does not rescue the outer-plank parent count.**

`Kakeya.not_card_assignedParents_le_const_of_boundedOverlap` runs the axial pencil with the
*empty* shading, so one might hope that the `fullness` clause of `Kakeya.IsFlatPrismFamily` —
which the pencil there violates outright — is what forbids the configuration.  It is not.  The
same pencil shaded by the whole of each leaf (`Kakeya.fullLeaf`) has fullness exactly `1`
(`Kakeya.fullness_fullLeaf_eq_one`), hence satisfies *every* fullness threshold `σ ^ η`, and it
still has `M = 2 ^ (2 n + 1)` assigned parents inside the `4`-dilate of a single `ρ`-tube.

So the hypothesis package refuted here is ship's GWZ Proposition 6.6(A) package minus only its
uniformity clause: nonemptiness, containment in `B₁`, **leaf-scale** essential distinctness,
fullness at an arbitrary threshold, a parent family, and bounded overlap at the sharpest constant
`1`.  None of it bounds the count.  A fullness-carrying strengthening of
`Tube.HasBoundedOverlap` is therefore *not* a candidate. -/
theorem not_card_assignedParents_le_const_of_boundedOverlap_of_full (C : NNReal) {η : ℝ}
    (hη : 0 < η) :
    ¬ ∀ (σ ρ : NNReal), 0 < σ → σ ≤ ρ → ρ ≤ 1 →
        ∀ (q r : Finset ℕ) (V : ℕ → ShadedTube σ (EuclideanSpace ℝ (Fin 3)))
          (R : ℕ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (assign : ℕ → ℕ)
          (W : Tube ρ (EuclideanSpace ℝ (Fin 3))),
          q.Nonempty →
          (∀ i ∈ q, (V i).carrier ⊆ Metric.closedBall 0 1) →
          (q : Set ℕ).Pairwise
            (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) →
          (σ : ENNReal) ^ η ≤ ShadedBody.fullness q (fun i => (V i).toShadedBody) →
          ml1Boot.IsParentFamily q (fun i => (V i).toTube) r R assign →
          Tube.HasBoundedOverlap q (fun i => (V i).toTube) r R 1 →
          ((r.filter fun k => ∃ i ∈ q, assign i = k ∧
              (V i).toConvexSpaceBody ≤ Tube.dilate W (4 : ℝ)).card : ENNReal)
            ≤ (C : ENNReal) := by
  classical
  intro hbound
  obtain ⟨m, hm⟩ := exists_nat_gt (C : ℝ)
  let n : ℕ := max 5 m
  have hn5 : 5 ≤ n := le_max_left _ _
  have hnm : m ≤ n := le_max_right _ _
  have hn2 : 2 ≤ n := le_trans (by norm_num) hn5
  set σ : NNReal := leafScale n with hσdef
  set ρ : NNReal := parentScale n with hρdef
  set M : ℕ := count n with hMdef
  have hσ0 : 0 < σ := leafScale_pos n
  have hρ0 : 0 < ρ := parentScale_pos n
  have hσρ : σ ≤ ρ := leafScale_le_parentScale hn2
  have hρ1 : ρ ≤ 1 := parentScale_le_one n
  have hσ1 : σ ≤ 1 := hσρ.trans hρ1
  have hρ128 : (ρ : ℝ) ≤ 1 / 128 := parentScale_le_inv128 n
  have hax : 7 * (ρ : ℝ) * (M : ℝ) ≤ 1 / 12 := axial_bound n
  have htr : 3 * (σ : ℝ) * (M : ℝ) ≤ (ρ : ℝ) := essDistinctCex_trans_bound_le_parentScale hn5
  have hM0 : 0 < M := by
    simp [hMdef, count]
  have hball : ∀ i ∈ Finset.range M,
      (fullLeaf σ ρ i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro i hi
    exact leaf_carrier_subset_ball hσρ hρ128 hax (trans_bound_inv12 hn5)
      (le_of_lt (Finset.mem_range.mp hi))
  have hED : ((Finset.range M : Finset ℕ) : Set ℕ).Pairwise
      (fun i j => IsEssentiallyDistinct (fullLeaf σ ρ i).carrier (fullLeaf σ ρ j).carrier) := by
    intro i _ j _ hij
    exact isEssentiallyDistinct_leaf hσ0 hij
  have hfull : (σ : ENNReal) ^ η ≤
      ShadedBody.fullness (Finset.range M) (fun i => (fullLeaf σ ρ i).toShadedBody) := by
    rw [fullness_fullLeaf_eq_one hσ0 hσ1 hM0]
    have : (σ : ENNReal) ^ η ≤ (1 : ENNReal) ^ η :=
      ENNReal.rpow_le_rpow (by exact_mod_cast hσ1) hη.le
    simpa using this
  have hkey := hbound σ ρ hσ0 hσρ hρ1 (Finset.range M) (Finset.range M) (fullLeaf σ ρ)
    (parent σ ρ) id (parent σ ρ 0) ⟨0, Finset.mem_range.mpr hM0⟩ hball hED hfull
    (isParentFamily hσρ hρ0 hρ128 (Finset.range M))
    (hasBoundedOverlap hσρ hρ0 hρ128 (Finset.range M) (Finset.range M))
  have hfilter :
      ((Finset.range M).filter fun k => ∃ i ∈ Finset.range M, id i = k ∧
        (fullLeaf σ ρ i).toConvexSpaceBody ≤ Kakeya.Tube.dilate (parent σ ρ 0) (4 : ℝ))
        = Finset.range M := by
    ext k
    simp only [Finset.mem_filter, id]
    refine ⟨fun h => h.1, fun hk => ⟨hk, k, hk, rfl, ?_⟩⟩
    exact SetLike.coe_subset_coe.mpr
      (essDistinctCex_leaf_carrier_subset_parentZero_dilate hσρ hρ128 hax htr
        (le_of_lt (Finset.mem_range.mp hk)))
  rw [hfilter, Finset.card_range] at hkey
  have hMC : (C : ℝ) < (M : ℝ) := by
    have h1 : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnm
    have h2 : (n : ℝ) < (M : ℝ) := by
      have hnM : n < M := by
        have hlt : n < 2 ^ n := Nat.lt_two_pow_self
        have hle : (2 : ℕ) ^ n ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        simpa [hMdef, count] using lt_of_lt_of_le hlt hle
      exact_mod_cast hnM
    linarith
  have hMC' : (C : ENNReal) < (M : ENNReal) := by
    have hlt : (C : NNReal) < (M : NNReal) := by
      rw [← NNReal.coe_lt_coe]
      simpa using hMC
    exact_mod_cast hlt
  exact absurd hkey (not_le.mpr hMC')

end Fullness

end Kakeya

end
