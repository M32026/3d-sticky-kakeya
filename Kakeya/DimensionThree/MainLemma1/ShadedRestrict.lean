/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ShadedUniform

/-!
# Two shade-side moves that keep GWZ Definition 2.2

`ShadedTube.ShadedUniformTubeSet` is *two-sided*: besides the upper brackets
`card_shadeClass_le` and `branchingN_le` it carries the two lower brackets
`le_card_shadeClass` and `le_branchingN`.  The lower brackets are what makes the predicate
fail to be hereditary — a shade-class count only shrinks when the index set shrinks or when a
shading is cut — and that failure is the recorded blocker of
`Kakeya.ml1Boot.exists_uniformFactorCore`: the shaded uniformizers
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` and
`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet` return no density bracket on their
own output shading, and the density bracket that `Kakeya.ml1Boot.IsUniformFactorCore.fine_dens`
demands is obtained by a pigeonhole that moves the index set, which then destroys the
uniformity just produced.

This file supplies the two moves that are *not* obstructed, and states them at exactly the
generality the blocker needs.

* `ShadedTube.nonempty_shadedUniformTubeSet_of_band` — the shaded analogue of
  `Kakeya.MultiScaleFac.exists_restrict_uniformTubeSet_band`.  Given tube uniformity on an
  arbitrary index set together with a **supplied** two-sided band on the shade-class counts —
  one band vector `B : ℕ → ℝ≥0`, valid at every point of the shade union and every node the
  fibre of that point meets — Definition 2.2 holds on that index set outright, with
  `localN x k := B k`.  Both lower brackets are then discharged by the supplied band, so no
  hereditary property of the ambient hierarchy is used and the ambient
  `ShadedUniformTubeSet` need not even exist.

  This is the exact reduction of the missing Section-2 interface: after the density pigeonhole
  has chosen its subfamily, what remains to be produced is a shade-class band on that
  subfamily, and nothing else.

* `ShadedTube.interShade` and `ShadedTube.shadedUniformTubeSet_interShade` — cutting **every**
  shading of the family by one common measurable set `W` preserves Definition 2.2 verbatim, at
  the same hierarchy, the same `branchingN`, the same `localN` and the same constant.  This is
  the one shade-shrinking operation the predicate is closed under, and it is closed under it
  exactly: at a point `x` of the cut shade union one has `x ∈ W`, so every shade class is
  literally unchanged.  A per-tube cut has no such property, which is why the density bracket
  cannot be installed by shrinking the heavy shadings.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace ShadedTube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

/-! ### Definition 2.2 from tube uniformity plus a supplied shade-class band -/

omit [Nontrivial E] [BorelSpace E] in
/-- **Definition 2.2 from a supplied shade-class band** — the shaded analogue of
`Kakeya.MultiScaleFac.exists_restrict_uniformTubeSet_band`.

`𝒰` is tube uniformity on the index set `s`; `B` is a band vector for the shade-class counts,
asked to bracket, at *every* point of the shade union and *every* grid index `k ≤ N`, the
number of members of the node `assign k i` whose shading covers that point.  The output takes
`localN x k := B k`, so the two lower brackets `le_card_shadeClass` and `le_branchingN` are the
supplied lower band and reflexivity respectively, and the two upper brackets are the supplied
upper band and reflexivity.

Nothing is assumed about a shaded hierarchy on any larger index set: the band is the whole
input.  Consequently this lemma applies verbatim to a subfamily chosen by a density pigeonhole,
and reduces the shaded half of `Kakeya.ml1Boot.exists_uniformFactorCore` to producing the band
`B` on that subfamily. -/
theorem nonempty_shadedUniformTubeSet_of_band {δ : NNReal} {s : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {Cu A C : NNReal}
    (𝒰 : UniformTubeSet s (fun i => (V i).toTube) N Cu)
    (hCuC : Cu ≤ C) (hAC : A ≤ C) (hC1 : 1 ≤ C) (B : ℕ → NNReal)
    (hband : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, ∀ i ∈ s, x ∈ (V i).shade →
      B k ≤ ((shadeClass s V (𝒰.cover.assign k) (𝒰.cover.assign k i) x).card : NNReal) ∧
        ((shadeClass s V (𝒰.cover.assign k) (𝒰.cover.assign k i) x).card : NNReal)
          ≤ A * B k) :
    Nonempty (ShadedUniformTubeSet s V N C) := by
  refine ⟨{
    tubeUniform := 𝒰.mono hCuC
    branchingN := B
    localN := fun _ k => B k
    card_shadeClass_le := ?_
    le_card_shadeClass := ?_
    branchingN_le := ?_
    le_branchingN := ?_ }⟩
  · intro x hx k hk i hi hxi
    exact (hband x hx k hk i hi hxi).2.trans (mul_le_mul_of_nonneg_right hAC zero_le)
  · intro x hx k hk i hi hxi
    exact (hband x hx k hk i hi hxi).1.trans (le_mul_of_one_le_left zero_le hC1)
  · intro _ _ _ _
    exact le_mul_of_one_le_left zero_le hC1
  · intro _ _ _ _
    exact le_mul_of_one_le_left zero_le hC1

/-! ### Cutting every shading by one common set -/

/-- Every shading of the family cut by one common measurable set `W`.  The tubes are
untouched. -/
def interShade {δ : NNReal} (V : ι → ShadedTube δ E) (W : Set E) (hW : MeasurableSet W) :
    ι → ShadedTube δ E := fun i =>
  { (V i) with
    shade := (V i).shade ∩ W
    measurableSet_shade := (V i).measurableSet_shade.inter hW
    shade_subset := Set.Subset.trans Set.inter_subset_left (V i).shade_subset }

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
@[simp]
theorem interShade_toTube {δ : NNReal} (V : ι → ShadedTube δ E) (W : Set E)
    (hW : MeasurableSet W) (i : ι) : (interShade V W hW i).toTube = (V i).toTube := rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
@[simp]
theorem interShade_shade {δ : NNReal} (V : ι → ShadedTube δ E) (W : Set E)
    (hW : MeasurableSet W) (i : ι) :
    (interShade V W hW i).shade = (V i).shade ∩ W := rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem interShade_shade_subset {δ : NNReal} (V : ι → ShadedTube δ E) (W : Set E)
    (hW : MeasurableSet W) (i : ι) : (interShade V W hW i).shade ⊆ (V i).shade :=
  Set.inter_subset_left

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- At a point of `W` the shade class of the cut family is the shade class of the original
family. -/
theorem shadeClass_interShade {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E) (W : Set E)
    (hW : MeasurableSet W) (assign : ι → ι) (j : ι) {x : E} (hx : x ∈ W) :
    shadeClass s (interShade V W hW) assign j x = shadeClass s V assign j x := by
  classical
  refine Finset.filter_congr ?_
  intro i _
  simp [interShade, hx]

/-- **Cutting every shading by one common measurable set preserves GWZ Definition 2.2**, at the
same hierarchy, the same branching functions and the same constant.

The point is that the cut shade union is contained in `W`, and at a point of `W` no shade class
moves: `ShadedTube.shadeClass_interShade`.  A cut that varies with the tube has no such
property, and that is why the density bracket of
`Kakeya.ml1Boot.IsUniformFactorCore.fine_dens` cannot be installed by shrinking the heavy
shadings of an already uniform family. -/
def shadedUniformTubeSet_interShade {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E}
    {N : ℕ} {C : NNReal} (𝒱 : ShadedUniformTubeSet s V N C) (W : Set E)
    (hW : MeasurableSet W) :
    ShadedUniformTubeSet s (interShade V W hW) N C := by
  classical
  have hmemW : ∀ x ∈ (⋃ i ∈ s, (interShade V W hW i).shade), x ∈ W := by
    intro x hx
    obtain ⟨i, _, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact hxi.2
  have hmemV : ∀ x ∈ (⋃ i ∈ s, (interShade V W hW i).shade), x ∈ (⋃ i ∈ s, (V i).shade) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hxi.1⟩
  exact
    { tubeUniform := 𝒱.tubeUniform
      branchingN := 𝒱.branchingN
      localN := 𝒱.localN
      card_shadeClass_le := by
        intro x hx k hk i hi hxi
        rw [shadeClass_interShade s V W hW _ _ (hmemW x hx)]
        exact 𝒱.card_shadeClass_le x (hmemV x hx) k hk i hi hxi.1
      le_card_shadeClass := by
        intro x hx k hk i hi hxi
        rw [shadeClass_interShade s V W hW _ _ (hmemW x hx)]
        exact 𝒱.le_card_shadeClass x (hmemV x hx) k hk i hi hxi.1
      branchingN_le := by
        intro x hx k hk
        exact 𝒱.branchingN_le x (hmemV x hx) k hk
      le_branchingN := by
        intro x hx k hk
        exact 𝒱.le_branchingN x (hmemV x hx) k hk }

/-! ### Disjoint shadings are uniform for free -/

omit [Nontrivial E] [BorelSpace E] in
/-- **A family with pairwise disjoint shadings satisfies GWZ Definition 2.2 outright**, at the
constant of its tube hierarchy, with `branchingN k = 1` and `localN x k = 1`.

If the shadings are pairwise disjoint then at a point `x` covered by the shading of `i` no other
member of any class covers `x`, so every shade class the fibre of `x` meets is the singleton
`{i}`: the band of `ShadedTube.nonempty_shadedUniformTubeSet_of_band` holds at `B ≡ 1` and
`A = 1`.

Disjointness is *hereditary*, and so is this conclusion: unlike the output of
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`, a Definition 2.2 bundle obtained this way
survives every later pigeonhole on the index set, provided the tube hierarchy is restored on the
subfamily — which `Kakeya.MultiScaleFac.exists_restrict_uniformTubeSet_band` does from a supplied
class-size band.  This is what makes the pair
(`ShadedTube.exists_shade_disjointification`, this lemma) a route to shaded uniformity that
composes with a density pigeonhole, which the shaded uniformizers of `Kakeya/ShadedUniform.lean`
do not.

The price is paid in mass, not in the constant: by
`ShadedTube.exists_shade_disjointification` the disjointified family retains
`|⋃ Y(V)|` of the original `∑ |Y(V)|`, i.e. a `1 / µ(𝕍, Y)` fraction, where `µ` is the
multiplicity of the original family.  That is a genuine loss and is *not* subpolynomial in
general, so this route pays for `Kakeya.ml1Boot.IsUniformFactorCore.fine_refinement` exactly when
the family's multiplicity is at most the refinement budget. -/
theorem nonempty_shadedUniformTubeSet_of_pairwiseDisjoint {δ : NNReal} {s : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {Cu C : NNReal}
    (𝒰 : UniformTubeSet s (fun i => (V i).toTube) N Cu) (hCuC : Cu ≤ C) (hC1 : 1 ≤ C)
    (hdisj : (s : Set ι).Pairwise fun i j => Disjoint (V i).shade (V j).shade) :
    Nonempty (ShadedUniformTubeSet s V N C) := by
  classical
  refine nonempty_shadedUniformTubeSet_of_band 𝒰 hCuC hC1 hC1 (fun _ => 1) ?_
  intro x _ k _ i hi hxi
  have hsingleton :
      shadeClass s V (𝒰.cover.assign k) (𝒰.cover.assign k i) x = {i} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · simp only [shadeClass, coverClass, Finset.mem_filter]
      exact ⟨⟨hi, trivial⟩, hxi⟩
    · intro j hj
      simp only [shadeClass, coverClass, Finset.mem_filter] at hj
      by_contra hne
      exact (hdisj hj.1.1 hi hne).le_bot ⟨hj.2, hxi⟩
  rw [hsingleton]
  simp

/-! ### Making the shadings disjoint -/

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- **Disjointification of a shading.**  Every shaded family has a shade-refinement — tubes
unchanged, shadings only shrunk, no subfamily taken — whose shadings are pairwise disjoint on
the index set and whose union is unchanged.  The retained mass is therefore exactly
`|⋃_{i ∈ s} Y(V_i)|`, that is, a `1 / µ(𝕍, Y)` fraction of `∑_{i ∈ s} |Y(V_i)|`.

The construction is the usual greedy one against a well-ordering of the index type: the shading
of `i` keeps only the points not already covered by an earlier member of `s`.  Since no subfamily
is taken, this composes with `ShadedTube.nonempty_shadedUniformTubeSet_of_pairwiseDisjoint`
without disturbing any hierarchy. -/
theorem exists_shade_disjointification {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E) :
    ∃ Z : ι → ShadedTube δ E,
      (∀ i, (Z i).toTube = (V i).toTube) ∧
      (∀ i, (Z i).shade ⊆ (V i).shade) ∧
      (s : Set ι).Pairwise (fun i j => Disjoint (Z i).shade (Z j).shade) ∧
      (⋃ i ∈ s, (Z i).shade) = (⋃ i ∈ s, (V i).shade) ∧
      ∑ i ∈ s, volume (Z i).shade = volume (⋃ i ∈ s, (V i).shade) := by
  classical
  letI : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  set earlier : ι → Set E := fun i => ⋃ j ∈ s.filter (fun j => j < i), (V j).shade with hearlier
  have hmeas : ∀ i, MeasurableSet (earlier i) := by
    intro i
    exact Finset.measurableSet_biUnion _ fun j _ => (V j).measurableSet_shade
  refine ⟨fun i =>
    { (V i) with
      shade := (V i).shade \ earlier i
      measurableSet_shade := (V i).measurableSet_shade.diff (hmeas i)
      shade_subset := Set.Subset.trans Set.sdiff_subset (V i).shade_subset }, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; rfl
  · intro i; exact Set.sdiff_subset
  · intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with h | h
    · refine Set.disjoint_left.mpr fun x hxi hxj => hxj.2 ?_
      exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hi, h⟩) hxi.1
    · refine Set.disjoint_left.mpr fun x hxi hxj => hxi.2 ?_
      exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hj, h⟩) hxj.1
  · apply Set.Subset.antisymm
    · exact Set.iUnion₂_mono fun i _ => Set.sdiff_subset
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨m, hm, hmin⟩ :=
        (Finset.exists_min_image (s.filter (fun j => x ∈ (V j).shade)) id
          ⟨i, Finset.mem_filter.mpr ⟨hi, hxi⟩⟩)
      obtain ⟨hms, hmx⟩ := Finset.mem_filter.mp hm
      refine Set.mem_iUnion₂.mpr ⟨m, hms, hmx, ?_⟩
      intro hmem
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hmem
      obtain ⟨hjs, hjm⟩ := Finset.mem_filter.mp hj
      exact absurd (hmin j (Finset.mem_filter.mpr ⟨hjs, hxj⟩)) (not_le.mpr hjm)
  · have hdisj : (s : Set ι).Pairwise
        (Function.onFun Disjoint (fun i => (V i).shade \ earlier i)) := by
      intro i hi j hj hij
      rcases lt_or_gt_of_ne hij with h | h
      · refine Set.disjoint_left.mpr fun x hxi hxj => hxj.2 ?_
        exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hi, h⟩) hxi.1
      · refine Set.disjoint_left.mpr fun x hxi hxj => hxi.2 ?_
        exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hj, h⟩) hxj.1
    have hunion : (⋃ i ∈ s, ((V i).shade \ earlier i)) = (⋃ i ∈ s, (V i).shade) := by
      apply Set.Subset.antisymm
      · exact Set.iUnion₂_mono fun i _ => Set.sdiff_subset
      · intro x hx
        obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
        obtain ⟨m, hm, hmin⟩ :=
          (Finset.exists_min_image (s.filter (fun j => x ∈ (V j).shade)) id
            ⟨i, Finset.mem_filter.mpr ⟨hi, hxi⟩⟩)
        obtain ⟨hms, hmx⟩ := Finset.mem_filter.mp hm
        refine Set.mem_iUnion₂.mpr ⟨m, hms, hmx, ?_⟩
        intro hmem
        obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hmem
        obtain ⟨hjs, hjm⟩ := Finset.mem_filter.mp hj
        exact absurd (hmin j (Finset.mem_filter.mpr ⟨hjs, hxj⟩)) (not_le.mpr hjm)
    rw [← hunion]
    exact (measure_biUnion_finset hdisj
      (fun i _ => (V i).measurableSet_shade.diff (hmeas i))).symm

end ShadedTube

end
