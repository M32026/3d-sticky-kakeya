/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Shading
public import Kakeya.Uniform

/-!
  # Shade-fibre pigeonholing, and shaded uniformity on the tube hierarchy

  The measure-theoretic machinery on which the shaded uniformization of GWZ
  Definition 2.2 is built, followed by that uniformization itself.  The
  definition is `ShadedTube.ShadedUniformTubeSet`, which reads the
  per-point data on the nodes of one tube hierarchy; the refinement statement is
  `ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`.

  * `exists_dominant_band_finset` (from `Kakeya.Pigeonhole`) — the measure
    pigeonhole selecting a dominant cell of a finite partition.  The pointwise
    shade count itself is `ShadedBody.pointwiseMultiplicity`.
  * `shadeFiber`, `measurableSet_shadeFiber_eq`, `exists_dominant_profile`,
    `measurableSet_profile_eq`, `exists_dominant_profile_sum` — the fibre of a
    point inside a shaded family, and the pigeonhole that fixes one fibre
    profile across a dominant cell.
  * `refinedShade`, `shadeRestrict`, `refinedShade_fiber` — the refined shading
    cut out by a per-fibre refinement map, and the identity that its fibre is
    the refined fibre.
  * `sum_volume_eq_lintegral_card`, `sum_le_of_fiber_card_le` — the
    multiplicity-integral identity turning a pointwise fibre bound into a
    shade-mass bound.

  All of these are proved and are consumed by the shaded uniformization in the
  second half of this file.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace ShadedTube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasureSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

open Classical in
/-- **Shade-fiber** at `x` (Route B Step 2/R3): the tubes of `t` whose shade
contains `x`.  As `x` varies it takes finitely many values (subsets of `t`); the
refined shading `Y'` is defined through a deterministic map `g` of this fiber. -/
private noncomputable def shadeFiber {δ : NNReal} (t : Finset ι) (V : ι → ShadedTube δ E)
    (x : E) : Finset ι :=
  t.filter (fun i => x ∈ (V i).shade)

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- Each level set `{x | shadeFiber t V x = S}` is measurable (a finite
intersection of shades and shade-complements), so any function of the fiber has
measurable level sets. -/
private lemma measurableSet_shadeFiber_eq {δ : NNReal} (t : Finset ι)
    (V : ι → ShadedTube δ E) (S : Finset ι) :
    MeasurableSet {x : E | shadeFiber t V x = S} := by
  classical
  by_cases hS : S ⊆ t
  · have hset : {x : E | shadeFiber t V x = S}
        = (⋂ i ∈ S, (V i).shade) ∩ (⋂ i ∈ (t \ S), (V i).shadeᶜ) := by
      ext x
      simp only [shadeFiber, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_compl_iff, Finset.mem_sdiff]
      constructor
      · intro hx
        refine ⟨fun i hiS => ?_, fun i hi => ?_⟩
        · have : i ∈ t.filter (fun i => x ∈ (V i).shade) := hx ▸ hiS
          exact (Finset.mem_filter.mp this).2
        · intro hxi
          have : i ∈ t.filter (fun i => x ∈ (V i).shade) := Finset.mem_filter.mpr ⟨hi.1, hxi⟩
          exact hi.2 (hx ▸ this)
      · rintro ⟨h1, h2⟩
        apply Finset.ext
        intro i
        rw [Finset.mem_filter]
        constructor
        · rintro ⟨hit, hxi⟩
          by_contra hiS
          exact h2 i ⟨hit, hiS⟩ hxi
        · intro hiS
          exact ⟨hS hiS, h1 i hiS⟩
    rw [hset]
    exact MeasurableSet.inter
      (MeasurableSet.biInter S.countable_toSet (fun i _ => (V i).measurableSet_shade))
      (MeasurableSet.biInter (t \ S).countable_toSet
        (fun i _ => (V i).measurableSet_shade.compl))
  · have hempty : {x : E | shadeFiber t V x = S} = ∅ := by
      ext x
      simp only [shadeFiber, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hS (hx ▸ Finset.filter_subset _ _)
    rw [hempty]; exact MeasurableSet.empty

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- **Profile pigeonhole** (R4): the fiber map `x ↦ shadeFiber t V x` takes finitely many values, so
`x ↦ bN (shadeFiber t V x)` ranges over the `Finset` `t.powerset.image bN`; among the level sets
`{x | bN (F_x) = p}` one captures a `1/|image|` share of the `volume` of any set `W`.  Abstracting
over `bN` lets it be instantiated with the dyadic index of the per-fiber branching. -/
private lemma exists_dominant_profile {δ : NNReal} {β : Type*} [DecidableEq β]
    (t : Finset ι) (V : ι → ShadedTube δ E) (bN : Finset ι → β) (W : Set E) :
    ∃ p : β, p ∈ t.powerset.image bN ∧
      volume W ≤ (t.powerset.image bN).card
        • volume (W ∩ {x : E | bN (shadeFiber t V x) = p}) := by
  classical
  apply exists_dominant_band_finset (t.powerset.image bN)
    ⟨bN ∅, Finset.mem_image.mpr ⟨∅, Finset.empty_mem_powerset _, rfl⟩⟩ W
    (fun p => {x : E | bN (shadeFiber t V x) = p})
  intro x _hx
  exact Set.mem_iUnion₂.mpr ⟨bN (shadeFiber t V x),
    Finset.mem_image.mpr ⟨shadeFiber t V x,
      Finset.mem_powerset.mpr (Finset.filter_subset _ _), rfl⟩, rfl⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- The dominant-profile cell `X* = {x | bN (F_x) = p}` is measurable: it is the
finite union of the (measurable) fiber level sets `{x | F_x = S}` over the
sub-fibers `S ⊆ t` with `bN S = p`. -/
private lemma measurableSet_profile_eq {δ : NNReal} {β : Type*}
    (t : Finset ι) (V : ι → ShadedTube δ E) (bN : Finset ι → β) (p : β) :
    MeasurableSet {x : E | bN (shadeFiber t V x) = p} := by
  classical
  have hset : {x : E | bN (shadeFiber t V x) = p}
      = ⋃ S ∈ t.powerset.filter (fun S => bN S = p), {x : E | shadeFiber t V x = S} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter,
      Finset.mem_powerset, exists_prop]
    constructor
    · intro hx
      exact ⟨shadeFiber t V x, ⟨Finset.filter_subset _ _, hx⟩, rfl⟩
    · rintro ⟨S, ⟨_, hSp⟩, hxS⟩
      rw [hxS]; exact hSp
  rw [hset]
  exact Finset.measurableSet_biUnion _ (fun S _ => measurableSet_shadeFiber_eq t V S)

open Classical in
omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- **Sum profile pigeonhole** (R4, λ-survival form): one profile value `p`
captures a `1/|image|` share of the *sum* `∑ᵢ vol (A i)` (the quantity inside
`fullness'`).  Unlike `exists_dominant_profile`, which bounds the volume of a
single union, this bounds the sum, since the profile level sets partition `E`. -/
private lemma exists_dominant_profile_sum {δ : NNReal} {β : Type*} [DecidableEq β]
    (t : Finset ι) (V : ι → ShadedTube δ E) (bN : Finset ι → β)
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i)) :
    ∃ p : β, p ∈ t.powerset.image bN ∧
      ∑ i ∈ t, volume (A i)
        ≤ (t.powerset.image bN).card
          • ∑ i ∈ t, volume (A i ∩ {x : E | bN (shadeFiber t V x) = p}) := by
  classical
  set T := t.powerset.image bN with hT
  have hTne : T.Nonempty :=
    ⟨bN ∅, Finset.mem_image.mpr ⟨∅, Finset.empty_mem_powerset _, rfl⟩⟩
  have hpart : ∀ i, volume (A i)
      = ∑ p ∈ T, volume (A i ∩ {x : E | bN (shadeFiber t V x) = p}) := by
    intro i
    have hd : (↑T : Set β).PairwiseDisjoint
        (fun p => A i ∩ {x : E | bN (shadeFiber t V x) = p}) := by
      intro p _ q _ hpq
      apply Set.disjoint_left.mpr
      intro x hxp hxq
      exact hpq (hxp.2.symm.trans hxq.2)
    have hm : ∀ p ∈ T, MeasurableSet (A i ∩ {x : E | bN (shadeFiber t V x) = p}) :=
      fun p _ => (hA i).inter (measurableSet_profile_eq t V bN p)
    have hcover : A i = ⋃ p ∈ T, A i ∩ {x : E | bN (shadeFiber t V x) = p} := by
      ext x
      simp only [Set.mem_iUnion₂, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · intro hx
        exact ⟨bN (shadeFiber t V x),
          Finset.mem_image.mpr ⟨shadeFiber t V x,
            Finset.mem_powerset.mpr (Finset.filter_subset _ _), rfl⟩, hx, rfl⟩
      · rintro ⟨p, _, hx, _⟩; exact hx
    conv_lhs => rw [hcover]
    exact MeasureTheory.measure_biUnion_finset hd hm
  have hsum : ∑ i ∈ t, volume (A i)
      = ∑ p ∈ T, ∑ i ∈ t, volume (A i ∩ {x : E | bN (shadeFiber t V x) = p}) := by
    simp_rw [hpart]
    rw [Finset.sum_comm]
  obtain ⟨p, hp, hmax⟩ := T.exists_max_image
    (fun p => ∑ i ∈ t, volume (A i ∩ {x : E | bN (shadeFiber t V x) = p})) hTne
  refine ⟨p, hp, ?_⟩
  rw [hsum]
  calc ∑ q ∈ T, ∑ i ∈ t, volume (A i ∩ {x : E | bN (shadeFiber t V x) = q})
      ≤ ∑ _q ∈ T, ∑ i ∈ t, volume (A i ∩ {x : E | bN (shadeFiber t V x) = p}) :=
        Finset.sum_le_sum (fun q hq => hmax q hq)
    _ = T.card • ∑ i ∈ t, volume (A i ∩ {x : E | bN (shadeFiber t V x) = p}) := by
        rw [Finset.sum_const]

/-- **Refined shading** from a fiber-refinement map `g` (think `g F = F'`, the
uniform sub-fiber): keep `x ∈ Y(i)` only when `i` survives in `g (shadeFiber x)`. -/
private noncomputable def refinedShade {δ : NNReal} (t : Finset ι) (V : ι → ShadedTube δ E)
    (g : Finset ι → Finset ι) (i : ι) : Set E :=
  (V i).shade ∩ {x : E | i ∈ g (shadeFiber t V x)}

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
private lemma measurableSet_refinedShade {δ : NNReal} (t : Finset ι)
    (V : ι → ShadedTube δ E) (g : Finset ι → Finset ι) (i : ι) :
    MeasurableSet (refinedShade t V g i) := by
  classical
  have hset : {x : E | i ∈ g (shadeFiber t V x)}
      = ⋃ S ∈ (t.powerset.filter (fun S => i ∈ g S)),
          {x : E | shadeFiber t V x = S} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter,
      Finset.mem_powerset, exists_prop]
    constructor
    · intro hx
      exact ⟨shadeFiber t V x, ⟨Finset.filter_subset _ _, hx⟩, rfl⟩
    · rintro ⟨S, ⟨_, hiS⟩, hxS⟩
      rw [hxS]; exact hiS
  refine (V i).measurableSet_shade.inter ?_
  rw [hset]
  exact Finset.measurableSet_biUnion _ (fun S _ => measurableSet_shadeFiber_eq t V S)

/-- `refinedShade` further cut to a point-cell `X` (the R4 dominant-profile set
`X*`).  Kept as an opaque `def` so that `Decidable (x ∈ shadeRestrict …)` resolves
via `Classical.propDecidable` rather than `decidableInter` — matching the instance
baked into the shade-fibre index sets of `ShadedUniformTubeSet`. -/
private noncomputable def shadeRestrict {δ : NNReal} (t : Finset ι) (V : ι → ShadedTube δ E)
    (g : Finset ι → Finset ι) (X : Set E) (i : ι) : Set E :=
  refinedShade t V g i ∩ X

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
private lemma measurableSet_shadeRestrict {δ : NNReal} (t : Finset ι) (V : ι → ShadedTube δ E)
    (g : Finset ι → Finset ι) {X : Set E} (hX : MeasurableSet X) (i : ι) :
    MeasurableSet (shadeRestrict t V g X i) :=
  (measurableSet_refinedShade t V g i).inter hX

open Classical in
omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- The `refinedShade`-fiber at `x` is exactly `g (shadeFiber x)`, provided `g`
shrinks fibers (`g F ⊆ F`).  This is the "Y′-fiber = F_x′" identity. -/
private lemma refinedShade_fiber {δ : NNReal} (t : Finset ι) (V : ι → ShadedTube δ E)
    (g : Finset ι → Finset ι) (hg : ∀ F, g F ⊆ F) (x : E) :
    (t.filter (fun i => x ∈ refinedShade t V g i)) = g (shadeFiber t V x) := by
  classical
  ext i
  simp only [refinedShade, Finset.mem_filter, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, _, hig⟩; exact hig
  · intro hig
    have hiF : i ∈ shadeFiber t V x := hg _ hig
    rw [shadeFiber, Finset.mem_filter] at hiF
    exact ⟨hiF.1, hiF.2, hig⟩

open Classical in
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [BorelSpace E] [ProperSpace E] in
/-- **g-step** (abstract): if pointwise the shade-fibre is at most `(Kb+1)^(M-1)`
times the refined fibre, then `∑ vol (sh i) ≤ (Kb+1)^(M-1) · ∑ vol (Yr i)`.  Proved
by the multiplicity-integral identity `sum_volume_eq_lintegral_card`.  Abstract over
`sh`, `Yr` so it runs in a clean context. -/
private lemma sum_le_of_fiber_card_le (M Kb : ℕ) (s' : Finset ι)
    (sh Yr : ι → Set E) (hsh : ∀ i, MeasurableSet (sh i)) (hYr : ∀ i, MeasurableSet (Yr i))
    (hcard : ∀ x : E, (s'.filter (fun i => x ∈ sh i)).card
        ≤ (Kb + 1) ^ (M - 1) * (s'.filter (fun i => x ∈ Yr i)).card) :
    ∑ i ∈ s', volume (sh i) ≤ ((Kb + 1) ^ (M - 1) : ℕ) * ∑ i ∈ s', volume (Yr i) := by
  classical
  rw [sum_volume_eq_lintegral_card s' sh hsh, sum_volume_eq_lintegral_card s' Yr hYr,
      ← MeasureTheory.lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
  apply MeasureTheory.lintegral_mono
  intro x
  dsimp only
  calc (↑(s'.filter (fun i => x ∈ sh i)).card : ENNReal)
      ≤ ↑((Kb + 1) ^ (M - 1) * (s'.filter (fun i => x ∈ Yr i)).card) := by exact_mod_cast hcard x
    _ = ((Kb + 1) ^ (M - 1) : ℕ) * ↑(s'.filter (fun i => x ∈ Yr i)).card := by push_cast; ring

universe u

/-!
## Shaded uniformity, re-based on the tube hierarchy

GWZ Definition 2.2 and the §2 shaded refinement, read against the tube hierarchy, built on the
shade-fibre pigeonholing above.

### What changes, and why

**The per-point data lives on the ambient nodes.**  The older scale-set predicate (a shaded family
was uniform on a set of scales) gave every point `x` of the shade union its own
`Tube.IsUniformAtScale` bundle, each with its own `parent` and `parentTube`,
and nothing tied any of them either to each other or to the ambient uniformity of the underlying
tubes.  That is the same defect that `Tube.UniformTubeSet` removes at the tube level, and it
had the same symptom: the shared branching count had to be glued on by two extra inequalities
(`branchingN_le` and `le_branchingN`) against a family of unrelated objects, and matching the
tube-level constant then required the banding to be performed simultaneously across all scales lest
the constant compound to `C^N`.

Here the fibre of `x` is measured on the nodes of the *one* hierarchy carried by `tubeUniform`:
`shadeClass` is the part of a node's class that `x` sees.  The branching sandwich is then a
statement about a single indexed family, and the simultaneity is structural rather than a proof
obligation.

**Only the nodes the fibre actually meets are constrained.**  A node may contain no member whose
shading covers `x`; demanding a two-sided bracket there would force `branchingN k = 0`.  The
quantifier is therefore over the nodes hit by the fibre, spelled as `assign k i` for `i` in the
fibre, which is automatically a hit node and needs no auxiliary filter.

**The loss is shaped like the tube-level one.**  Both the cardinality loss and the fullness loss are
`(A (log₂ #s + 1))^{O(N)}` with `A` depending on the dimension only and quantified before `N` and
`δ`, exactly as in `Tube.exists_uniformTubeSet_subfamily`.  That is what allows the statement
to be instantiated at the `δ`-dependent grid length `Tube.ssfGridLen δ = ⌈log log 1/δ⌉` of
Definition 2.2; see `ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`.
-/

/-! ### The part of a class that a point sees -/

/-- The members of the class of the node `j` whose shading covers `x`: the fibre of `x` inside that
class.  This is the object on which GWZ Definition 2.2's local uniformity is imposed, replacing the
per-point hierarchy of the older scale-set predicate. -/
noncomputable def shadeClass {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E)
    (assign : ι → ι) (j : ι) (x : E) : Finset ι :=
  open scoped Classical in
  (coverClass s assign j).filter (fun i => x ∈ (V i).shade)

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
theorem shadeClass_subset {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E)
    (assign : ι → ι) (j : ι) (x : E) :
    shadeClass s V assign j x ⊆ coverClass s assign j := by
  classical
  simp [shadeClass]

/-! ### Uniform shaded sets of tubes -/

/-- **GWZ Definition 2.2, read against the tube hierarchy.**  `tubeUniform` is the ambient hierarchy
of the underlying `δ`-tubes, `branchingN` the single per-scale count shared by all points and
`localN x` the count at the point `x`: the two class brackets say every node the fibre of `x` meets
carries `≈ localN x k` members of that fibre, and the two branching brackets say that `localN x k`
does not depend on `x` beyond a factor `C`. -/
structure ShadedUniformTubeSet {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E) (N : ℕ)
    (C : NNReal) where
  /-- The underlying tubes carry a uniform hierarchy along the grid `ρ_k = δ^{k/N}`. -/
  tubeUniform : UniformTubeSet s (fun i => (V i).toTube) N C
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

/-- Weakening the constant.  The hierarchy and both branching functions are unchanged. -/
def ShadedUniformTubeSet.mono {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E} {N : ℕ}
    {C C' : NNReal} (𝒱 : ShadedUniformTubeSet s V N C) (hC : C ≤ C') :
    ShadedUniformTubeSet s V N C' where
  tubeUniform := 𝒱.tubeUniform.mono hC
  branchingN := 𝒱.branchingN
  localN := 𝒱.localN
  card_shadeClass_le x hx k hk i hi hxi :=
    (𝒱.card_shadeClass_le x hx k hk i hi hxi).trans (mul_le_mul_left hC _)
  le_card_shadeClass x hx k hk i hi hxi :=
    (𝒱.le_card_shadeClass x hx k hk i hi hxi).trans (mul_le_mul_left hC _)
  branchingN_le x hx k hk := (𝒱.branchingN_le x hx k hk).trans (mul_le_mul_left hC _)
  le_branchingN x hx k hk := (𝒱.le_branchingN x hx k hk).trans (mul_le_mul_left hC _)

/-! ### Decomposition of `exists_shadedUniformTubeSet_subfamily`

The dyadic banding of the per-point counts happens on the ambient nodes of the tube-level cover
`𝒰.cover`, exactly as the `ShadedUniformTubeSet` fibre `shadeClass` reads them.  A `uniformTubeSet`
(which `exists_uniformTubeSet_subfamily` supplies at the tube level) plus the shading `V` determine,
at each point `x` and each grid index, the number of members of that point's node class whose
shading covers `x`; the refinement makes those numbers comparable across nodes and across points.
It is done in two stages, for the reason set out in the docstring of
`exists_balanced_shadeRefinement`:

  * `exists_balanced_pruning_fibre`, `exists_fibre_balancer` — prune inside each fibre so that all
    nodes met at a given grid index carry comparable counts;
  * `shadeClass_refined_eq`, `dyadic_band_of_band` — read that band off the refined shading and
    round it to a power of two;
  * `card_image_bandProfile_le` — the rounded band vectors range over a set of size
    `(clamp+1)^(N+1)`, so a second pigeonhole fixes one of them across points;
  * `fibre_card_le_of_balancer`, `sum_shade_le_sum_refinedShade`, `fullness_le_of_shade_sum` — the
    two fullness losses, one per stage, whence the exponent `2N+2`.
-/

/-! ### Stage 1: balancing one fibre along the hierarchy -/

omit [Nontrivial E] [MeasureSpace E] [BorelSpace E] in
/-- **Stage 1, one fibre.**  A fibre `F ⊆ s` has a subset `F'` on which, at every grid index, all
nodes met by `F'` carry the same number of `F'`-members up to a factor `2`.  This is
`Tube.exists_pruned_subset_noroot_notop` applied to `F` with the ambient cover's own
`parent`/`assign`, legitimate because `GridCoverSystem.nested` makes the classes of `F` refine along
the grid.  A dummy root level is prepended so that the pigeonhole's loss starts at `1`. -/
private theorem exists_balanced_pruning_fibre {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} (𝒢 : GridCoverSystem s T N)
    {F : Finset ι} (hFs : F ⊆ s) (hFne : F.Nonempty) :
    ∃ (F' : Finset ι) (bnd : ℕ → ℕ),
      F' ⊆ F ∧ F'.Nonempty ∧
      (F.card : ℝ) ≤ ((⌊Real.logb 2 (F.card : ℝ)⌋₊ : ℝ) + 1) ^ (N + 1) * (F'.card : ℝ) ∧
      (∀ k ≤ N, ∀ i ∈ F',
        bnd k ≤ (coverClass F' (𝒢.assign k) (𝒢.assign k i)).card ∧
        (coverClass F' (𝒢.assign k) (𝒢.assign k i)).card < 2 * bnd k) := by
  classical
  have hFne' : F.Nonempty := hFne
  obtain ⟨i₀, hi₀⟩ := hFne
  let parentE : ℕ → Finset ι := fun k => if k = 0 then {i₀} else 𝒢.indexSet (k - 1)
  let assignE : ℕ → ι → ι := fun k => if k = 0 then (fun _ => i₀) else 𝒢.assign (k - 1)
  have h_assign_mem' : ∀ k ≤ N + 1, ∀ ⦃i⦄, i ∈ F → assignE k i ∈ parentE k := by
    intro k hk i hi
    by_cases hk0 : k = 0
    · subst k
      simp [assignE, parentE]
    · have hk1 : k - 1 ≤ N := by omega
      simpa [assignE, parentE, hk0] using 𝒢.assign_mem (k - 1) hk1 i (hFs hi)
  have h_nested' : ∀ k, k < N + 1 → ∀ ⦃i j⦄, i ∈ F → j ∈ F →
      assignE (k + 1) i = assignE (k + 1) j → assignE k i = assignE k j := by
    intro k hk i j hi hj h_eq
    by_cases hk0 : k = 0
    · subst k
      simp [assignE]
    · have hkn : (k - 1) + 1 ≤ N := by omega
      have h_eq' : 𝒢.assign k i = 𝒢.assign k j := by
        simpa [assignE, Nat.succ_eq_add_one] using h_eq
      have h_eq'' : 𝒢.assign (k - 1 + 1) i = 𝒢.assign (k - 1 + 1) j := by
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using h_eq'
      simpa [assignE, hk0] using 𝒢.nested (k - 1) hkn i (hFs hi) j (hFs hj) h_eq''
  have hC₀_pos : (0 : ℝ) < 1 := by norm_num
  have hC₀ : ((parentE 0).card : ℝ) ≤ 1 := by
    simp [parentE]
  obtain ⟨s', bnd', parent', hs'_sub, hcard, hpsub, hamem, hact, hband⟩ :=
    Tube.exists_pruned_subset_noroot_notop (s := F) (M := N + 1) hFne'
      parentE assignE h_assign_mem' h_nested' (C₀ := 1) hC₀_pos hC₀
  have hFcard_pos : (1 : ℝ) ≤ (F.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨i₀, hi₀⟩)
  have hde : (0 : ℝ) < 1 * (((⌊Real.logb 2 (F.card : ℝ)⌋₊ : ℝ) + 1) ^ (N + 1)) := by
    positivity
  have hcard' : (F.card : ℝ)
      ≤ (((⌊Real.logb 2 (F.card : ℝ)⌋₊ : ℝ) + 1) ^ (N + 1)) * (s'.card : ℝ) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using (div_le_iff₀ hde).mp hcard
  refine ⟨s', fun k => bnd' (k + 1), hs'_sub, ?_hne, ?_hcard, ?_hband⟩
  · have hh : (0 : ℝ) < (((⌊Real.logb 2 (F.card : ℝ)⌋₊ : ℝ) + 1) ^ (N + 1)) * (s'.card : ℝ) := by
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_trans hFcard_pos hcard')
    have hX2 : (0 : ℝ) < (((⌊Real.logb 2 (F.card : ℝ)⌋₊ : ℝ) + 1) ^ (N + 1)) := by
      positivity
    refine Finset.card_pos.mp ?_
    exact_mod_cast (mul_pos_iff_of_pos_left hX2).mp hh
  · exact hcard'
  · intro k hk i hi
    have hk1 : k + 1 ≤ N + 1 := by omega
    have hmv : assignE (k + 1) i ∈ parent' (k + 1) := by
      exact hamem (k + 1) hk1 hi
    have hvpar : 𝒢.assign k i ∈ parent' (k + 1) := by
      simpa [assignE, Nat.succ_eq_add_one] using hmv
    have hfilter : s'.filter (fun j => assignE (k + 1) j = 𝒢.assign k i)
        = coverClass s' (𝒢.assign k) (𝒢.assign k i) := by
      simp [assignE, coverClass]
    have hband' := hband (k + 1) hk1 (𝒢.assign k i) hvpar
    constructor
    · rw [← hfilter]
      exact hband'.1
    · rw [← hfilter]
      exact hband'.2

omit [Nontrivial E] [MeasureSpace E] [BorelSpace E] in
/-- **Stage 1, all fibres at once.**  A choice of balanced pruning for every fibre, obtained from
`exists_balanced_pruning_fibre` by `choose`.  Fibres that are not subsets of `s`, and the empty
fibre, are sent to `∅`; the conclusions are guarded accordingly.  This is the `g` that
`ShadedTube.refinedShade` consumes. -/
private theorem exists_fibre_balancer {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} (𝒢 : GridCoverSystem s T N) :
    ∃ (g : Finset ι → Finset ι) (bnd : Finset ι → ℕ → ℕ),
      (∀ F, g F ⊆ F) ∧
      (∀ F, F ⊆ s → F.Nonempty → (g F).Nonempty) ∧
      (∀ F, F ⊆ s →
        (F.card : ℝ) ≤ ((⌊Real.logb 2 (F.card : ℝ)⌋₊ : ℝ) + 1) ^ (N + 1) * ((g F).card : ℝ)) ∧
      (∀ F, F ⊆ s → ∀ k ≤ N, ∀ i ∈ g F,
        bnd F k ≤ (coverClass (g F) (𝒢.assign k) (𝒢.assign k i)).card ∧
        (coverClass (g F) (𝒢.assign k) (𝒢.assign k i)).card < 2 * bnd F k) := by
  classical
  have key : ∀ F : Finset ι, ∃ p : Finset ι × (ℕ → ℕ),
      p.1 ⊆ F ∧
      (F ⊆ s → F.Nonempty → p.1.Nonempty) ∧
      (F ⊆ s → (F.card : ℝ) ≤ ((⌊Real.logb 2 (F.card : ℝ)⌋₊ : ℝ) + 1) ^ (N + 1) * (p.1.card : ℝ)) ∧
      (F ⊆ s → ∀ k ≤ N, ∀ i ∈ p.1,
        p.2 k ≤ (coverClass p.1 (𝒢.assign k) (𝒢.assign k i)).card ∧
        (coverClass p.1 (𝒢.assign k) (𝒢.assign k i)).card < 2 * p.2 k) := by
    intro F
    by_cases hF : F ⊆ s ∧ F.Nonempty
    · obtain ⟨F', bnd, h1, h2, h3, h4⟩ :=
        exists_balanced_pruning_fibre (s := s) (T := T) (N := N) 𝒢 hF.1 hF.2
      exact ⟨(F', bnd), h1, fun _ _ => h2, fun _ => h3, fun _ => h4⟩
    · refine ⟨(∅, fun _ => 0), ?_, ?_, ?_, ?_⟩
      · simp
      · intro hFs hFne
        exact absurd ⟨hFs, hFne⟩ hF
      · intro hFs
        have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp
          (by intro hne; exact hF ⟨hFs, hne⟩)
        simp [hFempty]
      · intro hFs k hk i hi
        simp at hi
  choose p hp using key
  refine ⟨fun F => (p F).1, fun F => (p F).2, ?_, ?_, ?_, ?_⟩
  · intro F; exact (hp F).1
  · intro F hFs hFne; exact (hp F).2.1 hFs hFne
  · intro F hFs; exact (hp F).2.2.1 hFs
  · intro F hFs; exact (hp F).2.2.2 hFs

/-! ### Stage 2 ingredients -/

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- The retained fibre of a node, after both stages.  For a point of the dominant cell `X` the
`V'`-fibre is `g (shadeFiber s V x)` — this is `ShadedTube.refinedShade_fiber`, the identity
that makes stage 1 idempotent — so intersecting with a node class gives the class of that node
inside the pruned fibre. -/
private theorem shadeClass_refined_eq {δ : NNReal} {s : Finset ι} {V V' : ι → ShadedTube δ E}
    (g : Finset ι → Finset ι) (hg_sub : ∀ F, g F ⊆ F) (X : Set E)
    (hV' : ∀ i, (V' i).shade = ShadedTube.shadeRestrict s V g X i)
    (assign : ι → ι) (j : ι) {x : E} (hxX : x ∈ X) :
    shadeClass s V' assign j x
      = coverClass (g (ShadedTube.shadeFiber s V x)) assign j := by
  classical
  ext i
  simp only [shadeClass, coverClass, Finset.mem_filter, hV' i,
    ShadedTube.shadeRestrict, Set.mem_inter_iff]
  have hfib : i ∈ s ∧ x ∈ ShadedTube.refinedShade s V g i ↔
      i ∈ g (ShadedTube.shadeFiber s V x) := by
    rw [← ShadedTube.refinedShade_fiber s V g hg_sub x]
    rw [Finset.mem_filter]
  tauto

/-- From a factor-`2` band on `b` and the clamp being inactive, a factor-`4` *dyadic* band.  The
extra factor `2` is the price of rounding the band value `b` to `2 ^ ⌊log₂ b⌋`; rounding is what
makes the band vector range over a set of size `(clamp+1)^{N+1}`, which is what the stage-2
pigeonhole needs. -/
private theorem dyadic_band_of_band {m b clamp p : ℕ}
    (hb : b ≤ m) (hm : m < 2 * b) (hclamp : Nat.log 2 m ≤ clamp)
    (hp : min (Nat.log 2 b) clamp = p) :
    2 ^ p ≤ m ∧ m < 4 * 2 ^ p := by
  have hbne : b ≠ 0 := by
    intro hb0
    omega
  have hmin_eq : min (Nat.log 2 b) clamp = Nat.log 2 b := by
    apply min_eq_left
    exact le_trans (Nat.log_mono_right hb) hclamp
  have hp_eq : p = Nat.log 2 b := by
    rw [hmin_eq] at hp
    exact hp.symm
  constructor
  · rw [hp_eq]
    exact (Nat.pow_log_le_self 2 hbne).trans hb
  · rw [hp_eq]
    have hb_lt2 : b < 2 * 2 ^ Nat.log 2 b := by
      simpa [pow_succ'] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) b
    calc
      m < 2 * b := hm
      _ < 2 * (2 * 2 ^ Nat.log 2 b) := Nat.mul_lt_mul_of_pos_left hb_lt2 (by norm_num : 0 < 2)
      _ = 4 * 2 ^ Nat.log 2 b := by ring

/-- The per-fibre cardinality loss, converted from the polylogarithm in `|F|` to the clamp. -/
private theorem fibre_card_le_of_balancer {N clamp : ℕ} (F Fg : Finset ι)
    (hFg : (F.card : ℝ) ≤ ((⌊Real.logb 2 (F.card : ℝ)⌋₊ : ℝ) + 1) ^ (N + 1) * (Fg.card : ℝ))
    (hclamp : Nat.log 2 F.card ≤ clamp) :
    F.card ≤ (clamp + 1) ^ (N + 1) * Fg.card := by
  have hfloor : (⌊Real.logb 2 (F.card : ℝ)⌋₊ : ℝ) = (Nat.log 2 F.card : ℝ) := by
    exact_mod_cast (Real.natFloor_logb_natCast 2 F.card)
  have hFg' : (F.card : ℝ) ≤ ((Nat.log 2 F.card : ℝ) + 1) ^ (N + 1) * (Fg.card : ℝ) := by
    simpa [hfloor] using hFg
  have hclamp_cast : (Nat.log 2 F.card : ℝ) ≤ (clamp : ℝ) := by
    exact_mod_cast hclamp
  have hclamp_real : (Nat.log 2 F.card : ℝ) + 1 ≤ (clamp : ℝ) + 1 := by
    linarith
  have hFg'' : (F.card : ℝ) ≤ ((clamp : ℝ) + 1) ^ (N + 1) * (Fg.card : ℝ) := by
    calc
      (F.card : ℝ) ≤ ((Nat.log 2 F.card : ℝ) + 1) ^ (N + 1) * (Fg.card : ℝ) := hFg'
      _ ≤ ((clamp : ℝ) + 1) ^ (N + 1) * (Fg.card : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (Nat.log 2 F.card : ℝ) + 1)
            hclamp_real (N + 1))
          (by positivity : (0 : ℝ) ≤ (Fg.card : ℝ))
  exact_mod_cast hFg''

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- **Stage 1, shade-sum form.**  The pointwise per-fibre cardinality loss integrates to the
shade-sum loss, by the multiplicity-integral identity behind
`ShadedTube.sum_le_of_fiber_card_le`. -/
private theorem sum_shade_le_sum_refinedShade {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E)
    (g : Finset ι → Finset ι) (hg_sub : ∀ F, g F ⊆ F) (clamp N : ℕ)
    (hcard : ∀ x : E, (ShadedTube.shadeFiber s V x).card
      ≤ (clamp + 1) ^ (N + 1) * (g (ShadedTube.shadeFiber s V x)).card) :
    ∑ i ∈ s, volume (V i).shade
      ≤ (((clamp + 1) ^ (N + 1) : ℕ) : ENNReal)
        * ∑ i ∈ s, volume (ShadedTube.refinedShade s V g i) := by
  classical
  have hcard' : ∀ x : E, (s.filter (fun i => x ∈ (V i).shade)).card
      ≤ (clamp + 1) ^ ((N + 2) - 1) *
        (s.filter (fun i => x ∈ ShadedTube.refinedShade s V g i)).card := by
    intro x
    rw [ShadedTube.refinedShade_fiber s V g hg_sub x]
    change (ShadedTube.shadeFiber s V x).card
      ≤ (clamp + 1) ^ ((N + 2) - 1) * (g (ShadedTube.shadeFiber s V x)).card
    have hk : (N + 2) - 1 = N + 1 := by omega
    rw [hk]
    exact hcard x
  have hk : (N + 2) - 1 = N + 1 := by omega
  simpa [hk] using
    ShadedTube.sum_le_of_fiber_card_le (N + 2) clamp s
      (fun i => (V i).shade) (ShadedTube.refinedShade s V g)
      (fun i => (V i).measurableSet_shade)
      (ShadedTube.measurableSet_refinedShade s V g) hcard'

/-- The band vectors range over the clamped cube, so the stage-2 pigeonhole loses at most
`(clamp+1)^{N+1}`. -/
private theorem card_image_bandProfile_le {N : ℕ} (bnd : Finset ι → ℕ → ℕ) (clamp : ℕ)
    (t : Finset ι) :
    (t.powerset.image
        (fun F : Finset ι => fun k : Fin (N + 1) => min (Nat.log 2 (bnd F k)) clamp)).card
      ≤ (clamp + 1) ^ (N + 1) := by
  classical
  let T : Finset (Fin (N + 1) → ℕ) :=
    Fintype.piFinset (fun _ : Fin (N + 1) => Finset.range (clamp + 1))
  have hTcard : T.card = (clamp + 1) ^ (N + 1) := by
    dsimp [T]
    rw [Fintype.card_piFinset]
    simp only [Finset.card_range]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have himg : t.powerset.image
      (fun F : Finset ι => fun k : Fin (N + 1) => min (Nat.log 2 (bnd F k)) clamp) ⊆ T := by
    intro v hv
    dsimp [T]
    rw [Fintype.mem_piFinset]
    intro k
    simp only [Finset.mem_range]
    rcases Finset.mem_image.mp hv with ⟨F, _, rfl⟩
    exact Nat.lt_succ_iff.mpr (min_le_right _ _)
  exact (Finset.card_le_card himg).trans hTcard.le

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- Fullness from the shade-sum pigeonhole, since the refinement leaves the carriers (tubes)
unchanged. -/
private theorem fullness_le_of_shade_sum {δ : NNReal} {s : Finset ι} (clamp : ℕ) (N : ℕ)
    (V V' : ι → ShadedTube δ E) (htube : ∀ i, (V' i).toTube = (V i).toTube)
    (hnum : (∑ i ∈ s, volume (V i).shade)
      ≤ ((clamp + 1 : ℕ) : ENNReal) ^ (N + 1) * (∑ i ∈ s, volume (V' i).shade)) :
    ShadedBody.fullness' s (fun i => (V i).toShadedBody)
      ≤ ((clamp + 1 : ℕ) : ENNReal) ^ (N + 1) *
        ShadedBody.fullness' s (fun i => (V' i).toShadedBody) := by
  classical
  change (∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier)
      ≤ ((clamp + 1 : ℕ) : ENNReal) ^ (N + 1) *
        ((∑ i ∈ s, volume (V' i).shade) / (∑ i ∈ s, volume (V' i).carrier))
  have hden : (∑ i ∈ s, volume (V i).carrier) = ∑ i ∈ s, volume (V' i).carrier := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    calc (V i).carrier = (V i).toTube.carrier := rfl
      _ = (V' i).toTube.carrier := by rw [← htube i]
      _ = (V' i).carrier := rfl
  calc (∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier)
      ≤ (((clamp + 1 : ℕ) : ENNReal) ^ (N + 1) * (∑ i ∈ s, volume (V' i).shade))
          / (∑ i ∈ s, volume (V i).carrier) := ENNReal.div_le_div_right hnum _
    _ = ((clamp + 1 : ℕ) : ENNReal) ^ (N + 1)
          * ((∑ i ∈ s, volume (V' i).shade) / (∑ i ∈ s, volume (V i).carrier)) :=
        mul_div_assoc _ _ _
    _ = ((clamp + 1 : ℕ) : ENNReal) ^ (N + 1)
          * ((∑ i ∈ s, volume (V' i).shade) / (∑ i ∈ s, volume (V' i).carrier)) := by
        rw [hden]

omit [Nontrivial E] [BorelSpace E] in
/-- **H2, balanced refinement of the shading, against a bare cover system.**  There is a refinement
of the shading — tubes unchanged, shades shrunk — and a single band vector `Pstar` such that at
every retained point and every grid index, every node met by the retained fibre carries a number of
retained members in the dyadic band `[2^{Pstar k}, 2^{Pstar k + 1})`.  The shade-mass loss is
`(clamp+1)^{2N+2}`, one factor per grid index per pigeonhole stage; the bracket is stated on `V'`,
not on `V`.

Only the *cover's assignment* enters: neither the two branching brackets of
`Tube.UniformTubeSet` nor the cover's own tubes are used by the pigeonholing, which is why the
hypothesis is a bare `Tube.GridCoverSystem` over an *arbitrary* tube family `W`, at an arbitrary
thickness `σ`, unrelated to the tubes of `V`.  That matters for consumers that build their own
nested cover: the angular hierarchy of blueprint `lem:ml2murho` groups the tubes of `V` by
*direction*, so its nodes are direction tubes through the origin
(`Kakeya.AngularCover.dirTube`) and cannot contain the tubes of `V` at all — no
`GridCoverSystem s (fun i => (V i).toTube) N` records that hierarchy.  Such a consumer also
cannot supply the tube-level branching brackets without first passing to a subfamily, which
would destroy the shade mass this statement preserves.
`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet` is the specialization at
`W = fun i => (V i).toTube` and `𝒢 = 𝒰.cover`. -/
theorem exists_balanced_shadeRefinement_of_cover {δ σ : NNReal} {s : Finset ι}
    {V : ι → ShadedTube δ E} {W : ι → Tube σ E} {N : ℕ}
    (𝒢 : GridCoverSystem s W N) (_hN : 0 < N)
    (clamp : ℕ) (hclamp : ∀ t : Finset ι, t ⊆ s → Nat.log 2 t.card ≤ clamp) :
    ∃ (Pstar : ℕ → ℕ) (V' : ι → ShadedTube δ E),
      (∀ i, (V' i).toTube = (V i).toTube) ∧
      (∀ i, (V' i).shade ⊆ (V i).shade) ∧
      (∀ x, x ∈ (⋃ i ∈ s, (V' i).shade) → ∀ k ≤ N, ∀ i ∈ s, x ∈ (V' i).shade →
        2 ^ Pstar k ≤ (shadeClass s V' (𝒢.assign k) (𝒢.assign k i) x).card ∧
          (shadeClass s V' (𝒢.assign k) (𝒢.assign k i) x).card < 4 * 2 ^ Pstar k) ∧
      ∑ i ∈ s, volume (V i).shade
        ≤ ((clamp + 1 : ℕ) : ENNReal) ^ (2 * N + 2) * ∑ i ∈ s, volume (V' i).shade := by
  classical
  obtain ⟨g, bnd, hg_sub, hg_ne, hg_card, hg_band⟩ :=
    exists_fibre_balancer (T := W) (N := N) 𝒢
  set bN : Finset ι → (Fin (N + 1) → ℕ) :=
    fun F k => min (Nat.log 2 (bnd F k)) clamp with hbN
  obtain ⟨Pfin, hPmem, hPig⟩ :=
    ShadedTube.exists_dominant_profile_sum (E := E) (δ := δ) s V bN
      (ShadedTube.refinedShade s V g)
      (ShadedTube.measurableSet_refinedShade s V g)
  set Xstar : Set E := {x : E | bN (ShadedTube.shadeFiber s V x) = Pfin} with hXstar
  have hXstar_meas : MeasurableSet Xstar :=
    ShadedTube.measurableSet_profile_eq s V bN Pfin
  set V' : ι → ShadedTube δ E := fun i =>
    { V i with
      shade := ShadedTube.shadeRestrict s V g Xstar i
      measurableSet_shade :=
        ShadedTube.measurableSet_shadeRestrict s V g hXstar_meas i
      shade_subset :=
        Set.inter_subset_left.trans (Set.inter_subset_left.trans (V i).shade_subset) } with hV'
  have hVto : ∀ i, (V' i).toTube = (V i).toTube := fun i => rfl
  have hVshade : ∀ i, (V' i).shade = ShadedTube.shadeRestrict s V g Xstar i :=
    fun i => rfl
  have hVsub : ∀ i, (V' i).shade ⊆ (V i).shade := by
    intro i
    rw [hVshade i]
    exact Set.inter_subset_left.trans Set.inter_subset_left
  refine ⟨fun k => if h : k < N + 1 then Pfin ⟨k, h⟩ else 0, V', hVto, hVsub, ?_, ?_⟩
  · intro x _hx k hk i _hi hxi
    have hxi' : x ∈ ShadedTube.refinedShade s V g i ∩ Xstar := by
      rw [hVshade i] at hxi; exact hxi
    have hxX : x ∈ Xstar := hxi'.2
    have hxr : x ∈ (V i).shade ∩ {y : E | i ∈ g (ShadedTube.shadeFiber s V y)} := hxi'.1
    have hiG : i ∈ g (ShadedTube.shadeFiber s V x) := hxr.2
    have hFs : ShadedTube.shadeFiber s V x ⊆ s := Finset.filter_subset _ _
    have hcls : shadeClass s V' (𝒢.assign k) (𝒢.assign k i) x
        = coverClass (g (ShadedTube.shadeFiber s V x)) (𝒢.assign k)
            (𝒢.assign k i) :=
      shadeClass_refined_eq g hg_sub Xstar hVshade (𝒢.assign k) (𝒢.assign k i) hxX
    have hband := hg_band (ShadedTube.shadeFiber s V x) hFs k hk i hiG
    have hsub : coverClass (g (ShadedTube.shadeFiber s V x)) (𝒢.assign k)
        (𝒢.assign k i) ⊆ s := by
      refine Finset.Subset.trans ?_ ((hg_sub _).trans hFs)
      simp [coverClass]
    have hclampm : Nat.log 2 (coverClass (g (ShadedTube.shadeFiber s V x))
        (𝒢.assign k) (𝒢.assign k i)).card ≤ clamp := by
      exact hclamp _ hsub
    have hk' : k < N + 1 := Nat.lt_succ_of_le hk
    have hxXeq : bN (ShadedTube.shadeFiber s V x) = Pfin := hxX
    have hPk : (if h : k < N + 1 then Pfin ⟨k, h⟩ else 0)
        = min (Nat.log 2 (bnd (ShadedTube.shadeFiber s V x) k)) clamp := by
      rw [dif_pos hk', ← hxXeq, hbN]
    rw [hcls]
    simp only [hPk]
    exact dyadic_band_of_band hband.1 hband.2 hclampm rfl
  · have hcard_pt : ∀ x : E, (ShadedTube.shadeFiber s V x).card
        ≤ (clamp + 1) ^ (N + 1) * (g (ShadedTube.shadeFiber s V x)).card := by
      intro x
      have hFs : ShadedTube.shadeFiber s V x ⊆ s := Finset.filter_subset _ _
      have hlog : Nat.log 2 (ShadedTube.shadeFiber s V x).card ≤ clamp := by
        exact hclamp _ hFs
      exact fibre_card_le_of_balancer _ _ (hg_card _ hFs) hlog
    have hstage1 : ∑ i ∈ s, volume (V i).shade
        ≤ (((clamp + 1) ^ (N + 1) : ℕ) : ENNReal)
          * ∑ i ∈ s, volume (ShadedTube.refinedShade s V g i) :=
      sum_shade_le_sum_refinedShade s V g hg_sub clamp N hcard_pt
    have hVsh : ∀ i, ShadedTube.refinedShade s V g i ∩ Xstar = (V' i).shade := by
      intro i; rw [hVshade i]; rfl
    have himg : ((s.powerset.image bN).card : ENNReal)
        ≤ (((clamp + 1) ^ (N + 1) : ℕ) : ENNReal) := by
      have h := card_image_bandProfile_le (N := N) bnd clamp s
      rw [hbN]
      exact_mod_cast h
    have hstage2 : ∑ i ∈ s, volume (ShadedTube.refinedShade s V g i)
        ≤ (((clamp + 1) ^ (N + 1) : ℕ) : ENNReal) * ∑ i ∈ s, volume (V' i).shade := by
      calc ∑ i ∈ s, volume (ShadedTube.refinedShade s V g i)
          ≤ (s.powerset.image bN).card
              • ∑ i ∈ s, volume (ShadedTube.refinedShade s V g i ∩ Xstar) := hPig
        _ = ((s.powerset.image bN).card : ENNReal) * ∑ i ∈ s, volume (V' i).shade := by
            rw [nsmul_eq_mul]; simp_rw [hVsh]
        _ ≤ (((clamp + 1) ^ (N + 1) : ℕ) : ENNReal) * ∑ i ∈ s, volume (V' i).shade :=
            mul_le_mul_left himg _
    have hexp : (N + 1) + (N + 1) = 2 * N + 2 := by omega
    have hnum : ∑ i ∈ s, volume (V i).shade
        ≤ ((clamp + 1 : ℕ) : ENNReal) ^ (2 * N + 2) * ∑ i ∈ s, volume (V' i).shade := by
      calc ∑ i ∈ s, volume (V i).shade
          ≤ (((clamp + 1) ^ (N + 1) : ℕ) : ENNReal)
              * ∑ i ∈ s, volume (ShadedTube.refinedShade s V g i) := hstage1
        _ ≤ (((clamp + 1) ^ (N + 1) : ℕ) : ENNReal)
              * ((((clamp + 1) ^ (N + 1) : ℕ) : ENNReal) * ∑ i ∈ s, volume (V' i).shade) :=
            mul_le_mul_right hstage2 _
        _ = ((clamp + 1 : ℕ) : ENNReal) ^ (2 * N + 2) * ∑ i ∈ s, volume (V' i).shade := by
            push_cast
            rw [← mul_assoc, ← pow_add, hexp]
    exact hnum

/-! ### The shaded refinement lemma -/

omit [Nontrivial E] [BorelSpace E] in
/-- **Shaded uniformization on a fixed index set.**  Given a tube-level hierarchy `𝒰` already built
on `s`, the shading alone is refined — tubes unchanged, shades shrunk, **no subfamily taken** —
until GWZ Definition 2.2 holds against that same hierarchy.  The returned bundle carries the *given*
hierarchy and only weakens the constant, from `C` to `max C 4`; the fullness loss is
`(clamp+1)^{2N+2}`. -/
theorem exists_shadedUniformTubeSet_of_uniformTubeSet {δ : NNReal} {s : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : UniformTubeSet s (fun i => (V i).toTube) N C) (hN : 0 < N)
    (clamp : ℕ) (hclamp : ∀ t : Finset ι, t ⊆ s → Nat.log 2 t.card ≤ clamp) :
    ∃ V' : ι → ShadedTube δ E,
      (∀ i, (V' i).toTube = (V i).toTube) ∧
      (∀ i, (V' i).shade ⊆ (V i).shade) ∧
      ShadedBody.fullness' s (fun i => (V i).toShadedBody)
          ≤ ((clamp + 1 : ℕ) : ENNReal) ^ (2 * N + 2)
            * ShadedBody.fullness' s (fun i => (V' i).toShadedBody) ∧
      ∃ 𝒱 : ShadedUniformTubeSet s V' N (max C 4),
        𝒱.tubeUniform.cover.indexSet = 𝒰.cover.indexSet ∧
        𝒱.tubeUniform.cover.assign = 𝒰.cover.assign ∧
        𝒱.tubeUniform.cover.tube = 𝒰.cover.tube ∧
        𝒱.tubeUniform.branchingN = 𝒰.branchingN := by
  classical
  obtain ⟨Pstar₀, V', hVto, hVshade, hband₀, hsum₀⟩ :=
    exists_balanced_shadeRefinement_of_cover (V := V) (𝒢 := 𝒰.cover) hN clamp hclamp
  have hfull₀ : ShadedBody.fullness' s (fun i => (V i).toShadedBody)
      ≤ ((clamp + 1 : ℕ) : ENNReal) ^ (2 * N + 2) *
        ShadedBody.fullness' s (fun i => (V' i).toShadedBody) :=
    fullness_le_of_shade_sum clamp (2 * N + 1) V V' hVto hsum₀
  let 𝒢₁ : GridCoverSystem s (fun i => (V' i).toTube) N :=
    { indexSet := 𝒰.cover.indexSet
      assign := 𝒰.cover.assign
      tube := 𝒰.cover.tube
      assign_mem := 𝒰.cover.assign_mem
      le_tube_assign := by
        intro k hk i hi
        simpa [hVto i] using 𝒰.cover.le_tube_assign k hk i hi
      nested := 𝒰.cover.nested
      tube_nested := 𝒰.cover.tube_nested }
  let 𝒰₁ : UniformTubeSet s (fun i => (V' i).toTube) N C :=
    { cover := 𝒢₁
      branchingN := 𝒰.branchingN
      tube_injOn := 𝒰.tube_injOn
      card_class_le := 𝒰.card_class_le
      le_card_class := 𝒰.le_card_class
      boundedOverlap := by
        intro k hk W
        simpa [hVto] using 𝒰.boundedOverlap k hk W }
  let 𝒰₂ : UniformTubeSet s (fun i => (V' i).toTube) N (max C 4) :=
    𝒰₁.mono (le_max_left C 4)
  have h4_le_C : (4 : NNReal) ≤ max C 4 := le_max_right C 4
  have h1_le_C : (1 : NNReal) ≤ max C 4 := le_trans (by norm_num) h4_le_C
  refine ⟨V', hVto, hVshade, hfull₀, ?_⟩
  refine ⟨{
      tubeUniform := 𝒰₂
      branchingN := fun k => (2 : NNReal) ^ Pstar₀ k
      localN := fun x k => (2 : NNReal) ^ Pstar₀ k
      card_shadeClass_le := by
        intro x hx k hk i hi hxi
        have hband := hband₀ x hx k hk i hi hxi
        have hle : (shadeClass s V' (𝒰₂.cover.assign k) (𝒰₂.cover.assign k i) x).card
            ≤ 4 * 2 ^ Pstar₀ k := Nat.le_of_lt hband.2
        have hleNN :
            ((shadeClass s V' (𝒰₂.cover.assign k) (𝒰₂.cover.assign k i) x).card : NNReal)
              ≤ (4 : NNReal) * (2 ^ Pstar₀ k : NNReal) := by
          exact_mod_cast hle
        calc
          ((shadeClass s V' (𝒰₂.cover.assign k) (𝒰₂.cover.assign k i) x).card : NNReal)
              ≤ (4 : NNReal) * (2 ^ Pstar₀ k : NNReal) := hleNN
          _ ≤ (max C 4) * (2 ^ Pstar₀ k : NNReal) := mul_le_mul_left h4_le_C _
      le_card_shadeClass := by
        intro x hx k hk i hi hxi
        have hband := hband₀ x hx k hk i hi hxi
        have hnn : ((2 ^ Pstar₀ k : ℕ) : NNReal)
            ≤ (shadeClass s V' (𝒰₂.cover.assign k) (𝒰₂.cover.assign k i) x).card := by
          exact_mod_cast hband.1
        calc
          (2 : NNReal) ^ Pstar₀ k
              ≤ (shadeClass s V' (𝒰₂.cover.assign k) (𝒰₂.cover.assign k i) x).card := by
            simpa using hnn
          _ ≤ (max C 4) * (shadeClass s V' (𝒰₂.cover.assign k) (𝒰₂.cover.assign k i) x).card :=
            le_mul_of_one_le_left (by positivity) h1_le_C
      branchingN_le := by
        intro x hx k hk
        exact le_mul_of_one_le_left (by positivity) h1_le_C
      le_branchingN := by
        intro x hx k hk
        exact le_mul_of_one_le_left (by positivity) h1_le_C
    }, rfl, rfl, rfl, rfl⟩

/-- The uniformity constant produced by shaded multiscale uniformization: it depends only on the
ambient dimension. -/
def ssfUniformConst (n : ℕ) : NNReal := max (uniformConst n) 4

theorem one_le_ssfUniformConst (n : ℕ) : 1 ≤ ssfUniformConst n := by
  unfold ssfUniformConst
  exact le_trans (by norm_num : (1 : NNReal) ≤ (4 : NNReal)) (le_max_right _ _)

theorem uniformConst_le_ssfUniformConst (n : ℕ) : uniformConst n ≤ ssfUniformConst n := by
  exact le_max_left _ _

/-- **Shaded uniformization** (GWZ §2: every pair `(𝕋, Y)` has a `≈1`-refinement that is uniform),
stated against `ShadedTube.ShadedUniformTubeSet`.  The refinement keeps the tubes and may only
shrink the shadings and pass to a subset; both losses, cardinality and fullness, are
`(A (log₂ #s + 1))^{O(N)}`, with `A` and the uniformity constant fixed before `N` and `δ`. -/
theorem exists_shadedUniformTubeSet_subfamily :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ {ι : Type u} {δ : NNReal} (N : ℕ), 0 < δ → 0 < N →
      δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s : Finset ι) (V : ι → ShadedTube δ E),
      (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∃ s' ⊆ s, ∃ V' : ι → ShadedTube δ E,
        (∀ i, (V' i).toTube = (V i).toTube) ∧
        (∀ i, (V' i).shade ⊆ (V i).shade) ∧
        (s.card : ℝ)
            ≤ (A * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1)) ^ N * (s'.card : ℝ) ∧
        ShadedBody.fullness' s' (fun i => (V i).toShadedBody)
            ≤ ENNReal.ofReal
                ((A * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1)) ^ (2 * N + 2))
              * ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) ∧
        Nonempty (ShadedUniformTubeSet s' V' N (ssfUniformConst (Module.finrank ℝ E))) := by
  classical
  obtain ⟨A₀, hA₀, hsubfam⟩ := exists_uniformTubeSet_subfamily (E := E)
  let Cu₀ : NNReal := uniformConst (Module.finrank ℝ E)
  let Cn : ℕ := 1
  let A₁ : ℝ := (Nat.log 2 (Cn ^ 2) : ℝ) + 2
  have hA₁ : 1 ≤ A₁ := by
    dsimp [A₁]
    have hn0 : 0 ≤ (Nat.log 2 (Cn ^ 2) : ℝ) := by exact_mod_cast Nat.zero_le _
    linarith
  let A : ℝ := max A₀ A₁
  let Cu : NNReal := max Cu₀ 4
  refine ⟨A, ?_hA_ge1, ?_main⟩
  · dsimp [A]
    exact le_trans hA₀ (le_max_left _ _)
  · intro ι δ N hδ hN hδ0 s V hs_B1
    have hs_B1_tube : ∀ i ∈ s, ((V i).toTube).carrier ⊆ Metric.closedBall (0 : E) 1 := by
      intro i hi
      simpa using hs_B1 i hi
    obtain ⟨s', hs'_sub, hs'_card, hu⟩ :=
      hsubfam (ι := ι) (δ := δ) (N := N) hδ hN hδ0 s (fun i => (V i).toTube) hs_B1_tube
    let B : ℝ := (⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1
    have hfloornonneg : (0 : ℝ) ≤ (⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) := by
      exact_mod_cast (Nat.zero_le (⌊Real.logb 2 (s.card : ℝ)⌋₊))
    have hB_ge0 : 0 ≤ B := by dsimp [B]; linarith
    have hB_ge1 : (1 : ℝ) ≤ B := by dsimp [B]; linarith
    have hA₀_le_A : A₀ ≤ A := by dsimp [A]; exact le_max_left _ _
    have hA₁_le_A : A₁ ≤ A := by dsimp [A]; exact le_max_right _ _
    have hCu₀_le_Cu : Cu₀ ≤ Cu := by dsimp [Cu]; exact le_max_left _ _
    have h4_le_Cu : (4 : NNReal) ≤ Cu := by dsimp [Cu]; exact le_max_right _ _
    have h1_le_Cu : (1 : NNReal) ≤ Cu := by
      exact le_trans (by norm_num : (1 : NNReal) ≤ 4) h4_le_Cu
    have hCn_ge1 : (1 : ℕ) ≤ Cn := by simp [Cn]
    let clamp : ℕ := Nat.log 2 (Cn ^ 2 * s.card)
    have hClamped : ∀ (t : Finset ι), t ⊆ s → Nat.log 2 t.card ≤ clamp := by
      intro t hts
      dsimp [clamp]
      have hsub : t.card ≤ s.card := Finset.card_le_card hts
      have hsc : s.card ≤ Cn ^ 2 * s.card := by
        dsimp [Cn]
        omega
      have hcard : t.card ≤ Cn ^ 2 * s.card := le_trans hsub hsc
      exact Nat.log_mono_right (by simpa using hcard)
    obtain ⟨Pstar₀, V', hVto, hVshade, hband₀, hsum₀⟩ :=
      exists_balanced_shadeRefinement_of_cover (V := V) (𝒢 := (hu.some).cover) hN clamp
        (fun t ht => hClamped t (ht.trans hs'_sub))
    have hfull₀ : ShadedBody.fullness' s' (fun i => (V i).toShadedBody)
        ≤ ((clamp + 1 : ℕ) : ENNReal) ^ (2 * N + 2) *
          ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) :=
      fullness_le_of_shade_sum clamp (2 * N + 1) V V' hVto hsum₀
    have hVto' : (fun i => (V' i).toTube) = (fun i => (V i).toTube) := by
      funext i; exact hVto i
    let 𝒢₁ : GridCoverSystem s' (fun i => (V' i).toTube) N :=
      { indexSet := (hu.some).cover.indexSet
        assign := (hu.some).cover.assign
        tube := (hu.some).cover.tube
        assign_mem := (hu.some).cover.assign_mem
        le_tube_assign := by
          intro k hk i hi
          simpa [hVto i] using (hu.some).cover.le_tube_assign k hk i hi
        nested := (hu.some).cover.nested
        tube_nested := (hu.some).cover.tube_nested }
    let 𝒰₁ : UniformTubeSet s' (fun i => (V' i).toTube) N Cu₀ :=
      { cover := 𝒢₁
        branchingN := (hu.some).branchingN
        tube_injOn := (hu.some).tube_injOn
        card_class_le := (hu.some).card_class_le
        le_card_class := (hu.some).le_card_class
        boundedOverlap := by
          intro k hk V
          simpa [hVto] using (hu.some).boundedOverlap k hk V }
    let 𝒰 : UniformTubeSet s' (fun i => (V' i).toTube) N Cu := 𝒰₁.mono hCu₀_le_Cu
    have hclamp_poly : ∀ (t : Finset ι),
        ((Nat.log 2 (Cn ^ 2 * t.card) + 1 : ℕ) : ℝ)
          ≤ A₁ * ((⌊Real.logb 2 (t.card : ℝ)⌋₊ : ℝ) + 1) := by
      intro t
      dsimp [Cn, A₁]
      rw [show ⌊Real.logb 2 (t.card : ℝ)⌋₊ = Nat.log 2 t.card by
        exact_mod_cast (Real.natFloor_logb_natCast 2 t.card)]
      norm_num
      have hd : 0 ≤ (Nat.log 2 t.card : ℝ) := by exact_mod_cast Nat.zero_le _
      nlinarith
    have hclampB : (clamp + 1 : ℕ) ≤ A * B := by
      have hstep : (Nat.log 2 (Cn ^ 2 * s.card) + 1 : ℕ) ≤ A₁ * B := by
        dsimp [B]
        simpa [clamp] using hclamp_poly s
      have hA₁B : A₁ * B ≤ A * B := by
        exact mul_le_mul_of_nonneg_right hA₁_le_A hB_ge0
      have hcast : (clamp + 1 : ℕ) = (Nat.log 2 (Cn ^ 2 * s.card) + 1 : ℕ) := by
        rfl
      rw [hcast]
      exact le_trans hstep hA₁B
    have hclampB_real : ((clamp + 1 : ℕ) : ℝ) ≤ A * B := by
      exact_mod_cast hclampB
    refine ⟨s', hs'_sub, V', hVto, hVshade, ?_hcard, ?_hfull, ?_hstruct⟩
    · have hA₀B_le_AB : A₀ * B ≤ A * B :=
        mul_le_mul_of_nonneg_right hA₀_le_A hB_ge0
      have hA₀B_nonneg : (0 : ℝ) ≤ A₀ * B :=
        mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hA₀) hB_ge0
      have hpow : (A₀ * B) ^ N ≤ (A * B) ^ N :=
        pow_le_pow_left₀ hA₀B_nonneg hA₀B_le_AB N
      have hs'nonneg : (0 : ℝ) ≤ (s'.card : ℝ) := by exact_mod_cast Nat.zero_le _
      calc
        (s.card : ℝ) ≤ (A₀ * B) ^ N * (s'.card : ℝ) := by simpa [B] using hs'_card
        _ ≤ (A * B) ^ N * (s'.card : ℝ) :=
          mul_le_mul_of_nonneg_right hpow hs'nonneg
    · have hclampB_real' : (clamp : ℝ) + 1 ≤ A * B := by simpa using hclampB_real
      have hpow_cAB : ((clamp : ℝ) + 1) ^ (2 * N + 2) ≤ (A * B) ^ (2 * N + 2) :=
        pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (clamp : ℝ) + 1) hclampB_real' (2 * N + 2)
      have hcoef :
          ((clamp + 1 : ℕ) : ENNReal) ^ (2 * N + 2) ≤ ENNReal.ofReal ((A * B) ^ (2 * N + 2)) := by
        have hpos : (0 : ℝ) ≤ (clamp : ℝ) + 1 := by positivity
        rw [← ENNReal.ofReal_natCast (clamp + 1)]
        rw [show ((clamp + 1 : ℕ) : ℝ) = (clamp : ℝ) + 1 by norm_num]
        rw [← ENNReal.ofReal_pow hpos (2 * N + 2)]
        exact ENNReal.ofReal_le_ofReal hpow_cAB
      calc
        ShadedBody.fullness' s' (fun i => (V i).toShadedBody)
            ≤ ((clamp + 1 : ℕ) : ENNReal) ^ (2 * N + 2) *
                ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) := hfull₀
        _ ≤ ENNReal.ofReal ((A * B) ^ (2 * N + 2)) *
                ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) :=
              mul_le_mul_left hcoef _
    · refine ⟨{
              tubeUniform := 𝒰
              branchingN := fun k => (2 : NNReal) ^ Pstar₀ k
              localN := fun x k => (2 : NNReal) ^ Pstar₀ k
              card_shadeClass_le := by
                intro x hx k hk i hi hxi
                have hband := hband₀ x hx k hk i hi hxi
                have hle :
                    (shadeClass s' V' (𝒰.cover.assign k) (𝒰.cover.assign k i) x).card
                      ≤ 4 * 2 ^ Pstar₀ k := Nat.le_of_lt hband.2
                have hleNN :
                    ((shadeClass s' V' (𝒰.cover.assign k) (𝒰.cover.assign k i) x).card : NNReal)
                      ≤ (4 : NNReal) * (2 ^ Pstar₀ k : NNReal) := by
                  exact_mod_cast hle
                calc
                  ((shadeClass s' V' (𝒰.cover.assign k) (𝒰.cover.assign k i) x).card : NNReal)
                      ≤ (4 : NNReal) * (2 ^ Pstar₀ k : NNReal) := hleNN
                  _ ≤ Cu * (2 ^ Pstar₀ k : NNReal) := mul_le_mul_left h4_le_Cu _
              le_card_shadeClass := by
                intro x hx k hk i hi hxi
                have hband := hband₀ x hx k hk i hi hxi
                have hnn : ((2 ^ Pstar₀ k : ℕ) : NNReal)
                    ≤ (shadeClass s' V' (𝒰.cover.assign k) (𝒰.cover.assign k i) x).card := by
                  exact_mod_cast hband.1
                calc
                  (2 : NNReal) ^ Pstar₀ k
                      ≤ (shadeClass s' V' (𝒰.cover.assign k) (𝒰.cover.assign k i) x).card := by
                    simpa using hnn
                  _ ≤ Cu * (shadeClass s' V' (𝒰.cover.assign k) (𝒰.cover.assign k i) x).card :=
                    le_mul_of_one_le_left (by positivity) h1_le_Cu
              branchingN_le := by
                intro x hx k hk
                exact le_mul_of_one_le_left (by positivity) h1_le_Cu
              le_branchingN := by
                intro x hx k hk
                exact le_mul_of_one_le_left (by positivity) h1_le_Cu
            }⟩

/-- **The faithful form: GWZ Definition 2.2 at its own grid length.**
`ShadedTube.exists_shadedUniformTubeSet_subfamily` instantiated at
`N = Tube.ssfGridLen δ = ⌈log log 1/δ⌉`, with both losses absorbed into a prescribed `δ^{-α}`.  The
cardinality bound `#s ≤ δ^{-K₀}` turns the polylogarithm in `#s` into one in `1/δ`; the two losses
are budgeted separately, `α` for the cardinality and `α'` for the fullness. -/
theorem exists_shadedUniformTubeSet_subfamily_ssf (K₀ : ℕ) (α α' : ℝ) (hα : 0 < α) (hα' : 0 < α') :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (s : Finset ι) (V : ι → ShadedTube δ E),
      (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (s.card : ℝ) ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) →
      ∃ s' ⊆ s, ∃ V' : ι → ShadedTube δ E,
        (∀ i, (V' i).toTube = (V i).toTube) ∧
        (∀ i, (V' i).shade ⊆ (V i).shade) ∧
        (s.card : ℝ) ≤ (δ : ℝ) ^ (-α) * (s'.card : ℝ) ∧
        ShadedBody.fullness' s' (fun i => (V i).toShadedBody)
            ≤ ENNReal.ofReal ((δ : ℝ) ^ (-α'))
              * ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) ∧
        Nonempty (ShadedUniformTubeSet s' V' (ssfGridLen δ)
            (ssfUniformConst (Module.finrank ℝ E))) := by
  classical
  obtain ⟨A, hA, hsubfam⟩ := exists_shadedUniformTubeSet_subfamily (E := E)
  obtain ⟨δ₁, hδ₁pos, hδ₁le1, hthr₁⟩ :=
    exists_threshold_polylog_pow_ssfGridLen_le A hA K₀ 1 α hα
  obtain ⟨δ₂, hδ₂pos, hδ₂le1, hthr₂⟩ :=
    exists_threshold_polylog_pow_ssfGridLen_le A hA K₀ 2 α' hα'
  let δ₀ : NNReal := min (min δ₁ δ₂) 1
  refine ⟨δ₀, ?_, ?_, ?_⟩
  · dsimp [δ₀]
    exact lt_min (lt_min hδ₁pos hδ₂pos) (by norm_num)
  · dsimp [δ₀]
    exact min_le_right _ _
  · intro ι δ hδ hδδ₀ s V hs_B1 hscard
    have hδδ₁ : δ ≤ δ₁ :=
      le_trans hδδ₀ (le_trans (min_le_left _ _) (min_le_left _ _))
    have hδδ₂ : δ ≤ δ₂ :=
      le_trans hδδ₀ (le_trans (min_le_left _ _) (min_le_right _ _))
    have hsAbs₁ := hthr₁ hδ hδδ₁
    have hsAbs₂ := hthr₂ hδ hδδ₂
    have hNpos : 0 < ssfGridLen δ := hsAbs₁.1
    have hN16 : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ)) := hsAbs₁.2.1
    obtain ⟨s', hs'_sub, V', hVto, hVshade, hcard, hfull, hstruct⟩ :=
      hsubfam (ι := ι) (δ := δ) (ssfGridLen δ) hδ hNpos hN16 s V hs_B1
    set base : ℝ := A * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1) with hbase_def
    have hc_nonneg : (0 : ℝ) ≤ (s.card : ℝ) := by positivity
    have habs₁ := hsAbs₁.2.2 (s.card : ℝ) hc_nonneg hscard
    have habs₂ := hsAbs₂.2.2 (s.card : ℝ) hc_nonneg hscard
    have hbase1 : (1 : ℝ) ≤ base := by
      have hfac : (1 : ℝ) ≤ ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1) := by
        have hflr : (0 : ℝ) ≤ (⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) := by
          exact_mod_cast (Nat.zero_le (⌊Real.logb 2 (s.card : ℝ)⌋₊))
        linarith
      rw [hbase_def]
      simpa using mul_le_mul hA hfac (by norm_num) (by linarith [hA])
    have hpow_card : base ^ ssfGridLen δ ≤ base ^ (1 * ssfGridLen δ + 1) := by
      apply pow_le_pow_right₀ hbase1
      omega
    refine ⟨s', hs'_sub, V', hVto, hVshade, ?_, ?_, hstruct⟩
    · calc
        (s.card : ℝ) ≤ base ^ ssfGridLen δ * (s'.card : ℝ) := by
          simpa [hbase_def] using hcard
        _ ≤ base ^ (1 * ssfGridLen δ + 1) * (s'.card : ℝ) := by
          exact mul_le_mul_of_nonneg_right hpow_card (by positivity : 0 ≤ (s'.card : ℝ))
        _ ≤ (δ : ℝ) ^ (-α) * (s'.card : ℝ) := by
          exact mul_le_mul_of_nonneg_right habs₁ (by positivity : 0 ≤ (s'.card : ℝ))
    · have hcoef : ENNReal.ofReal (base ^ (2 * ssfGridLen δ + 2)) ≤
          ENNReal.ofReal ((δ : ℝ) ^ (-α')) := by
        exact ENNReal.ofReal_le_ofReal habs₂
      calc
        ShadedBody.fullness' s' (fun i => (V i).toShadedBody)
            ≤ ENNReal.ofReal (base ^ (2 * ssfGridLen δ + 2)) *
                ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) := by
              simpa [hbase_def] using hfull
        _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-α')) *
                ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) :=
              mul_le_mul_left hcoef _

end ShadedTube
open Tube
