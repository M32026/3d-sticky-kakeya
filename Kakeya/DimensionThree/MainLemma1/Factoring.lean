/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Asymptotics
public import Kakeya.Factoring.FlatPrisms
public import Kakeya.Factoring.RhoTubesUndilated
public import Kakeya.Frostman
public import Kakeya.Tube.Dilate
public import Kakeya.Tube.IntersectionVolume
public import Kakeya.Multiplicity
public import Kakeya.RelativePlank

/-!
# Main Lemma 1: named parent families and the two-scale factoring chain

This file formalizes the "general infrastructure" part of Case (ii) of GWZ Main Lemma 1:
the vocabulary of *named parent families* (`GWZAdapted/section8_parents.tex`), the
pigeonholing that replaces GWZ's "abusing notation, we may suppose that all the families in
sight are uniform" (`GWZAdapted/section8_uniformize.tex`), and the composition of two
applications of GWZ Lemma 5.11 that produces the triple-product bound
(`GWZAdapted/section8_factoring.tex`).

## The one-scale loss constant, and why it carries two binders

`ShadedBody.shadingMultiplicityEstimateForRhoTubes`, which
`Kakeya.ml1Boot.factorOneScale.C` used to be read off, was refuted and deleted; the surviving
estimate is `ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam` in
`Kakeya/Factoring/RhoTubesUndilated.lean`, whose loss constant depends on the ambient dimension,
on the inner cardinality and on the inner tube scale.

`Kakeya.ml1Boot.factorOneScale.C` is that constant, `(N, σ) ↦ …`, and
`Kakeya.ml1Boot.exists_factorOneScale` is stated and proved at it.  Every statement downstream
carries the same two binders, read at the data actually in scope: the fields of
`Kakeya.ml1Boot.IsFactorOneScale` and `Kakeya.ml1Boot.IsUniformFactorCore` at `#s` and the
inner tube scale, and the fields of `Kakeya.ml1Boot.IsFactorTwoScales` through
`Kakeya.ml1Boot.factorTwoScales.C`, which is the *product* of the two applications' constants
and not the square of one of them — the two applications are made at different cardinalities
and different scales, and no monotonicity of the loss constant is available to compare them.

The lemmas that merely *transport* the constant — `Kakeya.ml1Boot.multiplicity_le_of_middle`,
and the threshold and collapse lemmas of `Rescaling/` — carry it as a free parameter instead,
which is strictly more general and is what lets a caller supply the instantiated value.

The dilate chain is deliberately **not** stated at this constant; see
`Kakeya.ml1Boot.factorOneScaleUniformDilate.C`.

Throughout, `δ` is an **auxiliary small parameter** and `σ`, `ρ`, `τ`, `θ` are **tube
scales**, with `δ ≤ σ ≤ ρ ≤ 1`.  Every "for all sufficiently small" clause refers to `δ`
and to `δ` only, and every subpolynomial loss is a power of `δ` and not of a tube scale:
the tube scales occurring in the application are `δ / τ`, `τ / θ` and `θ`, none of which is
small.

## Blueprint correspondence

Each of the three main lemmas states its conclusion as a `Prop`-valued structure whose
fields are the numbered items of the corresponding blueprint lemma.

* `Kakeya.ml1Boot.IsParentFamily` ↔ `def:ml1bootParentFamily`
* `Kakeya.ml1Boot.IsUniformRefinement` ↔ `lem:ml1bootUniformizePair`, items (i)–(vii) and (ix)
* `Kakeya.ml1Boot.IsFactorOneScale` ↔ `lem:ml1bootFactorOneScaleUniform`, items (a)–(g)
* `Kakeya.ml1Boot.IsFactorTwoScales` ↔ `lem:ml1bootFactorTwoScales`, items (a)–(h)

A blueprint item that is a conjunction of several inequalities becomes several fields, one
per inequality, so that consumers name what they use instead of projecting into a tuple.

## Divergence from the informal statement

*Items (viii) and (ix) of `lem:ml1bootUniformizePair`.*  Item (viii)
`item:uniformizeFibreUnif` is the *containment*-fibre clause: it speaks about the fibres of
the parent families internal to the uniformity data.  Those families are exposed by
`ShadedTube.ShadedUniformTubeSet` through its hierarchy `tubeUniform.cover`, so phrasing it
as a field of the conclusion would mean naming that data; it is therefore not a field of
`Kakeya.ml1Boot.IsUniformRefinement`.

What the assembly of Case (ii) actually consumes is item (ix)
`item:uniformizeGivenFibreUnif`, uniformity of the *parent-map* fibres of the *given* parent
families — `Kakeya.ml1Boot.multiplicity_le_middle` is applied to `fibre t'τ pθ l₀` — and that
is what the field `Kakeya.ml1Boot.IsUniformRefinement.fibreUnif` records, propagated to
`Kakeya.ml1Boot.IsFactorOneScale.fibreUnif` and
`Kakeya.ml1Boot.IsFactorTwoScales.midFibreUnif`.

Every fibre-uniformity field on the live chain — those two,
`Kakeya.ml1Boot.IsUniformFactorCore.fibreUnif` and
`Kakeya.ml1Boot.IsUniformFactorCoreDilate.fibreUnif` — is stated at the **one-sided**
`Kakeya.IsFlatPrismUniform`, GWZ Definition 2.2 minus `le_card_shadeClass` and `branchingN_le`.
Nothing anywhere reads either dropped clause, and read one-sidedly the fibre clause is a
consequence of the global one at the same constant
(`Kakeya.ml1Boot.nonempty_isFlatPrismUniform_fibre_of_shadedUniformTubeSet`).  The two-sided
reading was a typing commitment inherited from
`Kakeya.ml1Boot.multiplicity_le_middle`, and it has been removed; the docstring of
`Kakeya.ml1Boot.exists_uniformFactorCore` records what that took and which declarations moved.
`Kakeya.ml1Boot.IsUniformRefinement.fibreUnif` is the one that remains two-sided, and it is inert:
its producer `Kakeya.ml1Boot.exists_uniformRefinement` is *false*, refuted in this file by
`Kakeya.ml1Boot.not_exists_uniformRefinement`, so nothing consumes that structure.  Its uniformity
constant is
`Kakeya.ml1Boot.uniformize.C 3`, which depends on the ambient dimension alone; that is what
lets the constant `Cunif` of
`Kakeya.ml1Boot.multiplicity_le_middle` be fixed before the `∀ᶠ δ in 𝓝[>] 0`.  As the
blueprint records, item (ix) is not implied by item (viii) and is an obligation on the
refinement construction rather than a consequence of `unif`: a parent-map fibre is a
subfamily of a containment fibre, and uniformity does not pass to arbitrary subfamilies.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Named parent families -/

/-- The fibre `s[k] = {i ∈ s : p i = k}` of a parent map `p` over the parent index `k`.
The blueprint writes `𝕍[V_{ρ,k}]` for the corresponding subfamily `(V_i)_{i ∈ s[k]}`, and
`𝕍[V_{ρ,k}]|_{s'}` for `𝕍|_{s[k] ∩ s'}`, which here is `fibre (s ∩ s') p k`. -/
def fibre {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (p : ι → κ) (k : κ) : Finset ι :=
  s.filter fun i => p i = k

/-- **Restricting to a set of parents deletes only whole fibres.**

If `s' = {i ∈ s : p i ∈ u}` then for every `k ∈ u` the fibre of `s'` over `k` is the *whole*
fibre of `s` over `k`: the restriction removes exactly those `i` whose parent is outside `u`,
and none of those lies over a `k ∈ u`.

This is the index-alignment crux of the two-scale factoring step, blueprint
`lem:ml1bootFactorTwoScales`.  That step has **no Lean producer**:
`exists_factorTwoScales` is not a declaration, and neither is `exists_twoScaleFactorPair`; only
the target structure `Kakeya.ml1Boot.IsFactorTwoScales` and the assembly
`Kakeya.ml1Boot.isFactorTwoScales_of_factorPair` exist.  See blueprint
`note:ml1bootCaseTwoConstructionLayerEmpty`.  GWZ writes
"abusing notation, we will continue to refer to these refinements as …" when the second
application of the one-scale step refines the middle family a second time; the Lean
bookkeeping has to pull the fine family back along the parent map, and this lemma is what
makes the pull-back free on every fibre that survives. -/
theorem fibre_filter_mem {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (p : ι → κ)
    (u : Finset κ) {k : κ} (hk : k ∈ u) :
    fibre (s.filter fun i => p i ∈ u) p k = fibre s p k := by
  unfold fibre
  rw [Finset.filter_filter]
  exact Finset.filter_congr (fun i hi => by
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨by rw [h]; exact hk, h⟩)

/-- **A parent family for `𝕍` at scale `ρ`** (blueprint `def:ml1bootParentFamily`): a finite
index set `t`, an injectively indexed family `𝕍_ρ = (V_{ρ,k})_{k ∈ t}` of `ρ`-tubes, and a
map `p : ι → κ` sending `s` into `t` with `V_i ⊆ V_{ρ,p(i)}` for every `i ∈ s`.

The scale ordering `0 < σ ≤ ρ ≤ 1` of the blueprint is *not* part of this predicate: it is
a hypothesis of every lemma that consumes a parent family, and keeping it out here lets the
same predicate be reused at the scales `δ ≤ τ`, `τ ≤ θ` without repetition.

Injectivity is stated for the underlying convex bodies rather than for the `Tube` records,
which is what the downstream counting arguments use. -/
structure IsParentFamily {ι κ : Type*} {σ ρ : NNReal} (s : Finset ι) (V : ι → Tube σ E)
    (t : Finset κ) (Vρ : κ → Tube ρ E) (p : ι → κ) : Prop where
  /-- The parent map sends `s` into the parent index set `t`. -/
  mapsTo : ∀ i ∈ s, p i ∈ t
  /-- The parent family is indexed injectively. -/
  injOn : Set.InjOn (fun k => (Vρ k).toConvexSpaceBody) t
  /-- Each member of `𝕍` is contained in its parent. -/
  le_parent : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ (Vρ (p i)).toConvexSpaceBody

/-- **A `c`-dilate parent family for `𝕍` at scale `ρ`** (blueprint
`def:ml1bootParentFamilyDilate`): the same data `(t, 𝕍_ρ, p)` as
`Kakeya.ml1Boot.IsParentFamily`, with the containment clause weakened from
`V i ≤ V_{ρ, p i}` to `V i ≤ c · V_{ρ, p i}`, the `c`-dilate `Kakeya.Tube.dilate` of the
parent about its centre.

For `c = 1` the homothety is the identity and the notion is *exactly*
`Kakeya.ml1Boot.IsParentFamily`, so this is a genuine weakening and every parent family is a
`c`-dilate parent family for every `c ≥ 1`.

The weakening is forced longitudinally: a `Kakeya.Tube` has a core segment of length exactly
`1`, hence circumradius `1/2 + O(b)`, whereas the planks of this development have
`ethickness … 0` anywhere up to `1`, a bound that blueprint
`note:ml1bootPlankInTubeVacuous` shows cannot be improved.  The tube attached to a plank by
`Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one` therefore contains the plank only
after dilation by `2`; the applications use `c = 2` and nothing else.

Every consumer pays only a constant: in `ℝ³` a dilation by `c` multiplies volumes by `c ³`
(`Kakeya.Tube.tubeDilateVolume`), and the containment clause is used downstream only through
a volume comparison. -/
structure IsParentFamilyDilate [Nontrivial E] {ι κ : Type*} {σ ρ : NNReal} (c : ℝ)
    (s : Finset ι) (V : ι → Tube σ E) (t : Finset κ) (Vρ : κ → Tube ρ E) (p : ι → κ) :
    Prop where
  /-- The dilation ratio is at least `1`, so that this weakens `IsParentFamily`. -/
  one_le : 1 ≤ c
  /-- The parent map sends `s` into the parent index set `t`. -/
  mapsTo : ∀ i ∈ s, p i ∈ t
  /-- The parent family is indexed injectively. -/
  injOn : Set.InjOn (fun k => (Vρ k).toConvexSpaceBody) t
  /-- Each member of `𝕍` is contained in the `c`-dilate of its parent. -/
  le_parent_dilate : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ Tube.dilate (Vρ (p i)) c

/-- **Bounded overlap of a parent family** (blueprint `def:ml1bootParentBoundedOverlap`).

A parent family `(t, 𝕍_ρ, p)` for `𝕍 = (V i)_{i ∈ s}` has *overlap bounded by `Co`* when, for
every `ρ`-tube `W`, at most `Co` of the parents *meet `W` through `𝕍`* — share a member of `𝕍`
with `W`.

This is `Tube.UniformTubeSet.boundedOverlap` transcribed from the nodes of a hierarchy at
a grid index to a free parent family, word for word: taking `t` to be the node index set, `𝕍_ρ`
the node tubes at that index and `𝕍` the leaves recovers the field exactly, which is what
`Kakeya.ml1Boot.hasBoundedOverlap_nodes` records.  So at the Case (ii) call sites the hypothesis
is discharged by a single field read, with `Co = C_ds`.

The relativization by `𝕍` is what makes the condition satisfiable at all: bare intersection with
`W` is not a bounded condition, a fixed `ρ`-tube being met, as a set, by `ρ`-tubes of every
direction.

It is *not* implied by `Kakeya.ml1Boot.IsParentFamily`; see blueprint
`note:ml1bootEssDistinctParents` for the family that violates it, `δ ^ (-1)` transverse translates
of one `ρ`-tube by multiples of `δ ^ 10`, all containing every leaf.

It does **not**, however, buy an essentially distinct selection at a subpolynomial cost.  Parents
that are axial slides of one another by `≤ c_*` fail to be essentially distinct while their leaves
sit in no common `ρ`-tube, so a family of `≍ ρ ⁻¹` of them has overlap bounded by `1`; that is
`Kakeya.ml1Boot.not_exists_essDistinct_parentFamily`, which refutes the scale-free form of
`Kakeya.ml1Boot.exists_essDistinct_parentFamily` *with* this hypothesis in force.  The retention
such a selection can promise is `c ρ / Co`, and that is what the surviving statement assumes.

The definition itself now lives upstream, as `Tube.HasBoundedOverlap` in
`Kakeya/Uniform.lean`, next to the field it transcribes and where the `ShadedBody` forms of GWZ
Lemma 5.11 can also reach it; this is the `ml1Boot` name for it, and the two are the same
`Prop`. -/
abbrev HasBoundedOverlap {ι κ : Type*} {σ ρ : NNReal} (s : Finset ι) (V : ι → Tube σ E)
    (t : Finset κ) (Vρ : κ → Tube ρ E) (Co : NNReal) : Prop :=
  Tube.HasBoundedOverlap s V t Vρ Co

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Deduplicating a family of tubes** (blueprint `lem:ml1bootDedupeTubeFamily`).

A finite family `(V k)_{k ∈ s}` of `ρ`-tubes, *not* assumed injectively indexed, admits a
subset `t ⊆ s` and a map `q : ι → ι` with `V_{q k} = V_k` for `k ∈ s`, with `k ↦ V_k`
injective on `t`, and with `q` surjective from `s` onto `t`.

This is the bookkeeping that turns an arbitrary indexed family of parents into one satisfying
the injectivity clause of `Kakeya.ml1Boot.IsParentFamily`; it is `Set.rangeSplitting` applied
to `k ↦ V k`.  Equality is asserted for the underlying convex bodies, which is the form the
injectivity clause of `Kakeya.ml1Boot.IsParentFamily` is stated in.

No constraint is imposed on the scale `ρ`: the argument is `Set.rangeSplitting` on a finite
family and never inspects the tubes, so requiring `0 < ρ ≤ 1` would only obstruct the callers
that dedupe at a scale `C b` with `C ≥ 1`, such as
`Kakeya.ml1Boot.exists_plankTube_family`. -/
theorem exists_dedupe {ρ : NNReal}
    {ι : Type*} (s : Finset ι) (V : ι → Tube ρ E) :
    ∃ t ⊆ s, ∃ q : ι → ι,
      (∀ k ∈ s, q k ∈ t) ∧
      (∀ k ∈ s, (V (q k)).toConvexSpaceBody = (V k).toConvexSpaceBody) ∧
      Set.InjOn (fun k => (V k).toConvexSpaceBody) ↑t ∧
      Set.SurjOn q ↑s ↑t := by
  classical
  let f : ι → ConvexSpaceBody E := fun k => (V k).toConvexSpaceBody
  have exists_rep : ∀ k ∈ s, ∃ l ∈ s, f l = f k := by
    intro k hk
    exact ⟨k, hk, rfl⟩
  let q : ι → ι := fun k => if hk : k ∈ s then Classical.choose (exists_rep k hk) else k
  let t : Finset ι := s.image q
  have hq_in_s : ∀ k ∈ s, q k ∈ s := by
    intro k hk
    unfold q
    rw [dif_pos hk]
    exact (Classical.choose_spec (exists_rep k hk)).1
  have ht_sub : t ⊆ s := by
    intro k hk
    change k ∈ s.image q at hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨i, hi, rfl⟩
    exact hq_in_s i hi
  have hfq : ∀ k ∈ s, f (q k) = f k := by
    intro k hk
    unfold q
    rw [dif_pos hk]
    exact (Classical.choose_spec (exists_rep k hk)).2
  have hq_eq : ∀ {k l : ι}, k ∈ s → l ∈ s → f k = f l → q k = q l := by
    intro k l hk hl hff
    unfold q
    simp only [hk, hl]
    simp only [hff.symm]
    exact congrArg Classical.choose (Subsingleton.elim _ _)
  refine ⟨t, ht_sub, q, ?_, ?_, ?_, ?_⟩
  · intro k hk
    change q k ∈ s.image q
    exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
  · intro k hk
    simpa [f] using hfq k hk
  · intro k hk k' hk' hbody
    change k ∈ s.image q at hk
    change k' ∈ s.image q at hk'
    rw [Finset.mem_image] at hk
    rw [Finset.mem_image] at hk'
    rcases hk with ⟨i, hi, hqik⟩
    rcases hk' with ⟨i', hi', hqi'k'⟩
    subst k
    subst k'
    have hff : f (q i) = f (q i') := by
      simpa [f] using hbody
    have hfi : f (q i) = f i := hfq i hi
    have hfi' : f (q i') = f i' := hfq i' hi'
    have hff' : f i = f i' := hfi.symm.trans (hff.trans hfi')
    exact hq_eq hi hi' hff'
  · intro k hk
    change k ∈ s.image q at hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨i, hi, hqik⟩
    exact ⟨i, hi, hqik⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Every family of tubes has a parent family at every coarser scale** (blueprint
`lem:ml1bootExistsParentFamily`).

For `0 < σ ≤ ρ ≤ 1` and a family `𝕍 = (V i)_{i ∈ s}` of `σ`-tubes there are a subset
`t ⊆ s`, a family `𝕍_ρ` of `ρ`-tubes and a parent map `p : s → t` making `(t, 𝕍_ρ, p)` a
parent family for `𝕍` at scale `ρ` with `p` **surjective** onto `t`; and if every `V i` lies
in `B₁` then every parent lies in `B₂`.

The construction is elementary and costs nothing: a `σ`-tube is the closed
`σ`-neighbourhood of a unit segment, so the closed `ρ`-neighbourhood of the *same* segment
is a `ρ`-tube containing it.  Taking one representative index per distinct such body gives
`t`, the injectivity required by `Kakeya.ml1Boot.IsParentFamily`, and surjectivity of `p`.
The parents are only contained in `B₂`, not in `B₁`: the `ρ`-neighbourhood of a segment in
`B₁` reaches out to radius `1 + ρ`.  None of the three consumers above needs the parents to
lie in `B₁`.

Pairwise essential distinctness of the parents is *not* asserted, and cannot be arranged by
this construction.  It is to be supplied separately by
`Kakeya.ml1Boot.exists_essDistinct_parentFamily`, whose statement includes
a scale hypothesis `δ ^ ε' ≤ c ρ / Co` that a caller must pay
(`Kakeya.ml1Boot.not_exists_essDistinct_parentFamily` shows the hypothesis cannot be dropped):
nothing currently supplies it. -/
theorem exists_parentFamily {σ ρ : NNReal} (_hσ0 : 0 < σ) (hσρ : σ ≤ ρ) (hρ1 : ρ ≤ 1)
    {ι : Type*} {s : Finset ι} (V : ι → Tube σ E)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) :
    ∃ (t : Finset ι) (Vρ : ι → Tube ρ E) (p : ι → ι),
      t ⊆ s ∧ IsParentFamily s V t Vρ p ∧ Set.SurjOn p ↑s ↑t ∧
        ∀ k ∈ t, (Vρ k).carrier ⊆ Metric.closedBall 0 2 := by
  classical
  let f : ι → ConvexSpaceBody E := fun i => ((V i).rescale ρ).toConvexSpaceBody
  have exists_rep : ∀ i ∈ s, ∃ j ∈ s, f j = f i := by
    intro i hi
    exact ⟨i, hi, rfl⟩
  let p : ι → ι := fun i => if hi : i ∈ s then Classical.choose (exists_rep i hi) else i
  let t : Finset ι := s.image p
  let Vρ : ι → Tube ρ E := fun k => (V k).rescale ρ
  have hp_in_s : ∀ i ∈ s, p i ∈ s := by
    intro i hi
    unfold p
    rw [dif_pos hi]
    exact (Classical.choose_spec (exists_rep i hi)).1
  have ht_sub : t ⊆ s := by
    intro k hk
    change k ∈ s.image p at hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨i, hi, rfl⟩
    exact hp_in_s i hi
  have hfp : ∀ i ∈ s, f (p i) = f i := by
    intro i hi
    unfold p
    rw [dif_pos hi]
    exact (Classical.choose_spec (exists_rep i hi)).2
  have hp_eq : ∀ {i i' : ι}, i ∈ s → i' ∈ s → f i = f i' → p i = p i' := by
    intro i i' hi hi' hff
    unfold p
    simp only [hi, hi']
    simp only [hff.symm]
    exact congrArg Classical.choose (Subsingleton.elim _ _)
  refine ⟨t, Vρ, p, ht_sub, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro i hi
      change p i ∈ s.image p
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    · intro k hk k' hk' hbody
      change k ∈ s.image p at hk
      change k' ∈ s.image p at hk'
      rw [Finset.mem_image] at hk
      rw [Finset.mem_image] at hk'
      rcases hk with ⟨i, hi, hpik⟩
      rcases hk' with ⟨i', hi', hpi'k'⟩
      subst k
      subst k'
      have hff : f (p i) = f (p i') := by
        simpa [Vρ, f] using hbody
      have hfi : f (p i) = f i := hfp i hi
      have hfi' : f (p i') = f i' := hfp i' hi'
      have hff' : f i = f i' := hfi.symm.trans (hff.trans hfi')
      exact hp_eq hi hi' hff'
    · intro i hi
      change (V i).toConvexSpaceBody ≤ ((V (p i)).rescale ρ).toConvexSpaceBody
      have hle := (V i).le_rescale hσρ
      have hspec : f (p i) = f i := hfp i hi
      have hf_eq : ((V (p i)).rescale ρ).toConvexSpaceBody =
          ((V i).rescale ρ).toConvexSpaceBody := by
        simpa [f] using hspec
      rw [hf_eq]
      exact hle
  · intro k hk
    change k ∈ s.image p at hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨i, hi, hpik⟩
    exact ⟨i, hi, hpik⟩
  · intro k hk
    have hk_s : k ∈ s := ht_sub hk
    have hz0 : ∀ z ∈ segment ℝ (V k).x (V k).y, dist z 0 ≤ 1 := by
      intro z hz
      have hz_carrier : z ∈ (V k).carrier := by
        rw [(V k).carrier_eq]
        exact Set.mem_iUnion₂.mpr ⟨z, hz, Metric.mem_closedBall_self (NNReal.coe_nonneg σ)⟩
      have hz_ball := hball k hk_s hz_carrier
      simpa [Metric.mem_closedBall] using hz_ball
    intro w hw
    rw [(Vρ k).carrier_eq] at hw
    obtain ⟨z, hz_seg, hwz⟩ := Set.mem_iUnion₂.mp hw
    rw [Metric.mem_closedBall]
    have hwz_le : dist w z ≤ (ρ : ℝ) := by
      simpa [Metric.mem_closedBall] using hwz
    have htri := dist_triangle w z 0
    have hb : dist w z + dist z 0 ≤ (2 : ℝ) := by
      have hρle : (ρ : ℝ) ≤ (1 : ℝ) := NNReal.coe_le_coe.mpr hρ1
      have hz01 : dist z 0 ≤ 1 := hz0 z hz_seg
      nlinarith
    exact le_trans htri hb

/- **Moved interface: essentially distinct parents of a boundedly overlapping parent family,
at a cost
`δ ^ (-ε')` and under a scale hypothesis** (blueprint `prop:ml1bootEssDistinctParents`).

> **The hypothesis-free form of this statement — the same conclusion for every `δ ≤ σ ≤ ρ ≤ 1` —
> is false**, and `Kakeya.ml1Boot.not_exists_essDistinct_parentFamily` proves its negation.  What
> is false is the *size* of the loss, not the shape of the conclusion: the loss must be a power of
> the parent scale `ρ` and cannot be a power of `δ` alone.  The statement below is the repaired
> one: it carries the scale hypothesis `δ ^ ε' ≤ c ρ / Co`, which the refuting pencil violates.
> The refutation next door is retained as the record of why that hypothesis is in the signature;
> do not drop the hypothesis, and do not delete the refutation.  See "The bounded-overlap
> hypothesis is not enough" below.

Given a uniform family of shaded, pairwise essentially distinct `σ`-tubes in `B₁ ⊆ ℝ³` and a
parent family for it at a scale `ρ ≥ σ` **whose overlap is bounded by `Co`** in the sense of
`Kakeya.ml1Boot.HasBoundedOverlap`, one may discard all but a pairwise essentially distinct set
`t'` of parents, keeping the leaves that lie over `t'`, and retain a `δ ^ ε'` share of **one
caller-chosen weight** `w` on the leaves — *provided* `δ ^ ε'` is at most the honest retention
`c ρ / Co` of a greedy selection, which is the hypothesis `δ ^ ε' ≤ c ρ / Co`.

## What the greedy route actually delivers, and how the statement was fitted to it

The route is: choose `t' ⊆ t` maximal pairwise essentially distinct, greedily along the order of
*decreasing fibre weight* `k ↦ ∑ i ∈ fibre s p k, w i`, and put `s' = {i ∈ s : p i ∈ t'}`.
Four consequences, each of which is a clause below.

* *Leaves are discarded, never reassigned.*  Sending the leaves of a discarded parent to its
  representative would break `Kakeya.ml1Boot.IsParentFamily.le_parent`: two parents that fail to
  be essentially distinct have large intersection, which is not containment, so a leaf of one
  need not lie in the other.  So `s'` is a *filter* along `p`, and `IsParentFamily s' _ t' Vρ p`
  holds with `mapsTo` — the clause `∀ i ∈ s', p i ∈ t'` — true by construction.
* *The fibres over the retained parents are untouched.*  `Kakeya.ml1Boot.fibre_filter_mem`:
  restricting to a set of parents deletes only **whole** fibres, so for `k ∈ t'` one has
  `fibre s' p k = fibre s p k` on the nose.  The fibrewise Frostman clause below is therefore
  delivered with *no loss at all*, the stated `δ ^ (-ε')` being pure slack; this is what makes it
  legitimate to state it in the shape of `Kakeya.ml1Boot.IsUniformRefinement.fibreFrostman`,
  with the side condition at the **fibre** and not at the whole family, which is the shape the
  Case (ii) repair consumes.
* *The retention is a constant, and it is for the weight the greedy was ordered by.*  Each
  discarded `k` is charged to the representative `r k ∈ t'` it fails to be essentially distinct
  from; bounded overlap caps `|r ⁻¹ k'| ≤ Co`, and the ordering gives
  `∑_{fibre s p k} w ≤ ∑_{fibre s p (r k)} w`.  Summing over the fibres, which partition `s`,
  gives `∑ i ∈ s, w i ≤ Co * ∑ i ∈ s', w i`, and a constant fixed before `δ` is absorbed into
  `δ ^ (-ε')`.
* *One weight, not two.*  The weight is a **parameter** because no essentially distinct selection
  can retain a constant share of two incomparable weights at once, and the two the Case (ii)
  chain wants — the counting weight `w = 1` and the shade mass `w i = volume (V i).shade` — are
  incomparable.  Two parents that fail to be essentially distinct, carrying `(|s[k]|, mass) =
  (M, 1/M)` and `(1, 1)` respectively: exactly one survives, and whichever it is, one of the two
  shares is `≈ 1/M`.  Nothing in the hypotheses forbids this — `ShadedTube.ShadedUniformTubeSet`
  controls the *local* multiplicity of the shadings, never the individual volumes
  `volume (V i).shade` — so the two shares are genuinely alternatives.  Callers pick: `w = 1`
  gives the cardinality share, from which the *global* Frostman transport follows through
  `ConvexSpaceBody.frostmanConstIn_subfamily_le`; `w i = volume (V i).shade` gives the shade-mass
  share and hence `ShadedBody.IsCRefinement`, which is
  `Kakeya.ml1Boot.essDistinct_parentFamily_isCRefinement`.

## The bounded-overlap hypothesis is not enough

*What earlier revisions got right.*  Without `hoverlap` the statement is false.  Fix a `ρ`-tube
`V₀` in `B₁`, let the leaves be pairwise essentially distinct `σ`-tubes well inside `V₀`, and let
`t` index `M = δ ⁻¹` translates of `V₀` by distinct multiples of `δ ^ 10` in a transverse
direction.  These are distinct convex bodies, so `Kakeya.ml1Boot.IsParentFamily.injOn` holds, and
each still contains every leaf, so `le_parent` holds; split the leaves evenly along `p`.  Any two
parents overlap in `(1 - o(1))` of their volume, so every pairwise essentially distinct `t' ⊆ t`
is a singleton, whence at `w = 1` the retention reads `1 ≤ δ ^ (1 - ε')`.  That configuration does
violate bounded overlap: at `W = Vρ k₀` all `δ ⁻¹` parents meet `W` through `𝕍`.

*What they got wrong.*  Adding `hoverlap` does not repair it.  Earlier revisions argued that it
does, on the ground that nearly-coincident parents carrying leaves must meet each other through
`𝕍`; that inference is false, and the paragraph that withdrew it — "take two translates
overlapping in `0.9 v` and put every leaf of `k'` inside `Vρ k' \ Vρ k` … so `k'` is not counted
at `W = Vρ k`" — did not finish the job either, because `Kakeya.Tube.HasBoundedOverlap`
quantifies over **every** `ρ`-tube `W` and not only over the members of `𝕍_ρ`.  Two parents that
overlap in `0.9 v` are within `O(ρ)` of one another, so the `ρ`-tube on the core of a leaf of `k`
contains a leaf of `k'` as well, and `Co` is forced up after all.

*The counterexample that does work.*  Separate the parents **axially** instead of transversally.
A `Kakeya.Tube` has a core of length exactly `1`, so containment in a `ρ`-tube pins the axial
position to within `3 ρ` (`Kakeya.Tube.endpoints_close_of_body_le`), while an axial slide of
length up to `c_* = 1 / 12` leaves two `ρ`-tubes overlapping in `≥ 3/4` of their volume
(`Kakeya.Tube.not_essDistinct_of_axial_slide`).  Between `3 ρ` and `c_*` there is room for
`M ≍ ρ ⁻¹` parents that pairwise fail to be essentially distinct while no `ρ`-tube whatever
contains two leaves: overlap `Co = 1`, and the retention is `1 / M ≍ ρ`.  Taking
`ρ ≍ σ ^ (1/2) ≍ δ ^ (1/2)` makes `M ≍ δ ^ (-1/2)` and refutes the statement for every
`ε' ≤ 1/8`.  This is `Kakeya.ml1Boot.not_exists_essDistinct_parentFamily`; the pencil is
`Kakeya.ml1Boot.essDistinctCex.leaf`.

*The repair, which is what is stated below.*  The honest retention of a greedy essentially
distinct selection is `c ρ / Co` with `c` dimensional, not `δ ^ ε'`: the axial position is the one
tube parameter that essential distinctness does not separate but bounded overlap does, which is
the same `ρ ^ (-5)` against `ρ ^ (-4)` discrepancy recorded in
`Kakeya/DimensionThree/BoundedOverlapCount.lean`.  So the statement becomes true — with its scale hypothesis explicit — on adding the scale hypothesis `δ ^ ε' ≤ c ρ / Co` to the ladder
`δ ≤ σ → σ ≤ ρ → ρ ≤ 1`, with `c` a constant depending on the ambient dimension alone.  Nothing
else changes.  The axial pencil violates it: there `ρ ≍ δ ^ (1/4)` while `ε' ≤ 1/8` keeps
`δ ^ ε' ≥ δ ^ (1/8)`, so `δ ^ ε' ≤ c ρ / Co` fails at every large stage of the pencil for each
fixed `c > 0`, which is precisely why the refutation no longer applies.  In the intended
application the loss is harmless: the module docstring records that the tube scales occurring
there are `δ / τ`, `τ / θ` and `θ`, none of which is small, so `c ρ / Co` is a constant absorbed
into `δ ^ (-ε')`.

## Why the constant is existentially quantified, and quantified outermost

`c` is *not* given a value. Pinning a numeral would therefore be a guess in the dangerous direction — `c` is
a *small* constant standing on the large side of a hypothesis, so choosing it too large makes the
statement false again, exactly the failure this repair corrects. It is instead returned as
`∃ c : NNReal, 0 < c ∧ …`, which is the honest reading "there is a dimensional constant `c`". Since it stands outside `ε'`, `Cunif` and `Co`, it may depend on none of them, only on the ambient
dimension, which `hdim` pins to `3`; that placement is what keeps this the strongest form of the
repair rather than a weaker one in which the constant is allowed to chase the other parameters. Consequently no `Constant in Lemma` definition accompanies it: there is no Lean definition to
point `\lean{…}` at until the greedy bound is proved, at which point the witness that proof
produces should be promoted to a named definition in the style of
`Kakeya.Tube.overlapConstBOTight`.

## How the repair reaches the consumer

Adding a hypothesis changes the arity, and the sole code consumer,
`Kakeya.ml1Boot.exists_repairEssDistinct` (`Kakeya/DimensionThree/MainLemma1/Repair.lean`), reads
this statement through `filter_upwards` and applies it positionally at `(σ, ρ) = (δ, θ)` and
`(δ, τ)`, each at `ε' / 2`.  That consumer quantifies `τ` and `θ` over the whole ladder
`δ ≤ τ ≤ θ ≤ 1`, so it cannot pay `δ ^ (ε'/2) ≤ c τ / Co` from its own signature: it was
over-general in exactly the same way, and was itself false for that reason.  The repair is
therefore a two-declaration change and has been made as one.  The consumer now carries the single
hypothesis `δ ^ (ε'/2) ≤ c τ / Co` — at the fine scale `τ ≤ θ`, from which the coarse instance
follows — and passes on the very `c` obtained here.  `exists_repairEssDistinct` has no code
consumers of its own, so the thread stops there and nothing further had to pay.

*Unaffected by all of this.*  The proposition becomes vacuous — on taking `s' = s`, `t' = t` — as
soon as the hypothesis `hed` of the `ShadedBody` form of GWZ Lemma 5.11 is weakened to
the same bounded-overlap condition.  Note that the blueprint statement of that lemma asks for
pairwise essential distinctness and **not** for bounded overlap, so that weakening is a change to
an accepted interface rather than a correction of its Lean transcription: it *merges* this
obligation into that one rather than discharging either, and it makes the loss constant depend on
`Co`.  See blueprint `note:ml1bootEssDistinctParents`.

At the Case (ii) call sites `hoverlap` is one field read,
`Kakeya.ml1Boot.hasBoundedOverlap_nodes`, with `Co = C_ds`, and both applications run on the
**leaves**: the coarse one takes the `θ`-node family with the composed parent map, so no shading
of a parent tube is ever needed and the shading and uniformity hypotheses stay where the route
uses them, on `𝕍`. Blueprint `note:ml1bootRepairEDCoarseShading`. -/
/-! ### The counterexample: a boundedly overlapping parent family with no essentially distinct
subfamily

`Kakeya.ml1Boot.not_exists_essDistinct_parentFamily` below refutes the statement above *read
without its scale hypothesis* — which is why that hypothesis is there.  The witness is an *axial
pencil*: `M ≍ ρ ⁻¹` leaves whose cores are unit segments in one common
direction, spaced `7 ρ` apart along that direction and displaced transversally by `3 σ` per step,
each with the `ρ`-tube on its own core as its parent.

Three elementary facts drive it, and all three are already in the development.

* **The parents pairwise fail to be essentially distinct.**  They are axial slides of one another
  by at most `7 ρ M ≤ c_* = 1 / 12`, and `Kakeya.Tube.not_essDistinct_of_axial_slide` says an
  axial slide of that range overlaps the original in `≥ 3/4` of its volume.  No volume of an
  intersection is ever computed.
* **The overlap is bounded by `Co = 1`.**  A `Tube` has a core of length exactly `1`, so
  `Kakeya.Tube.endpoints_close_of_body_le` turns `V i ≤ W` into "the endpoints of `V i` and `W`
  agree to within `3 ρ`".  Two leaves `7 ρ` apart along the core direction therefore never lie in
  a common `ρ`-tube, and a leaf lies in no parent but its own.  This is the point the docstring
  above misses: `Kakeya.Tube.HasBoundedOverlap` quantifies over **every** `ρ`-tube `W`, and the
  refuting paragraph of that docstring only tests `W = V_ρ k`.
* **The leaves are pairwise essentially distinct, indeed disjoint.**  Consecutive cores are
  `3 σ` apart in the transverse direction `e₂`, and a leaf is confined to the slab
  `|⟪·, e₂⟫ - 3 σ i| ≤ σ`; the slabs are disjoint.

Uniformity of the leaf family is *not* constructed by hand: `Kakeya.Tube.exists_uniformTubeSet_subfamily_ssf`
refines any family in `B₁` to a uniform subfamily at the grid length `Tube.ssfGridLen σ` with a
dimensional constant, at a cost `σ ^ (-ε')`, and the shading clauses of
`ShadedTube.ShadedUniformTubeSet` are vacuous for the empty shading — which the statement above
permits, since it constrains no shading density.

The scales are taken along the sequence `σ = 2 ^ (-8n)`, `ρ = 2 ^ (-(2n+9))`, `M = 2 ^ (2n+1)`, so
that `M ≍ σ ^ (-1/4)` beats the two losses `σ ^ ε'` (uniformization) and `δ ^ ε'` (retention)
whenever `ε' ≤ 1/8`. -/

/-- The first standard basis vector of `ℝ³`: the common core direction of every tube of the
counterexample family `Kakeya.ml1Boot.essDistinctCex.leaf`. -/
noncomputable def essDistinctCex.e₁ : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 (1 : ℝ)

/-- The second standard basis vector of `ℝ³`: the direction of the transverse displacement that
makes the leaves of `Kakeya.ml1Boot.essDistinctCex.leaf` pairwise disjoint. -/
noncomputable def essDistinctCex.e₂ : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 1 (1 : ℝ)

namespace essDistinctCex

/-! #### The two coordinates the argument uses

Everything below is read off two orthonormal directions: `e₁`, along which containment in a
unit-core tube pins the axial position, and `e₂`, along which the leaves are separated. -/

theorem norm_e₁ : ‖e₁‖ = 1 := by
  simp [e₁]

theorem norm_e₂ : ‖e₂‖ = 1 := by
  simp [e₂]

theorem inner_e₁_e₁ : (inner ℝ e₁ e₁ : ℝ) = 1 := by
  simp [e₁]

theorem inner_e₂_e₁ : (inner ℝ e₂ e₁ : ℝ) = 0 := by
  simp [e₁, e₂, EuclideanSpace.inner_single_right, (by decide : (0 : Fin 3) ≠ 1)]

theorem inner_e₁_e₂ : (inner ℝ e₁ e₂ : ℝ) = 0 := by
  simp [e₁, e₂, EuclideanSpace.inner_single_right, (by decide : (1 : Fin 3) ≠ 0)]

theorem inner_e₂_e₂ : (inner ℝ e₂ e₂ : ℝ) = 1 := by
  simp [e₂]

/-- The axial coordinate of the `i`-th core of the pencil: the cores are spaced `7 ρ` apart along
the common direction `e₁`, and centred so that the whole pencil lies in `B₁`. -/
noncomputable def axial (ρ : NNReal) (i : ℕ) : ℝ := 7 * (ρ : ℝ) * i - 1 / 2

/-- The transverse coordinate of the `i`-th core of the pencil: consecutive cores are `3 σ` apart
along `e₂`, which is what makes the leaves disjoint. -/
noncomputable def trans (σ : NNReal) (i : ℕ) : ℝ := 3 * (σ : ℝ) * i

/-- The starting endpoint of the `i`-th core of the pencil. -/
noncomputable def base (σ ρ : NNReal) (i : ℕ) : EuclideanSpace ℝ (Fin 3) :=
  (axial ρ i) • e₁ + (trans σ i) • e₂

theorem inner_base_e₁ (σ ρ : NNReal) (i : ℕ) :
    (inner ℝ (base σ ρ i) e₁ : ℝ) = axial ρ i := by
  unfold base
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  rw [inner_e₁_e₁, inner_e₂_e₁]
  ring

theorem inner_base_e₂ (σ ρ : NNReal) (i : ℕ) :
    (inner ℝ (base σ ρ i) e₂ : ℝ) = trans σ i := by
  unfold base
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  rw [inner_e₁_e₂, inner_e₂_e₂]
  ring

theorem dist_base (σ ρ : NNReal) (i : ℕ) : dist (base σ ρ i) (base σ ρ i + e₁) = 1 := by
  rw [dist_self_add_right]
  rw [norm_e₁]

/-- The `i`-th **leaf** of the counterexample: the `σ`-tube whose core is the unit segment from
`base σ ρ i` to `base σ ρ i + e₁`. -/
noncomputable def leaf (σ ρ : NNReal) (i : ℕ) : Tube σ (EuclideanSpace ℝ (Fin 3)) :=
  Tube.mk' σ (dist_base σ ρ i)

/-- The `i`-th **parent** of the counterexample: the `ρ`-tube on the core of the `i`-th leaf. -/
noncomputable def parent (σ ρ : NNReal) (i : ℕ) : Tube ρ (EuclideanSpace ℝ (Fin 3)) :=
  (leaf σ ρ i).rescale ρ

/-- The `i`-th leaf with the **empty** shading.  The statement refuted below constrains no shading
density, so the empty shading is admissible, and it makes every shading clause of
`ShadedTube.ShadedUniformTubeSet` vacuous. -/
noncomputable def shadedLeaf (σ ρ : NNReal) (i : ℕ) :
    ShadedTube σ (EuclideanSpace ℝ (Fin 3)) where
  toTube := leaf σ ρ i
  shade := ∅
  measurableSet_shade := MeasurableSet.empty
  shade_subset := Set.empty_subset _

@[simp] theorem leaf_x (σ ρ : NNReal) (i : ℕ) : (leaf σ ρ i).x = base σ ρ i := rfl

@[simp] theorem leaf_y (σ ρ : NNReal) (i : ℕ) : (leaf σ ρ i).y = base σ ρ i + e₁ := rfl

@[simp] theorem parent_x (σ ρ : NNReal) (i : ℕ) : (parent σ ρ i).x = base σ ρ i := rfl

@[simp] theorem parent_y (σ ρ : NNReal) (i : ℕ) : (parent σ ρ i).y = base σ ρ i + e₁ := rfl

@[simp] theorem shadedLeaf_toTube (σ ρ : NNReal) (i : ℕ) :
    (shadedLeaf σ ρ i).toTube = leaf σ ρ i := rfl

@[simp] theorem shadedLeaf_shade (σ ρ : NNReal) (i : ℕ) : (shadedLeaf σ ρ i).shade = ∅ := rfl

theorem parent_direction (σ ρ : NNReal) (i : ℕ) : (parent σ ρ i).direction = e₁ := by
  simp [Tube.direction]

/-- **Every leaf of the pencil lies in `B₁`.**  The core of the `i`-th leaf has endpoints with
`e₁`-coordinate in `[-1/2, 1/2 + 7 ρ M]` and `e₂`-coordinate `3 σ i ≤ 3 σ M`, so both endpoints
lie in `B̄(0, 2/3)` and the carrier in `B̄(0, 2/3 + σ)`. -/
theorem leaf_carrier_subset_ball {σ ρ : NNReal} {M : ℕ} (hσρ : σ ≤ ρ)
    (hρ : (ρ : ℝ) ≤ 1 / 128) (hax : 7 * (ρ : ℝ) * M ≤ 1 / 12)
    (htr : 3 * (σ : ℝ) * M ≤ 1 / 12) {i : ℕ} (hi : i ≤ M) :
    (leaf σ ρ i).carrier ⊆ Metric.closedBall 0 1 := by
  let E := EuclideanSpace ℝ (Fin 3)
  have hi' : (i : ℝ) ≤ (M : ℝ) := by exact_mod_cast hi
  have hi0 : 0 ≤ (i : ℝ) := by exact_mod_cast (Nat.zero_le i)
  have h7pos : 0 ≤ 7 * (ρ : ℝ) := mul_nonneg (by norm_num) (NNReal.coe_nonneg ρ)
  have h3pos : 0 ≤ 3 * (σ : ℝ) := mul_nonneg (by norm_num) (NNReal.coe_nonneg σ)
  have hax_i : 7 * (ρ : ℝ) * (i : ℝ) ≤ 1 / 12 := by
    exact (mul_le_mul_of_nonneg_left hi' h7pos).trans hax
  have htr_i : 3 * (σ : ℝ) * (i : ℝ) ≤ 1 / 12 := by
    exact (mul_le_mul_of_nonneg_left hi' h3pos).trans htr
  have hax0 : 0 ≤ 7 * (ρ : ℝ) * (i : ℝ) := by
    exact mul_nonneg h7pos hi0
  have htr0 : 0 ≤ 3 * (σ : ℝ) * (i : ℝ) := by
    exact mul_nonneg h3pos hi0
  have ha_abs : |axial ρ i| ≤ 1 / 2 := by
    rw [abs_le]
    constructor
    · dsimp [axial]
      nlinarith [hax0]
    · dsimp [axial]
      nlinarith [hax_i]
  have hb_abs : |trans σ i| ≤ 1 / 12 := by
    rw [abs_le]
    constructor
    · dsimp [trans]
      nlinarith [htr0]
    · dsimp [trans]
      nlinarith [htr_i]
  have ha1_abs : |axial ρ i + 1| ≤ 1 / 2 + 1 / 12 := by
    rw [abs_le]
    constructor
    · dsimp [axial]
      nlinarith [hax0]
    · dsimp [axial]
      nlinarith [hax_i]
  have hdecomp : base σ ρ i + e₁ = (axial ρ i + 1) • e₁ + trans σ i • e₂ := by
    rw [base, add_smul, one_smul]
    ac_rfl
  have hp_norm : ‖base σ ρ i‖ ≤ 2 / 3 := by
    calc
      ‖base σ ρ i‖ = ‖axial ρ i • e₁ + trans σ i • e₂‖ := by simp [base]
      _ ≤ ‖axial ρ i • e₁‖ + ‖trans σ i • e₂‖ := norm_add_le _ _
      _ = |axial ρ i| + |trans σ i| := by simp [norm_smul, norm_e₁, norm_e₂]
      _ ≤ 1 / 2 + 1 / 12 := by gcongr
      _ ≤ 2 / 3 := by norm_num
  have hq_norm : ‖base σ ρ i + e₁‖ ≤ 2 / 3 := by
    rw [hdecomp]
    calc
      ‖(axial ρ i + 1) • e₁ + trans σ i • e₂‖ ≤ ‖(axial ρ i + 1) • e₁‖ + ‖trans σ i • e₂‖ :=
        norm_add_le _ _
      _ = |axial ρ i + 1| + |trans σ i| := by simp [norm_smul, norm_e₁, norm_e₂]
      _ ≤ (1 / 2 + 1 / 12) + 1 / 12 := by gcongr
      _ ≤ 2 / 3 := by norm_num
  have hp_ball : base σ ρ i ∈ Metric.closedBall (0 : E) (2 / 3 : ℝ) := by
    rw [Metric.mem_closedBall]
    rw [dist_eq_norm]
    simpa using hp_norm
  have hq_ball : base σ ρ i + e₁ ∈ Metric.closedBall (0 : E) (2 / 3 : ℝ) := by
    rw [Metric.mem_closedBall]
    rw [dist_eq_norm]
    simpa using hq_norm
  have hseg : segment ℝ (base σ ρ i) (base σ ρ i + e₁) ⊆
      Metric.closedBall (0 : E) (2 / 3 : ℝ) :=
    Convex.segment_subset (convex_closedBall (0 : E) (2 / 3 : ℝ)) hp_ball hq_ball
  intro w hw
  rw [(leaf σ ρ i).carrier_eq] at hw
  rw [leaf_x, leaf_y] at hw
  rw [Set.mem_iUnion₂] at hw
  rcases hw with ⟨z, hz, hwz⟩
  have hwz' : dist w z ≤ (σ : ℝ) := Metric.mem_closedBall.mp hwz
  have hzb : z ∈ Metric.closedBall (0 : E) (2 / 3 : ℝ) := hseg hz
  have hz0 : dist z 0 ≤ 2 / 3 := Metric.mem_closedBall.mp hzb
  have hσ_le : (σ : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hσρ
  have hσ_le_128 : (σ : ℝ) ≤ 1 / 128 := le_trans hσ_le hρ
  have hw0 : dist w 0 ≤ 1 := by
    calc
      dist w 0 ≤ dist w z + dist z 0 := dist_triangle w z 0
      _ ≤ (σ : ℝ) + 2 / 3 := by gcongr
      _ ≤ 1 / 128 + 2 / 3 := by gcongr
      _ ≤ 1 := by norm_num
  exact Metric.mem_closedBall.mpr hw0

/-- **A leaf is confined to a transverse slab of width `2 σ` about its own core.**  Every point of
the carrier has `e₂`-coordinate within `σ` of `3 σ i`, because the `e₂`-coordinate is constant
along the core (the core direction is `e₁`) and the carrier is its `σ`-neighbourhood. -/
theorem abs_inner_e₂_sub_le {σ ρ : NNReal} {i : ℕ} {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ (leaf σ ρ i).carrier) :
    |(inner ℝ z e₂ : ℝ) - trans σ i| ≤ (σ : ℝ) := by
  rw [(leaf σ ρ i).carrier_eq] at hz
  rw [leaf_x, leaf_y] at hz
  rw [Set.mem_iUnion₂] at hz
  rcases hz with ⟨w, hw, hzw⟩
  have hwz : dist z w ≤ (σ : ℝ) := Metric.mem_closedBall.mp hzw
  have hw_inner : (inner ℝ w e₂ : ℝ) = trans σ i := by
    rw [segment_eq_image] at hw
    rcases hw with ⟨lam, _, rfl⟩
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    rw [inner_add_left, inner_base_e₂, inner_e₁_e₂]
    ring
  calc
    |(inner ℝ z e₂ : ℝ) - trans σ i| = |(inner ℝ (z - w) e₂ : ℝ)| := by
      rw [← hw_inner]
      rw [← inner_sub_left]
    _ ≤ ‖z - w‖ * ‖e₂‖ := abs_real_inner_le_norm (z - w) e₂
    _ = ‖z - w‖ := by simp [norm_e₂]
    _ = dist z w := by rw [← dist_eq_norm]
    _ ≤ (σ : ℝ) := hwz

/-- **Distinct leaves of the pencil are disjoint**: their transverse slabs are `3 σ` apart and
`2 σ` wide. -/
theorem leaf_carrier_disjoint {σ ρ : NNReal} (hσ0 : 0 < σ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (leaf σ ρ i).carrier (leaf σ ρ j).carrier := by
  rw [Set.disjoint_left]
  intro z hzi hzj
  let c : ℝ := (inner ℝ z e₂ : ℝ)
  have h1 : |(inner ℝ z e₂ : ℝ) - trans σ i| ≤ (σ : ℝ) :=
    abs_inner_e₂_sub_le (σ := σ) (ρ := ρ) (i := i) (z := z) hzi
  have h2 : |(inner ℝ z e₂ : ℝ) - trans σ j| ≤ (σ : ℝ) :=
    abs_inner_e₂_sub_le (σ := σ) (ρ := ρ) (i := j) (z := z) hzj
  have hle : |trans σ i - trans σ j| ≤ 2 * (σ : ℝ) := by
    calc
      |trans σ i - trans σ j| = |(trans σ i - c) + (c - trans σ j)| := by
        dsimp [c]
        ring_nf
      _ ≤ |trans σ i - c| + |c - trans σ j| := abs_add_le (trans σ i - c) (c - trans σ j)
      _ = |c - trans σ i| + |c - trans σ j| := by rw [abs_sub_comm]
      _ = |(inner ℝ z e₂ : ℝ) - trans σ i| + |(inner ℝ z e₂ : ℝ) - trans σ j| := rfl
      _ ≤ (σ : ℝ) + (σ : ℝ) := add_le_add h1 h2
      _ = 2 * (σ : ℝ) := by ring
  have htransi : trans σ i = 3 * (σ : ℝ) * (i : ℝ) := rfl
  have htransj : trans σ j = 3 * (σ : ℝ) * (j : ℝ) := rfl
  have hdiff :
      |(3 * (σ : ℝ) * (i : ℝ)) - (3 * (σ : ℝ) * (j : ℝ))| ≤ 2 * (σ : ℝ) := by
    rw [htransi, htransj] at hle
    exact hle
  have hσℝ : 0 < (σ : ℝ) := by exact_mod_cast hσ0
  have h3σ : 0 ≤ 3 * (σ : ℝ) := by linarith
  have hmain : (3 * (σ : ℝ)) * |(i : ℝ) - (j : ℝ)| ≤ 2 * (σ : ℝ) := by
    calc
      (3 * (σ : ℝ)) * |(i : ℝ) - (j : ℝ)| =
          |(3 * (σ : ℝ)) * ((i : ℝ) - (j : ℝ))| := by
            rw [abs_mul, abs_of_nonneg h3σ]
      _ = |(3 * (σ : ℝ)) * (i : ℝ) - (3 * (σ : ℝ)) * (j : ℝ)| := by ring_nf
      _ ≤ 2 * (σ : ℝ) := hdiff
  have hsep : (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by
    by_cases hlt : i < j
    · have hic : (i : ℝ) < (j : ℝ) := by exact_mod_cast hlt
      have hone : (1 : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
        have hi1 : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hlt)
        linarith
      rw [abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ (j : ℝ) - (i : ℝ))]
      exact hone
    · have hgt : j < i := lt_of_le_of_ne (Nat.le_of_not_gt hlt) hij.symm
      have hjc : (j : ℝ) < (i : ℝ) := by exact_mod_cast hgt
      have hone : (1 : ℝ) ≤ (i : ℝ) - (j : ℝ) := by
        have hj1 : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hgt)
        linarith
      rw [abs_of_nonneg (by linarith : 0 ≤ (i : ℝ) - (j : ℝ))]
      exact hone
  have h3low : 3 * (σ : ℝ) ≤ (3 * (σ : ℝ)) * |(i : ℝ) - (j : ℝ)| := by
    have hm := mul_le_mul_of_nonneg_left hsep h3σ
    simpa [mul_one] using hm
  have hcontr : 3 * (σ : ℝ) ≤ 2 * (σ : ℝ) := le_trans h3low hmain
  have hbad : 2 * (σ : ℝ) < 3 * (σ : ℝ) := by linarith
  exact (not_le_of_gt hbad) hcontr

/-- **The leaves of the pencil are pairwise essentially distinct**, being pairwise disjoint. -/
theorem isEssentiallyDistinct_leaf {σ ρ : NNReal} (hσ0 : 0 < σ) {i j : ℕ} (hij : i ≠ j) :
    IsEssentiallyDistinct (leaf σ ρ i).carrier (leaf σ ρ j).carrier := by
  unfold IsEssentiallyDistinct
  have hd : Disjoint (leaf σ ρ i).carrier (leaf σ ρ j).carrier := leaf_carrier_disjoint hσ0 hij
  have hint : (leaf σ ρ i).carrier ∩ (leaf σ ρ j).carrier = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp hd
  simp [hint]

/-- **The parents of the pencil pairwise fail to be essentially distinct.**

`parent σ ρ j` is the axial slide of `parent σ ρ i` by `α = 7 ρ (j - i)`, up to a transverse error
`3 σ |j - i|`.  With `|α| ≤ 7 ρ M ≤ 1/12 = c_*` and the error `≤ ρ / 12 = c_* ρ`, this is
`Kakeya.Tube.not_essDistinct_of_axial_slide` verbatim. -/
theorem not_isEssentiallyDistinct_parent {σ ρ : NNReal} {M : ℕ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hax : 7 * (ρ : ℝ) * M ≤ 1 / 12) (htr : 3 * (σ : ℝ) * M ≤ (ρ : ℝ) / 12)
    {i j : ℕ} (hi : i ≤ M) (hj : j ≤ M) :
    ¬ IsEssentiallyDistinct (parent σ ρ i).carrier (parent σ ρ j).carrier := by
  let α : ℝ := 7 * (ρ : ℝ) * ((j : ℝ) - (i : ℝ))
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hc : 1 / (4 * (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ)) = 1 / 12 := by
    rw [hfin]
    norm_num
  have hj' : (j : ℝ) ≤ (M : ℝ) := by exact_mod_cast hj
  have hi' : (i : ℝ) ≤ (M : ℝ) := by exact_mod_cast hi
  have hi0 : 0 ≤ (i : ℝ) := by exact_mod_cast (Nat.zero_le i)
  have hj0 : 0 ≤ (j : ℝ) := by exact_mod_cast (Nat.zero_le j)
  have hji : |(j : ℝ) - (i : ℝ)| ≤ (M : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have h7ρ0 : 0 ≤ 7 * (ρ : ℝ) := mul_nonneg (by norm_num) (NNReal.coe_nonneg ρ)
  have h3σ0 : 0 ≤ 3 * (σ : ℝ) := mul_nonneg (by norm_num) (NNReal.coe_nonneg σ)
  have hα : |α| ≤ 1 / (4 * (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ)) := by
    rw [hc]
    calc
      |α| = 7 * (ρ : ℝ) * |(j : ℝ) - (i : ℝ)| := by
        simp [α, abs_mul, abs_of_nonneg h7ρ0]
      _ ≤ 7 * (ρ : ℝ) * (M : ℝ) := by
        exact mul_le_mul_of_nonneg_left hji h7ρ0
      _ ≤ 1 / 12 := hax
  have hdiff : base σ ρ j - (base σ ρ i + α • e₁) =
      (3 * (σ : ℝ) * ((j : ℝ) - (i : ℝ))) • e₂ := by
    dsimp [base, axial, trans, α]
    module
  have hdiff' : base σ ρ j + e₁ - (base σ ρ i + e₁ + α • e₁) =
      (3 * (σ : ℝ) * ((j : ℝ) - (i : ℝ))) • e₂ := by
    dsimp [base, axial, trans, α]
    module
  have hnorm : ‖(3 * (σ : ℝ) * ((j : ℝ) - (i : ℝ))) • e₂‖ ≤ 1 / 12 * (ρ : ℝ) := by
    calc
      ‖(3 * (σ : ℝ) * ((j : ℝ) - (i : ℝ))) • e₂‖
          = |3 * (σ : ℝ) * ((j : ℝ) - (i : ℝ))| * ‖e₂‖ := by
            simp [norm_smul]
      _ = 3 * (σ : ℝ) * |(j : ℝ) - (i : ℝ)| := by
        rw [norm_e₂, mul_one, abs_mul, abs_of_nonneg h3σ0]
      _ ≤ 3 * (σ : ℝ) * (M : ℝ) := by
        exact mul_le_mul_of_nonneg_left hji h3σ0
      _ ≤ (ρ : ℝ) / 12 := htr
      _ = 1 / 12 * (ρ : ℝ) := by ring
  have hp : dist (parent σ ρ j).x ((parent σ ρ i).x + α • (parent σ ρ i).direction)
      ≤ 1 / (4 * (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ)) * (ρ : ℝ) := by
    rw [hc]
    simp [parent_direction]
    rw [dist_eq_norm]
    rw [hdiff]
    simpa [one_div] using hnorm
  have hq : dist (parent σ ρ j).y ((parent σ ρ i).y + α • (parent σ ρ i).direction)
      ≤ 1 / (4 * (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ)) * (ρ : ℝ) := by
    rw [hc]
    simp [parent_direction]
    rw [dist_eq_norm]
    rw [hdiff']
    simpa [one_div] using hnorm
  exact Tube.not_essDistinct_of_axial_slide (E := EuclideanSpace ℝ (Fin 3)) (σ := ρ) hρ0 hρ1
    (parent σ ρ i) (parent σ ρ j) (α := α) hα hp hq

/-- **No `ρ`-tube contains two leaves of the pencil.**

A `Kakeya.Tube` has a core of length exactly `1`, so by
`Kakeya.Tube.endpoints_close_of_body_le` a leaf contained in the `ρ`-tube `W` has its endpoints
within `3 ρ` of the endpoints of `W`, in one of the two orientations.  Comparing
`e₁`-coordinates, two leaves in a common `W` have `7 ρ |i - j| ≤ 6 ρ` in the aligned cases, and
force `1 ≤ 6 ρ` in the crossed ones. -/
theorem eq_of_le_common {σ ρ : NNReal} (hρ0 : 0 < ρ) (hρ : (ρ : ℝ) ≤ 1 / 128)
    (W : Tube ρ (EuclideanSpace ℝ (Fin 3))) {i j : ℕ}
    (hi : (leaf σ ρ i).toConvexSpaceBody ≤ W.toConvexSpaceBody)
    (hj : (leaf σ ρ j).toConvexSpaceBody ≤ W.toConvexSpaceBody) :
    i = j := by
  let E := EuclideanSpace ℝ (Fin 3)
  let u : ℝ := inner ℝ W.x e₁
  let v : ℝ := inner ℝ W.y e₁
  let A : ℝ := axial ρ i
  let B : ℝ := axial ρ j
  have hinX (k : ℕ) : (inner ℝ ((leaf σ ρ k).x) e₁ : ℝ) = axial ρ k := by
    rw [leaf_x, inner_base_e₁]
  have hinY (k : ℕ) : (inner ℝ ((leaf σ ρ k).y) e₁ : ℝ) = axial ρ k + 1 := by
    rw [leaf_y, inner_add_left, inner_base_e₁, inner_e₁_e₁]
  have hproj (a b : E) : |(inner ℝ a e₁ : ℝ) - (inner ℝ b e₁ : ℝ)| ≤ ‖a - b‖ := by
    calc
      |(inner ℝ a e₁ : ℝ) - (inner ℝ b e₁ : ℝ)| = |(inner ℝ (a - b) e₁ : ℝ)| := by
        rw [← inner_sub_left]
      _ ≤ ‖a - b‖ * ‖e₁‖ := abs_real_inner_le_norm (a - b) e₁
      _ = ‖a - b‖ := by rw [norm_e₁, mul_one]
  have hxU (k : ℕ) : ‖(leaf σ ρ k).x - W.x‖ ≤ 3 * (ρ : ℝ) →
      |axial ρ k - u| ≤ 3 * (ρ : ℝ) := by
    intro hk
    calc
      |axial ρ k - u| =
          |(inner ℝ (leaf σ ρ k).x e₁ : ℝ) - (inner ℝ W.x e₁ : ℝ)| := by
            simp [u, ← hinX k]
      _ ≤ ‖(leaf σ ρ k).x - W.x‖ := hproj (leaf σ ρ k).x W.x
      _ ≤ 3 * (ρ : ℝ) := hk
  have hyU (k : ℕ) : ‖(leaf σ ρ k).y - W.x‖ ≤ 3 * (ρ : ℝ) →
      |axial ρ k + 1 - u| ≤ 3 * (ρ : ℝ) := by
    intro hk
    calc
      |axial ρ k + 1 - u| =
          |(inner ℝ (leaf σ ρ k).y e₁ : ℝ) - (inner ℝ W.x e₁ : ℝ)| := by
            simp [u, ← hinY k]
      _ ≤ ‖(leaf σ ρ k).y - W.x‖ := hproj (leaf σ ρ k).y W.x
      _ ≤ 3 * (ρ : ℝ) := hk
  have hxV (k : ℕ) : ‖(leaf σ ρ k).x - W.y‖ ≤ 3 * (ρ : ℝ) →
      |axial ρ k - v| ≤ 3 * (ρ : ℝ) := by
    intro hk
    calc
      |axial ρ k - v| =
          |(inner ℝ (leaf σ ρ k).x e₁ : ℝ) - (inner ℝ W.y e₁ : ℝ)| := by
            simp [v, ← hinX k]
      _ ≤ ‖(leaf σ ρ k).x - W.y‖ := hproj (leaf σ ρ k).x W.y
      _ ≤ 3 * (ρ : ℝ) := hk
  have hyV (k : ℕ) : ‖(leaf σ ρ k).y - W.y‖ ≤ 3 * (ρ : ℝ) →
      |axial ρ k + 1 - v| ≤ 3 * (ρ : ℝ) := by
    intro hk
    calc
      |axial ρ k + 1 - v| =
          |(inner ℝ (leaf σ ρ k).y e₁ : ℝ) - (inner ℝ W.y e₁ : ℝ)| := by
            simp [v, ← hinY k]
      _ ≤ ‖(leaf σ ρ k).y - W.y‖ := hproj (leaf σ ρ k).y W.y
      _ ≤ 3 * (ρ : ℝ) := hk
  have hgap (w : ℝ) (ha : |A - w| ≤ 3 * (ρ : ℝ)) (hb : |B - w| ≤ 3 * (ρ : ℝ)) : i = j := by
    have htri : |A - B| ≤ |A - w| + |w - B| := by
      calc
        |A - B| = |(A - w) + (w - B)| := congrArg abs (by ring)
        _ ≤ |A - w| + |w - B| := abs_add_le (A - w) (w - B)
    have hAB : |A - B| ≤ 6 * (ρ : ℝ) := by
      have hconv : |w - B| = |B - w| := abs_sub_comm w B
      calc
        |A - B| ≤ |A - w| + |w - B| := htri
        _ ≤ 3 * (ρ : ℝ) + 3 * (ρ : ℝ) := by
          rw [hconv]
          exact add_le_add ha hb
        _ = 6 * (ρ : ℝ) := by ring
    have hABeq : A - B = 7 * (ρ : ℝ) * ((i : ℝ) - (j : ℝ)) := by
      dsimp [A, B, axial]
      ring
    have hnorm : |7 * (ρ : ℝ) * ((i : ℝ) - (j : ℝ))| ≤ 6 * (ρ : ℝ) := by
      rw [← hABeq]
      exact hAB
    have h7nn : 0 ≤ 7 * (ρ : ℝ) := by positivity
    have hb : |(i : ℝ) - (j : ℝ)| * (7 * (ρ : ℝ)) ≤ 6 * (ρ : ℝ) := by
      calc
        |(i : ℝ) - (j : ℝ)| * (7 * (ρ : ℝ)) =
            |7 * (ρ : ℝ) * ((i : ℝ) - (j : ℝ))| := by
              rw [abs_mul, abs_of_nonneg h7nn]
              ring
        _ ≤ 6 * (ρ : ℝ) := hnorm
    have hlt1 : |(i : ℝ) - (j : ℝ)| < 1 := by
      by_contra h1
      have hon : (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := le_of_not_gt h1
      have h7le : 7 * (ρ : ℝ) ≤ |(i : ℝ) - (j : ℝ)| * (7 * (ρ : ℝ)) := by
        simpa using mul_le_mul_of_nonneg_right hon h7nn
      have hbad : 7 * (ρ : ℝ) ≤ 6 * (ρ : ℝ) := le_trans h7le hb
      have hρgt : 0 < (ρ : ℝ) := by exact_mod_cast hρ0
      linarith
    by_contra hne
    have hsep' : (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by
      by_cases hlt : i < j
      · have hic : (i : ℝ) < (j : ℝ) := by exact_mod_cast hlt
        have hone : (1 : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
          have hi1 : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hlt)
          linarith
        rw [abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ (j : ℝ) - (i : ℝ))]
        exact hone
      · have hgt : j < i := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hne)
        have hjc : (j : ℝ) < (i : ℝ) := by exact_mod_cast hgt
        have hone : (1 : ℝ) ≤ (i : ℝ) - (j : ℝ) := by
          have hj1 : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hgt)
          linarith
        rw [abs_of_nonneg (by linarith : 0 ≤ (i : ℝ) - (j : ℝ))]
        exact hone
    linarith
  have hcross (h1 : |A - B - 1| ≤ 6 * (ρ : ℝ)) (h2 : |A - B + 1| ≤ 6 * (ρ : ℝ)) : False := by
    have ha : 1 - 6 * (ρ : ℝ) ≤ A - B := by
      have habs := abs_le.mp h1
      linarith
    have hb : A - B ≤ -1 + 6 * (ρ : ℝ) := by
      have habs := abs_le.mp h2
      linarith
    have hcc : (2 : ℝ) ≤ 12 * (ρ : ℝ) := by linarith
    nlinarith [hcc, hρ]
  have hc1 (w : ℝ) (hw1 : |A - w| ≤ 3 * (ρ : ℝ)) (hw2 : |B + 1 - w| ≤ 3 * (ρ : ℝ)) :
      |A - B - 1| ≤ 6 * (ρ : ℝ) := by
    calc
      |A - B - 1| ≤ |A - w| + |w - (B + 1)| := by
        calc
          |A - B - 1| = |(A - w) + (w - (B + 1))| := congrArg abs (by ring)
          _ ≤ |A - w| + |w - (B + 1)| := abs_add_le (A - w) (w - (B + 1))
      _ ≤ 3 * (ρ : ℝ) + 3 * (ρ : ℝ) := by
        have hconv : |w - (B + 1)| = |(B + 1) - w| := abs_sub_comm w (B + 1)
        rw [hconv]
        exact add_le_add hw1 hw2
      _ = 6 * (ρ : ℝ) := by ring
  have hc2 (w : ℝ) (hw1 : |A + 1 - w| ≤ 3 * (ρ : ℝ)) (hw2 : |B - w| ≤ 3 * (ρ : ℝ)) :
      |A - B + 1| ≤ 6 * (ρ : ℝ) := by
    calc
      |A - B + 1| ≤ |A + 1 - w| + |w - B| := by
        calc
          |A - B + 1| = |(A + 1 - w) + (w - B)| := congrArg abs (by ring)
          _ ≤ |A + 1 - w| + |w - B| := abs_add_le (A + 1 - w) (w - B)
      _ ≤ 3 * (ρ : ℝ) + 3 * (ρ : ℝ) := by
        have hconv : |w - B| = |B - w| := abs_sub_comm w B
        rw [hconv]
        exact add_le_add hw1 hw2
      _ = 6 * (ρ : ℝ) := by ring
  have hor_i := Tube.endpoints_close_of_body_le (leaf σ ρ i) W hi
  have hor_j := Tube.endpoints_close_of_body_le (leaf σ ρ j) W hj
  rcases hor_i with hi_al | hi_cr
  · rcases hor_j with hj_al | hj_cr
    · rcases hi_al with ⟨hix, hiy⟩
      rcases hj_al with ⟨hjx, hjy⟩
      exact hgap u (hxU i hix) (hxU j hjx)
    · rcases hi_al with ⟨hix, hiy⟩
      rcases hj_cr with ⟨hjx, hjy⟩
      exact False.elim
        (hcross (hc1 u (hxU i hix) (hyU j hjy)) (hc2 v (hyV i hiy) (hxV j hjx)))
  · rcases hor_j with hj_al | hj_cr
    · rcases hi_cr with ⟨hix, hiy⟩
      rcases hj_al with ⟨hjx, hjy⟩
      exact False.elim
        (hcross (hc1 v (hxV i hix) (hyV j hjy)) (hc2 u (hyU i hiy) (hxU j hjx)))
    · rcases hi_cr with ⟨hix, hiy⟩
      rcases hj_cr with ⟨hjx, hjy⟩
      exact hgap v (hxV i hix) (hxV j hjx)

/-- **A leaf of the pencil lies in no parent but its own.**  This is
`Kakeya.ml1Boot.essDistinctCex.eq_of_le_common` at `W = parent σ ρ j`, which contains the `j`-th
leaf by `Kakeya.Tube.le_rescale`. -/
theorem eq_of_le_parent {σ ρ : NNReal} (hσρ : σ ≤ ρ) (hρ0 : 0 < ρ) (hρ : (ρ : ℝ) ≤ 1 / 128)
    {i j : ℕ} (hij : (leaf σ ρ i).toConvexSpaceBody ≤ (parent σ ρ j).toConvexSpaceBody) :
    i = j := by
  apply eq_of_le_common hρ0 hρ (parent σ ρ j) hij
  simpa [parent] using Tube.le_rescale (leaf σ ρ j) hσρ

/-- **The pencil has overlap bounded by `1`.**  For a `ρ`-tube `W`, a parent counted at `W` owns a
leaf that lies both in it and in `W`; the leaf determines the parent
(`Kakeya.ml1Boot.essDistinctCex.eq_of_le_parent`) and `W` determines the leaf
(`Kakeya.ml1Boot.essDistinctCex.eq_of_le_common`), so at most one parent is counted. -/
theorem hasBoundedOverlap {σ ρ : NNReal} (hσρ : σ ≤ ρ) (hρ0 : 0 < ρ) (hρ : (ρ : ℝ) ≤ 1 / 128)
    (s t : Finset ℕ) :
    Tube.HasBoundedOverlap s (leaf σ ρ) t (parent σ ρ) 1 := by
  classical
  intro W
  have hcard : (t.filter (fun k => ∃ i ∈ s,
      (leaf σ ρ i).toConvexSpaceBody ≤ (parent σ ρ k).toConvexSpaceBody ∧
      (leaf σ ρ i).toConvexSpaceBody ≤ W.toConvexSpaceBody)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro k hk k' hk'
    rcases Finset.mem_filter.mp hk with ⟨_, ⟨i, ⟨hi_s, ⟨hik, hiW⟩⟩⟩⟩
    rcases Finset.mem_filter.mp hk' with ⟨_, ⟨i', ⟨hi'_s, ⟨hi'k', hi'W⟩⟩⟩⟩
    have hpi : i = k := eq_of_le_parent hσρ hρ0 hρ hik
    have hpi' : i' = k' := eq_of_le_parent hσρ hρ0 hρ hi'k'
    have hii' : i = i' := eq_of_le_common hρ0 hρ W hiW hi'W
    calc
      k = i := hpi.symm
      _ = i' := hii'
      _ = k' := hpi'
  exact_mod_cast hcard

/-- **The pencil is a parent family for itself along the identity.**  Injectivity of the parents is
`Kakeya.ml1Boot.essDistinctCex.eq_of_le_parent` again, and the containment clause is
`Kakeya.Tube.le_rescale`. -/
theorem isParentFamily {σ ρ : NNReal} (hσρ : σ ≤ ρ) (hρ0 : 0 < ρ) (hρ : (ρ : ℝ) ≤ 1 / 128)
    (s : Finset ℕ) :
    IsParentFamily s (leaf σ ρ) s (parent σ ρ) id := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact hi
  · intro k hk k' hk' h
    apply eq_of_le_parent hσρ hρ0 hρ
    calc
      (leaf σ ρ k).toConvexSpaceBody ≤ (parent σ ρ k).toConvexSpaceBody :=
        Tube.le_rescale (leaf σ ρ k) hσρ
      _ = (parent σ ρ k').toConvexSpaceBody := h
  · intro i hi
    exact Tube.le_rescale (leaf σ ρ i) hσρ

/-- **A family with empty shadings is shaded-uniform as soon as its tubes are uniform.**  All four
shading clauses of `ShadedTube.ShadedUniformTubeSet` are quantified over the points of
`⋃ i ∈ s, (V i).shade`, so they are vacuous. -/
noncomputable def shadedUniformTubeSet_of_shade_empty {σ : NNReal} {ι : Type*} {s : Finset ι}
    (V : ι → ShadedTube σ (EuclideanSpace ℝ (Fin 3))) (hshade : ∀ i, (V i).shade = ∅)
    {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s (fun i => (V i).toTube) N C) :
    ShadedTube.ShadedUniformTubeSet s V N C where
  tubeUniform := 𝒰
  branchingN := fun _ => 0
  localN := fun _ _ => 0
  card_shadeClass_le := by
    intro x hx
    simp [hshade] at hx
  le_card_shadeClass := by
    intro x hx
    simp [hshade] at hx
  branchingN_le := by
    intro x hx
    simp [hshade] at hx
  le_branchingN := by
    intro x hx
    simp [hshade] at hx

/-! #### The scale sequence -/

/-- The leaf scale of the counterexample at stage `n`, which is also the auxiliary parameter `δ`:
`2 ^ (-8n)`. -/
noncomputable def leafScale (n : ℕ) : NNReal := (1 / 2) ^ (8 * n)

/-- The parent scale of the counterexample at stage `n`: `2 ^ (-(2n+9))`, of order the square root
of the leaf scale, which is what maximizes the length of the axial pencil. -/
noncomputable def parentScale (n : ℕ) : NNReal := (1 / 2) ^ (2 * n + 9)

/-- The length of the axial pencil at stage `n`: `2 ^ (2n+1) ≍ (leafScale n) ^ (-1/4)`. -/
def count (n : ℕ) : ℕ := 2 ^ (2 * n + 1)

theorem leafScale_pos (n : ℕ) : 0 < leafScale n := by
  unfold leafScale
  exact pow_pos (by norm_num : (0 : NNReal) < 1 / 2) _

theorem parentScale_pos (n : ℕ) : 0 < parentScale n := by
  unfold parentScale
  exact pow_pos (by norm_num : (0 : NNReal) < 1 / 2) _

theorem leafScale_le_parentScale {n : ℕ} (hn : 2 ≤ n) : leafScale n ≤ parentScale n := by
  unfold leafScale parentScale
  exact pow_le_pow_of_le_one (by norm_num : (0 : NNReal) ≤ 1 / 2)
    (by norm_num : (1 / 2 : NNReal) ≤ 1) (by omega : 2 * n + 9 ≤ 8 * n)

theorem parentScale_le_inv128 (n : ℕ) : (parentScale n : ℝ) ≤ 1 / 128 := by
  unfold parentScale
  rw [NNReal.coe_pow]
  calc
    ((1 / 2 : NNReal) ^ (2 * n + 9) : ℝ) = (1 / 2 : ℝ) ^ (2 * n + 9) := by norm_num
    _ ≤ (1 / 2 : ℝ) ^ 7 :=
      pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (by omega : 7 ≤ 2 * n + 9)
    _ ≤ 1 / 128 := by norm_num

theorem parentScale_le_one (n : ℕ) : parentScale n ≤ 1 := by
  unfold parentScale
  exact pow_le_one₀ (by norm_num : (0 : NNReal) ≤ 1 / 2) (by norm_num : (1 / 2 : NNReal) ≤ 1)

theorem axial_bound (n : ℕ) : 7 * (parentScale n : ℝ) * (count n) ≤ 1 / 12 := by
  rw [parentScale, count]
  rw [NNReal.coe_pow]
  norm_num
  have hsplit : 2 * n + 9 = (2 * n + 1) + 8 := by omega
  have hmul : (1 / 2 : ℝ) ^ (2 * n + 1) * (2 : ℝ) ^ (2 * n + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    7 * (1 / 2 : ℝ) ^ (2 * n + 9) * (2 : ℝ) ^ (2 * n + 1)
        = 7 * (1 / 2 : ℝ) ^ 8 := by
          rw [hsplit, pow_add]
          rw [show 7 * ((1 / 2 : ℝ) ^ (2 * n + 1) * (1 / 2 : ℝ) ^ 8) * (2 : ℝ) ^ (2 * n + 1)
              = 7 * (1 / 2 : ℝ) ^ 8 * ((1 / 2 : ℝ) ^ (2 * n + 1) * (2 : ℝ) ^ (2 * n + 1))
            by ring]
          rw [hmul]
          ring
    _ ≤ 1 / 12 := by norm_num

theorem trans_bound {n : ℕ} (hn : 5 ≤ n) :
    3 * (leafScale n : ℝ) * (count n) ≤ (parentScale n : ℝ) / 12 := by
  rw [leafScale, parentScale, count]
  rw [NNReal.coe_pow, NNReal.coe_pow]
  norm_num
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]
  field_simp
  ring_nf
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]
  field_simp
  have hbig : (36864 : ℝ) ≤ (2 : ℝ) ^ (4 * n) := by
    have h : (2 : ℝ) ^ 20 ≤ (2 : ℝ) ^ (4 * n) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 20 ≤ 4 * n)
    exact (by norm_num : (36864 : ℝ) ≤ (2 : ℝ) ^ 20).trans h
  have hL : ((2 : ℝ) ^ (n * 2)) ^ 2 * 72 * 512 = 36864 * (2 : ℝ) ^ (4 * n) := by
    ring_nf
  have hR : (2 : ℝ) ^ (n * 8) = (2 : ℝ) ^ (4 * n) * (2 : ℝ) ^ (4 * n) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hL, hR]
  exact mul_le_mul_of_nonneg_right hbig (by positivity)

theorem trans_bound_inv12 {n : ℕ} (hn : 5 ≤ n) :
    3 * (leafScale n : ℝ) * (count n) ≤ 1 / 12 := by
  rw [leafScale, count]
  rw [NNReal.coe_pow]
  norm_num
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]
  field_simp
  ring_nf
  have hbig : (72 : ℝ) ≤ (2 : ℝ)^(6 * n) := by
    have h : (2 : ℝ)^7 ≤ (2 : ℝ)^(6*n) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 7 ≤ 6*n)
    exact (by norm_num : (72 : ℝ) ≤ (2 : ℝ)^7).trans h
  rw [show (2 : ℝ)^(n*2) = (2 : ℝ)^(2*n) by congr 1; omega]
  rw [show (2 : ℝ)^(n*8) = (2 : ℝ)^(2*n) * (2 : ℝ)^(6*n) by
    rw [← pow_add]; congr 1; omega]
  nlinarith [hbig, (show (0 : ℝ) ≤ (2 : ℝ)^(2*n) by positivity)]

theorem count_le_leafScale_inv {n : ℕ} (hn : 1 ≤ n) :
    ((count n : ℝ)) ≤ (leafScale n : ℝ) ^ (-(1 : ℕ) : ℝ) := by
  unfold count leafScale
  rw [NNReal.coe_pow]
  norm_num
  rw [Real.rpow_neg_one, show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow, inv_inv]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 2 * n + 1 ≤ 8 * n)

/-- **The scale sequence reaches into every punctured neighbourhood of `0`.**  So a property
holding eventually along `𝓝[>] 0` holds at `leafScale n` for arbitrarily large `n`, and below any
prescribed threshold. -/
theorem exists_stage {p : NNReal → Prop} (h : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, p δ)
    (n₀ : ℕ) {c : NNReal} (hc : 0 < c) :
    ∃ n : ℕ, n₀ ≤ n ∧ leafScale n ≤ c ∧ p (leafScale n) := by
  have htend0 : Tendsto leafScale atTop (𝓝 (0 : NNReal)) := by
    have hpow := NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (r := (1 / 2 : NNReal) ^ 8) (by norm_num : (1 / 2 : NNReal) ^ 8 < 1)
    exact hpow.congr' (by
      filter_upwards with n
      unfold leafScale
      rw [pow_mul])
  have hwithin : ∀ᶠ n in atTop, (0 : NNReal) < leafScale n := by
    filter_upwards with n
    exact leafScale_pos n
  have hlt : ∀ᶠ n in atTop, leafScale n < c :=
    htend0.eventually_lt (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)) hc
  have hle : ∀ᶠ n in atTop, leafScale n ≤ c := hlt.mono fun n hn => le_of_lt hn
  have htend : Tendsto leafScale atTop (𝓝[>] (0 : NNReal)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within leafScale htend0 hwithin
  have hp : ∀ᶠ n in atTop, p (leafScale n) := htend.eventually h
  have hge : ∀ᶠ n in atTop, n₀ ≤ n := eventually_ge_atTop n₀
  have hall : ∀ᶠ n in atTop, n₀ ≤ n ∧ leafScale n ≤ c ∧ p (leafScale n) := by
    filter_upwards [hge, hle, hp] with n hn₀ hnle hnδ
    exact ⟨hn₀, hnle, hnδ⟩
  exact hall.exists

/-! #### The two halves of the contradiction -/

/-- **Any essentially distinct subfamily of the pencil retains at most one leaf.**

The parents pairwise fail to be essentially distinct, so a pairwise essentially distinct
`t' ⊆ t` has at most one element; and `Kakeya.ml1Boot.IsParentFamily.mapsTo` along the identity
puts `s'` inside `t'`. -/
theorem card_le_one {σ ρ : NNReal} {M : ℕ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hax : 7 * (ρ : ℝ) * M ≤ 1 / 12) (htr : 3 * (σ : ℝ) * M ≤ (ρ : ℝ) / 12)
    {s' t' : Finset ℕ} (ht' : t' ⊆ Finset.range M)
    (hpf : IsParentFamily s' (leaf σ ρ) t' (parent σ ρ) id)
    (hed : (t' : Set ℕ).Pairwise
      (fun k l => IsEssentiallyDistinct (parent σ ρ k).carrier (parent σ ρ l).carrier)) :
    s'.card ≤ 1 := by
  have ht'card : t'.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro k hk l hl
    by_contra hne
    have hkM : k ≤ M := le_of_lt (Finset.mem_range.mp (ht' hk))
    have hlM : l ≤ M := le_of_lt (Finset.mem_range.mp (ht' hl))
    exact (not_isEssentiallyDistinct_parent hρ0 hρ1 hax htr hkM hlM) (hed hk hl hne)
  have hsub : s' ⊆ t' := by
    intro i hi
    simpa using hpf.mapsTo i hi
  exact le_trans (Finset.card_le_card hsub) ht'card

/-- **The arithmetic of the two losses.**  The uniformization costs `leafScale n ^ ε'` and the
asserted retention costs `leafScale n ^ ε'` again, while the pencil has `count n` leaves; for
`ε' ≤ 1/8` the product `leafScale n ^ (2 ε') * count n ≥ 2` exceeds the `1` that the retention
clause allows.

The stage bound `5 ≤ n` is carried so that this reads as a statement about the stages the
counterexample actually uses; it is not needed, the estimate holding at every stage. -/
theorem absurd_of_retention {ε' : ℝ} (hε'0 : 0 < ε') (hε'8 : ε' ≤ 1 / 8) {n : ℕ} (_hn : 5 ≤ n)
    {c : ℕ}
    (hcard : ((count n : ℝ)) ≤ (leafScale n : ℝ) ^ (-ε') * (c : ℝ))
    (hret : ((leafScale n : ENNReal)) ^ ε' * (c : ENNReal) ≤ 1) :
    False := by
  have hℓ : (leafScale n : ℝ) = (1 / 2 : ℝ) ^ (8 * n) := by
    unfold leafScale
    rw [NNReal.coe_pow]
    norm_num
  have hL0 : (0 : ℝ) < (leafScale n : ℝ) := by
    rw [hℓ]
    exact pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _
  have hL1 : (leafScale n : ℝ) ≤ 1 := by
    rw [hℓ]
    exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hretNN : (leafScale n ^ ε' * (c : NNReal) : NNReal) ≤ 1 := by
    have hfinite : (1 : ENNReal) ≠ ⊤ := by simp
    have h := ENNReal.toNNReal_mono hfinite hret
    simpa using h
  have hretR : (leafScale n : ℝ) ^ ε' * (c : ℝ) ≤ 1 := by
    exact_mod_cast hretNN
  have hrpowpos : 0 < (leafScale n : ℝ) ^ ε' := Real.rpow_pos_of_pos hL0 ε'
  have hstep1 : (leafScale n : ℝ) ^ ε' * (count n : ℝ) ≤ (c : ℝ) := by
    calc
      (leafScale n : ℝ) ^ ε' * (count n : ℝ)
          ≤ (leafScale n : ℝ) ^ ε' * ((leafScale n : ℝ) ^ (-ε') * (c : ℝ)) :=
            mul_le_mul_of_nonneg_left hcard (le_of_lt hrpowpos)
      _ = (c : ℝ) := by
        rw [← mul_assoc]
        have hm : (leafScale n : ℝ) ^ ε' * (leafScale n : ℝ) ^ (-ε') = 1 := by
          rw [← Real.rpow_add hL0]
          have hz : ε' + -ε' = (0 : ℝ) := by ring
          rw [hz, Real.rpow_zero]
        rw [hm]
        ring
  have hsq : (leafScale n : ℝ) ^ ε' * (leafScale n : ℝ) ^ ε' =
      (leafScale n : ℝ) ^ (2 * ε') := by
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  have hstep2 : (leafScale n : ℝ) ^ (2 * ε') * (count n : ℝ)
      ≤ (leafScale n : ℝ) ^ ε' * (c : ℝ) := by
    calc
      (leafScale n : ℝ) ^ (2 * ε') * (count n : ℝ)
          = (leafScale n : ℝ) ^ ε' * ((leafScale n : ℝ) ^ ε' * (count n : ℝ)) := by
            rw [← hsq]
            ring
      _ ≤ (leafScale n : ℝ) ^ ε' * (c : ℝ) :=
            mul_le_mul_of_nonneg_left hstep1 (le_of_lt hrpowpos)
  have hcomb : (leafScale n : ℝ) ^ (2 * ε') * (count n : ℝ) ≤ 1 :=
    le_trans hstep2 hretR
  have hlow : (leafScale n : ℝ) ^ (1 / 4 : ℝ) ≤ (leafScale n : ℝ) ^ (2 * ε') := by
    exact Real.rpow_le_rpow_of_exponent_ge hL0 hL1 (by linarith)
  have hqpow : (leafScale n : ℝ) ^ (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ (2 * n : ℕ) := by
    rw [hℓ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [show (((8 * n : ℕ) : ℝ) * (1 / 4 : ℝ)) = ((2 * n : ℕ) : ℝ) by
      calc
        ((8 * n : ℕ) : ℝ) * (1 / 4 : ℝ) = (8 : ℝ) * (n : ℝ) * (1 / 4) := by
          rw [Nat.cast_mul]
          norm_num
        _ = (2 : ℝ) * (n : ℝ) := by ring
        _ = ((2 * n : ℕ) : ℝ) := by
          rw [Nat.cast_mul]
          norm_num]
    rw [Real.rpow_natCast]
  have hq : (leafScale n : ℝ) ^ (1 / 4 : ℝ) * (count n : ℝ) = (2 : ℝ) := by
    rw [hqpow]
    have hcountR : (count n : ℝ) = (2 : ℝ) ^ (2 * n + 1 : ℕ) := by
      unfold count
      norm_cast
    rw [hcountR]
    have hsplit : (2 : ℝ) ^ (2 * n + 1 : ℕ) = (2 : ℝ) ^ (2 * n : ℕ) * (2 : ℝ) := by
      rw [pow_succ]
    rw [hsplit, ← mul_assoc]
    have hmul : (1 / 2 : ℝ) ^ (2 * n : ℕ) * (2 : ℝ) ^ (2 * n : ℕ) = 1 := by
      rw [← mul_pow]
      norm_num
    rw [hmul]
    norm_num
  have hcount_nonneg : (0 : ℝ) ≤ (count n : ℝ) := by positivity
  have hbig : (2 : ℝ) ≤ 1 := by
    calc
      (2 : ℝ) = (leafScale n : ℝ) ^ (1 / 4 : ℝ) * (count n : ℝ) := by rw [hq]
      _ ≤ (leafScale n : ℝ) ^ (2 * ε') * (count n : ℝ) :=
            mul_le_mul_of_nonneg_right hlow hcount_nonneg
      _ ≤ 1 := hcomb
  linarith

end essDistinctCex

/-- **(negative result) The scale-free form of `Kakeya.ml1Boot.exists_essDistinct_parentFamily` is
false.**

*What this does and does not now bite.*  The proposition refuted here is the one obtained from
`Kakeya.ml1Boot.exists_essDistinct_parentFamily` by **deleting its scale hypothesis**
`δ ^ ε' ≤ c ρ / Co` — that is, the form that declaration had before the repair.  It does **not**
refute the current declaration, and the two statements can be compared side by side to see it:
the pencil below runs at `ρ = 2 ^ (-(2n+9))` and `δ = σ = 2 ^ (-8n)` with `ε' ≤ 1/8`, so
`δ ^ ε' ≥ 2 ^ (-n)` while `c ρ / Co ≤ c · 2 ^ (-(2n+9))`, and for every fixed `c > 0` the scale
hypothesis fails at all large `n`; the refutation draws its witness from arbitrarily large `n`
(`Kakeya.ml1Boot.essDistinctCex.exists_stage`), so it has no stage left to work with once that
hypothesis is in force.  This is retained, and must be, as the record of why the scale hypothesis
is in the signature: without it the positive statement is false, and this proves so.

The statement is spelled out inline rather than cited, so that this refutation survives any
reshaping of the declaration it refutes; what is spelled out is the pre-repair statement of that
declaration at `E = EuclideanSpace ℝ (Fin 3)` (where its hypothesis `hdim` is discharged), at
`ι = κ = ℕ`, with the **fourth conclusion clause discarded**.  Discarding a conclusion clause makes the refuted
proposition strictly weaker, so this refutes the fibrewise-Frostman clause too; the hypotheses are
kept in full, and the two constants are quantified upwards, so no enlargement of `Cunif` or of
`Co` repairs it.

## The counterexample

An *axial pencil* of `M = 2 ^ (2n+1)` leaves at scale `σ = 2 ^ (-8n)` under `M` parents at scale
`ρ = 2 ^ (-(2n+9))`; see the section docstring above and
`Kakeya.ml1Boot.essDistinctCex.leaf`.  All the hypotheses hold:

* `Kakeya.ml1Boot.essDistinctCex.isEssentiallyDistinct_leaf` — the leaves are pairwise disjoint;
* `Kakeya.ml1Boot.essDistinctCex.isParentFamily`,
  `Kakeya.ml1Boot.essDistinctCex.hasBoundedOverlap` — a parent family with `Co = 1`, the
  sharpest value the hypothesis permits;
* `Kakeya.ml1Boot.essDistinctCex.leaf_carrier_subset_ball` — containment in `B₁`;
* uniformity, from `Kakeya.Tube.exists_uniformTubeSet_subfamily_ssf` on a subfamily of
  `σ ^ (-ε')`-comparable cardinality, made shaded-uniform by
  `Kakeya.ml1Boot.essDistinctCex.shadedUniformTubeSet_of_shade_empty`.

But the parents pairwise fail to be essentially distinct
(`Kakeya.ml1Boot.essDistinctCex.not_isEssentiallyDistinct_parent`), so every pairwise essentially
distinct `t' ⊆ t` is a singleton and the retained index set is a singleton
(`Kakeya.ml1Boot.essDistinctCex.card_le_one`), whereas at `w = 1` the retention clause asks for
`δ ^ ε'` of `M ≍ δ ^ (-1/4)` leaves.

## What this says about the hypothesis `hoverlap`

`Kakeya.Tube.HasBoundedOverlap` is satisfied here at `Co = 1`, so the loss cannot be a function of
`Co` and `ε'` alone.  The pencil has `M ≍ ρ ⁻¹` members and that is sharp: bounded overlap
identifies two parents only when they share a leaf, and along the axial direction — the one tube
parameter that essential distinctness does not separate, cf.
`Kakeya/DimensionThree/BoundedOverlapCount.lean` and its `ρ ^ (-5)` against the `ρ ^ (-4)` of
`Kakeya.ml1Boot.card_le` — a `ρ`-tube pins its contents only to within `3 ρ`.  So the honest
retention factor of a greedy essentially distinct selection is `c ρ / Co` and not `δ ^ ε'`, and the
statement becomes true once `δ ^ ε' ≤ c ρ / Co` is assumed.  That hypothesis is now in the
signature of `Kakeya.ml1Boot.exists_essDistinct_parentFamily`, and it was threaded through
`Kakeya.ml1Boot.exists_repairEssDistinct` at the same time, the two being one change; see the
former's docstring for the constant and for the threading. -/
theorem not_exists_essDistinct_parentFamily {ε' : ℝ} (hε'0 : 0 < ε') (hε'8 : ε' ≤ 1 / 8)
    {Cunif : NNReal} (hCunif : Tube.uniformConst 3 ≤ Cunif)
    {Co : NNReal} (hCo : 1 ≤ Co) :
    ¬ ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ σ ρ : NNReal, δ ≤ σ → σ ≤ ρ → ρ ≤ 1 →
        ∀ {s t : Finset ℕ}
          (V : ℕ → ShadedTube σ (EuclideanSpace ℝ (Fin 3)))
          (Vρ : ℕ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (p : ℕ → ℕ) (w : ℕ → ENNReal),
          s.Nonempty →
          ShadedTube.ShadedUniformTubeSet s V (Tube.ssfGridLen σ) Cunif →
          (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
          (s : Set ℕ).Pairwise
            (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) →
          IsParentFamily s (fun i => (V i).toTube) t Vρ p →
          HasBoundedOverlap s (fun i => (V i).toTube) t Vρ Co →
          ∃ s' ⊆ s, ∃ t' ⊆ t,
            IsParentFamily s' (fun i => (V i).toTube) t' Vρ p ∧
            (t' : Set ℕ).Pairwise
              (fun k l => IsEssentiallyDistinct (Vρ k).carrier (Vρ l).carrier) ∧
            (δ : ENNReal) ^ ε' * (∑ i ∈ s, w i) ≤ ∑ i ∈ s', w i := by
  intro hE
  obtain ⟨δ₀, hδ₀pos, _hδ₀le1, huni⟩ :=
    Tube.exists_uniformTubeSet_subfamily_ssf (E := EuclideanSpace ℝ (Fin 3)) 1 ε' hε'0
  obtain ⟨n, hn5, hnδ₀, hP⟩ := essDistinctCex.exists_stage hE 5 hδ₀pos
  let σ : NNReal := essDistinctCex.leafScale n
  let ρ : NNReal := essDistinctCex.parentScale n
  let M : ℕ := essDistinctCex.count n
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hσ0 : 0 < σ := by simpa [σ] using essDistinctCex.leafScale_pos n
  have hρ0 : 0 < ρ := by simpa [ρ] using essDistinctCex.parentScale_pos n
  have hσρ : σ ≤ ρ := by
    simpa [σ, ρ] using essDistinctCex.leafScale_le_parentScale hn2
  have hρ1 : ρ ≤ 1 := by
    simpa [ρ] using essDistinctCex.parentScale_le_one n
  have hρinv : (ρ : ℝ) ≤ 1 / 128 := by
    simpa [ρ] using essDistinctCex.parentScale_le_inv128 n
  have hball : ∀ i ∈ Finset.range M, (essDistinctCex.leaf σ ρ i).carrier ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro i hi
    exact essDistinctCex.leaf_carrier_subset_ball hσρ
      (essDistinctCex.parentScale_le_inv128 n) (essDistinctCex.axial_bound n)
      (essDistinctCex.trans_bound_inv12 hn5) (le_of_lt (Finset.mem_range.mp hi))
  have hcardHyp : ((Finset.range M).card : ℝ) ≤ (σ : ℝ) ^ (-(1 : ℕ) : ℝ) := by
    rw [Finset.card_range]
    simpa [σ, M] using essDistinctCex.count_le_leafScale_inv hn1
  obtain ⟨s₁, hs₁sub, hcard, huni𝒰⟩ :=
    huni (δ := σ) (s := Finset.range M) (T := essDistinctCex.leaf σ ρ)
      hσ0 (by simpa [σ] using hnδ₀) hball hcardHyp
  rcases huni𝒰 with ⟨𝒰⟩
  have hUnif : ShadedTube.ShadedUniformTubeSet s₁ (essDistinctCex.shadedLeaf σ ρ)
      (Tube.ssfGridLen σ) Cunif := by
    have hU0 : Tube.UniformTubeSet s₁ (fun i => (essDistinctCex.shadedLeaf σ ρ i).toTube)
        (Tube.ssfGridLen σ) (Tube.uniformConst 3) := by
      simpa using 𝒰
    exact (essDistinctCex.shadedUniformTubeSet_of_shade_empty
      (essDistinctCex.shadedLeaf σ ρ) (fun i => rfl) hU0).mono hCunif
  have hs₁ne : s₁.Nonempty := by
    rw [← Finset.card_pos]
    by_contra h
    have hc0 : s₁.card = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt h)
    have hbad : (M : ℝ) ≤ 0 := by
      calc
        (M : ℝ) = ((Finset.range M).card : ℕ) := by rw [Finset.card_range]
        _ ≤ (σ : ℝ) ^ (-ε') * (s₁.card : ℝ) := by simpa [Finset.card_range] using hcard
        _ = 0 := by rw [hc0]; simp
    have hMpos : (0 : ℝ) < (M : ℝ) := by
      dsimp [M]
      unfold essDistinctCex.count
      rw [Nat.cast_pow]
      exact pow_pos (by norm_num : (0 : ℝ) < 2) (2 * n + 1)
    nlinarith
  have hball_sh : ∀ i ∈ s₁, (essDistinctCex.shadedLeaf σ ρ i).carrier ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro i hi
    simpa using hball i (hs₁sub hi)
  have hED_sh : (s₁ : Set ℕ).Pairwise
      (fun i j => IsEssentiallyDistinct (essDistinctCex.shadedLeaf σ ρ i).carrier
        (essDistinctCex.shadedLeaf σ ρ j).carrier) := by
    intro i hi j hj hij
    simpa using essDistinctCex.isEssentiallyDistinct_leaf hσ0 hij
  have hpf_sh : IsParentFamily s₁ (fun i => (essDistinctCex.shadedLeaf σ ρ i).toTube)
      s₁ (essDistinctCex.parent σ ρ) id := by
    simpa using (essDistinctCex.isParentFamily hσρ hρ0 hρinv s₁)
  have hBo_sh : HasBoundedOverlap s₁ (fun i => (essDistinctCex.shadedLeaf σ ρ i).toTube)
      s₁ (essDistinctCex.parent σ ρ) Co := by
    rw [HasBoundedOverlap, Tube.HasBoundedOverlap]
    intro W
    exact le_trans (by simpa using (essDistinctCex.hasBoundedOverlap hσρ hρ0 hρinv s₁ s₁ W)) hCo
  obtain ⟨s', hs's₁, t', ht's₁, hpf', hedt', hret'⟩ :=
    hP σ ρ (le_rfl : σ ≤ σ) hσρ hρ1 (s := s₁) (t := s₁)
      (essDistinctCex.shadedLeaf σ ρ) (essDistinctCex.parent σ ρ) id (fun _ : ℕ => (1 : ENNReal))
      hs₁ne hUnif hball_sh hED_sh hpf_sh hBo_sh
  have ht'range : t' ⊆ Finset.range M := subset_trans ht's₁ hs₁sub
  have hpf_leaf : IsParentFamily s' (essDistinctCex.leaf σ ρ) t'
      (essDistinctCex.parent σ ρ) id := by
    simpa [essDistinctCex.shadedLeaf_toTube] using hpf'
  have hsc' : s'.card ≤ 1 :=
    essDistinctCex.card_le_one hρ0 hρ1 (essDistinctCex.axial_bound n)
      (essDistinctCex.trans_bound hn5) ht'range hpf_leaf hedt'
  have hret0 : (σ : ENNReal) ^ ε' * (s₁.card : ENNReal) ≤ (s'.card : ENNReal) := by
    simpa [Finset.sum_const, nsmul_eq_mul, mul_one] using hret'
  have hret1 : (σ : ENNReal) ^ ε' * (s₁.card : ENNReal) ≤ (1 : ENNReal) := by
    exact le_trans hret0 (by exact_mod_cast hsc')
  have hcard' : ((essDistinctCex.count n : ℝ) ≤
      (essDistinctCex.leafScale n : ℝ) ^ (-ε') * (s₁.card : ℝ)) := by
    simpa [σ, M, Finset.card_range] using hcard
  exact essDistinctCex.absurd_of_retention hε'0 hε'8 hn5 hcard' (by simpa [σ] using hret1)

/-- **The shade-mass reading of `Kakeya.ml1Boot.exists_essDistinct_parentFamily`** (blueprint
`lem:ml1bootEssDistinctParentsRefinement`).

Instantiating the weight parameter at `w i = volume (V i).shade` turns the retention clause into
`ShadedBody.IsCRefinement`, which is the form the shading side of the Case (ii) chain reads.
Nothing is proved here beyond the arithmetic of the two spellings: `ShadedBody.IsRefinement` is
free for a subfamily of the *same* shaded bodies, and the mass clause is
`ShadedBody.isCRefinement_of_sum_le`.

The counting reading needs no companion lemma: it is the same conclusion at `w = fun _ => 1`,
where `∑ i ∈ s, w i` is `s.card`. -/
theorem essDistinct_parentFamily_isCRefinement {σ : NNReal} {δ : NNReal} {ε' : ℝ}
    {ι : Type*} {s s' : Finset ι} (V : ι → ShadedTube σ E) (hsub : s' ⊆ s)
    (hδ0 : 0 < δ)
    (hmass : (δ : ENNReal) ^ ε' * (∑ i ∈ s, volume (V i).shade)
      ≤ ∑ i ∈ s', volume (V i).shade) :
    ShadedBody.IsCRefinement s' (fun i => (V i).toShadedBody) s
      (fun i => (V i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩ := by
  unfold ShadedBody.IsCRefinement ShadedBody.IsRefinement
  constructor
  · constructor
    · exact hsub
    · intro i hi
      constructor
      · rfl
      · exact subset_rfl
  · set c : NNReal := ⟨(δ : ℝ) ^ ε', by positivity⟩ with hc_def
    have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ0
    have hcoef : (c : ENNReal) = (δ : ENNReal) ^ ε' := by
      rw [hc_def]
      rw [ENNReal.ofReal_coe_nnreal.symm]
      exact (ennreal_coe_nnreal_rpow hδR ε').symm
    rw [hcoef]
    simpa using hmass

/-! ### Refining a shaded family to a uniform one -/

/-- **The raw uniformity constant of the shaded uniformization**.

`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` produces a uniformity constant `C_u`
which depends on the ambient dimension only and is quantified *before* the grid length and the
scale — the order matters, since Definition 2.2 is used at the `δ`-dependent grid length
`Tube.ssfGridLen δ`.

This was formerly `opaque`, and that was a design defect rather than a caution: an opaque
constant has no properties, so the one bridge between two uniformity constants,
`ShadedTube.ShadedUniformTubeSet.mono`, could never be applied.  Every uniformization the
development can actually run lands at `ShadedTube.ssfUniformConst`, so that is the value
committed to here, which makes the `mono` step disappear rather than become provable.  Nothing
reads this constant except through `Kakeya.ml1Boot.uniformize.C`, so no field and no consumer
changes shape.

It was never the project's only `opaque` declaration, and removing it did not leave the project
with none: `Kakeya.ml1Boot.factorOneScaleUniformDilate.CWitness` is still `opaque`, and
deliberately so — that one carries the two clauses asked of it in the *type* of the witness, so
it exposes properties even while committing to no value, which is exactly what this constant
did not do.

**What committing to this value settles, and what it does not.**  It was the only *executable* of
the two repairs blueprint `note:ml1bootUniformizeConstantOpaque` offers: the second is conditional
on the Section 2 interface being "later stated with its own constant", and that interface is not a
Lean declaration.  Taking the first strictly increased what is provable — while `rawC` was
`opaque` the one available fact was `Kakeya.ml1Boot.one_le_uniformize_C` — and it lands on the
constant the uniformity fields want: dimension-only, which is what lets the `Cunif` of
`Kakeya.ml1Boot.multiplicity_le_middle` be fixed before the `∀ᶠ δ in 𝓝[>] 0` (module docstring),
and equal to what `ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`
(Kakeya/ShadedUniform.lean:1075) produces, namely
`ShadedTube.ssfUniformConst (Module.finrank ℝ E)`.

What it does not settle is the demand of `fine_unif` and `coarse_unif` together.  (It used to be a
three-way demand, `fibreUnif` included; that field is now one-sided and free, and the route below
is no longer needed for it — see the docstring of `Kakeya.ml1Boot.exists_uniformFactorCore`.)  The
only route to simultaneous global-plus-fibrewise two-sided uniformity,
`Kakeya.exists_jointPartitionRegularization` (RelativePlank.lean:520), lands at a constant
depending on `#s` and unbounded as `δ → 0`, and `ShadedTube.ShadedUniformTubeSet.mono` weakens a
constant only upwards.  Restating the uniformity fields at a *quantified* constant is a defensible
change, but it is additive to the definition here rather
than a correction of it, and it is not what leaves
`Kakeya.ml1Boot.exists_uniformFactorCore` sorried; see that docstring's last two sections.  None
of this is a smallness question: the `16 ^ (-N)` separation the ambient hierarchy needs is
supplied for small `δ` by the fully proved
`Tube.exists_threshold_polylog_pow_ssfGridLen_le` (Kakeya/Uniform.lean:649). -/
def uniformize.rawC (n : ℕ) : NNReal := ShadedTube.ssfUniformConst n

/-- **The uniformity constant `C_{unif}(n) ≥ 1`** of the shaded uniformization: the raw constant
`Kakeya.ml1Boot.uniformize.rawC n`, enlarged to be at least `1`.

Enlarging a uniformity constant only weakens the statement it appears in, so taking the maximum
costs nothing and makes `Kakeya.ml1Boot.one_le_uniformize_C` a theorem rather than one more
unprovable assumption. -/
noncomputable def uniformize.C (n : ℕ) : NNReal := max 1 (uniformize.rawC n)

/-- The uniformity constant of the shaded uniformization is at least `1`. -/
theorem one_le_uniformize_C (n : ℕ) : 1 ≤ uniformize.C n :=
  le_max_left (a := (1 : NNReal)) (b := uniformize.rawC n)

/-- **The constant every producer actually lands at fits inside `C_{unif}`.**

This is the bridge that `ShadedTube.ShadedUniformTubeSet.mono` needs in order to place a
hierarchy produced at `ShadedTube.ssfUniformConst n` into a field stated at
`Kakeya.ml1Boot.uniformize.C n`.  While `uniformize.rawC` was `opaque` it was unprovable, and
that — not any missing mathematics — is what blocked
`Kakeya.ml1Boot.exists_uniformFactorCore` and its dilate twin. -/
theorem ssfUniformConst_le_uniformize_C (n : ℕ) :
    ShadedTube.ssfUniformConst n ≤ uniformize.C n :=
  le_max_right (a := (1 : NNReal)) (b := uniformize.rawC n)

/-- **The conclusions of `Kakeya.ml1Boot.exists_uniformRefinement`, one field per item.**

Here `(𝕍, Z)` is a family of shaded `σ`-tubes indexed by `s`, `(ρ r, t r, Vρ r, p r)` are
`m` scales with parent families for `𝕍`, and the refinement data is `s'`, `λ'`, `t'` and
`N`.  The fields are items (i)–(vii) and (ix) of the blueprint lemma
`lem:ml1bootUniformizePair`; for why item (viii) is not among them see the module
docstring. -/
structure IsUniformRefinement {ι κ : Type*} [DecidableEq κ] {m : ℕ} {σ : NNReal}
    (δ : NNReal) (ε' : ℝ) (s : Finset ι) (V : ι → ShadedTube σ E)
    (ρ : Fin m → NNReal) (t : Fin m → Finset κ) (Vρ : (r : Fin m) → κ → Tube (ρ r) E)
    (p : Fin m → ι → κ) (s' : Finset ι) (lam' : NNReal) (t' : Fin m → Finset κ)
    (N : Fin m → NNReal) : Prop where
  /-- (i) `(𝕍|_{s'}, Z)` is a `δ ^ ε'`-refinement of `(𝕍, Z)`. -/
  refinement : ShadedBody.IsCRefinement s' (fun i => (V i).toShadedBody) s
    (fun i => (V i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩
  /-- (ii) `(𝕍|_{s'}, Z)` is uniform, at the dimension-only constant
  `Kakeya.ml1Boot.uniformize.C 3`.  `ShadedTube.ShadedUniformTubeSet` is data-valued, so the
  `Prop`-valued clause is its `Nonempty`. -/
  unif : Nonempty (ShadedTube.ShadedUniformTubeSet s' V (Tube.ssfGridLen σ)
    (uniformize.C 3))
  /-- (iii) The shading densities on `s'` are two-sidedly comparable to `λ'`, which is
  itself at least `δ ^ ε'` times the fullness of the original family. -/
  dens : (∀ i ∈ s', (lam' : ENNReal) * volume (V i).carrier ≤ volume (V i).shade ∧
      volume (V i).shade ≤ 2 * (lam' : ENNReal) * volume (V i).carrier) ∧
    (δ : ENNReal) ^ ε' * ShadedBody.fullness s (fun i => (V i).toShadedBody) ≤ (lam' : ENNReal)
  /-- (iv) `|s'| ≥ δ ^ ε' |s|`, and consequently the Frostman constant grows by at most
  `δ ^ (-ε')` in every convex body containing the whole family. -/
  card : (δ : ENNReal) ^ ε' * (s.card : ENNReal) ≤ (s'.card : ENNReal) ∧
    ∀ K : ConvexSpaceBody E, (∀ i ∈ s, (V i).toConvexSpaceBody ≤ K) →
      frostmanConstIn s' (fun i => (V i).toConvexSpaceBody) K
        ≤ (δ : ENNReal) ^ (-ε') * frostmanConstIn s (fun i => (V i).toConvexSpaceBody) K
  /-- (v) Essential distinctness is inherited by the subfamily. -/
  essDistinct : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) →
    (s' : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier)
  /-- (vi) The parents of the retained members lie in `t' r`, the retained fibres all have
  cardinality comparable to `N r`, and each retains at least a `δ ^ ε'` fraction. -/
  branch : ∀ r : Fin m, t' r ⊆ t r ∧ (∀ i ∈ s', p r i ∈ t' r) ∧
    ∀ k ∈ t' r,
      (N r : ENNReal) ≤ ((fibre s' (p r) k).card : ENNReal) ∧
      ((fibre s' (p r) k).card : ENNReal) ≤ 2 * (N r : ENNReal) ∧
      (δ : ENNReal) ^ ε' * ((fibre s (p r) k).card : ENNReal)
        ≤ ((fibre s' (p r) k).card : ENNReal)
  /-- (vii) The Frostman constant of each fibre grows by at most `δ ^ (-ε')`. -/
  fibreFrostman : ∀ r : Fin m, ∀ k ∈ t' r, ∀ K : ConvexSpaceBody E,
    (∀ i ∈ fibre s (p r) k, (V i).toConvexSpaceBody ≤ K) →
    frostmanConstIn (fibre s' (p r) k) (fun i => (V i).toConvexSpaceBody) K
      ≤ (δ : ENNReal) ^ (-ε')
        * frostmanConstIn (fibre s (p r) k) (fun i => (V i).toConvexSpaceBody) K
  /-- (ix) (`item:uniformizeGivenFibreUnif`) Every retained *parent-map* fibre of every
  *given* parent family is itself uniform, at the constant
  `Kakeya.ml1Boot.uniformize.C 3`.  This is the clause that
  `Kakeya.ml1Boot.multiplicity_le_middle` consumes.  Item (viii)
  `item:uniformizeFibreUnif`, the containment-fibre clause, is not a field here; see the
  module docstring. -/
  fibreUnif : ∀ r : Fin m, ∀ k ∈ t' r,
    Nonempty (ShadedTube.ShadedUniformTubeSet (fibre s' (p r) k) V
      (Tube.ssfGridLen σ) (uniformize.C 3))

/-! ### The refuted uniformization, and why no statement of that shape appears here

`Kakeya.ml1Boot.exists_uniformRefinement` used to stand here: the step of Case (ii) that GWZ
dispatches with "we may suppose that all sets of the form … are uniform", asserting that a
family equipped with `m` parent families may be passed to a `δ ^ ε'`-refinement that is uniform
with constant `2`, has two-sidedly comparable shading densities, retains a `δ ^ ε'` fraction of
the index set and of every fibre, and loses at most `δ ^ (-ε')` in every Frostman constant.

It has been **deleted**, because it is false and had no consumer:
`Kakeya.ml1Boot.exists_uniformFactorPair` and `Kakeya.ml1Boot.exists_uniformFactorCore` replaced
it, and nothing cited it in code.  `Kakeya.ml1Boot.not_exists_uniformRefinement` below is kept as
the record and the guardrail: it is a self-contained refutation, and its docstring carries the
full diagnosis, including a second obstruction that survives the obvious repair.  The bundle
`Kakeya.ml1Boot.IsUniformRefinement` is likewise retained, now referenced only from prose, so
that the refuted shape stays legible.

Do not reintroduce a statement of this shape: an `∃`-conclusion asserting a positive lower bound
on shading densities, with no hypothesis constraining those shadings, is refuted by the
all-empty shading.

Prose elsewhere in this file still names `Kakeya.ml1Boot.exists_uniformRefinement`, deliberately:
it is the clearest way to say *which* statement is refuted, and several docstrings record that
they do not cite it.  Those are references to a deleted declaration, not to a live one; read
`Kakeya.ml1Boot.not_exists_uniformRefinement` for the diagnosis, and blueprint
`lem:ml1bootUniformizePair` for the statement as GWZ have it.

### Two further names in this file that are not declarations

The second was
the only consumer of the first and had none itself, so the pair was dead as a unit; the deletion
record is `Kakeya/DimensionThree/MainLemma1/Inventory.lean`, §B. Unlike the refuted statement
above, these two were not false: what is gone is the Lean carrier, not the mathematics. The
obligation is unchanged and is stated in blueprint `lem:ml1bootFactorOneScaleUniform`; the
reduction of the fine group to it, together with every proved piece of that reduction, is set out
in the docstring of `Kakeya.ml1Boot.exists_uniformFactorCore`.

Docstrings below therefore speak of "the shaded-uniformization interface" as a *shape* Section 2
still owes, and never as a declaration.  Do not read a claim of formalization into it. -/

/-- **A half-tube in `B₁ ⊆ ℝ³` carrying the empty shading.**

The tube whose core is the segment from `-e/2` to `e/2`, with `e` the first standard basis
vector, shaded by `∅`.  Its core lies in the ball of radius `1/2` about the origin, so its
closed `(1/2)`-neighbourhood — its carrier — lies in `B₁`; and the carrier contains the ball of
radius `1/2` about the core's endpoint, so it has positive volume.

This is the witness of `Kakeya.ml1Boot.not_exists_uniformRefinement`: a shaded tube satisfying
every hypothesis of `Kakeya.ml1Boot.exists_uniformRefinement` whose shading is null. -/
theorem exists_emptyShadedHalfTube :
    ∃ V : ShadedTube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3)),
      V.carrier ⊆ Metric.closedBall 0 1 ∧ V.shade = ∅ ∧ 0 < volume V.carrier := by
  let e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 (1 : ℝ)
  let p : EuclideanSpace ℝ (Fin 3) := -(1 / 2 : ℝ) • e
  let q : EuclideanSpace ℝ (Fin 3) := (1 / 2 : ℝ) • e
  have hnorm_e : ‖e‖ = 1 := by
    simp [e]
  have hqp : q - p = e := by
    dsimp [q, p, e]
    rw [sub_eq_add_neg]
    rw [neg_smul, neg_neg]
    rw [← add_smul]
    norm_num
  have hdist : dist p q = 1 := by
    rw [dist_eq_norm_sub' p q, hqp, hnorm_e]
  have hp_norm : ‖p‖ = 1 / 2 := by
    dsimp [p]
    rw [norm_smul, hnorm_e]
    norm_num
  have hq_norm : ‖q‖ = 1 / 2 := by
    dsimp [q]
    rw [norm_smul, hnorm_e]
    norm_num
  have hp_ball : p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ) := by
    rw [Metric.mem_closedBall]
    rw [dist_eq_norm, sub_zero, hp_norm]
  have hq_ball : q ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ) := by
    rw [Metric.mem_closedBall]
    rw [dist_eq_norm, sub_zero, hq_norm]
  have hconv : Convex ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ)) :=
    convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ)
  have hseg : segment ℝ p q ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ) :=
    Convex.segment_subset hconv hp_ball hq_ball
  let T : Tube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3)) :=
    Tube.mk' (1 / 2 : NNReal) (x := p) (y := q) hdist
  let V : ShadedTube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3)) :=
    { toTube := T
      shade := ∅
      measurableSet_shade := MeasurableSet.empty
      shade_subset := Set.empty_subset _ }
  refine ⟨V, ?_, ?_, ?_⟩
  · intro w hw
    dsimp [V, T] at hw
    change w ∈ ⋃ z ∈ segment ℝ p q, Metric.closedBall z ((1 / 2 : NNReal) : ℝ) at hw
    rw [Set.mem_iUnion₂] at hw
    rcases hw with ⟨z, hz, hwz⟩
    have hwz' : dist w z ≤ (1 / 2 : ℝ) := by
      have h := Metric.mem_closedBall.mp hwz
      norm_num at h ⊢
      exact h
    have hz_ball : z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ) := hseg hz
    have hz0 : dist z 0 ≤ 1 / 2 := Metric.mem_closedBall.mp hz_ball
    have hw0 : dist w 0 ≤ 1 := by
      calc
        dist w 0 ≤ dist w z + dist z 0 := dist_triangle w z 0
        _ ≤ (1 / 2 : ℝ) + (1 / 2 : ℝ) := by gcongr
        _ = 1 := by norm_num
    exact Metric.mem_closedBall.mpr hw0
  · rfl
  · have hsubT : Metric.closedBall p ((1 / 2 : NNReal) : ℝ) ⊆ T.carrier := by
      rw [T.carrier_eq]
      exact Set.subset_iUnion₂ (s := fun z _ => Metric.closedBall z ((1 / 2 : NNReal) : ℝ)) p
        (left_mem_segment ℝ p q)
    have hsub : Metric.closedBall p ((1 / 2 : NNReal) : ℝ) ⊆ V.carrier := by
      simpa [V] using hsubT
    have hpos : 0 < volume (Metric.closedBall p ((1 / 2 : NNReal) : ℝ)) := by
      exact Metric.measure_closedBall_pos volume p (by norm_num)
    exact lt_of_lt_of_le hpos (measure_mono hsub)

/-- **Extracting one small witness from a `∀ᶠ δ in 𝓝[>] 0` clause.**

A property holding eventually along `𝓝[>] (0 : NNReal)` holds at some `δ` with
`0 < δ ≤ 1/2`: that filter is nontrivial, `Set.Ioi 0` belongs to it, and so does
`Set.Iio (1/2)`, a neighbourhood of `0`.  This is all that
`Kakeya.ml1Boot.not_exists_uniformRefinement` needs from the smallness quantifier of
`Kakeya.ml1Boot.exists_uniformRefinement`. -/
theorem exists_small_of_eventually_nhdsGT {p : NNReal → Prop}
    (h : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, p δ) :
    ∃ δ : NNReal, 0 < δ ∧ δ ≤ 1 / 2 ∧ p δ := by
  have hpos : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, 0 < δ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hδ
  have hle : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, δ ≤ 1 / 2 := by
    filter_upwards
      [mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (show (0 : NNReal) < (1 / 2 : NNReal) by norm_num))] with δ hδ
    exact le_of_lt hδ
  rcases (h.and (hpos.and hle)).exists with ⟨δ, hpδ, hrest⟩
  exact ⟨δ, hrest.1, hrest.2, hpδ⟩

/-- **(negative result) the uniformization of blueprint `lem:ml1bootUniformizePair` is false: it
bounds the shading densities from below without assuming anything about them.**

**The refuted shape has been removed from this file; this theorem is retained as the record.**
The declaration it refuted, `Kakeya.ml1Boot.exists_uniformRefinement`, was deleted once it was
established that it is false and that nothing cited it in code
(`Kakeya.ml1Boot.exists_uniformFactorPair` and `Kakeya.ml1Boot.exists_uniformFactorCore` had
replaced it).  The statement below is self-contained — it spells the refuted proposition out
rather than referring to a declaration — so it survives that deletion, and it is the only
guardrail against the shape being written back.  The bundle
`Kakeya.ml1Boot.IsUniformRefinement` is also retained, referenced now only from prose.

## What was refuted

The deleted statement, at `m = 0` and `E = EuclideanSpace ℝ (Fin 3)`, with

* the parent-family data (`ρ`, `t`, `Vρ`, `p`) and every hypothesis about it dropped.  At
  `m = 0` those are functions on `Fin 0`, and `Monotone ρ`, `∀ r, σ ≤ ρ r`, `∀ r, ρ r ≤ 1` and
  `∀ r, IsParentFamily …` are all vacuously true, so dropping them removes nothing;
* only the first inequality of `Kakeya.ml1Boot.IsUniformRefinement.dens`, the first inequality
  of `Kakeya.ml1Boot.IsUniformRefinement.card`, and the positivity `0 < lam'` retained.  Every
  other clause — `refinement`, `unif`, `essDistinct`, and the vacuous `branch`,
  `fibreFrostman`, `fibreUnif` — is discarded, which makes this a refutation of a strictly
  weaker statement.

Instantiate at `σ = 1/2`, `ι = Unit`, `s = {}` and `V` the constant family whose member is
the empty-shaded half-tube of `Kakeya.ml1Boot.exists_emptyShadedHalfTube`.  Both retained
hypotheses hold.  But `δ ^ ε' > 0` and `s.card = 1`, so the cardinality clause forces `s'` to
be nonempty, and the density clause then reads
`lam' * volume (V ).carrier ≤ volume ∅ = 0` with `lam' > 0` and
`volume (V ).carrier > 0`.

## The repair, and why it is not enough

The missing hypothesis is a positive lower bound on the shading densities of `𝕍`, in the shape
`∀ i ∈ s, (a : ENNReal) * volume (V i).carrier ≤ volume (V i).shade` for some `0 < a ≤ 1` —
exactly the hypothesis `hZ` of
`Kakeya.ShadedBody.exists_isCRefinement_comparable_density`, the proved pigeonhole that the
`dens` field was supposed to be read off.  The blueprint's `𝕍` always carries such a bound (the
input fullness `δ ^ η_full` of Case (ii)); it was simply not transcribed.

**A second obstruction, which the repair does not remove, and which is why the statement was
deleted rather than re-shaped.**  The `unif` field asked for
`ShadedTube.ShadedUniformTubeSet s' V (Tube.ssfGridLen σ) (uniformize.C 3)` at the
**original** shading `V`, whereas `ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`
produces uniformity only after *shrinking* the shadings to some `V'` with
`(V' i).shade ⊆ (V i).shade`.  Passing to a subfamily can only decrease every pointwise count
`#{i : x ∈ (V i).shade}` simultaneously, at every `x` at once, so it cannot flatten a shading
whose pointwise multiplicity is genuinely non-constant: take many indices carrying the *same*
carrier with *nested* shadings of pairwise comparable volume, so that the density bracket of
`dens` is satisfied by every subfamily, while the pointwise count drops from `#s'` at a point of
the innermost shading to `1` at a point of the outermost one.  Bounded overlap confines the
retained indices to at most `uniformize.C 3` node classes, so one class inherits the same
spread, and chaining the four brackets of `ShadedTube.ShadedUniformTubeSet` caps that spread
by `uniformize.C 3 ^ 4`; taking the number of nested shadings above
`uniformize.C 3 ^ 5 * δ ^ (-ε')` then contradicts `card`.  Since
`Kakeya.ml1Boot.IsUniformRefinement` is not parameterized by an output shading, this cannot be
repaired by adding a hypothesis.  That is why any replacement has to take a density bracket as a
*hypothesis* and hand one back at *its own output* shading.

**That replacement has no Lean carrier.**  This file used to state it as a sorried interface,
`exists_shadedUniform_of_card_le`, together with the one lemma proved from it,
`exists_fineUniformBand`.  Both have been **deleted**: the second was the only consumer of the
first and had none itself, so the pair was dead as a unit
(`Kakeya/DimensionThree/MainLemma1/Inventory.lean`, §B).  Nothing in the development now asserts
the replacement, so where the docstrings of this file speak of "the shaded-uniformization
interface" they name a *shape* that a Section 2 statement would have to have, not a declaration.
The requirement itself is unchanged and is recorded in blueprint
`lem:ml1bootFactorOneScaleUniform`.

The hypothesis `0 < ε'` is carried so that this is an instance of the refuted statement and
not something weaker; it happens to be unused, `δ ^ ε'` being positive for every real
exponent once `0 < δ < ⊤`. -/
theorem not_exists_uniformRefinement {ε' : ℝ} (_hε' : 0 < ε') :
    ¬ ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ σ : NNReal, δ ≤ σ → σ ≤ 1 →
        ∀ {ι : Type} {s : Finset ι} (V : ι → ShadedTube σ (EuclideanSpace ℝ (Fin 3))),
          s.Nonempty →
          (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
          ∃ s' ⊆ s, ∃ lam' : NNReal, 0 < lam' ∧
            (∀ i ∈ s', (lam' : ENNReal) * volume (V i).carrier ≤ volume (V i).shade) ∧
            (δ : ENNReal) ^ ε' * (s.card : ENNReal) ≤ (s'.card : ENNReal) := by
  intro hE
  obtain ⟨d, dP, dH, dS⟩ := exists_small_of_eventually_nhdsGT hE
  obtain ⟨W, wB, wS, wV⟩ := exists_emptyShadedHalfTube
  let F : Unit → ShadedTube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3)) := fun _ => W
  have hF : ∀ i ∈ ({()} : Finset Unit), (F i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i _
    simpa [F] using wB
  have hG := dS (1 / 2 : NNReal) dH (by norm_num : (1 / 2 : NNReal) ≤ 1)
    (ι := Unit) (s := ({()} : Finset Unit)) F (Finset.singleton_nonempty ()) hF
  rcases hG with ⟨t, hSub, la, lp, ld, lc⟩
  have hAb : 0 < (d : ENNReal) := ENNReal.coe_pos.mpr dP
  have hA : 0 < (d : ENNReal) ^ ε' := ENNReal.rpow_pos hAb ENNReal.coe_ne_top
  have hOn : (({()} : Finset Unit).card : ENNReal) = 1 := by simp
  have hB : 0 < (d : ENNReal) ^ ε' * (({()} : Finset Unit).card : ENNReal) := by
    rw [hOn]
    simpa using hA
  have hC : 0 < (t.card : ENNReal) := lt_of_lt_of_le hB lc
  have hN : (0 : ℕ) < t.card := by
    by_contra hn
    have hz : t.card = 0 := by omega
    exact (ne_of_gt hC) (by simp [hz])
  obtain ⟨i, hi⟩ := (Finset.card_pos).mp hN
  have hD : (la : ENNReal) * (volume W.carrier : ENNReal) ≤
      (volume W.shade : ENNReal) := by
    simpa [F] using ld i hi
  have hL : 0 < (la : ENNReal) := ENNReal.coe_pos.mpr lp
  have hV : 0 < (volume W.carrier : ENNReal) := wV
  have hM : 0 < (la : ENNReal) * (volume W.carrier : ENNReal) :=
    ENNReal.mul_pos (ne_of_gt hL) (ne_of_gt hV)
  have hNon : ¬ (la : ENNReal) * (volume W.carrier : ENNReal) ≤
      (volume W.shade : ENNReal) := by
    have hz : (volume W.shade : ENNReal) = 0 := by simp [wS]
    rw [hz]
    exact not_le_of_gt hM
  exact hNon hD

/-! ### The two-scale factoring chain -/

/-- **The constant `C_{lem:ml1bootFactorOneScale}`** of one factoring step (blueprint
`def:ml1bootFactorConstant`), at inner cardinality `N` and inner tube scale `σ`: the `c = 1`
case, in the ambient dimension `3`, of
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C`.

This is the constant `Kakeya.ml1Boot.exists_factorOneScale` is *proved* at, and it is **not**
absolute: it grows with `N` and with `σ⁻¹`, subpolynomially in both by
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox`.

It used to be the numeral `1`, read off `ShadedBody.shadingMultiplicityEstimateForRhoTubes.C`;
that statement has since been **refuted and deleted** (it was false at `1`, and false at every
nonzero constant, for the reasons recorded in the docstring of
`ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated`), and no proved estimate supports
an absolute value.  The two binders are therefore carried by every statement stated at this
constant — the fields of `Kakeya.ml1Boot.IsFactorOneScale`,
`Kakeya.ml1Boot.IsUniformFactorCore` and, through
`Kakeya.ml1Boot.factorTwoScales.C`, `Kakeya.ml1Boot.IsFactorTwoScales`.

Only `Kakeya.ml1Boot.one_le_factorOneScale_C` and the subpolynomial estimate
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox` are used downstream, never
the numerical value. -/
noncomputable def factorOneScale.C (N : ℕ) (σ : NNReal) : NNReal :=
  ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C 3 N σ 1

/-- **(GWZ Lemma 5.11) One factoring step, in named form** (blueprint
`lem:ml1bootFactorOneScale`).

Write `C = Kakeya.ml1Boot.factorOneScale.C #s σ`.  For a family `(𝕍, Z)` of shaded
`σ`-tubes in `B₁ ⊆ ℝ³` whose shading densities are two-sidedly comparable to `λ` with
constant `C_d`, and a parent family `(t, 𝕍_ρ, p)` at a scale `ρ ∈ [σ, 1]`,
`ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam` supplies a subset `t' ⊆ t`, a
shading `Z_ρ` of `𝕍_ρ|_{t'}` and a shading `Z'` of `𝕍|_{s'}`, where `s' = {i ∈ s : p i ∈ t'}`,
satisfying items (i)–(iv) of the blueprint lemma.

Only the naming of the output objects is new; the content is
`ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam` with the partition of `s` given
by the parent map `p`.  As in `Kakeya.ml1Boot.IsFactorTwoScales`, the two output shadings are
given as families of `ShadedTube`, the clause "`Z_ρ` is a shading of `𝕍_ρ|_{t'}`" being recorded
as the equality of the underlying tubes.

## The constant is not absolute

The former source of this lemma, `ShadedBody.shadingMultiplicityEstimateForRhoTubes`, was
refuted and deleted; the surviving estimate is proved at
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C (Module.finrank ℝ E) #s σ 1`, which
grows with `#s` and with `σ⁻¹`.  That value is named `Kakeya.ml1Boot.factorOneScale.C #s σ`,
and items (ii) and (iv) are stated at it.  Item (i) carries in addition the factor `C_d` paid
by the conversion from a fullness lower bound to a lower bound by the density parameter `λ`
(`ShadedBody.le_fullness_of_le_fullness_of_forall_density`).

## Three hypotheses that were previously inert are now used

`hσ0` and `hball` are consumed by the pipeline behind the dilate estimate.  `hs0` is the
nondegeneracy condition of the `λ` form and is **not** removable: on the empty family the density
hypotheses are vacuous while the outer fullness is `0`, which refutes item (i) at every constant.
Conversely `_hunif`, `_hov` and the upper density bound in `hdens` are inert for every conclusion
below, and are retained only as the interface the intended callers can point at. -/
theorem exists_factorOneScale (hdim : Module.finrank ℝ E = 3)
    {σ ρ : NNReal} (hσ0 : 0 < σ) (hσρ : σ ≤ ρ) (hρ1 : ρ ≤ 1)
    {ι κ : Type*} [DecidableEq κ] {s : Finset ι} {t : Finset κ}
    (V : ι → ShadedTube σ E) (Vρ : κ → Tube ρ E) (p : ι → κ)
    (Cunif : NNReal)
    (_hunif : ShadedTube.ShadedUniformTubeSet s V (Tube.ssfGridLen σ) Cunif)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    {lam Cd : NNReal} (_hlam0 : 0 < lam) (_hlam1 : lam ≤ 1) (hCd : 1 ≤ Cd)
    (hdens : ∀ i ∈ s, (Cd : ENNReal)⁻¹ * (lam : ENNReal) * volume (V i).carrier
        ≤ volume (V i).shade ∧
      volume (V i).shade ≤ (Cd : ENNReal) * (lam : ENNReal) * volume (V i).carrier)
    (hs0 : ∑ i ∈ s, volume (V i).carrier ≠ 0)
    (hparent : IsParentFamily s (fun i => (V i).toTube) t Vρ p)
    {Co : NNReal} (_hov : HasBoundedOverlap s (fun i => (V i).toTube) t Vρ Co) :
    ∃ t' ⊆ t, ∃ (Zρ : κ → ShadedTube ρ E) (Z' : ι → ShadedTube σ E),
      (∀ k ∈ t', (Zρ k).toTube = Vρ k) ∧
      (∀ i ∈ s, p i ∈ t' → (Z' i).toTube = (V i).toTube) ∧
      -- (i)
      ((Cd * factorOneScale.C s.card σ : NNReal) : ENNReal)⁻¹ * (lam : ENNReal)
          ≤ ShadedBody.fullness t' (fun k => (Zρ k).toShadedBody) ∧
      -- (ii)
      ((∀ i ∈ s, p i ∈ t' → (Z' i).shade ⊆ (V i).shade) ∧
        ShadedBody.IsCRefinement (s.filter fun i => p i ∈ t')
          (fun i => (Z' i).toShadedBody) s (fun i => (V i).toShadedBody)
          (factorOneScale.C s.card σ)⁻¹) ∧
      -- (iii)
      (∀ i ∈ s, p i ∈ t' → (Z' i).shade ⊆ (Zρ (p i)).shade) ∧
      -- (iv)
      ∀ k ∈ t', ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
        ≤ (factorOneScale.C s.card σ : ENNReal)
          * ShadedBody.multiplicity t' (fun k' => (Zρ k').toShadedBody)
          * ShadedBody.multiplicity (fibre (s.filter fun i => p i ∈ t') p k)
              (fun i => (Z' i).toShadedBody) := by
  classical
  haveI : Nontrivial E := Module.finrank_pos_iff.mp (by rw [hdim]; norm_num)
  have hcover : ∀ i ∈ s, (V i).toShadedBody.toConvexSpaceBody ≤ (Vρ (p i)).toConvexSpaceBody := by
    intro i hi
    simpa using hparent.le_parent i hi
  have hlam_lb : ∀ i ∈ s,
      (Cd : ENNReal)⁻¹ * ((lam : ENNReal) * volume (V i).toShadedBody.carrier)
        ≤ volume (V i).shade := by
    intro i hi
    simpa [mul_assoc] using (hdens i hi).1
  let F : ShadedBody.FactorFamily E ι κ :=
    { innerSet := s
      innerBody := fun i => (V i).toShadedBody
      outerSet := t
      outerBody := fun k => (Vρ k).toConvexSpaceBody
      parent := p
      parent_mem := hparent.mapsTo
      inner_le_parent := hcover }
  have hinner : ∀ i ∈ F.innerSet, F.innerBody i = (V i).toShadedBody := by
    intro i hi
    rfl
  have houter : ∀ j ∈ F.outerSet, F.outerBody j = (Vρ j).toConvexSpaceBody := by
    intro j hj
    rfl
  have hCd0 : Cd ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) hCd)
  obtain ⟨G, hG_outer, hG_inner, hG_parent, hSρ_bodyC, hT'_body, _hne, hfull, hcref, hmult,
      hpt, _hvol⟩ :=
    ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam hσ0 ⟨hσρ, hρ1⟩ hCd0 F V Vρ
      hinner houter
      (by
        intro i hi
        simpa [F] using hball i hi)
      (by simpa [F] using hs0)
      hlam_lb
  let t' : Finset κ := G.outerSet
  let Sρ : κ → ShadedBody E := G.outerBody
  let T' : ι → ShadedBody E := G.innerBody
  have ht'sub : t' ⊆ t := by simpa [t'] using hG_outer
  have hG_inner' : G.innerSet = s.filter (fun i => p i ∈ t') := by
    simpa [F, t'] using hG_inner
  have hSρ_body : ∀ k ∈ t', (Sρ k).carrier = (Vρ k).carrier := by
    intro k hk
    have hh := hSρ_bodyC k hk
    simpa [t', Sρ, F] using congrArg (fun b : ConvexSpaceBody E => b.carrier) hh
  let Zρ : κ → ShadedTube ρ E := fun k =>
    if hk : k ∈ t' then
      { toTube := Vρ k
        shade := (Sρ k).shade
        measurableSet_shade := (Sρ k).measurableSet_shade
        shade_subset := by
          rw [← hSρ_body k hk]
          exact (Sρ k).shade_subset }
    else
      { toTube := Vρ k
        shade := ∅
        measurableSet_shade := MeasurableSet.empty
        shade_subset := by simp }
  let Z' : ι → ShadedTube σ E := fun i =>
    if hi : i ∈ s.filter (fun i => p i ∈ t') then
      { toTube := (V i).toTube
        shade := (T' i).shade
        measurableSet_shade := (T' i).measurableSet_shade
        shade_subset := by
          have hi_s : i ∈ s := (Finset.mem_filter.mp hi).1
          have hbody : (T' i).toConvexSpaceBody = (V i).toConvexSpaceBody := by
            simpa using hT'_body i hi_s
          change (T' i).shade ⊆ (V i).toConvexSpaceBody.carrier
          rw [← hbody]
          exact (T' i).shade_subset }
    else
      { toTube := (V i).toTube
        shade := ∅
        measurableSet_shade := MeasurableSet.empty
        shade_subset := by simp }
  have hZρ_shade : ∀ k ∈ t', (Zρ k).shade = (Sρ k).shade := by
    intro k hk
    simp [Zρ, hk]
  have hZρ_carrier : ∀ k ∈ t', (Zρ k).carrier = (Sρ k).carrier := by
    intro k hk
    have hZ : (Zρ k).carrier = (Vρ k).carrier := by simp [Zρ, hk]
    rw [hZ, hSρ_body k hk]
  have hZ'_shade : ∀ i ∈ s.filter (fun i => p i ∈ t'), (Z' i).shade = (T' i).shade := by
    intro i hi
    have hi' : i ∈ s ∧ p i ∈ t' := Finset.mem_filter.mp hi
    simp [Z', hi']
  have hZ'_body : ∀ i ∈ s.filter (fun i => p i ∈ t'),
      (Z' i).toConvexSpaceBody = (T' i).toConvexSpaceBody := by
    intro i hi
    have hi' : i ∈ s ∧ p i ∈ t' := Finset.mem_filter.mp hi
    have hZ : (Z' i).toConvexSpaceBody = (V i).toConvexSpaceBody := by simp [Z', hi']
    rw [hZ]
    exact (hT'_body i hi'.1).symm
  refine ⟨t', ht'sub, Zρ, Z', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    simp [Zρ, hk]
  · intro i hi_s hip
    simp [Z', hi_s, hip]
  · -- (i)
    have hsum_shade : (∑ k ∈ t', volume ((Zρ k).toShadedBody).shade)
        = ∑ k ∈ t', volume (Sρ k).shade := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [hZρ_shade k hk]
    have hsum_carrier : (∑ k ∈ t', volume ((Zρ k).toShadedBody).carrier)
        = ∑ k ∈ t', volume (Sρ k).carrier := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [hZρ_carrier k hk]
    rw [show ShadedBody.fullness t' (fun k => (Zρ k).toShadedBody)
        = ShadedBody.fullness t' Sρ from by
          unfold ShadedBody.fullness ShadedBody.fullness'
          simp [hsum_shade, hsum_carrier]]
    have hC0 : Cd * factorOneScale.C s.card σ ≠ 0 := by
      unfold factorOneScale.C
      exact mul_ne_zero (ne_of_gt (lt_of_lt_of_le (by norm_num) hCd))
        (ne_of_gt (lt_of_lt_of_le (by norm_num)
          (ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.one_le_C 3 s.card σ 1)))
    have hfullNN : (Cd * factorOneScale.C s.card σ)⁻¹ * lam
        ≤ ShadedBody.fullness t' Sρ := by
      simpa [factorOneScale.C, hdim] using hfull
    rw [← ENNReal.coe_inv hC0, ← ENNReal.coe_mul]
    exact_mod_cast hfullNN
  · -- (ii)
    constructor
    · intro i hi_s hip
      have hi' : i ∈ G.innerSet := by
        rw [hG_inner']
        exact Finset.mem_filter.mpr ⟨hi_s, hip⟩
      simpa [Z', hi_s, hip] using (hcref.1.2 i hi').2
    · -- IsCRefinement
      constructor
      · constructor
        · rw [← hG_inner']
          simpa using hcref.1.1
        · intro i hi
          have hi' : i ∈ G.innerSet := by
            rw [hG_inner']
            exact hi
          constructor
          · simpa [hZ'_body i hi] using (hcref.1.2 i hi').1
          · simpa [hZ'_shade i hi] using (hcref.1.2 i hi').2
      · calc
          (factorOneScale.C s.card σ)⁻¹ * ∑ i ∈ s, volume ((V i).toShadedBody).shade
              ≤ ∑ i ∈ s.filter (fun i => p i ∈ t'), volume (T' i).shade := by
                simpa [factorOneScale.C, hdim, ← hG_inner'] using hcref.2
          _ = ∑ i ∈ s.filter (fun i => p i ∈ t'), volume ((Z' i).toShadedBody).shade := by
                apply Finset.sum_congr rfl
                intro i hi
                simp [hZ'_shade i hi]
  · -- (iii)
    intro i hi_s hip
    have hi : i ∈ s.filter (fun i => p i ∈ t') := Finset.mem_filter.mpr ⟨hi_s, hip⟩
    have hi' : i ∈ G.innerSet := by
      rw [hG_inner']
      exact hi
    simpa [Z', Zρ, hi_s, hip] using hpt i hi'
  · -- (iv)
    intro k hk
    have hfibre : fibre (s.filter fun i => p i ∈ t') p k = s.filter (fun i => p i = k) := by
      unfold fibre
      rw [Finset.filter_filter]
      exact Finset.filter_congr (fun i hi => by
        constructor
        · intro h; exact h.2
        · intro h; exact ⟨by rw [h]; exact hk, h⟩)
    have hG_fiber : (ShadedBody.ShadedFactorFamily.fiber G k : Finset ι) =
        fibre (s.filter fun i => p i ∈ t') p k := by
      simp [ShadedBody.ShadedFactorFamily.fiber, fibre, F, hG_inner', hG_parent]
    have hm := hmult k hk
    have hm' : ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
        ≤ (factorOneScale.C s.card σ : ENNReal)
          * ShadedBody.multiplicity t' Sρ
          * ShadedBody.multiplicity (s.filter (fun i => p i = k)) T' := by
      simpa [factorOneScale.C, hdim, F, t', Sρ, T', hG_fiber, hfibre] using hm
    have hmulZρ : ShadedBody.multiplicity t' (fun k' => (Zρ k').toShadedBody)
        = ShadedBody.multiplicity t' Sρ := by
      unfold ShadedBody.multiplicity
      congr 1
      · apply Finset.sum_congr rfl; intro k' hk'; simp [hZρ_shade k' hk']
      · apply congrArg volume
        apply Set.iUnion₂_congr
        intro k' hk'
        simp [hZρ_shade k' hk']
    have hmulZ' : ShadedBody.multiplicity (fibre (s.filter fun i => p i ∈ t') p k)
        (fun i => (Z' i).toShadedBody)
        = ShadedBody.multiplicity (s.filter (fun i => p i = k)) T' := by
      rw [hfibre]
      unfold ShadedBody.multiplicity
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        have hi' : i ∈ s.filter (fun i => p i ∈ t') := by
          have hi_s : i ∈ s := (Finset.mem_filter.mp hi).1
          have hpik : p i = k := (Finset.mem_filter.mp hi).2
          exact Finset.mem_filter.mpr ⟨hi_s, by rw [hpik]; exact hk⟩
        simp [hZ'_shade i hi']
      · apply congrArg volume
        apply Set.iUnion₂_congr
        intro i hi
        have hi' : i ∈ s.filter (fun i => p i ∈ t') := by
          have hi_s : i ∈ s := (Finset.mem_filter.mp hi).1
          have hpik : p i = k := (Finset.mem_filter.mp hi).2
          exact Finset.mem_filter.mpr ⟨hi_s, by rw [hpik]; exact hk⟩
        simp [hZ'_shade i hi']
    calc
      ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
          ≤ (factorOneScale.C s.card σ : ENNReal)
            * ShadedBody.multiplicity t' Sρ
            * ShadedBody.multiplicity (s.filter (fun i => p i = k)) T' := by
              exact hm'
      _ = (factorOneScale.C s.card σ : ENNReal)
            * ShadedBody.multiplicity t' (fun k' => (Zρ k').toShadedBody)
            * ShadedBody.multiplicity (fibre (s.filter fun i => p i ∈ t') p k)
                (fun i => (Z' i).toShadedBody) := by
            rw [hmulZρ, hmulZ']

/-- **The constant `C_{lem:ml1bootFactorTwoScales}`** of the two-scale factoring chain
(blueprint `def:ml1bootFactorTwoScalesConstant`): the **product** of the two applications'
one-scale constants, since the chain is two applications of the one-scale step.

`N₁` and `δ` are the cardinality and tube scale of the *inner* family of the first application;
`N₂` and `τ` those of the *second*, whose inner family is the intermediate middle index set
`t''_τ` at the middle scale `τ`.  It is not the square of a single constant: the two
applications are made at different cardinalities and different scales, and no monotonicity of
`Kakeya.ml1Boot.factorOneScale.C` in either argument is available to compare them. -/
noncomputable def factorTwoScales.C (N₁ : ℕ) (δ : NNReal) (N₂ : ℕ) (τ : NNReal) : NNReal :=
  factorOneScale.C N₁ δ * factorOneScale.C N₂ τ

/-- **Composing two fullness losses** (blueprint `lem:ml1bootFullnessCompose`).

Substituting `λ₁ ≥ C₁⁻¹ δ ^ a λ₀` into `λ₂ ≥ C₂⁻¹ δ ^ b λ₁` is legitimate because
`C₂⁻¹ δ ^ b ≥ 0`, and gives `λ₂ ≥ (C₁ C₂)⁻¹ δ ^ (a + b) λ₀`.  This is the arithmetic behind the
fullness lower bounds of items (b) and (c) of blueprint `lem:ml1bootFactorTwoScales`.

The two applications of the one-scale step are made at different inner cardinalities and
different inner tube scales, so their loss constants are genuinely two constants and the
composed loss is their product, not a square. -/
theorem fullness_compose {C₁ C₂ : NNReal} (_hC₁ : 1 ≤ C₁) (_hC₂ : 1 ≤ C₂)
    {δ : NNReal} (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1)
    {a b : ℝ} (_ha : 0 ≤ a) (_hb : 0 ≤ b) {lam₀ lam₁ lam₂ : ENNReal}
    (h₁ : (C₁ : ENNReal)⁻¹ * (δ : ENNReal) ^ a * lam₀ ≤ lam₁)
    (h₂ : (C₂ : ENNReal)⁻¹ * (δ : ENNReal) ^ b * lam₁ ≤ lam₂) :
    ((C₁ : ENNReal) * (C₂ : ENNReal))⁻¹ * (δ : ENNReal) ^ (a + b) * lam₀ ≤ lam₂ := by
  have hC₁nz : (C₁ : ENNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one _hC₁))
  have hinv : (((C₁ : ENNReal) * (C₂ : ENNReal))⁻¹) =
      (C₁ : ENNReal)⁻¹ * (C₂ : ENNReal)⁻¹ := by
    exact ENNReal.mul_inv (Or.inl hC₁nz) (Or.inl ENNReal.coe_ne_top)
  have hδ0' : (δ : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hδ0)
  have hpow : (δ : ENNReal) ^ (a + b) = (δ : ENNReal) ^ a * (δ : ENNReal) ^ b :=
    ENNReal.rpow_add a b hδ0' ENNReal.coe_ne_top
  calc
    ((C₁ : ENNReal) * (C₂ : ENNReal))⁻¹ * (δ : ENNReal) ^ (a + b) * lam₀
        = (C₂ : ENNReal)⁻¹ * (δ : ENNReal) ^ b
            * ((C₁ : ENNReal)⁻¹ * (δ : ENNReal) ^ a * lam₀) := by
          rw [hinv, hpow]
          ring_nf
    _ ≤ (C₂ : ENNReal)⁻¹ * (δ : ENNReal) ^ b * lam₁ := by gcongr
    _ ≤ lam₂ := h₂

/-- **Composing two factoring losses** (blueprint `lem:ml1bootTwoScaleLossArith`).

Since `0 < δ ≤ σ ≤ 1` and `b ≥ 0` we have `σ ^ (-b) ≤ δ ^ (-b)`, so substituting
`B₁ ≤ C σ ^ (-b) B₃ B₄` into `A ≤ C δ ^ (-a) B₁ B₂` is monotone and gives
`A ≤ C² δ ^ (-a - b) B₂ B₃ B₄`.  This is what turns the two applications of
`Kakeya.ml1Boot.exists_factorOneScaleUniform` into the triple-product bound, with the *same*
auxiliary parameter `δ` measuring both losses even though the second application is made at
the tube scale `σ = τ`. -/
theorem twoScaleLoss {C : NNReal} (_hC : 1 ≤ C) {δ σ : NNReal} (hδ0 : 0 < δ) (hδσ : δ ≤ σ)
    (_hσ1 : σ ≤ 1) {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) {A B₁ B₂ B₃ B₄ : ENNReal}
    (hA : A ≤ (C : ENNReal) * (δ : ENNReal) ^ (-a) * B₁ * B₂)
    (hB : B₁ ≤ (C : ENNReal) * (σ : ENNReal) ^ (-b) * B₃ * B₄) :
    A ≤ (C : ENNReal) ^ 2 * (δ : ENNReal) ^ (-a - b) * B₂ * B₃ * B₄ := by
  have hσb : (σ : ENNReal) ^ (-b) ≤ (δ : ENNReal) ^ (-b) := by
    rw [← ENNReal.coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le hδ0 hδσ)) (-b),
        ← ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδ0) (-b)]
    exact ENNReal.coe_le_coe.mpr (NNReal.rpow_le_rpow_of_nonpos hδ0 hδσ (by linarith))
  have hB' : B₁ ≤ (C : ENNReal) * (δ : ENNReal) ^ (-b) * B₃ * B₄ := by
    exact le_trans hB (by
      calc
        (C : ENNReal) * (σ : ENNReal) ^ (-b) * B₃ * B₄
            ≤ (C : ENNReal) * (δ : ENNReal) ^ (-b) * B₃ * B₄ := by gcongr)
  have hB2 : (C : ENNReal) * (δ : ENNReal) ^ (-a) * B₁ * B₂ ≤
      (C : ENNReal) * (δ : ENNReal) ^ (-a) *
        ((C : ENNReal) * (δ : ENNReal) ^ (-b) * B₃ * B₄) * B₂ := by
    gcongr
  calc
    A ≤ (C : ENNReal) * (δ : ENNReal) ^ (-a) *
          ((C : ENNReal) * (δ : ENNReal) ^ (-b) * B₃ * B₄) * B₂ := le_trans hA hB2
    _ = (C : ENNReal) ^ 2 * (δ : ENNReal) ^ (-a - b) * B₂ * B₃ * B₄ := by
      have hpow : (δ : ENNReal) ^ (-a - b) = (δ : ENNReal) ^ (-a) * (δ : ENNReal) ^ (-b) := by
        rw [show -a - b = -a + -b by ring]
        exact ENNReal.rpow_add (-a) (-b) (by exact_mod_cast (ne_of_gt hδ0)) ENNReal.coe_ne_top
      rw [hpow]
      ring_nf

/-- **The conclusions of `Kakeya.ml1Boot.exists_factorOneScaleUniform`, one field per clause.**

Here `(𝕍, Z)` is a family of shaded `σ`-tubes indexed by `s`, `(t, 𝕍_ρ, p)` is a parent family
for `𝕍` at scale `ρ`, and `(tq, q)` is an auxiliary *classification* of the parent indices (see
below).  The output data is `s'`, `t''`, `t'q`, the shadings `Z'`, `Z_ρ` and the numbers
`λ_σ`, `λ_ρ`, `N`.  The fields are items (a)–(g) of the blueprint lemma
`lem:ml1bootFactorOneScaleUniform`, split one clause per field.

## The auxiliary classification `q`, and the clause that had to be removed

`q : κ → lc` is an arbitrary map, given *before* the refinement is chosen, together with a
finite index set `tq` of its values; `aux_subset` and `aux_card` retain a `δ ^ (2 ε')` fraction
of `tq` as `t'q`.  Both are harmless: `t'q := tq` always satisfies them.

The bundle used to carry a third clause, `coarse_fibre_card`, asserting that `t''` retains a
`δ ^ (2 ε')` fraction of every `q`-fibre `fibre t q l'` over `l' ∈ t'q`.  **That clause is
false**, and it has been removed.  Take `q` constant with `tq` a singleton; `aux_card` then
forces `t'q = tq`, and the clause collapses to the absolute `δ ^ (2 ε') |t| ≤ |t''|`, which is
the deleted `coarse_card` verbatim.  The *thin-parents* configuration refutes it, and it does
so with every parent carrying a member, so no surjectivity hypothesis repairs it: at `σ = δ`
and `ρ = δ ^ (1/2)`, let one parent `k₀` carry `⌈δ ^ (-1)⌉` pairwise essentially distinct
fully shaded `δ`-tubes and let `⌈δ ^ (-1/2)⌉` further parents carry one each.  The mass half
of `fine_refinement` reads `δ ^ (2 ε') ∑_{i ∈ s} |Z i| ≤ ∑_{i ∈ s'} |Z' i|` with
`∑_{i ∈ s} |Z i| ≍ δ ^ (-1) δ ^ 2 = δ`, while everything outside the class of `k₀` contributes
only `≍ δ ^ (-1/2) δ ^ 2 = δ ^ (3/2)`; so for `ε' < 1/4` and `δ` small the retained set must
keep `≳ δ ^ (2 ε' - 1)` members of that class, whence `k₀ ∈ t''` by `branch_mapsTo`.  The
bracket of `branch_card` is stated with a *single* `N`, so `N ≥ δ ^ (2 ε' - 1) / 2`, while
every thin parent has fibre cardinality at most `1 < N`; hence `t'' = {k₀}` and the clause
demands `δ ^ (2 ε') (1 + ⌈δ ^ (-1/2)⌉) ≤ 1`, which fails.

The obstruction is structural: one dyadic pigeonhole cannot simultaneously select the class
maximizing the number of *tubes* (which the mass clause forces) and retain a polynomial share
of the *parents* (which the deleted clause demanded), and the configuration above is exactly a
place where the two choices are incompatible.  `q`, `tq`, `t'q`, `aux_subset` and `aux_card`
are kept because callers are written against them, but they now carry no fibre information;
see the docstring of `Kakeya.ml1Boot.IsFactorTwoScales` for what this costs downstream and
blueprint `note:ml1bootLowerFrostmanFibre`. -/
structure IsFactorOneScale {ι κ lc : Type*} [DecidableEq κ] [DecidableEq lc]
    {σ ρ : NNReal} (δ : NNReal) (ε' : ℝ) (s : Finset ι) (V : ι → ShadedTube σ E)
    (t : Finset κ) (Vρ : κ → Tube ρ E) (p : ι → κ)
    (tq : Finset lc) (q : κ → lc)
    (s' : Finset ι) (t'' : Finset κ) (t'q : Finset lc)
    (Z' : ι → ShadedTube σ E) (Zρ : κ → ShadedTube ρ E)
    (lamσ lamρ N : NNReal) : Prop where
  /-- (a) The fine index set is a subset of `s`. -/
  fine_subset : s' ⊆ s
  /-- (a) `Z'` shades the same tubes as `𝕍` and is contained in `Z`. -/
  fine_shade : ∀ i ∈ s', (Z' i).toTube = (V i).toTube ∧ (Z' i).shade ⊆ (V i).shade
  /-- (a) `(𝕍|_{s'}, Z')` is a `δ ^ (2 ε')`-refinement of `(𝕍, Z)`. -/
  fine_refinement : ShadedBody.IsCRefinement s' (fun i => (Z' i).toShadedBody) s
    (fun i => (V i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩
  /-- (a) The fine family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  fine_unif : Nonempty (ShadedTube.ShadedUniformTubeSet s' Z' (Tube.ssfGridLen σ)
    (uniformize.C 3))
  /-- (a) Essential distinctness is inherited by the fine family. -/
  fine_essDistinct : (s' : Set ι).Pairwise
    (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier)
  /-- (a) The fine shading densities are two-sidedly comparable to `λ_σ`. -/
  fine_dens : ∀ i ∈ s', (lamσ : ENNReal) * volume (V i).carrier ≤ volume (Z' i).shade ∧
    volume (Z' i).shade ≤ 2 * (lamσ : ENNReal) * volume (V i).carrier
  /-- (a) `λ_σ ≥ δ ^ (2 ε') λ(𝕍, Z)`. -/
  fine_fullness : (δ : ENNReal) ^ (2 * ε')
      * ShadedBody.fullness s (fun i => (V i).toShadedBody) ≤ (lamσ : ENNReal)
  /-- (b) The coarse index set is a subset of `t`. -/
  coarse_subset : t'' ⊆ t
  /-- (b) `Z_ρ` shades the parent tubes. -/
  coarse_tube : ∀ k ∈ t'', (Zρ k).toTube = Vρ k
  /-- (b) The coarse family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  coarse_unif : Nonempty (ShadedTube.ShadedUniformTubeSet t'' Zρ (Tube.ssfGridLen ρ)
    (uniformize.C 3))
  /-- (b) Essential distinctness is inherited by the coarse family. -/
  coarse_essDistinct : (t'' : Set κ).Pairwise
    (fun k k' => IsEssentiallyDistinct (Vρ k).carrier (Vρ k').carrier)
  /-- (b) The coarse shading densities are two-sidedly comparable to `λ_ρ`. -/
  coarse_dens : ∀ k ∈ t'', (lamρ : ENNReal) * volume (Vρ k).carrier ≤ volume (Zρ k).shade ∧
    volume (Zρ k).shade ≤ 2 * (lamρ : ENNReal) * volume (Vρ k).carrier
  /-- (b) `λ_ρ ≥ C⁻¹ δ ^ (2 ε') λ(𝕍, Z)`, at `C = factorOneScale.C #s σ`. -/
  coarse_fullness : (factorOneScale.C s.card σ : ENNReal)⁻¹ * (δ : ENNReal) ^ (2 * ε')
      * ShadedBody.fullness s (fun i => (V i).toShadedBody) ≤ (lamρ : ENNReal)
  /-- (b) The retained classification index set is a subset of `tq`. -/
  aux_subset : t'q ⊆ tq
  /-- (b) A `δ ^ (2 ε')` fraction of the classification indices is retained. -/
  aux_card : (δ : ENNReal) ^ (2 * ε') * (tq.card : ENNReal) ≤ (t'q.card : ENNReal)
  /-- (c) The shadings are nested along the parent map. -/
  contain : ∀ i ∈ s', p i ∈ t'' → (Z' i).shade ⊆ (Zρ (p i)).shade
  /-- (d) Every retained member has its parent retained. -/
  branch_mapsTo : ∀ i ∈ s', p i ∈ t''
  /-- (d) The retained fibres have cardinality comparable to `N` and each retains a
  `δ ^ (2 ε')` fraction. -/
  branch_card : ∀ k ∈ t'',
    (N : ENNReal) ≤ ((fibre s' p k).card : ENNReal) ∧
    ((fibre s' p k).card : ENNReal) ≤ 2 * (N : ENNReal) ∧
    (δ : ENNReal) ^ (2 * ε') * ((fibre s p k).card : ENNReal)
      ≤ ((fibre s' p k).card : ENNReal)
  /-- (e) Every fibre Frostman constant grows by at most `δ ^ (-2 ε')`. -/
  frostman : ∀ k ∈ t'', ∀ K : ConvexSpaceBody E,
    (∀ i ∈ s, p i = k → (V i).toConvexSpaceBody ≤ K) →
    frostmanConstIn (fibre s' p k) (fun i => (V i).toConvexSpaceBody) K
      ≤ (δ : ENNReal) ^ (-2 * ε')
        * frostmanConstIn (fibre s p k) (fun i => (V i).toConvexSpaceBody) K
  /-- (f) The multiplicity factors with loss `C δ ^ (-2 ε')`, at `C = factorOneScale.C #s σ`. -/
  product : ∀ k ∈ t'', ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
    ≤ (factorOneScale.C s.card σ : ENNReal) * (δ : ENNReal) ^ (-2 * ε')
      * ShadedBody.multiplicity t'' (fun k' => (Zρ k').toShadedBody)
      * ShadedBody.multiplicity (fibre s' p k) (fun i => (Z' i).toShadedBody)
  /-- (g) Every retained fibre of the parent map is itself uniform, in the **one-sided** reading
  `Kakeya.IsFlatPrismUniform`: GWZ Definition 2.2 minus `le_card_shadeClass` and `branchingN_le`.
  Nothing along the consumer chain reads either dropped clause; see the module docstring. -/
  fibreUnif : ∀ k ∈ t'', Nonempty (IsFlatPrismUniform (fibre s' p k) Z'
    (Tube.ssfGridLen σ) (uniformize.C 3))

/-! #### The degenerate branch: a null shading

`Kakeya.ml1Boot.IsFactorOneScale` has **no** clause forcing either retained index set to be
nonempty: the absolute parent-counting clause `coarse_card` was deleted as refuted (see the
structure docstring), and every surviving clause is either a statement about members of `s'` or
`t''` or an inequality whose left-hand side vanishes with the shading.  So a family whose total
shading volume is `0` — which no hypothesis of `Kakeya.ml1Boot.exists_factorOneScaleUniform`
forbids, a `Kakeya.ShadedTube` only asking its shading to be a measurable subset of the carrier —
is handled by the *empty* refinement, with no pigeonholing at all.  That is what keeps
`Kakeya.ml1Boot.exists_factorOneScaleUniform` clear of the defect that refutes
`Kakeya.ml1Boot.exists_uniformRefinement`, whose `card` clause forces `s'` to be nonempty and
whose `dens` clause then demands a positive lower bound on a null shading.
-/

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Every scale admits a tube.**

A `Kakeya.Tube` is the closed `ρ`-neighbourhood of a segment of length exactly `1`, so producing
one needs only a unit vector, which a nontrivial normed space has:
`Kakeya.Tube.ofMidpointDirection` centred at the origin.

This is what lets the empty family carry uniformity data.
`Tube.GridCoverSystem` stores a node tube at *every* grid index, and those nodes are
unconstrained once the family is empty, so the only obstacle to building the bundle is producing
the tubes at all. -/
theorem nonempty_tube [Nontrivial E] (ρ : NNReal) : Nonempty (Tube ρ E) := by
  rcases exists_ne (0 : E) with ⟨v, hv⟩
  let u : E := ‖v‖⁻¹ • v
  have hvne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
    exact inv_mul_cancel₀ hvne
  exact ⟨Tube.ofMidpointDirection ρ 0 u hu⟩

/-- **The empty family is uniform, at every grid length and every constant.**

Every field of `ShadedTube.ShadedUniformTubeSet` and of the underlying
`Tube.UniformTubeSet` is either a statement about members of the index set, or one about
the nodes met by the family through the index set, or a cardinality bound on a subset of the node
index set; taking the index set and every node index set empty makes all of them vacuous or `0 ≤ C`.
Only the node tubes of the `Tube.GridCoverSystem` have to be produced, and
`Kakeya.ml1Boot.nonempty_tube` produces them.

`Kakeya.ml1Boot.IsFactorOneScale.fine_unif`, `coarse_unif` and `fibreUnif` are the only fields of
that bundle which are not vacuous when the retained index sets are empty, so this is exactly what
the degenerate branch of `Kakeya.ml1Boot.exists_factorOneScaleUniform` needs. -/
theorem nonempty_shadedUniformTubeSet_empty [Nontrivial E] {σ : NNReal} {ι : Type*}
    (V : ι → ShadedTube σ E) (N : ℕ) (C : NNReal) :
    Nonempty (ShadedTube.ShadedUniformTubeSet (∅ : Finset ι) V N C) := by
  classical
  let gcs : Tube.GridCoverSystem (∅ : Finset ι) (fun i => (V i).toTube) N :=
    { indexSet := fun _ => (∅ : Finset ι)
      assign := fun _ i => i
      tube := fun k _ => (nonempty_tube (Tube.gridScale σ N k)).some
      assign_mem := by simp
      le_tube_assign := by simp
      nested := by simp
      tube_nested := by simp }
  let utu : Tube.UniformTubeSet (∅ : Finset ι) (fun i => (V i).toTube) N C :=
    { cover := gcs
      branchingN := fun _ => 0
      tube_injOn := by simp [gcs]
      boundedOverlap := by simp [gcs]
      card_class_le := by simp [gcs]
      le_card_class := by simp [gcs] }
  refine ⟨{ tubeUniform := utu
            branchingN := fun _ => 0
            localN := fun _ _ => 0
            card_shadeClass_le := by simp
            le_card_shadeClass := by simp
            branchingN_le := by simp
            le_branchingN := by simp }⟩

/-- **A null total shading has null fullness.**

`ShadedBody.fullness` is the quotient of the total shading volume by the total carrier volume, so
it vanishes as soon as the numerator does; in `ENNReal` this needs no hypothesis on the
denominator, `0 / 0` being `0`. -/
theorem fullness_eq_zero_of_sum_shade_eq_zero {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E)
    (h : ∑ i ∈ s, volume (V i).shade = 0) : ShadedBody.fullness s V = 0 := by
  rw [← ENNReal.coe_inj]
  rw [ShadedBody.fullness_def, h]
  simp

/-- **The auxiliary parameter is eventually at most `1`.**

`Set.Iio 1` is a neighbourhood of `0` in `NNReal`, so it belongs to `𝓝[>] 0`.  This is the only
smallness that the degenerate branch of `Kakeya.ml1Boot.exists_factorOneScaleUniform` consumes: it
is what makes `δ ^ (2 ε') ≤ 1`, hence `Kakeya.ml1Boot.IsFactorOneScale.aux_card` true at
`t'q = tq`. -/
theorem eventually_le_one_nhdsGT : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, δ ≤ 1 := by
  filter_upwards
    [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : NNReal) < 1 by norm_num))] with δ hδ
  exact le_of_lt hδ

omit [BorelSpace E] in
/-- **A null shading of a prescribed tube.**

The tube `T` shaded by `∅`.  This is the coarse shading of the degenerate branch of
`Kakeya.ml1Boot.exists_factorOneScaleUniform`: `Kakeya.ml1Boot.IsFactorOneScale.coarse_dens` and
`coarse_tube` quantify over the retained coarse index set, which is empty there, so nothing
constrains the shading and the cheapest one will do. -/
theorem exists_nullShadedTube {ρ : NNReal} (T : Tube ρ E) :
    ∃ Z : ShadedTube ρ E, Z.toTube = T ∧ Z.shade = ∅ := by
  exact ⟨{ toTube := T, shade := ∅, measurableSet_shade := MeasurableSet.empty,
           shade_subset := Set.empty_subset _ }, rfl, rfl⟩

/-- **A subpolynomial factor is at most `1`.**

For `δ ≤ 1` and a nonnegative exponent, `δ ^ a ≤ 1` in `[0, ∞]`; multiplying a cardinality by it
therefore only decreases it.  This is `Kakeya.ml1Boot.IsFactorOneScale.aux_card` at the choice
`t'q = tq`, which the structure docstring records as always admissible. -/
theorem rpow_mul_card_le_card {δ : NNReal} (hδ1 : δ ≤ 1) {a : ℝ} (ha : 0 ≤ a)
    {lc : Type*} (tq : Finset lc) :
    (δ : ENNReal) ^ a * (tq.card : ENNReal) ≤ (tq.card : ENNReal) := by
  have hp : (δ : ENNReal) ^ a ≤ 1 := ENNReal.rpow_le_one (by exact_mod_cast hδ1) ha
  exact mul_le_of_le_one_left zero_le hp

/-- **The auxiliary parameter is eventually at most any prescribed positive bound.**

`Set.Iio c` is a neighbourhood of `0` in `NNReal` whenever `0 < c`, so it belongs to `𝓝[>] 0`.
This is the generic form of `Kakeya.ml1Boot.eventually_le_one_nhdsGT`; it is what turns a
smallness condition on `δ` alone — such as the one in
`Kakeya.ml1Boot.card_le_rpow_neg_seven` — into a clause of a `∀ᶠ δ in 𝓝[>] 0` statement. -/
theorem eventually_le_nhdsGT {c : NNReal} (hc : 0 < c) : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, δ ≤ c := by
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hc)] with δ hδ
  exact le_of_lt hδ

/-- **The constant-free cardinality bound for essentially distinct tubes in `B₁ ⊆ ℝ³`.**

A family of pairwise essentially distinct `σ`-tubes contained in `B₁ ⊆ ℝ³` has at most
`δ ^ (-7)` members, for every tube scale `σ ≥ δ` and every `δ` small enough that
`δ · C ≤ 1`, where `C = Tube.card_le_of_EssDistinct.C 3 = 78 ^ 6 + 1`.

The input is `Tube.card_le_of_EssDistinct` at radius `r = 1` in dimension `n = 3`, which gives
the *constant-carrying* bound `#s ≤ C · σ ^ (-6) ≤ C · δ ^ (-6)`; the smallness of `δ` absorbs
`C` into one further power of `1 / δ`, which is where the exponent `7` comes from.  The
`ℝ`-valued `Tube.card_le_of_EssDistinct` is used rather than the sharper `ENNReal`-valued
`Kakeya.ml1Boot.card_le` (exponent `-4`) because the shape wanted downstream is literally the
`ℝ`-valued, constant-free hypothesis `(s.card : ℝ) ≤ · ^ (-K₀)` of the shaded uniformization;
the extra exponent is free, since `K₀` only enters there through the choice of the threshold.

Note that the bound is stated at the *auxiliary* parameter `δ` and not at the tube scale `σ`:
`σ` may be as large as `1`, and `σ ≥ δ` makes `σ ^ (-6) ≤ δ ^ (-6)`.  This is exactly the form
in which `Kakeya.ml1Boot.exists_uniformFactorPair` needs it, and the form the two-scale step
would need, both quantifying over `δ ≤ σ ≤ 1`.  (The two-scale step has no declaration:
`exists_twoScaleFactorPair` is not one, see blueprint
`note:ml1bootCaseTwoConstructionLayerEmpty`.)

It is written for the shaded-uniformization *interface* discussed at
`Kakeya.ml1Boot.not_exists_uniformRefinement` — which is a shape and not a declaration, the
sorried `exists_shadedUniform_of_card_le` that used to record it having been deleted
(`Kakeya/DimensionThree/MainLemma1/Inventory.lean`, §B) — and **not** for
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`.  The Section 2 statement reads its
cardinality hypothesis at its own single scale variable, which is the tube scale of the family;
applied to a family of `σ`-tubes it therefore asks for `#s ≤ σ ^ (-K₀)`, and since `δ ≤ σ` the
bound proved here is *weaker* than that, not stronger.  No choice of `K₀` repairs this: the only
bound available at the tube scale is `#s ≤ C σ ^ (-6)`, and `σ ^ (-K₀) ≥ C σ ^ (-6)` fails for
`σ` near `1`, where `σ ^ (6 - K₀) < C`.  See the docstring of
`Kakeya.ml1Boot.exists_uniformFactorCore` for the interface shape in full. -/
theorem card_le_rpow_neg_seven (hdim : Module.finrank ℝ E = 3) {δ σ : NNReal}
    (hδ0 : 0 < δ) (hδσ : δ ≤ σ)
    (hδC : (δ : ℝ) * Tube.card_le_of_EssDistinct.C 3 ≤ 1)
    {ι : Type*} (s : Finset ι) (V : ι → Tube σ E)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (hED : (s : Set ι).Pairwise
      fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) :
    (s.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) := by
  haveI : Nontrivial E := by
    exact Module.finrank_pos_iff.mp (by rw [hdim]; norm_num)
  have hσ0 : 0 < σ := hδ0.trans_le hδσ
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hσR : 0 < (σ : ℝ) := by exact_mod_cast hσ0
  have hC0 : 0 ≤ Tube.card_le_of_EssDistinct.C 3 :=
    (Tube.card_le_of_EssDistinct.C_pos (n := 3)).le
  have hcard0 : (s.card : ℝ) ≤
      Tube.card_le_of_EssDistinct.C 3 * (1 / (σ : ℝ)) ^ 6 := by
    have h' := Tube.card_le_of_EssDistinct (E := E) (δ := σ) hσ0 (1 : ℝ) s V hball hED
    rw [hdim] at h'
    simpa using h'
  have h_one_over_le : (1 : ℝ) / (σ : ℝ) ≤ (1 : ℝ) / (δ : ℝ) := by
    rw [div_le_div_iff₀ hσR hδR]
    simpa using (NNReal.coe_le_coe.mpr hδσ)
  have h_pow_le : ((1 : ℝ) / (σ : ℝ)) ^ 6 ≤ ((1 : ℝ) / (δ : ℝ)) ^ 6 := by
    exact pow_le_pow_left₀ (by positivity) h_one_over_le 6
  have hfun : Tube.card_le_of_EssDistinct.C 3 * (1 / (σ : ℝ)) ^ 6 ≤
      Tube.card_le_of_EssDistinct.C 3 * (1 / (δ : ℝ)) ^ 6 := by
    exact mul_le_mul_of_nonneg_left h_pow_le hC0
  have hsix : (1 / (δ : ℝ)) ^ 6 = (δ : ℝ) ^ (-(6 : ℝ)) := by
    simp [Real.rpow_neg (le_of_lt hδR) (6 : ℝ), one_div, inv_pow]
  have hC_le_inv : Tube.card_le_of_EssDistinct.C 3 ≤ (δ : ℝ)⁻¹ := by
    rw [← one_div]
    rw [le_div_iff₀ hδR]
    simpa [mul_comm] using hδC
  have hneg1 : (δ : ℝ) ^ (-(1 : ℝ)) = (δ : ℝ)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hδR) (1 : ℝ)]
    simp
  have hC_le_neg1 : Tube.card_le_of_EssDistinct.C 3 ≤ (δ : ℝ) ^ (-(1 : ℝ)) := by
    rw [hneg1]
    exact hC_le_inv
  calc
    (s.card : ℝ) ≤ Tube.card_le_of_EssDistinct.C 3 * (1 / (δ : ℝ)) ^ 6 :=
      le_trans hcard0 hfun
    _ = Tube.card_le_of_EssDistinct.C 3 * (δ : ℝ) ^ (-(6 : ℝ)) := by rw [hsix]
    _ ≤ (δ : ℝ) ^ (-(1 : ℝ)) * (δ : ℝ) ^ (-(6 : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hC_le_neg1 (Real.rpow_nonneg (le_of_lt hδR) _)
    _ = (δ : ℝ) ^ (-(7 : ℝ)) := by
      rw [← Real.rpow_add hδR]
      congr 1
      norm_num

/-- **The cardinality bound of `Kakeya.ml1Boot.card_le_rpow_neg_seven`, as a smallness clause
in `δ`.**

The smallness hypothesis `δ · C ≤ 1` of `Kakeya.ml1Boot.card_le_rpow_neg_seven` constrains the
auxiliary parameter alone, so it may be absorbed into the `∀ᶠ δ in 𝓝[>] 0` prefix that every
statement of this file carries.  In this form the bound is a hypothesis-free consequence of the
geometry, and it discharges the cardinality hypothesis of the shaded-uniformization interface at
`K₀ = 7` — that being a shape and not a declaration, the sorried
`exists_shadedUniform_of_card_le` that used to record it having been deleted
(`Kakeya/DimensionThree/MainLemma1/Inventory.lean`, §B).

It does **not** discharge the cardinality hypothesis of
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`, which is read at the tube scale rather
than at the auxiliary parameter and is therefore a strictly stronger demand; see the docstring
of `Kakeya.ml1Boot.card_le_rpow_neg_seven`. -/
theorem eventually_card_le_rpow_neg_seven (hdim : Module.finrank ℝ E = 3) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ σ : NNReal, δ ≤ σ →
      ∀ {ι : Type*} (s : Finset ι) (V : ι → Tube σ E),
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) →
        (s.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) := by
  let c : NNReal :=
    ⟨(Tube.card_le_of_EssDistinct.C 3 : ℝ)⁻¹, by
      exact inv_nonneg.mpr (le_of_lt (show 0 < Tube.card_le_of_EssDistinct.C 3
        from Tube.card_le_of_EssDistinct.C_pos (n := 3)))⟩
  have hcR : 0 < (c : ℝ) := by
    dsimp [c]
    exact inv_pos.mpr (by exact_mod_cast (Tube.card_le_of_EssDistinct.C_pos (n := 3)))
  have hc : 0 < c := by
    exact_mod_cast hcR
  filter_upwards [eventually_le_nhdsGT (c := c) hc, self_mem_nhdsWithin] with δ hδ hδ0
  intro σ hσ ι s V hball hED
  have hδ0' : 0 < δ := hδ0
  have hTCpos : 0 < (Tube.card_le_of_EssDistinct.C 3 : ℝ) := by
    exact_mod_cast (Tube.card_le_of_EssDistinct.C_pos (n := 3))
  have hδC : (δ : ℝ) * (Tube.card_le_of_EssDistinct.C 3 : ℝ) ≤ 1 := by
    calc
      (δ : ℝ) * (Tube.card_le_of_EssDistinct.C 3 : ℝ)
          ≤ (c : ℝ) * (Tube.card_le_of_EssDistinct.C 3 : ℝ) := by
            exact mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hδ) (le_of_lt hTCpos)
      _ = 1 := by
            have hb : (c : ℝ) = (Tube.card_le_of_EssDistinct.C 3 : ℝ)⁻¹ := rfl
            rw [hb]
            exact inv_mul_cancel₀ (ne_of_gt hTCpos)
  exact card_le_rpow_neg_seven hdim hδ0' hσ hδC s V hball hED

/-- **The loss of a shade-volume banding of a family of `n` shaded tubes.**

`8 (1 + log₂ (2 n))`, in `[0, ∞]`.  It depends on the *cardinality* of the family alone, and this
is the whole point: the naive density banding of
`Kakeya.ShadedBody.exists_isCRefinement_comparable_density` has loss `1 + log₂ (1/a)`, where `a` is
a lower bound for the shading densities, and the only such bound available from
`ShadedBody.isCRefinement_discardLowShading` is `a ≍ λ(𝕍, Z)`.  Nothing in this development bounds
the fullness `λ(𝕍, Z)` from below by a power of `δ` — the hypothesis of
`Kakeya.ml1Boot.exists_uniformFactorCore` is only `0 < ∑_{i ∈ s} |Z i|` — so that loss is *not*
subpolynomial in `δ` uniformly in the family, and the density banding cannot be made to fit the
budget `δ ^ (2 ε')` that way.

Banding the shade *volumes* relative to their maximum instead of relative to the fullness repairs
this.  Members carrying less than `1/(2 n)` of the maximum carry at most half the total mass in
aggregate, so discarding them is free; what survives lies in a range of ratio at most `2 n`, and a
dyadic pigeonhole over a range of ratio `R` costs `1 + log₂ R`.  Since all tubes at a fixed scale
have the same carrier volume (`Kakeya.Tube.volume_carrier_eq_volume_carrier`), a band of the shade
volumes *is* a band of the shading densities.

The two factors of `2` and the leading `8` are slack, so that the same constant serves both
conclusions of `Kakeya.ml1Boot.exists_massBand`. -/
noncomputable def bandLoss (n : ℕ) : ENNReal :=
  8 * ENNReal.ofReal (1 + Real.logb 2 (2 * (n : ℝ)))

/-- **The banding loss is eventually subpolynomial, for families of subpolynomial size.**

`Kakeya.ml1Boot.bandLoss n` grows like `log n`, so a cardinality bound `n ≤ δ ^ (-7)` — which is
what `Kakeya.ml1Boot.eventually_card_le_rpow_neg_seven` supplies for a family of pairwise
essentially distinct tubes in `B₁ ⊆ ℝ³` — makes it at most `δ ^ (-η)` for every fixed `η > 0` and
all sufficiently small `δ`.  This is the step that makes the banding of
`Kakeya.ml1Boot.exists_massBand` affordable inside the budget of
`Kakeya.ml1Boot.IsUniformFactorCore.fine_refinement`, and it is the reason the banding has to be
by shade volume rather than by density; see the docstring of `Kakeya.ml1Boot.bandLoss`. -/
theorem eventually_bandLoss_le_rpow_neg {η : ℝ} (hη : 0 < η) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ n : ℕ, (n : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) →
      bandLoss n ≤ (δ : ENNReal) ^ (-η) := by
  filter_upwards [nnreal_eventually_of_real_eventually
      (absorb_log_le_rpow_neg (C := 72 / Real.log 2) (M := 1) (η := η / 2)
        (by positivity) one_pos (by linarith)),
    eventually_le_nhdsGT (c := (1 / 2 : NNReal)) (by norm_num),
    self_mem_nhdsWithin] with δ habs hδ2 hδmem
  have hδ0 : 0 < δ := hδmem
  have hηe : -(2 * (η / 2)) = -η := by ring
  have habs' : (72 / Real.log 2) * (1 * Real.log (1 / (δ : ℝ))) ≤ (δ : ℝ) ^ (-η) := by
    simpa [hηe] using habs
  intro n hn
  rw [ennreal_coe_nnreal_rpow (by exact_mod_cast hδ0) (-η)]
  have hpt : bandLoss n ≤ ENNReal.ofReal (72 * Real.logb 2 (1 / (δ : ℝ))) := by
    unfold bandLoss
    let L : ℝ := Real.logb 2 (1 / (δ : ℝ))
    have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ0
    have hδle : 0 ≤ (δ : ℝ) := hδR.le
    have hq : 0 < 1 / (δ : ℝ) := by positivity
    -- 1/δ ≥ 2
    have hinv : 2 ≤ 1 / (δ : ℝ) := by
      rw [le_div_iff₀ hδR]
      have hδ2R : (δ : ℝ) ≤ 1 / 2 := by exact_mod_cast hδ2
      nlinarith
    -- logb 2 2 = 1
    have hL2 : Real.logb 2 (2 : ℝ) = 1 := by
      rw [Real.logb]
      exact div_self (Real.log_ne_zero.mpr (by norm_num))
    have h1 : 1 ≤ L := by
      have hmono :=
        (Real.logb_le_logb (by norm_num : 1 < (2 : ℝ)) (by norm_num : 0 < (2 : ℝ)) hq).2 hinv
      rwa [hL2] at hmono
    -- exponent identity (δ)^(-7) = (1/δ)^7
    have hpow7 : (δ : ℝ) ^ (-(7 : ℝ)) = (1 / (δ : ℝ)) ^ (7 : ℝ) := by
      rw [Real.rpow_neg hδle (7 : ℝ)]
      rw [← Real.inv_rpow hδle (7 : ℝ)]
      simp [one_div]
    have h2 : Real.logb 2 (2 * (n : ℝ)) ≤ 1 + 7 * L := by
      by_cases hn0 : n = 0
      · subst n
        norm_num
        nlinarith [h1]
      · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
        have h2n : 0 < 2 * (n : ℝ) := by positivity
        have hnle : 2 * (n : ℝ) ≤ 2 * (δ : ℝ) ^ (-(7 : ℝ)) := by nlinarith
        have hpos2 : 0 < 2 * (δ : ℝ) ^ (-(7 : ℝ)) := by
          rw [hpow7]
          positivity
        have hmono := (Real.logb_le_logb (by norm_num : 1 < (2 : ℝ)) h2n hpos2).2 hnle
        have hname : Real.logb 2 (2 * (δ : ℝ) ^ (-(7 : ℝ))) = 1 + 7 * L := by
          rw [hpow7]
          rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0)
            (ne_of_gt (Real.rpow_pos_of_pos hq (7 : ℝ)))]
          rw [Real.logb_rpow_eq_mul_logb_of_pos hq]
          rw [hL2]
        rwa [hname] at hmono
    calc
      8 * ENNReal.ofReal (1 + Real.logb 2 (2 * (n : ℝ)))
          ≤ 8 * ENNReal.ofReal (9 * L) := by
            exact mul_le_mul_of_nonneg_left
              (ENNReal.ofReal_le_ofReal (by nlinarith [h2, h1])) (by norm_num)
        _ = ENNReal.ofReal (72 * L) := by
            rw [show 72 * L = 8 * (9 * L) by ring]
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
            norm_num
  exact le_trans hpt (ENNReal.ofReal_le_ofReal (by
    calc
      72 * Real.logb 2 (1 / (δ : ℝ)) = (72 / Real.log 2) * (1 * Real.log (1 / (δ : ℝ))) := by
        simp [Real.logb]
        ring
      _ ≤ (δ : ℝ) ^ (-η) := habs'))

/-- **A cardinality bound `n ≤ δ ^ (-7)` makes the banding loss a multiple of `log (1/δ)`.**

The pointwise half of `Kakeya.ml1Boot.eventually_bandLoss_le_rpow_neg`, separated because it is pure
real analysis and involves no filter: for `δ ≤ 1/2` one has `log₂ (1/δ) ≥ 1`, so the additive
constants of `bandLoss` are themselves absorbed into a multiple of `log₂ (1/δ)`, and
`log₂ (2 n) ≤ 1 + 7 log₂ (1/δ)` by monotonicity of `log₂`.  The case `n = 0` is covered because
`Real.logb 2 0 = 0`. -/
theorem bandLoss_le_ofReal_logb {δ : NNReal} (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2) {n : ℕ}
    (hn : (n : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ))) :
    bandLoss n ≤ ENNReal.ofReal (72 * Real.logb 2 (1 / (δ : ℝ))) := by
  classical
  set L : ℝ := Real.logb 2 (1 / (δ : ℝ)) with hLdef
  have hd0 : 0 < (δ : ℝ) := NNReal.coe_pos.mpr hδ0
  have hd22 : (δ : ℝ) ≤ (1 : ℝ) / 2 := by
    exact_mod_cast hδ2
  have h2le : 2 ≤ 1 / (δ : ℝ) := by
    rw [le_div_iff₀' hd0]
    nlinarith
  have hL1 : 1 ≤ L := by
    have hleL : Real.logb 2 (2 : ℝ) ≤ L := by
      dsimp [L]
      exact (Real.logb_le_logb (b := 2) (by norm_num : 1 < (2 : ℝ))
        (by norm_num : 0 < (2 : ℝ)) (one_div_pos.mpr hd0)).mpr h2le
    simpa using hleL
  have hr : 8 * (1 + Real.logb 2 (2 * (n : ℝ))) ≤ 72 * L := by
    by_cases hn0 : n = 0
    · have hlog : Real.logb 2 (2 * (n : ℝ)) = 0 := by
        rw [hn0]
        simp
      rw [hlog]
      nlinarith [hL1]
    · have hn1 : 1 ≤ n := by omega
      have hn' : 0 < (n : ℝ) := by exact_mod_cast hn1
      have hle1 : Real.logb 2 (n : ℝ) ≤ Real.logb 2 ((δ : ℝ) ^ (-(7 : ℝ))) := by
        exact (Real.logb_le_logb (b := 2) (by norm_num : 1 < (2 : ℝ)) hn'
          (Real.rpow_pos_of_pos hd0 (-(7 : ℝ)))).mpr hn
      have hln : Real.logb 2 (n : ℝ) ≤ 7 * L := by
        calc
          Real.logb 2 (n : ℝ) ≤ Real.logb 2 ((δ : ℝ) ^ (-(7 : ℝ))) := hle1
          _ = 7 * L := by
            rw [Real.logb_rpow_eq_mul_logb_of_pos (b := 2) hd0]
            dsimp [L]
            have hreflog : Real.logb 2 (1 / (δ : ℝ)) = -Real.logb 2 (δ : ℝ) := by
              simp
            rw [hreflog]
            ring
      have hlogmul : Real.logb 2 (2 * (n : ℝ)) = 1 + Real.logb 2 (n : ℝ) := by
        have h := Real.logb_mul (b := 2) (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hn')
        simp [h]
      have keep : Real.logb 2 (2 * (n : ℝ)) ≤ 1 + 7 * L := by
        rw [hlogmul]
        nlinarith [hln]
      nlinarith [keep, hL1]
  calc
    bandLoss n = ENNReal.ofReal (8 * (1 + Real.logb 2 (2 * (n : ℝ)))) := by
      simp [bandLoss, ENNReal.ofReal_mul]
    _ ≤ ENNReal.ofReal (72 * L) := ENNReal.ofReal_le_ofReal hr

/-- **Discarding the members lying far below the maximum keeps half of the total.**

If every term of a finite sum of extended reals is at most `μ`, and `μ` itself is at most the sum,
then the terms `x i` with `2 #s · x i < μ` contribute at most half the sum: there are at most `#s`
of them and each is below `μ / (2 #s)`.  So the complementary set retains half.

This is the discarding step of `Kakeya.ml1Boot.exists_massBand`, stated for a bare family of
extended reals because nothing geometric enters.  It plays the role that
`ShadedBody.isCRefinement_discardLowShading` plays for the density banding, but with the threshold
read off the *maximum* term rather than off the fullness — which is the whole point of the shade
volume banding; see the docstring of `Kakeya.ml1Boot.bandLoss`. -/
theorem sum_le_two_mul_sum_filter_of_le_max {ι : Type*} (s : Finset ι) (x : ι → ENNReal)
    {μ : ENNReal} (hmax : ∀ i ∈ s, x i ≤ μ) (hμ : μ ≤ ∑ i ∈ s, x i)
    (htop : ∑ i ∈ s, x i ≠ ⊤) :
    ∑ i ∈ s, x i
      ≤ 2 * ∑ i ∈ (open scoped Classical in
          s.filter (fun i => μ ≤ 2 * (s.card : ENNReal) * x i)), x i := by
  classical
  let M : ENNReal := ∑ i ∈ s, x i
  let F : Finset ι := s.filter (fun i => μ ≤ 2 * (s.card : ENNReal) * x i)
  let G : Finset ι := s.filter (fun i => ¬ (μ ≤ 2 * (s.card : ENNReal) * x i))
  by_cases hs : s = ∅
  · subst s
    simp
  · have hne : s.Nonempty := (Finset.nonempty_iff_ne_empty).mpr hs
    have hcard_pos : 0 < s.card := Finset.card_pos.mpr hne
    have hcard0 : (s.card : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hcard_pos)
    have hcardtop : (s.card : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hsum : (∑ i ∈ F, x i) + (∑ i ∈ G, x i) = M := by
      unfold F G M
      rw [← Finset.sum_filter_add_sum_filter_not (s := s)
        (p := fun i => μ ≤ 2 * (s.card : ENNReal) * x i) x]
    have hG_le : ∀ i ∈ G, 2 * (s.card : ENNReal) * x i ≤ μ := by
      intro i hi
      have hlt : 2 * (s.card : ENNReal) * x i < μ :=
        lt_of_not_ge (by simpa [G] using (Finset.mem_filter.mp hi).2)
      exact le_of_lt hlt
    have hcancel : 2 * (∑ i ∈ G, x i) ≤ μ := by
      have hsumG_le : 2 * (s.card : ENNReal) * (∑ i ∈ G, x i) ≤ (s.card : ENNReal) * μ := by
        calc
          2 * (s.card : ENNReal) * (∑ i ∈ G, x i) = ∑ i ∈ G, 2 * (s.card : ENNReal) * x i := by
            rw [Finset.mul_sum]
          _ ≤ ∑ i ∈ G, μ := by
            exact Finset.sum_le_sum hG_le
          _ = (G.card : ENNReal) * μ := by
            rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (s.card : ENNReal) * μ := by
            have hcG : (G.card : ENNReal) ≤ (s.card : ENNReal) := by
              dsimp [G]
              exact_mod_cast (Finset.card_filter_le s
                (fun i => ¬ (μ ≤ 2 * (s.card : ENNReal) * x i)))
            exact mul_le_mul_of_nonneg_right hcG (by positivity)
      have hrw : 2 * (s.card : ENNReal) * (∑ i ∈ G, x i)
          = (s.card : ENNReal) * (2 * (∑ i ∈ G, x i)) := by
        ring
      have hright : (2 * (∑ i ∈ G, x i)) * (s.card : ENNReal)
          ≤ μ * (s.card : ENNReal) := by
        calc
          (2 * (∑ i ∈ G, x i)) * (s.card : ENNReal)
              = (s.card : ENNReal) * (2 * (∑ i ∈ G, x i)) := by rw [mul_comm]
          _ ≤ (s.card : ENNReal) * μ := by simpa [hrw] using hsumG_le
          _ = μ * (s.card : ENNReal) := by rw [mul_comm]
      exact (ENNReal.mul_le_mul_iff_left hcard0 hcardtop).1 hright
    have h2G_le_M : 2 * (∑ i ∈ G, x i) ≤ M := le_trans hcancel hμ
    have h2M : 2 * M ≤ 2 * (∑ i ∈ F, x i) + M := by
      calc
        2 * M = 2 * ((∑ i ∈ F, x i) + (∑ i ∈ G, x i)) := by rw [← hsum]
        _ = 2 * (∑ i ∈ F, x i) + 2 * (∑ i ∈ G, x i) := by rw [mul_add]
        _ ≤ 2 * (∑ i ∈ F, x i) + M := by
          gcongr
    have hfin : M ≤ 2 * (∑ i ∈ F, x i) := by
      have hMtop : M ≠ ⊤ := htop
      have h2M' : M + M ≤ 2 * (∑ i ∈ F, x i) + M := by
        simpa [two_mul] using h2M
      exact (ENNReal.add_le_add_iff_right hMtop).1 h2M'
    simpa [M, F] using hfin

/-- **Banding a finite family of extended reals into a factor-two window, at a loss logarithmic in
the cardinality.**

A finite family `(x i)_{i ∈ s}` of extended reals with positive finite total has a subfamily on
which the values lie in a window `[μ, 2 μ]` with `μ > 0`, retaining all but a factor
`2 (1 + log₂ (2 #s))` of the total.

This is the combinatorial core of `Kakeya.ml1Boot.exists_massBand`, with the geometry stripped out.
Two steps: discard the members below `1/(2 #s)` of the maximum, which
`Kakeya.ml1Boot.sum_le_two_mul_sum_filter_of_le_max` shows costs a factor `2`; what survives lies in
a range of ratio at most `2 #s`, and `ENNReal.dyadic_pigeonhole₁''` extracts a factor-two window
from it at a cost `1 + log₂ (2 #s)`.

The loss depends on the *cardinality* and on nothing else — in particular not on how small the
values are — which is exactly what the density banding of
`Kakeya.ShadedBody.exists_isCRefinement_comparable_density` fails to achieve; see the docstring of
`Kakeya.ml1Boot.bandLoss`. -/
theorem exists_twoSidedBand {ι : Type*} (s : Finset ι) (x : ι → ENNReal)
    (hpos : 0 < ∑ i ∈ s, x i) (htop : ∑ i ∈ s, x i ≠ ⊤) :
    ∃ s₂ ⊆ s, ∃ μ : ENNReal, 0 < μ ∧ μ ≠ ⊤ ∧ s₂.Nonempty ∧
      (∀ i ∈ s₂, μ ≤ x i ∧ x i ≤ 2 * μ) ∧
      ∑ i ∈ s, x i
        ≤ 2 * ENNReal.ofReal (1 + Real.logb 2 (2 * (s.card : ℝ))) * ∑ i ∈ s₂, x i := by
  classical
  -- 0. s is nonempty
  have hsne : s.Nonempty := by
    by_contra h
    have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hsempty] at hpos
  have hcard_pos : 0 < s.card := Finset.card_pos.mpr hsne
  have hcard_nn : (s.card : NNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hcard_pos)
  have hcard_enn : (s.card : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hcard_pos)
  have hcard_ℝ : (s.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hcard_pos)
  have hxi_le_sum : ∀ i ∈ s, x i ≤ ∑ i ∈ s, x i := by
    intro i hi
    exact Finset.single_le_sum (fun i _ => bot_le) hi
  have hxi_top : ∀ i ∈ s, x i ≠ ⊤ := by
    intro i hi
    exact ne_top_of_le_ne_top htop (hxi_le_sum i hi)
  -- 1. maximum
  rcases Finset.exists_max_image s x hsne with ⟨iₘ, hiₘ, hmax⟩
  let ν : ENNReal := x iₘ
  have hν_top : ν ≠ ⊤ := by simpa [ν] using hxi_top iₘ hiₘ
  have hν_pos : 0 < ν := by
    by_contra h
    have hle0 : ν ≤ 0 := le_of_not_gt h
    have hsum0 : ∑ i ∈ s, x i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact le_antisymm (le_trans (hmax i hi) hle0) bot_le
    exact (ne_of_gt hpos) hsum0
  have hν_le_sum : ν ≤ ∑ i ∈ s, x i := by simpa [ν] using hxi_le_sum iₘ hiₘ
  have hν_ne0 : ν ≠ 0 := ne_of_gt hν_pos
  -- 2. discard low members
  let s₁ : Finset ι := s.filter (fun i => ν ≤ 2 * (s.card : ENNReal) * x i)
  have hs₁ss : s₁ ⊆ s := Finset.filter_subset _ s
  have hsum₁ : ∑ i ∈ s, x i ≤ 2 * ∑ i ∈ s₁, x i := by
    have hA := sum_le_two_mul_sum_filter_of_le_max s x (fun i hi => by simpa [ν] using hmax i hi)
      (by simpa [ν] using hν_le_sum) htop
    simpa [s₁] using hA
  have hone_le : (1 : ENNReal) ≤ 2 * (s.card : ENNReal) := by
    have hc1 : (1 : ℕ) ≤ s.card := Nat.succ_le_of_lt hcard_pos
    have h1 : (1 : ENNReal) ≤ (s.card : ENNReal) := by exact_mod_cast hc1
    have h2 : (s.card : ENNReal) ≤ (2 : ENNReal) * (s.card : ENNReal) := by
      calc
        (s.card : ENNReal) = (1 : ENNReal) * (s.card : ENNReal) := by rw [one_mul]
        _ ≤ (2 : ENNReal) * (s.card : ENNReal) := by
          exact mul_le_mul_of_nonneg_right (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal)) zero_le
    exact h1.trans h2
  have hmₘ_s₁ : iₘ ∈ s₁ := by
    apply Finset.mem_filter.mpr
    constructor
    · exact hiₘ
    · dsimp [ν]
      calc
        x iₘ = 1 * x iₘ := by rw [one_mul]
        _ ≤ (2 * (s.card : ENNReal)) * x iₘ := by
          exact mul_le_mul_of_nonneg_right hone_le zero_le
        _ = 2 * (s.card : ENNReal) * x iₘ := by rfl
  have hs₁ne : s₁.Nonempty := ⟨iₘ, hmₘ_s₁⟩
  have hs₁_pos : 0 < ∑ i ∈ s₁, x i := by
    have hx : x iₘ ≤ ∑ i ∈ s₁, x i :=
      Finset.single_le_sum (fun i _ => bot_le) hmₘ_s₁
    exact lt_of_lt_of_le (by simpa [ν] using hν_pos) hx
  -- 3. NNReal normalisation
  let N : NNReal := ν.toNNReal
  have hN_coe : (N : ENNReal) = ν := by
    dsimp [N]
    exact ENNReal.coe_toNNReal hν_top
  have hN_pos : 0 < N := by
    dsimp [N]
    exact ENNReal.toNNReal_pos hν_ne0 hν_top
  have hN_ne0 : N ≠ 0 := ne_of_gt hN_pos
  let b : NNReal := N
  let a : NNReal := N / (2 * (s.card : NNReal))
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have h2nn : (2 * (s.card : NNReal) : NNReal) ≠ 0 := by
    exact mul_ne_zero (by norm_num : (2 : NNReal) ≠ 0) hcard_nn
  have ha_coe : (a : ENNReal) = ν / (2 * (s.card : ENNReal)) := by
    dsimp [a]
    rw [ENNReal.coe_div h2nn]
    rw [hN_coe]
    simp
  have hNℝ : (N : ℝ) ≠ 0 := by exact_mod_cast hN_ne0
  have hratio : (b : ℝ) / (a : ℝ) = 2 * (s.card : ℝ) := by
    dsimp [a, b]
    norm_cast
    field_simp [hNℝ, hcard_ℝ]
    norm_num
  -- 4. pigeonhole
  have hden0 : (2 * (s.card : ENNReal)) ≠ 0 := by
    exact mul_ne_zero (by norm_num : (2 : ENNReal) ≠ 0) hcard_enn
  have hdenTop : (2 * (s.card : ENNReal)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top 2) (ENNReal.natCast_ne_top s.card)
  have hIcc : ∀ i ∈ s₁, x i ∈ Set.Icc (a : ENNReal) (b : ENNReal) := by
    intro i hi
    rw [Set.mem_Icc]
    constructor
    · rw [ha_coe]
      have hc : ν ≤ 2 * (s.card : ENNReal) * x i := (Finset.mem_filter.mp hi).2
      refine (ENNReal.div_le_iff_le_mul (Or.inl hden0) (Or.inl hdenTop)).mpr ?_
      rwa [mul_comm] at hc
    · have his : i ∈ s := hs₁ss hi
      have hxh : x i ≤ ν := by simpa [ν] using hmax i his
      change x i ≤ (b : ENNReal)
      dsimp [b]
      rw [hN_coe]
      exact hxh
  rcases ENNReal.dyadic_pigeonhole₁'' (s := s₁) x x (a := a) (b := b) ha_pos hIcc with
    ⟨s₂, hs₂s₁, hsum₂, hband⟩
  -- 5. s₂ nonempty
  have hs₂ne : s₂.Nonempty := by
    by_contra h
    have hs₂empty : s₂ = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have h₁le0 : (∑ i ∈ s₁, x i) ≤ 0 := by
      have hz : ENNReal.ofReal (1 + Real.logb 2 ((b : ℝ) / a)) * (∑ i ∈ s₂, x i) = 0 := by
        simp [hs₂empty]
      simpa [hz] using hsum₂
    exact (not_lt_of_ge h₁le0) hs₁_pos
  -- 6. minimum on s₂
  rcases Finset.exists_min_image s₂ x hs₂ne with ⟨i₁, hi₁₂, hmin⟩
  let μ : ENNReal := x i₁
  have hi₁s₁ : i₁ ∈ s₁ := hs₂s₁ hi₁₂
  have hμ_pos : 0 < μ := by
    have hlb : ν ≤ 2 * (s.card : ENNReal) * x i₁ := (Finset.mem_filter.mp hi₁s₁).2
    have hx_ne0 : x i₁ ≠ 0 := by
      intro hx
      have : 0 < (2 * (s.card : ENNReal)) * x i₁ := lt_of_lt_of_le hν_pos hlb
      simp [hx] at this
    have hposx : 0 < x i₁ := lt_of_le_of_ne zero_le (Ne.symm hx_ne0)
    simpa [μ] using hposx
  have hμ_top : μ ≠ ⊤ := by
    have hi₁s : i₁ ∈ s := hs₁ss hi₁s₁
    have hle : x i₁ ≤ ∑ i ∈ s, x i := Finset.single_le_sum (fun i _ => bot_le) hi₁s
    simpa [μ] using (ne_top_of_le_ne_top htop hle)
  have hwindow : ∀ i ∈ s₂, μ ≤ x i ∧ x i ≤ 2 * μ := by
    intro i hi
    constructor
    · simpa [μ] using hmin i hi
    · simpa [μ] using hband i hi i₁ hi₁₂
  -- 7. assemble
  refine ⟨s₂, hs₂s₁.trans hs₁ss, μ, hμ_pos, hμ_top, hs₂ne, hwindow, ?_⟩
  have hof : ENNReal.ofReal (1 + Real.logb 2 ((b : ℝ) / a))
      = ENNReal.ofReal (1 + Real.logb 2 (2 * (s.card : ℝ))) := by
    rw [hratio]
  calc
    ∑ i ∈ s, x i ≤ 2 * ∑ i ∈ s₁, x i := hsum₁
    _ ≤ 2 * (ENNReal.ofReal (1 + Real.logb 2 ((b : ℝ) / a)) * ∑ i ∈ s₂, x i) := by
      exact mul_le_mul_of_nonneg_left hsum₂ (by positivity)
    _ = 2 * (ENNReal.ofReal (1 + Real.logb 2 (2 * (s.card : ℝ))) * ∑ i ∈ s₂, x i) := by
      rw [hof]
    _ = (2 * ENNReal.ofReal (1 + Real.logb 2 (2 * (s.card : ℝ)))) * ∑ i ∈ s₂, x i := by
      rw [← mul_assoc]

/-- **Banding the shade volumes of a family of shaded tubes, at a loss depending on the
cardinality alone.**

A family of shaded `σ`-tubes of positive total shading volume has a subfamily on which the
shading densities are two-sidedly comparable to a single positive `λ`, at the cost of a factor
`Kakeya.ml1Boot.bandLoss #s` in the retained mass, and with `λ` at least
`(bandLoss #s)⁻¹ λ(𝕍, Z)`.

This is the pigeonhole that the shaded-uniformization interface needs of its input: that
interface asks for a two-sided density bracket at some `λ₀ > 0`, and no hypothesis of
`Kakeya.ml1Boot.exists_uniformFactorCore` provides one.  (The interface has no Lean carrier; the
sorried `exists_shadedUniform_of_card_le` that used to record it was deleted, see
`Kakeya/DimensionThree/MainLemma1/Inventory.lean`, §B.)  It is *not*
`Kakeya.ShadedBody.exists_isCRefinement_comparable_density`, whose loss is not subpolynomial in
`δ` uniformly in the family; see the docstring of `Kakeya.ml1Boot.bandLoss` for why, and
`Kakeya.ml1Boot.eventually_bandLoss_le_rpow_neg` for the bound that makes this one affordable.

Note that the shading is *not* changed: the conclusion is a statement about the given `Z`, with
only the index set cut down.  That is what lets the interface be applied to the output and its
`fine_shade` clause be read off against the original family. -/
theorem exists_massBand [Nontrivial E] {σ : NNReal} (hσ0 : 0 < σ)
    {ι : Type*} (s : Finset ι) (V : ι → ShadedTube σ E)
    (hmass : 0 < ∑ i ∈ s, volume (V i).shade) :
    ∃ s₂ ⊆ s, ∃ lam : NNReal, 0 < lam ∧ s₂.Nonempty ∧
      (∀ i ∈ s₂, (lam : ENNReal) * volume (V i).carrier ≤ volume (V i).shade ∧
        volume (V i).shade ≤ 2 * (lam : ENNReal) * volume (V i).carrier) ∧
      ∑ i ∈ s, volume (V i).shade ≤ bandLoss s.card * ∑ i ∈ s₂, volume (V i).shade ∧
      (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal)
        ≤ bandLoss s.card * (lam : ENNReal) := by
  classical
  have hs_nonempty : s.Nonempty := by
    by_contra hne
    have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hs_empty] at hmass
  rcases hs_nonempty with ⟨i₀, hi₀⟩
  set M : ENNReal := ∑ i ∈ s, volume (V i).shade with hM_def
  have hv0_t : 0 < volume (V i₀).toTube.carrier := by
    have hc : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) := by
      exact ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))
    have hσp : 0 < (σ : ENNReal) ^ (Module.finrank ℝ E - 1) := by
      exact ENNReal.pow_pos (ENNReal.coe_pos.mpr hσ0) (Module.finrank ℝ E - 1)
    have hpos : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
        (σ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
      ENNReal.mul_pos (ne_of_gt hc) (ne_of_gt hσp)
    exact lt_of_lt_of_le hpos (by simpa using _root_.Tube.le_volume (V i₀).toTube)
  let v : ENNReal := volume (V i₀).carrier
  have hv_pos : 0 < v := by simpa [v] using hv0_t
  have hv_top : v ≠ ⊤ := by
    have htop : volume (V i₀).toTube.carrier ≠ ⊤ :=
      (V i₀).toTube.isCompact.measure_lt_top.ne
    simpa [v] using htop
  have hcarrier : ∀ i, volume (V i).carrier = v := by
    intro i
    calc
      volume (V i).carrier = volume (V i₀).carrier := by
        simpa using
          _root_.Tube.volume_carrier_eq_volume_carrier (V i).toTube (V i₀).toTube
      _ = v := rfl
  have hsum_car : ∑ i ∈ s, volume (V i).carrier = (s.card : ENNReal) * v := by
    simpa [v] using
      _root_.Tube.sum_volume_carrier_eq_card_mul (fun i => (V i).toTube) (V i₀).toTube s
  have hM_le : M ≤ (s.card : ENNReal) * v := by
    calc
      M ≤ ∑ i ∈ s, volume (V i).carrier := by
        simpa [M] using Finset.sum_le_sum (fun i hi => measure_mono (V i).shade_subset)
      _ = (s.card : ENNReal) * v := hsum_car
  have hcard0 : (s.card : ENNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Finset.card_pos.mpr ⟨i₀, hi₀⟩))
  have hcardtop : (s.card : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hden0 : (s.card : ENNReal) * v ≠ 0 := ne_of_gt (ENNReal.mul_pos hcard0 (ne_of_gt hv_pos))
  have hdenTop : (s.card : ENNReal) * v ≠ ⊤ := ENNReal.mul_ne_top hcardtop hv_top
  have hM_top : M ≠ ⊤ := by
    exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hM_le (lt_top_iff_ne_top.mpr hdenTop))
  rcases exists_twoSidedBand s (fun i => volume (V i).shade) hmass hM_top with
    ⟨s₂, hss₂, μ, hμ0, hμtop, hs₂ne, hwindow, htotal⟩
  set ofL : ENNReal := ENNReal.ofReal (1 + Real.logb 2 (2 * (s.card : ℝ))) with hofL
  let lam : NNReal := (μ / v).toNNReal
  have hμv0 : μ / v ≠ 0 := ne_of_gt (ENNReal.div_pos (ne_of_gt hμ0) hv_top)
  have hμvTop : μ / v ≠ ⊤ := ENNReal.div_ne_top hμtop (ne_of_gt hv_pos)
  have hlam_pos : 0 < lam := by
    exact ENNReal.toNNReal_pos hμv0 hμvTop
  have hlam_coe : (lam : ENNReal) = μ / v := by
    exact ENNReal.coe_toNNReal hμvTop
  have hlam_mul : (lam : ENNReal) * v = μ := by
    rw [hlam_coe]
    exact ENNReal.div_mul_cancel (ne_of_gt hv_pos) hv_top
  have hdens : ∀ i ∈ s₂, (lam : ENNReal) * volume (V i).carrier ≤ volume (V i).shade ∧
      volume (V i).shade ≤ 2 * (lam : ENNReal) * volume (V i).carrier := by
    intro i hi
    constructor
    · calc
        (lam : ENNReal) * volume (V i).carrier = (lam : ENNReal) * v := by rw [hcarrier i]
        _ = μ := hlam_mul
        _ ≤ volume (V i).shade := (hwindow i hi).1
    · calc
        volume (V i).shade ≤ 2 * μ := (hwindow i hi).2
        _ = 2 * ((lam : ENNReal) * v) := by rw [← hlam_mul]
        _ = 2 * (lam : ENNReal) * v := by rw [mul_assoc]
        _ = 2 * (lam : ENNReal) * volume (V i).carrier := by rw [hcarrier i]
  have hmassBand : M ≤ bandLoss s.card * (∑ i ∈ s₂, volume (V i).shade) := by
    calc
      M ≤ 2 * ofL * (∑ i ∈ s₂, volume (V i).shade) := htotal
      _ ≤ bandLoss s.card * (∑ i ∈ s₂, volume (V i).shade) := by
        change (2 : ENNReal) * ofL * (∑ i ∈ s₂, volume (V i).shade)
            ≤ (8 : ENNReal) * ofL * (∑ i ∈ s₂, volume (V i).shade)
        gcongr
        norm_num
  have hfull_eq :
      (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal)
        = M / ((s.card : ENNReal) * v) := by
    rw [ShadedBody.fullness_def]
    congr 1
  have hRhs : M ≤ (8 : ENNReal) * ofL * (lam : ENNReal) * ((s.card : ENNReal) * v) := by
    have hM2_le : (∑ i ∈ s₂, volume (V i).shade) ≤ (s₂.card : ENNReal) * (2 * μ) := by
      calc
        ∑ i ∈ s₂, volume (V i).shade ≤ ∑ i ∈ s₂, 2 * μ := by
          exact Finset.sum_le_sum (fun i hi => (hwindow i hi).2)
        _ = (s₂.card : ENNReal) * (2 * μ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    calc
      M ≤ 2 * ofL * (∑ i ∈ s₂, volume (V i).shade) := htotal
      _ ≤ 2 * ofL * ((s₂.card : ENNReal) * (2 * μ)) := by
        gcongr
      _ ≤ 2 * ofL * ((s.card : ENNReal) * (2 * μ)) := by
        gcongr
      _ = (4 : ENNReal) * ofL * μ * (s.card : ENNReal) := by ring
      _ = (4 : ENNReal) * ofL * ((lam : ENNReal) * v) * (s.card : ENNReal) := by
        rw [← hlam_mul]
      _ ≤ (8 : ENNReal) * ofL * ((lam : ENNReal) * v) * (s.card : ENNReal) := by
        gcongr
        norm_num
      _ = (8 : ENNReal) * ofL * (lam : ENNReal) * ((s.card : ENNReal) * v) := by ring
  have hfull_le :
      (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal)
        ≤ bandLoss s.card * (lam : ENNReal) := by
    rw [hfull_eq]
    change M / ((s.card : ENNReal) * v) ≤ (8 : ENNReal) * ofL * (lam : ENNReal)
    rw [ENNReal.div_le_iff hden0 hdenTop]
    exact hRhs
  exact ⟨s₂, hss₂, lam, hlam_pos, hs₂ne, hdens, hmassBand, hfull_le⟩

/-- **The empty subfamily is a `c`-refinement of a null-shaded family, for every `c`.**

`ShadedBody.IsRefinement` is vacuous on the empty index set, and the mass clause of
`ShadedBody.IsCRefinement` reads `c · 0 ≤ 0`.  No positivity or upper bound on `c` is needed.

This is the field `Kakeya.ml1Boot.IsFactorOneScale.fine_refinement` in the degenerate branch of
`Kakeya.ml1Boot.exists_factorOneScaleUniform`, and it is the precise point at which that branch
needs the total shading volume to vanish: for a family of positive total shading volume the empty
refinement retains no mass at all. -/
theorem isCRefinement_empty_of_sum_shade_eq_zero {ι : Type*} (s : Finset ι)
    (V : ι → ShadedBody E) (c : NNReal) (h : ∑ i ∈ s, volume (V i).shade = 0) :
    ShadedBody.IsCRefinement (∅ : Finset ι) V s V c := by
  refine ⟨⟨Finset.empty_subset s, by simp⟩, ?_⟩
  simp [h]

/-- **The degenerate branch of `Kakeya.ml1Boot.exists_factorOneScaleUniform`: a null shading.**

When the total shading volume of `(𝕍, Z)` vanishes, `Kakeya.ml1Boot.IsFactorOneScale` is satisfied
by the *empty* refinement: `s' = ∅`, `t'' = ∅`, `t'q = tq`, the fine shading left as `Z` and the
coarse shading null, with `λ_σ = λ_ρ = N = 1`.

Field by field: `fine_shade`, `fine_essDistinct`, `fine_dens`, `coarse_tube`,
`coarse_essDistinct`, `coarse_dens`, `contain`, `branch_mapsTo`, `branch_card`, `frostman`,
`product` and `fibreUnif` are vacuous, quantifying over a member of `s' = ∅` or of `t'' = ∅`; the
mass half of `fine_refinement` reads `δ ^ (2 ε') · 0 ≤ 0`; both fullness clauses read `0 ≤ 1`
because `Kakeya.ml1Boot.fullness_eq_zero_of_sum_shade_eq_zero` makes the fullness vanish;
`fine_unif` and `coarse_unif` are `Kakeya.ml1Boot.nonempty_shadedUniformTubeSet_empty`; and
`aux_card` holds at `t'q = tq` because `δ ≤ 1` and `2 ε' ≥ 0` give `δ ^ (2 ε') ≤ 1`.

No hypothesis of `Kakeya.ml1Boot.exists_factorOneScaleUniform` is used beyond `δ ≤ 1`: in
particular neither the parent family nor either essential-distinctness assumption enters.  This is
the half of the case split on the total shading volume that needs no pigeonholing; the other half
is `Kakeya.ml1Boot.exists_uniformFactorPair`, whose shading-density bracket is unobtainable
exactly when this branch applies. -/
theorem exists_factorOneScale_of_sum_shade_eq_zero [Nontrivial E] {δ : NNReal} (hδ1 : δ ≤ 1)
    {ε' : ℝ} (hε' : 0 < ε') {σ ρ : NNReal}
    {ι κ lc : Type*} [DecidableEq κ] [DecidableEq lc] {s : Finset ι} {t : Finset κ}
    {tq : Finset lc}
    (V : ι → ShadedTube σ E) (Vρ : κ → Tube ρ E) (p : ι → κ) (q : κ → lc)
    (hmass : ∑ i ∈ s, volume (V i).shade = 0) :
    ∃ (s' : Finset ι) (t'' : Finset κ) (t'q : Finset lc)
      (Z' : ι → ShadedTube σ E) (Zρ : κ → ShadedTube ρ E),
      ∃ lamσ lamρ N : NNReal, 0 < lamσ ∧ 0 < lamρ ∧ 0 < N ∧
        IsFactorOneScale δ ε' s V t Vρ p tq q s' t'' t'q Z' Zρ lamσ lamρ N := by
  classical
  choose Zρ hZρtube hZρshade using fun k => exists_nullShadedTube (E := E) (Vρ k)
  refine ⟨∅, ∅, tq, V, Zρ, 1, 1, 1, one_pos, one_pos, one_pos, ?_⟩
  have hfull : ShadedBody.fullness s (fun i => (V i).toShadedBody) = 0 :=
    fullness_eq_zero_of_sum_shade_eq_zero s (fun i => (V i).toShadedBody) (by simpa using hmass)
  exact { fine_subset := Finset.empty_subset s
          fine_shade := by simp
          fine_refinement := isCRefinement_empty_of_sum_shade_eq_zero s
            (fun i => (V i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩
            (by simpa using hmass)
          fine_unif := nonempty_shadedUniformTubeSet_empty V (Tube.ssfGridLen σ)
            (uniformize.C 3)
          fine_essDistinct := by simp
          fine_dens := by simp
          fine_fullness := by simp [hfull]
          coarse_subset := Finset.empty_subset t
          coarse_tube := by simp
          coarse_unif := nonempty_shadedUniformTubeSet_empty Zρ (Tube.ssfGridLen ρ)
            (uniformize.C 3)
          coarse_essDistinct := by simp
          coarse_dens := by simp
          coarse_fullness := by simp [hfull]
          aux_subset := Finset.Subset.refl tq
          aux_card := rpow_mul_card_le_card hδ1 (by positivity : 0 ≤ 2 * ε') tq
          contain := by simp
          branch_mapsTo := by simp
          branch_card := by simp
          frostman := by simp
          product := by simp
          fibreUnif := by simp }

/-- **The leaf-dependent part of `Kakeya.ml1Boot.IsFactorOneScale`.**

`Kakeya.ml1Boot.IsFactorOneScale` with the five clauses that do *not* depend on the Section 2
uniformization leaf removed:

* `fine_essDistinct` and `coarse_essDistinct`, which are `Set.Pairwise.mono` along
  `fine_subset` and `coarse_subset`;
* `aux_subset` and `aux_card`, which hold at `t'q = tq` by
  `Kakeya.ml1Boot.rpow_mul_card_le_card`;
* `frostman`, which is `ConvexSpaceBody.frostmanConstIn_subfamily_le` applied to the fibre
  retention already recorded in `branch_card`.

`Kakeya.ml1Boot.isFactorOneScale_of_core` proves all five, so this bundle and
`Kakeya.ml1Boot.IsFactorOneScale` differ only by proved material.  Splitting them is what lets
the gap of `Kakeya.ml1Boot.exists_uniformFactorPair` be stated without them.

The auxiliary classification `(tq, q, t'q)` of `Kakeya.ml1Boot.IsFactorOneScale` is absent here
for the same reason: it carries no information that the construction has to supply. -/
structure IsUniformFactorCore {ι κ : Type*} [DecidableEq κ]
    {σ ρ : NNReal} (δ : NNReal) (ε' : ℝ) (s : Finset ι) (V : ι → ShadedTube σ E)
    (t : Finset κ) (Vρ : κ → Tube ρ E) (p : ι → κ)
    (s' : Finset ι) (t'' : Finset κ)
    (Z' : ι → ShadedTube σ E) (Zρ : κ → ShadedTube ρ E)
    (lamσ lamρ N : NNReal) : Prop where
  /-- The fine index set is a subset of `s`. -/
  fine_subset : s' ⊆ s
  /-- `Z'` shades the same tubes as `𝕍` and is contained in `Z`. -/
  fine_shade : ∀ i ∈ s', (Z' i).toTube = (V i).toTube ∧ (Z' i).shade ⊆ (V i).shade
  /-- `(𝕍|_{s'}, Z')` is a `δ ^ (2 ε')`-refinement of `(𝕍, Z)`. -/
  fine_refinement : ShadedBody.IsCRefinement s' (fun i => (Z' i).toShadedBody) s
    (fun i => (V i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩
  /-- The fine family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  fine_unif : Nonempty (ShadedTube.ShadedUniformTubeSet s' Z' (Tube.ssfGridLen σ)
    (uniformize.C 3))
  /-- The fine shading densities are two-sidedly comparable to `λ_σ`. -/
  fine_dens : ∀ i ∈ s', (lamσ : ENNReal) * volume (V i).carrier ≤ volume (Z' i).shade ∧
    volume (Z' i).shade ≤ 2 * (lamσ : ENNReal) * volume (V i).carrier
  /-- `λ_σ ≥ δ ^ (2 ε') λ(𝕍, Z)`. -/
  fine_fullness : (δ : ENNReal) ^ (2 * ε')
      * ShadedBody.fullness s (fun i => (V i).toShadedBody) ≤ (lamσ : ENNReal)
  /-- The coarse index set is a subset of `t`. -/
  coarse_subset : t'' ⊆ t
  /-- `Z_ρ` shades the parent tubes. -/
  coarse_tube : ∀ k ∈ t'', (Zρ k).toTube = Vρ k
  /-- The coarse family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  coarse_unif : Nonempty (ShadedTube.ShadedUniformTubeSet t'' Zρ (Tube.ssfGridLen ρ)
    (uniformize.C 3))
  /-- The coarse shading densities are two-sidedly comparable to `λ_ρ`. -/
  coarse_dens : ∀ k ∈ t'', (lamρ : ENNReal) * volume (Vρ k).carrier ≤ volume (Zρ k).shade ∧
    volume (Zρ k).shade ≤ 2 * (lamρ : ENNReal) * volume (Vρ k).carrier
  /-- `λ_ρ ≥ C⁻¹ δ ^ (2 ε') λ(𝕍, Z)`, at `C = factorOneScale.C #s σ`. -/
  coarse_fullness : (factorOneScale.C s.card σ : ENNReal)⁻¹ * (δ : ENNReal) ^ (2 * ε')
      * ShadedBody.fullness s (fun i => (V i).toShadedBody) ≤ (lamρ : ENNReal)
  /-- The shadings are nested along the parent map. -/
  contain : ∀ i ∈ s', p i ∈ t'' → (Z' i).shade ⊆ (Zρ (p i)).shade
  /-- Every retained member has its parent retained. -/
  branch_mapsTo : ∀ i ∈ s', p i ∈ t''
  /-- The retained fibres have cardinality comparable to `N` and each retains a
  `δ ^ (2 ε')` fraction. -/
  branch_card : ∀ k ∈ t'',
    (N : ENNReal) ≤ ((fibre s' p k).card : ENNReal) ∧
    ((fibre s' p k).card : ENNReal) ≤ 2 * (N : ENNReal) ∧
    (δ : ENNReal) ^ (2 * ε') * ((fibre s p k).card : ENNReal)
      ≤ ((fibre s' p k).card : ENNReal)
  /-- The multiplicity factors with loss `C δ ^ (-2 ε')`, at `C = factorOneScale.C #s σ`. -/
  product : ∀ k ∈ t'', ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
    ≤ (factorOneScale.C s.card σ : ENNReal) * (δ : ENNReal) ^ (-2 * ε')
      * ShadedBody.multiplicity t'' (fun k' => (Zρ k').toShadedBody)
      * ShadedBody.multiplicity (fibre s' p k) (fun i => (Z' i).toShadedBody)
  /-- Every retained fibre of the parent map is itself uniform, in the **one-sided** reading
  `Kakeya.IsFlatPrismUniform`.  Read this way the clause is a *consequence* of `fine_unif` at the
  same constant, by
  `Kakeya.ml1Boot.nonempty_isFlatPrismUniform_fibre_of_shadedUniformTubeSet`, so it costs the
  producer nothing; see the docstring of `Kakeya.ml1Boot.exists_uniformFactorCore`. -/
  fibreUnif : ∀ k ∈ t'', Nonempty (IsFlatPrismUniform (fibre s' p k) Z'
    (Tube.ssfGridLen σ) (uniformize.C 3))

/-- **Fibrewise uniformity is free in the one-sided reading: same constant, no loss.**

`Kakeya.ml1Boot.IsUniformFactorCore.fibreUnif` used to ask for a *two-sided*
`ShadedTube.ShadedUniformTubeSet` on every fibre `fibre s' p k`, at the very shading `Z'` that
`fine_unif` uniformizes globally.  That joint demand was the simultaneity obstruction of
`Kakeya.ml1Boot.exists_uniformFactorCore`: nothing transports a two-sided
hierarchy to a subfamily, `le_card_shadeClass` and `branchingN_le` being lower bounds on filtered
cardinalities, which shrink under restriction.

This lemma is what isolated how much of that obstruction was real, and it is now what discharges
the field.  Drop the two lower brackets — read uniformity as `Kakeya.IsFlatPrismUniform`, the
one-sided half of GWZ Definition 2.2 that the downstream chain is in fact typed against — and the
fibre clause becomes a *consequence* of the global one, at the same constant, with no pigeonholing
and no shrinking of the shading.  The simultaneity obstruction was therefore not a statement about
fibres: it was precisely and only the demand for the two lower brackets, and since the field is now
stated one-sidedly it is gone.

The route is `Kakeya.IsFlatPrismUniform.of_shadedUniformTubeSet_subset` at `Finset.filter_subset`,
a fibre being a filter of `s'`. -/
theorem nonempty_isFlatPrismUniform_fibre_of_shadedUniformTubeSet
    {ι κ : Type*} [DecidableEq κ] {σ : NNReal} {s' : Finset ι} {Z' : ι → ShadedTube σ E}
    {N : ℕ} {C : NNReal} (p : ι → κ) (k : κ)
    (h : Nonempty (ShadedTube.ShadedUniformTubeSet s' Z' N C)) :
    Nonempty (IsFlatPrismUniform (fibre s' p k) Z' N C) := by
  rcases h with ⟨𝒱⟩
  exact ⟨IsFlatPrismUniform.of_shadedUniformTubeSet_subset 𝒱 (by
    simp [fibre])⟩

/-- **The core bundle gives the full one-scale bundle.**

Every clause of `Kakeya.ml1Boot.IsFactorOneScale` that is absent from
`Kakeya.ml1Boot.IsUniformFactorCore` is a consequence of the core together with the hypotheses
of `Kakeya.ml1Boot.exists_factorOneScaleUniform`, at the choice `t'q = tq`:

* `fine_essDistinct` and `coarse_essDistinct` restrict the given pairwise conditions along
  `fine_subset` and `coarse_subset`; essential distinctness is a condition on pairs.
* `aux_subset` is `Finset.Subset.refl` and `aux_card` is
  `Kakeya.ml1Boot.rpow_mul_card_le_card`, using `δ ≤ 1` and `0 ≤ 2 ε'`.
* `frostman` is `ConvexSpaceBody.frostmanConstIn_subfamily_le` at `κ = δ ^ (2 ε')`, whose
  cardinality hypothesis is the third clause of `branch_card` and whose common-volume
  hypothesis holds because all `σ`-tubes have the same carrier volume; the retained fibre is
  nonempty because `0 < N` bounds it below.

This is the precise sense in which the gap of `Kakeya.ml1Boot.exists_uniformFactorPair` is
narrower than the bundle it produces. -/
theorem isFactorOneScale_of_core [Nontrivial E] {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {ε' : ℝ} (hε' : 0 < ε') {σ ρ : NNReal}
    {ι κ lc : Type*} [DecidableEq κ] [DecidableEq lc] {s : Finset ι} {t : Finset κ}
    {tq : Finset lc} {V : ι → ShadedTube σ E} {Vρ : κ → Tube ρ E} {p : ι → κ} {q : κ → lc}
    {s' : Finset ι} {t'' : Finset κ} {Z' : ι → ShadedTube σ E} {Zρ : κ → ShadedTube ρ E}
    {lamσ lamρ N : NNReal} (hN : 0 < N)
    (hED : (s : Set ι).Pairwise fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier)
    (hEDρ : (t : Set κ).Pairwise
      fun k k' => IsEssentiallyDistinct (Vρ k).carrier (Vρ k').carrier)
    (hcore : IsUniformFactorCore δ ε' s V t Vρ p s' t'' Z' Zρ lamσ lamρ N) :
    IsFactorOneScale δ ε' s V t Vρ p tq q s' t'' tq Z' Zρ lamσ lamρ N := by
  classical
  refine {
    fine_subset := hcore.fine_subset
    fine_shade := hcore.fine_shade
    fine_refinement := hcore.fine_refinement
    fine_unif := hcore.fine_unif
    fine_essDistinct := ?_
    fine_dens := hcore.fine_dens
    fine_fullness := hcore.fine_fullness
    coarse_subset := hcore.coarse_subset
    coarse_tube := hcore.coarse_tube
    coarse_unif := hcore.coarse_unif
    coarse_essDistinct := ?_
    coarse_dens := hcore.coarse_dens
    coarse_fullness := hcore.coarse_fullness
    aux_subset := ?_
    aux_card := ?_
    contain := hcore.contain
    branch_mapsTo := hcore.branch_mapsTo
    branch_card := hcore.branch_card
    frostman := ?_
    product := hcore.product
    fibreUnif := hcore.fibreUnif }
  · exact hED.mono (Finset.coe_subset.mpr hcore.fine_subset)
  · exact hEDρ.mono (Finset.coe_subset.mpr hcore.coarse_subset)
  · exact Finset.Subset.refl tq
  · exact rpow_mul_card_le_card hδ1 (by positivity : 0 ≤ 2 * ε') tq
  · intro k hk K hK
    have hbc := hcore.branch_card k hk
    have hfibre_sub : fibre s' p k ⊆ fibre s p k := by
      unfold fibre
      exact Finset.filter_subset_filter (fun i => p i = k) hcore.fine_subset
    have hlt : (0 : ENNReal) < ((fibre s' p k).card : ENNReal) :=
      lt_of_lt_of_le (by exact_mod_cast hN) hbc.1
    have hpos_card : 0 < (fibre s' p k).card := by
      exact_mod_cast hlt
    have hne_s : (fibre s p k).Nonempty := by
      have hne_s' : (fibre s' p k).Nonempty := Finset.card_pos.mp hpos_card
      rcases hne_s' with ⟨i, hi⟩
      exact ⟨i, hfibre_sub hi⟩
    obtain ⟨i₀, hi₀⟩ := id hne_s
    let v : ENNReal := volume ((V i₀).toConvexSpaceBody).carrier
    have hvol : ∀ i ∈ fibre s p k, volume ((V i).toConvexSpaceBody).carrier = v := by
      intro i hi
      have h := Tube.volume_carrier_eq_volume_carrier (V i).toTube (V i₀).toTube
      simpa [v] using h
    have hκ : (δ : ENNReal) ^ (2 * ε') ≠ 0 := by
      exact ne_of_gt (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ0) ENNReal.coe_ne_top)
    have hKfib : ∀ i ∈ fibre s p k, (V i).toConvexSpaceBody ≤ K := by
      intro i hi
      have himem : i ∈ s.filter (fun j => p j = k) := by
        simpa [fibre] using hi
      rcases Finset.mem_filter.mp himem with ⟨his, hp⟩
      exact hK i his hp
    have hf := ConvexSpaceBody.frostmanConstIn_subfamily_le
      (s := fibre s p k) (s' := fibre s' p k)
      (W := fun i => (V i).toConvexSpaceBody) (K := K) (κ := (δ : ENNReal) ^ (2 * ε'))
      (v := v) hne_s hvol hKfib hfibre_sub hκ hbc.2.2
    rw [← ENNReal.rpow_neg, ← show -2 * ε' = -(2 * ε') by ring] at hf
    exact hf

theorem isUniformFactorCore_of_isFactorOneScale
    {δ : NNReal} {ε' : ℝ} {σ ρ : NNReal}
    {ι κ lc : Type*} [DecidableEq κ] [DecidableEq lc]
    {s : Finset ι} {t : Finset κ} {tq : Finset lc} {q : κ → lc}
    {V : ι → ShadedTube σ E} {Vρ : κ → Tube ρ E} {p : ι → κ}
    {s' : Finset ι} {t'' : Finset κ} {t'q : Finset lc}
    {Z' : ι → ShadedTube σ E} {Zρ : κ → ShadedTube ρ E}
    {lamσ lamρ N : NNReal}
    (h : IsFactorOneScale δ ε' s V t Vρ p tq q s' t'' t'q Z' Zρ lamσ lamρ N) :
    IsUniformFactorCore δ ε' s V t Vρ p s' t'' Z' Zρ lamσ lamρ N := by
  exact {
    fine_subset := h.fine_subset
    fine_shade := h.fine_shade
    fine_refinement := h.fine_refinement
    fine_unif := h.fine_unif
    fine_dens := h.fine_dens
    fine_fullness := h.fine_fullness
    coarse_subset := h.coarse_subset
    coarse_tube := h.coarse_tube
    coarse_unif := h.coarse_unif
    coarse_dens := h.coarse_dens
    coarse_fullness := h.coarse_fullness
    contain := h.contain
    branch_mapsTo := h.branch_mapsTo
    branch_card := h.branch_card
    product := h.product
    fibreUnif := h.fibreUnif }

theorem exists_isFactorOneScale_iff_exists_isUniformFactorCore [Nontrivial E]
    {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {ε' : ℝ} (hε' : 0 < ε') {σ ρ : NNReal}
    {ι κ lc : Type*} [DecidableEq κ] [DecidableEq lc]
    {s : Finset ι} {t : Finset κ} {tq : Finset lc} {q : κ → lc}
    {V : ι → ShadedTube σ E} {Vρ : κ → Tube ρ E} {p : ι → κ}
    (hED : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier))
    (hEDρ : (t : Set κ).Pairwise
      (fun k k' => IsEssentiallyDistinct (Vρ k).carrier (Vρ k').carrier)) :
    (∃ (s' : Finset ι) (t'' : Finset κ) (Z' : ι → ShadedTube σ E)
        (Zρ : κ → ShadedTube ρ E) (lamσ lamρ N : NNReal),
        0 < N ∧ IsFactorOneScale δ ε' s V t Vρ p tq q s' t'' tq
          Z' Zρ lamσ lamρ N) ↔
      ∃ (s' : Finset ι) (t'' : Finset κ) (Z' : ι → ShadedTube σ E)
        (Zρ : κ → ShadedTube ρ E) (lamσ lamρ N : NNReal),
        0 < N ∧ IsUniformFactorCore δ ε' s V t Vρ p s' t'' Z' Zρ lamσ lamρ N := by
  constructor
  · rintro ⟨s', t'', Z', Zρ, lamσ, lamρ, N, hN, h⟩
    exact ⟨s', t'', Z', Zρ, lamσ, lamρ, N, hN,
      isUniformFactorCore_of_isFactorOneScale h⟩
  · rintro ⟨s', t'', Z', Zρ, lamσ, lamρ, N, hN, h⟩
    exact ⟨s', t'', Z', Zρ, lamσ, lamρ, N, hN,
      isFactorOneScale_of_core hδ0 hδ1 hε' hN hED hEDρ h⟩

/-- Filtering the fine family by a retained parent set does not change a retained parent's
fibre. -/
theorem fibre_filter_parent_mem_eq {ι : Type u} {κ : Type v} [DecidableEq κ]
    (s : Finset ι) (p : ι → κ) (t'' : Finset κ) {k : κ} (hk : k ∈ t'') :
    fibre (s.filter fun i => p i ∈ t'') p k = fibre s p k := by
  ext i
  simp only [fibre, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hi, _⟩, hp⟩
    exact ⟨hi, hp⟩
  · rintro ⟨hi, hp⟩
    exact ⟨⟨hi, hp ▸ hk⟩, hp⟩

/-- Every member of a family filtered by its parent has a retained parent. -/
theorem parent_mem_of_mem_filter_parent {ι : Type u} {κ : Type v} [DecidableEq κ]
    (s : Finset ι) (p : ι → κ) (t'' : Finset κ) :
    ∀ i ∈ s.filter (fun i => p i ∈ t''), p i ∈ t'' := by
  intro i hi
  exact (Finset.mem_filter.mp hi).2

/-- The full `branch_card` bracket for a parent-filtered family follows from the two dyadic
bounds on the original fibres.  The relative-retention clause is automatic because every
retained fibre is unchanged. -/
theorem branch_card_filter_parent {ι : Type u} {κ : Type v} [DecidableEq κ]
    {δ : NNReal} (hδ1 : δ ≤ 1) {ε' : ℝ} (hε' : 0 ≤ ε')
    (s : Finset ι) (p : ι → κ) (t'' : Finset κ) (N : NNReal)
    (hbr : ∀ k ∈ t'',
      (N : ENNReal) ≤ ((fibre s p k).card : ENNReal) ∧
      ((fibre s p k).card : ENNReal) ≤ 2 * (N : ENNReal)) :
    ∀ k ∈ t'',
      (N : ENNReal) ≤ ((fibre (s.filter fun i => p i ∈ t'') p k).card : ENNReal) ∧
      ((fibre (s.filter fun i => p i ∈ t'') p k).card : ENNReal) ≤ 2 * (N : ENNReal) ∧
      (δ : ENNReal) ^ (2 * ε') * ((fibre s p k).card : ENNReal) ≤
        ((fibre (s.filter fun i => p i ∈ t'') p k).card : ENNReal) := by
  intro k hk
  rw [fibre_filter_parent_mem_eq s p t'' hk]
  refine ⟨(hbr k hk).1, (hbr k hk).2, ?_⟩
  have hpow : (δ : ENNReal) ^ (2 * ε') ≤ 1 :=
    ENNReal.rpow_le_one (by exact_mod_cast hδ1) (by positivity)
  exact mul_le_of_le_one_left zero_le hpow

/-- **Transferring a mass share through a cardinality share and two density windows.**

Suppose `s' ⊆ s₂ ⊆ s`, the old shading `X` is bounded above by `2 λ₀ v` on `s₂`, the new shading `Y`
is bounded below by `λ v` on `s'`, and `X` retains a factor `Lb⁻¹` of its total mass on `s₂`.  Then
a single numerical inequality — comparing `c Lb` times the largest possible mass on `s₂` with the
smallest possible mass on `s'` — upgrades the *cardinality* retention hidden in `#s'` to a *mass*
retention `c` from all of `s` to `s'`.

This is the arithmetic of `Kakeya.ml1Boot.IsUniformFactorCore.fine_refinement`, isolated because
the shaded-uniformization interface returns its retention as a cardinality comparison
while `ShadedBody.IsCRefinement` demands a mass comparison, and the bridge is exactly the pair of
density windows: all tubes at one scale have the same carrier volume `v`, so a two-sided density
bracket converts sums into cardinalities in both directions. -/
theorem mass_retention_of_card_share {ι : Type*} {s s₂ s' : Finset ι} {X Y : ι → ENNReal}
    {v : ENNReal} {lam₀ lam : NNReal} {c Lb : ENNReal}
    (hupper : ∀ i ∈ s₂, X i ≤ 2 * (lam₀ : ENNReal) * v)
    (hlower : ∀ i ∈ s', (lam : ENNReal) * v ≤ Y i)
    (hmass : ∑ i ∈ s, X i ≤ Lb * ∑ i ∈ s₂, X i)
    (hkey : c * Lb * (2 * (lam₀ : ENNReal) * v * (s₂.card : ENNReal))
      ≤ (lam : ENNReal) * v * (s'.card : ENNReal)) :
    c * ∑ i ∈ s, X i ≤ ∑ i ∈ s', Y i := by
  have hupper_sum : ∑ i ∈ s₂, X i ≤ (s₂.card : ENNReal) * (2 * (lam₀ : ENNReal) * v) := by
    calc
      ∑ i ∈ s₂, X i ≤ ∑ i ∈ s₂, 2 * (lam₀ : ENNReal) * v := Finset.sum_le_sum hupper
      _ = (s₂.card : ENNReal) * (2 * (lam₀ : ENNReal) * v) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hlower_sum : (s'.card : ENNReal) * ((lam : ENNReal) * v) ≤ ∑ i ∈ s', Y i := by
    calc
      (s'.card : ENNReal) * ((lam : ENNReal) * v) = ∑ i ∈ s', (lam : ENNReal) * v := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s', Y i := Finset.sum_le_sum hlower
  calc
    c * ∑ i ∈ s, X i ≤ c * (Lb * ∑ i ∈ s₂, X i) := by
      exact mul_le_mul_right hmass c
    _ ≤ c * (Lb * ((s₂.card : ENNReal) * (2 * (lam₀ : ENNReal) * v))) := by
      gcongr
    _ = c * Lb * (2 * (lam₀ : ENNReal) * v * (s₂.card : ENNReal)) := by
      ring
    _ ≤ (lam : ENNReal) * v * (s'.card : ENNReal) := by
      exact hkey
    _ = (s'.card : ENNReal) * ((lam : ENNReal) * v) := by
      ring
    _ ≤ ∑ i ∈ s', Y i := hlower_sum

/-- **The `[0, ∞]`-reading of the `ℝ≥0`-valued subpolynomial factor.**

The `c`-refinement constants of this file are the `NNReal` numbers `⟨δ ^ a, _⟩` built from a real
power, while every inequality they occur in is read in `[0, ∞]`, where the same quantity is the
`ENNReal` power `(δ : ENNReal) ^ a`.  This identifies the two, so that the two spellings can be
rewritten into one another. -/
theorem coe_nnreal_rpow_eq {δ : NNReal} (hδ0 : 0 < δ) {a : ℝ} {c : NNReal}
    (hc : (c : ℝ) = (δ : ℝ) ^ a) :
    (c : ENNReal) = (δ : ENNReal) ^ a := by
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  rw [Kakeya.ennreal_coe_nnreal_rpow hδR a, ← hc, ENNReal.ofReal_coe_nnreal]

/-- **A `c`-refinement of shaded tubes from an equality of tubes and a mass bound.**

`ShadedBody.IsCRefinement` asks for equality of the underlying *convex bodies*, which for shaded
tubes follows from equality of the underlying `Kakeya.Tube`s, plus the inclusion of shades and the
mass comparison.  Packaging the three makes the shaded-tube call sites read off a bundle instead of
unfolding the definition. -/
theorem isCRefinement_of_tube_eq {σ : NNReal} {ι : Type*} {s' s : Finset ι}
    {V Z' : ι → ShadedTube σ E} {c : NNReal} (hsub : s' ⊆ s)
    (htube : ∀ i ∈ s', (Z' i).toTube = (V i).toTube)
    (hshade : ∀ i ∈ s', (Z' i).shade ⊆ (V i).shade)
    (hmass : (c : ENNReal) * ∑ i ∈ s, volume (V i).shade
      ≤ ∑ i ∈ s', volume (Z' i).shade) :
    ShadedBody.IsCRefinement s' (fun i => (Z' i).toShadedBody) s
      (fun i => (V i).toShadedBody) c := by
  refine ⟨⟨hsub, fun i hi => ⟨?_, hshade i hi⟩⟩, hmass⟩
  change (Z' i).toTube.toConvexSpaceBody = (V i).toTube.toConvexSpaceBody
  exact congrArg (fun T : Tube σ E => T.toConvexSpaceBody) (htube i hi)

/-- **A cardinality retention stated as a real inequality, read in `[0, ∞]`.**

The shaded-uniformization interface records its retention as `#s ≤ δ ^ (-α) #s'` in
`ℝ`, whereas everything the factoring bundles compare lives in `[0, ∞]`.  This is the transport,
which is just multiplying by `δ ^ α > 0` and coercing. -/
theorem coe_rpow_mul_card_le_card {δ : NNReal} (hδ0 : 0 < δ) {a : ℝ} {m m' : ℕ}
    (h : (m : ℝ) ≤ (δ : ℝ) ^ (-a) * (m' : ℝ)) :
    (δ : ENNReal) ^ a * (m : ENNReal) ≤ (m' : ENNReal) := by
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hRpow_ne : (δ : ℝ) ^ a ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hδR a)
  have hreal : (δ : ℝ) ^ a * (m : ℝ) ≤ (m' : ℝ) := by
    calc
      (δ : ℝ) ^ a * (m : ℝ) ≤ (δ : ℝ) ^ a * ((δ : ℝ) ^ (-a) * (m' : ℝ)) :=
        mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hδR.le a)
      _ = (m' : ℝ) := by
        rw [Real.rpow_neg hδR.le, ← mul_assoc, mul_inv_cancel₀ hRpow_ne, one_mul]
  rw [ennreal_coe_nnreal_rpow hδR a, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδR.le a)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **The four losses of one fine uniformization multiply to `δ ^ (2 ε')`.**

The arithmetic at the heart of `Kakeya.ml1Boot.IsUniformFactorCore.fine_refinement`: the banding
loss `Lb ≤ δ ^ (-ε'/2)`, the factor `2` of the density window (itself at most `δ ^ (-ε'/2)`), the
cardinality retention `δ ^ (ε'/2) #s₂ ≤ #s'` and the density retention `δ ^ (ε'/2) λ₀ ≤ λ` combine
to exactly `δ ^ (2 ε') · Lb · 2 λ₀ v #s₂ ≤ λ v #s'`, because
`2 ε' - ε'/2 - ε'/2 = ε'/2 + ε'/2`.

Separated from the fine-group assembly because it is pure `[0, ∞]`-valued `rpow`
bookkeeping with no geometry in it: it is the reason `α = α' = ε'/2` is the right choice of loss
exponents in the interface, leaving the whole of the remaining budget `ε'` for the banding and for
the width of the density window.  (That assembly, `exists_fineUniformBand`, has since been deleted
along with the interface it was proved from; see
`Kakeya/DimensionThree/MainLemma1/Inventory.lean`, §B.  This lemma is kept because the exponent
choice it justifies is what any replacement interface will have to be applied at.) -/
theorem key_loss_arith {δ : NNReal} (hδ0 : 0 < δ) {ε' : ℝ}
    {Lb : ENNReal} (hLb : Lb ≤ (δ : ENNReal) ^ (-(ε' / 2)))
    (htwo : (2 : ENNReal) ≤ (δ : ENNReal) ^ (-(ε' / 2)))
    {v : ENNReal} {lam₀ lam : NNReal} {m m' : ℕ}
    (hcard : (δ : ENNReal) ^ (ε' / 2) * (m : ENNReal) ≤ (m' : ENNReal))
    (hlam : (δ : ENNReal) ^ (ε' / 2) * (lam₀ : ENNReal) ≤ (lam : ENNReal)) :
    (δ : ENNReal) ^ (2 * ε') * Lb * (2 * (lam₀ : ENNReal) * v * (m : ENNReal))
      ≤ (lam : ENNReal) * v * (m' : ENNReal) := by
  let d : ENNReal := δ
  have hd0 : d ≠ 0 := by
    dsimp [d]
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt hδ0)
  have hdtop : d ≠ ⊤ := by
    dsimp [d]
    exact ENNReal.coe_ne_top
  calc
    d ^ (2 * ε') * Lb * (2 * (lam₀ : ENNReal) * v * (m : ENNReal))
        = (d ^ (2 * ε') * Lb * 2) * ((lam₀ : ENNReal) * v * (m : ENNReal)) := by
          ring
    _ ≤ (d ^ (2 * ε') * d ^ (-(ε' / 2)) * d ^ (-(ε' / 2)))
          * ((lam₀ : ENNReal) * v * (m : ENNReal)) := by
          gcongr
    _ = d ^ (2 * ε' - ε' / 2 - ε' / 2) * ((lam₀ : ENNReal) * v * (m : ENNReal)) := by
          rw [← ENNReal.rpow_add (2 * ε') (-(ε' / 2)) hd0 hdtop]
          rw [← ENNReal.rpow_add (2 * ε' + -(ε' / 2)) (-(ε' / 2)) hd0 hdtop]
          rw [show (2 * ε' + -(ε' / 2)) + -(ε' / 2) = 2 * ε' - ε' / 2 - ε' / 2 by ring]
    _ = ((d ^ (ε' / 2) * (lam₀ : ENNReal)) * v) * (d ^ (ε' / 2) * (m : ENNReal)) := by
          rw [show 2 * ε' - ε' / 2 - ε' / 2 = ε' / 2 + ε' / 2 by ring]
          rw [ENNReal.rpow_add (ε' / 2) (ε' / 2) hd0 hdtop]
          ring
    _ ≤ (lam : ENNReal) * v * (m' : ENNReal) := by
          gcongr

/-- **The mass clause of the fine refinement, from the banding and the uniformization retentions.**

`Kakeya.ml1Boot.mass_retention_of_card_share` and `Kakeya.ml1Boot.key_loss_arith` combined, with the
common carrier volume `v` substituted: the banding loss `Lb`, the width `2` of the density window,
the cardinality retention and the density retention deliver the mass retention `δ ^ (2 ε')` that
`Kakeya.ml1Boot.IsUniformFactorCore.fine_refinement` asks for. -/
theorem fine_mass_retention {δ : NNReal} (hδ0 : 0 < δ) {ε' : ℝ} {σ : NNReal}
    {ι : Type*} {s s₂ s' : Finset ι} {V Z' : ι → ShadedTube σ E}
    {lam₀ lam : NNReal} {v Lb : ENNReal}
    (hv : ∀ i, volume (V i).carrier = v)
    (hwin : ∀ i ∈ s₂, volume (V i).shade ≤ 2 * (lam₀ : ENNReal) * volume (V i).carrier)
    (hbr : ∀ i ∈ s', (lam : ENNReal) * volume (V i).carrier ≤ volume (Z' i).shade)
    (hmass : ∑ i ∈ s, volume (V i).shade ≤ Lb * ∑ i ∈ s₂, volume (V i).shade)
    (hLb : Lb ≤ (δ : ENNReal) ^ (-(ε' / 2)))
    (htwo : (2 : ENNReal) ≤ (δ : ENNReal) ^ (-(ε' / 2)))
    (hcard : (δ : ENNReal) ^ (ε' / 2) * (s₂.card : ENNReal) ≤ (s'.card : ENNReal))
    (hlamret : (δ : ENNReal) ^ (ε' / 2) * (lam₀ : ENNReal) ≤ (lam : ENNReal)) :
    (δ : ENNReal) ^ (2 * ε') * ∑ i ∈ s, volume (V i).shade
      ≤ ∑ i ∈ s', volume (Z' i).shade := by
  simp only [hv] at hwin hbr
  exact mass_retention_of_card_share (X := fun i => volume (V i).shade)
    (Y := fun i => volume (Z' i).shade) (v := v) (lam₀ := lam₀) (lam := lam)
    (c := (δ : ENNReal) ^ (2 * ε'))
    (Lb := Lb) hwin hbr hmass (key_loss_arith hδ0 hLb htwo hcard hlamret)

/-- **The fullness clause of the fine refinement.**

The banding gives `λ(𝕍, Z) ≤ Lb λ₀` and the uniformization gives `δ ^ (ε'/2) λ₀ ≤ λ`; with
`Lb ≤ δ ^ (-ε'/2)` these compose to `δ ^ (2 ε') λ(𝕍, Z) ≤ λ`, since
`2 ε' - ε'/2 ≥ ε'/2` and `δ ≤ 1`. -/
theorem fine_fullness_bound {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {ε' : ℝ} (hε' : 0 < ε')
    {F : ENNReal} {lam₀ lam : NNReal} {Lb : ENNReal}
    (hfull : F ≤ Lb * (lam₀ : ENNReal))
    (hLb : Lb ≤ (δ : ENNReal) ^ (-(ε' / 2)))
    (hlamret : (δ : ENNReal) ^ (ε' / 2) * (lam₀ : ENNReal) ≤ (lam : ENNReal)) :
    (δ : ENNReal) ^ (2 * ε') * F ≤ (lam : ENNReal) := by
  have hd0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδ0)
  calc
    (δ : ENNReal) ^ (2 * ε') * F
        ≤ (δ : ENNReal) ^ (2 * ε') * (Lb * (lam₀ : ENNReal)) := by
          gcongr
    _ ≤ (δ : ENNReal) ^ (2 * ε') * ((δ : ENNReal) ^ (-(ε' / 2)) * (lam₀ : ENNReal)) := by
          gcongr
    _ = (δ : ENNReal) ^ (2 * ε' - ε' / 2) * (lam₀ : ENNReal) := by
          rw [← mul_assoc]
          rw [← ENNReal.rpow_add (2 * ε') (-(ε' / 2)) hd0 ENNReal.coe_ne_top]
          rw [show 2 * ε' + -(ε' / 2) = 2 * ε' - ε' / 2 by ring]
    _ ≤ (δ : ENNReal) ^ (ε' / 2) * (lam₀ : ENNReal) := by
          have hmono : (δ : ENNReal) ^ (2 * ε' - ε' / 2) ≤ (δ : ENNReal) ^ (ε' / 2) :=
            ENNReal.rpow_le_rpow_of_exponent_ge (ENNReal.coe_le_one_iff.mpr hδ1) (by linarith)
          gcongr
    _ ≤ (lam : ENNReal) := by
          exact hlamret









/-! ### One factoring step over a `2`-dilate parent family -/

/-- **The admissible constants for `lem:ml1bootFactorOneScaleUniformDilate`** are nonempty
(blueprint `def:ml1bootFactorOneScaleUniformDilateConstant`).

`1` is admissible, so an opaque witness may be taken at the subtype `{C : NNReal // 1 ≤ C}`
without assuming anything: the clause rides in the type, and the value of the witness stays
inaccessible.

The subtype used to carry a second clause, `factorOneScale.C ≤ C`.  That clause is gone, and
its disappearance is forced rather than cosmetic: `Kakeya.ml1Boot.factorOneScale.C` is a
function of the inner cardinality and the inner tube scale and is unbounded in the first, so no
absolute `C` dominates it.  See the docstring of `Kakeya.ml1Boot.factorOneScaleUniformDilate.C`
for what replaces it. -/
instance factorOneScaleUniformDilate.instNonemptyAdmissible :
    Nonempty {C : NNReal // 1 ≤ C} := by
  exact ⟨⟨1, le_rfl⟩⟩

/-- **The opaque witness behind `C_{lem:ml1bootFactorOneScaleUniformDilate}`** (blueprint
`def:ml1bootFactorOneScaleUniformDilateConstant`).

The clause the blueprint definition asks of the constant is carried here, in the type, so that
it is a theorem about the constant rather than an assumption about an opaque object that
exposes nothing.  No *value* is committed to: the witness is `opaque`, and
`Kakeya.ml1Boot.factorOneScaleUniformDilate.instNonemptyAdmissible` only says the subtype is
inhabited, not which element is chosen. -/
noncomputable opaque factorOneScaleUniformDilate.CWitness :
    {C : NNReal // 1 ≤ C}

/-- **The constant `C_{lem:ml1bootFactorOneScaleUniformDilate}`** (blueprint
`def:ml1bootFactorOneScaleUniformDilateConstant`): the loss constant of one factoring step run
over a **`2`-dilate** parent family at fullness `λ(𝕍, Z) ≥ δ ^ ε'`.

It is deliberately **not** `Kakeya.ml1Boot.factorOneScale.C`.  The dilate form is a restatement
of GWZ Lemma 5.11 under a weakened containment, and what the restatement costs is not known at
this constant.  The blueprint accordingly proposes *no* value, provisional or otherwise, so the
constant remains opaque.

The single clause the blueprint definition asks of it, `1 ≤ C`, is carried by the **type** of
the opaque witness `Kakeya.ml1Boot.factorOneScaleUniformDilate.CWitness` rather than asserted
about a constant that exposes no value.  Nothing is assumed thereby: the subtype is inhabited
by `1`, so the witness exists outright, and
`Kakeya.ml1Boot.factorOneScaleUniformDilate.one_le_C` is a *theorem* — the projection of the
witness — rather than an assumption.  The **value** stays unknown: the witness is `opaque`, so
no consumer can unfold `C` past
`Kakeya.ml1Boot.factorOneScaleUniformDilate.CWitness.val`, and no lemma stated at this
constant, in particular `Kakeya.ml1Boot.exists_factorOneScaleUniform_dilate`, is thereby
strengthened.

## The comparison clause `factorOneScale.C ≤ C` has been removed, and had to be

The witness used to carry a second clause, `factorOneScale.C ≤ C`, and
`Kakeya.ml1Boot.IsUniformFactorCoreDilate` used to be stated at
`Kakeya.ml1Boot.factorOneScale.C`, the passage to this constant happening in
`Kakeya.ml1Boot.IsUniformFactorCoreDilate.toFactorOneScaleDilate` by that comparison. That
was tenable only while `Kakeya.ml1Boot.factorOneScale.C` was the numeral `1`. It is now a
function of the inner cardinality `#s` and the inner tube scale, unbounded in the first, so no
*absolute* constant dominates it and the clause is unstatable at this arity. The two options
were to give this constant the same two binders, or to state the dilate core here. The first
is not available: this constant is `opaque`, so nothing but `1 ≤ C` is provable of it, and the
dilate assembly `Kakeya.ml1Boot.normalized_le_of_coarse_dilate` needs
`C · δ̃ ^ ap' ≤ 1` eventually in `δ̃` **before** the family and hence `#s` exist — a
subpolynomial bound in `#s` that an opaque constant cannot supply. So
`Kakeya.ml1Boot.IsUniformFactorCoreDilate` is now stated at this constant directly.

It depends only on the ambient dimension `3`; in particular not on `δ`, on `σ`, on `ρ`, on
`ε'`, or on the family. -/
noncomputable def factorOneScaleUniformDilate.C : NNReal :=
  factorOneScaleUniformDilate.CWitness.val

/-- **`C ≥ 1`** for the dilate factoring constant (blueprint
`def:ml1bootFactorOneScaleUniformDilateConstant`).  A theorem, not an assumption: it is the
defining property carried by the type of
`Kakeya.ml1Boot.factorOneScaleUniformDilate.CWitness`. -/
theorem factorOneScaleUniformDilate.one_le_C : 1 ≤ factorOneScaleUniformDilate.C := by
  exact factorOneScaleUniformDilate.CWitness.property

/-- **The conclusions of `Kakeya.ml1Boot.exists_factorOneScaleUniform_dilate`, one field per
item** (blueprint `lem:ml1bootFactorOneScaleUniformDilate`, items (a)–(e)).

These are items (a), (b), (d), (e) and (f) of `Kakeya.ml1Boot.IsFactorOneScale`, at the opaque
absolute constant `Kakeya.ml1Boot.factorOneScaleUniformDilate.C` in place of that structure's
scale- and cardinality-dependent `Kakeya.ml1Boot.factorOneScale.C #s σ`; see the former's
docstring for why the dilate chain is stated at an absolute constant.  Three groups of fields
of that structure are **dropped**,
and none of them is dropped because it fails:

* `Kakeya.ml1Boot.IsFactorOneScale.contain`, the pointwise nesting `Z' i ⊆ Z_ρ (p i)` of the
  shadings, is *false* in the dilate setting — a fine tube in `2 · V_{ρ,k}` may be disjoint
  from `V_{ρ,k}` — and asserting it would be asserting something false;
* `Kakeya.ml1Boot.IsFactorOneScale.fibreUnif`, fibre uniformity, and the auxiliary
  classification `(tq, q, t'q)` with its two cardinality clauses, are simply unused by the
  dilate consumer, which cites (a)–(e) and nothing else.

The coarse output `𝕍_ρ|_{t''}` is a family of **honest** `ρ`-tubes and `Z_ρ` shades those
tubes, not their dilates; that is what keeps
`Kakeya.ml1Boot.normalized_le_of_coarse`'s coarse hypothesis applicable to what this returns,
and it is also where the difficulty of the assumption sits. -/
structure IsFactorOneScaleDilate {ι κ : Type*} [DecidableEq κ]
    {σ ρ : NNReal} (δ : NNReal) (ε' : ℝ) (s : Finset ι) (V : ι → ShadedTube σ E)
    (t : Finset κ) (Vρ : κ → Tube ρ E) (p : ι → κ)
    (s' : Finset ι) (t'' : Finset κ)
    (Z' : ι → ShadedTube σ E) (Zρ : κ → ShadedTube ρ E)
    (lamσ lamρ N : NNReal) : Prop where
  /-- (a) The fine index set is a subset of `s`. -/
  fine_subset : s' ⊆ s
  /-- (a) `Z'` shades the same tubes as `𝕍` and is contained in `Z`. -/
  fine_shade : ∀ i ∈ s', (Z' i).toTube = (V i).toTube ∧ (Z' i).shade ⊆ (V i).shade
  /-- (a) `(𝕍|_{s'}, Z')` is a `δ ^ (2 ε')`-refinement of `(𝕍, Z)`. -/
  fine_refinement : ShadedBody.IsCRefinement s' (fun i => (Z' i).toShadedBody) s
    (fun i => (V i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩
  /-- (a) The fine family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  fine_unif : Nonempty (ShadedTube.ShadedUniformTubeSet s' Z' (Tube.ssfGridLen σ)
    (uniformize.C 3))
  /-- (a) Essential distinctness is inherited by the fine family. -/
  fine_essDistinct : (s' : Set ι).Pairwise
    (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier)
  /-- (a) The fine shading densities are two-sidedly comparable to `λ_σ`. -/
  fine_dens : ∀ i ∈ s', (lamσ : ENNReal) * volume (V i).carrier ≤ volume (Z' i).shade ∧
    volume (Z' i).shade ≤ 2 * (lamσ : ENNReal) * volume (V i).carrier
  /-- (a) `λ_σ ≥ δ ^ (2 ε') λ(𝕍, Z)`. -/
  fine_fullness : (δ : ENNReal) ^ (2 * ε')
      * ShadedBody.fullness s (fun i => (V i).toShadedBody) ≤ (lamσ : ENNReal)
  /-- (b) The coarse index set is a subset of `t`. -/
  coarse_subset : t'' ⊆ t
  /-- (b) `Z_ρ` shades the parent tubes themselves, not their dilates. -/
  coarse_tube : ∀ k ∈ t'', (Zρ k).toTube = Vρ k
  /-- (b) The coarse family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  coarse_unif : Nonempty (ShadedTube.ShadedUniformTubeSet t'' Zρ (Tube.ssfGridLen ρ)
    (uniformize.C 3))
  /-- (b) Essential distinctness is inherited by the coarse family. -/
  coarse_essDistinct : (t'' : Set κ).Pairwise
    (fun k k' => IsEssentiallyDistinct (Vρ k).carrier (Vρ k').carrier)
  /-- (b) The coarse shading densities are two-sidedly comparable to `λ_ρ`. -/
  coarse_dens : ∀ k ∈ t'', (lamρ : ENNReal) * volume (Vρ k).carrier ≤ volume (Zρ k).shade ∧
    volume (Zρ k).shade ≤ 2 * (lamρ : ENNReal) * volume (Vρ k).carrier
  /-- (b) `λ_ρ ≥ C⁻¹ δ ^ (2 ε') λ(𝕍, Z)`, at the **dilate** constant. -/
  coarse_fullness : (factorOneScaleUniformDilate.C : ENNReal)⁻¹ * (δ : ENNReal) ^ (2 * ε')
      * ShadedBody.fullness s (fun i => (V i).toShadedBody) ≤ (lamρ : ENNReal)
  /-- (c) Every retained member has its parent retained. -/
  branch_mapsTo : ∀ i ∈ s', p i ∈ t''
  /-- (c) The retained fibres have cardinality comparable to `N` and each retains a
  `δ ^ (2 ε')` fraction. -/
  branch_card : ∀ k ∈ t'',
    (N : ENNReal) ≤ ((fibre s' p k).card : ENNReal) ∧
    ((fibre s' p k).card : ENNReal) ≤ 2 * (N : ENNReal) ∧
    (δ : ENNReal) ^ (2 * ε') * ((fibre s p k).card : ENNReal)
      ≤ ((fibre s' p k).card : ENNReal)
  /-- (d) Every fibre Frostman constant grows by at most `δ ^ (-2 ε')`. -/
  frostman : ∀ k ∈ t'', ∀ K : ConvexSpaceBody E,
    (∀ i ∈ s, p i = k → (V i).toConvexSpaceBody ≤ K) →
    frostmanConstIn (fibre s' p k) (fun i => (V i).toConvexSpaceBody) K
      ≤ (δ : ENNReal) ^ (-2 * ε')
        * frostmanConstIn (fibre s p k) (fun i => (V i).toConvexSpaceBody) K
  /-- (e) The multiplicity factors with loss `C δ ^ (-2 ε')`, at the **dilate** constant. -/
  product : ∀ k ∈ t'', ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
    ≤ (factorOneScaleUniformDilate.C : ENNReal) * (δ : ENNReal) ^ (-2 * ε')
      * ShadedBody.multiplicity t'' (fun k' => (Zρ k').toShadedBody)
      * ShadedBody.multiplicity (fibre s' p k) (fun i => (Z' i).toShadedBody)

/-- **The core bundle of one factoring step over a `c`-dilate parent family.**

`Kakeya.ml1Boot.IsUniformFactorCore` with the single field `contain` deleted, the field
`fibreUnif` weakened to its one-sided reading, and the two
constants moved from `Kakeya.ml1Boot.factorOneScale.C` to the opaque
`Kakeya.ml1Boot.factorOneScaleUniformDilate.C`; see the latter's docstring for why the move is
forced and why it weakens rather than strengthens what this bundle asserts.

*Why `fibreUnif` is one-sided here.*  Not by design, but because this bundle's only consumer
permits it.  `Kakeya.ml1Boot.IsUniformFactorCoreDilate` feeds
only `Kakeya.ml1Boot.IsUniformFactorCoreDilate.toFactorOneScaleDilate`, whose target
`Kakeya.ml1Boot.IsFactorOneScaleDilate` has no fibre-uniformity field at all, so the field has no
consumer anywhere in the repository and nothing reads either of the two lower brackets from it.
The undilated `Kakeya.ml1Boot.IsUniformFactorCore.fibreUnif` does have consumers, and its chain was
typed two-sidedly as far out as `Kakeya.ml1Boot.multiplicity_le_middle`; it is now one-sided too,
so the two bundles agree again.  The section "Obstruction 2 is gone: the `fibreUnif` restatement,
carried out" in the docstring of `Kakeya.ml1Boot.exists_uniformFactorCore` records what moving it
took.  Weakening the field here cost nothing and removed the simultaneity obstruction from this
bundle's producer.

`contain` is the one field of the core that reads the parent *containment*: it asserts
`(Z' i).shade ⊆ (Zρ (p i)).shade`, and under a `c`-dilate parent family the fine tube lies in
`c · V_{ρ, p i}` rather than in `V_{ρ, p i}`, so its shading has no reason to sit inside the
parent's.  Every other field of the core is a statement about the fine family, the coarse
family, the refinement, the densities, the fullnesses, the branching or the product, none of
which mentions the containment.  That is why this is a deletion rather than a rewrite. -/
structure IsUniformFactorCoreDilate {ι κ : Type*} [DecidableEq κ]
    {σ ρ : NNReal} (δ : NNReal) (ε' : ℝ) (s : Finset ι) (V : ι → ShadedTube σ E)
    (t : Finset κ) (Vρ : κ → Tube ρ E) (p : ι → κ)
    (s' : Finset ι) (t'' : Finset κ)
    (Z' : ι → ShadedTube σ E) (Zρ : κ → ShadedTube ρ E)
    (lamσ lamρ N : NNReal) : Prop where
  /-- The fine index set is a subset of `s`. -/
  fine_subset : s' ⊆ s
  /-- `Z'` shades the same tubes as `𝕍` and is contained in `Z`. -/
  fine_shade : ∀ i ∈ s', (Z' i).toTube = (V i).toTube ∧ (Z' i).shade ⊆ (V i).shade
  /-- `(𝕍|_{s'}, Z')` is a `δ ^ (2 ε')`-refinement of `(𝕍, Z)`. -/
  fine_refinement : ShadedBody.IsCRefinement s' (fun i => (Z' i).toShadedBody) s
    (fun i => (V i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩
  /-- The fine family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  fine_unif : Nonempty (ShadedTube.ShadedUniformTubeSet s' Z' (Tube.ssfGridLen σ)
    (uniformize.C 3))
  /-- The fine shading densities are two-sidedly comparable to `λ_σ`. -/
  fine_dens : ∀ i ∈ s', (lamσ : ENNReal) * volume (V i).carrier ≤ volume (Z' i).shade ∧
    volume (Z' i).shade ≤ 2 * (lamσ : ENNReal) * volume (V i).carrier
  /-- `λ_σ ≥ δ ^ (2 ε') λ(𝕍, Z)`. -/
  fine_fullness : (δ : ENNReal) ^ (2 * ε')
      * ShadedBody.fullness s (fun i => (V i).toShadedBody) ≤ (lamσ : ENNReal)
  /-- The coarse index set is a subset of `t`. -/
  coarse_subset : t'' ⊆ t
  /-- `Z_ρ` shades the parent tubes. -/
  coarse_tube : ∀ k ∈ t'', (Zρ k).toTube = Vρ k
  /-- The coarse family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  coarse_unif : Nonempty (ShadedTube.ShadedUniformTubeSet t'' Zρ (Tube.ssfGridLen ρ)
    (uniformize.C 3))
  /-- The coarse shading densities are two-sidedly comparable to `λ_ρ`. -/
  coarse_dens : ∀ k ∈ t'', (lamρ : ENNReal) * volume (Vρ k).carrier ≤ volume (Zρ k).shade ∧
    volume (Zρ k).shade ≤ 2 * (lamρ : ENNReal) * volume (Vρ k).carrier
  /-- `λ_ρ ≥ C⁻¹ δ ^ (2 ε') λ(𝕍, Z)`, at the **dilate** constant. -/
  coarse_fullness : (factorOneScaleUniformDilate.C : ENNReal)⁻¹ * (δ : ENNReal) ^ (2 * ε')
      * ShadedBody.fullness s (fun i => (V i).toShadedBody) ≤ (lamρ : ENNReal)
  /-- Every retained member has its parent retained. -/
  branch_mapsTo : ∀ i ∈ s', p i ∈ t''
  /-- The retained fibres have cardinality comparable to `N` and each retains a
  `δ ^ (2 ε')` fraction. -/
  branch_card : ∀ k ∈ t'',
    (N : ENNReal) ≤ ((fibre s' p k).card : ENNReal) ∧
    ((fibre s' p k).card : ENNReal) ≤ 2 * (N : ENNReal) ∧
    (δ : ENNReal) ^ (2 * ε') * ((fibre s p k).card : ENNReal)
      ≤ ((fibre s' p k).card : ENNReal)
  /-- The multiplicity factors with loss `C δ ^ (-2 ε')`, at the **dilate** constant. -/
  product : ∀ k ∈ t'', ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
    ≤ (factorOneScaleUniformDilate.C : ENNReal) * (δ : ENNReal) ^ (-2 * ε')
      * ShadedBody.multiplicity t'' (fun k' => (Zρ k').toShadedBody)
      * ShadedBody.multiplicity (fibre s' p k) (fun i => (Z' i).toShadedBody)
  /-- Every retained fibre of the parent map is itself uniform, in the **one-sided** reading:
  `Kakeya.IsFlatPrismUniform`, GWZ Definition 2.2 minus `le_card_shadeClass` and `branchingN_le`.
  This field has no consumer (see the structure docstring), and read one-sidedly it is a
  consequence of `fine_unif` at the same constant, by
  `Kakeya.ml1Boot.nonempty_isFlatPrismUniform_fibre_of_shadedUniformTubeSet`. -/
  fibreUnif : ∀ k ∈ t'', Nonempty (IsFlatPrismUniform (fibre s' p k) Z'
    (Tube.ssfGridLen σ) (uniformize.C 3))



/-- **The dilate core bundle gives the full dilate bundle.**

Every field of `Kakeya.ml1Boot.IsFactorOneScaleDilate` that is absent from
`Kakeya.ml1Boot.IsUniformFactorCoreDilate` is a consequence of the core together with the
ambient hypotheses, exactly as in the undilated case:

* `fine_essDistinct` and `coarse_essDistinct` restrict the given pairwise conditions along
  `fine_subset` and `coarse_subset`; essential distinctness is a condition on pairs.
* `frostman` is `Kakeya.ConvexSpaceBody.frostmanConstIn_subfamily_le` (Frostman.lean:753) at
  `κ = δ ^ (2 ε')`, whose ambient body is arbitrary, whose cardinality hypothesis is the third
  clause of `branch_card` and whose common-volume hypothesis holds because all `σ`-tubes have
  the same carrier volume; the fibre over a retained `k` is nonempty because `0 < N` bounds
  `|fibre s' p k|` below.

The two constants are already at `Kakeya.ml1Boot.factorOneScaleUniformDilate.C` on both sides,
so `coarse_fullness` and `product` transfer verbatim; the passage from
`Kakeya.ml1Boot.factorOneScale.C` that used to happen here is gone with the comparison clause
it rested on (see the docstring of `Kakeya.ml1Boot.factorOneScaleUniformDilate.C`).  The field
`fibreUnif` of the core is simply dropped, the dilate bundle not asking for it. -/
theorem IsUniformFactorCoreDilate.toFactorOneScaleDilate {ι κ : Type*} [DecidableEq κ]
    {σ ρ δ : NNReal} {ε' : ℝ} (hε' : 0 < ε') (hδ0 : 0 < δ)
    {s : Finset ι} {t : Finset κ} {V : ι → ShadedTube σ E} {Vρ : κ → Tube ρ E} {p : ι → κ}
    {s' : Finset ι} {t'' : Finset κ} {Z' : ι → ShadedTube σ E} {Zρ : κ → ShadedTube ρ E}
    {lamσ lamρ N : NNReal} (hN : 0 < N)
    (hED : (s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier))
    (hEDρ : (t : Set κ).Pairwise
      (fun k k' => IsEssentiallyDistinct (Vρ k).carrier (Vρ k').carrier))
    (hcore : IsUniformFactorCoreDilate δ ε' s V t Vρ p s' t'' Z' Zρ lamσ lamρ N) :
    IsFactorOneScaleDilate δ ε' s V t Vρ p s' t'' Z' Zρ lamσ lamρ N := by
  classical
  refine {
    fine_subset := hcore.fine_subset
    fine_shade := hcore.fine_shade
    fine_refinement := hcore.fine_refinement
    fine_unif := hcore.fine_unif
    fine_essDistinct := ?_
    fine_dens := hcore.fine_dens
    fine_fullness := hcore.fine_fullness
    coarse_subset := hcore.coarse_subset
    coarse_tube := hcore.coarse_tube
    coarse_unif := hcore.coarse_unif
    coarse_essDistinct := ?_
    coarse_dens := hcore.coarse_dens
    coarse_fullness := hcore.coarse_fullness
    branch_mapsTo := hcore.branch_mapsTo
    branch_card := hcore.branch_card
    frostman := ?_
    product := hcore.product }
  · exact hED.mono (Finset.coe_subset.mpr hcore.fine_subset)
  · exact hEDρ.mono (Finset.coe_subset.mpr hcore.coarse_subset)
  · intro k hk K hK
    have hbc := hcore.branch_card k hk
    have hfibre_sub : fibre s' p k ⊆ fibre s p k := by
      unfold fibre
      exact Finset.filter_subset_filter (fun i => p i = k) hcore.fine_subset
    have hlt : (0 : ENNReal) < ((fibre s' p k).card : ENNReal) :=
      lt_of_lt_of_le (by exact_mod_cast hN) hbc.1
    have hpos_card : 0 < (fibre s' p k).card := by
      exact_mod_cast hlt
    have hne_s : (fibre s p k).Nonempty := by
      have hne_s' : (fibre s' p k).Nonempty := Finset.card_pos.mp hpos_card
      rcases hne_s' with ⟨i, hi⟩
      exact ⟨i, hfibre_sub hi⟩
    obtain ⟨i₀, hi₀⟩ := id hne_s
    let v : ENNReal := volume ((V i₀).toConvexSpaceBody).carrier
    have hvol : ∀ i ∈ fibre s p k, volume ((V i).toConvexSpaceBody).carrier = v := by
      intro i hi
      have h := _root_.Tube.volume_carrier_eq_volume_carrier (V i).toTube (V i₀).toTube
      simpa [v] using h
    have hκ : (δ : ENNReal) ^ (2 * ε') ≠ 0 := by
      have hεnonneg : 0 ≤ 2 * ε' := mul_nonneg (by norm_num) (le_of_lt hε')
      exact ne_of_gt (ENNReal.rpow_pos_of_nonneg (ENNReal.coe_pos.mpr hδ0) hεnonneg)
    have hKfib : ∀ i ∈ fibre s p k, (V i).toConvexSpaceBody ≤ K := by
      intro i hi
      have himem : i ∈ s.filter (fun j => p j = k) := by
        simpa [fibre] using hi
      rcases Finset.mem_filter.mp himem with ⟨his, hp⟩
      exact hK i his hp
    have hf := ConvexSpaceBody.frostmanConstIn_subfamily_le
      (s := fibre s p k) (s' := fibre s' p k)
      (W := fun i => (V i).toConvexSpaceBody) (K := K) (κ := (δ : ENNReal) ^ (2 * ε'))
      (v := v) hne_s hvol hKfib hfibre_sub hκ hbc.2.2
    rw [← ENNReal.rpow_neg, ← show -2 * ε' = -(2 * ε') by ring] at hf
    exact hf



/-- **The conclusions of the two-scale factoring step, one field per item.**

There is no Lean producer for this structure.  `exists_factorTwoScales` and
`exists_twoScaleFactorPair` are **not declarations**, and the fine pair the intended route went
through is refuted (`Kakeya.ml1Boot.not_exists_twoScaleFinePair`); what exists is this structure,
the assembly `Kakeya.ml1Boot.isFactorTwoScales_of_factorPair` from two one-scale bundles and a
fine pair, and the exit `Kakeya.ml1Boot.multiplicity_le_caseTwo_of_factorTwoScales`.  See
blueprint `lem:ml1bootFactorTwoScales` and `note:ml1bootCaseTwoConstructionLayerEmpty`.

Here `(𝕋, Y)` is a family of shaded `δ`-tubes indexed by `s`, `(t_τ, 𝕋_τ, p_τ)` is a parent
family for `𝕋` at scale `τ`, `(t_θ, 𝕋_θ, p_θ)` is a parent family for `𝕋_τ` at scale `θ`,
and the output data is `s'`, `t''_τ`, `t'_τ`, `t'_θ`, the shadings `Y'`, `Y_τ`, `Y_θ` and
the numbers `λ_δ`, `λ_τ`, `λ_θ`, `N_τ`, `N_θ`.  The fields are items (a)–(h) of the
blueprint lemma `lem:ml1bootFactorTwoScales`; `C` abbreviates
`Kakeya.ml1Boot.factorTwoScales.C #s δ #t''τ τ`, the product of the two applications' one-scale
loss constants, each read at the cardinality and tube scale of *its own* inner family: `(#s, δ)`
for the first application and `(#t''τ, τ)` for the second, whose inner family is the
intermediate middle index set.

## The intermediate middle index set `t''_τ`

The structure carries a *fourth* index set `t''_τ` with `t'_τ ⊆ t''_τ ⊆ t_τ`, namely the
coarse output of the **first** of the two factoring applications, before the second one
refines the middle family again.  It is not decoration: the only item that mentions a
Frostman constant of an *unrefined* middle fibre, `frostman_mid`, is read off the second
application, which is made to `𝕋_τ|_{t''_τ}` and not to `𝕋_τ`, so the base of that
comparison is `fibre t''τ pθ l'`.  Writing `fibre tτ pθ l'` there — as an earlier form of
both this structure and the blueprint display for `item:twoScaleFrostman` did — is a
non-sequitur, and it cannot be repaired by monotonicity: `Kakeya.frostmanConstIn` is a
*ratio* (the least `C` with `densityIn ≤ C * densityIn` against the anchor, over all
sub-bodies), so shrinking the index set shrinks numerator and denominator together and the
constant moves in neither direction.  The one transport this development has from an ambient
family to a subfamily, `ConvexSpaceBody.IsFrostmanIn.of_subset`, does point the right way,
but it charges the mass ratio: it turns `IsFrostmanIn s W K C` into
`IsFrostmanIn t W K (C * C')` only given `∑_{i ∈ s} |W i| ≤ C' ∑_{i ∈ t} |W i|`.  Supplying
that at `t = fibre t''τ pθ l'`, `s = fibre tτ pθ l'` is exactly the composite fibre retention
that `note:ml1bootCoarseFibreRetentionRetired` refutes, so the route is closed and not merely
unbuilt.

Every other field is insensitive to the distinction, and `frostman_mid` has no consumer in
this development: the middle-side collision reads its upper bound at the unrefined node
family instead, from `Kakeya.ml1Boot.IsCaseTwoInput` through blueprint
`lem:ml1bootLocalDensityUnrefined`.  See blueprint
`note:ml1bootTwoScaleFrostmanMidBase` and `note:ml1bootMiddleCollisionUnrefined`(4).

The shadings are given as families of `ShadedTube`, with the clause "`Y_τ` is a shading of
`𝕋_τ|_{t'_τ}`" recorded as the equality `(Yτ k).toTube = Tτ k` of the underlying tubes.
This is what lets the uniformity clauses be stated at all: `ShadedTube.ShadedUniformTubeSet` is
data-valued, so each uniformity clause is its `Nonempty`. -/
structure IsFactorTwoScales {ι κ l : Type*} [DecidableEq κ] [DecidableEq l]
    {δ τ θ : NNReal} (ε' : ℝ) (s : Finset ι) (T : ι → ShadedTube δ E)
    (tτ : Finset κ) (Tτ : κ → Tube τ E) (pτ : ι → κ)
    (tθ : Finset l) (Tθ : l → Tube θ E) (pθ : κ → l)
    (s' : Finset ι) (t''τ t'τ : Finset κ) (t'θ : Finset l)
    (Y' : ι → ShadedTube δ E) (Yτ : κ → ShadedTube τ E) (Yθ : l → ShadedTube θ E)
    (lamδ lamτ lamθ Nτ Nθ : NNReal) : Prop where
  /-- (a) `(𝕋|_{s'}, Y')` refines `(𝕋, Y)` by `δ ^ (2 ε')`, is uniform with constant `2`, has
  pairwise essentially distinct tubes, and has shading densities comparable to `λ_δ`.

  **Why the budget here is `δ ^ (2 ε')` and not `δ ^ ε'`.**  The fine index set produced by
  the chain is `s' = s'₁ ∩ p_τ⁻¹(s'₂)`, where `s'₁` is the fine output of the first
  application of `Kakeya.ml1Boot.exists_factorOneScaleUniform` and `s'₂` is the fine output of
  the second; the intersection is forced because the second application refines the *middle*
  family again (GWZ: "abusing notation, we will continue to refer to these refinements as …")
  and the fine family has to be pulled back along `p_τ`.  Every clause of this item that is
  *fibrewise* survives that intersection for free, by
  `Kakeya.ml1Boot.fibre_filter_mem`.  The three *global* clauses — the refinement bound
  against `s`, uniformity of `s'` as a whole, and the lower bound on `λ_δ` — do not, and are
  would be restored by one further application, at `m = 1`, of the uniform-refinement step to the
  intersection, which costs a second factor `δ ^ ε'`.  Since `ε'` is at the caller's disposal this
  costs nothing.  That step is **false** in the form it was written in — see
  `Kakeya.ml1Boot.not_exists_uniformRefinement`, and the Lean carrier
  `exists_uniformRefinement` has been deleted — so the three global clauses are, as of now,
  owed to a shaded-uniformization interface that does not exist; see the docstring of
  `Kakeya.ml1Boot.exists_uniformFactorCore`. -/
  fine_subset : s' ⊆ s
  /-- (a) `Y'` shades the same tubes as `𝕋` and is contained in `Y`. -/
  fine_shade : ∀ i ∈ s', (Y' i).toTube = (T i).toTube ∧ (Y' i).shade ⊆ (T i).shade
  /-- (a) `(𝕋|_{s'}, Y')` is a `δ ^ (2 ε')`-refinement of `(𝕋, Y)`; see `fine_subset` for why
  the budget is `2 ε'`. -/
  fine_refinement : ShadedBody.IsCRefinement s' (fun i => (Y' i).toShadedBody) s
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩
  /-- (a) The fine family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  fine_unif : Nonempty (ShadedTube.ShadedUniformTubeSet s' Y' (Tube.ssfGridLen δ)
    (uniformize.C 3))
  /-- (a) Essential distinctness is inherited by the fine family. -/
  fine_essDistinct : (s' : Set ι).Pairwise
    (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
  /-- (a) The fine shading densities are two-sidedly comparable to `λ_δ`. -/
  fine_dens : ∀ i ∈ s', (lamδ : ENNReal) * volume (T i).carrier ≤ volume (Y' i).shade ∧
    volume (Y' i).shade ≤ 2 * (lamδ : ENNReal) * volume (T i).carrier
  /-- (a) `λ_δ ≥ δ ^ (2 ε') λ(𝕋, Y)`. -/
  fine_fullness : (δ : ENNReal) ^ (2 * ε')
      * ShadedBody.fullness s (fun i => (T i).toShadedBody) ≤ (lamδ : ENNReal)
  /-- (b) The intermediate middle index set — the coarse output of the *first* factoring
  application — is a subset of `t_τ`. -/
  midAmbient_subset : t''τ ⊆ tτ
  /-- (b) The retained middle index set — the fine output of the *second* application — is a
  subset of the intermediate one.  Composed with `midAmbient_subset` this is
  `Kakeya.ml1Boot.IsFactorTwoScales.mid_subset`, `t'τ ⊆ tτ`. -/
  mid_subset' : t'τ ⊆ t''τ
  /-- (b) `Y_τ` shades the middle tubes. -/
  mid_tube : ∀ k ∈ t'τ, (Yτ k).toTube = Tτ k
  /-- (b) The middle family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  mid_unif : Nonempty (ShadedTube.ShadedUniformTubeSet t'τ Yτ (Tube.ssfGridLen τ)
    (uniformize.C 3))
  /-- (b) The retained middle tubes are pairwise essentially distinct. -/
  mid_essDistinct : (t'τ : Set κ).Pairwise
    (fun k k' => IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier)
  /-- (b) The middle shading densities are two-sidedly comparable to `λ_τ`. -/
  mid_dens : ∀ k ∈ t'τ, (lamτ : ENNReal) * volume (Tτ k).carrier ≤ volume (Yτ k).shade ∧
    volume (Yτ k).shade ≤ 2 * (lamτ : ENNReal) * volume (Tτ k).carrier
  /-- (b) `λ_τ ≥ C⁻¹ δ ^ ε' λ(𝕋, Y)`, at `C = factorTwoScales.C #s δ #t''τ τ`. -/
  mid_fullness : (factorTwoScales.C s.card δ t''τ.card τ : ENNReal)⁻¹ * (δ : ENNReal) ^ ε'
      * ShadedBody.fullness s (fun i => (T i).toShadedBody) ≤ (lamτ : ENNReal)
  /-- (c) The retained coarse index set is a subset of `t_θ`. -/
  coarse_subset : t'θ ⊆ tθ
  /-- (c) `Y_θ` shades the coarse tubes. -/
  coarse_tube : ∀ l' ∈ t'θ, (Yθ l').toTube = Tθ l'
  /-- (c) The coarse family is uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`. -/
  coarse_unif : Nonempty (ShadedTube.ShadedUniformTubeSet t'θ Yθ (Tube.ssfGridLen θ)
    (uniformize.C 3))
  /-- (c) The retained coarse tubes are pairwise essentially distinct. -/
  coarse_essDistinct : (t'θ : Set l).Pairwise
    (fun l₁ l₂ => IsEssentiallyDistinct (Tθ l₁).carrier (Tθ l₂).carrier)
  /-- (c) The coarse shading densities are two-sidedly comparable to `λ_θ`. -/
  coarse_dens : ∀ l' ∈ t'θ, (lamθ : ENNReal) * volume (Tθ l').carrier ≤ volume (Yθ l').shade ∧
    volume (Yθ l').shade ≤ 2 * (lamθ : ENNReal) * volume (Tθ l').carrier
  /-- (c) `λ_θ ≥ C⁻¹ δ ^ ε' λ(𝕋, Y)`, at `C = factorTwoScales.C #s δ #t''τ τ`. -/
  coarse_fullness : (factorTwoScales.C s.card δ t''τ.card τ : ENNReal)⁻¹ * (δ : ENNReal) ^ ε'
      * ShadedBody.fullness s (fun i => (T i).toShadedBody) ≤ (lamθ : ENNReal)
  /-- (d) Every retained fine index has its `τ`-parent retained. -/
  branch_fine_mapsTo : ∀ i ∈ s', pτ i ∈ t'τ
  /-- (d) Every retained middle index has its `θ`-parent retained. -/
  branch_mid_mapsTo : ∀ k ∈ t'τ, pθ k ∈ t'θ
  /-- (d) Every retained fine fibre has cardinality comparable to `N_τ`. -/
  branch_fine_card : ∀ k ∈ t'τ, (Nτ : ENNReal) ≤ ((fibre s' pτ k).card : ENNReal) ∧
    ((fibre s' pτ k).card : ENNReal) ≤ 2 * (Nτ : ENNReal)
  /-- (d) Every retained middle fibre has cardinality comparable to `N_θ`. -/
  branch_mid_card : ∀ l' ∈ t'θ, (Nθ : ENNReal) ≤ ((fibre t'τ pθ l').card : ENNReal) ∧
    ((fibre t'τ pθ l').card : ENNReal) ≤ 2 * (Nθ : ENNReal)
  /-- (e) The fine shadings are nested in the middle ones along `p_τ`. -/
  contain_fine : ∀ i ∈ s', pτ i ∈ t'τ → (Y' i).shade ⊆ (Yτ (pτ i)).shade
  /-- (e) The middle shadings are nested in the coarse ones along `p_θ`. -/
  contain_mid : ∀ k ∈ t'τ, pθ k ∈ t'θ → (Yτ k).shade ⊆ (Yθ (pθ k)).shade
  /-- (f) The Frostman constant of every fine fibre grows by at most `δ ^ (-ε')`. -/
  frostman_fine : ∀ k ∈ t'τ,
    frostmanConstIn (fibre s' pτ k) (fun i => (T i).toConvexSpaceBody)
        (Tτ k).toConvexSpaceBody
      ≤ (δ : ENNReal) ^ (-ε') * frostmanConstIn (fibre s pτ k)
          (fun i => (T i).toConvexSpaceBody) (Tτ k).toConvexSpaceBody
  /-- (f) The Frostman constant of every middle fibre grows by at most `δ ^ (-ε')`, measured
  against the fibre of the **intermediate** index set `t''τ` and not of `tτ`.

  This is the second factoring application's `Kakeya.ml1Boot.IsFactorOneScale.frostman`, and
  that application is made to `𝕋_τ|_{t''τ}`; the base of the comparison is therefore
  `fibre t''τ pθ l'`.  See the section "The intermediate middle index set `t''_τ`" of the
  docstring of this structure for why `fibre tτ pθ l'` is not available here. -/
  frostman_mid : ∀ l' ∈ t'θ,
    frostmanConstIn (fibre t'τ pθ l') (fun k => (Tτ k).toConvexSpaceBody)
        (Tθ l').toConvexSpaceBody
      ≤ (δ : ENNReal) ^ (-ε') * frostmanConstIn (fibre t''τ pθ l')
          (fun k => (Tτ k).toConvexSpaceBody) (Tθ l').toConvexSpaceBody
  /-- (g) **The triple-product bound**: for every retained `k` and `l`, the multiplicity of
  `(𝕋, Y)` is at most `C δ ^ (-ε')` times the product of the fine, middle and coarse
  multiplicities. -/
  product : ∀ k ∈ t'τ, ∀ l' ∈ t'θ,
    ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
      ≤ (factorTwoScales.C s.card δ t''τ.card τ : ENNReal) * (δ : ENNReal) ^ (-ε')
        * ShadedBody.multiplicity (fibre s' pτ k) (fun i => (Y' i).toShadedBody)
        * ShadedBody.multiplicity (fibre t'τ pθ l') (fun k' => (Yτ k').toShadedBody)
        * ShadedBody.multiplicity t'θ (fun l₂ => (Yθ l₂).toShadedBody)
  /-- (h) Every retained fibre of the middle family over the coarse parent map is itself
  uniform, at the constant `Kakeya.ml1Boot.uniformize.C 3`, in the **one-sided** reading
  `Kakeya.IsFlatPrismUniform`.  This is the hypothesis
  `IsFlatPrismUniform u U (Tube.ssfGridLen τ) Cunif` of
  `Kakeya.ml1Boot.multiplicity_le_middle` at `u = fibre t'τ pθ l'`; it does not follow from
  `mid_unif`, since a parent-map fibre is an arbitrary subfamily of a uniform family.  It is
  `Kakeya.ml1Boot.IsFactorOneScale.fibreUnif` at the second application, tube scale `τ` and
  parent scale `θ`. -/
  midFibreUnif : ∀ l' ∈ t'θ,
    Nonempty (IsFlatPrismUniform (fibre t'τ pθ l') Yτ
      (Tube.ssfGridLen τ) (uniformize.C 3))

/-- (b) The retained middle index set is a subset of `t_τ`; the composite of
`Kakeya.ml1Boot.IsFactorTwoScales.mid_subset'` and
`Kakeya.ml1Boot.IsFactorTwoScales.midAmbient_subset`. -/
theorem IsFactorTwoScales.mid_subset {ι κ l : Type*} [DecidableEq κ] [DecidableEq l]
    {δ τ θ : NNReal} {ε' : ℝ} {s : Finset ι} {T : ι → ShadedTube δ E}
    {tτ : Finset κ} {Tτ : κ → Tube τ E} {pτ : ι → κ}
    {tθ : Finset l} {Tθ : l → Tube θ E} {pθ : κ → l}
    {s' : Finset ι} {t''τ t'τ : Finset κ} {t'θ : Finset l}
    {Y' : ι → ShadedTube δ E} {Yτ : κ → ShadedTube τ E} {Yθ : l → ShadedTube θ E}
    {lamδ lamτ lamθ Nτ Nθ : NNReal}
    (h : IsFactorTwoScales ε' s T tτ Tτ pτ tθ Tθ pθ s' t''τ t'τ t'θ Y' Yτ Yθ
      lamδ lamτ lamθ Nτ Nθ) :
    t'τ ⊆ tτ :=
  h.mid_subset'.trans h.midAmbient_subset

/-! #### Arithmetic and transport lemmas for the two-scale chain -/

/-- **A tube has positive and finite carrier volume.**

`Tube.le_volume` bounds the carrier volume of a `ρ`-tube below by
`Tube.le_volume.c n * ρ ^ (n - 1)`, which is positive as soon as `ρ` is, and the carrier is
compact, hence of finite volume.

Both halves are needed to turn a termwise shading-density lower bound into a lower bound on
`ShadedBody.fullness`, which is a ratio of two sums: see
`Kakeya.ml1Boot.le_fullness_of_dens_lower`. -/
theorem tube_volume_pos_ne_top [Nontrivial E] {ρ : NNReal} (hρ : 0 < ρ) (T : Tube ρ E) :
    0 < volume T.carrier ∧ volume T.carrier ≠ ⊤ := by
  constructor
  · have hc : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) := by
      exact ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))
    have hρp : 0 < (ρ : ENNReal) ^ (Module.finrank ℝ E - 1) := by
      exact ENNReal.pow_pos (ENNReal.coe_pos.mpr hρ) (Module.finrank ℝ E - 1)
    have hpos : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
        (ρ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
      ENNReal.mul_pos (ne_of_gt hc) (ne_of_gt hρp)
    exact lt_of_lt_of_le hpos (by simpa using _root_.Tube.le_volume T)
  · exact T.isCompact.measure_lt_top.ne

/-- **A termwise shading-density lower bound descends to the fullness.**

If every member of a nonempty family of shaded `ρ`-tubes satisfies `|Z_k| ≥ λ |V_k|`, then
`λ ≤ λ(𝕍, Z)`: summing the termwise bound gives `λ ∑ |V_k| ≤ ∑ |Z_k|`, and the denominator
`∑ |V_k|` is positive and finite by `Kakeya.ml1Boot.tube_volume_pos_ne_top`, so the division
defining `ShadedBody.fullness` may be cleared.

A lower bound on a fullness does *not* pass to subfamilies, fullness being a ratio of two
sums, whereas a termwise bound does; that is what makes this the usable shape here.  The
two-scale chain needs `λ_{τ,1} ≤ λ(𝕋_τ|_{t''₁}, Z_{ρ,1})` for the middle family produced by
the first factoring step, and all it has about that family is the two-sided density bracket
`Kakeya.ml1Boot.IsFactorOneScale.coarse_dens`. -/
theorem le_fullness_of_dens_lower [Nontrivial E] {ρ : NNReal} (hρ : 0 < ρ) {κ : Type*}
    {u : Finset κ} (hu : u.Nonempty) (W : κ → ShadedTube ρ E) {lam : NNReal}
    (hdens : ∀ k ∈ u, (lam : ENNReal) * volume (W k).carrier ≤ volume (W k).shade) :
    (lam : ENNReal) ≤ (ShadedBody.fullness u (fun k => (W k).toShadedBody) : ENNReal) := by
  classical
  rw [ShadedBody.fullness_def]
  rcases hu with ⟨k₀, hk₀⟩
  have hden0 : (∑ i ∈ u, volume ((W i).toShadedBody).carrier) ≠ 0 := by
    have hsum : 0 < ∑ i ∈ u, volume ((W i).toShadedBody).carrier := by
      have hsingle : volume (W k₀).carrier ≤ ∑ i ∈ u, volume ((W i).toShadedBody).carrier := by
        simpa using Finset.single_le_sum (s := u)
          (f := fun i => volume ((W i).toShadedBody).carrier)
          (fun i hi => bot_le) hk₀
      exact lt_of_lt_of_le (by simpa using (tube_volume_pos_ne_top hρ (W k₀).toTube).1) hsingle
    exact ne_of_gt hsum
  have hdenTop : (∑ i ∈ u, volume ((W i).toShadedBody).carrier) ≠ ⊤ := by
    have hlt : (∑ i ∈ u, volume ((W i).toShadedBody).carrier) < ⊤ := by
      rw [ENNReal.sum_lt_top]
      intro i hi
      exact lt_top_iff_ne_top.mpr
        (by simpa using (tube_volume_pos_ne_top hρ (W i).toTube).2)
    exact ne_of_lt hlt
  rw [ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdenTop)]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun k hk => by simpa using hdens k hk)

/-- **The Frostman constant depends on the family only through its members on the index set.**

`ConvexSpaceBody.frostmanConstIn` is an infimum over the predicate
`ConvexSpaceBody.IsFrostmanIn`, and `Kakeya.isFrostmanIn_of_eqOn` transports that predicate
along a pointwise equality on the index set; taking the infimum in both directions gives
equality of the constants.

The two-scale chain needs this because the second factoring application is made to the
*shaded* middle family `Z_{ρ,1}`, so its Frostman item speaks about
`(Z_{ρ,1} k).toConvexSpaceBody`, whereas `Kakeya.ml1Boot.IsFactorTwoScales.frostman_mid` is
stated at the given middle tubes `𝕋_τ`.  On the retained index set the two agree, by
`Kakeya.ml1Boot.IsFactorOneScale.coarse_tube`. -/
theorem frostmanConstIn_congr {κ : Type*} (u : Finset κ) {W W' : κ → ConvexSpaceBody E}
    (h : ∀ k ∈ u, W k = W' k) (K : ConvexSpaceBody E) :
    frostmanConstIn u W K = frostmanConstIn u W' K := by
  apply le_antisymm
  · exact frostmanConstIn_le
      (isFrostmanIn_of_eqOn (E := E) (s := u) (W := W') (W' := W)
        (fun k hk => (h k hk).symm) (K := K) (C := frostmanConstIn u W' K)
        (isFrostmanIn_frostmanConstIn u W' K))
  · exact frostmanConstIn_le
      (isFrostmanIn_of_eqOn (E := E) (s := u) (W := W) (W' := W') h
        (K := K) (C := frostmanConstIn u W K) (isFrostmanIn_frostmanConstIn u W K))

/-- **Transporting a fibrewise Frostman comparison from a shaded family to the tubes it shades.**

Both fibres `fibre v p l'` and `fibre u p l'` occurring in the comparison lie inside `u`, where
the shaded family `Z_ρ` shades exactly the given tubes `𝕋_τ`, so
`Kakeya.ml1Boot.frostmanConstIn_congr` replaces the body family on both sides at once.

This is the step that turns the second factoring application's Frostman item — stated at the
*shaded* middle family it was applied to — into
`Kakeya.ml1Boot.IsFactorTwoScales.frostman_mid`, which is stated at the given middle tubes. -/
theorem frostmanConstIn_fibre_congr {κ lc : Type*} [DecidableEq lc]
    {τ : NNReal} {u v : Finset κ} {Tτ : κ → Tube τ E} {Zρ : κ → ShadedTube τ E}
    (hvu : v ⊆ u) (htube : ∀ k ∈ u, (Zρ k).toTube = Tτ k)
    {p : κ → lc} {l' : lc} {K : ConvexSpaceBody E} {x : ENNReal}
    (h : frostmanConstIn (fibre v p l') (fun k => (Zρ k).toConvexSpaceBody) K
        ≤ x * frostmanConstIn (fibre u p l') (fun k => (Zρ k).toConvexSpaceBody) K) :
    frostmanConstIn (fibre v p l') (fun k => (Tτ k).toConvexSpaceBody) K
      ≤ x * frostmanConstIn (fibre u p l') (fun k => (Tτ k).toConvexSpaceBody) K := by
  have hvbody : ∀ k ∈ fibre v p l', (Zρ k).toConvexSpaceBody = (Tτ k).toConvexSpaceBody := by
    intro k hk
    exact congrArg (fun T : Tube τ E => T.toConvexSpaceBody)
      (htube k (hvu (Finset.mem_filter.mp hk).1))
  have hubody : ∀ k ∈ fibre u p l', (Zρ k).toConvexSpaceBody = (Tτ k).toConvexSpaceBody := by
    intro k hk
    exact congrArg (fun T : Tube τ E => T.toConvexSpaceBody)
      (htube k (Finset.mem_filter.mp hk).1)
  have hv : frostmanConstIn (fibre v p l') (fun k => (Zρ k).toConvexSpaceBody) K =
      frostmanConstIn (fibre v p l') (fun k => (Tτ k).toConvexSpaceBody) K := by
    exact frostmanConstIn_congr (fibre v p l') (K := K)
      (W := fun k => (Zρ k).toConvexSpaceBody) (W' := fun k => (Tτ k).toConvexSpaceBody) hvbody
  have hu : frostmanConstIn (fibre u p l') (fun k => (Zρ k).toConvexSpaceBody) K =
      frostmanConstIn (fibre u p l') (fun k => (Tτ k).toConvexSpaceBody) K := by
    exact frostmanConstIn_congr (fibre u p l') (K := K)
      (W := fun k => (Zρ k).toConvexSpaceBody) (W' := fun k => (Tτ k).toConvexSpaceBody) hubody
  rw [hv] at h
  rw [hu] at h
  exact h

/-- **Weakening the constant of a `c`-refinement.**

`ShadedBody.IsCRefinement` adds to `ShadedBody.IsRefinement` the mass bound
`c ∑_{i ∈ s} |Z_i| ≤ ∑_{i ∈ s'} |Z'_i|`, so replacing `c` by a smaller constant only weakens
the statement.

`Kakeya.ml1Boot.isCRefinement_mono` in `Kakeya/DimensionThree/MainLemma1/ThreePass.lean` is the
same statement, but that file belongs to a later part of the development and is not among the
imports of this one, so the two-line proof is repeated here rather than the import graph being
rearranged.  It is used to bring the two one-scale factoring applications, made at an auxiliary
exponent `ε₀ < ε'`, down to the exponent `2 ε'` that
`Kakeya.ml1Boot.IsFactorTwoScales.fine_refinement` asks for. -/
theorem isCRefinement_weaken {ι : Type*} {s' s : Finset ι} {V' V : ι → ShadedBody E}
    {c c' : NNReal} (h : ShadedBody.IsCRefinement s' V' s V c) (hc : c' ≤ c) :
    ShadedBody.IsCRefinement s' V' s V c' := by
  exact ⟨h.1, le_trans (mul_le_mul' (ENNReal.coe_le_coe.mpr hc) le_rfl) h.2⟩

/-- **A refinement of a family of positive total shading volume has a nonempty index set.**

The mass clause of `ShadedBody.IsCRefinement` reads `c ∑_{i ∈ s} |Z_i| ≤ ∑_{i ∈ s'} |Z'_i|`, and
for `c > 0` and `∑_{i ∈ s} |Z_i| > 0` its left-hand side is positive, so the right-hand side
cannot be the empty sum.

This is how the two-scale chain would learn that its intermediate middle index set is nonempty,
which is what `Kakeya.ml1Boot.le_fullness_of_dens_lower` needs: the fine index set of the
two-scale factor pair is nonempty, and the parent of one of its members lies in that intermediate
set.  (`exists_twoScaleFactorPair` is not a declaration; blueprint
`note:ml1bootCaseTwoConstructionLayerEmpty`.) -/
theorem nonempty_of_isCRefinement_of_sum_shade_pos {ι : Type*} {s' s : Finset ι}
    {V' V : ι → ShadedBody E} {c : NNReal} (hc : 0 < c)
    (h : ShadedBody.IsCRefinement s' V' s V c)
    (hmass : 0 < ∑ i ∈ s, volume (V i).shade) : s'.Nonempty := by
  by_contra hne
  have hs' : s' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
  have hpos : 0 < (c : ENNReal) * ∑ i ∈ s, volume (V i).shade :=
    ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr hc.ne') hmass.ne'
  exact (not_le_of_gt hpos) (by simpa [hs'] using h.2)

/-- **Composing two fullness losses across an intermediate comparison.**

`Kakeya.ml1Boot.fullness_compose` chains `λ₁ ≥ C⁻¹ δ ^ a λ₀` with `λ₂ ≥ C⁻¹ δ ^ b λ₁`.  In the
two-scale chain the second application's fullness clause is stated at the *fullness* of the
middle family rather than at the number `λ_{τ,1}` produced by the first application, and the two
are related only by the one-sided `λ_{τ,1} ≤ λ(𝕋_τ|_{t''₁}, Z_{ρ,1})` of
`Kakeya.ml1Boot.le_fullness_of_dens_lower`.  Since the middle quantity occurs on the small side
of one inequality and the large side of the other, that one-sided comparison is enough. -/
theorem fullness_compose_through {C₁ C₂ : NNReal} (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂)
    {δ : NNReal} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {lam₀ lam₁ mid lam₂ : ENNReal}
    (h₁ : (C₁ : ENNReal)⁻¹ * (δ : ENNReal) ^ a * lam₀ ≤ lam₁)
    (hmid : lam₁ ≤ mid)
    (h₂ : (C₂ : ENNReal)⁻¹ * (δ : ENNReal) ^ b * mid ≤ lam₂) :
    ((C₁ : ENNReal) * (C₂ : ENNReal))⁻¹ * (δ : ENNReal) ^ (a + b) * lam₀ ≤ lam₂ := by
  exact fullness_compose hC₁ hC₂ hδ0 hδ1 ha hb (le_trans h₁ hmid) h₂

/-- **A subpolynomial factor is monotone decreasing in its exponent.**

For `0 < δ ≤ 1` the map `a ↦ δ ^ a` is antitone, so a larger exponent gives a smaller factor.
Every exponent alignment of the two-scale chain is an instance: the chain runs its two
applications at an auxiliary `ε₀ < ε'` and has to land on the budgets `δ ^ (2 ε')`, `δ ^ ε'`
and `δ ^ (-ε')` of `Kakeya.ml1Boot.IsFactorTwoScales`. -/
theorem rpow_mono_exponent {δ : NNReal} (_hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {a b : ℝ} (hab : a ≤ b) :
    (δ : ENNReal) ^ b ≤ (δ : ENNReal) ^ a := by
  exact ENNReal.rpow_le_rpow_of_exponent_ge (ENNReal.coe_le_one_iff.mpr hδ1) hab

/-- **Weakening the exponent of a `δ ^ a`-refinement.**

`Kakeya.ml1Boot.isCRefinement_weaken` in the shape the two-scale chain uses it: the refinement
constant of `Kakeya.ml1Boot.IsFactorTwoScales.fine_refinement` is `δ ^ (2 ε')`, while the two
applications deliver `δ ^ (2 ε₀)` with `ε₀ < ε'`, and for `δ ≤ 1` the former is the smaller. -/
theorem isCRefinement_weaken_exponent {ι : Type*} {s' s : Finset ι} {V' V : ι → ShadedBody E}
    {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {a b : ℝ} (hab : a ≤ b)
    (h : ShadedBody.IsCRefinement s' V' s V ⟨(δ : ℝ) ^ a, by positivity⟩) :
    ShadedBody.IsCRefinement s' V' s V ⟨(δ : ℝ) ^ b, by positivity⟩ := by
  refine isCRefinement_weaken h ?_
  exact NNReal.coe_le_coe.mp (Real.rpow_le_rpow_of_exponent_ge
    (by exact_mod_cast hδ0) (by exact_mod_cast hδ1) hab)

/-- **The one-scale factoring constant is at least `1`.**

It is `ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C 3 N σ 1`, whose outer `max 1`
records that the loss is never a gain.  `Kakeya.ml1Boot.fullness_compose`,
`Kakeya.ml1Boot.twoScaleLoss` and their two-scale specializations all take `1 ≤ C`, and this is
the form they are supplied in. -/
theorem one_le_factorOneScale_C (N : ℕ) (σ : NNReal) : 1 ≤ factorOneScale.C N σ :=
  ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.one_le_C 3 N σ 1

/-- **The two-scale constant is the product of the two one-scale constants, in `[0, ∞]`.**

`Kakeya.ml1Boot.factorTwoScales.C` is by definition that product; this records the commutation
of the product with the coercion into `ENNReal`, which is the form the fields of
`Kakeya.ml1Boot.IsFactorTwoScales` are stated in. -/
theorem coe_factorTwoScales_C (N₁ : ℕ) (δ : NNReal) (N₂ : ℕ) (τ : NNReal) :
    (factorTwoScales.C N₁ δ N₂ τ : ENNReal)
      = (factorOneScale.C N₁ δ : ENNReal) * (factorOneScale.C N₂ τ : ENNReal) := by
  simp [factorTwoScales.C]

/-- **Prefixing a bound by the inverse of a constant `≥ 1` only weakens it.** -/
theorem inv_coe_mul_le {C : NNReal} (hC : 1 ≤ C) {x y : ENNReal} (h : x ≤ y) :
    (C : ENNReal)⁻¹ * x ≤ y := by
  have h1c : 1 ≤ (C : ENNReal) := ENNReal.one_le_coe_iff.mpr hC
  have hc1 : (C : ENNReal)⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr h1c
  calc
    (C : ENNReal)⁻¹ * x ≤ 1 * x := by
      exact mul_le_mul_left hc1 x
    _ = x := by simp
    _ ≤ y := h

/-- **The composed fullness lower bound of the two-scale chain, at the exponent of the
conclusion.**

`Kakeya.ml1Boot.fullness_compose_through` followed by one weakening of the exponent: the two
applications each contribute `δ ^ a` with `a = 2 ε₀`, and the conclusion asks for `δ ^ e` with
`e ≥ 2 a`, which for `δ ≤ 1` is the weaker demand.  This is
`Kakeya.ml1Boot.IsFactorTwoScales.mid_fullness` and `coarse_fullness` in one step. -/
theorem twoScaleFullnessOut {C₁ C₂ : NNReal} (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂)
    {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {a e : ℝ} (ha : 0 ≤ a) (hae : 2 * a ≤ e) {F lam₁ mid lam₂ : ENNReal}
    (h₁ : (C₁ : ENNReal)⁻¹ * (δ : ENNReal) ^ a * F ≤ lam₁) (hmid : lam₁ ≤ mid)
    (h₂ : (C₂ : ENNReal)⁻¹ * (δ : ENNReal) ^ a * mid ≤ lam₂) :
    ((C₁ : ENNReal) * (C₂ : ENNReal))⁻¹ * (δ : ENNReal) ^ e * F ≤ lam₂ := by
  have hcomp := fullness_compose_through hC₁ hC₂ hδ0 hδ1 ha ha h₁ hmid h₂
  have hmono : ((C₁ : ENNReal) * (C₂ : ENNReal))⁻¹ * (δ : ENNReal) ^ e * F ≤
      ((C₁ : ENNReal) * (C₂ : ENNReal))⁻¹ * (δ : ENNReal) ^ (a + a) * F := by
    have hpe : (δ : ENNReal) ^ e ≤ (δ : ENNReal) ^ (a + a) :=
      rpow_mono_exponent hδ0 hδ1 (by linarith)
    gcongr
  exact le_trans hmono hcomp

/-- **The triple-product bound of the two-scale chain, assembled from three two-factor bounds.**

`Kakeya.ml1Boot.twoScaleLoss` at `σ = δ` composes the two applications' multiplicity items,
whose middle factor `B₁` is the multiplicity of the intermediate middle family; a third
substitution replaces the first application's fine factor `B₂` by the multiplicity of the fine
family the chain actually exports, at one more factor `δ ^ c`.  Three losses `δ ^ c` with
`c ≤ 0` therefore accumulate, and the conclusion's exponent `e ≤ 3 c` absorbs them because
`δ ≤ 1`.  The output order of the three factors is that of
`Kakeya.ml1Boot.IsFactorTwoScales.product`: fine, middle, coarse. -/
theorem twoScaleProduct {C₁ C₂ : NNReal} (_hC₁ : 1 ≤ C₁) (_hC₂ : 1 ≤ C₂)
    {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {c e : ℝ} (hce : e ≤ 3 * c) {A B₁ B₂ B₂' B₃ B₄ : ENNReal}
    (hA : A ≤ (C₁ : ENNReal) * (δ : ENNReal) ^ c * B₁ * B₂)
    (hB : B₁ ≤ (C₂ : ENNReal) * (δ : ENNReal) ^ c * B₃ * B₄)
    (hfine : B₂ ≤ (δ : ENNReal) ^ c * B₂') :
    A ≤ (C₁ : ENNReal) * (C₂ : ENNReal) * (δ : ENNReal) ^ e * B₂' * B₄ * B₃ := by
  have hδ0' : (δ : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hδ0)
  have hpow : (δ : ENNReal) ^ (3 * c) =
      (δ : ENNReal) ^ c * (δ : ENNReal) ^ c * (δ : ENNReal) ^ c := by
    rw [show 3 * c = c + c + c by ring]
    rw [ENNReal.rpow_add (c + c) c hδ0' ENNReal.coe_ne_top]
    rw [ENNReal.rpow_add c c hδ0' ENNReal.coe_ne_top]
  calc
    A ≤ (C₁ : ENNReal) * (δ : ENNReal) ^ c * B₁ * B₂ := hA
    _ ≤ (C₁ : ENNReal) * (δ : ENNReal) ^ c *
          ((C₂ : ENNReal) * (δ : ENNReal) ^ c * B₃ * B₄) * ((δ : ENNReal) ^ c * B₂') := by
          gcongr
    _ = (C₁ : ENNReal) * (C₂ : ENNReal) * (δ : ENNReal) ^ (3 * c) * B₂' * B₄ * B₃ := by
          rw [hpow]
          ring
    _ ≤ (C₁ : ENNReal) * (C₂ : ENNReal) * (δ : ENNReal) ^ e * B₂' * B₄ * B₃ := by
      have hpowle : (δ : ENNReal) ^ (3 * c) ≤ (δ : ENNReal) ^ e :=
        rpow_mono_exponent hδ0 hδ1 hce
      calc
        (C₁ : ENNReal) * (C₂ : ENNReal) * (δ : ENNReal) ^ (3 * c) * B₂' * B₄ * B₃
            = (C₁ : ENNReal) * (C₂ : ENNReal) * B₂' * B₄ * B₃ * (δ : ENNReal) ^ (3 * c) := by ring
        _ ≤ (C₁ : ENNReal) * (C₂ : ENNReal) * B₂' * B₄ * B₃ * (δ : ENNReal) ^ e := by
              exact mul_le_mul_of_nonneg_left hpowle zero_le
        _ = (C₁ : ENNReal) * (C₂ : ENNReal) * (δ : ENNReal) ^ e * B₂' * B₄ * B₃ := by ring

/-- **A retained singleton classification is the whole singleton.**

`Kakeya.ml1Boot.IsFactorOneScale.aux_card` reads `δ ^ (2 ε') |tq| ≤ |t'q|`, and for `0 < δ` the
factor is nonzero, so at `tq = {}` the retained set is nonempty; being a subset of a
singleton it is the singleton.  This is what lets the two-scale chain state its first
application with the literal `({} : Finset Unit)` in the `t'q` slot instead of an
existentially bound one. -/
theorem aux_eq_singleton_of_isFactorOneScale {δ : NNReal} (hδ0 : 0 < δ) {ε' : ℝ}
    {σ ρ : NNReal} {ι κ : Type*} [DecidableEq κ] {s : Finset ι} {t : Finset κ}
    {V : ι → ShadedTube σ E} {Vρ : κ → Tube ρ E} {p : ι → κ}
    {s' : Finset ι} {t'' : Finset κ} {t'q : Finset Unit}
    {Z' : ι → ShadedTube σ E} {Zρ : κ → ShadedTube ρ E} {lamσ lamρ N : NNReal}
    (h : IsFactorOneScale δ ε' s V t Vρ p ({()} : Finset Unit) (fun _ => ())
      s' t'' t'q Z' Zρ lamσ lamρ N) :
    t'q = ({()} : Finset Unit) := by
  apply Finset.eq_of_subset_of_card_le h.aux_subset
  have hcard_unit : (({()} : Finset Unit).card : ENNReal) = 1 := by simp
  have hδpos0 : 0 < (δ : ENNReal) ^ (2 * ε') :=
    ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ0) ENNReal.coe_ne_top
  have hcard_enn : 0 < (t'q.card : ENNReal) := by
    have hle : (δ : ENNReal) ^ (2 * ε') ≤ (t'q.card : ENNReal) := by
      simpa [hcard_unit] using h.aux_card
    exact lt_of_lt_of_le (by simpa using hδpos0) hle
  have hcard_ne : t'q.card ≠ 0 := by
    intro hz
    have : (t'q.card : ENNReal) = 0 := by simp [hz]
    exact (ne_of_gt hcard_enn) this
  have hcard : 0 < t'q.card := Nat.pos_of_ne_zero hcard_ne
  simpa using hcard

/-- **The coarse output of one factoring step satisfies the hypotheses of the next one.**

The second application of `Kakeya.ml1Boot.exists_factorOneScaleUniform` in the two-scale chain
is made to the coarse family `(t''₁, Z_{ρ,1})` produced by the first, at tube scale `τ` and
parent scale `θ`.  Its four geometric hypotheses are all read off the first bundle:

* `t''₁` is nonempty because `0 < ∑_{i ∈ s} |Z i|` and the mass clause of `fine_refinement`
  force `s'₁` to be nonempty (`Kakeya.ml1Boot.nonempty_of_isCRefinement_of_sum_shade_pos`), and
  `branch_mapsTo` then puts a parent of a retained member in `t''₁`;
* containment in `B₁` and pairwise essential distinctness transfer from `𝕋_τ` because
  `coarse_tube` says the coarse shading shades the *given* parent tubes, so the carriers agree,
  and `coarse_subset` places `t''₁` inside `tτ`;
* the `θ`-parent family restricts along `t''₁ ⊆ tτ`, injectivity of the `θ`-family being a
  statement about `tθ` alone.

Isolating this is what would make the two-scale factor pair a short assembly; that assembly is
not written, `exists_twoScaleFactorPair` being no declaration (blueprint
`note:ml1bootCaseTwoConstructionLayerEmpty`). -/
theorem coarse_hypotheses_of_isFactorOneScale {δ : NNReal} (hδ0 : 0 < δ) {ε' : ℝ}
    {τ θ : NNReal} {ι κ l : Type*} [DecidableEq κ] [DecidableEq l]
    {s : Finset ι} {tτ : Finset κ} {tθ : Finset l}
    {T : ι → ShadedTube δ E} {Tτ : κ → Tube τ E} {pτ : ι → κ}
    {Tθ : l → Tube θ E} {pθ : κ → l}
    {s'₁ : Finset ι} {t''₁ : Finset κ} {t'q₁ : Finset Unit}
    {Z'₁ : ι → ShadedTube δ E} {Zρ₁ : κ → ShadedTube τ E} {lamδ₁ lamτ₁ N₁ : NNReal}
    (hballτ : ∀ k ∈ tτ, (Tτ k).carrier ⊆ Metric.closedBall 0 1)
    (hEDτ : (tτ : Set κ).Pairwise
      fun k k' => IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier)
    (hparθ : IsParentFamily tτ Tτ tθ Tθ pθ)
    (hmass : 0 < ∑ i ∈ s, volume (T i).shade)
    (h1 : IsFactorOneScale δ ε' s T tτ Tτ pτ ({()} : Finset Unit) (fun _ => ())
      s'₁ t''₁ t'q₁ Z'₁ Zρ₁ lamδ₁ lamτ₁ N₁) :
    t''₁.Nonempty ∧
    (∀ k ∈ t''₁, (Zρ₁ k).carrier ⊆ Metric.closedBall 0 1) ∧
    (t''₁ : Set κ).Pairwise
      (fun k k' => IsEssentiallyDistinct (Zρ₁ k).carrier (Zρ₁ k').carrier) ∧
    IsParentFamily t''₁ (fun k => (Zρ₁ k).toTube) tθ Tθ pθ := by
  have hRδ : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hc : 0 < (⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩ : NNReal) := by
    exact_mod_cast (Real.rpow_pos_of_pos hRδ (2 * ε'))
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hnon : s'₁.Nonempty :=
      nonempty_of_isCRefinement_of_sum_shade_pos hc h1.fine_refinement hmass
    rcases hnon with ⟨i, hi⟩
    exact ⟨pτ i, h1.branch_mapsTo i hi⟩
  · intro k hk
    have hcar : (Zρ₁ k).carrier = (Tτ k).carrier :=
      congrArg (fun T : Tube τ E => T.carrier) (h1.coarse_tube k hk)
    rw [hcar]
    exact hballτ k (h1.coarse_subset hk)
  · intro k hk k' hk' hne
    have hED : IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier :=
      hEDτ (h1.coarse_subset hk) (h1.coarse_subset hk') hne
    have hkcar : (Zρ₁ k).carrier = (Tτ k).carrier :=
      congrArg (fun T : Tube τ E => T.carrier) (h1.coarse_tube k hk)
    have hk'car : (Zρ₁ k').carrier = (Tτ k').carrier :=
      congrArg (fun T : Tube τ E => T.carrier) (h1.coarse_tube k' hk')
    simpa [hkcar, hk'car] using hED
  · constructor
    · intro k hk
      exact hparθ.mapsTo k (h1.coarse_subset hk)
    · exact hparθ.injOn
    · intro k hk
      rw [h1.coarse_tube k hk]
      exact hparθ.le_parent k (h1.coarse_subset hk)

/-! #### The refutation of the fine pair

The configuration described in the docstring of `Kakeya.ml1Boot.exists_twoScaleFinePair` is
realized below, and `Kakeya.ml1Boot.not_exists_twoScaleFinePair` is the resulting refutation.
The declarations between here and it are the pieces it is assembled from: a shaded tube with a
prescribed shading, uniformity of a one-member family, the multiplicity of a one-member family,
a density constant matching a prescribed pair of volumes, a smallness clause for a positive
power of the auxiliary parameter, a one-member `Kakeya.ml1Boot.IsFactorOneScale` bundle, and
the geometry of the counterexample.
-/

omit [BorelSpace E] in
/-- **A shading of a prescribed tube by a prescribed measurable subset.**

The tube `T` shaded by `S`.  This is the general form of
`Kakeya.ml1Boot.exists_nullShadedTube`, and it is how the three shadings of the counterexample
to `Kakeya.ml1Boot.exists_twoScaleFinePair` are produced: the fine shading is the whole carrier
of the fine tube, the middle shading is the whole carrier of the parent tube, and the retained
middle shading is a ball disjoint from the fine tube. -/
theorem exists_shadedTube_of_subset {ρ : NNReal} (T : Tube ρ E) {S : Set E}
    (hS : MeasurableSet S) (hST : S ⊆ T.carrier) :
    ∃ Z : ShadedTube ρ E, Z.toTube = T ∧ Z.shade = S :=
  ⟨{ toTube := T, shade := S, measurableSet_shade := hS, shade_subset := hST }, rfl, rfl⟩

/-- **A one-member family is uniform, at every grid length and every constant `≥ 1`.**

With a single index there is only one node at each grid scale — the member's own tube rescaled
to the grid radius, which contains it because `σ ≤ ρ_k` for `k ≤ N` and `σ ≤ 1` — so every
class, every shade class and every node set is a singleton or empty.  The four brackets of
`ShadedTube.ShadedUniformTubeSet` and the two of `Tube.UniformTubeSet` then hold at
`branchingN = localN = 1`, since each of them compares two quantities equal to `1` up to the
factor `C ≥ 1`.  Nestedness is automatic, the assignment being constant, and the nodes are
nested because the grid radius decreases in `k`.

This is the companion of `Kakeya.ml1Boot.nonempty_shadedUniformTubeSet_empty` at the other
degenerate size, and it is what supplies `fine_unif`, `coarse_unif` and `fibreUnif` for the
one-member bundles of `Kakeya.ml1Boot.isFactorOneScale_singleton`. -/
theorem nonempty_shadedUniformTubeSet_singleton {σ : NNReal} (hσ1 : σ ≤ 1) {ι : Type*}
    (i₀ : ι) (V : ι → ShadedTube σ E) (N : ℕ) {C : NNReal} (hC : 1 ≤ C) :
    Nonempty (ShadedTube.ShadedUniformTubeSet ({i₀} : Finset ι) V N C) := by
  classical
  have gridAntitone : ∀ {a b : ℕ}, a ≤ b →
      Tube.gridScale σ N b ≤ Tube.gridScale σ N a := by
    intro a b hab
    by_cases hN : (N : ℝ) = 0
    · simp [Tube.gridScale, hN]
    · by_cases hσ0 : σ = 0
      · subst σ
        by_cases ha0 : a = 0
        · subst ha0
          simpa [Tube.gridScale]
            using (Tube.gridScale_le_one hσ1 N b)
        · have hb0 : b ≠ 0 := by
            omega
          have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb0
          have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha0
          have he1 : (b : ℝ) / (N : ℝ) ≠ 0 := div_ne_zero hbR hN
          have he2 : (a : ℝ) / (N : ℝ) ≠ 0 := div_ne_zero haR hN
          simp [Tube.gridScale, he1, he2]
      · have hσpos : 0 < σ := lt_of_le_of_ne (by positivity) (Ne.symm hσ0)
        apply NNReal.rpow_le_rpow_of_exponent_ge hσpos hσ1
        exact div_le_div_of_nonneg_right (by exact_mod_cast hab)
          (by exact_mod_cast (Nat.zero_le N))
  have gridAbove : ∀ {k : ℕ}, k ≤ N → σ ≤ Tube.gridScale σ N k := by
    intro k hk
    by_cases hN : N = 0
    · subst N
      have hk0 : k = 0 := by omega
      subst hk0
      simpa [Tube.gridScale] using hσ1
    · have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
      by_cases hσ0 : σ = 0
      · rw [hσ0]
        simp
      · have hdiv : (k : ℝ) / (N : ℝ) ≤ 1 := by
          rw [← div_self (ne_of_gt hNpos)]
          exact div_le_div_of_nonneg_right (by exact_mod_cast hk) (le_of_lt hNpos)
        have hσpos : 0 < σ := lt_of_le_of_ne (by positivity) (Ne.symm hσ0)
        simpa [Tube.gridScale]
          using (NNReal.rpow_le_rpow_of_exponent_ge hσpos hσ1 hdiv)
  let gcs : Tube.GridCoverSystem ({i₀} : Finset ι) (fun i => (V i).toTube) N :=
    { indexSet := fun _ => ({i₀} : Finset ι)
      assign := fun _ i => i₀
      tube := fun k _ => (V i₀).toTube.rescale (Tube.gridScale σ N k)
      assign_mem := by simp
      le_tube_assign := by
        intro k hk i hi
        have hi₀ : i = i₀ := Finset.mem_singleton.mp hi
        subst i
        exact Tube.le_rescale (V i₀).toTube (gridAbove hk)
      nested := by simp
      tube_nested := by
        intro k hk i hi
        exact Tube.rescale_le_rescale_of_radius_le (V i₀).toTube
          (gridAntitone (Nat.le_succ k)) }
  let utu : Tube.UniformTubeSet ({i₀} : Finset ι) (fun i => (V i).toTube) N C :=
    { cover := gcs
      branchingN := fun _ => 1
      tube_injOn := by
        intro k hk a ha b hb hab
        have ha' : a ∈ ({i₀} : Finset ι) := by simpa [gcs] using ha
        have hb' : b ∈ ({i₀} : Finset ι) := by simpa [gcs] using hb
        exact (Finset.mem_singleton.mp ha').trans (Finset.mem_singleton.mp hb').symm
      boundedOverlap := by
        intro k hk W
        have hle : ((gcs.indexSet k).filter
            (fun j => ∃ i ∈ ({i₀} : Finset ι),
              (V i).toTube.toConvexSpaceBody ≤ (gcs.tube k j).toConvexSpaceBody ∧
              (V i).toTube.toConvexSpaceBody ≤ W.toConvexSpaceBody)).card
            ≤ (gcs.indexSet k).card :=
          Finset.card_filter_le _ _
        have hleNN : (((gcs.indexSet k).filter
            (fun j => ∃ i ∈ ({i₀} : Finset ι),
              (V i).toTube.toConvexSpaceBody ≤ (gcs.tube k j).toConvexSpaceBody ∧
              (V i).toTube.toConvexSpaceBody ≤ W.toConvexSpaceBody)).card : NNReal)
            ≤ ((gcs.indexSet k).card : NNReal) := by
          exact_mod_cast hle
        have hcard : ((gcs.indexSet k).card : NNReal) ≤ C := by simpa [gcs] using hC
        exact hleNN.trans hcard
      card_class_le := by
        intro k hk j hj
        have hg : j = i₀ := by simpa [gcs] using hj
        simpa [gcs, hg, Tube.coverClass] using hC
      le_card_class := by
        intro k hk j hj
        have hg : j = i₀ := by simpa [gcs] using hj
        simpa [gcs, hg, Tube.coverClass] using hC }
  refine ⟨{ tubeUniform := utu
            branchingN := fun _ => 1
            localN := fun _ _ => 1
            card_shadeClass_le := by
              intro x hx k hk i hi hxi
              have hsub : (ShadedTube.shadeClass ({i₀} : Finset ι) V
                    (utu.cover.assign k) (utu.cover.assign k i) x) ⊆ ({i₀} : Finset ι) := by
                exact (ShadedTube.shadeClass_subset ({i₀} : Finset ι) V
                    (utu.cover.assign k) (utu.cover.assign k i) x).trans
                  (Finset.filter_subset (fun z => utu.cover.assign k z = utu.cover.assign k i)
                    ({i₀} : Finset ι))
              have hle2 : (((ShadedTube.shadeClass ({i₀} : Finset ι) V
                    (utu.cover.assign k) (utu.cover.assign k i) x).card : NNReal))
                  ≤ (1 : NNReal) := by
                have hle3 : ((ShadedTube.shadeClass ({i₀} : Finset ι) V
                      (utu.cover.assign k) (utu.cover.assign k i) x).card : NNReal)
                      ≤ (({i₀} : Finset ι).card : NNReal) := by
                  exact_mod_cast (Finset.card_le_card hsub)
                simpa using hle3
              simpa using (hle2.trans hC)
            le_card_shadeClass := by
              intro x hx k hk i hi hxi
              have hii : i = i₀ := by simpa [gcs] using hi
              subst i
              have hmem : i₀ ∈ ShadedTube.shadeClass ({i₀} : Finset ι) V
                    (utu.cover.assign k) (utu.cover.assign k i₀) x := by
                simp [ShadedTube.shadeClass, Tube.coverClass, utu, gcs, hxi]
              have hpos : 0 < (ShadedTube.shadeClass ({i₀} : Finset ι) V
                    (utu.cover.assign k) (utu.cover.assign k i₀) x).card :=
                Finset.card_pos.mpr ⟨i₀, hmem⟩
              have hone : (1 : NNReal) ≤ (ShadedTube.shadeClass ({i₀} : Finset ι) V
                    (utu.cover.assign k) (utu.cover.assign k i₀) x).card := by
                exact_mod_cast (Nat.succ_le_of_lt hpos)
              have hprod : (C : NNReal) ≤ C * (ShadedTube.shadeClass ({i₀} : Finset ι) V
                    (utu.cover.assign k) (utu.cover.assign k i₀) x).card := by
                rw [mul_comm]
                simpa using (mul_le_mul_left hone (C : NNReal))
              exact hC.trans hprod
            branchingN_le := by
              intro x hx k hk
              simpa using hC
            le_branchingN := by
              intro x hx k hk
              simpa using hC }⟩

/-- **The multiplicity of a one-member family is `1`.**

`ShadedBody.multiplicity` is the total shading volume divided by the volume of the union of the
shadings; over a single index the two agree, and the quotient is `1` as soon as that common
value is neither `0` nor `∞` — the latter being automatic, a shading sitting inside a compact
carrier. -/
theorem multiplicity_singleton {ι : Type*} (i₀ : ι) (V : ι → ShadedBody E)
    (h : volume (V i₀).shade ≠ 0) :
    ShadedBody.multiplicity ({i₀} : Finset ι) V = 1 := by
  rw [ShadedBody.multiplicity_eq_div]
  rw [Finset.sum_singleton]
  rw [Finset.set_biUnion_singleton]
  exact ENNReal.div_self h
    (ne_top_of_le_ne_top (V i₀).isCompact.measure_ne_top (measure_mono (V i₀).shade_subset))

/-- **A density constant matching a prescribed pair of volumes.**

For `a`, `b` positive and finite there is a positive `λ` with `λ b = a` exactly, namely
`(a / b).toNNReal`.  Both halves of a two-sided density bracket `λ b ≤ a ≤ 2 λ b` follow at
once.  This is what produces the middle density `λ_{τ,2}` of the counterexample, where the
retained middle shading is a ball whose volume is not a convenient multiple of the volume of
the parent tube. -/
theorem exists_nnreal_mul_eq {a b : ENNReal} (ha0 : a ≠ 0) (hatop : a ≠ ⊤)
    (hb0 : b ≠ 0) (hbtop : b ≠ ⊤) :
    ∃ lam : NNReal, 0 < lam ∧ (lam : ENNReal) * b = a := by
  refine ⟨(a / b).toNNReal, ?_, ?_⟩
  · exact ENNReal.toNNReal_pos (ENNReal.div_ne_zero.mpr ⟨ha0, hbtop⟩)
      (ENNReal.div_ne_top hatop hb0)
  · rw [ENNReal.coe_toNNReal (ENNReal.div_ne_top hatop hb0), ENNReal.div_mul_cancel hb0 hbtop]

/-- **A positive power of the auxiliary parameter is eventually below any positive bound.**

For `0 < b` the map `δ ↦ δ ^ b` is monotone and tends to `0`, so `δ ^ b ≤ a` holds on a
neighbourhood of `0` in `(0, ∞)` for every `a ≠ 0`: it suffices that `δ ≤ a ^ (1 / b)`, which is
a clause of `𝓝[>] 0` by `Kakeya.ml1Boot.eventually_le_nhdsGT`.  This is the smallness that the
refutation of `Kakeya.ml1Boot.exists_twoScaleFinePair` extracts, at `b = 2 ε₀`. -/
theorem eventually_rpow_le {a : ENNReal} (ha0 : a ≠ 0) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, (δ : ENNReal) ^ b ≤ a := by
  by_cases hatop : a = ⊤
  · exact Filter.Eventually.of_forall fun δ => by
      rw [hatop]
      exact le_top
  · let c : NNReal := a.toNNReal ^ (1 / b)
    have hto : 0 < a.toNNReal := ENNReal.toNNReal_pos ha0 hatop
    have hc : 0 < c := by
      dsimp [c]
      exact NNReal.rpow_pos hto
    filter_upwards [eventually_le_nhdsGT hc] with δ hδ
    have hδc : (δ : ENNReal) ≤ (c : ENNReal) := by
      exact_mod_cast hδ
    have hc_pow : c ^ b = a.toNNReal := by
      calc
        c ^ b = (a.toNNReal ^ (1 / b)) ^ b := by rfl
        _ = a.toNNReal ^ ((1 / b) * b) := by
          rw [← NNReal.rpow_mul a.toNNReal (1 / b) b]
        _ = a.toNNReal ^ (1 : ℝ) := by
          rw [one_div_mul_cancel hb.ne']
        _ = a.toNNReal := by
          rw [NNReal.rpow_one]
    calc
      (δ : ENNReal) ^ b ≤ (c : ENNReal) ^ b :=
        ENNReal.rpow_le_rpow hδc hb.le
      _ = ((c ^ b : NNReal) : ENNReal) := by
        rw [← ENNReal.coe_rpow_of_nonneg c hb.le]
      _ = ((a.toNNReal : NNReal) : ENNReal) := by
        rw [hc_pow]
      _ = a := by
        rw [ENNReal.coe_toNNReal hatop]

/-- **A one-member `Kakeya.ml1Boot.IsFactorOneScale` bundle.**

Everything is indexed by `Unit`: the family is the single shaded `σ`-tube `V₀`, its parent is
the single `ρ`-tube `P₀`, and both retained index sets and the classification data are the
singleton.  The output shadings are `Z'₀` of `V₀` and `Z_ρ₀` of `P₀`, and the branching number
is `1`.

Every field is then either vacuous, a statement about a singleton, or one of the hypotheses.
The two fullness fields are stated here in the stronger form `δ ^ (2 ε') ≤ λ_σ` and
`C⁻¹ δ ^ (2 ε') ≤ λ_ρ`, which implies the fields because `ShadedBody.fullness_le_one`.  The two
non-nullity hypotheses are what `product` needs: over singletons all three multiplicities are
`1` by `Kakeya.ml1Boot.multiplicity_singleton`, and `1 ≤ C δ ^ (-2 ε')`.  Nothing here relates
`V₀` to `P₀`: no field of `Kakeya.ml1Boot.IsFactorOneScale` does, the containment of a member in
its parent living in `Kakeya.ml1Boot.IsParentFamily` instead.

Both bundles of the counterexample to `Kakeya.ml1Boot.exists_twoScaleFinePair` are instances of
this, which is what makes that counterexample short. -/
theorem isFactorOneScale_singleton {σ ρ δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1) {ε' : ℝ} (hε' : 0 < ε')
    (V₀ Z'₀ : ShadedTube σ E) (P₀ : Tube ρ E) (Zρ₀ : ShadedTube ρ E) (lamσ lamρ : NNReal)
    (htube : Z'₀.toTube = V₀.toTube) (hshade : Z'₀.shade ⊆ V₀.shade)
    (hmass : (δ : ENNReal) ^ (2 * ε') * volume V₀.shade ≤ volume Z'₀.shade)
    (hdens₁ : (lamσ : ENNReal) * volume V₀.carrier ≤ volume Z'₀.shade)
    (hdens₂ : volume Z'₀.shade ≤ 2 * (lamσ : ENNReal) * volume V₀.carrier)
    (hfull : (δ : ENNReal) ^ (2 * ε') ≤ (lamσ : ENNReal))
    (hcoarseTube : Zρ₀.toTube = P₀)
    (hdensρ₁ : (lamρ : ENNReal) * volume P₀.carrier ≤ volume Zρ₀.shade)
    (hdensρ₂ : volume Zρ₀.shade ≤ 2 * (lamρ : ENNReal) * volume P₀.carrier)
    (hfullρ : (factorOneScale.C 1 σ : ENNReal)⁻¹ * (δ : ENNReal) ^ (2 * ε') ≤ (lamρ : ENNReal))
    (hcontain : Z'₀.shade ⊆ Zρ₀.shade)
    (hne' : volume Z'₀.shade ≠ 0) (hneρ : volume Zρ₀.shade ≠ 0) :
    IsFactorOneScale δ ε' ({()} : Finset Unit) (fun _ => V₀) ({()} : Finset Unit)
      (fun _ => P₀) (fun _ => ()) ({()} : Finset Unit) (fun _ => ())
      ({()} : Finset Unit) ({()} : Finset Unit) ({()} : Finset Unit)
      (fun _ => Z'₀) (fun _ => Zρ₀) lamσ lamρ 1 := by
  classical
  have hε : 0 ≤ 2 * ε' := by positivity
  have hpow1 : (δ : ENNReal) ^ (2 * ε') ≤ 1 :=
    ENNReal.rpow_le_one (by exact_mod_cast hδ1) hε
  have hpowinv : (1 : ENNReal) ≤ (δ : ENNReal) ^ (-2 * ε') := by
    rw [show -2 * ε' = -(2 * ε') by ring]
    rw [ENNReal.rpow_neg]
    exact ENNReal.le_inv_iff_mul_le.mpr (by simpa using hpow1)
  have hC1 : (1 : NNReal) ≤ factorOneScale.C 1 σ := by
    exact one_le_factorOneScale_C 1 σ
  have hC1' : (1 : ENNReal) ≤ (factorOneScale.C 1 σ : ENNReal) := by
    exact_mod_cast hC1
  have hfib : fibre ({()} : Finset Unit) (fun _ : Unit => ()) () = ({()} : Finset Unit) := by
    simp [fibre]
  refine {
    fine_subset := ?_,
    fine_shade := ?_,
    fine_refinement := ?_,
    fine_unif := ?_,
    fine_essDistinct := ?_,
    fine_dens := ?_,
    fine_fullness := ?_,
    coarse_subset := ?_,
    coarse_tube := ?_,
    coarse_unif := ?_,
    coarse_essDistinct := ?_,
    coarse_dens := ?_,
    coarse_fullness := ?_,
    aux_subset := ?_,
    aux_card := ?_,
    contain := ?_,
    branch_mapsTo := ?_,
    branch_card := ?_,
    frostman := ?_,
    product := ?_,
    fibreUnif := ?_ }
  · exact Finset.Subset.refl _
  · intro i _
    exact ⟨htube, hshade⟩
  · constructor
    · constructor
      · exact Finset.Subset.refl _
      · intro i _
        constructor
        · simpa using congrArg (fun T : Tube σ E => T.toConvexSpaceBody) htube
        · exact hshade
    · have hcoe : ((δ ^ (2 * ε') : NNReal) : ENNReal) = (δ : ENNReal) ^ (2 * ε') :=
        ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδ0) (2 * ε')
      simp only [Finset.sum_singleton]
      change ((δ ^ (2 * ε') : NNReal) : ENNReal) * volume V₀.shade ≤ volume Z'₀.shade
      rw [hcoe]
      exact hmass
  · exact nonempty_shadedUniformTubeSet_singleton hσ1 () (fun _ => Z'₀)
      (Tube.ssfGridLen σ) (one_le_uniformize_C 3)
  · simp
  · intro i _
    exact ⟨hdens₁, hdens₂⟩
  · have hf : (ShadedBody.fullness ({()} : Finset Unit)
        (fun _ => V₀.toShadedBody) : ENNReal) ≤ 1 := by
      exact_mod_cast ShadedBody.fullness_le_one ({()} : Finset Unit) (fun _ => V₀.toShadedBody)
    calc
      (δ : ENNReal) ^ (2 * ε') *
          (ShadedBody.fullness ({()} : Finset Unit) (fun _ => V₀.toShadedBody) : ENNReal)
          ≤ (δ : ENNReal) ^ (2 * ε') * 1 := by
            gcongr
      _ = (δ : ENNReal) ^ (2 * ε') := by rw [mul_one]
      _ ≤ (lamσ : ENNReal) := hfull
  · exact Finset.Subset.refl _
  · intro k _
    exact hcoarseTube
  · exact nonempty_shadedUniformTubeSet_singleton hρ1 () (fun _ => Zρ₀)
      (Tube.ssfGridLen ρ) (one_le_uniformize_C 3)
  · simp
  · intro k _
    exact ⟨hdensρ₁, hdensρ₂⟩
  · let hf : (ShadedBody.fullness ({()} : Finset Unit)
        (fun _ => V₀.toShadedBody) : ENNReal) ≤ 1 := by
      exact_mod_cast ShadedBody.fullness_le_one ({()} : Finset Unit) (fun _ => V₀.toShadedBody)
    calc
      (factorOneScale.C 1 σ : ENNReal)⁻¹ * (δ : ENNReal) ^ (2 * ε') *
          (ShadedBody.fullness ({()} : Finset Unit) (fun _ => V₀.toShadedBody) : ENNReal)
          ≤ (factorOneScale.C 1 σ : ENNReal)⁻¹ * (δ : ENNReal) ^ (2 * ε') * 1 := by
            gcongr
      _ = (factorOneScale.C 1 σ : ENNReal)⁻¹ * (δ : ENNReal) ^ (2 * ε') := by rw [mul_one]
      _ ≤ (lamρ : ENNReal) := hfullρ
  · exact Finset.Subset.refl _
  · exact rpow_mul_card_le_card hδ1 (by positivity) ({()} : Finset Unit)
  · exact fun i hi hk => hcontain
  · intro i _
    simp
  · intro k hk
    have hk₁ : k = () := Finset.mem_singleton.mp hk
    subst hk₁
    constructor
    · simp [hfib]
    · constructor
      · simp [hfib]
      · simpa [hfib] using hpow1
  · intro k hk K u
    have hk₁ : k = () := Finset.mem_singleton.mp hk
    subst hk₁
    exact le_mul_of_one_le_left zero_le hpowinv
  · intro k hk
    have hVmono : volume Z'₀.shade ≤ volume V₀.shade := measure_mono hshade
    have hVne : volume V₀.shade ≠ 0 := by
      intro h
      exact hne' (le_antisymm (by simpa [h] using hVmono) zero_le)
    rw [multiplicity_singleton () (fun _ : Unit => V₀.toShadedBody) hVne]
    rw [multiplicity_singleton () (fun _ : Unit => Zρ₀.toShadedBody) hneρ]
    rw [hfib]
    rw [multiplicity_singleton () (fun _ : Unit => Z'₀.toShadedBody) hne']
    have hm : (1 : ENNReal) ≤ (factorOneScale.C 1 σ : ENNReal) * (δ : ENNReal) ^ (-2 * ε') := by
      calc
        (1 : ENNReal) = 1 * 1 := by rw [one_mul]
        _ ≤ (factorOneScale.C 1 σ : ENNReal) * (δ : ENNReal) ^ (-2 * ε') :=
          mul_le_mul hC1' hpowinv zero_le zero_le
    simpa [mul_one] using hm
  · intro k hk
    have hk₁ : k = () := Finset.mem_singleton.mp hk
    subst hk₁
    exact nonempty_isFlatPrismUniform_fibre_of_shadedUniformTubeSet (fun _ : Unit => ()) ()
      (nonempty_shadedUniformTubeSet_singleton hσ1 () (fun _ => Z'₀) (Tube.ssfGridLen σ)
        (one_le_uniformize_C 3))

/-- **The geometry of the counterexample to `Kakeya.ml1Boot.exists_twoScaleFinePair`.**

In `B₁ ⊆ ℝ³`, around the segment from `-e/2` to `e/2` with `e` the first standard basis vector:
`W` is the `(1/2)`-tube, `V` is the concentric `δ`-tube, and `B` is the closed ball of radius
`1/16` about `(3/4) e`.  That ball lies within `1/2` of the endpoint `e/2` of the core, hence
inside `W`; and every point of `V` is within `δ ≤ 1/8` of the core, whose points are at distance
at least `1/4` from `(3/4) e`, so `B` and `V` are disjoint.  Finally `B` has volume
`(1/16)³ |B₁|` while `W ⊆ B₁`, which is the last clause.

`B` is the "large part of the middle shading disjoint from the fine shadings" of the docstring
of `Kakeya.ml1Boot.exists_twoScaleFinePair`.  It is a ball rather than the whole complement
`W \ V` because the middle density bracket is two-sided: the retained middle shading has to
have volume comparable to a *prescribed* multiple of `|W|`, and a ball's volume is computable
whereas `|W| - |V|` is not, at this level of the development. -/
theorem exists_finePairCounterexampleGeometry {δ : NNReal} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8) :
    ∃ (W : Tube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3)))
      (V : Tube δ (EuclideanSpace ℝ (Fin 3))) (B : Set (EuclideanSpace ℝ (Fin 3))),
      W.carrier ⊆ Metric.closedBall 0 1 ∧
      V.carrier ⊆ Metric.closedBall 0 1 ∧
      V.toConvexSpaceBody ≤ W.toConvexSpaceBody ∧
      0 < volume V.carrier ∧
      MeasurableSet B ∧ B ⊆ W.carrier ∧ Disjoint B V.carrier ∧
      0 < volume B ∧ volume W.carrier ≤ 4096 * volume B := by
  let e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 (1 : ℝ)
  let p : EuclideanSpace ℝ (Fin 3) := -(1 / 2 : ℝ) • e
  let q : EuclideanSpace ℝ (Fin 3) := (1 / 2 : ℝ) • e
  have hnorm_e : ‖e‖ = 1 := by
    simp [e]
  have hqp : q - p = e := by
    dsimp [q, p, e]
    rw [sub_eq_add_neg]
    rw [neg_smul, neg_neg]
    rw [← add_smul]
    norm_num
  have hdist : dist p q = 1 := by
    rw [dist_eq_norm_sub' p q, hqp, hnorm_e]
  have hp_norm : ‖p‖ = 1 / 2 := by
    dsimp [p]
    rw [norm_smul, hnorm_e]
    norm_num
  have hq_norm : ‖q‖ = 1 / 2 := by
    dsimp [q]
    rw [norm_smul, hnorm_e]
    norm_num
  have hp_ball : p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ) := by
    rw [Metric.mem_closedBall]
    rw [dist_eq_norm, sub_zero, hp_norm]
  have hq_ball : q ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ) := by
    rw [Metric.mem_closedBall]
    rw [dist_eq_norm, sub_zero, hq_norm]
  have hconv : Convex ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ)) :=
    convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ)
  have hseg : segment ℝ p q ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ) :=
    Convex.segment_subset hconv hp_ball hq_ball
  let W : Tube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3)) :=
    Tube.mk' (1 / 2 : NNReal) (x := p) (y := q) hdist
  let V : Tube δ (EuclideanSpace ℝ (Fin 3)) := W.rescale δ
  let y : EuclideanSpace ℝ (Fin 3) := (3 / 4 : ℝ) • e
  let B : Set (EuclideanSpace ℝ (Fin 3)) := Metric.closedBall y (1 / 16 : ℝ)
  have hδHalf : δ ≤ (1 / 2 : NNReal) := by
    exact le_trans hδ (by exact_mod_cast (show (1 / 8 : ℝ) ≤ (1 / 2 : ℝ) by norm_num))
  -- Clause 1: W ⊆ B₁
  have hW1 : W.carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro w hw
    dsimp [W] at hw
    change w ∈ ⋃ z ∈ segment ℝ p q, Metric.closedBall z ((1 / 2 : NNReal) : ℝ) at hw
    rw [Set.mem_iUnion₂] at hw
    rcases hw with ⟨z, hz, hwz⟩
    have hwz' : dist w z ≤ (1 / 2 : ℝ) := by
      have h := Metric.mem_closedBall.mp hwz
      norm_num at h ⊢
      exact h
    have hz_ball : z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ) := hseg hz
    have hz0 : dist z 0 ≤ 1 / 2 := Metric.mem_closedBall.mp hz_ball
    have hw0 : dist w 0 ≤ 1 := by
      calc
        dist w 0 ≤ dist w z + dist z 0 := dist_triangle w z 0
        _ ≤ (1 / 2 : ℝ) + (1 / 2 : ℝ) := by gcongr
        _ = 1 := by norm_num
    exact Metric.mem_closedBall.mpr hw0
  -- Clause 3 (and 2): V is the concentric smaller tube, so V ≤ W as convex bodies
  have hVW : V.toConvexSpaceBody ≤ W.toConvexSpaceBody := by
    calc
      V.toConvexSpaceBody = (W.rescale δ).toConvexSpaceBody := by rfl
      _ ≤ (W.rescale (1 / 2 : NNReal)).toConvexSpaceBody :=
        Tube.rescale_le_rescale_of_radius_le W hδHalf
      _ = W.toConvexSpaceBody := by
        apply ConvexSpaceBody.ext
        change (⋃ z ∈ segment ℝ p q, Metric.closedBall z ((1 / 2 : NNReal) : ℝ)) =
          (⋃ z ∈ segment ℝ p q, Metric.closedBall z ((1 / 2 : NNReal) : ℝ))
        rfl
  have hVW_carrier : V.carrier ⊆ W.carrier := by
    intro x hx
    change x ∈ W.toConvexSpaceBody
    exact hVW hx
  have hV1 : V.carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro x hx
    exact hW1 (hVW_carrier hx)
  -- Clause 4: 0 < volume V.carrier
  have hsubV : Metric.closedBall p (δ : ℝ) ⊆ V.carrier := by
    dsimp [V, W, Tube.rescale]
    change Metric.closedBall p (δ : ℝ) ⊆ ⋃ z ∈ segment ℝ p q, Metric.closedBall z (δ : ℝ)
    exact Set.subset_iUnion₂ (s := fun z _ => Metric.closedBall z (δ : ℝ)) p
      (left_mem_segment ℝ p q)
  have hposV : 0 < volume (Metric.closedBall p (δ : ℝ)) := by
    exact Metric.measure_closedBall_pos volume p (by exact_mod_cast hδ0)
  have hVpos : 0 < volume V.carrier :=
    lt_of_lt_of_le hposV (measure_mono hsubV)
  -- Clause 5: MeasurableSet B
  have hBmeas : MeasurableSet B := by
    change MeasurableSet (Metric.closedBall y (1 / 16 : ℝ))
    exact measurableSet_closedBall
  -- Clause 6: B ⊆ W.carrier
  have hyq : dist y q = 1 / 4 := by
    rw [dist_eq_norm_sub']
    dsimp [y, q]
    have hyq' : (1 / 2 : ℝ) • e - (3 / 4 : ℝ) • e = (-(1 / 4 : ℝ)) • e := by
      rw [← sub_smul]
      norm_num
    rw [hyq']
    rw [norm_smul, hnorm_e]
    norm_num
  have hB6 : B ⊆ W.carrier := by
    intro x hx
    have hxy : dist x y ≤ 1 / 16 := Metric.mem_closedBall.mp hx
    have hxq : dist x q ≤ (1 / 2 : ℝ) := by
      calc
        dist x q ≤ dist x y + dist y q := dist_triangle x y q
        _ = dist x y + 1 / 4 := by rw [hyq]
        _ ≤ 1 / 16 + 1 / 4 := by gcongr
        _ = 5 / 16 := by norm_num
        _ ≤ 1 / 2 := by norm_num
    change x ∈ (⋃ z ∈ segment ℝ p q, Metric.closedBall z ((1 / 2 : NNReal) : ℝ))
    rw [Set.mem_iUnion₂]
    refine ⟨q, right_mem_segment ℝ p q, ?_⟩
    exact Metric.mem_closedBall.mpr hxq
  -- Clause 7: Disjoint B V.carrier
  have hB7 : Disjoint B V.carrier := by
    rw [Set.disjoint_left]
    intro x hxB hxV
    have hxy : dist x y ≤ 1 / 16 := Metric.mem_closedBall.mp hxB
    change x ∈ (⋃ z ∈ segment ℝ p q, Metric.closedBall z (δ : ℝ)) at hxV
    rw [Set.mem_iUnion₂] at hxV
    rcases hxV with ⟨z, hz, hxz⟩
    rcases hz with ⟨a, b, ha, hb, hab, hz_eq⟩
    have hzeq : z = ((b - a) / 2 : ℝ) • e := by
      rw [hz_eq.symm]
      dsimp [p, q]
      rw [smul_smul, smul_smul, ← add_smul]
      ring_nf
    have hdist_y_ge : (1 / 4 : ℝ) ≤ dist y z := by
      have h04 : 0 ≤ (3 / 4 : ℝ) - (b - a) / 2 := by
        exact le_trans (by norm_num : (0 : ℝ) ≤ 1 / 4)
          (by nlinarith [ha, hb, hab])
      have h14 : (1 / 4 : ℝ) ≤ 3 / 4 - (b - a) / 2 := by nlinarith [ha, hb, hab]
      have hn : ‖y - z‖ = 3 / 4 - (b - a) / 2 := by
        dsimp [y]
        rw [hzeq]
        rw [← sub_smul]
        rw [norm_smul, hnorm_e]
        rw [Real.norm_eq_abs, abs_of_nonneg h04, mul_one]
      calc
        (1 / 4 : ℝ) ≤ 3 / 4 - (b - a) / 2 := h14
        _ = ‖y - z‖ := hn.symm
        _ = dist y z := by rw [dist_eq_norm]
    have hle2 : dist y z ≤ 3 / 16 := by
      have hdistyx : dist y x ≤ 1 / 16 := by
        rw [dist_comm]
        exact hxy
      calc
        dist y z ≤ dist y x + dist x z := dist_triangle y x z
        _ ≤ 1 / 16 + (δ : ℝ) := add_le_add hdistyx hxz
        _ ≤ 1 / 16 + (1 / 8 : ℝ) := by
          gcongr
          exact_mod_cast hδ
        _ = 3 / 16 := by norm_num
    have : (1 / 4 : ℝ) ≤ 3 / 16 := le_trans hdist_y_ge hle2
    norm_num at this
  -- Clause 8: 0 < volume B
  have hBpos : 0 < volume B := by
    change 0 < volume (Metric.closedBall y (1 / 16 : ℝ))
    exact Metric.measure_closedBall_pos volume y (by norm_num)
  -- Clause 9: volume W.carrier ≤ 4096 * volume B
  have hW1vol : volume W.carrier ≤ volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    measure_mono hW1
  have hBvol : volume B = ENNReal.ofReal ((1 / 16 : ℝ) ^ 3) *
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    change volume (Metric.closedBall y (1 / 16 : ℝ)) =
      ENNReal.ofReal ((1 / 16 : ℝ) ^ 3) * volume (Metric.ball 0 1)
    rw [MeasureTheory.Measure.addHaar_closedBall volume y (by norm_num : (0 : ℝ) ≤ 1 / 16)]
    congr 1
    rw [finrank_euclideanSpace_fin]
  have h4096 : (4096 : ENNReal) * ENNReal.ofReal ((1 / 16 : ℝ) ^ 3) = 1 := by
    have hnat : (4096 : ENNReal) = ENNReal.ofReal (4096 : ℝ) := by
      norm_num [ENNReal.ofReal_eq_coe_nnreal]
    rw [hnat]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4096)]
    norm_num
  have hvol : volume W.carrier ≤ 4096 * volume B := by
    calc
      volume W.carrier ≤ volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) := hW1vol
      _ = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
        rw [MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball]
      _ = 1 * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) := by rw [one_mul]
      _ = (4096 : ENNReal) * ENNReal.ofReal ((1 / 16 : ℝ) ^ 3) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
        rw [h4096]
      _ = (4096 : ENNReal) * volume B := by
        rw [hBvol]
        rw [mul_assoc]
  refine ⟨W, V, B, hW1, hV1, hVW, hVpos, hBmeas, hB6, hB7, hBpos, hvol⟩

/-- **(negative result) `Kakeya.ml1Boot.exists_twoScaleFinePair` is false: nothing forces the
retained middle shading to meet the fine shadings.**

The refuted statement is `Kakeya.ml1Boot.exists_twoScaleFinePair` at
`E = EuclideanSpace ℝ (Fin 3)` and `ι = κ = l = Unit`, with

* every hypothesis retained — none of them is vacuous here, and all of them are verified by the
  configuration below;
* of the conclusion, only `s' ⊆ s'₁ ∩ p_τ^{-1}(s'₂)`, the shading half of the fine shade clause,
  the refinement `Kakeya.ShadedBody.IsCRefinement`, and the nesting
  `Y'_i ⊆ Z'_2(p_τ(i))` retained.  The positivity of `λ_δ` and `N_τ`, the tube half of the fine
  shade clause, `fine_unif`, the density bracket, the fullness bound, the branching bracket, the
  Frostman clause and the multiplicity clause are all discarded, which makes this a refutation of
  a strictly weaker statement.  In particular the branching clause, which the earlier analysis in
  the docstring above used to force the fibres of `s'` to be nonempty, is *not* needed: the mass
  half of the refinement already forces `s'` to carry positive shading mass.

## The configuration

Fix `δ` small, and take `τ = θ = 1/2`.  Let `W` be the `(1/2)`-tube and `V` the concentric
`δ`-tube around the segment from `-e/2` to `e/2`, and let `B` be the ball of radius `1/16` about
`(3/4) e`, so that `B ⊆ W`, `B ∩ V = ∅` and `|W| ≤ 4096 |B|`
(`Kakeya.ml1Boot.exists_finePairCounterexampleGeometry`).  Then

* `s = t_τ = t_θ = {}`, `T` is `V` shaded by the whole of `V`, and `𝕋_τ`, `𝕋_θ` are both `W`;
* the first bundle has `s'₁ = t''₁ = {}`, `Z'₁ = T`, and `Z_{ρ,1}` the tube `W` shaded by the
  whole of `W`, with `λ_δ₁ = λ_τ₁ = N₁ = 1`;
* the second bundle has `s'₂ = t''₂ = {}`, `Z'₂` the tube `W` shaded by `B`, and `Z_{ρ,2}` the
  tube `W` shaded by the whole of `W`, with `λ_θ₂ = N₂ = 1` and `λ_τ₂ |W| = |B|`.

Every field of both bundles holds by `Kakeya.ml1Boot.isFactorOneScale_singleton`; the only
quantitative points are that `|W| ≤ 4096 |B|` forces `λ_τ₂ ≥ 4096⁻¹`, and that `δ` is taken small
enough that `δ ^ (2 ε₀) ≤ 4096⁻¹`, which is what makes both the fullness bound and the mass
clause of the second bundle's `fine_refinement` hold.

## Why the conclusion then fails

The mass half of `Kakeya.ShadedBody.IsCRefinement` reads
`δ ^ (2 ε₀) |V| ≤ ∑_{i ∈ s'} |Y'_i|`, and its left-hand side is positive, so some `i ∈ s'` has
`|Y'_i| > 0`.  But `s' ⊆ {}`, so that `i` is ``, and the two retained containments put
`Y'_{}` inside `(T ).shade ∩ (Z'_2 ).shade = V ∩ B = ∅`.

This is exactly the configuration described in the docstring of
`Kakeya.ml1Boot.exists_twoScaleFinePair`: `Z_{ρ,1}(k) = A ∪ B` with `A` the part meeting the fine
shadings — here all of `V` — and `B` disjoint from all of them, with `Z'_2(k) ⊆ B`.  No field of
`Kakeya.ml1Boot.IsFactorOneScale` asserts that the coarse shading is covered, even up to a
constant, by the fine shadings over its fibre, and that is the missing assertion.  For what the
repair would have to be, and why it is not applied here, see the docstring of
`Kakeya.ml1Boot.exists_twoScaleFinePair`. -/
theorem not_exists_twoScaleFinePair {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ¬ ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ τ θ : NNReal, δ ≤ τ → τ ≤ θ → θ ≤ 1 →
        ∀ {s tτ tθ : Finset Unit}
          (T : Unit → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
          (Tτ : Unit → Tube τ (EuclideanSpace ℝ (Fin 3))) (pτ : Unit → Unit)
          (Tθ : Unit → Tube θ (EuclideanSpace ℝ (Fin 3))) (pθ : Unit → Unit),
          s.Nonempty →
          (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
          (s : Set Unit).Pairwise
            (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
          IsParentFamily s (fun i => (T i).toTube) tτ Tτ pτ →
          (∀ k ∈ tτ, (Tτ k).carrier ⊆ Metric.closedBall 0 1) →
          (tτ : Set Unit).Pairwise
            (fun k k' => IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier) →
          IsParentFamily tτ Tτ tθ Tθ pθ →
          0 < ∑ i ∈ s, volume (T i).shade →
          ∀ {s'₁ t''₁ : Finset Unit}
            {Z'₁ : Unit → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
            {Zρ₁ : Unit → ShadedTube τ (EuclideanSpace ℝ (Fin 3))}
            {lamδ₁ lamτ₁ N₁ : NNReal}
            {s'₂ t''₂ t'q₂ : Finset Unit}
            {Z'₂ : Unit → ShadedTube τ (EuclideanSpace ℝ (Fin 3))}
            {Zρ₂ : Unit → ShadedTube θ (EuclideanSpace ℝ (Fin 3))}
            {lamτ₂ lamθ₂ N₂ : NNReal},
            0 < lamδ₁ → 0 < lamτ₁ → 0 < N₁ → 0 < lamτ₂ → 0 < lamθ₂ → 0 < N₂ →
            IsFactorOneScale δ ε₀ s T tτ Tτ pτ ({()} : Finset Unit) (fun _ => ())
              s'₁ t''₁ ({()} : Finset Unit) Z'₁ Zρ₁ lamδ₁ lamτ₁ N₁ →
            IsFactorOneScale δ ε₀ t''₁ Zρ₁ tθ Tθ pθ ({()} : Finset Unit) (fun _ => ())
              s'₂ t''₂ t'q₂ Z'₂ Zρ₂ lamτ₂ lamθ₂ N₂ →
            ∃ (s' : Finset Unit) (Y' : Unit → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
              s' ⊆ s'₁.filter (fun i => pτ i ∈ s'₂) ∧
              (∀ i ∈ s', (Y' i).shade ⊆ (T i).shade) ∧
              ShadedBody.IsCRefinement s' (fun i => (Y' i).toShadedBody) s
                (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε₀), by positivity⟩ ∧
              (∀ i ∈ s', (Y' i).shade ⊆ (Z'₂ (pτ i)).shade) := by
  intro hE
  -- STEP 1: extract δ
  have hc8 : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, δ ≤ (1 / 8 : NNReal) :=
    eventually_le_nhdsGT (by norm_num : (0 : NNReal) < 1 / 8)
  have hrp : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      (δ : ENNReal) ^ (2 * ε₀) ≤ (4096 : ENNReal)⁻¹ :=
    eventually_rpow_le (a := (4096 : ENNReal)⁻¹) (by simp) (by nlinarith [hε₀])
  have hmem : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, 0 < δ := by
    filter_upwards [self_mem_nhdsWithin] with δ h
    exact h
  rcases ((hE.and hc8).and (hrp.and hmem)).exists with ⟨δ, hA, hB⟩
  rcases hA with ⟨hP, hδ8⟩
  rcases hB with ⟨hSmall, hδ0⟩
  have hd18 : (1 / 8 : NNReal) ≤ 1 := by
    exact_mod_cast (show (1 / 8 : ℝ) ≤ 1 by norm_num)
  have hd18h : (1 / 8 : NNReal) ≤ (1 / 2 : NNReal) := by
    exact_mod_cast (show (1 / 8 : ℝ) ≤ (1 / 2 : ℝ) by norm_num)
  have hδ1 : δ ≤ 1 := hδ8.trans hd18
  have hδhalf : δ ≤ (1 / 2 : NNReal) := hδ8.trans hd18h
  let cv : NNReal := ⟨(δ : ℝ) ^ (2 * ε₀), by positivity⟩
  have hfull : (δ : ENNReal) ^ (2 * ε₀) ≤ (1 : ENNReal) := by
    exact hSmall.trans (by norm_num : (4096 : ENNReal)⁻¹ ≤ (1 : ENNReal))
  have hfullρ : ∀ σ : NNReal,
      (factorOneScale.C 1 σ : ENNReal)⁻¹ * (δ : ENNReal) ^ (2 * ε₀) ≤ (1 : ENNReal) :=
    fun σ => inv_coe_mul_le (one_le_factorOneScale_C 1 σ) hfull
  have hcpos : 0 < cv := by
    dsimp [cv]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hδ0) (2 * ε₀)
  -- STEP 2: the geometry
  obtain ⟨W, V, B, hW1, hV1, hVW, hVpos, hBmeas, hBW, hBV, hBpos, hWB⟩ :=
    exists_finePairCounterexampleGeometry hδ0 hδ8
  have hVmeas : MeasurableSet V.carrier := V.isCompact.isClosed.measurableSet
  have hWmeas : MeasurableSet W.carrier := W.isCompact.isClosed.measurableSet
  have hWtop : volume W.carrier ≠ ⊤ := W.isCompact.measure_ne_top
  have hBtop : volume B ≠ ⊤ := ne_top_of_le_ne_top hWtop (measure_mono hBW)
  have hWpos : 0 < volume W.carrier := lt_of_lt_of_le hBpos (measure_mono hBW)
  have hBne : volume B ≠ 0 := hBpos.ne'
  have hWne : volume W.carrier ≠ 0 := hWpos.ne'
  -- STEP 3: three shaded tubes
  obtain ⟨T₀, hT₀tube, hT₀shade⟩ :=
    exists_shadedTube_of_subset V hVmeas (subset_rfl : V.carrier ⊆ V.carrier)
  obtain ⟨Zρ, hZρtube, hZρshade⟩ :=
    exists_shadedTube_of_subset W hWmeas (subset_rfl : W.carrier ⊆ W.carrier)
  obtain ⟨Z₂, hZ₂tube, hZ₂shade⟩ := exists_shadedTube_of_subset W hBmeas hBW
  -- STEP 4: the middle density
  obtain ⟨lam, hlam0, hlameq⟩ :=
    exists_nnreal_mul_eq (a := volume B) (b := volume W.carrier) hBne hBtop hWne hWtop
  have hw2 : volume W.carrier ≤ (4096 : ENNReal) * ((lam : ENNReal) * volume W.carrier) := by
    simpa [hlameq.symm] using hWB
  have hw3 : volume W.carrier ≤ (4096 : ENNReal) * (lam : ENNReal) * volume W.carrier := by
    simpa [mul_assoc] using hw2
  have hOne : (1 : ENNReal) ≤ (4096 : ENNReal) * (lam : ENNReal) := by
    have hm : volume W.carrier * (volume W.carrier)⁻¹
        ≤ ((4096 : ENNReal) * (lam : ENNReal) * volume W.carrier) * (volume W.carrier)⁻¹ := by
      exact mul_le_mul_left hw3 (volume W.carrier)⁻¹
    simpa [mul_assoc, ENNReal.mul_inv_cancel hWne hWtop, mul_one] using hm
  have h4096 : (4096 : ENNReal) ≠ 0 := by norm_num
  have h4096t : (4096 : ENNReal) ≠ ⊤ := by norm_num
  have hI1 : (4096 : ENNReal)⁻¹ ≤ (lam : ENNReal) := by
    have hm : (4096 : ENNReal)⁻¹ * (1 : ENNReal)
        ≤ (4096 : ENNReal)⁻¹ * ((4096 : ENNReal) * (lam : ENNReal)) := by
      exact mul_le_mul_right hOne (4096 : ENNReal)⁻¹
    rw [mul_one] at hm
    calc
      (4096 : ENNReal)⁻¹ ≤ (4096 : ENNReal)⁻¹ * ((4096 : ENNReal) * (lam : ENNReal)) := hm
      _ = (lam : ENNReal) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel h4096 h4096t, one_mul]
  have hδlam : (δ : ENNReal) ^ (2 * ε₀) ≤ (lam : ENNReal) := hSmall.trans hI1
  have hle_two (x : ENNReal) : x ≤ (2 : ENNReal) * x := by
    calc
      x = (1 : ENNReal) * x := by simp
      _ ≤ (2 : ENNReal) * x := by
        exact mul_le_mul_of_nonneg_right (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal))
          (bot_le : (0 : ENNReal) ≤ x)
  -- STEP 5: the two bundles
  have hBundle1 : IsFactorOneScale δ ε₀ ({()} : Finset Unit) (fun _ : Unit => T₀)
      ({()} : Finset Unit) (fun _ : Unit => W) (fun _ : Unit => ())
      ({()} : Finset Unit) (fun _ : Unit => ())
      ({()} : Finset Unit) ({()} : Finset Unit) ({()} : Finset Unit)
      (fun _ : Unit => T₀) (fun _ : Unit => Zρ) (1 : NNReal) 1 1 := by
    refine isFactorOneScale_singleton (σ := δ) (ρ := (1 / 2 : NNReal)) (ε' := ε₀)
      hδ0 hδ1 hδ1 (by norm_num) hε₀
      (V₀ := T₀) (Z'₀ := T₀) (P₀ := W) (Zρ₀ := Zρ) (lamσ := 1) (lamρ := 1)
      rfl subset_rfl ?_ ?_ ?_ ?_ hZρtube ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hT₀shade]
      calc
        (δ : ENNReal) ^ (2 * ε₀) * volume V.carrier ≤ (1 : ENNReal) * volume V.carrier := by
          gcongr
        _ = volume V.carrier := by simp
    · rw [hT₀shade]
      simp [hT₀tube, one_mul]
    · rw [hT₀shade]
      simpa [hT₀tube, mul_assoc, one_mul, mul_one] using hle_two (volume V.carrier)
    · simpa [ENNReal.coe_one] using hfull
    · rw [hZρshade]
      simp [one_mul]
    · rw [hZρshade]
      simpa [hZρtube, mul_assoc, one_mul, mul_one] using hle_two (volume W.carrier)
    · simpa using hfullρ δ
    · rw [hT₀shade, hZρshade]
      exact (SetLike.coe_subset_coe.mpr hVW)
    · rw [hT₀shade]
      exact (hVpos.ne')
    · rw [hZρshade]
      exact (hWpos.ne')
  have hBundle2 : IsFactorOneScale δ ε₀ ({()} : Finset Unit) (fun _ : Unit => Zρ)
      ({()} : Finset Unit) (fun _ : Unit => W) (fun _ : Unit => ())
      ({()} : Finset Unit) (fun _ : Unit => ())
      ({()} : Finset Unit) ({()} : Finset Unit) ({()} : Finset Unit)
      (fun _ : Unit => Z₂) (fun _ : Unit => Zρ) lam 1 1 := by
    refine isFactorOneScale_singleton (σ := (1 / 2 : NNReal)) (ρ := (1 / 2 : NNReal)) (ε' := ε₀)
      hδ0 hδ1 (by norm_num : (1 / 2 : NNReal) ≤ 1) (by norm_num : (1 / 2 : NNReal) ≤ 1) hε₀
      (V₀ := Zρ) (Z'₀ := Z₂) (P₀ := W) (Zρ₀ := Zρ) (lamσ := lam) (lamρ := 1)
      ?_ ?_ ?_ ?_ ?_ ?_ hZρtube ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hZ₂tube, hZρtube]
    · rw [hZ₂shade, hZρshade]
      exact hBW
    · rw [hZ₂shade, hZρshade]
      calc
        (δ : ENNReal) ^ (2 * ε₀) * volume W.carrier ≤ (lam : ENNReal) * volume W.carrier := by
          gcongr
        _ = volume B := by rw [hlameq]
    · rw [hZ₂shade, hZρtube]
      exact (le_of_eq hlameq)
    · rw [hZ₂shade, hZρtube]
      calc
        volume B ≤ (2 : ENNReal) * volume B := hle_two (volume B)
        _ = (2 : ENNReal) * (lam : ENNReal) * volume W.carrier := by
          rw [← hlameq]
          rw [mul_assoc]
    · exact hδlam
    · rw [hZρshade]
      simp [one_mul]
    · rw [hZρshade]
      simpa [hZρtube, mul_assoc, one_mul, mul_one] using hle_two (volume W.carrier)
    · simpa using hfullρ (1 / 2 : NNReal)
    · rw [hZ₂shade, hZρshade]
      exact hBW
    · rw [hZ₂shade]
      exact hBne
    · rw [hZρshade]
      exact hWne
  -- STEP 6: instantiate the premise
  let T : Unit → ShadedTube δ (EuclideanSpace ℝ (Fin 3)) := fun _ => T₀
  let Tτ : Unit → Tube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3)) := fun _ => W
  let pτ : Unit → Unit := fun _ => ()
  let Tθ : Unit → Tube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3)) := fun _ => W
  let pθ : Unit → Unit := fun _ => ()
  have hSteps := hP (1 / 2 : NNReal) (1 / 2 : NNReal) hδhalf le_rfl
    (by norm_num : (1 / 2 : NNReal) ≤ 1)
    (s := ({()} : Finset Unit)) (tτ := ({()} : Finset Unit)) (tθ := ({()} : Finset Unit))
    T Tτ pτ Tθ pθ
  have hBall : ∀ i ∈ ({()} : Finset Unit), (T i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    simpa [T, hT₀tube] using hV1
  have hPair1 : (({()} : Finset Unit) : Set Unit).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) := by
    simp [T]
  have hPar1 : IsParentFamily ({()} : Finset Unit) (fun i : Unit => (T i).toTube)
      ({()} : Finset Unit) Tτ pτ := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp [pτ]
    · intro k hk k' hk' h
      change k ∈ ({()} : Finset Unit) at hk
      change k' ∈ ({()} : Finset Unit) at hk'
      exact (Finset.mem_singleton.mp hk).trans (Finset.mem_singleton.mp hk').symm
    · intro i hi
      simpa [T, Tτ, pτ, hT₀tube] using hVW
  have hBallT : ∀ k ∈ ({()} : Finset Unit), (Tτ k).carrier ⊆ Metric.closedBall 0 1 := by
    intro k hk
    simpa [Tτ] using hW1
  have hPair2 : (({()} : Finset Unit) : Set Unit).Pairwise
      (fun k k' => IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier) := by
    simp
  have hPar2 : IsParentFamily ({()} : Finset Unit) Tτ ({()} : Finset Unit) Tθ pθ := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp [pθ]
    · intro a ha b hb h
      change a ∈ ({()} : Finset Unit) at ha
      change b ∈ ({()} : Finset Unit) at hb
      exact (Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm
    · intro i hi
      simp [Tτ, Tθ, pθ]
  have hSumPos : 0 < ∑ j ∈ ({()} : Finset Unit), volume (T j).shade := by
    rw [Finset.sum_singleton]
    simpa [T, hT₀shade] using hVpos
  have hFam := hSteps (Finset.singleton_nonempty ()) hBall hPair1 hPar1 hBallT hPair2 hPar2
    hSumPos
    (s'₁ := ({()} : Finset Unit)) (t''₁ := ({()} : Finset Unit))
    (Z'₁ := fun _ => T₀) (Zρ₁ := fun _ => Zρ)
    (lamδ₁ := 1) (lamτ₁ := 1) (N₁ := 1)
    (s'₂ := ({()} : Finset Unit)) (t''₂ := ({()} : Finset Unit)) (t'q₂ := ({()} : Finset Unit))
    (Z'₂ := fun _ => Z₂) (Zρ₂ := fun _ => Zρ)
    (lamτ₂ := lam) (lamθ₂ := 1) (N₂ := 1)
    (one_pos) (one_pos) (one_pos) hlam0 (one_pos) (one_pos)
    hBundle1 hBundle2
  obtain ⟨s', Y', hSubY, hShade, hCref, hEnder⟩ := hFam
  -- STEP 7: the contradiction
  have hT₀V : 0 < volume T₀.shade := by
    rw [hT₀shade]
    exact hVpos
  have hLHSpos : 0 < (cv : ENNReal) * ∑ i ∈ ({()} : Finset Unit),
      volume ((T i).toShadedBody).shade := by
    rw [Finset.sum_singleton]
    simpa [T] using
      ENNReal.mul_pos (ENNReal.coe_pos.mpr hcpos).ne' hT₀V.ne'
  have hsum0 : ∑ i ∈ s', volume (Y' i).shade = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hb : (Y' i).shade ⊆ B := by
      simpa [hZ₂shade] using (hEnder i hi)
    have hca : (Y' i).shade ⊆ V.carrier := by
      simpa [T, hT₀shade] using (hShade i hi)
    have hInter : (Y' i).shade ⊆ B ∩ V.carrier := Set.subset_inter hb hca
    have hD : B ∩ V.carrier = ∅ := (Set.disjoint_iff_inter_eq_empty.mp hBV)
    have heqw : (Y' i).shade = ∅ := by
      rw [hD] at hInter
      exact Set.subset_empty_iff.mp hInter
    rw [heqw]
    simp
  have hle : (cv : ENNReal) * ∑ i ∈ ({()} : Finset Unit),
      volume ((T i).toShadedBody).shade ≤ 0 := by
    calc
      (cv : ENNReal) * ∑ i ∈ ({()} : Finset Unit), volume ((T i).toShadedBody).shade
          ≤ ∑ i ∈ s', volume ((Y' i).toShadedBody).shade := hCref.2
      _ = 0 := by
        simpa using hsum0
  exact (lt_irrefl (0 : ENNReal)) (lt_of_lt_of_le hLHSpos hle)

/-- **Assembling `Kakeya.ml1Boot.IsFactorTwoScales` from two one-scale bundles and a fine
pair.**

This is the whole content of the positive-mass branch of the two-scale factoring step (blueprint
`lem:ml1bootFactorTwoScales`) except the existential plumbing: given the data that the two-scale
factor pair *would* produce — two `Kakeya.ml1Boot.IsFactorOneScale`
bundles at a common auxiliary exponent `ε₀`, and a fine pair `(s', Y')` over the pull-back
`s'₁ ∩ p_τ^{-1}(s'₂)` — every field of `Kakeya.ml1Boot.IsFactorTwoScales` follows, at the
instantiation `t''τ := t''₁`, `t'τ := s'₂`, `Y_τ := Z'₂`, `t'θ := t''₂`, `Y_θ := Z_{ρ,2}`.

**Nothing supplies that data.**  `exists_twoScaleFactorPair` and
`exists_factorTwoScales_of_sum_shade_pos` are not declarations, and the fine pair is refuted
(`Kakeya.ml1Boot.not_exists_twoScaleFinePair`): `IsFactorOneScale` has a `contain` field but no
converse covering clause, so the two applications may pick disjoint fine shadings.  This lemma is
therefore the assembly step alone, correct and unused; the repair it waits on is an
induced-shading field on `Kakeya.ml1Boot.IsFactorOneScale`.  See blueprint
`note:ml1bootTwoScaleRouteRefuted` and `note:ml1bootCaseTwoConstructionLayerEmpty`.

The single hypothesis
`6 ε₀ ≤ ε'` covers every exponent alignment: the largest demand is the triple loss
`δ ^ (-6 ε₀)` of `Kakeya.ml1Boot.twoScaleProduct`, and `δ ≤ 1` makes all the others weaker.

The positive-mass hypothesis is used only to know that the fine index set, hence the
intermediate middle index set `t''₁`, is nonempty, which is what
`Kakeya.ml1Boot.le_fullness_of_dens_lower` needs for the two composed fullness fields. -/
theorem isFactorTwoScales_of_factorPair [Nontrivial E] {δ τ θ : NNReal} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (hδτ : δ ≤ τ) {ε' ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀ε : 6 * ε₀ ≤ ε')
    {ι κ l : Type*} [DecidableEq κ] [DecidableEq l]
    {s : Finset ι} {tτ : Finset κ} {tθ : Finset l}
    (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ)
    (Tθ : l → Tube θ E) (pθ : κ → l)
    (hparθ : IsParentFamily tτ Tτ tθ Tθ pθ)
    (hmass : 0 < ∑ i ∈ s, volume (T i).shade)
    {s'₁ : Finset ι} {t''₁ : Finset κ} {Z'₁ : ι → ShadedTube δ E} {Zρ₁ : κ → ShadedTube τ E}
    {lamδ₁ lamτ₁ N₁ : NNReal}
    {s'₂ : Finset κ} {t''₂ : Finset l} {t'q₂ : Finset Unit}
    {Z'₂ : κ → ShadedTube τ E} {Zρ₂ : l → ShadedTube θ E} {lamτ₂ lamθ₂ N₂ : NNReal}
    {s' : Finset ι} {Y' : ι → ShadedTube δ E} {lamδ Nτ : NNReal}
    (h1 : IsFactorOneScale δ ε₀ s T tτ Tτ pτ ({()} : Finset Unit) (fun _ => ())
      s'₁ t''₁ ({()} : Finset Unit) Z'₁ Zρ₁ lamδ₁ lamτ₁ N₁)
    (h2 : IsFactorOneScale δ ε₀ t''₁ Zρ₁ tθ Tθ pθ ({()} : Finset Unit) (fun _ => ())
      s'₂ t''₂ t'q₂ Z'₂ Zρ₂ lamτ₂ lamθ₂ N₂)
    (hsub : s' ⊆ s'₁.filter (fun i => pτ i ∈ s'₂))
    (hshade : ∀ i ∈ s', (Y' i).toTube = (T i).toTube ∧ (Y' i).shade ⊆ (T i).shade)
    (href : ShadedBody.IsCRefinement s' (fun i => (Y' i).toShadedBody) s
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε₀), by positivity⟩)
    (hunif : Nonempty (ShadedTube.ShadedUniformTubeSet s' Y' (Tube.ssfGridLen δ)
      (uniformize.C 3)))
    (hdens : ∀ i ∈ s', (lamδ : ENNReal) * volume (T i).carrier ≤ volume (Y' i).shade ∧
      volume (Y' i).shade ≤ 2 * (lamδ : ENNReal) * volume (T i).carrier)
    (hfull : (δ : ENNReal) ^ (2 * ε₀) * ShadedBody.fullness s (fun i => (T i).toShadedBody)
      ≤ (lamδ : ENNReal))
    (hbr : ∀ k ∈ s'₂, (Nτ : ENNReal) ≤ ((fibre s' pτ k).card : ENNReal) ∧
      ((fibre s' pτ k).card : ENNReal) ≤ 2 * (Nτ : ENNReal))
    (hcont : ∀ i ∈ s', (Y' i).shade ⊆ (Z'₂ (pτ i)).shade)
    (hfro : ∀ k ∈ s'₂,
      frostmanConstIn (fibre s' pτ k) (fun i => (T i).toConvexSpaceBody)
          (Tτ k).toConvexSpaceBody
        ≤ (δ : ENNReal) ^ (-2 * ε₀) * frostmanConstIn (fibre s pτ k)
            (fun i => (T i).toConvexSpaceBody) (Tτ k).toConvexSpaceBody)
    (hmultfine : ∀ k ∈ s'₂,
      ShadedBody.multiplicity (fibre s'₁ pτ k) (fun i => (Z'₁ i).toShadedBody)
        ≤ (δ : ENNReal) ^ (-2 * ε₀)
          * ShadedBody.multiplicity (fibre s' pτ k) (fun i => (Y' i).toShadedBody)) :
    IsFactorTwoScales ε' s T tτ Tτ pτ tθ Tθ pθ s' t''₁ s'₂ t''₂ Y' Z'₂ Zρ₂
      lamδ lamτ₂ lamθ₂ Nτ N₂ := by
  classical
  have hmem : ∀ i ∈ s', i ∈ s'₁ ∧ pτ i ∈ s'₂ := fun i hi => Finset.mem_filter.mp (hsub hi)
  have hs'sub : s' ⊆ s := fun i hi => h1.fine_subset (hmem i hi).1
  have hs2sub : s'₂ ⊆ t''₁ := h2.fine_subset
  have ht1sub : t''₁ ⊆ tτ := h1.coarse_subset
  have hτ0 : 0 < τ := lt_of_lt_of_le hδ0 hδτ
  have hδR0 : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hposN : 0 < (⟨(δ : ℝ) ^ (2 * ε₀), by positivity⟩ : NNReal) := by
    exact_mod_cast (Real.rpow_pos_of_pos hδR0 (2 * ε₀))
  have hs'ne : s'.Nonempty :=
    nonempty_of_isCRefinement_of_sum_shade_pos
      (c := ⟨(δ : ℝ) ^ (2 * ε₀), by positivity⟩) hposN href hmass
  have ht1ne : t''₁.Nonempty := by
    rcases hs'ne with ⟨i, hi⟩
    exact ⟨pτ i, hs2sub ((hmem i hi).2)⟩
  have hcar : ∀ k ∈ t''₁, volume (Zρ₁ k).carrier = volume (Tτ k).carrier := by
    intro k hk
    simpa using congrArg (fun T : Tube τ E => volume T.carrier) (h1.coarse_tube k hk)
  have hmidfull : (lamτ₁ : ENNReal) ≤
      (fullness t''₁ (fun k => (Zρ₁ k).toShadedBody) : ENNReal) := by
    exact le_fullness_of_dens_lower hτ0 ht1ne Zρ₁ (fun k hk => by
      simpa [hcar k hk] using (h1.coarse_dens k hk).1)
  have hmid₂ : (factorOneScale.C t''₁.card τ : ENNReal)⁻¹ * (δ : ENNReal) ^ (2 * ε₀) *
      fullness t''₁ (fun k => (Zρ₁ k).toShadedBody) ≤ (lamτ₂ : ENNReal) := by
    rw [mul_assoc]
    exact inv_coe_mul_le (one_le_factorOneScale_C _ _) h2.fine_fullness
  exact { fine_subset := hs'sub
          fine_shade := hshade
          fine_refinement := isCRefinement_weaken_exponent hδ0 hδ1
            (by linarith : 2 * ε₀ ≤ 2 * ε') href
          fine_unif := hunif
          fine_essDistinct := h1.fine_essDistinct.mono
            (Finset.coe_subset.mpr (fun i hi => (hmem i hi).1))
          fine_dens := hdens
          fine_fullness := by
            have hpow : (δ : ENNReal) ^ (2 * ε') ≤ (δ : ENNReal) ^ (2 * ε₀) :=
              rpow_mono_exponent hδ0 hδ1 (by linarith : 2 * ε₀ ≤ 2 * ε')
            exact le_trans (mul_le_mul_of_nonneg_right hpow zero_le) hfull
          midAmbient_subset := h1.coarse_subset
          mid_subset' := h2.fine_subset
          mid_tube := fun k hk => ((h2.fine_shade k hk).1).trans (h1.coarse_tube k (hs2sub hk))
          mid_unif := h2.fine_unif
          mid_essDistinct := h1.coarse_essDistinct.mono (Finset.coe_subset.mpr hs2sub)
          mid_dens := fun k hk => by simpa [hcar k (hs2sub hk)] using h2.fine_dens k hk
          mid_fullness := by
            rw [coe_factorTwoScales_C]
            exact twoScaleFullnessOut (one_le_factorOneScale_C _ _) (one_le_factorOneScale_C _ _)
              hδ0 hδ1 (a := 2 * ε₀)
              (by positivity) (by linarith) h1.coarse_fullness hmidfull hmid₂
          coarse_subset := h2.coarse_subset
          coarse_tube := h2.coarse_tube
          coarse_unif := h2.coarse_unif
          coarse_essDistinct := h2.coarse_essDistinct
          coarse_dens := h2.coarse_dens
          coarse_fullness := by
            rw [coe_factorTwoScales_C]
            exact twoScaleFullnessOut (one_le_factorOneScale_C _ _) (one_le_factorOneScale_C _ _)
              hδ0 hδ1 (by positivity) (by linarith)
              h1.coarse_fullness hmidfull h2.coarse_fullness
          branch_fine_mapsTo := fun i hi => (hmem i hi).2
          branch_mid_mapsTo := h2.branch_mapsTo
          branch_fine_card := hbr
          branch_mid_card := fun l' hl' => ⟨(h2.branch_card l' hl').1, (h2.branch_card l' hl').2.1⟩
          contain_fine := fun i hi _ => hcont i hi
          contain_mid := h2.contain
          frostman_fine := by
            intro k hk
            have hpow : (δ : ENNReal) ^ (-2 * ε₀) ≤ (δ : ENNReal) ^ (-ε') :=
              rpow_mono_exponent hδ0 hδ1 (by linarith : -ε' ≤ -2 * ε₀)
            exact le_trans (hfro k hk) (mul_le_mul_of_nonneg_right hpow zero_le)
          frostman_mid := by
            intro l' hl'
            apply frostmanConstIn_fibre_congr hs2sub h1.coarse_tube
              (p := pθ) (l' := l') (K := (Tθ l').toConvexSpaceBody)
              (x := (δ : ENNReal) ^ (-ε'))
            have hK : ∀ k ∈ t''₁, pθ k = l' → (Zρ₁ k).toConvexSpaceBody ≤
                (Tθ l').toConvexSpaceBody := by
              intro k hk hpl
              have hZ : (Zρ₁ k).toConvexSpaceBody = (Tτ k).toConvexSpaceBody := by
                simpa using congrArg (fun T : Tube τ E => T.toConvexSpaceBody) (h1.coarse_tube k hk)
              rw [hZ, ← hpl]
              exact hparθ.le_parent k (ht1sub hk)
            have hprotp : (δ : ENNReal) ^ (-2 * ε₀) ≤ (δ : ENNReal) ^ (-ε') :=
              rpow_mono_exponent hδ0 hδ1 (by linarith : -ε' ≤ -2 * ε₀)
            exact le_trans (h2.frostman l' hl' ((Tθ l').toConvexSpaceBody) hK)
              (mul_le_mul_of_nonneg_right hprotp zero_le)
          product := by
            intro k hk l' hl'
            rw [coe_factorTwoScales_C]
            exact twoScaleProduct (one_le_factorOneScale_C _ _) (one_le_factorOneScale_C _ _)
              hδ0 hδ1
              (by linarith : -ε' ≤ 3 * (-2 * ε₀))
              (h1.product k (hs2sub hk)) (h2.product l' hl') (hmultfine k hk)
          midFibreUnif := h2.fibreUnif }

/-! ### Selecting an essentially distinct parent family -/

/-- **A finite constant is eventually dominated by a negative power of the scale.** -/
theorem eventually_finite_const_le_rpow_neg {c : ENNReal} (hc : c ≠ ⊤) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, c ≤ (δ : ENNReal) ^ (-a) := by
  have hinv : c⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hc
  filter_upwards [eventually_rpow_le hinv ha] with δ hδ
  have hcc : c * c⁻¹ ≤ 1 := by
    rcases eq_or_ne c 0 with rfl | hc0
    · simp
    · rw [ENNReal.mul_inv_cancel hc0 hc]
  rw [ENNReal.rpow_neg]
  refine ENNReal.le_inv_iff_mul_le.mpr ?_
  calc c * (δ : ENNReal) ^ a ≤ c * c⁻¹ := by gcongr
    _ ≤ 1 := hcc

/-- **Weighted greedy selection against a bounded-degree symmetric relation, for `ENNReal`
weights.**

Let `Rel` be symmetric and let every vertex of `t` have at most `Co` `Rel`-neighbours inside `t`.
Then `t` has an `Rel`-independent subset carrying all but a factor `Co + 1` of any weight.

Greedy in decreasing weight: take a heaviest `k₀`, delete it together with its neighbours — at most
`Co + 1` vertices, each of weight at most `wt k₀` — and recurse.  The deleted block is charged to
`k₀`, which is retained.

**This is the `ENNReal`-valued companion of `Kakeya.IsEDUpToMult.exists_pairwise_subset_with_weight`
(`Kakeya/Tube/EDUpToMult.lean`), which is the same statement for `ℝ`-valued weights and is
proved.**  Only the weight type differs, and it differs load-bearingly: the weights the Section 8
selections carry are shade volumes and cardinalities, which live in `ENNReal`, and the `ℝ` version
needs a finiteness that a caller holding `volume (Y i)` does not have on hand.

The degree bound is phrased over *subsets* rather than as the cardinality of a filter, which keeps
it free of any decidability instance and so lets a caller supply it from a differently-elaborated
form without an instance mismatch. -/
theorem exists_pairwise_notRel_weighted {κ : Type*} [DecidableEq κ] (Rel : κ → κ → Prop)
    (hsymm : ∀ a b, Rel a b → Rel b a) (wt : κ → ENNReal) (Co : ℕ) (t : Finset κ)
    (hbound : ∀ k' ∈ t, ∀ u : Finset κ, u ⊆ t → (∀ k ∈ u, Rel k k') → u.card ≤ Co) :
    ∃ t' ⊆ t, (t' : Set κ).Pairwise (fun a b => ¬ Rel a b) ∧
      ∑ k ∈ t, wt k ≤ ((Co : ENNReal) + 1) * ∑ k ∈ t', wt k := by
  classical
  revert hbound
  induction t using Finset.strongInduction with
  | _ t ih =>
  intro hbound
  rcases Finset.eq_empty_or_nonempty t with rfl | hne
  · exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
  obtain ⟨k₀, hk₀t, hk₀max⟩ := t.exists_max_image wt hne
  set B : Finset κ := insert k₀ (t.filter (fun k => Rel k k₀)) with hB
  have hBt : B ⊆ t := by
    rw [hB]
    exact Finset.insert_subset hk₀t (Finset.filter_subset _ _)
  have hk₀B : k₀ ∈ B := by
    rw [hB]
    exact Finset.mem_insert_self _ _
  have hBcard : B.card ≤ Co + 1 := by
    refine le_trans (by rw [hB]; exact Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
    refine hbound k₀ hk₀t (t.filter (fun k => Rel k k₀)) (Finset.filter_subset _ _) ?_
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  have hsub : t \ B ⊂ t := by
    refine (Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr ⟨k₀, hk₀t, ?_⟩
    simp only [Finset.mem_sdiff, not_and, not_not]
    exact fun _ => hk₀B
  obtain ⟨t₁', ht₁'sub, ht₁'pw, ht₁'wt⟩ :=
    ih (t \ B) hsub (fun k' hk' u hu hRel =>
      hbound k' (Finset.sdiff_subset hk') u (hu.trans Finset.sdiff_subset) hRel)
  have hk₀notin : k₀ ∉ t \ B := by
    simp only [Finset.mem_sdiff, not_and, not_not]
    exact fun _ => hk₀B
  have hne₀ : ∀ a ∈ t₁', ¬ Rel a k₀ := by
    intro a ha hRel
    have hat : a ∈ t \ B := ht₁'sub ha
    rw [Finset.mem_sdiff] at hat
    refine hat.2 ?_
    rw [hB]
    exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hat.1, hRel⟩)
  refine ⟨insert k₀ t₁', Finset.insert_subset hk₀t (ht₁'sub.trans Finset.sdiff_subset), ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact fun hR => hne₀ b hb (hsymm _ _ hR)
    · rcases hb with rfl | hb
      · exact hne₀ a ha
      · exact ht₁'pw ha hb hab
  · have hsplit : ∑ k ∈ t, wt k = ∑ k ∈ B, wt k + ∑ k ∈ t \ B, wt k := by
      rw [add_comm]
      exact (Finset.sum_sdiff hBt).symm
    have hBle : ∑ k ∈ B, wt k ≤ ((Co : ENNReal) + 1) * wt k₀ := by
      calc ∑ k ∈ B, wt k ≤ ∑ _k ∈ B, wt k₀ :=
            Finset.sum_le_sum fun k hk => hk₀max k (hBt hk)
        _ = (B.card : ENNReal) * wt k₀ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((Co : ENNReal) + 1) * wt k₀ := by
            gcongr
            calc (B.card : ENNReal) ≤ ((Co + 1 : ℕ) : ENNReal) := Nat.cast_le.mpr hBcard
              _ = (Co : ENNReal) + 1 := by push_cast; ring
    have hins : ∑ k ∈ insert k₀ t₁', wt k = wt k₀ + ∑ k ∈ t₁', wt k :=
      Finset.sum_insert (fun h => hk₀notin (ht₁'sub h))
    rw [hsplit, hins, mul_add]
    exact add_le_add hBle ht₁'wt

/-- **(GWZ Lemma 8.1) An essentially distinct parent family** (blueprint
`lem:ml1bootEssDistinctParents`).

A parent family `(t, 𝕍_ρ, p)` for `(s, 𝕍)` admits a subfamily whose parents are pairwise
essentially distinct, retaining a `δ ^ ε'` share of any caller-supplied weight `w`, with the
fibrewise Frostman constants transported.

## The hypothesis, and why it is `Kakeya.IsEDUpToMult` and not `Tube.HasBoundedOverlap`

It could not be
proved, and not for want of effort: the greedy selection needs, for a discarded parent `k` charged
to a retained `k'`, a bound on how many parents can be charged to one `k'`, and
`Tube.HasBoundedOverlap` is *leaf-mediated* — it counts parents admitting a leaf `V i` with
`V i ≤ V_ρ k` **and** `V i ≤ W` — while essential distinctness is a statement about the parent
*bodies*. There is no implication from the second to the first: all `ρ`-tubes have the same volume,
so two translates overlapping in `0.9` of it fail to be essentially distinct, and putting every leaf
of `k'` inside `V_ρ k' \ V_ρ k` leaves no leaf in the common part.

What the greedy consumes is the body-level bound, and the development already has the vocabulary
for it: `Kakeya.IsEDUpToMult t (fun k => (Vρ k).carrier) Co` — at most `Co` members of the family
fail to be essentially distinct from any given member.  Against that hypothesis the selection is
`Kakeya.ml1Boot.exists_pairwise_notRel_weighted` and the retention is exact.

## Essential distinctness is not what Section 3 actually needs

The reason to manufacture strict essential distinctness of the parents at all is that the coarse
factor feeds its family to `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale`, whose hypothesis
is strict `Pairwise IsEssentiallyDistinct`, reaching it through
`Kakeya.ml1Boot.IsFactorTwoScales.coarse_essDistinct` and
`Kakeya.ml1Boot.coarse_input_of_isFactorTwoScales` — the only place in the development where
parent-level essential distinctness is consumed rather than threaded.  That hypothesis is a
convenience wrapper: the engine underneath, `Kakeya.FrostmanEstimate.ball2_version_edUpToMult`,
runs on `Kakeya.IsEDUpToMult` with the multiplicity allowed to grow subpolynomially, and
`Kakeya.KatzTaoEstimate.multiplicity_bound` asks for no distinctness at all.

## What is exact and what is lossy

* `s'` is a *filter* of `s` along `p`, so restricting to the retained parents deletes only **whole**
  fibres and `fibre s' p k = fibre s p k` on the nose for every `k ∈ t'`.  The fibrewise Frostman
  clause therefore holds with equality, the stated `δ ^ (-ε')` being pure slack.  The leaves of a
  discarded parent are never reassigned, and cannot be: two parents that fail to be essentially
  distinct have large intersection but not containment, so a leaf of one need not lie in the other.
* the retention is at *one* weight.  No essentially distinct selection retains a constant share of
  two incomparable weights — two parents failing distinctness and carrying `(|s[k]|, mass)` equal to
  `(M, 1/M)` and `(1, 1)` show it — so the counting weight `w = 1` and the shade mass
  `w i = volume (V i).shade` are genuine alternatives, and `w` is a parameter for that reason.
  `Kakeya.ml1Boot.essDistinct_parentFamily_isCRefinement` is the shade-mass reading.
* the retention constant `Co + 1` is fixed before the scale, so `δ ^ ε'` absorbs it. -/
theorem exists_essDistinct_parentFamily_of_edUpToMult {ε' : ℝ} (hε' : 0 < ε') (Co : ℕ) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ σ ρ : NNReal, δ ≤ σ → σ ≤ ρ → ρ ≤ 1 →
      ∀ {ι κ : Type*} [DecidableEq κ] {s : Finset ι} {t : Finset κ}
        (V : ι → ShadedTube σ E) (Vρ : κ → Tube ρ E) (p : ι → κ) (w : ι → ENNReal),
        IsParentFamily s (fun i => (V i).toTube) t Vρ p →
        IsEDUpToMult t (fun k => (Vρ k).carrier) Co →
        ∃ s' ⊆ s, ∃ t' ⊆ t,
          IsParentFamily s' (fun i => (V i).toTube) t' Vρ p ∧
          (t' : Set κ).Pairwise
            (fun k l => IsEssentiallyDistinct (Vρ k).carrier (Vρ l).carrier) ∧
          (δ : ENNReal) ^ ε' * (∑ i ∈ s, w i) ≤ ∑ i ∈ s', w i ∧
          ∀ k ∈ t', ∀ K : ConvexSpaceBody E,
            (∀ i ∈ fibre s p k, (V i).toConvexSpaceBody ≤ K) →
            frostmanConstIn (fibre s' p k) (fun i => (V i).toConvexSpaceBody) K
              ≤ (δ : ENNReal) ^ (-ε')
                * frostmanConstIn (fibre s p k) (fun i => (V i).toConvexSpaceBody) K := by
  filter_upwards [eventually_finite_const_le_rpow_neg (c := ((Co : ENNReal) + 1))
      (by simp) hε', eventually_le_nhdsGT (c := 1) zero_lt_one, self_mem_nhdsWithin]
    with δ habs hδ1 hδ0
  intro σ ρ _hδσ _hσρ _hρ1 ι κ _inst s t V Vρ p w hparent hover
  have hδpos : (0 : NNReal) < δ := hδ0
  have hδne : (δ : ENNReal) ≠ 0 := by simpa using (ne_of_gt hδpos)
  have hδtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hone : (1 : ENNReal) ≤ (δ : ENNReal) ^ (-ε') := by
    rw [ENNReal.rpow_neg]
    refine ENNReal.le_inv_iff_mul_le.mpr ?_
    rw [one_mul]
    calc (δ : ENNReal) ^ ε' ≤ (1 : ENNReal) ^ ε' := by
          gcongr
          exact_mod_cast hδ1
      _ = 1 := ENNReal.one_rpow _
  obtain ⟨t', ht'sub, ht'pw, ht'wt⟩ :=
    exists_pairwise_notRel_weighted
      (Rel := fun k l => ¬ IsEssentiallyDistinct (Vρ k).carrier (Vρ l).carrier)
      (fun a b hab hba => hab (isEssentiallyDistinct_symm hba))
      (wt := fun k => ∑ i ∈ fibre s p k, w i) Co t
      (fun k' hk' u hu hRel => by
        refine le_trans (Finset.card_le_card ?_) (hover k' hk')
        intro k hk
        simp only [notEssDistinctSet, Finset.mem_filter]
        exact ⟨hu hk, hRel k hk⟩)
  set s' : Finset ι := {i ∈ s | p i ∈ t'} with hs'
  have hmaps : ∀ i ∈ s', p i ∈ t' := fun i hi => (Finset.mem_filter.mp hi).2
  have hfibre : ∀ k ∈ t', Finset.filter (fun i => p i = k) s' = fibre s p k := by
    intro k hk
    ext i
    simp only [hs', fibre, Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, h.2 ▸ hk⟩, h.2⟩
  refine ⟨s', Finset.filter_subset _ _, t', ht'sub, ?_, ?_, ?_, ?_⟩
  · exact
      { mapsTo := hmaps
        injOn := fun a ha b hb hab => hparent.injOn (ht'sub ha) (ht'sub hb) hab
        le_parent := fun i hi => hparent.le_parent i (Finset.mem_filter.mp hi).1 }
  · intro a ha b hb hab
    exact not_not.mp (ht'pw ha hb hab)
  · have hsum_t : ∑ k ∈ t, (∑ i ∈ fibre s p k, w i) = ∑ i ∈ s, w i :=
      Finset.sum_fiberwise_of_maps_to (fun i hi => hparent.mapsTo i hi) w
    have hsum_t' : ∑ k ∈ t', (∑ i ∈ fibre s p k, w i) = ∑ i ∈ s', w i := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := s') (t := t') (g := p) hmaps w]
      exact Finset.sum_congr rfl fun k hk => by rw [hfibre k hk]
    rw [hsum_t, hsum_t'] at ht'wt
    calc (δ : ENNReal) ^ ε' * ∑ i ∈ s, w i
        ≤ (δ : ENNReal) ^ ε' * (((Co : ENNReal) + 1) * ∑ i ∈ s', w i) := by gcongr
      _ ≤ (δ : ENNReal) ^ ε' * ((δ : ENNReal) ^ (-ε') * ∑ i ∈ s', w i) := by gcongr
      _ = ((δ : ENNReal) ^ ε' * (δ : ENNReal) ^ (-ε')) * ∑ i ∈ s', w i := by ring
      _ = ∑ i ∈ s', w i := by
          rw [← ENNReal.rpow_add _ _ hδne hδtop]
          simp
  · intro k hk K _hKside
    have heq : fibre s' p k = fibre s p k := hfibre k hk
    rw [heq]
    calc frostmanConstIn (fibre s p k) (fun i => (V i).toConvexSpaceBody) K
        = 1 * frostmanConstIn (fibre s p k) (fun i => (V i).toConvexSpaceBody) K :=
          (one_mul _).symm
      _ ≤ (δ : ENNReal) ^ (-ε')
          * frostmanConstIn (fibre s p k) (fun i => (V i).toConvexSpaceBody) K := by gcongr

/-- The joint-cleaning cardinality loss is monotone in the number of jointly cleaned partitions. -/
lemma relativePlankJointLoss_mono (n : ℕ) {M M' : ℕ} (hMM' : M ≤ M') :
    relativePlankJointLoss n M ≤ relativePlankJointLoss n M' := by
  unfold relativePlankJointLoss relativePlankRounds
  exact Nat.mul_le_mul_left 2
    (Nat.pow_le_pow_right (one_le_relativePlankBucket n) (by omega))

/-- The joint-cleaning class-band ratio is monotone in the number of jointly cleaned partitions. -/
lemma relativePlankBandRatio_mono (n : ℕ) {M M' : ℕ} (hMM' : M ≤ M') :
    relativePlankBandRatio n M ≤ relativePlankBandRatio n M' := by
  unfold relativePlankBandRatio relativePlankThreshold relativePlankRounds
  exact Nat.mul_le_mul_left 2
    (Nat.mul_le_mul (Nat.mul_le_mul_left 4 (by omega))
      (Nat.pow_le_pow_right (one_le_relativePlankBucket n) (by omega)))

/-- The joint-cleaning cardinality loss is absorbed by the total loss. -/
lemma relativePlankJointLoss_le_relativePlankTotalLoss (n M : ℕ) :
    relativePlankJointLoss n M ≤ relativePlankTotalLoss n M := by
  unfold relativePlankTotalLoss
  exact Nat.le_mul_of_pos_right (relativePlankJointLoss n M)
    (Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_relativePlankShadeLoss n M))

/-- The terminal shade-only fullness loss is absorbed by the total loss. -/
lemma relativePlankShadeLoss_le_relativePlankTotalLoss (n M : ℕ) :
    relativePlankShadeLoss n M ≤ relativePlankTotalLoss n M := by
  unfold relativePlankTotalLoss
  exact Nat.le_mul_of_pos_left (relativePlankShadeLoss n M)
    (Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_relativePlankJointLoss n M))

-- `tτ`/`pτ` stay in the statement as the consumer-facing interface (item 40.25), but no
-- longer occur in the type once the fibrewise conjunct is gone; the linter flags them.
set_option linter.unusedVariables false in
/-- **The band-preserving shaded uniformization tool — Stage I, band-at-INPUT form**
(blueprint item 40.13; the corrected statement from the item's `informal.proof`).

The originally recorded 9-conjunct interface is REFUTED as stated (FINDING 1, mass
concentration); the input-band hypothesis `hband` repairs it: `dens`@T and the output band are
FREE with `lam' := lam₀`, `card` closes via joint-pigeonhole count retention × uniformization
count retention, `refinement`@Y' via fullness'-retention + band.  The fibrewise conjunct is
DROPPED (route (iii): the per-fibre retention through the tube-uniformization cut moves to the
consumer level, item 40.25).  DECISION: Stage I proves the band-at-INPUT form only; Stage II
(band-at-OUTPUT) is item 40.29.  The positive shade-mass hypothesis is dropped (follows from
the band lower half + `s.Nonempty`); `hdim` serves `eventually_card_le_rpow_neg_seven`. -/
theorem exists_bandShadedUniformTubeSet (hdim : Module.finrank ℝ E = 3) {ε' : ℝ}
    (hε' : 0 < ε') :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι κ : Type*} [DecidableEq κ] {s : Finset ι} {tτ : Finset κ}
        (T : ι → ShadedTube δ E) (pτ : ι → κ),
        s.Nonempty →
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        ∀ (lam₀ : NNReal), 0 < lam₀ →
          (∀ i ∈ s, (lam₀ : ENNReal) * volume (T i).carrier ≤ volume (T i).shade ∧
            volume (T i).shade ≤ 2 * (lam₀ : ENNReal) * volume (T i).carrier) →
          ∃ s' ⊆ s, ∃ Y' : ι → ShadedTube δ E, ∃ lam' : NNReal,
            s'.Nonempty ∧ 0 < lam' ∧
            (∀ i ∈ s', (Y' i).toTube = (T i).toTube ∧ (Y' i).shade ⊆ (T i).shade) ∧
            (s.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s'.card : ℝ) ∧
            ShadedBody.IsCRefinement s' (fun i => (Y' i).toShadedBody) s
              (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩ ∧
            Nonempty (ShadedTube.ShadedUniformTubeSet s' Y' (Tube.ssfGridLen δ)
              (uniformize.C 3)) ∧
            (∀ i ∈ s', (lam' : ENNReal) * volume (T i).carrier ≤ volume (T i).shade ∧
              volume (T i).shade ≤ 2 * (lam' : ENNReal) * volume (T i).carrier) ∧
            (δ : ENNReal) ^ ε' * ShadedBody.fullness s (fun i => (T i).toShadedBody)
              ≤ (lam' : ENNReal) := by
  classical
  haveI : Nontrivial E := by
    exact Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  have hε'3 : 0 < ε' / 3 := by positivity
  have hε'6 : 0 < ε' / 6 := by positivity
  obtain ⟨δP, hδPpos, hδPle1, hPthr⟩ :=
    exists_threshold_relativePlankTotalLoss_le 7 (ε' / 6) hε'6
  obtain ⟨δS, hδSpos, hδSle1, hSthr⟩ :=
    exists_threshold_relativePlankTotalLoss_le 7 (ε' / 3) hε'3
  obtain ⟨δU, hδUpos, hδUle1, hU⟩ :=
    Tube.exists_uniformTubeSet_subfamily_ssf (E := E) 7 (ε' / 6) hε'6
  obtain ⟨δG, hδGpos, hδGle1, hGthr⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le 1 le_rfl 0 1 1 one_pos
  obtain ⟨δ2, hδ2pos, hδ2le1, h2thr⟩ := exists_threshold_natCast_le_rpow 2 (ε' / 3) hε'3
  obtain ⟨δ2', hδ2'pos, hδ2'le1, h2thr'⟩ := exists_threshold_natCast_le_rpow 2 ε' hε'
  filter_upwards [eventually_card_le_rpow_neg_seven (E := E) hdim,
      eventually_le_nhdsGT (c := δP) hδPpos,
      eventually_le_nhdsGT (c := δS) hδSpos,
      eventually_le_nhdsGT (c := δU) hδUpos,
      eventually_le_nhdsGT (c := δG) hδGpos,
      eventually_le_nhdsGT (c := δ2) hδ2pos,
      eventually_le_nhdsGT (c := δ2') hδ2'pos,
      eventually_le_nhdsGT (c := (1 : NNReal)) one_pos,
      self_mem_nhdsWithin]
    with δ hcard7 hδP hδS hδU hδG hδ2 hδ2' hδ1 hδmem
  intro ι κ _ s tτ T pτ hs hball hED lam₀ hlam₀ hband
  have hδ0 : (0 : NNReal) < δ := hδmem
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδR1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hδe0 : (δ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hδ0).ne'
  have hδetop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hNpos : 0 < Tube.ssfGridLen δ := (hGthr hδ0 hδG).1
  have h7 : (s.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) :=
    hcard7 δ le_rfl s (fun i => (T i).toTube) (by intro i hi; simpa using hball i hi)
      (by intro i hi j hj hij; simpa using hED hi hj hij)
  have hsCardpos : 0 < s.card := Finset.card_pos.mpr hs
  -- common carrier volume
  obtain ⟨i₀, hi₀⟩ := hs
  set v : ENNReal := volume (T i₀).carrier with hv_def
  have hvpos : 0 < v := by
    have hc : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) :=
      ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))
    have hδp : 0 < (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr hδ0) (Module.finrank ℝ E - 1)
    exact lt_of_lt_of_le (ENNReal.mul_pos hc.ne' hδp.ne')
      (by simpa [hv_def] using _root_.Tube.le_volume (T i₀).toTube)
  have hvtop : v ≠ ⊤ := (T i₀).isCompact.measure_ne_top
  have hcarr : ∀ i, volume (T i).carrier = v := fun i => by
    simpa [hv_def] using
      _root_.Tube.volume_carrier_eq_volume_carrier (T i).toTube (T i₀).toTube
  have hsumcar : ∀ X : Finset ι, ∑ i ∈ X, volume (T i).carrier = (X.card : ENNReal) * v :=
    fun X => by
      simpa [hv_def] using
        _root_.Tube.sum_volume_carrier_eq_card_mul (fun i => (T i).toTube) (T i₀).toTube X
  -- **Step 1.**  Joint pigeonhole, partition 0 = `pτ` protected against the ORIGINAL `s`.
  let f : Fin (1 + 2) → ι → κ := fun _ => pτ
  obtain ⟨s₁, hs₁s, _, hjointCard, _, _⟩ :=
    exists_jointPartitionRegularization s 1 f
  have hs₁Card7 : (s₁.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) :=
    le_trans (by exact_mod_cast Finset.card_le_card hs₁s) h7
  have hlossJ : ((relativePlankJointLoss s.card 1 : ℕ) : ℝ) ≤ (δ : ℝ) ^ (-(ε' / 6)) := by
    have hm := relativePlankJointLoss_mono s.card (by omega : 1 ≤ Tube.ssfGridLen δ)
    have ht := relativePlankJointLoss_le_relativePlankTotalLoss s.card (Tube.ssfGridLen δ)
    calc
      ((relativePlankJointLoss s.card 1 : ℕ) : ℝ)
          ≤ ((relativePlankJointLoss s.card (Tube.ssfGridLen δ) : ℕ) : ℝ) := by
            exact_mod_cast hm
      _ ≤ ((relativePlankTotalLoss s.card (Tube.ssfGridLen δ) : ℕ) : ℝ) := by
            exact_mod_cast ht
      _ ≤ (δ : ℝ) ^ (-(ε' / 6)) := hPthr hδ0 hδP s.card h7
  -- **Step 2.**  Tube uniformization at `ε'/6` (GLOBAL count retention).
  obtain ⟨s₂, hs₂s₁, huniCard, huni⟩ :=
    hU (ι := ι) (δ := δ) hδ0 hδU s₁ (fun i => (T i).toTube)
      (by intro i hi; simpa using hball i (hs₁s hi)) hs₁Card7
  rcases huni with ⟨𝒰⟩
  have hs₂s : s₂ ⊆ s := hs₂s₁.trans hs₁s
  have hCardChain : (s.card : ℝ) ≤ (δ : ℝ) ^ (-(ε' / 3)) * (s₂.card : ℝ) := by
    calc
      (s.card : ℝ) ≤ ((relativePlankJointLoss s.card 1 : ℕ) : ℝ) * (s₁.card : ℝ) := by
        exact_mod_cast hjointCard
      _ ≤ (δ : ℝ) ^ (-(ε' / 6)) * (s₁.card : ℝ) :=
        mul_le_mul_of_nonneg_right hlossJ (by positivity)
      _ ≤ (δ : ℝ) ^ (-(ε' / 6)) * ((δ : ℝ) ^ (-(ε' / 6)) * (s₂.card : ℝ)) :=
        mul_le_mul_of_nonneg_left huniCard (Real.rpow_nonneg (le_of_lt hδR) _)
      _ = (δ : ℝ) ^ (-(ε' / 3)) * (s₂.card : ℝ) := by
        rw [← mul_assoc, ← Real.rpow_add hδR]; congr 1; ring_nf
  have hCard : (s.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s₂.card : ℝ) := by
    calc
      (s.card : ℝ) ≤ (δ : ℝ) ^ (-(ε' / 3)) * (s₂.card : ℝ) := hCardChain
      _ ≤ (δ : ℝ) ^ (-ε') * (s₂.card : ℝ) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_ge hδR hδR1 (by linarith)) (by positivity)
  have hs₂ne : s₂.Nonempty := by
    have h1card₂ : (1 : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s₂.card : ℝ) :=
      ((by exact_mod_cast Nat.succ_le_of_lt hsCardpos : (1 : ℝ) ≤ (s.card : ℝ))).trans hCard
    by_contra hne
    have hs₂0 : s₂.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
    rw [hs₂0] at h1card₂
    norm_num at h1card₂
  -- **Step 3.**  Index-fixed shade refinement.
  obtain ⟨Y', hY'tube, hY'shade, hfull, 𝒱₀, _, _, _, _⟩ :=
    ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet (V := T) 𝒰 hNpos
      (Nat.log 2 s₂.card) (fun t ht => Nat.log_mono_right (Finset.card_le_card ht))
  have hlossShade : (((Nat.log 2 s₂.card + 1 : ℕ) : ℝ) ^ (2 * Tube.ssfGridLen δ + 2))
      ≤ (δ : ℝ) ^ (-(ε' / 3)) := by
    have hs₂Card7 : (s₂.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) :=
      le_trans (by exact_mod_cast Finset.card_le_card hs₂s) h7
    have ht := hSthr hδ0 hδS s₂.card hs₂Card7
    have hsl := relativePlankShadeLoss_le_relativePlankTotalLoss s₂.card (Tube.ssfGridLen δ)
    have hmain : ((relativePlankShadeLoss s₂.card (Tube.ssfGridLen δ) : ℕ) : ℝ)
        ≤ (δ : ℝ) ^ (-(ε' / 3)) := (Nat.cast_le.mpr hsl).trans ht
    simpa [relativePlankShadeLoss, relativePlankBucket] using hmain
  have hunifC : Nonempty
      (ShadedTube.ShadedUniformTubeSet s₂ Y' (Tube.ssfGridLen δ) (uniformize.C 3)) := by
    have hmax : (max (Tube.uniformConst (Module.finrank ℝ E)) 4 : NNReal) ≤ uniformize.C 3 := by
      dsimp only [uniformize.C, uniformize.rawC, ShadedTube.ssfUniformConst]
      rw [hdim]
      exact le_max_right _ _
    exact ⟨ShadedTube.ShadedUniformTubeSet.mono 𝒱₀ hmax⟩
  have hshadeTube : ∀ i ∈ s₂, (Y' i).toTube = (T i).toTube ∧ (Y' i).shade ⊆ (T i).shade :=
    fun i hi => ⟨hY'tube i, hY'shade i⟩
  have hbandFinal : ∀ i ∈ s₂, (lam₀ : ENNReal) * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ 2 * (lam₀ : ENNReal) * volume (T i).carrier :=
    fun i hi => hband i (hs₂s hi)
  -- `dens`@T with `lam' := lam₀`: `fullness s ≤ 2λ₀` and `δ^ε' ≤ 1/2`.
  have hδpowR : (δ : ℝ) ^ ε' ≤ (1 / 2 : ℝ) := by
    have hxpos : 0 < (δ : ℝ) ^ ε' := Real.rpow_pos_of_pos hδR ε'
    have hle := (inv_le_inv₀ (inv_pos.mpr hxpos) (by norm_num : (0 : ℝ) < 2)).mpr
      (by simpa [Real.rpow_neg (le_of_lt hδR)] using (h2thr' hδ0 hδ2'))
    simpa [inv_inv, div_eq_inv_mul] using hle
  have hδpow : (δ : ENNReal) ^ ε' ≤ (1 / 2 : ENNReal) := by
    rw [ennreal_coe_nnreal_rpow hδR ε',
      show (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) by simp]
    exact ENNReal.ofReal_le_ofReal hδpowR
  have hfullness_le : (ShadedBody.fullness s (fun i => (T i).toShadedBody) : ENNReal)
      ≤ 2 * (lam₀ : ENNReal) := by
    rw [ShadedBody.coe_fullness, ShadedBody.fullness']
    refine (ENNReal.div_le_iff_le_mul ?_ ?_).mpr ?_
    · rw [hsumcar s]
      exact Or.inl (mul_ne_zero (by exact_mod_cast (ne_of_gt hsCardpos)) (ne_of_gt hvpos))
    · rw [hsumcar s]
      exact Or.inl (ENNReal.mul_ne_top (ENNReal.natCast_ne_top s.card) hvtop)
    · calc
        ∑ i ∈ s, volume (T i).shade ≤ ∑ i ∈ s, (2 * (lam₀ : ENNReal) * volume (T i).carrier) :=
          Finset.sum_le_sum fun i hi => (hband i hi).2
        _ = (2 * (lam₀ : ENNReal)) * ∑ i ∈ s, volume (T i).carrier := by rw [Finset.mul_sum]
  have hdens : (δ : ENNReal) ^ ε' * ShadedBody.fullness s (fun i => (T i).toShadedBody)
      ≤ (lam₀ : ENNReal) := by
    have hδ2le1 : (δ : ENNReal) ^ ε' * 2 ≤ 1 := by
      rw [ennreal_coe_nnreal_rpow hδR ε']
      have hreal : (δ : ℝ) ^ ε' * 2 ≤ 1 := by
        calc
          (δ : ℝ) ^ ε' * 2 ≤ (1 / 2 : ℝ) * 2 :=
            mul_le_mul_of_nonneg_right hδpowR (by norm_num)
          _ = (1 : ℝ) := by norm_num
      have hof2 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by simp
      rw [hof2]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hδR) ε')]
      simpa using ENNReal.ofReal_le_ofReal hreal
    calc
      (δ : ENNReal) ^ ε' * ShadedBody.fullness s (fun i => (T i).toShadedBody)
          ≤ (δ : ENNReal) ^ ε' * (2 * (lam₀ : ENNReal)) :=
            mul_le_mul_right hfullness_le ((δ : ENNReal) ^ ε')
      _ = ((δ : ENNReal) ^ ε' * 2) * (lam₀ : ENNReal) := by ring
      _ ≤ (1 : ENNReal) * (lam₀ : ENNReal) := mul_le_mul_left hδ2le1 (lam₀ : ENNReal)
      _ = (lam₀ : ENNReal) := by simp
  -- `refinement`@Y': mass half via card + fullness retention + band.
  have hCardE : (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-(ε' / 3)) * (s₂.card : ENNReal) := by
    rw [← ENNReal.ofReal_natCast s.card, ← ENNReal.ofReal_natCast s₂.card]
    rw [show (δ : ENNReal) ^ (-(ε' / 3)) = ENNReal.ofReal ((δ : ℝ) ^ (-(ε' / 3))) from
      (ennreal_coe_nnreal_rpow hδR (-(ε' / 3)))]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hδR) (-(ε' / 3)))]
    exact ENNReal.ofReal_le_ofReal hCardChain
  have h2inv : (2 : ENNReal) ≤ (δ : ENNReal) ^ (-(ε' / 3)) := by
    rw [ennreal_coe_nnreal_rpow hδR (-(ε' / 3)),
      show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by simp]
    exact ENNReal.ofReal_le_ofReal (h2thr hδ0 hδ2)
  have hlossShadeE : (((Nat.log 2 s₂.card + 1 : ℕ) : ENNReal) ^ (2 * Tube.ssfGridLen δ + 2))
      ≤ (δ : ENNReal) ^ (-(ε' / 3)) := by
    rw [ennreal_coe_nnreal_rpow hδR (-(ε' / 3))]
    rw [show (((Nat.log 2 s₂.card + 1 : ℕ) : ENNReal) ^ (2 * Tube.ssfGridLen δ + 2)) =
        (((Nat.log 2 s₂.card + 1) ^ (2 * Tube.ssfGridLen δ + 2) : ℕ) : ENNReal) by
      rw [Nat.cast_pow]]
    rw [(ENNReal.ofReal_natCast ((Nat.log 2 s₂.card + 1) ^ (2 * Tube.ssfGridLen δ + 2))).symm]
    exact ENNReal.ofReal_le_ofReal (by simpa [Nat.cast_pow] using hlossShade)
  have hfullT : (lam₀ : ENNReal) ≤
      ShadedBody.fullness' s₂ (fun i => (T i).toShadedBody) := by
    rw [ShadedBody.fullness']
    refine (ENNReal.le_div_iff_mul_le ?_ ?_).mpr ?_
    · rw [hsumcar s₂]
      exact Or.inl (mul_ne_zero
        (by exact_mod_cast (Finset.card_ne_zero.mpr hs₂ne) : (s₂.card : ENNReal) ≠ 0)
        (ne_of_gt hvpos))
    · rw [hsumcar s₂]
      exact Or.inl (ENNReal.mul_ne_top (ENNReal.natCast_ne_top s₂.card) hvtop)
    · calc
        (lam₀ : ENNReal) * ∑ i ∈ s₂, volume (T i).carrier
            = ∑ i ∈ s₂, ((lam₀ : ENNReal) * volume (T i).carrier) := by rw [Finset.mul_sum]
        _ ≤ ∑ i ∈ s₂, volume (T i).shade :=
            Finset.sum_le_sum fun i hi => (hband i (hs₂s hi)).1
  have hfullY : (lam₀ : ENNReal) * (δ : ENNReal) ^ (ε' / 3) ≤
      ShadedBody.fullness' s₂ (fun i => (Y' i).toShadedBody) := by
    have hAδ : (((Nat.log 2 s₂.card + 1 : ℕ) : ENNReal) ^ (2 * Tube.ssfGridLen δ + 2))
        * (δ : ENNReal) ^ (ε' / 3) ≤ 1 := by
      calc
        (((Nat.log 2 s₂.card + 1 : ℕ) : ENNReal) ^ (2 * Tube.ssfGridLen δ + 2))
            * (δ : ENNReal) ^ (ε' / 3)
            ≤ (δ : ENNReal) ^ (-(ε' / 3)) * (δ : ENNReal) ^ (ε' / 3) :=
              mul_le_mul_left hlossShadeE ((δ : ENNReal) ^ (ε' / 3))
        _ = (1 : ENNReal) := by
            rw [← ENNReal.rpow_add (-(ε' / 3)) (ε' / 3) hδe0 hδetop]; simp
    calc
      (lam₀ : ENNReal) * (δ : ENNReal) ^ (ε' / 3)
          ≤ ShadedBody.fullness' s₂ (fun i => (T i).toShadedBody) * (δ : ENNReal) ^ (ε' / 3) :=
            mul_le_mul_left hfullT ((δ : ENNReal) ^ (ε' / 3))
      _ ≤ ((((Nat.log 2 s₂.card + 1 : ℕ) : ENNReal) ^ (2 * Tube.ssfGridLen δ + 2))
          * ShadedBody.fullness' s₂ (fun i => (Y' i).toShadedBody))
            * (δ : ENNReal) ^ (ε' / 3) :=
              mul_le_mul_left hfull ((δ : ENNReal) ^ (ε' / 3))
      _ = ShadedBody.fullness' s₂ (fun i => (Y' i).toShadedBody)
          * ((((Nat.log 2 s₂.card + 1 : ℕ) : ENNReal) ^ (2 * Tube.ssfGridLen δ + 2))
            * (δ : ENNReal) ^ (ε' / 3)) := by ring
      _ ≤ ShadedBody.fullness' s₂ (fun i => (Y' i).toShadedBody) * 1 :=
          mul_le_mul_right hAδ (ShadedBody.fullness' s₂ (fun i => (Y' i).toShadedBody))
      _ = ShadedBody.fullness' s₂ (fun i => (Y' i).toShadedBody) := by simp
  have hcarrY : ∀ i, volume (Y' i).carrier = v := fun i => by
    calc
      volume (Y' i).carrier = volume ((Y' i).toTube).carrier := by simp
      _ = volume ((T i).toTube).carrier :=
          congrArg (fun t : Tube δ E => volume t.carrier) (hY'tube i)
      _ = v := by simpa using hcarr i
  have hsumcarY : ∑ i ∈ s₂, volume (Y' i).carrier = (s₂.card : ENNReal) * v := by
    simp [hcarrY]
  have hsumY : ∑ i ∈ s₂, volume (Y' i).shade =
      ShadedBody.fullness' s₂ (fun i => (Y' i).toShadedBody) * ((s₂.card : ENNReal) * v) := by
    calc
      ∑ i ∈ s₂, volume (Y' i).shade =
          ShadedBody.fullness s₂ (fun i => (Y' i).toShadedBody)
            * ∑ i ∈ s₂, volume (Y' i).carrier :=
              ShadedBody.sum_volumeReal_shade_eq_fullness_mul s₂
                (fun i => (Y' i).toShadedBody)
      _ = ShadedBody.fullness' s₂ (fun i => (Y' i).toShadedBody) * ((s₂.card : ENNReal) * v) := by
          rw [ShadedBody.coe_fullness, hsumcarY]
  have hmass : (δ : ENNReal) ^ ε' * ∑ i ∈ s, volume (T i).shade
      ≤ ∑ i ∈ s₂, volume (Y' i).shade := by
    have hsumShade_le : ∑ i ∈ s, volume (T i).shade
        ≤ (2 * (lam₀ : ENNReal)) * ((s.card : ENNReal) * v) := by
      calc
        ∑ i ∈ s, volume (T i).shade ≤ ∑ i ∈ s, (2 * (lam₀ : ENNReal) * volume (T i).carrier) :=
          Finset.sum_le_sum fun i hi => (hband i hi).2
        _ = (2 * (lam₀ : ENNReal)) * ∑ i ∈ s, volume (T i).carrier := by rw [Finset.mul_sum]
        _ = (2 * (lam₀ : ENNReal)) * ((s.card : ENNReal) * v) := by rw [hsumcar s]
    have hδmid : (δ : ENNReal) ^ ε' * 2 * (δ : ENNReal) ^ (-(ε' / 3))
        ≤ (δ : ENNReal) ^ (ε' / 3) := by
      calc
        (δ : ENNReal) ^ ε' * 2 * (δ : ENNReal) ^ (-(ε' / 3))
            = (δ : ENNReal) ^ ε' * (δ : ENNReal) ^ (-(ε' / 3)) * 2 := by ring
        _ = (δ : ENNReal) ^ (ε' + -(ε' / 3)) * 2 := by
              rw [ENNReal.rpow_add ε' (-(ε' / 3)) hδe0 hδetop]
        _ = 2 * (δ : ENNReal) ^ (ε' + -(ε' / 3)) := by ring
        _ = 2 * (δ : ENNReal) ^ (2 * ε' / 3) := by congr 1; ring_nf
        _ ≤ (δ : ENNReal) ^ (-(ε' / 3)) * (δ : ENNReal) ^ (2 * ε' / 3) :=
              mul_le_mul_left h2inv ((δ : ENNReal) ^ (2 * ε' / 3))
        _ = (δ : ENNReal) ^ (ε' / 3) := by
              rw [← ENNReal.rpow_add (-(ε' / 3)) (2 * ε' / 3) hδe0 hδetop]; congr 1; ring_nf
    calc
      (δ : ENNReal) ^ ε' * ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ENNReal) ^ ε' * ((2 * (lam₀ : ENNReal)) * ((s.card : ENNReal) * v)) :=
            mul_le_mul_right hsumShade_le ((δ : ENNReal) ^ ε')
      _ = (δ : ENNReal) ^ ε' * (2 * (lam₀ : ENNReal)) * ((s.card : ENNReal) * v) := by ring
      _ ≤ (δ : ENNReal) ^ ε' * (2 * (lam₀ : ENNReal))
          * (((δ : ENNReal) ^ (-(ε' / 3)) * (s₂.card : ENNReal)) * v) := by
            refine mul_le_mul_right ?_ ((δ : ENNReal) ^ ε' * (2 * (lam₀ : ENNReal)))
            exact mul_le_mul_left hCardE v
      _ = ((δ : ENNReal) ^ ε' * (2 * (lam₀ : ENNReal)) * (δ : ENNReal) ^ (-(ε' / 3)))
          * ((s₂.card : ENNReal) * v) := by ring
      _ ≤ (δ : ENNReal) ^ (ε' / 3) * (lam₀ : ENNReal) * ((s₂.card : ENNReal) * v) := by
          refine mul_le_mul_left ?_ ((s₂.card : ENNReal) * v)
          calc
            (δ : ENNReal) ^ ε' * (2 * (lam₀ : ENNReal)) * (δ : ENNReal) ^ (-(ε' / 3))
                = ((δ : ENNReal) ^ ε' * 2 * (δ : ENNReal) ^ (-(ε' / 3))) * (lam₀ : ENNReal) :=
                  by ring
            _ ≤ (δ : ENNReal) ^ (ε' / 3) * (lam₀ : ENNReal) :=
                mul_le_mul_left hδmid (lam₀ : ENNReal)
      _ = (lam₀ : ENNReal) * (δ : ENNReal) ^ (ε' / 3) * ((s₂.card : ENNReal) * v) := by ring
      _ ≤ ShadedBody.fullness' s₂ (fun i => (Y' i).toShadedBody) * ((s₂.card : ENNReal) * v) := by
          refine mul_le_mul_left hfullY ((s₂.card : ENNReal) * v)
      _ = ∑ i ∈ s₂, volume (Y' i).shade := by rw [hsumY]
  have href : ShadedBody.IsCRefinement s₂ (fun i => (Y' i).toShadedBody) s
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩ := by
    refine ⟨⟨hs₂s, ?_⟩, ?_⟩
    · intro i hi
      exact ⟨congrArg Tube.toConvexSpaceBody (hY'tube i), hY'shade i⟩
    · let c₀ : NNReal := ⟨(δ : ℝ) ^ ε', Real.rpow_nonneg (le_of_lt hδR) ε'⟩
      change (c₀ : ENNReal) * ∑ i ∈ s, volume (T i).shade ≤ ∑ i ∈ s₂, volume (Y' i).shade
      have hc₀ : (c₀ : ENNReal) = (δ : ENNReal) ^ ε' := by
        rw [show (c₀ : ENNReal) = ENNReal.ofReal ((c₀ : NNReal) : ℝ) from
          (ENNReal.ofReal_coe_nnreal (p := c₀)).symm]
        change ENNReal.ofReal ((δ : ℝ) ^ ε') = (δ : ENNReal) ^ ε'
        rw [ennreal_coe_nnreal_rpow hδR ε']
      rw [hc₀]
      exact hmass
  refine ⟨s₂, hs₂s, Y', lam₀, hs₂ne, hlam₀, hshadeTube, hCard, href, hunifC, hbandFinal,
    hdens⟩

end ml1Boot

end Kakeya
