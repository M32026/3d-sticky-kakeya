/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.CoarseFibre
public import Kakeya.Tube.Rescale
public import Kakeya.Tube.Dilate

/-!
# Main Lemma 1, Case (ii), Step 5a: the completed coarse fibre and the local density bound

Blueprint `subsec:ml1bootFibreCompletion`.  Step 5a of the middle-factor argument reconciles two
families that Steps 5b–5c must compare: the *retained* fine node family `t_τ`, whose fibre over a
coarse node `l` is what the factoring chain produces, and the family of *all* fine nodes lying in a
bounded enlargement of the coarse node tube `P_a(l)`, which is what the collision tests against.
The two statements of this file are the two halves of that reconciliation, and — this is the
structural point that makes them reachable at all — **both are statements about the unrefined node
families of the hierarchy**, so neither needs a retention, refinement-stability or purity
hypothesis of any kind.

* `Kakeya.ml1Boot.completedFibre` is `\widetilde t_τ(l)`, the fine nodes of `t_τ` lying inside the
  concentric rescaling `P_a(l)^{(Λ ρ_a)}`, together with
  `Kakeya.ml1Boot.fibre_subset_completedFibre`,
  `Kakeya.ml1Boot.card_completedFibreParents_le` and `Kakeya.ml1Boot.card_completedFibre_le`:
  the completion contains the parent-map fibre, its parents are `O(1)` in number, and it is
  `O(N_m)` in size (blueprint `lem:ml1bootFibreCompletion`).
* `Kakeya.ml1Boot.densityIn_le_of_card_neighbouringParents` is the density estimate of (5.10a)
  **with the parent count removed from it** (blueprint `lem:ml1bootLocalDensityCore`): the parent
  count enters as a bare hypothesis `|𝒫^♮(big)| ≤ M₀` on the cardinality of
  `Kakeya.ml1Boot.neighbouringParents`, and no covering family, tube, homothety factor or
  essential-distinctness hypothesis occurs.  This is the common core of the two routes to (5.10a)
  in this development, and it is stated so that the density argument is written **once** in this
  file.
* `Kakeya.ml1Boot.densityIn_le_of_neighbouringParents` is the local density bound (5.10a): the
  density of the *unrefined* level-`b` family in any convex body inside an *arbitrary* container
  `big` is `≲ δ ^ (-ε') (θ/τ) ^ (η m) D_m` (blueprint `lem:ml1bootLocalDensityUnrefined`).  The
  container is a free parameter and not a concentric rescaling of a coarse node tube, which is what
  makes the bound readable at a homothety-shaped region.  It is now the instance of the core at
  `M₀ = M · C_ds`, its cardinality hypothesis discharged by
  `Kakeya.ml1Boot.card_neighbouringParents_le_of_cover`; its statement is unchanged.

Two suppliers of the parent count stand side by side here.
`Kakeya.ml1Boot.neighbouringParents` names the set
`𝒫_Λ(W) = {assign_a i : i ∈ s', T i ⊆ W^{(Λθ)}}` of `a`-nodes reached by the leaves in an
enlargement, and

* `Kakeya.ml1Boot.card_neighbouringParents_le_of_cover` is the counting half of the
  `O(1)`-neighbouring-parents bound at a **supplied covering family** (blueprint
  `lem:ml1bootNeighbouringParentsCounting`);
* `Kakeya.ml1Boot.card_neighbouringParents_le_of_essDistinct` counts the same set at a
  **homothety container** `K ⊆ c · V` under the hypothesis (R1) that the coarse node tubes reached
  inside `K` are pairwise essentially distinct (blueprint
  `lem:ml1bootNeighbouringParentsEssDistinct`).  Its geometric half is
  `Kakeya.ml1Boot.node_le_dilate_of_leaf_le` (blueprint `lem:ml1bootNodeTubeInDilate`): a `θ`-tube
  containing a leaf that lies in `c · V` is itself inside `Λ · V` for any `Λ ≥ c + 4`.  **(R1) has
  no supplier in this development**, so this route is conditional and is not evidence that an
  absolute parent count is available at a homothety container.

And `Kakeya.densityIn_le_sum_densityIn_of_cover` and `Kakeya.densityIn_le_densityIn_of_forall_le`
are the two generic facts about `Kakeya.densityIn` that the density core is assembled from
(blueprint `lem:ml1bootDensityCoverRestrict`); they mention no tube, scale or hierarchy and so
carry no `ml1Boot` prefix.

## Two unformalized constants, replaced by explicit parameters

The blueprint displays this material with two constants that have no Lean counterpart, and the
statements below substitute an explicit parameter for each.  Neither substitution weakens
anything: each replaces a constant whose *existence* is asserted elsewhere by a parameter, so the
Lean statements are families containing the displayed ones.

* The **enlargement constant** `C₀ = C_{ml1bootEnlargement}(3)` of blueprint
  `def:ml1bootEnlargementConstant` is defined by a supremum and has no Lean definition.  The
  radius `2 C₀ θ` of the completion and the radius `3 C₀ θ` of the density region are therefore
  both written `Λ * ρ_a` for a free `Λ`; the displayed statements are the instances `Λ = 2 C₀`
  and `Λ = 3 C₀`.  The two parameters are *independent*, and the assembly that feeds the
  completion into the density bound owes the relation `Λ_completion + 1 ≤ Λ_density` (blueprint
  `lem:ml1bootLocalDensityUnrefined`); it is a hypothesis of neither lemma separately.
* The **neighbouring-parent count** `C_{ml1bootNeighbouringParents}(3,Λ,C_ds)` of blueprint
  `def:ml1bootNeighbouringParentsConstant` is `M(3,Λ) · C_ds`, and the finiteness of `M(3,Λ)` is a
  net construction that is not formalized.  Every statement below therefore takes
  `Kakeya.ml1Boot.IsEnlargementCover` — the existence of `M` covering tubes of the exact grid
  radius — as a *hypothesis* and states its bound with the explicit product `M * Cu`.

## Divergences from the blueprint display, recorded

* `Kakeya.ml1Boot.card_neighbouringParents_le_of_cover` is stated at an arbitrary convex
  container `K` rather than at `W^{(Λθ)}` for a `θ`-tube `W` and a `Λ ≥ 1`.  The container enters
  the proof only through the covering hypothesis, so `Λ` and `W` would be binders that name `K`
  and nothing else; the displayed statement is the instance
  `K = (W.rescale (Λ * ρ_a)).toConvexSpaceBody`.
* `Kakeya.ml1Boot.card_completedFibre_le` takes only the *upper* half
  `|t_τ[T_{θ,l'}]| ≤ Λ_load N_m` of the blueprint's two-sided load bracket.  The lower half
  `Λ_load⁻¹ N_m ≤ |t_τ[T_{θ,l'}]|` is not used, there or in this file; it is owed by the assembly
  that supplies the pair `(N_m, Λ_load)`, not by this lemma.
* `Kakeya.ml1Boot.densityIn_le_of_neighbouringParents` is stated at an arbitrary container `big`
  rather than at the blueprint's `P_a(l)^{(3 C₀ θ)}`, for the same reason as
  `Kakeya.ml1Boot.card_neighbouringParents_le_of_cover` above: `l` and `Λ` would be binders naming
  the container and nothing else.  This is not cosmetic here — it is what makes the bound available
  to a consumer whose region is a *homothety* rather than a concentric rescaling, which is the shape
  the repaired plank enlargement produces (blueprint `note:ml1bootEnlargementTubeStatus`).
* `Kakeya.ml1Boot.densityIn_le_of_neighbouringParents` takes
  `StickyKakeya.IsFrostmanDividingBlock` — the `block` field of
  `Kakeya.ml1Boot.IsCaseTwoInput`, which is stated on `𝒰'` alone — in place of the whole Case (ii)
  input bundle the blueprint names.  The Case (ii) bundle's refinement, shade-mass and banding
  clauses speak about a shading this lemma never mentions.  Three of the block's seven fields are
  read: `frostman_nodes` for the Frostman factor, `coarse_lt_fine` for the grid nesting
  `P_b(assign_b i) ⊆ P_a(assign_a i)` from `a` to `b`, and `fine_le` for `assign_mem a` and for
  the hypothesis `a ≤ N` of `Kakeya.ml1Boot.card_neighbouringParents_le_of_cover`.  The remaining
  four — `exponent_lt`, `separated`, `frostman_leaves`, `frostman_lower` — are unused here and
  arrive bundled, the block being a single hypothesis at every call site.  The statement likewise
  omits the blueprint's `0 < D_m` and `1 ≤ Λ_Δ`, which fix the interpretation of the pair and are
  not used.

*Why the density bound is stated at the containment family.*  The family attached to a
neighbouring parent `l''` is `Tube.UniformTubeSet.nodesUnder b a l''` — *all* level-`b`
nodes whose node tube lies inside `P_a(l'')` — and **not** the fibre of a coarse node parent map.
The distinction is not cosmetic: `StickyKakeya.IsFrostmanDividingBlock.frostman_nodes`, the clause
that supplies the Frostman factor, is asserted at the containment family, and reading it at a
parent-map fibre would be an appeal to a statement this development does not make.  A second gain
is that no parent map occurs in that lemma at all.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody StickyKakeya Tube Convexity Filter Topology

namespace Kakeya

universe u

/-! ### Two generic facts about `Kakeya.densityIn`

Blueprint `lem:ml1bootDensityCoverRestrict`.  Neither statement mentions a tube, a scale, a
hierarchy or a dimension; they are here only because
`Kakeya.ml1Boot.densityIn_le_of_neighbouringParents` is made of them. -/

section GenericDensity

variable {E : Type*} [TopologicalSpace E] [ConvexSpace ℝ E] [MeasureSpace E] {ι κ : Type*}

/-- **Splitting the density over a finite cover of the contributing indices** (blueprint
`lem:ml1bootDensityCoverRestrict`(a)).

If every `i ∈ s` whose body lies in `K` lies in some `s p`, then `Δ(𝕎, K)` is at most the sum of
the `Δ(𝕎|_{s p}, K)`.  The denominators are equal, and the numerator on the left is a sum of
nonnegative terms each of which occurs in at least one numerator on the right.

The `s p` are **not** required to be pairwise disjoint, and need not cover `s` — only its
contributing part. -/
theorem densityIn_le_sum_densityIn_of_cover (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) (P : Finset κ) (sp : κ → Finset ι)
    (hcover : ∀ i ∈ s, W i ≤ K → ∃ q ∈ P, i ∈ sp q) :
    densityIn s W K ≤ ∑ q ∈ P, densityIn (sp q) W K := by
  classical
  let T : κ → Finset ι := fun q => {i ∈ sp q | W i ≤ K}
  have hdouble : (∑ i ∈ P.biUnion T, volume (W i).carrier) ≤
      ∑ q ∈ P, ∑ i ∈ T q, volume (W i).carrier := by
    calc
      (∑ i ∈ P.biUnion T, volume (W i).carrier)
          ≤ ∑ i ∈ P.biUnion T, ∑ q ∈ P,
              (if i ∈ T q then volume (W i).carrier else 0) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            rcases (Finset.mem_biUnion.mp hi) with ⟨q, hqP, hqT⟩
            calc
              volume (W i).carrier = if i ∈ T q then volume (W i).carrier else 0 := by simp [hqT]
              _ ≤ ∑ q' ∈ P, (if i ∈ T q' then volume (W i).carrier else 0) := by
                  exact Finset.single_le_sum_of_canonicallyOrdered
                    (f := fun q' => if i ∈ T q' then volume (W i).carrier else 0) hqP
      _ = ∑ q ∈ P, ∑ i ∈ P.biUnion T,
            (if i ∈ T q then volume (W i).carrier else 0) := by
          rw [Finset.sum_comm]
      _ = ∑ q ∈ P, ∑ i ∈ T q, volume (W i).carrier := by
          apply Finset.sum_congr rfl
          intro q hqP
          have h₁ : T q ⊆ P.biUnion T := by
            intro i hi
            exact Finset.mem_biUnion.mpr ⟨q, hqP, hi⟩
          have h₀ : ∀ x ∈ P.biUnion T, x ∉ T q →
              (if x ∈ T q then volume (W x).carrier else 0) = 0 := by
            intro x hx hxnot
            simp [hxnot]
          rw [← Finset.sum_subset h₁ h₀]
          simp
  have hAcover : ({i ∈ s | W i ≤ K} : Finset ι) ⊆ P.biUnion T := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rcases hcover i hi.1 hi.2 with ⟨q, hqP, hqsp⟩
    exact Finset.mem_biUnion.mpr ⟨q, hqP, Finset.mem_filter.mpr ⟨hqsp, hi.2⟩⟩
  have hnum : (∑ i ∈ s with W i ≤ K, volume (W i).carrier) ≤
      ∑ q ∈ P, ∑ i ∈ T q, volume (W i).carrier :=
    (Finset.sum_le_sum_of_subset hAcover).trans hdouble
  have hRHS : (∑ q ∈ P, densityIn (sp q) W K) =
      (∑ q ∈ P, ∑ i ∈ T q, volume (W i).carrier) / volume K.carrier := by
    unfold densityIn
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul]
  unfold densityIn
  rw [hRHS]
  apply ENNReal.div_le_div
  · exact hnum
  · exact le_rfl

/-- **Shrinking the test body** (blueprint `lem:ml1bootDensityCoverRestrict`(b)).

If `K'' ≤ K` and every member of the family contained in `K` is already contained in `K''`, then
the two numerators are equal while the denominator can only shrink, so the density can only
increase.

This is the form the call site actually has, and it is weaker in its hypothesis than
`Kakeya.densityIn_le_densityIn_inter` of `Kakeya/Frostman.lean`, which forms `K ⊓ K'` explicitly
and asks that *every* member of the family lie in `K'`. -/
theorem densityIn_le_densityIn_of_forall_le (s : Finset ι) (W : ι → ConvexSpaceBody E)
    {K K'' : ConvexSpaceBody E} (hKK : K'' ≤ K) (h : ∀ i ∈ s, W i ≤ K → W i ≤ K'') :
    densityIn s W K ≤ densityIn s W K'' := by
  classical
  unfold densityIn
  apply ENNReal.div_le_div
  · have hsub : (s.filter fun i ↦ W i ≤ K) ⊆ (s.filter fun i ↦ W i ≤ K'') := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, h i hi.1 hi.2⟩
    exact Finset.sum_le_sum_of_subset hsub
  · exact measure_mono hKK

end GenericDensity

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-! ### The neighbouring parents of a container, and the counting half of their `O(1)` bound -/

/-- **The `a`-nodes reached by the leaves lying in a container** (blueprint
`lem:ml1bootNeighbouringParents`, the set `𝒫_Λ(W)`).

`𝒫_Λ(W) = {assign_a i : i ∈ s', T i ⊆ W^{(Λθ)}}` is the instance `K = (W.rescale (Λ * ρ_a))` of
this definition; the container is left arbitrary because it enters nothing but the filter.  That
freedom is used: the two suppliers of a bound on the cardinality read it at containers of
*different shapes* — `Kakeya.ml1Boot.card_neighbouringParents_le_of_cover` at whatever container
carries a covering family (the displayed instance being a concentric rescaling of a coarse node
tube), and `Kakeya.ml1Boot.card_neighbouringParents_le_of_essDistinct` at a homothety `K ≤ c · V`.

Note that the container is a `Kakeya.ConvexSpaceBody`-level containment on the *leaves*, not on
the nodes: it is the leaves that are pushed through `assign a`.  Which fact then bounds the result
depends on the route and is **not** part of this definition:
`Tube.UniformTubeSet.boundedOverlap` — a statement about nodes meeting a tube *through
`s'`* — is what the covering route uses, and by blueprint
`note:ml1bootHomothetyOverlapInsufficient` it is exactly what the homothety route cannot use; that
route counts the node tubes directly, as a packing problem. -/
noncomputable def neighbouringParents {ι : Type*} {δ : NNReal} {s' : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu) (a : ℕ) (K : ConvexSpaceBody E) :
    Finset ι :=
  open scoped Classical in
  (s'.filter fun i => (T i).toConvexSpaceBody ≤ K).image (𝒰'.cover.assign a)

/-- **A finite cover of the leaves in a container by tubes of the exact grid radius** (blueprint
`def:ml1bootNeighbouringParentsConstant`).

`M` tubes `V_1, …, V_M` of radius exactly `ρ` catch, between them, every leaf of `s'` that lies in
the container `K`.  At all four call sites below `ρ` is the coarse grid radius `ρ_a`; `K` is a
concentric enlargement `P_a(l)^{(Λ ρ_a)}` of a coarse node at
`Kakeya.ml1Boot.card_completedFibreParents_le` and `Kakeya.ml1Boot.card_completedFibre_le`, and an
arbitrary container at `Kakeya.ml1Boot.card_neighbouringParents_le_of_cover` and
`Kakeya.ml1Boot.densityIn_le_of_neighbouringParents`.

This is the named hypothesis that stands in for the unformalized quantity `M(3,Λ)` of blueprint
`def:ml1bootNeighbouringParentsConstant`.  What that definition asserts, and what remains
informal, is that `M` may be chosen independently of `θ`, of `δ` and of the container; the net
argument producing such a family is what needs `δ ≤ θ/2`, which is accordingly *not* a hypothesis
of anything below — it is needed to *produce* a cover, not to count against one.

The covering tubes are existentially quantified rather than carried as data: no consumer reads
which family it is, only that one exists and how large `M` is.

Keeping the `V q` at radius exactly `ρ` is essential and not a normalization.  The clause that
converts a cover into a node count, `Tube.UniformTubeSet.boundedOverlap`, is asserted only
at the exact grid radius. -/
structure IsEnlargementCover {ι : Type*} {δ : NNReal} (s' : Finset ι) (T : ι → Tube δ E)
    (ρ : NNReal) (K : ConvexSpaceBody E) (M : ℕ) : Prop where
  /-- Every leaf of `s'` inside `K` lies in one of `M` tubes of radius `ρ`. -/
  exists_cover : ∃ V : Fin M → Tube ρ E,
    ∀ i ∈ s', (T i).toConvexSpaceBody ≤ K →
      ∃ q : Fin M, (T i).toConvexSpaceBody ≤ (V q).toConvexSpaceBody

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **`O(1)` neighbouring parents: the counting half, at a given covering family** (blueprint
`lem:ml1bootNeighbouringParentsCounting`).

Given a cover of the leaves inside the container `K` by `M` tubes of the exact grid radius
(`Kakeya.ml1Boot.IsEnlargementCover`), the set of `a`-nodes those leaves reach has at most
`M * Cu` members.

Each such node meets some `V q` through `s'` — it contains the leaf, by clause (b) of
`Tube.GridCoverSystem`, and so does `V q` — so `neighbouringParents` is covered by the
`M` sets `Tube.UniformTubeSet.meetingNodes a (V q)`, each of size at most `Cu` by
`Tube.UniformTubeSet.card_meetingNodes_le`.

`ha : a ≤ N` is what lets `Tube.UniformTubeSet.boundedOverlap` and clause (b) of the grid
cover system be read at the index `a`; it is the only thing this statement asks of `a`. -/
theorem card_neighbouringParents_le_of_cover {ι : Type*} {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {N a : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu) (ha : a ≤ N)
    {K : ConvexSpaceBody E} {M : ℕ} (hcov : IsEnlargementCover s' T (gridScale δ N a) K M) :
    ((neighbouringParents 𝒰' a K).card : NNReal) ≤ M * Cu := by
  classical
  rcases hcov.exists_cover with ⟨V, hV⟩
  have hsub : neighbouringParents 𝒰' a K ⊆
      Finset.univ.biUnion (fun q : Fin M => 𝒰'.meetingNodes a (V q)) := by
    intro l hl
    rw [neighbouringParents, Finset.mem_image] at hl
    rcases hl with ⟨i, hi, rfl⟩
    rw [Finset.mem_filter] at hi
    rcases hi with ⟨hi, hK⟩
    rw [Finset.mem_biUnion]
    rcases hV i hi hK with ⟨q, hq⟩
    refine ⟨q, Finset.mem_univ _, ?_⟩
    rw [UniformTubeSet.meetingNodes, Finset.mem_filter]
    constructor
    · exact 𝒰'.cover.assign_mem a ha i hi
    · refine ⟨i, hi, ?_, hq⟩
      exact 𝒰'.cover.le_tube_assign a ha i hi
  have hcard : (neighbouringParents 𝒰' a K).card ≤
      ∑ q : Fin M, (𝒰'.meetingNodes a (V q)).card := by
    calc
      (neighbouringParents 𝒰' a K).card ≤
          (Finset.univ.biUnion (fun q : Fin M => 𝒰'.meetingNodes a (V q))).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ q : Fin M, (𝒰'.meetingNodes a (V q)).card := Finset.card_biUnion_le
  have hsumn : (∑ q : Fin M, (𝒰'.meetingNodes a (V q)).card : NNReal) ≤ M * Cu := by
    calc
      (∑ q : Fin M, (𝒰'.meetingNodes a (V q)).card : NNReal)
          ≤ ∑ q : Fin M, (Cu : NNReal) := by
            apply Finset.sum_le_sum
            intro q hq
            exact 𝒰'.card_meetingNodes_le ha (V q)
      _ = M * Cu := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    ((neighbouringParents 𝒰' a K).card : NNReal)
        ≤ (∑ q : Fin M, (𝒰'.meetingNodes a (V q)).card : NNReal) := by
          exact_mod_cast hcard
    _ ≤ M * Cu := hsumn

/-! ### The second supplier of a parent count: a homothety container under essential distinctness

Blueprint `subsec:ml1bootHomothetyParents`.  The two statements below are the geometric half and
the packing half of a count for `Kakeya.ml1Boot.neighbouringParents` at a container of *homothety*
shape `K ⊆ c · V`, which is the shape the repaired plank enlargement produces and which
`Kakeya.ml1Boot.card_neighbouringParents_le_of_cover` cannot be read at.  The count is conditional
on an essential-distinctness hypothesis that **has no supplier in this development**; see the
docstring of `Kakeya.ml1Boot.card_neighbouringParents_le_of_essDistinct`. -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- A segment through a point `m` in a direction `e`, extended from half-length `s` to
half-length `t`, is monotone in the half-length. -/
lemma axisSegment_incl {s t : ℝ} (hm0 : 0 ≤ s) (hst : s ≤ t) (ht0 : 0 < t)
    (m : E) (e : E) :
    segment ℝ (m - s • e) (m + s • e) ⊆ segment ℝ (m - t • e) (m + t • e) := by
  refine Convex.segment_subset (convex_segment (m - t • e) (m + t • e)) ?_ ?_
  · -- `m - s • e` lies in the big segment
    let a : ℝ := (t - s) / (2 * t)
    have ha : a ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [a]
      constructor
      · exact div_nonneg (sub_nonneg.mpr hst) (mul_pos (by norm_num) ht0).le
      · rw [div_le_iff₀ (mul_pos (by norm_num) ht0)]
        nlinarith [hm0, hst, ht0]
    have hx : AffineMap.lineMap (m - t • e) (m + t • e) a = m - s • e := by
      rw [AffineMap.lineMap_apply_module]
      have hcombo : ∀ u : ℝ,
          (1 - u) • (m - t • e) + u • (m + t • e) = m + ((2 * u - 1) * t) • e := by
        intro u
        module
      rw [hcombo a]
      have hscalar : (2 * a - 1) * t = -s := by
        dsimp [a]
        field_simp [ne_of_gt ht0]
        ring
      rw [hscalar]
      module
    rw [← hx]
    exact lineMap_mem_segment ℝ _ _ ha
  · -- `m + s • e` lies in the big segment
    let a : ℝ := (t + s) / (2 * t)
    have ha : a ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [a]
      constructor
      · exact div_nonneg (by linarith) (mul_pos (by norm_num) ht0).le
      · rw [div_le_iff₀ (mul_pos (by norm_num) ht0)]
        nlinarith [hm0, hst, ht0]
    have hx : AffineMap.lineMap (m - t • e) (m + t • e) a = m + s • e := by
      rw [AffineMap.lineMap_apply_module]
      have hcombo : ∀ u : ℝ,
          (1 - u) • (m - t • e) + u • (m + t • e) = m + ((2 * u - 1) * t) • e := by
        intro u
        module
      rw [hcombo a]
      have hscalar : (2 * a - 1) * t = s := by
        dsimp [a]
        field_simp [ne_of_gt ht0]
        ring
      rw [hscalar]
    rw [← hx]
    exact lineMap_mem_segment ℝ _ _ ha

omit [Nontrivial E] in
/-- **A `θ`-tube containing a leaf that lies in `c · V` is inside `Λ · V`** (blueprint
`lem:ml1bootNodeTubeInDilate`).

Let `V` be a `C θ`-tube with `C ≥ 1`, let `P` be a `θ`-tube and let `T` be a `σ`-tube with
`T ⊆ P` and `T ⊆ c · V`.  Then `P ⊆ Λ · V` for every `Λ ≥ c + 4`.  Both dilates are the
homothety `Kakeya.Tube.dilate` and **not** the concentric rescaling `Kakeya.Tube.rescale`; the only
concentric rescaling in the argument is the intermediate one supplied by
`Kakeya.Tube.le_rescale_of_subset`, which turns `T ⊆ P` into `P ⊆ T^{(4θ)}`.

No relation between `σ` and `θ` is needed, none between `θ` and `1`, and **no positivity on `θ`**:
`Kakeya.Tube.le_rescale_of_subset` assumes none on either radius, and the arithmetic
`c C θ + 4 θ ≤ (c + 4) C θ` needs only `C ≥ 1` and `θ ≥ 0`, which for `NNReal` is free.  The
blueprint display asks only `θ, δ ≥ 0` for the same reason, so the two agree.  Of the homothety
factor only
positivity is asked, that being what `Kakeya.Tube.dilate_carrier_eq_cthickening` needs in order to
read `c · V` as a thickened segment; the comparison `c ≤ Λ` that the proof also uses is already
contained in `c + 4 ≤ Λ`.

This is pure tube geometry, and it is separated from
`Kakeya.ml1Boot.card_neighbouringParents_le_of_essDistinct` so that neither proof carries both the
geometry and the packing count. -/
theorem node_le_dilate_of_leaf_le {σ θ C : NNReal} (hC : 1 ≤ C)
    {c Λ : ℝ} (hc : 0 < c) (hcΛ : c + 4 ≤ Λ)
    (V : Tube (C * θ) E) (P : Tube θ E) (T : Tube σ E)
    (hTP : (T.toConvexSpaceBody : ConvexSpaceBody E) ≤ P.toConvexSpaceBody)
    (hTV : (T.toConvexSpaceBody : ConvexSpaceBody E) ≤ Tube.dilate V c) :
    (P.toConvexSpaceBody : ConvexSpaceBody E) ≤ Tube.dilate V Λ := by
  classical
  have hθ0 : 0 ≤ (θ : ℝ) := NNReal.coe_nonneg θ
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hCθ0 : 0 ≤ ((C * θ : NNReal) : ℝ) := NNReal.coe_nonneg (C * θ)
  have hΛpos : 0 < Λ := by
    exact lt_of_lt_of_le (add_pos hc (by norm_num)) hcΛ
  have hcΛ' : c ≤ Λ := by linarith
  have hc0 : 0 ≤ c := le_of_lt hc
  set Sc : Set E :=
    segment ℝ (V.center - (c / 2) • V.direction) (V.center + (c / 2) • V.direction)
  set Sl : Set E :=
    segment ℝ (V.center - (Λ / 2) • V.direction) (V.center + (Λ / 2) • V.direction)
  have hdlc : (Tube.dilate V c).carrier =
      Metric.cthickening (c * ((C * θ : NNReal) : ℝ)) Sc := by
    simpa [Sc] using (_root_.Tube.dilate_carrier_eq_cthickening V hc)
  have hdlΛ : (Tube.dilate V Λ).carrier =
      Metric.cthickening (Λ * ((C * θ : NNReal) : ℝ)) Sl := by
    simpa [Sl] using (_root_.Tube.dilate_carrier_eq_cthickening V hΛpos)
  -- step 1: `P ⊆ T^{(4θ)}` from `T ⊆ P`
  have hP_le : (P.toConvexSpaceBody : ConvexSpaceBody E) ≤
      (T.rescale (4 * θ)).toConvexSpaceBody :=
    Tube.le_rescale_of_subset T P hTP
  -- the axis of `T` lies inside `c · V`
  have hTVc : T.carrier ⊆ (Tube.dilate V c).carrier := by
    exact (SetLike.coe_subset_coe.mpr hTV)
  have hseg_in_dil : segment ℝ T.x T.y ⊆ (Tube.dilate V c).carrier := by
    calc
      segment ℝ T.x T.y ⊆ T.carrier := by
        rw [Tube.carrier_eq_cthickening]
        exact Metric.self_subset_cthickening (segment ℝ T.x T.y)
      _ ⊆ (Tube.dilate V c).carrier := hTVc
  change (P.toConvexSpaceBody : Set E) ⊆ (Tube.dilate V Λ).carrier
  intro v hv
  have hPsub : P.carrier ⊆ (T.rescale (4 * θ)).carrier := by
    exact hP_le
  have hv1 : v ∈ (T.rescale (4 * θ)).carrier := hPsub hv
  have hv2 : v ∈ Metric.cthickening ((4 * θ : NNReal) : ℝ) (segment ℝ T.x T.y) := by
    rw [Tube.carrier_eq_cthickening] at hv1
    have hrx : (T.rescale (4 * θ)).x = T.x := rfl
    have hry : (T.rescale (4 * θ)).y = T.y := rfl
    simpa [hrx, hry] using hv1
  have hseg_in_cth : segment ℝ T.x T.y ⊆
      Metric.cthickening (c * ((C * θ : NNReal) : ℝ)) Sc := by
    rw [← hdlc]
    exact hseg_in_dil
  have hv3 : v ∈ Metric.cthickening ((4 * θ : NNReal) : ℝ)
      (Metric.cthickening (c * ((C * θ : NNReal) : ℝ)) Sc) := by
    exact Metric.cthickening_subset_of_subset ((4 * θ : NNReal) : ℝ) hseg_in_cth hv2
  have hcCθ0 : 0 ≤ c * ((C * θ : NNReal) : ℝ) := mul_nonneg hc0 hCθ0
  have hv4 : v ∈ Metric.cthickening
      (((4 * θ : NNReal) : ℝ) + c * ((C * θ : NNReal) : ℝ)) Sc := by
    exact Metric.cthickening_cthickening_subset
      (NNReal.coe_nonneg (4 * θ)) hcCθ0 Sc hv3
  -- arithmetic: `4θ + c·Cθ ≤ Λ·Cθ`
  have hθ_le_Cθ : (θ : ℝ) ≤ ((C * θ : NNReal) : ℝ) := by
    calc
      (θ : ℝ) = 1 * (θ : ℝ) := by ring
      _ ≤ (C : ℝ) * (θ : ℝ) := mul_le_mul_of_nonneg_right hC1 hθ0
      _ = ((C * θ : NNReal) : ℝ) := by
        rw [NNReal.coe_mul]
  have h4θ_le : ((4 * θ : NNReal) : ℝ) ≤ 4 * ((C * θ : NNReal) : ℝ) := by
    have h4 : ((4 * θ : NNReal) : ℝ) = 4 * (θ : ℝ) := by
      rw [NNReal.coe_mul]
      norm_num
    rw [h4]
    exact mul_le_mul_of_nonneg_left hθ_le_Cθ (by norm_num)
  have hsum1 : ((4 * θ : NNReal) : ℝ) + c * ((C * θ : NNReal) : ℝ) ≤
      (c + 4) * ((C * θ : NNReal) : ℝ) := by
    nlinarith [h4θ_le]
  have hstep : (c + 4) * ((C * θ : NNReal) : ℝ) ≤ Λ * ((C * θ : NNReal) : ℝ) :=
    mul_le_mul_of_nonneg_right hcΛ hCθ0
  have hsum_le : ((4 * θ : NNReal) : ℝ) + c * ((C * θ : NNReal) : ℝ) ≤
      Λ * ((C * θ : NNReal) : ℝ) :=
    hsum1.trans hstep
  -- segment inclusion `S_c ⊆ S_Λ`
  have hSc : Sc ⊆ Sl := by
    dsimp [Sc, Sl]
    apply axisSegment_incl (m := V.center) (e := V.direction)
    · exact div_nonneg hc0 (by norm_num)
    · exact div_le_div_of_nonneg_right hcΛ' (by norm_num : (0 : ℝ) ≤ 2)
    · exact div_pos hΛpos (by norm_num)
  have hv5 : v ∈ Metric.cthickening (Λ * ((C * θ : NNReal) : ℝ)) Sl := by
    have hmid_sub : Metric.cthickening
          (((4 * θ : NNReal) : ℝ) + c * ((C * θ : NNReal) : ℝ)) Sc
        ⊆ Metric.cthickening (Λ * ((C * θ : NNReal) : ℝ)) Sl := by
      calc
        Metric.cthickening (((4 * θ : NNReal) : ℝ) + c * ((C * θ : NNReal) : ℝ)) Sc
            ⊆ Metric.cthickening (((4 * θ : NNReal) : ℝ) + c * ((C * θ : NNReal) : ℝ)) Sl :=
              Metric.cthickening_subset_of_subset
                (((4 * θ : NNReal) : ℝ) + c * ((C * θ : NNReal) : ℝ)) hSc
        _ ⊆ Metric.cthickening (Λ * ((C * θ : NNReal) : ℝ)) Sl :=
              Metric.cthickening_mono hsum_le Sl
    exact hmid_sub hv4
  rw [hdlΛ]
  exact hv5

/-- **`O(1)` neighbouring parents at a homothety container, under essential distinctness**
(blueprint `lem:ml1bootNeighbouringParentsEssDistinct`).

Write `θ = ρ_a` for the coarse grid radius.  Let `V` be a `C θ`-tube with `C ≥ 1` and
`C θ ≤ 1`, let `c ≥ 1` satisfy `c + 4 ≤ C_n` — the linear dilation constant
`Kakeya.Tube.tubeOverlapCoreClose.C` — and let `K` be a convex body inside the *homothety*
`c · V`.  If the coarse node tubes reached by the leaves inside `K` are pairwise essentially
distinct, then `Kakeya.ml1Boot.neighbouringParents 𝒰' a K` has at most
`Kakeya.Tube.comparableReplacement.C n C` members, a bound depending on nothing but the ambient
dimension and `C`.

Each such node tube contains a leaf lying in `c · V` (clause (b) of
`Tube.GridCoverSystem`), so `Kakeya.ml1Boot.node_le_dilate_of_leaf_le` at `Λ = C_n` puts it
inside `C_n · V`; the family is then a finite pairwise essentially distinct family of `θ`-tubes in
`C_n · V`, and `Kakeya.Tube.essDistinctTubesInDilate` counts it.  Finiteness is automatic here,
`Kakeya.ml1Boot.neighbouringParents` being a `Finset`.

**This is a conditional statement and may not be cited as evidence that an absolute parent count is
available at a homothety container.**  The essential-distinctness hypothesis `hED` has no supplier
in this development: it is caution (R1) of the blueprint, and in the configuration of
`note:ml1bootHomothetyOverlapInsufficient` it fails already for the nodes reached inside a single
container.  What the lemma says is that (R1) buys a count.

Nothing is asked of the hierarchy but clause (b) of `Tube.GridCoverSystem` — a leaf lies in
the node tube it is assigned to — read at the index `a`, which is what `ha : a ≤ N` is for.  In
particular `Tube.UniformTubeSet.boundedOverlap` is **not** used, and by
`note:ml1bootHomothetyOverlapInsufficient` it could not be; accordingly the bound carries no factor
`C_ds`, and no covering family and no hypothesis `δ ≤ θ/2` occurs.

The two restrictions on the container are hypotheses of the statement and are not concealed in the
constant.  That `V` be a `C θ`-tube is what `Kakeya.Tube.essDistinctTubesInDilate` needs, it
counting `C⁻¹ ρ`-tubes inside a dilate of a `ρ`-tube; the comparison `C = ρ(V)/θ` is owed by the
caller in the caller's own picture.  That `c + 4 ≤ C_n` is an artefact of
`Kakeya.Tube.essDistinctTubesInDilate` being stated at the single dilation factor `C_n` rather than
at a free one: a container with `c + 4 > C_n` would first have to be cut into `⌈(c+4)/C_n⌉` axial
translates, and **that covering is not carried out here**. -/
theorem card_neighbouringParents_le_of_essDistinct {ι : Type*} {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {N a : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu) (ha : a ≤ N)
    (hθ : 0 < gridScale δ N a) {C : NNReal} (hC : 1 ≤ C)
    (hCθ : C * gridScale δ N a ≤ 1) (V : Tube (C * gridScale δ N a) E)
    {c : ℝ} (hc : 1 ≤ c) (hcC : c + 4 ≤ Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))
    {K : ConvexSpaceBody E} (hK : K ≤ Tube.dilate V c)
    (hED : ((neighbouringParents 𝒰' a K : Finset ι) : Set ι).Pairwise fun l l' =>
      IsEssentiallyDistinct (𝒰'.cover.tube a l).carrier (𝒰'.cover.tube a l').carrier) :
    ((neighbouringParents 𝒰' a K).card : ENNReal)
      ≤ (Tube.comparableReplacement.C (Module.finrank ℝ E) C : ENNReal) := by
  classical
  let U : ι → Tube (C⁻¹ * (C * gridScale δ N a)) E :=
    fun l => (𝒰'.cover.tube a l).rescale (C⁻¹ * (C * gridScale δ N a))
  have hC0 : C ≠ 0 := (lt_of_lt_of_le zero_lt_one hC).ne'
  have hred : C⁻¹ * (C * gridScale δ N a) = gridScale δ N a := by
    calc
      C⁻¹ * (C * gridScale δ N a) = (C⁻¹ * C) * gridScale δ N a := by rw [mul_assoc]
      _ = gridScale δ N a := by rw [inv_mul_cancel₀ hC0, one_mul]
  have hcarU : ∀ l : ι, (U l).carrier = (𝒰'.cover.tube a l).carrier := by
    intro l
    dsimp [U]
    rw [hred]
    calc
      ((𝒰'.cover.tube a l).rescale (gridScale δ N a)).carrier
          = ⋃ z ∈ segment ℝ (𝒰'.cover.tube a l).x (𝒰'.cover.tube a l).y,
              Metric.closedBall z (gridScale δ N a) := by
            dsimp [Tube.rescale, Tube.mk']
      _ = (𝒰'.cover.tube a l).carrier := by
            rw [Tube.carrier_eq]
  have hUED : (↑(neighbouringParents 𝒰' a K) : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (U i).carrier (U j).carrier) := by
    intro i hi j hj hne
    simpa [hcarU] using hED hi hj hne
  have hrho0 : 0 < C * gridScale δ N a :=
    mul_pos (lt_of_lt_of_le zero_lt_one hC) hθ
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hUV : ∀ j ∈ neighbouringParents 𝒰' a K, (U j).carrier ⊆
      (Tube.dilate V (Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier := by
    intro j hj
    rw [neighbouringParents, Finset.mem_image] at hj
    rcases hj with ⟨i, hi, rfl⟩
    have hmem : i ∈ s' := (Finset.mem_filter.mp hi).1
    have hleafK : (T i).toConvexSpaceBody ≤ K := (Finset.mem_filter.mp hi).2
    have hleafV : (T i).toConvexSpaceBody ≤ Tube.dilate V c := le_trans hleafK hK
    have hTP : (T i).toConvexSpaceBody ≤
        (𝒰'.cover.tube a (𝒰'.cover.assign a i)).toConvexSpaceBody :=
      𝒰'.cover.le_tube_assign a ha i hmem
    have hin : (𝒰'.cover.tube a (𝒰'.cover.assign a i)).toConvexSpaceBody ≤
        Tube.dilate V (Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)) :=
      node_le_dilate_of_leaf_le hC hc0 hcC V (𝒰'.cover.tube a (𝒰'.cover.assign a i)) (T i)
        hTP hleafV
    have hsub : (𝒰'.cover.tube a (𝒰'.cover.assign a i)).carrier ⊆
        (Tube.dilate V (Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier :=
      SetLike.coe_subset_coe.mpr hin
    rw [hcarU (𝒰'.cover.assign a i)]
    exact hsub
  have hpack := Tube.essDistinctTubesInDilate (ρ := C * gridScale δ N a) hC hrho0 hCθ V
    (neighbouringParents 𝒰' a K) U hUED hUV
  exact hpack

/-! ### Step 5a, first half: the completed coarse fibre -/

/-- **The completed coarse fibre** `\widetilde t_τ(l)` (blueprint `lem:ml1bootFibreCompletion`).

For a retained fine node family `t_τ`, a coarse node `l` and a parameter `Λ`, the fine nodes of
`t_τ` whose node tube lies inside the *concentric radius-rescaling* `P_a(l)^{(Λ ρ_a)}` — same
core, radius `Λ ρ_a` — and **not** inside a homothety of `P_a(l)`.  The two dilates are different
operations and the distinction is load-bearing throughout Step 5a.

The blueprint displays this at `Λ = 2 C₀` with `C₀ = C_{ml1bootEnlargement}(3)`; `Λ` is free here
because `C₀` has no Lean definition.  See the module docstring. -/
noncomputable def completedFibre {ι : Type*} {δ : NNReal} {s' : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu) (a b : ℕ) (tτ : Finset ι) (Λ : NNReal)
    (l : ι) : Finset ι :=
  open scoped Classical in
  tτ.filter fun k => (𝒰'.cover.tube b k).toConvexSpaceBody ≤
    ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).toConvexSpaceBody

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **The completion contains the parent-map fibre** (blueprint `lem:ml1bootFibreCompletion`(a)).

If `ϖ_{b→a} k = l` then `P_b(k) ⊆ P_a(l)` by the parent clause of
`Kakeya.ml1Boot.IsCoarseNodeParents`, and `P_a(l) ⊆ P_a(l)^{(Λ ρ_a)}` because `Λ ≥ 1` and a
radius-rescaling to a larger radius contains the original tube (`Kakeya.Tube.le_rescale`). -/
theorem fibre_subset_completedFibre {ι : Type*} [DecidableEq ι] {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu) {pθ : ι → ι}
    (hcnp : IsCoarseNodeParents 𝒰' a b pθ) {tτ : Finset ι} (htτ : tτ ⊆ 𝒰'.cover.indexSet b)
    {Λ : NNReal} (hΛ : 1 ≤ Λ) (l : ι) :
    fibre tτ pθ l ⊆ completedFibre 𝒰' a b tτ Λ l := by
  classical
  intro k hk
  rw [fibre] at hk
  have hk_tτ : k ∈ tτ := (Finset.mem_filter.mp hk).1
  have hk_pθ : pθ k = l := (Finset.mem_filter.mp hk).2
  rw [completedFibre]
  rw [Finset.mem_filter]
  constructor
  · exact hk_tτ
  · have hle_parent := hcnp.parent.le_parent k (htτ hk_tτ)
    have hscale : gridScale δ N a ≤ Λ * gridScale δ N a :=
      le_mul_of_one_le_left' hΛ
    have hrescale : (𝒰'.cover.tube a (pθ k)).toConvexSpaceBody ≤
        ((𝒰'.cover.tube a (pθ k)).rescale (Λ * gridScale δ N a)).toConvexSpaceBody :=
      Tube.le_rescale (𝒰'.cover.tube a (pθ k)) hscale
    simpa [hk_pθ] using hle_parent.trans hrescale

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **The neighbouring parents of the completion are `O(1)` in number** (blueprint
`lem:ml1bootFibreCompletion`(b)).

`𝒫(l) = ϖ_{b→a} '' \widetilde t_τ(l)` has at most `M * Cu` members.  Every `k` in the completion
carries a leaf `i` — clause (a) of `Kakeya.ml1Boot.IsCoarseNodeParents`, `k` being a node of
`𝒰'_b` — and that leaf satisfies `T i ⊆ P_b(k) ⊆ P_a(l)^{(Λ ρ_a)}` and
`assign_a i = ϖ_{b→a} k`, by the characterising identity.  So `𝒫(l)` sits inside
`Kakeya.ml1Boot.neighbouringParents` at that container, and
`Kakeya.ml1Boot.card_neighbouringParents_le_of_cover` bounds the latter. -/
theorem card_completedFibreParents_le {ι : Type*} [DecidableEq ι] {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu) (ha : a ≤ N)
    {pθ : ι → ι} (hcnp : IsCoarseNodeParents 𝒰' a b pθ) {tτ : Finset ι}
    (htτ : tτ ⊆ 𝒰'.cover.indexSet b) {Λ : NNReal} (l : ι) {M : ℕ}
    (hcov : IsEnlargementCover s' T (gridScale δ N a)
      ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).toConvexSpaceBody M) :
    (((completedFibre 𝒰' a b tτ Λ l).image pθ).card : NNReal) ≤ M * Cu := by
  classical
  let C : Finset ι := completedFibre 𝒰' a b tτ Λ l
  let K : ConvexSpaceBody E := ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).toConvexSpaceBody
  have hsubset : C.image pθ ⊆ neighbouringParents 𝒰' a K := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨k, hk, hxk⟩
    have hk_mem : k ∈ (tτ.filter fun j => (𝒰'.cover.tube b j).toConvexSpaceBody ≤ K) := by
      simpa [C, completedFibre] using hk
    have hk_tτ : k ∈ tτ := (Finset.mem_filter.mp hk_mem).1
    have hk_K : (𝒰'.cover.tube b k).toConvexSpaceBody ≤ K := (Finset.mem_filter.mp hk_mem).2
    have hk_index : k ∈ 𝒰'.cover.indexSet b := htτ hk_tτ
    rcases hcnp.nodes_carry_leaf k hk_index with ⟨i, hi, hassign⟩
    have hmemfilter : i ∈ s'.filter (fun j => (T j).toConvexSpaceBody ≤ K) := by
      rw [Finset.mem_filter]
      constructor
      · exact hi
      · have hTi : (T i).toConvexSpaceBody ≤ (𝒰'.cover.tube b k).toConvexSpaceBody := by
          simpa [hassign] using 𝒰'.cover.le_tube_assign b hcnp.le_gridLen i hi
        exact hTi.trans hk_K
    rw [neighbouringParents]
    have h_is : 𝒰'.cover.assign a i = x := by
      calc
        𝒰'.cover.assign a i = pθ (𝒰'.cover.assign b i) := (hcnp.assign_comp i hi).symm
        _ = pθ k := by rw [hassign]
        _ = x := hxk
    rw [← h_is]
    letI : DecidableEq ι := Classical.decEq ι
    exact Finset.mem_image.mpr ⟨i, hmemfilter, rfl⟩
  have hc1 : ((C.image pθ).card : NNReal) ≤ ((neighbouringParents 𝒰' a K).card : NNReal) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hc2 : ((neighbouringParents 𝒰' a K).card : NNReal) ≤ M * Cu := by
    simpa [K] using card_neighbouringParents_le_of_cover 𝒰' ha hcov
  simpa [C] using (le_trans hc1 hc2)

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **The completion is `O(Λ_load N_m)` in size** (blueprint `lem:ml1bootFibreCompletion`(c)).

Every `k` in the completion lies in the fibre of its own parent, so the completion is covered by
the fibres over `𝒫(l)`; each of those has at most `Λ_load N_m` members, every parent occurring
lying in `t_θ` by `hpθ`, and there are at most `M * Cu` of them by
`Kakeya.ml1Boot.card_completedFibreParents_le`.

`N_m` is a **cardinality** of retained fine nodes.  It is not the `D_m` of
`Kakeya.ml1Boot.densityIn_le_of_neighbouringParents`, which is a **density** of unrefined ones,
and the two are related by nothing proved here (blueprint `note:ml1bootStep5aTwoLoads`).

Only the upper half of the blueprint's two-sided load bracket is taken; see the module
docstring. -/
theorem card_completedFibre_le {ι : Type*} [DecidableEq ι] {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {N a b : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu) (ha : a ≤ N)
    {pθ : ι → ι} (hcnp : IsCoarseNodeParents 𝒰' a b pθ) {tτ tθ : Finset ι}
    (htτ : tτ ⊆ 𝒰'.cover.indexSet b) (hpθ : ∀ k ∈ tτ, pθ k ∈ tθ) {Λ : NNReal} (l : ι) {M : ℕ}
    (hcov : IsEnlargementCover s' T (gridScale δ N a)
      ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).toConvexSpaceBody M)
    {Nm Λload : NNReal}
    (hload : ∀ l' ∈ tθ, ((fibre tτ pθ l').card : NNReal) ≤ Λload * Nm) :
    ((completedFibre 𝒰' a b tτ Λ l).card : NNReal) ≤ Λload * (M * Cu) * Nm := by
  classical
  let C : Finset ι := completedFibre 𝒰' a b tτ Λ l
  let P : Finset ι := C.image pθ
  have hsub : C ⊆ P.biUnion (fun l' => fibre tτ pθ l') := by
    intro k hk
    have hk_mem : k ∈ (tτ.filter fun j => (𝒰'.cover.tube b j).toConvexSpaceBody ≤
        ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).toConvexSpaceBody) := by
      simpa [C, completedFibre] using hk
    have hk_tτ : k ∈ tτ := (Finset.mem_filter.mp hk_mem).1
    rw [Finset.mem_biUnion]
    refine ⟨pθ k, ?hp, ?hfk⟩
    · dsimp [P]
      rw [Finset.mem_image]
      exact ⟨k, hk, rfl⟩
    · rw [fibre, Finset.mem_filter]
      exact ⟨hk_tτ, rfl⟩
  have hcard_le_sum : (C.card : NNReal) ≤ (∑ l' ∈ P, (fibre tτ pθ l').card : NNReal) := by
    exact_mod_cast (le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le))
  have hsum_le : (∑ l' ∈ P, (fibre tτ pθ l').card : NNReal) ≤ P.card * (Λload * Nm) := by
    calc
      (∑ l' ∈ P, (fibre tτ pθ l').card : NNReal) ≤ ∑ l' ∈ P, (Λload * Nm) := by
        exact Finset.sum_le_sum (by
          intro l' hl'
          have hl'_tθ : l' ∈ tθ := by
            dsimp [P] at hl'
            rw [Finset.mem_image] at hl'
            rcases hl' with ⟨k, hkC, rfl⟩
            have hk_mem : k ∈ (tτ.filter fun j => (𝒰'.cover.tube b j).toConvexSpaceBody ≤
                ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).toConvexSpaceBody) := by
              simpa [C, completedFibre] using hkC
            exact hpθ k (Finset.mem_filter.mp hk_mem).1
          exact hload l' hl'_tθ)
      _ = P.card * (Λload * Nm) := by
        rw [Finset.sum_const]
        simp [nsmul_eq_mul]
  have hcard_le : (C.card : NNReal) ≤ P.card * (Λload * Nm) := hcard_le_sum.trans hsum_le
  have hP : (P.card : NNReal) ≤ M * Cu := by
    simpa [P] using card_completedFibreParents_le 𝒰' ha hcnp htτ l hcov
  have hP_mul : P.card * (Λload * Nm) ≤ (M * Cu) * (Λload * Nm) := by
    exact mul_le_mul_of_nonneg_right hP (by positivity)
  calc
    (C.card : NNReal) ≤ P.card * (Λload * Nm) := hcard_le
    _ ≤ (M * Cu) * (Λload * Nm) := hP_mul
    _ = Λload * (M * Cu) * Nm := by
      ring

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **The nodes of a member nest along the grid** (blueprint `lem:nodeNestingAcrossGrid`).

If `a ≤ b ≤ N` then the `b`-node of a member `i` lies inside its `a`-node,
`P_b(assign_b i) ≤ P_a(assign_a i)`.  This is the chain of
`Tube.GridCoverSystem.tube_nested` from `a` up to `b`, threaded by
`Tube.GridCoverSystem.assign_mem` along the way.  A member of the threaded class
appears at every index between `a` and `b`, so the chain connects the two endpoints. -/
theorem node_nesting {ι : Type*} {δ : NNReal} {s' : Finset ι} {T : ι → Tube δ E}
    {N a b : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu) (hab : a ≤ b) (hb : b ≤ N)
    (i : ι) (hi : i ∈ s') :
    (𝒰'.cover.tube b (𝒰'.cover.assign b i)).toConvexSpaceBody ≤
      (𝒰'.cover.tube a (𝒰'.cover.assign a i)).toConvexSpaceBody := by
  have hcd : ∀ (m d : ℕ), m + d ≤ b → ∀ j ∈ s',
      (𝒰'.cover.tube (m + d) (𝒰'.cover.assign (m + d) j)).toConvexSpaceBody ≤
        (𝒰'.cover.tube m (𝒰'.cover.assign m j)).toConvexSpaceBody := by
    intro m d
    induction d with
    | zero => intro h j hj; exact le_rfl
    | succ d ih =>
        intro h j hj
        have hmN : (m + d) + 1 ≤ N := by exact le_trans (by omega) hb
        rw [show m + (d + 1) = (m + d) + 1 by omega]
        have hstep := 𝒰'.cover.tube_nested (m + d) hmN j hj
        have htail := ih (by omega) j hj
        exact le_trans hstep htail
  have hle : a + (b - a) ≤ b := by omega
  have h' := hcd a (b - a) hle i hi
  rw [Nat.add_sub_cancel' hab] at h'
  exact h'

/-! ### Step 5a, second half: the local density bound (5.10a) at the unrefined family -/

omit [Nontrivial E] in
/-- **The density estimate of (5.10a), with the parent count taken as a hypothesis** (blueprint
`lem:ml1bootLocalDensityCore`).

For every convex body `K'` inside an **arbitrary** container `big`, the density of the
**unrefined** level-`b` node family in `K'` is at most
`Λ_Δ · M₀ · δ ^ (-ε') · (θ/τ) ^ (η m) · D_m`, where `M₀` is any bound on the cardinality of
`Kakeya.ml1Boot.neighbouringParents 𝒰' a big`.

*This is (5.10a) with the parent count removed from it*, and it is the common core of the two
routes to (5.10a) in this development, stated so that the density argument is written once.
Nothing in it names a covering family, a tube, a homothety factor, essential distinctness or
`Tube.UniformTubeSet.boundedOverlap`; the container enters only through
`Kakeya.ml1Boot.neighbouringParents` and through `hK'`, and no property of its *shape* is read.
The whole difference between the two routes is which supplier is used for `M₀`:

* `Kakeya.ml1Boot.densityIn_le_of_neighbouringParents` below is this lemma at `M₀ = M · Cu`, the
  count coming from `Kakeya.ml1Boot.card_neighbouringParents_le_of_cover` at a covering family
  supplied for `big`;
* the essential-distinctness route is this lemma at
  `M₀ = Kakeya.Tube.comparableReplacement.C n C`, the count coming from
  `Kakeya.ml1Boot.card_neighbouringParents_le_of_essDistinct` at a homothety container under (R1).

`M₀` is a hypothesis and not a constant attached to this lemma.  It is deliberately not written
`M`: the `M` of `Kakeya.ml1Boot.IsEnlargementCover` is the cardinality of a covering family of
tubes, whereas `M₀` bounds a set of *nodes*, and the first instance above is at `M₀ = M · Cu` and
not at `M₀ = M`.  The blueprint's finiteness half of the hypothesis needs no counterpart:
`Kakeya.ml1Boot.neighbouringParents` is a `Finset`.

The proof: a level-`b` node `k'` inside `K'` carries a leaf `i` (`hleaf`), whose coarse node
`l'' = assign_a i` is then a neighbouring parent of `l`, and whose node tubes nest,
`P_b(k') ⊆ P_a(l'')`, by `Tube.GridCoverSystem.tube_nested` chained from `a` to `b` — this
is where `hblock.coarse_lt_fine` is read, and `hblock.fine_le` is what puts `a` and `b` on the
grid, giving `assign_mem a`.  So
the containment families `𝒩_b(P_a(l''))` cover everything contributing at `K'`, and
`Kakeya.densityIn_le_sum_densityIn_of_cover` splits the density into at most `M₀` terms — this is
where, and only where, `hcard` is read.  At each parent,
`Kakeya.densityIn_le_densityIn_of_forall_le` moves the test body from `K'` to `K' ⊓ P_a(l'')`, and
`ConvexSpaceBody.isFrostmanIn_frostmanConstant` trades that for the Frostman constant of the
containment family in `P_a(l'')`.  It must be `ConvexSpaceBody.frostmanConstant` and not
`Kakeya.frostmanConstIn`: `StickyKakeya.IsFrostmanDividingBlock.frostman_nodes`, the clause that
bounds it by `Cu · totalLoss · (θ/τ) ^ (η m) ≤ δ ^ (-ε') · (θ/τ) ^ (η m)` using `hloss`, is
spelled with the former.  (The two are `rfl`-equal by
`Kakeya.frostmanConstIn_eq_frostmanConstant`, so the choice is one of spelling only.)

`hloss` is the explicit form of the blueprint's "for all sufficiently small `δ`", and is what
`Kakeya.ml1Boot.eventually_dichotomyLoss_le` supplies.

The hypotheses of `Kakeya.ml1Boot.card_completedFibre_le` are **not** assumed, and `(D_m, Λ_Δ)`
are **not** the `(N_m, Λ_load)` of that lemma: the two speak about different families (unrefined
containment families here, a retained parent-map fibre there) and different quantities (a density
here, a cardinality there).  No parent map occurs in this statement at all. -/
theorem densityIn_le_of_card_neighbouringParents {ι : Type u} {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {Cu : NNReal} {Kds cds a b m : ℕ} {p : Params} {ε' : ℝ}
    (𝒰' : UniformTubeSet s' T (ssfGridLen δ) Cu)
    (hblock : IsFrostmanDividingBlock 𝒰' Cu Kds cds p.η p.ε a b m p.N)
    (hloss : (Cu : ENNReal) * totalLoss Cu Kds cds δ ≤ (δ : ENNReal) ^ (-ε'))
    (hleaf : ∀ k ∈ 𝒰'.cover.indexSet b, ∃ i ∈ s', 𝒰'.cover.assign b i = k)
    (big : ConvexSpaceBody E) {M₀ : ENNReal}
    (hcard : ((neighbouringParents 𝒰' a big).card : ENNReal) ≤ M₀)
    {Dm ΛΔ : ENNReal}
    (hdens : ∀ l'' ∈ neighbouringParents 𝒰' a big,
      densityIn (𝒰'.nodesUnder b a l'') (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
          (𝒰'.cover.tube a l'').toConvexSpaceBody ≤ ΛΔ * Dm)
    {K' : ConvexSpaceBody E}
    (hK' : K' ≤ big) :
    densityIn (𝒰'.cover.indexSet b) (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K'
      ≤ ΛΔ * M₀ * (δ : ENNReal) ^ (-ε') *
          ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m) * Dm := by
  classical
  have hb_le : b ≤ ssfGridLen δ := hblock.fine_le
  have ha_le : a ≤ ssfGridLen δ := by
    exact le_trans (le_of_lt hblock.coarse_lt_fine) hb_le
  set W : ι → ConvexSpaceBody E := fun k => (𝒰'.cover.tube b k).toConvexSpaceBody
  set P : Finset ι := neighbouringParents 𝒰' a big
  set CF : ENNReal := (δ : ENNReal) ^ (-ε') * ENNReal.ofReal
      (((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m)
  -- Step 1: the containment families cover the contributing part of the level-`b` nodes.
  have hcover : ∀ k' ∈ 𝒰'.cover.indexSet b, W k' ≤ K' →
      ∃ l'' ∈ P, k' ∈ 𝒰'.nodesUnder b a l'' := by
    intro k' hk' hWk'
    rcases hleaf k' hk' with ⟨i, hi, heq⟩
    refine ⟨𝒰'.cover.assign a i, ?_, ?_⟩
    · -- the leaf's `a`-node is a neighbouring parent of `l`
      have hTi : (T i).toConvexSpaceBody ≤ K' := by
        calc
          (T i).toConvexSpaceBody ≤ (𝒰'.cover.tube b (𝒰'.cover.assign b i)).toConvexSpaceBody :=
            𝒰'.cover.le_tube_assign b hb_le i hi
          _ = W (𝒰'.cover.assign b i) := rfl
          _ = W k' := by rw [heq]
          _ ≤ K' := hWk'
      have hTiK : (T i).toConvexSpaceBody ≤ big := le_trans hTi hK'
      change (𝒰'.cover.assign a i) ∈ neighbouringParents 𝒰' a big
      rw [neighbouringParents, Finset.mem_image]
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hTiK⟩, rfl⟩
    · -- `k'` lies inside the `a`-node tube of its leaf
      have hchain := node_nesting 𝒰' (le_of_lt hblock.coarse_lt_fine) hb_le i hi
      apply Finset.mem_filter.mpr
      constructor
      · exact hk'
      · simpa [heq] using hchain
  -- Step 2: bound the density at each neighbouring parent.
  have hper : ∀ l'' ∈ P, densityIn (𝒰'.nodesUnder b a l'') W K' ≤ CF * (ΛΔ * Dm) := by
    intro l'' h0P
    have h0idx : l'' ∈ 𝒰'.cover.indexSet a := by
      unfold P at h0P
      rcases Finset.mem_image.mp h0P with ⟨i, hiF, heq⟩
      have hip : i ∈ s' := (Finset.mem_filter.mp hiF).1
      have has : 𝒰'.cover.assign a i ∈ 𝒰'.cover.indexSet a :=
        𝒰'.cover.assign_mem a ha_le i hip
      simpa [heq] using has
    let Q : Finset ι := (𝒰'.nodesUnder b a l'').filter fun k => W k ≤ K'
    by_cases hQe : Q = ∅
    · have hzero : densityIn (𝒰'.nodesUnder b a l'') W K' = 0 := by
        rw [densityIn]
        rw [show (𝒰'.nodesUnder b a l'').filter (fun k => W k ≤ K') = ∅ by simpa [Q] using hQe]
        simp
      rw [hzero]
      exact zero_le
    · have hk0 : ∃ k, k ∈ Q := Finset.nonempty_iff_ne_empty.mpr hQe
      rcases hk0 with ⟨k0, hk0Q⟩
      have hk0N : k0 ∈ 𝒰'.nodesUnder b a l'' := (Finset.mem_filter.mp hk0Q).1
      have hk0le : W k0 ≤ K' := (Finset.mem_filter.mp hk0Q).2
      have hne : (K'.carrier ∩ (𝒰'.cover.tube a l'').toConvexSpaceBody.carrier).Nonempty := by
        have h1 : (W k0).carrier ⊆ K'.carrier := SetLike.coe_subset_coe.mpr hk0le
        have h2 : W k0 ≤ (𝒰'.cover.tube a l'').toConvexSpaceBody :=
          (Finset.mem_filter.mp hk0N).2
        have h3 : (W k0).carrier ⊆ (𝒰'.cover.tube a l'').toConvexSpaceBody.carrier :=
          SetLike.coe_subset_coe.mpr h2
        exact (W k0).nonempty'.mono (Set.subset_inter h1 h3)
      let K'' : ConvexSpaceBody E :=
        ConvexSpaceBody.inter K' (𝒰'.cover.tube a l'').toConvexSpaceBody hne
      have hK''le : K'' ≤ K' := by
        change K''.carrier ⊆ K'.carrier
        dsimp [K'']
        rw [ConvexSpaceBody.inter_carrier]
        exact Set.inter_subset_left
      have hK''le2 : K'' ≤ (𝒰'.cover.tube a l'').toConvexSpaceBody := by
        change K''.carrier ⊆ (𝒰'.cover.tube a l'').toConvexSpaceBody.carrier
        dsimp [K'']
        rw [ConvexSpaceBody.inter_carrier]
        exact Set.inter_subset_right
      have hLema : densityIn (𝒰'.nodesUnder b a l'') W K' ≤
          densityIn (𝒰'.nodesUnder b a l'') W K'' := by
        apply Kakeya.densityIn_le_densityIn_of_forall_le (𝒰'.nodesUnder b a l'') W
        · exact hK''le
        · intro k hkN hkK'
          apply SetLike.coe_subset_coe.mp
          have hA : (W k).carrier ⊆ K'.carrier := SetLike.coe_subset_coe.mpr hkK'
          have hB : (W k).carrier ⊆ (𝒰'.cover.tube a l'').toConvexSpaceBody.carrier := by
            have h : W k ≤ (𝒰'.cover.tube a l'').toConvexSpaceBody :=
              (Finset.mem_filter.mp hkN).2
            exact SetLike.coe_subset_coe.mpr h
          calc
            (W k).carrier ⊆ K'.carrier ∩ (𝒰'.cover.tube a l'').toConvexSpaceBody.carrier := Set.subset_inter hA hB
            _ = K''.carrier := by simp [K'', ConvexSpaceBody.inter_carrier]
      have hfrost : densityIn (𝒰'.nodesUnder b a l'') W K'' ≤
          ConvexSpaceBody.frostmanConstant (𝒰'.nodesUnder b a l'') W
            (𝒰'.cover.tube a l'').toConvexSpaceBody *
          densityIn (𝒰'.nodesUnder b a l'') W (𝒰'.cover.tube a l'').toConvexSpaceBody :=
        (ConvexSpaceBody.isFrostmanIn_frostmanConstant (s := 𝒰'.nodesUnder b a l'') (W := W)
          (K := (𝒰'.cover.tube a l'').toConvexSpaceBody)) K'' hK''le2
      have hfrostb : ConvexSpaceBody.frostmanConstant (𝒰'.nodesUnder b a l'') W
              (𝒰'.cover.tube a l'').toConvexSpaceBody ≤
            (Cu : ENNReal) * totalLoss Cu Kds cds δ * ENNReal.ofReal
              (((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m) :=
        hblock.frostman_nodes l'' h0idx
      have hdensb : densityIn (𝒰'.nodesUnder b a l'') W (𝒰'.cover.tube a l'').toConvexSpaceBody ≤
            ΛΔ * Dm :=
        hdens l'' h0P
      have hcombine : ConvexSpaceBody.frostmanConstant (𝒰'.nodesUnder b a l'') W
              (𝒰'.cover.tube a l'').toConvexSpaceBody *
            densityIn (𝒰'.nodesUnder b a l'') W (𝒰'.cover.tube a l'').toConvexSpaceBody ≤
            (Cu : ENNReal) * totalLoss Cu Kds cds δ * ENNReal.ofReal
              (((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m) *
            (ΛΔ * Dm) :=
        by
        gcongr
      have hAbs : (Cu : ENNReal) * totalLoss Cu Kds cds δ * ENNReal.ofReal
              (((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m) *
            (ΛΔ * Dm) ≤
            (δ : ENNReal) ^ (-ε') * ENNReal.ofReal
              (((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m) *
            (ΛΔ * Dm) := by
        gcongr
      calc
        densityIn (𝒰'.nodesUnder b a l'') W K' ≤ densityIn (𝒰'.nodesUnder b a l'') W K'' := hLema
        _ ≤ ConvexSpaceBody.frostmanConstant (𝒰'.nodesUnder b a l'') W
              (𝒰'.cover.tube a l'').toConvexSpaceBody *
            densityIn (𝒰'.nodesUnder b a l'') W (𝒰'.cover.tube a l'').toConvexSpaceBody := hfrost
        _ ≤ (Cu : ENNReal) * totalLoss Cu Kds cds δ * ENNReal.ofReal
              (((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m) *
            (ΛΔ * Dm) := hcombine
        _ ≤ (δ : ENNReal) ^ (-ε') * ENNReal.ofReal
              (((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m) *
            (ΛΔ * Dm) := by
            gcongr
        _ = CF * (ΛΔ * Dm) := by simp [CF]
  -- Step 3: sum over the neighbouring parents.
  have hsplit : densityIn (𝒰'.cover.indexSet b) W K' ≤
      ∑ l'' ∈ P, densityIn (𝒰'.nodesUnder b a l'') W K' := by
    refine Kakeya.densityIn_le_sum_densityIn_of_cover (𝒰'.cover.indexSet b) W K' P
      (fun l'' => 𝒰'.nodesUnder b a l'') ?_
    · intro k hk hkwk
      exact hcover k hk hkwk
  have hsumle : (∑ l'' ∈ P, densityIn (𝒰'.nodesUnder b a l'') W K') ≤
      ∑ l'' ∈ P, (CF * (ΛΔ * Dm)) := by
    exact Finset.sum_le_sum (fun q hq => hper q hq)
  have hsum : (∑ l'' ∈ P, (CF * (ΛΔ * Dm))) = (P.card : ENNReal) * (CF * (ΛΔ * Dm)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  calc
    densityIn (𝒰'.cover.indexSet b) W K' ≤ (P.card : ENNReal) * (CF * (ΛΔ * Dm)) := by
      exact hsplit.trans (hsumle.trans (by simp [hsum]))
    _ ≤ M₀ * (CF * (ΛΔ * Dm)) := by
      gcongr
    _ = ΛΔ * M₀ * (δ : ENNReal) ^ (-ε') *
          ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m) * Dm := by
      simp only [CF]
      ring

omit [Nontrivial E] in
/-- **The local density bound (5.10a)** (blueprint `lem:ml1bootLocalDensityUnrefined`).

For every convex body `K'` inside an **arbitrary** container `big`, the density of the
**unrefined** level-`b` node family in `K'` is at most
`Λ_Δ · (M Cu) · δ ^ (-ε') · (θ/τ) ^ (η m) · D_m`.

The container is arbitrary and not a concentric rescaling `P_a(l)^{(Λ ρ_a)}` of a coarse node.
It enters only through the covering hypothesis `hcov`, through `Kakeya.ml1Boot.neighbouringParents`
and through `hK'`, and the proof uses nothing else about it, so binders naming `l` and `Λ` would
name `big` and nothing more; the displayed statement is the instance
`big = ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ (ssfGridLen δ) a)).toConvexSpaceBody`.
This is what lets a consumer whose region is *not* of that shape — a homothety, as the repaired
plank enlargement `Kakeya.ml1Boot.subset_dilate_rescale_of_thickness_le` produces — read the bound
at its own region (blueprint `note:ml1bootEnlargementTubeStatus`).

This is `Kakeya.ml1Boot.densityIn_le_of_card_neighbouringParents` at `M₀ = M · Cu`, the cardinality
hypothesis supplied by `Kakeya.ml1Boot.card_neighbouringParents_le_of_cover`; `hcov` is read there
and nowhere else, and `hblock.fine_le` with `hblock.coarse_lt_fine` supply the `a ≤ N` that lemma
asks for.  The density estimate itself is written once, in the core, and is not repeated here.

`hloss` is the explicit form of the blueprint's "for all sufficiently small `δ`", and is what
`Kakeya.ml1Boot.eventually_dichotomyLoss_le` supplies.

The hypotheses of `Kakeya.ml1Boot.card_completedFibre_le` are **not** assumed, and `(D_m, Λ_Δ)`
are **not** the `(N_m, Λ_load)` of that lemma: the two speak about different families (unrefined
containment families here, a retained parent-map fibre there) and different quantities (a density
here, a cardinality there).  No parent map occurs in this statement at all. -/
theorem densityIn_le_of_neighbouringParents {ι : Type u} {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {Cu : NNReal} {Kds cds a b m : ℕ} {p : Params} {ε' : ℝ}
    (𝒰' : UniformTubeSet s' T (ssfGridLen δ) Cu)
    (hblock : IsFrostmanDividingBlock 𝒰' Cu Kds cds p.η p.ε a b m p.N)
    (hloss : (Cu : ENNReal) * totalLoss Cu Kds cds δ ≤ (δ : ENNReal) ^ (-ε'))
    (hleaf : ∀ k ∈ 𝒰'.cover.indexSet b, ∃ i ∈ s', 𝒰'.cover.assign b i = k)
    (big : ConvexSpaceBody E) {M : ℕ}
    (hcov : IsEnlargementCover s' T (gridScale δ (ssfGridLen δ) a) big M)
    {Dm ΛΔ : ENNReal}
    (hdens : ∀ l'' ∈ neighbouringParents 𝒰' a big,
      densityIn (𝒰'.nodesUnder b a l'') (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
          (𝒰'.cover.tube a l'').toConvexSpaceBody ≤ ΛΔ * Dm)
    {K' : ConvexSpaceBody E}
    (hK' : K' ≤ big) :
    densityIn (𝒰'.cover.indexSet b) (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K'
      ≤ ΛΔ * (M * Cu : NNReal) * (δ : ENNReal) ^ (-ε') *
          ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m) * Dm := by
  have ha_le : a ≤ ssfGridLen δ :=
    le_trans (le_of_lt hblock.coarse_lt_fine) hblock.fine_le
  refine densityIn_le_of_card_neighbouringParents 𝒰' hblock hloss hleaf big ?_ hdens hK'
  exact_mod_cast card_neighbouringParents_le_of_cover 𝒰' ha_le hcov

end ml1Boot

end Kakeya
