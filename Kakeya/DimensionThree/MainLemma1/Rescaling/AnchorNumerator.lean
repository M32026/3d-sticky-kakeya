/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.FibreCompletion
public import Kakeya.DimensionThree.MainLemma1.Rescaling.DensityTransfer
public import Kakeya.DimensionThree.MainLemma1.TwoLoads

/-!
# Main Lemma 1, Case (ii): the local density bound at a homothety container, and the anchor

Blueprint `lem:ml1bootLocalDensityEssDistinct`, `lem:ml1bootAnchorFrostmanEssDistinct`,
`lem:ml1bootAnchorFrostmanFromLoad` and `lem:ml1bootAnchorFrostmanEssDistinctFromLoad` and
`lem:ml1bootAnchorFrostmanFromUniformity`.  This
module contains five statements, and **all five are instances and none is an argument**.

* `Kakeya.ml1Boot.densityIn_le_of_essDistinctParents` (5.10a) is
  `Kakeya.ml1Boot.densityIn_le_of_card_neighbouringParents` — the density core of
  `Kakeya/DimensionThree/MainLemma1/FibreCompletion.lean`, blueprint `lem:ml1bootLocalDensityCore` —
  read at

  ```
  M₀ = Kakeya.Tube.comparableReplacement.C (Module.finrank ℝ E) C,
  ```

  with its cardinality hypothesis supplied by
  `Kakeya.ml1Boot.card_neighbouringParents_le_of_essDistinct`.  **No step of the density argument is
  repeated here**, and in particular nothing of the proof of
  `Kakeya.ml1Boot.densityIn_le_of_neighbouringParents` is copied: that lemma is a *sibling* instance
  of the same core at `M₀ = M · C_ds`, and it is neither edited nor weakened nor re-derived by
  anything in this file.
* `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_essDistinctParents` (5.10b) is the wiring: it is
  `Kakeya.ml1Boot.frostmanConstIn_anchor_le` of
  `Kakeya/DimensionThree/MainLemma1/Rescaling/DensityTransfer.lean` — blueprint
  `lem:ml1bootAnchorFrostmanUpper` — with its numerator hypothesis `hnum` discharged by the first
  statement of this file, read at `big = K` and at the family
  `𝕍 = (P_b k)_{k ∈ 𝒰'_b}` of `τ`-tubes.  Nothing else changes: the *denominator* side
  (`t`, `W`, `L`) is assumed here exactly as it is assumed there.

* `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_load` (blueprint `lem:ml1bootAnchorFrostmanFromLoad`)
  is the same wiring on the **covering route**: it is
  `Kakeya.ml1Boot.frostmanConstIn_anchor_le` with its numerator hypothesis `hnum` discharged by
  `Kakeya.ml1Boot.densityIn_le_of_load` of `Kakeya/DimensionThree/MainLemma1/TwoLoads.lean`, again
  read at `big = K` and at the family `𝕍 = (P_b k)_{k ∈ 𝒰'_b}` of `τ`-tubes.  **It carries no
  essential-distinctness hypothesis at all**: its container is the *concentric rescaling*
  `P_a(l) ^ (Λ ρ_a)` and not a homothety, so blueprint
  `note:ml1bootHomothetyOverlapInsufficient` — which is what forces (R1) on the other route, and
  which cannot be removed there — **does not apply, and this statement misses that obstruction
  entirely**.  Neither (R1) nor either of the two container restrictions `C θ ≤ 1`, `c + 4 ≤ C_n`
  occurs in it.  That is the whole advantage of this route, and it is *not* an assertion that the
  other route is dispensable: the other route's container is of the shape the eventual Step 5c
  consumer is stated at, and this one's is not.
* `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_essDistinctParents_of_load` (blueprint
  `lem:ml1bootAnchorFrostmanEssDistinctFromLoad`) is the cheaper assembly: it is the *second*
  statement of this file — which is neither edited nor re-proved by it — read at `Λ_Δ = 1` and at
  `D_m` the right-hand side of `Kakeya.ml1Boot.densityIn_nodesUnder_le_of_load`, with the quantifier
  supplied by `Kakeya.ml1Boot.neighbouringParents_subset_indexSet`.  **No new anchor lemma is needed
  and none is written.**  What it discharges is exactly one bullet — the *density* bullet `hdens` —
  and **it leaves (R1) `hED`, the two container restrictions `C θ ≤ 1` and `c + 4 ≤ C_n`, and the
  denominator `L` exactly where they were**: `hED` is still a hypothesis with no supplier, the two
  restrictions are still carried, `L` is still assumed, and the transport to the Step 5c anchor is
  still not performed.
* `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_uniformity` (blueprint
  `lem:ml1bootAnchorFrostmanFromUniformity`) is the third statement of this file — which it neither
  edits nor re-derives — with its **load hypothesis deleted**: `hload` is discharged by
  `Kakeya.ml1Boot.card_coarseFibre_le_branchingRatio` of
  `Kakeya/DimensionThree/MainLemma1/TwoLoads.lean` at the pair `N_m = N_a/N_b`,
  `Λ_load = C_ds ^ 3`, at the cost of the one new hypothesis `0 < N_b`.  **No import edge is needed**,
  this file already importing `TwoLoads.lean` for the two assemblies above.  What it discharges is
  exactly one item of blueprint `note:ml1bootAnchorFromLoadStatus` — the load pair, item (iv) — and
  **only at the unrefined fibres**: for the retained families blueprint `lem:ml1bootFibreCompletion`
  still has no supplier, `Λ_load = C_ds ^ 3` is a power of the hierarchy's uniformity constant and
  not absolute so the budget question is moved and not answered, and **the denominator `L` is still
  assumed**.

Those statements are why this file imports all three of
`Kakeya/DimensionThree/MainLemma1/FibreCompletion.lean`, where the parent-count and density-core
material lives, `Kakeya/DimensionThree/MainLemma1/Rescaling/DensityTransfer.lean`, where
`Kakeya.ml1Boot.frostmanConstIn_anchor_le` lives, and — the one import edge the two load-route
assemblies cost — `Kakeya/DimensionThree/MainLemma1/TwoLoads.lean`, where the two-loads relation and
the load-fed (5.10a) live and which itself publicly imports
`Kakeya/DimensionThree/MainLemma1/EnlargementCover.lean`.  None of those files reaches this one or
either of the others, so there is no import cycle.

## Why a separate instance is needed at all

`Kakeya.ml1Boot.densityIn_le_of_neighbouringParents` already admits an *arbitrary* container, so it
can be read at the homothety-shaped region the repaired plank enlargement produces.  What it cannot
do there is give an **absolute** value to the cardinality `M` of the covering family its bound is
stated with: the only supplier of an absolute `M`, `Kakeya.ml1Boot.IsEnlargementCover` via
`Tube.UniformTubeSet.boundedOverlap`, works at a *concentric rescaling* of a coarse node
tube and not at a homothety.  That is the longitudinal-confinement gap of blueprint
`note:ml1bootEnlargementTubeStatus`.  This file replaces the quantity `M · C_ds` by a constant
depending on nothing but the ambient dimension and the shape parameter `C` of the container — at
the price of the essential-distinctness hypothesis `hED`.

## All five statements are conditional and none may be cited as unconditional

Three of the five carry `hED`, which is caution (R1) of blueprint `subsec:ml1bootHomothetyParents`:
it **has no supplier in this development**, and in the configuration of blueprint
`note:ml1bootHomothetyOverlapInsufficient` it fails already for the nodes reached inside a single
container.  What those lemmas say is that (R1) buys an absolute numerator for (5.10b); they are not
evidence that an absolute numerator is available.  The third statement,
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_load`, carries no `hED` — its container is a concentric
rescaling — but is conditional for the other reason, and so is the fifth,
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_uniformity`.

That other reason is common to the four that bound `C_F`, and none of them touches it: the
denominator `L` is *assumed* exactly as it is assumed in
`Kakeya.ml1Boot.frostmanConstIn_anchor_le`, nothing in this development supplies one, and that is
what still stands between these bounds and an unconditional (5.10b).  Blueprint
`note:ml1bootAnchorFromLoadStatus` itemizes the four things owed; `L` is the one of which nothing is
written.

## On the size of the signatures

Each binder list is the *union* of the hypotheses of the lemmas being composed, and the blueprint
prescribes exactly that composition.

For `Kakeya.ml1Boot.densityIn_le_of_essDistinctParents`: three groups come from the core
(`hblock`, `hloss`, `hleaf`); eight describe the container and its shape
(`hθ`, `hC`, `hCθ`, `V`, `hc`, `hcC`, `B`, `hB`) and are read only by
`Kakeya.ml1Boot.card_neighbouringParents_le_of_essDistinct`; one is (R1) (`hED`); and the last two
(`hdens`, `hK'`) are the core's density input and its test body.  None of them names a
mathematical concept shared with the others, so none is bundled: bundling here would invent a
container for an unrelated group, which the blueprint explicitly declines to do — the container's
*shape* hypotheses belong to the parent count and the density hypotheses belong to the core, and
the whole point of the split is that the core reads no shape.

`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_essDistinctParents` carries those same binders — minus
`hK'`, which is the bound variable of the numerator hypothesis it discharges — together with the
denominator group of `Kakeya.ml1Boot.frostmanConstIn_anchor_le`, which is passed through unchanged
and unread.  That group *does* name a mathematical concept — it is the block `t`, its plank `W` and
the lower density bound `L` on it — and it **is** now bundled, as
`Kakeya.ml1Boot.IsAnchorDenominator` of
`Kakeya/DimensionThree/MainLemma1/Rescaling/DensityTransfer.lean`, so that the four assemblies of
this file carry it as the single binder `hanch` alongside `hdim`, `hap0`, `hab`.

The two load-route assemblies are the same union at a different numerator.
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_load` is that denominator bundle together with the
binders of `Kakeya.ml1Boot.densityIn_le_of_load` (`hCu`, `𝒰'`, `hblock`, `hloss`, `hleaf`, `hcnp`,
`hδ0`, `hδ1`, `hδ`, `Λ`, `l`, `hload`) and the container `K`, `hK`; it carries **no** shape group,
which is the whole point of the covering route.
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_essDistinctParents_of_load` is the shape group *plus*
the load group, because it feeds a homothety container from a load pair.

The bundling is existing at **all eight** sites that displayed the group: the four assemblies of this
file; `Kakeya.ml1Boot.frostmanConstIn_anchor_le` itself;
`Kakeya.ml1Boot.plankWidth_le_of_anchor`, which carried the group as arrows inside the `∀ᶠ`
telescope rather than as binders; and the two that manufacture their own denominator out of a
count, `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_factorization` and
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_count` of
`Kakeya/DimensionThree/MainLemma1/Rescaling/AnchorDenominator.lean`.  The last two hold only the
placement half, `Kakeya.ml1Boot.IsAnchorPlacement`, since their `L` is built from the count rather
than assumed; that is the reason there are two bundles and not one, and it is why the placement
carries its ambient index set as a parameter — it is read at `t ⊆ s'` with a separate `s' ⊆ u''`
there and at `t ⊆ u''` here.

**Two members of the old group disappeared in that edit rather than being carried into the
bundle**, each becoming a step of the proof: `hcapture`, because `𝕍|_t[W] = t` holds for the plank
of any block — each `T k` with `k ∈ t` lies in the convex hull of the union over `t` — which is
`Kakeya.ml1Boot.familyIn_convexHull_biUnion_self`; and `hLtop`, because `Kakeya.le_maxDensity` and
`Kakeya.maxDensity_le_card` bound the density at the plank by `|t|`, so `denom_le` already forces
`L ≠ ⊤`, which is `Kakeya.ml1Boot.IsAnchorDenominator.denom_ne_top`.  Both were steps of a proof
masquerading as hypotheses, so dropping them weakens the hypotheses of every statement that
displayed them and strengthens none.

**`hdim` is still carried and is still unread.**  `Kakeya.ml1Boot.frostmanConstIn_anchor_le` spends
it nowhere — the one lemma it hands it to, `Kakeya.ml1Boot.density_dilate_ge`, binds it as the
unused `_hdim` — so the ambient dimension is genuinely free in this whole chain.  It is retained
because dropping it is a *generalization* of eight statements rather than a bundling, it would
ripple into every caller, and it is not what this edit is about; that removal is recorded as owed
and is not performed.

## Divergences from the blueprint display, recorded

* The blueprint asks the whole Case (ii) input bundle `def:ml1bootCaseTwoInput`; the Lean form
  takes only `StickyKakeya.IsFrostmanDividingBlock`, exactly as
  `Kakeya.ml1Boot.densityIn_le_of_card_neighbouringParents` does, and for the reason recorded in
  the module docstring of `Kakeya/DimensionThree/MainLemma1/FibreCompletion.lean`.
* The blueprint's `D_m > 0` and `Λ_Δ ≥ 1` fix the interpretation of the pair and are not used;
  they are omitted, again as in the core.
* The blueprint's `θ = ρ_a` and `τ = ρ_b` are written out as `gridScale δ (ssfGridLen δ) a` and
  `gridScale δ (ssfGridLen δ) b`.
* The blueprint writes the unrefined level-`b` family as `𝕍 = (P_b(k))_{k ∈ 𝒰'_b}` and its density
  as `Δ(𝕍, K')`, while `Kakeya.ml1Boot.densityIn_le_of_essDistinctParents` writes `Δ(𝒰'_b, K')`.
  These are the same object: `Kakeya.densityIn` at a node index set *means* the density at the
  family of node tubes indexed by it, so `𝕍` is spelled `fun k => (𝒰'.cover.tube b k)` and `𝒰'_b`
  is spelled `𝒰'.cover.indexSet b`, and no transport occurs in
  `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_essDistinctParents` between the two notations.
  Relatedly, that lemma reads `Kakeya.ml1Boot.frostmanConstIn_anchor_le` — which is stated at a
  family of `δ̃`-tubes for a free `δ̃` — at `δ̃ = τ`, in the un-normalized picture.
* The blueprint's `n = 3` is `hdim : Module.finrank ℝ E = 3`, a hypothesis of
  `Kakeya.ml1Boot.frostmanConstIn_anchor_le` and of nothing else here; the constants are written
  at `Module.finrank ℝ E` rather than at the numeral, so
  `Kakeya.ml1Boot.densityIn_le_of_essDistinctParents` needs no dimension hypothesis at all.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody StickyKakeya Tube Convexity Filter Topology

namespace Kakeya

universe u

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- **The local density bound (5.10a) at a homothety container, under essential distinctness**
(blueprint `lem:ml1bootLocalDensityEssDistinct`).

Write `θ = ρ_a` for the coarse grid radius and `τ = ρ_b` for the fine one.  Let `V` be a `C θ`-tube
with `C ≥ 1` and `C θ ≤ 1`, let `c ≥ 1` satisfy `c + 4 ≤ C_n = Kakeya.Tube.tubeOverlapCoreClose.C`,
and let the container `B` be a convex body inside the *homothety* `c · V`.  If the coarse node
tubes reached by the leaves inside `B` are pairwise essentially distinct — caution (R1) — then for
every convex body `K' ⊆ B` the density of the **unrefined** level-`b` node family in `K'` is at
most

`Λ_Δ · C_{comparableReplacement}(n, C) · δ ^ (-ε') · (θ/τ) ^ (η m) · D_m`,

a bound whose numerator depends on nothing but the ambient dimension and `C`.

*This is `Kakeya.ml1Boot.densityIn_le_of_card_neighbouringParents` at one value of `M₀`, and
nothing more.*  `hblock`, `hloss`, `hleaf`, `hdens` and `hK'` are that lemma's hypotheses verbatim;
`hθ`, `hC`, `hCθ`, `V`, `hc`, `hcC`, `hB` and `hED` are there only to produce its cardinality
hypothesis through `Kakeya.ml1Boot.card_neighbouringParents_le_of_essDistinct`, whose `a ≤ N` comes
from `hblock.fine_le` and `hblock.coarse_lt_fine`.  The container's shape is read there and
nowhere else; the core reads none of it.

**Conditional.**  `hED` has no supplier in this development; see the module docstring and the
docstring of `Kakeya.ml1Boot.card_neighbouringParents_le_of_essDistinct`. -/
theorem densityIn_le_of_essDistinctParents {ι : Type u} {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {Cu : NNReal} {Kds cds a b m : ℕ} {p : Params} {ε' : ℝ}
    (𝒰' : UniformTubeSet s' T (ssfGridLen δ) Cu)
    (hblock : IsFrostmanDividingBlock 𝒰' Cu Kds cds p.η p.ε a b m p.N)
    (hloss : (Cu : ENNReal) * totalLoss Cu Kds cds δ ≤ (δ : ENNReal) ^ (-ε'))
    (hleaf : ∀ k ∈ 𝒰'.cover.indexSet b, ∃ i ∈ s', 𝒰'.cover.assign b i = k)
    (hθ : 0 < gridScale δ (ssfGridLen δ) a) {C : NNReal} (hC : 1 ≤ C)
    (hCθ : C * gridScale δ (ssfGridLen δ) a ≤ 1)
    (V : Tube (C * gridScale δ (ssfGridLen δ) a) E)
    {c : ℝ} (hc : 1 ≤ c) (hcC : c + 4 ≤ Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))
    (B : ConvexSpaceBody E) (hB : B ≤ Tube.dilate V c)
    (hED : ((neighbouringParents 𝒰' a B : Finset ι) : Set ι).Pairwise fun l l' =>
      IsEssentiallyDistinct (𝒰'.cover.tube a l).carrier (𝒰'.cover.tube a l').carrier)
    {Dm ΛΔ : ENNReal}
    (hdens : ∀ l'' ∈ neighbouringParents 𝒰' a B,
      densityIn (𝒰'.nodesUnder b a l'') (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
          (𝒰'.cover.tube a l'').toConvexSpaceBody ≤ ΛΔ * Dm)
    {K' : ConvexSpaceBody E} (hK' : K' ≤ B) :
    densityIn (𝒰'.cover.indexSet b) (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K'
      ≤ ΛΔ * (Tube.comparableReplacement.C (Module.finrank ℝ E) C : ENNReal) *
          (δ : ENNReal) ^ (-ε') *
          ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m) * Dm := by
  classical
  have hb_le : b ≤ ssfGridLen δ := hblock.fine_le
  have ha_le : a ≤ ssfGridLen δ := by
    exact le_trans (le_of_lt hblock.coarse_lt_fine) hb_le
  exact densityIn_le_of_card_neighbouringParents (big := B)
    (M₀ := (Tube.comparableReplacement.C (Module.finrank ℝ E) C : ENNReal))
    (hcard := by
      exact card_neighbouringParents_le_of_essDistinct 𝒰' ha_le hθ hC hCθ V hc hcC hB hED)
    𝒰' hblock hloss hleaf hdens hK'

/-- **(5.10b) with its numerator discharged** (blueprint `lem:ml1bootAnchorFrostmanEssDistinct`).

Write `C_T = Kakeya.ml1Boot.densityTransfer.C`.  Let the anchor `K`, the reference tube `V` and the
factors `C`, `c` be as in `Kakeya.ml1Boot.densityIn_le_of_essDistinctParents`, let
`𝕍 = (P_b k)_{k ∈ 𝒰'_b}` be the **unrefined** level-`b` node family — a family of `τ`-tubes — and
assume the denominator bundle `Kakeya.ml1Boot.IsAnchorDenominator` at `𝕍`, `K` and a pair
`0 < a ≤ b`: a nonempty block `t ⊆ 𝒰'_b` whose plank `W` lies in `K` and satisfies
`|K| ≤ C_T (b/a) |W|`, with `0 < L ≤ Δ(𝕍|_t, W)`.  Then

`C_F(𝕍[K], K) ≤ C_T (b/a) · U / L`, where
`U = Λ_Δ · C_{comparableReplacement}(n, C) · δ ^ (-ε') · (θ/τ) ^ (η m) · D_m`,

a numerator in which every factor is either a hypothesis of the situation or an absolute constant:
**there is no residual covering cardinality `M`**.

*This is `Kakeya.ml1Boot.frostmanConstIn_anchor_le` at one value of `U`, and nothing more.*  Its
numerator hypothesis `hnum` — a uniform bound `Δ(𝕍, K') ≤ U` at every convex `K' ≤ K` — is exactly
what `Kakeya.ml1Boot.densityIn_le_of_essDistinctParents` delivers, read at the container `B = K`,
and the two densities are the same object by definition: writing a density at a node index set
means writing it at the family of node tubes indexed by that set.  No arithmetic is performed on
`U` and none on the exponents.

**What this does not settle.**  The denominator `L` is untouched: it is assumed here exactly as it
is assumed in `Kakeya.ml1Boot.frostmanConstIn_anchor_le`, and the inequality relating the two loads
of Step 5a — blueprint `note:ml1bootStep5aTwoLoads`, which is **open** — is what still stands
between this and an unconditional (5.10b), entering through `L`.  Nothing here identifies `D_m`
with `N_m`.

**This is not the Step 5c anchor, and the transport to it is not performed.**  This bound is
asserted in the *un-normalized* picture, at the family `𝕍` of `τ`-tubes and at an anchor `K` of
that picture, whereas `Kakeya.ml1Boot.plankWidth_le_of_anchor` reads
`Kakeya.ml1Boot.frostmanConstIn_anchor_le` *after* the normalization
`Kakeya.ml1Boot.tubeNormalizedFamily`, at `δ̃ = τ/θ` and at `K = 2 · T_b`.  This is caution (C2) of
blueprint `subsec:ml1bootHomothetyParents`; see the blueprint entry for the three checks that
transport would need, none of which is made here.

**Conditional.**  `hED` has no supplier in this development; see the module docstring. -/
theorem frostmanConstIn_anchor_le_of_essDistinctParents {ι : Type u} {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {Cu : NNReal} {Kds cds a b m : ℕ} {p : Params} {ε' : ℝ}
    (𝒰' : UniformTubeSet s' T (ssfGridLen δ) Cu)
    (hblock : IsFrostmanDividingBlock 𝒰' Cu Kds cds p.η p.ε a b m p.N)
    (hloss : (Cu : ENNReal) * totalLoss Cu Kds cds δ ≤ (δ : ENNReal) ^ (-ε'))
    (hleaf : ∀ k ∈ 𝒰'.cover.indexSet b, ∃ i ∈ s', 𝒰'.cover.assign b i = k)
    (hθ : 0 < gridScale δ (ssfGridLen δ) a) {C : NNReal} (hC : 1 ≤ C)
    (hCθ : C * gridScale δ (ssfGridLen δ) a ≤ 1)
    (V : Tube (C * gridScale δ (ssfGridLen δ) a) E)
    {c : ℝ} (hc : 1 ≤ c) (hcC : c + 4 ≤ Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))
    (K : ConvexSpaceBody E) (hK : K ≤ Tube.dilate V c)
    (hED : ((neighbouringParents 𝒰' a K : Finset ι) : Set ι).Pairwise fun l l' =>
      IsEssentiallyDistinct (𝒰'.cover.tube a l).carrier (𝒰'.cover.tube a l').carrier)
    {Dm ΛΔ : ENNReal}
    (hdens : ∀ l'' ∈ neighbouringParents 𝒰' a K,
      densityIn (𝒰'.nodesUnder b a l'') (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
          (𝒰'.cover.tube a l'').toConvexSpaceBody ≤ ΛΔ * Dm)
    (hdim : Module.finrank ℝ E = 3) {ap bp : NNReal} (hap0 : 0 < ap) (hab : ap ≤ bp)
    {t : Finset ι} {L : ENNReal}
    (hanch : IsAnchorDenominator (fun k => 𝒰'.cover.tube b k) K ap bp
      (𝒰'.cover.indexSet b) t L) :
    frostmanConstIn
        (familyIn (𝒰'.cover.indexSet b)
          (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K)
        (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K
      ≤ (densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) *
          ((ΛΔ * (Tube.comparableReplacement.C (Module.finrank ℝ E) C : ENNReal) *
            (δ : ENNReal) ^ (-ε') *
            ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m) * Dm) / L) := by
  classical
  refine frostmanConstIn_anchor_le (hdim := hdim) (δt := gridScale δ (ssfGridLen δ) b)
    (ap := ap) (bp := bp) (hap0 := hap0) (hab := hab)
    (T := fun k => 𝒰'.cover.tube b k) (K := K)
    (U := ΛΔ * (Tube.comparableReplacement.C (Module.finrank ℝ E) C : ENNReal) *
          (δ : ENNReal) ^ (-ε') *
          ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m) * Dm)
    (L := L)
    (hnum := fun K' hK' =>
      densityIn_le_of_essDistinctParents (𝒰' := 𝒰') (hblock := hblock) (hloss := hloss)
        (hleaf := hleaf) (hθ := hθ) (hC := hC) (hCθ := hCθ)  (V := V) (hc := hc) (hcC := hcC)
        (B := K) (hB := hK) (hED := hED) (hdens := hdens) (hK' := hK'))
    (hanch := hanch)

/-- **(GWZ (5.10b)) The anchor bound on the covering route** (blueprint
`lem:ml1bootAnchorFrostmanFromLoad`).

Write `C_T = Kakeya.ml1Boot.densityTransfer.C`.  Assume the whole situation of
`Kakeya.ml1Boot.densityIn_le_of_load`, and let the anchor `K` be *any* convex body inside the
concentric rescaling `P_a(l) ^ (Λ ρ_a)`.  Let `𝕍 = (P_b k)_{k ∈ 𝒰'_b}` be the **unrefined**
level-`b` node family — a family of `τ`-tubes — and assume the denominator bundle
`Kakeya.ml1Boot.IsAnchorDenominator` at `𝕍`, `K` and a pair `0 < ap ≤ bp`: a nonempty block
`t ⊆ 𝒰'_b` whose plank `W` lies in `K` and satisfies `|K| ≤ C_T (bp/ap) |W|`, with
`0 < L ≤ Δ(𝕍|_t, W)`.  Then

`C_F(𝕍[K], K) ≤ C_T (bp/ap) · U / L`, where

`U = M(E,Λ) · C_ds · δ ^ (-ε') · (θ/τ) ^ (η m)`
`      · (C_ds ^ 5 · Λ_load · N_m · C_{ltd}(n) · (τ/θ) ^ (n-1))`

is the right-hand side of `Kakeya.ml1Boot.densityIn_le_of_load`: every factor is either a hypothesis
of the situation or a constant already named, and **there is no residual covering cardinality `M`**,
that being what `Kakeya.ml1Boot.isEnlargementCover_node_rescale` buys.

*This is `Kakeya.ml1Boot.frostmanConstIn_anchor_le` at one value of `U`, and nothing more.*  Its
numerator hypothesis `hnum` is `Kakeya.ml1Boot.densityIn_le_of_load` read at each `K' ≤ K`, which is
condition because `K' ≤ K ≤ P_a(l) ^ (Λ ρ_a)`.  The scale parameter `δ̃` is read at `δ̃ = τ`, in the
un-normalized picture, and no arithmetic is performed on `U` or on the exponents.

**No essential distinctness, and the homothety obstruction is missed entirely.**  The container here
is the *concentric rescaling* `Kakeya.Tube.rescale`, not a homothety, so blueprint
`note:ml1bootHomothetyOverlapInsufficient` — which is what forces (R1) on the route of
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_essDistinctParents` — does not apply, and neither `hED`
nor either of the two container restrictions `C θ ≤ 1`, `c + 4 ≤ C_n` occurs above.  That is the
whole advantage of this route; it is *not* an assertion that the other route is dispensable, whose
container is of the shape the eventual Step 5c consumer is stated at.

**What this does not settle.**  The denominator `L` is untouched, assumed exactly as it is in
`Kakeya.ml1Boot.frostmanConstIn_anchor_le`; the placement of the plank-carrying tested body is the
longitudinal gap of blueprint `note:ml1bootEnlargementTubeStatus`, untouched; this is not the
Step 5c anchor and the transport to it is not performed; and the load pair `(N_m, Λ_load)` is still
*data* here, `hload` being a hypothesis. -/
theorem frostmanConstIn_anchor_le_of_load {ι : Type u} {δ : NNReal} {s' : Finset ι} [DecidableEq ι]
    {T : ι → Tube δ E} {Cu : NNReal} {Kds cds a b m : ℕ} {p : Params} {ε' : ℝ}
    (hCu : 1 ≤ Cu) (𝒰' : UniformTubeSet s' T (ssfGridLen δ) Cu)
    (hblock : IsFrostmanDividingBlock 𝒰' Cu Kds cds p.η p.ε a b m p.N)
    (hloss : (Cu : ENNReal) * totalLoss Cu Kds cds δ ≤ (δ : ENNReal) ^ (-ε'))
    (hleaf : ∀ k ∈ 𝒰'.cover.indexSet b, ∃ i ∈ s', 𝒰'.cover.assign b i = k)
    {pθ : ι → ι} (hcnp : IsCoarseNodeParents 𝒰' a b pθ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδ : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ)))
    (Λ : NNReal) (l : ι) {Nm Λload : NNReal}
    (hload : ∀ l' ∈ 𝒰'.cover.indexSet a,
      ((fibre (𝒰'.cover.indexSet b) pθ l').card : NNReal) ≤ Λload * Nm)
    (K : ConvexSpaceBody E)
    (hK : K ≤ ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ (ssfGridLen δ) a)).toConvexSpaceBody)
    (hdim : Module.finrank ℝ E = 3) {ap bp : NNReal} (hap0 : 0 < ap) (hab : ap ≤ bp)
    {t : Finset ι} {L : ENNReal}
    (hanch : IsAnchorDenominator (fun k => 𝒰'.cover.tube b k) K ap bp
      (𝒰'.cover.indexSet b) t L) :
    frostmanConstIn
        (familyIn (𝒰'.cover.indexSet b)
          (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K)
        (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K
      ≤ (densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) *
          ((((enlargementCoverConstant E Λ : ℕ) * Cu : NNReal) * (δ : ENNReal) ^ (-ε') *
            ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m) *
            (((Cu ^ 5 * Λload * Nm : NNReal) : ENNReal)
              * (loadToDensity.C (Module.finrank ℝ E) : ENNReal)
              * ((gridScale δ (ssfGridLen δ) b / gridScale δ (ssfGridLen δ) a : NNReal) : ENNReal)
                  ^ (Module.finrank ℝ E - 1))) / L) := by
  classical
  exact frostmanConstIn_anchor_le (hdim := hdim) (δt := gridScale δ (ssfGridLen δ) b)
    (ap := ap) (bp := bp) (hap0 := hap0) (hab := hab)
    (T := fun k => 𝒰'.cover.tube b k) (K := K)
    (U := ((enlargementCoverConstant E Λ : ℕ) * Cu : NNReal) * (δ : ENNReal) ^ (-ε') *
        ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
          / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m) *
        (((Cu ^ 5 * Λload * Nm : NNReal) : ENNReal)
          * (loadToDensity.C (Module.finrank ℝ E) : ENNReal)
          * ((gridScale δ (ssfGridLen δ) b / gridScale δ (ssfGridLen δ) a : NNReal) : ENNReal)
              ^ (Module.finrank ℝ E - 1)))
    (L := L)
    (hnum := fun K' hK' => by
      simpa only [one_mul] using
        densityIn_le_of_load hCu 𝒰' hblock hloss hleaf hcnp hδ0 hδ1 hδ Λ l hload
          (hK' := le_trans hK' hK))
    (hanch := hanch)

/-- **(GWZ (5.10b)) The anchor bound on the essential-distinctness route, from a load pair**
(blueprint `lem:ml1bootAnchorFrostmanEssDistinctFromLoad`).

`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_essDistinctParents` read at `Λ_Δ = 1` and at `D_m` the
right-hand side of `Kakeya.ml1Boot.densityIn_nodesUnder_le_of_load`.  **No new anchor lemma is
needed and none is written**: the density bullet `hdens` of that lemma is discharged by the
two-loads relation, whose quantifier over the neighbouring parents is covered by
`Kakeya.ml1Boot.neighbouringParents_subset_indexSet`, applicable because that lemma asks nothing of
the body — so the parents of a *homothety* lie in `𝒰'_a` just as those of a rescaling do, and the
load hypothesis, stated over the whole of `𝒰'_a`, is readable at each of them.  This is **not** an
evasion of blueprint `note:ml1bootHomothetyOverlapInsufficient`: what that note obstructs is the
`O(1)` parent *count* at a homothety, which is supplied here by `hED` and not by the load pair.

**Exactly one bullet is discharged and nothing else about that route changes.**  `hED`, which is
caution (R1), is still a hypothesis, still cannot be removed, and still has no supplier in this
development; the two container restrictions `C θ ≤ 1` and `c + 4 ≤ C_n` are still carried; the
denominator `L` is still assumed; and the transport to the Step 5c anchor is still not performed.
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_essDistinctParents` and
`Kakeya.ml1Boot.densityIn_le_of_essDistinctParents` are neither edited nor weakened nor re-derived
by this. -/
theorem frostmanConstIn_anchor_le_of_essDistinctParents_of_load {ι : Type u} {δ : NNReal}
    {s' : Finset ι} [DecidableEq ι]
    {T : ι → Tube δ E} {Cu : NNReal} {Kds cds a b m : ℕ} {p : Params} {ε' : ℝ}
    (hCu : 1 ≤ Cu) (𝒰' : UniformTubeSet s' T (ssfGridLen δ) Cu)
    (hblock : IsFrostmanDividingBlock 𝒰' Cu Kds cds p.η p.ε a b m p.N)
    (hloss : (Cu : ENNReal) * totalLoss Cu Kds cds δ ≤ (δ : ENNReal) ^ (-ε'))
    (hleaf : ∀ k ∈ 𝒰'.cover.indexSet b, ∃ i ∈ s', 𝒰'.cover.assign b i = k)
    (hθ : 0 < gridScale δ (ssfGridLen δ) a) {C : NNReal} (hC : 1 ≤ C)
    (hCθ : C * gridScale δ (ssfGridLen δ) a ≤ 1)
    (V : Tube (C * gridScale δ (ssfGridLen δ) a) E)
    {c : ℝ} (hc : 1 ≤ c) (hcC : c + 4 ≤ Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))
    (K : ConvexSpaceBody E) (hK : K ≤ Tube.dilate V c)
    (hED : ((neighbouringParents 𝒰' a K : Finset ι) : Set ι).Pairwise fun l l' =>
      IsEssentiallyDistinct (𝒰'.cover.tube a l).carrier (𝒰'.cover.tube a l').carrier)
    {pθ : ι → ι} (hcnp : IsCoarseNodeParents 𝒰' a b pθ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {Nm Λload : NNReal}
    (hload : ∀ l' ∈ 𝒰'.cover.indexSet a,
      ((fibre (𝒰'.cover.indexSet b) pθ l').card : NNReal) ≤ Λload * Nm)
    (hdim : Module.finrank ℝ E = 3) {ap bp : NNReal} (hap0 : 0 < ap) (hab : ap ≤ bp)
    {t : Finset ι} {L : ENNReal}
    (hanch : IsAnchorDenominator (fun k => 𝒰'.cover.tube b k) K ap bp
      (𝒰'.cover.indexSet b) t L) :
    frostmanConstIn
        (familyIn (𝒰'.cover.indexSet b)
          (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K)
        (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K
      ≤ (densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) *
          (((Tube.comparableReplacement.C (Module.finrank ℝ E) C : ENNReal) *
            (δ : ENNReal) ^ (-ε') *
            ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m) *
            (((Cu ^ 5 * Λload * Nm : NNReal) : ENNReal)
              * (loadToDensity.C (Module.finrank ℝ E) : ENNReal)
              * ((gridScale δ (ssfGridLen δ) b / gridScale δ (ssfGridLen δ) a : NNReal) : ENNReal)
                  ^ (Module.finrank ℝ E - 1))) / L) := by
  classical
  have ha : a ≤ ssfGridLen δ :=
    le_of_lt (lt_of_lt_of_le hblock.coarse_lt_fine hblock.fine_le)
  have hdens : ∀ l'' ∈ neighbouringParents 𝒰' a K,
      densityIn (𝒰'.nodesUnder b a l'') (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
          (𝒰'.cover.tube a l'').toConvexSpaceBody
        ≤ 1 * (((Cu ^ 5 * Λload * Nm : NNReal) : ENNReal)
            * (loadToDensity.C (Module.finrank ℝ E) : ENNReal)
            * ((gridScale δ (ssfGridLen δ) b / gridScale δ (ssfGridLen δ) a : NNReal) : ENNReal)
                ^ (Module.finrank ℝ E - 1)) := by
    intro l'' hl''
    have hl''a : l'' ∈ 𝒰'.cover.indexSet a :=
      neighbouringParents_subset_indexSet 𝒰' ha _ hl''
    rw [one_mul]
    exact densityIn_nodesUnder_le_of_load hCu 𝒰' hcnp hδ0 hδ1 hload hl''a hl''a
  simpa only [one_mul] using
    frostmanConstIn_anchor_le_of_essDistinctParents 𝒰' hblock hloss hleaf hθ hC hCθ V hc hcC
      K hK hED (ΛΔ := 1)
      (Dm := ((Cu ^ 5 * Λload * Nm : NNReal) : ENNReal)
        * (loadToDensity.C (Module.finrank ℝ E) : ENNReal)
        * ((gridScale δ (ssfGridLen δ) b / gridScale δ (ssfGridLen δ) a : NNReal) : ENNReal)
            ^ (Module.finrank ℝ E - 1))
      hdens hdim hap0 hab hanch

/-- **(GWZ (5.10b)) The anchor bound on the covering route, from the uniformity alone** (blueprint
`lem:ml1bootAnchorFrostmanFromUniformity`).

`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_load` with its **load hypothesis deleted**: the pair
`(N_m, Λ_load)` is instantiated at `N_m = N_a / N_b` and `Λ_load = C_ds ^ 3`, the values
`Kakeya.ml1Boot.card_coarseFibre_le_branchingRatio` supplies at *every* `a`-node, so that

```
C_F(𝕍[K], K) ≤ C_T (bp/ap) · U / L,
U = M(E,Λ) · C_ds · δ ^ (-ε') · (θ/τ) ^ (η m)
      · (C_ds ^ 5 · C_ds ^ 3 · (N_a/N_b) · C_{ltd}(n) · (τ/θ) ^ (n-1))
```

with **no free load parameter left in it**: everything on the right is a branching number of the
hierarchy, a grid scale, one of the block's own `δ`-dependent factors, a width, the denominator `L`,
or a constant already named.  It is to `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_load` exactly
what `Kakeya.ml1Boot.densityIn_le_of_uniformity` is to `Kakeya.ml1Boot.densityIn_le_of_load`, and
the two are read at the same pair.

*Intended proof.*  `Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_load` at that pair, its `hload`
being `Kakeya.ml1Boot.card_coarseFibre_le_branchingRatio` read at each `l' ∈ 𝒰'_a`.

**The one new Lean hypothesis is `hNb : 0 < N_b` and nothing else.**  It is what makes the branching
ratio a number and it is what `Kakeya.ml1Boot.card_coarseFibre_le_branchingRatio` asks.  The
condition `N_b ≤ N_a` that the blueprint displays of `lem:ml1bootLocalDensityFromUniformity` and
`lem:ml1bootAnchorFrostmanFromUniformity` both carry is *not* asked here, exactly as it is not asked
at `Kakeya.ml1Boot.densityIn_le_of_uniformity`: this chain reaches its numerator through
`Kakeya.ml1Boot.densityIn_le_of_load` and `Kakeya.ml1Boot.densityIn_le_of_rescale`, whose `D_m` and
`Λ_Δ` are bare parameters spending no `N_m ≥ 1`.  **This is not a divergence in the direction of
strength but in the direction of generality**: the blueprint's third bullet of
`lem:ml1bootLocalDensityUnrefined` asks `D_m > 0` outright, so the blueprint display must carry
`N_b ≤ N_a` to meet it at `N_m = N_a/N_b`, and this declaration is the more general statement of
which that display is an instance.  Widening that bullet to `D_m ≥ 0` is recorded as owed at
blueprint `note:ml1bootStep5aEdgeStatus`; nothing here does it.  The omission settles no question,
and in particular not the budget question about `C_ds ^ 3`.

**What this does not settle.**  The denominator `L` is untouched, assumed exactly as it is in
`Kakeya.ml1Boot.frostmanConstIn_anchor_le`; the placement of the plank-carrying tested body is the
longitudinal gap of blueprint `note:ml1bootEnlargementTubeStatus`, untouched; this is not the
Step 5c anchor and the transport to it is not performed; and nothing here says anything about the
*retained* families, for which blueprint `lem:ml1bootFibreCompletion` still has no load supplier.
An assembly of conditional inputs is a conditional statement: **this may not be cited as an
unconditional (5.10b)**.  What it discharges is item (iv) of blueprint
`note:ml1bootAnchorFromLoadStatus` — the load pair — and only at the unrefined fibres.

The constant is left as `Cu ^ 5 * Cu ^ 3` rather than contracted to `Cu ^ 8`, so that the reading at
`Λ_load = Cu ^ 3` stays visible, exactly as at `Kakeya.ml1Boot.densityIn_le_of_uniformity`. -/
theorem frostmanConstIn_anchor_le_of_uniformity {ι : Type u} {δ : NNReal} {s' : Finset ι}
    [DecidableEq ι]
    {T : ι → Tube δ E} {Cu : NNReal} {Kds cds a b m : ℕ} {p : Params} {ε' : ℝ}
    (hCu : 1 ≤ Cu) (𝒰' : UniformTubeSet s' T (ssfGridLen δ) Cu)
    (hblock : IsFrostmanDividingBlock 𝒰' Cu Kds cds p.η p.ε a b m p.N)
    (hloss : (Cu : ENNReal) * totalLoss Cu Kds cds δ ≤ (δ : ENNReal) ^ (-ε'))
    (hleaf : ∀ k ∈ 𝒰'.cover.indexSet b, ∃ i ∈ s', 𝒰'.cover.assign b i = k)
    {pθ : ι → ι} (hcnp : IsCoarseNodeParents 𝒰' a b pθ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδ : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ)))
    (hNb : 0 < 𝒰'.branchingN b)
    (Λ : NNReal) (l : ι)
    (K : ConvexSpaceBody E)
    (hK : K ≤ ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ (ssfGridLen δ) a)).toConvexSpaceBody)
    (hdim : Module.finrank ℝ E = 3) {ap bp : NNReal} (hap0 : 0 < ap) (hab : ap ≤ bp)
    {t : Finset ι} {L : ENNReal}
    (hanch : IsAnchorDenominator (fun k => 𝒰'.cover.tube b k) K ap bp
      (𝒰'.cover.indexSet b) t L) :
    frostmanConstIn
        (familyIn (𝒰'.cover.indexSet b)
          (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K)
        (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K
      ≤ (densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) *
          ((((enlargementCoverConstant E Λ : ℕ) * Cu : NNReal) * (δ : ENNReal) ^ (-ε') *
            ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m) *
            (((Cu ^ 5 * Cu ^ 3 * (𝒰'.branchingN a / 𝒰'.branchingN b) : NNReal) : ENNReal)
              * (loadToDensity.C (Module.finrank ℝ E) : ENNReal)
              * ((gridScale δ (ssfGridLen δ) b / gridScale δ (ssfGridLen δ) a : NNReal) : ENNReal)
                  ^ (Module.finrank ℝ E - 1))) / L) := by
  classical
  exact frostmanConstIn_anchor_le_of_load hCu 𝒰' hblock hloss hleaf hcnp hδ0 hδ1 hδ Λ l
    (Nm := 𝒰'.branchingN a / 𝒰'.branchingN b) (Λload := Cu ^ 3)
    (fun l' hl' => Kakeya.ml1Boot.card_coarseFibre_le_branchingRatio hCu 𝒰' hcnp hNb hl')
    K (hK := hK) (hdim := hdim) (hap0 := hap0) (hab := hab)
    (hanch := hanch)

end ml1Boot

end Kakeya
