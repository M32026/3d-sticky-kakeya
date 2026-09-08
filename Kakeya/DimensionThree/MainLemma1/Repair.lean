/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.CoarseFibre
public import Kakeya.DimensionThree.MainLemma1.Factoring
public import Kakeya.DimensionThree.MainLemma1.ParentConflictCover

/-!
# Main Lemma 1, Case (ii): the repair chain, moves (R1) and (R2)

Blueprint `lem:ml1bootRepairUniform` and `lem:ml1bootRepairEssDistinct`.  Step 2 of the Case (ii)
repair is a chain of three passes, `(R2) → (R1) → (R2)`, and this file holds both moves together
with the four small index-bookkeeping devices the reordered chain needs.

The (R2) pass is **one uniformization pass at two parent scales**, stated so that *the shape of
its input is the shape of its output*.

That shape is what makes the chain composable, and it is the whole point of the restatement:

* the pass **takes no uniformity hypothesis**, which is why it may legitimately run *first*,
  before the essential-distinctness deletion (R1) — see blueprint
  `note:ml1bootRepairEDLeafShadedUniformity` and `note:ml1bootRepairOrderGWZ`; and
* it **concludes** one, at a dimension-only constant, which is precisely what (R1) consumes and
  what that note recorded as unsupplied in the source's own ordering.

Move (R1), blueprint `lem:ml1bootRepairEssDistinct`, is `Kakeya.ml1Boot.exists_repairEssDistinct`
below. Its uniformity hypothesis is a *hypothesis*: the caller discharges it by running (R2)
first, which is the reordering blueprint `note:ml1bootRepairOrderGWZ` records and which is what
closed `note:ml1bootRepairEDLeafShadedUniformity`. What (R1) does **not** carry is a middle
bound at the retained `θ`-fibre; that obligation is governed by the dichotomy
`Kakeya.ml1Boot.IsFibrewiseEmptyOrShare`, whose descent
`Kakeya.ml1Boot.frostmanConstIn_retainedFibre_le` is proved in
`Kakeya/DimensionThree/MainLemma1/CoarseFibre.lean`. What is missing is a **caller** — see the docstring of
`Kakeya.ml1Boot.exists_repairEssDistinct` below, and blueprint
`note:ml1bootRepairEDMidRetained`.

## The four devices, over five declarations

* `Kakeya.ml1Boot.fibre_eq_empty_of_notMem` and
  `Kakeya.ml1Boot.frostmanConstIn_fibre_eq_zero_of_notMem` are the two halves of blueprint
  `lem:ml1bootAbsentParentFibre`: a node no retained leaf lies over carries an empty fibre, and
  an empty family has Frostman constant `0`, so every *upper* bound is free there.  This is what
  lets a pass's node deletions be discarded.
* `Kakeya.ml1Boot.fibreFrostman_of_mapsTo` is blueprint `lem:ml1bootFibreTransportPastDrop`, the
  consequence a caller actually reads: a fibrewise Frostman transport asserted at the nodes a
  pass keeps holds at every node, so discarding the pass's node output costs nothing on the
  upper side.  What makes this work is that the item transported is a *bound*: nothing of the
  kind holds for a node-level **property**, which is one reason no pass here concludes one.
* `Kakeya.ml1Boot.IsParentFamily.comp` is blueprint `lem:ml1bootCoarseParentFamilyForLeaves`: the
  coarse node family, read along the composed map, is a parent family for the **leaves**.  Move
  (R1) needs it, `Kakeya.ml1Boot.exists_essDistinct_parentFamily` consuming the *leaf* family at
  both scales.
* `Kakeya.ml1Boot.isParentFamily_trim` is blueprint `lem:ml1bootParentTrim`: a refinement that
  prices only leaves restores the **node**-level containment after the fine node set is trimmed
  to `{k ∈ u_τ : p_θ k ∈ u_θ}`.  Without the trim that containment is false, which is the point
  on which an earlier form of (R2) was retracted.

## Divergences from the informal statement

*The Case (ii) bundle is not a hypothesis.*  The blueprint phrases the lemma "in the situation
of `def:ml1bootCaseTwoInput`", with `ŝ ⊆ s'`, `t̂_τ ⊆ t_τ`, `t̂_θ ⊆ t_θ` and the two set-level
containments `{p_τ i : i ∈ ŝ} ⊆ t̂_τ`, `{p_θ k : k ∈ t̂_τ} ⊆ t̂_θ`; but its own prose says its
hypotheses "are the hypotheses of `lem:ml1bootUniformizePair` and nothing more".  They are, and
that is how they are stated here: the containments *together with* the ambient parent families
are exactly `Kakeya.ml1Boot.IsParentFamily` at the hatted sets, which is what blueprint
`lem:ml1bootCoarseParentFamilyForLeaves` extracts from the bundle.  So the Lean statement is
free-standing, mentions neither `Kakeya.ml1Boot.IsCaseTwoInput` nor a hierarchy, and is
applicable at either of the chain's two call sites without reproving anything.

*One node type, not two.*  Both parent index sets are `Finset κ` for a single type `κ`, and the
coarse parent map is `pθ : κ → κ`.  This is the shape the Case (ii) call site has, where every
index set is a `Finset` of the hierarchy's own index type and `pθ : ι → ι`
(`Kakeya.ml1Boot.IsCoarseNodeParents`).  Stating it at two unrelated types would be a
strengthening nothing available here supplies.

*The node containment in item (d).*  A uniformization that prices only *leaves* delivers the two
containments at the leaf level, `{p_τ i : i ∈ s'} ⊆ u_τ` and `{p_θ (p_τ i) : i ∈ s'} ⊆ u_θ`.
The node-level containment `{p_θ k : k ∈ u_τ} ⊆ u_θ` is **false in general**, since `u_τ` may
contain a node over which no retained leaf lies, and an earlier form of (R2) that asserted it
outright was retracted on exactly that point (blueprint `lem:ml1bootRepairUniform`, and
`note:ml1bootRepairEDMidRetained` for the sibling retraction).  The device that restores it is
the *trim* `t'τ = {k ∈ u_τ : p_θ k ∈ u_θ}` of blueprint `lem:ml1bootParentTrim`, proved below as
`Kakeya.ml1Boot.isParentFamily_trim`; with that witness the field
`Kakeya.ml1Boot.IsRepairUniformPass.parentCoarse` is true by construction.

*The count clause is stated in `ℝ`.*  Blueprint item (a) reads `|ŝ| ≤ δ ^ (-ε') |ŝ⁺|`, and the
one consumer of it is `Kakeya.ml1Boot.repairCountChain`, whose two count hypotheses are real
inequalities in exactly this spelling, so the `ENNReal`-to-`ℝ` conversion a uniformization's own
count clause would need is paid here rather than at the call site.

## Standing caveat: move (R2) is refuted, and its statement has been deleted

The (R2) statement — blueprint `lem:ml1bootRepairUniform`, intended producer
`Kakeya.ml1Boot.exists_repairUniform` — **is false**, and
`Kakeya.ml1Boot.not_exists_repairUniform` below proves its negation, spelling it out inline: the
pass hypothesised nothing about the shadings while concluding a positive lower bound on them at
a leaf set its own clauses force nonempty, so an all-empty shading refutes it. The retracted
proof went through
`Kakeya.ml1Boot.exists_uniformRefinement`, which is refuted for the same reason
(`Kakeya.ml1Boot.not_exists_uniformRefinement`); that citation has been removed and appears
nowhere in this file. The
conclusion bundle `Kakeya.ml1Boot.IsRepairUniformPass` also remains, as the record of what such
a pass was to deliver. Anything downstream that assumes move (R2) — in
`Kakeya/DimensionThree/MainLemma1/ThreePass.lean` and beyond — is a derivation
over a refuted premise and establishes nothing until the statement is repaired.

Move (R1) was **not** unaffected, and this paragraph used to say it was.  It is proved from
`Kakeya.ml1Boot.exists_essDistinct_parentFamily`, and the scale-free form of that citation is
false (`Kakeya.ml1Boot.not_exists_essDistinct_parentFamily`); since (R1) quantified `τ` and `θ`
over the whole ladder `δ ≤ τ ≤ θ ≤ 1`, it applied the citation inside the refuting regime and was
therefore false itself, its proof establishing nothing.  Both statements now carry the scale
hypothesis `δ ^ (ε'/2) ≤ c τ / Co` and the citation is again an accepted assumption; see the
docstring of `Kakeya.ml1Boot.exists_repairEssDistinct` below.

## Names below that are *intended* declarations and do not exist

Several docstrings in this file name the Case (ii) construction layer by the names it is to be
given. In this file the intended names used are
`Kakeya.ml1Boot.exists_repairUniform` (blueprint `lem:ml1bootRepairUniform`, deleted after
refutation as described above) and `Kakeya.ml1Boot.exists_repairThreePass` (blueprint
`lem:ml1bootRepairThreePass`). Blueprint `note:ml1bootCaseTwoConstructionLayerEmpty` holds the
authoritative inventory of the whole absent layer; read it before trusting any name in the
Case (ii) material. That inventory is itself checked against the source rather than assumed:
one of its entries, `Kakeya.ml1Boot.caseTwoThreePassScales`, has since been written, in
`Kakeya/DimensionThree/MainLemma1/ThreePass.lean`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The four index-bookkeeping devices -/

/-- **A node no leaf lies over carries an empty fibre** (blueprint
`lem:ml1bootAbsentParentFibre`, first display).

The hypothesis `hmaps` is the `Kakeya.ml1Boot.IsParentFamily.mapsTo` clause, so it holds in
particular whenever `(uτ, 𝕋_τ, pτ)` is a parent family for `𝕋|_u`; it is stated bare because that
is all the argument reads, and because a move which deletes nodes but keeps the *leaf*-level
containment supplies exactly this and nothing else about a node it has dropped.

The conclusion is the containment read contrapositively: an `i ∈ u` with `pτ i = k` would put
`k` into `uτ`. -/
theorem fibre_eq_empty_of_notMem {ι κ : Type*} [DecidableEq κ] {u : Finset ι} {uτ : Finset κ}
    {pτ : ι → κ} (hmaps : ∀ i ∈ u, pτ i ∈ uτ) {k : κ} (hk : k ∉ uτ) :
    fibre u pτ k = ∅ := by
  by_contra hne
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  rw [fibre, Finset.mem_filter] at hi
  exact hk (hi.2 ▸ hmaps i hi.1)

/-- **Every upper Frostman bound is free at a node the pass has dropped** (blueprint
`lem:ml1bootAbsentParentFibre`, second display).

If every retained leaf's `τ`-parent lies in `uτ` and `k ∉ uτ`, then the retained fibre over `k`
is empty and its Frostman constant vanishes in *every* body `K`.  So a caller may keep the
**input** node set as its output and lose nothing on the upper side — which is what lets
blueprint `lem:ml1bootRepairThreePass` output move (R1)'s node sets rather than the last (R2)
pass's.

As in `Kakeya.ml1Boot.fibre_eq_empty_of_notMem` the hypothesis is the bare `mapsTo` clause and
not a whole `Kakeya.ml1Boot.IsParentFamily`: neither the tubes nor the scales are read, and a
move which deletes nodes while keeping the *leaf*-level containment supplies exactly this.

The family `W` is unconstrained: the fibre is empty, so no property of it is read.  Nothing of
the kind is true on the *lower* side, where a bound at a dropped node is false, not free — nor
for a node-level *property* rather than a bound, which would not survive a node discard. -/
theorem frostmanConstIn_fibre_eq_zero_of_notMem {ι κ : Type*} [DecidableEq κ]
    {u : Finset ι} {uτ : Finset κ} {pτ : ι → κ}
    (hmaps : ∀ i ∈ u, pτ i ∈ uτ) {k : κ} (hk : k ∉ uτ)
    (W : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E) :
    frostmanConstIn (fibre u pτ k) W K = 0 := by
  rw [fibre_eq_empty_of_notMem hmaps hk]
  exact ConvexSpaceBody.frostmanConstIn_empty

/-- **A fibrewise Frostman transport extends past the nodes a pass has dropped** (blueprint
`lem:ml1bootFibreTransportPastDrop`).

The hypothesis is the shape a uniformization pass delivers: the transport at the nodes `v'τ` it
keeps, with the side condition stated at its own input fibre over `u0`.  The conclusion is that
same transport read at any node whatever — in particular at the nodes the *caller* keeps.  At a
node outside `v'τ` there is nothing to prove: the retained fibre over it is empty by
`Kakeya.ml1Boot.fibre_eq_empty_of_notMem`, so the left side is `0`.

No relation between `v'τ` and the caller's node set is asked for, and none is available in
general: the conclusion is unconditional in `k` precisely because a node outside `v'τ` carries an
empty retained fibre no matter where it sits.

This is the only thing needed to discard a pass's node output, and blueprint
`lem:ml1bootRepairThreePass` makes the step twice, once for each of its two (R2) passes. -/
theorem fibreFrostman_of_mapsTo {ι κ : Type*} [DecidableEq κ] {u0 u1 : Finset ι}
    {v'τ : Finset κ} {pτ : ι → κ} {A : ENNReal} (hmaps : ∀ i ∈ u1, pτ i ∈ v'τ)
    (W : ι → ConvexSpaceBody E)
    (h : ∀ k ∈ v'τ, ∀ K : ConvexSpaceBody E, (∀ i ∈ fibre u0 pτ k, W i ≤ K) →
      frostmanConstIn (fibre u1 pτ k) W K ≤ A * frostmanConstIn (fibre u0 pτ k) W K) :
    ∀ (k : κ), ∀ K : ConvexSpaceBody E, (∀ i ∈ fibre u0 pτ k, W i ≤ K) →
      frostmanConstIn (fibre u1 pτ k) W K ≤ A * frostmanConstIn (fibre u0 pτ k) W K := by
  intro k K hK
  by_cases hk : k ∈ v'τ
  · exact h k hk K hK
  · rw [frostmanConstIn_fibre_eq_zero_of_notMem hmaps hk]
    exact zero_le

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The coarse node family is a parent family for the leaves** (blueprint
`lem:ml1bootCoarseParentFamilyForLeaves`, item (d)).

If `(uτ, 𝕋_τ, pτ)` is a parent family for `𝕋|_u` at the scale `τ` and `(uθ, 𝕋_θ, pθ)` is one for
`𝕋_τ|_{uτ}` at the scale `θ`, then `(uθ, 𝕋_θ, pθ ∘ pτ)` is a parent family for `𝕋|_u` at `θ`.

*This is the item that does work.*  It is what lets every application of
`Kakeya.ml1Boot.exists_essDistinct_parentFamily` in the repair chain be made to the **leaf**
family at both scales.  That is forced rather than convenient: that citation consumes a *uniform
shaded* family, uniformity is not inherited by subfamilies, and the `τ`-nodes carry no shading at
all, so the coarse application can be made neither to the output of the fine one nor to `𝕋_τ`
(blueprint `note:ml1bootRepairEDCoarseShading`).

The blueprint's items (b) and (c) are the two hypotheses here, and its item (a) — the identity
`assign_a = pθ ∘ assign_b` of `Kakeya.ml1Boot.IsCoarseNodeParents.assign_comp` — is definitional
once the composite is written out, so this free-standing form carries the whole of that lemma.
Injectivity of the composed family is that of the coarse one, untouched; the containment clause is
the two containments chained. -/
theorem IsParentFamily.comp {ι κ μ : Type*} {δ τ θ : NNReal} {u : Finset ι} {T : ι → Tube δ E}
    {uτ : Finset κ} {Tτ : κ → Tube τ E} {pτ : ι → κ}
    {uθ : Finset μ} {Tθ : μ → Tube θ E} {pθ : κ → μ}
    (hfine : IsParentFamily u T uτ Tτ pτ) (hcoarse : IsParentFamily uτ Tτ uθ Tθ pθ) :
    IsParentFamily u T uθ Tθ (fun i => pθ (pτ i)) :=
  { mapsTo := fun i hi => hcoarse.mapsTo (pτ i) (hfine.mapsTo i hi)
    injOn := hcoarse.injOn
    le_parent := fun i hi =>
      (hfine.le_parent i hi).trans (hcoarse.le_parent (pτ i) (hfine.mapsTo i hi)) }

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The trim: restoring the node-level containment after a leaf-level refinement** (blueprint
`lem:ml1bootParentTrim`).

A refinement that prices only *leaves* delivers the two **leaf**-level containments
`{pτ i : i ∈ u} ⊆ uτ` and `{pθ (pτ i) : i ∈ u} ⊆ uθ`, here read as the parent family `hfine`
together with `hleaf`.  It does **not** deliver the node-level one `{pθ k : k ∈ uτ} ⊆ uθ`, which
is *false in general*: `uτ` may contain a node over which no retained leaf lies, and `pθ` may
carry that node outside `uθ`.  This is the point on which an earlier form of the (R2) statement
was retracted (blueprint `lem:ml1bootRepairUniform`; its intended producer
`Kakeya.ml1Boot.exists_repairUniform` is not a declaration — see the module docstring).

Trimming to `u⁺τ = {k ∈ uτ : pθ k ∈ uθ}` restores it, at no cost to the leaves: every `pτ i` with
`i ∈ u` survives the trim, by `hleaf`.  The coarse parent family is asked for at the *ambient*
node set `tθ ⊇ uθ`, which is the shape a caller has — it holds at the full node families, `pθ`
being total — and `hsub` is what carries its injectivity down to `uθ`.

With the trim in hand both hypotheses of `Kakeya.ml1Boot.IsParentFamily.comp` hold for `u`,
`u⁺τ`, `uθ`, so the composed coarse family for the leaves is available too. -/
theorem isParentFamily_trim {ι κ : Type*} [DecidableEq κ] {δ τ θ : NNReal}
    {u : Finset ι} {T : ι → Tube δ E} {uτ tθ uθ : Finset κ} {Tτ : κ → Tube τ E} {pτ : ι → κ}
    {Tθ : κ → Tube θ E} {pθ : κ → κ}
    (hfine : IsParentFamily u T uτ Tτ pτ) (hcoarse : IsParentFamily uτ Tτ tθ Tθ pθ)
    (hleaf : ∀ i ∈ u, pθ (pτ i) ∈ uθ) (hsub : uθ ⊆ tθ) :
    IsParentFamily u T (uτ.filter fun k => pθ k ∈ uθ) Tτ pτ ∧
      IsParentFamily (uτ.filter fun k => pθ k ∈ uθ) Tτ uθ Tθ pθ := by
  have hfilter : (uτ.filter fun k => pθ k ∈ uθ) ⊆ uτ := Finset.filter_subset _ _
  refine ⟨⟨?_, ?_, hfine.le_parent⟩, ?_, ?_, ?_⟩
  · exact fun i hi => Finset.mem_filter.mpr ⟨hfine.mapsTo i hi, hleaf i hi⟩
  · exact hfine.injOn.mono (Finset.coe_subset.mpr hfilter)
  · exact fun k hk => (Finset.mem_filter.mp hk).2
  · exact hcoarse.injOn.mono (Finset.coe_subset.mpr hsub)
  · exact fun k hk => hcoarse.le_parent k (hfilter hk)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A parent family restricts, on both sides at once** (blueprint
`lem:ml1bootParentFamilyMono`).

Both non-index clauses of `Kakeya.ml1Boot.IsParentFamily` are conditions on individual members —
that each member lie in the body its parent names, and that the parent bodies be distinct — so
both descend to `u ⊆ s` and `t' ⊆ t`.  What does *not* descend is `mapsTo`, which is why it is a
hypothesis here: a smaller parent set need not receive the smaller leaf set.

This is the move the three-pass assembly makes four times, once for each of the two output parent
families of blueprint `lem:ml1bootRepairThreePass`, item (c), whose containments the passes supply
while the other two clauses have to be restricted from the ambient families. -/
theorem IsParentFamily.mono {ι κ : Type*} {δ ρ : NNReal} {s u : Finset ι} {T : ι → Tube δ E}
    {t t' : Finset κ} {Vρ : κ → Tube ρ E} {p : ι → κ}
    (h : IsParentFamily s T t Vρ p) (hu : u ⊆ s) (ht : t' ⊆ t)
    (hmaps : ∀ i ∈ u, p i ∈ t') :
    IsParentFamily u T t' Vρ p :=
  { mapsTo := hmaps
    injOn := h.injOn.mono (Finset.coe_subset.mpr ht)
    le_parent := fun i hi => h.le_parent i (hu hi) }

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Bounded overlap passes to a subfamily of the leaves** (blueprint
`lem:ml1bootBoundedOverlapMono`, the leaf half).

`Kakeya.ml1Boot.HasBoundedOverlap s 𝕍 t 𝕍_ρ Co` counts, for each `ρ`-tube `W`, the parents that
meet `W` *through `𝕍`*; the set it counts at `u ⊆ s` is cut out of the same `t` by a condition
existentially quantified over `u` rather than over `s`, hence is a subset of the one counted at
`s`, hence has cardinality at most `Co` as well.

Only the leaf half is stated, because only it is used: blueprint `lem:ml1bootRepairThreePass`
hands move (R1) the *full* node families and a leaf set `s₁ ⊆ s'` shrunk by the (R2) pass before
it, so what has to be restricted is the leaf index and never the parent index. -/
theorem HasBoundedOverlap.mono_leaves {ι κ : Type*} {σ ρ : NNReal} {s u : Finset ι}
    {V : ι → Tube σ E} {t : Finset κ} {Vρ : κ → Tube ρ E} {Co : NNReal}
    (h : HasBoundedOverlap s V t Vρ Co) (hu : u ⊆ s) :
    HasBoundedOverlap u V t Vρ Co := by
  classical
  unfold HasBoundedOverlap
  intro W
  exact le_trans (by
    exact_mod_cast
      (Finset.card_le_card (by
        intro k hk
        simp only [Finset.mem_filter] at hk ⊢
        exact ⟨hk.1, by
          rcases hk.2 with ⟨i, hi, hiv⟩
          exact ⟨i, hu hi, hiv⟩⟩))) (h W)

/-- **Fibrewise Frostman transports compose along a chain of leaf sets** (blueprint
`lem:ml1bootFibreTransportChain`).

The content is the side condition and not the chaining.  Each hypothesis states its side condition
at its *own* input fibre, which is the shape `Kakeya.ml1Boot.IsRepairUniformPass.fibreFrostman`
and `Kakeya.ml1Boot.IsRepairEssDistinctPass.fibreFrostman` have; it is the nesting of the leaf
sets that makes all three side conditions follow from the single one assumed at `u₀`, a fibre
being cut out of a leaf set by a condition on `i` alone.

Only `u₁ ⊆ u₀` and `u₂ ⊆ u₁` are asked for.  The blueprint states the lemma along the full chain
`u₃ ⊆ u₂ ⊆ u₁ ⊆ u₀`, but the last inclusion is not used: no side condition is read at `u₃`, the
third transport delivering the bound there outright.  Asking for it would leave an unused
argument.

Stated at a fixed `k` and quantified over `K`, which is the shape blueprint
`lem:ml1bootRepairThreePass` item (e) consumes. -/
theorem fibreFrostman_chain {ι κ : Type*} [DecidableEq κ] {u0 u1 u2 u3 : Finset ι}
    {pτ : ι → κ} {A1 A2 A3 : ENNReal} (h1 : u1 ⊆ u0) (h2 : u2 ⊆ u1)
    (W : ι → ConvexSpaceBody E) {k : κ}
    (t1 : ∀ K : ConvexSpaceBody E, (∀ i ∈ fibre u0 pτ k, W i ≤ K) →
      frostmanConstIn (fibre u1 pτ k) W K ≤ A1 * frostmanConstIn (fibre u0 pτ k) W K)
    (t2 : ∀ K : ConvexSpaceBody E, (∀ i ∈ fibre u1 pτ k, W i ≤ K) →
      frostmanConstIn (fibre u2 pτ k) W K ≤ A2 * frostmanConstIn (fibre u1 pτ k) W K)
    (t3 : ∀ K : ConvexSpaceBody E, (∀ i ∈ fibre u2 pτ k, W i ≤ K) →
      frostmanConstIn (fibre u3 pτ k) W K ≤ A3 * frostmanConstIn (fibre u2 pτ k) W K) :
    ∀ K : ConvexSpaceBody E, (∀ i ∈ fibre u0 pτ k, W i ≤ K) →
      frostmanConstIn (fibre u3 pτ k) W K
        ≤ A1 * A2 * A3 * frostmanConstIn (fibre u0 pτ k) W K := by
  intro K hK
  have hfib_mono : ∀ {u v : Finset ι}, u ⊆ v → fibre u pτ k ⊆ fibre v pτ k := by
    intro u v huv i hi
    rcases Finset.mem_filter.mp hi with ⟨hiu, hik⟩
    exact Finset.mem_filter.mpr ⟨huv hiu, hik⟩
  have hK1 : ∀ i ∈ fibre u1 pτ k, W i ≤ K := by
    intro i hi
    exact hK i (hfib_mono h1 hi)
  have hK2 : ∀ i ∈ fibre u2 pτ k, W i ≤ K := by
    intro i hi
    exact hK i (hfib_mono (h2.trans h1) hi)
  calc
    frostmanConstIn (fibre u3 pτ k) W K ≤ A3 * frostmanConstIn (fibre u2 pτ k) W K := t3 K hK2
    _ ≤ A3 * (A2 * frostmanConstIn (fibre u1 pτ k) W K) := by
      exact mul_le_mul_right (t2 K hK1) A3
    _ ≤ A3 * (A2 * (A1 * frostmanConstIn (fibre u0 pτ k) W K)) := by
      exact mul_le_mul_right (mul_le_mul_right (t1 K hK) A2) A3
    _ = A1 * A2 * A3 * frostmanConstIn (fibre u0 pτ k) W K := by
      ring

/-! ### Move (R2): the uniformization pass -/

/-- **The conclusions the (R2) pass was to deliver, one field per inequality** (blueprint
`lem:ml1bootRepairUniform`, items (a)–(e)).

The intended producer is `Kakeya.ml1Boot.exists_repairUniform`, which is not a declaration:
see the module docstring, where the refutation and the deletion are recorded.

Here `(𝕋, Y)` is a family of shaded `δ`-tubes indexed by `s`, `(tτ, 𝕋_τ, pτ)` is a parent
family for it at the scale `τ` and `(tθ, 𝕋_θ, pθ)` one for `𝕋_τ` at the scale `θ`; the pass
returns `s' ⊆ s`, `t'τ ⊆ tτ`, `t'θ ⊆ tθ` and a shade density `λ' > 0`.

As elsewhere in this development a blueprint item that is a conjunction of several inequalities
becomes several fields, so that consumers name what they use.  The blueprint's items (a)–(e) are
`refinement`/`card`, `unif`/`dens`/`lamGe`, the three `essDistinct*`,
`parentFine`/`parentCoarse`, and `fibreFrostman`.  There is no sixth item; the blueprint lemma
above is where what the pass deliberately does not conclude is recorded. -/
structure IsRepairUniformPass {ι κ : Type*} [DecidableEq κ] {δ τ θ : NNReal} (ε' : ℝ)
    (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ) (Tθ : κ → Tube θ E) (pθ : κ → κ)
    (s : Finset ι) (tτ tθ : Finset κ)
    (s' : Finset ι) (t'τ t'θ : Finset κ) (lam' : NNReal) : Prop where
  /-- (a) `(𝕋|_{s'}, Y)` is a `δ ^ ε'`-refinement of `(𝕋|_{s}, Y)`. -/
  refinement : ShadedBody.IsCRefinement s' (fun i => (T i).toShadedBody) s
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩
  /-- (a) …and retains all but a `δ ^ (-ε')` share of the index set.  Stated in `ℝ`, which is
  the spelling `Kakeya.ml1Boot.repairCountChain` reads. -/
  card : (s.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s'.card : ℝ)
  /-- (b) The retained family is uniform, at the dimension-only constant
  `Kakeya.ml1Boot.uniformize.C 3`.  `ShadedTube.ShadedUniformTubeSet` is data-valued, so the
  `Prop`-valued clause is its `Nonempty`.  This is the clause move (R1) consumes and which the
  source's ordering left unsupplied (blueprint
  `note:ml1bootRepairEDLeafShadedUniformity`). -/
  unif : Nonempty (ShadedTube.ShadedUniformTubeSet s' T (Tube.ssfGridLen δ)
    (uniformize.C 3))
  /-- (b) The shading densities on `s'` are two-sidedly comparable to `λ'`.

  **This is the clause that refutes the (R2) statement.**  Its lower half asserts a positive
  lower bound on a shading, at a leaf set the retracted statement's own conclusion forced
  nonempty, while that statement hypothesised nothing whatever about the shadings.  The
  refutation is `Kakeya.ml1Boot.not_exists_repairUniform`, which spells the statement out
  inline; the name `Kakeya.ml1Boot.exists_repairUniform` is the intended producer's and is not
  a declaration, so nothing here is a claim about one.  The field is *correct as a field* — a
  pass that assumed a density bracket at its input could deliver it — and it is the pass's
  hypotheses, not this clause, that are defective, so the structure is left as it stands.

  *No consumer reads `λ'` today*: `Kakeya.ml1Boot.repairCountChain` reads its banding from
  `Kakeya.ml1Boot.IsCaseTwoInput.band` instead, which every subfamily inherits and which costs
  no exponent. -/
  dens : ∀ i ∈ s', (lam' : ENNReal) * volume (T i).carrier ≤ volume (T i).shade ∧
    volume (T i).shade ≤ 2 * (lam' : ENNReal) * volume (T i).carrier
  /-- (b) …and `λ'` is itself at least `δ ^ ε'` times the fullness of the input family, which is
  the half of the blueprint's `λ' ≥ δ ^ ε' λ(𝕋|_ŝ)` that relates the output banding to the
  input's. -/
  lamGe : (δ : ENNReal) ^ ε' * ShadedBody.fullness s (fun i => (T i).toShadedBody)
    ≤ (lam' : ENNReal)
  /-- (c) Essential distinctness of the leaves is inherited. -/
  essDistinctLeaf : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
    (s' : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
  /-- (c) Essential distinctness of the `τ`-nodes is inherited; free, essential distinctness
  being a condition on pairs and `t'τ ⊆ tτ`. -/
  essDistinctFine : (tτ : Set κ).Pairwise
      (fun k k' => IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier) →
    (t'τ : Set κ).Pairwise (fun k k' => IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier)
  /-- (c) Essential distinctness of the `θ`-nodes is inherited, for the same reason. -/
  essDistinctCoarse : (tθ : Set κ).Pairwise
      (fun l l' => IsEssentiallyDistinct (Tθ l).carrier (Tθ l').carrier) →
    (t'θ : Set κ).Pairwise (fun l l' => IsEssentiallyDistinct (Tθ l).carrier (Tθ l').carrier)
  /-- (d) `(t'τ, 𝕋_τ, pτ)` is again a parent family, for the retained leaves at scale `τ`.  Its
  `mapsTo` clause is the leaf-level containment `{pτ i : i ∈ s'} ⊆ t'τ`. -/
  parentFine : IsParentFamily s' (fun i => (T i).toTube) t'τ Tτ pτ
  /-- (d) `(t'θ, 𝕋_θ, pθ)` is again a parent family, for the retained `τ`-nodes at scale `θ`.
  Its `mapsTo` clause is the **node**-level containment `{pθ k : k ∈ t'τ} ⊆ t'θ`, which holds
  only for the *trimmed* fine set `t'τ = {k ∈ u_τ : pθ k ∈ u_θ}` and is false for the untrimmed
  one; see the module docstring. -/
  parentCoarse : IsParentFamily t'τ Tτ t'θ Tθ pθ
  /-- (e) The Frostman constant of every retained fine fibre grows by at most `δ ^ (-ε')`, the
  side condition being stated at the **fibre** and not at the whole family — which is the shape
  the repair consumes. -/
  fibreFrostman : ∀ k ∈ t'τ, ∀ K : ConvexSpaceBody E,
    (∀ i ∈ fibre s pτ k, (T i).toConvexSpaceBody ≤ K) →
    frostmanConstIn (fibre s' pτ k) (fun i => (T i).toConvexSpaceBody) K
      ≤ (δ : ENNReal) ^ (-ε')
        * frostmanConstIn (fibre s pτ k) (fun i => (T i).toConvexSpaceBody) K

/-- **Uniformity caps the spread of the pointwise shade-class counts by `C ^ 4`** (blueprint
`lem:ml1bootShadedUniformSpreadCap`).

The four brackets of `ShadedTube.ShadedUniformTubeSet` chained: for any two points `x`, `y` of
the shade union and any two indices `i`, `j` whose shadings contain them,

  `#shadeClass(i, x) ≤ C·localN x ≤ C²·branchingN ≤ C³·localN y ≤ C⁴·#shadeClass(j, y)`.

So a uniform shaded family has a pointwise shade-class count that is *constant up to `C ^ 4`*,
across points and across indices at once — the shared `branchingN` being what couples the two
ends.  Nothing geometric is used; this is the four fields and `NNReal` arithmetic.

**This is the engine of the second obstruction to move (R2)**, recorded in the module docstring
above — the intended producer `Kakeya.ml1Boot.exists_repairUniform` is not a declaration and so
has no docstring — and, for the sibling statement, in
`Kakeya.ml1Boot.not_exists_uniformRefinement`.  The obstruction is that
`Kakeya.ml1Boot.IsRepairUniformPass.unif` asserts uniformity at the shading it is *handed*, and
the cap above is a property no hypothesis on that shading can supply: take indices carrying the
same carrier with *nested* shadings of pairwise comparable volume, so that the density bracket
holds on every subfamily, and read the cap at an index minimal in its cover class — at a point
of the innermost shading `#shadeClass` is the whole class, at a point of the outermost it is `1`,
so the class has at most `C ^ 4` members whatever subfamily was retained.  Formalizing that
witness is what would turn "unobtainable" into "false"; this lemma is the half of it that needs
no geometry.

Stated with the two readings at *different* indices, which is more than the witness needs and is
what makes the cap a statement about the family rather than about one class. -/
theorem card_shadeClass_le_card_shadeClass {δ : NNReal} {ι : Type*} {s : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {C : NNReal}
    (𝒱 : ShadedTube.ShadedUniformTubeSet s V N C)
    {k : ℕ} (hk : k ≤ N) {x y : E}
    (hx : x ∈ ⋃ i ∈ s, (V i).shade) (hy : y ∈ ⋃ i ∈ s, (V i).shade)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hxi : x ∈ (V i).shade) (hyj : y ∈ (V j).shade) :
    ((ShadedTube.shadeClass s V (𝒱.tubeUniform.cover.assign k)
          (𝒱.tubeUniform.cover.assign k i) x).card : NNReal)
      ≤ C ^ 4 * ((ShadedTube.shadeClass s V (𝒱.tubeUniform.cover.assign k)
          (𝒱.tubeUniform.cover.assign k j) y).card : NNReal) := by
  calc
    ((ShadedTube.shadeClass s V (𝒱.tubeUniform.cover.assign k)
          (𝒱.tubeUniform.cover.assign k i) x).card : NNReal)
        ≤ C * 𝒱.localN x k := 𝒱.card_shadeClass_le x hx k hk i hi hxi
    _ ≤ C * (C * 𝒱.branchingN k) := by
        gcongr
        exact 𝒱.le_branchingN x hx k hk
    _ ≤ C * (C * (C * 𝒱.localN y k)) := by
        gcongr
        exact 𝒱.branchingN_le y hy k hk
    _ ≤ C * (C * (C * (C * ((ShadedTube.shadeClass s V (𝒱.tubeUniform.cover.assign k)
          (𝒱.tubeUniform.cover.assign k j) y).card : NNReal)))) := by
        gcongr
        exact 𝒱.le_card_shadeClass y hy k hk j hj hyj
    _ = C ^ 4 * ((ShadedTube.shadeClass s V (𝒱.tubeUniform.cover.assign k)
          (𝒱.tubeUniform.cover.assign k j) y).card : NNReal) := by
        ring

/-- **An empty-shaded `ρ`-tube in `B₁ ⊆ ℝ³`, together with a `1`-tube containing it.**

The tube whose core is the segment from `-e/2` to `e/2`, with `e` the first standard basis
vector, shaded by `∅`, at an arbitrary radius `ρ ∈ (0, 1/2]`; and the same core read at radius
`1`.  The core lies in the ball of radius `1/2` about the origin, so the closed
`ρ`-neighbourhood — the carrier — lies in `B₁`; and the carrier contains the ball of radius `ρ`
about the core's endpoint, so it has positive volume.  Since `ρ ≤ 1` the carrier is contained in
the wider tube's.

This is the witness of `Kakeya.ml1Boot.not_exists_repairUniform`, which needs the counterexample
at a radius it does not choose: the leaf scale there is the smallness parameter `δ` itself, and
not a free second scale, so the fixed-radius
`Kakeya.ml1Boot.exists_emptyShadedHalfTube` is not applicable.  The `1`-tube `P` is what turns
the single leaf into a two-scale parent tower: `(fun _ => P)` is a parent family for it at every
scale, both parent index sets being singletons, so all the parent hypotheses of a pass are
available at no cost. -/
theorem exists_emptyShadedTubeTower {ρ : NNReal} (hρ0 : 0 < ρ) (hρ : ρ ≤ 1 / 2) :
    ∃ (V : ShadedTube ρ (EuclideanSpace ℝ (Fin 3)))
      (P : Tube 1 (EuclideanSpace ℝ (Fin 3))),
      V.carrier ⊆ Metric.closedBall 0 1 ∧ V.shade = ∅ ∧ 0 < volume V.carrier ∧
        V.toTube.toConvexSpaceBody ≤ P.toConvexSpaceBody := by
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
  have hseg : segment ℝ p q ⊆ Metric.closedBall 0 (1 / 2 : ℝ) :=
    Convex.segment_subset hconv hp_ball hq_ball
  let T : Tube ρ (EuclideanSpace ℝ (Fin 3)) :=
    Tube.mk' ρ (x := p) (y := q) hdist
  let P : Tube 1 (EuclideanSpace ℝ (Fin 3)) :=
    Tube.mk' 1 (x := p) (y := q) hdist
  let V : ShadedTube ρ (EuclideanSpace ℝ (Fin 3)) :=
    { toTube := T
      shade := ∅
      measurableSet_shade := MeasurableSet.empty
      shade_subset := Set.empty_subset _ }
  have hρ1 : ρ ≤ 1 := le_trans hρ (by norm_num)
  have hρ1R : (ρ : ℝ) ≤ 1 := by exact_mod_cast hρ1
  refine ⟨V, P, ?_, ?_, ?_, ?_⟩
  · intro w hw
    dsimp [V, T] at hw
    change w ∈ ⋃ z ∈ segment ℝ p q, Metric.closedBall z (ρ : ℝ) at hw
    rw [Set.mem_iUnion₂] at hw
    rcases hw with ⟨z, hz, hwz⟩
    have hwz' : dist w z ≤ (ρ : ℝ) := Metric.mem_closedBall.mp hwz
    have hz_ball : z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ) := hseg hz
    have hz0 : dist z 0 ≤ 1 / 2 := Metric.mem_closedBall.mp hz_ball
    have hw0 : dist w 0 ≤ 1 := by
      calc
        dist w 0 ≤ dist w z + dist z 0 := dist_triangle w z 0
        _ ≤ (ρ : ℝ) + (1 / 2 : ℝ) := by gcongr
        _ ≤ 1 := by
          have hρR : (ρ : ℝ) ≤ 1 / 2 := by exact_mod_cast hρ
          linarith
    exact Metric.mem_closedBall.mpr hw0
  · rfl
  · have hsubT : Metric.closedBall p (ρ : ℝ) ⊆ T.carrier := by
      rw [T.carrier_eq]
      exact Set.subset_iUnion₂ (s := fun z _ => Metric.closedBall z (ρ : ℝ)) p
        (left_mem_segment ℝ p q)
    have hsub : Metric.closedBall p (ρ : ℝ) ⊆ V.carrier := by
      simpa [V] using hsubT
    have hpos : 0 < volume (Metric.closedBall p (ρ : ℝ)) := by
      exact Metric.measure_closedBall_pos volume p (by exact_mod_cast hρ0)
    exact lt_of_lt_of_le hpos (measure_mono hsub)
  · intro w hw
    dsimp [V, T] at hw
    change w ∈ ⋃ z ∈ segment ℝ p q, Metric.closedBall z (ρ : ℝ) at hw
    rw [Set.mem_iUnion₂] at hw
    rcases hw with ⟨z, hz, hwz⟩
    dsimp [P]
    change w ∈ ⋃ z ∈ segment ℝ p q, Metric.closedBall z (1 : ℝ)
    rw [Set.mem_iUnion₂]
    exact ⟨z, hz, Metric.closedBall_subset_closedBall hρ1R hwz⟩

/-- **(negative result) The (R2) statement is false: it bounds the shading densities from below
without assuming anything about them.**

The refuted statement is spelled out inline below, and is the one the intended producer
`Kakeya.ml1Boot.exists_repairUniform` (blueprint `lem:ml1bootRepairUniform`) was to carry; that
name is not a declaration — see the module docstring.  It is read at
`E = EuclideanSpace ℝ (Fin 3)`, with

* the two node outputs `t'τ`, `t'θ` and their containments dropped, and
* only `s'.Nonempty`, the positivity `0 < lam'` and the *lower* half of
  `Kakeya.ml1Boot.IsRepairUniformPass.dens` retained.  Every other clause — `refinement`,
  `card`, `unif`, `lamGe`, the three `essDistinct*`, `parentFine`, `parentCoarse` and
  `fibreFrostman` — is discarded, which makes this a refutation of a strictly weaker statement,
  and therefore of the (R2) statement itself.

Instantiate at `τ = θ = 1`, `ι = κ = Unit`, `s = tτ = tθ = {}`, `pτ = fun _ => `,
`pθ = id`, and at the empty-shaded leaf and its `1`-tube parent from
`Kakeya.ml1Boot.exists_emptyShadedTubeTower`, read at the small `δ` the smallness quantifier
supplies (`Kakeya.ml1Boot.exists_small_of_eventually_nhdsGT`, which gives `0 < δ ≤ 1/2`).  Both
parent-family hypotheses hold: the containments are containments of one tube in a wider tube
with the same core, and injectivity is injectivity on a singleton.  The `B₁` containment holds
by construction.  But `s'` is nonempty, so the density clause reads
`lam' * volume (V ).carrier ≤ volume ∅ = 0` with `lam' > 0` and `volume (V ).carrier > 0`.

*Why the two parent families cost nothing.*  It is worth being explicit that the refutation is
not an artefact of degenerate parent data.  `Kakeya.ml1Boot.IsParentFamily` asks only for a
containment and an injectivity, both of which a singleton node set satisfies for free, so the
parent hypotheses of the pass cannot exclude the counterexample; and the same configuration
survives replacing the singleton by any family of essentially distinct empty-shaded tubes.  The
defect is exactly the missing shading-density hypothesis, and nothing else.

The hypothesis `0 < ε'` is carried so that this is an instance of the refuted statement and not
something weaker; it happens to be unused, `ε'` appearing in no retained clause. -/
theorem not_exists_repairUniform {ε' : ℝ} (_hε' : 0 < ε') :
    ¬ ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ τ θ : NNReal, δ ≤ τ → τ ≤ θ → θ ≤ 1 →
        ∀ {ι κ : Type} [DecidableEq κ] {s : Finset ι} {tτ tθ : Finset κ}
          (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
          (Tτ : κ → Tube τ (EuclideanSpace ℝ (Fin 3))) (pτ : ι → κ)
          (Tθ : κ → Tube θ (EuclideanSpace ℝ (Fin 3))) (pθ : κ → κ),
          s.Nonempty →
          (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
          IsParentFamily s (fun i => (T i).toTube) tτ Tτ pτ →
          IsParentFamily tτ Tτ tθ Tθ pθ →
          ∃ s' ⊆ s, ∃ lam' : NNReal, 0 < lam' ∧ s'.Nonempty ∧
            ∀ i ∈ s', (lam' : ENNReal) * volume (T i).carrier ≤ volume (T i).shade := by
  intro hE
  obtain ⟨d, dP, dH, dS⟩ := exists_small_of_eventually_nhdsGT hE
  obtain ⟨V, P, hV, hsh, hvol, hle⟩ := exists_emptyShadedTubeTower dP dH
  let T : Unit → ShadedTube d (EuclideanSpace ℝ (Fin 3)) := fun _ => V
  have hd1 : d ≤ 1 := le_trans dH (by norm_num)
  have hBall : ∀ i ∈ ({()} : Finset Unit), (T i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i _
    simpa [T] using hV
  have hFine : IsParentFamily ({()} : Finset Unit) (fun i : Unit => (T i).toTube)
      ({()} : Finset Unit) (fun _ : Unit => P) (fun _ : Unit => ()) := by
    constructor
    · intro i _
      simp
    · intro a _ b _ _
      exact Subsingleton.elim a b
    · intro i _
      simpa [T] using hle
  have hCoarse : IsParentFamily ({()} : Finset Unit) (fun _ : Unit => P)
      ({()} : Finset Unit) (fun _ : Unit => P) (id) := by
    constructor
    · intro k hk
      simp
    · intro a _ b _ _
      exact Subsingleton.elim a b
    · intro k _
      rfl
  have hD := dS 1 1 hd1 (by norm_num : (1 : NNReal) ≤ 1) (by norm_num : (1 : NNReal) ≤ 1)
      (ι := Unit) (κ := Unit) (s := ({()} : Finset Unit))
      (tτ := ({()} : Finset Unit)) (tθ := ({()} : Finset Unit))
      T (fun _ => P) (fun _ => ()) (fun _ => P) (id)
      (Finset.singleton_nonempty ()) hBall hFine hCoarse
  rcases hD with ⟨sp, hSub, lam, hLam0, hS, hDen⟩
  obtain ⟨i, hi⟩ := hS
  have hL : 0 < (lam : ENNReal) := ENNReal.coe_pos.mpr hLam0
  have hM : 0 < (lam : ENNReal) * volume V.carrier :=
    ENNReal.mul_pos (ne_of_gt hL) (ne_of_gt hvol)
  have hD0 : (lam : ENNReal) * volume V.carrier ≤ volume V.shade := by
    simpa [T] using hDen i hi
  have hNon : ¬ (lam : ENNReal) * volume V.carrier ≤ volume V.shade := by
    have hz : volume V.shade = (0 : ENNReal) := by
      simp [hsh]
    rw [hz]
    exact not_le_of_gt hM
  exact hNon hD0

/-! ### Move (R1): essential distinctness at both parent scales -/

/-- **The conclusions of `Kakeya.ml1Boot.exists_repairEssDistinct`, one field per clause**
(blueprint `lem:ml1bootRepairEssDistinct`, items (a)–(c)).

Here `(𝕋, Y)` is a family of shaded `δ`-tubes indexed by `s`, `pτ` is the `τ`-parent map and `pθ`
the `θ`-parent map on the `τ`-nodes, `w` is the caller's weight on the leaves, and the pass
returns `s' ⊆ s`, `t'τ` and `t'θ`.

As elsewhere in this development a blueprint item that is a conjunction becomes several fields, so
that consumers name what they use.  Item (a) is `weight`/`parentFine`/`parentCoarse` — the two
containments of that item being the `Kakeya.ml1Boot.IsParentFamily.mapsTo` clauses of the latter
two — item (b) is the two `essDistinct*`, and item (c) is `fibreFrostman`. -/
structure IsRepairEssDistinctPass {ι κ : Type*} [DecidableEq κ] {δ τ θ : NNReal} (ε' : ℝ)
    (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ) (Tθ : κ → Tube θ E) (pθ : κ → κ)
    (w : ι → ENNReal) (s s' : Finset ι) (t'τ t'θ : Finset κ) : Prop where
  /-- (a) The caller's weight is retained up to `δ ^ ε'`.  *One* weight: no essentially distinct
  selection retains a constant share of two incomparable weights, which is why
  `Kakeya.ml1Boot.exists_essDistinct_parentFamily` takes `w` as a parameter and why this pass
  passes it on rather than fixing it. -/
  weight : (δ : ENNReal) ^ ε' * (∑ i ∈ s, w i) ≤ ∑ i ∈ s', w i
  /-- (a) `(t'τ, 𝕋_τ, pτ)` is again a parent family, for the retained leaves at scale `τ`. -/
  parentFine : IsParentFamily s' (fun i => (T i).toTube) t'τ Tτ pτ
  /-- (a) `(t'θ, 𝕋_θ, pθ)` is again a parent family, for the retained `τ`-nodes at scale `θ`. -/
  parentCoarse : IsParentFamily t'τ Tτ t'θ Tθ pθ
  /-- (b) The retained `τ`-nodes are pairwise essentially distinct. -/
  essDistinctFine : (t'τ : Set κ).Pairwise
    (fun k l => IsEssentiallyDistinct (Tτ k).carrier (Tτ l).carrier)
  /-- (b) The retained `θ`-nodes are pairwise essentially distinct. -/
  essDistinctCoarse : (t'θ : Set κ).Pairwise
    (fun k l => IsEssentiallyDistinct (Tθ k).carrier (Tθ l).carrier)
  /-- (c) The fine Frostman constants transport **fibrewise**, with the side condition stated at
  the pass's own *input* fibre.

  This is a transport and not an absolute bound: the leaf family is a parameter, so no raw bound
  is available to read, and none is needed — it composes with the raw bound and with the
  transports of the (R2) passes on either side, the composition being done once at the call
  site. -/
  fibreFrostman : ∀ k ∈ t'τ, ∀ K : ConvexSpaceBody E,
    (∀ i ∈ fibre s pτ k, (T i).toConvexSpaceBody ≤ K) →
    frostmanConstIn (fibre s' pτ k) (fun i => (T i).toConvexSpaceBody) K
      ≤ (δ : ENNReal) ^ (-ε')
        * frostmanConstIn (fibre s pτ k) (fun i => (T i).toConvexSpaceBody) K

/-- **Case (ii) repair, move (R1): essential distinctness at both scales** (blueprint
`lem:ml1bootRepairEssDistinct`).

There is a dimensional constant `c > 0` such that the following holds.  Let `ε' > 0`, let `Cunif`
be a uniformity constant and `Co ≥ 1` an overlap constant.  Then for all
sufficiently small `δ > 0`: given a nonempty family `(𝕋, Y)` of shaded `δ`-tubes in `B₁ ⊆ ℝ³`
indexed by `s`, **uniform and with pairwise essentially distinct members**, a parent family
`(tτ, 𝕋_τ, pτ)` for it at a scale `τ ≥ δ` **with `δ ^ (ε'/2) ≤ c τ / Co`**, a parent family
`(tθ, 𝕋_θ, pθ)` for `𝕋_τ` at a scale `θ ∈ [τ, 1]`, both of bounded overlap over the leaves, and
any weight `w`, there are `s' ⊆ s`, `t'τ ⊆ tτ` and `t'θ ⊆ tθ` with
`Kakeya.ml1Boot.IsRepairEssDistinctPass` holding.

## The scale hypothesis, and why it is at `ε'/2` and at `τ`

> An earlier form of this statement omitted the scale hypothesis and **was false**.  It applied
> `Kakeya.ml1Boot.exists_essDistinct_parentFamily` over the whole ladder `δ ≤ τ ≤ θ ≤ 1`, hence
> also at `τ ≍ δ ^ (1/2)`, which is inside the regime the axial pencil of
> `Kakeya.ml1Boot.not_exists_essDistinct_parentFamily` occupies; a proof over a false premise
> establishes nothing, so nothing was lost in adding the hypothesis and a false belief was
> corrected.

The citation retains a `c ρ / Co` share of the caller's weight and no more — see its docstring —
so each of the two selections may be run only where `δ` raised to *its own* exponent is at most
that share.  Both are run at `ε' / 2`, which is why the exponent here is `ε' / 2` and not `ε'`:
the two halves compose to the `δ ^ ε'` of
`Kakeya.ml1Boot.IsRepairEssDistinctPass.weight`, and since `δ ≤ 1` the hypothesis at `ε'` would
be the weaker statement and would not discharge either application.  One hypothesis suffices for
both scales because it is asked at the *fine* scale `τ ≤ θ`, and `c τ / Co ≤ c θ / Co`.

The constant `c` is the citation's own, passed on unchanged; it is existentially quantified
outside `ε'`, `Cunif` and `Co` for the reasons given in that docstring, chief among them that
only the upper bound on the achievable retention is proved and pinning a numeral would risk
restoring the falsity this hypothesis removes.

## The uniformity is a hypothesis, and the caller discharges it by running (R2) first

Both applications of `Kakeya.ml1Boot.exists_essDistinct_parentFamily` in the proof consume the
shaded uniformity of the family they run on, and the Case (ii) bundle does not supply it at `s`:
that was blueprint `note:ml1bootRepairEDLeafShadedUniformity`.  It is therefore *assumed* here, on
a leaf set the caller names, and the caller is to discharge it by running move (R2) first: the
(R2) output is uniform by construction and the pass takes no uniformity hypothesis of its own.
That reordering is blueprint `note:ml1bootRepairOrderGWZ`, and it is the whole reason this
declaration may be stated at all.  No caller does so today — the intended producer
`Kakeya.ml1Boot.exists_repairUniform` is not a declaration, and the statement it was to carry is
refuted; see the module docstring.

The uniformity constant `Cunif` is a parameter quantified *before* `δ`, exactly as in the single
citation `Kakeya.ml1Boot.exists_essDistinct_parentFamily` and exactly as `Co` is.  Both are
*hypothesis* parameters and neither is a constant this lemma introduces, so neither carries a
`Constant in Lemma` definition of its own; blueprint `lem:ml1bootRepairEssDistinct` and
`prop:ml1bootEssDistinctParents` name them `C_u` and `C_o`.

## Why the signature is this long

Ten hypothesis groups, and each is the hypothesis of one of the two applications of
`Kakeya.ml1Boot.exists_essDistinct_parentFamily`, which is the only citation.  Its ladder
hypotheses `δ ≤ τ ≤ θ ≤ 1` (read at `(δ, τ)` and at `(δ, θ)`), its scale hypothesis, `s.Nonempty`,
the uniformity, the
`B₁` containment and the pairwise essential distinctness of the *leaves* are shared by the two
applications; the two parent families and the two bounded-overlap hypotheses are what distinguish
them.  Nothing is bundled into `Kakeya.ml1Boot.IsCaseTwoInput`: as for (R2), the free-standing
form is what makes the declaration applicable at the chain's call site without reproving anything.

*Both bounded-overlap hypotheses are relativized by the **leaves**.*  That is not a slip.
`Kakeya.ml1Boot.HasBoundedOverlap s 𝕍 t 𝕍_ρ Co` counts the parents that meet a given `ρ`-tube
*through `𝕍`*, so it is a condition on the pair `(𝕍, 𝕍_ρ)` and mentions no parent map; the
coarse application is made to the leaf family along `pθ ∘ pτ`
(`Kakeya.ml1Boot.IsParentFamily.comp`), so what it needs is the overlap of `𝕋_θ|_{tθ}` through
`𝕋|_s`, and **not** through `𝕋_τ|_{tτ}`.  Those are different hypotheses and only the first is
what the citation reads.  At the call site both are one field read,
`Kakeya.ml1Boot.hasBoundedOverlap_nodes` at the two grid indices.

*The node parameters may be the **full** node families.*  Nothing here asks `tτ` and `tθ` to be
proper subsets, and the two containments are automatic at the full node families, the parent maps
being total.  So the caller may hand this pass the full node families and discard the node output
of the (R2) pass before it: this pass reads no property of its node parameters beyond the two
containments — no uniformity, no essential distinctness, no Frostman bound — so a larger node
parameter is a weaker hypothesis.

## The proof route

Two applications of `Kakeya.ml1Boot.exists_essDistinct_parentFamily`, each at `ε' / 2`, to the
*same* pair `(𝕋|_s, Y)`, followed by an assembly.

* the **coarse** one, at the composed parent family `(tθ, 𝕋_θ, pθ ∘ pτ)` of
  `Kakeya.ml1Boot.IsParentFamily.comp` and at weight `w`, returning `s_a` and `t'θ`;
* the **fine** one, at `(tτ, 𝕋_τ, pτ)` and at weight `w · 1_{s_a}` — folding the first output's
  indicator into the weight is what charges the fine selection against the leaves the coarse one
  has already kept, with no hypothesis on `𝕋|_{s_a}` — returning `s'₂` and `t¹'τ`;
* the **assembly** `t'τ = {k ∈ t¹'τ : pθ k ∈ t'θ}` and `s' = {i ∈ s'₂ : pτ i ∈ t'τ}`.

Both selections must be made on the same leaf family, and that is forced: the citation consumes a
uniform shaded family, uniformity is not inherited by subfamilies, and `𝕋_τ` carries no shading at
all.  `s'` is defined by *filtering the fine output*, not as `s_a ∩ s'₂`: only the filter form
leaves the retained fine fibres unchanged (`Kakeya.ml1Boot.fibre_filter_mem`), which is what makes
`Kakeya.ml1Boot.IsRepairEssDistinctPass.fibreFrostman` a read-off of the fine selection's own
fibrewise clause; and `s_a ∩ s'₂ ⊆ s'` is what keeps the intersection's weight, so nothing is
lost.  Blueprint `note:ml1bootRepairEDFilterForm`.

## What this pass does *not* conclude

*No nonemptiness of `s'`.*  The following (R2) pass demands `s.Nonempty` of its input, so the
chain has an obligation here that this statement does not discharge, and it is recorded rather
than asserted: `Kakeya.ml1Boot.exists_essDistinct_parentFamily` gives only the weight retention
`δ ^ ε' * ∑_{i ∈ s} w i ≤ ∑_{i ∈ s'} w i`, from which `s'.Nonempty` follows **only** when
`∑ i ∈ s, w i ≠ 0` — a hypothesis on the caller's weight that the blueprint statement does not
make and that the citation does not supply.  Adding it to the conclusion without that hypothesis
would be a strengthening, so the caller must either pass a weight with nonzero total or obtain
nonemptiness some other way.

There is no middle bound among the conclusions, and the reason is structural: it would be
asserted at the *retained* `θ`-fibre `{k ∈ t'τ : pθ k = l}`, and this move deletes `τ`-nodes — it
is the only move of the repair that does.  The obligation is
`Kakeya.ml1Boot.IsFibrewiseEmptyOrShare` for this one selection, whose descent
`Kakeya.ml1Boot.frostmanConstIn_retainedFibre_le` is proved; blueprint
`note:ml1bootRepairEDMidRetained` and `note:ml1bootEssDistinctFibrewiseShare`.

The dichotomy itself is **not** unsupplied, and this paragraph used to say otherwise. What is missing is a
**caller**: no declaration yet runs the trim after this selection and carries the dichotomy on
to the consumer. The gap is in the assembly, not in the dichotomy.

## The two overlap hypotheses are `Tube.HasBoundedOverlap`, not `Kakeya.IsEDUpToMult`

An intermediate edit stated them as `Kakeya.IsEDUpToMult tτ 𝕋_τ Co` and
`Kakeya.IsEDUpToMult tθ 𝕋_θ Co`, which does not typecheck — that predicate's multiplicity is a
natural number and `Co` here is an `NNReal` — and which the proof cannot use either: the single
citation `Kakeya.ml1Boot.exists_essDistinct_parentFamily` reads `Tube.HasBoundedOverlap`. They are
back in the leaf-mediated form the rest of this docstring describes. -/
theorem exists_repairEssDistinct (hdim : Module.finrank ℝ E = 3) :
    ∃ c : NNReal, 0 < c ∧
    ∀ {ε' : ℝ}, 0 < ε' → ∀ (Cunif : NNReal) {Co : NNReal}, 1 ≤ Co →
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ τ θ : NNReal, δ ≤ τ → τ ≤ θ → θ ≤ 1 →
      (δ : ℝ) ^ (ε' / 2) ≤ (c : ℝ) * τ / Co →
      ∀ {ι κ : Type*} [DecidableEq κ] {s : Finset ι} {tτ tθ : Finset κ}
        (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ)
        (Tθ : κ → Tube θ E) (pθ : κ → κ) (w : ι → ENNReal),
        s.Nonempty →
        ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) Cunif →
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        IsParentFamily s (fun i => (T i).toTube) tτ Tτ pτ →
        IsParentFamily tτ Tτ tθ Tθ pθ →
        HasBoundedOverlap s (fun i => (T i).toTube) tτ Tτ Co →
        HasBoundedOverlap s (fun i => (T i).toTube) tθ Tθ Co →
        ∃ s' ⊆ s, ∃ t'τ ⊆ tτ, ∃ t'θ ⊆ tθ,
          IsRepairEssDistinctPass ε' T Tτ pτ Tθ pθ w s s' t'τ t'θ := by
  obtain ⟨c, hc0, H⟩ := exists_essDistinct_parentFamily (E := E) hdim
  refine ⟨c, hc0, ?_⟩
  intro ε' hε' Cunif Co hCo
  have hε'2 : 0 < ε' / 2 := div_pos hε' (by norm_num)
  filter_upwards [H hε'2 Cunif hCo] with δ hev
  intro τ θ hδτ hτθ hθ1 hscale ι κ _s s tτ tθ T Tτ pτ Tθ pθ w hs hunif hball hed hfine hcoarse hovτ hovθ
  classical
  -- the two selections, both at ε'/2
  have hδθ : δ ≤ θ := le_trans hδτ hτθ
  have hτ1 : τ ≤ 1 := le_trans hτθ hθ1
  have hδ1 : δ ≤ 1 := le_trans hδτ hτ1
  have hscaleθ : (δ : ℝ) ^ (ε' / 2) ≤ (c : ℝ) * θ / Co := by
    exact le_trans hscale (by
      gcongr)
  rcases hev δ θ (le_rfl : δ ≤ δ) hδθ hθ1 hscaleθ (V := T) (Vρ := Tθ)
      (p := fun i : ι => pθ (pτ i)) (w := w)
      hs hunif hball hed (IsParentFamily.comp hfine hcoarse) hovθ with
    ⟨sa, hsa_sub, tb0, htb0_sub, hpfΘ, hdistΘ, hretΘ, _hfroΘ⟩
  let wsa : ι → ENNReal := fun i : ι => if i ∈ sa then w i else 0
  rcases hev δ τ (le_rfl : δ ≤ δ) hδτ hτ1 hscale (V := T) (Vρ := Tτ) (p := pτ) (w := wsa)
      hs hunif hball hed hfine hovτ with
    ⟨s2, hs2_sub, tf0, htf0_sub, hpfT, hdistT, hretT, hfrosT⟩
  -- the assembly
  let tf : Finset κ := tf0.filter fun k => pθ k ∈ tb0
  let s2o : Finset ι := s2.filter fun i => pτ i ∈ tf
  have hkey : (sa ∩ s2 : Finset ι) ⊆ s2o := by
    intro i hi
    rcases Finset.mem_inter.mp hi with ⟨hi_sa, hi_s2⟩
    exact Finset.mem_filter.mpr
      ⟨hi_s2, Finset.mem_filter.mpr ⟨hpfT.mapsTo i hi_s2, hpfΘ.mapsTo i hi_sa⟩⟩
  have hfs : s.filter (fun i => i ∈ sa) = sa := by
    ext i
    constructor
    · intro hi
      exact (Finset.mem_filter.mp hi).2
    · intro hi
      exact Finset.mem_filter.mpr ⟨hsa_sub hi, hi⟩
  have hws1 : (∑ i ∈ s, wsa i) = ∑ i ∈ sa, w i := by
    change (∑ i ∈ s, (if i ∈ sa then w i else 0)) = ∑ i ∈ sa, w i
    rw [← Finset.sum_filter]
    rw [hfs]
  have hf2 : s2.filter (fun i => i ∈ sa) = sa ∩ s2 := by
    ext i
    constructor
    · intro hi
      exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hi).1⟩
    · intro hi
      exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hi).2, (Finset.mem_inter.mp hi).1⟩
  have hws2 : (∑ i ∈ s2, wsa i) = ∑ i ∈ sa ∩ s2, w i := by
    change (∑ i ∈ s2, (if i ∈ sa then w i else 0)) = ∑ i ∈ sa ∩ s2, w i
    rw [← Finset.sum_filter]
    rw [hf2]
  have hretT2 : (δ : ENNReal) ^ (ε' / 2) * (∑ i ∈ sa, w i) ≤ ∑ i ∈ sa ∩ s2, w i := by
    rw [← hws1, ← hws2]
    exact hretT
  have hpowHalf : (δ : ENNReal) ^ ε' = (δ : ENNReal) ^ (ε' / 2) * (δ : ENNReal) ^ (ε' / 2) := by
    rw [← ENNReal.rpow_add_of_nonneg (x := (δ : ENNReal)) (ε' / 2) (ε' / 2)
      (le_of_lt hε'2) (le_of_lt hε'2)]
    congr 1
    ring
  have hsumsub : (∑ i ∈ sa ∩ s2, w i) ≤ ∑ i ∈ s2o, w i := by
    exact Finset.sum_le_sum_of_subset hkey
  have hweight : (δ : ENNReal) ^ ε' * (∑ i ∈ s, w i) ≤ ∑ i ∈ s2o, w i := by
    calc
      (δ : ENNReal) ^ ε' * (∑ i ∈ s, w i)
          = (δ : ENNReal) ^ (ε' / 2) * ((δ : ENNReal) ^ (ε' / 2) * (∑ i ∈ s, w i)) := by
              rw [hpowHalf]
              rw [mul_assoc]
      _ ≤ (δ : ENNReal) ^ (ε' / 2) * (∑ i ∈ sa, w i) := by
              exact mul_le_mul_of_nonneg_left hretΘ zero_le
      _ ≤ ∑ i ∈ sa ∩ s2, w i := hretT2
      _ ≤ ∑ i ∈ s2o, w i := hsumsub
  have hparentFine : IsParentFamily s2o (fun i => (T i).toTube) tf Tτ pτ := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      change i ∈ s2.filter (fun i => pτ i ∈ tf) at hi
      exact (Finset.mem_filter.mp hi).2
    · apply Set.InjOn.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
      exact hpfT.injOn
    · intro i hi
      exact hpfT.le_parent i (Finset.filter_subset (fun i => pτ i ∈ tf) s2 hi)
  have hparentCoarse : IsParentFamily tf Tτ tb0 Tθ pθ := by
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      exact (Finset.mem_filter.mp hk).2
    · apply Set.InjOn.mono (Finset.coe_subset.mpr htb0_sub)
      exact hcoarse.injOn
    · intro k hk
      exact hcoarse.le_parent k (htf0_sub (Finset.filter_subset _ _ hk))
  have hFineDist : (tf : Set κ).Pairwise
      (fun k l => IsEssentiallyDistinct (Tτ k).carrier (Tτ l).carrier) := by
    exact Set.Pairwise.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)) hdistT
  have hDistCoarse : (tb0 : Set κ).Pairwise
      (fun k l => IsEssentiallyDistinct (Tθ k).carrier (Tθ l).carrier) := by
    exact hdistΘ
  have hFibFros : ∀ k ∈ tf, ∀ K : ConvexSpaceBody E,
      (∀ i ∈ fibre s pτ k, (T i).toConvexSpaceBody ≤ K) →
      frostmanConstIn (fibre s2o pτ k) (fun i => (T i).toConvexSpaceBody) K
        ≤ (δ : ENNReal) ^ (-ε')
          * frostmanConstIn (fibre s pτ k) (fun i => (T i).toConvexSpaceBody) K := by
    intro k hk K hKfib
    have hk0 : k ∈ tf0 := Finset.filter_subset _ _ hk
    have hfib : fibre s2o pτ k = fibre s2 pτ k := by
      change fibre (s2.filter (fun i => pτ i ∈ tf)) pτ k = fibre s2 pτ k
      exact fibre_filter_mem s2 pτ tf hk
    calc
      frostmanConstIn (fibre s2o pτ k) (fun i => (T i).toConvexSpaceBody) K
          = frostmanConstIn (fibre s2 pτ k) (fun i => (T i).toConvexSpaceBody) K := by
              rw [hfib]
      _ ≤ (δ : ENNReal) ^ (-(ε' / 2))
            * frostmanConstIn (fibre s pτ k) (fun i => (T i).toConvexSpaceBody) K :=
              hfrosT k hk0 K hKfib
      _ ≤ (δ : ENNReal) ^ (-ε')
            * frostmanConstIn (fibre s pτ k) (fun i => (T i).toConvexSpaceBody) K := by
              exact mul_le_mul_of_nonneg_right
                (ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1)
                  (by linarith : -ε' ≤ -(ε' / 2)))
                zero_le
  refine ⟨s2o, ?hs2o, tf, ?htf, tb0, htb0_sub, ?pass⟩
  · intro i hi
    exact hs2_sub (Finset.filter_subset (fun i => pτ i ∈ tf) s2 hi)
  · intro k hk
    exact htf0_sub (Finset.filter_subset _ _ hk)
  · exact
      { weight := hweight
        parentFine := hparentFine
        parentCoarse := hparentCoarse
        essDistinctFine := hFineDist
        essDistinctCoarse := hDistCoarse
        fibreFrostman := hFibFros }

/-- **Case (ii) repair, move (R1): essential distinctness at both scales, on ED-up-to-mult**
(blueprint `lem:ml1bootRepairEssDistinct`, elimination route item 40.47).

The name is NEW (`_edUpToMult`
suffix) — the old name stays occupied by the existing theorem until its retirement at
integration.

## Provenance

Blueprint item 40.47 (`eliminate_fineScale_ED_interface`, the "Intended elimination route" of
`section8_parents.tex:618–624`). The
replacement citation is proved (`lean_verify` axioms `{propext, Classical.choice, Quot.sound}`,
`sorryAx`-free) and reads body-level `IsEDUpToMult` of the parent bodies instead of
leaf-mediated overlap, so the scale clause, the uniformity, `s.Nonempty`, the B₁-ball, the fine
pairwise ED and `hdim` all go.

## The scaffold decision (b)

**USER DECISION (b):** the downstream call sites will carry `IsEDUpToMult` node-family
hypotheses as an explicit scaffold (like `hShallow` was), to be resolved by the 40.33
middle-factor redesign.  Hence this pass states the two `IsEDUpToMult` hypotheses at ONE shared
`(Co : ℕ)` parameter, in the sibling's exact spelling (`IsEDUpToMult t (fun k => (Vρ k).carrier)
Co`).

## The downstream obligation note

`IsEDUpToMult` of the node families is **not free from the dichotomy side** (see 40.47's survey
note and the prep MISSING flag): `hasBoundedOverlap_nodes` supplies only leaf-mediated
`HasBoundedOverlap`, which does not transfer to the body-level predicate, and the proved pencil
`not_exists_essDistinct_parentFamily` shows fixed-Co multiplicity is false for node families in
general.  A NEW supplier is needed — `IsEDUpToMult (𝒰.cover.indexSet k)
(fun j => (𝒰.cover.tube k j).carrier) M(δ)` with δ-dependent multiplicity `M(δ)` (or a
thread-up to the Case (ii) bundle) — and the call-site revision carrying it is item 40.51.  The
fine-family ED stays free (`IsCaseFamily.essDistinct`, the dichotomy's own input), which is why
the fine pairwise-ED hypothesis may be dropped here with no supplier obligation.

## Conclusions

Identical to the current `exists_repairEssDistinct` — the `IsRepairEssDistinctPass` bundle —
copied verbatim. -/
theorem exists_repairEssDistinct_edUpToMult {ε' : ℝ} (hε' : 0 < ε') (Co : ℕ) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ τ θ : NNReal, δ ≤ τ → τ ≤ θ → θ ≤ 1 →
      ∀ {ι κ : Type*} [DecidableEq κ] {s : Finset ι} {tτ tθ : Finset κ}
        (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ)
        (Tθ : κ → Tube θ E) (pθ : κ → κ) (w : ι → ENNReal),
        IsParentFamily s (fun i => (T i).toTube) tτ Tτ pτ →
        IsParentFamily tτ Tτ tθ Tθ pθ →
        IsEDUpToMult tτ (fun k => (Tτ k).carrier) Co →
        IsEDUpToMult tθ (fun k => (Tθ k).carrier) Co →
        ∃ s' ⊆ s, ∃ t'τ ⊆ tτ, ∃ t'θ ⊆ tθ,
          IsRepairEssDistinctPass ε' T Tτ pτ Tθ pθ w s s' t'τ t'θ := by
  have hε'2 : 0 < ε' / 2 := div_pos hε' (by norm_num)
  have hev := exists_essDistinct_parentFamily_of_edUpToMult (E := E) hε'2 Co
  filter_upwards [hev] with δ hev
  intro τ θ hδτ hτθ hθ1 ι κ _s s tτ tθ T Tτ pτ Tθ pθ w hfine hcoarse hEDτ hEDθ
  classical
  -- the two selections, both at ε'/2
  have hδθ : δ ≤ θ := le_trans hδτ hτθ
  have hτ1 : τ ≤ 1 := le_trans hτθ hθ1
  have hδ1 : δ ≤ 1 := le_trans hδτ hτ1
  rcases hev δ θ (le_rfl : δ ≤ δ) hδθ hθ1 (V := T) (Vρ := Tθ)
      (p := fun i : ι => pθ (pτ i)) (w := w)
      (IsParentFamily.comp hfine hcoarse) hEDθ with
    ⟨sa, hsa_sub, tb0, htb0_sub, hpfΘ, hdistΘ, hretΘ, _hfroΘ⟩
  let wsa : ι → ENNReal := fun i : ι => if i ∈ sa then w i else 0
  rcases hev δ τ (le_rfl : δ ≤ δ) hδτ hτ1 (V := T) (Vρ := Tτ) (p := pτ) (w := wsa)
      hfine hEDτ with
    ⟨s2, hs2_sub, tf0, htf0_sub, hpfT, hdistT, hretT, hfrosT⟩
  -- the assembly
  let tf : Finset κ := tf0.filter fun k => pθ k ∈ tb0
  let s2o : Finset ι := s2.filter fun i => pτ i ∈ tf
  have hkey : (sa ∩ s2 : Finset ι) ⊆ s2o := by
    intro i hi
    rcases Finset.mem_inter.mp hi with ⟨hi_sa, hi_s2⟩
    exact Finset.mem_filter.mpr
      ⟨hi_s2, Finset.mem_filter.mpr ⟨hpfT.mapsTo i hi_s2, hpfΘ.mapsTo i hi_sa⟩⟩
  have hfs : s.filter (fun i => i ∈ sa) = sa := by
    ext i
    constructor
    · intro hi
      exact (Finset.mem_filter.mp hi).2
    · intro hi
      exact Finset.mem_filter.mpr ⟨hsa_sub hi, hi⟩
  have hws1 : (∑ i ∈ s, wsa i) = ∑ i ∈ sa, w i := by
    change (∑ i ∈ s, (if i ∈ sa then w i else 0)) = ∑ i ∈ sa, w i
    rw [← Finset.sum_filter]
    rw [hfs]
  have hf2 : s2.filter (fun i => i ∈ sa) = sa ∩ s2 := by
    ext i
    constructor
    · intro hi
      exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hi).1⟩
    · intro hi
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).2, (Finset.mem_inter.mp hi).1⟩
  have hws2 : (∑ i ∈ s2, wsa i) = ∑ i ∈ sa ∩ s2, w i := by
    change (∑ i ∈ s2, (if i ∈ sa then w i else 0)) = ∑ i ∈ sa ∩ s2, w i
    rw [← Finset.sum_filter]
    rw [hf2]
  have hretT2 : (δ : ENNReal) ^ (ε' / 2) * (∑ i ∈ sa, w i) ≤ ∑ i ∈ sa ∩ s2, w i := by
    rw [← hws1, ← hws2]
    exact hretT
  have hpowHalf : (δ : ENNReal) ^ ε' = (δ : ENNReal) ^ (ε' / 2) * (δ : ENNReal) ^ (ε' / 2) := by
    rw [← ENNReal.rpow_add_of_nonneg (x := (δ : ENNReal)) (ε' / 2) (ε' / 2)
      (le_of_lt hε'2) (le_of_lt hε'2)]
    congr 1
    ring
  have hsumsub : (∑ i ∈ sa ∩ s2, w i) ≤ ∑ i ∈ s2o, w i := by
    exact Finset.sum_le_sum_of_subset hkey
  have hweight : (δ : ENNReal) ^ ε' * (∑ i ∈ s, w i) ≤ ∑ i ∈ s2o, w i := by
    calc
      (δ : ENNReal) ^ ε' * (∑ i ∈ s, w i)
          = (δ : ENNReal) ^ (ε' / 2) * ((δ : ENNReal) ^ (ε' / 2) * (∑ i ∈ s, w i)) := by
              rw [hpowHalf]
              rw [mul_assoc]
      _ ≤ (δ : ENNReal) ^ (ε' / 2) * (∑ i ∈ sa, w i) := by
              exact mul_le_mul_of_nonneg_left hretΘ zero_le
      _ ≤ ∑ i ∈ sa ∩ s2, w i := hretT2
      _ ≤ ∑ i ∈ s2o, w i := hsumsub
  have hparentFine : IsParentFamily s2o (fun i => (T i).toTube) tf Tτ pτ := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      change i ∈ s2.filter (fun i => pτ i ∈ tf) at hi
      exact (Finset.mem_filter.mp hi).2
    · apply Set.InjOn.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
      exact hpfT.injOn
    · intro i hi
      exact hpfT.le_parent i (Finset.filter_subset (fun i => pτ i ∈ tf) s2 hi)
  have hparentCoarse : IsParentFamily tf Tτ tb0 Tθ pθ := by
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      exact (Finset.mem_filter.mp hk).2
    · apply Set.InjOn.mono (Finset.coe_subset.mpr htb0_sub)
      exact hcoarse.injOn
    · intro k hk
      exact hcoarse.le_parent k (htf0_sub (Finset.filter_subset _ _ hk))
  have hFineDist : (tf : Set κ).Pairwise
      (fun k l => IsEssentiallyDistinct (Tτ k).carrier (Tτ l).carrier) := by
    exact Set.Pairwise.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)) hdistT
  have hDistCoarse : (tb0 : Set κ).Pairwise
      (fun k l => IsEssentiallyDistinct (Tθ k).carrier (Tθ l).carrier) := by
    exact hdistΘ
  have hFibFros : ∀ k ∈ tf, ∀ K : ConvexSpaceBody E,
      (∀ i ∈ fibre s pτ k, (T i).toConvexSpaceBody ≤ K) →
      frostmanConstIn (fibre s2o pτ k) (fun i => (T i).toConvexSpaceBody) K
        ≤ (δ : ENNReal) ^ (-ε')
          * frostmanConstIn (fibre s pτ k) (fun i => (T i).toConvexSpaceBody) K := by
    intro k hk K hKfib
    have hk0 : k ∈ tf0 := Finset.filter_subset _ _ hk
    have hfib : fibre s2o pτ k = fibre s2 pτ k := by
      change fibre (s2.filter (fun i => pτ i ∈ tf)) pτ k = fibre s2 pτ k
      exact fibre_filter_mem s2 pτ tf hk
    calc
      frostmanConstIn (fibre s2o pτ k) (fun i => (T i).toConvexSpaceBody) K
          = frostmanConstIn (fibre s2 pτ k) (fun i => (T i).toConvexSpaceBody) K := by
              rw [hfib]
      _ ≤ (δ : ENNReal) ^ (-(ε' / 2))
            * frostmanConstIn (fibre s pτ k) (fun i => (T i).toConvexSpaceBody) K :=
              hfrosT k hk0 K hKfib
      _ ≤ (δ : ENNReal) ^ (-ε')
            * frostmanConstIn (fibre s pτ k) (fun i => (T i).toConvexSpaceBody) K := by
              exact mul_le_mul_of_nonneg_right
                (ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1)
                  (by linarith : -ε' ≤ -(ε' / 2)))
                zero_le
  refine ⟨s2o, ?hs2o, tf, ?htf, tb0, htb0_sub, ?pass⟩
  · intro i hi
    exact hs2_sub (Finset.filter_subset (fun i => pτ i ∈ tf) s2 hi)
  · intro k hk
    exact htf0_sub (Finset.filter_subset _ _ hk)
  · exact
      { weight := hweight
        parentFine := hparentFine
        parentCoarse := hparentCoarse
        essDistinctFine := hFineDist
        essDistinctCoarse := hDistCoarse
        fibreFrostman := hFibFros }


/-! ### The post-selection trim

Blueprint `lem:ml1bootFibrewiseTrim`, `lem:ml1bootFibrewiseTrimCost` and the banding corollary
`lem:ml1bootFibrewiseTrimCostBanded`.

These are route 3 of blueprint `note:ml1bootEssDistinctFibrewiseShare`: rather than asking the
essential-distinctness selection to *conclude* `Kakeya.ml1Boot.IsFibrewiseEmptyOrShare`, take its
output as a black box and **construct** from it a smaller node set that has the dichotomy by
fiat, discarding whole coarse fibres into the free empty branch.  Nothing here closes that note:
the trim buys the dichotomy at the price of the weight-retention clause, and
`Kakeya.ml1Boot.fibrewiseTrimCost` pays that price only under a two-sided comparability of the
weight a single node's fibre carries, whose availability at the leaf set the first (R2) pass
leaves behind is exactly what remains unchecked.
-/

/-- **The short coarse fibres of a selection** (blueprint `lem:ml1bootFibrewiseTrim`, the set
`B`).

Over the coarse node set `sa`, the coarse nodes `l` whose retained fibre `fibre t' pθ l` is
nonempty but carries *less* than a `ν`-share of the full fibre `fibre sb pθ l` — that is,
precisely the coarse nodes at which `t'` violates
`Kakeya.ml1Boot.IsFibrewiseEmptyOrShare` at `ν`.  Discarding them is what
`Kakeya.ml1Boot.trimNodes` does. -/
noncomputable def shortCoarseFibres {κ : Type*} [DecidableEq κ] (sb sa t' : Finset κ)
    (pθ : κ → κ) (ν : ENNReal) : Finset κ :=
  open scoped Classical in
  sa.filter fun l =>
    (fibre t' pθ l).Nonempty ∧
      ((fibre t' pθ l).card : ENNReal) < ν * ((fibre sb pθ l).card : ENNReal)

/-- **The post-selection trim of a node set** (blueprint `lem:ml1bootFibrewiseTrim`, the set
`t''`).

`t'` with every node lying over a short coarse fibre deleted, so that each coarse fibre is either
kept in full — that is, exactly as `t'` kept it — or emptied outright.  The deletion is by *whole*
coarse fibres, which is what makes `Kakeya.ml1Boot.IsFibrewiseEmptyOrShare` hold of the result
without any hypothesis on how `t'` was selected. -/
noncomputable def trimNodes {κ : Type*} [DecidableEq κ] (sb sa t' : Finset κ) (pθ : κ → κ)
    (ν : ENNReal) : Finset κ :=
  t'.filter fun k => pθ k ∉ shortCoarseFibres sb sa t' pθ ν

/-- **The post-selection trim** (blueprint `lem:ml1bootFibrewiseTrim`).

Given an *arbitrary* selection `t'` of fine nodes carrying a parent family for the leaves `u'`
and pairwise essentially distinct parents, the trim `t'' = Kakeya.ml1Boot.trimNodes` and the
filtered leaf set `u'' = {i ∈ u' : p i ∈ t''}` satisfy:

* (a) `u''`, `t''` is again a parent family — `Kakeya.ml1Boot.IsParentFamily.mono`;
* (b) the trimmed parents are again pairwise essentially distinct, essential distinctness being a
  condition on pairs;
* (c) `t''` **is** fibrewise empty-or-share at `ν`, which is the missing antecedent of
  `Kakeya.ml1Boot.frostmanConstIn_retainedFibre_le`;
* (d) every retained fibre is *literally unchanged*, `Kakeya.ml1Boot.fibre_filter_mem`, so any
  fibrewise hypothesis carried at `u'` — a Frostman transport, say — holds verbatim at `u''`
  with the same constant and **no exponent is spent**;
* (e) the leaves lost are exactly those over the deleted nodes, and the deleted nodes number at
  most `ν |sb|`.

Neither the ambient leaf set `u` nor the containment `t' ⊆ sb` is needed: the construction reads
only `t'`, `pθ` and the two node sets `sb`, `sa` through the cardinalities in
`Kakeya.ml1Boot.shortCoarseFibres`.

*A correction to the blueprint display.*  Blueprint item (e) states the node count as the strict
`∑_{l ∈ B} |F_l ∩ t'| < ν |sb|`.  That is false when `B = ∅` — both sides are then `0` — the
blueprint proof's step "the sum is less than `ν ∑_{l ∈ B}|F_l|`" needing `B` nonempty.  The
non-strict form stated here is what the proof gives and what
`Kakeya.ml1Boot.fibrewiseTrimCost` consumes. -/
theorem fibrewiseTrim {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {σ τ : NNReal}
    {u' u'' : Finset ι} {V : ι → Tube σ E} {sb sa t' t'' : Finset κ} {Vτ : κ → Tube τ E}
    {p : ι → κ} {pθ : κ → κ} {ν : ENNReal}
    (ht'' : t'' = trimNodes sb sa t' pθ ν)
    (hu'' : u'' = u'.filter fun i => p i ∈ t'')
    (hpar : IsParentFamily u' V t' Vτ p)
    (hED : (t' : Set κ).Pairwise fun k k' =>
      IsEssentiallyDistinct (Vτ k).carrier (Vτ k').carrier) :
    IsParentFamily u'' V t'' Vτ p ∧
      (t'' : Set κ).Pairwise
        (fun k k' => IsEssentiallyDistinct (Vτ k).carrier (Vτ k').carrier) ∧
      IsFibrewiseEmptyOrShare sb sa t'' pθ ν ∧
      (∀ k ∈ t'', fibre u'' p k = fibre u' p k) ∧
      (u' \ u'' = (t' \ t'').biUnion fun k => fibre u' p k) ∧
      (((t' \ t'').card : ENNReal) ≤ ν * (sb.card : ENNReal)) := by
  classical
  let B : Finset κ := shortCoarseFibres sb sa t' pθ ν
  have ht''0 : t'' = t'.filter (fun k => pθ k ∉ B) := by
    rw [ht'']
    ext k
    simp [trimNodes, B, shortCoarseFibres]
  -- (a) the trimmed leaf/node pair is again a parent family
  have htsub : t'' ⊆ t' := by
    rw [ht''0]
    exact Finset.filter_subset _ _
  have hpa : IsParentFamily u'' V t'' Vτ p := by
    refine IsParentFamily.mono hpar ?_ ?_ ?_
    · intro i hi
      rw [hu''] at hi
      exact (Finset.mem_filter.mp hi).1
    · exact htsub
    · intro i hi
      rw [hu''] at hi
      exact (Finset.mem_filter.mp hi).2
  -- (b) the essential distinctness descends to t''
  have hED0 : (t'' : Set κ).Pairwise
      (fun k k' => IsEssentiallyDistinct (Vτ k).carrier (Vτ k').carrier) := by
    exact Set.Pairwise.mono (Finset.coe_subset.mpr htsub) hED
  -- (c) the fibre of the trimmed set is unchanged off B and empty on B
  have hfib_eq : ∀ l : κ, l ∉ B → fibre t'' pθ l = fibre t' pθ l := by
    intro l hlB
    ext k
    simp only [fibre, ht''0, Finset.mem_filter, Finset.filter_filter]
    constructor
    · intro hk
      exact ⟨hk.1, hk.2.2⟩
    · intro hk
      exact ⟨hk.1, (by rw [hk.2]; exact hlB), hk.2⟩
  have hfib_empty : ∀ l : κ, l ∈ B → fibre t'' pθ l = ∅ := by
    intro l hlB
    rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    simp only [fibre, ht''0, Finset.filter_filter, Finset.mem_filter] at hk
    rcases hk with ⟨hk', hres⟩
    rcases hres with ⟨hnB, hEq⟩
    exact hnB (hEq.symm ▸ hlB)
  have hDich : IsFibrewiseEmptyOrShare sb sa t'' pθ ν := by
    intro l hl
    by_cases hlB : l ∈ B
    · left
      exact hfib_empty l hlB
    · by_cases hne : (fibre t' pθ l).Nonempty
      · right
        have hnf : ¬ ((fibre t' pθ l).Nonempty ∧
            ((fibre t' pθ l).card : ENNReal) < ν * ((fibre sb pθ l).card : ENNReal)) := by
          intro hn
          exact hlB (Finset.mem_filter.mpr ⟨hl, hn⟩)
        have hlt : ¬ ((fibre t' pθ l).card : ENNReal) <
            ν * ((fibre sb pθ l).card : ENNReal) := (not_and.mp hnf) hne
        have hge : ν * ((fibre sb pθ l).card : ENNReal) ≤
            ((fibre t' pθ l).card : ENNReal) := not_lt.mp hlt
        rw [hfib_eq l hlB]
        exact hge
      · left
        rw [hfib_eq l hlB]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro k hk
        exact hne ⟨k, hk⟩
  -- (d) the retained fibres are literally unchanged
  have hfibU : ∀ k, k ∈ t'' → fibre u'' p k = fibre u' p k := by
    intro k hk
    rw [hu'']
    exact fibre_filter_mem u' p t'' hk
  -- (e) the lost leaves are exactly those over the deleted nodes
  have hlost : u' \ u'' = (t' \ t'').biUnion (fun k => fibre u' p k) := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_sdiff.mp hi with ⟨hi', hiu''⟩
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨p i, ?_, ?_⟩
      · rw [Finset.mem_sdiff]
        refine ⟨hpar.mapsTo i hi', ?_⟩
        intro hpit''
        exact hiu'' (by
          rw [hu'']
          exact Finset.mem_filter.mpr ⟨hi', hpit''⟩)
      · rw [fibre]
        exact Finset.mem_filter.mpr ⟨hi', rfl⟩
    · intro hi
      rcases (Finset.mem_biUnion.mp hi) with ⟨k, hk, hik⟩
      rw [Finset.mem_sdiff]
      rcases (Finset.mem_sdiff.mp hk) with ⟨_, hkt''⟩
      rw [fibre] at hik
      rcases (Finset.mem_filter.mp hik) with ⟨hi', hpa⟩
      constructor
      · exact hi'
      · intro hiu''
        rw [hu''] at hiu''
        rcases (Finset.mem_filter.mp hiu'') with ⟨_, hpa'⟩
        exact hkt'' (hpa ▸ hpa')
  -- (f) the count: the deleted nodes number at most ν·|sb|
  have hdisj : (B : Set κ).PairwiseDisjoint (fun l => fibre t' pθ l) := by
    intro a ha b hb hab
    change Disjoint (fibre t' pθ a) (fibre t' pθ b)
    rw [Finset.disjoint_left]
    intro k hka hkb
    rw [fibre] at hka hkb
    rcases (Finset.mem_filter.mp hka) with ⟨_, hka'⟩
    rcases (Finset.mem_filter.mp hkb) with ⟨_, hkb'⟩
    exact hab (hka'.symm.trans hkb')
  have hTB : t' \ t'' = B.biUnion (fun l => fibre t' pθ l) := by
    ext k
    rw [Finset.mem_sdiff]
    constructor
    · intro hk
      rcases hk with ⟨hk0, hkk⟩
      refine Finset.mem_biUnion.mpr ⟨pθ k, ?_, ?_⟩
      · by_contra hnb
        exact hkk (by
          rw [ht''0]
          exact Finset.mem_filter.mpr ⟨hk0, hnb⟩)
      · rw [fibre]
        exact Finset.mem_filter.mpr ⟨hk0, rfl⟩
    · intro hk
      rcases (Finset.mem_biUnion.mp hk) with ⟨l, hlB, hkl⟩
      rw [ht''0]
      rw [fibre] at hkl
      rcases (Finset.mem_filter.mp hkl) with ⟨hk0, hkl0⟩
      constructor
      · exact hk0
      · intro hkt
        rcases (Finset.mem_filter.mp hkt) with ⟨_, hnb⟩
        exact hnb (hkl0.symm ▸ hlB)
  have hcardB : ∀ l ∈ B, ((fibre t' pθ l).card : ENNReal) ≤
      ν * ((fibre sb pθ l).card : ENNReal) := by
    intro l hlB
    have hlB0 : l ∈ shortCoarseFibres sb sa t' pθ ν := by
      simpa [B] using hlB
    exact le_of_lt (Finset.mem_filter.mp hlB0).2.2
  have hdisjB : (B : Set κ).PairwiseDisjoint (fun l => fibre sb pθ l) := by
    intro a ha b hb hab
    change Disjoint (fibre sb pθ a) (fibre sb pθ b)
    rw [Finset.disjoint_left]
    intro k hka hkb
    rw [fibre] at hka hkb
    rcases (Finset.mem_filter.mp hka) with ⟨_, hka'⟩
    rcases (Finset.mem_filter.mp hkb) with ⟨_, hkb'⟩
    exact hab (hka'.symm.trans hkb')
  have hle2 : (∑ l ∈ B, (fibre sb pθ l).card) ≤ sb.card := by
    calc
      (∑ l ∈ B, (fibre sb pθ l).card) = (B.biUnion (fun l => fibre sb pθ l)).card := by
        rw [Finset.card_biUnion hdisjB]
      _ ≤ sb.card := by
        exact Finset.card_le_card (by
          intro x hx
          rcases (Finset.mem_biUnion.mp hx) with ⟨l, hlB, hxl⟩
          rw [fibre] at hxl
          exact (Finset.mem_filter.mp hxl).1)
  have hcount : ((t' \ t'').card : ENNReal) ≤ ν * (sb.card : ENNReal) := by
    calc
      ((t' \ t'').card : ENNReal) = ((B.biUnion fun l => fibre t' pθ l).card : ENNReal) := by
        rw [hTB]
      _ = ∑ l ∈ B, ((fibre t' pθ l).card : ENNReal) := by
        rw [Finset.card_biUnion hdisj]
        rw [Nat.cast_sum]
      _ ≤ ∑ l ∈ B, ν * ((fibre sb pθ l).card : ENNReal) := by
        exact Finset.sum_le_sum hcardB
      _ = ν * (∑ l ∈ B, ((fibre sb pθ l).card : ENNReal)) := by
        rw [Finset.mul_sum]
      _ ≤ ν * (sb.card : ENNReal) := by
        exact mul_le_mul_right (by exact_mod_cast hle2) ν
  exact ⟨hpa, hED0, hDich, hfibU, hlost, hcount⟩

/-- **The first display of the trim's cost** (blueprint `lem:ml1bootFibrewiseTrimCost`).

`w(u') ≤ w(u'') + |t' \ t''| · m₊`, which composed with the node count of
`Kakeya.ml1Boot.fibrewiseTrim`(e) is the blueprint's `w(u') - w(u'') ≤ ν m₊ |sb|`.  Stated
additively: `ENNReal` has no subtraction cancellation, so the blueprint's difference form is not
available as such. -/
theorem trimLostWeight_le {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {u' u'' : Finset ι} {t' t'' : Finset κ} {p : ι → κ} {w : ι → ENNReal} {mplus : ENNReal}
    (hu'' : u'' = u'.filter fun i => p i ∈ t'')
    (hlost : u' \ u'' = (t' \ t'').biUnion fun k => fibre u' p k)
    (hplus : ∀ k ∈ t', ∑ i ∈ fibre u' p k, w i ≤ mplus) :
    ∑ i ∈ u', w i ≤ (∑ i ∈ u'', w i) + ((t' \ t'').card : ENNReal) * mplus := by
  classical
  subst hu''
  have hdisj : (↑(t' \ t'') : Set κ).PairwiseDisjoint (fun a => fibre u' p a) := by
    intro a ha b hb hab
    change Disjoint (fibre u' p a) (fibre u' p b)
    rw [Finset.disjoint_left]
    intro i hia hib
    have hpa : p i = a := (Finset.mem_filter.mp hia).2
    have hpb : p i = b := (Finset.mem_filter.mp hib).2
    exact hab (hpa.symm.trans hpb)
  have hfibLost : (∑ i ∈ u' \ u'.filter (fun i => p i ∈ t''), w i)
      ≤ ((t' \ t'').card : ENNReal) * mplus := by
    rw [hlost]
    rw [Finset.sum_biUnion hdisj]
    calc
      (∑ k ∈ t' \ t'', ∑ i ∈ fibre u' p k, w i) ≤ ∑ k ∈ t' \ t'', mplus := by
        exact Finset.sum_le_sum (fun k hk => hplus k (Finset.mem_sdiff.mp hk).1)
      _ = ((t' \ t'').card : ENNReal) * mplus := by
        rw [Finset.sum_const, nsmul_eq_mul]
  calc
    (∑ i ∈ u', w i) = (∑ i ∈ u' \ u'.filter (fun i => p i ∈ t''), w i) +
        (∑ i ∈ u'.filter (fun i => p i ∈ t''), w i) := by
      rw [← Finset.sum_sdiff (Finset.filter_subset (fun i => p i ∈ t'') u')]
    _ ≤ (∑ i ∈ u'.filter (fun i => p i ∈ t''), w i) + ((t' \ t'').card : ENNReal) * mplus := by
      rw [add_comm (∑ i ∈ u'.filter (fun i => p i ∈ t''), w i)]
      exact add_le_add_left hfibLost (∑ i ∈ u'.filter (fun i => p i ∈ t''), w i)

/-- **A lower bracket on every fibre bounds the node count by the total weight** (blueprint
`lem:ml1bootFibrewiseTrimCost`, second paragraph).

`p` is defined on all of `u` and lands in `sb`, so `u` is the disjoint union of the fibres
`u[k]`, `k ∈ sb`, and `m₋ ≤ w(u[k])` for each of them gives `m₋ |sb| ≤ w(u)`.  This is the
blueprint's `|sb| ≤ m₋⁻¹ w(u)`, stated multiplicatively to avoid `ENNReal` division.

This is the *pointwise-to-aggregate channel* into
`Kakeya.ml1Boot.fibrewiseTrimCost`, whose lower-bound hypothesis is the aggregate conclusion
here.  It is the right route exactly when the pointwise bracket is available; at the Case (ii)
call site it is not, a preceding (R2) pass being permitted to empty a node's fibre, and
`Kakeya.ml1Boot.aggregateLower_of_classBracket` supplies the aggregate by a different argument
that never reads a single node. -/
theorem card_mul_le_sum_fibre {ι κ : Type*} [DecidableEq κ]
    {u : Finset ι} {sb : Finset κ} {p : ι → κ} {w : ι → ENNReal} {mminus : ENNReal}
    (hmaps : ∀ i ∈ u, p i ∈ sb) (hminus : ∀ k ∈ sb, mminus ≤ ∑ i ∈ fibre u p k, w i) :
    mminus * (sb.card : ENNReal) ≤ ∑ i ∈ u, w i := by
  classical
  calc
    mminus * (sb.card : ENNReal) = ∑ k ∈ sb, mminus := by
      rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    _ ≤ ∑ k ∈ sb, ∑ i ∈ fibre u p k, w i := by
      exact Finset.sum_le_sum hminus
    _ = ∑ i ∈ u, w i := by
      simp only [fibre]
      rw [Finset.sum_fiberwise_of_maps_to hmaps w]

/-- **What the trim costs, and when the cost is affordable** (blueprint
`lem:ml1bootFibrewiseTrimCost`).

Under an upper bound `w(u'[k]) ≤ m₊` on the weight one node's fibre carries, an *aggregate*
lower bound `m₋ |sb| ≤ w(u)`, and a selection retaining the weight at `η`, a share `ν` small
enough that `2 ν m₊ ≤ η m₋` leaves the trimmed leaf set with half of that retention.

*The lower bound is deliberately aggregate and not pointwise.*  An earlier form of this lemma
asked for `m₋ ≤ w(u[k])` at **every** `k ∈ sb`, and that is what
`Kakeya.ml1Boot.card_mul_le_sum_fibre` converts into the aggregate form used here — that
specialization is still available and is the right route whenever the pointwise bracket holds.
But the pointwise reading is false at the intended call site: the trim is taken at the leaf set a
(R2) pass leaves behind, and a pass may *empty* a node's fibre outright, where no positive `m₋`
survives.  The aggregate form never inspects an individual node, so an emptied node costs
nothing; `Kakeya.ml1Boot.aggregateLower_of_classBracket` is what supplies it at that leaf set,
from the class brackets read at the hierarchy's own leaf set.  Blueprint
`note:ml1bootEssDistinctFibrewiseShare` is where this distinction is the whole question.

The conclusion is stated as `η w(u) ≤ 2 w(u'')` rather than `w(u'') ≥ ½ η w(u)`: `ENNReal`
division by `2` is harmless but the doubled form is what the proof produces, the whole argument
being division-free.  The finiteness hypothesis `hfin` is what licenses the one cancellation;
it is free at every intended call site, `w` being a volume on a finite family.

*This is the whole of what the trim owes, and it is a statement about the leaves.*  Nothing here
constrains how `t'` was chosen. -/
theorem fibrewiseTrimCost {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {u u' u'' : Finset ι} {sb t' t'' : Finset κ} {p : ι → κ} {w : ι → ENNReal}
    {ν η mplus mminus : ENNReal}
    (ht' : t' ⊆ sb)
    (hu'' : u'' = u'.filter fun i => p i ∈ t'')
    (hlost : u' \ u'' = (t' \ t'').biUnion fun k => fibre u' p k)
    (hcard : ((t' \ t'').card : ENNReal) ≤ ν * (sb.card : ENNReal))
    (hplus : ∀ k ∈ sb, ∑ i ∈ fibre u' p k, w i ≤ mplus)
    (hminus_agg : mminus * (sb.card : ENNReal) ≤ ∑ i ∈ u, w i)
    (hν : 2 * (ν * mplus) ≤ η * mminus)
    (hret : η * ∑ i ∈ u, w i ≤ ∑ i ∈ u', w i)
    (hfin : η * ∑ i ∈ u, w i ≠ ⊤) :
    η * ∑ i ∈ u, w i ≤ 2 * ∑ i ∈ u'', w i := by
  classical
  -- W' ≤ W'' + |t' \ t''| · m₊, by the lost-weight estimate
  have hle : (∑ i ∈ u', w i) ≤
      (∑ i ∈ u'', w i) + ((t' \ t'').card : ENNReal) * mplus :=
    trimLostWeight_le hu'' hlost (fun k hk => hplus k (ht' hk))
  -- |t' \ t''| · m₊ ≤ (ν · |sb|) · m₊ via the node count, hence W' ≤ W'' + ν |sb| m₊
  have hcardMul : ((t' \ t'').card : ENNReal) * mplus ≤
      (ν * (sb.card : ENNReal)) * mplus :=
    mul_le_mul_left hcard mplus
  have hle' : (∑ i ∈ u', w i) ≤
      (∑ i ∈ u'', w i) + (ν * (sb.card : ENNReal)) * mplus :=
    le_trans hle (add_le_add_right hcardMul (∑ i ∈ u'', w i))
  -- doubling: 2 W' ≤ 2 W'' + 2 ν |sb| m₊
  have h2le : 2 * (∑ i ∈ u', w i) ≤
      2 * (∑ i ∈ u'', w i) + 2 * (ν * (sb.card : ENNReal) * mplus) := by
    calc
      2 * (∑ i ∈ u', w i) ≤ 2 * ((∑ i ∈ u'', w i) + ((t' \ t'').card : ENNReal) * mplus) := by
        exact mul_le_mul_right hle (2 : ENNReal)
      _ = 2 * (∑ i ∈ u'', w i) + 2 * (((t' \ t'').card : ENNReal) * mplus) := by
        rw [mul_add]
      _ ≤ 2 * (∑ i ∈ u'', w i) + 2 * ((ν * (sb.card : ENNReal)) * mplus) := by
        exact add_le_add_right (mul_le_mul_right hcardMul (2 : ENNReal))
          (2 * (∑ i ∈ u'', w i))
  -- the cost term: 2 ν |sb| m₊ = (2 ν m₊) |sb| ≤ (η m₋) |sb| = η (m₋ |sb|) ≤ η W
  have hcost : 2 * (ν * (sb.card : ENNReal) * mplus) ≤ η * (∑ i ∈ u, w i) := by
    calc
      2 * (ν * (sb.card : ENNReal) * mplus) = (2 * (ν * mplus)) * (sb.card : ENNReal) := by
        ring
      _ ≤ (η * mminus) * (sb.card : ENNReal) := by
        exact mul_le_mul_left hν (sb.card : ENNReal)
      _ = η * (mminus * (sb.card : ENNReal)) := by
        ring
      _ ≤ η * (∑ i ∈ u, w i) := by
        exact mul_le_mul_right hminus_agg η
  have h2le2 : 2 * (∑ i ∈ u'', w i) + 2 * (ν * (sb.card : ENNReal) * mplus) ≤
      2 * (∑ i ∈ u'', w i) + η * (∑ i ∈ u, w i) := by
    exact add_le_add_right hcost (2 * (∑ i ∈ u'', w i))
  have h2final : 2 * (∑ i ∈ u', w i) ≤
      2 * (∑ i ∈ u'', w i) + η * (∑ i ∈ u, w i) :=
    le_trans h2le h2le2
  -- retention doubled: η W + η W = 2 (η W) ≤ 2 W'
  have h2ret : η * (∑ i ∈ u, w i) + η * (∑ i ∈ u, w i) ≤ 2 * (∑ i ∈ u', w i) := by
    calc
      η * (∑ i ∈ u, w i) + η * (∑ i ∈ u, w i) = 2 * (η * (∑ i ∈ u, w i)) := by
        ring
      _ ≤ 2 * (∑ i ∈ u', w i) := by
        exact mul_le_mul_right hret (2 : ENNReal)
  -- chain the halves, then cancel the finite addend
  have h3 : η * (∑ i ∈ u, w i) + η * (∑ i ∈ u, w i) ≤
      2 * (∑ i ∈ u'', w i) + η * (∑ i ∈ u, w i) :=
    le_trans h2ret h2final
  exact (ENNReal.add_le_add_iff_right hfin).mp h3

/-- **A trimmed leaf set of positive weight is nonempty** (blueprint
`lem:ml1bootFibrewiseTrimCost`, last clause). -/
theorem nonempty_of_weight_pos {ι : Type*} {u u'' : Finset ι} {w : ι → ENNReal} {η : ENNReal}
    (h : η * ∑ i ∈ u, w i ≤ 2 * ∑ i ∈ u'', w i) (hpos : 0 < η * ∑ i ∈ u, w i) :
    u''.Nonempty := by
  rcases Finset.eq_empty_or_nonempty u'' with hEmpty | hNonempty
  · exfalso
    have hle : η * ∑ i ∈ u, w i ≤ 0 := by
      simpa [hEmpty] using h
    exact (lt_irrefl _) (lt_of_le_of_lt hle hpos)
  · exact hNonempty

/-- **Banding turns a counting bracket into a weight bracket, at the cost of a factor `2`**
(blueprint `lem:ml1bootFibrewiseTrimCostBanded`, first half).

If a weight `w` is banded against a second quantity `c` — `lam · c i ≤ w i ≤ 2 · lam · c i` — and
`c` is *constant* on `s`, then on every `X ⊆ s` the weight of `X` is bracketed by its cardinality
times `lam · v`, two-sidedly, with ratio exactly `2`.

The intended instance is the shade mass: `w i = volume (T i).shade`, `c i = volume (T i).carrier`
and `v` the common volume of a `δ`-tube (`Kakeya.Tube.volume_carrier_eq_volume_carrier`), the
banding being the `band` clause of `Kakeya.ml1Boot.IsCaseTwoInput`, which is *pointwise* and
hence inherited by every subfamily.  Stated abstractly in `ENNReal` so that it neither imports
the Case (ii) bundle nor fixes the ambient geometry. -/
theorem sum_bracket_of_band {ι : Type*} {s X : Finset ι} {w c : ι → ENNReal} {lam v : ENNReal}
    (hc : ∀ i ∈ s, c i = v)
    (hband : ∀ i ∈ s, lam * c i ≤ w i ∧ w i ≤ 2 * (lam * c i))
    (hX : X ⊆ s) :
    lam * v * (X.card : ENNReal) ≤ ∑ i ∈ X, w i ∧
      ∑ i ∈ X, w i ≤ 2 * (lam * v * (X.card : ENNReal)) := by
  have hsum_const (a : ENNReal) : (∑ i ∈ X, a) = (X.card : ENNReal) * a := by
    rw [Finset.sum_const, nsmul_eq_mul]
  constructor
  · calc
      lam * v * (X.card : ENNReal) = (X.card : ENNReal) * (lam * v) := by ring
      _ = ∑ i ∈ X, lam * v := (hsum_const (lam * v)).symm
      _ = ∑ i ∈ X, lam * c i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hc i (hX hi)]
      _ ≤ ∑ i ∈ X, w i := by
        exact Finset.sum_le_sum (fun i hi => (hband i (hX hi)).1)
  · calc
      ∑ i ∈ X, w i ≤ ∑ i ∈ X, 2 * (lam * c i) := by
        exact Finset.sum_le_sum (fun i hi => (hband i (hX hi)).2)
      _ = ∑ i ∈ X, 2 * (lam * v) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hc i (hX hi)]
      _ = (X.card : ENNReal) * (2 * (lam * v)) := hsum_const (2 * (lam * v))
      _ = 2 * (lam * v * (X.card : ENNReal)) := by ring

/-- **The banded form of the trim's cost** (blueprint `lem:ml1bootFibrewiseTrimCostBanded`).

For a banded weight the two-sided comparability that `Kakeya.ml1Boot.fibrewiseTrimCost` asks for
is *free from a counting bracket*: `m₊/m₋` picks up only the banding's own factor `2`, so the
requirement `2 ν m₊ ≤ η m₋` reads simply

  `4 ν n₊ ≤ η n₋`,

with `n₊`, `n₋` the counting brackets on the fibres.  No power of `δ` is spent, and in particular
`lem:cardLowerBoundFromRefinement` — the general count-to-mass passage, which does cost an
accuracy — is not needed.  The common factor `lam · v` cancels *formally*, by monotonicity of
multiplication, so no positivity or finiteness of the tube volume is required.

*What this closes, and what it does not.*  It closes the half of blueprint
`note:ml1bootEssDistinctFibrewiseShare` that recorded the shade-mass reading of the comparability
as "not checked at all": for the shade mass the reading is the counting reading, times `2`.  It
does **not** close the other half — whether the class brackets survive the first (R2) pass to the
leaf set `s₁`, including at the nodes that pass has emptied, where the lower bracket fails
outright.  That is still the check route 3 turns on. -/
theorem fibrewiseTrimCost_of_band {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {u u' u'' : Finset ι} {sb t' t'' : Finset κ} {p : ι → κ} {w c : ι → ENNReal}
    {lam v ν η nplus nminus : ENNReal}
    (hmaps : ∀ i ∈ u, p i ∈ sb) (ht' : t' ⊆ sb) (hu' : u' ⊆ u)
    (hu'' : u'' = u'.filter fun i => p i ∈ t'')
    (hlost : u' \ u'' = (t' \ t'').biUnion fun k => fibre u' p k)
    (hcard : ((t' \ t'').card : ENNReal) ≤ ν * (sb.card : ENNReal))
    (hc : ∀ i ∈ u, c i = v)
    (hband : ∀ i ∈ u, lam * c i ≤ w i ∧ w i ≤ 2 * (lam * c i))
    (hnplus : ∀ k ∈ sb, ((fibre u' p k).card : ENNReal) ≤ nplus)
    (hnminus : ∀ k ∈ sb, nminus ≤ ((fibre u p k).card : ENNReal))
    (hν : 4 * (ν * nplus) ≤ η * nminus)
    (hret : η * ∑ i ∈ u, w i ≤ ∑ i ∈ u', w i)
    (hfin : η * ∑ i ∈ u, w i ≠ ⊤) :
    η * ∑ i ∈ u, w i ≤ 2 * ∑ i ∈ u'', w i := by
  have hν0 : 2 * (ν * (2 * (lam * v * nplus))) ≤ η * (lam * v * nminus) := by
    calc
      2 * (ν * (2 * (lam * v * nplus))) = (4 * (ν * nplus)) * (lam * v) := by ring
      _ ≤ (η * nminus) * (lam * v) := by
        exact mul_le_mul_left hν (lam * v)
      _ = η * (lam * v * nminus) := by ring
  have hplus : ∀ k ∈ sb, ∑ i ∈ fibre u' p k, w i ≤ 2 * (lam * v * nplus) := by
    intro k hk
    have hsub : fibre u' p k ⊆ u := by
      exact Finset.Subset.trans (Finset.filter_subset (fun i => p i = k) u') hu'
    have hb : ∑ i ∈ fibre u' p k, w i ≤ 2 * (lam * v * ((fibre u' p k).card : ENNReal)) :=
      (sum_bracket_of_band hc hband hsub).2
    calc
      ∑ i ∈ fibre u' p k, w i ≤ 2 * (lam * v * ((fibre u' p k).card : ENNReal)) := hb
      _ ≤ 2 * (lam * v * nplus) := by
        exact mul_le_mul_right (mul_le_mul_right (hnplus k hk) (lam * v)) (2 : ENNReal)
  have hminus : ∀ k ∈ sb, lam * v * nminus ≤ ∑ i ∈ fibre u p k, w i := by
    intro k hk
    have hsub : fibre u p k ⊆ u := Finset.filter_subset (fun i => p i = k) u
    have hlb : lam * v * ((fibre u p k).card : ENNReal) ≤ ∑ i ∈ fibre u p k, w i :=
      (sum_bracket_of_band hc hband hsub).1
    exact le_trans (mul_le_mul_right (hnminus k hk) (lam * v)) hlb
  exact fibrewiseTrimCost ht' hu'' hlost hcard hplus
    (card_mul_le_sum_fibre hmaps hminus) hν0 hret hfin

/-! ### The comparability at the leaf set a (R2) pass leaves behind

Blueprint `lem:ml1bootTrimComparabilityAtS1`, and with it the first of the two questions
`note:ml1bootEssDistinctFibrewiseShare` leaves route 3 turning on.

The point is a change of quantifier order, and nothing else.  `Kakeya.ml1Boot.fibrewiseTrimCost`
now asks only for the aggregate `m₋ |𝒰'_b| ≤ w(s₁)`, and the aggregate is available at `s₁`
even though the pointwise bracket is not: the class brackets of
`Tube.UniformTubeSet` are read at the hierarchy's **own** leaf set `s'`, where they
hold by definition, and the passage `s' ⇝ s₁` is made once, in bulk, by the pass's count
retention.  At no point is a bracket asserted at a node of `𝒰'_b` inside `s₁` — which is exactly
why the nodes a pass has emptied are not an obstruction.
-/

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The classes of a grid index account for the whole leaf set** (blueprint
`lem:ml1bootTrimComparabilityAtS1`, first step).

Summing the lower class bracket `Tube.UniformTubeSet.le_card_class`,
`N_b ≤ C_u |s'⟨k⟩|`, over the `b`-nodes: the classes *partition* `s'`, the assignment being a
function into the node index set, so `N_b |𝒰'_b| ≤ C_u |s'|`.

Stated in `NNReal`, which is where the branching numbers and the constant live. -/
theorem branchingN_mul_card_indexSet_le {ι : Type*} [Nontrivial E] {δ : NNReal}
    {s' : Finset ι} {Tt : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : Tube.UniformTubeSet s' Tt N Cu) {b : ℕ} (hb : b ≤ N) :
    𝒰.branchingN b * ((𝒰.cover.indexSet b).card : NNReal) ≤ Cu * (s'.card : NNReal) := by
  classical
  -- the b-node classes partition the leaf index set: |s'| = ∑_k |s'⟨k⟩|
  have hmap : (s' : Set ι).MapsTo (𝒰.cover.assign b) (𝒰.cover.indexSet b) := by
    intro i hi
    exact 𝒰.cover.assign_mem b hb i hi
  have hcard : (∑ k ∈ 𝒰.cover.indexSet b,
      (Tube.coverClass s' (𝒰.cover.assign b) k).card) = s'.card := by
    calc
      (∑ k ∈ 𝒰.cover.indexSet b, (Tube.coverClass s' (𝒰.cover.assign b) k).card)
          = ∑ k ∈ 𝒰.cover.indexSet b, (s'.filter (fun i => 𝒰.cover.assign b i = k)).card := by
              apply Finset.sum_congr rfl
              intro k hk
              simp only [Tube.coverClass]
      _ = s'.card := by
          exact (Finset.card_eq_sum_card_fiberwise hmap).symm
  have hcardNN : (∑ k ∈ 𝒰.cover.indexSet b,
      ((Tube.coverClass s' (𝒰.cover.assign b) k).card : NNReal)) = (s'.card : NNReal) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hcard
  calc
    𝒰.branchingN b * ((𝒰.cover.indexSet b).card : NNReal)
        = ∑ k ∈ 𝒰.cover.indexSet b, 𝒰.branchingN b := by
            rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    _ ≤ ∑ k ∈ 𝒰.cover.indexSet b,
        Cu * ((Tube.coverClass s' (𝒰.cover.assign b) k).card : NNReal) := by
            exact Finset.sum_le_sum (fun k hk => 𝒰.le_card_class b hb k hk)
    _ = Cu * (∑ k ∈ 𝒰.cover.indexSet b,
        ((Tube.coverClass s' (𝒰.cover.assign b) k).card : NNReal)) := by
            rw [Finset.mul_sum]
    _ = Cu * (s'.card : NNReal) := by
            rw [hcardNN]

section B3BranchCard

variable [Nontrivial E]

/-- The fixed hierarchy supplies the non-tautological branch/cardinality comparison needed by
the collapse.  We use `Cu = C ^ 2`, so `Cu ^ 4 = C ^ 8`; the direct count costs only `C ^ 5`.
-/
theorem b3_branch_card_of_hierarchy
    {ι : Type*} [DecidableEq ι] {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {N a b : ℕ} {C : NNReal} (hC : 1 ≤ C)
    (U : Tube.UniformTubeSet s' T N C) {pθ : ι → ι}
    (hcnp : IsCoarseNodeParents U a b pθ)
    {kF lM : ι} (hkF : kF ∈ U.cover.indexSet b)
    (hlM : lM ∈ U.cover.indexSet a) {tθAct : Finset ι}
    (htθAct : tθAct ⊆ U.cover.indexSet a) :
    ((fibre s' (U.cover.assign b) kF).card : ENNReal) *
        ((fibre (U.cover.indexSet b) pθ lM).card : ENNReal) *
        (tθAct.card : ENNReal)
      ≤ (((C ^ 2 : NNReal) : ENNReal) ^ 4) * (s'.card : ENNReal) := by
  classical
  let Nb : NNReal := U.branchingN b
  let Na : NNReal := U.branchingN a
  let P1 : NNReal := (fibre s' (U.cover.assign b) kF).card
  let P2 : NNReal := (fibre (U.cover.indexSet b) pθ lM).card
  let P3 : NNReal := tθAct.card
  have hbN : b ≤ N := hcnp.le_gridLen
  have haN : a ≤ N := hcnp.le_index.trans hbN
  have hP1 : P1 ≤ C * Nb := by
    simpa only [P1, Nb, fibre, Tube.coverClass, eq_comm] using
      U.card_class_le b hbN kF hkF
  have hP2R : (Nb : ℝ) * (P2 : ℝ) ≤ (C : ℝ) ^ 3 * (Na : ℝ) := by
    have hsub := (card_nodesIn_le_card_coarseFibre hC U hcnp hlM).1
    have hsubNN : P2 ≤
        ((U.nodesIn b (U.cover.tube a lM).toConvexSpaceBody).card : NNReal) := by
      dsimp only [P2]
      exact_mod_cast Finset.card_le_card hsub
    have hsubR : (P2 : ℝ) ≤
        ((U.nodesIn b (U.cover.tube a lM).toConvexSpaceBody).card : ℝ) := by
      exact_mod_cast hsubNN
    calc
      (Nb : ℝ) * (P2 : ℝ)
          ≤ (Nb : ℝ) *
              ((U.nodesIn b (U.cover.tube a lM).toConvexSpaceBody).card : ℝ) := by
            gcongr
      _ ≤ (C : ℝ) ^ 3 * (Na : ℝ) := by
            simpa [Nb, Na] using
              branching_mul_card_nodesIn_le U hcnp.le_index hcnp.le_gridLen lM
  have hP2NN : Nb * P2 ≤ C ^ 3 * Na := by
    exact_mod_cast hP2R
  have hP3NN : Na * P3 ≤ C * (s'.card : NNReal) := by
    have hcardNN : P3 ≤ ((U.cover.indexSet a).card : NNReal) := by
      dsimp only [P3]
      exact_mod_cast Finset.card_le_card htθAct
    calc
      Na * P3 ≤ Na * ((U.cover.indexSet a).card : NNReal) := by
        gcongr
      _ ≤ C * (s'.card : NNReal) := by
        simpa [Na] using branchingN_mul_card_indexSet_le U haN
  have hP1E : (P1 : ENNReal) ≤ (C : ENNReal) * (Nb : ENNReal) := by
    exact_mod_cast hP1
  have hP2E : (Nb : ENNReal) * (P2 : ENNReal) ≤
      (C : ENNReal) ^ 3 * (Na : ENNReal) := by
    exact_mod_cast hP2NN
  have hP3E : (Na : ENNReal) * (P3 : ENNReal) ≤
      (C : ENNReal) * (s'.card : ENNReal) := by
    exact_mod_cast hP3NN
  have hCpow : (C : ENNReal) ^ 5 ≤ (C : ENNReal) ^ 8 := by
    exact pow_le_pow_right₀ (by exact_mod_cast hC) (by omega)
  change (P1 : ENNReal) * (P2 : ENNReal) * (P3 : ENNReal) ≤ _
  calc
    (P1 : ENNReal) * (P2 : ENNReal) * (P3 : ENNReal)
        ≤ ((C : ENNReal) * (Nb : ENNReal)) * (P2 : ENNReal) * (P3 : ENNReal) := by
          gcongr
    _ = (C : ENNReal) * ((Nb : ENNReal) * (P2 : ENNReal)) * (P3 : ENNReal) := by ring
    _ ≤ (C : ENNReal) * ((C : ENNReal) ^ 3 * (Na : ENNReal)) * (P3 : ENNReal) := by
          gcongr
    _ = (C : ENNReal) ^ 4 * ((Na : ENNReal) * (P3 : ENNReal)) := by ring
    _ ≤ (C : ENNReal) ^ 4 * ((C : ENNReal) * (s'.card : ENNReal)) := by
          gcongr
    _ = (C : ENNReal) ^ 5 * (s'.card : ENNReal) := by ring
    _ ≤ (C : ENNReal) ^ 8 * (s'.card : ENNReal) := by gcongr
    _ = (((C ^ 2 : NNReal) : ENNReal) ^ 4) * (s'.card : ENNReal) := by
          norm_num [ENNReal.coe_pow]
          ring

end B3BranchCard

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The aggregate lower bound at the leaf set a pass leaves behind** (blueprint
`lem:ml1bootTrimComparabilityAtS1`).

Let `𝒰` be a `C_u`-uniform hierarchy on its own leaf set `s'`, let `s₁ ⊆ s'` be any subset
retaining a share `r` of the count, `r |s'| ≤ |s₁|`, and let the weight `w` be banded against a
quantity `c` that is constant `= v` on `s'`.  Then

  `(λ v · r N_b) · |𝒰'_b| ≤ C_u · w(s₁)`,

which is the aggregate lower bound `Kakeya.ml1Boot.fibrewiseTrimCost` consumes, at
`m₋ = λ v r N_b / C_u`.

*Where each factor comes from, and why no node is inspected.*  `w(s₁) ≥ λ v |s₁|` is
`Kakeya.ml1Boot.sum_bracket_of_band` (lower half) at `X = s₁`; `|s₁| ≥ r |s'|` is the pass's own
count retention; and `|s'| ≥ N_b |𝒰'_b| / C_u` is
`Kakeya.ml1Boot.branchingN_mul_card_indexSet_le`, the class bracket summed over the `b`-nodes
**at `s'`**.  The class bracket is therefore never read at `s₁`, where its lower half is false at
any node the pass has emptied; the whole passage `s' ⇝ s₁` is the single bulk factor `r`.  This
is the argument blueprint `note:ml1bootEssDistinctFibrewiseShare` recorded as a sketch.

Division-free: the `C_u⁻¹` of `m₋` is kept on the right-hand side here and introduced once, in
`Kakeya.ml1Boot.fibrewiseTrimCost_of_hierarchy`. -/
theorem aggregateLower_of_classBracket {ι : Type*} [Nontrivial E] {δ : NNReal}
    {s' : Finset ι} {Tt : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : Tube.UniformTubeSet s' Tt N Cu) {b : ℕ} (hb : b ≤ N)
    {s₁ : Finset ι} (hs₁ : s₁ ⊆ s') {w c : ι → ENNReal} {lam v r : ENNReal}
    (hc : ∀ i ∈ s', c i = v)
    (hband : ∀ i ∈ s', lam * c i ≤ w i ∧ w i ≤ 2 * (lam * c i))
    (hretain : r * (s'.card : ENNReal) ≤ (s₁.card : ENNReal)) :
    lam * v * (r * (𝒰.branchingN b : ENNReal)) * ((𝒰.cover.indexSet b).card : ENNReal)
      ≤ (Cu : ENNReal) * ∑ i ∈ s₁, w i := by
  let Nb : ENNReal := (𝒰.branchingN b : ENNReal)
  let Ib : ENNReal := ((𝒰.cover.indexSet b).card : ENNReal)
  have hNb : Nb * Ib ≤ (Cu : ENNReal) * (s'.card : ENNReal) := by
    exact ENNReal.coe_le_coe.mpr (by
      simpa [Nb, Ib, ENNReal.coe_mul, ENNReal.coe_natCast]
        using branchingN_mul_card_indexSet_le 𝒰 hb)
  have hband_low : lam * v * (s₁.card : ENNReal) ≤ ∑ i ∈ s₁, w i :=
    (sum_bracket_of_band hc hband hs₁).1
  calc
    lam * v * (r * Nb) * Ib = (lam * v) * (r * (Nb * Ib)) := by ring
    _ ≤ (lam * v) * (r * ((Cu : ENNReal) * (s'.card : ENNReal))) := by
      exact mul_le_mul_right (mul_le_mul_right hNb (r : ENNReal)) (lam * v)
    _ = (Cu : ENNReal) * ((lam * v) * (r * (s'.card : ENNReal))) := by ring
    _ ≤ (Cu : ENNReal) * ((lam * v) * (s₁.card : ENNReal)) := by
      exact mul_le_mul_right (mul_le_mul_right hretain (lam * v)) (Cu : ENNReal)
    _ ≤ (Cu : ENNReal) * ∑ i ∈ s₁, w i := by
      exact mul_le_mul_right hband_low (Cu : ENNReal)

/-! ### The aggregate lower bound survives a shrinking of the shadings

Blueprint `lem:ml1bootTrimComparabilityAtShrunkShading`.  These two declarations settle the
question on which reshaping move (R2) to return its own shading turns.

Every construction of `ShadedTube.ShadedUniformTubeSet` shrinks the shading it is handed, so a
repaired (R2) pass delivers a shading `Y' ⊆ Y` and its consumers must read the weight at `Y'`.
The obstruction that looks fatal is that the banding clause of `Kakeya.ml1Boot.IsCaseTwoInput` is
*pointwise* and **frozen**: under `(Y' i).shade ⊆ (Y i).shade` its upper half survives and its
lower half does not, and it is the lower half that the count-to-mass passage reads.

It is not fatal, and the reason is a quantifier order that has already been paid for.
`Kakeya.ml1Boot.fibrewiseTrimCost` no longer asks for a pointwise lower bound — that hypothesis
was weakened to the aggregate `m₋ |𝒰'_b| ≤ w(u)` — and the shrinking control that
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` delivers is aggregate too, being a
comparison of `ShadedBody.fullness'` at its own output set.  So the pointwise lower bound is
needed at `Y` only, where it holds, and the passage `Y ⇝ Y'` costs exactly the one factor the
uniformization charges for it. -/

/-- **An aggregate fullness comparison is an aggregate mass comparison, the carriers being the
same** (blueprint `lem:ml1bootTrimComparabilityAtShrunkShading`, first step).

`ShadedBody.fullness'` is `(∑ |Y_i|) / (∑ |T_i|)`, and a shrinking of a shading leaves the
underlying bodies alone, so the two fullnesses being compared have a *common* denominator.
Clearing it turns the comparison `λ'(Y) ≤ A λ'(Y')` delivered by
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` into the mass retention
`∑_{s} |Y_i| ≤ A ∑_{s} |Y'_i|`, which is the shape the aggregate lower bound consumes.

The two side conditions are exactly what clearing a denominator in `ENNReal` needs, and both are
free for a nonempty family of `δ`-tubes with `δ > 0`: a tube carrier contains a ball of radius
`δ`, and it is contained in one, so the sum is neither `0` nor `⊤`. -/
theorem sum_shade_le_of_fullness'_le {ι : Type*} {s : Finset ι} (Y Y' : ι → ShadedBody E)
    {A : ENNReal}
    (hcar : ∀ i ∈ s, volume (Y' i).carrier = volume (Y i).carrier)
    (hD0 : 0 < ∑ i ∈ s, volume (Y i).carrier)
    (hDtop : (∑ i ∈ s, volume (Y i).carrier) ≠ ⊤)
    (h : ShadedBody.fullness' s Y ≤ A * ShadedBody.fullness' s Y') :
    (∑ i ∈ s, volume (Y i).shade) ≤ A * ∑ i ∈ s, volume (Y' i).shade := by
  let N : ENNReal := ∑ i ∈ s, volume (Y i).shade
  let N' : ENNReal := ∑ i ∈ s, volume (Y' i).shade
  let D : ENNReal := ∑ i ∈ s, volume (Y i).carrier
  have hDenom : (∑ i ∈ s, volume (Y' i).carrier) = D := by
    dsimp [D]
    exact Finset.sum_congr rfl (fun i hi => hcar i hi)
  have hD : N / D ≤ A * (N' / D) := by
    simpa [ShadedBody.fullness', N, N', D, hDenom] using h
  have h_le : N ≤ (A * (N' / D)) * D :=
    (ENNReal.div_le_iff hD0.ne' hDtop).mp hD
  have h' : N ≤ A * N' := by
    calc
      N ≤ (A * (N' / D)) * D := h_le
      _ = A * ((N' / D) * D) := by rw [mul_assoc]
      _ = A * N' := by rw [ENNReal.div_mul_cancel hD0.ne' hDtop]
  simpa [N, N'] using h'

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The aggregate lower bound at a shrunken shading** (blueprint
`lem:ml1bootTrimComparabilityAtShrunkShading`).

`Kakeya.ml1Boot.aggregateLower_of_classBracket` with the weight read at a shrunken shading `w'`
in place of `w`, at the cost of the single aggregate factor `A` that the shrinking is controlled
by.  **No pointwise lower bound on `w'` is used, and none is available**: the banding is read at
`w`, where it holds, and the passage to `w'` is the one bulk factor `A`.

This is what makes reshaping move (R2) to return its own shading a controlled change rather than
an open-ended one.  Formally the proof is one monotonicity step on top of the unshrunk lemma; the
content is that the unshrunk lemma's `hband` hypothesis is never read at `w'`. -/
theorem aggregateLower_of_classBracket_shrunk {ι : Type*} [Nontrivial E] {δ : NNReal}
    {s' : Finset ι} {Tt : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : Tube.UniformTubeSet s' Tt N Cu) {b : ℕ} (hb : b ≤ N)
    {s₁ : Finset ι} (hs₁ : s₁ ⊆ s') {w w' c : ι → ENNReal} {lam v r A : ENNReal}
    (hc : ∀ i ∈ s', c i = v)
    (hband : ∀ i ∈ s', lam * c i ≤ w i ∧ w i ≤ 2 * (lam * c i))
    (hretain : r * (s'.card : ENNReal) ≤ (s₁.card : ENNReal))
    (hshrink : (∑ i ∈ s₁, w i) ≤ A * ∑ i ∈ s₁, w' i) :
    lam * v * (r * (𝒰.branchingN b : ENNReal)) * ((𝒰.cover.indexSet b).card : ENNReal)
      ≤ A * ((Cu : ENNReal) * ∑ i ∈ s₁, w' i) := by
  have hagg :=
    aggregateLower_of_classBracket (𝒰 := 𝒰) (hb := hb) (hs₁ := hs₁)
      (hc := hc) (hband := hband) (hretain := hretain)
  calc
    lam * v * (r * (𝒰.branchingN b : ENNReal)) * ((𝒰.cover.indexSet b).card : ENNReal)
        ≤ (Cu : ENNReal) * ∑ i ∈ s₁, w i := hagg
    _ ≤ (Cu : ENNReal) * (A * ∑ i ∈ s₁, w' i) := by
        gcongr
    _ = A * ((Cu : ENNReal) * ∑ i ∈ s₁, w' i) := by
        ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The trim's cost, at the Case (ii) leaf set, with the comparability discharged** (blueprint
`lem:ml1bootTrimCostAtS1`).

This is `Kakeya.ml1Boot.fibrewiseTrimCost` with both of its weight hypotheses supplied from the
hierarchy: the upper one from the class bracket
`Tube.UniformTubeSet.card_class_le` at a fibre of `u' ⊆ s₁ ⊆ s'`, the lower one from
`Kakeya.ml1Boot.aggregateLower_of_classBracket`.  The condition on the share `ν` comes out
explicitly as

  `4 ν C_u ² ≤ η r`,

with `η` the selection's own weight retention and `r` the (R2) pass's count retention.  Reading
both at `δ ^ ε'`, as the Case (ii) chain does, this is `ν ≤ δ ^ (2 ε') / (4 C_u ²)`, so
`ν = δ ^ (3 ε')` is admissible for all small `δ` — `C_u` being fixed before `δ`; that last step is
`Kakeya.ml1Boot.eventually_trimShare_admissible`.

*What this does not do.*  It does not reconcile that `ν` with the `κ = δ ^ (ε'/4)` at which
`Kakeya.ml1Boot.frostmanConstIn_retainedFibre_le` is consumed in the three-pass tally, which is
the second and now only remaining question of blueprint
`note:ml1bootEssDistinctFibrewiseShare`, and it does not rewire the three-pass lemma — intended
producer `Kakeya.ml1Boot.exists_repairThreePass` (blueprint `lem:ml1bootRepairThreePass`), which
is not a declaration; see the module docstring — to output the trimmed node set.  Route 3 is
therefore still not carried out, and `lem:ml1bootAssembleMiddle` still carries the obligation. -/
theorem fibrewiseTrimCost_of_hierarchy {ι : Type*} [DecidableEq ι] [Nontrivial E] {δ : NNReal}
    {s' : Finset ι} {Tt : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : Tube.UniformTubeSet s' Tt N Cu) (hCu : 0 < Cu) {b : ℕ} (hb : b ≤ N)
    {s₁ u' u'' t' t'' : Finset ι} {w c : ι → ENNReal} {lam v r ν η : ENNReal}
    (hs₁ : s₁ ⊆ s') (hu' : u' ⊆ s₁) (ht' : t' ⊆ 𝒰.cover.indexSet b)
    (hu'' : u'' = u'.filter fun i => 𝒰.cover.assign b i ∈ t'')
    (hlost : u' \ u'' = (t' \ t'').biUnion fun k => fibre u' (𝒰.cover.assign b) k)
    (hcard : ((t' \ t'').card : ENNReal) ≤ ν * ((𝒰.cover.indexSet b).card : ENNReal))
    (hc : ∀ i ∈ s', c i = v)
    (hband : ∀ i ∈ s', lam * c i ≤ w i ∧ w i ≤ 2 * (lam * c i))
    (hretain : r * (s'.card : ENNReal) ≤ (s₁.card : ENNReal))
    (hν : 4 * (ν * (Cu : ENNReal) ^ 2) ≤ η * r)
    (hret : η * ∑ i ∈ s₁, w i ≤ ∑ i ∈ u', w i)
    (hfin : η * ∑ i ∈ s₁, w i ≠ ⊤) :
    η * ∑ i ∈ s₁, w i ≤ 2 * ∑ i ∈ u'', w i := by
  classical
  let mplus : ENNReal := 2 * (lam * v * ((Cu : ENNReal) * (𝒰.branchingN b : ENNReal)))
  let mminus : ENNReal := lam * v * (r * (𝒰.branchingN b : ENNReal)) * (Cu : ENNReal)⁻¹
  have hCu0 : (Cu : ENNReal) ≠ 0 := ne_of_gt (ENNReal.coe_pos.mpr hCu)
  have hCuT : (Cu : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCuinv : (Cu : ENNReal) * (Cu : ENNReal)⁻¹ = 1 := ENNReal.mul_inv_cancel hCu0 hCuT
  -- (A) the fibrewise upper bound, from the class bracket and the banding
  have hplus : ∀ k ∈ 𝒰.cover.indexSet b,
      (∑ i ∈ fibre u' (𝒰.cover.assign b) k, w i) ≤ mplus := by
    intro k hk
    have hXsub : fibre u' (𝒰.cover.assign b) k ⊆ s' := by
      simpa [fibre] using (Finset.filter_subset (fun i => 𝒰.cover.assign b i = k) u').trans
        (hu'.trans hs₁)
    have hbks : (∑ i ∈ fibre u' (𝒰.cover.assign b) k, w i) ≤
        2 * (lam * v * ((fibre u' (𝒰.cover.assign b) k).card : ENNReal)) := by
      exact (sum_bracket_of_band (s := s') (X := fibre u' (𝒰.cover.assign b) k)
        (hc := hc) (hband := hband) hXsub).2
    have hfib_le : (fibre u' (𝒰.cover.assign b) k).card ≤
        (Tube.coverClass s' (𝒰.cover.assign b) k).card := by
      exact Finset.card_le_card (by
        rw [fibre_eq_coverClass u' (𝒰.cover.assign b) k]
        exact Tube.coverClass_subset_of_subset (hu'.trans hs₁)
          (𝒰.cover.assign b) k)
    have hfcc : (fibre u' (𝒰.cover.assign b) k).card ≤ Cu * (𝒰.branchingN b) := by
      have hfib_le' : ((fibre u' (𝒰.cover.assign b) k).card : NNReal) ≤
          ((Tube.coverClass s' (𝒰.cover.assign b) k).card : NNReal) := by
        exact_mod_cast hfib_le
      exact hfib_le'.trans (𝒰.card_class_le b hb k hk)
    have henc : ((fibre u' (𝒰.cover.assign b) k).card : ENNReal) ≤
        (Cu : ENNReal) * (𝒰.branchingN b : ENNReal) := by
      exact_mod_cast hfcc
    calc
      ∑ i ∈ fibre u' (𝒰.cover.assign b) k, w i ≤
          2 * (lam * v * ((fibre u' (𝒰.cover.assign b) k).card : ENNReal)) := hbks
      _ ≤ mplus := by
        dsimp [mplus]
        exact mul_le_mul_right (mul_le_mul_right henc (lam * v)) (2 : ENNReal)
  -- (B) the aggregate lower bound at s₁, from the class brackets
  have hagg :=
    aggregateLower_of_classBracket (𝒰 := 𝒰) (hb := hb) (hs₁ := hs₁)
      (hc := hc) (hband := hband) (hretain := hretain)
  have hminus_agg : mminus * ((𝒰.cover.indexSet b).card : ENNReal) ≤ (∑ i ∈ s₁, w i) := by
    calc
      mminus * ((𝒰.cover.indexSet b).card : ENNReal)
          = (lam * v * (r * (𝒰.branchingN b : ENNReal)) *
              ((𝒰.cover.indexSet b).card : ENNReal)) * (Cu : ENNReal)⁻¹ := by
              dsimp [mminus]
              ring
      _ ≤ ((Cu : ENNReal) * (∑ i ∈ s₁, w i)) * (Cu : ENNReal)⁻¹ := by
              exact mul_le_mul_left hagg (Cu : ENNReal)⁻¹
      _ = ∑ i ∈ s₁, w i := by
        calc
          (Cu : ENNReal) * (∑ i ∈ s₁, w i) * (Cu : ENNReal)⁻¹
              = (Cu : ENNReal) * (Cu : ENNReal)⁻¹ * (∑ i ∈ s₁, w i) := by
                  ring
          _ = 1 * (∑ i ∈ s₁, w i) := by
                rw [hCuinv]
          _ = ∑ i ∈ s₁, w i := by
                rw [one_mul]
  -- (C) the share condition, from 4 ν Cᵤ² ≤ η r by multiplying by Cᵤ⁻¹
  have h4m : 4 * (ν * (Cu : ENNReal)) ≤ η * r * (Cu : ENNReal)⁻¹ := by
    have hstep : (4 * (ν * (Cu : ENNReal) ^ 2)) * (Cu : ENNReal)⁻¹ ≤
        (η * r) * (Cu : ENNReal)⁻¹ := by
      exact mul_le_mul_left hν (Cu : ENNReal)⁻¹
    calc
      4 * (ν * (Cu : ENNReal)) = (4 * (ν * (Cu : ENNReal) ^ 2)) * (Cu : ENNReal)⁻¹ := by
        calc
          4 * (ν * (Cu : ENNReal)) = (4 * (ν * (Cu : ENNReal))) * (1 : ENNReal) := by ring
          _ = (4 * (ν * (Cu : ENNReal))) * ((Cu : ENNReal) * (Cu : ENNReal)⁻¹) := by
                rw [hCuinv]
          _ = (4 * (ν * (Cu : ENNReal) ^ 2)) * (Cu : ENNReal)⁻¹ := by ring
      _ ≤ (η * r) * (Cu : ENNReal)⁻¹ := hstep
  have hν' : 2 * (ν * mplus) ≤ η * mminus := by
    calc
      2 * (ν * mplus) = (4 * (ν * (Cu : ENNReal))) * (lam * v * (𝒰.branchingN b : ENNReal)) := by
        dsimp [mplus]
        ring
      _ ≤ (η * r * (Cu : ENNReal)⁻¹) * (lam * v * (𝒰.branchingN b : ENNReal)) := by
        exact mul_le_mul_left h4m (lam * v * (𝒰.branchingN b : ENNReal))
      _ = η * mminus := by
        dsimp [mminus]
        ring
  exact fibrewiseTrimCost (sb := 𝒰.cover.indexSet b) (p := 𝒰.cover.assign b) (u := s₁)
    ht' hu'' hlost hcard hplus hminus_agg hν' hret hfin

/-- **The share `δ ^ (3 ε')` is admissible for all small `δ`** (blueprint
`lem:ml1bootTrimComparabilityAtS1`, the exponent read-off).

The condition `4 ν C_u ² ≤ η r` of `Kakeya.ml1Boot.fibrewiseTrimCost_of_hierarchy`, at
`ν = δ ^ (3 ε')` and `η = r = δ ^ ε'`, is `4 C_u ² δ ^ ε' ≤ 1`, which holds eventually since
`C_u` is fixed before `δ`.  This is what turns the explicit bound
`ν ≤ δ ^ (2 ε') / (4 C_u ²)` into the round exponent the blueprint sketch names. -/
theorem eventually_trimShare_admissible (Cu : NNReal) {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      4 * ((δ : ENNReal) ^ (3 * ε') * (Cu : ENNReal) ^ 2)
        ≤ (δ : ENNReal) ^ ε' * (δ : ENNReal) ^ ε' := by
  -- Step 1: the absorption, in ENNReal
  have habs : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      4 * (Cu : ENNReal) ^ 2 ≤ (δ : ENNReal) ^ (-ε') := by
    have hCposR : (0 : ℝ) < 4 * (Cu : ℝ) ^ 2 + 1 := by positivity
    filter_upwards [nnreal_eventually_of_real_eventually
        (Kakeya.absorb_const_le_rpow_neg hCposR hε'), self_mem_nhdsWithin]
      with δ hcst hδ0
    have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
    have hRle : 4 * (Cu : ℝ) ^ 2 ≤ (δ : ℝ) ^ (-ε') := by
      exact le_trans (by nlinarith) hcst
    rw [ennreal_coe_nnreal_rpow hδR (-ε')]
    calc
      4 * (Cu : ENNReal) ^ 2 = ENNReal.ofReal (4 * (Cu : ℝ) ^ 2) := by
        norm_num [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_pow, ENNReal.ofReal_mul]
      _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ε')) := ENNReal.ofReal_le_ofReal hRle
  -- Step 2: the rpow arithmetic
  filter_upwards [habs, self_mem_nhdsWithin] with δ hδabs hδ0
  have hδne : ((δ : NNReal) : ENNReal) ≠ 0 := ne_of_gt (ENNReal.coe_pos.mpr hδ0)
  calc
    4 * ((δ : ENNReal) ^ (3 * ε') * (Cu : ENNReal) ^ 2)
        = (4 * (Cu : ENNReal) ^ 2) * (δ : ENNReal) ^ (3 * ε') := by ring
    _ ≤ (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ (3 * ε') := by
        exact mul_le_mul_left hδabs ((δ : ENNReal) ^ (3 * ε'))
    _ = (δ : ENNReal) ^ (-ε' + 3 * ε') := by
        rw [← ENNReal.rpow_add _ _ hδne ENNReal.coe_ne_top]
    _ = (δ : ENNReal) ^ (ε' + ε') := by
        congr 1
        ring
    _ = (δ : ENNReal) ^ ε' * (δ : ENNReal) ^ ε' := by
        rw [ENNReal.rpow_add _ _ hδne ENNReal.coe_ne_top]

/-! ### Move (R2), restored: the banded uniformization pass at an output shading

The **bare** move (R2) — the hypothesis-free `Kakeya.ml1Boot.exists_repairUniform`, deleted
earlier — is refuted by `Kakeya.ml1Boot.not_exists_repairUniform` above.  What follows is a
*restoration under two added hypotheses*, harvested and re-verified from a parallel branch, and
it is **additive**: nothing above is changed, and in particular
`Kakeya.ml1Boot.IsRepairUniformPass` is left exactly as it stands, as the record of what the
bare pass was to deliver.

Two things had to change for a pass to exist at all, and both appear as *added hypotheses* or as
a *new* record, never as a weakening of anything already here.

* **An input band.**  The refutation's witness is an all-empty shading, so the restored pass
  assumes the two-sided band `lam₀ · |T i| ≤ |(T i).shade| ≤ 2 · lam₀ · |T i|` on its input.
  That excludes the refuting witness, and it makes the two density clauses free with
  `lam' := lam₀`.

* **An output shading.**  `Kakeya.ml1Boot.IsRepairUniformPass.unif` asserts uniformity at the
  shading the pass is *handed*, and no construction delivers that: uniformity is produced only
  after shrinking a shading, and the second obstruction recorded in the docstring of
  `Kakeya.ml1Boot.card_shadeClass_le_card_shadeClass` is exactly this.  So the restored pass
  returns its own shading `Y'`, and the record it lands in is the **new** structure
  `Kakeya.ml1Boot.IsRepairUniformPassThreaded` below, whose `unif` and refinement-mass clauses
  read at `Y'` and which carries the containment clause `shadeTube` making `Y'` an output
  shading.  The new record also omits the old `fibreFrostman` field: the composed fibrewise
  Frostman transport is *not* available from the uniformization tool this pass runs, so it is not
  claimed here.  **That is a real, hypothesis**, not a discharged one; see the note on
  `Kakeya.ml1Boot.IsRepairUniformPassThreaded`.
-/

/-- **The conclusions of the restored banded (R2) pass, one field per inequality** — the
output-shading form of `Kakeya.ml1Boot.IsRepairUniformPass`.

This is a **new** structure, not a restatement: `Kakeya.ml1Boot.IsRepairUniformPass` is
untouched above, and this record exists because that one is undeliverable in two respects.
The differences, both of them weakenings *relative to that record*, are declared here rather
than hidden:

* `unif` and the mass half of `refinement` read at the pass's **own** output shading
  `Y' : ι → ShadedTube δ E`, related to the input `T` only by the new field `shadeTube`
  (`(Y' i).toTube = (T i).toTube` and `(Y' i).shade ⊆ (T i).shade` on `s'`).  Every other field
  reads at `T`, unchanged.

* There is **no** `fibreFrostman` field.  `Kakeya.ml1Boot.IsRepairUniformPass.fibreFrostman`
  bounds the growth of every retained fine fibre's Frostman constant by `δ ^ (-ε')`; the
  uniformization route used by `Kakeya.ml1Boot.exists_repairUniform_banded` below cuts fibres
  and does not control that ratio, so the clause is dropped from *this* record and becomes an
  obligation on whatever consumes it.  Consumers must therefore carry the fibrewise transport
  as their own hypothesis; no declaration in this development discharges it today. -/
structure IsRepairUniformPassThreaded {ι κ : Type*} [DecidableEq κ] {δ τ θ : NNReal} (ε' : ℝ)
    (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ) (Tθ : κ → Tube θ E) (pθ : κ → κ)
    (s : Finset ι) (tτ tθ : Finset κ)
    (s' : Finset ι) (t'τ t'θ : Finset κ) (Y' : ι → ShadedTube δ E) (lam' : NNReal) : Prop where
  /-- (a) The output shading `Y'` shades the same tubes as `T`, with shades contained in `T`'s,
  on the retained leaf set.  This is what makes `Y'` an output shading of the pass. -/
  shadeTube : ∀ i ∈ s', (Y' i).toTube = (T i).toTube ∧ (Y' i).shade ⊆ (T i).shade
  /-- (a) `(𝕋|_{s'}, Y')` is a `δ ^ ε'`-refinement of `(𝕋|_{s}, Y)`; the refined side reads at
  the output shading. -/
  refinement : ShadedBody.IsCRefinement s' (fun i => (Y' i).toShadedBody) s
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩
  /-- (a) …and retains all but a `δ ^ (-ε')` share of the index set. -/
  card : (s.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s'.card : ℝ)
  /-- (b) The retained family is uniform at `Kakeya.ml1Boot.uniformize.C 3`, **at the output
  shading `Y'`**. -/
  unif : Nonempty (ShadedTube.ShadedUniformTubeSet s' Y' (Tube.ssfGridLen δ)
    (uniformize.C 3))
  /-- (b) The shading densities on `s'` are two-sidedly comparable to `λ'`, read at the input
  shading `T`.  Free from the input band. -/
  dens : ∀ i ∈ s', (lam' : ENNReal) * volume (T i).carrier ≤ volume (T i).shade ∧
    volume (T i).shade ≤ 2 * (lam' : ENNReal) * volume (T i).carrier
  /-- (b) …and `λ'` is at least `δ ^ ε'` times the fullness of the input family. -/
  lamGe : (δ : ENNReal) ^ ε' * ShadedBody.fullness s (fun i => (T i).toShadedBody)
    ≤ (lam' : ENNReal)
  /-- (c) Essential distinctness of the leaves is inherited. -/
  essDistinctLeaf : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
    (s' : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
  /-- (c) Essential distinctness of the `τ`-nodes is inherited. -/
  essDistinctFine : (tτ : Set κ).Pairwise
      (fun k k' => IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier) →
    (t'τ : Set κ).Pairwise (fun k k' => IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier)
  /-- (c) Essential distinctness of the `θ`-nodes is inherited. -/
  essDistinctCoarse : (tθ : Set κ).Pairwise
      (fun l l' => IsEssentiallyDistinct (Tθ l).carrier (Tθ l').carrier) →
    (t'θ : Set κ).Pairwise (fun l l' => IsEssentiallyDistinct (Tθ l).carrier (Tθ l').carrier)
  /-- (d) `(t'τ, 𝕋_τ, pτ)` is again a parent family for the retained leaves at scale `τ`. -/
  parentFine : IsParentFamily s' (fun i => (T i).toTube) t'τ Tτ pτ
  /-- (d) `(t'θ, 𝕋_θ, pθ)` is again a parent family for the retained `τ`-nodes at scale `θ`. -/
  parentCoarse : IsParentFamily t'τ Tτ t'θ Tθ pθ

/-- **The restored (R2) uniformization pass, banded at the input** (blueprint
`lem:ml1bootRepairUniform`, restored form; harvested from `zzk` `7d4c144b1` and re-verified
here).

From `s.Nonempty`, positive input shade mass, `B₁`-containment, pairwise essentially distinct
leaves, the two `IsParentFamily` hypotheses and the **input band**
`(lam₀)(hlam₀)(hband)`, this concludes a retained leaf set `s' ⊆ s`, the trivial node outputs
`t'τ := tτ` and `t'θ := tθ`, an output shading `Y'`, a density `lam'` and
`Kakeya.ml1Boot.IsRepairUniformPassThreaded`.

**Why this is not an instance of the refutation.**
`Kakeya.ml1Boot.not_exists_repairUniform` refutes the pass that hypothesises *nothing* about the
shadings while concluding `dens`'s positive lower bound at a leaf set its own clauses force
nonempty; its witness is an all-empty shading, which violates both the positive-mass hypothesis
and the band here.  The band is what makes `dens` and `lamGe` free, with `lam' := lam₀`.

The whole gated cluster — `shadeTube`, `card`, `refinement` at `Y'`, `unif` at `Y'`,
`s'.Nonempty` — is one citation of `Kakeya.ml1Boot.exists_bandShadedUniformTubeSet`. -/
theorem exists_repairUniform_banded (hdim : Module.finrank ℝ E = 3) {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ τ θ : NNReal, δ ≤ τ → τ ≤ θ → θ ≤ 1 →
      ∀ {ι κ : Type*} [DecidableEq κ] {s : Finset ι} {tτ tθ : Finset κ}
        (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ)
        (Tθ : κ → Tube θ E) (pθ : κ → κ),
        s.Nonempty →
        0 < ∑ i ∈ s, volume (T i).shade →
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        IsParentFamily s (fun i => (T i).toTube) tτ Tτ pτ →
        IsParentFamily tτ Tτ tθ Tθ pθ →
        ∀ (lam₀ : NNReal), 0 < lam₀ →
          (∀ i ∈ s, (lam₀ : ENNReal) * volume (T i).carrier ≤ volume (T i).shade ∧
            volume (T i).shade ≤ 2 * (lam₀ : ENNReal) * volume (T i).carrier) →
        ∃ s' ⊆ s, ∃ t'τ ⊆ tτ, ∃ t'θ ⊆ tθ, ∃ Y' : ι → ShadedTube δ E, ∃ lam' : NNReal,
          0 < lam' ∧ s'.Nonempty ∧
            IsRepairUniformPassThreaded ε' T Tτ pτ Tθ pθ s tτ tθ s' t'τ t'θ Y' lam' := by
  classical
  filter_upwards [self_mem_nhdsWithin, exists_bandShadedUniformTubeSet hdim hε'] with δ _ hδtool
  intro τ θ hδτ hτθ hθ1 ι κ _ s tτ tθ T Tτ pτ Tθ pθ hs hpos hball hED hFine hCoarse lam₀
    hlam₀ hband
  have hR2 : ∃ s' ⊆ s, ∃ Y' : ι → ShadedTube δ E, ∃ lam' : NNReal,
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
    exact hδtool (s := s) (tτ := tτ) T pτ hs hball hED lam₀ hlam₀ hband
  rcases hR2 with ⟨s', hs's, Y', lam', hne, hlam, hshade, hcard, href, hunif, hdens, hlamGe⟩
  refine ⟨s', hs's, tτ, ?_, tθ, ?_, Y', lam', hlam, hne, ?_⟩
  · intro k hk
    exact hk
  · intro k hk
    exact hk
  · refine ({
      shadeTube := hshade,
      refinement := href,
      card := hcard,
      unif := hunif,
      dens := hdens,
      lamGe := hlamGe,
      essDistinctLeaf := fun h => Set.Pairwise.mono (Finset.coe_subset.mpr hs's) h,
      essDistinctFine := fun h => h,
      essDistinctCoarse := fun h => h,
      parentFine := IsParentFamily.mono hFine hs's (by intro k hk; exact hk)
        (fun i hi => hFine.mapsTo i (hs's hi)),
      parentCoarse := IsParentFamily.mono hCoarse (by intro k hk; exact hk)
        (by intro k hk; exact hk) (fun k hk => hCoarse.mapsTo k hk) })

/-- **The discard intermediate of the restored (R2) pass** (blueprint
`lem:ml1bootRepairUniformDiscard`, restored banded form; harvested from `zzk` `abace0895`).

Same hypotheses as `Kakeya.ml1Boot.exists_repairUniform_banded`; the conclusion keeps only the
clauses the three-pass assembly reads — `s' ⊆ s` with `s'.Nonempty`, the output shading `Y'`
with its containment, `refinement` at `Y'`, `card`, `unif` at `Y'` and the `essDistinctLeaf`
inheritance — dropping the node outputs, the density clauses and `lam'`. -/
theorem exists_repairUniformDiscard_banded (hdim : Module.finrank ℝ E = 3) {ε' : ℝ}
    (hε' : 0 < ε') :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ τ θ : NNReal, δ ≤ τ → τ ≤ θ → θ ≤ 1 →
      ∀ {ι κ : Type*} [DecidableEq κ] {s : Finset ι} {tτ tθ : Finset κ}
        (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ)
        (Tθ : κ → Tube θ E) (pθ : κ → κ),
        s.Nonempty →
        0 < ∑ i ∈ s, volume (T i).shade →
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        IsParentFamily s (fun i => (T i).toTube) tτ Tτ pτ →
        IsParentFamily tτ Tτ tθ Tθ pθ →
        ∀ (lam₀ : NNReal), 0 < lam₀ →
          (∀ i ∈ s, (lam₀ : ENNReal) * volume (T i).carrier ≤ volume (T i).shade ∧
            volume (T i).shade ≤ 2 * (lam₀ : ENNReal) * volume (T i).carrier) →
        ∃ s' ⊆ s, ∃ Y' : ι → ShadedTube δ E,
          s'.Nonempty ∧
            (∀ i ∈ s', (Y' i).toTube = (T i).toTube ∧ (Y' i).shade ⊆ (T i).shade) ∧
            ShadedBody.IsCRefinement s' (fun i => (Y' i).toShadedBody) s
              (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩ ∧
            (s.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s'.card : ℝ) ∧
            Nonempty (ShadedTube.ShadedUniformTubeSet s' Y' (Tube.ssfGridLen δ)
              (uniformize.C 3)) ∧
            ((s : Set ι).Pairwise
                (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
              (s' : Set ι).Pairwise
                (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)) := by
  filter_upwards [exists_repairUniform_banded hdim hε'] with δ hδ
  intro τ θ hδτ hτθ hθ1 ι κ _ s tτ tθ T Tτ pτ Tθ pθ hsne hpos hBall hED hfine hcoarse lam₀
    hlam₀ hband
  rcases hδ τ θ hδτ hτθ hθ1 (s := s) (tτ := tτ) (tθ := tθ) T Tτ pτ Tθ pθ hsne hpos hBall hED
    hfine hcoarse lam₀ hlam₀ hband with
    ⟨s1, hs1, t'τ, ht'τ, t'θ, ht'θ, Y', lam', hlam0, hs1ne, hpass⟩
  refine ⟨s1, hs1, Y', hs1ne, hpass.shadeTube, hpass.refinement, hpass.card, hpass.unif,
    hpass.essDistinctLeaf⟩


end ml1Boot

end Kakeya
