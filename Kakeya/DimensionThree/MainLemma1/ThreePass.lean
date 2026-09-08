/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Repair

/-!
# Main Lemma 1, Case (ii): Step 2 of the repair, the three passes (R2) → (R1) → (R2)

Blueprint `lem:ml1bootRepairThreePass`.  Move (R1) is
`Kakeya.ml1Boot.exists_repairEssDistinct`, stated and proved in
`Kakeya/DimensionThree/MainLemma1/Repair.lean`.  Move (R2) has **no** Lean statement: its former
one was deleted as refuted, see below.

**The assembly itself is not written**, and this docstring used to describe it as though it
were.  There is no `Kakeya.ml1Boot.exists_repairThreePass` and no
`Kakeya.ml1Boot.exists_repairUniformDiscard` anywhere in the project; where those names appear
in this file they name the *intended* declarations, not existing ones.  What the file actually
contains is the target bundle, the device the assembly would run, and the side facts its call
site needs:

* two exponent identities, `Kakeya.ml1Boot.nnrealPow_mul_self` and
  `Kakeya.ml1Boot.ennrealPow_neg_three`;
* the conclusion bundle `Kakeya.ml1Boot.IsRepairThreePass`;
* the post-selection trim `Kakeya.ml1Boot.exists_trimmedPass`, which is proved and which is what
  produces the fibrewise empty-or-share clause of that bundle;
* the bridging devices for the Case (ii) call site, from
  `Kakeya.ml1Boot.gridScale_le_gridScale` to `Kakeya.ml1Boot.eventually_rpow_le_quarter`.

## The premise the assembly would rest on is refuted

**Move (R2) is false.**  Its negation is proved, in
`Kakeya/DimensionThree/MainLemma1/Repair.lean`, as
`Kakeya.ml1Boot.not_exists_repairUniform`: the pass hypothesises nothing about the shadings
while concluding a positive lower bound on them at a leaf set its own clauses force nonempty, so
an all-empty shading contradicts it.  The statement has accordingly been deleted, and its
blueprint environment carries no `\leanok`.

So the assembly cannot be written in the shape the blueprint states: it would cite (R2) twice,
and any such derivation would establish nothing.  That, and not an unfinished proof, is why no
assembly declaration appears below.  Move (R1) is unaffected.

**The claim that this assembly would be reusable verbatim once (R2) gains its missing hypothesis
is withdrawn.**  (R2) has a *second* defect, recorded in the docstring of
`Kakeya.ml1Boot.card_shadeClass_le_card_shadeClass` in
`Kakeya/DimensionThree/MainLemma1/Repair.lean`:
`Kakeya.ml1Boot.IsRepairUniformPass.unif` asserts uniformity
at the shading the pass is handed, and no hypothesis removes that, because uniformity is produced
only after *shrinking* the shading.  A repaired pass therefore returns a shading of its own, and
then this assembly is not reusable verbatim: two of its three passes are (R2), so the leaf shading
is shrunk twice, and three things here read the shading and not merely the index set — the two
refinement links composed by `ShadedBody.IsCRefinement.trans`, which would compose across three
distinct shadings; the weight and bracket arguments that read the *frozen* banding clause of
`Kakeya.ml1Boot.IsCaseTwoInput`, which is stated at the input shading and would not cover the
output; and `Kakeya.ml1Boot.IsRepairThreePass.unif`, which would be delivered at the twice-shrunk
shading.  Whether to pay that or to weaken `unif` at the source is an open design decision about
this assembly.

## Why the order is (R2) → (R1) → (R2), and why there are three passes and not two

Uniformity is not inherited by subfamilies.  Move (R1) *consumes* a uniform shaded family, so it
cannot run first; and it *deletes leaves*, so the uniformity it consumed does not survive it
either, while `Kakeya.ml1Boot.IsCaseTwoData.refine_unif` demands the final leaf family be uniform.
Hence a (R2) pass on each side.  Blueprint `note:ml1bootRepairOrderGWZ` records that this diverges
from the source's ordering, and `note:ml1bootRepairEDLeafShadedUniformity` records that the
divergence is what makes the chain statable at all.

## The node outputs of the two (R2) passes are discarded

The three-pass lemma returns move (R1)'s node sets `t'τ = t²τ ⊆ 𝒰'_b` and `t'θ = t¹θ`, not the
last pass's.  Discarding is free on the *upper* side: at a node a pass has dropped no retained
leaf lies, so the retained fine fibre there is empty and every upper Frostman bound holds at it
for nothing — `Kakeya.ml1Boot.fibre_eq_empty_of_notMem` and
`Kakeya.ml1Boot.fibreFrostman_of_mapsTo`.  That is what the intended
`Kakeya.ml1Boot.exists_repairUniformDiscard` would package: one (R2) pass, its node output
dropped, its fibrewise transport extended from the nodes it kept to *every* node.  The three-pass
proof would then make exactly three citations — that lemma twice and (R1) once — plus one call of
`Kakeya.ml1Boot.fibreFrostman_chain`.

Why the discard is worth making: it puts the whole of Case (ii)'s residual obligation on **one**
application of `Kakeya.ml1Boot.exists_essDistinct_parentFamily`, at an index set cut out of the
full node family `𝒰'_b` directly, rather than on a composite of three deletions two of which are
pigeonhole uniformizations that could not respect coarse fibres even in principle.  That obligation
is the fibrewise empty-or-share dichotomy `Kakeya.ml1Boot.IsFibrewiseEmptyOrShare`; blueprint
`note:ml1bootEssDistinctFibrewiseShare` is its record.

The dichotomy itself is **supplied**, and this paragraph used to say it was still open. What is open is a
**caller**: nothing yet runs the trim at this point of the chain and hands the dichotomy on.

## What the discard costs, and it is exactly one thing

The output node sets may contain nodes carrying *no* retained leaf: `t'τ` is (R1)'s and the third
pass deletes leaves after it, so a `k ∈ t'τ` need have no `i ∈ s₀` with `pτ i = k`.  Item (c) of
the blueprint lemma — here `Kakeya.ml1Boot.IsRepairThreePass.parentFine` — asserts the containment
`{pτ i : i ∈ s₀} ⊆ t'τ` and **not** its converse, and the analogue of
`Kakeya.ml1Boot.IsCoarseNodeParents.nodes_carry_leaf` at `(t'τ, s₀)` is therefore *not* available
downstream and must not be assumed from the input bundle having it at `(𝒰'_b, s')`.  Nothing in
the conclusion needs it: the fibrewise item is an *upper* bound, the essential-distinctness items
are conditions on pairs, and the containments are one-sided by design.

## No middle bound appears, in the hypotheses or the conclusion

Move (R1) is the only step that deletes a `τ`-node from the output, and it does not control what
survives inside a coarse fibre, so there is nothing for a middle clause to transport.  See
`Kakeya.ml1Boot.frostmanConstIn_retainedFibre_le` for the half of that item which *is* proved, and
blueprint `note:ml1bootEssDistinctFibrewiseShare` for the half which is not.  The fibrewise item
(e) below is at the **fine** fibres of `pτ`, a different statement, and it is transported by all
three passes.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody Filter Topology

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Two exponent identities

The three-pass tally is `ε' + ε' = 2 ε'` on the refinement side and `-ε' - ε' - ε' = -3 ε'` on the
fibre side.  Both are pure `rpow` arithmetic, and both are stated separately here rather than
inlined, because the assembly below is otherwise plumbing and this is the only place in it where a
side condition on `δ` is read. -/

/-- **The refinement constant of two composed passes** (blueprint `lem:ml1bootRepairThreePass`,
item (a)).

`ShadedBody.IsCRefinement.trans` returns the *product* of the two constants, and the conclusion is
stated at a single `rpow`; this is the conversion, in `NNReal`, where the constants live. -/
theorem nnrealPow_mul_self (δ : NNReal) (hδ : 0 < δ) (ε' : ℝ) :
    (⟨(δ : ℝ) ^ ε', by positivity⟩ : NNReal) * ⟨(δ : ℝ) ^ ε', by positivity⟩
      = ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩ := by
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ
  simp [← Real.rpow_add hδR, show ε' + ε' = 2 * ε' by ring]

/-- **The fibre-transport constant of three composed passes** (blueprint
`lem:ml1bootRepairThreePass`, item (e)).

`Kakeya.ml1Boot.fibreFrostman_chain` returns the product of the three factors, and the conclusion
is stated at a single `rpow`; this is the conversion, in `ENNReal`. -/
theorem ennrealPow_neg_three (δ : NNReal) (hδ : 0 < δ) (ε' : ℝ) :
    (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ (-ε')
      = (δ : ENNReal) ^ (-3 * ε') := by
  have hδ0 : (δ : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hδ)
  rw [← ENNReal.rpow_add _ _ hδ0 ENNReal.coe_ne_top]
  rw [← ENNReal.rpow_add _ _ hδ0 ENNReal.coe_ne_top]
  exact congrArg (fun x : ℝ => (δ : ENNReal) ^ x) (by ring)

/-- **The conclusions of `Kakeya.ml1Boot.exists_repairThreePass`, one field per clause**
(blueprint `lem:ml1bootRepairThreePass`, items (a)–(e)).

Here `(𝕋, Y)` is the family of shaded `δ`-tubes indexed by the input leaf set `s'`, `(tτ, 𝕋_τ, pτ)`
and `(tθ, 𝕋_θ, pθ)` are the two ambient node parent families, `s₂` is where the first two passes
end and `s₀` where the third does, and `t'τ`, `t'θ` are move (R1)'s node sets.

*Why `s₂` is a parameter and not only `s₀`.*  The two chains
`Kakeya.ml1Boot.repairFullnessChain` and `Kakeya.ml1Boot.repairCountChain` are three-link chains
`s → s' → s₂ → s₀`, and the middle link is the composite of the first two passes; `s₂` is where
that composite ends, so it has to be visible.  The outer link `s → s'` is the caller's — the two
accuracy-carrying clauses of `Kakeya.ml1Boot.IsCaseTwoInput` — and is deliberately not read here:
this lemma is the passes and nothing else. -/
structure IsRepairThreePass {ι κ : Type*} [DecidableEq κ] {δ τ θ : NNReal} (ε' : ℝ)
    (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ) (Tθ : κ → Tube θ E) (pθ : κ → κ)
    (tτ tθ : Finset κ) (s' s₂ s₀ : Finset ι) (t'τ t'θ : Finset κ) : Prop where
  /-- (f) **The fibrewise empty-or-share dichotomy at the retained fine node set**
  (`Kakeya.ml1Boot.IsFibrewiseEmptyOrShare`), at the share `δ ^ (6 ε')`.

  This is the clause `Kakeya.ml1Boot.exists_caseTwoData` needs and that nothing used to supply:
  at every coarse node of `tθ`, the fibre of `t'τ` is either empty or carries a
  `δ ^ (6 ε')`-share of the fibre of the *ambient* fine node set `tτ`.  It is produced by the
  post-selection trim `Kakeya.ml1Boot.fibrewiseTrim`, run inside the proof between move (R1) and
  the third pass — the only point at which (R1)'s own weight retention and the first pass's count
  retention are both in scope.

  The exponent is `6 ε'` because the consumer reads this structure at `ε' = ε'_outer / 8` and asks
  for the share at `δ ^ (3 ε'_outer / 4) = δ ^ (6 ε')`.  The trim supplies a *larger* share and
  `Kakeya.ml1Boot.IsFibrewiseEmptyOrShare.mono_share` weakens it to this one.

  The ambient node sets `tτ`, `tθ` are structure parameters rather than a hierarchy: the dichotomy
  is a statement about two `Finset`s and a map, so this structure stays free-standing even though
  the theorem producing it no longer is. -/
  dichotomy : IsFibrewiseEmptyOrShare tτ tθ t'τ pθ ((δ : ENNReal) ^ (6 * ε'))
  /-- (a) The composite of the first two passes is a `δ ^ (2 ε')`-refinement. -/
  refineMid : ShadedBody.IsCRefinement s₂ (fun i => (T i).toShadedBody) s'
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩
  /-- (a) …and the third pass is a `δ ^ ε'`-refinement on top of it. -/
  refineLast : ShadedBody.IsCRefinement s₀ (fun i => (T i).toShadedBody) s₂
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩
  /-- (a) The third pass retains all but a `δ ^ (-ε')` share of the index set.  Stated in `ℝ`,
  which is the spelling `Kakeya.ml1Boot.repairCountChain` reads. -/
  card : (s₂.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s₀.card : ℝ)
  /-- (a) `s₂` is nonempty.  This is what the third pass consumes, and it comes from the mass
  retention of the first two together with the assumed positivity of the input shade mass. -/
  nonemptyMid : s₂.Nonempty
  /-- (a) `s₀` is nonempty. -/
  nonemptyLast : s₀.Nonempty
  /-- (b) The final leaf family is uniform, at the dimension-only constant
  `Kakeya.ml1Boot.uniformize.C 3`.  *This is why there are three passes and not two*: move (R1)
  deletes leaves, so the first pass's uniformity does not survive to `s₂`. -/
  unif : Nonempty (ShadedTube.ShadedUniformTubeSet s₀ T (Tube.ssfGridLen δ)
    (uniformize.C 3))
  /-- (c) `(t'τ, 𝕋_τ, pτ)` is a parent family for the retained leaves at scale `τ`.  Its `mapsTo`
  clause is the containment `{pτ i : i ∈ s₀} ⊆ t'τ`; the converse is **false** in general, `t'τ`
  being move (R1)'s and the third pass deleting leaves after it. -/
  parentFine : IsParentFamily s₀ (fun i => (T i).toTube) t'τ Tτ pτ
  /-- (c) `(t'θ, 𝕋_θ, pθ)` is a parent family for the retained `τ`-nodes at scale `θ`. -/
  parentCoarse : IsParentFamily t'τ Tτ t'θ Tθ pθ
  /-- (d) The retained `τ`-nodes are pairwise essentially distinct.  This is move (R1)'s own
  clause read verbatim, with no inheritance step. -/
  essDistinctFine : (t'τ : Set κ).Pairwise
    (fun k l => IsEssentiallyDistinct (Tτ k).carrier (Tτ l).carrier)
  /-- (d) The retained `θ`-nodes are pairwise essentially distinct. -/
  essDistinctCoarse : (t'θ : Set κ).Pairwise
    (fun k l => IsEssentiallyDistinct (Tθ k).carrier (Tθ l).carrier)
  /-- (e) The three passes' fibrewise Frostman transports, composed: the factor is `δ ^ (-3 ε')`,
  one `δ ^ (-ε')` per pass.  The side condition is at the pass's own *input* fibre over `s'`,
  which is what makes `Kakeya.ml1Boot.fibreFrostman_chain` applicable, and the bound is asserted at
  every `k ∈ t'τ` — including the nodes the third pass dropped, where it is free. -/
  fibreFrostman : ∀ k ∈ t'τ, ∀ K : ConvexSpaceBody E,
    (∀ i ∈ fibre s' pτ k, (T i).toConvexSpaceBody ≤ K) →
    frostmanConstIn (fibre s₀ pτ k) (fun i => (T i).toConvexSpaceBody) K
      ≤ (δ : ENNReal) ^ (-3 * ε')
        * frostmanConstIn (fibre s' pτ k) (fun i => (T i).toConvexSpaceBody) K

/-- **The post-selection trim, packaged for the three-pass proof** (blueprint
`lem:ml1bootTrimmedPass`).

`Kakeya.ml1Boot.fibrewiseTrim` together with the payment of its cost by
`Kakeya.ml1Boot.fibrewiseTrimCost`, in the one shape the three-pass proof consumes: applied to
move (R1)'s output `(s₂, t₂τ)`, against the ambient node sets `tτ`, `tθ` and the input leaf set
`s'`, at the shade-mass weight.

The two weight hypotheses are abstract — a fibrewise upper bound and an *aggregate* lower bound,
both statements about the input data `s'`, `tτ` — which is what keeps the three-pass lemma free of
any hierarchy; the caller discharges them from the class brackets and the banding exactly as
`Kakeya.ml1Boot.fibrewiseTrimCost_of_hierarchy` does.

The fourth conclusion is the one that makes the trim usable downstream: the retained fibres are
*literally unchanged*, so every fibrewise statement carried at `s₂` transfers verbatim to `s₂''`.
A Frostman constant is a ratio and does not descend to a subfamily, so this equality — and not any
monotonicity — is what lets the fibrewise transport survive the trim. -/
theorem exists_trimmedPass {ι κ : Type*} [DecidableEq κ] {δ σ : NNReal}
    {s' s1 s2 : Finset ι} {tτ tθ t2τ : Finset κ} {T : ι → ShadedTube δ E}
    {Tτ : κ → Tube σ E} {pτ : ι → κ} {pθ : κ → κ} {ν η mplus mminus : ENNReal}
    (ht2τ : t2τ ⊆ tτ) (hs2 : s2 ⊆ s1) (hs1 : s1 ⊆ s')
    (hpar : IsParentFamily s2 (fun i => (T i).toTube) t2τ Tτ pτ)
    (hED : (t2τ : Set κ).Pairwise fun k k' =>
      IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier)
    (hplus : ∀ k ∈ tτ, (∑ i ∈ fibre s' pτ k, volume (T i).shade) ≤ mplus)
    (hminus : mminus * (tτ.card : ENNReal) ≤ ∑ i ∈ s', volume (T i).shade)
    (hν : 2 * (ν * mplus) ≤ η * mminus)
    (hret : η * (∑ i ∈ s', volume (T i).shade) ≤ ∑ i ∈ s2, volume (T i).shade)
    (hfin : η * (∑ i ∈ s', volume (T i).shade) ≠ ⊤) :
    ∃ t'' ⊆ t2τ, ∃ s2'' ⊆ s2,
      IsParentFamily s2'' (fun i => (T i).toTube) t'' Tτ pτ ∧
      (t'' : Set κ).Pairwise
        (fun k k' => IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier) ∧
      IsFibrewiseEmptyOrShare tτ tθ t'' pθ ν ∧
      (∀ k ∈ t'', fibre s2'' pτ k = fibre s2 pτ k) ∧
      η * (∑ i ∈ s', volume (T i).shade) ≤ 2 * ∑ i ∈ s2'', volume (T i).shade := by
  classical
  set t'' : Finset κ := trimNodes tτ tθ t2τ pθ ν with ht''def
  set s2'' : Finset ι := s2.filter (fun i => pτ i ∈ t'') with hs2''def
  obtain ⟨htPar, htED, htDich, htFib, htLost, htCard⟩ :=
    fibrewiseTrim (E := E) ht''def hs2''def hpar hED
  have hcost : η * (∑ i ∈ s', volume (T i).shade) ≤ 2 * ∑ i ∈ s2'', volume (T i).shade := by
    refine fibrewiseTrimCost (u := s') (u' := s2) (u'' := s2'') (sb := tτ)
      (t' := t2τ) (t'' := t'') (p := pτ) (w := fun i => volume (T i).shade)
      (ν := ν) (η := η) (mplus := mplus) (mminus := mminus)
      ht2τ hs2''def htLost htCard
      (fun k hk => le_trans (Finset.sum_le_sum_of_subset
          (by simpa only [fibre] using Finset.filter_subset_filter _ (hs2.trans hs1)))
        (hplus k hk))
      hminus hν hret hfin
  exact ⟨t'', by simpa only [ht''def, trimNodes] using Finset.filter_subset _ _,
    s2'', Finset.filter_subset _ _,
    htPar, htED, htDich, htFib, hcost⟩

/-! ### Bridging devices for the Case (ii) call site

`Kakeya.ml1Boot.exists_caseTwoDataRepair` applies the three-pass lemma at the node families of a
hierarchy, and nine small facts stand between its hypotheses and the three-pass hypotheses.  Each
is two lines and none of them existed; they are collected here rather than at their subject matter
because each is used exactly once, at that call site.

The last three close the remaining places where a hypothesis would otherwise have to be massaged
inline at that call site, which is what this section exists to prevent.
`Kakeya.ml1Boot.sum_shade_pos_of_fullness_ge` takes the fullness bound in the shape
`Kakeya.ml1Boot.IsCaseFamily.fullness` actually has — a `δ`-power lower bound in `ENNReal`, not
the `NNReal` positivity that `Kakeya.ml1Boot.sum_shade_pos_of_fullness_pos` asks for;
`Kakeya.ml1Boot.nonempty_of_sum_shade_pos` supplies `s'.Nonempty`, the one three-pass hypothesis
for which the Case (ii) bundle offers no field at all; and
`Kakeya.ml1Boot.eventually_rpow_le_quarter` absorbs, into the eventual smallness of `δ`, the two
side conditions `δ ≤ 1` and `(δ : ℝ) ^ (ε' / 4) ≤ 1 / 4` that the Case (ii) chain lemmas carry —
a statement about the filter `δ → 0⁺` rather than about the passes.

*What is still missing after these nine is not a lemma but a hypothesis.*
`Kakeya.ml1Boot.isParentFamily_nodes_fine` asks for
`Set.InjOn (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) (𝒰'.cover.indexSet b)`, and nothing in
the Case (ii) input supplies it: `Tube.UniformTubeSet.tube_injOn` gives injectivity of
`k ↦ 𝒰'.cover.tube b k` as a *tube*, which is strictly weaker, `Tube` carrying two endpoint fields
beyond its body.  It is needed by the *conclusion* as well, through
`Kakeya.ml1Boot.IsCaseTwoRepairData.parentFine`, so it is not an artefact of this route and cannot
be routed around.  At the coarse index it is free, being
`Kakeya.ml1Boot.IsCoarseNodeParents.parent.injOn`; at the fine index it must become a hypothesis of
`Kakeya.ml1Boot.exists_caseTwoDataRepair`. -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The grid of scales is antitone in the index.**

`Tube.gridScale δ N k = δ ^ (k / N)` and `δ ≤ 1`, so a larger index names a *smaller*
scale.  This is what supplies `τ ≤ θ` at the Case (ii) call site, where `τ` is the scale of the
fine index `b` and `θ` that of the coarse index `a ≤ b`. -/
theorem gridScale_le_gridScale {δ : NNReal} (hδ1 : δ ≤ 1) (N : ℕ) {a b : ℕ} (hab : a ≤ b) :
    Tube.gridScale δ N b ≤ Tube.gridScale δ N a := by
  by_cases hN : (N : ℝ) = 0
  · simp [Tube.gridScale, hN]
  · by_cases hδ0 : δ = 0
    · subst hδ0
      by_cases ha0 : a = 0
      · subst ha0
        simpa [Tube.gridScale]
          using (Tube.gridScale_le_one hδ1 N b)
      · have hb0 : b ≠ 0 := by
          omega
        have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb0
        have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha0
        have he1 : (b : ℝ) / (N : ℝ) ≠ 0 := div_ne_zero hbR hN
        have he2 : (a : ℝ) / (N : ℝ) ≠ 0 := div_ne_zero haR hN
        simp [Tube.gridScale, he1, he2]
    · have hδpos : 0 < δ := lt_of_le_of_ne (by positivity) (Ne.symm hδ0)
      apply NNReal.rpow_le_rpow_of_exponent_ge hδpos hδ1
      exact div_le_div_of_nonneg_right (by exact_mod_cast hab) (by exact_mod_cast (Nat.zero_le N))

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Every grid scale is at least `δ`.**

`δ ^ (k / N) ≥ δ ^ 1` for `δ ≤ 1` and `k ≤ N`.  This is what supplies `δ ≤ τ` at the Case (ii)
call site.  No positivity of `N` is needed: at `N = 0` the hypothesis forces `k = 0` and the scale
is `1`. -/
theorem le_gridScale {δ : NNReal} (hδ1 : δ ≤ 1) {N k : ℕ} (hk : k ≤ N) :
    δ ≤ Tube.gridScale δ N k := by
  by_cases hN : N = 0
  · subst N
    have hk0 : k = 0 := by omega
    subst hk0
    simpa [Tube.gridScale] using hδ1
  · have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
    by_cases hδ0 : δ = 0
    · rw [hδ0]
      simp
    · have hdiv : (k : ℝ) / (N : ℝ) ≤ 1 := by
        rw [← div_self (ne_of_gt hNpos)]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hk) (le_of_lt hNpos)
      have hδpos : 0 < δ := lt_of_le_of_ne (by positivity) (Ne.symm hδ0)
      simpa [Tube.gridScale]
        using (NNReal.rpow_le_rpow_of_exponent_ge hδpos hδ1 hdiv)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Bounded overlap weakens in the constant** (blueprint `lem:ml1bootBoundedOverlapMonoConst`).

This is a *companion* of blueprint `lem:ml1bootBoundedOverlapMono` and not a part of it: that
lemma restricts the two index sets at a **fixed** constant, and its three parts are the
parent-family clause and the two restrictions.  Weakening the constant is a fourth statement, and
it is stated separately so that no `\lean` tag claims one for the other.

In Lean it is the companion of `Kakeya.ml1Boot.HasBoundedOverlap.mono_leaves`.  It is what lets a
caller holding
the hierarchy's own overlap constant `C_ds`, which carries no lower bound, feed
`Kakeya.ml1Boot.exists_repairThreePass`, whose overlap parameter is asked to be at least `1`: run
the three-pass at `max 1 C_ds` and weaken. -/
theorem HasBoundedOverlap.mono_const {ι κ : Type*} {σ ρ : NNReal} {s : Finset ι}
    {V : ι → Tube σ E} {t : Finset κ} {Vρ : κ → Tube ρ E} {Co Co' : NNReal}
    (h : HasBoundedOverlap s V t Vρ Co) (hCo : Co ≤ Co') :
    HasBoundedOverlap s V t Vρ Co' :=
  fun W => le_trans (h W) hCo

/-- **A `c`-refinement is a `c'`-refinement for every smaller `c'`.**

`ShadedBody.IsCRefinement` bounds the retained shade mass *below* by `c` times the input's, so
lowering `c` weakens the assertion.  The Case (ii) chain lemmas
`Kakeya.ml1Boot.repairFullnessChain` and `Kakeya.ml1Boot.repairCountChain` each ask for their three
links at one common exponent, while the three passes deliver them at `ε'`, `2 ε'` and `ε'`; this is
what brings them to the common one. -/
theorem isCRefinement_mono {ι : Type*} {s u : Finset ι} {V' V : ι → ShadedBody E} {c c' : NNReal}
    (h : ShadedBody.IsCRefinement u V' s V c) (hc : c' ≤ c) :
    ShadedBody.IsCRefinement u V' s V c' := by
  exact ⟨h.1, le_trans (mul_le_mul' (ENNReal.coe_le_coe.mpr hc) le_rfl) h.2⟩

/-- **A family of positive fullness carries positive shade mass.**

`ShadedBody.fullness` is the ratio `∑ |Y_i| / ∑ |T_i|`, so a positive fullness forces a positive
numerator.  This is the core of the step that turns `Kakeya.ml1Boot.IsCaseFamily.fullness` into
the shade-mass hypothesis of `Kakeya.ml1Boot.exists_repairThreePass`; the hypothesis here is a
`NNReal` positivity, whereas that field is an `ENNReal` bound `δ ^ η(γ) ≤ ↑λ`, so the call site
goes through `Kakeya.ml1Boot.sum_shade_pos_of_fullness_ge` rather than through this lemma
directly.  The argument is written out inside `Kakeya.ml1Boot.fullness_le_of_isCRefinement` but
was not exported. -/
theorem sum_shade_pos_of_fullness_pos {ι : Type*} {δ : NNReal} {s : Finset ι}
    (T : ι → ShadedTube δ E)
    (h : 0 < ShadedBody.fullness s (fun i => (T i).toShadedBody)) :
    0 < ∑ i ∈ s, volume (T i).shade := by
  have hfullENN : (0 : ENNReal) <
      (ShadedBody.fullness s (fun i => (T i).toShadedBody) : ENNReal) := by
    exact ENNReal.coe_pos.mpr h
  by_contra hnotpos
  have hAs : (∑ i ∈ s, volume (T i).shade) = 0 := by
    exact le_antisymm (not_lt.mp hnotpos) (by positivity)
  rw [ShadedBody.coe_fullness] at hfullENN
  simp [hAs] at hfullENN

/-- **Positive shade mass descends along a refinement.**

The second component of `ShadedBody.IsCRefinement` is exactly a lower bound on the retained mass by
a positive multiple of the input's.  Composed with
`Kakeya.ml1Boot.sum_shade_pos_of_fullness_pos` this carries the Case (ii) family's positive shade
mass from `s` down to the dichotomy's refinement `s'`, which is where
`Kakeya.ml1Boot.exists_repairThreePass` asks for it. -/
theorem sum_shade_pos_of_isCRefinement {ι : Type*} {δ : NNReal} {ε' : ℝ} {s u : Finset ι}
    (hδ : 0 < δ) (T : ι → ShadedTube δ E)
    (h : ShadedBody.IsCRefinement u (fun i => (T i).toShadedBody) s
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩)
    (hs : 0 < ∑ i ∈ s, volume (T i).shade) :
    0 < ∑ i ∈ u, volume (T i).shade := by
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ
  set c : NNReal := ⟨(δ : ℝ) ^ ε', by positivity⟩
  have hCoef : (0 : ENNReal) < (c : ENNReal) := by
    rw [ENNReal.ofReal_coe_nnreal.symm]
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδR ε')
  have hle : (c : ENNReal) * (∑ i ∈ s, volume (T i).shade) ≤
      ∑ i ∈ u, volume (T i).shade := by
    simpa using h.2
  exact lt_of_lt_of_le (ENNReal.mul_pos (ne_of_gt hCoef) (ne_of_gt hs)) hle

/-- **A `δ`-power lower bound on the fullness gives positive shade mass.**

`Kakeya.ml1Boot.sum_shade_pos_of_fullness_pos` asks for `0 < ShadedBody.fullness s 𝕋` as a
`NNReal` inequality, while the only supplier of it in Case (ii),
`Kakeya.ml1Boot.IsCaseFamily.fullness`, reads `δ ^ η(γ) ≤ ↑(ShadedBody.fullness s 𝕋)` in
`ENNReal`.  The gap between the two is one coercion and the positivity of `δ ^ x`, and this
lemma is that step, stated at an arbitrary exponent `x` because nothing here inspects `η(γ)`.

It is what makes the shade-mass hypothesis of `Kakeya.ml1Boot.exists_repairThreePass` a single
citation at the Case (ii) call site, in the shape the bundle actually hands over: apply this at
`s`, then descend to the dichotomy's refinement `s'` by
`Kakeya.ml1Boot.sum_shade_pos_of_isCRefinement` along
`Kakeya.ml1Boot.IsCaseTwoInput.refine_mass`. -/
theorem sum_shade_pos_of_fullness_ge {ι : Type*} {δ : NNReal} {x : ℝ} {s : Finset ι}
    (hδ : 0 < δ) (T : ι → ShadedTube δ E)
    (h : (δ : ENNReal) ^ x ≤ ShadedBody.fullness s (fun i => (T i).toShadedBody)) :
    0 < ∑ i ∈ s, volume (T i).shade := by
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hpow : (0 : ENNReal) < (δ : ENNReal) ^ x := by
    rw [ennreal_coe_nnreal_rpow hδR x]
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδR x)
  exact sum_shade_pos_of_fullness_pos T (ENNReal.coe_pos.mp (lt_of_lt_of_le hpow h))

/-- **A family of positive shade mass is nonempty.**

The empty sum is `0`, so a positive total shade mass forces an inhabited index set.  This is the
only hypothesis of `Kakeya.ml1Boot.exists_repairThreePass` for which
`Kakeya.ml1Boot.IsCaseTwoInput` has no field: the bundle's `subset` and `card_le` relate `s'` to
`s` but neither asserts `s'.Nonempty`, and `Kakeya.ml1Boot.IsCaseFamily.nonempty` is a statement
about `s`.  Composed with `Kakeya.ml1Boot.sum_shade_pos_of_fullness_ge` and
`Kakeya.ml1Boot.sum_shade_pos_of_isCRefinement` it supplies it from the same shade mass that the
three-pass lemma is separately asking for, so the call site pays for it once.

The argument is the one written inline for `s₂` inside
`Kakeya.ml1Boot.exists_repairThreePass`, where the mass in hand is move (R1)'s weight retention
rather than the bundle's. -/
theorem nonempty_of_sum_shade_pos {ι : Type*} {δ : NNReal} {s : Finset ι}
    (T : ι → ShadedTube δ E) (h : 0 < ∑ i ∈ s, volume (T i).shade) :
    s.Nonempty := by
  refine Finset.nonempty_iff_ne_empty.mpr ?_
  intro he
  have hZ : (∑ i ∈ s, volume (T i).shade) = 0 := by
    rw [he]
    simp
  exact (ne_of_gt h) hZ

/-- **Two absorptions into the eventual smallness of the scale** (blueprint
`lem:ml1bootEventuallySmallDelta`).

Let `α > 0`.  Then for all sufficiently small `δ > 0` one has both `δ ≤ 1` and
`(δ : ℝ) ^ α ≤ 1 / 4`.

The second conjunct is the side hypothesis `(δ : ℝ) ^ (ε' / 4) ≤ 1 / 4` of
`Kakeya.ml1Boot.caseTwoRepairCountChain`, read at `α = ε' / 4`; the first is the ambient
`0 < δ ≤ 1` that the chain lemmas of the Case (ii) region carry.  Every consumer in that region
needs both, and neither of them is an exponent — this is a statement about the filter `δ → 0⁺`
alone, which is why it is stated at a bare exponent `α` and here, away from the region it serves.
It is the ninth bridging device for the Case (ii) call site, and it exists so that the absorption
is a citation there rather than an inline filter computation.

The route: `Kakeya.absorb_const_le_rpow_neg` at `C = 4`, `η = α`, which gives `(4 : ℝ) ≤ δ ^ (-α)`
on `𝓝[>] (0 : ℝ)`, transported to `NNReal` by `Kakeya.nnreal_eventually_of_real_eventually`
(`Kakeya/Asymptotics.lean`), intersected with the elementary `δ ≤ 1` near `0`. -/
theorem eventually_rpow_le_quarter {α : ℝ} (hα : 0 < α) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, δ ≤ 1 ∧ (δ : ℝ) ^ α ≤ 1 / 4 := by
  have hδ1R : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), δ ≤ (1 : ℝ) := by
    apply Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))
    intro δ hδ
    simp only [Set.mem_Ioo] at hδ
    exact le_of_lt hδ.2
  filter_upwards [nnreal_eventually_of_real_eventually hδ1R,
      nnreal_eventually_of_real_eventually
        (absorb_const_le_rpow_neg (by norm_num : (0 : ℝ) < 4) hα),
      self_mem_nhdsWithin] with δ hδ1 hδ4 hδ0
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  constructor
  · exact_mod_cast hδ1
  · rw [Real.rpow_neg hδR.le] at hδ4
    let x : ℝ := (δ : ℝ) ^ α
    have hx : 0 < x := by
      dsimp [x]
      exact Real.rpow_pos_of_pos hδR α
    have hxinv : x⁻¹ * x = 1 := inv_mul_cancel₀ (ne_of_gt hx)
    have h4x : 4 * x ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_right hδ4 (le_of_lt hx), hxinv]
    have hxle : x ≤ 1 / 4 := by
      nlinarith [h4x, (by norm_num : (0 : ℝ) < 4)]
    simpa [x] using hxle

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Case (ii): the scale chain, the overlap constant and the two bounded-overlap conditions**
(blueprint `lem:ml1bootCaseIIPassScales`).

The three hypotheses of `Kakeya.ml1Boot.exists_repairThreePass` that read only the grid of the
hierarchy and the overlap constant, collected at one call so that the Case (ii) call site
discharges them by a single citation.  With `τ = ρ_b` and `θ = ρ_a` the fine and coarse grid
scales and `Co = max 1 C_ds`, these are the chain `δ ≤ τ ≤ θ ≤ 1`, the bound `1 ≤ Co`, and
bounded overlap `Co` of the leaves over each of the two node families.

Nothing here reads the shading, a parent map, `ε'`, `η` or the accuracy of the input; those are
the other half of the discharge.  Only `δ ≤ 1` is needed, not `0 < δ`: at `δ = 0` the grid is
still antitone and still bounded below by `δ`. -/
theorem caseTwoThreePassScales {ι : Type*} [Nontrivial E] {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {Cds : NNReal} (hδ1 : δ ≤ 1)
    (𝒰' : Tube.UniformTubeSet s' T N Cds) {a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N) :
    (δ ≤ Tube.gridScale δ N b ∧ Tube.gridScale δ N b ≤ Tube.gridScale δ N a ∧
        Tube.gridScale δ N a ≤ 1) ∧
      (1 : NNReal) ≤ max 1 Cds ∧
      HasBoundedOverlap s' T (𝒰'.cover.indexSet b) (𝒰'.cover.tube b) (max 1 Cds) ∧
      HasBoundedOverlap s' T (𝒰'.cover.indexSet a) (𝒰'.cover.tube a) (max 1 Cds) := by
  constructor
  · constructor
    · exact le_gridScale hδ1 hbN
    · constructor
      · exact gridScale_le_gridScale hδ1 N hab
      · exact Tube.gridScale_le_one hδ1 N a
  · constructor
    · exact le_max_left _ _
    · constructor
      · exact HasBoundedOverlap.mono_const (hasBoundedOverlap_nodes 𝒰' hbN) (le_max_right _ _)
      · exact HasBoundedOverlap.mono_const (hasBoundedOverlap_nodes 𝒰' (hab.trans hbN))
          (le_max_right _ _)

/-- **Case (ii): the two parent families, the shade mass and the nonemptiness of the refinement**
(blueprint `lem:ml1bootCaseIIPassShading`).

The other three hypotheses of `Kakeya.ml1Boot.exists_repairThreePass` that have to be produced
rather than inherited — the two counting as one item, being read off in one place — collected at
one call so that the Case (ii) call site discharges them by a single citation.  These are the ones
that inspect the shading and the parent maps;
`Kakeya.ml1Boot.caseTwoThreePassScales` is the half that reads only the grid and the overlap
constant.

The remaining two hypotheses of that lemma, that the leaves of `𝕋|_{s'}` lie in `B₁` and are
pairwise essentially distinct, are not here: they are standing hypotheses on `(𝕋, Y)` inherited by
`s' ⊆ s`, so there is nothing to prove and nothing to collect.

## What is unbundled, and why

The blueprint states this in the situation of `Kakeya.ml1Boot.IsCaseTwoInput` at accuracy `ε' / 8`.
That structure is declared in `Kakeya/DimensionThree/MainLemma1.lean`, which imports this file, so
it cannot be named here; `hmass` is its `refine_mass` field read at that accuracy and `hfull` is
`Kakeya.ml1Boot.IsCaseFamily.fullness` read at `η = p.ηGamma γ`, and a caller holding the two
bundles supplies both by projection.  The same unbundling is why
`Kakeya.ml1Boot.caseTwoThreePassScales` takes the hierarchy rather than the input.

No sign hypothesis on `η` is needed: `Kakeya.ml1Boot.sum_shade_pos_of_fullness_ge` reads the bound
at an arbitrary exponent, `δ ^ η` being positive for every real `η` once `δ > 0`.

## The node-body injectivity clause is carried, not proved

`hinjFine` is the injectivity clause of `Kakeya.ml1Boot.IsParentFamily` at the *fine* index, which
`Kakeya.ml1Boot.isParentFamily_nodes_fine` asks for and which nothing in the Case (ii) input
supplies: `Tube.UniformTubeSet.tube_injOn` gives injectivity of `k ↦ 𝒰'.cover.tube b k` as a
*tube*, which is strictly weaker, `Tube` carrying two endpoint fields beyond its body.  It is
needed by the conclusion as well, through `Kakeya.ml1Boot.IsCaseTwoRepairData.parentFine`, so it is
not an artefact of this route and cannot be routed around, and it is a hypothesis here for the
reason recorded above `Kakeya.ml1Boot.gridScale_le_gridScale`.  At the coarse index it is free,
being `Kakeya.ml1Boot.IsCoarseNodeParents.parent.injOn`, which is why only the fine clause is
asked for. -/
theorem caseTwoThreePassShading {ι : Type*} [Nontrivial E] {δ : NNReal} {ε' η : ℝ}
    {s s' : Finset ι} {T : ι → ShadedTube δ E} {N : ℕ} {Cds : NNReal} (hδ : 0 < δ)
    (𝒰' : Tube.UniformTubeSet s' (fun i => (T i).toTube) N Cds) {a b : ℕ} {pθ : ι → ι}
    (hcnp : IsCoarseNodeParents 𝒰' a b pθ)
    (hinjFine : Set.InjOn (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
      (𝒰'.cover.indexSet b))
    (hmass : ShadedBody.IsCRefinement s' (fun i => (T i).toShadedBody) s
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (ε' / 8), by positivity⟩)
    (hfull : (δ : ENNReal) ^ η ≤ ShadedBody.fullness s (fun i => (T i).toShadedBody)) :
    (IsParentFamily s' (fun i => (T i).toTube) (𝒰'.cover.indexSet b) (𝒰'.cover.tube b)
        (𝒰'.cover.assign b) ∧
      IsParentFamily (𝒰'.cover.indexSet b) (𝒰'.cover.tube b) (𝒰'.cover.indexSet a)
        (𝒰'.cover.tube a) pθ) ∧
    0 < ∑ i ∈ s', volume (T i).shade ∧ s'.Nonempty := by
  have hS : 0 < ∑ i ∈ s, volume (T i).shade := sum_shade_pos_of_fullness_ge hδ T hfull
  have hS' : 0 < ∑ i ∈ s', volume (T i).shade := sum_shade_pos_of_isCRefinement hδ T hmass hS
  exact ⟨⟨isParentFamily_nodes_fine 𝒰' hcnp.le_gridLen hinjFine, hcnp.parent⟩, hS',
    nonempty_of_sum_shade_pos T hS'⟩

/-! ### The three-pass assembly, restored in banded / ED-up-to-multiplicity form

What follows is **additive**: `Kakeya.ml1Boot.IsRepairThreePass` above is untouched, and so is
its consumer `Kakeya.ml1Boot.caseTwoRepairData_of_isRepairThreePass`.  The assembly below lands
in a **new** record, `Kakeya.ml1Boot.IsRepairThreePassThreaded`, because two clauses of the old
one are not deliverable by any route available today; the differences are declared on that
structure rather than smuggled in.

The three passes are `Kakeya.ml1Boot.exists_repairUniformDiscard_banded` (twice) and
`Kakeya.ml1Boot.exists_repairEssDistinct_edUpToMult` (once), plus one call of
`Kakeya.ml1Boot.exists_trimmedPass` between the second and third.  Both citations carry
hypotheses the bare blueprint statements did not:

* the (R2) discard needs the **input band**, because the bare (R2) is refuted
  (`Kakeya.ml1Boot.not_exists_repairUniform`);

* the (R1) pass used here reads body-level `Kakeya.IsEDUpToMult` multiplicity of the two node
  families at a fixed `Co : ℕ`, in place of the leaf-mediated `Kakeya.ml1Boot.HasBoundedOverlap`
  of `Kakeya.ml1Boot.exists_essDistinct_parentFamily`. **Those two hypotheses have no supplier
  in this development**, and fixed-multiplicity essential distinctness of node families is in
  general false — `Kakeya.ml1Boot.not_exists_essDistinct_parentFamily`'s axial pencil produces
  `≍ ρ ⁻¹` pairwise non-essentially-distinct parents. A supplier would have to give a
  `δ`-dependent multiplicity. -/

/-- **The conclusions of the restored three-pass assembly** — the output-shading form of
`Kakeya.ml1Boot.IsRepairThreePass`, minus its fibrewise clause.

A **new** structure; `Kakeya.ml1Boot.IsRepairThreePass` is untouched above.  Relative to it:

* the extra parameter `Y₃ : ι → ShadedTube δ E` is the third pass's own output shading, with the
  new containment field `shadeTube`, and `unif` reads at `Y₃`.  Uniformity at a *handed* shading
  is undeliverable — see `Kakeya.ml1Boot.card_shadeClass_le_card_shadeClass` — so this is the
  minimal threading that lets the clause be produced at all.  Every other field still reads at
  the input shading `T`, including `refineMid` and `refineLast`, whose mass lower bounds
  transfer from `Y₃` to `T` for free along `(Y₃ i).shade ⊆ (T i).shade`.

* there is **no** `fibreFrostman` field.  `Kakeya.ml1Boot.IsRepairThreePass.fibreFrostman`
  composes the three passes' fibrewise Frostman transports at `δ ^ (-3 ε')`; the banded (R2)
  pass does not deliver its own factor (see
  `Kakeya.ml1Boot.IsRepairUniformPassThreaded`), so the composite is unavailable and is not
  claimed.  It stays an hypothesis on any consumer of this record — which is why
  `Kakeya.ml1Boot.caseTwoRepairData_of_isRepairThreePass`, which reads
  `Kakeya.ml1Boot.IsRepairThreePass.fibreFrostman`, is deliberately *not* rewritten against this
  record. -/
structure IsRepairThreePassThreaded {ι κ : Type*} [DecidableEq κ] {δ τ θ : NNReal} (ε' : ℝ)
    (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ) (Tθ : κ → Tube θ E) (pθ : κ → κ)
    (tτ tθ : Finset κ) (s' s₂ s₀ : Finset ι) (t'τ t'θ : Finset κ)
    (Y₃ : ι → ShadedTube δ E) : Prop where
  /-- (a) The third pass's output shading `Y₃` shades the same tubes as `T`, with shades
  contained in `T`'s, on the retained leaf set `s₀`. -/
  shadeTube : ∀ i ∈ s₀, (Y₃ i).toTube = (T i).toTube ∧ (Y₃ i).shade ⊆ (T i).shade
  /-- (f) The fibrewise empty-or-share dichotomy at the retained fine node set, at the share
  `δ ^ (6 ε')`; produced by `Kakeya.ml1Boot.exists_trimmedPass`, run between move (R1) and the
  third pass. -/
  dichotomy : IsFibrewiseEmptyOrShare tτ tθ t'τ pθ ((δ : ENNReal) ^ (6 * ε'))
  /-- (a) The composite of the first two passes is a `δ ^ (2 ε')`-refinement. -/
  refineMid : ShadedBody.IsCRefinement s₂ (fun i => (T i).toShadedBody) s'
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩
  /-- (a) …and the third pass is a `δ ^ ε'`-refinement on top of it. -/
  refineLast : ShadedBody.IsCRefinement s₀ (fun i => (T i).toShadedBody) s₂
    (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ ε', by positivity⟩
  /-- (a) The third pass retains all but a `δ ^ (-ε')` share of the index set. -/
  card : (s₂.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s₀.card : ℝ)
  /-- (a) `s₂` is nonempty. -/
  nonemptyMid : s₂.Nonempty
  /-- (a) `s₀` is nonempty. -/
  nonemptyLast : s₀.Nonempty
  /-- (b) The final leaf family is uniform at `Kakeya.ml1Boot.uniformize.C 3`, **at the third
  pass's output shading `Y₃`**. -/
  unif : Nonempty (ShadedTube.ShadedUniformTubeSet s₀ Y₃ (Tube.ssfGridLen δ)
    (uniformize.C 3))
  /-- (c) `(t'τ, 𝕋_τ, pτ)` is a parent family for the retained leaves at scale `τ`. -/
  parentFine : IsParentFamily s₀ (fun i => (T i).toTube) t'τ Tτ pτ
  /-- (c) `(t'θ, 𝕋_θ, pθ)` is a parent family for the retained `τ`-nodes at scale `θ`. -/
  parentCoarse : IsParentFamily t'τ Tτ t'θ Tθ pθ
  /-- (d) The retained `τ`-nodes are pairwise essentially distinct. -/
  essDistinctFine : (t'τ : Set κ).Pairwise
    (fun k l => IsEssentiallyDistinct (Tτ k).carrier (Tτ l).carrier)
  /-- (d) The retained `θ`-nodes are pairwise essentially distinct. -/
  essDistinctCoarse : (t'θ : Set κ).Pairwise
    (fun k l => IsEssentiallyDistinct (Tθ k).carrier (Tθ l).carrier)

/-- **The restored three-pass assembly, banded and ED-up-to-multiplicity** (blueprint
`lem:ml1bootRepairThreePass`, restored form; harvested from `zzk` `5d5a41c21` and re-verified
here).

`(R2) → (R1) → (R2)` at accuracy `ε'/2` each, with `Kakeya.ml1Boot.exists_trimmedPass` between
the second and third, concluding `Kakeya.ml1Boot.IsRepairThreePassThreaded` at `ε'`.

Two hypothesis groups are additions to the blueprint statement and are **not** discharged
anywhere in this development: the input band `(lam₀)(hlam₀)(hband)`, which is available at the
Case (ii) call site from `Kakeya.ml1Boot.IsCaseTwoInput.band`, and the two node-family
`Kakeya.IsEDUpToMult... Co` hypotheses at a single fixed `Co : ℕ`, which are **not** available
there — see the section note above. -/
theorem exists_repairThreePass_edUpToMult_banded (hdim : Module.finrank ℝ E = 3) {ε' : ℝ}
    (hε' : 0 < ε') (Co : ℕ) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ τ θ : NNReal, δ ≤ τ → τ ≤ θ → θ ≤ 1 →
      ∀ {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {s' : Finset ι} {tτ tθ : Finset κ}
        (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ)
        (Tθ : κ → Tube θ E) (pθ : κ → κ) (mplus mminus : ENNReal),
        s'.Nonempty →
        0 < ∑ i ∈ s', volume (T i).shade →
        (∑ i ∈ s', volume (T i).shade) ≠ ⊤ →
        (∀ i ∈ s', (T i).carrier ⊆ Metric.closedBall 0 1) →
        (s' : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        IsParentFamily s' (fun i => (T i).toTube) tτ Tτ pτ →
        IsParentFamily tτ Tτ tθ Tθ pθ →
        ∀ (lam₀ : NNReal), 0 < lam₀ →
          (∀ i ∈ s', (lam₀ : ENNReal) * volume (T i).carrier ≤ volume (T i).shade ∧
            volume (T i).shade ≤ 2 * (lam₀ : ENNReal) * volume (T i).carrier) →
        IsEDUpToMult tτ (fun k => (Tτ k).carrier) Co →
        IsEDUpToMult tθ (fun k => (Tθ k).carrier) Co →
        (∀ k ∈ tτ, (∑ i ∈ fibre s' pτ k, volume (T i).shade) ≤ mplus) →
        mminus * (tτ.card : ENNReal) ≤ ∑ i ∈ s', volume (T i).shade →
        2 * ((δ : ENNReal) ^ (6 * ε') * mplus) ≤ (δ : ENNReal) ^ ε' * mminus →
        ∃ s₂ ⊆ s', ∃ s₀ ⊆ s₂, ∃ t'τ ⊆ tτ, ∃ t'θ ⊆ tθ,
          ∃ Y₃ : ι → ShadedTube δ E,
            IsRepairThreePassThreaded ε' T Tτ pτ Tθ pθ tτ tθ s' s₂ s₀ t'τ t'θ Y₃ := by
  filter_upwards [exists_repairUniformDiscard_banded hdim (show (0 : ℝ) < ε' / 2 by linarith),
      exists_repairEssDistinct_edUpToMult (E := E) (show (0 : ℝ) < ε' / 2 by linarith) Co,
      eventually_rpow_le_quarter hε', self_mem_nhdsWithin] with δ hD hEDev hQ hδpos
  intro τ θ hδτ hτθ hθ1 ι κ _ _ s' tτ tθ T Tτ pτ Tθ pθ mplus mminus
    hs'ne hMass hMassTop hBall hEd hFine hCoarse lam₀ hlam₀ hband hEDτ hEDθ hplus hminus hshare
  classical
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδpos
  have hhalf : 2 * ((δ : ENNReal) ^ ε') ≤ 1 := by
    rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
      show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num, ennreal_coe_nnreal_rpow hδR ε',
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [hQ.2])
  -- passes 1 and 2, at ε'/2
  rcases hD τ θ hδτ hτθ hθ1 (s := s') (tτ := tτ) (tθ := tθ) T Tτ pτ Tθ pθ
      hs'ne hMass hBall hEd hFine hCoarse lam₀ hlam₀ hband with
    ⟨s1, hs1, Y1, _, hshade1, ref1, hcard1, _, _⟩
  have hTube1 : ∀ i ∈ s1, (Y1 i).toTube = (T i).toTube := fun i hi => (hshade1 i hi).1
  have hFine1 : IsParentFamily s1 (fun i => (Y1 i).toTube) tτ Tτ pτ := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi; exact hFine.mapsTo i (hs1 hi)
    · exact hFine.injOn
    · intro i hi; simpa only [hTube1 i hi] using hFine.le_parent i (hs1 hi)
  rcases hEDev τ θ hδτ hτθ hθ1 (s := s1) (tτ := tτ) (tθ := tθ) Y1 Tτ pτ Tθ pθ
      (fun i => volume (T i).shade) hFine1 hCoarse hEDτ hEDθ with
    ⟨s2, hs2, t2τ, ht2τ, t2θ, ht2θ, p2⟩
  have hpowHalf2 : (δ : ENNReal) ^ ε' = (δ : ENNReal) ^ (ε' / 2) * (δ : ENNReal) ^ (ε' / 2) := by
    rw [← ENNReal.rpow_add_of_nonneg (x := (δ : ENNReal)) (ε' / 2) (ε' / 2)
        (le_of_lt (div_pos hε' (by norm_num))) (le_of_lt (div_pos hε' (by norm_num)))]
    exact congrArg (fun x : ℝ => (δ : ENNReal) ^ x) (by ring)
  set c1 : NNReal := ⟨(δ : ℝ) ^ (ε' / 2), by positivity⟩
  have hcoef1 : (c1 : ENNReal) = (δ : ENNReal) ^ (ε' / 2) := by
    rw [show (c1 : ENNReal) = ENNReal.ofReal (c1 : ℝ) from (ENNReal.ofReal_coe_nnreal).symm]
    change ENNReal.ofReal ((δ : ℝ) ^ (ε' / 2)) = (δ : ENNReal) ^ (ε' / 2)
    exact (ennreal_coe_nnreal_rpow hδR (ε' / 2)).symm
  have href1 : (δ : ENNReal) ^ (ε' / 2) * (∑ i ∈ s', volume (T i).shade) ≤
      ∑ i ∈ s1, volume (T i).shade := by
    have h := ref1.2
    rw [hcoef1] at h
    exact le_trans h (Finset.sum_le_sum (fun i hi => measure_mono (hshade1 i hi).2))
  have hret : (δ : ENNReal) ^ ε' * (∑ i ∈ s', volume (T i).shade) ≤
      ∑ i ∈ s2, volume (T i).shade := by
    calc
      (δ : ENNReal) ^ ε' * (∑ i ∈ s', volume (T i).shade)
          = ((δ : ENNReal) ^ (ε' / 2) * (δ : ENNReal) ^ (ε' / 2))
              * (∑ i ∈ s', volume (T i).shade) := by rw [hpowHalf2]
      _ = (δ : ENNReal) ^ (ε' / 2)
              * ((δ : ENNReal) ^ (ε' / 2) * (∑ i ∈ s', volume (T i).shade)) := by rw [mul_assoc]
      _ ≤ (δ : ENNReal) ^ (ε' / 2) * (∑ i ∈ s1, volume (T i).shade) := by
              exact mul_le_mul_of_nonneg_left href1 zero_le
      _ ≤ ∑ i ∈ s2, volume (T i).shade := p2.weight
  -- the post-selection trim between move (R1) and the third pass
  have hfin : (δ : ENNReal) ^ ε' * (∑ i ∈ s', volume (T i).shade) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (le_of_lt hε') (by simp : (δ : ENNReal) ≠ ⊤)) hMassTop
  have hp2FineT : IsParentFamily s2 (fun i => (T i).toTube) t2τ Tτ pτ := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi; exact p2.parentFine.mapsTo i hi
    · exact p2.parentFine.injOn
    · intro i hi; rw [← hTube1 i (hs2 hi)]; exact p2.parentFine.le_parent i hi
  obtain ⟨t'', ht''sub, s2'', hs2''sub, htPar, htED, htDich, htFib, hcost⟩ :=
    exists_trimmedPass (tτ := tτ) (tθ := tθ) (pθ := pθ) ht2τ hs2 hs1 hp2FineT
      p2.essDistinctFine hplus hminus hshare hret hfin
  have hs2''subS' : s2'' ⊆ s' := hs2''sub.trans (hs2.trans hs1)
  have hpowTwoEps : (δ : ENNReal) ^ (2 * ε') = (δ : ENNReal) ^ ε' * (δ : ENNReal) ^ ε' := by
    rw [← ENNReal.rpow_add_of_nonneg (x := (δ : ENNReal)) ε' ε' (le_of_lt hε') (le_of_lt hε')]
    exact congrArg (fun x : ℝ => (δ : ENNReal) ^ x) (by ring)
  have hmidMass : (δ : ENNReal) ^ (2 * ε') * (∑ i ∈ s', volume (T i).shade) ≤
      ∑ i ∈ s2'', volume (T i).shade := by
    calc
      (δ : ENNReal) ^ (2 * ε') * (∑ i ∈ s', volume (T i).shade)
          = (δ : ENNReal) ^ ε' * ((δ : ENNReal) ^ ε' * (∑ i ∈ s', volume (T i).shade)) := by
              rw [hpowTwoEps, mul_assoc]
      _ ≤ (δ : ENNReal) ^ ε' * (2 * ∑ i ∈ s2'', volume (T i).shade) := by
              exact mul_le_mul_of_nonneg_left hcost zero_le
      _ = (2 * (δ : ENNReal) ^ ε') * (∑ i ∈ s2'', volume (T i).shade) := by ring
      _ ≤ 1 * (∑ i ∈ s2'', volume (T i).shade) := by
              exact mul_le_mul_of_nonneg_right hhalf zero_le
      _ = ∑ i ∈ s2'', volume (T i).shade := by rw [one_mul]
  set cMid : NNReal := ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩
  have hcMid_coe : (cMid : ENNReal) = (δ : ENNReal) ^ (2 * ε') := by
    rw [show (cMid : ENNReal) = ENNReal.ofReal (cMid : ℝ) from (ENNReal.ofReal_coe_nnreal).symm]
    change ENNReal.ofReal ((δ : ℝ) ^ (2 * ε')) = (δ : ENNReal) ^ (2 * ε')
    exact (ennreal_coe_nnreal_rpow hδR (2 * ε')).symm
  have hmid : ShadedBody.IsCRefinement s2'' (fun i => (T i).toShadedBody) s'
      (fun i => (T i).toShadedBody) ⟨(δ : ℝ) ^ (2 * ε'), by positivity⟩ := by
    unfold ShadedBody.IsCRefinement ShadedBody.IsRefinement
    refine ⟨⟨hs2''subS', fun _ _ => ⟨rfl, subset_rfl⟩⟩, ?_⟩
    rw [hcMid_coe]
    exact hmidMass
  have h2pow : (0 : ENNReal) < (δ : ENNReal) ^ ε' := by
    rw [ennreal_coe_nnreal_rpow hδR ε']
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδR ε')
  have hpos : (0 : ENNReal) < (δ : ENNReal) ^ ε' * (∑ i ∈ s', volume (T i).shade) :=
    ENNReal.mul_pos (ne_of_gt h2pow) (ne_of_gt hMass)
  have h2ne : s2''.Nonempty := nonempty_of_weight_pos hcost hpos
  have hpos3 : 0 < ∑ i ∈ s2'', volume (T i).shade :=
    (ENNReal.mul_pos_iff.mp (lt_of_lt_of_le hpos hcost)).2
  have hEd2'' : (s2'' : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) :=
    Set.Pairwise.mono (Finset.coe_subset.mpr hs2''subS') hEd
  have hcoarse'' : IsParentFamily t'' Tτ t2θ Tθ pθ :=
    IsParentFamily.mono p2.parentCoarse ht''sub (by intro i hi; exact hi)
      (fun k hk => p2.parentCoarse.mapsTo k (ht''sub hk))
  rcases hD τ θ hδτ hτθ hθ1 (s := s2'') (tτ := t'') (tθ := t2θ) T Tτ pτ Tθ pθ
      h2ne hpos3 (fun i hi => hBall i (hs1 (hs2 (hs2''sub hi)))) hEd2'' htPar hcoarse''
      lam₀ hlam₀ (fun i hi => hband i (hs2''subS' hi)) with
    ⟨s0, hs0, Y3, hs0ne, hshade3, ref3, hcard3, hunif3, hInh3⟩
  let cLast : NNReal := ⟨(δ : ℝ) ^ ε', by positivity⟩
  let cHalf : NNReal := ⟨(δ : ℝ) ^ (ε' / 2), by positivity⟩
  have hcLast : cLast ≤ cHalf := by
    exact_mod_cast (Real.rpow_le_rpow_of_exponent_ge hδR hQ.1 (by linarith))
  have hcCard : (δ : ℝ) ^ (-(ε' / 2)) ≤ (δ : ℝ) ^ (-ε') := by
    exact Real.rpow_le_rpow_of_exponent_ge hδR hQ.1 (by linarith)
  have hcardF : (s2''.card : ℝ) ≤ (δ : ℝ) ^ (-ε') * (s0.card : ℝ) := by
    exact le_trans hcard3 (mul_le_mul_of_nonneg_right hcCard (by positivity))
  have hLastRef : ShadedBody.IsRefinement s0 (fun i => (T i).toShadedBody) s2''
      (fun i => (T i).toShadedBody) := by
    unfold ShadedBody.IsRefinement
    exact ⟨ref3.1.1, fun _ _ => ⟨rfl, subset_rfl⟩⟩
  have hLastMass : (cLast : ENNReal) * (∑ i ∈ s2'', volume (T i).shade) ≤
      ∑ i ∈ s0, volume (T i).shade := by
    calc
      (cLast : ENNReal) * (∑ i ∈ s2'', volume (T i).shade)
          ≤ (cHalf : ENNReal) * (∑ i ∈ s2'', volume (T i).shade) := by
              exact mul_le_mul' (ENNReal.coe_le_coe.mpr hcLast) le_rfl
      _ ≤ ∑ i ∈ s0, volume (Y3 i).shade := ref3.2
      _ ≤ ∑ i ∈ s0, volume (T i).shade := by
              exact Finset.sum_le_sum (fun i hi => measure_mono (hshade3 i hi).2)
  refine ⟨s2'', hs2''subS', s0, hs0, t'', ht''sub.trans ht2τ, t2θ, ht2θ, Y3, ?_⟩
  exact
    { shadeTube := hshade3
      dichotomy := htDich
      refineMid := hmid
      refineLast := ⟨hLastRef, hLastMass⟩
      card := hcardF
      nonemptyMid := h2ne
      nonemptyLast := hs0ne
      unif := hunif3
      parentFine := IsParentFamily.mono htPar hs0 (by intro i hi; exact hi)
        (fun i hi => htPar.mapsTo i (hs0 hi))
      parentCoarse := hcoarse''
      essDistinctFine := htED
      essDistinctCoarse := p2.essDistinctCoarse }


end ml1Boot

end Kakeya
