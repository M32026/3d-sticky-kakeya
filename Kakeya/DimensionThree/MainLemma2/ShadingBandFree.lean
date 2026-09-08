/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.AScaleResidues

/-!
# The density band of Configuration `hyp:ml2setup` needs no pigeonhole

The recorded second blocker of the setup lemma is that the per-tube density band of
Configuration `hyp:ml2setup` — the fields `Kakeya.VeryNotSticky.lam`,
`Kakeya.VeryNotSticky.Cd`, `Kakeya.VeryNotSticky.lam_ge`, `Kakeya.VeryNotSticky.shading_lb`,
`Kakeya.VeryNotSticky.shading_ub` — is produced by a pigeonhole on the values `|Y(T)|`, that
the pigeonhole **moves the index set**, and that moving the index set destroys the two lower
brackets of GWZ Definition 2.2 (`le_card_shadeClass`, `le_branchingN`) and hence the field
`Kakeya.VeryNotSticky.uniform`.  Banding after uniformizing breaks `uniform`; banding before
breaks `shading_lb`, because every shaded uniformizer in the tree only *shrinks* shadings.

**This file removes the blocker by removing the band.**  Three tripwires, each an `rfl`
between a refactored declaration and the tree's own, establish mechanically that the per-tube
lower bracket is consumed *only* through the single aggregate inequality
`lam / Cd ≤ λ(𝕋, Y)`:

* `ShadedBody.le_fullness_of_le_fullness_of_fullness_ge` and
  `ShadedBody.fullness_ge_of_forall_density` split
  `ShadedBody.le_fullness_of_le_fullness_of_forall_density` — the only place the per-body
  hypothesis is touched — into "per-body ⇒ aggregate" and "aggregate ⇒ conclusion"; the tripwire
  `ShadedBody.le_fullness_of_le_fullness_of_forall_density_refactored` is `rfl`-equal to it.
* `ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam_of_fullness` is GWZ Lemma
  5.11's density-parameter form with the per-body hypothesis replaced by the aggregate one.  It
  needs neither `Cd ≠ 0` nor the nondegeneracy `hs0`, both of which existed only to run the
  per-body step.  Its tripwire is again `rfl`-equal to the tree's `…_lam`.
* `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_subfamily_of_fullness` is the
  configuration-level consumer — the *only* consumer of `shading_lb` in the development that is
  not itself re-supplying the field — proved from the aggregate datum, with the tripwire
  `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_subfamily_refactored` `rfl`-equal to the
  tree's.

And `Kakeya.VeryNotSticky.exists_bandData_of_fullness_two_eta` closes the loop: from
`δ^{2η} ≤ λ(𝕋, Y)` alone — the *repaired* `Kakeya.VeryNotSticky.fullness_ge` — the choice

  `lam := δ^η`,  `Cd := δ^{-η}`

delivers `1 ≤ Cd`, `Cd δ^{2η} ≤ lam` (with equality), the aggregate `lam / Cd ≤ λ(𝕋, Y)`, and
`shading_ub`, the last **for free**: at that normalisation `Cd · lam = 1`, so `shading_ub` is
the tautology `|Y(T)| ≤ |T|`.  The scale-invariant combination `Cd⁻¹ lam` is `δ^{2η}`, the same
value a dyadic band at `Cd = 2` delivers, and the consumers read only that combination.

**Consequence, which is a structure-field question and is therefore reported, not applied.**
Weakening `Kakeya.VeryNotSticky.shading_lb` from its per-tube form to
`(Cd : ℝ≥0∞)⁻¹ * lam ≤ λ(𝕋, Y)` costs the development nothing — the three tripwires prove that
every consumer still runs — and after that weakening the whole band group is deliverable from
the repaired `fullness_ge` with **no pigeonhole, no index selection, and no interaction with
`uniform` whatsoever**.  `Kakeya.VeryNotSticky.fullness_ge_of_shading_lb` records that the
weakening is a genuine weakening: the present field implies the aggregate one.

**Re-measured at the tip, and the number is five, not one.**  `AScaleResidues.lean` has grown by
`+3117` lines since the first measurement, and `Kakeya.VeryNotSticky.shading_lb` now has five
consumers besides the two sites that merely re-supply the field
(`Kakeya.VeryNotSticky.rescaleDensity`, `Kakeya.VeryNotSticky.deleteShade`).  Each is classified
here by a `rfl` tripwire against the tree's own declaration:

| consumer | verdict |
|---|---|
| `exists_coarseShadedFamilyAtGrid_subfamily` | aggregate suffices |
| `lam_le_Cd` | aggregate suffices — `fullness ≤ 1` |
| `le_volume_innerShadedUnion` | aggregate suffices — the largest shading beats the average |
| `exists_coarseShadedFamilyAtGrid_inducedFullness` | **needs one dense tube per active node** |
| `rpow_two_eta_mul_volume_carrier_le_volume_shade` | **irreducibly per-tube: it *concludes* one** |

The fourth is localised exactly, and without touching the shared Section-5 file:
`ShadedBody.exists_rhoTubesSection9_fullFamily` uses its per-tube `hlam` only at the witness
`hactive` supplies, one per coarse node, so the two hypotheses fuse into
`ShadedBody.exists_rhoTubesSection9_fullFamily_of_representatives`, from which the shared lemma
is re-derived by `rfl`.  That fused demand is **not** implied by an aggregate: a family whose
whole shading sits in the class of one node has `Cd⁻¹ lam ≤ λ(𝕋, Y)` and outer fullness at most
`1 / |𝕋_ρ|`.

**So the aggregate weakening is not free at the tip, and this file does not apply it.**  It is a
structure-field change, and the last section of the file is what removes its price.

## `uniform` does not have to be strengthened

The residual after the classification above is: *can the configuration force every **active**
node — a node with nonempty class — to contain a tube of density `≥ Cd⁻¹ lam`?*

**It cannot, and it does not need to.**  It cannot, because Definition 2.2 does not see a dead
node: `Kakeya.VeryNotSticky.exists_shadedUniformTubeSet_of_axes_injOn` builds the predicate for an
*arbitrary* shading, so a member with empty shading is not excluded by any reading of
`Kakeya.VeryNotSticky.uniform`, at any constant; and a family whose whole shading sits in one
node's class has outer fullness `≤ 1 / |𝕋_ρ|` while its aggregate fullness is whatever one likes.
The gap between "nonempty class" and "nonempty shaded fibre" has to be paid for, not argued away.

It does not need to, because the price is affordable out of data the configuration already has:

* `ShadedBody.sum_carrier_dense_ge` — Markov in carrier mass: with aggregate density `a` and the
  per-tube **upper** bound `u` of `Kakeya.VeryNotSticky.shading_ub` (which no consumer reads and
  which holds by construction at `lam := max density`), the members of density `≥ a/2` carry an
  `a/(2u)` fraction of the carrier mass;
* `ShadedBody.card_mul_card_le_of_class_comparable` — the two-sided branching bracket of
  `Tube.UniformTubeSet`, and *only* that bracket, turns a fraction of members into a fraction of
  nodes, at `B = C₀²` (`Kakeya.VeryNotSticky.card_coverClass_le_of_uniform`);
* `ShadedBody.le_fullness_inducedCoarseShading_of_aggregate` and
  `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_inducedFullness_of_aggregate` — the dead
  nodes contribute nothing and are carried in the denominator, so
  `exists_coarseShadedFamilyAtGrid_inducedFullness` survives at the **full** node family with the
  extra factor `Cd³ C₀²`, which is `δ^{-O(η)}` and not purely dimensional.

And row 7 is answered in the same coin: `ShadedBody.card_dense_ge_of_aggregate` and
`Kakeya.VeryNotSticky.card_dense_mul_delta_ge_of_aggregate` replace *"every tube is
`δ^{2η}`-full"* by *"at least `≍ δ^{-1}/Cd²` tubes are"*, which is quantitative, still forces a
count, and therefore still pins `Kakeya.VeryNotSticky.lam_ge`.

**What is still owed before the field may be weakened** is therefore only the bookkeeping:
restating `exists_coarseShadedFamilyAtGrid_inducedFullness` at the larger constant, and
restating the two refutation devices at the count.  Both are statement changes, so they are
reported and not taken here.
-/

@[expose] public section

open MeasureTheory Metric Set Convexity Kakeya
open scoped NNReal ENNReal

namespace ShadedBody

section BandFree

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*}

omit [Nontrivial E] in
/-- **The aggregate half of `ShadedBody.le_fullness_of_le_fullness_of_forall_density`.** -/
theorem le_fullness_of_le_fullness_of_fullness_ge
    {s : Finset ι} {V : ι → ShadedBody E} {t : Finset κ} {W : κ → ShadedBody E}
    {lam Cd C : NNReal}
    (hlam : lam / Cd ≤ fullness s V)
    (hfull : C⁻¹ * fullness s V ≤ fullness t W) :
    (Cd * C)⁻¹ * lam ≤ fullness t W := by
  calc
    (Cd * C)⁻¹ * lam = C⁻¹ * (lam / Cd) := by
      rw [mul_inv, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm Cd⁻¹]
    _ ≤ C⁻¹ * fullness s V := by gcongr
    _ ≤ fullness t W := hfull

omit [Nontrivial E] in
/-- **The per-tube density hypothesis enters only through its aggregate consequence.** -/
theorem fullness_ge_of_forall_density
    {s : Finset ι} {V : ι → ShadedBody E} {lam Cd : NNReal} (hCd : Cd ≠ 0)
    (hs0 : ∑ i ∈ s, volume (V i).carrier ≠ 0)
    (hlam_lb : ∀ i ∈ s, (Cd : ENNReal)⁻¹ * ((lam : ENNReal) * volume (V i).carrier)
      ≤ volume (V i).shade) :
    lam / Cd ≤ fullness s V := by
  have hcd0 : (Cd : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hCd
  have hcdt : (Cd : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsum_ne_top : ∑ i ∈ s, volume (V i).carrier ≠ ⊤ := by
    intro h
    rcases ENNReal.sum_eq_top.1 h with ⟨i, _, hf⟩
    exact (V i).isCompact.measure_ne_top hf
  have hlam' : ∀ i ∈ s, (lam : ENNReal) * volume (V i).carrier ≤
      (Cd : ENNReal) * volume (V i).shade := by
    intro i hi
    calc
      (lam : ENNReal) * volume (V i).carrier
          = (Cd : ENNReal) * ((Cd : ENNReal)⁻¹ * ((lam : ENNReal) * volume (V i).carrier)) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel hcd0 hcdt, one_mul]
      _ ≤ (Cd : ENNReal) * volume (V i).shade := by
        gcongr
        exact hlam_lb i hi
  have hstep : (lam : ENNReal) / (Cd : ENNReal) ≤ (fullness s V : ENNReal) :=
    le_fullness_of_forall_mul_volume_carrier_le (t := s) (W := V)
      (a := (lam : ENNReal)) (b := (Cd : ENNReal)) hcd0 hcdt hs0 hsum_ne_top hlam'
  apply ENNReal.coe_le_coe.1
  rw [ENNReal.coe_div hCd]
  exact hstep

omit [Nontrivial E] in
/-- **Tripwire: the library lemma factors through the aggregate form.** -/
theorem le_fullness_of_le_fullness_of_forall_density_refactored
    {s : Finset ι} {V : ι → ShadedBody E} {t : Finset κ} {W : κ → ShadedBody E}
    {lam Cd C : NNReal} (hCd : Cd ≠ 0)
    (hs0 : ∑ i ∈ s, volume (V i).carrier ≠ 0)
    (hlam_lb : ∀ i ∈ s, (Cd : ENNReal)⁻¹ * ((lam : ENNReal) * volume (V i).carrier)
      ≤ volume (V i).shade)
    (hfull : C⁻¹ * fullness s V ≤ fullness t W) :
    (Cd * C)⁻¹ * lam ≤ fullness t W :=
  le_fullness_of_le_fullness_of_fullness_ge
    (fullness_ge_of_forall_density hCd hs0 hlam_lb) hfull

example : @le_fullness_of_le_fullness_of_forall_density_refactored
    = @ShadedBody.le_fullness_of_le_fullness_of_forall_density := rfl

open Classical in
/-- **GWZ Lemma 5.11, density-parameter form, with the *aggregate* density hypothesis.**

Identical to `ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam` except that the
per-body hypothesis `hlam_lb` is replaced by the single aggregate inequality
`lam / Cd ≤ fullness F.innerSet F.innerBody` that it is used to derive — and, as a consequence,
neither `hCd : Cd ≠ 0` nor the nondegeneracy `hs0` is needed. -/
theorem shadingMultiplicityEstimateForRhoTubesUndilated_lam_of_fullness
    {δ ρ Cd lam : ℝ≥0} (hδ : 0 < δ) (hρ : ρ ∈ Set.Icc δ 1)
    (F : FactorFamily E ι κ)
    (T : ι → ShadedTube δ E) (Tρ : κ → Tube ρ E)
    (hinner : ∀ i ∈ F.innerSet, F.innerBody i = (T i).toShadedBody)
    (houter : ∀ j ∈ F.outerSet, F.outerBody j = (Tρ j).toConvexSpaceBody)
    (hball : ∀ i ∈ F.innerSet, (F.innerBody i).carrier ⊆ Metric.closedBall 0 1)
    (hagg : lam / Cd ≤ fullness F.innerSet F.innerBody) :
    ∃ G : ShadedFactorFamily E ι κ,
      G.outerSet ⊆ F.outerSet ∧
      G.innerSet = {i ∈ F.innerSet | F.parent i ∈ G.outerSet} ∧
      G.parent = F.parent ∧
      (∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody = F.outerBody j) ∧
      (∀ i ∈ F.innerSet,
        (G.innerBody i).toConvexSpaceBody = (F.innerBody i).toConvexSpaceBody) ∧
      (0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade → G.outerSet.Nonempty) ∧
      (Cd * shadingMultiplicityEstimateForRhoTubesDilate.C
            (Module.finrank ℝ E) F.innerSet.card δ 1)⁻¹ * lam
        ≤ fullness G.outerSet G.outerBody ∧
      IsCRefinement G.innerSet G.innerBody F.innerSet F.innerBody
        (shadingMultiplicityEstimateForRhoTubesDilate.C
          (Module.finrank ℝ E) F.innerSet.card δ 1)⁻¹ ∧
      (∀ j ∈ G.outerSet,
        multiplicity F.innerSet F.innerBody
          ≤ (shadingMultiplicityEstimateForRhoTubesDilate.C
                (Module.finrank ℝ E) F.innerSet.card δ 1 : ENNReal)
            * multiplicity G.outerSet G.outerBody
            * multiplicity (G.fiber j) G.innerBody) ∧
      (∀ i ∈ G.innerSet,
        (G.innerBody i).shade ⊆ (G.outerBody (F.parent i)).shade) ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (shadingMultiplicityEstimateForRhoTubesDilate.C
              (Module.finrank ℝ E) F.innerSet.card δ 1 : ENNReal)⁻¹
          * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
          * (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ Metric.ball x (ρ : ℝ))
              / volume (Metric.ball x (ρ : ℝ)))
          ≤ volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade))
      -- GWZ Definition 5.7, exposed: the outer shading contains the `2ρ`-neighbourhood, inside the
      -- outer carrier, of every selected inner shade of its fibre
      ∧ (∀ j ∈ G.outerSet, ∀ i ∈ G.innerSet, G.parent i = j →
          (G.outerBody j).carrier ∩ Metric.cthickening (2 * (ρ : ℝ)) (G.innerBody i).shade
            ⊆ (G.outerBody j).shade) := by
  obtain ⟨G, h1, h2, h3, h4, h5, h6, hfull, h8, h9, h10, h11, h12⟩ :=
    shadingMultiplicityEstimateForRhoTubesUndilated hδ hρ F T Tρ hinner houter hball
  exact ⟨G, h1, h2, h3, h4, h5, h6,
    le_fullness_of_le_fullness_of_fullness_ge hagg hfull, h8, h9, h10, h11, h12⟩

open Classical in
/-- **Tripwire: the library `_lam` estimate factors through the aggregate one.** -/
theorem shadingMultiplicityEstimateForRhoTubesUndilated_lam_refactored
    {δ ρ Cd lam : ℝ≥0} (hδ : 0 < δ) (hρ : ρ ∈ Set.Icc δ 1) (hCd : Cd ≠ 0)
    (F : FactorFamily E ι κ)
    (T : ι → ShadedTube δ E) (Tρ : κ → Tube ρ E)
    (hinner : ∀ i ∈ F.innerSet, F.innerBody i = (T i).toShadedBody)
    (houter : ∀ j ∈ F.outerSet, F.outerBody j = (Tρ j).toConvexSpaceBody)
    (hball : ∀ i ∈ F.innerSet, (F.innerBody i).carrier ⊆ Metric.closedBall 0 1)
    (hs0 : ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier ≠ 0)
    (hlam_lb : ∀ i ∈ F.innerSet,
      (Cd : ENNReal)⁻¹ * ((lam : ENNReal) * volume (F.innerBody i).carrier)
        ≤ volume (F.innerBody i).shade) :
    ∃ G : ShadedFactorFamily E ι κ,
      G.outerSet ⊆ F.outerSet ∧
      G.innerSet = {i ∈ F.innerSet | F.parent i ∈ G.outerSet} ∧
      G.parent = F.parent ∧
      (∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody = F.outerBody j) ∧
      (∀ i ∈ F.innerSet,
        (G.innerBody i).toConvexSpaceBody = (F.innerBody i).toConvexSpaceBody) ∧
      (0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade → G.outerSet.Nonempty) ∧
      (Cd * shadingMultiplicityEstimateForRhoTubesDilate.C
            (Module.finrank ℝ E) F.innerSet.card δ 1)⁻¹ * lam
        ≤ fullness G.outerSet G.outerBody ∧
      IsCRefinement G.innerSet G.innerBody F.innerSet F.innerBody
        (shadingMultiplicityEstimateForRhoTubesDilate.C
          (Module.finrank ℝ E) F.innerSet.card δ 1)⁻¹ ∧
      (∀ j ∈ G.outerSet,
        multiplicity F.innerSet F.innerBody
          ≤ (shadingMultiplicityEstimateForRhoTubesDilate.C
                (Module.finrank ℝ E) F.innerSet.card δ 1 : ENNReal)
            * multiplicity G.outerSet G.outerBody
            * multiplicity (G.fiber j) G.innerBody) ∧
      (∀ i ∈ G.innerSet,
        (G.innerBody i).shade ⊆ (G.outerBody (F.parent i)).shade) ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (shadingMultiplicityEstimateForRhoTubesDilate.C
              (Module.finrank ℝ E) F.innerSet.card δ 1 : ENNReal)⁻¹
          * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
          * (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ Metric.ball x (ρ : ℝ))
              / volume (Metric.ball x (ρ : ℝ)))
          ≤ volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade))
      -- GWZ Definition 5.7, exposed: the outer shading contains the `2ρ`-neighbourhood, inside the
      -- outer carrier, of every selected inner shade of its fibre
      ∧ (∀ j ∈ G.outerSet, ∀ i ∈ G.innerSet, G.parent i = j →
          (G.outerBody j).carrier ∩ Metric.cthickening (2 * (ρ : ℝ)) (G.innerBody i).shade
            ⊆ (G.outerBody j).shade) := by
  exact shadingMultiplicityEstimateForRhoTubesUndilated_lam_of_fullness (Cd := Cd) (lam := lam)
    hδ hρ F T Tρ hinner houter hball (fullness_ge_of_forall_density hCd hs0 hlam_lb)

example : @shadingMultiplicityEstimateForRhoTubesUndilated_lam_refactored
    = @ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam := rfl

end BandFree

section Representatives

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*}

omit [Nontrivial E] in
/-- Fullness is monotone in the shading when the carriers agree. -/
theorem fullness_mono_shade {t : Finset κ} {V V' : κ → ShadedBody E}
    (hcar : ∀ j ∈ t, volume (V j).carrier = volume (V' j).carrier)
    (hsh : ∀ j ∈ t, volume (V j).shade ≤ volume (V' j).shade) :
    fullness t V ≤ fullness t V' := by
  rw [← ENNReal.coe_le_coe, coe_fullness, coe_fullness]
  refine ENNReal.div_le_div (Finset.sum_le_sum hsh) (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun j hj => (hcar j hj).symm)

omit [Nontrivial E] in
/-- The induced coarse shading is monotone in the fine index set. -/
theorem inducedCoarseShading_shade_mono {δ ρ : ℝ≥0} {s s' : Finset ι} (hss : s' ⊆ s)
    (T : ι → ShadedTube δ E) (p : ι → κ) (W : κ → Tube ρ E) (j : κ) :
    (inducedCoarseShading s' T p W j).shade ⊆ (inducedCoarseShading s T p W j).shade := by
  classical
  refine Set.inter_subset_inter_right _ (Metric.cthickening_subset_of_subset _ ?_)
  refine Set.biUnion_subset_biUnion_left ?_
  intro i hi
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hi ⊢
  exact ⟨hss hi.1, hi.2⟩

open Classical in
/-- **GWZ Lemma 5.11's fullness clause needs only ONE dense fine tube per coarse node.**

`ShadedBody.exists_rhoTubesSection9_fullFamily` asks for the density bound at *every* member of
`s`.  Its proof uses it only at the witness that `hactive` supplies — one per coarse node — so
the two hypotheses fuse into the strictly weaker `hrep` below: *every coarse node has, in its
fibre, at least one fine tube of density at least `Cd⁻¹ lam`*.  The conclusion is unchanged, and
`ShadedBody.exists_rhoTubesSection9_fullFamily_refactored` re-derives the shared lemma from this
one, so **no edit to `Kakeya/Factoring/RhoTubesSection9.lean` is needed** to obtain the
weakening.

Stated on `ShadedBody.inducedCoarseShading` rather than as an `∃ G`, because the shared lemma's
`∃ G` pins only `(G.outerBody j).toConvexSpaceBody` and so cannot be transported;
`ShadedBody.exists_rhoTubesSection9_fullFamily_of_representatives` packages it. -/
theorem le_fullness_inducedCoarseShading_of_representatives
    {δ ρ Cd lam : ℝ≥0} (hδ : 0 < δ) (hρ : ρ ∈ Set.Icc δ 1) (hCd : Cd ≠ 0)
    {s : Finset ι} {t : Finset κ}
    (T : ι → ShadedTube δ E) (W : κ → Tube ρ E) (p : ι → κ)
    (hmaps : ∀ i ∈ s, p i ∈ t)
    (hle : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ (W (p i)).toConvexSpaceBody)
    (ht : t.Nonempty)
    (hrep : ∀ j ∈ t, ∃ i ∈ s, p i = j ∧
      (Cd : ENNReal)⁻¹ * ((lam : ENNReal) * volume (T i).carrier) ≤ volume (T i).shade) :
    (Cd * rhoTubesInducedFullnessLoss (Module.finrank ℝ E))⁻¹ * lam
      ≤ fullness t (inducedCoarseShading s T p W) := by
  classical
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ hρ.1
  have hcar : ∀ i ∈ s, ((T i).toConvexSpaceBody : Set E) ⊆ ((W (p i)).toConvexSpaceBody : Set E) :=
    fun i hi => SetLike.coe_subset_coe.mpr (hle i hi)
  have hsubU : ∀ i ∈ s, (T i).shade ⊆
      Metric.cthickening (2 * (ρ : ℝ))
        (⋃ i' ∈ ({i' ∈ s | p i' = p i} : Finset ι), (T i').shade) := by
    intro i hi
    refine subset_trans ?_ (Metric.self_subset_cthickening _)
    exact Set.subset_biUnion_of_mem (u := fun i' => (T i').shade)
      (Finset.mem_filter.mpr ⟨hi, rfl⟩)
  -- the representative of each coarse body carries the density into the induced shading
  have key : ∀ j ∈ t,
      ((Cd : ENNReal)⁻¹ * (lam : ENNReal)) * volume (W j).carrier
        ≤ (rhoTubesInducedFullnessLoss (Module.finrank ℝ E) : ENNReal) *
            volume (inducedCoarseShading s T p W j).shade := by
    intro j hj
    obtain ⟨i, hi, hpi, hdense⟩ := hrep j hj
    subst hpi
    have hTcar0 : volume (T i).carrier ≠ 0 := by
      have h := Tube.le_volume (T i).toTube
      have hc : (0 : ENNReal) <
          ((Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0) : ENNReal) *
            (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
        ENNReal.mul_pos (ne_of_gt (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos _)))
          (ne_of_gt (ENNReal.pow_pos (ENNReal.coe_pos.mpr hδ) _))
      exact ne_of_gt (lt_of_lt_of_le hc (by simpa using h))
    have hTcarTop : volume (T i).carrier ≠ ⊤ := (T i).isCompact'.measure_ne_top
    have hdens : (Cd : ENNReal)⁻¹ * (lam : ENNReal)
        ≤ volume (T i).shade / volume (T i).carrier := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hTcar0) (Or.inl hTcarTop), mul_assoc]
      exact hdense
    have hgeo := Kakeya.Tube.volume_dilate_inter_cthickening_ge (E := E) hδ hρ.1 hρ.2
      (c := (1 : ℝ)) le_rfl (T i).toTube (W (p i))
      (by rw [Kakeya.Tube.dilate_one]; exact hcar i hi) (T i).shade_subset
    rw [Kakeya.Tube.dilate_one] at hgeo
    simp only [one_pow, ENNReal.ofReal_one, mul_one] at hgeo
    have hmono : volume ((W (p i)).carrier ∩ Metric.cthickening (2 * (ρ : ℝ)) (T i).shade)
        ≤ volume (inducedCoarseShading s T p W (p i)).shade :=
      measure_mono (Set.inter_subset_inter_right _
        (Metric.cthickening_subset_of_subset _
          (Set.subset_biUnion_of_mem (u := fun i' => (T i').shade)
            (Finset.mem_filter.mpr ⟨hi, rfl⟩))))
    calc
      ((Cd : ENNReal)⁻¹ * (lam : ENNReal)) * volume (W (p i)).carrier
          ≤ (volume (T i).shade / volume (T i).carrier) * volume (W (p i)).carrier :=
            mul_le_mul' hdens le_rfl
      _ ≤ (Kakeya.Tube.dilateFullness.C (Module.finrank ℝ E) : ENNReal) *
            volume ((W (p i)).carrier ∩ Metric.cthickening (2 * (ρ : ℝ)) (T i).shade) := hgeo
      _ ≤ (rhoTubesInducedFullnessLoss (Module.finrank ℝ E) : ENNReal) *
            volume (inducedCoarseShading s T p W (p i)).shade :=
            mul_le_mul' (ENNReal.coe_le_coe.mpr (le_max_right _ _)) hmono
  obtain ⟨j₀, hj₀⟩ := ht
  have hWpos : ∀ j : κ, 0 < volume (W j).carrier := by
    intro j
    have h := Tube.le_volume (W j)
    have hc : (0 : ENNReal) <
        ((Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0) : ENNReal) *
          (ρ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
      ENNReal.mul_pos (ne_of_gt (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos _)))
        (ne_of_gt (ENNReal.pow_pos (ENNReal.coe_pos.mpr hρ0) _))
    exact lt_of_lt_of_le hc (by simpa using h)
  have ht0 : ∑ j ∈ t, volume (inducedCoarseShading s T p W j).carrier ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le (hWpos j₀) ?_)
    exact Finset.single_le_sum
      (f := fun j => volume (inducedCoarseShading s T p W j).carrier)
      (fun _ _ => by positivity) hj₀
  have httop : ∑ j ∈ t, volume (inducedCoarseShading s T p W j).carrier ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun j _ => (W j).isCompact'.measure_ne_top
  have hfull := le_fullness_of_forall_mul_volume_carrier_le
    (t := t) (W := inducedCoarseShading s T p W)
    (a := (Cd : ENNReal)⁻¹ * (lam : ENNReal))
    (b := (rhoTubesInducedFullnessLoss (Module.finrank ℝ E) : ENNReal))
    (ENNReal.coe_ne_zero.mpr (rhoTubesInducedFullnessLoss_ne_zero _))
    ENNReal.coe_ne_top ht0 httop key
  have hne : Cd * rhoTubesInducedFullnessLoss (Module.finrank ℝ E) ≠ 0 :=
    mul_ne_zero hCd (rhoTubesInducedFullnessLoss_ne_zero _)
  show (Cd * rhoTubesInducedFullnessLoss (Module.finrank ℝ E))⁻¹ * lam
      ≤ fullness t (inducedCoarseShading s T p W)
  rw [← ENNReal.coe_le_coe]
  refine le_trans (le_of_eq ?_) hfull
  rw [ENNReal.coe_mul, ENNReal.coe_inv hne, ENNReal.coe_mul,
    ENNReal.mul_inv (Or.inl (ENNReal.coe_ne_zero.mpr hCd)) (Or.inl ENNReal.coe_ne_top),
    ENNReal.div_eq_inv_mul]
  ring


open Classical in
/-- The `∃ G` packaging of `ShadedBody.le_fullness_inducedCoarseShading_of_representatives`. -/
theorem exists_rhoTubesSection9_fullFamily_of_representatives
    {δ ρ Cd lam : ℝ≥0} (hδ : 0 < δ) (hρ : ρ ∈ Set.Icc δ 1) (hCd : Cd ≠ 0)
    {s : Finset ι} {t : Finset κ}
    (T : ι → ShadedTube δ E) (W : κ → Tube ρ E) (p : ι → κ)
    (hmaps : ∀ i ∈ s, p i ∈ t)
    (hle : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ (W (p i)).toConvexSpaceBody)
    (ht : t.Nonempty)
    (hrep : ∀ j ∈ t, ∃ i ∈ s, p i = j ∧
      (Cd : ENNReal)⁻¹ * ((lam : ENNReal) * volume (T i).carrier) ≤ volume (T i).shade) :
    ∃ G : ShadedFactorFamily E ι κ,
      G.innerSet = s ∧
      (∀ i, G.innerBody i = (T i).toShadedBody) ∧
      G.outerSet = t ∧
      G.parent = p ∧
      (∀ j, (G.outerBody j).toConvexSpaceBody = (W j).toConvexSpaceBody) ∧
      (Cd * rhoTubesInducedFullnessLoss (Module.finrank ℝ E))⁻¹ * lam
        ≤ fullness G.outerSet G.outerBody := by
  classical
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ hρ.1
  have hcar : ∀ i ∈ s, ((T i).toConvexSpaceBody : Set E) ⊆ ((W (p i)).toConvexSpaceBody : Set E) :=
    fun i hi => SetLike.coe_subset_coe.mpr (hle i hi)
  have hsubU : ∀ i ∈ s, (T i).shade ⊆
      Metric.cthickening (2 * (ρ : ℝ))
        (⋃ i' ∈ ({i' ∈ s | p i' = p i} : Finset ι), (T i').shade) := by
    intro i hi
    refine subset_trans ?_ (Metric.self_subset_cthickening _)
    exact Set.subset_biUnion_of_mem (u := fun i' => (T i').shade)
      (Finset.mem_filter.mpr ⟨hi, rfl⟩)
  exact ⟨{ innerSet := s
           innerBody := fun i => (T i).toShadedBody
           outerSet := t
           outerBody := inducedCoarseShading s T p W
           parent := p
           parent_mem := hmaps
           inner_le_parent := hle
           shade_subset_parent := by
             intro i hi
             exact Set.subset_inter (subset_trans (T i).shade_subset (hcar i hi))
               (hsubU i hi) },
    rfl, fun _ => rfl, rfl, rfl, fun _ => rfl,
    le_fullness_inducedCoarseShading_of_representatives hδ hρ hCd T W p hmaps hle ht hrep⟩

open Classical in
/-- **Tripwire: the shared Section-5 lemma factors through the representatives form.** -/
theorem exists_rhoTubesSection9_fullFamily_refactored
    {δ ρ Cd lam : ℝ≥0} (hδ : 0 < δ) (hρ : ρ ∈ Set.Icc δ 1) (hCd : Cd ≠ 0)
    {s : Finset ι} {t : Finset κ}
    (T : ι → ShadedTube δ E) (W : κ → Tube ρ E) (p : ι → κ)
    (hmaps : ∀ i ∈ s, p i ∈ t)
    (hle : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ (W (p i)).toConvexSpaceBody)
    (hactive : ∀ j ∈ t, ∃ i ∈ s, p i = j) (ht : t.Nonempty)
    (hlam : ∀ i ∈ s,
      (Cd : ENNReal)⁻¹ * ((lam : ENNReal) * volume (T i).carrier) ≤ volume (T i).shade) :
    ∃ G : ShadedFactorFamily E ι κ,
      G.innerSet = s ∧
      (∀ i, G.innerBody i = (T i).toShadedBody) ∧
      G.outerSet = t ∧
      G.parent = p ∧
      (∀ j, (G.outerBody j).toConvexSpaceBody = (W j).toConvexSpaceBody) ∧
      (Cd * rhoTubesInducedFullnessLoss (Module.finrank ℝ E))⁻¹ * lam
        ≤ fullness G.outerSet G.outerBody :=
  exists_rhoTubesSection9_fullFamily_of_representatives hδ hρ hCd T W p hmaps hle ht
    (fun j hj => by
      obtain ⟨i, hi, hpi⟩ := hactive j hj
      exact ⟨i, hi, hpi, hlam i hi⟩)

example : @exists_rhoTubesSection9_fullFamily_refactored
    = @ShadedBody.exists_rhoTubesSection9_fullFamily := rfl

end Representatives

section NodeFraction

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*}

omit [Nontrivial E] in
/-- **Markov, in carrier mass.**  If the aggregate shading mass is at least `a` times the
aggregate carrier mass and no body has shading density above `u`, then the bodies of density at
least `a/2` carry at least an `a/(2u)` fraction of the carrier mass. -/
theorem sum_carrier_dense_ge
    {s : Finset ι} {V : ι → ShadedBody E} {a u : ℝ≥0}
    (hfull : (a : ENNReal) * ∑ i ∈ s, volume (V i).carrier ≤ ∑ i ∈ s, volume (V i).shade)
    (hub : ∀ i ∈ s, volume (V i).shade ≤ (u : ENNReal) * volume (V i).carrier) :
    (a : ENNReal) * ∑ i ∈ s, volume (V i).carrier
      ≤ 2 * (u : ENNReal) *
          ∑ i ∈ s.filter (fun i => (a : ENNReal) * volume (V i).carrier
            ≤ 2 * volume (V i).shade), volume (V i).carrier := by
  classical
  set D : Finset ι := s.filter (fun i => (a : ENNReal) * volume (V i).carrier
    ≤ 2 * volume (V i).shade) with hD_def
  have hcarfin : ∀ i, volume (V i).carrier ≠ ⊤ := fun i => (V i).isCompact.measure_ne_top
  have hsumfin : (∑ i ∈ s, volume (V i).carrier) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ => hcarfin i
  have hAfin : (a : ENNReal) * ∑ i ∈ s, volume (V i).carrier ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hsumfin
  -- split the shade mass
  have hDs : D ⊆ s := Finset.filter_subset _ _
  have hsplit : ∑ i ∈ s, volume (V i).shade
      = ∑ i ∈ D, volume (V i).shade + ∑ i ∈ s \ D, volume (V i).shade := by
    rw [add_comm]
    exact (Finset.sum_sdiff hDs).symm
  -- the dense part, bounded above by `u`
  have hDense : ∑ i ∈ D, volume (V i).shade
      ≤ (u : ENNReal) * ∑ i ∈ D, volume (V i).carrier := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => hub i ?_)
    exact (Finset.mem_filter.1 hi).1
  -- the sparse part, bounded above by `a/2`
  have hSparse : 2 * ∑ i ∈ s \ D, volume (V i).shade
      ≤ (a : ENNReal) * ∑ i ∈ s, volume (V i).carrier := by
    have h1 : 2 * ∑ i ∈ s \ D, volume (V i).shade
        ≤ (a : ENNReal) * ∑ i ∈ s \ D, volume (V i).carrier := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum (fun i hi => ?_)
      have hi' : i ∈ s ∧ i ∉ D := Finset.mem_sdiff.1 hi
      have : ¬ ((a : ENNReal) * volume (V i).carrier ≤ 2 * volume (V i).shade) := by
        intro h
        exact hi'.2 (Finset.mem_filter.2 ⟨hi'.1, h⟩)
      exact le_of_lt (not_le.1 this)
    refine le_trans h1 ?_
    gcongr
    exact Finset.sdiff_subset
  -- combine
  have hkey : (a : ENNReal) * ∑ i ∈ s, volume (V i).carrier
        + (a : ENNReal) * ∑ i ∈ s, volume (V i).carrier
      ≤ 2 * (u : ENNReal) * ∑ i ∈ D, volume (V i).carrier
        + (a : ENNReal) * ∑ i ∈ s, volume (V i).carrier := by
    calc (a : ENNReal) * ∑ i ∈ s, volume (V i).carrier
          + (a : ENNReal) * ∑ i ∈ s, volume (V i).carrier
        = 2 * ((a : ENNReal) * ∑ i ∈ s, volume (V i).carrier) := by ring
      _ ≤ 2 * ∑ i ∈ s, volume (V i).shade := by gcongr
      _ = 2 * ∑ i ∈ D, volume (V i).shade + 2 * ∑ i ∈ s \ D, volume (V i).shade := by
            rw [hsplit]; ring
      _ ≤ 2 * ((u : ENNReal) * ∑ i ∈ D, volume (V i).carrier)
            + (a : ENNReal) * ∑ i ∈ s, volume (V i).carrier := by
            gcongr
      _ = 2 * (u : ENNReal) * ∑ i ∈ D, volume (V i).carrier
            + (a : ENNReal) * ∑ i ∈ s, volume (V i).carrier := by ring
  exact (ENNReal.add_le_add_iff_right hAfin).1 hkey

omit [Nontrivial E] in
open Classical in
/-- **From a fraction of members to a fraction of nodes.**  If the fibres of `p` over `t` are
comparable within `B`, then a subfamily `D ⊆ s` meets at least a `|D| / (B |s|)` fraction of the
nodes.  This is the only place the two-sided branching bracket of `Tube.UniformTubeSet` is used:
`card_class_le` and `le_card_class` give exactly this comparability at `B = C₀²`. -/
theorem card_mul_card_le_of_class_comparable
    {s : Finset ι} {t : Finset κ} {p : ι → κ} (ht : t.Nonempty)
    {D : Finset ι} (hDs : D ⊆ s) {B : ℝ≥0}
    (hpart : ∀ i ∈ s, p i ∈ t)
    (hclass : ∀ j ∈ t, ∀ j' ∈ t,
      ((s.filter (fun i => p i = j')).card : ℝ≥0)
        ≤ B * ((s.filter (fun i => p i = j)).card : ℝ≥0)) :
    ((t.card : ℝ≥0)) * (D.card : ℝ≥0)
      ≤ B * (((D.image p).card : ℝ≥0) * (s.card : ℝ≥0)) := by
  classical
  obtain ⟨j₁, hj₁, hj₁max⟩ :=
    Finset.exists_max_image t (fun j => (s.filter (fun i => p i = j)).card) ht
  -- `D` is covered by the fibres of the nodes it meets
  have hDcard : D.card = ∑ j ∈ D.image p, (D.filter (fun i => p i = j)).card :=
    Finset.card_eq_sum_card_fiberwise (fun i hi => Finset.mem_image_of_mem p hi)
  have hDle : (D.card : ℝ≥0)
      ≤ ((D.image p).card : ℝ≥0) * ((s.filter (fun i => p i = j₁)).card : ℝ≥0) := by
    have hstep : ∀ j ∈ D.image p,
        ((D.filter (fun i => p i = j)).card : ℝ≥0)
          ≤ ((s.filter (fun i => p i = j₁)).card : ℝ≥0) := by
      intro j hj
      obtain ⟨i, hiD, hij⟩ := Finset.mem_image.1 hj
      have hjt : j ∈ t := hij ▸ hpart i (hDs hiD)
      have h1 : (D.filter (fun i => p i = j)).card ≤ (s.filter (fun i => p i = j)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ hDs)
      have h2 : (s.filter (fun i => p i = j)).card
          ≤ (s.filter (fun i => p i = j₁)).card := hj₁max j hjt
      exact_mod_cast le_trans h1 h2
    calc (D.card : ℝ≥0)
        = ∑ j ∈ D.image p, ((D.filter (fun i => p i = j)).card : ℝ≥0) := by
          rw [hDcard]; push_cast; ring
      _ ≤ ∑ _j ∈ D.image p, ((s.filter (fun i => p i = j₁)).card : ℝ≥0) :=
          Finset.sum_le_sum hstep
      _ = ((D.image p).card : ℝ≥0) * ((s.filter (fun i => p i = j₁)).card : ℝ≥0) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- and `s` is at least `|t|` fibres, each within `B` of the largest
  have hscard : s.card = ∑ j ∈ t, (s.filter (fun i => p i = j)).card :=
    Finset.card_eq_sum_card_fiberwise hpart
  have hsge : (t.card : ℝ≥0) * ((s.filter (fun i => p i = j₁)).card : ℝ≥0)
      ≤ B * (s.card : ℝ≥0) := by
    calc (t.card : ℝ≥0) * ((s.filter (fun i => p i = j₁)).card : ℝ≥0)
        = ∑ _j ∈ t, ((s.filter (fun i => p i = j₁)).card : ℝ≥0) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ t, B * ((s.filter (fun i => p i = j)).card : ℝ≥0) :=
          Finset.sum_le_sum (fun j hj => hclass j hj j₁ hj₁)
      _ = B * (s.card : ℝ≥0) := by
          rw [← Finset.mul_sum, hscard]
          congr 1
          push_cast
          ring
  calc ((t.card : ℝ≥0)) * (D.card : ℝ≥0)
      ≤ (t.card : ℝ≥0) *
          (((D.image p).card : ℝ≥0) * ((s.filter (fun i => p i = j₁)).card : ℝ≥0)) := by
        gcongr
    _ = ((D.image p).card : ℝ≥0) *
          ((t.card : ℝ≥0) * ((s.filter (fun i => p i = j₁)).card : ℝ≥0)) := by ring
    _ ≤ ((D.image p).card : ℝ≥0) * (B * (s.card : ℝ≥0)) := by gcongr
    _ = B * (((D.image p).card : ℝ≥0) * (s.card : ℝ≥0)) := by ring

open Classical in
/-- **The fullness clause of GWZ Lemma 5.11 at the FULL node family, from the AGGREGATE datum.**

No per-tube *lower* density bound is assumed.  What is assumed instead is what a configuration
supplies for free: the aggregate fullness `a`, the per-tube *upper* bound `u`
(`Kakeya.VeryNotSticky.shading_ub`, which no consumer reads and which holds by construction at
`lam := max density`), and the two-sided branching bracket `B` that
`Tube.UniformTubeSet` already carries.

Markov turns `a` and `u` into a set `D` of members of density `≥ a/2` carrying an `a/(2u)`
fraction of the carrier mass; the bracket turns that into a fraction of *nodes*; and
`ShadedBody.exists_rhoTubesSection9_fullFamily_of_representatives`, applied to `D` and the nodes
it meets, turns each such node into outer shading.  The nodes with no dense member contribute
nothing and are simply carried in the denominator, which is where the extra factor comes from. -/
theorem le_fullness_inducedCoarseShading_of_aggregate
    {δ ρ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : ρ ∈ Set.Icc δ 1)
    {s : Finset ι} {t : Finset κ}
    (T : ι → ShadedTube δ E) (W : κ → Tube ρ E) (p : ι → κ)
    (hpart : ∀ i ∈ s, p i ∈ t) (hs : s.Nonempty)
    (hle : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ (W (p i)).toConvexSpaceBody)
    {a u B : ℝ≥0} (ha : 0 < a)
    (hfull : (a : ENNReal) * ∑ i ∈ s, volume (T i).carrier ≤ ∑ i ∈ s, volume (T i).shade)
    (hub : ∀ i ∈ s, volume (T i).shade ≤ (u : ENNReal) * volume (T i).carrier)
    (hclass : ∀ j ∈ t, ∀ j' ∈ t,
      ((s.filter (fun i => p i = j')).card : ℝ≥0)
        ≤ B * ((s.filter (fun i => p i = j)).card : ℝ≥0)) :
    a * a * Tube.le_volume.c (Module.finrank ℝ E) * Tube.le_volume.c (Module.finrank ℝ E)
      ≤ 4 * rhoTubesInducedFullnessLoss (Module.finrank ℝ E) * u
          * Tube.volume_le.C (Module.finrank ℝ E) * Tube.volume_le.C (Module.finrank ℝ E) * B
          * fullness t (inducedCoarseShading s T p W) := by
  classical
  set n := Module.finrank ℝ E with hn
  set cv := Tube.le_volume.c n with hcv
  set Cv := Tube.volume_le.C n with hCv
  set loss := rhoTubesInducedFullnessLoss n with hloss
  have hρ1 : ρ ≤ 1 := hρ.2
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ hρ.1
  have hcv0 : 0 < cv := Tube.le_volume.c_pos n
  -- the dense members
  set D : Finset ι := s.filter (fun i => (a : ENNReal) * volume (T i).carrier
    ≤ 2 * volume (T i).shade) with hD
  have hDs : D ⊆ s := Finset.filter_subset _ _
  set P : Finset κ := D.image p with hP
  have hPt : P ⊆ t := by
    intro j hj
    obtain ⟨i, hiD, hij⟩ := Finset.mem_image.1 hj
    exact hij ▸ hpart i (hDs hiD)
  -- volumes of the fine and coarse tubes
  have hTlow : ∀ i, (cv : ENNReal) * (δ : ENNReal) ^ (n - 1) ≤ volume (T i).carrier := by
    intro i; simpa [hcv, hn] using Tube.le_volume (T i).toTube
  have hTup : ∀ i, volume (T i).carrier ≤ (Cv : ENNReal) * (δ : ENNReal) ^ (n - 1) := by
    intro i; simpa [hCv, hn] using Tube.volume_le hδ1 (T i).toTube
  have hWlow : ∀ j, (cv : ENNReal) * (ρ : ENNReal) ^ (n - 1) ≤ volume (W j).carrier := by
    intro j; simpa [hcv, hn] using Tube.le_volume (W j)
  have hWup : ∀ j, volume (W j).carrier ≤ (Cv : ENNReal) * (ρ : ENNReal) ^ (n - 1) := by
    intro j; simpa [hCv, hn] using Tube.volume_le hρ1 (W j)
  have hδp : (0 : ENNReal) < (δ : ENNReal) ^ (n - 1) :=
    ENNReal.pow_pos (ENNReal.coe_pos.mpr hδ) _
  have hρp : (0 : ENNReal) < (ρ : ENNReal) ^ (n - 1) :=
    ENNReal.pow_pos (ENNReal.coe_pos.mpr hρ0) _
  have hδptop : (δ : ENNReal) ^ (n - 1) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hρptop : (ρ : ENNReal) ^ (n - 1) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  -- `D` is nonempty
  have hMark0 := sum_carrier_dense_ge (V := fun i => (T i).toShadedBody) hfull hub
  have hMark : (a : ENNReal) * ∑ i ∈ s, volume (T i).carrier
      ≤ 2 * (u : ENNReal) * ∑ i ∈ D, volume (T i).carrier := hMark0
  have hsumTpos : 0 < ∑ i ∈ s, volume (T i).carrier := by
    obtain ⟨i₀, hi₀⟩ := hs
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum
      (f := fun i => volume (T i).carrier) (fun _ _ => bot_le) hi₀)
    exact lt_of_lt_of_le (ENNReal.mul_pos (ne_of_gt (ENNReal.coe_pos.mpr hcv0)) hδp.ne')
      (hTlow i₀)
  have hDne : D.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h] at hMark
    simp only [Finset.sum_empty, mul_zero] at hMark
    exact absurd (le_antisymm hMark bot_le)
      (ne_of_gt (ENNReal.mul_pos (ENNReal.coe_pos.mpr ha).ne' hsumTpos.ne'))
  have hPne : P.Nonempty := hDne.image p
  have htne : t.Nonempty := ⟨_, hPt hPne.choose_spec⟩
  -- STEP 1: `a * cv * |t| ≤ 2 * u * Cv * B * |P|`
  have hstep1 : (a : ENNReal) * cv * (t.card : ENNReal)
      ≤ 2 * (u : ENNReal) * Cv * B * (P.card : ENNReal) := by
    have hsumD : ∑ i ∈ D, volume (T i).carrier
        ≤ (D.card : ENNReal) * ((Cv : ENNReal) * (δ : ENNReal) ^ (n - 1)) := by
      simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul D
        (fun i => volume (T i).carrier) _ (fun i _ => hTup i)
    have hsumS : (s.card : ENNReal) * ((cv : ENNReal) * (δ : ENNReal) ^ (n - 1))
        ≤ ∑ i ∈ s, volume (T i).carrier := by
      simpa [nsmul_eq_mul] using Finset.card_nsmul_le_sum s
        (fun i => volume (T i).carrier) _ (fun i _ => hTlow i)
    -- cancel `δ^{n-1}`
    have hA : ((δ : ENNReal) ^ (n - 1)) * ((a : ENNReal) * cv * (s.card : ENNReal))
        ≤ ((δ : ENNReal) ^ (n - 1)) * (2 * (u : ENNReal) * Cv * (D.card : ENNReal)) := by
      calc ((δ : ENNReal) ^ (n - 1)) * ((a : ENNReal) * cv * (s.card : ENNReal))
          = (a : ENNReal) * ((s.card : ENNReal) * ((cv : ENNReal) * (δ : ENNReal) ^ (n-1))) := by
            ring
        _ ≤ (a : ENNReal) * ∑ i ∈ s, volume (T i).carrier := by gcongr
        _ ≤ 2 * (u : ENNReal) * ∑ i ∈ D, volume (T i).carrier := hMark
        _ ≤ 2 * (u : ENNReal) * ((D.card : ENNReal) * ((Cv : ENNReal) * (δ:ENNReal)^(n-1))) := by
            gcongr
        _ = ((δ : ENNReal) ^ (n - 1)) * (2 * (u : ENNReal) * Cv * (D.card : ENNReal)) := by ring
    have hA' : (a : ENNReal) * cv * (s.card : ENNReal)
        ≤ 2 * (u : ENNReal) * Cv * (D.card : ENNReal) :=
      (ENNReal.mul_le_mul_iff_right hδp.ne' hδptop).1 hA
    -- the node count
    have hcount := card_mul_card_le_of_class_comparable (s := s) (t := t) (p := p)
      htne hDs hpart hclass
    have hcountE : (t.card : ENNReal) * (D.card : ENNReal)
        ≤ (B : ENNReal) * ((P.card : ENNReal) * (s.card : ENNReal)) := by
      have := ENNReal.coe_le_coe.mpr hcount
      push_cast at this ⊢
      simpa [hP] using this
    -- combine and cancel `|s|`
    have hscard0 : (s.card : ENNReal) ≠ 0 := by
      simpa using Finset.card_ne_zero_of_mem hs.choose_spec
    have hscardtop : (s.card : ENNReal) ≠ ⊤ := by simp
    have hB : (a : ENNReal) * cv * (t.card : ENNReal) * (s.card : ENNReal)
        ≤ 2 * (u : ENNReal) * Cv * B * (P.card : ENNReal) * (s.card : ENNReal) := by
      calc (a : ENNReal) * cv * (t.card : ENNReal) * (s.card : ENNReal)
          = (t.card : ENNReal) * ((a : ENNReal) * cv * (s.card : ENNReal)) := by ring
        _ ≤ (t.card : ENNReal) * (2 * (u : ENNReal) * Cv * (D.card : ENNReal)) := by gcongr
        _ = 2 * (u : ENNReal) * Cv * ((t.card : ENNReal) * (D.card : ENNReal)) := by ring
        _ ≤ 2 * (u : ENNReal) * Cv * ((B : ENNReal) * ((P.card : ENNReal) * (s.card:ENNReal))) := by
            gcongr
        _ = 2 * (u : ENNReal) * Cv * B * (P.card : ENNReal) * (s.card : ENNReal) := by ring
    exact (ENNReal.mul_le_mul_iff_left hscard0 hscardtop).1 hB
  -- STEP 2: `a * cv * |P| ≤ 2 * loss * Cv * |t| * F`
  set F : ℝ≥0 := fullness t (inducedCoarseShading s T p W) with hF
  have hstep2 : (a : ENNReal) * cv * (P.card : ENNReal)
      ≤ 2 * (loss : ENNReal) * Cv * (t.card : ENNReal) * (F : ENNReal) := by
    -- the representatives bound on the dense nodes
    have hrep : ∀ j ∈ P, ∃ i ∈ D, p i = j ∧
        ((2 : ℝ≥0) : ENNReal)⁻¹ * ((a : ENNReal) * volume (T i).carrier)
          ≤ volume (T i).shade := by
      intro j hj
      obtain ⟨i, hiD, hij⟩ := Finset.mem_image.1 hj
      refine ⟨i, hiD, hij, ?_⟩
      have hi2 : (a : ENNReal) * volume (T i).carrier ≤ 2 * volume (T i).shade :=
        (Finset.mem_filter.1 hiD).2
      have h2ne : ((2 : ℝ≥0) : ENNReal) ≠ 0 := by norm_num
      have h2top : ((2 : ℝ≥0) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
      calc ((2 : ℝ≥0) : ENNReal)⁻¹ * ((a : ENNReal) * volume (T i).carrier)
          ≤ ((2 : ℝ≥0) : ENNReal)⁻¹ * (2 * volume (T i).shade) := by gcongr
        _ = volume (T i).shade := by
            have hcoe2 : ((2 : ℝ≥0) : ENNReal) = (2 : ENNReal) := by norm_num
            rw [← mul_assoc, hcoe2, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
    have hcore := le_fullness_inducedCoarseShading_of_representatives (s := D) (t := P)
      (Cd := 2) (lam := a) hδ hρ (by norm_num) T W p
      (fun i hi => Finset.mem_image_of_mem p hi)
      (fun i hi => hle i (hDs hi)) hPne hrep
    -- clear the inverse
    have hlossne : (loss : ℝ≥0) ≠ 0 := rhoTubesInducedFullnessLoss_ne_zero n
    have hmulne : (2 * loss : ℝ≥0) ≠ 0 := by
      simpa using mul_ne_zero (by norm_num : (2 : ℝ≥0) ≠ 0) hlossne
    have hcore' : a ≤ 2 * loss * fullness P (inducedCoarseShading D T p W) := by
      have := mul_le_mul_left' hcore (2 * loss)
      rwa [← mul_assoc, mul_inv_cancel₀ hmulne, one_mul] at this
    -- turn it into a mass inequality
    have hsumPW : ∑ j ∈ P, volume (inducedCoarseShading D T p W j).carrier
        = ∑ j ∈ P, volume (W j).carrier := rfl
    have hmass : (a : ENNReal) * ∑ j ∈ P, volume (W j).carrier
        ≤ 2 * (loss : ENNReal) * ∑ j ∈ P, volume (inducedCoarseShading D T p W j).shade := by
      have hid : ∑ j ∈ P, volume (inducedCoarseShading D T p W j).shade
          = ((fullness P (inducedCoarseShading D T p W) : ℝ≥0) : ENNReal) *
              ∑ j ∈ P, volume (W j).carrier := by
        rw [sum_volumeReal_shade_eq_fullness_mul P (inducedCoarseShading D T p W), hsumPW]
      rw [hid]
      have hcoe : (a : ENNReal)
          ≤ ((2 * loss * fullness P (inducedCoarseShading D T p W) : ℝ≥0) : ENNReal) :=
        ENNReal.coe_le_coe.mpr hcore'
      calc (a : ENNReal) * ∑ j ∈ P, volume (W j).carrier
          ≤ ((2 * loss * fullness P (inducedCoarseShading D T p W) : ℝ≥0) : ENNReal) *
              ∑ j ∈ P, volume (W j).carrier := by gcongr
        _ = 2 * (loss : ENNReal) *
              (((fullness P (inducedCoarseShading D T p W) : ℝ≥0) : ENNReal) *
                ∑ j ∈ P, volume (W j).carrier) := by push_cast; ring
    -- transport the outer shading from `D` to `s` and from `P` to `t`
    have hmono : ∑ j ∈ P, volume (inducedCoarseShading D T p W j).shade
        ≤ ∑ j ∈ t, volume (inducedCoarseShading s T p W j).shade := by
      refine le_trans (Finset.sum_le_sum (fun j _ =>
        measure_mono (inducedCoarseShading_shade_mono hDs T p W j))) ?_
      exact Finset.sum_le_sum_of_subset hPt
    have hFid : ∑ j ∈ t, volume (inducedCoarseShading s T p W j).shade
        = (F : ENNReal) * ∑ j ∈ t, volume (W j).carrier := by
      rw [hF, sum_volumeReal_shade_eq_fullness_mul t (inducedCoarseShading s T p W)]
      rfl
    -- and compare the coarse carrier masses with the cardinalities
    have hPWlow : (P.card : ENNReal) * ((cv : ENNReal) * (ρ : ENNReal) ^ (n - 1))
        ≤ ∑ j ∈ P, volume (W j).carrier := by
      simpa [nsmul_eq_mul] using Finset.card_nsmul_le_sum P
        (fun j => volume (W j).carrier) _ (fun j _ => hWlow j)
    have htWup : ∑ j ∈ t, volume (W j).carrier
        ≤ (t.card : ENNReal) * ((Cv : ENNReal) * (ρ : ENNReal) ^ (n - 1)) := by
      simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul t
        (fun j => volume (W j).carrier) _ (fun j _ => hWup j)
    have hchain : ((ρ : ENNReal) ^ (n - 1)) * ((a : ENNReal) * cv * (P.card : ENNReal))
        ≤ ((ρ : ENNReal) ^ (n - 1)) *
            (2 * (loss : ENNReal) * Cv * (t.card : ENNReal) * (F : ENNReal)) := by
      calc ((ρ : ENNReal) ^ (n - 1)) * ((a : ENNReal) * cv * (P.card : ENNReal))
          = (a : ENNReal) * ((P.card : ENNReal) * ((cv : ENNReal) * (ρ:ENNReal)^(n-1))) := by ring
        _ ≤ (a : ENNReal) * ∑ j ∈ P, volume (W j).carrier := by gcongr
        _ ≤ 2 * (loss : ENNReal) *
              ∑ j ∈ P, volume (inducedCoarseShading D T p W j).shade := hmass
        _ ≤ 2 * (loss : ENNReal) *
              ∑ j ∈ t, volume (inducedCoarseShading s T p W j).shade := by gcongr
        _ = 2 * (loss : ENNReal) * ((F : ENNReal) * ∑ j ∈ t, volume (W j).carrier) := by
              rw [hFid]
        _ ≤ 2 * (loss : ENNReal) *
              ((F : ENNReal) * ((t.card : ENNReal) * ((Cv:ENNReal) * (ρ:ENNReal)^(n-1)))) := by
              gcongr
        _ = ((ρ : ENNReal) ^ (n - 1)) *
              (2 * (loss : ENNReal) * Cv * (t.card : ENNReal) * (F : ENNReal)) := by ring
    exact (ENNReal.mul_le_mul_iff_right hρp.ne' hρptop).1 hchain
  -- COMBINE
  have hPcard0 : (P.card : ENNReal) ≠ 0 := by
    simpa using Finset.card_ne_zero_of_mem hPne.choose_spec
  have htcard0 : (t.card : ENNReal) ≠ 0 := by
    simpa using Finset.card_ne_zero_of_mem htne.choose_spec
  have hprod := mul_le_mul' hstep1 hstep2
  have hfinal : ((a : ENNReal) * a * cv * cv) * ((t.card : ENNReal) * (P.card : ENNReal))
      ≤ (4 * (loss : ENNReal) * u * Cv * Cv * B * (F : ENNReal)) *
          ((t.card : ENNReal) * (P.card : ENNReal)) := by
    calc ((a : ENNReal) * a * cv * cv) * ((t.card : ENNReal) * (P.card : ENNReal))
        = ((a : ENNReal) * cv * (t.card : ENNReal)) * ((a : ENNReal) * cv * (P.card:ENNReal)) := by
          ring
      _ ≤ (2 * (u : ENNReal) * Cv * B * (P.card : ENNReal)) *
            (2 * (loss : ENNReal) * Cv * (t.card : ENNReal) * (F : ENNReal)) := hprod
      _ = (4 * (loss : ENNReal) * u * Cv * Cv * B * (F : ENNReal)) *
            ((t.card : ENNReal) * (P.card : ENNReal)) := by ring
  have hcancel := (ENNReal.mul_le_mul_iff_left
    (by simpa using mul_ne_zero htcard0 hPcard0)
    (ENNReal.mul_ne_top (by simp) (by simp))).1 hfinal
  have : ((a * a * cv * cv : ℝ≥0) : ENNReal)
      ≤ ((4 * loss * u * Cv * Cv * B * F : ℝ≥0) : ENNReal) := by
    push_cast
    convert hcancel using 2 <;> ring
  exact_mod_cast this

open Classical in
/-- **The aggregate datum forces MANY individually dense members.**

Markov, read as a cardinality: with aggregate fullness `a` and per-tube upper density `u`, the
members of density at least `a/2` number at least `a c / (2 u C)` times the whole family, `c` and
`C` being the dimensional bounds on the volume of a `δ`-tube.

This is the aggregate replacement for the composite
`Kakeya.VeryNotSticky.rpow_two_eta_mul_volume_carrier_le_volume_shade`, which asserts the density
of **every** member and is therefore not available from an aggregate.  A count is. -/
theorem card_dense_ge_of_aggregate {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} (T : ι → ShadedTube δ E) {a u : ℝ≥0}
    (hfull : (a : ENNReal) * ∑ i ∈ s, volume (T i).carrier ≤ ∑ i ∈ s, volume (T i).shade)
    (hub : ∀ i ∈ s, volume (T i).shade ≤ (u : ENNReal) * volume (T i).carrier) :
    (a : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E)) * (s.card : ENNReal)
      ≤ 2 * (u : ENNReal) * (Tube.volume_le.C (Module.finrank ℝ E)) *
          ((s.filter (fun i => (a : ENNReal) * volume (T i).carrier
            ≤ 2 * volume (T i).shade)).card : ENNReal) := by
  classical
  set n := Module.finrank ℝ E with hn
  set D : Finset ι := s.filter (fun i => (a : ENNReal) * volume (T i).carrier
    ≤ 2 * volume (T i).shade) with hD
  have hMark0 := sum_carrier_dense_ge (V := fun i => (T i).toShadedBody) hfull hub
  have hMark : (a : ENNReal) * ∑ i ∈ s, volume (T i).carrier
      ≤ 2 * (u : ENNReal) * ∑ i ∈ D, volume (T i).carrier := hMark0
  have hTlow : ∀ i, ((Tube.le_volume.c n : ℝ≥0) : ENNReal) * (δ : ENNReal) ^ (n - 1)
      ≤ volume (T i).carrier := by
    intro i; simpa [hn] using Tube.le_volume (T i).toTube
  have hTup : ∀ i, volume (T i).carrier
      ≤ ((Tube.volume_le.C n : ℝ≥0) : ENNReal) * (δ : ENNReal) ^ (n - 1) := by
    intro i; simpa [hn] using Tube.volume_le hδ1 (T i).toTube
  have hδp : (0 : ENNReal) < (δ : ENNReal) ^ (n - 1) :=
    ENNReal.pow_pos (ENNReal.coe_pos.mpr hδ) _
  have hδptop : (δ : ENNReal) ^ (n - 1) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hsumD : ∑ i ∈ D, volume (T i).carrier
      ≤ (D.card : ENNReal) * (((Tube.volume_le.C n : ℝ≥0) : ENNReal) * (δ : ENNReal) ^ (n-1)) := by
    simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul D
      (fun i => volume (T i).carrier) _ (fun i _ => hTup i)
  have hsumS : (s.card : ENNReal) *
        (((Tube.le_volume.c n : ℝ≥0) : ENNReal) * (δ : ENNReal) ^ (n - 1))
      ≤ ∑ i ∈ s, volume (T i).carrier := by
    simpa [nsmul_eq_mul] using Finset.card_nsmul_le_sum s
      (fun i => volume (T i).carrier) _ (fun i _ => hTlow i)
  have hA : ((δ : ENNReal) ^ (n - 1)) *
        ((a : ENNReal) * (Tube.le_volume.c n) * (s.card : ENNReal))
      ≤ ((δ : ENNReal) ^ (n - 1)) *
        (2 * (u : ENNReal) * (Tube.volume_le.C n) * (D.card : ENNReal)) := by
    calc ((δ : ENNReal) ^ (n - 1)) *
          ((a : ENNReal) * (Tube.le_volume.c n) * (s.card : ENNReal))
        = (a : ENNReal) * ((s.card : ENNReal) *
            (((Tube.le_volume.c n : ℝ≥0) : ENNReal) * (δ : ENNReal) ^ (n - 1))) := by ring
      _ ≤ (a : ENNReal) * ∑ i ∈ s, volume (T i).carrier := by gcongr
      _ ≤ 2 * (u : ENNReal) * ∑ i ∈ D, volume (T i).carrier := hMark
      _ ≤ 2 * (u : ENNReal) * ((D.card : ENNReal) *
            (((Tube.volume_le.C n : ℝ≥0) : ENNReal) * (δ : ENNReal) ^ (n-1))) := by gcongr
      _ = ((δ : ENNReal) ^ (n - 1)) *
            (2 * (u : ENNReal) * (Tube.volume_le.C n) * (D.card : ENNReal)) := by ring
  exact (ENNReal.mul_le_mul_iff_right hδp.ne' hδptop).1 hA


/-! ## The re-encoding test on the residual inequality

This run's standing test: before anyone tries to prove a residual obligation, ask whether it is
the conclusion in disguise.  Applied to `Cd⁻¹ lam · Σ_j |T_ρ| ≤ |U(𝕋, Y)|`, the answer is that it
is **equivalent** to a multiplicity bound, and at the top grid index to an *absolute* one — with
no `|𝕋|` factor, where `Kakeya.multiplicity_le_of_card_isEssDistinct_ge` concludes only
`µ ≤ δ^{ν-η}|𝕋|^β`.
-/

omit [Nontrivial E] in
/-- **A lower bound on the shaded union IS a multiplicity bound — both directions.**

`µ(s, V) = (∑ |Y|)/|U|`, so for any `v`, `v ≤ |U|` and `µ · v ≤ ∑ |Y|` are *the same statement*
whenever the union is nondegenerate.  This is the re-encoding test: a hypothesis of the first
shape is not a volume estimate that a geometry might supply, it is a multiplicity estimate
wearing a volume's clothes. -/
theorem le_volume_iUnionShade_iff_multiplicity_mul_le {s : Finset ι} {V : ι → ShadedBody E}
    (hU0 : volume (⋃ i ∈ s, (V i).shade) ≠ 0)
    (hUtop : volume (⋃ i ∈ s, (V i).shade) ≠ ⊤)
    {v : ENNReal} :
    v ≤ volume (⋃ i ∈ s, (V i).shade)
      ↔ multiplicity s V * v ≤ ∑ i ∈ s, volume (V i).shade := by
  have hid : multiplicity s V * volume (⋃ i ∈ s, (V i).shade)
      = ∑ i ∈ s, volume (V i).shade := by
    rw [multiplicity_eq_div]
    exact ENNReal.div_mul_cancel hU0 hUtop
  constructor
  · intro h
    calc multiplicity s V * v
        ≤ multiplicity s V * volume (⋃ i ∈ s, (V i).shade) := by gcongr
      _ = ∑ i ∈ s, volume (V i).shade := hid
  · intro h
    have hsumtop : (∑ i ∈ s, volume (V i).shade) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr fun i _ =>
        ne_top_of_le_ne_top ((V i).isCompact.measure_lt_top).ne
          (measure_mono (V i).shade_subset)
    have hz : (∑ i ∈ s, volume (V i).shade) ≠ 0 := by
      intro hz0
      exact hU0 (le_antisymm
        (le_trans (measure_biUnion_finset_le _ _) (le_of_eq hz0)) bot_le)
    have hmul0 : multiplicity s V ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hid
      exact hz hid.symm
    have hmultop : multiplicity s V ≠ ⊤ := by
      rw [multiplicity_eq_div]
      exact ENNReal.div_ne_top hsumtop hU0
    rw [← hid] at h
    exact (ENNReal.mul_le_mul_iff_right hmul0 hmultop).1 h


omit [Nontrivial E] in
/-- **What Katz–Tao supplies, in the residue's currency, and at what constant.**

`Kakeya.KatzTaoEstimate` concludes exactly `∑ |Y(T)| ≤ δ^{-ε} |𝕋|^β · |U(𝕋, Y)|` — a lower bound
on the shaded union in the same shape as the residue's residual obligation.  This lemma is the
transport: a Katz–Tao conclusion at constant `B` yields `v ≤ |U(𝕋, Y)|` **exactly when**
`B · v ≤ ∑ |Y(T)|`.

So the residual obligation `a · ∑_j |T_ρ| ≤ |U(𝕋, Y)|` is supplied by Katz–Tao at constant `B`
iff `B ≤ (∑_i |Y(T_i)|) / (a · ∑_j |T_ρ|)`, which for `a = Cd⁻¹ lam ≍ λ` and
`∑_i |T_i| ≍ ∑_j |T_ρ| ≍ 1` is `B ≲ 1`.  The `B` that `Kakeya.KatzTaoEstimate β` provides is
`δ^{-ε} |𝕋|^β`, and `|𝕋| ≥ δ^{-1}` by `Kakeya.VeryNotSticky.tube_count`, so it exceeds the
threshold by `δ^{-ε}|𝕋|^β`.

**The residual obligation is therefore Katz–Tao at `β = 0`** — the endpoint the bootstrap drives
`β` towards but never reaches, since Main Lemma 2 only lowers `β` to the fixed `ε > 0`. -/
theorem le_volume_iUnionShade_of_katzTao_shape {s : Finset ι} {V : ι → ShadedBody E}
    {B v : ENNReal} (hB0 : B ≠ 0) (hBtop : B ≠ ⊤)
    (hKT : ∑ i ∈ s, volume (V i).shade ≤ B * volume (⋃ i ∈ s, (V i).shade))
    (hv : B * v ≤ ∑ i ∈ s, volume (V i).shade) :
    v ≤ volume (⋃ i ∈ s, (V i).shade) := by
  have h : B * v ≤ B * volume (⋃ i ∈ s, (V i).shade) := le_trans hv hKT
  exact (ENNReal.mul_le_mul_iff_right hB0 hBtop).1 h


end NodeFraction

end ShadedBody

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody

universe u

/-- The ambient space of Section 9. -/
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The coarse shaded family at a grid scale, from the AGGREGATE density datum.**

Byte-for-byte the conclusion of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_subfamily`, but proved from
`lam / Cd ≤ λ(𝕋, Y)` instead of from the per-tube field
`Kakeya.VeryNotSticky.shading_lb`. -/
theorem exists_coarseShadedFamilyAtGrid_subfamily_of_fullness (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1)
    (hagg : cfg.lam / cfg.Cd ≤ ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody)) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.outerSet ⊆ cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      G.innerSet = {i ∈ cfg.s | 𝒱.tubeUniform.cover.assign k i ∈ G.outerSet} ∧
      G.parent = 𝒱.tubeUniform.cover.assign k ∧
      (∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody =
        (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (∀ i ∈ cfg.s, (G.innerBody i).toConvexSpaceBody = (cfg.T i).toConvexSpaceBody) ∧
      (cfg.Cd * cfg.coarseLoss)⁻¹ * cfg.lam ≤ ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.coarseLoss : ENNReal)⁻¹ *
            volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  subst hgrid
  let F : ShadedBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι :=
    cfg.nodeFactorFamily 𝒱.tubeUniform hk
  have hFi : F.innerSet = cfg.s := rfl
  have hFp : F.parent = 𝒱.tubeUniform.cover.assign k := rfl
  have hFo : F.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k := rfl
  have hFb : ∀ i, F.innerBody i = (cfg.T i).toShadedBody := fun _ => rfl
  have hFob : ∀ j, F.outerBody j = (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody :=
    fun _ => rfl
  obtain ⟨G, h1, h2, h3, h4, h5, h6, hfull, h8, h9, h10, h11, _h12⟩ :=
    _root_.ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam_of_fullness
      (E := EuclideanSpace ℝ (Fin 3)) (δ := cfg.δ) (Cd := cfg.Cd) (lam := cfg.lam)
      cfg.hδ hρ F cfg.T (𝒱.tubeUniform.cover.tube k)
      (fun i _ => rfl) (fun j _ => rfl)
      (fun i hi => cfg.contained i hi)
      hagg
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hloss : _root_.ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) F.innerSet.card cfg.δ 1
      = cfg.coarseLoss := by
    rw [hfr, hFi]
  refine ⟨G, hFo ▸ h1, (by rw [h2]; congr 1), hFp ▸ h3, fun j hj => (hFob _) ▸ h4 j hj,
    fun i hi => by simpa [hFb] using h5 i (hFi ▸ hi), ?_, ?_⟩
  · rw [← hloss]; exact hfull
  · rw [← hloss]; exact h11

/-- **The aggregate datum is what the field `shading_lb` is for.** -/
theorem fullness_ge_of_shading_lb (cfg : VeryNotSticky.{u}) :
    cfg.lam / cfg.Cd ≤ ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody) :=
  ShadedBody.fullness_ge_of_forall_density
    (ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.hCd))
    cfg.sum_volume_carrier_ne_zero cfg.shading_lb

/-- **The whole density-band group is free from an aggregate fullness bound at `δ^{2η}`.** -/
theorem exists_bandData_of_fullness_two_eta {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {η : ℝ} (hη : 0 ≤ η) {ι : Type*} {s : Finset ι} {V : ι → ShadedBody E3}
    (hfull : δ ^ (2 * η) ≤ ShadedBody.fullness s V) :
    ∃ lam Cd : NNReal, 1 ≤ Cd ∧ Cd * δ ^ (2 * η) ≤ lam ∧
      lam / Cd ≤ ShadedBody.fullness s V ∧
      (∀ i ∈ s, volume (V i).shade
        ≤ (Cd : ENNReal) * ((lam : ENNReal) * volume (V i).carrier)) := by
  have hpos : (0 : NNReal) < δ ^ η := NNReal.rpow_pos hδ0
  have hne : (δ : NNReal) ^ η ≠ 0 := hpos.ne'
  have hle1 : (δ : NNReal) ^ η ≤ 1 := NNReal.rpow_le_one hδ1 hη
  have hsplit : (δ : NNReal) ^ (2 * η) = δ ^ η * δ ^ η := by
    rw [← NNReal.rpow_add hδ0.ne']
    congr 1
    ring
  refine ⟨δ ^ η, (δ ^ η)⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [one_le_inv_iff₀]
    exact ⟨hpos, hle1⟩
  · rw [hsplit, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  · rw [div_eq_mul_inv, inv_inv, ← hsplit]
    exact hfull
  · intro i hi
    have hcancel : ((((δ ^ η)⁻¹ : NNReal)) : ENNReal) *
        ((((δ ^ η : NNReal)) : ENNReal) * volume (V i).carrier) = volume (V i).carrier := by
      rw [← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hne, ENNReal.coe_one, one_mul]
    rw [hcancel]
    exact measure_mono (V i).shade_subset
/-- **Tripwire: the tree's own coarse-family theorem factors through the aggregate one.** -/
theorem exists_coarseShadedFamilyAtGrid_subfamily_refactored (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.outerSet ⊆ cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      G.innerSet = {i ∈ cfg.s | 𝒱.tubeUniform.cover.assign k i ∈ G.outerSet} ∧
      G.parent = 𝒱.tubeUniform.cover.assign k ∧
      (∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody =
        (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (∀ i ∈ cfg.s, (G.innerBody i).toConvexSpaceBody = (cfg.T i).toConvexSpaceBody) ∧
      (cfg.Cd * cfg.coarseLoss)⁻¹ * cfg.lam ≤ ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.coarseLoss : ENNReal)⁻¹ *
            volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) :=
  exists_coarseShadedFamilyAtGrid_subfamily_of_fullness cfg 𝒱 hk hgrid hρ
    (fullness_ge_of_shading_lb cfg)

example : @exists_coarseShadedFamilyAtGrid_subfamily_refactored
    = @Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_subfamily := rfl

/-- `lam ≤ Cd` from the aggregate datum alone: fullness never exceeds `1`. -/
theorem lam_le_Cd_of_fullness (cfg : VeryNotSticky.{u})
    (hagg : cfg.lam / cfg.Cd ≤ ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody)) :
    cfg.lam ≤ cfg.Cd := by
  have hCd : 0 < cfg.Cd := lt_of_lt_of_le zero_lt_one cfg.hCd
  exact (div_le_one hCd).1 (le_trans hagg (ShadedBody.fullness_le_one _ _))

/-- Tripwire: the tree's `lam_le_Cd` factors through the aggregate. -/
theorem lam_le_Cd_refactored (cfg : VeryNotSticky.{u}) : cfg.lam ≤ cfg.Cd :=
  lam_le_Cd_of_fullness cfg (fullness_ge_of_shading_lb cfg)

example : @lam_le_Cd_refactored = @Kakeya.VeryNotSticky.lam_le_Cd := rfl

/-- The only lower bound on `|U(𝕋, Y)|` the configuration supplies, **from the aggregate datum**.

The per-tube field is not needed: the largest shading of the family is at least the average, the
average is `Cd⁻¹ lam` times the average carrier volume by
`ShadedBody.sum_volumeReal_shade_eq_fullness_mul`, and every carrier is at least `c δ²` by
`Tube.le_volume`. -/
theorem le_volume_innerShadedUnion_of_fullness (cfg : VeryNotSticky.{u})
    (hagg : cfg.lam / cfg.Cd ≤ ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody)) :
    (cfg.Cd : ENNReal)⁻¹ *
        ((cfg.lam : ENNReal) *
          ((((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) * (cfg.δ : ENNReal) ^ 2))
      ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) := by
  classical
  have hs : cfg.s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := cfg.tube_count
    rw [h] at this
    simp at this
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  set v : ENNReal := (((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) * (cfg.δ : ENNReal) ^ 2
    with hv_def
  have hvle : ∀ i, v ≤ volume ((cfg.T i).toShadedBody).carrier := by
    intro i
    have h := _root_.Tube.le_volume ((cfg.T i).toTube)
    rw [hfr] at h
    exact h
  have hCd0 : (cfg.Cd : ENNReal) ≠ 0 :=
    (ENNReal.coe_pos.mpr (lt_of_lt_of_le zero_lt_one cfg.hCd)).ne'
  -- the aggregate, cleared of the division
  have haggE : (cfg.Cd : ENNReal)⁻¹ * (cfg.lam : ENNReal)
      ≤ ((ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody) : NNReal) : ENNReal) := by
    have := ENNReal.coe_le_coe.mpr hagg
    rwa [ENNReal.coe_div (by exact ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.hCd)),
      ENNReal.div_eq_inv_mul] at this
  -- the largest shading dominates the average
  obtain ⟨i₀, hi₀, hmax⟩ :=
    Finset.exists_max_image cfg.s (fun i => volume ((cfg.T i).toShadedBody).shade) hs
  have hupper : ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).shade
      ≤ (cfg.s.card : ENNReal) * volume ((cfg.T i₀).toShadedBody).shade := by
    have h := Finset.sum_le_card_nsmul cfg.s
      (fun i => volume ((cfg.T i).toShadedBody).shade)
      (volume ((cfg.T i₀).toShadedBody).shade) hmax
    simpa [nsmul_eq_mul] using h
  have hlower : (cfg.s.card : ENNReal) * v
      ≤ ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).carrier := by
    have h := Finset.card_nsmul_le_sum cfg.s
      (fun i => volume ((cfg.T i).toShadedBody).carrier) v (fun i _ => hvle i)
    simpa [nsmul_eq_mul] using h
  have hmass : (cfg.Cd : ENNReal)⁻¹ * (cfg.lam : ENNReal) *
      ((cfg.s.card : ENNReal) * v) ≤ ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).shade := by
    rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul]
    exact mul_le_mul' haggE hlower
  have hcard0 : (cfg.s.card : ENNReal) ≠ 0 := by
    simpa using Finset.card_ne_zero_of_mem hi₀
  have hcardtop : (cfg.s.card : ENNReal) ≠ ⊤ := by simp
  have hkey : (cfg.Cd : ENNReal)⁻¹ * ((cfg.lam : ENNReal) * v) * (cfg.s.card : ENNReal)
      ≤ volume ((cfg.T i₀).toShadedBody).shade * (cfg.s.card : ENNReal) := by
    rw [mul_comm (volume ((cfg.T i₀).toShadedBody).shade) ((cfg.s.card : ENNReal))]
    refine le_trans (le_of_eq ?_) (le_trans hmass hupper)
    ring
  have hfinal : (cfg.Cd : ENNReal)⁻¹ * ((cfg.lam : ENNReal) * v)
      ≤ volume ((cfg.T i₀).toShadedBody).shade :=
    (ENNReal.mul_le_mul_iff_left hcard0 hcardtop).mp hkey
  exact le_trans hfinal (measure_mono (Set.subset_biUnion_of_mem
    (u := fun i => ((cfg.T i).toShadedBody).shade) hi₀))

/-- Tripwire: the tree's `le_volume_innerShadedUnion` factors through the aggregate. -/
theorem le_volume_innerShadedUnion_refactored (cfg : VeryNotSticky.{u}) :
    (cfg.Cd : ENNReal)⁻¹ *
        ((cfg.lam : ENNReal) *
          ((((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) * (cfg.δ : ENNReal) ^ 2))
      ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) :=
  le_volume_innerShadedUnion_of_fullness cfg (fullness_ge_of_shading_lb cfg)

example : @le_volume_innerShadedUnion_refactored
    = @Kakeya.VeryNotSticky.le_volume_innerShadedUnion := rfl

/-- **The residue's fullness conjunct at the full node family, from ONE dense tube per node.**

`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_inducedFullness` hands the whole per-tube
field `Kakeya.VeryNotSticky.shading_lb` to `ShadedBody.exists_rhoTubesSection9_fullFamily`.  This
is the same statement from the strictly weaker demand isolated by
`ShadedBody.exists_rhoTubesSection9_fullFamily_of_representatives`: every *active* node of the
hierarchy has, in its class, one tube of density at least `Cd⁻¹ lam`.

That is the exact residual obligation an aggregate `shading_lb` would owe here, and it is **not**
implied by an aggregate: a family whose whole shading sits inside the class of a single node
satisfies `Cd⁻¹ lam ≤ λ(𝕋, Y)` while leaving every other active node with no shaded tube at
all, and then the outer fullness is at most `1 / |𝕋_ρ|`. -/
theorem exists_coarseShadedFamilyAtGrid_inducedFullness_of_representatives
    (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1)
    (hrep : ∀ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k, ∃ i ∈ cfg.s,
      𝒱.tubeUniform.cover.assign k i = j ∧
      (cfg.Cd : ENNReal)⁻¹ * ((cfg.lam : ENNReal) * volume (cfg.T i).carrier)
        ≤ volume (cfg.T i).shade) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      G.parent = 𝒱.tubeUniform.cover.assign k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * ShadedBody.rhoTubesInducedFullnessLoss 3)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody := by
  classical
  subst hgrid
  have hs : cfg.s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := cfg.tube_count
    rw [h] at this
    simp at this
  obtain ⟨i₀, hi₀⟩ := hs
  have hmaps : ∀ i ∈ cfg.s, 𝒱.tubeUniform.cover.assign k i
      ∈ cfg.activeTubeNodes 𝒱.tubeUniform k := by
    intro i hi
    rw [activeTubeNodes, Finset.mem_filter]
    refine ⟨𝒱.tubeUniform.cover.assign_mem k hk i hi, ⟨i, ?_⟩⟩
    simp [tubeFibre, Tube.coverClass, hi]
  have hle : ∀ i ∈ cfg.s,
      (cfg.T i).toConvexSpaceBody ≤
        (𝒱.tubeUniform.cover.tube k (𝒱.tubeUniform.cover.assign k i)).toConvexSpaceBody := by
    intro i hi
    simpa using 𝒱.tubeUniform.cover.le_tube_assign k hk i hi
  have ht : (cfg.activeTubeNodes 𝒱.tubeUniform k).Nonempty :=
    ⟨𝒱.tubeUniform.cover.assign k i₀, hmaps i₀ hi₀⟩
  have hCd : cfg.Cd ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.hCd)
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  obtain ⟨G, h1, h2, h3, h4, h5, h6⟩ :=
    _root_.ShadedBody.exists_rhoTubesSection9_fullFamily_of_representatives
      (E := EuclideanSpace ℝ (Fin 3)) (δ := cfg.δ) (Cd := cfg.Cd) (lam := cfg.lam)
      cfg.hδ hρ hCd cfg.T (𝒱.tubeUniform.cover.tube k) (𝒱.tubeUniform.cover.assign k)
      hmaps hle ht hrep
  refine ⟨G, h1, fun i _ => h2 i, h3, h4, fun j _ => h5 j, ?_⟩
  rwa [hfr] at h6

/-- Tripwire: the tree's `inducedFullness` factors through the representatives form. -/
theorem exists_coarseShadedFamilyAtGrid_inducedFullness_refactored (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      G.parent = 𝒱.tubeUniform.cover.assign k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * ShadedBody.rhoTubesInducedFullnessLoss 3)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody := by
  classical
  refine exists_coarseShadedFamilyAtGrid_inducedFullness_of_representatives cfg 𝒱 hk hgrid hρ ?_
  intro j hj
  rw [activeTubeNodes, Finset.mem_filter] at hj
  obtain ⟨i, hi⟩ := hj.2
  rw [tubeFibre, Tube.coverClass, Finset.mem_filter] at hi
  exact ⟨i, hi.1, hi.2, cfg.shading_lb i hi.1⟩

example : @exists_coarseShadedFamilyAtGrid_inducedFullness_refactored
    = @Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_inducedFullness := rfl

/-- **The class sizes of the hierarchy are comparable within `C₀²`.**  This is the two-sided
branching bracket of `Tube.UniformTubeSet`, read as a statement about pairs of nodes. -/
theorem card_coverClass_le_of_uniform {cfg : VeryNotSticky.{u}}
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {j j' : cfg.ι} (hj : j ∈ 𝒱.tubeUniform.cover.indexSet k)
    (hj' : j' ∈ 𝒱.tubeUniform.cover.indexSet k) :
    ((Tube.coverClass cfg.s (𝒱.tubeUniform.cover.assign k) j').card : ℝ≥0)
      ≤ cfg.C₀ ^ 2 * ((Tube.coverClass cfg.s (𝒱.tubeUniform.cover.assign k) j).card : ℝ≥0) := by
  have h1 := 𝒱.tubeUniform.card_class_le k hk j' hj'
  have h2 := 𝒱.tubeUniform.le_card_class k hk j hj
  calc ((Tube.coverClass cfg.s (𝒱.tubeUniform.cover.assign k) j').card : ℝ≥0)
      ≤ cfg.C₀ * 𝒱.tubeUniform.branchingN k := h1
    _ ≤ cfg.C₀ * (cfg.C₀ *
        ((Tube.coverClass cfg.s (𝒱.tubeUniform.cover.assign k) j).card : ℝ≥0)) := by gcongr
    _ = cfg.C₀ ^ 2 *
        ((Tube.coverClass cfg.s (𝒱.tubeUniform.cover.assign k) j).card : ℝ≥0) := by ring

open Classical in
/-- **The residue's fullness conjunct at the FULL node family, from the AGGREGATE datum.**

No per-tube lower density bound: the hypothesis is the aggregate `lam / Cd ≤ λ(𝕋, Y)` — the
proposed weakening of `Kakeya.VeryNotSticky.shading_lb` — and the inputs are the per-tube
*upper* bound `Kakeya.VeryNotSticky.shading_ub`, which no consumer reads, and the two-sided
branching bracket that `Kakeya.VeryNotSticky.uniform` already carries.

**So the answer to "can `uniform` be strengthened to give one dense tube per active node" is
that it does not have to be.**  It cannot force *every* active node to be dense — a family whose
whole shading sits in one node's class is a counterexample, and Definition 2.2 does not see it,
since its clauses quantify over points of the shaded union only.  What the existing brackets do
give is that a `1 / (2 Cd² C₀²)`-fraction of the active nodes are dense, and that is enough:
the dead nodes contribute nothing and are simply carried in the denominator.

The price is the factor `Cd³ C₀²` over
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_inducedFullness`, which is `δ^{-O(η)}`
and not purely dimensional. -/
theorem exists_coarseShadedFamilyAtGrid_inducedFullness_of_aggregate (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1)
    (hagg : cfg.lam / cfg.Cd ≤ ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody)) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      G.parent = 𝒱.tubeUniform.cover.assign k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (∀ j, G.outerBody j = ShadedBody.inducedCoarseShading cfg.s cfg.T
        (𝒱.tubeUniform.cover.assign k) (𝒱.tubeUniform.cover.tube k) j) ∧
      cfg.lam * (Tube.le_volume.c 3) ^ 2
        ≤ 4 * ShadedBody.rhoTubesInducedFullnessLoss 3 * cfg.Cd ^ 3
            * (Tube.volume_le.C 3) ^ 2 * cfg.C₀ ^ 2
            * ShadedBody.fullness G.outerSet G.outerBody := by
  classical
  subst hgrid
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hs : cfg.s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := cfg.tube_count
    rw [h] at this
    simp at this
  obtain ⟨i₀, hi₀⟩ := hs
  have hmaps : ∀ i ∈ cfg.s, 𝒱.tubeUniform.cover.assign k i
      ∈ cfg.activeTubeNodes 𝒱.tubeUniform k := by
    intro i hi
    rw [activeTubeNodes, Finset.mem_filter]
    refine ⟨𝒱.tubeUniform.cover.assign_mem k hk i hi, ⟨i, ?_⟩⟩
    simp [tubeFibre, Tube.coverClass, hi]
  have hle : ∀ i ∈ cfg.s,
      (cfg.T i).toConvexSpaceBody ≤
        (𝒱.tubeUniform.cover.tube k (𝒱.tubeUniform.cover.assign k i)).toConvexSpaceBody := by
    intro i hi
    simpa using 𝒱.tubeUniform.cover.le_tube_assign k hk i hi
  have hCd0 : (cfg.Cd : ℝ≥0) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.hCd)
  -- the aggregate, as a mass inequality
  have haggE : ((cfg.lam / cfg.Cd : ℝ≥0) : ENNReal) *
        ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).carrier
      ≤ ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).shade := by
    rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul cfg.s (fun i => (cfg.T i).toShadedBody)]
    gcongr
  -- the per-tube upper bound
  have hub : ∀ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).shade
      ≤ ((cfg.Cd * cfg.lam : ℝ≥0) : ENNReal) * volume ((cfg.T i).toShadedBody).carrier := by
    intro i hi
    have := cfg.shading_ub i hi
    calc volume ((cfg.T i).toShadedBody).shade
        ≤ (cfg.Cd : ENNReal) * ((cfg.lam : ENNReal) *
            volume ((cfg.T i).toShadedBody).carrier) := this
      _ = ((cfg.Cd * cfg.lam : ℝ≥0) : ENNReal) *
            volume ((cfg.T i).toShadedBody).carrier := by push_cast; ring
  -- positivity of the aggregate density
  have hlam0 : (0 : ℝ≥0) < cfg.lam := by
    have h := cfg.lam_ge
    refine lt_of_lt_of_le ?_ h
    exact mul_pos (lt_of_lt_of_le zero_lt_one cfg.hCd) (NNReal.rpow_pos cfg.hδ)
  have ha : (0 : ℝ≥0) < cfg.lam / cfg.Cd := by
    exact div_pos hlam0 (lt_of_lt_of_le zero_lt_one cfg.hCd)
  -- the engine
  have hclass : ∀ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      ∀ j' ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      ((cfg.s.filter (fun i => 𝒱.tubeUniform.cover.assign k i = j')).card : ℝ≥0)
        ≤ cfg.C₀ ^ 2 *
          ((cfg.s.filter (fun i => 𝒱.tubeUniform.cover.assign k i = j)).card : ℝ≥0) := by
    intro j hj j' hj'
    have hjI : j ∈ 𝒱.tubeUniform.cover.indexSet k := by
      rw [activeTubeNodes, Finset.mem_filter] at hj; exact hj.1
    have hj'I : j' ∈ 𝒱.tubeUniform.cover.indexSet k := by
      rw [activeTubeNodes, Finset.mem_filter] at hj'; exact hj'.1
    simpa [Tube.coverClass] using card_coverClass_le_of_uniform 𝒱 hk hjI hj'I
  have hengine := ShadedBody.le_fullness_inducedCoarseShading_of_aggregate
    (E := EuclideanSpace ℝ (Fin 3)) cfg.hδ cfg.hδ1 hρ
    cfg.T (𝒱.tubeUniform.cover.tube k) (𝒱.tubeUniform.cover.assign k)
    hmaps ⟨i₀, hi₀⟩ hle ha haggE hub hclass
  -- package
  have hcar : ∀ i ∈ cfg.s,
      ((cfg.T i).toConvexSpaceBody : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ ((𝒱.tubeUniform.cover.tube k (𝒱.tubeUniform.cover.assign k i)).toConvexSpaceBody :
            Set (EuclideanSpace ℝ (Fin 3))) :=
    fun i hi => SetLike.coe_subset_coe.mpr (hle i hi)
  have hsubU : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆
      Metric.cthickening (2 * ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ℝ))
        (⋃ i' ∈ ({i' ∈ cfg.s | 𝒱.tubeUniform.cover.assign k i'
            = 𝒱.tubeUniform.cover.assign k i} : Finset cfg.ι), (cfg.T i').shade) := by
    intro i hi
    refine subset_trans ?_ (Metric.self_subset_cthickening _)
    exact Set.subset_biUnion_of_mem (u := fun i' => (cfg.T i').shade)
      (Finset.mem_filter.mpr ⟨hi, rfl⟩)
  refine ⟨{ innerSet := cfg.s
            innerBody := fun i => (cfg.T i).toShadedBody
            outerSet := cfg.activeTubeNodes 𝒱.tubeUniform k
            outerBody := ShadedBody.inducedCoarseShading cfg.s cfg.T
              (𝒱.tubeUniform.cover.assign k) (𝒱.tubeUniform.cover.tube k)
            parent := 𝒱.tubeUniform.cover.assign k
            parent_mem := hmaps
            inner_le_parent := hle
            shade_subset_parent := by
              intro i hi
              exact Set.subset_inter (subset_trans (cfg.T i).shade_subset (hcar i hi))
                (hsubU i hi) },
    rfl, fun i _ => rfl, rfl, rfl, fun j _ => rfl, fun _ => rfl, ?_⟩
  -- the numeric conclusion: divide the engine's bound by `lam` and clear `Cd`
  show cfg.lam * (Tube.le_volume.c 3) ^ 2
      ≤ 4 * ShadedBody.rhoTubesInducedFullnessLoss 3 * cfg.Cd ^ 3
          * (Tube.volume_le.C 3) ^ 2 * cfg.C₀ ^ 2
          * ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
              (ShadedBody.inducedCoarseShading cfg.s cfg.T
                (𝒱.tubeUniform.cover.assign k) (𝒱.tubeUniform.cover.tube k))
  rw [hfr] at hengine
  set F : ℝ≥0 := ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
    (ShadedBody.inducedCoarseShading cfg.s cfg.T
      (𝒱.tubeUniform.cover.assign k) (𝒱.tubeUniform.cover.tube k)) with hF
  have hmul : cfg.Cd ^ 2 * (cfg.lam / cfg.Cd * (cfg.lam / cfg.Cd)) = cfg.lam * cfg.lam := by
    field_simp
  have hstep : cfg.Cd ^ 2 * ((cfg.lam / cfg.Cd) * (cfg.lam / cfg.Cd) *
        Tube.le_volume.c 3 * Tube.le_volume.c 3)
      ≤ cfg.Cd ^ 2 * (4 * ShadedBody.rhoTubesInducedFullnessLoss 3 * (cfg.Cd * cfg.lam)
          * Tube.volume_le.C 3 * Tube.volume_le.C 3 * cfg.C₀ ^ 2 * F) := by
    gcongr
  have hL : cfg.Cd ^ 2 * ((cfg.lam / cfg.Cd) * (cfg.lam / cfg.Cd) *
        Tube.le_volume.c 3 * Tube.le_volume.c 3)
      = cfg.lam * (cfg.lam * (Tube.le_volume.c 3) ^ 2) := by
    rw [show (cfg.lam / cfg.Cd) * (cfg.lam / cfg.Cd) * Tube.le_volume.c 3 * Tube.le_volume.c 3
        = (cfg.lam / cfg.Cd * (cfg.lam / cfg.Cd)) * (Tube.le_volume.c 3) ^ 2 by ring,
      ← mul_assoc, hmul]
    ring
  have hR : cfg.Cd ^ 2 * (4 * ShadedBody.rhoTubesInducedFullnessLoss 3 * (cfg.Cd * cfg.lam)
        * Tube.volume_le.C 3 * Tube.volume_le.C 3 * cfg.C₀ ^ 2 * F)
      = cfg.lam * (4 * ShadedBody.rhoTubesInducedFullnessLoss 3 * cfg.Cd ^ 3
          * (Tube.volume_le.C 3) ^ 2 * cfg.C₀ ^ 2 * F) := by ring
  rw [hL, hR] at hstep
  exact le_of_mul_le_mul_left hstep hlam0


open Classical in
/-- **The aggregate datum still forces `≳ δ^{-1}` individually dense tubes.**

`Kakeya.VeryNotSticky.rpow_two_eta_mul_volume_carrier_le_volume_shade` reads the per-tube field
and concludes that *every* tube of `cfg.s` is individually `δ^{2η}`-full; that is exactly what an
aggregate cannot give.  What it does give is a **count**: with `a := Cd⁻¹ lam` (the aggregate
density, which the repaired `Kakeya.VeryNotSticky.fullness_ge` puts at `≥ δ^{2η}`) and the
per-tube upper bound `Kakeya.VeryNotSticky.shading_ub`, the members of density at least `a/2`
number at least `a c / (2 Cd lam C δ)`, i.e. `≳ δ^{-1} / Cd²` after
`Kakeya.VeryNotSticky.tube_count`.

This is what `Kakeya.VeryNotSticky.tubeCount_of_setupCaseSideDataStatement` and
`Kakeya.VeryNotSticky.not_setupCaseSideDataStatement_of_concentrated` would be restated at:
quantitative, still `δ^{-1}` up to the band width, and therefore still pinning
`Kakeya.VeryNotSticky.lam_ge`. -/
theorem card_dense_mul_delta_ge_of_aggregate (cfg : VeryNotSticky.{u})
    (hagg : cfg.lam / cfg.Cd ≤ ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody)) :
    ((cfg.lam / cfg.Cd : ℝ≥0) : ENNReal) * (Tube.le_volume.c 3)
      ≤ 2 * ((cfg.Cd * cfg.lam : ℝ≥0) : ENNReal) * (Tube.volume_le.C 3) * (cfg.δ : ENNReal) *
          ((cfg.s.filter (fun i => ((cfg.lam / cfg.Cd : ℝ≥0) : ENNReal) *
              volume ((cfg.T i).toShadedBody).carrier
                ≤ 2 * volume ((cfg.T i).toShadedBody).shade)).card : ENNReal) := by
  classical
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have haggE : ((cfg.lam / cfg.Cd : ℝ≥0) : ENNReal) *
        ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).carrier
      ≤ ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).shade := by
    rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul cfg.s (fun i => (cfg.T i).toShadedBody)]
    gcongr
  have hub : ∀ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).shade
      ≤ ((cfg.Cd * cfg.lam : ℝ≥0) : ENNReal) * volume ((cfg.T i).toShadedBody).carrier := by
    intro i hi
    calc volume ((cfg.T i).toShadedBody).shade
        ≤ (cfg.Cd : ENNReal) * ((cfg.lam : ENNReal) *
            volume ((cfg.T i).toShadedBody).carrier) := cfg.shading_ub i hi
      _ = ((cfg.Cd * cfg.lam : ℝ≥0) : ENNReal) *
            volume ((cfg.T i).toShadedBody).carrier := by push_cast; ring
  have hcount := ShadedBody.card_dense_ge_of_aggregate (E := EuclideanSpace ℝ (Fin 3))
    cfg.hδ cfg.hδ1 cfg.T haggE hub
  rw [hfr] at hcount
  calc ((cfg.lam / cfg.Cd : ℝ≥0) : ENNReal) * (Tube.le_volume.c 3)
      = ((cfg.lam / cfg.Cd : ℝ≥0) : ENNReal) * (Tube.le_volume.c 3) * 1 := by ring
    _ ≤ ((cfg.lam / cfg.Cd : ℝ≥0) : ENNReal) * (Tube.le_volume.c 3) *
          ((cfg.δ : ENNReal) * (cfg.s.card : ENNReal)) := by
        gcongr
        exact cfg.tube_count
    _ = (cfg.δ : ENNReal) * (((cfg.lam / cfg.Cd : ℝ≥0) : ENNReal) * (Tube.le_volume.c 3)
          * (cfg.s.card : ENNReal)) := by ring
    _ ≤ (cfg.δ : ENNReal) * (2 * ((cfg.Cd * cfg.lam : ℝ≥0) : ENNReal) * (Tube.volume_le.C 3) *
          ((cfg.s.filter (fun i => ((cfg.lam / cfg.Cd : ℝ≥0) : ENNReal) *
              volume ((cfg.T i).toShadedBody).carrier
                ≤ 2 * volume ((cfg.T i).toShadedBody).shade)).card : ENNReal)) := by
        gcongr
    _ = 2 * ((cfg.Cd * cfg.lam : ℝ≥0) : ENNReal) * (Tube.volume_le.C 3) * (cfg.δ : ENNReal) *
          ((cfg.s.filter (fun i => ((cfg.lam / cfg.Cd : ℝ≥0) : ENNReal) *
              volume ((cfg.T i).toShadedBody).carrier
                ≤ 2 * volume ((cfg.T i).toShadedBody).shade)).card : ENNReal) := by ring


/-- **The same bound in the currency the consumers read.**

Every consumer of the density group reads only the scale-invariant combination `Cd⁻¹ lam` — see
`ShadedBody.le_fullness_of_le_fullness_of_fullness_ge` and
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_subfamily_of_fullness` — so this is the
form to compare against
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_inducedFullness`, whose loss is
`Cd · rhoTubesInducedFullnessLoss 3`.

The extra factor over that is `Cd² C₀²`: the square of the **band width** and the square of the
branching bracket.  `C₀ ≤ δ^{-η}` by `Kakeya.VeryNotSticky.coe_C₀_le_rpow_neg_eta`, so the second
is subpolynomial unconditionally.  The first is **not** scale-invariant — `Cd` is a free field
bounded only below, and `Kakeya.VeryNotSticky.rescaleDensity` sends `(lam, Cd) ↦ (t lam, t Cd)`,
which leaves `Cd⁻¹ lam` fixed while inflating `Cd`.  That is honest rather than hidden: the
argument genuinely uses `Kakeya.VeryNotSticky.shading_ub`, and rescaling genuinely weakens it.  A
producer that takes the tight normalisation `lam := max density`, `Cd := lam / λ(𝕋, Y)` — at
which `shading_ub` is free and `lam_ge` is exactly the repaired `fullness_ge` — has
`Cd ≤ 1 / λ ≤ δ^{-2η}`, and then the whole factor is `δ^{-6η}`. -/
theorem le_fullness_inducedCoarseShading_at_grid_of_aggregate (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1)
    (hagg : cfg.lam / cfg.Cd ≤ ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody)) :
    (cfg.lam / cfg.Cd) * (Tube.le_volume.c 3) ^ 2
      ≤ 4 * ShadedBody.rhoTubesInducedFullnessLoss 3 * cfg.Cd ^ 2
          * (Tube.volume_le.C 3) ^ 2 * cfg.C₀ ^ 2
          * ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
              (ShadedBody.inducedCoarseShading cfg.s cfg.T
                (𝒱.tubeUniform.cover.assign k) (𝒱.tubeUniform.cover.tube k)) := by
  obtain ⟨G, _h1, _h2, h3, _h4, _h5, hbody, hnum⟩ :=
    exists_coarseShadedFamilyAtGrid_inducedFullness_of_aggregate cfg 𝒱 hk hgrid hρ hagg
  have hCd0 : (cfg.Cd : ℝ≥0) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.hCd)
  have hfun : G.outerBody = ShadedBody.inducedCoarseShading cfg.s cfg.T
      (𝒱.tubeUniform.cover.assign k) (𝒱.tubeUniform.cover.tube k) := funext hbody
  rw [h3, hfun] at hnum
  have hdiv : cfg.lam * (Tube.le_volume.c 3) ^ 2 / cfg.Cd
      ≤ (4 * ShadedBody.rhoTubesInducedFullnessLoss 3 * cfg.Cd ^ 3
          * (Tube.volume_le.C 3) ^ 2 * cfg.C₀ ^ 2
          * ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
              (ShadedBody.inducedCoarseShading cfg.s cfg.T
                (𝒱.tubeUniform.cover.assign k) (𝒱.tubeUniform.cover.tube k))) / cfg.Cd := by
    gcongr
  calc (cfg.lam / cfg.Cd) * (Tube.le_volume.c 3) ^ 2
      = cfg.lam * (Tube.le_volume.c 3) ^ 2 / cfg.Cd := by ring
    _ ≤ (4 * ShadedBody.rhoTubesInducedFullnessLoss 3 * cfg.Cd ^ 3
          * (Tube.volume_le.C 3) ^ 2 * cfg.C₀ ^ 2
          * ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
              (ShadedBody.inducedCoarseShading cfg.s cfg.T
                (𝒱.tubeUniform.cover.assign k) (𝒱.tubeUniform.cover.tube k))) / cfg.Cd := hdiv
    _ = 4 * ShadedBody.rhoTubesInducedFullnessLoss 3 * cfg.Cd ^ 2
          * (Tube.volume_le.C 3) ^ 2 * cfg.C₀ ^ 2
          * ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
              (ShadedBody.inducedCoarseShading cfg.s cfg.T
                (𝒱.tubeUniform.cover.assign k) (𝒱.tubeUniform.cover.tube k)) := by
        field_simp

/-! ## The residue's placeholder constant, checked

`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` — one of the tree's 22 sorries — is stated
at `ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 1`.  That is the thirteenth instance of
this development's most common defect: GWZ writes `⪆`, the rendering must choose a constant, and
`1` was chosen.  The tree already says so — `Kakeya.VeryNotSticky.coarseLoss` "is *not* the
placeholder … that `exists_coarseShadedFamilyAtGrid` below is stated with" — and
`Kakeya.VeryNotSticky.coarseLoss_le_rpow_neg_eta` puts the honest loss at `δ^{-η}`, resting on
the field `coarseLoss_absorb`.

The three lemmas below are what an in-place repair needs and what it costs.
-/

/-- `1 ≤ coarseLoss`. -/
theorem one_le_coarseLoss (cfg : VeryNotSticky.{u}) : 1 ≤ cfg.coarseLoss :=
  _root_.ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.one_le_C 3 cfg.s.card cfg.δ 1

/-- `coarseLoss ≤ δ^{-η}` as an `ℝ≥0` inequality. -/
theorem coarseLoss_le_rpow_neg_eta' (cfg : VeryNotSticky.{u}) :
    cfg.coarseLoss ≤ cfg.δ ^ (-cfg.η) := by
  have h := cfg.coarseLoss_le_rpow_neg_eta
  rw [← ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne'] at h
  exact_mod_cast h

/-- **The honest constant costs exactly one `η`.**

The residue `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` is stated at the placeholder
`ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 1`, and its only consumer
(`Kakeya.VeryNotSticky.exists_aScaleInputs`) converts its fullness conjunct into
`δ^{2η} ≤ λ(𝕋_ρ, Y_{𝕋_ρ})` using `Kakeya.VeryNotSticky.lam_ge` and `C = 1`.  Restated at the
honest `Kakeya.VeryNotSticky.coarseLoss`, the same conversion yields `δ^{3η}` and no less:
`lam_ge` gives `Cd δ^{2η} ≤ lam` and `Kakeya.VeryNotSticky.coarseLoss_le_rpow_neg_eta` gives
`coarseLoss ≤ δ^{-η}`.

So the price of honesty on the fullness side is **one `η`**, the same currency  spent once
already, and `Kakeya.aScaleExponentBudget` is where it has to come from. -/
theorem rpow_three_eta_le_of_honest_fullness (cfg : VeryNotSticky.{u})
    {κ : Type*} {t : Finset κ} {V : κ → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    (hhonest : (cfg.Cd * cfg.coarseLoss)⁻¹ * cfg.lam ≤ ShadedBody.fullness t V) :
    (cfg.δ : NNReal) ^ (3 * cfg.η) ≤ ShadedBody.fullness t V := by
  refine le_trans ?_ hhonest
  have hCd0 : cfg.Cd ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.hCd)
  have hcl0 : cfg.coarseLoss ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.one_le_coarseLoss)
  have hδ0 : (cfg.δ : NNReal) ≠ 0 := cfg.hδ.ne'
  -- `coarseLoss * δ^{3η} ≤ δ^{2η}`
  have hsplit : (cfg.δ : NNReal) ^ (-cfg.η) * (cfg.δ : NNReal) ^ (3 * cfg.η)
      = (cfg.δ : NNReal) ^ (2 * cfg.η) := by
    rw [← NNReal.rpow_add hδ0]
    congr 1
    ring
  have hkey : cfg.coarseLoss * (cfg.δ : NNReal) ^ (3 * cfg.η)
      ≤ (cfg.δ : NNReal) ^ (2 * cfg.η) := by
    calc cfg.coarseLoss * (cfg.δ : NNReal) ^ (3 * cfg.η)
        ≤ (cfg.δ : NNReal) ^ (-cfg.η) * (cfg.δ : NNReal) ^ (3 * cfg.η) := by
          gcongr
          exact cfg.coarseLoss_le_rpow_neg_eta'
      _ = (cfg.δ : NNReal) ^ (2 * cfg.η) := hsplit
  -- hence `δ^{3η} ≤ coarseLoss⁻¹ * δ^{2η} ≤ (Cd*coarseLoss)⁻¹ * lam`
  have hstep : (cfg.δ : NNReal) ^ (3 * cfg.η)
      ≤ cfg.coarseLoss⁻¹ * (cfg.δ : NNReal) ^ (2 * cfg.η) := by
    rw [le_inv_mul_iff₀ (lt_of_lt_of_le zero_lt_one cfg.one_le_coarseLoss)]
    exact hkey
  refine le_trans hstep ?_
  have hlam : cfg.Cd * (cfg.δ : NNReal) ^ (2 * cfg.η) ≤ cfg.lam := cfg.lam_ge
  calc cfg.coarseLoss⁻¹ * (cfg.δ : NNReal) ^ (2 * cfg.η)
      = (cfg.Cd * cfg.coarseLoss)⁻¹ * (cfg.Cd * (cfg.δ : NNReal) ^ (2 * cfg.η)) := by
        rw [mul_inv]
        field_simp
    _ ≤ (cfg.Cd * cfg.coarseLoss)⁻¹ * cfg.lam := by gcongr

/-- **The placeholder form implies the honest one, on the fullness conjunct.**

`ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 1` and `1 ≤ coarseLoss`, so the honest
small side is the smaller.  Weakening the residue to the honest constant therefore **loses
nothing**: anything the placeholder form would give, the honest form gives too. -/
theorem honest_fullness_of_placeholder (cfg : VeryNotSticky.{u}) {f : NNReal}
    (h : (cfg.Cd * _root_.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤ f) :
    (cfg.Cd * cfg.coarseLoss)⁻¹ * cfg.lam ≤ f := by
  refine le_trans ?_ h
  have hCd0 : (0 : NNReal) < cfg.Cd := lt_of_lt_of_le zero_lt_one cfg.hCd
  have hpos : (0 : NNReal) <
      cfg.Cd * _root_.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C := by
    rw [_root_.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C, mul_one]
    exact hCd0
  have hle : cfg.Cd * _root_.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C
      ≤ cfg.Cd * cfg.coarseLoss := by
    rw [_root_.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C, mul_one]
    exact le_mul_of_one_le_right bot_le cfg.one_le_coarseLoss
  exact mul_le_mul_right' (inv_anti₀ hpos hle) cfg.lam

/-- **The placeholder form implies the honest one, on the ball conjunct.** -/
theorem honest_ball_of_placeholder (cfg : VeryNotSticky.{u}) {A B : ENNReal}
    (h : (cfg.δ : ENNReal) ^ cfg.η *
        (((_root_.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹
          * A) ≤ B) :
    (cfg.δ : ENNReal) ^ cfg.η * (((cfg.coarseLoss : NNReal) : ENNReal)⁻¹ * A) ≤ B := by
  refine le_trans ?_ h
  have hinv : ((cfg.coarseLoss : NNReal) : ENNReal)⁻¹
      ≤ ((_root_.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ := by
    refine ENNReal.inv_le_inv.2 ?_
    rw [_root_.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C]
    exact_mod_cast cfg.one_le_coarseLoss
  gcongr


/-! ## The subfamily gap, relocated

`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` differs from its deliverer in two places
(`AScaleResidues.lean:163-175`): the loss constant, checked above, and the *subfamily gap* — the
deliverer produces `G.outerSet ⊆ 𝕋_ρ`, the residue demands equality.  With the constant settled,
the subfamily gap is the sole obstruction, and the recorded diagnosis is that the two conjuncts
are satisfiable only at opposite extremes of the legal shading range.

The three results below replace that diagnosis.  The minimal shading settles the ball conjunct
**unconditionally**, so there is no tension and no search; what remains is a single volume
inequality, `Cd⁻¹ lam · Σ_j |T_ρ| ≤ |U(𝕋, Y)|`.
-/

/-- **The minimal admissible coarse shading**: each node tube shaded by its intersection with the
inner shaded union.  This is the smallest shading the `ShadedBody.ShadedFactorFamily` clause
`shade_subset_parent` permits once the inner bodies are pinned, and it is the one
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_minimal` uses — but that statement hides it
behind an `∃ G` which pins only `(G.outerBody j).toConvexSpaceBody`, so it is rebuilt here where
it can be named. -/
noncomputable def minimalCoarseShading (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀) (k : ℕ)
    (j : cfg.ι) : ShadedBody (EuclideanSpace ℝ (Fin 3)) where
  toConvexSpaceBody := (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody
  shade := (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier ∩ (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade)
  measurableSet_shade :=
    ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.isCompact'.isClosed.measurableSet).inter
      cfg.measurableSet_innerShadedUnion
  shade_subset := Set.inter_subset_left

@[simp]
theorem minimalCoarseShading_carrier (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀) (k : ℕ)
    (j : cfg.ι) :
    (cfg.minimalCoarseShading 𝒱 k j).carrier
      = (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier := rfl

/-- The minimal coarse shaded union is contained in the inner one. -/
theorem iUnion_minimalCoarseShading_subset (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀) (k : ℕ)
    (t : Finset cfg.ι) :
    (⋃ j ∈ t, (cfg.minimalCoarseShading 𝒱 k j).shade) ⊆ (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) := by
  intro x hx
  obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 hx
  exact hxj.2

open Classical in
/-- **The subfamily gap closes as soon as the MINIMAL shading is full enough.**

`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` — one of the tree's 22 sorries — asks for
a single shading of the *full* node family satisfying both conjuncts, and the recorded diagnosis
is that the two are satisfiable only at opposite extremes of the legal shading range.  That
framing can be dropped: **the minimal shading satisfies the ball conjunct unconditionally**, at
the placeholder loss `1` and hence at any loss `≥ 1`, because its outer union is contained in the
inner one and the density factor never exceeds `1`.

So the residue is not a search over shadings.  It is exactly one inequality — *is the minimal
shading `Cd⁻¹ lam`-full?* — and this theorem is that reduction. -/
theorem exists_coarseShadedFamilyAtGrid_of_minimal_fullness (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1)
    (hmin : (cfg.Cd * _root_.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
      ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
        (cfg.minimalCoarseShading 𝒱 k)) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * _root_.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((_root_.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  subst hgrid
  have hmaps : ∀ i ∈ cfg.s, 𝒱.tubeUniform.cover.assign k i
      ∈ cfg.activeTubeNodes 𝒱.tubeUniform k := by
    intro i hi
    rw [activeTubeNodes, Finset.mem_filter]
    refine ⟨𝒱.tubeUniform.cover.assign_mem k hk i hi, ⟨i, ?_⟩⟩
    simp [tubeFibre, Tube.coverClass, hi]
  have hle : ∀ i ∈ cfg.s,
      (cfg.T i).toConvexSpaceBody ≤
        (𝒱.tubeUniform.cover.tube k (𝒱.tubeUniform.cover.assign k i)).toConvexSpaceBody := by
    intro i hi
    simpa using 𝒱.tubeUniform.cover.le_tube_assign k hk i hi
  refine ⟨{ innerSet := cfg.s
            innerBody := fun i => (cfg.T i).toShadedBody
            outerSet := cfg.activeTubeNodes 𝒱.tubeUniform k
            outerBody := cfg.minimalCoarseShading 𝒱 k
            parent := 𝒱.tubeUniform.cover.assign k
            parent_mem := hmaps
            inner_le_parent := hle
            shade_subset_parent := by
              intro i hi
              refine Set.subset_inter ?_ ?_
              · exact subset_trans (cfg.T i).shade_subset
                  (SetLike.coe_subset_coe.mpr (hle i hi))
              · exact Set.subset_biUnion_of_mem
                  (u := fun i' => ((cfg.T i').toShadedBody).shade) hi },
    rfl, fun i _ => rfl, rfl, fun j _ => rfl, hmin, ?_⟩
  intro x _
  have hUsub : volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
        (cfg.minimalCoarseShading 𝒱 k j).shade)
      ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) :=
    measure_mono (cfg.iUnion_minimalCoarseShading_subset 𝒱 k _)
  have hdens : volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩
        ball x ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ℝ)) /
      volume (ball x ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ℝ)) ≤ 1 := by
    refine ENNReal.div_le_of_le_mul ?_
    rw [one_mul]
    exact measure_mono Set.inter_subset_right
  have hδη : (cfg.δ : ENNReal) ^ cfg.η ≤ 1 :=
    ENNReal.rpow_le_one (by exact_mod_cast cfg.hδ1) cfg.hη.le
  have hC1 : ((_root_.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹
      = 1 := by
    rw [_root_.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C]
    simp
  rw [hC1]
  calc (cfg.δ : ENNReal) ^ cfg.η *
        (1 * volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            (cfg.minimalCoarseShading 𝒱 k j).shade) *
          (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩
              ball x ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ℝ)) /
            volume (ball x ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ℝ))))
      ≤ 1 * (1 * volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) * 1) := by
        gcongr
    _ = volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) := by ring

open Classical in
/-- **And that one inequality follows from a lower bound on the inner shaded union.**

The node tubes cover `U(𝕋, Y)`, so `Σ_j |W_j ∩ U(𝕋, Y)| ≥ |U(𝕋, Y)|`, and the minimal shading is
`a`-full as soon as `a · Σ_j |W_j| ≤ |U(𝕋, Y)|`.

The only such bound the
configuration supplies is one tube's worth,
`Kakeya.VeryNotSticky.le_volume_innerShadedUnion`, whose own docstring records that nothing in
`Kakeya.VeryNotSticky` improves on it: `maxDensity_le` is an *upper* bound on total tube volume
and `fullness_ge` is a ratio of sums. -/
theorem minimal_fullness_of_le_volume_innerShadedUnion (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ) {a : NNReal}
    (hU : (a : ENNReal) *
        (∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          volume (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
      ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade)) :
    a ≤ ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
        (cfg.minimalCoarseShading 𝒱 k) := by
  classical
  set t : Finset cfg.ι := cfg.activeTubeNodes 𝒱.tubeUniform k with ht
  have hs : cfg.s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := cfg.tube_count
    rw [h] at this
    simp at this
  obtain ⟨i₀, hi₀⟩ := hs
  have hmaps : ∀ i ∈ cfg.s, 𝒱.tubeUniform.cover.assign k i ∈ t := by
    intro i hi
    rw [ht, activeTubeNodes, Finset.mem_filter]
    refine ⟨𝒱.tubeUniform.cover.assign_mem k hk i hi, ⟨i, ?_⟩⟩
    simp [tubeFibre, Tube.coverClass, hi]
  -- the node tubes cover the inner union
  have hcov : volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade)
      ≤ ∑ j ∈ t, volume ((cfg.minimalCoarseShading 𝒱 k j).shade) := by
    have hsub : (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade)
        ⊆ ⋃ j ∈ t, (cfg.minimalCoarseShading 𝒱 k j).shade := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
      refine Set.mem_iUnion₂.2 ⟨𝒱.tubeUniform.cover.assign k i, hmaps i hi, ?_, ?_⟩
      · have hle : (cfg.T i).toConvexSpaceBody ≤
            (𝒱.tubeUniform.cover.tube k (𝒱.tubeUniform.cover.assign k i)).toConvexSpaceBody := by
          simpa using 𝒱.tubeUniform.cover.le_tube_assign k hk i hi
        exact (SetLike.coe_subset_coe.mpr hle) ((cfg.T i).shade_subset hxi)
      · exact Set.mem_iUnion₂.2 ⟨i, hi, hxi⟩
    exact le_trans (measure_mono hsub) (measure_biUnion_finset_le _ _)
  -- and the carriers are the node tubes'
  have hcar : ∑ j ∈ t, volume ((cfg.minimalCoarseShading 𝒱 k j).carrier)
      = ∑ j ∈ t, volume (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier := rfl
  have hmass : (a : ENNReal) * ∑ j ∈ t, volume ((cfg.minimalCoarseShading 𝒱 k j).carrier)
      ≤ ∑ j ∈ t, volume ((cfg.minimalCoarseShading 𝒱 k j).shade) := by
    rw [hcar]
    exact le_trans hU hcov
  -- nondegeneracy
  have hpos : (0 : ENNReal) < ∑ j ∈ t, volume ((cfg.minimalCoarseShading 𝒱 k j).carrier) := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum
      (f := fun j => volume ((cfg.minimalCoarseShading 𝒱 k j).carrier))
      (fun _ _ => bot_le) (hmaps i₀ hi₀))
    have h := _root_.Tube.le_volume
      (𝒱.tubeUniform.cover.tube k (𝒱.tubeUniform.cover.assign k i₀))
    refine lt_of_lt_of_le ?_ h
    refine ENNReal.mul_pos ?_ ?_
    · exact (ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos _)).ne'
    · refine (ENNReal.pow_pos ?_ _).ne'
      exact ENNReal.coe_pos.mpr (Tube.gridScale_pos cfg.hδ _ _)
  have htop : (∑ j ∈ t, volume ((cfg.minimalCoarseShading 𝒱 k j).carrier)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun j _ =>
      ((cfg.minimalCoarseShading 𝒱 k j).isCompact.measure_lt_top).ne
  -- conclude
  rw [← ENNReal.coe_le_coe, ShadedBody.coe_fullness, ShadedBody.fullness']
  exact ENNReal.le_div_iff_mul_le (Or.inl hpos.ne') (Or.inl htop) |>.2 hmass

open Classical in
/-- **THE SUBFAMILY GAP, REDUCED TO ONE VOLUME INEQUALITY.**

Composing the two results above: the residue
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` — one of the tree's 22 sorries — follows
from the single hypothesis

  `Cd⁻¹ lam · Σ_{T_ρ ∈ 𝕋_ρ} |T_ρ| ≤ |U(𝕋, Y)|`.

No existential over shadings, no tension between the two conjuncts, no choice of subfamily: the
minimal shading settles the ball conjunct outright and the node tubes cover the inner union, so
everything the residue asks for reduces to *how large the shaded union is*.

That relocates the obstruction. It is not, as recorded, that "the conjuncts are satisfiable only
at opposite extremes of the legal shading range"; it is that **the configuration supplies no
lower bound on `|U(𝕋, Y)|` beyond one tube's worth**
(`Kakeya.VeryNotSticky.le_volume_innerShadedUnion`, whose docstring says exactly that). -/
theorem exists_coarseShadedFamilyAtGrid_of_le_volume_innerShadedUnion (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1)
    (hU : (((cfg.Cd * _root_.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam
          : NNReal) : ENNReal) *
        (∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          volume (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
      ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade)) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * _root_.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((_root_.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) :=
  cfg.exists_coarseShadedFamilyAtGrid_of_minimal_fullness 𝒱 hk hgrid hρ
    (cfg.minimal_fullness_of_le_volume_innerShadedUnion 𝒱 hk hU)


open Classical in
/-- **THE REDUCTION'S HYPOTHESIS IS STRONGER THAN THE GOAL.**

`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_le_volume_innerShadedUnion` reduces the
residue to `Cd⁻¹ lam · Σ_j |T_ρ| ≤ |U(𝕋, Y)|`.  Read at the **top** grid index, where the node
tubes have radius `1`, that hypothesis forces an *absolute* multiplicity bound — no `|𝕋|`, no
`ρ` — because `Kakeya.VeryNotSticky.sum_volume_carrier_le` caps the shade mass at
`δ^{-η}|B_1|` and one node tube already contributes `Tube.le_volume.c 3` to the sum.

Compare the conclusion of `Kakeya.multiplicity_le_of_card_isEssDistinct_ge`, which is
`µ ≤ δ^{ν-η}|𝕋|^β` and *grows* with `|𝕋| ≥ δ^{-1}`.  An absolute bound is strictly stronger.
So the hypothesis is not the goal in disguise — **it is more than the goal**, and no producer can
supply it without already having more than Main Lemma 2.  This is the same verdict the tree
records for the neighbouring clause `δ^η |⋃ 𝕋_ρ| ≤ |U(𝕋,Y)|` in
`Kakeya.VeryNotSticky.multiplicity_le_of_coarseVolumeComparison`.

**The consequence is precise: the minimal-shading route to the residue is closed.**  It is not a
refutation of the residue — a non-minimal shading is treated separately, and at the top index saturation
already works — but it rules out the one route that made the ball conjunct free. -/
theorem multiplicity_le_of_minimal_fullness_hypothesis (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {a : NNReal} (ha : a ≠ 0)
    (hU : (a : ENNReal) *
        (∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform 0,
          volume (𝒱.tubeUniform.cover.tube 0 j).toConvexSpaceBody.carrier)
      ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade)) :
    ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody)
      ≤ (cfg.δ : ENNReal) ^ (-cfg.η) *
          volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) *
          ((a : ENNReal) * ((_root_.Tube.le_volume.c 3 : NNReal) : ENNReal))⁻¹ := by
  classical
  obtain ⟨j₀, hj₀⟩ := cfg.nonempty_activeTubeNodes 𝒱 (Nat.zero_le _)
  have hgrid0 : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) 0 = 1 := Tube.gridScale_zero _ _
  -- one node tube of radius `1` already contributes `c`
  have hnode : ((_root_.Tube.le_volume.c 3 : NNReal) : ENNReal)
      ≤ volume (𝒱.tubeUniform.cover.tube 0 j₀).toConvexSpaceBody.carrier := by
    have h := _root_.Tube.le_volume (𝒱.tubeUniform.cover.tube 0 j₀)
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    have hone : ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) 0 : NNReal) : ENNReal) = 1 := by
      rw [hgrid0]; simp
    rw [hfr, hone] at h
    simpa using h
  have hsum : ((_root_.Tube.le_volume.c 3 : NNReal) : ENNReal)
      ≤ ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform 0,
          volume (𝒱.tubeUniform.cover.tube 0 j).toConvexSpaceBody.carrier :=
    le_trans hnode (Finset.single_le_sum
      (f := fun j => volume (𝒱.tubeUniform.cover.tube 0 j).toConvexSpaceBody.carrier)
      (fun _ _ => bot_le) hj₀)
  -- so the hypothesis gives `a * c ≤ |U|`
  have hv : (a : ENNReal) * ((_root_.Tube.le_volume.c 3 : NNReal) : ENNReal)
      ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) := by
    refine le_trans ?_ hU
    gcongr
  -- and a lower bound on `|U|` is a multiplicity bound
  refine cfg.multiplicity_le_of_le_volume_innerShadedUnion hv ?_
  have hac0 : (a : ENNReal) * ((_root_.Tube.le_volume.c 3 : NNReal) : ENNReal) ≠ 0 := by
    exact mul_ne_zero (ENNReal.coe_ne_zero.mpr ha)
      (ENNReal.coe_ne_zero.mpr (ne_of_gt (_root_.Tube.le_volume.c_pos 3)))
  have hactop : (a : ENNReal) * ((_root_.Tube.le_volume.c 3 : NNReal) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  rw [mul_assoc, ENNReal.inv_mul_cancel hac0 hactop, mul_one]


/-- The inner shaded union of a configuration is nondegenerate. -/
theorem volume_innerShadedUnion_ne_zero (cfg : VeryNotSticky.{u}) :
    volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ≠ 0 := by
  have h := cfg.le_volume_innerShadedUnion
  refine ne_of_gt (lt_of_lt_of_le ?_ h)
  have hCdinv : ((cfg.Cd : ENNReal))⁻¹ ≠ 0 := by
    simp [ENNReal.inv_eq_zero]
  have hlam : ((cfg.lam : NNReal) : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le
      (mul_pos (lt_of_lt_of_le zero_lt_one cfg.hCd) (NNReal.rpow_pos cfg.hδ)) cfg.lam_ge))
  have hc : (((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (ne_of_gt (_root_.Tube.le_volume.c_pos 3))
  have hδ2 : ((cfg.δ : ENNReal)) ^ 2 ≠ 0 :=
    (ENNReal.pow_pos (ENNReal.coe_pos.mpr cfg.hδ) 2).ne'
  exact pos_iff_ne_zero.mpr (mul_ne_zero hCdinv (mul_ne_zero hlam (mul_ne_zero hc hδ2)))

theorem volume_innerShadedUnion_ne_top (cfg : VeryNotSticky.{u}) :
    volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ≠ ⊤ :=
  ShadedBody.volume_iUnion_shade_ne_top _ _

open Classical in
/-- **THE RE-ENCODING, AT THE CONFIGURATION, BOTH DIRECTIONS.**

The hypothesis to which
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_le_volume_innerShadedUnion` reduces the
residue is **equivalent** to a multiplicity bound.  Not "implies", not "is implied by":
equivalent, and both directions are compiled here through
`ShadedBody.le_volume_iUnionShade_iff_multiplicity_mul_le`, with
`ShadedBody.sum_volumeReal_shade_eq_fullness_mul` supplying `∑|Y(T)| = λ ∑|T|`.

So the residue's remaining obligation is a **multiplicity estimate**, which is what
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge` — the leaf this all sits under — exists to
prove.  Read at the top grid index it is worse than circular:
`Kakeya.VeryNotSticky.multiplicity_le_of_minimal_fullness_hypothesis` turns it into an
**absolute** bound, with no `|𝕋|` factor, while GWZ 9.1 concludes only `µ ≤ δ^{ν-η}|𝕋|^β`. -/
theorem le_volume_innerShadedUnion_iff_multiplicity (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀) (k : ℕ)
    {a : NNReal} :
    (a : ENNReal) *
        (∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          volume (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
      ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade)
    ↔ ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) *
        ((a : ENNReal) *
          (∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            volume (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier))
      ≤ ((ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody) : NNReal) : ENNReal) *
          ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).carrier := by
  rw [← ShadedBody.sum_volumeReal_shade_eq_fullness_mul cfg.s (fun i ↦ (cfg.T i).toShadedBody)]
  exact ShadedBody.le_volume_iUnionShade_iff_multiplicity_mul_le
    cfg.volume_innerShadedUnion_ne_zero cfg.volume_innerShadedUnion_ne_top



/-! ## The untried middle, bounded at once

The two endpoints of the legal shading range are known: `Kakeya.VeryNotSticky.minimalCoarseShading`
gives the ball conjunct free and dies on volume, and the saturated shading gives outer fullness
`1`.  Nothing in between had been examined.  The result below examines all of it at once, by
eliminating the outer shading from the two conjuncts and leaving a condition on the configuration
alone.
-/

open Classical in
/-- **EVERY shading in the interval must satisfy one non-concentration inequality.**

The two endpoints of the legal shading range have been examined — `minimalCoarseShading` gives
the ball conjunct free and dies on volume, the saturated one gives fullness `1` — and the
question is what lies between.  This theorem answers it for the whole interval at once, without
naming a shading: **whatever `G` the residue produces**, its two conjuncts combine into a
statement about the configuration alone.

The mechanism is that the two conjuncts pull on the same quantity from opposite sides.  Fullness
forces `∑_j |Z_j| ≥ a ∑_j |T_ρ|`; each `Z_j` sits inside the outer union, so `∑_j |Z_j| ≤ |𝕋_ρ| ·
|U_out|`; and the ball conjunct caps `|U_out|` against `|U(𝕋,Y)|`.  Eliminating `U_out` leaves

  `δ^η · a · ∑_j |T_ρ| · (|U(𝕋,Y) ∩ B(x,ρ)| / |B(x,ρ)|) ≤ |𝕋_ρ| · |U(𝕋,Y)|`  for every
  `x ∈ U(𝕋,Y)`,

which mentions no shading at all.  It is exactly a **non-concentration** condition on the shaded
union at scale `ρ` — the content `AScaleResidues.lean:2054` records the `max` form as
*discarding*, here derived as a necessary consequence rather than assumed.

So the middle is not empty by fiat, but it is bounded by this: a configuration whose shaded union
concentrates in a single `ρ`-ball admits **no** admissible shading whatever, minimal, saturated or
between. -/
theorem nonconcentration_of_coarseShadedFamily (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} {ρ : NNReal}
    {G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι}
    (hinner : G.innerSet = cfg.s)
    (hbody : ∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody)
    (houterSet : G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k)
    (houterBody : ∀ j ∈ G.outerSet,
      (G.outerBody j).toConvexSpaceBody = (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody)
    {a : NNReal}
    (hfull : a ≤ ShadedBody.fullness G.outerSet G.outerBody)
    (hball : ∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
      (cfg.δ : ENNReal) ^ cfg.η *
          (volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
            (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
              volume (ball x (ρ : ℝ)))) ≤
        volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) :
    ∀ x ∈ ⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade,
      (cfg.δ : ENNReal) ^ cfg.η * ((a : ENNReal) *
          (∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            volume (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)) *
          (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ)) /
            volume (ball x (ρ : ℝ)))
        ≤ ((cfg.activeTubeNodes 𝒱.tubeUniform k).card : ENNReal) *
            volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) := by
  classical
  -- identify the inner union
  have hUeq : (⋃ i ∈ G.innerSet, (G.innerBody i).shade)
      = ⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade := by
    rw [hinner]
    exact Set.iUnion₂_congr (fun i hi => by rw [hbody i hi])
  -- the outer carriers are the node tubes'
  have hcarsum : ∑ j ∈ G.outerSet, volume ((G.outerBody j).carrier)
      = ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          volume (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier := by
    rw [← houterSet]
    exact Finset.sum_congr rfl (fun j hj => by
      exact congrArg (fun B => volume (ConvexSpaceBody.carrier B)) (houterBody j hj))
  -- fullness, cleared of the quotient
  have hmass : (a : ENNReal) * ∑ j ∈ G.outerSet, volume ((G.outerBody j).carrier)
      ≤ ∑ j ∈ G.outerSet, volume ((G.outerBody j).shade) := by
    rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul G.outerSet G.outerBody]
    gcongr
  -- each outer shading sits inside the outer union
  have hsub : ∑ j ∈ G.outerSet, volume ((G.outerBody j).shade)
      ≤ (G.outerSet.card : ENNReal) *
          volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) := by
    have := Finset.sum_le_card_nsmul G.outerSet
      (fun j => volume ((G.outerBody j).shade))
      (volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade))
      (fun j hj => measure_mono (Set.subset_biUnion_of_mem
        (u := fun j' => (G.outerBody j').shade) hj))
    simpa [nsmul_eq_mul] using this
  intro x hx
  have hxV : x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade := by
    refine G.iUnionShade_inner_subset_outer ?_
    rw [hUeq]
    exact hx
  have hb := hball x hxV
  rw [hUeq] at hb
  -- combine
  calc (cfg.δ : ENNReal) ^ cfg.η * ((a : ENNReal) *
        (∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          volume (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)) *
        (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ)) /
          volume (ball x (ρ : ℝ)))
      = (cfg.δ : ENNReal) ^ cfg.η * ((a : ENNReal) *
          ∑ j ∈ G.outerSet, volume ((G.outerBody j).carrier)) *
          (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ)) /
            volume (ball x (ρ : ℝ))) := by rw [hcarsum]
    _ ≤ (cfg.δ : ENNReal) ^ cfg.η *
          ((G.outerSet.card : ENNReal) *
            volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade)) *
          (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ)) /
            volume (ball x (ρ : ℝ))) := by
        refine mul_le_mul_right' (mul_le_mul_left' ?_ _) _
        exact le_trans hmass hsub
    _ = (G.outerSet.card : ENNReal) *
          ((cfg.δ : ENNReal) ^ cfg.η *
            (volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ))))) := by ring
    _ ≤ (G.outerSet.card : ENNReal) *
          volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) := by gcongr
    _ = ((cfg.activeTubeNodes 𝒱.tubeUniform k).card : ENNReal) *
          volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) := by rw [houterSet]


open Classical in
/-- **A concentrated shaded union admits NO admissible shading — the middle is empty there.**

Instantiating `Kakeya.VeryNotSticky.nonconcentration_of_coarseShadedFamily` at a point where the
shaded union fills its own `ρ`-ball, `|U(𝕋,Y) ∩ B(x,ρ)| = |U(𝕋,Y)|`, the factor `|U(𝕋,Y)|`
cancels from both sides and what is left mentions neither the shading nor the shaded union:

  `δ^η · a · ∑_j |T_ρ| ≤ |𝕋_ρ| · |B(0,ρ)|`.

So this is a **refutation criterion for the whole interval at once**: if the coarse family is such
that `|𝕋_ρ| · |B(0,ρ)| < δ^η · a · ∑_j |T_ρ|`, then no `G` whatever — minimal, saturated, or
anything between — satisfies both conjuncts.

The criterion bites at the bottom of the grid. Each node tube has volume at least `c ρ²` and
`|B(0,ρ)| = C_B ρ³`, so the condition reduces to `δ^η a c ≲ C_B ρ`; with `a ≥ δ^{2η}` by
`Kakeya.VeryNotSticky.lam_ge` that is `ρ ≳ δ^{3η}`, and the grid runs down to `ρ = δ ≪ δ^{3η}`.
Whether a configuration whose shaded union is that concentrated exists is the standing
inhabitation question, so this is stated as a criterion and not as a refutation. -/
theorem not_coarseShadedFamily_of_concentrated (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} {ρ : NNReal} {a : NNReal}
    {x : EuclideanSpace ℝ (Fin 3)}
    (hxU : x ∈ ⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade)
    (hconc : volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ))
      = volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade))
    (hρ0 : (0 : ℝ) < (ρ : ℝ))
    (hviol : ((cfg.activeTubeNodes 𝒱.tubeUniform k).card : ENNReal) *
        volume (ball x (ρ : ℝ))
      < (cfg.δ : ENNReal) ^ cfg.η * ((a : ENNReal) *
          (∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            volume (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)))
    (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι)
    (hinner : G.innerSet = cfg.s)
    (hbody : ∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody)
    (houterSet : G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k)
    (houterBody : ∀ j ∈ G.outerSet,
      (G.outerBody j).toConvexSpaceBody = (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody)
    (hfull : a ≤ ShadedBody.fullness G.outerSet G.outerBody)
    (hball : ∀ y ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
      (cfg.δ : ENNReal) ^ cfg.η *
          (volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
            (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball y (ρ : ℝ)) /
              volume (ball y (ρ : ℝ)))) ≤
        volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) :
    False := by
  classical
  have hnc := cfg.nonconcentration_of_coarseShadedFamily 𝒱 hinner hbody houterSet houterBody
    hfull hball x hxU
  rw [hconc] at hnc
  set U : ENNReal := volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) with hU
  set B : ENNReal := volume (ball x (ρ : ℝ)) with hB
  set L : ENNReal := (cfg.δ : ENNReal) ^ cfg.η * ((a : ENNReal) *
      (∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
        volume (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)) with hL
  set N : ENNReal := ((cfg.activeTubeNodes 𝒱.tubeUniform k).card : ENNReal) with hN
  have hB0 : B ≠ 0 := (measure_ball_pos volume x hρ0).ne'
  have hBtop : B ≠ ⊤ := measure_ball_lt_top.ne
  have hU0 : U ≠ 0 := cfg.volume_innerShadedUnion_ne_zero
  have hUtop : U ≠ ⊤ := cfg.volume_innerShadedUnion_ne_top
  -- clear the quotient: `L * U ≤ N * U * B`
  have hstep : L * U ≤ N * U * B := by
    have h := mul_le_mul_right' hnc B
    rwa [mul_assoc, ENNReal.div_mul_cancel hB0 hBtop] at h
  -- cancel `U`
  have hcancel : L ≤ N * B := by
    have h : L * U ≤ (N * B) * U := by
      refine le_trans hstep (le_of_eq ?_)
      ring
    exact (ENNReal.mul_le_mul_iff_left hU0 hUtop).1 h
  exact absurd hcancel (not_le.mpr hviol)



/-! ## The residue restated with the datum it is missing

Rounds 6–8 reduced `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` to a non-concentration
condition on `U(𝕋, Y)` that nothing in `Kakeya.VeryNotSticky` supplies.  Carrying that condition
as a hypothesis closes the statement — at GWZ's own induced shading and at the loss Lemma 5.11
charges.  The two results after it price the restatement: the datum is *false* where the shaded
union concentrates, and the consumer's own working scale lies below the crossover.
-/

open Classical in
/-- **THE RESIDUE, RESTATED WITH THE DATUM IT IS MISSING — AND PROVED.**

`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` is one of the tree's 22 sorries.  Rounds 6
to 8 located its content exactly: the two conjuncts eliminate the shading between them and leave
a **non-concentration** condition on `U(𝕋, Y)` at scale `ρ`
(`Kakeya.VeryNotSticky.nonconcentration_of_coarseShadedFamily`), which nothing in
`Kakeya.VeryNotSticky` supplies.

Carry that condition as a hypothesis and the statement **closes**, at GWZ's own induced shading
`Y_{𝕋_ρ}` and at the loss Lemma 5.11 actually charges:

* the fullness conjunct is `ShadedBody.le_fullness_inducedCoarseShading_of_representatives`,
  discharged from the field `Kakeya.VeryNotSticky.shading_lb`;
* the ball conjunct is `hnc` itself, because the induced outer union is contained in `⋃ 𝕋_ρ` and
  `rhoTubesInducedFullnessLoss 3 ≥ 1` makes the reciprocal on the small side only help.

The only differences from the sorried statement are the loss constant — the placeholder
`ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 1` replaced by the honest
`ShadedBody.rhoTubesInducedFullnessLoss 3`, which is *purely dimensional* — and `hnc`.
`Kakeya.VeryNotSticky.nonconcentration_of_coarseShadedFamily` shows `hnc` is **not** an extra
demand smuggled in: the unqualified statement implies it. -/
theorem exists_coarseShadedFamilyAtGrid_of_nonconcentration (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1)
    (hnc : ∀ x : EuclideanSpace ℝ (Fin 3),
      (cfg.δ : ENNReal) ^ cfg.η *
          (volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
              (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) *
            (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ)) /
              volume (ball x (ρ : ℝ))))
        ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade)) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * _root_.ShadedBody.rhoTubesInducedFullnessLoss 3)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  subst hgrid
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hs : cfg.s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := cfg.tube_count
    rw [h] at this
    simp at this
  obtain ⟨i₀, hi₀⟩ := hs
  have hmaps : ∀ i ∈ cfg.s, 𝒱.tubeUniform.cover.assign k i
      ∈ cfg.activeTubeNodes 𝒱.tubeUniform k := by
    intro i hi
    rw [activeTubeNodes, Finset.mem_filter]
    refine ⟨𝒱.tubeUniform.cover.assign_mem k hk i hi, ⟨i, ?_⟩⟩
    simp [tubeFibre, Tube.coverClass, hi]
  have hle : ∀ i ∈ cfg.s,
      (cfg.T i).toConvexSpaceBody ≤
        (𝒱.tubeUniform.cover.tube k (𝒱.tubeUniform.cover.assign k i)).toConvexSpaceBody := by
    intro i hi
    simpa using 𝒱.tubeUniform.cover.le_tube_assign k hk i hi
  have ht : (cfg.activeTubeNodes 𝒱.tubeUniform k).Nonempty :=
    ⟨𝒱.tubeUniform.cover.assign k i₀, hmaps i₀ hi₀⟩
  have hCd : cfg.Cd ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.hCd)
  -- the fullness conjunct, at GWZ's own induced shading
  have hrep : ∀ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k, ∃ i ∈ cfg.s,
      𝒱.tubeUniform.cover.assign k i = j ∧
      (cfg.Cd : ENNReal)⁻¹ * ((cfg.lam : ENNReal) * volume (cfg.T i).carrier)
        ≤ volume (cfg.T i).shade := by
    intro j hj
    rw [activeTubeNodes, Finset.mem_filter] at hj
    obtain ⟨i, hi⟩ := hj.2
    rw [tubeFibre, Tube.coverClass, Finset.mem_filter] at hi
    exact ⟨i, hi.1, hi.2, cfg.shading_lb i hi.1⟩
  have hfull := _root_.ShadedBody.le_fullness_inducedCoarseShading_of_representatives
    (E := EuclideanSpace ℝ (Fin 3)) (δ := cfg.δ) (Cd := cfg.Cd) (lam := cfg.lam)
    cfg.hδ hρ hCd cfg.T (𝒱.tubeUniform.cover.tube k) (𝒱.tubeUniform.cover.assign k)
    hmaps hle ht hrep
  rw [hfr] at hfull
  -- the structure
  have hcar : ∀ i ∈ cfg.s,
      ((cfg.T i).toConvexSpaceBody : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ ((𝒱.tubeUniform.cover.tube k (𝒱.tubeUniform.cover.assign k i)).toConvexSpaceBody :
            Set (EuclideanSpace ℝ (Fin 3))) :=
    fun i hi => SetLike.coe_subset_coe.mpr (hle i hi)
  have hsubU : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆
      Metric.cthickening (2 * ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ℝ))
        (⋃ i' ∈ ({i' ∈ cfg.s | 𝒱.tubeUniform.cover.assign k i'
            = 𝒱.tubeUniform.cover.assign k i} : Finset cfg.ι), (cfg.T i').shade) := by
    intro i hi
    refine subset_trans ?_ (Metric.self_subset_cthickening _)
    exact Set.subset_biUnion_of_mem (u := fun i' => (cfg.T i').shade)
      (Finset.mem_filter.mpr ⟨hi, rfl⟩)
  refine ⟨{ innerSet := cfg.s
            innerBody := fun i => (cfg.T i).toShadedBody
            outerSet := cfg.activeTubeNodes 𝒱.tubeUniform k
            outerBody := _root_.ShadedBody.inducedCoarseShading cfg.s cfg.T
              (𝒱.tubeUniform.cover.assign k) (𝒱.tubeUniform.cover.tube k)
            parent := 𝒱.tubeUniform.cover.assign k
            parent_mem := hmaps
            inner_le_parent := hle
            shade_subset_parent := by
              intro i hi
              exact Set.subset_inter (subset_trans (cfg.T i).shade_subset (hcar i hi))
                (hsubU i hi) },
    rfl, fun i _ => rfl, rfl, fun j _ => rfl, hfull, ?_⟩
  -- the ball conjunct, straight from `hnc`
  intro x _
  have hVsub : (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
        (_root_.ShadedBody.inducedCoarseShading cfg.s cfg.T
          (𝒱.tubeUniform.cover.assign k) (𝒱.tubeUniform.cover.tube k) j).shade)
      ⊆ ⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier := by
    intro z hz
    obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion₂.1 hz
    exact Set.mem_iUnion₂.2 ⟨j, hj, hzj.1⟩
  have hlossinv : ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal)⁻¹ ≤ 1 := by
    refine ENNReal.inv_le_one.2 ?_
    exact_mod_cast _root_.ShadedBody.one_le_rhoTubesInducedFullnessLoss 3
  refine le_trans ?_ (hnc x)
  refine mul_le_mul_left' (mul_le_mul_right' ?_ _) _
  calc ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal)⁻¹ *
        volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          (_root_.ShadedBody.inducedCoarseShading cfg.s cfg.T
            (𝒱.tubeUniform.cover.assign k) (𝒱.tubeUniform.cover.tube k) j).shade)
      ≤ 1 * volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          (_root_.ShadedBody.inducedCoarseShading cfg.s cfg.T
            (𝒱.tubeUniform.cover.assign k) (𝒱.tubeUniform.cover.tube k) j).shade) := by
        gcongr
    _ = volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          (_root_.ShadedBody.inducedCoarseShading cfg.s cfg.T
            (𝒱.tubeUniform.cover.assign k) (𝒱.tubeUniform.cover.tube k) j).shade) := one_mul _
    _ ≤ volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) := measure_mono hVsub


open Classical in
/-- **The added datum is itself false where the shaded union concentrates.**

`hnc` of `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_nonconcentration` is not a
formality: instantiated at a point where the union fills its own `ρ`-ball, `|U(𝕋,Y)|` cancels and
it becomes `δ^η · |⋃ 𝕋_ρ| ≤ |B(0,ρ)|`, a statement about `ρ` alone.  So the restated residue is
**inapplicable**, not merely unproved, at any grid index where that fails. -/
theorem not_nonconcentration_of_concentrated (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} {ρ : NNReal} {x : EuclideanSpace ℝ (Fin 3)}
    (hconc : volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ))
      = volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade))
    (hρ0 : (0 : ℝ) < (ρ : ℝ))
    (hviol : volume (ball x (ρ : ℝ))
      < (cfg.δ : ENNReal) ^ cfg.η *
          volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)) :
    ¬ (∀ y : EuclideanSpace ℝ (Fin 3),
      (cfg.δ : ENNReal) ^ cfg.η *
          (volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
              (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) *
            (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball y (ρ : ℝ)) /
              volume (ball y (ρ : ℝ))))
        ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade)) := by
  classical
  intro hnc
  have h := hnc x
  rw [hconc] at h
  set U : ENNReal := volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) with hU
  set B : ENNReal := volume (ball x (ρ : ℝ)) with hB
  set L : ENNReal := (cfg.δ : ENNReal) ^ cfg.η *
      volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
        (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) with hL
  have hB0 : B ≠ 0 := (measure_ball_pos volume x hρ0).ne'
  have hBtop : B ≠ ⊤ := measure_ball_lt_top.ne
  have hU0 : U ≠ 0 := cfg.volume_innerShadedUnion_ne_zero
  have hUtop : U ≠ ⊤ := cfg.volume_innerShadedUnion_ne_top
  -- `L * (U / B) ≤ U` clears to `L * U ≤ U * B`, then `L ≤ B`
  have hstep : L * U ≤ U * B := by
    have h' := mul_le_mul_right' h B
    rw [mul_assoc, mul_assoc, ENNReal.div_mul_cancel hB0 hBtop] at h'
    refine le_trans (le_of_eq ?_) h'
    rw [hL]
    ring
  have hcancel : L ≤ B := by
    have h'' : L * U ≤ B * U := by
      refine le_trans hstep (le_of_eq ?_)
      ring
    exact (ENNReal.mul_le_mul_iff_left hU0 hUtop).1 h''
  exact absurd hcancel (not_le.mpr hviol)

/-- **The consumer needs the residue strictly below the crossover.**

`Kakeya.VeryNotSticky.exists_aScaleInputs` invokes the residue at a grid scale comparable to
`cfg.a`, and `Kakeya.VeryNotSticky.hdims` puts `a ≤ b ≤ δ^exscal`.  The `CaseParams` field
`slabDensity` is `3 η < exscal`, so `δ^exscal < δ^{3η}`: the scale the consumer needs is **below**
the crossover `ρ ≳ δ^{3η}` at which
`Kakeya.VeryNotSticky.not_nonconcentration_of_concentrated` starts to bite.

So the consumer cannot discharge `hnc` out of the configuration: at its own working scale the
datum is exactly the thing that can fail. -/
theorem a_lt_rpow_three_eta (cfg : VeryNotSticky.{u}) (hδ1 : cfg.δ < 1)
    (hex : 3 * cfg.η < cfg.exscal) :
    cfg.a < cfg.δ ^ (3 * cfg.η) := by
  have hab : cfg.a ≤ cfg.b := cfg.hdims.2.1
  have hb : cfg.b ≤ cfg.δ ^ cfg.exscal := cfg.hdims.2.2
  have hlt : cfg.δ ^ cfg.exscal < cfg.δ ^ (3 * cfg.η) :=
    NNReal.rpow_lt_rpow_of_exponent_gt cfg.hδ hδ1 hex
  exact lt_of_le_of_lt (le_trans hab hb) hlt


end Kakeya.VeryNotSticky
