/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Section6FactorAdapter
public import Kakeya.DimensionThree.Plank.Section6CoarseFactorisation
public import Kakeya.DimensionThree.Plank.TubePlankNormalisation
public import Kakeya.Factoring.Section6

/-!
# Section 6: the analytic input interface

`Kakeya.GlobalComparableBodyFactorization` and `Kakeya.ComparableBodyFactorization` are *geometric* objects:
they record cellwise containment, hull minimality, transverse comparability and the Katz--Tao
property of the outer family.  They deliberately carry no analytic data.  GWZ Section 6, on the
other hand, feeds its factorisation to two analytic engines:

* generic GWZ Proposition 5.1 (`ShadedBody.factoringAndMultPropCombined`), whose hypothesis
  `ShadedBody.FactorFamily.HasFrostmanFibers` is a Frostman statement about each fibre **inside the
  actual outer body**;
* GWZ Lemma 6.1/6.4, which consume a normalised inner family and therefore need a density transfer
  along the plank normalisation.

This file is the bridge.  It adds no geometry and mutates neither of the two geometric structures;
it supplies constructors and transfer theorems that turn the hypotheses Section 6 actually has into
the hypotheses those engines actually consume.

## What is bridged

1. **Fibre Frostman.**  Section 6 has Frostman control of a fibre inside the cell's *representative
   plank* — that is where the paper's `W` lives, and it is the field
   `Kakeya.Section6PartBFactorisation.coarse_fibre_frostman`.  Proposition 5.1 wants it inside the
   *actual body*.  `ConvexSpaceBody.isFrostmanIn_of_le_of_forall_le` performs that restriction
   **with no loss of constant**: the numerator of `Kakeya.densityIn` is unchanged (every fibre
   member already lies in the smaller body), so shrinking the test body can only *increase* the
   reference density.  This is what makes `Kakeya.Section6FactorData.fibre_frostman` a derived
   clause rather than an extra assumption.

2. **Fibre lower bound.**  `Kakeya.Section6CoarseTubeDecomposition.ofUniformAtScale` takes the
   fibre lower bound `hlb` as an explicit hypothesis, and that is *correct*: uniformity bounds the
   **containment** set `{i | T i ≤ (T k).rescale ρ}` from below, while the fibre of a chosen
   assignment can be strictly smaller; see
   `Kakeya.Section6CoarseTubeDecomposition.fibre_subset_filter_of_uniformAtScale`.
   The bound is therefore kept as data.  What this file adds is the one genuinely sufficient
   condition, `Kakeya.Section6CoarseTubeDecomposition.le_card_fibre_of_faithful`: if the choice
   function did not route any leaf *out* of a parent that contains it, the two sets coincide and
   uniformity's own lower bound transfers verbatim.  This is a property of the chosen assignment,
   not a geometric assumption, and nothing anywhere assumes that a leaf has a unique parent.

3. **Density transfer.**  `Plank.maxDensity_le_of_image_subset` already gives
   `Δ_max(normalised) ≤ C · Δ_max(original)` with the explicit constant `8 / (κ³ c₃)`.  It is
   re-exported here against the interface's own representative planks, with the constant named
   `Kakeya.section6NormalisedDensityConst`.  The constant is **not** `1`, and is not silently
   dropped.

4. **Representative and parent data.**  Reused verbatim: `Kakeya.Section6PartBFactorisation.repr`
   and `cellOf` for the outer layer, `Kakeya.Section6CoarseTubeDecomposition.assign` for the
   coarse/fine layer, and `Kakeya.Section6PartBData` for their combination.  No geometry is rebuilt
   here.

## Import direction

`Kakeya.Section6FactorAdapter` and `Kakeya.Section6CoarseFactorisation` are siblings over
`Kakeya.GlobalComparableBodyFactorization`; this module sits below both and above
`Kakeya.Factoring.Multiplicity`, which reaches it through the adapter.  Nothing is duplicated and no
existing import is reversed.  A Part-(A) consumer living in
`Kakeya/DimensionThree/Plank/FrostmanPlankEstimate.lean` is *upstream* of this file and cannot
consume the interface without first being moved below it; that move is not performed here.
-/

@[expose] public section

open MeasureTheory Convexity
-- Every fibre in this file is a `Finset.filter` over an arbitrary index type.
set_option linter.style.openClassical false
open scoped NNReal ENNReal Classical

noncomputable section

/-! ## Frostman restriction to a smaller test body -/

namespace ConvexSpaceBody

variable {E : Type*} [TopologicalSpace E] [Convexity.ConvexSpace ℝ E] [MeasureSpace E] {ι : Type*}

/-- **Frostman control restricts to a smaller test body with no loss of constant.**

If every member of the family already lies in `K` and `K ≤ K'`, then `C`-Frostman in `K'` implies
`C`-Frostman in `K`.  The numerator of `Kakeya.densityIn` is the same for both test bodies (the
containment filter is vacuous on either), so passing from `K'` to `K` only shrinks the denominator
and therefore *increases* the reference density; the defining inequality survives unchanged.

This is the bridge that lets Section 6 supply its Frostman datum in the representative plank — where
GWZ states it, and where `Kakeya.Section6PartBFactorisation.coarse_fibre_frostman` carries it — and
still meet `ShadedBody.FactorFamily.HasFrostmanFibers`, which is stated in the actual outer body. -/
theorem isFrostmanIn_of_le_of_forall_le
    {s : Finset ι} {V : ι → ConvexSpaceBody E} {K K' : ConvexSpaceBody E} {C : ENNReal}
    (hKK' : K ≤ K') (hV : ∀ i ∈ s, V i ≤ K) (h : IsFrostmanIn s V K' C) :
    IsFrostmanIn s V K C := by
  have hdens : Kakeya.densityIn s V K' ≤ Kakeya.densityIn s V K := by
    have hVK' : ∀ i ∈ s, V i ≤ K' := fun i hi => le_trans (hV i hi) hKK'
    rw [Kakeya.densityIn_of_all_le hVK', Kakeya.densityIn_of_all_le hV]
    gcongr
    exact hKK'
  intro K'' hK''
  refine (h K'' (le_trans hK'' hKK')).trans ?_
  exact mul_le_mul_of_nonneg_left hdens bot_le

end ConvexSpaceBody

namespace Kakeya

/-! ## Enriching a `GlobalComparableBodyFactorization` to a `Section6FactorData` -/

section OfGlobal

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {CFib : ENNReal} {C₀ Cmass Cdim : ℝ≥0}

open Classical in
/-- **The fibre-Frostman clause of `Kakeya.Section6FactorData`, derived.**

Given Frostman control of a cell's fibre inside the cell's representative plank, together with the
cellwise containment of `Kakeya.GlobalComparableBodyFactorization` and the representative containment
`cthickening_le_repr`, the fibre is Frostman inside the **actual** cell body with the *same*
constant.  No new hypothesis and no constant loss. -/
theorem fibre_frostman_of_repr
    (Fz : GlobalComparableBodyFactorization a b hab hb1 q (fun i => (T i).toConvexSpaceBody) C₀)
    (repr : Fz.Cell → Plank a b hab hb1)
    (hcth : ∀ x ∈ Fz.cells,
      (Fz.body x).cthickening ((Fz.body x).scale) ≤ (repr x).toConvexSpaceBody)
    (hfrost : ∀ x ∈ Fz.cells,
      ConvexSpaceBody.IsFrostmanIn ({i ∈ q | Fz.cellOf i = x} : Finset ι)
        (fun i => (T i).toConvexSpaceBody) (repr x).toConvexSpaceBody CFib) :
    ∀ x ∈ Fz.cells,
      ConvexSpaceBody.IsFrostmanIn ({i ∈ q | Fz.cellOf i = x} : Finset ι)
        (fun i => (T i).toConvexSpaceBody) (Fz.body x) CFib := by
  intro x hx
  refine ConvexSpaceBody.isFrostmanIn_of_le_of_forall_le ?_ ?_ (hfrost x hx)
  · exact le_trans (ConvexSpaceBody.self_le_cthickening (Fz.body x) ((Fz.body x).scale)) (hcth x hx)
  · intro i hi
    rw [Finset.mem_filter] at hi
    simpa [hi.2] using Fz.le_body i hi.1

open Classical in
/-- **The Section-6 analytic enrichment of a `Kakeya.GlobalComparableBodyFactorization`.**

The geometric fields — cells, actual bodies, the cell map, cellwise containment and the outer
Katz--Tao property — are taken over verbatim.  The genuinely new inputs are exactly the analytic
ones that a geometric structure has no business carrying:

* `hne`, `hfrost`, `hmass`: fibre nonemptiness, the fibre Frostman datum **stated in the
  representative plank**, and the comparability of fibre masses (GWZ Definition 4.2 clauses (2) and
  (5));
* `repr`, `hcth`, `hvol`: the representative `a × b × 1` plank as data together with the two-sided
  dimension comparison (clause (4)).  `Kakeya.GlobalComparableBodyFactorization.le_plank` supplies only an
  existential and only the upper half, so it cannot serve.

The structure's own `fibre_frostman` field, which is stated in the *actual* body, is derived from
`hfrost` by `Kakeya.fibre_frostman_of_repr` at no cost. -/
def Section6FactorData.ofGlobalPlankFactorization
    (Fz : GlobalComparableBodyFactorization a b hab hb1 q (fun i => (T i).toConvexSpaceBody) C₀)
    (repr : Fz.Cell → Plank a b hab hb1)
    (hcth : ∀ x ∈ Fz.cells,
      (Fz.body x).cthickening ((Fz.body x).scale) ≤ (repr x).toConvexSpaceBody)
    (hvol : ∀ x ∈ Fz.cells,
      volume ((repr x).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ≤ (Cdim : ENNReal) * volume (Fz.body x).carrier)
    (hne : ∀ x ∈ Fz.cells, ({i ∈ q | Fz.cellOf i = x} : Finset ι).Nonempty)
    (hfrost : ∀ x ∈ Fz.cells,
      ConvexSpaceBody.IsFrostmanIn ({i ∈ q | Fz.cellOf i = x} : Finset ι)
        (fun i => (T i).toConvexSpaceBody) (repr x).toConvexSpaceBody CFib)
    (hmass : ∀ x ∈ Fz.cells, ∀ y ∈ Fz.cells,
      Kakeya.densityIn ({i ∈ q | Fz.cellOf i = x} : Finset ι)
          (fun i => (T i).toConvexSpaceBody) (Fz.body x)
        ≤ (Cmass : ENNReal) * Kakeya.densityIn ({i ∈ q | Fz.cellOf i = y} : Finset ι)
          (fun i => (T i).toConvexSpaceBody) (Fz.body y)) :
    Section6FactorData a b hab hb1 q T CFib C₀ Cmass Cdim where
  Cell := Fz.Cell
  decEqCell := Classical.decEq Fz.Cell
  cells := Fz.cells
  body := Fz.body
  cellOf := Fz.cellOf
  cellOf_mem := Fz.cellOf_mem
  le_body := Fz.le_body
  fibre := fun x => {i ∈ q | Fz.cellOf i = x}
  fibre_mem := fun {_ _} => Finset.mem_filter
  fibre_nonempty := hne
  fibre_frostman := fibre_frostman_of_repr Fz repr hcth hfrost
  fibre_mass_comparable := hmass
  isKatzTao := Fz.isKatzTao
  repr := repr
  cthickening_le_repr := hcth
  volume_repr_le := hvol

end OfGlobal

/-! ## The Part-(B) factorisation as a Proposition-5.1 input -/

namespace Section6PartBFactorisation

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {CF C₀ : ℝ≥0}

/-- **The coarse fibre is Frostman in the actual cell body.**

`Kakeya.Section6PartBFactorisation.coarse_fibre_frostman` states the datum in the representative
plank, which is where GWZ states it.  Every member of a cell's coarse fibre already lies in the
actual body (`le_body`), so `ConvexSpaceBody.isFrostmanIn_of_le_of_forall_le` restricts the datum to
the actual body with the same constant `CF`. -/
theorem frostman_fibres_in_body (F : Section6PartBFactorisation a b hab hb1 coarseSet R CF C₀) :
    ∀ x ∈ F.cells,
      ConvexSpaceBody.IsFrostmanIn (F.coarseFibre x) (fun k => (R k).toConvexSpaceBody)
        (F.body x) (CF : ENNReal) := by
  intro x hx
  refine ConvexSpaceBody.isFrostmanIn_of_le_of_forall_le
    (F.body_le_repr x hx) ?hV ?h
  · intro k hk
    rw [mem_coarseFibre_iff] at hk
    rcases hk with ⟨hkcoarse, hkcell⟩
    simpa [hkcell] using F.le_body k hkcoarse
  · simpa [coarseFibre] using F.coarse_fibre_frostman x hx

open Classical in
/-- **The factor family handed to generic GWZ Proposition 5.1 in Part (B).**

Inner bodies are the shaded coarse tubes, outer bodies are the *actual* cell bodies, and the parent
map is the cell map.  Only a shading of the coarse tubes is required as extra input; the convex
carriers are those of `R`, so all the geometry is the factorisation's own. -/
def toShadedFactorFamily (F : Section6PartBFactorisation a b hab hb1 coarseSet R CF C₀)
    (Rs : κ → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hRs : ∀ k, (Rs k).toConvexSpaceBody = (R k).toConvexSpaceBody) :
    ShadedBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) κ F.Cell where
  innerSet := coarseSet
  innerBody := Rs
  outerSet := F.cells
  outerBody := F.body
  parent := F.cellOf
  parent_mem := F.cellOf_mem
  inner_le_parent := by
    intro k hk
    rw [hRs k]
    exact F.le_body k hk

open Classical in
/-- **The Proposition-5.1 Frostman hypothesis, discharged for Part (B).**

This is the clause `Kakeya.GlobalComparableBodyFactorization` structurally cannot provide, and it is the
reason this interface layer exists. -/
theorem hasFrostmanFibers (F : Section6PartBFactorisation a b hab hb1 coarseSet R CF C₀)
    (Rs : κ → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hRs : ∀ k, (Rs k).toConvexSpaceBody = (R k).toConvexSpaceBody) :
    (F.toShadedFactorFamily Rs hRs).HasFrostmanFibers (CF : ENNReal) := by
  intro x hx
  change ConvexSpaceBody.IsFrostmanIn ((F.toShadedFactorFamily Rs hRs).fiber x)
    (fun k => (Rs k).toConvexSpaceBody) (F.body x) (CF : ENNReal)
  change ConvexSpaceBody.IsFrostmanIn ({k ∈ coarseSet | F.cellOf k = x} : Finset κ)
    (fun k => (Rs k).toConvexSpaceBody) (F.body x) (CF : ENNReal)
  rw [show (fun k => (Rs k).toConvexSpaceBody) = (fun k => (R k).toConvexSpaceBody) by
        funext k; exact hRs k]
  exact frostman_fibres_in_body F x hx

end Section6PartBFactorisation

/-! ## The fibre lower bound -/

namespace Section6CoarseTubeDecomposition

open Classical in
/-- **The one sufficient condition for the fibre lower bound.**

`Tube.IsUniformAtScale.le_mul_card_filter` bounds the *containment* set
`{i ∈ q | T i ≤ (T k).rescale ρ}` from below, and
`Kakeya.Section6CoarseTubeDecomposition.fibre_subset_filter_of_uniformAtScale` shows the fibre of a
chosen assignment is contained in it — possibly strictly, since a leaf may lie in several parents
and the choice may have routed it elsewhere.  Under the reverse containment `hfaithful` the two
sets coincide and uniformity's lower bound transfers verbatim.

`hfaithful` is a property of the **choice function**, not of the geometry: it says the chosen
assignment did not route a leaf out of a parent containing it.  In particular nothing here asserts
that a leaf has a unique parent, and no such uniqueness is used anywhere downstream. -/
theorem le_card_fibre_of_faithful {ι : Type*} {q : Finset ι} {δ : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {ρ C : ℝ≥0}
    (U : Tube.IsUniformAtScale q (fun i => (T i).toTube) ρ C) (hC : 0 < C)
    {k : ι} (hk : k ∈ U.parent)
    (hfaithful :
      ({i ∈ q | ((T i).toTube).toConvexSpaceBody ≤
          (U.parentTube k).toConvexSpaceBody} : Finset ι)
        ⊆ ({i ∈ q | uniformCoarseAssign U i = k} : Finset ι)) :
    U.branchingN / C ≤ (({i ∈ q | uniformCoarseAssign U i = k} : Finset ι).card : ℝ≥0) := by
  classical
  let S : Finset ι :=
    {i ∈ q | ((T i).toTube).toConvexSpaceBody ≤ (U.parentTube k).toConvexSpaceBody}
  let F : Finset ι := {i ∈ q | uniformCoarseAssign U i = k}
  have hUb : U.branchingN ≤ C * (S.card : ℝ≥0) := by
    simpa [S] using (U.le_mul_card_filter hk)
  have hcard : (S.card : ℝ≥0) ≤ (F.card : ℝ≥0) := by
    simp only [S, F]
    exact Nat.cast_le.mpr (Finset.card_le_card hfaithful)
  have hmul : C * (S.card : ℝ≥0) ≤ C * (F.card : ℝ≥0) :=
    mul_le_mul_of_nonneg_left hcard (le_of_lt hC)
  have htot : U.branchingN ≤ C * (F.card : ℝ≥0) := hUb.trans hmul
  change U.branchingN / C ≤ (F.card : ℝ≥0)
  rw [div_le_iff₀ hC]
  rw [mul_comm]
  exact htot

open Classical in
/-- **The coarse decomposition from uniformity, with the fibre lower bound discharged.**

Same output as `Kakeya.Section6CoarseTubeDecomposition.ofUniformAtScale`, but the hypothesis `hlb`
is replaced by the faithfulness of the chosen assignment, from which it is derived by
`Kakeya.Section6CoarseTubeDecomposition.le_card_fibre_of_faithful`. -/
def ofUniformAtScaleOfFaithful {ι : Type*} {q : Finset ι} {δ : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {ρ C : ℝ≥0}
    (U : Tube.IsUniformAtScale q (fun i => (T i).toTube) ρ C) (hC : 1 ≤ C)
    (hN : 0 < U.branchingN)
    (hfaithful : ∀ k ∈ q.image (uniformCoarseAssign U),
      ({i ∈ q | ((T i).toTube).toConvexSpaceBody ≤
          (U.parentTube k).toConvexSpaceBody} : Finset ι)
        ⊆ ({i ∈ q | uniformCoarseAssign U i = k} : Finset ι)) :
    Section6CoarseTubeDecomposition q T (q.image (uniformCoarseAssign U))
      U.parentTube U.branchingN C :=
  ofUniformAtScale U hC hN (by
    intro k hk
    apply le_card_fibre_of_faithful U (lt_of_lt_of_le zero_lt_one hC)
    · rw [Finset.mem_image] at hk
      rcases hk with ⟨i, hi, hik⟩
      rw [← hik]
      exact uniformCoarseAssign.mem_parent U hi
    · exact hfaithful k hk)

end Section6CoarseTubeDecomposition

/-! ## The fine-family Remark 5.3 call -/

namespace Section6PartBData

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {m Cfib CF C₀ : ℝ≥0}
  (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)

open Classical in
/-- The Proposition-5.1 family for 6.6(B).  Its inner indices are the fine tubes; the coarse
tubes occur only in the proof of the Remark-5.3 Frostman hypothesis. -/
def toFineProp51Family :
    ShadedBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι D.factor.Cell where
  innerSet := q
  innerBody := fun i ↦ (T i).toShadedBody
  outerSet := D.factor.cells
  outerBody := D.factor.body
  parent := D.cellOfFine
  parent_mem := fun i hi ↦ D.factor.cellOf_mem _ (D.decomp.assign_mem i hi)
  inner_le_parent := fun i hi ↦
    le_trans (D.decomp.leaf_le_parent i hi)
      (D.factor.le_body _ (D.decomp.assign_mem i hi))

open Classical in
/-- Apply the corrected fixed-scale Proposition 5.1 under GWZ Remark 5.3.  In particular this
does not replace the fine inner family by the coarse tubes. -/
theorem prop51CoreAtScaleOfRemark53 {δ₀ w₁ : NNReal}
    (input : ShadedBody.Section6FactoringAtScaleInput D.toFineProp51Family δ₀ w₁)
    (hFrostman : D.toFineProp51Family.HasThickenedFrostmanFibers (CF : ENNReal)) :
    ShadedBody.FactoringAndMultPropCoreAtScale (C := (CF : ENNReal))
      D.toFineProp51Family input.hδ input.hdisc input.volumeRatio w₁ input.hw₁ :=
  ShadedBody.section6GlobalFactorisation D.toFineProp51Family input hFrostman

open Classical in
/-- Scale-selecting form of `prop51CoreAtScaleOfRemark53`.  The thickened-Frostman input is the
precise Section 6 obligation that still has to be obtained from the coarse-parent geometry. -/
theorem prop51CoreSelectScaleOfRemark53 {δ₀ B : NNReal}
    (input : ShadedBody.Section6FactoringSelectScaleInput D.toFineProp51Family δ₀ B)
    (hFrostman : D.toFineProp51Family.HasThickenedFrostmanFibers (CF : ENNReal)) :
    ShadedBody.FactoringAndMultPropCoreSelectScaleResult (C := (CF : ENNReal))
      D.toFineProp51Family input.hδ input.hdisc input.volumeRatio input.hδB input.hupper
        input.hmass :=
  ShadedBody.section6GlobalFactorisationSelectScale D.toFineProp51Family input hFrostman

end Section6PartBData

/-! ## Density transfer along the plank normalisation -/

/-- **The explicit constant of the Section-6 normalised density transfer.**

`8 / (κ³ c₃)`, where `κ` is the plank-normalisation parameter and `c₃` the dimensional lower bound
of `Tube.le_volume` in `ℝ³`.  It is an absolute constant once `κ` is fixed, and it is *not*
`1`: the normalisation is volume-preserving only up to the Jacobian, and the inner plank model is
strictly larger than the image tube it contains. -/
def section6NormalisedDensityConst (κ : ℝ) : ℝ≥0 :=
  8 / (Real.toNNReal κ ^ 3 * Tube.le_volume.c 3)

section DensityTransfer

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {CFib : ENNReal} {C₀ Cmass Cdim : ℝ≥0}

open Classical in
/-- **Normalised density transfer against a cell's representative plank.**

`Δ_max` of the inner plank models of a cell's fibre is bounded by
`section6NormalisedDensityConst κ` times `Δ_max` of the fine tubes themselves.  This is
`Plank.maxDensity_le_of_image_subset` read through the interface: the representative plank is
`F.repr x`, and the fibre is the cell's fibre.

The constant is carried explicitly.  Forcing it to `1` would be false. -/
theorem Section6FactorData.maxDensity_normalised_le
    (F : Section6FactorData a b hab hb1 q T CFib C₀ Cmass Cdim)
    (ha : 0 < a) (hδ0 : 0 < δ) (x : F.Cell)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ} (hκ : 0 < κ)
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : Plank.IsPlankNormalisation (F.repr x) f κ g) {J : ℝ≥0}
    (hvolf : ∀ A : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' A) = (J : ENNReal) * volume A)
    {ha'b' : δ / b ≤ δ / a} {hb'1 : δ / a ≤ 1} (P : ι → Plank (δ / b) (δ / a) ha'b' hb'1)
    (hsub : ∀ i ∈ ({i ∈ q | F.cellOf i = x} : Finset ι),
      f '' ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    Kakeya.maxDensity ({i ∈ q | F.cellOf i = x} : Finset ι)
        (fun i => (P i).toConvexSpaceBody)
      ≤ ((section6NormalisedDensityConst κ : ℝ≥0) : ENNReal)
        * Kakeya.maxDensity ({i ∈ q | F.cellOf i = x} : Finset ι)
            (fun i => (T i).toConvexSpaceBody) := by
  exact Plank.maxDensity_le_of_image_subset
    ({i ∈ q | F.cellOf i = x} : Finset ι) ha hδ0 (F.repr x) hκ hnorm
    hvolf T P hsub

end DensityTransfer

end Kakeya

end

end
