/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.CollarPlankPresentation
public import Kakeya.DimensionThree.Plank.Section6PartBProp51Input

/-!
# GWZ Proposition 5.1 for Part (B), on exact `a × b × 1` shaded planks

`Kakeya.Section6PartBData.exists_prop51SelectScale` makes GWZ Proposition 5.1 a **theorem** of the
Part-(B) datum, and `Kakeya.Section6PartBData.exists_prop51_split_over_constructed_output` records
its refinement and multiplicity split.  Both live on the *actual cell bodies*: the outer bodies of
the constructed output are the `Kakeya.ConvexSpaceBody.scale`-collars of the cell bodies
(`Kakeya.ShadedBody.FactoringAndMultPropCoreAtScale.outer_carrier`).

`Kakeya.Section6PartBData.OuterPackage`, which the Section-6 assembly consumes, lives on
`Kakeya.ShadedPlank a b`s instead.  This file crosses that gap, using
`Kakeya.collarPlank` (`Kakeya/DimensionThree/Plank/CollarPlankPresentation.lean`) — the single
common homothety, under which the multiplicity split transports **exactly**.

## The one hypothesis that is not free

`Kakeya.IsPlankOfDimensions Cw a b (D.factor.body x)` — the two-sided bracketing of the three
affine thicknesses of a cell body.  Its *upper* half is free from the datum
(`Kakeya.Section6PartBFactorisation.body_le_repr` puts the body in an exact `a × b × 1` plank, so
`Kakeya.Section6PartBData.ethickness_two_body_le` and `Kakeya.Prism3D.ethickness_one_le` give the
two transverse bounds, and `repr_window` gives the longitudinal one); the *lower* half is the
content, and it is exactly what GWZ Proposition 6.6(B)'s own `wide` clause is for.  Its producer is
already in the tree:

`Kakeya.GlobalPlankFactorization.exists_isPlankFamilyOfDimensions`
(`Kakeya/DimensionThree/Plank/GlobalPlankDatumBridge.lean`)

returns `∃ a', ρ ≤ a' ∧ a' ≤ a ∧ IsPlankFamilyOfDimensions (plankReadingConst Cw C₀) a' b …` for
the 6.6(B) datum, at a re-declared thin half-width `a' ≤ a`; re-declaring `a` downward only makes
the conclusion `(a / b) ^ β` of 6.6(B) weaker than the truth, so nothing is lost.  This is why the
hypothesis is a genuine interface and not a deferral.

## What is *not* done here

Pairwise essential distinctness of the presented planks.  It is not derivable from essential
distinctness of the representative planks — the presentation shrinks the *positions* by the common
homothety ratio while keeping the declared half-widths `a × b × 1`, so the presented family is
fatter relative to its separation.  That is the (independent) essential-distinctness gap; the tree's
tool for it is `Kakeya.exists_pairwise_plank_subset_of_isThickeningNonconcentrated`
(`Kakeya/Factoring/FlatPrisms.lean`), which is how the proved Part-(A) theorem
`Kakeya.multiplicity_le_of_factorsThroughFlatPrisms_of_parentPresentation` extracts an essentially
distinct outer subfamily internally.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal ENNReal Classical

noncomputable section

namespace Kakeya

namespace Section6PartBData

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {m Cfib CF C₀ : ℝ≥0}
  (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)

theorem one_le_plankWindowRadius : (1 : ℝ≥0) ≤ plankWindowRadius := by
  rw [plankWindowRadius]; norm_num

/-- Reassociation used once below; stated separately so that `ring` sees no metavariables. -/
private theorem mulReassoc4 (c c' A B : ENNReal) : c * (c' * A * B) = (c * c') * A * B := by
  ring

open Classical in
/-- **The constructed Part-(B) Proposition-5.1 output is collar-presentable.**

Everything the plank presentation of `Kakeya/DimensionThree/Plank/CollarPlankPresentation.lean`
needs, over the family GWZ Proposition 5.1 actually constructs for Part (B), together with the
refinement and multiplicity split of
`Kakeya.Section6PartBData.exists_prop51_split_over_constructed_output`.

The window radius is `Kakeya.plankWindowRadius`, i.e. `4`; this is the whole reason the
window-generalised envelope of `Kakeya/DimensionThree/Plank/PlankEnvelopeWindow.lean` is needed,
since `Kakeya.comparablePlankEnvelope` asks for the unit ball and the Part-(B) datum cannot
supply it. -/
theorem exists_collarPresentable_prop51_output
    (hδ0 : 0 < δ) (hδhalf : (δ : ℝ) ≤ 1 / 2) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδa : δ ≤ a)
    (hball : ∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 1)
    (hmass : 0 < ∑ i ∈ q, volume (T i).shade)
    (hsmall : δ + 2 * a ≤ 1)
    (hcfne : ∀ x ∈ D.factor.cells, (D.factor.coarseFibre x).Nonempty)
    {Cw : ℝ≥0}
    (hdimK : ∀ x ∈ D.factor.cells, IsPlankOfDimensions Cw a b (D.factor.body x)) :
    ∃ (Cs : ℝ≥0)
      (O : ShadedBody.ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) ι D.factor.Cell),
      1 ≤ Cs ∧
      O.outerSet ⊆ D.factor.cells ∧
      (∀ j ∈ O.outerSet,
        IsCollarPresentable plankWindowRadius Cw a b (D.factor.body j) (O.outerBody j)) ∧
      ShadedBody.IsRefinement O.innerSet O.innerBody q (fun i => (T i).toShadedBody) ∧
      (∀ j, O.fiber j ⊆ D.fineFibre j) ∧
      (∀ j ∈ O.outerSet,
        ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
          ≤ (Cs : ENNReal) * ShadedBody.multiplicity O.outerSet O.outerBody
              * ShadedBody.multiplicity (O.fiber j) O.innerBody) := by
  classical
  set input := D.section6SelectScaleInput hδ0 hδhalf hδa le_rfl hball hmass with hinput
  have Q : ShadedBody.FactoringAndMultPropCoreSelectScaleResult
      (C := ((remark53ThickConst Cfib CF : ℝ≥0) : ENNReal))
      D.toFineProp51Family input.hδ input.hdisc input.volumeRatio input.hδB input.hupper
        input.hmass :=
    D.prop51SelectScaleOfDatum input hδ0 hρ0 hρ1 hsmall hcfne
  have href1 := Q.selection_refinement D.toFineProp51Family input.hδ input.hdisc
    input.volumeRatio input.hδB input.hupper input.hmass
  have hcore := Q.core
  have href2 := hcore.refinement
  have hsplit := hcore.multiplicity_product
  have houtsub := hcore.outerSet_subset
  -- the outer-scale selection constant is nonzero
  set selC : ℝ≥0 := ShadedBody.outerScaleSelectionConstant δ a with hselC
  have hselpos : 0 < (selC : ENNReal) * ∑ i ∈ (ShadedBody.selectedOuterScaleFamily
      D.toFineProp51Family input.hδ input.hdisc input.hδB input.hupper input.hmass).innerSet,
      volume ((ShadedBody.selectedOuterScaleFamily D.toFineProp51Family input.hδ input.hdisc
        input.hδB input.hupper input.hmass).innerBody i).shade :=
    input.hmass.trans_le Q.selection_mass
  have hsel0 : (selC : ENNReal) ≠ 0 := (pos_of_mul_pos_left hselpos (by positivity)).ne'
  have hsel0' : selC ≠ 0 := by
    intro h
    exact hsel0 (by rw [h]; simp)
  have hseltop : (selC : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- the selected family's outer indices are cells of the datum
  have hsubSelected : (ShadedBody.selectedOuterScaleFamily D.toFineProp51Family input.hδ
      input.hdisc input.hδB input.hupper input.hmass).outerSet ⊆ D.factor.cells := by
    simpa [ShadedBody.selectedOuterScaleFamily,
      ShadedBody.FactorFamily.restrictOuter_outerSet] using
      ((ShadedBody.outerScaleSelection D.toFineProp51Family input.hδ input.hdisc
        input.hδB input.hupper input.hmass).selected_subset.trans
          D.toFineProp51Family.innerSet_image_parent_subset_outerSet)
  set prodC : ℝ≥0 := ShadedBody.factoringCoreAtScaleUniformProductConstant
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
    (ShadedBody.selectedOuterScaleFamily D.toFineProp51Family input.hδ input.hdisc
      input.hδB input.hupper input.hmass).innerSet.card
    (input.volumeRatio.restrictOuter _
      ((ShadedBody.outerScaleSelection D.toFineProp51Family input.hδ input.hdisc
        input.hδB input.hupper input.hmass).selected_subset.trans
          D.toFineProp51Family.innerSet_image_parent_subset_outerSet)).exponent
    (ShadedBody.selectedOuterScale D.toFineProp51Family input.hδ input.hdisc
      input.hδB input.hupper input.hmass) with hprodC
  -- the window and plank-dimension inputs, on the retained cells
  have hwin : ∀ j ∈ (ShadedBody.selectedOuterScaleFamily D.toFineProp51Family input.hδ
      input.hdisc input.hδB input.hupper input.hmass).outerSet,
      (((ShadedBody.selectedOuterScaleFamily D.toFineProp51Family input.hδ input.hdisc
        input.hδB input.hupper input.hmass).outerBody j).carrier
        : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ Metric.closedBall 0 ((plankWindowRadius : ℝ≥0) : ℝ) := by
    intro j hj
    exact D.body_carrier_subset_window (hsubSelected hj)
  have hdimSel : ∀ j ∈ (ShadedBody.selectedOuterScaleFamily D.toFineProp51Family input.hδ
      input.hdisc input.hδB input.hupper input.hmass).outerSet,
      IsPlankOfDimensions Cw a b ((ShadedBody.selectedOuterScaleFamily D.toFineProp51Family
        input.hδ input.hdisc input.hδB input.hupper input.hmass).outerBody j) := by
    intro j hj
    exact hdimK j (hsubSelected hj)
  have hpres := isCollarPresentable_outerThickFamilyAtScale
    (ShadedBody.selectedOuterScaleFamily D.toFineProp51Family input.hδ input.hdisc
      input.hδB input.hupper input.hmass)
    input.hδ (input.hdisc.restrictOuter _)
    (input.volumeRatio.restrictOuter _
      ((ShadedBody.outerScaleSelection D.toFineProp51Family input.hδ input.hdisc
        input.hδB input.hupper input.hmass).selected_subset.trans
          D.toFineProp51Family.innerSet_image_parent_subset_outerSet))
    (ShadedBody.selectedOuterScale D.toFineProp51Family input.hδ input.hdisc
      input.hδB input.hupper input.hmass) Q.scale_pos hcore hwin hdimSel
  -- the fibres of the constructed output sit inside the datum's own fine fibres
  have hfibsub := fun j =>
    (fiber_outerThickFamilyAtScale_subset
      (ShadedBody.selectedOuterScaleFamily D.toFineProp51Family input.hδ input.hdisc
        input.hδB input.hupper input.hmass)
      input.hδ (input.hdisc.restrictOuter _)
      (input.volumeRatio.restrictOuter _
        ((ShadedBody.outerScaleSelection D.toFineProp51Family input.hδ input.hdisc
          input.hδB input.hupper input.hmass).selected_subset.trans
            D.toFineProp51Family.innerSet_image_parent_subset_outerSet))
      (ShadedBody.selectedOuterScale D.toFineProp51Family input.hδ input.hdisc
        input.hδB input.hupper input.hmass) Q.scale_pos hcore j).trans
      ((fiber_restrictOuter_subset D.toFineProp51Family
        (ShadedBody.outerScaleSelection D.toFineProp51Family input.hδ input.hdisc
          input.hδB input.hupper input.hmass).selected j).trans
        (le_of_eq (D.toFineProp51Family_fiber j)))
  refine ⟨max 1 (selC * prodC), _, le_max_left _ _,
    houtsub.trans hsubSelected, hpres, href2.1.trans href1.1, hfibsub, ?_⟩
  intro j hj
  have hstep1 : ((selC : ENNReal))⁻¹ * ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
      ≤ ShadedBody.multiplicity (ShadedBody.selectedOuterScaleFamily D.toFineProp51Family
          input.hδ input.hdisc input.hδB input.hupper input.hmass).innerSet
        (ShadedBody.selectedOuterScaleFamily D.toFineProp51Family input.hδ input.hdisc
          input.hδB input.hupper input.hmass).innerBody := by
    have h := href1.mul_multiplicity_le
    rwa [ENNReal.coe_inv hsel0'] at h
  have hstep2 := hsplit j hj
  have hcancel : (selC : ENNReal) * ((selC : ENNReal))⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hsel0 hseltop
  calc ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
      = (selC : ENNReal) * (((selC : ENNReal))⁻¹
          * ShadedBody.multiplicity q (fun i => (T i).toShadedBody)) := by
        rw [← mul_assoc, hcancel, one_mul]
    _ ≤ (selC : ENNReal) * ((prodC : ENNReal)
          * ShadedBody.multiplicity _ _ * ShadedBody.multiplicity _ _) := by
        exact mul_le_mul_left' (le_trans hstep1 hstep2) _
    _ = ((selC : ENNReal) * (prodC : ENNReal))
          * ShadedBody.multiplicity _ _ * ShadedBody.multiplicity _ _ :=
        mulReassoc4 _ _ _ _
    _ ≤ ((max 1 (selC * prodC) : ℝ≥0) : ENNReal)
          * ShadedBody.multiplicity _ _ * ShadedBody.multiplicity _ _ := by
        gcongr
        rw [← ENNReal.coe_mul]
        exact ENNReal.coe_le_coe.mpr (le_max_right _ _)

open Classical in
/-- **The Part-(B) Proposition-5.1 multiplicity split, on exact `a × b × 1` shaded planks.**

This is the statement the Section-6 assembly wants and did not have.  The outer family is a genuine
`Kakeya.ShadedPlank a b hab hb1`-valued family, in the fixed radius-`4` Section-6 window, carrying
Katz--Tao with two absolute losses, and the multiplicity split is the *same* inequality as over the
actual cell bodies: the common homothety leaves `Kakeya.ShadedBody.multiplicity` untouched, and
nothing is clipped.

The fullness transport is `Kakeya.le_fullness_collarPlank` and its summed form
`Kakeya.collarPlank_sum_fullness_transport`, applied at the presentation data returned by
`Kakeya.Section6PartBData.exists_collarPresentable_prop51_output`; it is stated separately because
the Proposition-5.1 fullness clause is quadratic in the fine fullness and its constant is best left
where it is. -/
theorem exists_plank_presented_prop51_split
    (hδ0 : 0 < δ) (hδhalf : (δ : ℝ) ≤ 1 / 2) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδa : δ ≤ a) (ha0 : 0 < a) (hb0 : 0 < b)
    (hball : ∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 1)
    (hmass : 0 < ∑ i ∈ q, volume (T i).shade)
    (hsmall : δ + 2 * a ≤ 1)
    (hcfne : ∀ x ∈ D.factor.cells, (D.factor.coarseFibre x).Nonempty)
    {Cw : ℝ≥0} (hCw : 1 ≤ Cw)
    (hdimK : ∀ x ∈ D.factor.cells, IsPlankOfDimensions Cw a b (D.factor.body x)) :
    ∃ (Cs : ℝ≥0) (ts : Finset D.factor.Cell) (W : D.factor.Cell → ShadedPlank a b hab hb1)
      (isub : Finset ι) (Oin : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (fib : D.factor.Cell → Finset ι),
      1 ≤ Cs ∧
      ts ⊆ D.factor.cells ∧
      (∀ j ∈ ts, ((W j).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ Metric.closedBall 0 ((plankWindowRadius : ℝ≥0) : ℝ)) ∧
      ShadedBody.IsRefinement isub Oin q (fun i => (T i).toShadedBody) ∧
      (∀ j, fib j ⊆ D.fineFibre j) ∧
      ConvexSpaceBody.IsKatzTao ts (fun j => (W j).toConvexSpaceBody)
        ((flatPrismEnvelopeVolumeRatio.C
            (windowPlankEnvelope.windowConst plankWindowRadius Cw) : ENNReal)
          * ((Metric.volume_comparison.C 3 : ENNReal) * (C₀ : ENNReal))) ∧
      (∀ j ∈ ts,
        ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
          ≤ (Cs : ENNReal) * ShadedBody.multiplicity ts (fun j => (W j).toShadedBody)
              * ShadedBody.multiplicity (fib j) Oin) := by
  classical
  obtain ⟨Cs, O, hCs, htssub, hpres, href, hfibsub, hsplit⟩ :=
    D.exists_collarPresentable_prop51_output hδ0 hδhalf hρ0 hρ1 hδa hball hmass hsmall hcfne
      hdimK
  have hR : (1 : ℝ≥0) ≤ plankWindowRadius := one_le_plankWindowRadius
  refine ⟨Cs, O.outerSet,
    fun j => collarPlank hR hCw hab hb1 (D.factor.body j) (O.outerBody j),
    O.innerSet, O.innerBody, O.fiber, hCs, htssub, ?_, href, hfibsub, ?_, ?_⟩
  · intro j hj
    exact collarPlank_carrier_subset_window hR hCw hab hb1 (O.outerBody j)
      (D.body_carrier_subset_window (htssub hj))
  · refine isKatzTao_collarPlank hR hCw hab hb1 ha0 hb0 O.outerSet
      (fun j => D.factor.body j) O.outerBody hpres
      (fun j hj => hdimK j (htssub hj)) ?_
    exact D.factor.isKatzTao.subset htssub
  · intro j hj
    have hmul : ShadedBody.multiplicity O.outerSet
        (fun j => (collarPlank hR hCw hab hb1 (D.factor.body j) (O.outerBody j)).toShadedBody)
        = ShadedBody.multiplicity O.outerSet O.outerBody :=
      multiplicity_collarPlank hR hCw hab hb1 O.outerSet (fun j => D.factor.body j)
        O.outerBody hpres
    rw [hmul]
    exact hsplit j hj

end Section6PartBData

end Kakeya

end

end
