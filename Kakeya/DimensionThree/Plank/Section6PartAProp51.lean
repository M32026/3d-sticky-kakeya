/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Section6PartAFactorData
public import Kakeya.DimensionThree.Plank.FrostmanPlankEstimate

/-!
# The corrected Proposition 5.1 output for Proposition 6.6(A)

The actual outer bodies produced parent by parent in Section 6 need not have a common shortest
scale.  Consequently this adapter uses the mass-weighted `SelectScale` wrapper, rather than
pretending that `ComparableBodyFactorization` supplies `OuterIsAtScale`.  The selected family keeps
complete fibres.  Its logarithmic mass loss is carried explicitly both in the refinement back to
the original fine family and in the squared fullness estimate.

Only Proposition 5.1 is assembled here.  Representative-plank geometry belongs to
`Section6PartAFactorData`; the master-scale Lemma 6.1/6.4 estimates remain separate hypotheses of
the eventual Proposition 6.6(A) consumer.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya

universe u_section6PartAOutput

namespace Section6PartAFactorData

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type u_section6PartAOutput} {q : Finset ι} {δ ρ : ℝ≥0}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {Cpar : ℝ≥0} {PS : ExternalParentSystem q (fun i ↦ (T i).toTube) ρ Cpar}
  {CFib : ENNReal} {C₀ Cmass Cdim B : ℝ≥0}
  (D : Section6PartAFactorData a b hab hb1 q T PS CFib C₀ Cmass Cdim B)

/-- The complete-fibre family retained by the outer-scale pigeonhole. -/
noncomputable def selectedFamily :
    ShadedBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) ι D.core.Cell := by
  letI := D.core.decEqCell
  exact ShadedBody.selectedOuterScaleFamily D.core.toFactorFamily D.input.hδ D.input.hdisc
    D.input.hδB D.input.hupper D.input.hmass

/-- The common shortest scale selected by shading mass. -/
noncomputable def selectedScale : NNReal := by
  letI := D.core.decEqCell
  exact ShadedBody.selectedOuterScale D.core.toFactorFamily D.input.hδ D.input.hdisc
    D.input.hδB D.input.hupper D.input.hmass

/-- The outer/inner volume-ratio datum restricted to the selected complete fibres. -/
noncomputable def selectedVolumeRatio : ShadedBody.OuterInnerVolumeRatio D.selectedFamily := by
  letI := D.core.decEqCell
  exact D.input.volumeRatio.restrictOuter _
    ((ShadedBody.outerScaleSelection D.core.toFactorFamily D.input.hδ D.input.hdisc
      D.input.hδB D.input.hupper D.input.hmass).selected_subset.trans
        D.core.toFactorFamily.innerSet_image_parent_subset_outerSet)

/-- The thick, productive outer family returned by the fixed-scale core after selection. -/
noncomputable def thickOutput :
    ShadedBody.ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) ι D.core.Cell := by
  letI := D.core.decEqCell
  exact ShadedBody.outerThickFamilyAtScale D.selectedFamily D.input.hδ
    (D.input.hdisc.restrictOuter _)
    D.selectedVolumeRatio
    D.selectedScale D.prop51CoreSelectScale.scale_pos

/-- The Section-6 presentation of the selected thick shade on the exact representative plank. -/
noncomputable def outerPlank (x : D.core.Cell) : ShadedPlank a b hab hb1 :=
  D.core.outerView D.thickOutput x

@[simp] theorem outerPlank_toPrism3D (x : D.core.Cell) :
    (D.outerPlank x).toPrism3D = D.core.repr x := rfl

/-- The fixed decidable equality carried by the aggregated cell data. -/
local instance instDecidableEqCellCore : DecidableEq D.core.Cell := D.core.decEqCell

/-- Decidable equality for the external coarse-parent indices. -/
local instance instDecidableEqParent : DecidableEq PS.Parent := Classical.decEq PS.Parent

/-- The logarithmic loss paid when the outer bodies are restricted to one common scale. -/
noncomputable def selectionConstant (δ B : NNReal) : NNReal :=
  ShadedBody.outerScaleSelectionConstant δ B

/-- The uniform refinement constant in the fixed-scale Proposition 5.1 core. -/
noncomputable def refinementConstant : NNReal :=
  ShadedBody.factoringCoreAtScaleUniformRefinementConstant 3 D.selectedFamily.innerSet.card
    D.selectedVolumeRatio.exponent D.selectedScale

/-- The uniform aggregate-fullness constant in the fixed-scale Proposition 5.1 core. -/
noncomputable def fullnessConstant : NNReal :=
  ShadedBody.factoringCoreAtScaleUniformFullnessConstant 3 D.selectedFamily.innerSet.card
    D.selectedVolumeRatio.exponent D.selectedScale

/-- The uniform multiplicity-product constant in the fixed-scale Proposition 5.1 core. -/
noncomputable def productConstant : NNReal :=
  ShadedBody.factoringCoreAtScaleUniformProductConstant 3 D.selectedFamily.innerSet.card
    D.selectedVolumeRatio.exponent D.selectedScale

/-- The corrected Proposition 5.1 output used by Proposition 6.6(A).

The scale-selection loss is visible twice: `selection_refinement` is the bridge from the selected
complete-fibre family back to the original fine family, while `selection_fullness` is the
corresponding density statement.  In particular `multiplicity_product` starts with the original
fine family, not merely the family on the selected outer scale. -/
structure Prop51Output : Prop where
  /-- Positive input shading mass produces a nonempty outer plank family. -/
  outerSet_nonempty : D.thickOutput.outerSet.Nonempty
  /-- Every output cell is one of the original dependent-sum cells. -/
  outerSet_subset : D.thickOutput.outerSet ⊆ D.core.cells
  /-- Output representative planks lie in the common Section-6 window. -/
  outer_window : ∀ x ∈ D.thickOutput.outerSet,
    (D.outerPlank x).toConvexSpaceBody ≤ plankWindow
  /-- The output representative planks are pairwise essentially distinct. -/
  outer_pairwise : (D.thickOutput.outerSet : Set D.core.Cell).Pairwise
    (fun x y ↦ _root_.IsEssentiallyDistinct
      (D.outerPlank x).carrier (D.outerPlank y).carrier)
  /-- Output cells retain their original occupied coarse-parent labels. -/
  parent_mem : ∀ x ∈ D.thickOutput.outerSet, D.parent x ∈ PS.parents
  /-- Every output cell contains a fine tube assigned to its own coarse parent. -/
  occupancy : ∀ x ∈ D.thickOutput.outerSet, ∃ i ∈ q,
    PS.assign i = D.parent x ∧ (T i).toConvexSpaceBody ≤ D.core.body x
  /-- The actual factor body lies in its representative plank. -/
  body_le_outerPlank : ∀ x ∈ D.thickOutput.outerSet,
    D.core.body x ≤ (D.outerPlank x).toConvexSpaceBody
  /-- Katz--Tao control is retained separately on every original coarse-parent fibre. -/
  parent_katzTao : ∀ k ∈ PS.parents,
    IsKatzTao (D.thickOutput.outerSet.filter fun x ↦ D.parent x = k)
      (fun x ↦ (D.outerPlank x).toConvexSpaceBody) (C₀ : ENNReal)
  /-- The selected complete-fibre family refines the original fine family with the explicit
  scale-selection loss. -/
  selection_refinement :
    ShadedBody.IsCRefinement D.selectedFamily.innerSet D.selectedFamily.innerBody
      D.core.toFactorFamily.innerSet D.core.toFactorFamily.innerBody (selectionConstant δ B)⁻¹
  /-- The same scale-selection loss controls the fullness of the selected fine family. -/
  selection_fullness : ((((selectionConstant δ B)⁻¹ : NNReal) : ENNReal)) *
      (ShadedBody.fullness D.core.toFactorFamily.innerSet D.core.toFactorFamily.innerBody : ENNReal)
    ≤ (ShadedBody.fullness D.selectedFamily.innerSet D.selectedFamily.innerBody : ENNReal)
  /-- The final fine shading is a refinement of the selected complete-fibre family. -/
  core_refinement :
    ShadedBody.IsCRefinement D.thickOutput.innerSet D.thickOutput.innerBody
      D.selectedFamily.innerSet D.selectedFamily.innerBody (refinementConstant D)
  /-- Aggregate outer fullness, before the Section-6 representative-plank reshape. -/
  core_fullness : (fullnessConstant D : ENNReal) * CFib⁻¹ *
      (ShadedBody.fullness D.selectedFamily.innerSet D.selectedFamily.innerBody : ENNReal) ^ 2 *
        (∑ x ∈ D.thickOutput.outerSet, volume (D.thickOutput.outerBody x).carrier) ≤
      ∑ x ∈ D.thickOutput.outerSet, volume (D.thickOutput.outerBody x).shade
  /-- The multiplicity split begins with the original fine family.  The factor on the left is
  exactly the single logarithmic loss from selecting an outer scale. -/
  multiplicity_product : ∀ x ∈ D.thickOutput.outerSet,
    ((((selectionConstant δ B)⁻¹ : NNReal) : ENNReal)) *
        ShadedBody.multiplicity D.core.toFactorFamily.innerSet D.core.toFactorFamily.innerBody ≤
      (productConstant D : ENNReal) *
        ShadedBody.multiplicity D.thickOutput.outerSet
          (fun y ↦ (D.outerPlank y).toShadedBody) *
        ShadedBody.multiplicity (D.thickOutput.fiber x) D.thickOutput.innerBody
  /-- The final fine shade lies in the thick outer shade of its retained parent. -/
  shading_containment : ∀ i ∈ D.thickOutput.innerSet,
    (D.thickOutput.innerBody i).shade ⊆
      (D.outerPlank (D.thickOutput.parent i)).shade
  /-- Every output fibre has positive shaded-union measure. -/
  fiber_nonnull : ∀ x ∈ D.thickOutput.outerSet,
    volume (ShadedBody.iUnionShade (D.thickOutput.fiber x) D.thickOutput.innerBody) ≠ 0

/-- Assemble the corrected Proposition 5.1 output for Proposition 6.6(A).

This theorem replaces the former Section-6 identity shell: it invokes `CoreSelectScale`, pays the
scale-selection loss in both density and multiplicity, and then re-presents the thick outer shades
on the exact Section-6 planks without changing them. -/
theorem prop51Output : D.Prop51Output := by
  classical
  letI := D.core.decEqCell
  let Q := D.prop51CoreSelectScale
  have hsubSelected : D.selectedFamily.outerSet ⊆ D.core.cells := by
    simpa [selectedFamily, ShadedBody.selectedOuterScaleFamily,
      ShadedBody.FactorFamily.restrictOuter_outerSet] using
      ((ShadedBody.outerScaleSelection D.core.toFactorFamily D.input.hδ D.input.hdisc
        D.input.hδB D.input.hupper D.input.hmass).selected_subset.trans
          D.core.toFactorFamily.innerSet_image_parent_subset_outerSet)
  have hsub : D.thickOutput.outerSet ⊆ D.core.cells :=
    Q.core.outerSet_subset.trans hsubSelected
  have hcar : ∀ x ∈ D.thickOutput.outerSet,
      (D.thickOutput.outerBody x).toConvexSpaceBody =
        (D.core.body x).cthickening (D.core.body x).scale := by
    intro x hx
    have hs : (D.thickOutput.outerBody x).toConvexSpaceBody =
        (D.selectedFamily.outerBody x).cthickening (D.selectedFamily.outerBody x).scale := by
      simpa only [thickOutput, selectedFamily, selectedVolumeRatio, selectedScale] using
        Q.core.outer_carrier x
    simpa [selectedFamily, ShadedBody.selectedOuterScaleFamily,
      ShadedBody.FactorFamily.restrictOuter, Section6CoreFactorData.toFactorFamily] using hs
  have hshade : ∀ x ∈ D.thickOutput.outerSet,
      (D.outerPlank x).shade = (D.thickOutput.outerBody x).shade :=
    D.core.shade_outerView_of_mem D.thickOutput hsub hcar
  have hselectedMass : 0 < ∑ i ∈ D.selectedFamily.innerSet,
      volume (D.selectedFamily.innerBody i).shade := by
    have hprod : 0 < (selectionConstant δ B : ENNReal) *
        ∑ i ∈ D.selectedFamily.innerSet, volume (D.selectedFamily.innerBody i).shade :=
      D.input.hmass.trans_le (by
        simpa [selectionConstant, selectedFamily] using Q.selection_mass)
    exact pos_of_mul_pos_right hprod (by positivity)
  refine
    { outerSet_nonempty := Q.core.outerSet_nonempty_of_input_mass_pos hselectedMass
      outerSet_subset := hsub
      outer_window := ?_
      outer_pairwise := ?_
      parent_mem := fun x hx ↦ D.parent_mem x (hsub hx)
      occupancy := fun x hx ↦ D.occupancy x (hsub hx)
      body_le_outerPlank := ?_
      parent_katzTao := ?_
      selection_refinement := ?_
      selection_fullness := ?_
      core_refinement := ?_
      core_fullness := ?_
      multiplicity_product := ?_
      shading_containment := ?_
      fiber_nonnull := ?_ }
  · intro x hx
    simpa [outerPlank] using D.repr_window x (hsub hx)
  · exact Set.Pairwise.mono (Finset.coe_subset.mpr hsub) (by
      simpa [outerPlank] using D.repr_pairwise)
  · intro x hx
    exact (ConvexSpaceBody.self_le_cthickening _ _).trans (D.core.cthickening_le_repr x (hsub hx))
  · intro k hk
    have hfilter : D.thickOutput.outerSet.filter (fun x ↦ D.parent x = k) ⊆
        D.core.cells.filter (fun x ↦ D.parent x = k) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hsub hx.1, hx.2⟩
    simpa [outerPlank] using (D.repr_katzTao k hk).subset hfilter
  · simpa [selectionConstant, selectedFamily] using
      Q.selection_refinement D.core.toFactorFamily D.input.hδ D.input.hdisc
        D.input.volumeRatio D.input.hδB D.input.hupper D.input.hmass
  · simpa [selectionConstant, selectedFamily] using
      Q.selection_fullness D.core.toFactorFamily D.input.hδ D.input.hdisc
        D.input.volumeRatio D.input.hδB D.input.hupper D.input.hmass
  · simpa [refinementConstant, thickOutput, selectedFamily, selectedVolumeRatio,
      selectedScale] using Q.core.refinement
  · simpa [fullnessConstant, thickOutput, selectedFamily, selectedVolumeRatio,
      selectedScale] using Q.core.thick_fullness
  · intro x hx
    calc
      ((((selectionConstant δ B)⁻¹ : NNReal) : ENNReal)) *
          ShadedBody.multiplicity D.core.toFactorFamily.innerSet
            D.core.toFactorFamily.innerBody
          ≤ ShadedBody.multiplicity D.selectedFamily.innerSet D.selectedFamily.innerBody :=
        (by simpa [selectionConstant, selectedFamily] using
          (Q.selection_refinement D.core.toFactorFamily D.input.hδ D.input.hdisc
            D.input.volumeRatio D.input.hδB D.input.hupper D.input.hmass).mul_multiplicity_le)
      _ ≤ (productConstant D : ENNReal) *
          ShadedBody.multiplicity D.thickOutput.outerSet D.thickOutput.outerBody *
          ShadedBody.multiplicity (D.thickOutput.fiber x) D.thickOutput.innerBody := by
        simpa [productConstant, thickOutput, selectedFamily, selectedVolumeRatio,
          selectedScale] using Q.core.multiplicity_product x hx
      _ = (productConstant D : ENNReal) *
          ShadedBody.multiplicity D.thickOutput.outerSet
            (fun y ↦ (D.outerPlank y).toShadedBody) *
          ShadedBody.multiplicity (D.thickOutput.fiber x) D.thickOutput.innerBody := by
        simpa [outerPlank] using congrArg
          (fun μ ↦ (productConstant D : ENNReal) * μ *
            ShadedBody.multiplicity (D.thickOutput.fiber x) D.thickOutput.innerBody)
          (D.core.multiplicity_outerView D.thickOutput hsub hcar).symm
  · intro i hi
    have hc : (D.thickOutput.innerBody i).shade ⊆
        (D.thickOutput.outerBody (D.thickOutput.parent i)).shade := by
      simpa [thickOutput, selectedFamily, selectedVolumeRatio, selectedScale,
        ShadedBody.selectedOuterScaleFamily] using Q.core.shading_containment i hi
    rw [hshade (D.thickOutput.parent i) (D.thickOutput.parent_mem i hi)]
    exact hc
  · intro x hx
    simpa [thickOutput, selectedFamily, selectedVolumeRatio, selectedScale,
      ShadedBody.selectedOuterScaleFamily] using Q.core.fiber_nonnull x hx

/-- The multiplicity product with the scale-selection loss moved to the right-hand side.

This is the form consumed by Section 6: it starts with the original fine family, and pays exactly
one copy of the logarithmic outer-scale selection constant. -/
theorem Prop51Output.multiplicity_product_original (P : D.Prop51Output)
    (x : D.core.Cell) (hx : x ∈ D.thickOutput.outerSet) :
    ShadedBody.multiplicity D.core.toFactorFamily.innerSet
        D.core.toFactorFamily.innerBody ≤
      (selectionConstant δ B : ENNReal) * (productConstant D : ENNReal) *
        ShadedBody.multiplicity D.thickOutput.outerSet
          (fun y ↦ (D.outerPlank y).toShadedBody) *
        ShadedBody.multiplicity (D.thickOutput.fiber x) D.thickOutput.innerBody := by
  have hprod : 0 < (selectionConstant δ B : ENNReal) *
      ∑ i ∈ D.selectedFamily.innerSet, volume (D.selectedFamily.innerBody i).shade :=
    D.input.hmass.trans_le (by
      simpa [selectionConstant, selectedFamily] using D.prop51CoreSelectScale.selection_mass)
  have hsel0 : (selectionConstant δ B : ENNReal) ≠ 0 := by
    exact (pos_of_mul_pos_left hprod (by positivity)).ne'
  have hsel0nn : selectionConstant δ B ≠ 0 := ENNReal.coe_ne_zero.mp hsel0
  have hseltop : (selectionConstant δ B : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hcancel : (selectionConstant δ B : ENNReal) *
      ((((selectionConstant δ B)⁻¹ : NNReal) : ENNReal)) = 1 := by
    rw [ENNReal.coe_inv hsel0nn]
    exact ENNReal.mul_inv_cancel hsel0 hseltop
  calc
    ShadedBody.multiplicity D.core.toFactorFamily.innerSet
        D.core.toFactorFamily.innerBody =
        (selectionConstant δ B : ENNReal) *
          ((((selectionConstant δ B)⁻¹ : NNReal) : ENNReal)) *
          ShadedBody.multiplicity D.core.toFactorFamily.innerSet
            D.core.toFactorFamily.innerBody := by rw [hcancel, one_mul]
    _ = (selectionConstant δ B : ENNReal) *
          (((((selectionConstant δ B)⁻¹ : NNReal) : ENNReal)) *
            ShadedBody.multiplicity D.core.toFactorFamily.innerSet
              D.core.toFactorFamily.innerBody) := by ring
    _ ≤ (selectionConstant δ B : ENNReal) *
          ((productConstant D : ENNReal) *
            ShadedBody.multiplicity D.thickOutput.outerSet
              (fun y ↦ (D.outerPlank y).toShadedBody) *
            ShadedBody.multiplicity (D.thickOutput.fiber x) D.thickOutput.innerBody) := by
      exact mul_le_mul_right (P.multiplicity_product x hx) _
    _ = (selectionConstant δ B : ENNReal) * (productConstant D : ENNReal) *
          ShadedBody.multiplicity D.thickOutput.outerSet
            (fun y ↦ (D.outerPlank y).toShadedBody) *
          ShadedBody.multiplicity (D.thickOutput.fiber x) D.thickOutput.innerBody := by ring

/-- Transfer the aggregate fullness inequality from the enlarged actual bodies to the exact
representative planks.  The only loss is the declared volume-comparison constant `Cdim`; the shade
and therefore the numerator are unchanged. -/
theorem Prop51Output.plank_fullness (P : D.Prop51Output) :
    (fullnessConstant D : ENNReal) * CFib⁻¹ *
        (ShadedBody.fullness D.selectedFamily.innerSet D.selectedFamily.innerBody : ENNReal) ^ 2 *
        (∑ x ∈ D.thickOutput.outerSet, volume (D.outerPlank x).carrier) ≤
      (Cdim : ENNReal) *
        ∑ x ∈ D.thickOutput.outerSet, volume (D.outerPlank x).shade := by
  classical
  letI := D.core.decEqCell
  have hcar : ∀ x ∈ D.thickOutput.outerSet,
      (D.thickOutput.outerBody x).toConvexSpaceBody =
        (D.core.body x).cthickening (D.core.body x).scale := by
    intro x hx
    have hs : (D.thickOutput.outerBody x).toConvexSpaceBody =
        (D.selectedFamily.outerBody x).cthickening (D.selectedFamily.outerBody x).scale := by
      simpa only [thickOutput, selectedFamily, selectedVolumeRatio, selectedScale] using
        D.prop51CoreSelectScale.core.outer_carrier x
    simpa [selectedFamily, ShadedBody.selectedOuterScaleFamily,
      ShadedBody.FactorFamily.restrictOuter, Section6CoreFactorData.toFactorFamily] using hs
  have hsum : (∑ x ∈ D.thickOutput.outerSet, volume (D.outerPlank x).carrier) ≤
      (Cdim : ENNReal) *
        ∑ x ∈ D.thickOutput.outerSet, volume (D.thickOutput.outerBody x).carrier := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun x hx ↦
      D.core.volume_outerView_le D.thickOutput (P.outerSet_subset hx) (hcar x hx)
  calc
    (fullnessConstant D : ENNReal) * CFib⁻¹ *
          (ShadedBody.fullness D.selectedFamily.innerSet
            D.selectedFamily.innerBody : ENNReal) ^ 2 *
          (∑ x ∈ D.thickOutput.outerSet, volume (D.outerPlank x).carrier)
        ≤ (fullnessConstant D : ENNReal) * CFib⁻¹ *
          (ShadedBody.fullness D.selectedFamily.innerSet
            D.selectedFamily.innerBody : ENNReal) ^ 2 *
          ((Cdim : ENNReal) *
            ∑ x ∈ D.thickOutput.outerSet,
              volume (D.thickOutput.outerBody x).carrier) := by gcongr
    _ = (Cdim : ENNReal) *
          ((fullnessConstant D : ENNReal) * CFib⁻¹ *
            (ShadedBody.fullness D.selectedFamily.innerSet
              D.selectedFamily.innerBody : ENNReal) ^ 2 *
            ∑ x ∈ D.thickOutput.outerSet,
              volume (D.thickOutput.outerBody x).carrier) := by ring
    _ ≤ (Cdim : ENNReal) *
          ∑ x ∈ D.thickOutput.outerSet,
            volume (D.thickOutput.outerBody x).shade :=
      by simpa [mul_comm] using
        (mul_le_mul_right P.core_fullness (Cdim : ENNReal))
    _ = (Cdim : ENNReal) *
          ∑ x ∈ D.thickOutput.outerSet, volume (D.outerPlank x).shade := by
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      exact congrArg volume (D.core.shade_outerView_of_mem D.thickOutput
        P.outerSet_subset hcar x hx).symm

/-- The representative-plank fullness estimate stated directly in terms of the original fine
family.  The scale-selection loss is squared, as required by Proposition 5.1 item 2. -/
theorem Prop51Output.plank_fullness_from_original (P : D.Prop51Output) :
    (fullnessConstant D : ENNReal) * CFib⁻¹ *
        (((selectionConstant δ B)⁻¹ : NNReal) : ENNReal) ^ 2 *
        (ShadedBody.fullness D.core.toFactorFamily.innerSet
          D.core.toFactorFamily.innerBody : ENNReal) ^ 2 *
        (∑ x ∈ D.thickOutput.outerSet, volume (D.outerPlank x).carrier) ≤
      (Cdim : ENNReal) *
        ∑ x ∈ D.thickOutput.outerSet, volume (D.outerPlank x).shade := by
  calc
    (fullnessConstant D : ENNReal) * CFib⁻¹ *
          (((selectionConstant δ B)⁻¹ : NNReal) : ENNReal) ^ 2 *
          (ShadedBody.fullness D.core.toFactorFamily.innerSet
            D.core.toFactorFamily.innerBody : ENNReal) ^ 2 *
          (∑ x ∈ D.thickOutput.outerSet, volume (D.outerPlank x).carrier)
        = (fullnessConstant D : ENNReal) * CFib⁻¹ *
          ((((selectionConstant δ B)⁻¹ : NNReal) : ENNReal) *
            (ShadedBody.fullness D.core.toFactorFamily.innerSet
              D.core.toFactorFamily.innerBody : ENNReal)) ^ 2 *
          (∑ x ∈ D.thickOutput.outerSet, volume (D.outerPlank x).carrier) := by ring
    _ ≤ (fullnessConstant D : ENNReal) * CFib⁻¹ *
          (ShadedBody.fullness D.selectedFamily.innerSet
            D.selectedFamily.innerBody : ENNReal) ^ 2 *
          (∑ x ∈ D.thickOutput.outerSet, volume (D.outerPlank x).carrier) := by
      gcongr
      simpa only [ENNReal.coe_inv] using P.selection_fullness
    _ ≤ (Cdim : ENNReal) *
          ∑ x ∈ D.thickOutput.outerSet, volume (D.outerPlank x).shade := P.plank_fullness

/-- Output cells of one coarse parent contained in a dilated thick-plank test body. -/
noncomputable def dilatedParentCells (C_NC : NNReal) (j : D.core.Cell) (θ : NNReal)
    (hθ1 : θ ≤ 1) (k : PS.Parent) : Finset D.core.Cell := by
  classical
  exact D.thickOutput.outerSet.filter fun x ↦
    ((D.outerPlank x).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (((Plank.thickened (D.outerPlank j).toPrism3D θ hθ1).toPrismNDim.dilation C_NC).carrier :
        Set (EuclideanSpace ℝ (Fin 3))) ∧ D.parent x = k

/-- Proposition 5.1 together with the two elementary Section-6 consequences used by 6.6(A).

The local dilated count is derived from the parentwise Katz--Tao datum; it is not attributed to
Proposition 5.1.  Likewise `δ ≤ a` is derived from an occupied fine tube inside an actual body and
the actual-body-to-representative containment. -/
structure CombinedOutput (C_NC : NNReal) : Prop extends D.Prop51Output where
  /-- Occupancy forces the fine tube radius below the representative plank's thin width. -/
  delta_le_thinWidth : δ ≤ a
  /-- The parentwise count at the exact dilated thick-plank test body. -/
  parentwise_dilated_count : ∀ j ∈ D.thickOutput.outerSet, ∀ (θ : NNReal),
    a / b ≤ θ → ∀ (hθ1 : θ ≤ 1), ∀ k ∈ PS.parents,
      ((D.dilatedParentCells C_NC j θ hθ1 k).card : NNReal)
        ≤ C₀ * C_NC ^ 3 * (b / a) * θ

/-- Assemble the corrected 6.6(A) Proposition-5.1 interface. -/
theorem factoringAndMultPropCombined (C_NC : NNReal) (_hC_NC : 1 ≤ C_NC) :
    D.CombinedOutput C_NC := by
  classical
  letI := D.core.decEqCell
  let P := D.prop51Output
  have ha : 0 < a := by
    obtain ⟨x, hx⟩ := P.outerSet_nonempty
    obtain ⟨i, hi, _, hTi⟩ := P.occupancy x hx
    have hδa := le_thinWidth_of_tube_le_plank (T i).toTube (D.outerPlank x).toPrism3D
      (hTi.trans (P.body_le_outerPlank x hx))
    exact D.input.hδ.trans_le hδa
  refine { toProp51Output := P, delta_le_thinWidth := ?_, parentwise_dilated_count := ?_ }
  · obtain ⟨x, hx⟩ := P.outerSet_nonempty
    obtain ⟨i, hi, _, hTi⟩ := P.occupancy x hx
    exact le_thinWidth_of_tube_le_plank (T i).toTube (D.outerPlank x).toPrism3D
      (hTi.trans (P.body_le_outerPlank x hx))
  · intro j hj θ hθ hθ1 k hk
    have hKT := P.parent_katzTao k hk
    have hfilter :
        (D.thickOutput.outerSet.filter fun x ↦ D.parent x = k).filter (fun x ↦
          ((D.outerPlank x).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
            (((Plank.thickened (D.outerPlank j).toPrism3D θ hθ1).toPrismNDim.dilation
              C_NC).carrier : Set (EuclideanSpace ℝ (Fin 3)))) =
                D.dilatedParentCells C_NC j θ hθ1 k := by
      ext x
      simp only [Finset.mem_filter, dilatedParentCells]
      tauto
    rw [← hfilter]
    simpa [mul_assoc] using
      card_le_of_isKatzTao_dilatedThickening
        ha (ha.trans_le hab) (D.thickOutput.outerSet.filter fun x ↦ D.parent x = k)
        (fun x ↦ (D.outerPlank x).toPrism3D) hKT C_NC j hθ1

end Section6PartAFactorData

end Kakeya

end
