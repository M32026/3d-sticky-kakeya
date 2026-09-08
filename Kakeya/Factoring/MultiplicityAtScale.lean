/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.CoreAtScale

/-! # Corrected factoring and multiplicity proposition (GWZ Proposition 5.1), `CoreAtScale` form

This compatibility layer gives the seven blueprint items names close to the former interface.
The mathematical source is `factoringAndMultPropCoreAtScale` together with its counting extension
`factoringAndMultPropCombined`. The scale `w₁` and construction proofs are explicit, and the thick
and counting outer shadings are deliberately distinct.
-/

@[expose] public section

open MeasureTheory Convexity Kakeya
open scoped ENNReal NNReal

namespace ShadedBody

/-! Main's `CoreAtScale`-based rewrite of the Proposition 5.1 interface, kept verbatim in
its own namespace.  Twelve of its names (`outerFactoringFamily`, `outerFactoringIndex`,
...) also exist in `Kakeya/Factoring/Multiplicity.lean` with *different* definitions and
signatures -- that file implements the same interface over its own pipeline rather than
over `Kakeya.Factoring.CoreAtScale`.  The two cannot share a namespace, and neither has
been deleted: which one Section 5 keeps is an open decision for the author of
`wjq/lem5.1-core` (PR #1843).  Nothing consumes this namespace yet. -/
namespace AtScale

section FactoringAndMultiplicity

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [DecidableEq κ]

/-- The thick outer factoring family in the corrected Proposition 5.1. -/
noncomputable def outerFactoringFamily
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) : ShadedFactorFamily E ι κ :=
  outerThickFamilyAtScale F hδ hdisc D w₁ hw₁

/-- The exact counting outer family paired with `outerFactoringFamily`. -/
noncomputable def outerFactoringCountingFamily
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) : ShadedFactorFamily E ι κ :=
  outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁

/-- The retained productive outer indices. -/
noncomputable def outerFactoringIndex
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) : Finset κ :=
  (outerFactoringFamily F hδ hdisc D w₁ hw₁).outerSet

/-- The thick outer shaded bodies. -/
noncomputable def outerFactoringOuterShaded
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) : κ → ShadedBody E :=
  (outerFactoringFamily F hδ hdisc D w₁ hw₁).outerBody

/-- The final inner shaded bodies. -/
noncomputable def outerFactoringInner
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) : ι → ShadedBody E :=
  (outerFactoringFamily F hδ hdisc D w₁ hw₁).innerBody

/-- Uniform small constant in Item 1 of the corrected Proposition 5.1. -/
noncomputable def outerFactoringRefinementConstant
    (n M N : ℕ) (w₁ : NNReal) : NNReal :=
  factoringCoreAtScaleUniformRefinementConstant n M N w₁

/-- Uniform small constant in Item 2 of the corrected Proposition 5.1. -/
noncomputable def outerFactoringFullnessConstant
    (n M N : ℕ) (w₁ : NNReal) : NNReal :=
  factoringCoreAtScaleUniformFullnessConstant n M N w₁

/-- The one-sided counting multiplicity constant in Item 3 of the corrected Proposition 5.1. -/
def outerFactoringCountingMultiplicityConstant : NNReal := 2

/-- The dyadic comparison constant in Item 4 of the corrected Proposition 5.1. -/
def outerFactoringInnerMultiplicityConstant : ℕ := 2

/-- Uniform large constant in Item 5 of the corrected Proposition 5.1. -/
noncomputable def outerFactoringProductConstant
    (n M N : ℕ) (w₁ : NNReal) : NNReal :=
  factoringCoreAtScaleUniformProductConstant n M N w₁

/-- The unequal-radius ball comparison constant in Item 7 of the corrected Proposition 5.1. -/
noncomputable def outerFactoringBallComparisonConstant (n : ℕ) : NNReal :=
  4 * factoringStep5OverlapConstant n

/-- Structural clauses of the corrected fixed-scale construction. -/
theorem outerFactoringFamily_carrier
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    (outerFactoringFamily F hδ hdisc D w₁ hw₁).outerSet ⊆ F.outerSet ∧
      (outerFactoringFamily F hδ hdisc D w₁ hw₁).innerSet =
        {i ∈ F.innerSet |
          F.parent i ∈ (outerFactoringFamily F hδ hdisc D w₁ hw₁).outerSet} ∧
      (∀ j,
        ((outerFactoringFamily F hδ hdisc D w₁ hw₁).outerBody j).toConvexSpaceBody =
          (F.outerBody j).cthickening (F.outerBody j).scale) ∧
      ∀ i,
        ((outerFactoringFamily F hδ hdisc D w₁ hw₁).innerBody i).toConvexSpaceBody =
          (F.innerBody i).toConvexSpaceBody := by
  exact ⟨outerThickFamilyAtScale_outerSet_subset F hδ hdisc D w₁ hw₁,
    outerThickFamilyAtScale_innerSet_eq_filter F hδ hdisc D w₁ hw₁,
    outerThickFamilyAtScale_outerBody_toConvexSpaceBody F hδ hdisc D w₁ hw₁,
    outerThickFamilyAtScale_innerBody_toConvexSpaceBody F hδ hdisc D w₁ hw₁⟩

/-- The thick outer shading lies in the twice-scale neighbourhood of its final fiber union. -/
theorem outerFactoringFamily_outerShadeSubset
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    ∀ j ∈ (outerFactoringFamily F hδ hdisc D w₁ hw₁).outerSet,
      ((outerFactoringFamily F hδ hdisc D w₁ hw₁).outerBody j).shade ⊆
        Metric.cthickening (2 * (F.outerBody j).scale)
          (iUnionShade ((outerFactoringFamily F hδ hdisc D w₁ hw₁).fiber j)
            (outerFactoringFamily F hδ hdisc D w₁ hw₁).innerBody) := by
  intro j _
  exact outerThickFamilyAtScale_outerShade_subset F hδ hdisc D w₁ hw₁ j

/-- **Item 1** of corrected GWZ Proposition 5.1: substantial final inner refinement. -/
theorem outerFactoringFamily_refinement
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    IsCRefinement (outerFactoringFamily F hδ hdisc D w₁ hw₁).innerSet
      (outerFactoringFamily F hδ hdisc D w₁ hw₁).innerBody F.innerSet F.innerBody
      (outerFactoringRefinementConstant (Module.finrank ℝ E) F.innerSet.card
        D.exponent w₁) :=
  outerThickFamilyAtScale_isCRefinement_of_lossBound F hδ hdisc D w₁ hw₁
    (FactoringAtScaleLossBound.uniform F hδ hdisc D w₁ hw₁)

/-- **Item 2** of corrected GWZ Proposition 5.1: summed fullness for the thick outer shading. -/
theorem outerFactoringFamily_lambda
    (F : FactorFamily E ι κ) {C : ENNReal} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hdim : Module.finrank ℝ E = 3)
    (hshape : F.InnerHasSimilarShape 2) (hFrostman : F.HasFrostmanFibers C) :
    (outerFactoringFullnessConstant (Module.finrank ℝ E) F.innerSet.card
        D.exponent w₁ : ENNReal) * C⁻¹ *
          (fullness F.innerSet F.innerBody : ENNReal) ^ 2 *
        (∑ j ∈ (outerFactoringFamily F hδ hdisc D w₁ hw₁).outerSet,
          volume (((outerFactoringFamily F hδ hdisc D w₁ hw₁).outerBody j).carrier)) ≤
      ∑ j ∈ (outerFactoringFamily F hδ hdisc D w₁ hw₁).outerSet,
        volume (((outerFactoringFamily F hδ hdisc D w₁ hw₁).outerBody j).shade) :=
  outerThickFamilyAtScale_fullness_of_lossBound hδ hdisc D w₁ hw₁ hdim hshape
    hFrostman (FactoringAtScaleLossBound.uniform F hδ hdisc D w₁ hw₁)

/-- **Item 3** of corrected GWZ Proposition 5.1: one-sided constant multiplicity for the exact
counting shading. The thick family is intentionally absent from this assertion. -/
theorem outerFactoringFamily_outerConstMult
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    ∀ x ∈ iUnionShade (outerFactoringCountingFamily F hδ hdisc D w₁ hw₁).outerSet
        (outerFactoringCountingFamily F hδ hdisc D w₁ hw₁).outerBody,
      (pointwiseMultiplicity
          (outerFactoringCountingFamily F hδ hdisc D w₁ hw₁).outerSet
          (outerFactoringCountingFamily F hδ hdisc D w₁ hw₁).outerBody x : ENNReal) ≤
        (outerFactoringCountingMultiplicityConstant : ENNReal) *
          multiplicity (outerFactoringCountingFamily F hδ hdisc D w₁ hw₁).outerSet
          (outerFactoringCountingFamily F hδ hdisc D w₁ hw₁).outerBody := by
  intro x hx
  simpa only [outerFactoringCountingMultiplicityConstant, outerFactoringCountingFamily,
    ENNReal.coe_ofNat] using
    outerCountingFamilyAtScale_pointwiseMultiplicity_le_mul_multiplicity
      hδ hdisc D w₁ hw₁ hx

/-- The final inner shading lies in its exact counting parent shading. -/
theorem outerFactoringCountingFamily_shadingContainment
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    ∀ i ∈ (outerFactoringCountingFamily F hδ hdisc D w₁ hw₁).innerSet,
      ((outerFactoringCountingFamily F hδ hdisc D w₁ hw₁).innerBody i).shade ⊆
        ((outerFactoringCountingFamily F hδ hdisc D w₁ hw₁).outerBody
          ((outerFactoringCountingFamily F hδ hdisc D w₁ hw₁).parent i)).shade :=
  (outerFactoringCountingFamily F hδ hdisc D w₁ hw₁).shade_subset_parent

/-- Positive input shading mass makes the exact counting union non-null. -/
theorem outerFactoringCountingFamily_union_volume_ne_zero_of_input_mass_pos
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    volume (iUnionShade
      (outerFactoringCountingFamily F hδ hdisc D w₁ hw₁).outerSet
      (outerFactoringCountingFamily F hδ hdisc D w₁ hw₁).outerBody) ≠ 0 :=
  outerCountingFamilyAtScale_union_volume_ne_zero_of_input_mass_pos
    F hδ hdisc D w₁ hw₁ hmass

/-- **Item 4** of corrected GWZ Proposition 5.1: one common dyadic inner multiplicity level. -/
theorem outerFactoringFamily_innerConstMult
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    ∀ j ∈ (outerFactoringFamily F hδ hdisc D w₁ hw₁).outerSet,
      ∀ x ∈ iUnionShade ((outerFactoringFamily F hδ hdisc D w₁ hw₁).fiber j)
          (outerFactoringFamily F hδ hdisc D w₁ hw₁).innerBody,
        2 ^ F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ)
              (by exact_mod_cast hw₁) ≤
            pointwiseMultiplicity ((outerFactoringFamily F hδ hdisc D w₁ hw₁).fiber j)
              (outerFactoringFamily F hδ hdisc D w₁ hw₁).innerBody x ∧
          pointwiseMultiplicity ((outerFactoringFamily F hδ hdisc D w₁ hw₁).fiber j)
              (outerFactoringFamily F hδ hdisc D w₁ hw₁).innerBody x <
            outerFactoringInnerMultiplicityConstant *
              2 ^ F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ)
                (by exact_mod_cast hw₁) := by
  intro _ _ _ hx
  simpa only [outerFactoringInnerMultiplicityConstant, outerFactoringFamily, pow_succ,
    mul_comm] using
    outerThickFamilyAtScale_fiber_multiplicity hδ hdisc D w₁ hw₁ hx

/-- **Item 5** of corrected GWZ Proposition 5.1: the product inequality is fiberwise. -/
theorem outerFactoringFamily_multDominated
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hscale : F.OuterIsAtScale 2 w₁) :
    ∀ j ∈ (outerFactoringFamily F hδ hdisc D w₁ hw₁).outerSet,
      multiplicity F.innerSet F.innerBody ≤
        (outerFactoringProductConstant (Module.finrank ℝ E) F.innerSet.card
            D.exponent w₁ : ENNReal) *
          multiplicity (outerFactoringFamily F hδ hdisc D w₁ hw₁).outerSet
            (outerFactoringFamily F hδ hdisc D w₁ hw₁).outerBody *
          multiplicity ((outerFactoringFamily F hδ hdisc D w₁ hw₁).fiber j)
            (outerFactoringFamily F hδ hdisc D w₁ hw₁).innerBody := by
  intro _ hj
  exact outerThickFamilyAtScale_multiplicity_product_of_lossBound hδ hdisc D w₁ hw₁
    hscale (FactoringAtScaleLossBound.uniform F hδ hdisc D w₁ hw₁) hj

/-- **Item 6** of corrected GWZ Proposition 5.1: pointwise inner-to-thick containment. -/
theorem outerFactoringFamily_shadingContainment
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    ∀ i ∈ (outerFactoringFamily F hδ hdisc D w₁ hw₁).innerSet,
      ((outerFactoringFamily F hδ hdisc D w₁ hw₁).innerBody i).shade ⊆
        ((outerFactoringFamily F hδ hdisc D w₁ hw₁).outerBody
          ((outerFactoringFamily F hδ hdisc D w₁ hw₁).parent i)).shade :=
  (outerFactoringFamily F hδ hdisc D w₁ hw₁).shade_subset_parent

/-- **Item 7** of corrected GWZ Proposition 5.1: open radius `w₁` versus closed radius `2 w₁`. -/
theorem outerFactoringFamily_avgMultOnBalls
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    ∀ x ∈ iUnionShade (outerFactoringFamily F hδ hdisc D w₁ hw₁).innerSet
        (outerFactoringFamily F hδ hdisc D w₁ hw₁).innerBody,
      ∀ y ∈ iUnionShade (outerFactoringFamily F hδ hdisc D w₁ hw₁).innerSet
          (outerFactoringFamily F hδ hdisc D w₁ hw₁).innerBody,
        volume (iUnionShade (outerFactoringFamily F hδ hdisc D w₁ hw₁).innerSet
            (outerFactoringFamily F hδ hdisc D w₁ hw₁).innerBody ∩
              Metric.ball x (w₁ : ℝ)) ≤
          (outerFactoringBallComparisonConstant (Module.finrank ℝ E) : ENNReal) *
            volume (iUnionShade (outerFactoringFamily F hδ hdisc D w₁ hw₁).innerSet
              (outerFactoringFamily F hδ hdisc D w₁ hw₁).innerBody ∩
                Metric.closedBall y (2 * (w₁ : ℝ))) := by
  intro x _ y hy
  simpa only [outerFactoringBallComparisonConstant, outerFactoringFamily,
    outerCountingFamilyAtScale, outerThickFamilyAtScale, productiveCountingFamily_innerSet,
    productiveThickFamily_innerSet, productiveCountingFamily_innerBody,
    productiveThickFamily_innerBody, ENNReal.coe_mul, ENNReal.coe_ofNat,
    ENNReal.coe_natCast] using
    outerCountingFamilyAtScale_ballComparison hδ hdisc D w₁ hw₁ x (by
      simpa only [outerFactoringFamily, outerCountingFamilyAtScale, outerThickFamilyAtScale,
        productiveCountingFamily_innerSet, productiveThickFamily_innerSet,
        productiveCountingFamily_innerBody, productiveThickFamily_innerBody] using hy)

end FactoringAndMultiplicity

end AtScale

open AtScale in
/-- **Item 3** of corrected GWZ Proposition 5.1, under The thick family is intentionally absent from it. -/
theorem outerFactoringFamily_outerConstMult
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {ι κ : Type*} [DecidableEq κ]
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    ∀ x ∈ iUnionShade (outerFactoringCountingFamily F hδ hdisc D w₁ hw₁).outerSet
        (outerFactoringCountingFamily F hδ hdisc D w₁ hw₁).outerBody,
      (pointwiseMultiplicity
          (outerFactoringCountingFamily F hδ hdisc D w₁ hw₁).outerSet
          (outerFactoringCountingFamily F hδ hdisc D w₁ hw₁).outerBody x : ENNReal) ≤
        (outerFactoringCountingMultiplicityConstant : ENNReal) *
          multiplicity (outerFactoringCountingFamily F hδ hdisc D w₁ hw₁).outerSet
          (outerFactoringCountingFamily F hδ hdisc D w₁ hw₁).outerBody :=
  AtScale.outerFactoringFamily_outerConstMult F hδ hdisc D w₁ hw₁

end ShadedBody
