/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.CoreAtScale

/-! # Bundled corrected Proposition 5.1 at a fixed outer scale

The common core exposes only the thick outer shading and the final inner family.  The combined
interface additionally exposes the exact counting shading used by the Section 9 multiplicity
arguments.  Both families have the same productive outer indices and the same enlarged carriers.
-/

@[expose] public section

open MeasureTheory Convexity Kakeya
open scoped ENNReal NNReal

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [DecidableEq κ]

/-- The common Section 6/Section 9 content of the corrected Proposition 5.1 at one fixed scale. -/
structure FactoringAndMultPropCoreAtScale
    (F : FactorFamily E ι κ) {C : ENNReal} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) : Prop where
  /-- The retained thick outer indices are original outer indices. -/
  outerSet_subset :
    (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet ⊆ F.outerSet
  /-- The final inner set consists exactly of the input indices over retained parents. -/
  innerSet_eq :
    (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet =
      {i ∈ F.innerSet |
        F.parent i ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet}
  /-- The final family keeps the input parent map. -/
  parent_eq : (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).parent = F.parent
  /-- Final inner bodies retain their input carriers. -/
  inner_carrier : ∀ i,
    ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody
  /-- A thick outer carrier is the original body enlarged by its own shortest scale. -/
  outer_carrier : ∀ j,
    ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).toConvexSpaceBody =
      (F.outerBody j).cthickening (F.outerBody j).scale
  /-- A thick shade stays in the twice-scale neighbourhood of its final fiber union. -/
  outer_shade_subset : ∀ j,
    ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade ⊆
      Metric.cthickening (2 * (F.outerBody j).scale)
        (iUnionShade ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
          (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody)
  /-- The final inner shading is a quantitative substantial refinement. -/
  refinement :
    IsCRefinement (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
      (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody F.innerSet F.innerBody
      (factoringCoreAtScaleUniformRefinementConstant (Module.finrank ℝ E)
        F.innerSet.card D.exponent w₁)
  /-- Aggregate Córdoba gives the summed thick fullness estimate. -/
  thick_fullness :
    (factoringCoreAtScaleUniformFullnessConstant (Module.finrank ℝ E)
        F.innerSet.card D.exponent w₁ : ENNReal) * C⁻¹ *
          (fullness F.innerSet F.innerBody : ENNReal) ^ 2 *
        (∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
          volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).carrier)) ≤
      ∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
        volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade)
  /-- All productive fibers use the same inner dyadic multiplicity level. -/
  inner_multiplicity :
    ∀ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
      ∀ x ∈ iUnionShade ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
          (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody,
        2 ^ F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ)
              (by exact_mod_cast hw₁) ≤
            pointwiseMultiplicity
              ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
              (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody x ∧
          pointwiseMultiplicity
              ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
              (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody x <
            2 ^ (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ)
              (by exact_mod_cast hw₁) + 1)
  /-- The multiplicity product inequality holds separately on each retained fiber. -/
  multiplicity_product :
    ∀ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
      multiplicity F.innerSet F.innerBody ≤
        (factoringCoreAtScaleUniformProductConstant (Module.finrank ℝ E)
          F.innerSet.card D.exponent w₁ : ENNReal) *
          multiplicity (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
            (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody *
          multiplicity ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
            (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody
  /-- The inner shading lies in its thick outer parent shading. -/
  shading_containment :
    ∀ i ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet,
      ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody i).shade ⊆
        ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody
          ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).parent i)).shade
  /-- Every retained fiber has positive shaded-union measure. -/
  fiber_nonnull :
    ∀ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
      volume (iUnionShade ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
        (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody) ≠ 0
  /-- Every retained original outer body has positive shortest scale. -/
  outer_scale_pos :
    ∀ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
      0 < (F.outerBody j).scale
  /-- Positive input shading mass produces at least one productive outer block. -/
  outerSet_nonempty_of_input_mass_pos :
    0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade →
      (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet.Nonempty

/-- The canonical thick construction satisfies the common corrected Proposition 5.1 interface. -/
theorem factoringAndMultPropCoreAtScale
    (F : FactorFamily E ι κ) {C : ENNReal} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hscale : F.OuterIsAtScale 2 w₁)
    (hdim : Module.finrank ℝ E = 3) (hshape : F.InnerHasSimilarShape 2)
    (hFrostman : F.HasFrostmanFibers C) :
    FactoringAndMultPropCoreAtScale (C := C) F hδ hdisc D w₁ hw₁ := by
  refine
    { outerSet_subset := outerThickFamilyAtScale_outerSet_subset F hδ hdisc D w₁ hw₁
      innerSet_eq := outerThickFamilyAtScale_innerSet_eq_filter F hδ hdisc D w₁ hw₁
      parent_eq := outerThickFamilyAtScale_parent F hδ hdisc D w₁ hw₁
      inner_carrier := outerThickFamilyAtScale_innerBody_toConvexSpaceBody F hδ hdisc D w₁ hw₁
      outer_carrier := outerThickFamilyAtScale_outerBody_toConvexSpaceBody F hδ hdisc D w₁ hw₁
      outer_shade_subset := outerThickFamilyAtScale_outerShade_subset F hδ hdisc D w₁ hw₁
      refinement := outerThickFamilyAtScale_isCRefinement_of_lossBound
        F hδ hdisc D w₁ hw₁ (FactoringAtScaleLossBound.uniform F hδ hdisc D w₁ hw₁)
      thick_fullness := outerThickFamilyAtScale_fullness_of_lossBound
        hδ hdisc D w₁ hw₁ hdim hshape hFrostman
          (FactoringAtScaleLossBound.uniform F hδ hdisc D w₁ hw₁)
      inner_multiplicity := fun _ _ _ hx ↦
        outerThickFamilyAtScale_fiber_multiplicity hδ hdisc D w₁ hw₁ hx
      multiplicity_product := fun _ hj ↦
        outerThickFamilyAtScale_multiplicity_product_of_lossBound
          hδ hdisc D w₁ hw₁ hscale
            (FactoringAtScaleLossBound.uniform F hδ hdisc D w₁ hw₁) hj
      shading_containment :=
        (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).shade_subset_parent
      fiber_nonnull := fun _ hj ↦
        outerThickFamilyAtScale_fiber_volume_ne_zero F hδ hdisc D w₁ hw₁ hj
      outer_scale_pos := fun _ hj ↦
        outerThickFamilyAtScale_originalScale_pos F hδ hdisc D w₁ hw₁ hscale hj
      outerSet_nonempty_of_input_mass_pos :=
        outerThickFamilyAtScale_outerSet_nonempty_of_sum_volume_shade_pos
          hδ hdisc D w₁ hw₁ }

/-- The canonical thick construction satisfies Proposition 5.1 under GWZ Remark 5.3's weaker
Frostman hypothesis on the inner carriers thickened at the shortest outer scale. -/
theorem factoringAndMultPropCoreAtScale_of_thickenedFrostman
    (F : FactorFamily E ι κ) {C : ENNReal} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hscale : F.OuterIsAtScale 2 w₁)
    (hdim : Module.finrank ℝ E = 3) (hshape : F.InnerHasSimilarShape 2)
    (hFrostman : F.HasThickenedFrostmanFibers C) :
    FactoringAndMultPropCoreAtScale (C := C) F hδ hdisc D w₁ hw₁ := by
  refine
    { outerSet_subset := outerThickFamilyAtScale_outerSet_subset F hδ hdisc D w₁ hw₁
      innerSet_eq := outerThickFamilyAtScale_innerSet_eq_filter F hδ hdisc D w₁ hw₁
      parent_eq := outerThickFamilyAtScale_parent F hδ hdisc D w₁ hw₁
      inner_carrier := outerThickFamilyAtScale_innerBody_toConvexSpaceBody F hδ hdisc D w₁ hw₁
      outer_carrier := outerThickFamilyAtScale_outerBody_toConvexSpaceBody F hδ hdisc D w₁ hw₁
      outer_shade_subset := outerThickFamilyAtScale_outerShade_subset F hδ hdisc D w₁ hw₁
      refinement := outerThickFamilyAtScale_isCRefinement_of_lossBound
        F hδ hdisc D w₁ hw₁ (FactoringAtScaleLossBound.uniform F hδ hdisc D w₁ hw₁)
      thick_fullness := outerThickFamilyAtScale_fullness_of_lossBound_of_thickenedFrostman
        hδ hdisc D w₁ hw₁ hdim hshape hFrostman
          (FactoringAtScaleLossBound.uniform F hδ hdisc D w₁ hw₁)
      inner_multiplicity := fun _ _ _ hx ↦
        outerThickFamilyAtScale_fiber_multiplicity hδ hdisc D w₁ hw₁ hx
      multiplicity_product := fun _ hj ↦
        outerThickFamilyAtScale_multiplicity_product_of_lossBound
          hδ hdisc D w₁ hw₁ hscale
            (FactoringAtScaleLossBound.uniform F hδ hdisc D w₁ hw₁) hj
      shading_containment :=
        (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).shade_subset_parent
      fiber_nonnull := fun _ hj ↦
        outerThickFamilyAtScale_fiber_volume_ne_zero F hδ hdisc D w₁ hw₁ hj
      outer_scale_pos := fun _ hj ↦
        outerThickFamilyAtScale_originalScale_pos F hδ hdisc D w₁ hw₁ hscale hj
      outerSet_nonempty_of_input_mass_pos :=
        outerThickFamilyAtScale_outerSet_nonempty_of_sum_volume_shade_pos
          hδ hdisc D w₁ hw₁ }

/-- The Section 9 extension of the corrected fixed-scale core. -/
structure FactoringAndMultPropCombinedAtScale
    (F : FactorFamily E ι κ) {C : ENNReal} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hscale : F.OuterIsAtScale 2 w₁)
    (hdim : Module.finrank ℝ E = 3) (hshape : F.InnerHasSimilarShape 2)
    (hFrostman : F.HasFrostmanFibers C) : Prop where
  /-- The common thick-family core. -/
  core : FactoringAndMultPropCoreAtScale (C := C) F hδ hdisc D w₁ hw₁
  /-- Counting and thick shadings use the same outer indices. -/
  outerSet_eq :
    (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet =
      (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
  /-- Counting and thick outer bodies use the same enlarged carrier. -/
  carrier_eq : ∀ j,
    ((outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).toConvexSpaceBody =
      ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).toConvexSpaceBody
  /-- Every counting shade is contained in the corresponding thick shade. -/
  count_shade_subset : ∀ j,
    ((outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade ⊆
      ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade
  /-- Every final inner shade lies in its exact counting parent shade. -/
  count_shading_containment :
    ∀ i ∈ (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet,
      ((outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody i).shade ⊆
        ((outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody
          ((outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).parent i)).shade
  /-- The counting outer union is exactly the final inner union. -/
  counting_union_eq_inner :
    iUnionShade (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody =
      iUnionShade (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody
  /-- Positive input shading mass makes the exact counting union non-null. -/
  counting_union_nonnull_of_input_mass_pos :
    0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade →
      volume (iUnionShade (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody) ≠ 0
  /-- Corrected one-sided outer counting multiplicity. -/
  count_pointwise_le :
    ∀ x ∈ iUnionShade (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody,
      (pointwiseMultiplicity
          (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
          (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody x : ENNReal) ≤
        2 * multiplicity (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
          (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody
  /-- Corrected Item 7: open radius `w₁` versus closed radius `2 w₁`, on the final inner union. -/
  ball_comparison :
    ∀ x ∈ iUnionShade (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody,
      ∀ y ∈ iUnionShade (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
          (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody,
        volume (iUnionShade (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
            (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody ∩
              Metric.ball x (w₁ : ℝ)) ≤
          4 * (factoringStep5OverlapConstant (Module.finrank ℝ E) : ENNReal) *
            volume (iUnionShade
              (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
              (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody ∩
                Metric.closedBall y (2 * (w₁ : ℝ)))

/-- The canonical thick/count pair satisfies the corrected combined Proposition 5.1 interface. -/
theorem factoringAndMultPropCombined
    (F : FactorFamily E ι κ) {C : ENNReal} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hscale : F.OuterIsAtScale 2 w₁)
    (hdim : Module.finrank ℝ E = 3) (hshape : F.InnerHasSimilarShape 2)
    (hFrostman : F.HasFrostmanFibers C) :
    FactoringAndMultPropCombinedAtScale F hδ hdisc D w₁ hw₁ hscale hdim hshape
      hFrostman := by
  refine
    { core := factoringAndMultPropCoreAtScale F hδ hdisc D w₁ hw₁ hscale hdim hshape hFrostman
      outerSet_eq := outerCountingFamilyAtScale_outerSet_eq_outerThickFamilyAtScale
        F hδ hdisc D w₁ hw₁
      carrier_eq := outerCountingFamilyAtScale_carrier_eq_outerThickFamilyAtScale
        F hδ hdisc D w₁ hw₁
      count_shade_subset := outerCountingFamilyAtScale_shade_subset_outerThickFamilyAtScale
        F hδ hdisc D w₁ hw₁
      count_shading_containment :=
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).shade_subset_parent
      counting_union_eq_inner :=
        iUnionShade_outerCountingFamilyAtScale_eq_inner F hδ hdisc D w₁ hw₁
      counting_union_nonnull_of_input_mass_pos :=
        outerCountingFamilyAtScale_union_volume_ne_zero_of_input_mass_pos
          F hδ hdisc D w₁ hw₁
      count_pointwise_le := fun _ hx ↦
        outerCountingFamilyAtScale_pointwiseMultiplicity_le_mul_multiplicity
          hδ hdisc D w₁ hw₁ hx
      ball_comparison := fun x _ _ hy ↦
        outerCountingFamilyAtScale_ballComparison hδ hdisc D w₁ hw₁ x hy }

end ShadedBody
