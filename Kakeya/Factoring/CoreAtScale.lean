/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.InducedShading
public import Kakeya.Factoring.OuterMultiplicity
public import Kakeya.Factoring.ProductiveFamilies
public import Kakeya.Factoring.WeightedPipelineRefinement
public import Kakeya.Factoring.WeightedFullness

/-! # The carrier-weighted factoring output at one scale

This is the canonical single-scale construction for the corrected Proposition 5.1.  The same
positive scale `w₁` is used by the open-ball Step 2 level set and the Step 5 covering.  Its
preliminary family comes from carrier-weighted Step 1.  Productive restriction then produces two
outer shadings on the same enlarged carriers: an exact counting shading and a thick induced
shading.
-/

@[expose] public section

open MeasureTheory Convexity Kakeya
open scoped ENNReal NNReal

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [DecidableEq κ]

open Classical in
/-- The Step 5 witnesses selected internally after carrier-weighted Steps 1--3. -/
structure WeightedFactoringPipelineSelection (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) where
  /-- The separated Step 5 cover. -/
  cover : Finset E
  /-- The positive-mass subcover retained by the self-pigeonholing. -/
  selected : Finset E
  cover_subset : (cover : Set E) ⊆ iUnionShade (F.weightedPipelineInnerSet hδ hdisc D)
    (step3InnerBody F F.step0.innerSet (F.weightedPipelineStep1 hδ hdisc D).outerSet
      (F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
      (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁))
      (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁)))
  cover_separated : Metric.IsSeparated (w₁ : ENNReal) (cover : Set E)
  covers_step3 : iUnionShade (F.weightedPipelineInnerSet hδ hdisc D)
      (step3InnerBody F F.step0.innerSet (F.weightedPipelineStep1 hδ hdisc D).outerSet
        (F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
        (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁))
        (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))) ⊆
    ⋃ c ∈ cover, Metric.closedBall c (w₁ : ℝ)
  cover_overlap : ∀ x : E,
    {c ∈ cover | x ∈ Metric.closedBall c (w₁ : ℝ)}.card ≤
      Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E)
  selected_subset : selected ⊆ cover
  selected_positive : ∀ c ∈ selected,
    volume (iUnionShade (F.weightedPipelineInnerSet hδ hdisc D)
      (F.weightedPipelineFamily hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁)
        (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁)) selected w₁).innerBody ∩
        Metric.closedBall c (w₁ : ℝ)) ≠ 0
  selected_separated : Metric.IsSeparated (w₁ : ENNReal) (selected : Set E)
  refinement : IsCRefinement (F.weightedPipelineInnerSet hδ hdisc D)
    (step5InnerBody F F.step0.innerSet (F.weightedPipelineStep1 hδ hdisc D).outerSet
      (F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
      (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁))
      (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁)) selected w₁)
    (F.weightedPipelineInnerSet hδ hdisc D)
    (step3InnerBody F F.step0.innerSet (F.weightedPipelineStep1 hδ hdisc D).outerSet
      (F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
      (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁))
      (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁)))
    (Kakeya.factoringStep5SelfPigeonholeConstant
      (Module.finrank ℝ E) cover.card)⁻¹
  selected_ball_comparable : ∀ c ∈ selected, ∀ c' ∈ selected,
    volume (iUnionShade (F.weightedPipelineInnerSet hδ hdisc D)
        (step5InnerBody F F.step0.innerSet
          (F.weightedPipelineStep1 hδ hdisc D).outerSet
          (F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
          (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
            (by exact_mod_cast hw₁))
          (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
          selected w₁) ∩
          Metric.closedBall c (w₁ : ℝ)) ≤
      2 * volume (iUnionShade (F.weightedPipelineInnerSet hδ hdisc D)
        (step5InnerBody F F.step0.innerSet
          (F.weightedPipelineStep1 hδ hdisc D).outerSet
          (F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
          (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
            (by exact_mod_cast hw₁))
          (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
          selected w₁) ∩
          Metric.closedBall c' (w₁ : ℝ))

open Classical in
/-- The carrier-weighted pipeline has a self-pigeonholed Step 5 selection. -/
theorem nonempty_weightedFactoringPipelineSelection (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    Nonempty (WeightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁) := by
  let hr : (0 : ℝ) < (w₁ : ℝ) := by exact_mod_cast hw₁
  let hΩ := F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ) hr
  obtain ⟨T, T', hTsub, hTsep, hTcover, hover, hT'T, hT'pos, hT'sep, href, hcomp⟩ :=
    exists_weightedFactoringPipelineSelf F hδ hdisc D (w₁ : ℝ) hr hΩ hw₁
  exact ⟨
    { cover := T
      selected := T'
      cover_subset := by simpa only [hr, hΩ] using hTsub
      cover_separated := hTsep
      covers_step3 := by simpa only [hr, hΩ] using hTcover
      cover_overlap := hover
      selected_subset := hT'T
      selected_positive := by simpa only [hr, hΩ] using hT'pos
      selected_separated := hT'sep
      refinement := by simpa only [hr, hΩ] using href
      selected_ball_comparable := by
        simpa only [hr, hΩ, FactorFamily.weightedPipelineFamily_innerBody] using hcomp }⟩

/-- The Step 5 witnesses chosen internally from the single-scale input. -/
noncomputable def weightedFactoringPipelineSelection (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    WeightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁ :=
  Classical.choice (nonempty_weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁)

/-- The genuine carrier-weighted Step 5 family before productive restriction. -/
noncomputable def preliminaryFactoringFamilyAtScale (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) : ShadedFactorFamily E ι κ :=
  F.weightedPipelineFamily hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁)
    (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
    (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).selected w₁

/-- The preliminary family keeps every input inner carrier. -/
theorem preliminaryFactoringFamilyAtScale_innerBody (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (i : ι) :
    ShadedBody.toConvexSpaceBody
        ((preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody i) =
      (F.innerBody i).toConvexSpaceBody := by
  apply F.weightedPipelineFamily_innerBody_toConvexSpaceBody

/-- The preliminary family keeps the original parent map. -/
theorem preliminaryFactoringFamilyAtScale_parent (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).parent = F.parent := by
  apply F.weightedPipelineFamily_parent

/-- The preliminary outer indices form an input outer subfamily. -/
theorem preliminaryFactoringFamilyAtScale_outerSet_subset
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet ⊆ F.outerSet := by
  apply F.weightedPipelineFamily_outerSet_subset

/-- The final exact counting family at the fixed scale. -/
noncomputable def outerCountingFamilyAtScale (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) : ShadedFactorFamily E ι κ :=
  productiveCountingFamily F (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁)
    (preliminaryFactoringFamilyAtScale_innerBody F hδ hdisc D w₁ hw₁)
    (preliminaryFactoringFamilyAtScale_parent F hδ hdisc D w₁ hw₁)

/-- The final thick induced family at the fixed scale. -/
noncomputable def outerThickFamilyAtScale (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) : ShadedFactorFamily E ι κ :=
  productiveThickFamily F (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁)
    (preliminaryFactoringFamilyAtScale_innerBody F hδ hdisc D w₁ hw₁)
    (preliminaryFactoringFamilyAtScale_parent F hδ hdisc D w₁ hw₁)

/-- Counting and thick output families retain exactly the same productive outer indices. -/
theorem outerCountingFamilyAtScale_outerSet_eq_outerThickFamilyAtScale
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet =
      (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet := rfl

open Classical in
/-- The final inner set is the restriction of the original family to productive parents. -/
theorem outerThickFamilyAtScale_innerSet_eq_filter
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet =
      {i ∈ F.innerSet |
        F.parent i ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet} := by
  ext i
  simp only [outerThickFamilyAtScale, productiveThickFamily_innerSet,
    productiveThickFamily_outerSet, mem_productiveFinalInnerSet_iff, Finset.mem_filter]

/-- The final zero-extended inner shading keeps every original inner carrier. -/
theorem outerThickFamilyAtScale_innerBody_toConvexSpaceBody
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (i : ι) :
    ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody := by
  apply zeroExtendedInnerBody_toConvexSpaceBody
  exact preliminaryFactoringFamilyAtScale_innerBody F hδ hdisc D w₁ hw₁

/-- Every thick output carrier is the canonical enlargement of its original outer body. -/
theorem outerThickFamilyAtScale_outerBody_toConvexSpaceBody
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (j : κ) :
    ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).toConvexSpaceBody =
      (F.outerBody j).cthickening (F.outerBody j).scale := by
  apply productiveThickFamily_outerBody_toConvexSpaceBody

/-- A thick outer shade stays inside the twice-scale neighbourhood of its final fiber union.
This is the upper half of the definition of the induced shading; it is the containment needed
by the Section 9 tube-neighbourhood argument. -/
theorem outerThickFamilyAtScale_outerShade_subset
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (j : κ) :
    ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade ⊆
      Metric.cthickening (2 * (F.outerBody j).scale)
        (iUnionShade ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
          (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody) := by
  rw [outerThickFamilyAtScale, productiveThickFamily_fiber_eq,
    productiveThickFamily_innerBody]
  let G := preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁
  change (productiveThickBody F G j).shade ⊆
    Metric.cthickening (2 * (F.outerBody j).scale)
      (iUnionShade (productiveFiber F G j) (zeroExtendedInnerBody F G))
  rw [productiveThickBody, shade_inducedShading]
  exact Set.inter_subset_left

/-- The final productive families retain the original parent map. -/
theorem outerThickFamilyAtScale_parent
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).parent = F.parent := rfl

/-- At a positive selected scale, every retained original outer body has positive shortest scale. -/
theorem outerThickFamilyAtScale_originalScale_pos
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hscale : F.OuterIsAtScale 2 w₁)
    {j : κ} (hj : j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet) :
    0 < (F.outerBody j).scale := by
  have hjF := preliminaryFactoringFamilyAtScale_outerSet_subset F hδ hdisc D w₁ hw₁
    (Finset.mem_filter.mp hj).1
  have hs := (hscale j hjF).2
  have hwreal : (0 : ℝ) < (w₁ : ℝ) := by exact_mod_cast hw₁
  norm_num at hs
  dsimp only [ConvexSpaceBody.scale]
  nlinarith

/-- The complete original fiber with the final shading extended by zero. -/
noncomputable def aggregateInputFamilyAtScale (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) : FactorFamily E ι κ :=
  productiveInputFamily F (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁)
    (preliminaryFactoringFamilyAtScale_innerBody F hδ hdisc D w₁ hw₁)

/-- Average final shading density in one complete original fiber. -/
noncomputable def finalFiberFullnessAtScale (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (j : κ) : NNReal :=
  fullness ((aggregateInputFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
    (aggregateInputFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody

/-- The defining formula for the final complete-fiber fullness. -/
theorem finalFiberFullnessAtScale_eq (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (j : κ) :
    finalFiberFullnessAtScale F hδ hdisc D w₁ hw₁ j =
      fullness ((aggregateInputFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
        (aggregateInputFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody := rfl

/-- Counting and thick output families have identical outer carriers. -/
theorem outerCountingFamilyAtScale_carrier_eq_outerThickFamilyAtScale
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (j : κ) :
    ShadedBody.toConvexSpaceBody
        ((outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j) =
      ShadedBody.toConvexSpaceBody
        ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j) := by
  apply productiveCountingFamily_carrier_eq_productiveThickFamily

/-- The exact counting shading is contained in the thick induced shading. -/
theorem outerCountingFamilyAtScale_shade_subset_outerThickFamilyAtScale
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (j : κ) :
    ((outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade ⊆
      ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade := by
  apply productiveCountingFamily_shade_subset_productiveThickFamily

/-- The counting outer union is exactly the final inner shaded union. -/
theorem iUnionShade_outerCountingFamilyAtScale_eq_inner
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    iUnionShade (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody =
      iUnionShade (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody := by
  apply iUnionShade_productiveCountingFamily_eq_inner

/-- Exact retained-mass constant of the carrier-weighted self-pigeonholed pipeline. -/
noncomputable def factoringCoreAtScaleRefinementConstant
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) : NNReal :=
  Kakeya.factoringWeightedPipelineSelfRefinementConstant (Module.finrank ℝ E)
    F.innerSet.card F.innerSet.card D.exponent
    (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).cover.card

/-- A family-independent packing bound for the Step 5 cover in the fixed-scale core.  The
centres lie in the closed unit ball and are `w₁`-separated. -/
noncomputable def factoringCoreAtScaleCoverCardBound (n : ℕ) (w₁ : NNReal) : NNReal :=
  Real.toNNReal ((2 * (1 + (w₁ : ℝ)) / (w₁ : ℝ)) ^ n)

/-- The explicit cover-cardinality bound is at least one at every positive scale. -/
theorem one_le_factoringCoreAtScaleCoverCardBound (n : ℕ) {w₁ : NNReal} (hw₁ : 0 < w₁) :
    1 ≤ factoringCoreAtScaleCoverCardBound n w₁ := by
  rw [factoringCoreAtScaleCoverCardBound, Real.one_le_toNNReal]
  apply one_le_pow₀
  have hw : (0 : ℝ) < w₁ := by exact_mod_cast hw₁
  rw [le_div_iff₀ hw]
  linarith

/-- The internally selected Step 5 cover obeys the family-independent packing bound. -/
theorem weightedFactoringPipelineSelection_cover_card_le
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    ((weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).cover.card : NNReal) ≤
      factoringCoreAtScaleCoverCardBound (Module.finrank ℝ E) w₁ := by
  let Q := weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁
  have hQsub : (Q.cover : Set E) ⊆ Metric.closedBall 0 1 := by
    intro x hx
    have hxU := Q.cover_subset hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxU
    have hiF : i ∈ F.innerSet := by
      rw [F.weightedPipelineInnerSet_eq_filter hδ hdisc D] at hi
      exact F.innerSet_step0_subset (Finset.mem_filter.mp hi).1
    apply hdisc.inner_subset_unitBall hiF
    exact (step3InnerBody F F.step0.innerSet (F.weightedPipelineStep1 hδ hdisc D).outerSet
      (F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
      (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁))
      (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁)) i).shade_subset
        hxi
  have hcard := Metric.card_le_of_isSeparated_subset_closedBall hw₁
    (x := (0 : E)) (R := 1) (by norm_num) hQsub Q.cover_separated
  rw [← NNReal.coe_le_coe]
  rw [factoringCoreAtScaleCoverCardBound,
    Real.coe_toNNReal _ (by positivity :
      0 ≤ (2 * (1 + (w₁ : ℝ)) / (w₁ : ℝ)) ^ Module.finrank ℝ E)]
  exact_mod_cast hcard

/-- Uniform retained-mass coefficient of the fixed-scale core.  It depends only on the ambient
dimension, the inner-family cardinality, the volume-ratio exponent, and the chosen scale. -/
noncomputable def factoringCoreAtScaleUniformRefinementConstant
    (n M N : ℕ) (w₁ : NNReal) : NNReal :=
  Kakeya.factoringWeightedPipelineSelfRefinementConstant n M M N
    (factoringCoreAtScaleCoverCardBound n w₁)

/-- The uniform retained-mass coefficient is no larger than the exact coefficient selected by
the construction. -/
theorem factoringCoreAtScaleUniformRefinementConstant_le
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    factoringCoreAtScaleUniformRefinementConstant (Module.finrank ℝ E)
        F.innerSet.card D.exponent w₁ ≤
      factoringCoreAtScaleRefinementConstant F hδ hdisc D w₁ hw₁ := by
  let Q := weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁
  have hcard : (Q.cover.card : NNReal) ≤
      factoringCoreAtScaleCoverCardBound (Module.finrank ℝ E) w₁ := by
    simpa only [Q] using weightedFactoringPipelineSelection_cover_card_le F hδ hdisc D w₁ hw₁
  have hbound : 1 ≤ factoringCoreAtScaleCoverCardBound (Module.finrank ℝ E) w₁ :=
    one_le_factoringCoreAtScaleCoverCardBound _ hw₁
  simpa only [factoringCoreAtScaleUniformRefinementConstant,
    factoringCoreAtScaleRefinementConstant, Q] using
      Kakeya.factoringWeightedPipelineSelfRefinementConstant_anti_coverCard hcard hbound

/-- The preliminary Step 5 family is the quantitative refinement delivered by the weighted
pipeline. -/
theorem preliminaryFactoringFamilyAtScale_isCRefinement
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    IsCRefinement (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
      (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody
      F.innerSet F.innerBody
      (factoringCoreAtScaleRefinementConstant F hδ hdisc D w₁ hw₁) := by
  let hr : (0 : ℝ) < (w₁ : ℝ) := by exact_mod_cast hw₁
  let hΩ := F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ) hr
  simpa only [preliminaryFactoringFamilyAtScale, factoringCoreAtScaleRefinementConstant, hr, hΩ]
    using F.weightedPipelineFamily_isCRefinementSelf hδ hdisc D (w₁ : ℝ) hr hΩ
      (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).selected w₁
      (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).refinement

open Classical in
/-- Productive restriction and zero extension preserve the weighted refinement mass. -/
theorem outerThickFamilyAtScale_isCRefinement
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    IsCRefinement (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
      (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody
      F.innerSet F.innerBody
      (factoringCoreAtScaleRefinementConstant F hδ hdisc D w₁ hw₁) := by
  let G := preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁
  let hbody := preliminaryFactoringFamilyAtScale_innerBody F hδ hdisc D w₁ hw₁
  let hparent := preliminaryFactoringFamilyAtScale_parent F hδ hdisc D w₁ hw₁
  have href := preliminaryFactoringFamilyAtScale_isCRefinement F hδ hdisc D w₁ hw₁
  have hsub : G.innerSet ⊆ F.innerSet := href.1.1
  refine ⟨?_, ?_⟩
  · constructor
    · intro i hi
      exact (mem_productiveFinalInnerSet_iff F G i).mp hi |>.1
    · intro i hi
      constructor
      · exact zeroExtendedInnerBody_toConvexSpaceBody F G hbody i
      · by_cases hiG : i ∈ G.innerSet
        · simpa [outerThickFamilyAtScale, productiveThickFamily,
            productiveFinalInnerSet, G, zeroExtendedInnerBody, hiG] using
            (href.1.2 i hiG).2
        · simp [outerThickFamilyAtScale, productiveThickFamily,
            productiveFinalInnerSet, G, zeroExtendedInnerBody, hiG]
  · have hmass : ∑ i ∈ productiveFinalInnerSet F G,
          volume (zeroExtendedInnerBody F G i).shade =
        ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := by
      exact sum_volume_zeroExtendedInnerBody F G hsub hparent
    rw [show ∑ i ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet,
        volume ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody i).shade =
      ∑ i ∈ G.innerSet, volume (G.innerBody i).shade by
        change ∑ i ∈ productiveFinalInnerSet F G,
            volume (zeroExtendedInnerBody F G i).shade = _
        exact hmass]
    exact href.2

/-- The counting family has the same final inner refinement as the thick family. -/
theorem outerCountingFamilyAtScale_isCRefinement
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    IsCRefinement (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
      (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody
      F.innerSet F.innerBody
      (factoringCoreAtScaleRefinementConstant F hδ hdisc D w₁ hw₁) := by
  simpa [outerCountingFamilyAtScale, outerThickFamilyAtScale, productiveCountingFamily,
    productiveThickFamily] using
      outerThickFamilyAtScale_isCRefinement F hδ hdisc D w₁ hw₁

open Classical in
/-- By definition, every retained block has a non-null final fiber union. -/
theorem outerThickFamilyAtScale_fiber_volume_ne_zero
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) {j : κ}
    (hj : j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet) :
    volume (iUnionShade ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
      (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody) ≠ 0 := by
  let G := preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁
  have hjprod : j ∈ productiveOuterSet G := by
    simpa only [outerThickFamilyAtScale, productiveThickFamily_outerSet, G] using hj
  simpa only [outerThickFamilyAtScale, productiveThickFamily_innerSet,
    productiveThickFamily_innerBody, productiveThickFamily_fiber_eq, G] using
    volume_iUnionShade_zeroExtended_fiber_ne_zero F G
      (preliminaryFactoringFamilyAtScale_isCRefinement F hδ hdisc D w₁ hw₁).1.1
      (preliminaryFactoringFamilyAtScale_parent F hδ hdisc D w₁ hw₁) hjprod

/-- Every productive final outer index is an original outer index. -/
theorem outerThickFamilyAtScale_outerSet_subset
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet ⊆ F.outerSet := by
  intro j hj
  exact preliminaryFactoringFamilyAtScale_outerSet_subset F hδ hdisc D w₁ hw₁
    (Finset.mem_filter.mp hj).1

open Classical in
/-- The carrier mass in a productive aggregate fiber is the complete original fiber volume. -/
theorem aggregateInputFamilyAtScale_fiberCarrierVolume_eq
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) {j : κ}
    (hj : j ∈ (aggregateInputFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet) :
    (∑ i ∈ (aggregateInputFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j,
        volume ((aggregateInputFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody i).carrier) =
      fiberVolume F F.innerSet j := by
  let G := preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁
  let hbody := preliminaryFactoringFamilyAtScale_innerBody F hδ hdisc D w₁ hw₁
  have hjG : j ∈ productiveOuterSet G := by
    simpa only [aggregateInputFamilyAtScale, productiveInputFamily_outerSet, G, hbody] using hj
  rw [show (aggregateInputFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j = F.fiber j by
    simpa only [aggregateInputFamilyAtScale, G, hbody] using
      productiveInputFamily_fiber_eq F G hbody hjG]
  rw [show (aggregateInputFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody =
      zeroExtendedInnerBody F G by rfl]
  rw [fiberVolume_eq_sum]
  simp only [FactorFamily.fiber]
  simp only [zeroExtendedInnerBody_toConvexSpaceBody F G hbody]
  apply Finset.sum_congr
  · ext i
    simp
  · intro i _
    rfl

/-- A thick output carrier is exactly the original outer body enlarged by its shortest scale. -/
theorem outerThickFamilyAtScale_carrierVolume_eq_enlargedOuterVolume
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (j : κ) :
    volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).carrier) =
      enlargedOuterVolume F j := by
  rw [enlargedOuterVolume_eq]
  change volume ((inducedShading (productiveFiber F
    (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁) j)
      (zeroExtendedInnerBody F
        (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁))
      (F.outerBody j)).carrier) = _
  rw [toConvexSpaceBody_inducedShading]

open Classical in
/-- The complete-fiber and enlarged-outer weights are cross-comparable on productive blocks. -/
theorem aggregateFiberVolume_cross_comparable
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    ∀ i ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
      ∀ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
        fiberVolume F F.innerSet i * enlargedOuterVolume F j ≤
          2 * enlargedOuterVolume F i * fiberVolume F F.innerSet j := by
  intro i hi j hj
  have hiG : i ∈ (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet :=
    (Finset.mem_filter.mp hi).1
  have hjG : j ∈ (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet :=
    (Finset.mem_filter.mp hj).1
  have hcomp : normalizedFiberVolume F F.innerSet i ≤
      2 * normalizedFiberVolume F F.innerSet j := by
    exact F.weightedPipelineFamily_normalizedFiberVolume_le_two_mul hδ hdisc D
      (w₁ : ℝ) (by exact_mod_cast hw₁)
      (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁))
      (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).selected w₁ hiG hjG
  have hiImage : i ∈ F.innerSet.image F.parent := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp
      (F.weightedPipelineFamily_outerSet_subset_image hδ hdisc D
        (w₁ : ℝ) (by exact_mod_cast hw₁)
        (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁))
        (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).selected w₁ hiG)
    exact Finset.mem_image_of_mem F.parent (F.innerSet_step0_subset hq)
  have hjImage : j ∈ F.innerSet.image F.parent := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp
      (F.weightedPipelineFamily_outerSet_subset_image hδ hdisc D
        (w₁ : ℝ) (by exact_mod_cast hw₁)
        (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁))
        (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).selected w₁ hjG)
    exact Finset.mem_image_of_mem F.parent (F.innerSet_step0_subset hq)
  exact fiberVolume_mul_enlargedOuterVolume_le_of_normalizedFiberVolume_le
    F hδ hdisc (by rfl) hiImage hjImage 2 hcomp

set_option maxHeartbeats 800000 in
-- This transports the weighted Step 2 estimate through Step 5 and productive zero extension.
open Classical in
/-- Every productive final fiber has the common dyadic inner multiplicity level selected by the
weighted Step 2. -/
theorem outerCountingFamilyAtScale_fiber_multiplicity
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) {j : κ} {x : E}
    (hx : x ∈ iUnionShade ((outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
      (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody) :
    2 ^ F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁) ≤
        pointwiseMultiplicity
          ((outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
          (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody x ∧
      pointwiseMultiplicity
          ((outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
          (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody x <
        2 ^ (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁) + 1) := by
  let G := preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁
  let hbody := preliminaryFactoringFamilyAtScale_innerBody F hδ hdisc D w₁ hw₁
  let hparent := preliminaryFactoringFamilyAtScale_parent F hδ hdisc D w₁ hw₁
  have href := preliminaryFactoringFamilyAtScale_isCRefinement F hδ hdisc D w₁ hw₁
  have hfiber : (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j =
      productiveFiber F G j := by
    simpa only [outerCountingFamilyAtScale, G, hbody, hparent] using
      productiveCountingFamily_fiber_eq F G hbody hparent j
  have hinner : (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody =
      zeroExtendedInnerBody F G := by
    simp only [outerCountingFamilyAtScale, productiveCountingFamily_innerBody, G]
  rw [hfiber, hinner] at hx ⊢
  obtain ⟨i, hi, _⟩ := Set.mem_iUnion₂.mp hx
  have hi' := (mem_productiveFiber_iff F G j i).mp hi
  have hj : j ∈ productiveOuterSet G := hi'.2.2 ▸ hi'.2.1
  have hu := iUnionShade_zeroExtended_fiber F G href.1.1 hparent hj
  have hp := pointwiseMultiplicity_zeroExtended_fiber F G href.1.1 hparent hj x
  have hxG : x ∈ iUnionShade (G.fiber j) G.innerBody := by
    rw [← hu]
    exact hx
  have hpipe :
      2 ^ F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁) ≤
          pointwiseMultiplicity (G.fiber j) G.innerBody x ∧
        pointwiseMultiplicity (G.fiber j) G.innerBody x <
          2 ^ (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ)
            (by exact_mod_cast hw₁) + 1) := by
    simpa only [G, preliminaryFactoringFamilyAtScale] using
      F.weightedPipelineFamily_fiber_multiplicity hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁)
        (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁))
        (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).selected w₁ hxG
  constructor
  · calc
      _ ≤ pointwiseMultiplicity (G.fiber j) G.innerBody x := hpipe.1
      _ = _ := hp.symm
  · calc
      _ = pointwiseMultiplicity (G.fiber j) G.innerBody x := hp
      _ < _ := hpipe.2

open Classical in
/-- Counting and thick families have the same final inner multiplicity on every fiber. -/
theorem outerThickFamilyAtScale_fiber_multiplicity
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) {j : κ} {x : E}
    (hx : x ∈ iUnionShade ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
      (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody) :
    2 ^ F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁) ≤
        pointwiseMultiplicity
          ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
          (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody x ∧
      pointwiseMultiplicity
          ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
          (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody x <
        2 ^ (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁) + 1) := by
  have hxC : x ∈ iUnionShade
      ((outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
      (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody := by
    simpa only [outerCountingFamilyAtScale, outerThickFamilyAtScale,
      productiveCountingFamily_fiber_eq, productiveThickFamily_fiber_eq,
      productiveCountingFamily_innerBody, productiveThickFamily_innerBody] using hx
  have h := outerCountingFamilyAtScale_fiber_multiplicity hδ hdisc D w₁ hw₁ hxC
  simpa only [outerCountingFamilyAtScale, outerThickFamilyAtScale,
    productiveCountingFamily_fiber_eq, productiveThickFamily_fiber_eq,
    productiveCountingFamily_innerBody, productiveThickFamily_innerBody] using h

set_option maxHeartbeats 800000 in
-- Productive restriction is compared pointwise with the genuine weighted Step 5 family.
open Classical in
/-- The productive final inner family satisfies the global Step 2 multiplicity upper bound. -/
theorem outerCountingFamilyAtScale_pointwiseMultiplicity_lt
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) {x : E}
    (hx : x ∈ iUnionShade
      (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
      (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody) :
    pointwiseMultiplicity
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody x <
      4 * (2 ^ F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁) *
        2 ^ F.weightedPipelineOuterExponent hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁)) := by
  let G := preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁
  let hbody := preliminaryFactoringFamilyAtScale_innerBody F hδ hdisc D w₁ hw₁
  let hparent := preliminaryFactoringFamilyAtScale_parent F hδ hdisc D w₁ hw₁
  have hxG : x ∈ iUnionShade G.innerSet G.innerBody :=
    iUnionShade_productiveFinalInnerSet_subset F G (by
      simpa only [outerCountingFamilyAtScale, productiveCountingFamily_innerSet,
        productiveCountingFamily_innerBody, G, hbody, hparent] using hx)
  have hpipe := F.weightedPipelineFamily_multiplicity hδ hdisc D (w₁ : ℝ)
    (by exact_mod_cast hw₁)
    (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
      (by exact_mod_cast hw₁))
    (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).selected w₁
    (by simpa only [G, preliminaryFactoringFamilyAtScale] using hxG)
  have hp := pointwiseMultiplicity_productiveFinalInnerSet_le F G x
  calc
    pointwiseMultiplicity
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody x ≤
      pointwiseMultiplicity G.innerSet G.innerBody x := by
        simpa only [outerCountingFamilyAtScale, productiveCountingFamily_innerSet,
          productiveCountingFamily_innerBody, G, hbody, hparent] using hp
    _ < _ := by simpa only [G, preliminaryFactoringFamilyAtScale] using hpipe.2

open Classical in
/-- Scalar multiplicity upper bound for the productive final inner family. -/
theorem outerCountingFamilyAtScale_multiplicity_le
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    multiplicity (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody ≤
      (4 * (2 ^ F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁) *
        2 ^ F.weightedPipelineOuterExponent hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁)) : ℕ) := by
  apply multiplicity_le_of_pointwiseMultiplicity_le
  intro x hx
  exact_mod_cast (outerCountingFamilyAtScale_pointwiseMultiplicity_lt
    hδ hdisc D w₁ hw₁ hx).le

open Classical in
/-- A point of the preliminary Step 5 union certifies that the selected cover is nonempty. -/
theorem weightedFactoringPipelineSelection_selected_nonempty
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) {y : E}
    (hy : y ∈ iUnionShade (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
      (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody) :
    (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).selected.Nonempty := by
  let G := preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁
  let Q := weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁
  have hGinnerBody : G.innerBody =
      step5InnerBody F F.step0.innerSet
        (F.weightedPipelineStep1 hδ hdisc D).outerSet
        (F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
        (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁))
        (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
        Q.selected w₁ := by
    simpa only [G, preliminaryFactoringFamilyAtScale] using
      F.weightedPipelineFamily_innerBody hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁)
        (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁)) Q.selected w₁
  obtain ⟨i, _, hyi⟩ := Set.mem_iUnion₂.mp hy
  have hyi' : y ∈
      (step5InnerBody F F.step0.innerSet
        (F.weightedPipelineStep1 hδ hdisc D).outerSet
        (F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
        (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁))
        (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
        Q.selected w₁ i).shade := by
    rw [← hGinnerBody]
    exact hyi
  rw [shade_step5InnerBody] at hyi'
  obtain ⟨c, hc, _⟩ := Set.mem_iUnion₂.mp hyi'.2
  exact ⟨c, hc⟩

open Classical in
/-- The preliminary inner union is the explicit weighted Step 5 union. -/
theorem iUnionShade_preliminaryFactoringFamilyAtScale
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    iUnionShade (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
        (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody =
      iUnionShade (F.weightedPipelineInnerSet hδ hdisc D)
        (step5InnerBody F F.step0.innerSet
          (F.weightedPipelineStep1 hδ hdisc D).outerSet
          (F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
          (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
            (by exact_mod_cast hw₁))
          (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
          (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).selected w₁) := by
  rw [preliminaryFactoringFamilyAtScale, F.weightedPipelineFamily_innerSet,
    F.weightedPipelineFamily_innerBody]

open Classical in
/-- The final counting inner union is pointwise contained in the preliminary Step 5 union. -/
theorem iUnionShade_outerCountingFamilyAtScale_subset_preliminary
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    iUnionShade (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody ⊆
      iUnionShade (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
        (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody := by
  let G := preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁
  apply iUnionShade_productiveFinalInnerSet_subset F G

open Classical in
/-- Productive restriction preserves every intersection volume of the final inner union. -/
theorem volume_iUnionShade_outerCountingFamilyAtScale_inter_eq_preliminary
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (A : Set E) :
    volume (iUnionShade (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody ∩ A) =
      volume (iUnionShade
        (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
        (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody ∩ A) := by
  let G := preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁
  let hbody := preliminaryFactoringFamilyAtScale_innerBody F hδ hdisc D w₁ hw₁
  let hparent := preliminaryFactoringFamilyAtScale_parent F hδ hdisc D w₁ hw₁
  have href := preliminaryFactoringFamilyAtScale_isCRefinement F hδ hdisc D w₁ hw₁
  simpa only [outerCountingFamilyAtScale, productiveCountingFamily_innerSet,
    productiveCountingFamily_innerBody, G, hbody, hparent] using
      volume_iUnionShade_zeroExtended_inter_eq F G href.1.1 hparent A

set_option maxHeartbeats 800000 in
-- This instantiates the existing Step 5 theorem with the selected weighted-pipeline witnesses.
open Classical in
/-- Unequal-radius comparison on the explicit weighted Step 5 union. -/
theorem weightedFactoringStep5_ballComparison
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁)
    (hQne : (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).selected.Nonempty)
    (x : E) {y : E}
    (hy : y ∈ iUnionShade (F.weightedPipelineInnerSet hδ hdisc D)
      (step5InnerBody F F.step0.innerSet
        (F.weightedPipelineStep1 hδ hdisc D).outerSet
        (F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
        (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁))
        (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
        (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).selected w₁)) :
    volume (iUnionShade (F.weightedPipelineInnerSet hδ hdisc D)
        (step5InnerBody F F.step0.innerSet
          (F.weightedPipelineStep1 hδ hdisc D).outerSet
          (F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
          (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
            (by exact_mod_cast hw₁))
          (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
          (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).selected w₁) ∩
          Metric.ball x (w₁ : ℝ)) ≤
      4 * (Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E) : ENNReal) *
        volume (iUnionShade (F.weightedPipelineInnerSet hδ hdisc D)
          (step5InnerBody F F.step0.innerSet
            (F.weightedPipelineStep1 hδ hdisc D).outerSet
            (F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
            (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
              (by exact_mod_cast hw₁))
            (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ)
              (by exact_mod_cast hw₁))
            (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).selected w₁) ∩
            Metric.closedBall y (2 * (w₁ : ℝ))) := by
  let Q := weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁
  rw [F.weightedPipelineInnerSet_eq_filter] at hy ⊢
  refine volume_iUnionShade_step5_inter_ball_le_mul_volume_inter_closedBall
    F F.step0.innerSet (F.weightedPipelineStep1 hδ hdisc D).outerSet
    (F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
    (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
      (by exact_mod_cast hw₁))
    (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
    hw₁ (by simpa only [Q] using hQne) Q.selected_separated ?_ x ?_
  · simpa only [FactorFamily.weightedPipelineInnerSet_eq_filter] using
      Q.selected_ball_comparable
  · exact hy

set_option maxHeartbeats 2000000 in
-- Productive restriction is transported only after applying the Step 5 comparison.
open Classical in
/-- Corrected Item 7 at the canonical scale: an open `w₁`-ball is controlled by a closed
`2 w₁`-ball, with the second centre in the final inner union. -/
theorem outerCountingFamilyAtScale_ballComparison
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (x : E) {y : E}
    (hy : y ∈ iUnionShade (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
      (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody) :
    volume (iUnionShade (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody ∩
          Metric.ball x (w₁ : ℝ)) ≤
      4 * (Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E) : ENNReal) *
        volume (iUnionShade
          (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
          (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody ∩
            Metric.closedBall y (2 * (w₁ : ℝ))) := by
  have hyG : y ∈ iUnionShade
      (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
      (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody :=
    iUnionShade_outerCountingFamilyAtScale_subset_preliminary F hδ hdisc D w₁ hw₁ hy
  have hQne :=
    weightedFactoringPipelineSelection_selected_nonempty hδ hdisc D w₁ hw₁ hyG
  have hUnion := iUnionShade_preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁
  have hyStep : y ∈ iUnionShade (F.weightedPipelineInnerSet hδ hdisc D)
      (step5InnerBody F F.step0.innerSet
        (F.weightedPipelineStep1 hδ hdisc D).outerSet
        (F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
        (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁))
        (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
        (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).selected w₁) := by
    rw [← hUnion]
    exact hyG
  have hstep :=
    weightedFactoringStep5_ballComparison hδ hdisc D w₁ hw₁ hQne x hyStep
  rw [volume_iUnionShade_outerCountingFamilyAtScale_inter_eq_preliminary
      F hδ hdisc D w₁ hw₁ (Metric.ball x (w₁ : ℝ)),
    volume_iUnionShade_outerCountingFamilyAtScale_inter_eq_preliminary
      F hδ hdisc D w₁ hw₁ (Metric.closedBall y (2 * (w₁ : ℝ))),
    hUnion]
  exact hstep

set_option maxHeartbeats 800000 in
-- The complete original fiber is assembled before applying aggregate Lemma 5.9.
open Classical in
/-- Per-block thick fullness supplied by the direct aggregate Córdoba estimate. -/
private theorem outerThickFamilyAtScale_blockFullness_aux
    {F : FactorFamily E ι κ} {C : ENNReal} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hdim : Module.finrank ℝ E = 3)
    (hshape : F.InnerHasSimilarShape 2)
    (hFrostman : F.HasFrostmanFibers C ∨ F.HasThickenedFrostmanFibers C) :
    ∀ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
      C⁻¹ * (finalFiberFullnessAtScale F hδ hdisc D w₁ hw₁ j : ENNReal) ^ 2 *
          volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).carrier) ≤
        (lambdaInducedSingleWUniform.C : ENNReal) * ((D.exponent : ENNReal) + 1) *
          volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade) := by
  let G := preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁
  let hbody := preliminaryFactoringFamilyAtScale_innerBody F hδ hdisc D w₁ hw₁
  let H := aggregateInputFamilyAtScale F hδ hdisc D w₁ hw₁
  have href := preliminaryFactoringFamilyAtScale_isCRefinement F hδ hdisc D w₁ hw₁
  have hparent : G.parent = F.parent :=
    preliminaryFactoringFamilyAtScale_parent F hδ hdisc D w₁ hw₁
  have houter : G.outerSet ⊆ F.outerSet :=
    preliminaryFactoringFamilyAtScale_outerSet_subset F hδ hdisc D w₁ hw₁
  have hshapeH : H.InnerHasSimilarShape 2 := by
    intro i hi i' hi'
    have hiF : i ∈ F.innerSet :=
      (mem_productiveInputFamily_innerSet_iff F G hbody i).mp hi |>.1
    have hiF' : i' ∈ F.innerSet :=
      (mem_productiveInputFamily_innerSet_iff F G hbody i').mp hi' |>.1
    change Metric.thickness ℝ (zeroExtendedInnerBody F G i).carrier ≤
      ((2 : NNReal) : ℝ) • Metric.thickness ℝ (zeroExtendedInnerBody F G i').carrier
    simpa only [zeroExtendedInnerBody_toConvexSpaceBody F G hbody] using
      hshape i hiF i' hiF'
  have hFrostmanH : H.HasFrostmanFibers C ∨ H.HasThickenedFrostmanFibers C :=
    hFrostman.elim
      (fun hFrostman ↦ Or.inl (by
        intro j hj
        have hjG : j ∈ productiveOuterSet G := by
          simpa only [H, aggregateInputFamilyAtScale, productiveInputFamily_outerSet] using hj
        have hjF : j ∈ F.outerSet := houter (Finset.mem_filter.mp hjG).1
        rw [show H.fiber j = F.fiber j by
          simpa only [H, aggregateInputFamilyAtScale] using
            productiveInputFamily_fiber_eq F G hbody hjG]
        change ConvexSpaceBody.IsFrostmanIn (F.fiber j)
          (fun i ↦ (zeroExtendedInnerBody F G i).toConvexSpaceBody) (F.outerBody j) C
        simpa only [zeroExtendedInnerBody_toConvexSpaceBody F G hbody] using
          hFrostman j hjF))
      (fun hFrostman ↦ Or.inr (by
        intro j hj
        have hjG : j ∈ productiveOuterSet G := by
          simpa only [H, aggregateInputFamilyAtScale, productiveInputFamily_outerSet] using hj
        have hjF : j ∈ F.outerSet := houter (Finset.mem_filter.mp hjG).1
        rw [show H.fiber j = F.fiber j by
          simpa only [H, aggregateInputFamilyAtScale] using
            productiveInputFamily_fiber_eq F G hbody hjG]
        change Kakeya.maxDensity (F.fiber j) (fun i ↦
            (zeroExtendedInnerBody F G i).toConvexSpaceBody.cthickening
              (2 * (F.outerBody j).scale)) * volume (F.outerBody j).carrier ≤
          C * ∑ i ∈ F.fiber j,
            volume ((zeroExtendedInnerBody F G i).toConvexSpaceBody.cthickening
              (2 * (F.outerBody j).scale)).carrier
        simpa only [zeroExtendedInnerBody_toConvexSpaceBody F G hbody] using
          hFrostman j hjF))
  have hneH : ∀ j ∈ H.outerSet, (H.fiber j).Nonempty := by
    intro j hj
    have hjG : j ∈ productiveOuterSet G := by
      simpa only [H, aggregateInputFamilyAtScale, productiveInputFamily_outerSet] using hj
    obtain ⟨x, hx⟩ := MeasureTheory.nonempty_of_measure_ne_zero (Finset.mem_filter.mp hjG).2
    obtain ⟨i, hi, _⟩ := Set.mem_iUnion₂.mp hx
    have hi' := (mem_shadedFactorFamily_fiber_iff G j i).mp hi
    rw [show H.fiber j = F.fiber j by
      simpa only [H, aggregateInputFamilyAtScale] using
        productiveInputFamily_fiber_eq F G hbody hjG]
    exact ⟨i, (mem_factorFamily_fiber_iff F j i).mpr
      ⟨href.1.1 hi'.1, by simpa [hparent] using hi'.2⟩⟩
  have hVposH : ∀ i ∈ H.innerSet, volume (H.innerBody i).carrier ≠ 0 := by
    intro i hi
    have hiF : i ∈ F.innerSet :=
      (mem_productiveInputFamily_innerSet_iff F G hbody i).mp hi |>.1
    change volume (zeroExtendedInnerBody F G i).carrier ≠ 0
    rw [zeroExtendedInnerBody_toConvexSpaceBody F G hbody]
    apply ne_of_gt
    have hδnz : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
    exact (ENNReal.mul_pos (ENNReal.coe_pos.mpr
      (Metric.lt_volume_convexHull.c_pos (Module.finrank ℝ E))).ne'
        (pow_ne_zero _ hδnz)).trans_le (hdisc.volume_innerBody_mem_Icc hiF).1
  have hlamH : ∀ j ∈ H.outerSet,
      (finalFiberFullnessAtScale F hδ hdisc D w₁ hw₁ j : ENNReal) *
          (∑ i ∈ H.fiber j, volume (H.innerBody i).carrier) ≤
        ∑ i ∈ H.fiber j, volume (H.innerBody i).shade := by
    intro j _
    rw [show (finalFiberFullnessAtScale F hδ hdisc D w₁ hw₁ j : ENNReal) =
      fullness (H.fiber j) H.innerBody by rfl]
    exact (sum_volumeReal_shade_eq_fullness_mul (H.fiber j) H.innerBody).ge
  have hNH : ∀ j ∈ H.outerSet, ∀ i ∈ H.fiber j,
      volume (H.outerBody j).carrier ≤
        2 ^ D.exponent * volume (H.innerBody i).carrier := by
    intro j hj i hi
    have hjG : j ∈ productiveOuterSet G := by
      simpa only [H, aggregateInputFamilyAtScale, productiveInputFamily_outerSet] using hj
    have hjF : j ∈ F.outerSet := houter (Finset.mem_filter.mp hjG).1
    have hiFfiber : i ∈ F.fiber j := by
      rw [← productiveInputFamily_fiber_eq F G hbody hjG]
      simpa only [H, aggregateInputFamilyAtScale] using hi
    change volume (F.outerBody j).carrier ≤
      2 ^ D.exponent * volume (zeroExtendedInnerBody F G i).carrier
    rw [zeroExtendedInnerBody_toConvexSpaceBody F G hbody]
    exact D.volume_outer_le j hjF i hiFfiber
  have hagg := hFrostmanH.elim
    (fun hFrostmanH ↦ aggregateFullnessForInducedShading_of_measurable H hdim hshapeH
      hFrostmanH hneH hVposH
      (fun j ↦ (finalFiberFullnessAtScale F hδ hdisc D w₁ hw₁ j : ENNReal)) hlamH hNH)
    (fun hFrostmanH ↦
      aggregateFullnessForInducedShading_of_measurable_of_thickenedFrostman H hdim hshapeH
        hFrostmanH hneH hVposH
        (fun j ↦ (finalFiberFullnessAtScale F hδ hdisc D w₁ hw₁ j : ENNReal)) hlamH hNH)
  intro j hj
  have hjH : j ∈ H.outerSet := by
    simpa only [outerThickFamilyAtScale, productiveThickFamily_outerSet, H,
      aggregateInputFamilyAtScale, productiveInputFamily_outerSet, G] using hj
  have hjG : j ∈ productiveOuterSet G := by
    simpa only [H, aggregateInputFamilyAtScale, productiveInputFamily_outerSet] using hjH
  have hjraw := hagg j hjH
  have hfiber : H.fiber j = productiveFiber F G j := by
    calc
      H.fiber j = F.fiber j := by
        simpa only [H, aggregateInputFamilyAtScale] using
          productiveInputFamily_fiber_eq F G hbody hjG
      _ = productiveFiber F G j := (productiveFiber_eq_fiber F G hjG).symm
  have hinduced : inducedShading (H.fiber j) H.innerBody (H.outerBody j) =
      (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j := by
    rw [hfiber]
    rfl
  rw [← hinduced]
  change C⁻¹ * (finalFiberFullnessAtScale F hδ hdisc D w₁ hw₁ j : ENNReal) ^ 2 *
      volume ((H.outerBody j).cthickening (H.outerBody j).scale).carrier ≤
        (lambdaInducedSingleWUniform.C : ENNReal) * ((D.exponent : ENNReal) + 1) *
          volume (inducedShading (H.fiber j) H.innerBody (H.outerBody j)).shade
  simpa only [ConvexSpaceBody.scale, hinduced] using hjraw

set_option maxHeartbeats 800000 in
-- Elaborating the shared aggregate Córdoba conclusion requires a larger reduction budget.
open Classical in
/-- Per-block thick fullness under the ordinary fibrewise Frostman hypothesis. -/
theorem outerThickFamilyAtScale_blockFullness
    {F : FactorFamily E ι κ} {C : ENNReal} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hdim : Module.finrank ℝ E = 3)
    (hshape : F.InnerHasSimilarShape 2) (hFrostman : F.HasFrostmanFibers C) :
    ∀ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
      C⁻¹ * (finalFiberFullnessAtScale F hδ hdisc D w₁ hw₁ j : ENNReal) ^ 2 *
          volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).carrier) ≤
        (lambdaInducedSingleWUniform.C : ENNReal) * ((D.exponent : ENNReal) + 1) *
          volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade) :=
  outerThickFamilyAtScale_blockFullness_aux hδ hdisc D w₁ hw₁ hdim hshape
    (Or.inl hFrostman)

set_option maxHeartbeats 800000 in
-- Elaborating the shared aggregate Córdoba conclusion requires a larger reduction budget.
open Classical in
/-- Per-block thick fullness under GWZ Remark 5.3's thickened fibrewise Frostman hypothesis. -/
theorem outerThickFamilyAtScale_blockFullness_of_thickenedFrostman
    {F : FactorFamily E ι κ} {C : ENNReal} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hdim : Module.finrank ℝ E = 3)
    (hshape : F.InnerHasSimilarShape 2) (hFrostman : F.HasThickenedFrostmanFibers C) :
    ∀ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
      C⁻¹ * (finalFiberFullnessAtScale F hδ hdisc D w₁ hw₁ j : ENNReal) ^ 2 *
          volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).carrier) ≤
        (lambdaInducedSingleWUniform.C : ENNReal) * ((D.exponent : ENNReal) + 1) *
          volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade) :=
  outerThickFamilyAtScale_blockFullness_aux hδ hdisc D w₁ hw₁ hdim hshape
    (Or.inr hFrostman)

set_option maxHeartbeats 1200000 in
-- The proof expands two fiberwise sums and transports them through two weighted moment estimates.
open Classical in
/-- Summed thick fullness at the canonical scale, before normalizing the explicit right-hand
constant.  This is the global weighted second-moment consequence of aggregate Lemma 5.9. -/
private theorem outerThickFamilyAtScale_fullness_raw_aux
    {F : FactorFamily E ι κ} {C : ENNReal} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hdim : Module.finrank ℝ E = 3)
    (hshape : F.InnerHasSimilarShape 2)
    (hFrostman : F.HasFrostmanFibers C ∨ F.HasThickenedFrostmanFibers C) :
    C⁻¹ * ((factoringCoreAtScaleRefinementConstant F hδ hdisc D w₁ hw₁ : ENNReal) *
          (fullness F.innerSet F.innerBody : ENNReal)) ^ 2 *
        (∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
          volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).carrier)) ≤
      2 * (2 : ENNReal) ^ 2 *
        ((lambdaInducedSingleWUniform.C : ENNReal) * ((D.exponent : ENNReal) + 1)) *
          (∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
            volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade)) := by
  let W := outerThickFamilyAtScale F hδ hdisc D w₁ hw₁
  let H := aggregateInputFamilyAtScale F hδ hdisc D w₁ hw₁
  let c : ENNReal := factoringCoreAtScaleRefinementConstant F hδ hdisc D w₁ hw₁
  let lam : ENNReal := fullness F.innerSet F.innerBody
  let a : κ → ENNReal := fun j ↦ ∑ i ∈ H.fiber j, volume (H.innerBody i).carrier
  let b : κ → ENNReal := fun j ↦ volume (W.outerBody j).carrier
  let q : κ → ENNReal := fun j ↦ fullness (H.fiber j) H.innerBody
  let K : ENNReal := (lambdaInducedSingleWUniform.C : ENNReal) *
    ((D.exponent : ENNReal) + 1)
  by_cases hs : W.outerSet = ∅
  · simp [W, hs]
  have hsne : W.outerSet.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
  have houterH : H.outerSet = W.outerSet := rfl
  have hinnerH : H.innerSet = W.innerSet := rfl
  have hbodyH : H.innerBody = W.innerBody := rfl
  have hA0 : (∑ j ∈ W.outerSet, a j) ≠ 0 := by
    obtain ⟨j, hj⟩ := hsne
    have hjH : j ∈ H.outerSet := houterH.symm ▸ hj
    have hjProd : j ∈ productiveOuterSet
        (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁) := by
      simpa only [H, aggregateInputFamilyAtScale, productiveInputFamily_outerSet] using hjH
    obtain ⟨x, hx⟩ := MeasureTheory.nonempty_of_measure_ne_zero
      (Finset.mem_filter.mp hjProd).2
    obtain ⟨i, hiG, _⟩ := Set.mem_iUnion₂.mp hx
    have hiG' := (mem_shadedFactorFamily_fiber_iff
      (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁) j i).mp hiG
    have hiF : i ∈ F.innerSet :=
      (preliminaryFactoringFamilyAtScale_isCRefinement F hδ hdisc D w₁ hw₁).1.1 hiG'.1
    have hiH : i ∈ H.fiber j := by
      rw [show H.fiber j = F.fiber j by
        simpa only [H, aggregateInputFamilyAtScale] using
          productiveInputFamily_fiber_eq F
            (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁)
            (preliminaryFactoringFamilyAtScale_innerBody F hδ hdisc D w₁ hw₁) hjProd]
      exact (mem_factorFamily_fiber_iff F j i).mpr
        ⟨hiF, by simpa [preliminaryFactoringFamilyAtScale_parent F hδ hdisc D w₁ hw₁]
          using hiG'.2⟩
    have hVi : 0 < volume (H.innerBody i).carrier := by
      change 0 < volume (zeroExtendedInnerBody F
        (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁) i).carrier
      rw [zeroExtendedInnerBody_toConvexSpaceBody F
        (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁)
        (preliminaryFactoringFamilyAtScale_innerBody F hδ hdisc D w₁ hw₁)]
      have hδnz : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
      exact (ENNReal.mul_pos (ENNReal.coe_pos.mpr
        (Metric.lt_volume_convexHull.c_pos (Module.finrank ℝ E))).ne'
          (pow_ne_zero _ hδnz)).trans_le (hdisc.volume_innerBody_mem_Icc hiF).1
    have hAj : 0 < a j := by
      apply hVi.trans_le
      exact Finset.single_le_sum_of_canonicallyOrdered
        (f := fun k ↦ volume (H.innerBody k).carrier) hiH
    apply (hAj.trans_le ?_).ne'
    exact Finset.single_le_sum_of_canonicallyOrdered (f := a) hj
  have hAtop : (∑ j ∈ W.outerSet, a j) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro j hj
    dsimp only [a]
    rw [ENNReal.sum_ne_top]
    intro i hi
    exact (H.innerBody i).isCompact.measure_ne_top
  have hfull : c * lam ≤ fullness H.innerSet H.innerBody := by
    simpa only [c, lam, hinnerH, hbodyH] using
      (outerThickFamilyAtScale_isCRefinement F hδ hdisc D w₁ hw₁).coe_mul_fullness_le
  have havgA : (c * lam) * (∑ j ∈ W.outerSet, a j) ≤
      ∑ j ∈ W.outerSet, q j * a j := by
    calc
      (c * lam) * (∑ j ∈ W.outerSet, a j) ≤
          (fullness H.innerSet H.innerBody : ENNReal) *
            (∑ j ∈ W.outerSet, a j) := by gcongr
      _ = (fullness H.innerSet H.innerBody : ENNReal) *
            (∑ i ∈ H.innerSet, volume (H.innerBody i).carrier) := by
        rw [← sum_fiber_carrierVolume_eq H, houterH]
      _ = ∑ i ∈ H.innerSet, volume (H.innerBody i).shade := by
        rw [← sum_volumeReal_shade_eq_fullness_mul]
      _ = ∑ j ∈ W.outerSet, q j * a j := by
        rw [← sum_fullness_mul_fiberCarrierVolume_eq H, houterH]
  have hcross : ∀ i ∈ W.outerSet, ∀ j ∈ W.outerSet,
      a i * b j ≤ 2 * b i * a j := by
    intro i hi j hj
    have hiH : i ∈ H.outerSet := houterH.symm ▸ hi
    have hjH : j ∈ H.outerSet := houterH.symm ▸ hj
    dsimp only [a, b]
    rw [aggregateInputFamilyAtScale_fiberCarrierVolume_eq F hδ hdisc D w₁ hw₁ hiH,
      aggregateInputFamilyAtScale_fiberCarrierVolume_eq F hδ hdisc D w₁ hw₁ hjH]
    change fiberVolume F F.innerSet i * volume (W.outerBody j).carrier ≤
      2 * volume (W.outerBody i).carrier * fiberVolume F F.innerSet j
    rw [show volume (W.outerBody j).carrier = enlargedOuterVolume F j by
        exact outerThickFamilyAtScale_carrierVolume_eq_enlargedOuterVolume
          F hδ hdisc D w₁ hw₁ j,
      show volume (W.outerBody i).carrier = enlargedOuterVolume F i by
        exact outerThickFamilyAtScale_carrierVolume_eq_enlargedOuterVolume
          F hδ hdisc D w₁ hw₁ i]
    exact aggregateFiberVolume_cross_comparable F hδ hdisc D w₁ hw₁ i hi j hj
  have havgB : (c * lam) * (∑ j ∈ W.outerSet, b j) ≤
      2 * (∑ j ∈ W.outerSet, q j * b j) :=
    weightedAverage_transfer_of_cross_comparable W.outerSet a b q (c * lam) 2
      hA0 hAtop hcross havgA
  have hB0 : (∑ j ∈ W.outerSet, b j) ≠ 0 := by
    obtain ⟨j, hj⟩ := hsne
    have hjF : j ∈ F.innerSet.image F.parent := by
      have hjG : j ∈ (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet :=
        (Finset.mem_filter.mp hj).1
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp
        (F.weightedPipelineFamily_outerSet_subset_image hδ hdisc D
          (w₁ : ℝ) (by exact_mod_cast hw₁)
          (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
            (by exact_mod_cast hw₁))
          (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).selected w₁ hjG)
      exact Finset.mem_image_of_mem F.parent (F.innerSet_step0_subset hi)
    have hb : 0 < b j := by
      change 0 < volume (W.outerBody j).carrier
      rw [show volume (W.outerBody j).carrier = enlargedOuterVolume F j by
        exact outerThickFamilyAtScale_carrierVolume_eq_enlargedOuterVolume
          F hδ hdisc D w₁ hw₁ j]
      exact enlargedOuterVolume_pos F hδ hdisc (by rfl) hjF
    exact (hb.trans_le (Finset.single_le_sum_of_canonicallyOrdered (f := b) hj)).ne'
  have hBtop : (∑ j ∈ W.outerSet, b j) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro j hj
    exact (W.outerBody j).isCompact.measure_ne_top
  have hsecond : (c * lam) ^ 2 * (∑ j ∈ W.outerSet, b j) ≤
      2 * (2 : ENNReal) ^ 2 * (∑ j ∈ W.outerSet, q j ^ 2 * b j) :=
    ENNReal.weighted_second_moment_lower W.outerSet q b (c * lam) 2 hB0 hBtop havgB
  have hblocks := hFrostman.elim
    (fun hFrostman ↦ Finset.sum_le_sum fun j hj ↦
      outerThickFamilyAtScale_blockFullness hδ hdisc D w₁ hw₁ hdim hshape
        hFrostman j hj)
    (fun hFrostman ↦ Finset.sum_le_sum fun j hj ↦
      outerThickFamilyAtScale_blockFullness_of_thickenedFrostman hδ hdisc D w₁ hw₁ hdim
        hshape hFrostman j hj)
  have hblocksum : C⁻¹ * (∑ j ∈ W.outerSet, q j ^ 2 * b j) ≤
      K * (∑ j ∈ W.outerSet, volume (W.outerBody j).shade) := by
    simpa only [W, H, q, b, K, finalFiberFullnessAtScale_eq,
      Finset.mul_sum, mul_assoc] using hblocks
  change C⁻¹ * (c * lam) ^ 2 * (∑ j ∈ W.outerSet, b j) ≤
    2 * (2 : ENNReal) ^ 2 * K *
      (∑ j ∈ W.outerSet, volume (W.outerBody j).shade)
  calc
    C⁻¹ * (c * lam) ^ 2 * (∑ j ∈ W.outerSet, b j) =
        C⁻¹ * ((c * lam) ^ 2 * (∑ j ∈ W.outerSet, b j)) := by ring
    _ ≤ C⁻¹ * (2 * (2 : ENNReal) ^ 2 *
        (∑ j ∈ W.outerSet, q j ^ 2 * b j)) := by gcongr
    _ = 2 * (2 : ENNReal) ^ 2 *
        (C⁻¹ * (∑ j ∈ W.outerSet, q j ^ 2 * b j)) := by ring
    _ ≤ 2 * (2 : ENNReal) ^ 2 *
        (K * (∑ j ∈ W.outerSet, volume (W.outerBody j).shade)) := by gcongr
    _ = 2 * (2 : ENNReal) ^ 2 * K *
        (∑ j ∈ W.outerSet, volume (W.outerBody j).shade) := by ring

set_option maxHeartbeats 1200000 in
-- The proof expands two fiberwise sums and transports them through two weighted moment estimates.
open Classical in
/-- Summed thick fullness under the ordinary fibrewise Frostman hypothesis. -/
theorem outerThickFamilyAtScale_fullness_raw
    {F : FactorFamily E ι κ} {C : ENNReal} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hdim : Module.finrank ℝ E = 3)
    (hshape : F.InnerHasSimilarShape 2) (hFrostman : F.HasFrostmanFibers C) :
    C⁻¹ * ((factoringCoreAtScaleRefinementConstant F hδ hdisc D w₁ hw₁ : ENNReal) *
          (fullness F.innerSet F.innerBody : ENNReal)) ^ 2 *
        (∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
          volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).carrier)) ≤
      2 * (2 : ENNReal) ^ 2 *
        ((lambdaInducedSingleWUniform.C : ENNReal) * ((D.exponent : ENNReal) + 1)) *
          (∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
            volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade)) :=
  outerThickFamilyAtScale_fullness_raw_aux hδ hdisc D w₁ hw₁ hdim hshape
    (Or.inl hFrostman)

set_option maxHeartbeats 1200000 in
-- The proof expands two fiberwise sums and transports them through two weighted moment estimates.
open Classical in
/-- Summed thick fullness under GWZ Remark 5.3's thickened fibrewise Frostman hypothesis. -/
theorem outerThickFamilyAtScale_fullness_raw_of_thickenedFrostman
    {F : FactorFamily E ι κ} {C : ENNReal} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hdim : Module.finrank ℝ E = 3)
    (hshape : F.InnerHasSimilarShape 2) (hFrostman : F.HasThickenedFrostmanFibers C) :
    C⁻¹ * ((factoringCoreAtScaleRefinementConstant F hδ hdisc D w₁ hw₁ : ENNReal) *
          (fullness F.innerSet F.innerBody : ENNReal)) ^ 2 *
        (∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
          volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).carrier)) ≤
      2 * (2 : ENNReal) ^ 2 *
        ((lambdaInducedSingleWUniform.C : ENNReal) * ((D.exponent : ENNReal) + 1)) *
          (∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
            volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade)) :=
  outerThickFamilyAtScale_fullness_raw_aux hδ hdisc D w₁ hw₁ hdim hshape
    (Or.inr hFrostman)

/-- The explicit large constant lost when summing the blockwise aggregate Córdoba estimates. -/
noncomputable def factoringCoreAtScaleFullnessLoss
    (F : FactorFamily E ι κ) (D : OuterInnerVolumeRatio F) : NNReal :=
  2 * 2 ^ 2 * lambdaInducedSingleWUniform.C * (D.exponent + 1)

/-- The small constant in the global thick-fullness conclusion of the canonical core. -/
noncomputable def factoringCoreAtScaleFullnessConstant
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) : NNReal :=
  (factoringCoreAtScaleFullnessLoss F D)⁻¹ *
    (factoringCoreAtScaleRefinementConstant F hδ hdisc D w₁ hw₁) ^ 2

/-- Uniform small coefficient in the global thick-fullness estimate. -/
noncomputable def factoringCoreAtScaleUniformFullnessConstant
    (n M N : ℕ) (w₁ : NNReal) : NNReal :=
  (2 * 2 ^ 2 * lambdaInducedSingleWUniform.C * (N + 1))⁻¹ *
    (factoringCoreAtScaleUniformRefinementConstant n M N w₁) ^ 2

/-- The uniform fullness coefficient is no larger than the exact construction coefficient. -/
theorem factoringCoreAtScaleUniformFullnessConstant_le
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    factoringCoreAtScaleUniformFullnessConstant (Module.finrank ℝ E)
        F.innerSet.card D.exponent w₁ ≤
      factoringCoreAtScaleFullnessConstant F hδ hdisc D w₁ hw₁ := by
  rw [factoringCoreAtScaleUniformFullnessConstant, factoringCoreAtScaleFullnessConstant,
    factoringCoreAtScaleFullnessLoss]
  gcongr
  exact factoringCoreAtScaleUniformRefinementConstant_le F hδ hdisc D w₁ hw₁

set_option maxHeartbeats 400000 in
-- This only normalizes the explicit positive loss in `outerThickFamilyAtScale_fullness_raw`.
open Classical in
/-- Global thick fullness in the normalized form used by Proposition 5.1. -/
private theorem outerThickFamilyAtScale_fullness_aux
    {F : FactorFamily E ι κ} {C : ENNReal} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hdim : Module.finrank ℝ E = 3)
    (hshape : F.InnerHasSimilarShape 2)
    (hFrostman : F.HasFrostmanFibers C ∨ F.HasThickenedFrostmanFibers C) :
    (factoringCoreAtScaleFullnessConstant F hδ hdisc D w₁ hw₁ : ENNReal) * C⁻¹ *
        (fullness F.innerSet F.innerBody : ENNReal) ^ 2 *
          (∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
            volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).carrier)) ≤
      ∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
        volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade) := by
  let L : ENNReal := factoringCoreAtScaleFullnessLoss F D
  let c : ENNReal := factoringCoreAtScaleRefinementConstant F hδ hdisc D w₁ hw₁
  let lam : ENNReal := fullness F.innerSet F.innerBody
  let B : ENNReal := ∑ j ∈
    (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
      volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).carrier)
  let Y : ENNReal := ∑ j ∈
    (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
      volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade)
  have hraw : C⁻¹ * (c * lam) ^ 2 * B ≤ L * Y := by
    simpa only [c, lam, B, Y, L, factoringCoreAtScaleFullnessLoss,
      ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat, ENNReal.coe_add,
      ENNReal.coe_natCast, ENNReal.coe_one, mul_assoc] using
        outerThickFamilyAtScale_fullness_raw_aux hδ hdisc D w₁ hw₁ hdim hshape hFrostman
  have hLossPos : 0 < factoringCoreAtScaleFullnessLoss F D := by
    rw [factoringCoreAtScaleFullnessLoss]
    have hCpos : 0 < lambdaInducedSingleWUniform.C := by
      have hdouble (n m : ℕ) (hm : 0 < m) : 0 < cthickeningDoublingConst n m := by
        rw [cthickeningDoublingConst]
        exact div_pos (mul_pos (by positivity) (pow_pos (by exact_mod_cast hm) n))
          (Metric.lt_volume_convexHull.c_pos n)
      have hproj : 0 < projectionVolumeComparisonConst := by
        rw [projectionVolumeComparisonConst]
        exact hdouble 3 4 (by norm_num)
      have hproduct : 0 < productBodyVolumeRatioConst := by
        rw [productBodyVolumeRatioConst]
        exact hdouble 3 9 (by norm_num)
      have haggregate : 0 < aggregateProjectionWeightConst := by
        rw [aggregateProjectionWeightConst]
        exact mul_pos (Metric.volume_comparison.C_pos 3)
          (Metric.volume_comparison.C_pos 2)
      rw [lambdaInducedSingleWUniform.C]
      have h0 : 0 < 68 *
          (ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim.c)⁻¹ :=
        mul_pos (by norm_num) (inv_pos.mpr
          ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim.c_pos)
      have h1 : 0 < 68 *
          (ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim.c)⁻¹ *
          (IsConvexSet.volume_cthickening_ge_of_volume_ge.c 3)⁻¹ ^ 2 :=
        mul_pos h0 (pow_pos (inv_pos.mpr
          (IsConvexSet.volume_cthickening_ge_of_volume_ge.c_pos 3)) 2)
      have h2 : 0 < 68 *
          (ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim.c)⁻¹ *
          (IsConvexSet.volume_cthickening_ge_of_volume_ge.c 3)⁻¹ ^ 2 *
          projectionVolumeComparisonConst ^ 5 := mul_pos h1 (pow_pos hproj 5)
      have h3 : 0 < 68 *
          (ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim.c)⁻¹ *
          (IsConvexSet.volume_cthickening_ge_of_volume_ge.c 3)⁻¹ ^ 2 *
          projectionVolumeComparisonConst ^ 5 * (1 + thickeningRatioConst 3 ^ 2) :=
        mul_pos h2 (by positivity)
      have h4 : 0 < 68 *
          (ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim.c)⁻¹ *
          (IsConvexSet.volume_cthickening_ge_of_volume_ge.c 3)⁻¹ ^ 2 *
          projectionVolumeComparisonConst ^ 5 * (1 + thickeningRatioConst 3 ^ 2) *
          productBodyVolumeRatioConst := mul_pos h3 hproduct
      exact mul_pos h4 (pow_pos haggregate 2)
    positivity
  have hLoss0 : factoringCoreAtScaleFullnessLoss F D ≠ 0 := hLossPos.ne'
  have hL0 : L ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr hLoss0
  have hLtop : L ≠ ⊤ := by
    dsimp only [L, factoringCoreAtScaleFullnessLoss]
    exact ENNReal.coe_ne_top
  rw [factoringCoreAtScaleFullnessConstant, ENNReal.coe_mul, ENNReal.coe_pow,
    ENNReal.coe_inv hLoss0]
  change L⁻¹ * c ^ 2 * C⁻¹ * lam ^ 2 * B ≤ Y
  calc
    L⁻¹ * c ^ 2 * C⁻¹ * lam ^ 2 * B =
        L⁻¹ * (C⁻¹ * (c * lam) ^ 2 * B) := by ring
    _ ≤ L⁻¹ * (L * Y) := by gcongr
    _ = Y := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hL0 hLtop, one_mul]

set_option maxHeartbeats 400000 in
-- This only normalizes the explicit positive loss in the raw summed fullness estimate.
open Classical in
/-- Global thick fullness under the ordinary fibrewise Frostman hypothesis. -/
theorem outerThickFamilyAtScale_fullness
    {F : FactorFamily E ι κ} {C : ENNReal} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hdim : Module.finrank ℝ E = 3)
    (hshape : F.InnerHasSimilarShape 2) (hFrostman : F.HasFrostmanFibers C) :
    (factoringCoreAtScaleFullnessConstant F hδ hdisc D w₁ hw₁ : ENNReal) * C⁻¹ *
        (fullness F.innerSet F.innerBody : ENNReal) ^ 2 *
          (∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
            volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).carrier)) ≤
      ∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
        volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade) :=
  outerThickFamilyAtScale_fullness_aux hδ hdisc D w₁ hw₁ hdim hshape
    (Or.inl hFrostman)

set_option maxHeartbeats 400000 in
-- This only normalizes the explicit positive loss in the raw summed fullness estimate.
open Classical in
/-- Global thick fullness under GWZ Remark 5.3's thickened fibrewise Frostman hypothesis. -/
theorem outerThickFamilyAtScale_fullness_of_thickenedFrostman
    {F : FactorFamily E ι κ} {C : ENNReal} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hdim : Module.finrank ℝ E = 3)
    (hshape : F.InnerHasSimilarShape 2) (hFrostman : F.HasThickenedFrostmanFibers C) :
    (factoringCoreAtScaleFullnessConstant F hδ hdisc D w₁ hw₁ : ENNReal) * C⁻¹ *
        (fullness F.innerSet F.innerBody : ENNReal) ^ 2 *
          (∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
            volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).carrier)) ≤
      ∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
        volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade) :=
  outerThickFamilyAtScale_fullness_aux hδ hdisc D w₁ hw₁ hdim hshape
    (Or.inr hFrostman)

set_option maxHeartbeats 2000000 in
-- The proof removes the finite union of null preliminary fibers before choosing each witness.
open Classical in
/-- The Step 2 outer level controls the average multiplicity of the thick productive family. -/
theorem outerThickFamilyAtScale_outerMultiplicity_lower
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hscale : F.OuterIsAtScale 2 w₁)
    (hne : (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet.Nonempty) :
    (2 ^ F.weightedPipelineOuterExponent hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁) : ENNReal) ≤
      (outerMultiplicityFromLocalBalls.C (Module.finrank ℝ E) : ENNReal) *
        multiplicity (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
          (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody := by
  let G := preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁
  let Q := weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁
  let W := outerThickFamilyAtScale F hδ hdisc D w₁ hw₁
  let u := F.step0.innerSet
  let t := (F.weightedPipelineStep1 hδ hdisc D).outerSet
  let Omega := F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁)
  let k := F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁)
  let l := F.weightedPipelineOuterExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁)
  have hGinnerSet : G.innerSet = F.weightedPipelineInnerSet hδ hdisc D := by
    simpa only [G, preliminaryFactoringFamilyAtScale] using
      F.weightedPipelineFamily_innerSet hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁)
        (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁)) Q.selected w₁
  have hGinnerBody : G.innerBody = step5InnerBody F u t Omega
      (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁)) k Q.selected w₁ := by
    simpa only [G, preliminaryFactoringFamilyAtScale, u, t, Omega, k] using
      F.weightedPipelineFamily_innerBody hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁)
        (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁)) Q.selected w₁
  have hGouterSet : G.outerSet = t := by
    simpa only [G, preliminaryFactoringFamilyAtScale, t] using
      F.weightedPipelineFamily_outerSet hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁)
        (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁)) Q.selected w₁
  have hGparent : G.parent = F.parent :=
    preliminaryFactoringFamilyAtScale_parent F hδ hdisc D w₁ hw₁
  have hGfiber_subset (q : κ) :
      iUnionShade (G.fiber q) G.innerBody ⊆ iUnionShade G.innerSet G.innerBody := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr
      ⟨i, (mem_shadedFactorFamily_fiber_iff G q i).mp hi |>.1, hxi⟩
  let Z : Set E := ⋃ q ∈ G.outerSet.filter (fun q ↦ q ∉ productiveOuterSet G),
    iUnionShade (G.fiber q) G.innerBody
  have hZzero : volume Z = 0 := by
    change volume (⋃ q ∈ ((G.outerSet.filter
      (fun q ↦ q ∉ productiveOuterSet G)) : Set κ),
        iUnionShade (G.fiber q) G.innerBody) = 0
    apply (measure_biUnion_null_iff
      (Set.to_countable ((G.outerSet.filter
        (fun q ↦ q ∉ productiveOuterSet G)) : Set κ))).2
    intro q hq
    obtain ⟨hqG, hqnot⟩ := Finset.mem_filter.mp hq
    by_contra hqvol
    exact hqnot (Finset.mem_filter.mpr ⟨hqG, hqvol⟩)
  have hscale' : ∀ q ∈ W.outerSet,
      (w₁ : ℝ) / 2 ≤ (F.outerBody q).scale ∧
        (F.outerBody q).scale ≤ 2 * (w₁ : ℝ) := by
    intro q hq
    have hqF := outerThickFamilyAtScale_outerSet_subset F hδ hdisc D w₁ hw₁ hq
    have hs := hscale q hqF
    norm_num at hs
    constructor
    · dsimp only [ConvexSpaceBody.scale]
      nlinarith [hs.2]
    · simpa only [ConvexSpaceBody.scale] using hs.1
  have hcover : iUnionShade W.outerSet W.outerBody ⊆
      ⋃ c ∈ Q.selected, Metric.closedBall c (5 * (w₁ : ℝ)) := by
    intro y hy
    obtain ⟨q, hq, hyq⟩ := Set.mem_iUnion₂.mp hy
    change y ∈ Metric.cthickening (2 * (F.outerBody q).scale)
        (iUnionShade (productiveFiber F G q) (zeroExtendedInnerBody F G)) ∩
      Metric.cthickening (F.outerBody q).scale (F.outerBody q).carrier at hyq
    have hy4 : y ∈ Metric.cthickening (4 * (w₁ : ℝ))
        (iUnionShade (productiveFiber F G q) (zeroExtendedInnerBody F G)) :=
      Metric.cthickening_mono (by nlinarith [(hscale' q hq).2]) _ hyq.1
    rw [Metric.cthickening_eq_biUnion_closedBall _ (by positivity)] at hy4
    obtain ⟨z, hzcl, hyz⟩ := Set.mem_iUnion₂.mp hy4
    have hUsel : iUnionShade (productiveFiber F G q) (zeroExtendedInnerBody F G) ⊆
        step5Selection Q.selected w₁ := by
      intro x hx
      have hxG : x ∈ iUnionShade G.innerSet G.innerBody := by
        have href := preliminaryFactoringFamilyAtScale_isCRefinement F hδ hdisc D w₁ hw₁
        have hqprod : q ∈ productiveOuterSet G := by simpa only [W,
          outerThickFamilyAtScale, productiveThickFamily_outerSet, G] using hq
        rw [iUnionShade_zeroExtended_fiber F G href.1.1
          (preliminaryFactoringFamilyAtScale_parent F hδ hdisc D w₁ hw₁) hqprod] at hx
        exact hGfiber_subset q hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxG
      have hxi5 : x ∈ (step5InnerBody F u t Omega
          (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
            (by exact_mod_cast hw₁)) k Q.selected w₁ i).shade := by
        rw [← hGinnerBody]
        exact hxi
      rw [shade_step5InnerBody] at hxi5
      exact hxi5.2
    have hzsel : z ∈ step5Selection Q.selected w₁ :=
      (closure_minimal hUsel (isClosed_step5Selection Q.selected w₁)) hzcl
    obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp hzsel
    refine Set.mem_iUnion₂.mpr ⟨c, hc, Metric.mem_closedBall.mpr ?_⟩
    calc
      dist y c ≤ dist y z + dist z c := dist_triangle _ _ _
      _ ≤ 4 * (w₁ : ℝ) + (w₁ : ℝ) := add_le_add
        (Metric.mem_closedBall.mp hyz) (Metric.mem_closedBall.mp hzc)
      _ = 5 * (w₁ : ℝ) := by ring
  have hQne : Q.selected.Nonempty := by
    obtain ⟨q, hq⟩ := hne
    have hqprod : q ∈ productiveOuterSet G := by
      simpa only [W, outerThickFamilyAtScale, productiveThickFamily_outerSet, G] using hq
    obtain ⟨x, hx⟩ := MeasureTheory.nonempty_of_measure_ne_zero
      (Finset.mem_filter.mp hqprod).2
    exact weightedFactoringPipelineSelection_selected_nonempty hδ hdisc D w₁ hw₁
      (hGfiber_subset q hx)
  have hlocal : ∀ c ∈ Q.selected, ∃ J : Finset κ, J ⊆ W.outerSet ∧
      2 ^ l ≤ J.card ∧ ∀ q ∈ J, ∃ p : E,
        Metric.ball p ((w₁ : ℝ) / 8) ⊆
          (W.outerBody q).shade ∩ Metric.ball c (2 * (w₁ : ℝ)) := by
    intro c hc
    let A : Set E := iUnionShade G.innerSet G.innerBody ∩
      Metric.closedBall c (w₁ : ℝ)
    have hA0 : volume A ≠ 0 := by
      change volume (iUnionShade G.innerSet G.innerBody ∩
        Metric.closedBall c (w₁ : ℝ)) ≠ 0
      rw [hGinnerSet, hGinnerBody]
      simpa only [FactorFamily.weightedPipelineFamily_innerBody] using
        Q.selected_positive c hc
    have hnotSub : ¬ A ⊆ Z := by
      intro hAZ
      exact hA0 (measure_mono_null hAZ hZzero)
    obtain ⟨y, hyA, hyZ⟩ := Set.not_subset.mp hnotSub
    obtain ⟨i₀, hi₀, hyi₀⟩ := Set.mem_iUnion₂.mp hyA.1
    have hyi₀' : y ∈ (step5InnerBody F u t Omega
        (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁)) k Q.selected w₁ i₀).shade := by
      rw [← hGinnerBody]
      exact hyi₀
    rw [shade_step5InnerBody, shade_step3InnerBody] at hyi₀'
    have hyOmega : y ∈ Omega := hyi₀'.1.1.2
    have hySel : y ∈ step5Selection Q.selected w₁ := hyi₀'.2
    let J := MultiplicityFamily.dyadicLevel t
      (fiberMultiplicity F (F.weightedPipelineInnerSet hδ hdisc D)) k y
    have hyfiber : ∀ q ∈ J, y ∈ iUnionShade (G.fiber q) G.innerBody := by
      intro q hq
      have hpos : 0 < fiberMultiplicity F (F.weightedPipelineInnerSet hδ hdisc D) q y :=
        lt_of_lt_of_le (pow_pos (by omega) k) (Finset.mem_filter.mp hq).2.1
      rw [fiberMultiplicity, pointwiseMultiplicity] at hpos
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      have hi' := Finset.mem_filter.mp hi
      have hib := Finset.mem_filter.mp hi'.1
      refine Set.mem_iUnion₂.mpr ⟨i, ?_, ?_⟩
      · apply (mem_shadedFactorFamily_fiber_iff G q i).mpr
        constructor
        · rw [hGinnerSet]
          exact hib.1
        · simpa only [hGparent] using hib.2
      · rw [hGinnerBody]
        rw [shade_step5InnerBody, shade_step3InnerBody]
        refine ⟨⟨⟨hi'.2, hyOmega⟩, ?_⟩, hySel⟩
        rw [hib.2, step3DyadicSet]
        have hinner : {x ∈ u | F.parent x ∈ t} =
            F.weightedPipelineInnerSet hδ hdisc D := by
          simpa only [u, t] using
            (F.weightedPipelineInnerSet_eq_filter hδ hdisc D).symm
        rw [hinner]
        change 2 ^ k ≤ fiberMultiplicity F
            (F.weightedPipelineInnerSet hδ hdisc D) q y ∧
          fiberMultiplicity F (F.weightedPipelineInnerSet hδ hdisc D) q y <
            2 ^ (k + 1)
        simpa only [J] using (Finset.mem_filter.mp hq).2
    refine ⟨J, ?_, ?_, ?_⟩
    · intro q hq
      have hqt : q ∈ t := (Finset.mem_filter.mp hq).1
      have hqG : q ∈ G.outerSet := by
        rw [hGouterSet]
        exact hqt
      have hqprod : q ∈ productiveOuterSet G := by
        apply Finset.mem_filter.mpr
        refine ⟨hqG, ?_⟩
        intro hzero
        apply hyZ
        exact Set.mem_iUnion₂.mpr ⟨q,
          Finset.mem_filter.mpr ⟨hqG, fun hprod ↦
            (Finset.mem_filter.mp hprod).2 hzero⟩, hyfiber q hq⟩
      simpa only [W, outerThickFamilyAtScale, productiveThickFamily_outerSet, G] using hqprod
    · have hb := F.bounds_of_mem_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁) hyOmega
      simpa only [J, l, k, t, Omega] using hb.2.2.1
    · intro q hq
      have hqW : q ∈ W.outerSet := by
        exact (show J ⊆ W.outerSet from by
          intro q' hq'
          have hqt : q' ∈ t := (Finset.mem_filter.mp hq').1
          have hqG : q' ∈ G.outerSet := by
            rw [hGouterSet]
            exact hqt
          have hqprod : q' ∈ productiveOuterSet G := by
            apply Finset.mem_filter.mpr
            refine ⟨hqG, ?_⟩
            intro hzero
            apply hyZ
            exact Set.mem_iUnion₂.mpr ⟨q',
              Finset.mem_filter.mpr ⟨hqG, fun hprod ↦
                (Finset.mem_filter.mp hprod).2 hzero⟩, hyfiber q' hq'⟩
          simpa only [W, outerThickFamilyAtScale,
            productiveThickFamily_outerSet, G] using hqprod) hq
      refine ⟨y, ?_⟩
      intro z hz
      have hyqG := hyfiber q hq
      have hqprod : q ∈ productiveOuterSet G := by
        simpa only [W, outerThickFamilyAtScale, productiveThickFamily_outerSet, G] using hqW
      have hyq : y ∈ iUnionShade (productiveFiber F G q)
          (zeroExtendedInnerBody F G) := by
        rw [iUnionShade_zeroExtended_fiber F G
          (preliminaryFactoringFamilyAtScale_isCRefinement F hδ hdisc D w₁ hw₁).1.1
          (preliminaryFactoringFamilyAtScale_parent F hδ hdisc D w₁ hw₁) hqprod]
        exact hyqG
      have hyrange := hscale' q hqW
      constructor
      · change z ∈ Metric.cthickening (2 * (F.outerBody q).scale)
            (iUnionShade (productiveFiber F G q) (zeroExtendedInnerBody F G)) ∩
          Metric.cthickening (F.outerBody q).scale (F.outerBody q).carrier
        constructor
        · exact Metric.mem_cthickening_of_dist_le z y _ _ hyq (by
            exact (le_of_lt (Metric.mem_ball.mp hz)).trans (by nlinarith [hyrange.1]))
        · have hycarrier : y ∈ (F.outerBody q).carrier := by
            obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hyq
            have hi' := (mem_productiveFiber_iff F G q i).mp hi
            have hyiCarrier := (zeroExtendedInnerBody F G i).shade_subset hyi
            rw [zeroExtendedInnerBody_toConvexSpaceBody F G
              (preliminaryFactoringFamilyAtScale_innerBody F hδ hdisc D w₁ hw₁)] at hyiCarrier
            change y ∈ F.outerBody q
            simpa only [hi'.2.2] using F.inner_le_parent i hi'.1 hyiCarrier
          exact Metric.mem_cthickening_of_dist_le z y _ _ hycarrier (by
            exact (le_of_lt (Metric.mem_ball.mp hz)).trans (by nlinarith [hyrange.1]))
      · apply Metric.mem_ball.mpr
        calc
          dist z c ≤ dist z y + dist y c := dist_triangle _ _ _
          _ < (w₁ : ℝ) / 8 + (w₁ : ℝ) := add_lt_add_of_lt_of_le
            (Metric.mem_ball.mp hz) (Metric.mem_closedBall.mp hyA.2)
          _ < 2 * (w₁ : ℝ) := by nlinarith [show (0 : ℝ) < (w₁ : ℝ) by exact_mod_cast hw₁]
  have hlpos : 0 < 2 ^ l := pow_pos (by omega) l
  simpa only [W, Q, l, Nat.cast_pow, Nat.cast_ofNat] using
    outerMultiplicity_lower_of_local_balls W.outerSet W.outerBody
    Q.selected w₁ (2 ^ l) hw₁ hlpos hQne Q.selected_separated hcover hlocal

open Classical in
/-- Every productive final fiber has scalar multiplicity at least its common Step 2 dyadic
level. -/
theorem outerThickFamilyAtScale_fiberMultiplicity_lower
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) {j : κ}
    (hj : j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet) :
    (2 ^ F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁) : ENNReal) ≤
      multiplicity ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
        (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody := by
  let G := preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁
  let C := outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁
  have hjprod : j ∈ productiveOuterSet G := by
    simpa only [outerThickFamilyAtScale, productiveThickFamily_outerSet, G] using hj
  have hnull : volume (iUnionShade (C.fiber j) C.innerBody) ≠ 0 := by
    simpa only [C, outerCountingFamilyAtScale,
      productiveCountingFamily_fiber_eq, productiveCountingFamily_innerBody, G] using
      volume_iUnionShade_zeroExtended_fiber_ne_zero F G
        (preliminaryFactoringFamilyAtScale_isCRefinement F hδ hdisc D w₁ hw₁).1.1
        (preliminaryFactoringFamilyAtScale_parent F hδ hdisc D w₁ hw₁) hjprod
  have hlower :
      (2 ^ F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁) : ENNReal) ≤ multiplicity (C.fiber j) C.innerBody := by
    apply le_multiplicity_of_le_pointwiseMultiplicity _ _ hnull
    intro x hx
    exact_mod_cast (outerCountingFamilyAtScale_fiber_multiplicity
      hδ hdisc D w₁ hw₁ hx).1
  simpa only [C, outerCountingFamilyAtScale, outerThickFamilyAtScale,
    productiveCountingFamily, productiveThickFamily,
    productiveCountingFamily_innerSet, productiveThickFamily_innerSet,
    productiveCountingFamily_innerBody, productiveThickFamily_innerBody,
    ShadedFactorFamily.fiber] using hlower

open Classical in
/-- Membership in a counting shade is exactly membership in the Step 2 outer dyadic level. -/
theorem mem_weightedOuterDyadicLevel_of_mem_outerCountingShade
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) {j : κ} {x : E}
    (hj : j ∈ (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet)
    (hx : x ∈ ((outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade) :
    j ∈ MultiplicityFamily.dyadicLevel (F.weightedPipelineStep1 hδ hdisc D).outerSet
      (fiberMultiplicity F (F.weightedPipelineInnerSet hδ hdisc D))
      (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁)) x := by
  let G := preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁
  have href := preliminaryFactoringFamilyAtScale_isCRefinement F hδ hdisc D w₁ hw₁
  have hparent := preliminaryFactoringFamilyAtScale_parent F hδ hdisc D w₁ hw₁
  have hjprod : j ∈ productiveOuterSet G := by
    simpa only [outerCountingFamilyAtScale, productiveCountingFamily_outerSet, G] using hj
  have hxG : x ∈ iUnionShade (G.fiber j) G.innerBody := by
    rw [← iUnionShade_zeroExtended_fiber F G href.1.1 hparent hjprod]
    simpa only [outerCountingFamilyAtScale,
      productiveCountingFamily_outerBody_shade, G] using hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxG
  have hi' := (mem_shadedFactorFamily_fiber_iff G j i).mp hi
  have hbody : G.innerBody = step5InnerBody F F.step0.innerSet
      (F.weightedPipelineStep1 hδ hdisc D).outerSet
      (F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
      (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁))
      (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
      (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).selected w₁ := by
    simpa only [G, preliminaryFactoringFamilyAtScale] using
      F.weightedPipelineFamily_innerBody hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁)
        (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁))
        (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).selected w₁
  have hxi' := hxi
  rw [hbody, shade_step5InnerBody, shade_step3InnerBody] at hxi'
  have hlevel := hxi'.1.2
  have hip : F.parent i = j := by simpa only [← hparent] using hi'.2
  rw [step3DyadicSet, hip] at hlevel
  have hinner : {q ∈ F.step0.innerSet |
      F.parent q ∈ (F.weightedPipelineStep1 hδ hdisc D).outerSet} =
      F.weightedPipelineInnerSet hδ hdisc D :=
    (F.weightedPipelineInnerSet_eq_filter hδ hdisc D).symm
  rw [hinner] at hlevel
  apply Finset.mem_filter.mpr
  constructor
  · simpa only [G, preliminaryFactoringFamilyAtScale,
      FactorFamily.weightedPipelineFamily_outerSet] using
      (Finset.mem_filter.mp hjprod).1
  · exact hlevel

open Classical in
/-- The final counting union lies in the measurable Step 2 level set. -/
theorem outerCountingFamilyAtScale_subset_weightedPipelineSet
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    iUnionShade (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody ⊆
      F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁) := by
  intro x hx
  rw [iUnionShade_outerCountingFamilyAtScale_eq_inner] at hx
  have hxG := iUnionShade_outerCountingFamilyAtScale_subset_preliminary
    F hδ hdisc D w₁ hw₁ hx
  let G := preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁
  let Q := weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁
  obtain ⟨i, _, hxi⟩ := Set.mem_iUnion₂.mp hxG
  have hbody : G.innerBody = step5InnerBody F F.step0.innerSet
      (F.weightedPipelineStep1 hδ hdisc D).outerSet
      (F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
      (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁))
      (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁))
      Q.selected w₁ := by
    simpa only [G, preliminaryFactoringFamilyAtScale] using
      F.weightedPipelineFamily_innerBody hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁)
        (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁)) Q.selected w₁
  rw [hbody, shade_step5InnerBody, shade_step3InnerBody] at hxi
  exact hxi.1.1.2

open Classical in
/-- Productive restriction preserves the Step 2 upper bound for the exact counting outer family. -/
theorem outerCountingFamilyAtScale_outerPointwiseMultiplicity_lt
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) {x : E}
    (hx : x ∈ iUnionShade (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
      (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody) :
    pointwiseMultiplicity (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody x <
      2 ^ (F.weightedPipelineOuterExponent hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁) + 1) := by
  let J := MultiplicityFamily.dyadicLevel
    (F.weightedPipelineStep1 hδ hdisc D).outerSet
    (fiberMultiplicity F (F.weightedPipelineInnerSet hδ hdisc D))
    (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁)) x
  have hsub : {j ∈ (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet |
      x ∈ ((outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade} ⊆ J := by
    intro j hj
    exact mem_weightedOuterDyadicLevel_of_mem_outerCountingShade hδ hdisc D w₁ hw₁
      (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
  have hOmega := outerCountingFamilyAtScale_subset_weightedPipelineSet
    hδ hdisc D w₁ hw₁ hx
  have hb := F.bounds_of_mem_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
    (by exact_mod_cast hw₁) hOmega
  rw [pointwiseMultiplicity]
  exact (Finset.card_le_card hsub).trans_lt (by
    simpa only [J, pow_succ, mul_comm] using hb.2.2.2)

set_option maxHeartbeats 1000000 in
-- The proof transports one common Step 2 level through a null-fiber restriction.
open Classical in
/-- The Step 2 outer dyadic lower bound survives deletion of null fibers at the scalar level. -/
theorem outerCountingFamilyAtScale_outerMultiplicity_lower
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁)
    (hne : (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet.Nonempty) :
    (2 ^ F.weightedPipelineOuterExponent hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁) : ENNReal) ≤
      multiplicity (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody := by
  let G := preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁
  let C := outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁
  let Q := weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁
  let u := F.step0.innerSet
  let t := (F.weightedPipelineStep1 hδ hdisc D).outerSet
  let Omega := F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁)
  let k := F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁)
  let l := F.weightedPipelineOuterExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁)
  have href := preliminaryFactoringFamilyAtScale_isCRefinement F hδ hdisc D w₁ hw₁
  have hGinnerSet : G.innerSet = F.weightedPipelineInnerSet hδ hdisc D := by
    simpa only [G, preliminaryFactoringFamilyAtScale] using
      F.weightedPipelineFamily_innerSet hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁)
        (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁)) Q.selected w₁
  have hGinnerBody : G.innerBody = step5InnerBody F u t Omega
      (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁)) k Q.selected w₁ := by
    simpa only [G, preliminaryFactoringFamilyAtScale, u, t, Omega, k] using
      F.weightedPipelineFamily_innerBody hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁)
        (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁)) Q.selected w₁
  have hGouterSet : G.outerSet = t := by
    simpa only [G, preliminaryFactoringFamilyAtScale, t] using
      F.weightedPipelineFamily_outerSet hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁)
        (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
          (by exact_mod_cast hw₁)) Q.selected w₁
  have hGparent : G.parent = F.parent :=
    preliminaryFactoringFamilyAtScale_parent F hδ hdisc D w₁ hw₁
  let Z : Set E := ⋃ q ∈ G.outerSet.filter (fun q ↦ q ∉ productiveOuterSet G),
    iUnionShade (G.fiber q) G.innerBody
  have hZzero : volume Z = 0 := by
    change volume (⋃ q ∈ ((G.outerSet.filter
      (fun q ↦ q ∉ productiveOuterSet G)) : Set κ),
        iUnionShade (G.fiber q) G.innerBody) = 0
    apply (measure_biUnion_null_iff
      (Set.to_countable ((G.outerSet.filter
        (fun q ↦ q ∉ productiveOuterSet G)) : Set κ))).2
    intro q hq
    obtain ⟨hqG, hqnot⟩ := Finset.mem_filter.mp hq
    by_contra hqvol
    exact hqnot (Finset.mem_filter.mpr ⟨hqG, hqvol⟩)
  have hUnion0 : volume (iUnionShade C.outerSet C.outerBody) ≠ 0 := by
    obtain ⟨j, hj⟩ := hne
    have hjprod : j ∈ productiveOuterSet G := by
      simpa only [C, outerCountingFamilyAtScale,
        productiveCountingFamily_outerSet, G] using hj
    have hjzero := volume_iUnionShade_zeroExtended_fiber_ne_zero F G href.1.1
      hGparent hjprod
    intro hzero
    apply hjzero
    exact measure_mono_null (Set.subset_iUnion₂_of_subset j hj (Set.Subset.refl _)) hzero
  apply le_multiplicity_of_ae_le_pointwiseMultiplicity _ _ hUnion0
  have hAE : ∀ᵐ x, x ∉ Z := by
    rw [ae_iff]
    have hset : {x : E | ¬x ∉ Z} = Z := by ext x; simp
    rw [hset]
    exact hZzero
  filter_upwards [hAE] with x hxZ
  intro hxC
  have hxInner : x ∈ iUnionShade C.innerSet C.innerBody := by
    rw [← iUnionShade_outerCountingFamilyAtScale_eq_inner F hδ hdisc D w₁ hw₁]
    exact hxC
  have hxG := iUnionShade_outerCountingFamilyAtScale_subset_preliminary
    F hδ hdisc D w₁ hw₁ hxInner
  obtain ⟨i₀, _, hxi₀⟩ := Set.mem_iUnion₂.mp hxG
  have hxi₀' : x ∈ (step5InnerBody F u t Omega
      (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁)) k Q.selected w₁ i₀).shade := by
    rw [← hGinnerBody]
    exact hxi₀
  rw [shade_step5InnerBody, shade_step3InnerBody] at hxi₀'
  have hxOmega : x ∈ Omega := hxi₀'.1.1.2
  have hxSel : x ∈ step5Selection Q.selected w₁ := hxi₀'.2
  let J := MultiplicityFamily.dyadicLevel t
    (fiberMultiplicity F (F.weightedPipelineInnerSet hδ hdisc D)) k x
  have hxFiber : ∀ q ∈ J, x ∈ iUnionShade (G.fiber q) G.innerBody := by
    intro q hq
    have hpos : 0 < fiberMultiplicity F (F.weightedPipelineInnerSet hδ hdisc D) q x :=
      lt_of_lt_of_le (pow_pos (by omega) k) (Finset.mem_filter.mp hq).2.1
    rw [fiberMultiplicity, pointwiseMultiplicity] at hpos
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    have hi' := Finset.mem_filter.mp hi
    have hib := Finset.mem_filter.mp hi'.1
    refine Set.mem_iUnion₂.mpr ⟨i, ?_, ?_⟩
    · apply (mem_shadedFactorFamily_fiber_iff G q i).mpr
      constructor
      · rw [hGinnerSet]
        exact hib.1
      · simpa only [hGparent] using hib.2
    · rw [hGinnerBody, shade_step5InnerBody, shade_step3InnerBody]
      refine ⟨⟨⟨hi'.2, hxOmega⟩, ?_⟩, hxSel⟩
      rw [hib.2, step3DyadicSet]
      have hinner : {a ∈ u | F.parent a ∈ t} =
          F.weightedPipelineInnerSet hδ hdisc D := by
        simpa only [u, t] using
          (F.weightedPipelineInnerSet_eq_filter hδ hdisc D).symm
      rw [hinner]
      change 2 ^ k ≤ fiberMultiplicity F
          (F.weightedPipelineInnerSet hδ hdisc D) q x ∧
        fiberMultiplicity F (F.weightedPipelineInnerSet hδ hdisc D) q x <
          2 ^ (k + 1)
      simpa only [J] using (Finset.mem_filter.mp hq).2
  have hsub : J ⊆ {q ∈ C.outerSet | x ∈ (C.outerBody q).shade} := by
    intro q hq
    have hqG : q ∈ G.outerSet := by
      rw [hGouterSet]
      exact (Finset.mem_filter.mp hq).1
    have hqprod : q ∈ productiveOuterSet G := by
      apply Finset.mem_filter.mpr
      refine ⟨hqG, ?_⟩
      intro hzero
      apply hxZ
      exact Set.mem_iUnion₂.mpr ⟨q,
        Finset.mem_filter.mpr ⟨hqG, fun hp ↦ (Finset.mem_filter.mp hp).2 hzero⟩,
        hxFiber q hq⟩
    have hqC : q ∈ C.outerSet := by
      simpa only [C, outerCountingFamilyAtScale,
        productiveCountingFamily_outerSet, G] using hqprod
    apply Finset.mem_filter.mpr
    refine ⟨hqC, ?_⟩
    rw [show (C.outerBody q).shade =
        iUnionShade (productiveFiber F G q) (zeroExtendedInnerBody F G) by
      simp only [C, outerCountingFamilyAtScale,
        productiveCountingFamily_outerBody_shade, G]]
    rw [iUnionShade_zeroExtended_fiber F G href.1.1 hGparent hqprod]
    exact hxFiber q hq
  have hb := F.bounds_of_mem_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
    (by exact_mod_cast hw₁) hxOmega
  rw [pointwiseMultiplicity]
  exact_mod_cast (hb.2.2.1.trans (Finset.card_le_card hsub))

open Classical in
/-- Corrected Item 3: the exact counting family has the one-sided pointwise bound needed
downstream.  No corresponding assertion is made for the thick shading. -/
theorem outerCountingFamilyAtScale_pointwiseMultiplicity_le_mul_multiplicity
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) {x : E}
    (hx : x ∈ iUnionShade (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
      (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody) :
    (pointwiseMultiplicity (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody x : ENNReal) ≤
      2 * multiplicity (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody := by
  let l := F.weightedPipelineOuterExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁)
  have hne : (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet.Nonempty := by
    obtain ⟨j, hj, _⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨j, hj⟩
  have hlower : (2 ^ l : ENNReal) ≤
      multiplicity (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody := by
    simpa only [l] using
      outerCountingFamilyAtScale_outerMultiplicity_lower hδ hdisc D w₁ hw₁ hne
  have hupper := outerCountingFamilyAtScale_outerPointwiseMultiplicity_lt
    hδ hdisc D w₁ hw₁ hx
  calc
    (pointwiseMultiplicity (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody x : ENNReal) ≤
      (2 ^ (l + 1) : ℕ) := by exact_mod_cast hupper.le
    _ = 2 * (2 ^ l : ENNReal) := by
      rw [pow_succ]
      norm_num
      ring
    _ ≤ 2 * multiplicity (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody := by gcongr

open Classical in
/-- A nonempty productive output forces the internally selected Step 5 cover to be nonempty. -/
theorem weightedFactoringPipelineSelection_selected_nonempty_of_outer
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁)
    (hne : (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet.Nonempty) :
    (weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁).selected.Nonempty := by
  let G := preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁
  obtain ⟨j, hj⟩ := hne
  have hjprod : j ∈ productiveOuterSet G := by
    simpa only [outerThickFamilyAtScale, productiveThickFamily_outerSet, G] using hj
  obtain ⟨x, hx⟩ := MeasureTheory.nonempty_of_measure_ne_zero
    (Finset.mem_filter.mp hjprod).2
  apply weightedFactoringPipelineSelection_selected_nonempty hδ hdisc D w₁ hw₁
  · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr
      ⟨i, (mem_shadedFactorFamily_fiber_iff G j i).mp hi |>.1, hxi⟩

open Classical in
/-- The retained-mass constant is nonzero whenever the productive output is nonempty. -/
theorem factoringCoreAtScaleRefinementConstant_pos
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁)
    (hne : (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet.Nonempty) :
    0 < factoringCoreAtScaleRefinementConstant F hδ hdisc D w₁ hw₁ := by
  let Q := weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁
  have hne' := hne
  obtain ⟨j, hj⟩ := hne
  have hjG : j ∈ (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet :=
    (Finset.mem_filter.mp hj).1
  have hjImage : j ∈ F.step0.innerSet.image F.parent := by
    exact F.weightedPipelineFamily_outerSet_subset_image hδ hdisc D
      (w₁ : ℝ) (by exact_mod_cast hw₁)
      (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁)) Q.selected w₁ hjG
  have hbounds := F.normalizedFiberVolume_mem_Icc_step0Image hδ hdisc D.exponent
    D.volume_outer_le hjImage
  have hABENN : (Kakeya.weightedStep1LowerBd (Module.finrank ℝ E) D.exponent : ENNReal) ≤
      (Kakeya.weightedStep1UpperBd F.innerSet.card : ENNReal) := hbounds.1.trans hbounds.2
  have hAB : Kakeya.weightedStep1LowerBd (Module.finrank ℝ E) D.exponent ≤
      Kakeya.weightedStep1UpperBd F.innerSet.card := by exact_mod_cast hABENN
  have hstep1 : 0 < FactorFamily.weightedStep1AtScaleConstant
      (Module.finrank ℝ E) F.innerSet.card D.exponent :=
    FactorFamily.weightedStep1AtScaleConstant_pos hAB
  have hQne : Q.selected.Nonempty := by
    exact weightedFactoringPipelineSelection_selected_nonempty_of_outer
      hδ hdisc D w₁ hw₁ hne'
  have hcoverNe : Q.cover.Nonempty := hQne.mono Q.selected_subset
  have honeCover : (1 : NNReal) ≤ Q.cover.card := by
    exact_mod_cast (Finset.card_pos.mpr hcoverNe : 0 < Q.cover.card)
  rw [factoringCoreAtScaleRefinementConstant]
  exact Kakeya.factoringWeightedPipelineSelfRefinementConstant_pos hstep1 honeCover

open Classical in
/-- The uniform retained-mass coefficient is positive whenever the productive output is
nonempty. -/
theorem factoringCoreAtScaleUniformRefinementConstant_pos
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁)
    (hne : (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet.Nonempty) :
    0 < factoringCoreAtScaleUniformRefinementConstant (Module.finrank ℝ E)
      F.innerSet.card D.exponent w₁ := by
  let Q := weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁
  obtain ⟨j, hj⟩ := hne
  have hjG : j ∈ (preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet :=
    (Finset.mem_filter.mp hj).1
  have hjImage : j ∈ F.step0.innerSet.image F.parent := by
    exact F.weightedPipelineFamily_outerSet_subset_image hδ hdisc D
      (w₁ : ℝ) (by exact_mod_cast hw₁)
      (F.measurableSet_weightedPipelineSet hδ hdisc D (w₁ : ℝ)
        (by exact_mod_cast hw₁)) Q.selected w₁ hjG
  have hbounds := F.normalizedFiberVolume_mem_Icc_step0Image hδ hdisc D.exponent
    D.volume_outer_le hjImage
  have hABENN : (Kakeya.weightedStep1LowerBd (Module.finrank ℝ E) D.exponent : ENNReal) ≤
      (Kakeya.weightedStep1UpperBd F.innerSet.card : ENNReal) := hbounds.1.trans hbounds.2
  have hAB : Kakeya.weightedStep1LowerBd (Module.finrank ℝ E) D.exponent ≤
      Kakeya.weightedStep1UpperBd F.innerSet.card := by exact_mod_cast hABENN
  have hstep1 : 0 < FactorFamily.weightedStep1AtScaleConstant
      (Module.finrank ℝ E) F.innerSet.card D.exponent :=
    FactorFamily.weightedStep1AtScaleConstant_pos hAB
  rw [factoringCoreAtScaleUniformRefinementConstant]
  exact Kakeya.factoringWeightedPipelineSelfRefinementConstant_pos hstep1
    (one_le_factoringCoreAtScaleCoverCardBound _ hw₁)

open Classical in
/-- Positive input shading mass forces the productive outer family to be nonempty.

The proof deliberately runs through the pre-Step-5 mass ledger.  It first obtains a point of the
Step 3 union, hence a centre in the internally constructed Step 5 cover.  Only then is the full
pipeline refinement constant known to be positive.  Thus this argument does not assume the
nonemptiness of the output it is proving. -/
theorem outerThickFamilyAtScale_outerSet_nonempty_of_sum_volume_shade_pos
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet.Nonempty := by
  let hr : (0 : ℝ) < (w₁ : ℝ) := by exact_mod_cast hw₁
  let Omega := F.weightedPipelineSet hδ hdisc D (w₁ : ℝ) hr
  let hOmega : MeasurableSet Omega := F.measurableSet_weightedPipelineSet hδ hdisc D _ hr
  let G₃Body := step3InnerBody F F.step0.innerSet
    (F.weightedPipelineStep1 hδ hdisc D).outerSet Omega hOmega
    (F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) hr)
  let Q := weightedFactoringPipelineSelection F hδ hdisc D w₁ hw₁
  let G := preliminaryFactoringFamilyAtScale F hδ hdisc D w₁ hw₁
  have hstep1Outer : (F.weightedPipelineStep1 hδ hdisc D).outerSet.Nonempty := by
    rw [F.weightedPipelineStep1_eq hδ hdisc D]
    exact F.outerSet_weightedStep1AtScale_nonempty hδ hdisc D.exponent
      D.volume_outer_le hmass
  obtain ⟨j, hj⟩ := hstep1Outer
  have hjImage : j ∈ F.step0.innerSet.image F.parent :=
    F.outerSet_weightedStep1AtScale_subset_image hδ hdisc D.exponent
      D.volume_outer_le (by
        rw [← F.weightedPipelineStep1_eq hδ hdisc D]
        exact hj)
  have hbounds := F.normalizedFiberVolume_mem_Icc_step0Image hδ hdisc D.exponent
    D.volume_outer_le hjImage
  have hABENN :
      (Kakeya.weightedStep1LowerBd (Module.finrank ℝ E) D.exponent : ENNReal) ≤
        (Kakeya.weightedStep1UpperBd F.innerSet.card : ENNReal) :=
    hbounds.1.trans hbounds.2
  have hAB : Kakeya.weightedStep1LowerBd (Module.finrank ℝ E) D.exponent ≤
      Kakeya.weightedStep1UpperBd F.innerSet.card := by
    exact_mod_cast hABENN
  have hstep1 : 0 < FactorFamily.weightedStep1AtScaleConstant
      (Module.finrank ℝ E) F.innerSet.card D.exponent :=
    FactorFamily.weightedStep1AtScaleConstant_pos hAB
  have href1 := F.isCRefinement_weightedStep1AtScale hδ hdisc D.exponent D.volume_outer_le
  have hsum1 : 0 < ∑ i ∈ F.weightedPipelineInnerSet hδ hdisc D,
      volume (F.innerBody i).shade := by
    have hcoef : 0 <
        (((FactorFamily.weightedStep1AtScaleConstant
          (Module.finrank ℝ E) F.innerSet.card D.exponent)⁻¹ : NNReal) : ENNReal) := by
      positivity
    have hpos := ENNReal.mul_pos hcoef.ne' hmass.ne'
    apply hpos.trans_le
    rw [F.weightedPipelineInnerSet_eq_step1, F.weightedPipelineStep1_eq hδ hdisc D]
    simpa only [F.innerBody_weightedStep1AtScale] using href1.2
  have hstep23 : 0 <
      ((Kakeya.factoringStep2Step3Constant F.innerSet.card : ℕ) : ENNReal)⁻¹ := by
    exact ENNReal.inv_pos.mpr (by simp)
  have hsum3 : 0 < ∑ i ∈ F.weightedPipelineInnerSet hδ hdisc D,
      volume (G₃Body i).shade := by
    have hpos := ENNReal.mul_pos hstep23.ne' hsum1.ne'
    apply hpos.trans_le
    simpa only [G₃Body, Omega, hOmega] using
      weightedPipelineStep2Step3_mass F hδ hdisc D (w₁ : ℝ) hr hOmega
  obtain ⟨i, hi, hvi⟩ := Finset.sum_pos_iff.mp hsum3
  obtain ⟨x, hxi⟩ := MeasureTheory.nonempty_of_measure_ne_zero hvi.ne'
  have hx3 : x ∈ iUnionShade (F.weightedPipelineInnerSet hδ hdisc D) G₃Body :=
    Set.mem_iUnion₂.mpr ⟨i, hi, hxi⟩
  have hcover : Q.cover.Nonempty := by
    have hxcover := Q.covers_step3 (by
      simpa only [Q, G₃Body, Omega, hOmega] using hx3)
    obtain ⟨c, hc, _⟩ := Set.mem_iUnion₂.mp hxcover
    exact ⟨c, hc⟩
  have honeCover : (1 : NNReal) ≤ Q.cover.card := by
    exact_mod_cast (Finset.card_pos.mpr hcover : 0 < Q.cover.card)
  have hcore : 0 < factoringCoreAtScaleRefinementConstant F hδ hdisc D w₁ hw₁ := by
    rw [factoringCoreAtScaleRefinementConstant]
    exact Kakeya.factoringWeightedPipelineSelfRefinementConstant_pos hstep1 honeCover
  have href := preliminaryFactoringFamilyAtScale_isCRefinement F hδ hdisc D w₁ hw₁
  have hsumG : 0 < ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := by
    have hcoef : 0 <
        ((factoringCoreAtScaleRefinementConstant F hδ hdisc D w₁ hw₁ : NNReal) :
          ENNReal) := by exact_mod_cast hcore
    exact (ENNReal.mul_pos hcoef.ne' hmass.ne').trans_le href.2
  obtain ⟨i, hiG, hviG⟩ := Finset.sum_pos_iff.mp hsumG
  have hjprod : G.parent i ∈ productiveOuterSet G := by
    apply Finset.mem_filter.mpr
    refine ⟨G.parent_mem i hiG, ?_⟩
    have hmono : volume (G.innerBody i).shade ≤
        volume (iUnionShade (G.fiber (G.parent i)) G.innerBody) := by
      apply measure_mono
      exact Set.subset_iUnion₂_of_subset i
        ((mem_shadedFactorFamily_fiber_iff G (G.parent i) i).2 ⟨hiG, rfl⟩)
        (Set.Subset.refl _)
    exact ne_of_gt (hviG.trans_le hmono)
  exact ⟨G.parent i, by
    simpa only [outerThickFamilyAtScale, productiveThickFamily_outerSet, G] using hjprod⟩

/-- Positive input shading mass gives a counting union of positive measure.  Productive
restriction cannot use positivity of the thick union for this purpose, since the counting shade
is smaller; instead the proof embeds one non-null productive fiber into the exact counting
union. -/
theorem outerCountingFamilyAtScale_union_volume_ne_zero_of_input_mass_pos
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    volume (iUnionShade (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
      (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody) ≠ 0 := by
  rw [iUnionShade_outerCountingFamilyAtScale_eq_inner]
  obtain ⟨j, hj⟩ :=
    outerThickFamilyAtScale_outerSet_nonempty_of_sum_volume_shade_pos
      hδ hdisc D w₁ hw₁ hmass
  have hfiber :
      volume (iUnionShade ((outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
        (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody) ≠ 0 := by
    simpa only [outerCountingFamilyAtScale, outerThickFamilyAtScale,
      productiveCountingFamily_fiber_eq, productiveThickFamily_fiber_eq,
      productiveCountingFamily_innerBody, productiveThickFamily_innerBody] using
        outerThickFamilyAtScale_fiber_volume_ne_zero F hδ hdisc D w₁ hw₁ hj
  intro hzero
  apply hfiber
  apply measure_mono_null _ hzero
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨i,
    (mem_shadedFactorFamily_fiber_iff
      (outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁) j i).mp hi |>.1, hxi⟩

/-- **Constant in the product estimate of the corrected Proposition 5.1.**  It consists of the
global Step 2 factor `4`, the inverse retained-mass fraction, and the local-ball outer
multiplicity loss. -/
noncomputable def factoringCoreAtScaleProductConstant
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) : NNReal :=
  4 * (factoringCoreAtScaleRefinementConstant F hδ hdisc D w₁ hw₁)⁻¹ *
    outerMultiplicityFromLocalBalls.C (Module.finrank ℝ E)

/-- Uniform large coefficient in the fiberwise multiplicity-product estimate. -/
noncomputable def factoringCoreAtScaleUniformProductConstant
    (n M N : ℕ) (w₁ : NNReal) : NNReal :=
  4 * (factoringCoreAtScaleUniformRefinementConstant n M N w₁)⁻¹ *
    outerMultiplicityFromLocalBalls.C n

/-- On a nonempty productive output, the uniform product coefficient dominates the exact
construction coefficient. -/
theorem factoringCoreAtScaleProductConstant_le_uniform
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁)
    (hne : (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet.Nonempty) :
    factoringCoreAtScaleProductConstant F hδ hdisc D w₁ hw₁ ≤
      factoringCoreAtScaleUniformProductConstant (Module.finrank ℝ E)
        F.innerSet.card D.exponent w₁ := by
  have hpos := factoringCoreAtScaleUniformRefinementConstant_pos
    hδ hdisc D w₁ hw₁ hne
  have href := factoringCoreAtScaleUniformRefinementConstant_le F hδ hdisc D w₁ hw₁
  rw [factoringCoreAtScaleProductConstant, factoringCoreAtScaleUniformProductConstant]
  gcongr

open Classical in
/-- The corrected Item 5 product inequality holds for every productive outer block.  The outer
multiplicity is taken on the thick family, while the inner fiber is the common final inner
family. -/
theorem outerThickFamilyAtScale_multiplicity_product
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hscale : F.OuterIsAtScale 2 w₁)
    {j : κ} (hj : j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet) :
    multiplicity F.innerSet F.innerBody ≤
      (factoringCoreAtScaleProductConstant F hδ hdisc D w₁ hw₁ : ENNReal) *
        multiplicity (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
          (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody *
        multiplicity ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
          (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody := by
  let W := outerThickFamilyAtScale F hδ hdisc D w₁ hw₁
  let C := outerCountingFamilyAtScale F hδ hdisc D w₁ hw₁
  let c := factoringCoreAtScaleRefinementConstant F hδ hdisc D w₁ hw₁
  let k := F.weightedPipelineExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁)
  let l := F.weightedPipelineOuterExponent hδ hdisc D (w₁ : ℝ) (by exact_mod_cast hw₁)
  have hne : W.outerSet.Nonempty := ⟨j, hj⟩
  have hcpos : 0 < c := by
    exact factoringCoreAtScaleRefinementConstant_pos hδ hdisc D w₁ hw₁ hne
  have hcne : c ≠ 0 := hcpos.ne'
  have href : multiplicity F.innerSet F.innerBody ≤
      (c : ENNReal)⁻¹ * multiplicity C.innerSet C.innerBody := by
    apply multiplicity_le_of_isCRefinement (s := F.innerSet) (V := F.innerBody)
      (s' := C.innerSet) (V' := C.innerBody) hcne
    simpa only [C, c] using
      outerCountingFamilyAtScale_isCRefinement F hδ hdisc D w₁ hw₁
  have hglobal : multiplicity C.innerSet C.innerBody ≤
      4 * ((2 ^ k : ENNReal) * (2 ^ l : ENNReal)) := by
    simpa only [C, k, l, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      outerCountingFamilyAtScale_multiplicity_le hδ hdisc D w₁ hw₁
  have houter : (2 ^ l : ENNReal) ≤
      (outerMultiplicityFromLocalBalls.C (Module.finrank ℝ E) : ENNReal) *
        multiplicity W.outerSet W.outerBody := by
    simpa only [W, l] using
      outerThickFamilyAtScale_outerMultiplicity_lower hδ hdisc D w₁ hw₁ hscale hne
  have hfiber : (2 ^ k : ENNReal) ≤ multiplicity (W.fiber j) W.innerBody := by
    simpa only [W, k] using
      outerThickFamilyAtScale_fiberMultiplicity_lower hδ hdisc D w₁ hw₁ hj
  calc
    multiplicity F.innerSet F.innerBody ≤
        (c : ENNReal)⁻¹ * multiplicity C.innerSet C.innerBody := href
    _ ≤ (c : ENNReal)⁻¹ * (4 * ((2 ^ k : ENNReal) * (2 ^ l : ENNReal))) := by
      gcongr
    _ = (4 * (c : ENNReal)⁻¹) * (2 ^ l : ENNReal) * (2 ^ k : ENNReal) := by ring
    _ ≤ (4 * (c : ENNReal)⁻¹) *
        ((outerMultiplicityFromLocalBalls.C (Module.finrank ℝ E) : ENNReal) *
          multiplicity W.outerSet W.outerBody) * multiplicity (W.fiber j) W.innerBody := by
      gcongr
    _ = (factoringCoreAtScaleProductConstant F hδ hdisc D w₁ hw₁ : ENNReal) *
        multiplicity W.outerSet W.outerBody * multiplicity (W.fiber j) W.innerBody := by
      rw [factoringCoreAtScaleProductConstant, ENNReal.coe_mul, ENNReal.coe_mul,
        ENNReal.coe_inv hcne]
      norm_num
      ring

/-- A caller-facing envelope for the three quantitative losses in the fixed-scale core.
Refinement and fullness coefficients are lower bounds for the exact small constants, while the
product coefficient is an upper bound for the exact large constant. -/
structure FactoringAtScaleLossBound
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) where
  /-- Uniform small coefficient retained in the refinement estimate. -/
  refinementConstant : NNReal
  /-- Uniform small coefficient retained in the thick-fullness estimate. -/
  fullnessConstant : NNReal
  /-- Uniform large coefficient allowed in the multiplicity product estimate. -/
  productConstant : NNReal
  /-- The refinement envelope is no larger than the exact retained fraction. -/
  refinement_le : refinementConstant ≤
    factoringCoreAtScaleRefinementConstant F hδ hdisc D w₁ hw₁
  /-- The fullness envelope is no larger than the exact fullness coefficient. -/
  fullness_le : fullnessConstant ≤
    factoringCoreAtScaleFullnessConstant F hδ hdisc D w₁ hw₁
  /-- The product envelope dominates the exact multiplicative loss whenever there is a retained
  fiber on which the product estimate can be consumed. -/
  product_le : (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet.Nonempty →
    factoringCoreAtScaleProductConstant F hδ hdisc D w₁ hw₁ ≤ productConstant

/-- The exact three constants form the canonical loss envelope. -/
noncomputable def FactoringAtScaleLossBound.exact
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    FactoringAtScaleLossBound F hδ hdisc D w₁ hw₁ where
  refinementConstant := factoringCoreAtScaleRefinementConstant F hδ hdisc D w₁ hw₁
  fullnessConstant := factoringCoreAtScaleFullnessConstant F hδ hdisc D w₁ hw₁
  productConstant := factoringCoreAtScaleProductConstant F hδ hdisc D w₁ hw₁
  refinement_le := le_rfl
  fullness_le := le_rfl
  product_le := fun _ ↦ le_rfl

/-- The family-independent packing estimate supplies the canonical quantitative envelope.  Its
three numerical fields depend on the family only through `innerSet.card` and the explicit
outer/inner volume-ratio exponent. -/
noncomputable def FactoringAtScaleLossBound.uniform
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) :
    FactoringAtScaleLossBound F hδ hdisc D w₁ hw₁ where
  refinementConstant := factoringCoreAtScaleUniformRefinementConstant
    (Module.finrank ℝ E) F.innerSet.card D.exponent w₁
  fullnessConstant := factoringCoreAtScaleUniformFullnessConstant
    (Module.finrank ℝ E) F.innerSet.card D.exponent w₁
  productConstant := factoringCoreAtScaleUniformProductConstant
    (Module.finrank ℝ E) F.innerSet.card D.exponent w₁
  refinement_le := factoringCoreAtScaleUniformRefinementConstant_le F hδ hdisc D w₁ hw₁
  fullness_le := factoringCoreAtScaleUniformFullnessConstant_le F hδ hdisc D w₁ hw₁
  product_le := factoringCoreAtScaleProductConstant_le_uniform hδ hdisc D w₁ hw₁

/-- Weaken the exact refinement estimate to a caller-supplied loss envelope. -/
theorem outerThickFamilyAtScale_isCRefinement_of_lossBound
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁)
    (L : FactoringAtScaleLossBound F hδ hdisc D w₁ hw₁) :
    IsCRefinement (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet
      (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody F.innerSet F.innerBody
      L.refinementConstant := by
  have href := outerThickFamilyAtScale_isCRefinement F hδ hdisc D w₁ hw₁
  refine ⟨href.1, ?_⟩
  calc
    (L.refinementConstant : ENNReal) *
        ∑ i ∈ F.innerSet, volume (F.innerBody i).shade ≤
      (factoringCoreAtScaleRefinementConstant F hδ hdisc D w₁ hw₁ : ENNReal) *
        ∑ i ∈ F.innerSet, volume (F.innerBody i).shade := by
          gcongr
          exact_mod_cast L.refinement_le
    _ ≤ ∑ i ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerSet,
        volume ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody i).shade := href.2

/-- Weaken the exact summed fullness estimate to a caller-supplied loss envelope. -/
theorem outerThickFamilyAtScale_fullness_of_lossBound
    {F : FactorFamily E ι κ} {C : ENNReal} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hdim : Module.finrank ℝ E = 3)
    (hshape : F.InnerHasSimilarShape 2) (hFrostman : F.HasFrostmanFibers C)
    (L : FactoringAtScaleLossBound F hδ hdisc D w₁ hw₁) :
    (L.fullnessConstant : ENNReal) * C⁻¹ *
          (fullness F.innerSet F.innerBody : ENNReal) ^ 2 *
        (∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
          volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).carrier)) ≤
      ∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
        volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade) := by
  calc
    (L.fullnessConstant : ENNReal) * C⁻¹ *
          (fullness F.innerSet F.innerBody : ENNReal) ^ 2 *
        (∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
          volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).carrier)) ≤
      (factoringCoreAtScaleFullnessConstant F hδ hdisc D w₁ hw₁ : ENNReal) * C⁻¹ *
          (fullness F.innerSet F.innerBody : ENNReal) ^ 2 *
        (∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
          volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).carrier)) := by
            gcongr
            exact_mod_cast L.fullness_le
    _ ≤ ∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
        volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade) :=
      outerThickFamilyAtScale_fullness hδ hdisc D w₁ hw₁ hdim hshape hFrostman

/-- Weaken the Remark 5.3 summed fullness estimate to a caller-supplied loss envelope. -/
theorem outerThickFamilyAtScale_fullness_of_lossBound_of_thickenedFrostman
    {F : FactorFamily E ι κ} {C : ENNReal} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hdim : Module.finrank ℝ E = 3)
    (hshape : F.InnerHasSimilarShape 2) (hFrostman : F.HasThickenedFrostmanFibers C)
    (L : FactoringAtScaleLossBound F hδ hdisc D w₁ hw₁) :
    (L.fullnessConstant : ENNReal) * C⁻¹ *
          (fullness F.innerSet F.innerBody : ENNReal) ^ 2 *
        (∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
          volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).carrier)) ≤
      ∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
        volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade) := by
  calc
    (L.fullnessConstant : ENNReal) * C⁻¹ *
          (fullness F.innerSet F.innerBody : ENNReal) ^ 2 *
        (∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
          volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).carrier)) ≤
      (factoringCoreAtScaleFullnessConstant F hδ hdisc D w₁ hw₁ : ENNReal) * C⁻¹ *
          (fullness F.innerSet F.innerBody : ENNReal) ^ 2 *
        (∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
          volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).carrier)) := by
            gcongr
            exact_mod_cast L.fullness_le
    _ ≤ ∑ j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet,
        volume (((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody j).shade) :=
      outerThickFamilyAtScale_fullness_of_thickenedFrostman hδ hdisc D w₁ hw₁ hdim hshape
        hFrostman

/-- Weaken the exact fiberwise product estimate to a caller-supplied loss envelope. -/
theorem outerThickFamilyAtScale_multiplicity_product_of_lossBound
    {F : FactorFamily E ι κ} {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (w₁ : NNReal) (hw₁ : 0 < w₁) (hscale : F.OuterIsAtScale 2 w₁)
    (L : FactoringAtScaleLossBound F hδ hdisc D w₁ hw₁)
    {j : κ} (hj : j ∈ (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet) :
    multiplicity F.innerSet F.innerBody ≤
      (L.productConstant : ENNReal) *
        multiplicity (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
          (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody *
        multiplicity ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
          (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody := by
  calc
    multiplicity F.innerSet F.innerBody ≤
      (factoringCoreAtScaleProductConstant F hδ hdisc D w₁ hw₁ : ENNReal) *
        multiplicity (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
          (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody *
        multiplicity ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
          (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody :=
      outerThickFamilyAtScale_multiplicity_product hδ hdisc D w₁ hw₁ hscale hj
    _ ≤ (L.productConstant : ENNReal) *
        multiplicity (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerSet
          (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).outerBody *
        multiplicity ((outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).fiber j)
          (outerThickFamilyAtScale F hδ hdisc D w₁ hw₁).innerBody := by
      gcongr
      exact_mod_cast L.product_le ⟨j, hj⟩

end ShadedBody
