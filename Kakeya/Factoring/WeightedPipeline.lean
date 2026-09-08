/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.Pipeline
public import Kakeya.Factoring.WeightedStep1

/-! # The factoring pipeline with carrier-weighted Step 1

This file leaves the pipeline used by Lemma 5.11 unchanged and provides the parallel Step 2--5
assembly needed by the corrected Proposition 5.1.  Its first step classifies
`fiberVolume / enlargedOuterVolume`; all later definitions are the same open-ball and Step 5
constructions as in `Kakeya.Factoring.Pipeline`.
-/

public section

open MeasureTheory Convexity Kakeya
open scoped NNReal ENNReal

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [DecidableEq κ]

/-- Explicit outer/inner carrier-volume ratio data for a factor family. -/
structure OuterInnerVolumeRatio (F : FactorFamily E ι κ) where
  /-- Dyadic exponent in the carrier-volume ratio. -/
  exponent : ℕ
  /-- Every inner member controls the volume of its parent. -/
  volume_outer_le : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
    volume (F.outerBody j).carrier ≤ 2 ^ exponent * volume (F.innerBody i).carrier

/-- Construct outer/inner volume-ratio data from separate uniform outer and inner volume
bounds.  The dyadic comparison between the two bounds is deliberately explicit: inner
discretization alone does not bound arbitrary outer carriers. -/
@[expose] def OuterInnerVolumeRatio.ofVolumeBounds (F : FactorFamily E ι κ) (N : ℕ)
    (outerBound innerBound : ENNReal)
    (houter : ∀ j ∈ F.outerSet, volume (F.outerBody j).carrier ≤ outerBound)
    (hinner : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      innerBound ≤ volume (F.innerBody i).carrier)
    (hdyadic : outerBound ≤ 2 ^ N * innerBound) : OuterInnerVolumeRatio F where
  exponent := N
  volume_outer_le := by
    intro j hj i hi
    calc
      volume (F.outerBody j).carrier ≤ outerBound := houter j hj
      _ ≤ 2 ^ N * innerBound := hdyadic
      _ ≤ 2 ^ N * volume (F.innerBody i).carrier := by
        gcongr
        exact hinner j hj i hi

@[simp] theorem OuterInnerVolumeRatio.ofVolumeBounds_exponent (F : FactorFamily E ι κ) (N : ℕ)
    (outerBound innerBound : ENNReal)
    (houter : ∀ j ∈ F.outerSet, volume (F.outerBody j).carrier ≤ outerBound)
    (hinner : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      innerBound ≤ volume (F.innerBody i).carrier)
    (hdyadic : outerBound ≤ 2 ^ N * innerBound) :
    (OuterInnerVolumeRatio.ofVolumeBounds F N outerBound innerBound houter hinner
      hdyadic).exponent = N := rfl

/-- Construct dyadic outer/inner volume-ratio data from positive finite uniform bounds.

The exponent is the binary ceiling of an Archimedean upper bound for
`outerBound / innerBound`; in particular it records a logarithmic, rather than linear,
loss in the volume ratio. -/
-- `@[expose]` added by steps, and it is the *only* change made to this file.  Rationale, so
-- that the owner of this module can see it at a glance:
--   * `OuterInnerVolumeRatio.ofVolumeBounds`, one declaration above, already carries `@[expose]`,
--     so this restores an evidently intended pattern rather than introducing one;
--   * without it the exponent this definition produces — `Nat.clog 2 (Nat.find …)` — is opaque to
--     every `module` file, so no caller can bound it.  That is why
--     the logarithmic bound cited in
--     `Kakeya/DimensionThree/Plank/Section6PartBProp51Input.lean` was asserted in prose and never
--     written; it is now `Kakeya.PartBLoss.fineVolumeRatio_exponent_spec` in
--     `Kakeya/DimensionThree/Plank/PartBVolumeRatioExponent.lean`;
--   * `@[expose]` only makes a body visible across module boundaries.  It cannot change what any
--     existing proof proves and cannot make a false statement provable.
@[expose] noncomputable def OuterInnerVolumeRatio.ofFiniteVolumeBounds (F : FactorFamily E ι κ)
    (outerBound innerBound : ENNReal)
    (houter : ∀ j ∈ F.outerSet, volume (F.outerBody j).carrier ≤ outerBound)
    (hinner : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      innerBound ≤ volume (F.innerBody i).carrier)
    (houterTop : outerBound ≠ ∞) (hinnerPos : 0 < innerBound)
    (hinnerTop : innerBound ≠ ∞) : OuterInnerVolumeRatio F := by
  have hratioTop : outerBound / innerBound ≠ ∞ :=
    ENNReal.div_ne_top houterTop hinnerPos.ne'
  let m : ℕ := Nat.find (ENNReal.exists_nat_gt hratioTop)
  let N : ℕ := Nat.clog 2 m
  have hm : outerBound / innerBound < (m : ENNReal) :=
    Nat.find_spec (ENNReal.exists_nat_gt hratioTop)
  have hmN : (m : ENNReal) ≤ 2 ^ N := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) m
  have hratio : outerBound / innerBound ≤ 2 ^ N := hm.le.trans hmN
  exact OuterInnerVolumeRatio.ofVolumeBounds F N outerBound innerBound houter hinner
    ((ENNReal.div_le_iff hinnerPos.ne' hinnerTop).mp hratio)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [DecidableEq κ] in
private theorem isOpen_setOf_exists_mem_weightedPipelineNhd
    (f : E → ℕ) (j : κ) (r : ℝ) (v : ℕ) :
    IsOpen {x | ∃ y ∈ pipelineNhd r j x, f y = v} := by
  rw [show {x : E | ∃ y ∈ pipelineNhd r j x, f y = v} =
      ⋃ y, ⋃ (_ : f y = v), Metric.ball y r by
    ext x
    constructor
    · rintro ⟨y, hy, hyv⟩
      refine Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hyv, ?_⟩⟩
      simpa only [pipelineNhd, Metric.mem_ball_comm] using hy
    · intro hx
      obtain ⟨y, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hyv, hxy⟩ := Set.mem_iUnion.mp hx
      exact ⟨y, by simpa only [pipelineNhd, Metric.mem_ball_comm] using hxy, hyv⟩]
  exact isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball

namespace FactorFamily

/-- The carrier-weighted Step 1 family determined by explicit volume-ratio data. -/
noncomputable def weightedPipelineStep1 [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F) :
    FactorFamily E ι κ :=
  F.weightedStep1AtScale hδ hdisc D.exponent D.volume_outer_le

private theorem weightedPipelineStep1_eq_private [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F) :
    F.weightedPipelineStep1 hδ hdisc D =
      F.weightedStep1AtScale hδ hdisc D.exponent D.volume_outer_le := rfl

/-- Weighted pipeline Step 1 is the at-scale weighted Step 1 with the supplied ratio data. -/
theorem weightedPipelineStep1_eq [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F) :
    F.weightedPipelineStep1 hδ hdisc D =
      F.weightedStep1AtScale hδ hdisc D.exponent D.volume_outer_le :=
  weightedPipelineStep1_eq_private F hδ hdisc D

/-- The inner indices passed from weighted Step 1 to Steps 2--5. -/
noncomputable def weightedPipelineInnerSet [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F) : Finset ι :=
  (F.weightedPipelineStep1 hδ hdisc D).innerSet

private theorem weightedPipelineInnerSet_eq_step1_private [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F) :
    F.weightedPipelineInnerSet hδ hdisc D =
      (F.weightedPipelineStep1 hδ hdisc D).innerSet := rfl

/-- The weighted pipeline inner set is the inner set selected by weighted Step 1. -/
theorem weightedPipelineInnerSet_eq_step1 [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F) :
    F.weightedPipelineInnerSet hδ hdisc D =
      (F.weightedPipelineStep1 hδ hdisc D).innerSet :=
  weightedPipelineInnerSet_eq_step1_private F hδ hdisc D

/-- Weighted Step 1 keeps the input inner bodies. -/
theorem weightedPipelineStep1_innerBody [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F) :
    (F.weightedPipelineStep1 hδ hdisc D).innerBody = F.innerBody := by
  rw [weightedPipelineStep1, innerBody_weightedStep1AtScale]

theorem weightedPipelineInnerSet_eq_filter [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F) :
    F.weightedPipelineInnerSet hδ hdisc D =
      {i ∈ F.step0.innerSet | F.parent i ∈ (F.weightedPipelineStep1 hδ hdisc D).outerSet} := by
  rw [weightedPipelineInnerSet, weightedPipelineStep1, innerSet_weightedStep1AtScale]

/-- The Step 2 dyadic exponents selected after carrier-weighted Step 1. -/
noncomputable def weightedPipelineScaleTriple [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (r : ℝ) (hr : 0 < r) : ℕ × ℕ × ℕ :=
  (MultiplicityFamily.exists_isScaleTriple_lintegral_le
    (t := (F.weightedPipelineStep1 hδ hdisc D).outerSet)
    (m := fiberMultiplicity F (F.weightedPipelineInnerSet hδ hdisc D))
    (nhd := pipelineNhd r) (μ := volume) (M := F.innerSet.card)
    (fun j _ y ↦ by
      rw [weightedPipelineInnerSet_eq_filter]
      exact fiberMultiplicity_le_card F F.innerSet_step0_subset
        (F.weightedPipelineStep1 hδ hdisc D).outerSet j y)
    (fun _ _ _ ↦ Metric.mem_ball_self hr)).choose

theorem weightedPipelineScaleTriple_spec [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (r : ℝ) (hr : 0 < r) :
    F.weightedPipelineScaleTriple hδ hdisc D r hr ∈
        MultiplicityFamily.scaleTripleBox F.innerSet.card
          (F.weightedPipelineStep1 hδ hdisc D).outerSet.card ∧
      ((MultiplicityFamily.scalePigeonholeConstant F.innerSet.card
        (F.weightedPipelineStep1 hδ hdisc D).outerSet.card : ℝ≥0∞))⁻¹ *
          ∫⁻ x, ((∑ j ∈ (F.weightedPipelineStep1 hδ hdisc D).outerSet,
            fiberMultiplicity F (F.weightedPipelineInnerSet hδ hdisc D) j x : ℕ) : ℝ≥0∞)
        ≤ ∫⁻ x in pipelineLevelSet F F.step0.innerSet
            (F.weightedPipelineStep1 hδ hdisc D).outerSet r F.innerSet.card
            (F.weightedPipelineScaleTriple hδ hdisc D r hr).1
            (F.weightedPipelineScaleTriple hδ hdisc D r hr).2.1
            (F.weightedPipelineScaleTriple hδ hdisc D r hr).2.2,
          ((∑ j ∈ (F.weightedPipelineStep1 hδ hdisc D).outerSet,
            fiberMultiplicity F (F.weightedPipelineInnerSet hδ hdisc D) j x : ℕ) : ℝ≥0∞) :=
  by
  simpa only [weightedPipelineScaleTriple, pipelineLevelSet,
    weightedPipelineInnerSet_eq_filter] using
    (MultiplicityFamily.exists_isScaleTriple_lintegral_le
    (t := (F.weightedPipelineStep1 hδ hdisc D).outerSet)
    (m := fiberMultiplicity F (F.weightedPipelineInnerSet hδ hdisc D))
    (nhd := pipelineNhd r) (μ := volume) (M := F.innerSet.card)
    (fun j _ y ↦ by
      rw [weightedPipelineInnerSet_eq_filter]
      exact fiberMultiplicity_le_card F F.innerSet_step0_subset
        (F.weightedPipelineStep1 hδ hdisc D).outerSet j y)
    (fun _ _ _ ↦ Metric.mem_ball_self hr)).choose_spec

/-- The measurable Step 2 level set for the carrier-weighted pipeline. -/
noncomputable def weightedPipelineSet [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (r : ℝ) (hr : 0 < r) : Set E :=
  pipelineLevelSet F F.step0.innerSet (F.weightedPipelineStep1 hδ hdisc D).outerSet r
    F.innerSet.card (F.weightedPipelineScaleTriple hδ hdisc D r hr).1
    (F.weightedPipelineScaleTriple hδ hdisc D r hr).2.1
    (F.weightedPipelineScaleTriple hδ hdisc D r hr).2.2

private theorem weightedPipelineSet_eq_private [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (r : ℝ) (hr : 0 < r) :
    F.weightedPipelineSet hδ hdisc D r hr =
      pipelineLevelSet F F.step0.innerSet (F.weightedPipelineStep1 hδ hdisc D).outerSet r
        F.innerSet.card (F.weightedPipelineScaleTriple hδ hdisc D r hr).1
        (F.weightedPipelineScaleTriple hδ hdisc D r hr).2.1
        (F.weightedPipelineScaleTriple hδ hdisc D r hr).2.2 := rfl

/-- The weighted Step 2 set is the generic open-ball level set for its selected outer blocks. -/
theorem weightedPipelineSet_eq [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (r : ℝ) (hr : 0 < r) :
    F.weightedPipelineSet hδ hdisc D r hr =
      pipelineLevelSet F F.step0.innerSet (F.weightedPipelineStep1 hδ hdisc D).outerSet r
        F.innerSet.card (F.weightedPipelineScaleTriple hδ hdisc D r hr).1
        (F.weightedPipelineScaleTriple hδ hdisc D r hr).2.1
        (F.weightedPipelineScaleTriple hδ hdisc D r hr).2.2 :=
  weightedPipelineSet_eq_private F hδ hdisc D r hr

/-- The common inner multiplicity exponent selected by weighted Step 2. -/
noncomputable def weightedPipelineExponent [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (r : ℝ) (hr : 0 < r) : ℕ :=
  (F.weightedPipelineScaleTriple hδ hdisc D r hr).1

/-- The outer counting exponent selected by weighted Step 2. -/
noncomputable def weightedPipelineOuterExponent [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (r : ℝ) (hr : 0 < r) : ℕ :=
  (F.weightedPipelineScaleTriple hδ hdisc D r hr).2.1

/-- The final Step 5 shaded family for a fixed weighted-pipeline selection. -/
noncomputable def weightedPipelineFamily [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (r : ℝ) (hr : 0 < r) (hOmega : MeasurableSet (F.weightedPipelineSet hδ hdisc D r hr))
    (T' : Finset E) (w₁ : ℝ≥0) : ShadedFactorFamily E ι κ :=
  step5ShadedFactorFamily F F.innerSet_step0_subset
    (F.weightedPipelineStep1 hδ hdisc D).outerSet
    (F.weightedPipelineSet hδ hdisc D r hr) hOmega
    (F.weightedPipelineExponent hδ hdisc D r hr) T' w₁

/-- The weighted-pipeline Step 2 level set is measurable. -/
theorem measurableSet_weightedPipelineSet [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (r : ℝ) (hr : 0 < r) : MeasurableSet (F.weightedPipelineSet hδ hdisc D r hr) := by
  apply Kakeya.MultiplicityFamily.measurableSet_setOf_isScaleTriple
  · intro j _
    exact measurable_pointwiseMultiplicity _ _
  · intro j _ v
    exact (isOpen_setOf_exists_mem_weightedPipelineNhd
      (fiberMultiplicity F
        {i ∈ F.step0.innerSet | F.parent i ∈ (F.weightedPipelineStep1 hδ hdisc D).outerSet} j)
      j r v).measurableSet

/-- Pointwise Step 2 bounds for the carrier-weighted pipeline. -/
theorem bounds_of_mem_weightedPipelineSet [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (r : ℝ) (hr : 0 < r) {x : E} (hx : x ∈ F.weightedPipelineSet hδ hdisc D r hr) :
    2 ^ F.weightedPipelineExponent hδ hdisc D r hr *
          2 ^ F.weightedPipelineOuterExponent hδ hdisc D r hr ≤
        pointwiseMultiplicity (F.weightedPipelineInnerSet hδ hdisc D) F.innerBody x ∧
      pointwiseMultiplicity (F.weightedPipelineInnerSet hδ hdisc D) F.innerBody x ≤
        factoringStep2PointwiseConstant F.innerSet.card *
          (2 ^ F.weightedPipelineExponent hδ hdisc D r hr *
            2 ^ F.weightedPipelineOuterExponent hδ hdisc D r hr) ∧
      2 ^ F.weightedPipelineOuterExponent hδ hdisc D r hr ≤
        (MultiplicityFamily.dyadicLevel (F.weightedPipelineStep1 hδ hdisc D).outerSet
          (fiberMultiplicity F (F.weightedPipelineInnerSet hδ hdisc D))
          (F.weightedPipelineExponent hδ hdisc D r hr) x).card ∧
      (MultiplicityFamily.dyadicLevel (F.weightedPipelineStep1 hδ hdisc D).outerSet
        (fiberMultiplicity F (F.weightedPipelineInnerSet hδ hdisc D))
        (F.weightedPipelineExponent hδ hdisc D r hr) x).card <
          2 * 2 ^ F.weightedPipelineOuterExponent hδ hdisc D r hr := by
  have hst : MultiplicityFamily.IsScaleTriple
      (F.weightedPipelineStep1 hδ hdisc D).outerSet
      (fiberMultiplicity F (F.weightedPipelineInnerSet hδ hdisc D)) (pipelineNhd r)
      F.innerSet.card (F.weightedPipelineExponent hδ hdisc D r hr)
      (F.weightedPipelineOuterExponent hδ hdisc D r hr)
      (F.weightedPipelineScaleTriple hδ hdisc D r hr).2.2 x := by
    simpa only [weightedPipelineSet, pipelineLevelSet, weightedPipelineInnerSet_eq_filter,
      weightedPipelineExponent, weightedPipelineOuterExponent, Set.mem_setOf_eq] using hx
  have hsum := sum_fiberMultiplicity_eq_pointwiseMultiplicity F F.step0.innerSet
    (F.weightedPipelineStep1 hδ hdisc D).outerSet x
  rw [show pointwiseMultiplicity (F.weightedPipelineInnerSet hδ hdisc D) F.innerBody x =
      ∑ j ∈ (F.weightedPipelineStep1 hδ hdisc D).outerSet,
        fiberMultiplicity F (F.weightedPipelineInnerSet hδ hdisc D) j x by
    simpa only [weightedPipelineInnerSet_eq_filter] using hsum.symm]
  exact ⟨hst.mul_le_sum, hst.sum_le_mul, hst.le_card_dyadicLevel, hst.card_dyadicLevel_lt⟩

end FactorFamily

open Classical in
/-- Step 3 has pointwise multiplicity in a factor-four interval in the weighted pipeline. -/
private theorem weightedPipelineStep3_multiplicity [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (r : ℝ) (hr : 0 < r)
    (hOmega : MeasurableSet (F.weightedPipelineSet hδ hdisc D r hr)) {x : E}
    (hx : x ∈ iUnionShade (F.weightedPipelineInnerSet hδ hdisc D)
      (step3InnerBody F F.step0.innerSet (F.weightedPipelineStep1 hδ hdisc D).outerSet
        (F.weightedPipelineSet hδ hdisc D r hr) hOmega
        (F.weightedPipelineExponent hδ hdisc D r hr))) :
    let L := 2 ^ F.weightedPipelineExponent hδ hdisc D r hr *
      2 ^ F.weightedPipelineOuterExponent hδ hdisc D r hr
    L ≤ pointwiseMultiplicity (F.weightedPipelineInnerSet hδ hdisc D)
        (step3InnerBody F F.step0.innerSet (F.weightedPipelineStep1 hδ hdisc D).outerSet
          (F.weightedPipelineSet hδ hdisc D r hr) hOmega
          (F.weightedPipelineExponent hδ hdisc D r hr)) x ∧
      pointwiseMultiplicity (F.weightedPipelineInnerSet hδ hdisc D)
          (step3InnerBody F F.step0.innerSet
            (F.weightedPipelineStep1 hδ hdisc D).outerSet
            (F.weightedPipelineSet hδ hdisc D r hr) hOmega
            (F.weightedPipelineExponent hδ hdisc D r hr)) x < 4 * L := by
  let u := F.step0.innerSet
  let t' := (F.weightedPipelineStep1 hδ hdisc D).outerSet
  let Omega := F.weightedPipelineSet hδ hdisc D r hr
  let k := F.weightedPipelineExponent hδ hdisc D r hr
  let l := F.weightedPipelineOuterExponent hδ hdisc D r hr
  let d := MultiplicityFamily.dyadicLevel t'
    (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'}) k x
  have hxOmega : x ∈ Omega := by
    obtain ⟨i, _, hxi⟩ := Set.mem_iUnion₂.mp hx
    change x ∈ (F.innerBody i).shade ∩ Omega ∩ step3DyadicSet F u t' k (F.parent i) at hxi
    exact hxi.1.2
  have hb := F.bounds_of_mem_weightedPipelineSet hδ hdisc D r hr hxOmega
  have hd : 2 ^ l ≤ d.card ∧ d.card < 2 * 2 ^ l := by
    constructor
    · simpa [d, l, k, t', Omega, u, FactorFamily.weightedPipelineInnerSet_eq_filter]
        using hb.2.2.1
    · simpa [d, l, k, t', Omega, u, FactorFamily.weightedPipelineInnerSet_eq_filter]
        using hb.2.2.2
  have hsand := Nat.dyadic_class_card_sandwich d
    (fun j ↦ fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x) k
    (fun j hj ↦ (Finset.mem_filter.mp hj).2)
  have hpm : pointwiseMultiplicity (F.weightedPipelineInnerSet hδ hdisc D)
      (step3InnerBody F F.step0.innerSet (F.weightedPipelineStep1 hδ hdisc D).outerSet
        (F.weightedPipelineSet hδ hdisc D r hr) hOmega
        (F.weightedPipelineExponent hδ hdisc D r hr)) x =
      ∑ j ∈ d, fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x := by
    have h := pointwiseMultiplicity_step3FactorFamily F F.innerSet_step0_subset t' Omega
      hOmega k x
    rw [if_pos hxOmega] at h
    simpa [u, t', Omega, k, d, FactorFamily.weightedPipelineInnerSet_eq_filter] using h
  dsimp only
  rw [hpm]
  constructor
  · exact (Nat.mul_le_mul_left _ hd.1).trans hsand.1
  · calc
      ∑ j ∈ d, fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x
          ≤ 2 ^ (k + 1) * d.card := hsand.2
      _ < 2 ^ (k + 1) * (2 * 2 ^ l) := Nat.mul_lt_mul_of_pos_left hd.2 (by positivity)
      _ = 4 * (2 ^ k * 2 ^ l) := by simp [pow_succ]; ring

set_option maxHeartbeats 800000 in
-- The Step 5 mass ledger expands several nested finite sums and carrier restrictions.
open Classical in
/-- The self-pigeonholed Step 5 selection for the carrier-weighted pipeline. -/
theorem exists_weightedFactoringPipelineSelf [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (r : ℝ) (hr : 0 < r)
    (hOmega : MeasurableSet (F.weightedPipelineSet hδ hdisc D r hr))
    {w₁ : ℝ≥0} (hw₁ : 0 < w₁) :
    ∃ T T' : Finset E,
      (T : Set E) ⊆ iUnionShade (F.weightedPipelineInnerSet hδ hdisc D)
        (step3InnerBody F F.step0.innerSet (F.weightedPipelineStep1 hδ hdisc D).outerSet
          (F.weightedPipelineSet hδ hdisc D r hr) hOmega
          (F.weightedPipelineExponent hδ hdisc D r hr)) ∧
      Metric.IsSeparated (w₁ : ℝ≥0∞) (T : Set E) ∧
      iUnionShade (F.weightedPipelineInnerSet hδ hdisc D)
          (step3InnerBody F F.step0.innerSet
            (F.weightedPipelineStep1 hδ hdisc D).outerSet
            (F.weightedPipelineSet hδ hdisc D r hr) hOmega
            (F.weightedPipelineExponent hδ hdisc D r hr)) ⊆
        ⋃ c ∈ T, Metric.closedBall c (w₁ : ℝ) ∧
      (∀ x : E, {c ∈ T | x ∈ Metric.closedBall c (w₁ : ℝ)}.card ≤
        factoringStep5OverlapConstant (Module.finrank ℝ E)) ∧
      T' ⊆ T ∧
      (∀ c ∈ T', volume (iUnionShade (F.weightedPipelineInnerSet hδ hdisc D)
        (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerBody ∩
          Metric.closedBall c (w₁ : ℝ)) ≠ 0) ∧
      Metric.IsSeparated (w₁ : ℝ≥0∞) (T' : Set E) ∧
      IsCRefinement (F.weightedPipelineInnerSet hδ hdisc D)
        (step5InnerBody F F.step0.innerSet
          (F.weightedPipelineStep1 hδ hdisc D).outerSet
          (F.weightedPipelineSet hδ hdisc D r hr) hOmega
          (F.weightedPipelineExponent hδ hdisc D r hr) T' w₁)
        (F.weightedPipelineInnerSet hδ hdisc D)
        (step3InnerBody F F.step0.innerSet
          (F.weightedPipelineStep1 hδ hdisc D).outerSet
          (F.weightedPipelineSet hδ hdisc D r hr) hOmega
          (F.weightedPipelineExponent hδ hdisc D r hr))
        (Kakeya.factoringStep5SelfPigeonholeConstant (Module.finrank ℝ E) T.card)⁻¹ ∧
      (∀ c ∈ T', ∀ c' ∈ T',
        volume (iUnionShade (F.weightedPipelineInnerSet hδ hdisc D)
            (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerBody ∩
              Metric.closedBall c (w₁ : ℝ)) ≤
          2 * volume (iUnionShade (F.weightedPipelineInnerSet hδ hdisc D)
            (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerBody ∩
              Metric.closedBall c' (w₁ : ℝ))) := by
  classical
  let s := F.weightedPipelineInnerSet hδ hdisc D
  let t := (F.weightedPipelineStep1 hδ hdisc D).outerSet
  let Omega := F.weightedPipelineSet hδ hdisc D r hr
  let k := F.weightedPipelineExponent hδ hdisc D r hr
  let V := step3InnerBody F F.step0.innerSet t Omega hOmega k
  let U := iUnionShade s V
  obtain ⟨T, hTsub, hTsep, hTcover, hToverlap⟩ :=
    (isBounded_iUnionShade (s := s) (V := V)).exists_finset_isSeparated_isCover_closedBall hw₁
  let f : E → ℝ≥0∞ := fun c ↦ volume (U ∩ Metric.closedBall c (w₁ : ℝ))
  have hf : ∀ c ∈ T, f c ≠ ⊤ := by
    intro c _
    exact ne_top_of_le_ne_top (volume_iUnion_shade_ne_top s V)
      (measure_mono Set.inter_subset_left)
  obtain ⟨T', hT'T, hsumf, hcomp, hposf⟩ := exists_self_dyadic T f hf
  let L : ℕ := 2 ^ F.weightedPipelineExponent hδ hdisc D r hr *
    2 ^ F.weightedPipelineOuterExponent hδ hdisc D r hr
  let w : E → ℝ≥0∞ := fun c ↦
    step5BallMass F F.step0.innerSet t Omega hOmega k w₁ c
  have hlow : ∀ c : E, (L : ℝ≥0∞) * f c ≤ w c := by
    intro c
    simpa [w, f, U, V, s, t, Omega, k, step5BallMass,
      FactorFamily.weightedPipelineInnerSet_eq_filter] using
      (mul_volume_iUnionShade_inter_le_sum_volume_inter s V
        (Metric.closedBall c (w₁ : ℝ)) Metric.isClosed_closedBall.measurableSet L
        fun x hx ↦ by
          exact_mod_cast
            (weightedPipelineStep3_multiplicity F hδ hdisc D r hr hOmega hx).1)
  have hupp : ∀ c : E, w c ≤ (4 * L : ℕ) * f c := by
    intro c
    simpa [w, f, U, V, s, t, Omega, k, step5BallMass,
      FactorFamily.weightedPipelineInnerSet_eq_filter] using
      (sum_volume_inter_le_mul_volume_iUnionShade_inter s V _
        Metric.isClosed_closedBall.measurableSet (4 * L) fun x hx ↦ by
          exact_mod_cast
            (weightedPipelineStep3_multiplicity F hδ hdisc D r hr hOmega hx).2.le)
  have hsumw : ∑ c ∈ T, w c ≤
      (4 * (2 * factoringStep1FiberPigeonholeConstant 1 T.card) : ℝ≥0) *
        ∑ c ∈ T', w c := by
    calc
      ∑ c ∈ T, w c ≤ ∑ c ∈ T, (4 * L : ℕ) * f c :=
        Finset.sum_le_sum fun c _ ↦ hupp c
      _ = (4 * L : ℕ) * ∑ c ∈ T, f c := by rw [Finset.mul_sum]
      _ ≤ (4 * L : ℕ) *
          ((2 * factoringStep1FiberPigeonholeConstant 1 T.card : ℝ≥0) *
            ∑ c ∈ T', f c) := by gcongr
      _ = (4 * (2 * factoringStep1FiberPigeonholeConstant 1 T.card) : ℝ≥0) *
          ((L : ℝ≥0∞) * ∑ c ∈ T', f c) := by
        push_cast
        ring
      _ ≤ (4 * (2 * factoringStep1FiberPigeonholeConstant 1 T.card) : ℝ≥0) *
          ∑ c ∈ T', w c := by
        gcongr
        calc
          (L : ℝ≥0∞) * ∑ c ∈ T', f c =
              ∑ c ∈ T', (L : ℝ≥0∞) * f c := by rw [Finset.mul_sum]
          _ ≤ ∑ c ∈ T', w c := Finset.sum_le_sum fun c _ ↦ hlow c
  have hshade_le_T : ∑ i ∈ s, volume (V i).shade ≤ ∑ c ∈ T, w c := by
    calc
      ∑ i ∈ s, volume (V i).shade ≤
          ∑ i ∈ s, ∑ c ∈ T, volume ((V i).shade ∩ Metric.closedBall c (w₁ : ℝ)) := by
        exact Finset.sum_le_sum fun i hi ↦
          MeasureTheory.measure_le_sum_measure_inter_of_subset_biUnion volume T
            (fun c ↦ Metric.closedBall c (w₁ : ℝ))
            ((Set.subset_iUnion₂_of_subset i hi (Set.Subset.refl _)).trans hTcover)
      _ = ∑ c ∈ T, w c := by
        rw [Finset.sum_comm]
        simp only [w, step5BallMass, s, V, t, Omega, k,
          FactorFamily.weightedPipelineInnerSet_eq_filter]
  have hT'overlap : ∑ c ∈ T', w c ≤
      (factoringStep5OverlapConstant (Module.finrank ℝ E) : ℝ≥0∞) *
        ∑ i ∈ s, volume ((step5InnerBody F F.step0.innerSet t Omega hOmega k T' w₁ i).shade) := by
    simp only [w, step5BallMass]
    rw [Finset.sum_comm, Finset.mul_sum]
    rw [show s = {i ∈ F.step0.innerSet | F.parent i ∈ t} by
      simp only [s, t, FactorFamily.weightedPipelineInnerSet_eq_filter]]
    refine Finset.sum_le_sum ?_
    intro i hi
    rw [shade_step5InnerBody]
    exact MeasureTheory.sum_measure_inter_le_mul_measure_inter_biUnion
      (μ := volume) hT'T (B := fun c ↦ Metric.closedBall c (w₁ : ℝ))
      (hB := fun _ ↦ Metric.isClosed_closedBall.measurableSet)
      (A := (V i).shade) (hA := (V i).measurableSet_shade)
      (hK := fun x ↦ by
        simpa [factoringStep5OverlapConstant] using hToverlap x)
  have hmass : ∑ i ∈ s, volume (V i).shade ≤
      (Kakeya.factoringStep5SelfPigeonholeConstant (Module.finrank ℝ E) T.card : ℝ≥0∞) *
        ∑ i ∈ s,
          volume ((step5InnerBody F F.step0.innerSet t Omega hOmega k T' w₁ i).shade) := by
    calc
      ∑ i ∈ s, volume (V i).shade ≤ ∑ c ∈ T, w c := hshade_le_T
      _ ≤ (4 * (2 * factoringStep1FiberPigeonholeConstant 1 T.card) : ℝ≥0) *
          ∑ c ∈ T', w c := hsumw
      _ ≤ (4 * (2 * factoringStep1FiberPigeonholeConstant 1 T.card) : ℝ≥0) *
          ((factoringStep5OverlapConstant (Module.finrank ℝ E) : ℝ≥0∞) *
            ∑ i ∈ s,
              volume ((step5InnerBody F F.step0.innerSet t Omega hOmega k T' w₁ i).shade)) := by
        gcongr
      _ = (Kakeya.factoringStep5SelfPigeonholeConstant
            (Module.finrank ℝ E) T.card : ℝ≥0∞) *
          ∑ i ∈ s,
            volume ((step5InnerBody F F.step0.innerSet t Omega hOmega k T' w₁ i).shade) := by
        simp only [Kakeya.factoringStep5SelfPigeonholeConstant]
        push_cast
        ring
  have href : IsCRefinement s
      (step5InnerBody F F.step0.innerSet t Omega hOmega k T' w₁) s V
      (Kakeya.factoringStep5SelfPigeonholeConstant (Module.finrank ℝ E) T.card)⁻¹ := by
    refine isCRefinement_of_isRefinement_of_sum_le
      (s' := s) (V' := step5InnerBody F F.step0.innerSet t Omega hOmega k T' w₁)
      (s := s) (V := V)
      (C := Kakeya.factoringStep5SelfPigeonholeConstant
        (Module.finrank ℝ E) T.card) ?_ hmass
    exact isRefinement_step5FactorFamily F F.step0.innerSet t Omega hOmega k T' w₁ s
  refine ⟨T, T', hTsub, hTsep, hTcover, ?_, hT'T, ?_, hTsep.subset ?_, ?_, ?_⟩
  · simpa [factoringStep5OverlapConstant] using hToverlap
  · intro c hc
    have heq := congrArg volume
      (iUnionShade_step5FactorFamily_inter_closedBall F F.step0.innerSet t Omega hOmega k
        (w₁ := w₁) s hc)
    change volume (iUnionShade s
      (step5InnerBody F F.step0.innerSet t Omega hOmega k T' w₁) ∩
        Metric.closedBall c (w₁ : ℝ)) ≠ 0
    rw [heq]
    simpa only [f, U, V] using hposf c hc
  · exact_mod_cast hT'T
  · simpa only [s, V, t, Omega, k] using href
  · intro c hc c' hc'
    change volume (iUnionShade s
        (step5InnerBody F F.step0.innerSet t Omega hOmega k T' w₁) ∩
          Metric.closedBall c (w₁ : ℝ)) ≤
      2 * volume (iUnionShade s
        (step5InnerBody F F.step0.innerSet t Omega hOmega k T' w₁) ∩
          Metric.closedBall c' (w₁ : ℝ))
    rw [iUnionShade_step5FactorFamily_inter_closedBall F F.step0.innerSet t Omega hOmega k s hc,
      iUnionShade_step5FactorFamily_inter_closedBall F F.step0.innerSet t Omega hOmega k s hc']
    simpa only [f, U, V] using hcomp c hc c' hc'

namespace FactorFamily

variable [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
  (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
  (r : ℝ) (hr : 0 < r)
  (hOmega : MeasurableSet (F.weightedPipelineSet hδ hdisc D r hr))
  (T' : Finset E) (w₁ : ℝ≥0)

private theorem weightedPipelineFamily_outerSet_private :
    (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).outerSet =
      (F.weightedPipelineStep1 hδ hdisc D).outerSet := rfl

/-- The weighted pipeline retains the outer set selected in weighted Step 1. -/
theorem weightedPipelineFamily_outerSet :
    (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).outerSet =
      (F.weightedPipelineStep1 hδ hdisc D).outerSet :=
  weightedPipelineFamily_outerSet_private F hδ hdisc D r hr hOmega T' w₁

/-- The weighted-pipeline outer set is a subset of the original outer set. -/
theorem weightedPipelineFamily_outerSet_subset :
    (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).outerSet ⊆ F.outerSet := by
  intro j hj
  change j ∈ (F.weightedPipelineStep1 hδ hdisc D).outerSet at hj
  obtain ⟨i, hi, hpi⟩ := Finset.mem_image.mp
    (F.outerSet_weightedStep1AtScale_subset_image hδ hdisc D.exponent
      D.volume_outer_le hj)
  rw [← hpi]
  exact F.parent_mem i (F.innerSet_step0_subset hi)

/-- Every weighted-pipeline outer block meets the Step 0 inner family. -/
theorem weightedPipelineFamily_outerSet_subset_image :
    (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).outerSet ⊆
      F.step0.innerSet.image F.parent := by
  intro j hj
  change j ∈ (F.weightedPipelineStep1 hδ hdisc D).outerSet at hj
  rw [F.weightedPipelineStep1_eq hδ hdisc D] at hj
  exact F.outerSet_weightedStep1AtScale_subset_image hδ hdisc D.exponent
    D.volume_outer_le hj

private theorem weightedPipelineFamily_innerSet_private :
    (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerSet =
      F.weightedPipelineInnerSet hδ hdisc D := by
  rw [weightedPipelineFamily, step5ShadedFactorFamily_innerSet,
    weightedPipelineInnerSet_eq_filter]

/-- The output inner set is precisely the weighted Step 1 inner set. -/
@[simp]
theorem weightedPipelineFamily_innerSet :
    (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerSet =
      F.weightedPipelineInnerSet hδ hdisc D :=
  weightedPipelineFamily_innerSet_private F hδ hdisc D r hr hOmega T' w₁

private theorem weightedPipelineFamily_parent_private :
    (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).parent = F.parent := rfl

/-- The weighted pipeline keeps the original parent map. -/
@[simp]
theorem weightedPipelineFamily_parent :
    (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).parent = F.parent :=
  weightedPipelineFamily_parent_private F hδ hdisc D r hr hOmega T' w₁

private theorem weightedPipelineFamily_outerBody_private (j : κ) :
    ((F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).outerBody j).toConvexSpaceBody =
      (F.outerBody j).cthickening (F.outerBody j).scale := rfl

/-- The output outer carrier is the canonical enlarged outer carrier. -/
@[simp]
theorem weightedPipelineFamily_outerBody_toConvexSpaceBody (j : κ) :
    ((F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).outerBody j).toConvexSpaceBody =
      (F.outerBody j).cthickening (F.outerBody j).scale :=
  weightedPipelineFamily_outerBody_private F hδ hdisc D r hr hOmega T' w₁ j

private theorem weightedPipelineFamily_innerBody_private (i : ι) :
    ((F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody := rfl

/-- The weighted pipeline changes inner shadings but not inner carriers. -/
@[simp]
theorem weightedPipelineFamily_innerBody_toConvexSpaceBody (i : ι) :
    ((F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody :=
  weightedPipelineFamily_innerBody_private F hδ hdisc D r hr hOmega T' w₁ i

private theorem weightedPipelineFamily_innerBody_eq_private :
    (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerBody =
      step5InnerBody F F.step0.innerSet (F.weightedPipelineStep1 hδ hdisc D).outerSet
        (F.weightedPipelineSet hδ hdisc D r hr) hOmega
        (F.weightedPipelineExponent hδ hdisc D r hr) T' w₁ := rfl

/-- The output inner shading is exactly the Step 5 shading. -/
theorem weightedPipelineFamily_innerBody :
    (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerBody =
      step5InnerBody F F.step0.innerSet (F.weightedPipelineStep1 hδ hdisc D).outerSet
        (F.weightedPipelineSet hδ hdisc D r hr) hOmega
        (F.weightedPipelineExponent hδ hdisc D r hr) T' w₁ :=
  weightedPipelineFamily_innerBody_eq_private F hδ hdisc D r hr hOmega T' w₁

/-- The normalized volumes of surviving weighted-pipeline fibers are pairwise comparable. -/
theorem weightedPipelineFamily_normalizedFiberVolume_le_two_mul {j j' : κ}
    (hj : j ∈ (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).outerSet)
    (hj' : j' ∈ (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).outerSet) :
    normalizedFiberVolume F F.innerSet j ≤
      2 * normalizedFiberVolume F F.innerSet j' :=
  F.normalizedFiberVolume_weightedStep1AtScale_le_two_mul hδ hdisc D.exponent
    D.volume_outer_le hj hj'

/-- On its shaded union, the weighted pipeline retains the global dyadic multiplicity interval
selected in Steps 2--3. -/
theorem weightedPipelineFamily_multiplicity {x : E}
    (hx : x ∈ iUnionShade
      (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerSet
      (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerBody) :
    let L := 2 ^ F.weightedPipelineExponent hδ hdisc D r hr *
      2 ^ F.weightedPipelineOuterExponent hδ hdisc D r hr
    L ≤ pointwiseMultiplicity
        (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerSet
        (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerBody x ∧
      pointwiseMultiplicity
          (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerSet
          (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerBody x <
        4 * L := by
  classical
  let V₃ := step3InnerBody F F.step0.innerSet
    (F.weightedPipelineStep1 hδ hdisc D).outerSet
    (F.weightedPipelineSet hδ hdisc D r hr) hOmega
    (F.weightedPipelineExponent hδ hdisc D r hr)
  let G := F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  have hxi₅ : x ∈ (step5InnerBody F F.step0.innerSet
      (F.weightedPipelineStep1 hδ hdisc D).outerSet
      (F.weightedPipelineSet hδ hdisc D r hr) hOmega
      (F.weightedPipelineExponent hδ hdisc D r hr) T' w₁ i).shade := by
    simpa [G, weightedPipelineFamily] using hxi
  rw [shade_step5InnerBody] at hxi₅
  have hx₃ : x ∈ iUnionShade (F.weightedPipelineInnerSet hδ hdisc D) V₃ := by
    refine Set.mem_iUnion₂.mpr ⟨i, ?_, hxi₅.1⟩
    simpa [G] using hi
  have hbound := weightedPipelineStep3_multiplicity F hδ hdisc D r hr hOmega hx₃
  have hsel : x ∈ step5Selection T' w₁ := hxi₅.2
  simpa [G, V₃, weightedPipelineFamily, pointwiseMultiplicity,
    shade_step5InnerBody, hsel, weightedPipelineInnerSet_eq_filter] using hbound

/-- On every surviving fiber, weighted Step 2 supplies one common dyadic multiplicity level. -/
theorem weightedPipelineFamily_fiber_multiplicity {j : κ} {x : E}
    (hx : x ∈ iUnionShade
      ((F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).fiber j)
      (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerBody) :
    2 ^ F.weightedPipelineExponent hδ hdisc D r hr ≤
        pointwiseMultiplicity
          ((F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).fiber j)
          (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerBody x ∧
      pointwiseMultiplicity
          ((F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).fiber j)
          (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerBody x <
        2 ^ (F.weightedPipelineExponent hδ hdisc D r hr + 1) := by
  classical
  let u := F.step0.innerSet
  let t := (F.weightedPipelineStep1 hδ hdisc D).outerSet
  let Omega := F.weightedPipelineSet hδ hdisc D r hr
  let k := F.weightedPipelineExponent hδ hdisc D r hr
  let G := F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  have hi' : i ∈ G.innerSet ∧ G.parent i = j := by
    simpa only [ShadedFactorFamily.fiber, Finset.mem_filter] using hi
  have hiG : i ∈ G.innerSet := hi'.1
  have hp : G.parent i = j := hi'.2
  have hj : j ∈ t := by
    have hparent := G.parent_mem i hiG
    simpa [G, t, weightedPipelineFamily] using hp ▸ hparent
  have hsfiber : G.fiber j = {q ∈ u | F.parent q = j} := by
    rw [ShadedFactorFamily.fiber]
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hqG, hpq⟩
      have hqG' : q ∈ F.weightedPipelineInnerSet hδ hdisc D := by
        simpa [G] using hqG
      rw [weightedPipelineInnerSet_eq_filter] at hqG'
      exact ⟨(Finset.mem_filter.mp hqG').1, by
        simpa [G, weightedPipelineFamily] using hpq⟩
    · rintro ⟨hqu, hpq⟩
      have hqG : q ∈ G.innerSet := by
        have hqin : q ∈ F.weightedPipelineInnerSet hδ hdisc D := by
          rw [weightedPipelineInnerSet_eq_filter]
          exact Finset.mem_filter.mpr ⟨hqu, by simpa [hpq] using hj⟩
        simpa [G] using hqin
      exact ⟨hqG, by simpa [G, weightedPipelineFamily] using hpq⟩
  have h3fiber :
      (step3FactorFamily F F.innerSet_step0_subset t Omega hOmega k).fiber j =
        {q ∈ u | F.parent q = j} :=
    step3FactorFamily_fiber F F.innerSet_step0_subset t Omega hOmega k hj
  have hxi5 : x ∈ (step5InnerBody F u t Omega hOmega k T' w₁ i).shade := by
    simpa [G, u, t, Omega, k, weightedPipelineFamily] using hxi
  rw [shade_step5InnerBody] at hxi5
  have hx3 : x ∈ iUnionShade
      ((step3FactorFamily F F.innerSet_step0_subset t Omega hOmega k).fiber j)
      (step3FactorFamily F F.innerSet_step0_subset t Omega hOmega k).innerBody := by
    refine Set.mem_iUnion₂.mpr ⟨i, ?_, ?_⟩
    · rw [h3fiber, ← hsfiber]
      exact hi
    · simpa only [step3FactorFamily_innerBody] using hxi5.1
  have hbound := step3FactorFamily_fiber_multiplicity F F.innerSet_step0_subset
    t Omega hOmega k hx3
  have hsel : x ∈ step5Selection T' w₁ := hxi5.2
  rw [h3fiber] at hbound
  rw [hsfiber]
  simpa [G, u, t, Omega, k, weightedPipelineFamily, pointwiseMultiplicity,
    shade_step5InnerBody, hsel] using hbound

end FactorFamily

end ShadedBody
