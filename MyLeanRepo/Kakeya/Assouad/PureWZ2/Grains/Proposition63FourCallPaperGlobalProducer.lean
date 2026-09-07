import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperOrderedPairActual
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallInnerMassSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallFirstScalarEnvelope

/-!
# Pre-runtime producer for the paper-ordered four-call global data

The paper seed cutoffs and the final-current lift cutoffs depend only on the
frozen loss schedule.  This module chooses them before any callback-local
shading is exposed and takes their finite common minimum.

The common cutoff does not by itself imply that an ordered-pair scale
`rhoHat`, which is generally larger than `delta`, lies below the cutoff.  The
global constructor therefore asks for that genuinely uniform grid-scale
smallness statement explicitly.  In particular, it does not introduce a
circular hypothesis of the form `delta <= cutoff delta`.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- All indexwise paper cutoffs, together with separate positive cutoffs for
the runtime coarse scales and the original fine scale.  The split matters:
ordered-pair `rhoHat` scales are larger than the fine `delta`, so forcing both
through one minimum would spend an artificial power in the outer envelope. -/
structure Proposition63FourCallPaperGlobalCutoffData
    {sigma inputLoss discreteLoss gridOutputLoss : ℝ}
    {gridN : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (sourceCoefficient : NNReal) where
  paperCutoff : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallPaperSeedCutoffData
        (backward.seed index hindex)
        ((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient))
  firstUniformCutoff : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallFirstUniformCutoffData
        (backward.seed index hindex)
        ((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient))
  currentReentryAbsorption : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63CurrentReentryAbsorptionData
        inputLoss backward.rootNormalizationLoss backward.rootDensityLoss
        (backward.loss index) (backward.currentWeightLoss index hindex)
        (backward.seed index hindex).schedule.first.sourceLoss
        (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss)
  finalCandidateLiftAbsorption : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63ReentryDensityLiftAbsorptionData
        (backward.currentWeightLoss index hindex)
        (backward.seed index hindex).goodCellCandidateLoss
        (backward.loss (index + 1))
        (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss)
  rhoCommon : Proposition63FinitePositiveCutoff
    (finiteIntervalOrderedPairs gridN).length
    (fun index hindex => (paperCutoff index hindex).rhoCutoff)
  deltaCommon : Proposition63FinitePositiveCutoff
    (finiteIntervalOrderedPairs gridN).length
    (fun index hindex =>
      min (currentReentryAbsorption index hindex).delta₀ <|
      min (finalCandidateLiftAbsorption index hindex).delta₀ <|
      min (backward.seed index hindex).alignedAbsorption.delta₀
        (firstUniformCutoff index hindex).nested.delta₀)

/-- Aggregate explicitly supplied coefficient-aware paper and first-constant
cutoffs with the canonical loss-only fine-scale absorptions.  This is the
outer-envelope constructor: all coefficient-dependent choices are made by the
caller from pre-runtime power receipts. -/
theorem proposition63_four_call_paper_global_cutoff_of_families
    {sigma inputLoss discreteLoss gridOutputLoss : ℝ}
    {gridN : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (sourceCoefficient : NNReal)
    (inputLoss_lt_density : inputLoss < backward.rootDensityLoss)
    (paperCutoff : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        Proposition63FourCallPaperSeedCutoffData
          (backward.seed index hindex)
          ((4 : NNReal) *
            (lipschitzExtensionConstant Point3 * sourceCoefficient)))
    (firstUniformCutoff : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        Proposition63FourCallFirstUniformCutoffData
          (backward.seed index hindex)
          ((4 : NNReal) *
            (lipschitzExtensionConstant Point3 * sourceCoefficient))) :
    Nonempty (Proposition63FourCallPaperGlobalCutoffData
      (inputLoss := inputLoss) backward sourceCoefficient) := by
  let currentReentryAbsorption : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63CurrentReentryAbsorptionData
        inputLoss backward.rootNormalizationLoss backward.rootDensityLoss
        (backward.loss index) (backward.currentWeightLoss index hindex)
        (backward.seed index hindex).schedule.first.sourceLoss
        (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss) :=
    fun index hindex =>
      proposition63_four_call_inner_current_reentry_absorption_at backward
        inputLoss_lt_density index hindex
  let finalCandidateLiftAbsorption : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63ReentryDensityLiftAbsorptionData
        (backward.currentWeightLoss index hindex)
        (backward.seed index hindex).goodCellCandidateLoss
        (backward.loss (index + 1))
        (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss) :=
    fun index hindex =>
      proposition63_four_call_inner_final_lift_absorption_at backward index hindex
  let deltaThreshold : ∀ index,
      index < (finiteIntervalOrderedPairs gridN).length → ℝ :=
    fun index hindex =>
      min (currentReentryAbsorption index hindex).delta₀ <|
      min (finalCandidateLiftAbsorption index hindex).delta₀ <|
      min (backward.seed index hindex).alignedAbsorption.delta₀
        (firstUniformCutoff index hindex).nested.delta₀
  have deltaThreshold_pos : ∀ index,
      ∀ hindex : index < (finiteIntervalOrderedPairs gridN).length,
        0 < deltaThreshold index hindex := by
    intro index hindex
    exact lt_min (currentReentryAbsorption index hindex).delta₀_pos <|
      lt_min (finalCandidateLiftAbsorption index hindex).delta₀_pos <|
      lt_min (backward.seed index hindex).alignedAbsorption.delta₀_pos
        (firstUniformCutoff index hindex).nested.delta₀_pos
  let rhoCommon := Classical.choice <|
    proposition63_finite_positive_cutoff
      (finiteIntervalOrderedPairs gridN).length
      (fun index hindex => (paperCutoff index hindex).rhoCutoff)
      (fun index hindex => (paperCutoff index hindex).rhoCutoff_pos)
  let deltaCommon := Classical.choice <|
    proposition63_finite_positive_cutoff
      (finiteIntervalOrderedPairs gridN).length deltaThreshold deltaThreshold_pos
  exact ⟨{
    paperCutoff := paperCutoff
    firstUniformCutoff := firstUniformCutoff
    currentReentryAbsorption := currentReentryAbsorption
    finalCandidateLiftAbsorption := finalCandidateLiftAbsorption
    rhoCommon := rhoCommon
    deltaCommon := deltaCommon
  }⟩

/-- Select every family-free paper cutoff and aggregate it with the
corresponding final-current lift cutoff. -/
theorem proposition63_four_call_paper_global_cutoff
    {sigma inputLoss discreteLoss gridOutputLoss : ℝ}
    {gridN : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (sourceCoefficient : NNReal)
    (inputLoss_lt_density : inputLoss < backward.rootDensityLoss) :
    Nonempty (Proposition63FourCallPaperGlobalCutoffData
      (inputLoss := inputLoss) backward sourceCoefficient) := by
  let paperCutoff : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallPaperSeedCutoffData
        (backward.seed index hindex)
        ((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient)) :=
    fun index hindex => Classical.choice <|
      proposition63_four_call_paper_seed_cutoff
        (backward.seed index hindex)
        ((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient))
  let firstUniformCutoff : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallFirstUniformCutoffData
        (backward.seed index hindex)
        ((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient)) :=
    fun index hindex => Classical.choice <|
      proposition63_four_call_first_uniform_cutoff
        (backward.seed index hindex)
        ((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient))
  let currentReentryAbsorption : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63CurrentReentryAbsorptionData
        inputLoss backward.rootNormalizationLoss backward.rootDensityLoss
        (backward.loss index) (backward.currentWeightLoss index hindex)
        (backward.seed index hindex).schedule.first.sourceLoss
        (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss) :=
    fun index hindex =>
      proposition63_four_call_inner_current_reentry_absorption_at backward
        inputLoss_lt_density index hindex
  let finalCandidateLiftAbsorption : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63ReentryDensityLiftAbsorptionData
        (backward.currentWeightLoss index hindex)
        (backward.seed index hindex).goodCellCandidateLoss
        (backward.loss (index + 1))
        (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss) :=
    fun index hindex =>
      proposition63_four_call_inner_final_lift_absorption_at backward index hindex
  let deltaThreshold : ∀ index,
      index < (finiteIntervalOrderedPairs gridN).length → ℝ :=
    fun index hindex =>
      min (currentReentryAbsorption index hindex).delta₀ <|
      min (finalCandidateLiftAbsorption index hindex).delta₀ <|
      min (backward.seed index hindex).alignedAbsorption.delta₀
        (firstUniformCutoff index hindex).nested.delta₀
  have deltaThreshold_pos : ∀ index,
      ∀ hindex : index < (finiteIntervalOrderedPairs gridN).length,
        0 < deltaThreshold index hindex := by
    intro index hindex
    exact lt_min (currentReentryAbsorption index hindex).delta₀_pos <|
      lt_min (finalCandidateLiftAbsorption index hindex).delta₀_pos <|
      lt_min (backward.seed index hindex).alignedAbsorption.delta₀_pos
        (firstUniformCutoff index hindex).nested.delta₀_pos
  let rhoCommon := Classical.choice <|
    proposition63_finite_positive_cutoff
      (finiteIntervalOrderedPairs gridN).length
      (fun index hindex => (paperCutoff index hindex).rhoCutoff)
      (fun index hindex => (paperCutoff index hindex).rhoCutoff_pos)
  let deltaCommon := Classical.choice <|
    proposition63_finite_positive_cutoff
      (finiteIntervalOrderedPairs gridN).length deltaThreshold deltaThreshold_pos
  exact ⟨{
    paperCutoff := paperCutoff
    firstUniformCutoff := firstUniformCutoff
    currentReentryAbsorption := currentReentryAbsorption
    finalCandidateLiftAbsorption := finalCandidateLiftAbsorption
    rhoCommon := rhoCommon
    deltaCommon := deltaCommon
  }⟩

/-- Build the post-cycle paper global package from legacy global data and one
uniform pre-runtime cutoff receipt.  The scale receipt is intentionally
separate from `delta <= common.delta₀`: ordered-pair scales are not bounded by
`delta` in the required direction. -/
theorem proposition63_four_call_paper_global_producer
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (K : ℝ)
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (leftFactor rightFactor : ℕ → ENNReal)
    (sourceCoefficient : NNReal)
    (prelude : Proposition63FourCallPaperPreludeGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient)
    (cutoff : Proposition63FourCallPaperGlobalCutoffData
      (inputLoss := inputLoss) backward sourceCoefficient)
    (rho_le_common : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      ∀ scales : Proposition63FourCallOrderedPairIndexScales grid index,
        scales.rhoHat.1 ≤ cutoff.rhoCommon.delta₀)
    (delta_le_common : delta ≤ cutoff.deltaCommon.delta₀)
    (incidence_le_delta : incidence ≤ delta) :
    Nonempty (Proposition63FourCallPaperGlobalData (incidence := incidence) K
      backward root grid leftFactor rightFactor sourceCoefficient) := by
  refine ⟨{
    prelude := prelude
    paperCutoff := cutoff.paperCutoff
    rho_le_paperCutoff := ?_
    delta_le_finalCurrentLift := ?_
    firstUniformCutoff := cutoff.firstUniformCutoff
    delta_le_firstUniformCutoff := ?_
    hdeltaCurrentReentry := ?_
    currentReentryAbsorption := cutoff.currentReentryAbsorption
    finalCandidateLiftAbsorption := cutoff.finalCandidateLiftAbsorption
    delta_le_alignedAbsorption := ?_
    incidence_le_delta := incidence_le_delta
  }⟩
  · intro index hindex scales
    exact (rho_le_common index hindex scales).trans <|
      cutoff.rhoCommon.le_threshold index hindex
  · intro index hindex
    exact delta_le_common.trans <|
      (cutoff.deltaCommon.le_threshold index hindex).trans (by simp)
  · intro index hindex
    exact delta_le_common.trans <|
      (cutoff.deltaCommon.le_threshold index hindex).trans (by simp)
  · intro index hindex
    exact delta_le_common.trans <|
      (cutoff.deltaCommon.le_threshold index hindex).trans (by simp)
  · intro index hindex
    exact delta_le_common.trans <|
      (cutoff.deltaCommon.le_threshold index hindex).trans (by simp)

/-- Build the paper runtime package from pairwise coarse-scale bounds and a
single fine-scale bound.  This is the M9-facing form: ordered-pair scales need
only lie below their own coefficient-aware cutoffs, rather than below the
artificial minimum of all pairwise thresholds. -/
theorem proposition63_four_call_paper_global_producer_pairwise
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (K : ℝ)
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (leftFactor rightFactor : ℕ → ENNReal)
    (sourceCoefficient : NNReal)
    (prelude : Proposition63FourCallPaperPreludeGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient)
    (cutoff : Proposition63FourCallPaperGlobalCutoffData
      (inputLoss := inputLoss) backward sourceCoefficient)
    (rho_le_pair : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      ∀ scales : Proposition63FourCallOrderedPairIndexScales grid index,
        scales.rhoHat.1 ≤ (cutoff.paperCutoff index hindex).rhoCutoff)
    (delta_le_common : delta ≤ cutoff.deltaCommon.delta₀)
    (incidence_le_delta : incidence ≤ delta) :
    Nonempty (Proposition63FourCallPaperGlobalData (incidence := incidence) K
      backward root grid leftFactor rightFactor sourceCoefficient) := by
  refine ⟨{
    prelude := prelude
    paperCutoff := cutoff.paperCutoff
    rho_le_paperCutoff := rho_le_pair
    delta_le_finalCurrentLift := ?_
    firstUniformCutoff := cutoff.firstUniformCutoff
    delta_le_firstUniformCutoff := ?_
    hdeltaCurrentReentry := ?_
    currentReentryAbsorption := cutoff.currentReentryAbsorption
    finalCandidateLiftAbsorption := cutoff.finalCandidateLiftAbsorption
    delta_le_alignedAbsorption := ?_
    incidence_le_delta := incidence_le_delta
  }⟩
  · intro index hindex
    exact delta_le_common.trans <|
      (cutoff.deltaCommon.le_threshold index hindex).trans (by simp)
  · intro index hindex
    exact delta_le_common.trans <|
      (cutoff.deltaCommon.le_threshold index hindex).trans (by simp)
  · intro index hindex
    exact delta_le_common.trans <|
      (cutoff.deltaCommon.le_threshold index hindex).trans (by simp)
  · intro index hindex
    exact delta_le_common.trans <|
      (cutoff.deltaCommon.le_threshold index hindex).trans (by simp)

/-- Direct pairwise constructor used by the pre-Node-3 M9 envelope.  Every
cutoff witness and every scale comparison is supplied explicitly; no new
minimum is selected after the runtime scale is known. -/
def proposition63_four_call_paper_global_data_of_pairwise
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (K : ℝ)
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (leftFactor rightFactor : ℕ → ENNReal)
    (sourceCoefficient : NNReal)
    (prelude : Proposition63FourCallPaperPreludeGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient)
    (paperCutoff : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        Proposition63FourCallPaperSeedCutoffData
          (backward.seed index hindex)
          ((4 : NNReal) *
            (lipschitzExtensionConstant Point3 * sourceCoefficient)))
    (firstUniformCutoff : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        Proposition63FourCallFirstUniformCutoffData
          (backward.seed index hindex)
          ((4 : NNReal) *
            (lipschitzExtensionConstant Point3 * sourceCoefficient)))
    (currentReentryAbsorption : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        Proposition63CurrentReentryAbsorptionData
          inputLoss backward.rootNormalizationLoss backward.rootDensityLoss
          (backward.loss index) (backward.currentWeightLoss index hindex)
          (backward.seed index hindex).schedule.first.sourceLoss
          (proposition63CanonicalNearbyLevelCount
            backward.rootNormalizationLoss))
    (finalCandidateLiftAbsorption : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        Proposition63ReentryDensityLiftAbsorptionData
          (backward.currentWeightLoss index hindex)
          (backward.seed index hindex).goodCellCandidateLoss
          (backward.loss (index + 1))
          (proposition63CanonicalNearbyLevelCount
            backward.rootNormalizationLoss))
    (rho_le_pair : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      ∀ scales : Proposition63FourCallOrderedPairIndexScales grid index,
        scales.rhoHat.1 ≤ (paperCutoff index hindex).rhoCutoff)
    (delta_le_current : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        delta ≤ (currentReentryAbsorption index hindex).delta₀)
    (delta_le_final : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        delta ≤ (finalCandidateLiftAbsorption index hindex).delta₀)
    (delta_le_aligned : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        delta ≤ (backward.seed index hindex).alignedAbsorption.delta₀)
    (delta_le_first : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        delta ≤ (firstUniformCutoff index hindex).nested.delta₀)
    (incidence_le_delta : incidence ≤ delta) :
    Proposition63FourCallPaperGlobalData (incidence := incidence) K
      backward root grid leftFactor rightFactor sourceCoefficient where
  prelude := prelude
  paperCutoff := paperCutoff
  rho_le_paperCutoff := rho_le_pair
  firstUniformCutoff := firstUniformCutoff
  delta_le_firstUniformCutoff := delta_le_first
  currentReentryAbsorption := currentReentryAbsorption
  hdeltaCurrentReentry := delta_le_current
  finalCandidateLiftAbsorption := finalCandidateLiftAbsorption
  delta_le_finalCurrentLift := delta_le_final
  delta_le_alignedAbsorption := delta_le_aligned
  incidence_le_delta := incidence_le_delta

end Kakeya.Assouad.PureWZ2
