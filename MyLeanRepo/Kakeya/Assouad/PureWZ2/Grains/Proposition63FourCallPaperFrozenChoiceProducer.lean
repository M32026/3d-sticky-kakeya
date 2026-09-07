import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperPrelude
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPairScalarChoices
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperSeedCutoff
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperNestedPointCover

/-!
# Frozen paper-ordered Proposition 6.3 producer

This module keeps the first-call frozen-choice plumbing, but runs the last
three calls in the paper order.  The robust and interval-target scales are
distinct, and the fourth call uses the unweakened internal kernel.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- The two arithmetic inequalities which change when the interval target
scale and the internal fourth loss replace their legacy counterparts. -/
structure Proposition63FourCallPaperArithmeticReceiptsAt
    {delta sigma discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {outputLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed sigma outputLoss discreteLoss)
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    (sqrtPackage : Proposition63FourCallFrozenChoiceSqrtScalePackage
      seed.fourthKernel.internalLoss scales)
    (paperScales : Proposition63FourCallPaperScalePackage seed scales)
    (incidence : ℝ) (sourceCoefficient : NNReal)
    (firstConstant finalConstant : ENNReal) where
  firstArithmetic : ENNReal.ofReal
    ((proposition63RobustTauTotalVolume scales.rhoHat.1 sigma
        seed.schedule.third.normalizationLoss seed.schedule.thirdOutputLoss
        paperScales.targetRequested.1 scales.tau /
      (Real.rpow scales.rhoHat.1
          (1 + 7 * seed.epsilon₁ + seed.paperAngularExponent) *
        scales.tau ^ 2 / 200)) *
      (2 * proposition63DependentSlabWidth scales.rhoHat.1 scales.tau
        (proposition63DependentCoarseIncidence scales.rhoHat.1 incidence
          (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)))
        (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)) /
          scales.rhoHat.1 + 2)) ≤
    firstConstant *
      Kakeya.realRpowENN (scales.tau / scales.rhoHat.1) (1 - sigma)
  finalArithmetic : ENNReal.ofReal
    ((proposition63RobustTauTotalVolume scales.rhoHat.1 sigma
        seed.schedule.fourth.normalizationLoss seed.fourthKernel.internalLoss
        sqrtPackage.sqrtRequested.1 sqrtPackage.sqrtRequested.1 /
      (Real.rpow scales.rhoHat.1
          (1 + 7 * seed.epsilon₁ + seed.paperAngularExponent) *
        sqrtPackage.sqrtRequested.1 ^ 2 / 200)) *
      (2 * proposition63DependentSlabWidth scales.rhoHat.1
        sqrtPackage.sqrtRequested.1
        (proposition63DependentCoarseIncidence scales.rhoHat.1 incidence
          (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)))
        (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)) /
          scales.rhoHat.1 + 2)) ≤
    finalConstant * Kakeya.realRpowENN
      (sqrtPackage.sqrtRequested.1 / scales.rhoHat.1) (1 - sigma)

/-- Run one frozen ordered-pair choice on the actual current shading and
return the paper-ordered call2/call3/call4 M3 object. -/
theorem proposition63_four_call_paper_frozen_choice_producer
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
    (global : Proposition63FourCallPaperPreludeGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient)
    (index : ℕ)
    (hindex : index < (finiteIntervalOrderedPairs gridN).length)
    (paperCutoff : Proposition63FourCallPaperSeedCutoffData
      (backward.seed index hindex)
      ((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)))
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    (hrhoCutoff : scales.rhoHat.1 ≤ paperCutoff.rhoCutoff)
    {rhoInputLoss rhoNormalizationLoss : ℝ}
    {rhoSource : PureWZ2ExtremalConfiguration sigma rhoInputLoss
      scales.rhoHat.1}
    (rhoNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := rhoNormalizationLoss) rhoSource 0)
    {rhoCurrent : WZ1PaperTubeShading rhoNormalized.croppedFamily}
    (firstReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := (backward.seed index hindex).schedule.second.sourceLoss)
      rhoNormalized rhoCurrent)
    (hfirstNormalization : firstReentry.reentryNormalizationLoss =
      (backward.seed index hindex).schedule.second.normalizationLoss)
    (currentMap : PaperWZ1WeakPlaneMapData rhoCurrent
      (proposition63DependentCoarseIncidence scales.rhoHat.1 incidence
        (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient))))
    (hplaneLipschitz : LipschitzWith
      (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient))
      currentMap.planeMap) :
    let seed := backward.seed index hindex
    let publicSqrt := scales.choiceSqrtScalePackage
      (backward.loss (index + 1))
      (backward.loss_pos (index + 1) (by omega))
      ((backward.loss_le_terminal (index + 1) (by omega)).trans
        global.outputLoss_le_half)
      (global.rho_small index hindex scales)
    let receipts := global.scalar_receipts index hindex scales publicSqrt
      paperCutoff hrhoCutoff
    let paperScales := scales.choicePaperScalePackage seed
      global.discreteLoss_lt_half
    let sqrtPackage := scales.choiceSqrtScalePackage
      seed.fourthKernel.internalLoss seed.fourthKernel.internalLoss_pos
      (seed.fourthKernel.internalLoss_lt_discrete.le.trans
        global.discreteLoss_lt_half.le)
      (global.rho_small index hindex scales)
    let firstChoice := proposition63_four_call_first_constant_choice
      (rho := scales.rhoHat.1) (tau := scales.tau) (sigma := sigma)
      (normalizationLoss := seed.schedule.third.normalizationLoss)
      (outputLoss := seed.schedule.thirdOutputLoss)
      (robustScale := paperScales.targetRequested.1)
      (epsilon₁ := seed.epsilon₁)
      (epsilon₃ := seed.paperAngularExponent) (incidence := incidence)
      (coefficient :=
        4 * (lipschitzExtensionConstant Point3 * sourceCoefficient))
      (by
        exact (grid.scale_pos _
          (scales.first_lt_second.le.trans scales.second_le_gridN)).trans_le
            scales.logicalR_le_rhoHat)
      scales.rhoHat_le_tau receipts.hsigmaOne
    let finalChoice := proposition63_four_call_final_constant_choice
      (rho := scales.rhoHat.1) (sigma := sigma)
      (normalizationLoss := seed.schedule.fourth.normalizationLoss)
      (outputLoss := seed.fourthKernel.internalLoss)
      (sqrtScale := sqrtPackage.sqrtRequested.1)
      (epsilon₁ := seed.epsilon₁)
      (epsilon₃ := seed.paperAngularExponent) (incidence := incidence)
      (coefficient :=
        4 * (lipschitzExtensionConstant Point3 * sourceCoefficient))
      (by
        exact (grid.scale_pos _
          (scales.first_lt_second.le.trans scales.second_le_gridN)).trans_le
            scales.logicalR_le_rhoHat)
      sqrtPackage.sqrtRequested.property.1 receipts.hsigmaOne.le
    Nonempty (Proposition63FourCallPaperNestedPointCoverData
      (outerLoss := (backward.seed index hindex).schedule.secondOutputLoss)
      (targetReentryLoss :=
        (backward.seed index hindex).schedule.third.sourceLoss)
      (targetNormalizationLoss :=
        (backward.seed index hindex).schedule.third.normalizationLoss)
      (targetLoss := (backward.seed index hindex).schedule.thirdOutputLoss)
      (targetFirstLoss := (backward.seed index hindex).firstLoss)
      (restoredFirstLoss :=
        (backward.seed index hindex).ancestorRestoredLoss)
      (reentryLoss := (backward.seed index hindex).schedule.fourth.sourceLoss)
      (sqrtStickyLoss :=
        (backward.seed index hindex).fourthKernel.internalLoss)
      (secondLoss := (backward.seed index hindex).secondLoss)
      (finalLoss := (backward.seed index hindex).finalLoss)
      (tauScale := scales.tau)
      (sqrtScale := Real.sqrt scales.rhoHat.1) firstReentry
      (backward.seed index hindex).schedule.second.sourceLoss_pos
      (scales.choicePaperScalePackage (backward.seed index hindex)
        global.discreteLoss_lt_half).robustRequested
      (scales.choicePaperScalePackage (backward.seed index hindex)
        global.discreteLoss_lt_half).targetRequested
      (scales.choiceSqrtScalePackage
        (backward.seed index hindex).fourthKernel.internalLoss
        (backward.seed index hindex).fourthKernel.internalLoss_pos
        (by
          exact ((backward.seed index hindex).fourthKernel.internalLoss_lt_discrete.le.trans
            global.discreteLoss_lt_half.le))
        (global.rho_small index hindex scales)).sqrtRequested
      currentMap
      (firstChoice.firstConstant *
        Kakeya.realRpowENN (scales.tau / scales.rhoHat.1) (1 - sigma))
      (finalChoice.finalConstant *
        Kakeya.realRpowENN
          (Real.sqrt scales.rhoHat.1 / scales.rhoHat.1) (1 - sigma))
      (backward.seed index hindex).firstStageWeightLoss
      (backward.seed index hindex).nextWeightLoss) := by
  let seed := backward.seed index hindex
  let schedule := seed.schedule
  let cutoff := paperCutoff
  let publicSqrt := scales.choiceSqrtScalePackage
    (backward.loss (index + 1))
    (backward.loss_pos (index + 1) (by omega))
    ((backward.loss_le_terminal (index + 1) (by omega)).trans
      global.outputLoss_le_half)
    (global.rho_small index hindex scales)
  let sqrtPackage := scales.choiceSqrtScalePackage seed.fourthKernel.internalLoss
    seed.fourthKernel.internalLoss_pos
    (seed.fourthKernel.internalLoss_lt_discrete.le.trans
      global.discreteLoss_lt_half.le)
    (global.rho_small index hindex scales)
  let paperScales := scales.choicePaperScalePackage seed
    global.discreteLoss_lt_half
  let receipts := global.scalar_receipts index hindex scales publicSqrt
    paperCutoff hrhoCutoff
  let firstChoice := proposition63_four_call_first_constant_choice
    (rho := scales.rhoHat.1) (tau := scales.tau) (sigma := sigma)
    (normalizationLoss := seed.schedule.third.normalizationLoss)
    (outputLoss := seed.schedule.thirdOutputLoss)
    (robustScale := paperScales.targetRequested.1)
    (epsilon₁ := seed.epsilon₁) (epsilon₃ := seed.paperAngularExponent)
    (incidence := incidence)
    (coefficient :=
      4 * (lipschitzExtensionConstant Point3 * sourceCoefficient))
    (by
      exact (grid.scale_pos _
        (scales.first_lt_second.le.trans scales.second_le_gridN)).trans_le
          scales.logicalR_le_rhoHat)
    scales.rhoHat_le_tau receipts.hsigmaOne
  let finalChoice := proposition63_four_call_final_constant_choice
    (rho := scales.rhoHat.1) (sigma := sigma)
    (normalizationLoss := seed.schedule.fourth.normalizationLoss)
    (outputLoss := seed.fourthKernel.internalLoss)
    (sqrtScale := sqrtPackage.sqrtRequested.1)
    (epsilon₁ := seed.epsilon₁) (epsilon₃ := seed.paperAngularExponent)
    (incidence := incidence)
    (coefficient :=
      4 * (lipschitzExtensionConstant Point3 * sourceCoefficient))
    (by
      exact (grid.scale_pos _
        (scales.first_lt_second.le.trans scales.second_le_gridN)).trans_le
          scales.logicalR_le_rhoHat)
    sqrtPackage.sqrtRequested.property.1 receipts.hsigmaOne.le
  have hdeltaFirstStageSeed :
      scales.rhoHat.1 ≤ seed.firstStageAbsorption.delta₀ :=
    receipts.hdeltaFirstStage
  have hdeltaFirstCrossSeed :
      scales.rhoHat.1 ≤ seed.paperFirstCrossAbsorption.delta₀ :=
    hrhoCutoff.trans paperCutoff.rhoCutoff_le_paperFirstCrossAbsorption
  have hdeltaAncestorReentrySeed :
      scales.rhoHat.1 ≤ seed.ancestorReentryAbsorption.delta₀ :=
    hrhoCutoff.trans paperCutoff.rhoCutoff_le_ancestorReentryAbsorption
  have hdeltaSecondCrossSeed :
      scales.rhoHat.1 ≤ seed.paperSecondCrossAbsorption.delta₀ :=
    hrhoCutoff.trans paperCutoff.rhoCutoff_le_paperSecondCrossAbsorption
  let firstStageAbsorption : Proposition63CurrentReentryAbsorptionData
      schedule.second.sourceLoss firstReentry.reentryNormalizationLoss
      seed.firstStageDensityLoss seed.outerExtremalLoss
      seed.firstStageWeightLoss schedule.third.sourceLoss
      (proposition63CanonicalNearbyLevelCount
        firstReentry.reentryNormalizationLoss) := {
    delta₀ := seed.firstStageAbsorption.delta₀
    delta₀_pos := seed.firstStageAbsorption.delta₀_pos
    delta₀_le_one := seed.firstStageAbsorption.delta₀_le_one
    delta₀_le_tiny := seed.firstStageAbsorption.delta₀_le_tiny
    density_absorb := seed.firstStageAbsorption.density_absorb
    ambient_two := by
      intro delta hdeltaPos hdelta
      simpa only [hfirstNormalization] using
        seed.firstStageAbsorption.ambient_two hdeltaPos hdelta
    canonical_weight_absorb := seed.firstStageAbsorption.canonical_weight_absorb
    trace_fixed_absorb := seed.firstStageAbsorption.trace_fixed_absorb
    paper_fixed_absorb := seed.firstStageAbsorption.paper_fixed_absorb
    regularization_absorb := by
      intro delta sigma' inputLoss actualNormalizationLoss actualReentryLoss
        source' normalizationExponent' actualLevelCount normalized
        hnormalization schedule' hreentry hlevel hdeltaPos hdelta
      apply seed.firstStageAbsorption.regularization_absorb normalized
        (hnormalization.trans hfirstNormalization) schedule' hreentry
        (by
          simpa only [seed] using hlevel.trans
            (congrArg proposition63CanonicalNearbyLevelCount
              hfirstNormalization)) hdeltaPos hdelta
  }
  have hdeltaFirstStage : scales.rhoHat.1 ≤ firstStageAbsorption.delta₀ := by
    exact hdeltaFirstStageSeed
  let firstCrossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        seed.paperAngularExponent schedule.secondOutputLoss
        schedule.third.normalizationLoss seed.firstStageWeightLoss 4
        (proposition63CanonicalNearbyLevelCount
          firstReentry.reentryNormalizationLoss) := {
    delta₀ := seed.paperFirstCrossAbsorption.delta₀
    delta₀_pos := seed.paperFirstCrossAbsorption.delta₀_pos
    delta₀_le_one := seed.paperFirstCrossAbsorption.delta₀_le_one
    delta₀_le_tiny := seed.paperFirstCrossAbsorption.delta₀_le_tiny
    absorb := by
      intro delta robustScale terminalLoss hdeltaPos hdelta hrobust
        hterminalPos hterminal
      simpa only [seed, schedule, hfirstNormalization] using
        seed.paperFirstCrossAbsorption.absorb hdeltaPos hdelta hrobust
          hterminalPos hterminal
  }
  have hdeltaFirstCross : scales.rhoHat.1 ≤ firstCrossAbsorption.delta₀ := by
    exact hdeltaFirstCrossSeed
  let ancestorReentryAbsorption : Proposition63CurrentReentryAbsorptionData
      schedule.second.sourceLoss firstReentry.reentryNormalizationLoss
      seed.firstStageDensityLoss seed.ancestorRestoredLoss seed.nextWeightLoss
      schedule.fourth.sourceLoss
      (proposition63CanonicalNearbyLevelCount
        firstReentry.reentryNormalizationLoss) := {
    delta₀ := seed.ancestorReentryAbsorption.delta₀
    delta₀_pos := seed.ancestorReentryAbsorption.delta₀_pos
    delta₀_le_one := seed.ancestorReentryAbsorption.delta₀_le_one
    delta₀_le_tiny := seed.ancestorReentryAbsorption.delta₀_le_tiny
    density_absorb := seed.ancestorReentryAbsorption.density_absorb
    ambient_two := by
      intro delta hdeltaPos hdelta
      simpa only [hfirstNormalization] using
        seed.ancestorReentryAbsorption.ambient_two hdeltaPos hdelta
    canonical_weight_absorb := seed.ancestorReentryAbsorption.canonical_weight_absorb
    trace_fixed_absorb := seed.ancestorReentryAbsorption.trace_fixed_absorb
    paper_fixed_absorb := seed.ancestorReentryAbsorption.paper_fixed_absorb
    regularization_absorb := by
      intro delta sigma' inputLoss actualNormalizationLoss actualReentryLoss
        source' normalizationExponent' actualLevelCount normalized
        hnormalization schedule' hreentry hlevel hdeltaPos hdelta
      apply seed.ancestorReentryAbsorption.regularization_absorb normalized
        (hnormalization.trans hfirstNormalization) schedule' hreentry
        (by
          simpa only [seed] using hlevel.trans
            (congrArg proposition63CanonicalNearbyLevelCount
              hfirstNormalization)) hdeltaPos hdelta
  }
  have hdeltaAncestorReentry :
      scales.rhoHat.1 ≤ ancestorReentryAbsorption.delta₀ := by
    exact hdeltaAncestorReentrySeed
  let secondCrossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        seed.paperAngularExponent schedule.secondOutputLoss
        schedule.fourth.normalizationLoss seed.nextWeightLoss 4
        (proposition63CanonicalNearbyLevelCount
          firstReentry.reentryNormalizationLoss) := {
    delta₀ := seed.paperSecondCrossAbsorption.delta₀
    delta₀_pos := seed.paperSecondCrossAbsorption.delta₀_pos
    delta₀_le_one := seed.paperSecondCrossAbsorption.delta₀_le_one
    delta₀_le_tiny := seed.paperSecondCrossAbsorption.delta₀_le_tiny
    absorb := by
      intro delta robustScale terminalLoss hdeltaPos hdelta hrobust
        hterminalPos hterminal
      simpa only [seed, schedule, hfirstNormalization] using
        seed.paperSecondCrossAbsorption.absorb hdeltaPos hdelta hrobust
          hterminalPos hterminal
  }
  have hdeltaSecondCross : scales.rhoHat.1 ≤ secondCrossAbsorption.delta₀ := by
    exact hdeltaSecondCrossSeed
  let ancestorDensityLiftAbsorption :
      Proposition63ReentryDensityLiftAbsorptionData
        seed.firstStageWeightLoss seed.firstLoss seed.ancestorRestoredLoss
        (proposition63CanonicalNearbyLevelCount
          firstReentry.reentryNormalizationLoss) := {
    delta₀ := seed.ancestorDensityLiftAbsorption.delta₀
    delta₀_pos := seed.ancestorDensityLiftAbsorption.delta₀_pos
    delta₀_le_one := seed.ancestorDensityLiftAbsorption.delta₀_le_one
    delta₀_le_tiny := seed.ancestorDensityLiftAbsorption.delta₀_le_tiny
    absorb := by
      intro delta hdeltaPos hdelta
      simpa only [seed, schedule, hfirstNormalization] using
        seed.ancestorDensityLiftAbsorption.absorb hdeltaPos hdelta
  }
  have hrhoPos : 0 < scales.rhoHat.1 :=
    (grid.scale_pos _
      (scales.first_lt_second.le.trans scales.second_le_gridN)).trans_le
        scales.logicalR_le_rhoHat
  have hrhoPaper : scales.rhoHat.1 ≤ cutoff.rhoCutoff := by
    exact hrhoCutoff
  have htargetSmall : paperScales.targetRequested.1 ≤ 1 / 12 := by
    have hsqrt : Real.sqrt scales.rhoHat.1 ≤ 1 / 12 := by
      have hrhoNonneg := hrhoPos.le
      nlinarith [Real.sqrt_nonneg scales.rhoHat.1,
        Real.sq_sqrt hrhoNonneg, global.rho_small index hindex scales]
    rw [paperScales.targetScale_eq]
    apply max_le
    · exact (scales.tau_le_sqrt_logicalR.trans
        (Real.sqrt_le_sqrt scales.logicalR_le_rhoHat)).trans hsqrt
    · calc
        Real.rpow scales.rhoHat.1
            (1 - seed.schedule.thirdOutputLoss) ≤
            Real.sqrt scales.rhoHat.1 := by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_ge hrhoPos
            scales.rhoHat.property.2 (by
              linarith [seed.thirdOutputLoss_le_discrete,
                global.discreteLoss_lt_half])
        _ ≤ 1 / 12 := hsqrt
  have hkernelDelta : scales.rhoHat.1 ≤
      seed.fourthKernel.internalSchedule.delta₀ := by
    have hpublic := congrArg
      Proposition63RichStickyKernelScheduleData.delta₀
      seed.fourthKernel.public_eq
    have heq : schedule.fourth.delta₀ =
        seed.fourthKernel.internalSchedule.delta₀ := by
      simpa only [Proposition63RichStickyKernelScheduleData.mono_loss] using hpublic
    rw [← heq]
    exact receipts.hdeltaFourth
  have hrhoTiny : scales.rhoHat.1 ≤ 1 / 1000 :=
    (hrhoPaper.trans cutoff.rhoCutoff_le_ancestorReentryAbsorption).trans
      (seed.ancestorReentryAbsorption.delta₀_le_tiny.trans (by norm_num))
  apply proposition63_rho_level_four_call_paper_nested_point_cover_of_absorptions
    (paperRobustExponent := seed.paperAngularExponent)
    (epsilon₁ := seed.epsilon₁) (epsilon₃ := seed.paperAngularExponent)
    (firstStageDensityLoss := seed.firstStageDensityLoss)
    (firstStageWeightLoss := seed.firstStageWeightLoss)
    (outerExtremalLoss := seed.outerExtremalLoss)
    (parentLoss := seed.parentLoss) (firstLoss := seed.firstLoss)
    (ancestorRestoredLoss := seed.ancestorRestoredLoss)
    (nextWeightLoss := seed.nextWeightLoss)
    (secondLoss := seed.secondLoss) (middleLoss := seed.middleLoss)
    (finalLoss := seed.finalLoss)
    firstReentry schedule seed.fourthKernel rfl hfirstNormalization
    receipts.hdeltaSecondCall paperScales.robustRequested
    paperScales.robustLower paperScales.robustUpper receipts.hdeltaThirdCall
    firstStageAbsorption hdeltaFirstStage
    (by simpa only [hfirstNormalization] using receipts.hsourceOuter)
    receipts.houterExtremalLoss
    (by simpa only [hfirstNormalization] using
      seed.outerRetentionAbsorption.absorb hrhoPos receipts.hrhoOuterRetention)
    receipts.houterTargetReentry paperScales.targetRequested
    paperScales.targetLower paperScales.targetUpper currentMap hplaneLipschitz
    seed.firstGridAbsorption firstCrossAbsorption receipts.hdeltaFirstGrid
    hdeltaFirstCross
    paperScales.robustScale_eq scales.rhoHat_le_tau scales.tau_pos
    scales.tau_le_one seed.firstBoundaryAbsorption
    receipts.hdeltaFirstBoundary
    (cutoff.paperRobustScale_small scales.rhoHat.1 hrhoPos hrhoPaper)
    paperScales.robustKappa htargetSmall paperScales.targetTau
    (scales.scale_smallness global.coefficient_one global.discreteLoss_pos.le
      global.amplified_query_small).2.2.2
    receipts.hsigma receipts.hsigmaOne seed.epsilon₁_pos
    seed.paperAngularExponent_pos seed.paper_epsilon_sum_lt_one
    receipts.logScale receipts.hdeltaLog receipts.hlog
    (cutoff.paperCordobaAxis scales.rhoHat.1 hrhoPos hrhoPaper)
    firstChoice.firstConstant firstChoice.arithmetic
    (by rw [seed.parentLoss_eq, ← schedule.thirdOutputLoss_eq];
        exact schedule.third.normalizationLoss_lt_output.le)
    (seed.parentRetentionAbsorption.absorb hrhoPos
      receipts.hrhoParentRetention)
    (by rw [seed.parentLoss_eq, seed.firstLoss_eq];
        linarith [schedule.fourth.sourceLoss_pos])
    (by rw [seed.firstLoss_eq];
        exact div_pos schedule.fourth.sourceLoss_pos (by norm_num))
    seed.firstRestoreAbsorption receipts.hdeltaFirstRestore
    (by
      rw [seed.outerExtremalLoss_eq, seed.ancestorRestoredLoss_eq]
      have hthirdSourceLtFourth :
          seed.schedule.third.sourceLoss <
            seed.schedule.fourth.sourceLoss / 32 := by
        calc
          seed.schedule.third.sourceLoss ≤
              seed.schedule.third.normalizationLoss / 2 :=
            seed.schedule.third.sourceLoss_le_half
          _ < seed.schedule.thirdOutputLoss / 2 := by
            linarith [seed.schedule.third.normalizationLoss_lt_output]
          _ = seed.schedule.fourth.sourceLoss / 32 := by
            rw [seed.schedule.thirdOutputLoss_eq]
            ring
      linarith [hthirdSourceLtFourth, schedule.fourth.sourceLoss_pos])
    (by rw [seed.ancestorRestoredLoss_eq];
        exact div_pos schedule.fourth.sourceLoss_pos (by norm_num))
    ancestorDensityLiftAbsorption
    (hrhoPaper.trans cutoff.rhoCutoff_le_ancestorDensityLiftAbsorption)
    ancestorReentryAbsorption hdeltaAncestorReentry
    (by rw [seed.ancestorRestoredLoss_eq];
        linarith [schedule.fourth.sourceLoss_pos])
    hkernelDelta sqrtPackage.sqrtRequested sqrtPackage.hsqrtLower
    sqrtPackage.hsqrtUpper sqrtPackage.hsqrtOne
    seed.internalFourthBoundaryAbsorption
    (hrhoPaper.trans cutoff.rhoCutoff_le_internalFourthBoundaryAbsorption)
    seed.secondGridAbsorption receipts.hdeltaSecondGrid
    secondCrossAbsorption hdeltaSecondCross
    sqrtPackage.hsqrtSmall hrhoTiny sqrtPackage.hsqrtSq
    finalChoice.finalConstant finalChoice.arithmetic
    (by
      rw [seed.secondLoss_eq]
      have htrace := seed.traceGap
      rw [seed.finalLoss_eq, seed.middleLoss_eq, seed.secondLoss_eq] at htrace
      ring_nf at htrace ⊢
      linarith [schedule.fourth.sourceLoss_pos])
    (by rw [seed.secondLoss_eq];
        exact div_pos (add_pos schedule.fourth.normalizationLoss_pos
          seed.critical.structuralLoss_pos) (by norm_num))
    seed.secondRestoreAbsorption receipts.hdeltaSecondRestore
    (by
      rw [seed.middleLoss_eq]
      have htrace := seed.traceGap
      rw [seed.finalLoss_eq, seed.middleLoss_eq, seed.secondLoss_eq] at htrace
      rw [seed.secondLoss_eq]
      ring_nf at htrace ⊢
      linarith [schedule.fourth.sourceLoss_pos])
    (by
      rw [seed.middleLoss_eq]
      have hsecond : 0 < seed.secondLoss := by
        rw [seed.secondLoss_eq]
        exact div_pos (add_pos schedule.fourth.normalizationLoss_pos
          seed.critical.structuralLoss_pos) (by norm_num)
      exact div_pos (add_pos hsecond seed.critical.structuralLoss_pos)
        (by norm_num))
    seed.multiplicityAbsorption receipts.hdeltaMultiplicity
    (seed.balancingBoundaryAbsorption.absorb hrhoPos
      receipts.hrhoBalancingBoundary sqrtPackage.sqrtRequested
      sqrtPackage.sqrtScale_eq)
    seed.middleLoss_lt_finalLoss.le
    (by
      have hmiddle : 0 < seed.middleLoss := by
        rw [seed.middleLoss_eq]
        have hsecond : 0 < seed.secondLoss := by
          rw [seed.secondLoss_eq]
          exact div_pos (add_pos schedule.fourth.normalizationLoss_pos
            seed.critical.structuralLoss_pos) (by norm_num)
        exact div_pos (add_pos hsecond seed.critical.structuralLoss_pos)
          (by norm_num)
      exact hmiddle.trans seed.middleLoss_lt_finalLoss)
    seed.balancingAbsorption receipts.hdeltaBalancing

end Kakeya.Assouad.PureWZ2
