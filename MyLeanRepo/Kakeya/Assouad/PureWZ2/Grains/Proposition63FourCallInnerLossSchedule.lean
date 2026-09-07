import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ExtremalOneScalePlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ExtremalOneScaleFullGrain
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RobustPointCoverAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63AlignedIntervalAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RichBoundarySlackSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PureCriticalTailBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallBalancingBoundaryAbsorption

/-!
# Pre-runtime losses for the four-call inner iteration

This file records the part of the M6 backward choice which is genuinely
family-free.  In particular, every receipt below is made by its proved
constructor.  The three current-reentry calls deliberately retain their own
density loss.  This also documents the obstruction in the historical M5
interface, which asked them to share one density loss.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- The genuinely small paper angular exponent, chosen after the public
output loss but before any runtime scale or family is exposed. -/
noncomputable def proposition63FourCallPaperAngularExponent
    (outputLoss discreteLoss : ℝ) : ℝ :=
  min (discreteLoss / 4) (outputLoss / 32)

/-- The auxiliary sigma budget used to choose the last hidden rich kernel. -/
noncomputable def proposition63FourCallPaperSigmaBudget
    (sigma outputLoss discreteLoss : ℝ) : ℝ :=
  proposition63FourCallPaperAngularExponent outputLoss discreteLoss *
    sigma / 100

/-- The three intermediate scalar losses between the paper candidate A and
the public output E. -/
structure Proposition63StagedCandidateLossData (outputLoss : ℝ) where
  nestedCandidateLoss : ℝ
  sourceWitnessCandidateLoss : ℝ
  goodCellCandidateLoss : ℝ
  nestedCandidateLoss_eq : nestedCandidateLoss = 13 * outputLoss / 16
  sourceWitnessCandidateLoss_eq :
    sourceWitnessCandidateLoss = 7 * outputLoss / 8
  goodCellCandidateLoss_eq : goodCellCandidateLoss = 15 * outputLoss / 16
  terminalCandidateGap :
    sourceWitnessCandidateLoss < goodCellCandidateLoss
  finalCandidateGap : goodCellCandidateLoss < outputLoss

/-- The family-free loss and absorption data which can be selected before an
ordered pair exposes its scales or its current shading. -/
structure Proposition63FourCallInnerLossSeed
    (sigma outputLoss discreteLoss : ℝ) where
  floorLoss : ℝ
  floorLoss_pos : 0 < floorLoss
  structuralBudget : ℝ
  critical : PureWZ2CriticalFloorSelectionData
    sigma floorLoss structuralBudget
  schedule : Proposition63RichFourCallScheduleData sigma outputLoss
  fourthKernel : Proposition63RichInternalKernelScheduleData
    sigma outputLoss discreteLoss critical.structuralLoss
      (discreteLoss * sigma / 100)
      schedule.fourth
  paperAngularExponent : ℝ
  intervalTargetExponent : ℝ
  robustExponent : ℝ
  epsilon₁ : ℝ
  epsilon₃ : ℝ
  rhoDensityLoss : ℝ
  rhoWeightLoss : ℝ
  firstStageDensityLoss : ℝ
  outerExtremalLoss : ℝ
  firstStageWeightLoss : ℝ
  secondReentryDensityLoss : ℝ
  parentLoss : ℝ
  firstLoss : ℝ
  ancestorRestoredLoss : ℝ
  nextWeightLoss : ℝ
  secondLoss : ℝ
  middleLoss : ℝ
  finalLoss : ℝ
  paperCandidateLoss : ℝ
  stagedCandidateLosses : Proposition63StagedCandidateLossData outputLoss
  rhoAbsorption : Proposition63CurrentReentryAbsorptionData
    (schedule.second.sourceLoss / 16) (schedule.second.sourceLoss / 4)
    rhoDensityLoss schedule.firstOutputLoss rhoWeightLoss
    schedule.second.sourceLoss
    (proposition63CanonicalNearbyLevelCount
      (schedule.second.sourceLoss / 4))
  firstStageAbsorption : Proposition63CurrentReentryAbsorptionData
    schedule.second.sourceLoss schedule.second.normalizationLoss
    firstStageDensityLoss outerExtremalLoss firstStageWeightLoss
    schedule.third.sourceLoss
    (proposition63CanonicalNearbyLevelCount
      schedule.second.normalizationLoss)
  secondReentryAbsorption : Proposition63CurrentReentryAbsorptionData
    schedule.third.sourceLoss schedule.third.normalizationLoss
    secondReentryDensityLoss firstLoss nextWeightLoss
    schedule.fourth.sourceLoss
    (proposition63CanonicalNearbyLevelCount
      schedule.third.normalizationLoss)
  firstGridAbsorption : Proposition63RobustGridPruningAbsorptionData
    schedule.third.normalizationLoss epsilon₁
  secondGridAbsorption : Proposition63RobustGridPruningAbsorptionData
    schedule.fourth.normalizationLoss epsilon₁
  firstCrossAbsorption :
    Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
      robustExponent schedule.secondOutputLoss
      schedule.third.normalizationLoss firstStageWeightLoss 4
      (proposition63CanonicalNearbyLevelCount
        schedule.second.normalizationLoss)
  secondCrossAbsorption :
    Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
      robustExponent schedule.thirdOutputLoss
      schedule.fourth.normalizationLoss nextWeightLoss 4
      (proposition63CanonicalNearbyLevelCount
        schedule.third.normalizationLoss)
  ancestorDensityLiftAbsorption : Proposition63ReentryDensityLiftAbsorptionData
    firstStageWeightLoss firstLoss ancestorRestoredLoss
    (proposition63CanonicalNearbyLevelCount
      schedule.second.normalizationLoss)
  ancestorReentryAbsorption : Proposition63CurrentReentryAbsorptionData
    schedule.second.sourceLoss schedule.second.normalizationLoss
    firstStageDensityLoss ancestorRestoredLoss nextWeightLoss
    schedule.fourth.sourceLoss
    (proposition63CanonicalNearbyLevelCount
      schedule.second.normalizationLoss)
  nestedCandidateLiftAbsorption : Proposition63ReentryDensityLiftAbsorptionData
    nextWeightLoss paperCandidateLoss
      stagedCandidateLosses.nestedCandidateLoss
    (proposition63CanonicalNearbyLevelCount
      schedule.second.normalizationLoss)
  sourceWitnessCandidateLiftAbsorption :
    Proposition63ReentryDensityLiftAbsorptionData
      rhoWeightLoss stagedCandidateLosses.nestedCandidateLoss
        stagedCandidateLosses.sourceWitnessCandidateLoss
      (proposition63CanonicalNearbyLevelCount
        (schedule.second.sourceLoss / 4))
  paperFirstCrossAbsorption :
    Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
      paperAngularExponent schedule.secondOutputLoss
      schedule.third.normalizationLoss firstStageWeightLoss 4
      (proposition63CanonicalNearbyLevelCount
        schedule.second.normalizationLoss)
  paperSecondCrossAbsorption :
    Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
      paperAngularExponent schedule.secondOutputLoss
      schedule.fourth.normalizationLoss nextWeightLoss 4
      (proposition63CanonicalNearbyLevelCount
        schedule.second.normalizationLoss)
  firstBoundaryAbsorption : Proposition63RobustBoundaryAbsorptionData
    schedule.thirdOutputLoss schedule.third.normalizationLoss
  secondBoundaryAbsorption : Proposition63RobustBoundaryAbsorptionData
    outputLoss schedule.fourth.normalizationLoss
  internalFourthBoundaryAbsorption :
    Proposition63RobustBoundaryAbsorptionData
      fourthKernel.internalLoss schedule.fourth.normalizationLoss
  outerRetentionAbsorption : Proposition63RefinementRetentionAbsorptionData
    schedule.second.normalizationLoss outerExtremalLoss 61
  parentRetentionAbsorption : Proposition63RefinementRetentionAbsorptionData
    schedule.third.normalizationLoss parentLoss 61
  firstRestoreAbsorption :
    Proposition63RobustPointCoverRestorationAbsorptionData
      parentLoss firstLoss 0
  secondRestoreAbsorption :
    Proposition63RobustPointCoverRestorationAbsorptionData
      schedule.fourth.normalizationLoss secondLoss 61
  multiplicityAbsorption : Proposition63FullGrainLogAbsorptionData
    secondLoss middleLoss
  balancingBoundaryAbsorption :
    Proposition63FourCallBalancingBoundaryAbsorptionData middleLoss
  balancingAbsorption : Proposition63FullGrainBalancingAbsorptionData
    middleLoss finalLoss
  traceAbsorption : Proposition63PureCriticalTailTraceAbsorptionSchedule
    critical.structuralLoss schedule.fourth.sourceLoss finalLoss
  alignedAbsorption : Proposition63AlignedIntervalAbsorptionData discreteLoss
  robustExponent_eq : robustExponent = 1 - discreteLoss
  paperAngularExponent_eq : paperAngularExponent =
    proposition63FourCallPaperAngularExponent outputLoss discreteLoss
  intervalTargetExponent_eq : intervalTargetExponent = 1 - discreteLoss
  epsilon₁_eq : epsilon₁ = paperAngularExponent / 16
  epsilon₃_eq : epsilon₃ = 1 - 2 * epsilon₁
  robustExponent_pos : 0 < robustExponent
  robustExponent_le_one : robustExponent ≤ 1
  paperAngularExponent_pos : 0 < paperAngularExponent
  paperAngularExponent_le_one : paperAngularExponent ≤ 1
  paperAngularExponent_lt_sigma : paperAngularExponent < sigma
  intervalTargetExponent_pos : 0 < intervalTargetExponent
  intervalTargetExponent_le_one : intervalTargetExponent ≤ 1
  secondOutputLoss_lt_paperAngular :
    schedule.secondOutputLoss < paperAngularExponent
  paper_epsilon_sum_lt_one : epsilon₁ + paperAngularExponent < 1
  epsilon₁_pos : 0 < epsilon₁
  epsilon₃_pos : 0 < epsilon₃
  robustExponent_le_epsilon₃ : robustExponent ≤ epsilon₃
  epsilon_sum_lt_one : epsilon₁ + epsilon₃ < 1
  outerExtremalLoss_eq :
    outerExtremalLoss = schedule.third.sourceLoss / 16
  parentLoss_eq : parentLoss = schedule.fourth.sourceLoss / 16
  firstLoss_eq : firstLoss = schedule.fourth.sourceLoss / 12
  ancestorRestoredLoss_eq :
    ancestorRestoredLoss = schedule.fourth.sourceLoss / 10
  nextWeightLoss_eq : nextWeightLoss = schedule.fourth.sourceLoss / 4
  rhoWeightLoss_eq : rhoWeightLoss = schedule.second.sourceLoss / 3
  paperCandidateLoss_eq : paperCandidateLoss = 3 * outputLoss / 4
  paperCoarseBurden_lt_candidate :
    schedule.fourth.normalizationLoss +
        3 * fourthKernel.internalLoss / 2 +
        7 * epsilon₁ + paperAngularExponent <
      paperCandidateLoss - finalLoss - floorLoss
  firstLoss_le_sourceWitnessCandidate :
    firstLoss ≤ stagedCandidateLosses.sourceWitnessCandidateLoss
  nextReentryGap :
    paperCandidateLoss + nextWeightLoss <
      stagedCandidateLosses.nestedCandidateLoss
  sourceWitnessLoss_le_output : schedule.second.sourceLoss ≤ outputLoss
  sourceWitnessCurrentLoss_le_candidate :
    schedule.second.sourceLoss ≤ stagedCandidateLosses.sourceWitnessCandidateLoss
  rhoReentryGap :
    stagedCandidateLosses.nestedCandidateLoss + rhoWeightLoss <
      stagedCandidateLosses.sourceWitnessCandidateLoss
  secondOutputLoss_le_discrete : schedule.secondOutputLoss ≤ discreteLoss
  thirdOutputLoss_le_discrete : schedule.thirdOutputLoss ≤ discreteLoss
  secondLoss_eq :
    secondLoss =
      (schedule.fourth.normalizationLoss + critical.structuralLoss) / 2
  middleLoss_eq : middleLoss = (secondLoss + critical.structuralLoss) / 2
  finalLoss_eq : finalLoss =
    (middleLoss + (critical.structuralLoss - schedule.fourth.sourceLoss)) / 2
  middleLoss_lt_finalLoss : middleLoss < finalLoss
  traceGap : schedule.fourth.sourceLoss + finalLoss < critical.structuralLoss
  finalLoss_le_structural : finalLoss ≤ critical.structuralLoss
  paperCandidateGap : finalLoss + floorLoss < outputLoss / 2
  criticalStructural_le_paperSigma : critical.structuralLoss ≤
    paperAngularExponent * sigma / 100
  sigma_lt_one : sigma < 1
  fourthNormalization_lt_internalLoss :
    schedule.fourth.normalizationLoss < fourthKernel.internalLoss

noncomputable def Proposition63FourCallInnerLossSeed.nestedCandidateLoss
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss) : ℝ :=
  seed.stagedCandidateLosses.nestedCandidateLoss

noncomputable def Proposition63FourCallInnerLossSeed.sourceWitnessCandidateLoss
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss) : ℝ :=
  seed.stagedCandidateLosses.sourceWitnessCandidateLoss

noncomputable def Proposition63FourCallInnerLossSeed.goodCellCandidateLoss
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss) : ℝ :=
  seed.stagedCandidateLosses.goodCellCandidateLoss

theorem Proposition63FourCallInnerLossSeed.nestedCandidateLoss_eq
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss) :
    seed.nestedCandidateLoss = 13 * outputLoss / 16 :=
  seed.stagedCandidateLosses.nestedCandidateLoss_eq

theorem Proposition63FourCallInnerLossSeed.sourceWitnessCandidateLoss_eq
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss) :
    seed.sourceWitnessCandidateLoss = 7 * outputLoss / 8 :=
  seed.stagedCandidateLosses.sourceWitnessCandidateLoss_eq

theorem Proposition63FourCallInnerLossSeed.goodCellCandidateLoss_eq
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss) :
    seed.goodCellCandidateLoss = 15 * outputLoss / 16 :=
  seed.stagedCandidateLosses.goodCellCandidateLoss_eq

theorem Proposition63FourCallInnerLossSeed.terminalCandidateGap
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss) :
    seed.sourceWitnessCandidateLoss < seed.goodCellCandidateLoss :=
  seed.stagedCandidateLosses.terminalCandidateGap

theorem Proposition63FourCallInnerLossSeed.finalCandidateGap
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss) :
    seed.goodCellCandidateLoss < outputLoss :=
  seed.stagedCandidateLosses.finalCandidateGap

/-- Compatibility name for the historical C-stage candidate. -/
noncomputable def Proposition63FourCallInnerLossSeed.initialCandidateLoss
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss) : ℝ :=
  seed.sourceWitnessCandidateLoss

theorem Proposition63FourCallInnerLossSeed.initialCandidateLoss_eq
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss) :
    seed.initialCandidateLoss = seed.sourceWitnessCandidateLoss :=
  rfl

theorem Proposition63FourCallInnerLossSeed.firstLoss_le_initialCandidate
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss) :
    seed.firstLoss ≤ seed.initialCandidateLoss :=
  seed.firstLoss_le_sourceWitnessCandidate

/-- Explicit family-free hierarchy required by grid and cross absorption. -/
structure Proposition63FourCallInnerLossHierarchy
    (sigma discreteLoss outputLoss : ℝ)
    {tailBudget sigmaBudget : ℝ}
    (slack : Proposition63RichFourCallBudgetedBoundarySlackScheduleData
      sigma outputLoss discreteLoss tailBudget sigmaBudget) : Prop where
  secondOutput_le_discrete : slack.base.secondOutputLoss ≤ discreteLoss
  thirdOutput_le_discrete : slack.base.thirdOutputLoss ≤ discreteLoss
  thirdNormalization_lt_half :
    slack.base.third.normalizationLoss < discreteLoss / 2
  fourthNormalization_lt_half :
    slack.base.fourth.normalizationLoss < discreteLoss / 2
  firstCrossGap : 0 < (1 - discreteLoss) * sigma -
    slack.base.secondOutputLoss -
      2 * slack.base.third.normalizationLoss -
        slack.base.third.sourceLoss / 4
  secondCrossGap : 0 < (1 - discreteLoss) * sigma -
    slack.base.thirdOutputLoss -
      2 * slack.base.fourth.normalizationLoss -
        slack.base.fourth.sourceLoss / 4

/-- The quantitative hierarchy is a consequence of the actual budgeted
four-call construction; it is independent of the public output loss. -/
theorem proposition63_four_call_inner_loss_hierarchy
    {sigma discreteLoss outputLoss tailBudget sigmaBudget : ℝ}
    (slack : Proposition63RichFourCallBudgetedBoundarySlackScheduleData
      sigma outputLoss discreteLoss tailBudget sigmaBudget)
    (hsigma : 0 < sigma)
    (hdiscreteHalf : discreteLoss < 1 / 2)
    (hdiscreteSigma : discreteLoss < sigma / 10) :
    Proposition63FourCallInnerLossHierarchy
      sigma discreteLoss outputLoss slack := by
  let schedule := slack.base
  have positiveMain : sigma / 2 < (1 - discreteLoss) * sigma := by
    have := mul_lt_mul_of_pos_right hdiscreteHalf hsigma
    linarith
  have thirdSourceDiscrete : schedule.third.sourceLoss < discreteLoss / 4 := by
    nlinarith [schedule.third.sourceLoss_le_half,
      slack.third_normalization_lt_discrete_half]
  have fourthSourceDiscrete : schedule.fourth.sourceLoss < discreteLoss / 4 := by
    nlinarith [schedule.fourth.sourceLoss_le_half,
      slack.fourth_normalization_lt_discrete_half]
  refine {
    secondOutput_le_discrete := slack.secondOutputLoss_le_discrete
    thirdOutput_le_discrete := slack.thirdOutputLoss_le_discrete
    thirdNormalization_lt_half := slack.third_normalization_lt_discrete_half
    fourthNormalization_lt_half := slack.fourth_normalization_lt_discrete_half
    firstCrossGap := by
      nlinarith [slack.secondOutputLoss_le_discrete,
        slack.third_normalization_lt_discrete_half]
    secondCrossGap := by
      nlinarith [slack.thirdOutputLoss_le_discrete,
        slack.fourth_normalization_lt_discrete_half]
  }

/-- The two cross-call certificates needed when call two remains the robust
outer for both targets.  Their exponent is the paper-small angular exponent,
not the interval-window exponent used to choose the first target scale. -/
structure Proposition63FourCallPaperCrossAbsorptionData
    (sigma discreteLoss paperAngularExponent outputLoss : ℝ)
    {tailBudget sigmaBudget : ℝ}
    (slack : Proposition63RichFourCallBudgetedBoundarySlackScheduleData
      sigma outputLoss discreteLoss tailBudget sigmaBudget) where
  first : Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
    paperAngularExponent slack.base.secondOutputLoss
    slack.base.third.normalizationLoss (slack.base.third.sourceLoss / 4) 4
    (proposition63CanonicalNearbyLevelCount
      slack.base.second.normalizationLoss)
  secondOutput_lt_angular :
    slack.base.secondOutputLoss < paperAngularExponent
  second : Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
    paperAngularExponent slack.base.secondOutputLoss
    slack.base.fourth.normalizationLoss (slack.base.fourth.sourceLoss / 4) 4
    (proposition63CanonicalNearbyLevelCount
      slack.base.second.normalizationLoss)

theorem proposition63_four_call_paper_cross_absorptions
    {sigma discreteLoss paperAngularExponent outputLoss tailBudget
      sigmaBudget : ℝ}
    (slack : Proposition63RichFourCallBudgetedBoundarySlackScheduleData
      sigma outputLoss discreteLoss tailBudget sigmaBudget)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hpaperAngular : 0 < paperAngularExponent)
    (hpaperAngularOne : paperAngularExponent ≤ 1)
    (hfourthNorm : slack.base.fourth.normalizationLoss <
      paperAngularExponent * sigma / 100) :
    Nonempty (Proposition63FourCallPaperCrossAbsorptionData
      sigma discreteLoss paperAngularExponent outputLoss slack) := by
  let schedule := slack.base
  have fourthNormLtProduct :
      schedule.fourth.normalizationLoss <
        paperAngularExponent * sigma / 100 := hfourthNorm
  have thirdOutputLtProduct :
      schedule.thirdOutputLoss < paperAngularExponent * sigma / 3200 := by
    rw [schedule.thirdOutputLoss_eq]
    nlinarith [schedule.fourth.sourceLoss_le_half]
  have thirdNormLtProduct :
      schedule.third.normalizationLoss <
        paperAngularExponent * sigma / 3200 :=
    schedule.third.normalizationLoss_lt_output.trans thirdOutputLtProduct
  have secondOutputLtProduct :
      schedule.secondOutputLoss <
        paperAngularExponent * sigma / 102400 := by
    rw [schedule.secondOutputLoss_eq]
    nlinarith [schedule.third.sourceLoss_le_half, thirdNormLtProduct]
  have firstGap : 0 < paperAngularExponent * sigma -
      schedule.secondOutputLoss - 2 * schedule.third.normalizationLoss -
        schedule.third.sourceLoss / 4 := by
    nlinarith [hpaperAngular, hsigma, secondOutputLtProduct,
      thirdNormLtProduct, schedule.third.sourceLoss_le_half]
  have secondGap : 0 < paperAngularExponent * sigma -
      schedule.secondOutputLoss - 2 * schedule.fourth.normalizationLoss -
        schedule.fourth.sourceLoss / 4 := by
    nlinarith [hpaperAngular, hsigma, secondOutputLtProduct,
      fourthNormLtProduct, schedule.fourth.sourceLoss_le_half]
  rcases proposition63_scaled_two_rich_terminal_scalar_absorption sigma
      paperAngularExponent schedule.secondOutputLoss
      schedule.third.normalizationLoss (schedule.third.sourceLoss / 4) 4
      (proposition63CanonicalNearbyLevelCount
        schedule.second.normalizationLoss)
      hpaperAngular.le hpaperAngularOne firstGap with ⟨first⟩
  rcases proposition63_scaled_two_rich_terminal_scalar_absorption sigma
      paperAngularExponent schedule.secondOutputLoss
      schedule.fourth.normalizationLoss (schedule.fourth.sourceLoss / 4) 4
      (proposition63CanonicalNearbyLevelCount
        schedule.second.normalizationLoss)
      hpaperAngular.le hpaperAngularOne secondGap with ⟨second⟩
  exact ⟨{
    first := first
    second := second
    secondOutput_lt_angular := by
      nlinarith [secondOutputLtProduct, hpaperAngular, hsigmaOne]
  }⟩

private theorem paper_candidate_arithmetic_gap_of_quarters
    {sigma angular outputLoss finalLoss floorLoss normalizationLoss
      internalLoss : ℝ}
    (hsigma : sigma < 1) (hangular : 0 < angular)
    (hangularOutput : angular ≤ outputLoss / 32)
    (hnormalization : normalizationLoss < angular * sigma / 100)
    (hinternal : internalLoss < angular * sigma / 100)
    (hfinal : finalLoss + floorLoss < outputLoss / 2) :
    normalizationLoss + 3 * internalLoss / 2 +
        7 * (angular / 16) + angular <
      outputLoss - finalLoss - floorLoss := by
  have hproduct : angular * sigma < angular :=
    mul_lt_of_lt_one_right hangular hsigma
  have hsmall : normalizationLoss + 3 * internalLoss / 2 +
      7 * (angular / 16) + angular < outputLoss / 4 := by
    nlinarith
  linarith

private theorem paper_coarse_burden_lt_output_quarter
    {sigma angular outputLoss normalizationLoss internalLoss : ℝ}
    (hsigma : sigma < 1) (hangular : 0 < angular)
    (hangularOutput : angular ≤ outputLoss / 32)
    (hnormalization : normalizationLoss < angular * sigma / 100)
    (hinternal : internalLoss < angular * sigma / 100) :
    normalizationLoss + 3 * internalLoss / 2 +
        7 * (angular / 16) + angular < outputLoss / 4 := by
  have hproduct : angular * sigma < angular :=
    mul_lt_of_lt_one_right hangular hsigma
  nlinarith

private theorem staged_next_reentry_gap
    {outputLoss sourceLoss normalizationLoss structuralLoss : ℝ}
    (houtput : 0 < outputLoss)
    (hsource : sourceLoss ≤ normalizationLoss / 2)
    (hnormalization : normalizationLoss < structuralLoss)
    (hstructural : structuralLoss ≤ outputLoss / 8) :
    3 * outputLoss / 4 + sourceLoss / 4 < 13 * outputLoss / 16 := by
  linarith

private theorem staged_rho_reentry_gap
    {outputLoss secondSource thirdSource fourthSource normalizationLoss
      structuralLoss : ℝ}
    (houtput : 0 < outputLoss)
    (hsecond : secondSource < thirdSource / 32)
    (hthird : thirdSource < fourthSource / 32)
    (hfourth : fourthSource ≤ normalizationLoss / 2)
    (hnormalization : normalizationLoss < structuralLoss)
    (hstructural : structuralLoss ≤ outputLoss / 8) :
    13 * outputLoss / 16 + secondSource / 3 < 7 * outputLoss / 8 := by
  linarith

private theorem staged_source_witness_loss_le_output
    {outputLoss secondSource thirdSource fourthSource normalizationLoss
      structuralLoss : ℝ}
    (houtput : 0 < outputLoss)
    (hsecond : secondSource < thirdSource / 32)
    (hthird : thirdSource < fourthSource / 32)
    (hfourth : fourthSource ≤ normalizationLoss / 2)
    (hnormalization : normalizationLoss < structuralLoss)
    (hstructural : structuralLoss ≤ outputLoss / 8) :
    secondSource ≤ outputLoss := by
  linarith

private theorem staged_first_loss_le_initial_candidate
    {outputLoss sourceLoss normalizationLoss structuralLoss : ℝ}
    (houtput : 0 < outputLoss)
    (hsource : sourceLoss ≤ normalizationLoss / 2)
    (hnormalization : normalizationLoss < structuralLoss)
    (hstructural : structuralLoss ≤ outputLoss / 8) :
    sourceLoss / 12 ≤ 7 * outputLoss / 8 := by
  linarith

private theorem staged_final_current_weight_gap
    {outputLoss firstSource secondSource : ℝ}
    (houtput : 0 < outputLoss)
    (hfirst : firstSource < secondSource / 32)
    (hsecond : secondSource ≤ outputLoss) :
    15 * outputLoss / 16 + 5 * firstSource / 8 < outputLoss := by
  linarith

private theorem staged_nested_candidate_lift_absorption
    (outputLoss nextWeightLoss : ℝ) (levelCount : ℕ)
    (hgap : 3 * outputLoss / 4 + nextWeightLoss <
      13 * outputLoss / 16) :
    Nonempty (Proposition63ReentryDensityLiftAbsorptionData
      nextWeightLoss (3 * outputLoss / 4) (13 * outputLoss / 16)
      levelCount) :=
  proposition63_reentry_density_lift_absorption
    nextWeightLoss (3 * outputLoss / 4) (13 * outputLoss / 16)
    levelCount (by linarith)

private theorem staged_source_witness_candidate_lift_absorption
    (outputLoss rhoWeightLoss : ℝ) (levelCount : ℕ)
    (hgap : 13 * outputLoss / 16 + rhoWeightLoss <
      7 * outputLoss / 8) :
    Nonempty (Proposition63ReentryDensityLiftAbsorptionData
      rhoWeightLoss (13 * outputLoss / 16) (7 * outputLoss / 8)
      levelCount) :=
  proposition63_reentry_density_lift_absorption
    rhoWeightLoss (13 * outputLoss / 16) (7 * outputLoss / 8)
    levelCount (by linarith)

private structure Proposition63StagedCandidateLiftSelection
    (outputLoss nextWeightLoss rhoWeightLoss : ℝ)
    (nextLevelCount rhoLevelCount : ℕ) where
  losses : Proposition63StagedCandidateLossData outputLoss
  nextGap :
    3 * outputLoss / 4 + nextWeightLoss < losses.nestedCandidateLoss
  rhoGap :
    losses.nestedCandidateLoss + rhoWeightLoss <
      losses.sourceWitnessCandidateLoss
  nestedAbsorption : Proposition63ReentryDensityLiftAbsorptionData
    nextWeightLoss (3 * outputLoss / 4) losses.nestedCandidateLoss
      nextLevelCount
  sourceWitnessAbsorption : Proposition63ReentryDensityLiftAbsorptionData
    rhoWeightLoss losses.nestedCandidateLoss
      losses.sourceWitnessCandidateLoss rhoLevelCount

private theorem proposition63_staged_candidate_lift_selection
    (outputLoss nextWeightLoss rhoWeightLoss : ℝ)
    (nextLevelCount rhoLevelCount : ℕ)
    (houtput : 0 < outputLoss)
    (hnext : 3 * outputLoss / 4 + nextWeightLoss <
      13 * outputLoss / 16)
    (hrho : 13 * outputLoss / 16 + rhoWeightLoss <
      7 * outputLoss / 8) :
    Nonempty (Proposition63StagedCandidateLiftSelection outputLoss
      nextWeightLoss rhoWeightLoss nextLevelCount rhoLevelCount) := by
  let losses : Proposition63StagedCandidateLossData outputLoss := {
    nestedCandidateLoss := 13 * outputLoss / 16
    sourceWitnessCandidateLoss := 7 * outputLoss / 8
    goodCellCandidateLoss := 15 * outputLoss / 16
    nestedCandidateLoss_eq := rfl
    sourceWitnessCandidateLoss_eq := rfl
    goodCellCandidateLoss_eq := rfl
    terminalCandidateGap := by linarith
    finalCandidateGap := by linarith
  }
  rcases staged_nested_candidate_lift_absorption outputLoss nextWeightLoss
      nextLevelCount hnext with ⟨nestedAbsorption⟩
  rcases staged_source_witness_candidate_lift_absorption outputLoss
      rhoWeightLoss rhoLevelCount hrho with ⟨sourceWitnessAbsorption⟩
  exact ⟨{
    losses := losses
    nextGap := by simpa only [losses]
    rhoGap := by simpa only [losses]
    nestedAbsorption := by simpa only [losses] using nestedAbsorption
    sourceWitnessAbsorption := by
      simpa only [losses] using sourceWitnessAbsorption
  }⟩

/-- The small paper exponents, critical budget, and four-call schedules are
selected together before any runtime scale or tube family is exposed. -/
structure Proposition63FourCallPaperBudgetSelection
    (sigma outputLoss floorLoss discreteLoss : ℝ) where
  selectedFloorLoss : ℝ
  selectedFloorLoss_pos : 0 < selectedFloorLoss
  selectedFloorLoss_le_output_eighth :
    selectedFloorLoss ≤ outputLoss / 8
  paperAngularExponent : ℝ
  paperAngularExponent_eq : paperAngularExponent =
    proposition63FourCallPaperAngularExponent outputLoss discreteLoss
  paperAngularExponent_pos : 0 < paperAngularExponent
  paperAngularExponent_le_discrete_quarter :
    paperAngularExponent ≤ discreteLoss / 4
  paperAngularExponent_le_output_thirty_two :
    paperAngularExponent ≤ outputLoss / 32
  structuralBudget : ℝ
  structuralBudget_pos : 0 < structuralBudget
  structuralBudget_le_sigma_two_hundred : structuralBudget ≤ sigma / 200
  critical : PureWZ2CriticalFloorSelectionData
    sigma selectedFloorLoss structuralBudget
  criticalStructural_le_output_eighth :
    critical.structuralLoss ≤ outputLoss / 8
  criticalStructural_le_paperSigma :
    critical.structuralLoss ≤ paperAngularExponent * sigma / 100
  scheduleSlack : Proposition63RichFourCallBudgetedBoundarySlackScheduleData
    sigma outputLoss discreteLoss critical.structuralLoss
      (discreteLoss * sigma / 100)

theorem proposition63_four_call_paper_budget_selection
    (sigma : ℝ) (criticalPackage : PureWZ2CriticalPackage sigma)
    (outputLoss floorLoss discreteLoss : ℝ)
    (houtputLoss : 0 < outputLoss) (houtputOne : outputLoss ≤ 1)
    (hfloorLoss : 0 < floorLoss) (hdiscreteLoss : 0 < discreteLoss) :
    Nonempty (Proposition63FourCallPaperBudgetSelection
      sigma outputLoss floorLoss discreteLoss) := by
  let selectedFloorLoss : ℝ := min floorLoss (outputLoss / 8)
  have selectedFloorLossPos : 0 < selectedFloorLoss := by
    dsimp only [selectedFloorLoss]
    exact lt_min hfloorLoss (by linarith)
  let paperAngularExponent : ℝ :=
    proposition63FourCallPaperAngularExponent outputLoss discreteLoss
  have paperAngularPos : 0 < paperAngularExponent := by
    dsimp only [paperAngularExponent,
      proposition63FourCallPaperAngularExponent]
    exact lt_min (by linarith) (by linarith)
  have paperAngularDiscrete : paperAngularExponent ≤ discreteLoss / 4 := by
    dsimp only [paperAngularExponent,
      proposition63FourCallPaperAngularExponent]
    exact min_le_left _ _
  have paperAngularOutput : paperAngularExponent ≤ outputLoss / 32 := by
    dsimp only [paperAngularExponent,
      proposition63FourCallPaperAngularExponent]
    exact min_le_right _ _
  let paperSigmaBudget : ℝ := paperAngularExponent * sigma / 100
  have paperSigmaBudgetPos : 0 < paperSigmaBudget :=
    div_pos (mul_pos paperAngularPos criticalPackage.sigma_pos) (by norm_num)
  let structuralBudget : ℝ :=
    min (outputLoss / 8) <|
      min paperSigmaBudget (min (sigma / 200) (discreteLoss / 2))
  have structuralBudgetPos : 0 < structuralBudget := by
    dsimp only [structuralBudget]
    exact lt_min (by linarith) <| lt_min paperSigmaBudgetPos <|
      lt_min (by linarith [criticalPackage.sigma_pos]) (by linarith)
  rcases criticalPackage.select_pure_floor selectedFloorLossPos
      structuralBudgetPos with ⟨critical⟩
  have criticalOutput : critical.structuralLoss ≤ outputLoss / 8 :=
    critical.structuralLoss_le.trans (min_le_left _ _)
  have criticalPaper : critical.structuralLoss ≤
      paperAngularExponent * sigma / 100 := by
    apply critical.structuralLoss_le.trans
    exact (min_le_right _ _).trans (min_le_left _ _)
  let sigmaBudget : ℝ := discreteLoss * sigma / 100
  have sigmaBudgetPos : 0 < sigmaBudget :=
    div_pos (mul_pos hdiscreteLoss criticalPackage.sigma_pos) (by norm_num)
  rcases proposition63_rich_four_call_budgeted_boundary_slack_schedule
      sigma criticalPackage outputLoss discreteLoss critical.structuralLoss
      sigmaBudget houtputLoss houtputOne hdiscreteLoss
      critical.structuralLoss_pos sigmaBudgetPos with ⟨scheduleSlack⟩
  exact ⟨{
    selectedFloorLoss := selectedFloorLoss
    selectedFloorLoss_pos := selectedFloorLossPos
    selectedFloorLoss_le_output_eighth := min_le_right _ _
    paperAngularExponent := paperAngularExponent
    paperAngularExponent_eq := rfl
    paperAngularExponent_pos := paperAngularPos
    paperAngularExponent_le_discrete_quarter := paperAngularDiscrete
    paperAngularExponent_le_output_thirty_two := paperAngularOutput
    structuralBudget := structuralBudget
    structuralBudget_pos := structuralBudgetPos
    structuralBudget_le_sigma_two_hundred := by
      exact (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
    critical := critical
    criticalStructural_le_output_eighth := criticalOutput
    criticalStructural_le_paperSigma := criticalPaper
    scheduleSlack := by simpa only [sigmaBudget] using scheduleSlack
  }⟩

theorem Proposition63FourCallInnerLossSeed.paperCandidateArithmeticGap
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss) :
    seed.schedule.fourth.normalizationLoss +
        3 * seed.fourthKernel.internalLoss / 2 +
        7 * seed.epsilon₁ + seed.paperAngularExponent <
      outputLoss - seed.finalLoss - seed.floorLoss := by
  have hnormalization : seed.schedule.fourth.normalizationLoss <
      seed.paperAngularExponent * sigma / 100 :=
    seed.fourthNormalization_lt_internalLoss.trans
      (seed.fourthKernel.internalLoss_lt_tail.trans_le
        seed.criticalStructural_le_paperSigma)
  have hinternal : seed.fourthKernel.internalLoss <
      seed.paperAngularExponent * sigma / 100 :=
    seed.fourthKernel.internalLoss_lt_tail.trans_le
      seed.criticalStructural_le_paperSigma
  have hangularPos := seed.paperAngularExponent_pos
  have hangularOutput : seed.paperAngularExponent ≤ outputLoss / 32 := by
    rw [seed.paperAngularExponent_eq,
      proposition63FourCallPaperAngularExponent]
    exact min_le_right _ _
  rw [seed.epsilon₁_eq]
  exact paper_candidate_arithmetic_gap_of_quarters
    seed.sigma_lt_one hangularPos
    hangularOutput hnormalization hinternal seed.paperCandidateGap

/-- Construct all family-free receipts from an explicit pre-runtime loss
hierarchy and the boundary-slack four-call schedule. -/
theorem proposition63_four_call_inner_loss_seed
    (sigma : ℝ) (criticalPackage : PureWZ2CriticalPackage sigma)
    (outputLoss floorLoss discreteLoss : ℝ)
    (houtputLoss : 0 < outputLoss)
    (houtputOne : outputLoss ≤ 1)
    (hfloorLoss : 0 < floorLoss)
    (hdiscreteLoss : 0 < discreteLoss)
    (hdiscreteHalf : discreteLoss < 1 / 2)
    (hdiscreteSigma : discreteLoss < sigma / 10) :
    Nonempty (Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss) := by
  rcases proposition63_four_call_paper_budget_selection sigma criticalPackage
      outputLoss floorLoss discreteLoss houtputLoss houtputOne hfloorLoss
      hdiscreteLoss with ⟨budget⟩
  let chosenFloorLoss := budget.selectedFloorLoss
  have chosenFloorLossPos := budget.selectedFloorLoss_pos
  have chosenFloorLossLeOutput :=
    budget.selectedFloorLoss_le_output_eighth
  let paperAngularExponent := budget.paperAngularExponent
  have paperAngularExponentPos := budget.paperAngularExponent_pos
  have paperAngularLeDiscrete :=
    budget.paperAngularExponent_le_discrete_quarter
  have paperAngularLeOutput :=
    budget.paperAngularExponent_le_output_thirty_two
  let structuralBudget := budget.structuralBudget
  have structuralBudgetPos := budget.structuralBudget_pos
  have structuralBudgetLeOutput := budget.criticalStructural_le_output_eighth
  have structuralBudgetLePaperSigma :=
    budget.criticalStructural_le_paperSigma
  let critical := budget.critical
  let scheduleSlack := budget.scheduleSlack
  let schedule := scheduleSlack.base
  have hierarchy := proposition63_four_call_inner_loss_hierarchy scheduleSlack
    criticalPackage.sigma_pos hdiscreteHalf hdiscreteSigma
  let robustExponent : ℝ := 1 - discreteLoss
  let intervalTargetExponent : ℝ := 1 - discreteLoss
  let epsilon₁ : ℝ := paperAngularExponent / 16
  let epsilon₃ : ℝ := 1 - 2 * epsilon₁
  let rhoDensityLoss : ℝ := schedule.second.sourceLoss / 8
  let rhoWeightLoss : ℝ := schedule.second.sourceLoss / 3
  let firstStageDensityLoss : ℝ := schedule.third.sourceLoss / 8
  let outerExtremalLoss : ℝ := schedule.third.sourceLoss / 16
  let firstStageWeightLoss : ℝ := schedule.third.sourceLoss / 4
  let secondReentryDensityLoss : ℝ := schedule.fourth.sourceLoss / 8
  let parentLoss : ℝ := schedule.fourth.sourceLoss / 16
  let firstLoss : ℝ := schedule.fourth.sourceLoss / 12
  let ancestorRestoredLoss : ℝ := schedule.fourth.sourceLoss / 10
  let nextWeightLoss : ℝ := schedule.fourth.sourceLoss / 4
  let secondLoss : ℝ :=
    (schedule.fourth.normalizationLoss + critical.structuralLoss) / 2
  let middleLoss : ℝ := (secondLoss + critical.structuralLoss) / 2
  let finalLoss : ℝ :=
    (middleLoss +
      (critical.structuralLoss - schedule.fourth.sourceLoss)) / 2
  let paperCandidateLoss : ℝ := 3 * outputLoss / 4
  rcases proposition63_four_call_paper_cross_absorptions scheduleSlack
      criticalPackage.sigma_pos criticalPackage.sigma_lt_one
      paperAngularExponentPos
      (paperAngularLeOutput.trans (by linarith))
      (scheduleSlack.fourth_normalization_lt_tail.trans_le <|
        structuralBudgetLePaperSigma) with
    ⟨paperCrossAbsorptions⟩
  have secondSourcePos := schedule.second.sourceLoss_pos
  have thirdSourcePos := schedule.third.sourceLoss_pos
  have fourthSourcePos := schedule.fourth.sourceLoss_pos
  have secondNormPos := schedule.second.normalizationLoss_pos
  have thirdNormPos := schedule.third.normalizationLoss_pos
  have fourthNormPos := schedule.fourth.normalizationLoss_pos
  have paperAngularProductLt :
      paperAngularExponent * sigma < paperAngularExponent :=
    mul_lt_of_lt_one_right paperAngularExponentPos
      criticalPackage.sigma_lt_one
  have fourthNormLtPaperHundred :
      schedule.fourth.normalizationLoss < paperAngularExponent / 100 := by
    have hnorm := scheduleSlack.fourth_normalization_lt_tail.trans_le <|
      structuralBudgetLePaperSigma
    linarith only [hnorm, paperAngularProductLt]
  have thirdNormLtPaper :
      schedule.third.normalizationLoss < paperAngularExponent / 3200 := by
    calc
      schedule.third.normalizationLoss < schedule.thirdOutputLoss :=
        schedule.third.normalizationLoss_lt_output
      _ = schedule.fourth.sourceLoss / 16 :=
        schedule.thirdOutputLoss_eq
      _ ≤ schedule.fourth.normalizationLoss / 32 := by
        linarith [schedule.fourth.sourceLoss_le_half]
      _ < paperAngularExponent / 3200 := by
        linarith
  have secondSourceLtThird :
      schedule.second.sourceLoss < schedule.third.sourceLoss / 32 := by
    calc
      schedule.second.sourceLoss ≤ schedule.second.normalizationLoss / 2 :=
        schedule.second.sourceLoss_le_half
      _ < schedule.secondOutputLoss / 2 := by
        linarith [schedule.second.normalizationLoss_lt_output]
      _ = schedule.third.sourceLoss / 32 := by
        rw [schedule.secondOutputLoss_eq]
        ring
  have thirdSourceLtFourth :
      schedule.third.sourceLoss < schedule.fourth.sourceLoss / 32 := by
    calc
      schedule.third.sourceLoss ≤ schedule.third.normalizationLoss / 2 :=
        schedule.third.sourceLoss_le_half
      _ < schedule.thirdOutputLoss / 2 := by
        linarith [schedule.third.normalizationLoss_lt_output]
      _ = schedule.fourth.sourceLoss / 32 := by
        rw [schedule.thirdOutputLoss_eq]
        ring
  have secondSourceLeOutput : schedule.second.sourceLoss ≤ outputLoss :=
    staged_source_witness_loss_le_output houtputLoss secondSourceLtThird
      thirdSourceLtFourth schedule.fourth.sourceLoss_le_half
      scheduleSlack.fourth_normalization_lt_tail structuralBudgetLeOutput
  have thirdNormLtFourthSixteenth :
      schedule.third.normalizationLoss < schedule.fourth.sourceLoss / 16 := by
    rw [← schedule.thirdOutputLoss_eq]
    exact schedule.third.normalizationLoss_lt_output
  have fourthNormLtStructural :
      schedule.fourth.normalizationLoss < critical.structuralLoss :=
    scheduleSlack.fourth_normalization_lt_tail
  have fourthSourceLeHalf :
      schedule.fourth.sourceLoss ≤
        schedule.fourth.normalizationLoss / 2 :=
    schedule.fourth.sourceLoss_le_half
  have fourthSourceAddNormLtStructural :
      4 * schedule.fourth.sourceLoss +
          schedule.fourth.normalizationLoss < critical.structuralLoss := by
    linarith [scheduleSlack.fourth_tail_boundary_slack]
  rcases proposition63_current_reentry_absorption
      (schedule.second.sourceLoss / 16) (schedule.second.sourceLoss / 4)
      rhoDensityLoss schedule.firstOutputLoss rhoWeightLoss
      schedule.second.sourceLoss
      (proposition63CanonicalNearbyLevelCount
        (schedule.second.sourceLoss / 4))
      (by dsimp [rhoDensityLoss]; linarith)
      (by positivity)
      (by rw [schedule.firstOutputLoss_eq]; dsimp [rhoDensityLoss, rhoWeightLoss];
          linarith)
      (by dsimp [rhoWeightLoss]; linarith)
      (proposition63CanonicalNearbyLevelCount_pos (by positivity))
      secondSourcePos
      (by dsimp [rhoWeightLoss]; linarith) with ⟨rhoAbsorption⟩
  rcases proposition63_current_reentry_absorption
      schedule.second.sourceLoss schedule.second.normalizationLoss
      firstStageDensityLoss outerExtremalLoss firstStageWeightLoss
      schedule.third.sourceLoss
      (proposition63CanonicalNearbyLevelCount
        schedule.second.normalizationLoss)
      (by dsimp [firstStageDensityLoss]; linarith) secondNormPos
      (by dsimp [firstStageDensityLoss, outerExtremalLoss,
          firstStageWeightLoss]; linarith)
      (by dsimp [firstStageWeightLoss]; linarith)
      (proposition63CanonicalNearbyLevelCount_pos secondNormPos)
      thirdSourcePos
      (by dsimp [firstStageWeightLoss];
          linarith [schedule.second.normalizationLoss_lt_output,
            schedule.secondOutputLoss_eq]) with ⟨firstStageAbsorption⟩
  rcases proposition63_current_reentry_absorption
      schedule.third.sourceLoss schedule.third.normalizationLoss
      secondReentryDensityLoss firstLoss nextWeightLoss
      schedule.fourth.sourceLoss
      (proposition63CanonicalNearbyLevelCount
        schedule.third.normalizationLoss)
      (by dsimp [secondReentryDensityLoss]; linarith) thirdNormPos
      (by dsimp [secondReentryDensityLoss, firstLoss, nextWeightLoss];
          linarith)
      (by dsimp [nextWeightLoss]; linarith)
      (proposition63CanonicalNearbyLevelCount_pos thirdNormPos)
      fourthSourcePos
      (by dsimp [nextWeightLoss]; linarith [thirdNormLtFourthSixteenth]) with
    ⟨secondReentryAbsorption⟩
  rcases proposition63_reentry_density_lift_absorption
      firstStageWeightLoss firstLoss ancestorRestoredLoss
      (proposition63CanonicalNearbyLevelCount schedule.second.normalizationLoss)
      (by
        dsimp only [firstStageWeightLoss, firstLoss, ancestorRestoredLoss]
        linarith [thirdSourceLtFourth]) with ⟨ancestorDensityLiftAbsorption⟩
  rcases proposition63_current_reentry_absorption
      schedule.second.sourceLoss schedule.second.normalizationLoss
      firstStageDensityLoss ancestorRestoredLoss nextWeightLoss
      schedule.fourth.sourceLoss
      (proposition63CanonicalNearbyLevelCount schedule.second.normalizationLoss)
      (by
        dsimp only [firstStageDensityLoss]
        calc
          schedule.second.sourceLoss < schedule.third.sourceLoss / 32 :=
            secondSourceLtThird
          _ < schedule.third.sourceLoss / 8 := by
            linarith only [thirdSourcePos])
      secondNormPos
      (by
        dsimp only [firstStageDensityLoss, ancestorRestoredLoss, nextWeightLoss]
        linarith [thirdSourceLtFourth])
      (by dsimp only [nextWeightLoss]; linarith)
      (proposition63CanonicalNearbyLevelCount_pos secondNormPos)
      fourthSourcePos
      (by
        dsimp only [nextWeightLoss]
        linarith [schedule.second.normalizationLoss_lt_output,
          schedule.secondOutputLoss_eq, thirdSourceLtFourth]) with
    ⟨ancestorReentryAbsorption⟩
  have nextReentryGapRaw :
      3 * outputLoss / 4 + nextWeightLoss <
        13 * outputLoss / 16 := by
    simpa only [nextWeightLoss] using staged_next_reentry_gap houtputLoss
      fourthSourceLeHalf fourthNormLtStructural structuralBudgetLeOutput
  have rhoReentryGapRaw :
      13 * outputLoss / 16 + rhoWeightLoss <
        7 * outputLoss / 8 := by
    simpa only [rhoWeightLoss] using staged_rho_reentry_gap houtputLoss
      secondSourceLtThird thirdSourceLtFourth fourthSourceLeHalf
      fourthNormLtStructural structuralBudgetLeOutput
  rcases proposition63_staged_candidate_lift_selection outputLoss
      nextWeightLoss rhoWeightLoss
      (proposition63CanonicalNearbyLevelCount
        schedule.second.normalizationLoss)
      (proposition63CanonicalNearbyLevelCount
        (schedule.second.sourceLoss / 4))
      houtputLoss nextReentryGapRaw rhoReentryGapRaw with
    ⟨stagedSelection⟩
  rcases proposition63_robust_grid_pruning_absorption
      schedule.third.normalizationLoss epsilon₁
      (by
        dsimp only [epsilon₁]
        linarith [thirdNormLtPaper, paperAngularExponentPos]) with
    ⟨firstGridAbsorption⟩
  rcases proposition63_robust_grid_pruning_absorption
      schedule.fourth.normalizationLoss epsilon₁
      (by
        dsimp only [epsilon₁]
        linarith [fourthNormLtPaperHundred, paperAngularExponentPos])
      with ⟨secondGridAbsorption⟩
  rcases proposition63_scaled_two_rich_terminal_scalar_absorption sigma
      robustExponent schedule.secondOutputLoss
      schedule.third.normalizationLoss firstStageWeightLoss 4
      (proposition63CanonicalNearbyLevelCount
        schedule.second.normalizationLoss)
      (by dsimp [robustExponent]; linarith)
      (by dsimp [robustExponent]; linarith)
      (by simpa only [robustExponent, firstStageWeightLoss] using
        hierarchy.firstCrossGap) with ⟨firstCrossAbsorption⟩
  rcases proposition63_scaled_two_rich_terminal_scalar_absorption sigma
      robustExponent schedule.thirdOutputLoss
      schedule.fourth.normalizationLoss nextWeightLoss 4
      (proposition63CanonicalNearbyLevelCount
        schedule.third.normalizationLoss)
      (by dsimp [robustExponent]; linarith)
      (by dsimp [robustExponent]; linarith)
      (by simpa only [robustExponent, nextWeightLoss] using
        hierarchy.secondCrossGap) with ⟨secondCrossAbsorption⟩
  rcases proposition63_robust_boundary_absorption
      schedule.thirdOutputLoss schedule.third.normalizationLoss thirdNormPos
      (by dsimp [schedule]; linarith [scheduleSlack.third_boundary_slack]) with
    ⟨firstBoundaryAbsorption⟩
  rcases proposition63_robust_boundary_absorption outputLoss
      schedule.fourth.normalizationLoss fourthNormPos
      (by dsimp [schedule]; linarith [scheduleSlack.fourth_boundary_slack]) with
    ⟨secondBoundaryAbsorption⟩
  rcases proposition63_robust_boundary_absorption
      scheduleSlack.fourthKernel.internalLoss
      schedule.fourth.normalizationLoss fourthNormPos
      (by
        have hboundary := scheduleSlack.fourthKernel.internal_boundary_slack
        have hnormalization :
            scheduleSlack.base.fourth.normalizationLoss =
              scheduleSlack.fourthKernel.internalSchedule.normalizationLoss := by
          have hpublic := congrArg
            Proposition63RichStickyKernelScheduleData.normalizationLoss
            scheduleSlack.fourthKernel.public_eq
          simpa only [Proposition63RichStickyKernelScheduleData.mono_loss] using
            hpublic
        have hboundary' :
            4 * schedule.fourth.normalizationLoss <
              scheduleSlack.fourthKernel.internalLoss := by
          simpa only [schedule, hnormalization] using hboundary
        linarith) with
    ⟨internalFourthBoundaryAbsorption⟩
  have fourthNormalizationLtInternalLoss :
      schedule.fourth.normalizationLoss <
        scheduleSlack.fourthKernel.internalLoss := by
    have hboundary := scheduleSlack.fourthKernel.internal_boundary_slack
    have hnormalization :
        scheduleSlack.base.fourth.normalizationLoss =
          scheduleSlack.fourthKernel.internalSchedule.normalizationLoss := by
      have hpublic := congrArg
        Proposition63RichStickyKernelScheduleData.normalizationLoss
        scheduleSlack.fourthKernel.public_eq
      simpa only [Proposition63RichStickyKernelScheduleData.mono_loss] using
        hpublic
    have hboundary' : 4 * schedule.fourth.normalizationLoss <
        scheduleSlack.fourthKernel.internalLoss := by
      simpa only [schedule, hnormalization] using hboundary
    linarith [fourthNormPos]
  rcases proposition63_refinement_retention_absorption
      schedule.second.normalizationLoss outerExtremalLoss 61
      (by dsimp [outerExtremalLoss];
          linarith [schedule.second.normalizationLoss_lt_output,
            schedule.secondOutputLoss_eq])
      (by norm_num) with ⟨outerRetentionAbsorption⟩
  rcases proposition63_refinement_retention_absorption
      schedule.third.normalizationLoss parentLoss 61
      (by dsimp [parentLoss]; exact thirdNormLtFourthSixteenth)
      (by norm_num) with ⟨parentRetentionAbsorption⟩
  rcases proposition63_robust_point_cover_restoration_absorption
      parentLoss firstLoss 0
      (by dsimp [parentLoss, firstLoss]; linarith) with
    ⟨firstRestoreAbsorption⟩
  rcases proposition63_robust_point_cover_restoration_absorption
      schedule.fourth.normalizationLoss secondLoss 61
      (by dsimp [secondLoss]; linarith) with ⟨secondRestoreAbsorption⟩
  have secondLossLtStructural : secondLoss < critical.structuralLoss := by
    dsimp [secondLoss]
    linarith
  rcases proposition63_full_grain_log_absorption secondLoss middleLoss
      (by dsimp [middleLoss]; linarith) with
    ⟨multiplicityAbsorption⟩
  have middleLossLtStructural : middleLoss < critical.structuralLoss := by
    dsimp [middleLoss]
    linarith
  have structuralBudgetLeSigma : structuralBudget ≤ sigma / 200 := by
    exact budget.structuralBudget_le_sigma_two_hundred
  have middleLossLtOneEighth : middleLoss < 1 / 8 := by
    have criticalStructuralLtOneEighth :
        critical.structuralLoss < 1 / 8 := by
      calc
        critical.structuralLoss ≤ structuralBudget := critical.structuralLoss_le
        _ ≤ sigma / 200 := structuralBudgetLeSigma
        _ < 1 / 8 := by linarith [criticalPackage.sigma_lt_one]
    exact middleLossLtStructural.trans criticalStructuralLtOneEighth
  rcases proposition63_four_call_balancing_boundary_absorption middleLoss
      (by
        dsimp [middleLoss, secondLoss]
        linarith [fourthNormPos, critical.structuralLoss_pos])
      middleLossLtOneEighth with
    ⟨balancingBoundaryAbsorption⟩
  have middleLossLtFinal : middleLoss < finalLoss := by
    dsimp [finalLoss, middleLoss, secondLoss]
    linarith only [fourthSourceAddNormLtStructural]
  have traceGap :
      schedule.fourth.sourceLoss + finalLoss <
        critical.structuralLoss := by
    dsimp [finalLoss, middleLoss, secondLoss]
    linarith only [fourthSourceAddNormLtStructural]
  have finalLossLeStructural : finalLoss ≤ critical.structuralLoss := by
    linarith only [traceGap, fourthSourcePos]
  have paperCandidateGap : finalLoss + chosenFloorLoss < outputLoss / 2 := by
    have hfinalLe : finalLoss ≤ outputLoss / 8 :=
      finalLossLeStructural.trans structuralBudgetLeOutput
    linarith
  have paperCoarseBurdenLtCandidate :
      schedule.fourth.normalizationLoss +
          3 * scheduleSlack.fourthKernel.internalLoss / 2 +
          7 * epsilon₁ + paperAngularExponent <
        paperCandidateLoss - finalLoss - chosenFloorLoss := by
    have hinternal : scheduleSlack.fourthKernel.internalLoss <
        paperAngularExponent * sigma / 100 :=
      scheduleSlack.fourthKernel.internalLoss_lt_tail.trans_le
        structuralBudgetLePaperSigma
    have hnormalization : schedule.fourth.normalizationLoss <
        paperAngularExponent * sigma / 100 :=
      fourthNormalizationLtInternalLoss.trans hinternal
    have hburden :
        schedule.fourth.normalizationLoss +
            3 * scheduleSlack.fourthKernel.internalLoss / 2 +
            7 * epsilon₁ + paperAngularExponent < outputLoss / 4 := by
      simpa only [epsilon₁] using paper_coarse_burden_lt_output_quarter
        criticalPackage.sigma_lt_one paperAngularExponentPos
        paperAngularLeOutput hnormalization hinternal
    dsimp only [paperCandidateLoss]
    linarith only [hburden, paperCandidateGap]
  rcases proposition63_full_grain_balancing_absorption middleLoss finalLoss
      middleLossLtFinal with ⟨balancingAbsorption⟩
  rcases proposition63_pureCriticalTailTraceAbsorptionSchedule traceGap with
    ⟨traceAbsorption⟩
  rcases proposition63_aligned_interval_absorption hdiscreteLoss with
    ⟨alignedAbsorption⟩
  let result : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss := {
    floorLoss := chosenFloorLoss
    floorLoss_pos := chosenFloorLossPos
    structuralBudget := structuralBudget
    critical := critical
    schedule := schedule
    fourthKernel := scheduleSlack.fourthKernel
    paperAngularExponent := paperAngularExponent
    intervalTargetExponent := intervalTargetExponent
    robustExponent := robustExponent
    epsilon₁ := epsilon₁
    epsilon₃ := epsilon₃
    rhoDensityLoss := rhoDensityLoss
    rhoWeightLoss := rhoWeightLoss
    firstStageDensityLoss := firstStageDensityLoss
    outerExtremalLoss := outerExtremalLoss
    firstStageWeightLoss := firstStageWeightLoss
    secondReentryDensityLoss := secondReentryDensityLoss
    parentLoss := parentLoss
    firstLoss := firstLoss
    ancestorRestoredLoss := ancestorRestoredLoss
    nextWeightLoss := nextWeightLoss
    secondLoss := secondLoss
    middleLoss := middleLoss
    finalLoss := finalLoss
    paperCandidateLoss := paperCandidateLoss
    stagedCandidateLosses := stagedSelection.losses
    rhoAbsorption := rhoAbsorption
    firstStageAbsorption := firstStageAbsorption
    secondReentryAbsorption := secondReentryAbsorption
    ancestorDensityLiftAbsorption := ancestorDensityLiftAbsorption
    ancestorReentryAbsorption := ancestorReentryAbsorption
    nestedCandidateLiftAbsorption := stagedSelection.nestedAbsorption
    sourceWitnessCandidateLiftAbsorption :=
      stagedSelection.sourceWitnessAbsorption
    firstGridAbsorption := firstGridAbsorption
    secondGridAbsorption := secondGridAbsorption
    firstCrossAbsorption := firstCrossAbsorption
    secondCrossAbsorption := secondCrossAbsorption
    paperFirstCrossAbsorption := by
      simpa only [paperAngularExponent, firstStageWeightLoss, schedule] using
        paperCrossAbsorptions.first
    paperSecondCrossAbsorption := by
      simpa only [paperAngularExponent, nextWeightLoss, schedule] using
        paperCrossAbsorptions.second
    firstBoundaryAbsorption := firstBoundaryAbsorption
    secondBoundaryAbsorption := secondBoundaryAbsorption
    internalFourthBoundaryAbsorption := internalFourthBoundaryAbsorption
    outerRetentionAbsorption := outerRetentionAbsorption
    parentRetentionAbsorption := parentRetentionAbsorption
    firstRestoreAbsorption := firstRestoreAbsorption
    secondRestoreAbsorption := secondRestoreAbsorption
    multiplicityAbsorption := multiplicityAbsorption
    balancingBoundaryAbsorption := balancingBoundaryAbsorption
    balancingAbsorption := balancingAbsorption
    traceAbsorption := traceAbsorption
    alignedAbsorption := alignedAbsorption
    robustExponent_eq := rfl
    paperAngularExponent_eq := by
      simpa only [paperAngularExponent] using budget.paperAngularExponent_eq
    intervalTargetExponent_eq := rfl
    epsilon₁_eq := rfl
    epsilon₃_eq := rfl
    robustExponent_pos := by dsimp [robustExponent]; linarith
    robustExponent_le_one := by dsimp [robustExponent]; linarith
    paperAngularExponent_pos := by
      dsimp only [paperAngularExponent]
      linarith
    paperAngularExponent_le_one := by
      dsimp only [paperAngularExponent]
      linarith
    paperAngularExponent_lt_sigma := by
      dsimp only [paperAngularExponent]
      linarith
    intervalTargetExponent_pos := by
      dsimp only [intervalTargetExponent]
      linarith
    intervalTargetExponent_le_one := by
      dsimp only [intervalTargetExponent]
      linarith
    secondOutputLoss_lt_paperAngular := by
      simpa only [paperAngularExponent, schedule] using
        paperCrossAbsorptions.secondOutput_lt_angular
    paper_epsilon_sum_lt_one := by
      dsimp only [epsilon₁, paperAngularExponent]
      linarith only [paperAngularLeOutput, houtputOne]
    epsilon₁_pos := by
      dsimp only [epsilon₁]
      linarith only [paperAngularExponentPos]
    epsilon₃_pos := by
      dsimp only [epsilon₃, epsilon₁]
      have hangularLtQuarter : paperAngularExponent < 1 / 4 :=
        paperAngularLeDiscrete.trans_lt <| by linarith only [hdiscreteHalf]
      linarith only [hangularLtQuarter]
    robustExponent_le_epsilon₃ := by
      dsimp only [robustExponent, epsilon₃, epsilon₁]
      have hangularDiscrete : paperAngularExponent ≤ discreteLoss / 4 :=
        paperAngularLeDiscrete
      linarith only [hangularDiscrete, hdiscreteLoss]
    epsilon_sum_lt_one := by
      dsimp only [epsilon₁, epsilon₃]
      linarith only [paperAngularExponentPos]
    outerExtremalLoss_eq := rfl
    parentLoss_eq := rfl
    firstLoss_eq := rfl
    ancestorRestoredLoss_eq := rfl
    nextWeightLoss_eq := rfl
    rhoWeightLoss_eq := rfl
    paperCandidateLoss_eq := rfl
    paperCoarseBurden_lt_candidate := paperCoarseBurdenLtCandidate
    firstLoss_le_sourceWitnessCandidate := by
      rw [stagedSelection.losses.sourceWitnessCandidateLoss_eq]
      simpa only [firstLoss] using staged_first_loss_le_initial_candidate
        houtputLoss fourthSourceLeHalf fourthNormLtStructural
          structuralBudgetLeOutput
    nextReentryGap := by
      simpa only [paperCandidateLoss] using stagedSelection.nextGap
    sourceWitnessLoss_le_output := by
      exact secondSourceLeOutput
    sourceWitnessCurrentLoss_le_candidate := by
      rw [stagedSelection.losses.sourceWitnessCandidateLoss_eq]
      linarith only [secondSourceLtThird, thirdSourceLtFourth,
        fourthSourceLeHalf, fourthNormLtStructural, structuralBudgetLeOutput,
        houtputLoss]
    rhoReentryGap := stagedSelection.rhoGap
    secondOutputLoss_le_discrete := hierarchy.secondOutput_le_discrete
    thirdOutputLoss_le_discrete := hierarchy.thirdOutput_le_discrete
    secondLoss_eq := rfl
    middleLoss_eq := rfl
    finalLoss_eq := rfl
    middleLoss_lt_finalLoss := middleLossLtFinal
    traceGap := traceGap
    finalLoss_le_structural := finalLossLeStructural
    paperCandidateGap := paperCandidateGap
    criticalStructural_le_paperSigma := structuralBudgetLePaperSigma
    sigma_lt_one := criticalPackage.sigma_lt_one
    fourthNormalization_lt_internalLoss :=
      fourthNormalizationLtInternalLoss
  }
  exact ⟨result⟩

/-- A finite backward selection ending at the prescribed grid-output loss.
Each index owns an actual family-free seed whose output candidate is
definitionally the next entry of `loss`. -/
structure Proposition63FourCallInnerBackwardLossSchedule
    (sigma gridOutputLoss discreteLoss : ℝ) (N : ℕ) where
  loss : ℕ → ℝ
  seed : ∀ index, index < N → Proposition63FourCallInnerLossSeed
    sigma (loss (index + 1)) discreteLoss
  input_eq : ∀ index (hindex : index < N),
    loss index = (seed index hindex).schedule.first.sourceLoss / 4
  loss_lt_next : ∀ index, index < N → loss index < loss (index + 1)
  loss_pos : ∀ index, index ≤ N → 0 < loss index
  loss_le_terminal : ∀ index, index ≤ N → loss index ≤ gridOutputLoss
  final_loss : loss N = gridOutputLoss
  outputCandidateLoss : ℕ → ℝ
  output_candidate_eq : ∀ index, index < N →
    outputCandidateLoss index = loss (index + 1)
  rootBudget : ℝ
  rootBudget_pos : 0 < rootBudget
  rootBudget_le_first : ∀ index (hindex : index < N),
    rootBudget ≤ (seed index hindex).schedule.first.sourceLoss

/-- Select the complete finite loss hierarchy backwards.  Each public output
is the next tail loss, while every step independently selects its ordinary
critical structural loss before choosing the hidden rich kernels. -/
theorem proposition63_four_call_inner_backward_loss_schedule
    (sigma : ℝ) (criticalPackage : PureWZ2CriticalPackage sigma)
    (gridOutputLoss floorLoss discreteLoss : ℝ)
    (hgridOutputLoss : 0 < gridOutputLoss)
    (hgridOutputOne : gridOutputLoss ≤ 1)
    (hfloorLoss : 0 < floorLoss)
    (hdiscreteLoss : 0 < discreteLoss)
    (hdiscreteHalf : discreteLoss < 1 / 2)
    (hdiscreteSigma : discreteLoss < sigma / 10) :
    ∀ N, Nonempty (Proposition63FourCallInnerBackwardLossSchedule
      sigma gridOutputLoss discreteLoss N) := by
  intro N
  induction N with
  | zero =>
      exact ⟨{
        loss := fun _ => gridOutputLoss
        seed := by intro index hindex; omega
        input_eq := by intro index hindex; omega
        loss_lt_next := by intro index hindex; omega
        loss_pos := fun _ _ => hgridOutputLoss
        loss_le_terminal := fun _ _ => le_rfl
        final_loss := rfl
        outputCandidateLoss := fun _ => gridOutputLoss
        output_candidate_eq := by intro index hindex; omega
        rootBudget := gridOutputLoss
        rootBudget_pos := hgridOutputLoss
        rootBudget_le_first := by intro index hindex; omega
      }⟩
  | succ N inductionHypothesis =>
      rcases inductionHypothesis with ⟨tail⟩
      have tailInputPos : 0 < tail.loss 0 := tail.loss_pos 0 (by omega)
      have tailInputOne : tail.loss 0 ≤ 1 :=
        (tail.loss_le_terminal 0 (by omega)).trans hgridOutputOne
      rcases proposition63_four_call_inner_loss_seed sigma criticalPackage
          (tail.loss 0) floorLoss discreteLoss
          tailInputPos tailInputOne hfloorLoss hdiscreteLoss hdiscreteHalf
          hdiscreteSigma with
        ⟨head⟩
      let loss : ℕ → ℝ := fun index =>
        if index = 0 then head.schedule.first.sourceLoss / 4
        else tail.loss (index - 1)
      have loss_zero : loss 0 = head.schedule.first.sourceLoss / 4 := by
        simp [loss]
      have loss_succ : ∀ index, loss (index + 1) = tail.loss index := by
        intro index
        simp [loss]
      have headFirstSourceLtTail :
          head.schedule.first.sourceLoss < tail.loss 0 :=
        (head.schedule.first.sourceLoss_le_half.trans_lt (by
          nlinarith [head.schedule.first.normalizationLoss_pos])).trans
          head.schedule.first.normalizationLoss_lt_output |>.trans
            head.schedule.firstOutputLoss_lt_secondSource |>.trans
              (head.schedule.second.sourceLoss_le_half.trans_lt (by
                nlinarith [head.schedule.second.normalizationLoss_pos])) |>.trans
                head.schedule.second.normalizationLoss_lt_output |>.trans
                  head.schedule.secondOutputLoss_lt_thirdSource |>.trans
                    (head.schedule.third.sourceLoss_le_half.trans_lt (by
                      nlinarith [head.schedule.third.normalizationLoss_pos])) |>.trans
                      head.schedule.third.normalizationLoss_lt_output |>.trans
                        head.schedule.thirdOutputLoss_lt_fourthSource |>.trans
                          (head.schedule.fourth.sourceLoss_le_half.trans_lt (by
                            nlinarith [head.schedule.fourth.normalizationLoss_pos])) |>.trans
                            head.schedule.fourth.normalizationLoss_lt_output
      refine ⟨{
        loss := loss
        seed := ?_
        input_eq := ?_
        loss_lt_next := ?_
        loss_pos := ?_
        loss_le_terminal := ?_
        final_loss := ?_
        outputCandidateLoss := fun index => loss (index + 1)
        output_candidate_eq := fun _ _ => rfl
        rootBudget := min tail.rootBudget head.schedule.first.sourceLoss
        rootBudget_pos := lt_min tail.rootBudget_pos
          head.schedule.first.sourceLoss_pos
        rootBudget_le_first := ?_
      }⟩
      · intro index hindex
        rcases index with _ | index
        · simpa only [loss_succ] using head
        · simpa only [loss_succ] using tail.seed index (by omega)
      · intro index hindex
        rcases index with _ | index
        · exact loss_zero
        · rw [loss_succ]
          exact tail.input_eq index (by omega)
      · intro index hindex
        rcases index with _ | index
        · rw [loss_zero, loss_succ]
          nlinarith [head.schedule.first.sourceLoss_pos, headFirstSourceLtTail]
        · rw [loss_succ, loss_succ]
          exact tail.loss_lt_next index (by omega)
      · intro index hindex
        rcases index with _ | index
        · rw [loss_zero]
          exact div_pos head.schedule.first.sourceLoss_pos (by norm_num)
        · rw [loss_succ]
          exact tail.loss_pos index (by omega)
      · intro index hindex
        rcases index with _ | index
        · rw [loss_zero]
          have firstSourceLeTerminal :
              head.schedule.first.sourceLoss ≤ gridOutputLoss :=
            headFirstSourceLtTail.le.trans
              (tail.loss_le_terminal 0 (by omega))
          exact (div_le_self head.schedule.first.sourceLoss_pos.le
            (by norm_num)).trans firstSourceLeTerminal
        · rw [loss_succ]
          exact tail.loss_le_terminal index (by omega)
      · rw [loss_succ]
        exact tail.final_loss
      · intro index hindex
        rcases index with _ | index
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans
            (tail.rootBudget_le_first index (by omega))

/-- The uniform normalization loss paid before any runtime data is exposed. -/
noncomputable def Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss
    {sigma gridOutputLoss discreteLoss : ℝ} {N : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule
      sigma gridOutputLoss discreteLoss N) : ℝ :=
  backward.rootBudget / 16

/-- The matching pre-runtime density loss.  Runtime root normalization may
use its own existing density fields; this scalar only pays the initial
current-reentry receipt. -/
noncomputable def Proposition63FourCallInnerBackwardLossSchedule.rootDensityLoss
    {sigma gridOutputLoss discreteLoss : ℝ} {N : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule
      sigma gridOutputLoss discreteLoss N) : ℝ :=
  backward.rootBudget / 8

/-- The midpoint between the current density cost and the remaining strict
reentry room at one valid backward index. -/
noncomputable def Proposition63FourCallInnerBackwardLossSchedule.currentWeightLoss
    {sigma gridOutputLoss discreteLoss : ℝ} {N : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule
      sigma gridOutputLoss discreteLoss N)
    (index : ℕ) (hindex : index < N) : ℝ :=
  5 * (backward.seed index hindex).schedule.first.sourceLoss / 8

/-- The exact terminal D-to-E exponent gap after the backward index exposes
its current reentry weight.  This is intentionally only a scalar gap: the
terminal absorption constructor lives downstream of this acyclic schedule
module. -/
theorem Proposition63FourCallInnerBackwardLossSchedule.finalCurrentWeightGap
    {sigma gridOutputLoss discreteLoss : ℝ} {N : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule
      sigma gridOutputLoss discreteLoss N)
    (index : ℕ) (hindex : index < N) :
    (backward.seed index hindex).goodCellCandidateLoss +
        backward.currentWeightLoss index hindex <
      backward.loss (index + 1) := by
  let seed := backward.seed index hindex
  have firstSourceLtSecond :
      seed.schedule.first.sourceLoss <
        seed.schedule.second.sourceLoss / 32 := by
    calc
      seed.schedule.first.sourceLoss ≤
          seed.schedule.first.normalizationLoss / 2 :=
        seed.schedule.first.sourceLoss_le_half
      _ < seed.schedule.firstOutputLoss / 2 := by
        linarith [seed.schedule.first.normalizationLoss_lt_output]
      _ = seed.schedule.second.sourceLoss / 32 := by
        rw [seed.schedule.firstOutputLoss_eq]
        ring
  change seed.goodCellCandidateLoss +
      5 * seed.schedule.first.sourceLoss / 8 <
    backward.loss (index + 1)
  rw [seed.goodCellCandidateLoss_eq]
  exact staged_final_current_weight_gap
    (seed.schedule.second.sourceLoss_pos.trans_le
      seed.sourceWitnessLoss_le_output)
    firstSourceLtSecond seed.sourceWitnessLoss_le_output

/-- The current-reentry absorption is a loss-only choice.  Keeping this
outside the root-indexed schedule makes its cutoff available before a runtime
extremal source or normalization is selected. -/
noncomputable def proposition63_four_call_inner_current_reentry_absorption_at
    {sigma gridOutputLoss discreteLoss inputLoss : ℝ} {N : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule
      sigma gridOutputLoss discreteLoss N)
    (inputLoss_lt_density : inputLoss < backward.rootDensityLoss)
    (index : ℕ) (hindex : index < N) :
    Proposition63CurrentReentryAbsorptionData
      inputLoss backward.rootNormalizationLoss backward.rootDensityLoss
      (backward.loss index) (backward.currentWeightLoss index hindex)
      (backward.seed index hindex).schedule.first.sourceLoss
      (proposition63CanonicalNearbyLevelCount
        backward.rootNormalizationLoss) := by
  let firstSource := (backward.seed index hindex).schedule.first.sourceLoss
  have currentEq : backward.loss index = firstSource / 4 :=
    backward.input_eq index hindex
  have normalizationPos : 0 < backward.rootNormalizationLoss := by
    dsimp [Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss]
    exact div_pos backward.rootBudget_pos (by norm_num)
  have densityWeight : backward.rootDensityLoss + backward.loss index <
      backward.currentWeightLoss index hindex := by
    dsimp [Proposition63FourCallInnerBackwardLossSchedule.currentWeightLoss,
      Proposition63FourCallInnerBackwardLossSchedule.rootDensityLoss,
      Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss]
    rw [currentEq]
    nlinarith [backward.rootBudget_pos,
      backward.rootBudget_le_first index hindex]
  have weightAvailable : backward.currentWeightLoss index hindex <
      firstSource - 2 * backward.rootNormalizationLoss := by
    dsimp [Proposition63FourCallInnerBackwardLossSchedule.currentWeightLoss,
      Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss]
    change 5 * firstSource / 8 < firstSource - 2 * (backward.rootBudget / 16)
    nlinarith [backward.rootBudget_pos,
      backward.rootBudget_le_first index hindex]
  exact Classical.choice <| proposition63_current_reentry_absorption
    inputLoss backward.rootNormalizationLoss backward.rootDensityLoss
    (backward.loss index) (backward.currentWeightLoss index hindex)
    firstSource
    (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss)
    inputLoss_lt_density normalizationPos densityWeight
    (weightAvailable.trans_le (sub_le_self _ (by positivity)))
    (proposition63CanonicalNearbyLevelCount_pos normalizationPos)
    (backward.seed index hindex).schedule.first.sourceLoss_pos
    (by linarith)

/-- The final-candidate lift absorption is likewise determined only by the
frozen backward loss schedule. -/
noncomputable def proposition63_four_call_inner_final_lift_absorption_at
    {sigma gridOutputLoss discreteLoss : ℝ} {N : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule
      sigma gridOutputLoss discreteLoss N)
    (index : ℕ) (hindex : index < N) :
    Proposition63ReentryDensityLiftAbsorptionData
      (backward.currentWeightLoss index hindex)
      (backward.seed index hindex).goodCellCandidateLoss
      (backward.loss (index + 1))
      (proposition63CanonicalNearbyLevelCount
        backward.rootNormalizationLoss) :=
  Classical.choice <| proposition63_reentry_density_lift_absorption
    (backward.currentWeightLoss index hindex)
    (backward.seed index hindex).goodCellCandidateLoss
    (backward.loss (index + 1))
    (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss)
    (by linarith [backward.finalCurrentWeightGap index hindex])

/-- All pre-runtime scalar payments for the initial current reentry at one
valid index, including the receipt made by the canonical constructor. -/
structure Proposition63FourCallInnerCurrentReentryScheduleAt
    {delta sigma inputLoss gridOutputLoss discreteLoss : ℝ}
    {normalizationExponent N : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule
      sigma gridOutputLoss discreteLoss N)
    (source : PureWZ2ExtremalConfiguration sigma inputLoss delta)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss)
    (index : ℕ) (hindex : index < N) where
  density_absorb : Proposition63CurrentReentryAbsorptionData
    inputLoss backward.rootNormalizationLoss
    backward.rootDensityLoss (backward.loss index)
    (backward.currentWeightLoss index hindex)
    (backward.seed index hindex).schedule.first.sourceLoss
    (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss)
  finalCandidateLiftAbsorption : Proposition63ReentryDensityLiftAbsorptionData
    (backward.currentWeightLoss index hindex)
    (backward.seed index hindex).goodCellCandidateLoss
    (backward.loss (index + 1))
    (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss)
  currentLoss_pos : 0 < backward.loss index
  currentLoss_lt_reentry :
    backward.loss index <
      (backward.seed index hindex).schedule.first.sourceLoss
  density_weight_gap :
    backward.rootDensityLoss + backward.loss index <
      backward.currentWeightLoss index hindex
  weight_reentry_gap :
    backward.currentWeightLoss index hindex <
      (backward.seed index hindex).schedule.first.sourceLoss
  regularization_gap :
    0 < (backward.seed index hindex).schedule.first.sourceLoss -
      backward.currentWeightLoss index hindex -
        2 * backward.rootNormalizationLoss
  two_normalization_le_reentry :
    2 * backward.rootNormalizationLoss ≤
      (backward.seed index hindex).schedule.first.sourceLoss

/-- Construct the complete joint finite scalar schedule at every valid
backward index. -/
noncomputable def proposition63_four_call_inner_current_reentry_schedule_at
    {delta sigma inputLoss gridOutputLoss discreteLoss : ℝ}
    {normalizationExponent N : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule
      sigma gridOutputLoss discreteLoss N)
    (source : PureWZ2ExtremalConfiguration sigma inputLoss delta)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss)
    (index : ℕ) (hindex : index < N) :
    Proposition63FourCallInnerCurrentReentryScheduleAt
      backward source root index hindex := by
  let firstSource := (backward.seed index hindex).schedule.first.sourceLoss
  have budgetPos := backward.rootBudget_pos
  have budgetLe : backward.rootBudget ≤ firstSource :=
    backward.rootBudget_le_first index hindex
  have firstSourcePos := (backward.seed index hindex).schedule.first.sourceLoss_pos
  have currentEq : backward.loss index = firstSource / 4 :=
    backward.input_eq index hindex
  have normalizationPos : 0 < backward.rootNormalizationLoss := by
    dsimp [Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss]
    linarith
  have densitySource : inputLoss < backward.rootDensityLoss := by
    have inputLe := root.normalization.input_loss_le_half
    dsimp [Proposition63FourCallInnerBackwardLossSchedule.rootDensityLoss,
      Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss]
      at inputLe ⊢
    linarith
  have currentPos : 0 < backward.loss index := by
    rw [currentEq]
    positivity
  have currentLt : backward.loss index < firstSource := by
    rw [currentEq]
    linarith
  have densityWeight :
      backward.rootDensityLoss + backward.loss index <
        backward.currentWeightLoss index hindex := by
    dsimp [Proposition63FourCallInnerBackwardLossSchedule.currentWeightLoss,
      Proposition63FourCallInnerBackwardLossSchedule.rootDensityLoss,
      Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss]
    rw [currentEq]
    nlinarith
  have weightAvailable :
      backward.currentWeightLoss index hindex <
        firstSource - 2 * backward.rootNormalizationLoss := by
    dsimp [Proposition63FourCallInnerBackwardLossSchedule.currentWeightLoss,
      Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss]
    change 5 * firstSource / 8 < firstSource - 2 * (backward.rootBudget / 16)
    nlinarith
  have weightReentry :
      backward.currentWeightLoss index hindex < firstSource := by
    dsimp [Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss]
      at weightAvailable
    linarith
  have regularizationGap :
      0 < firstSource - backward.currentWeightLoss index hindex -
        2 * backward.rootNormalizationLoss := by
    linarith
  have twoNormalizationLe :
      2 * backward.rootNormalizationLoss ≤ firstSource := by
    dsimp [Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss]
    linarith
  let densityAbsorb :=
    proposition63_four_call_inner_current_reentry_absorption_at backward
      densitySource index hindex
  let finalCandidateLiftAbsorption :=
    proposition63_four_call_inner_final_lift_absorption_at backward index hindex
  exact {
    density_absorb := densityAbsorb
    finalCandidateLiftAbsorption := finalCandidateLiftAbsorption
    currentLoss_pos := currentPos
    currentLoss_lt_reentry := currentLt
    density_weight_gap := densityWeight
    weight_reentry_gap := weightReentry
    regularization_gap := regularizationGap
    two_normalization_le_reentry := twoNormalizationLe
  }

/-- The standalone root-normalization bound consumed by
`Proposition63RootNormalizationData.finiteNearbySchedule`. -/
theorem Proposition63FourCallInnerBackwardLossSchedule.two_rootNormalizationLoss_le_first
    {sigma gridOutputLoss discreteLoss : ℝ} {N : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule
      sigma gridOutputLoss discreteLoss N)
    (index : ℕ) (hindex : index < N) :
    2 * backward.rootNormalizationLoss ≤
      (backward.seed index hindex).schedule.first.sourceLoss := by
  dsimp [Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss]
  linarith [backward.rootBudget_pos,
    backward.rootBudget_le_first index hindex]

/-- The two genuine current-reentry constructor gaps cannot hold with one
shared density loss.  This records the minimal scalar obstruction in the old
M5 interface; the repaired interface gives the calls separate density losses. -/
theorem proposition63_shared_density_loss_obstruction
    {thirdSource densityLoss outerExtremalLoss firstStageWeightLoss
      : ℝ}
    (hfirstStageDensity :
      densityLoss + outerExtremalLoss < firstStageWeightLoss)
    (houterExtremalLoss : 0 ≤ outerExtremalLoss)
    (hfirstStageWeight : firstStageWeightLoss < thirdSource)
    (hsecondSourceDensity : thirdSource < densityLoss) : False := by
  linarith

end Kakeya.Assouad.PureWZ2
