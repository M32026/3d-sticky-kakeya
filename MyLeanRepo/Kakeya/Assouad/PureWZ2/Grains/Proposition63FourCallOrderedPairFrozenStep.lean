import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallOrderedPairCallback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallOrderedPairScaleSmallness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallRootInput

/-!
# Frozen pre-runtime inputs for the Proposition 6.3 ordered-pair step

The package in this file contains only index-local data fixed before the
iterator exposes its current shading.  In particular, the aligned lower scale,
the interval scale, and the alignment multiplier all come from the single
`scales` field.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- Complete pre-runtime data for one ordered pair.  Runtime shadings, their
extremality and convex-Wolff witnesses, and both mass ledgers are deliberately
absent. -/
structure Proposition63FourCallOrderedPairFrozenInputsAt
    {delta sigma inputLoss normalizationLoss rootDensityLoss rhoDensityLoss
      firstStageDensityLoss secondReentryDensityLoss outputLoss rhoWeightLoss
      firstStageWeightLoss
      currentWeightLoss outerExtremalLoss robustExponent epsilon₁ epsilon₃
      parentLoss firstLoss nextWeightLoss secondLoss middleLoss finalLoss
      incidence discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        rootDensityLoss)
    {gridN : ℕ}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (loss : ℕ → ℝ) (leftFactor rightFactor : ℕ → ENNReal)
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss)
    (currentSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := root.normalization.croppedFamily)
      (Kakeya.realRpowENN delta (-normalizationLoss))
      (Kakeya.realRpowENN delta (-schedule.first.sourceLoss))
      (proposition63CanonicalNearbyLevelCount normalizationLoss))
    (sourceCoefficient : NNReal)
    (index : ℕ) where
  scales : Proposition63FourCallOrderedPairIndexScales grid index
  ambient_two : (2 : ENNReal) <
    Kakeya.realRpowENN delta (-normalizationLoss)
  currentLoss_le_reentry : loss index ≤ schedule.first.sourceLoss
  currentLoss_pos : 0 < loss index
  reentryLoss_le_half : schedule.first.sourceLoss ≤
    schedule.first.normalizationLoss / 2
  canonical_weight_absorb :
    proposition63CanonicalReentryWeight delta currentWeightLoss ≤
      (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta rootDensityLoss *
        Kakeya.realRpowENN delta (loss index + 2)
  trace_fixed_absorb :
    (96 * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN delta
          (schedule.first.sourceLoss - currentWeightLoss) ≤ 1
  paper_fixed_absorb :
    ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN delta
          (schedule.first.sourceLoss - currentWeightLoss) ≤
      (73 / 100 : ENNReal)
  regularization_absorb :
    let degreeConstant :=
      16 * (currentSchedule.scaleCount : ENNReal) *
        (Nat.log 2 (2 * root.normalization.croppedFamily.card) + 1 :
          ENNReal) ^ currentSchedule.scaleCount
    let regularizationLoss :=
      (8 : ENNReal) *
        (Nat.log 2 (2 * root.normalization.croppedFamily.card) + 1 :
          ENNReal) ^ (currentSchedule.scaleCount + 1)
    max degreeConstant
        (((proposition63CanonicalReentryWeight delta currentWeightLoss)⁻¹ *
            (Kakeya.realRpowENN delta (-normalizationLoss) *
              (regularizationLoss *
                ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
                  Kakeya.realRpowENN delta 2)) *
              degreeConstant)) *
          Kakeya.realRpowENN delta (-normalizationLoss)) ≤
      Kakeya.realRpowENN delta (-schedule.first.sourceLoss)
  delta_small : delta ≤ 1 / 24
  hdeltaFirstCall : delta ≤ schedule.first.delta₀
  hrhoLower : Real.rpow delta (1 - schedule.firstOutputLoss) ≤ scales.rhoHat.1
  hrhoUpper : scales.rhoHat.1 ≤ Real.rpow delta schedule.firstOutputLoss
  hcellError :
    ((lipschitzExtensionConstant Point3 * sourceCoefficient : NNReal) : ℝ) *
      (scales.rhoHat.1 * Real.sqrt 3) ≤ 1 / 2
  rhoAbsorption : Proposition63CurrentReentryAbsorptionData
    (schedule.second.sourceLoss / 16) (schedule.second.sourceLoss / 4)
    rhoDensityLoss schedule.firstOutputLoss rhoWeightLoss
    schedule.second.sourceLoss
    (proposition63CanonicalNearbyLevelCount
      (schedule.second.sourceLoss / 4))
  hrhoAbsorption : scales.rhoHat.1 ≤ rhoAbsorption.delta₀
  hrhoSmall : scales.rhoHat.1 ≤ 1 / 24
  hdeltaSecondCall : scales.rhoHat.1 ≤ schedule.second.delta₀
  robustScale : WZ2PaperRequestedScale scales.rhoHat.1
  hrobustLower : Real.rpow scales.rhoHat.1
    (1 - schedule.secondOutputLoss) ≤ robustScale.1
  hrobustUpper : robustScale.1 ≤
    Real.rpow scales.rhoHat.1 schedule.secondOutputLoss
  hdeltaThirdCall : scales.rhoHat.1 ≤ schedule.third.delta₀
  firstStageAbsorption : Proposition63CurrentReentryAbsorptionData
    schedule.second.sourceLoss schedule.second.normalizationLoss
    firstStageDensityLoss
    outerExtremalLoss firstStageWeightLoss schedule.third.sourceLoss
    (proposition63CanonicalNearbyLevelCount
      schedule.second.normalizationLoss)
  hdeltaFirstStage : scales.rhoHat.1 ≤ firstStageAbsorption.delta₀
  hsourceOuter : schedule.second.normalizationLoss ≤ outerExtremalLoss
  houterExtremalLoss : 0 < outerExtremalLoss
  houterRetention : Kakeya.realRpowENN scales.rhoHat.1 outerExtremalLoss ≤
    wz2PaperPureRefinementFraction scales.rhoHat.1 61 *
      Kakeya.realRpowENN scales.rhoHat.1 schedule.second.normalizationLoss
  houterTargetReentry : outerExtremalLoss ≤ schedule.third.sourceLoss
  targetScale : WZ2PaperRequestedScale scales.rhoHat.1
  htargetLower : Real.rpow scales.rhoHat.1
    (1 - schedule.thirdOutputLoss) ≤ targetScale.1
  htargetUpper : targetScale.1 ≤
    Real.rpow scales.rhoHat.1 schedule.thirdOutputLoss
  firstGridAbsorption : Proposition63RobustGridPruningAbsorptionData
    schedule.third.normalizationLoss epsilon₁
  firstCrossAbsorption :
    Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
      robustExponent schedule.secondOutputLoss
      schedule.third.normalizationLoss firstStageWeightLoss 4
      (proposition63CanonicalNearbyLevelCount
        schedule.second.normalizationLoss)
  hdeltaFirstGrid : scales.rhoHat.1 ≤ firstGridAbsorption.delta₀
  hdeltaFirstCross : scales.rhoHat.1 ≤ firstCrossAbsorption.delta₀
  hrobustScale : robustScale.1 =
    Real.rpow scales.rhoHat.1 robustExponent
  htargetScale : targetScale.1 =
    Real.rpow scales.rhoHat.1 robustExponent
  firstBoundaryAbsorption : Proposition63RobustBoundaryAbsorptionData
    schedule.thirdOutputLoss schedule.third.normalizationLoss
  hdeltaFirstBoundary : scales.rhoHat.1 ≤ firstBoundaryAbsorption.delta₀
  hrobustSmall : robustScale.1 ≤ 1 / 10000
  hkappa : Real.rpow scales.rhoHat.1 epsilon₃ ≤ robustScale.1
  htargetSmall : targetScale.1 ≤ 1 / 12
  htargetTau : targetScale.1 ≤ 3 * scales.tau
  htauSq : scales.tau ^ 2 ≤ 4 * scales.rhoHat.1
  hsigma : 0 < sigma
  hsigmaOne : sigma < 1
  hepsilon₁ : 0 < epsilon₁
  hepsilon₃ : 0 < epsilon₃
  hepsilonSum : epsilon₁ + epsilon₃ < 1
  logScale : ℝ
  hdeltaLog : scales.rhoHat.1 ≤ logScale
  hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale → scale ≤ logScale →
    ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / scale ^ 3 →
      Real.rpow scale epsilon₁ *
        (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108
  haxis : 4 * (6 * scales.rhoHat.1) ^ 2 ≤
    (3 / 4 : ℝ) *
      (Real.rpow scales.rhoHat.1 (1 - epsilon₃)) ^ 2
  firstConstant : ENNReal
  hfirstArithmetic : ENNReal.ofReal
    ((proposition63RobustTauTotalVolume scales.rhoHat.1 sigma
        schedule.third.normalizationLoss schedule.thirdOutputLoss
        targetScale.1 scales.tau /
      (Real.rpow scales.rhoHat.1 (1 + 7 * epsilon₁ + epsilon₃) *
        scales.tau ^ 2 / 200)) *
      (2 * proposition63DependentSlabWidth scales.rhoHat.1 scales.tau
        (proposition63DependentCoarseIncidence scales.rhoHat.1 incidence
          (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)))
        (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)) /
          scales.rhoHat.1 + 2)) ≤
    firstConstant * Kakeya.realRpowENN
      (scales.tau / scales.rhoHat.1) (1 - sigma)
  hnormalizationParent : schedule.third.normalizationLoss ≤ parentLoss
  hparentRetention : Kakeya.realRpowENN scales.rhoHat.1 parentLoss ≤
    wz2PaperPureRefinementFraction scales.rhoHat.1 61 *
      Kakeya.realRpowENN scales.rhoHat.1 schedule.third.normalizationLoss
  hparentOutput : parentLoss ≤ firstLoss
  hfirstLoss : 0 < firstLoss
  firstRestoreAbsorption :
    Proposition63RobustPointCoverRestorationAbsorptionData
      parentLoss firstLoss 0
  hdeltaFirstRestore : scales.rhoHat.1 ≤ firstRestoreAbsorption.delta₀
  secondReentryAbsorption : Proposition63CurrentReentryAbsorptionData
    schedule.third.sourceLoss schedule.third.normalizationLoss
    secondReentryDensityLoss
    firstLoss nextWeightLoss schedule.fourth.sourceLoss
    (proposition63CanonicalNearbyLevelCount
      schedule.third.normalizationLoss)
  hdeltaSecondReentry : scales.rhoHat.1 ≤ secondReentryAbsorption.delta₀
  hfirstReentry : firstLoss ≤ schedule.fourth.sourceLoss
  hdeltaFourth : scales.rhoHat.1 ≤ schedule.fourth.delta₀
  sqrtRequested : WZ2PaperRequestedScale scales.rhoHat.1
  hsqrtLower : Real.rpow scales.rhoHat.1 (1 - outputLoss) ≤ sqrtRequested.1
  hsqrtUpper : sqrtRequested.1 ≤ Real.rpow scales.rhoHat.1 outputLoss
  hsqrtOne : sqrtRequested.1 ≤ 1
  secondBoundaryAbsorption : Proposition63RobustBoundaryAbsorptionData
    outputLoss schedule.fourth.normalizationLoss
  hdeltaSecondBoundary : scales.rhoHat.1 ≤ secondBoundaryAbsorption.delta₀
  secondGridAbsorption : Proposition63RobustGridPruningAbsorptionData
    schedule.fourth.normalizationLoss epsilon₁
  hdeltaSecondGrid : scales.rhoHat.1 ≤ secondGridAbsorption.delta₀
  secondCrossAbsorption :
    Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
      robustExponent schedule.thirdOutputLoss
      schedule.fourth.normalizationLoss nextWeightLoss 4
      (proposition63CanonicalNearbyLevelCount
        schedule.third.normalizationLoss)
  hdeltaSecondCross : scales.rhoHat.1 ≤ secondCrossAbsorption.delta₀
  htargetRobustSmall : targetScale.1 ≤ 1 / 10000
  htargetKappa : Real.rpow scales.rhoHat.1 epsilon₃ ≤ targetScale.1
  hsqrtSmall : sqrtRequested.1 ≤ 1 / 12
  hsqrtSq : sqrtRequested.1 ^ 2 ≤ 4 * scales.rhoHat.1
  finalConstant : ENNReal
  hfinalArithmetic : ENNReal.ofReal
    ((proposition63RobustTauTotalVolume scales.rhoHat.1 sigma
        schedule.fourth.normalizationLoss outputLoss sqrtRequested.1
        sqrtRequested.1 /
      (Real.rpow scales.rhoHat.1 (1 + 7 * epsilon₁ + epsilon₃) *
        sqrtRequested.1 ^ 2 / 200)) *
      (2 * proposition63DependentSlabWidth scales.rhoHat.1 sqrtRequested.1
        (proposition63DependentCoarseIncidence scales.rhoHat.1 incidence
          (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)))
        (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)) /
          scales.rhoHat.1 + 2)) ≤
    finalConstant * Kakeya.realRpowENN
      (sqrtRequested.1 / scales.rhoHat.1) (1 - sigma)
  hnormalizationSecond : schedule.fourth.normalizationLoss ≤ secondLoss
  hsecondLoss : 0 < secondLoss
  secondRestoreAbsorption :
    Proposition63RobustPointCoverRestorationAbsorptionData
      schedule.fourth.normalizationLoss secondLoss 61
  hdeltaSecondRestore : scales.rhoHat.1 ≤ secondRestoreAbsorption.delta₀
  hsecondMiddle : secondLoss ≤ middleLoss
  hmiddleLoss : 0 < middleLoss
  multiplicityAbsorption : Proposition63FullGrainLogAbsorptionData
    secondLoss middleLoss
  hdeltaMultiplicity : scales.rhoHat.1 ≤ multiplicityAbsorption.delta₀
  hbalancingBoundary : 2 * 24000000 *
    (Kakeya.realRpowENN scales.rhoHat.1 (-middleLoss) *
        wz2PaperBoundaryGeometryConstant + 1) *
    ENNReal.ofReal (Real.sqrt (scales.rhoHat.1 / sqrtRequested.1)) <
      Kakeya.realRpowENN scales.rhoHat.1 middleLoss
  hmiddleFinal : middleLoss ≤ finalLoss
  hfinalLoss : 0 < finalLoss
  balancingAbsorption : Proposition63FullGrainBalancingAbsorptionData
    middleLoss finalLoss
  hdeltaBalancing : scales.rhoHat.1 ≤ balancingAbsorption.delta₀
  floorLoss : ℝ
  structuralBudget : ℝ
  cellVolumeFloor : ℝ
  outputCandidateLoss : ℝ
  spatialScale : ℝ
  critical : PureWZ2CriticalFloorSelectionData
    sigma floorLoss structuralBudget
  coarseCritical : scales.rhoHat.1 ≤ critical.delta₀
  finalStructural : finalLoss ≤ critical.structuralLoss
  criticalTraceAbsorption :
    Proposition63PureCriticalTailTraceAbsorption scales.rhoHat.1
      critical.structuralLoss schedule.fourth.sourceLoss finalLoss
  cellVolumeFloor_pos : 0 < cellVolumeFloor
  cellBudget : ENNReal.ofReal cellVolumeFloor *
      Kakeya.realRpowENN sqrtRequested.1 (sigma - outputLoss) ≤
    Kakeya.realRpowENN scales.rhoHat.1 (sigma + floorLoss) *
      Kakeya.realRpowENN sqrtRequested.1 3
  tau_le_sqrt : scales.tau ≤ Real.sqrt scales.rhoHat.1
  sqrtScale_eq : sqrtRequested.1 = Real.sqrt scales.rhoHat.1
  hcoefficientOne : 1 ≤
    (((4 : NNReal) *
      (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ)
  coverBudget : ℕ
  hcoverBudgetPos : 0 < coverBudget
  hcoverBudget : (512 : ENNReal) *
    ((2 * Nat.ceil (2 *
        (((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ)) + 2 :
        ENNReal) *
      (finalConstant * Kakeya.realRpowENN
        (sqrtRequested.1 / scales.rhoHat.1) (1 - sigma))) ≤
    (coverBudget : ENNReal)
  hsqrtConstantFinite : finalConstant * Kakeya.realRpowENN
    (sqrtRequested.1 / scales.rhoHat.1) (1 - sigma) ≠ ⊤
  hnormalErrorTau : 8 *
    (((4 : NNReal) *
      (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ) *
      scales.rhoHat.1 ≤ scales.tau
  hhullTau : scales.rhoHat.1 * Real.sqrt 3 ≤ scales.tau
  hnextLoss : outputCandidateLoss = loss (index + 1)
  alignedAbsorption :
    Proposition63AlignedIntervalAbsorptionData discreteLoss
  hdeltaAlignedAbsorption : delta ≤ alignedAbsorption.delta₀
  nestedIntervalAbsorption : Proposition63NestedIntervalAbsorptionData
    (((4 : NNReal) *
      (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ)
    firstConstant alignedAbsorption.internalLoss
  hdeltaNestedInterval : delta ≤ nestedIntervalAbsorption.delta₀
  uniformLevel : ℕ
  hleftFactor : leftFactor index =
    proposition63FourCallFrozenActualLeftFactor
      root.normalization.croppedFamily delta scales.rhoHat.1 sigma
      schedule.firstOutputLoss currentWeightLoss 61
      (proposition63FourCallAncestorRetentionUpper
        root.normalization.croppedFamily scales.rhoHat.1 sigma
        schedule.firstOutputLoss schedule.second.normalizationLoss
        schedule.second.sourceLoss rhoWeightLoss firstStageWeightLoss)
      (proposition63FourCallFrozenLineCoverBase
        cellVolumeFloor sqrtRequested.1 coverBudget)
      (proposition63CanonicalReentryWeight
        scales.rhoHat.1 nextWeightLoss)
  hrightFactor : rightFactor index =
    proposition63UniformDependentRightFactor
      root.normalization.croppedFamily uniformLevel
  hcurrentLevel : proposition63CanonicalNearbyLevelCount normalizationLoss ≤
    uniformLevel
  hnestedLevel :
    proposition63CanonicalNearbyLevelCount schedule.third.normalizationLoss ≤
      uniformLevel
  hfourRho : 4 * scales.rhoHat.1 ≤ 1

/-- A family of pre-runtime index packages supplies the exact callback step. -/
theorem proposition63_four_call_ordered_pair_step_of_frozen_inputs
    {delta sigma inputLoss normalizationLoss rootDensityLoss rhoDensityLoss
      firstStageDensityLoss secondReentryDensityLoss outputLoss rhoWeightLoss
      firstStageWeightLoss
      currentWeightLoss outerExtremalLoss robustExponent epsilon₁ epsilon₃
      parentLoss firstLoss nextWeightLoss secondLoss middleLoss finalLoss
      incidence discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        rootDensityLoss)
    (rootInput : Proposition63FourCallRootInput root)
    {gridN : ℕ}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (loss : ℕ → ℝ) (leftFactor rightFactor : ℕ → ENNReal)
    (massSchedule : Proposition63FourCallUniformMassSchedule grid loss
      leftFactor rightFactor)
    (sourceMap : PaperWZ1WeakPlaneMapData
      root.normalization.croppedRefined incidence)
    (sourceCoefficient : NNReal)
    (extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient)
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss)
    (currentSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := root.normalization.croppedFamily)
      (Kakeya.realRpowENN delta (-normalizationLoss))
      (Kakeya.realRpowENN delta (-schedule.first.sourceLoss))
      (proposition63CanonicalNearbyLevelCount normalizationLoss))
    (frozenInputs : ∀ index,
      index < (finiteIntervalOrderedPairs gridN).length →
      Nonempty (Proposition63FourCallOrderedPairFrozenInputsAt
        (rhoDensityLoss := rhoDensityLoss)
        (firstStageDensityLoss := firstStageDensityLoss)
        (secondReentryDensityLoss := secondReentryDensityLoss)
        (rhoWeightLoss := rhoWeightLoss)
        (firstStageWeightLoss := firstStageWeightLoss)
        (currentWeightLoss := currentWeightLoss)
        (outerExtremalLoss := outerExtremalLoss)
        (robustExponent := robustExponent)
        (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
        (parentLoss := parentLoss) (firstLoss := firstLoss)
        (nextWeightLoss := nextWeightLoss) (secondLoss := secondLoss)
        (middleLoss := middleLoss) (finalLoss := finalLoss)
        (incidence := incidence) root grid loss leftFactor rightFactor schedule
        currentSchedule sourceCoefficient index)) :
    Proposition63FourCallOrderedPairStep grid
      root.normalization.croppedRefined extension.ambient.planeMap loss
      leftFactor rightFactor := by
  intro index hindex current current_sub current_cubical _currentMultiplicity
    current_extremal current_cwa _prefixMass _currentMass
  rcases frozenInputs index hindex with ⟨f⟩
  exact proposition63_four_call_ordered_pair_actual_of_scalar_bounds
    (rhoDensityLoss := rhoDensityLoss)
    (firstStageDensityLoss := firstStageDensityLoss)
    (secondReentryDensityLoss := secondReentryDensityLoss)
    (rhoWeightLoss := rhoWeightLoss)
    (firstStageWeightLoss := firstStageWeightLoss)
    root grid loss leftFactor rightFactor massSchedule sourceMap
    sourceCoefficient extension hindex current schedule currentSchedule
    f.ambient_two current_sub current_cubical current_extremal current_cwa
    f.currentLoss_le_reentry f.currentLoss_pos f.reentryLoss_le_half
    f.canonical_weight_absorb f.trace_fixed_absorb f.paper_fixed_absorb
    f.regularization_absorb f.delta_small
    rootInput.ordinaryAxialWindowEighth f.hdeltaFirstCall
    f.scales.rhoHat f.hrhoLower f.hrhoUpper f.hcellError f.rhoAbsorption
    f.hrhoAbsorption f.hrhoSmall f.hdeltaSecondCall f.robustScale
    f.hrobustLower f.hrobustUpper f.hdeltaThirdCall f.firstStageAbsorption
    f.hdeltaFirstStage f.hsourceOuter f.houterExtremalLoss
    f.houterRetention f.houterTargetReentry f.targetScale f.htargetLower
    f.htargetUpper f.firstGridAbsorption f.firstCrossAbsorption
    f.hdeltaFirstGrid f.hdeltaFirstCross f.hrobustScale f.htargetScale
    f.scales.rhoHat_le_tau f.scales.tau_pos f.scales.tau_le_one
    f.firstBoundaryAbsorption f.hdeltaFirstBoundary f.hrobustSmall f.hkappa
    f.htargetSmall f.htargetTau f.htauSq
    f.hsigma f.hsigmaOne f.hepsilon₁ f.hepsilon₃ f.hepsilonSum f.logScale
    f.hdeltaLog f.hlog f.haxis f.firstConstant f.hfirstArithmetic
    f.hnormalizationParent f.hparentRetention f.hparentOutput f.hfirstLoss
    f.firstRestoreAbsorption f.hdeltaFirstRestore f.secondReentryAbsorption
    f.hdeltaSecondReentry f.hfirstReentry f.hdeltaFourth f.sqrtRequested
    f.hsqrtLower f.hsqrtUpper f.hsqrtOne f.secondBoundaryAbsorption
    f.hdeltaSecondBoundary f.secondGridAbsorption f.hdeltaSecondGrid
    f.secondCrossAbsorption f.hdeltaSecondCross f.htargetRobustSmall
    f.htargetKappa f.hsqrtSmall f.hsqrtSq f.finalConstant
    f.hfinalArithmetic f.hnormalizationSecond f.hsecondLoss
    f.secondRestoreAbsorption f.hdeltaSecondRestore f.hsecondMiddle
    f.hmiddleLoss f.multiplicityAbsorption f.hdeltaMultiplicity
    f.hbalancingBoundary f.hmiddleFinal f.hfinalLoss f.balancingAbsorption
    f.hdeltaBalancing f.floorLoss f.structuralBudget f.cellVolumeFloor
    f.outputCandidateLoss f.spatialScale f.critical f.coarseCritical
    f.finalStructural f.criticalTraceAbsorption f.cellVolumeFloor_pos
    f.cellBudget f.tau_le_sqrt
    f.sqrtScale_eq f.hcoefficientOne f.coverBudget f.hcoverBudgetPos
    f.hcoverBudget f.hsqrtConstantFinite f.hnormalErrorTau f.hhullTau
    f.scales.scaleFactor f.scales.scaleFactor_pos f.scales.rhoHat_aligned
    f.scales.logicalR_le_rhoHat f.scales.rhoHat_le_two_logicalR
    f.scales.tau_eq f.hnextLoss f.alignedAbsorption
    f.hdeltaAlignedAbsorption f.nestedIntervalAbsorption
    f.hdeltaNestedInterval f.uniformLevel f.hleftFactor f.hrightFactor
    f.hcurrentLevel f.hnestedLevel f.hfourRho

end Kakeya.Assouad.PureWZ2
