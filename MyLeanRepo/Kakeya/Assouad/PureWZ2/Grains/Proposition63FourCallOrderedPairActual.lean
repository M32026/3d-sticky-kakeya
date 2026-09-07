import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallOrderedPairProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallFinalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallOrderedPair
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallOrderedPairMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63AlignedIntervalAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallReentryReceipts
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallOrderedPairScalarBounds

/-!
# Actual-current producer for one four-call ordered pair

This module isolates the dependent plumbing needed by the finite iterator.
It constructs a fresh re-entry from the callback's actual current shading,
restricts the one fixed ambient extension, runs the concrete four-call
assembly, builds its receipts from scalar facts, and invokes the M5 step.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- Execute one actual callback step.  The three universally quantified
premises are the remaining runtime-dependent scalar obligations; they expose
the precise critical, pullback, and interval-base gaps without accepting a
runtime, pullback object, receipt, or callback from the caller. -/
theorem proposition63_four_call_ordered_pair_actual_of_scalar_bounds
    {delta sigma inputLoss normalizationLoss rootDensityLoss rhoDensityLoss
      firstStageDensityLoss secondReentryDensityLoss outputLoss rhoWeightLoss
      firstStageWeightLoss currentWeightLoss outerExtremalLoss robustExponent
      tau epsilon₁ epsilon₃
      parentLoss firstLoss nextWeightLoss secondLoss middleLoss finalLoss
      incidence discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        rootDensityLoss)
    {gridN index : ℕ}
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
    (hindex : index < (finiteIntervalOrderedPairs gridN).length)
    (current : WZ1PaperTubeShading root.normalization.croppedFamily)
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss)
    (currentSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := root.normalization.croppedFamily)
      (Kakeya.realRpowENN delta (-normalizationLoss))
      (Kakeya.realRpowENN delta (-schedule.first.sourceLoss))
      (proposition63CanonicalNearbyLevelCount normalizationLoss))
    (ambient_two : (2 : ENNReal) <
      Kakeya.realRpowENN delta (-normalizationLoss))
    (current_sub : PaperIsSubshading current root.normalization.croppedRefined)
    (current_cubical : WZ1PaperIsCubicalShading current)
    (current_extremal : WZ2PaperCroppedIsExtremal sigma (loss index)
      root.normalization.croppedFamily current)
    (current_cwa : WZ2PaperConvexWolffBound root.normalization.croppedFamily
      (Kakeya.realRpowENN delta (-(loss index))))
    (currentLoss_le_reentry : loss index ≤ schedule.first.sourceLoss)
    (currentLoss_pos : 0 < loss index)
    (reentryLoss_le_half : schedule.first.sourceLoss ≤
      schedule.first.normalizationLoss / 2)
    (canonical_weight_absorb :
      proposition63CanonicalReentryWeight delta currentWeightLoss ≤
        (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta rootDensityLoss *
          Kakeya.realRpowENN delta (loss index + 2))
    (trace_fixed_absorb :
      (96 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta
            (schedule.first.sourceLoss - currentWeightLoss) ≤ 1)
    (paper_fixed_absorb :
      ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta
            (schedule.first.sourceLoss - currentWeightLoss) ≤
        (73 / 100 : ENNReal))
    (regularization_absorb :
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
        Kakeya.realRpowENN delta (-schedule.first.sourceLoss))
    (delta_small : delta ≤ 1 / 24)
    (rootAxialWindow : ∀ sourceIndex point,
      point ∈ root.normalization.frame ''
          root.normalization.ordinaryRefined.carrier sourceIndex →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (hdeltaFirstCall : delta ≤ schedule.first.delta₀)
    (rho : WZ2PaperRequestedScale delta)
    (hrhoLower : Real.rpow delta (1 - schedule.firstOutputLoss) ≤ rho.1)
    (hrhoUpper : rho.1 ≤ Real.rpow delta schedule.firstOutputLoss)
    (hcellError :
      ((lipschitzExtensionConstant Point3 * sourceCoefficient : NNReal) : ℝ) *
        (rho.1 * Real.sqrt 3) ≤ 1 / 2)
    (rhoAbsorption : Proposition63CurrentReentryAbsorptionData
      (schedule.second.sourceLoss / 16) (schedule.second.sourceLoss / 4)
      rhoDensityLoss schedule.firstOutputLoss rhoWeightLoss
      schedule.second.sourceLoss
      (proposition63CanonicalNearbyLevelCount
        (schedule.second.sourceLoss / 4)))
    (hrhoAbsorption : rho.1 ≤ rhoAbsorption.delta₀)
    (hrhoSmall : rho.1 ≤ 1 / 24)
    (hdeltaSecondCall : rho.1 ≤ schedule.second.delta₀)
    (robustScale : WZ2PaperRequestedScale rho.1)
    (hrobustLower : Real.rpow rho.1
      (1 - schedule.secondOutputLoss) ≤ robustScale.1)
    (hrobustUpper : robustScale.1 ≤
      Real.rpow rho.1 schedule.secondOutputLoss)
    (hdeltaThirdCall : rho.1 ≤ schedule.third.delta₀)
    (firstStageAbsorption : Proposition63CurrentReentryAbsorptionData
      schedule.second.sourceLoss schedule.second.normalizationLoss
      firstStageDensityLoss
      outerExtremalLoss firstStageWeightLoss schedule.third.sourceLoss
      (proposition63CanonicalNearbyLevelCount
        schedule.second.normalizationLoss))
    (hdeltaFirstStage : rho.1 ≤ firstStageAbsorption.delta₀)
    (hsourceOuter : schedule.second.normalizationLoss ≤ outerExtremalLoss)
    (houterExtremalLoss : 0 < outerExtremalLoss)
    (houterRetention : Kakeya.realRpowENN rho.1 outerExtremalLoss ≤
      wz2PaperPureRefinementFraction rho.1 61 *
        Kakeya.realRpowENN rho.1 schedule.second.normalizationLoss)
    (houterTargetReentry : outerExtremalLoss ≤ schedule.third.sourceLoss)
    (targetScale : WZ2PaperRequestedScale rho.1)
    (htargetLower : Real.rpow rho.1
      (1 - schedule.thirdOutputLoss) ≤ targetScale.1)
    (htargetUpper : targetScale.1 ≤
      Real.rpow rho.1 schedule.thirdOutputLoss)
    (firstGridAbsorption : Proposition63RobustGridPruningAbsorptionData
      schedule.third.normalizationLoss epsilon₁)
    (firstCrossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        robustExponent schedule.secondOutputLoss
        schedule.third.normalizationLoss firstStageWeightLoss 4
        (proposition63CanonicalNearbyLevelCount
          schedule.second.normalizationLoss))
    (hdeltaFirstGrid : rho.1 ≤ firstGridAbsorption.delta₀)
    (hdeltaFirstCross : rho.1 ≤ firstCrossAbsorption.delta₀)
    (hrobustScale : robustScale.1 = Real.rpow rho.1 robustExponent)
    (htargetScale : targetScale.1 = Real.rpow rho.1 robustExponent)
    (hdeltaTau : rho.1 ≤ tau) (htauPos : 0 < tau) (htauOne : tau ≤ 1)
    (firstBoundaryAbsorption : Proposition63RobustBoundaryAbsorptionData
      schedule.thirdOutputLoss schedule.third.normalizationLoss)
    (hdeltaFirstBoundary : rho.1 ≤ firstBoundaryAbsorption.delta₀)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hkappa : Real.rpow rho.1 epsilon₃ ≤ robustScale.1)
    (htargetSmall : targetScale.1 ≤ 1 / 12)
    (htargetTau : targetScale.1 ≤ 3 * tau)
    (htauSq : tau ^ 2 ≤ 4 * rho.1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : rho.1 ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale → scale ≤ logScale →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * rho.1) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2)
    (firstConstant : ENNReal)
    (hfirstArithmetic : ENNReal.ofReal
      ((proposition63RobustTauTotalVolume rho.1 sigma
          schedule.third.normalizationLoss schedule.thirdOutputLoss
          targetScale.1 tau /
          (Real.rpow rho.1 (1 + 7 * epsilon₁ + epsilon₃) * tau ^ 2 / 200)) *
        (2 * proposition63DependentSlabWidth rho.1 tau
          (proposition63DependentCoarseIncidence rho.1 incidence
            (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)))
          (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)) /
            rho.1 + 2)) ≤
      firstConstant * Kakeya.realRpowENN (tau / rho.1) (1 - sigma))
    (hnormalizationParent : schedule.third.normalizationLoss ≤ parentLoss)
    (hparentRetention : Kakeya.realRpowENN rho.1 parentLoss ≤
      wz2PaperPureRefinementFraction rho.1 61 *
        Kakeya.realRpowENN rho.1 schedule.third.normalizationLoss)
    (hparentOutput : parentLoss ≤ firstLoss) (hfirstLoss : 0 < firstLoss)
    (firstRestoreAbsorption :
      Proposition63RobustPointCoverRestorationAbsorptionData
        parentLoss firstLoss 0)
    (hdeltaFirstRestore : rho.1 ≤ firstRestoreAbsorption.delta₀)
    (secondReentryAbsorption : Proposition63CurrentReentryAbsorptionData
      schedule.third.sourceLoss schedule.third.normalizationLoss
      secondReentryDensityLoss
      firstLoss nextWeightLoss schedule.fourth.sourceLoss
      (proposition63CanonicalNearbyLevelCount
        schedule.third.normalizationLoss))
    (hdeltaSecondReentry : rho.1 ≤ secondReentryAbsorption.delta₀)
    (hfirstReentry : firstLoss ≤ schedule.fourth.sourceLoss)
    (hdeltaFourth : rho.1 ≤ schedule.fourth.delta₀)
    (sqrtRequested : WZ2PaperRequestedScale rho.1)
    (hsqrtLower : Real.rpow rho.1 (1 - outputLoss) ≤ sqrtRequested.1)
    (hsqrtUpper : sqrtRequested.1 ≤ Real.rpow rho.1 outputLoss)
    (hsqrtOne : sqrtRequested.1 ≤ 1)
    (secondBoundaryAbsorption : Proposition63RobustBoundaryAbsorptionData
      outputLoss schedule.fourth.normalizationLoss)
    (hdeltaSecondBoundary : rho.1 ≤ secondBoundaryAbsorption.delta₀)
    (secondGridAbsorption : Proposition63RobustGridPruningAbsorptionData
      schedule.fourth.normalizationLoss epsilon₁)
    (hdeltaSecondGrid : rho.1 ≤ secondGridAbsorption.delta₀)
    (secondCrossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        robustExponent schedule.thirdOutputLoss
        schedule.fourth.normalizationLoss nextWeightLoss 4
        (proposition63CanonicalNearbyLevelCount
          schedule.third.normalizationLoss))
    (hdeltaSecondCross : rho.1 ≤ secondCrossAbsorption.delta₀)
    (htargetRobustSmall : targetScale.1 ≤ 1 / 10000)
    (htargetKappa : Real.rpow rho.1 epsilon₃ ≤ targetScale.1)
    (hsqrtSmall : sqrtRequested.1 ≤ 1 / 12)
    (hsqrtSq : sqrtRequested.1 ^ 2 ≤ 4 * rho.1)
    (finalConstant : ENNReal)
    (hfinalArithmetic : ENNReal.ofReal
      ((proposition63RobustTauTotalVolume rho.1 sigma
          schedule.fourth.normalizationLoss outputLoss sqrtRequested.1
          sqrtRequested.1 /
          (Real.rpow rho.1 (1 + 7 * epsilon₁ + epsilon₃) *
            sqrtRequested.1 ^ 2 / 200)) *
        (2 * proposition63DependentSlabWidth rho.1 sqrtRequested.1
          (proposition63DependentCoarseIncidence rho.1 incidence
            (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)))
          (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)) /
            rho.1 + 2)) ≤
      finalConstant * Kakeya.realRpowENN
        (sqrtRequested.1 / rho.1) (1 - sigma))
    (hnormalizationSecond : schedule.fourth.normalizationLoss ≤ secondLoss)
    (hsecondLoss : 0 < secondLoss)
    (secondRestoreAbsorption :
      Proposition63RobustPointCoverRestorationAbsorptionData
        schedule.fourth.normalizationLoss secondLoss 61)
    (hdeltaSecondRestore : rho.1 ≤ secondRestoreAbsorption.delta₀)
    (hsecondMiddle : secondLoss ≤ middleLoss) (hmiddleLoss : 0 < middleLoss)
    (multiplicityAbsorption : Proposition63FullGrainLogAbsorptionData
      secondLoss middleLoss)
    (hdeltaMultiplicity : rho.1 ≤ multiplicityAbsorption.delta₀)
    (hbalancingBoundary : 2 * 24000000 *
      (Kakeya.realRpowENN rho.1 (-middleLoss) *
          wz2PaperBoundaryGeometryConstant + 1) *
      ENNReal.ofReal (Real.sqrt (rho.1 / sqrtRequested.1)) <
        Kakeya.realRpowENN rho.1 middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss) (hfinalLoss : 0 < finalLoss)
    (balancingAbsorption : Proposition63FullGrainBalancingAbsorptionData
      middleLoss finalLoss)
    (hdeltaBalancing : rho.1 ≤ balancingAbsorption.delta₀)
    (floorLoss structuralBudget cellVolumeFloor outputCandidateLoss
      spatialScale : ℝ)
    (critical : PureWZ2CriticalFloorSelectionData
      sigma floorLoss structuralBudget)
    (coarseCritical : rho.1 ≤ critical.delta₀)
    (finalStructural : finalLoss ≤ critical.structuralLoss)
    (criticalTraceAbsorption :
      Proposition63PureCriticalTailTraceAbsorption rho.1
        critical.structuralLoss schedule.fourth.sourceLoss finalLoss)
    (cellVolumeFloor_pos : 0 < cellVolumeFloor)
    (cellBudget : ENNReal.ofReal cellVolumeFloor *
        Kakeya.realRpowENN sqrtRequested.1 (sigma - outputLoss) ≤
      Kakeya.realRpowENN rho.1 (sigma + floorLoss) *
        Kakeya.realRpowENN sqrtRequested.1 3)
    (tau_le_sqrt : tau ≤ Real.sqrt rho.1)
    (sqrtScale_eq : sqrtRequested.1 = Real.sqrt rho.1)
    (hcoefficientOne : 1 ≤
      (((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ))
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (hcoverBudget : (512 : ENNReal) *
      ((2 * Nat.ceil (2 *
          (((4 : NNReal) *
            (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ)) + 2 :
          ENNReal) *
        (finalConstant * Kakeya.realRpowENN
          (sqrtRequested.1 / rho.1) (1 - sigma))) ≤
      (coverBudget : ENNReal))
    (hsqrtConstantFinite : finalConstant * Kakeya.realRpowENN
      (sqrtRequested.1 / rho.1) (1 - sigma) ≠ ⊤)
    (hnormalErrorTau : 8 *
      (((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ) *
        rho.1 ≤ tau)
    (hhullTau : rho.1 * Real.sqrt 3 ≤ tau)
    (scaleFactor : ℕ) (scaleFactor_pos : 0 < scaleFactor)
    (rho_aligned : rho.1 = (scaleFactor : ℝ) * delta)
    (logicalR_le_rho :
      (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ) ≤ rho.1)
    (rho_le_two_logicalR : rho.1 ≤
      2 * (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ))
    (htauAlign : tau =
      (grid.scale (finiteIntervalOrderedPair gridN index).2 : ℝ))
    (hnextLoss : outputCandidateLoss = loss (index + 1))
    (alignedAbsorption :
      Proposition63AlignedIntervalAbsorptionData discreteLoss)
    (hdeltaAlignedAbsorption : delta ≤ alignedAbsorption.delta₀)
    (nestedIntervalAbsorption : Proposition63NestedIntervalAbsorptionData
      (((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ)
      firstConstant alignedAbsorption.internalLoss)
    (hdeltaNestedInterval : delta ≤ nestedIntervalAbsorption.delta₀)
    (uniformLevel : ℕ)
    (hleftFactor : leftFactor index =
      proposition63FourCallFrozenActualLeftFactor
        root.normalization.croppedFamily delta rho.1 sigma
        schedule.firstOutputLoss currentWeightLoss 61
        (proposition63FourCallAncestorRetentionUpper
          root.normalization.croppedFamily rho.1 sigma
          schedule.firstOutputLoss schedule.second.normalizationLoss
          schedule.second.sourceLoss rhoWeightLoss firstStageWeightLoss)
        (proposition63FourCallFrozenLineCoverBase
          cellVolumeFloor sqrtRequested.1 coverBudget)
        (proposition63CanonicalReentryWeight rho.1 nextWeightLoss))
    (hrightFactor : rightFactor index =
      proposition63UniformDependentRightFactor
        root.normalization.croppedFamily uniformLevel)
    (hcurrentLevel : proposition63CanonicalNearbyLevelCount normalizationLoss ≤
      uniformLevel)
    (hnestedLevel :
      proposition63CanonicalNearbyLevelCount schedule.third.normalizationLoss ≤
        uniformLevel)
    (hfourRho : 4 * rho.1 ≤ 1)
    :
    ∃ next : WZ1PaperTubeShading root.normalization.croppedFamily,
      PaperIsSubshading next current ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union, next.pointMultiplicity point =
        current.pointMultiplicity point) ∧
      WZ2PaperCroppedIsExtremal sigma (loss (index + 1))
        root.normalization.croppedFamily next ∧
      WZ2PaperConvexWolffBound root.normalization.croppedFamily
        (Kakeya.realRpowENN delta (-(loss (index + 1)))) ∧
      PureWZ2IntervalCoveringAt next extension.ambient.planeMap
        (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
        (grid.scale (finiteIntervalOrderedPair gridN index).1)
        (grid.scale (finiteIntervalOrderedPair gridN index).2)
        (ENNReal.ofReal
          (Real.rpow delta (-discreteLoss) *
            Real.rpow
              ((grid.scale (finiteIntervalOrderedPair gridN index).2 : ℝ) /
                (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ))
              (1 - sigma))) ∧
      leftFactor index * current.mass ≤ rightFactor index * next.mass := by
  let incomingRetentionUpper : ENNReal :=
    proposition63FourCallIncomingRetentionUpper
      root.normalization.croppedFamily rho.1 sigma schedule.firstOutputLoss
  let ancestorRetentionUpper : ENNReal :=
    proposition63FourCallAncestorRetentionUpper
      root.normalization.croppedFamily rho.1 sigma schedule.firstOutputLoss
      schedule.second.normalizationLoss schedule.second.sourceLoss
      rhoWeightLoss firstStageWeightLoss
  let frozenLineCoverBase : ENNReal :=
    proposition63FourCallFrozenLineCoverBase
      cellVolumeFloor sqrtRequested.1 coverBudget
  let variationScale : ℝ :=
    proposition63FourCallVariationScale sourceCoefficient spatialScale
  rcases proposition63_four_call_ordered_pair_prepare_fresh_reentry root current
      currentSchedule ambient_two current_sub current_cubical current_extremal
      currentLoss_le_reentry currentLoss_pos schedule.first.normalizationLoss
      schedule.first.normalizationLoss_pos reentryLoss_le_half
      canonical_weight_absorb trace_fixed_absorb paper_fixed_absorb
      regularization_absorb delta_small with
    ⟨fineCurrentReentry, hfineWeight, hfineWeightUpper, hfineLevel,
      hnormalization⟩
  let currentMap : PaperWZ1WeakPlaneMapData current incidence :=
    paperWeakPlaneMapRestrict sourceMap current_sub
  let currentExtension := extension.restrict sourceMap sourceCoefficient
    current_sub
  let restrictedExtension := currentExtension.restrictToReentry currentMap
    sourceCoefficient fineCurrentReentry
  let runtimeAxialWindow := fineCurrentReentry.rootAxialWindow rootAxialWindow
    schedule.first.sourceLoss_pos
  let fineReentry :=
    fineCurrentReentry.normalization.toPropStickyReentryData
      schedule.first.sourceLoss_pos
      fineCurrentReentry.reentry_normalization_loss_pos
  rcases proposition63_four_call_nested_point_cover_of_absorptions
      (rhoDensityLoss := rhoDensityLoss)
      (firstStageDensityLoss := firstStageDensityLoss)
      (secondReentryDensityLoss := secondReentryDensityLoss)
      (rhoWeightLoss := rhoWeightLoss)
      (firstStageWeightLoss := firstStageWeightLoss)
      fineReentry schedule rfl hnormalization hdeltaFirstCall rho
      hrhoLower hrhoUpper
      runtimeAxialWindow restrictedExtension hcellError rhoAbsorption
      hrhoAbsorption hrhoSmall hdeltaSecondCall robustScale hrobustLower
      hrobustUpper hdeltaThirdCall firstStageAbsorption hdeltaFirstStage
      hsourceOuter houterExtremalLoss houterRetention houterTargetReentry
      targetScale htargetLower htargetUpper firstGridAbsorption
      firstCrossAbsorption hdeltaFirstGrid hdeltaFirstCross hrobustScale
      htargetScale hdeltaTau htauPos htauOne firstBoundaryAbsorption
      hdeltaFirstBoundary hrobustSmall hkappa htargetSmall htargetTau htauSq
      hsigma hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum logScale hdeltaLog hlog
      haxis firstConstant hfirstArithmetic hnormalizationParent
      hparentRetention hparentOutput hfirstLoss firstRestoreAbsorption
      hdeltaFirstRestore secondReentryAbsorption hdeltaSecondReentry
      hfirstReentry hdeltaFourth sqrtRequested hsqrtLower hsqrtUpper hsqrtOne
      secondBoundaryAbsorption hdeltaSecondBoundary secondGridAbsorption
      hdeltaSecondGrid secondCrossAbsorption hdeltaSecondCross
      htargetRobustSmall htargetKappa hsqrtSmall hsqrtSq finalConstant
      hfinalArithmetic hnormalizationSecond hsecondLoss secondRestoreAbsorption
      hdeltaSecondRestore hsecondMiddle hmiddleLoss multiplicityAbsorption
      hdeltaMultiplicity hbalancingBoundary hmiddleFinal hfinalLoss
      balancingAbsorption hdeltaBalancing with
    ⟨nestedRuntime⟩
  rcases nestedRuntime with
    ⟨rich1, runtimeMap, currentReentry, hcurrentNormalization,
      hcurrentCanonicalWeight, hcurrentCanonicalLevel, hruntimeMap, rhoData⟩
  rcases rhoData with
    ⟨outer, targetReentry, target, htargetNormalization,
      htargetCanonicalWeight, htargetCanonicalLevel, nested, hnested,
      secondTargetCard, hsecondTargetCardLe, nestedMass⟩
  let p1 := proposition63_four_call_first_pullback_of_runtime_witnesses
    schedule rich1 runtimeAxialWindow currentReentry
  have hrho_lt_one : rho.1 < 1 := by linarith
  rcases proposition63_four_call_pullback_of_runtime_witnesses
      (firstLoss := firstLoss)
      (fourthSourceLoss := schedule.fourth.sourceLoss)
      (thirdTargetLoss := schedule.thirdOutputLoss)
      (sqrtStickyLoss := outputLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (tauScale := tau)
      (sqrtScale := sqrtRequested.1) rich1.data p1
      schedule.second.sourceLoss_pos
      currentReentry.reentry_normalization_loss_pos outer targetReentry
      schedule.third.sourceLoss_pos target runtimeMap.planeMap
      (firstConstant * Kakeya.realRpowENN (tau / rho.1) (1 - sigma))
      (finalConstant * Kakeya.realRpowENN
        (sqrtRequested.1 / rho.1) (1 - sigma)) nested hnested hrho_lt_one with
    ⟨pullback, pullbackFormula⟩
  let runtime : Proposition63FourCallRuntimeAssemblyData
      fineCurrentReentry schedule schedule.first.sourceLoss_pos rho
      runtimeAxialWindow sourceCoefficient robustScale targetScale
      sqrtRequested firstConstant finalConstant :=
    { rich1 := rich1
      currentMap := runtimeMap
      currentLipschitz := by
        rw [hruntimeMap]
        exact restrictedExtension.lipschitz
      currentReentry := currentReentry
      currentNormalization := hcurrentNormalization
      outer := outer
      targetReentry := targetReentry
      target := target
      targetNormalization := htargetNormalization
      nested := nested
      nested_eq := hnested
      pullback := pullback }
  have hcurrentInitialCard :
      (schedule.callOneRhoRootNormalization rich1 runtimeAxialWindow).croppedFamily.card ≤
        root.normalization.croppedFamily.card := by
    change rich1.data.coarse.card ≤ root.normalization.croppedFamily.card
    have hcoarseSelected : rich1.data.coarse.card ≤
        rich1.data.selected.family.card := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective
        rich1.data.cover.toPaperTubeCover.parent
        rich1.data.cover.toPaperTubeCover.parent_surjective
    have hselectedFine : rich1.data.selected.family.card ≤
        fineCurrentReentry.normalization.croppedFamily.card := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        rich1.data.selected.embedding rich1.data.selected.embedding.injective
    have hfineRoot : fineCurrentReentry.normalization.croppedFamily.card ≤
        root.normalization.croppedFamily.card := by
      rw [fineCurrentReentry.normalization_croppedFamily]
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        fineCurrentReentry.regularized.selected.embedding
        fineCurrentReentry.regularized.selected.embedding.injective
    exact hcoarseSelected.trans (hselectedFine.trans hfineRoot)
  have htargetInitialCard : currentReentry.normalization.croppedFamily.card ≤
      root.normalization.croppedFamily.card := by
    rw [currentReentry.normalization_croppedFamily]
    have hselectedCurrent : currentReentry.regularized.selected.family.card ≤
        (schedule.callOneRhoRootNormalization rich1 runtimeAxialWindow).croppedFamily.card := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        currentReentry.regularized.selected.embedding
        currentReentry.regularized.selected.embedding.injective
    exact hselectedCurrent.trans hcurrentInitialCard
  let incomingRetention : ENNReal :=
    Kakeya.realRpowENN rho.1
        (2 - sigma - schedule.firstOutputLoss) * rich1.data.coarse.enncard
  let incomingUpper : ENNReal :=
    incomingRetentionUpper
  let p1Receipt : Proposition63FourCallReentryRetentionReceipt
      p1.retentionFactor currentReentry.regularized.regularizationLoss
      currentReentry.normalizationWeight incomingRetention := ⟨by rfl⟩
  let pullbackReceipt : Proposition63FourCallPullbackRetentionReceipt
      pullback.retentionFactor (wz2PaperPureRefinementFraction rho.1 61)
      targetReentry.regularized.regularizationLoss
      targetReentry.normalizationWeight p1.retentionFactor :=
    ⟨pullbackFormula⟩
  have hincoming : incomingRetention ≤ incomingUpper := by
    dsimp only [incomingRetention, incomingUpper, incomingRetentionUpper,
      proposition63FourCallIncomingRetentionUpper]
    gcongr
    have hcoarseRoot : rich1.data.coarse.card ≤
        root.normalization.croppedFamily.card := by
      exact hcurrentInitialCard
    change (rich1.data.coarse.card : ENNReal) ≤
      (root.normalization.croppedFamily.card : ENNReal)
    exact_mod_cast hcoarseRoot
  have hpullbackUpper : pullback.retentionFactor ≤
      proposition63FourCallPullbackRetentionFormula
        (wz2PaperPureRefinementFraction rho.1 61)
        (proposition63UniformReentryRegularizationLoss
          root.normalization.croppedFamily
          (proposition63CanonicalNearbyLevelCount schedule.second.normalizationLoss))
        (proposition63CanonicalReentryWeight rho.1 firstStageWeightLoss)
        (proposition63FourCallReentryRetentionFormula
          (proposition63UniformReentryRegularizationLoss
            root.normalization.croppedFamily
            (proposition63CanonicalNearbyLevelCount
              (schedule.second.sourceLoss / 4)))
          (proposition63CanonicalReentryWeight rho.1 rhoWeightLoss)
          incomingUpper) := by
    have htargetLevelFixed : targetReentry.levelCount =
        proposition63CanonicalNearbyLevelCount schedule.second.normalizationLoss :=
      htargetCanonicalLevel.trans <| congrArg
        proposition63CanonicalNearbyLevelCount hcurrentNormalization
    let currentReceipt : Proposition63CanonicalReentryReceipt currentReentry
        (proposition63CanonicalReentryWeight rho.1 rhoWeightLoss)
        (proposition63CanonicalNearbyLevelCount
          (schedule.second.sourceLoss / 4)) :=
      ⟨hcurrentCanonicalWeight, hcurrentCanonicalLevel⟩
    let targetReceipt : Proposition63CanonicalReentryReceipt targetReentry
        (proposition63CanonicalReentryWeight rho.1 firstStageWeightLoss)
        (proposition63CanonicalNearbyLevelCount
          schedule.second.normalizationLoss) :=
      ⟨htargetCanonicalWeight, htargetLevelFixed⟩
    have hp1Upper : p1.retentionFactor ≤
        proposition63FourCallReentryRetentionFormula
          (proposition63UniformReentryRegularizationLoss
            root.normalization.croppedFamily
            (proposition63CanonicalNearbyLevelCount
              (schedule.second.sourceLoss / 4)))
          (proposition63CanonicalReentryWeight rho.1 rhoWeightLoss)
          incomingUpper := by
      exact p1Receipt.le_uniform currentReceipt
        root.normalization.croppedFamily hcurrentInitialCard hincoming
    exact pullbackReceipt.le_uniform_of_reentry targetReceipt
      root.normalization.croppedFamily htargetInitialCard hp1Upper
  have hancestor : pullback.retentionFactor ≤ ancestorRetentionUpper :=
    hpullbackUpper.trans (by
      dsimp only [ancestorRetentionUpper,
        proposition63FourCallAncestorRetentionUpper]
      exact le_rfl)
  have htargetCurrentCard :
      targetReentry.normalization.croppedFamily.card ≤
        currentReentry.normalization.croppedFamily.card := by
    rw [targetReentry.normalization_croppedFamily]
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      targetReentry.regularized.selected.embedding
      targetReentry.regularized.selected.embedding.injective
  have hfirstTargetCard : target.data.selected.family.card ≤
      root.normalization.croppedFamily.card := by
    have hselectedTarget : target.data.selected.family.card ≤
        targetReentry.normalization.croppedFamily.card := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        target.data.selected.embedding target.data.selected.embedding.injective
    exact hselectedTarget.trans (htargetCurrentCard.trans htargetInitialCard)
  have hsecondTargetCard : secondTargetCard ≤
      root.normalization.croppedFamily.card := by
    exact hsecondTargetCardLe.trans (htargetCurrentCard.trans htargetInitialCard)
  have hleftBound : leftFactor index ≤ proposition63DependentFinePullbackLeft
      fineCurrentReentry rich1.data pullback.retentionFactor
      (ENNReal.ofReal ((cellVolumeFloor / 2) /
          (4 * (2 * sqrtRequested.1) ^ 2)) *
        (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) *
        (nested.secondRetainedFactor *
          ((73 / 100 : ENNReal) * nested.reentry.normalizationWeight) *
          nested.firstRetainedFactor)) := by
    rw [hleftFactor]
    exact proposition63_four_call_frozen_left_le_actual fineCurrentReentry
      rich1.data nestedMass pullback.retentionFactor ancestorRetentionUpper
      frozenLineCoverBase _ hfirstTargetCard hsecondTargetCard hancestor
      hfineWeight (by
        dsimp only [frozenLineCoverBase,
          proposition63FourCallFrozenLineCoverBase]
        exact le_rfl)
  have hrightBound : proposition63DependentFinePullbackRight fineCurrentReentry
      ((nested.reentry.regularized.regularizationLoss *
          nested.prepared.preparationLoss) *
        (2 * ENNReal.ofReal (4 * rho.1))) ≤ rightFactor index := by
    have hrightUniform : proposition63DependentFinePullbackRight
        fineCurrentReentry
          ((nested.reentry.regularized.regularizationLoss *
              nested.prepared.preparationLoss) *
            (2 * ENNReal.ofReal (4 * rho.1))) ≤
        proposition63UniformDependentRightFactor
          root.normalization.croppedFamily uniformLevel := by
      refine proposition63_four_call_actual_right_le_uniform
        (delta := delta) (sigma := sigma)
        (normalizationLoss := normalizationLoss)
        (fineReentryLoss := schedule.first.sourceLoss)
        (initialNormalized := root.normalization)
        (nestedInputLoss := schedule.third.sourceLoss)
        (nestedNormalizationLoss := targetReentry.reentryNormalizationLoss)
        (nestedReentryLoss := schedule.fourth.sourceLoss)
        (rho := rho.1)
        (nestedSource := targetReentry.ordinarySource)
        (nestedNormalized := targetReentry.normalization)
        (nestedCurrent := nested.first.shading)
        (uniformLevel := uniformLevel) fineCurrentReentry nested.reentry
        nestedMass ?_ ?_ ?_ ?_ ?_
      · exact hfineLevel.le.trans hcurrentLevel
      · exact htargetCurrentCard.trans htargetInitialCard
      · rw [htargetNormalization]
        exact hnestedLevel
      · exact proposition63_dependent_uniformPreparationLoss_le_root
          fineCurrentReentry rich1.data currentReentry.normalization
          targetReentry p1.coarseEmbedding
      · exact hfourRho
    exact hrightUniform.trans_eq hrightFactor.symm
  let internalConstant : ENNReal := ENNReal.ofReal
    (Real.rpow delta (-alignedAbsorption.internalLoss) *
      Real.rpow (tau / rho.1) (1 - sigma))
  have hinternalConstant :
      Proposition63NestedPointCoverData.FullGrainCells.nestedCandidateIntervalBound
          rho.1 rho.1
            (8 * (((4 : NNReal) *
              (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ) *
                rho.1)
            (((4 : NNReal) *
              (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ)
            (13 ^ 3)
            (firstConstant * Kakeya.realRpowENN (tau / rho.1) (1 - sigma)) ≤
        internalConstant := by
    exact proposition63_nestedCandidateIntervalBound_le_paper
      (((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ)
      firstConstant nestedIntervalAbsorption current_extremal.delta_pos
      hdeltaNestedInterval (current_extremal.delta_pos.trans_le rho.2.1)
  have hpair := finiteIntervalOrderedPair_valid hindex
  have hkLe : (finiteIntervalOrderedPair gridN index).1 ≤ gridN :=
    hpair.1.le.trans hpair.2
  have hlogicalPos : 0 <
      grid.scale (finiteIntervalOrderedPair gridN index).1 :=
    grid.scale_pos _ hkLe
  have base_scalar_bound : 2 * internalConstant ≤
      proposition63FourCallOrderedPairConstant grid index := by
    unfold proposition63FourCallOrderedPairConstant
    exact proposition63_aligned_internal_constant_le_ordered_pair_expression
      grid alignedAbsorption current_extremal.delta_pos
      hdeltaAlignedAbsorption hlogicalPos logicalR_le_rho htauAlign htauPos.le
      (by linarith) (by exact le_rfl)
  let criticalInputs : Proposition63FourCallCriticalTailInputs runtime :=
    { floorLoss := floorLoss
      structuralBudget := structuralBudget
      cellVolumeFloor := cellVolumeFloor
      outputCandidateLoss := outputCandidateLoss
      spatialScale := spatialScale
      variationScale := variationScale
      critical := critical
      coarseCritical := coarseCritical
      finalStructural := finalStructural
      traceAbsorption := criticalTraceAbsorption
      cellVolumeFloor_pos := cellVolumeFloor_pos
      cellBudget := cellBudget
      query_pos := current_extremal.delta_pos.trans_le rho.2.1
      query_le_one := rho.2.2
      tau_pos := htauPos
      query_le_tau := hdeltaTau
      tau_le_sqrt := tau_le_sqrt
      sqrtScale_eq := sqrtScale_eq }
  let planeInputs : Proposition63FourCallPlaneCoverReceipt
      runtime.currentMap.planeMap
      runtime.nested.prepared.refined.shading.union rho.1 tau
      (finalConstant * Kakeya.realRpowENN
        (sqrtRequested.1 / rho.1) (1 - sigma)) :=
    { plane_unit := by
        intro point hpoint
        apply runtime.currentMap.unit point
        apply runtime.currentReentry.normalization_croppedRefined_union_subset_current
        have htarget : point ∈ runtime.target.data.refined.union := by
          rw [← extendShading_union runtime.target.data.selected]
          rw [← runtime.nested_eq]
          exact runtime.nested.prepared_union_subset_current hpoint
        have htargetNormalized : point ∈
            runtime.targetReentry.normalization.croppedRefined.union :=
          refined_union_subset_shading runtime.target.data htarget
        have houterAmbient : point ∈
            (extendShading runtime.outer.data.selected
              runtime.outer.data.refined).union :=
          runtime.targetReentry.normalization_croppedRefined_union_subset_current
            htargetNormalized
        have houter : point ∈ runtime.outer.data.refined.union := by
          simpa only [extendShading_union runtime.outer.data.selected] using
            houterAmbient
        exact refined_union_subset_shading runtime.outer.data houter
      coefficient := 4 *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)
      coefficient_one := hcoefficientOne
      plane_lipschitz := runtime.currentLipschitz
      coverBudget := coverBudget
      coverBudget_pos := hcoverBudgetPos
      cover_budget := hcoverBudget
      sqrtConstant_finite := hsqrtConstantFinite
      normalErrorTau := hnormalErrorTau
      hullTau := hhullTau }
  let currentInputs : Proposition63FourCallCurrentReceipt
      (sigma := sigma) current rho.1 :=
    { scaleFactor := scaleFactor
      scaleFactor_pos := scaleFactor_pos
      rho_aligned := rho_aligned
      fineCurrentLoss := loss index
      current_extremal := current_extremal
      current_cwa := current_cwa }
  let massInputs : Proposition63FourCallMassReceipt
      (Proposition63NestedPointCoverData.FullGrainCells.nestedCandidateIntervalBound
        rho.1 rho.1
          (8 * (planeInputs.coefficient : ℝ) * rho.1)
          (planeInputs.coefficient : ℝ) (13 ^ 3)
          (firstConstant * Kakeya.realRpowENN (tau / rho.1) (1 - sigma)))
      (proposition63DependentFinePullbackLeft fineCurrentReentry
        runtime.rich1.data runtime.pullback.retentionFactor
        (ENNReal.ofReal ((criticalInputs.cellVolumeFloor / 2) /
            (4 * (2 * sqrtRequested.1) ^ 2)) *
          (((1 : ENNReal) / 2) / (2 * (planeInputs.coverBudget : ENNReal))) *
          (runtime.nested.secondRetainedFactor *
            ((73 / 100 : ENNReal) *
              runtime.nested.reentry.normalizationWeight) *
            runtime.nested.firstRetainedFactor)))
      (proposition63DependentFinePullbackRight fineCurrentReentry
        ((runtime.nested.reentry.regularized.regularizationLoss *
            runtime.nested.prepared.preparationLoss) *
          (2 * ENNReal.ofReal (4 * rho.1))))
      delta outputCandidateLoss (loss index) planeInputs.coefficient
      spatialScale variationScale :=
    { targetConstant := internalConstant
      targetLeft := leftFactor index
      targetRight := rightFactor index
      constant_bound := by
        simpa [planeInputs]
          using hinternalConstant
      left_bound := hleftBound
      right_bound := hrightBound
      targetLeft_pos := massSchedule.left_pos index hindex
      targetLeft_finite := massSchedule.left_finite index hindex
      targetRight_finite := massSchedule.right_finite index hindex
      currentOutput := by
        rw [hnextLoss]
        exact massSchedule.loss_mono index hindex
      outputCandidateLoss_pos := by
        rw [hnextLoss]
        exact massSchedule.next_loss_pos index hindex
      restore := by
        rw [hnextLoss]
        exact massSchedule.restore index hindex
      variation := by
        dsimp only [variationScale, proposition63FourCallVariationScale]
        simpa [planeInputs] using (le_refl
          ((((4 : NNReal) *
            (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ) *
              spatialScale)) }
  rcases runtime.finalCandidate criticalInputs planeInputs currentInputs
      massInputs with
    ⟨next, hsub, hcubical, hmultiplicity, hextremal, hcwa, hcover, hmass, _⟩
  have hruntimeMap' : runtime.currentMap.planeMap =
      extension.ambient.planeMap := by
    exact hruntimeMap.trans rfl
  have hrhoNonneg : 0 ≤ rho.1 :=
    (current_extremal.delta_pos.trans_le rho.2.1).le
  have hrhoCoe : ((Real.toNNReal rho.1 : NNReal) : ℝ) = rho.1 :=
    Real.coe_toNNReal _ hrhoNonneg
  have hresolutionLower :
      grid.scale (finiteIntervalOrderedPair gridN index).1 ≤
        Real.toNNReal rho.1 := by
    exact NNReal.coe_le_coe.mp (by simpa only [hrhoCoe] using logicalR_le_rho)
  have hresolutionUpper : Real.toNNReal rho.1 ≤
      2 * grid.scale (finiteIntervalOrderedPair gridN index).1 := by
    exact NNReal.coe_le_coe.mp (by simpa only [hrhoCoe, NNReal.coe_mul,
      NNReal.coe_ofNat] using rho_le_two_logicalR)
  have hwindowEq : Real.toNNReal tau =
      grid.scale (finiteIntervalOrderedPair gridN index).2 := by
    apply NNReal.eq
    rw [Real.coe_toNNReal]
    · exact htauAlign
    · rw [htauAlign]
      positivity
  change PureWZ2IntervalCoveringAt next runtime.currentMap.planeMap rho.1
    (Real.toNNReal rho.1) (Real.toNNReal tau) internalConstant at hcover
  have hcoverAligned : PureWZ2IntervalCoveringAt next
      runtime.currentMap.planeMap
      (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
      (grid.scale (finiteIntervalOrderedPair gridN index).1)
      (grid.scale (finiteIntervalOrderedPair gridN index).2)
      (2 * internalConstant) := by
    apply pureWZ2IntervalCoveringAt_mono_query_refine_resolution_two
      logicalR_le_rho hlogicalPos hresolutionLower hresolutionUpper
    simpa only [hwindowEq] using hcover
  refine ⟨next, hsub, hcubical, hmultiplicity, ?_, ?_, ?_, ?_⟩
  · change WZ2PaperCroppedIsExtremal sigma outputCandidateLoss
      root.normalization.croppedFamily next at hextremal
    rw [← hnextLoss]
    exact hextremal
  · change WZ2PaperConvexWolffBound root.normalization.croppedFamily
      (Kakeya.realRpowENN delta (-outputCandidateLoss)) at hcwa
    rw [← hnextLoss]
    exact hcwa
  · rw [← hruntimeMap']
    exact pureWZ2IntervalCoveringAt_mono_constant base_scalar_bound hcoverAligned
  · exact hmass

end Kakeya.Assouad.PureWZ2
