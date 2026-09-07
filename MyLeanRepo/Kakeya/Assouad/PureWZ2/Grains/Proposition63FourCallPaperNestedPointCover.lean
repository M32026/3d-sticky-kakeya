import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallAncestorOuter

/-!
# Paper-ordered four-call nested point cover

This module records the paper ordering of the last three localizations.  Call
two is retained as the outer ambient, call three supplies the target-scale
point cover, and the unweakened internal kernel behind call four supplies the
square-root localization.  In particular, the target scale is not reused as
the second kappa and the public `lastThree` fourth call does not occur in this
interface.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- Data returned by the paper-ordered call2/call3/call4 construction.

Unlike `Proposition63RhoLevelFourCallData`, the nested cover is rooted on the
call-two ancestor.  The call-three cover is retained separately, so its mass
receipt is not silently multiplied into the square-root call. -/
structure Proposition63FourCallPaperNestedPointCoverData
    {delta sigma initialInputLoss normalizationLoss firstReentryLoss
      outerLoss targetReentryLoss targetNormalizationLoss targetLoss
      targetFirstLoss restoredFirstLoss
      reentryLoss sqrtStickyLoss secondLoss finalLoss tauScale sqrtScale
      incidenceBound : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource 0}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (firstReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := firstReentryLoss) initialNormalized current)
    (hfirstReentryLoss : 0 < firstReentryLoss)
    (robustScale targetScale sqrtRequested : WZ2PaperRequestedScale delta)
    (currentMap : PaperWZ1WeakPlaneMapData current incidenceBound)
    (tauConstant sqrtConstant : ENNReal)
    (targetWeightLoss nestedWeightLoss : ℝ) where
  outer : Proposition63RichTerminalStickyData
    (outputLoss := outerLoss) firstReentry.normalization.croppedRefined
    (firstReentry.normalization.toPropStickyReentryData
      hfirstReentryLoss
      firstReentry.reentry_normalization_loss_pos) robustScale
  targetReentry : Proposition63CurrentShadingReentryData
    (reentryLoss := targetReentryLoss) firstReentry.normalization
    (extendShading outer.data.selected outer.data.refined)
  targetReentryLoss_pos : 0 < targetReentryLoss
  target : Proposition63RichTerminalStickyData
    (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
    (targetReentry.normalization.toPropStickyReentryData
      targetReentryLoss_pos
      targetReentry.reentry_normalization_loss_pos) targetScale
  targetFirst : Proposition63LiftedPointCoverData
    (outputLoss := targetFirstLoss) (queryScale := delta)
    (spatialRadius := tauScale) targetReentry.normalization
    (extendShading target.data.selected target.data.refined)
    currentMap.planeMap tauConstant
  targetFirstRetainedFactor : targetFirst.retainedFactor =
    (81 / 400 : ENNReal) *
      (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
        ENNReal))⁻¹
  targetNormalization : targetReentry.reentryNormalizationLoss =
    targetNormalizationLoss
  targetCanonicalWeightExact : targetReentry.normalizationWeight =
    proposition63CanonicalReentryWeight delta targetWeightLoss
  targetCanonicalWeight : ∃ weightLoss : ℝ,
    targetReentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta weightLoss
  targetCanonicalLevel : targetReentry.levelCount =
    proposition63CanonicalNearbyLevelCount
      firstReentry.reentryNormalizationLoss
  restoredFirst : Proposition63LiftedPointCoverData
    (outputLoss := restoredFirstLoss) (queryScale := delta)
    (spatialRadius := tauScale) firstReentry.normalization
    (extendShading outer.data.selected outer.data.refined)
    currentMap.planeMap tauConstant
  restoredFirst_union : restoredFirst.state.shading.union =
    targetFirst.state.shading.union
  restoredFirstRetainedFactor : restoredFirst.retainedFactor =
    targetReentry.regularized.regularizationLoss⁻¹ *
      (((73 / 100 : ENNReal) * targetReentry.normalizationWeight) *
        (wz2PaperPureRefinementFraction delta 61 *
          targetFirst.retainedFactor))
  nested : Proposition63NestedPointCoverData
    (firstLoss := restoredFirstLoss) (reentryLoss := reentryLoss)
    (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
    (finalLoss := finalLoss) (queryScale := delta)
    (tauScale := tauScale) (sqrtScale := sqrtScale)
    firstReentry.normalization currentMap.planeMap tauConstant sqrtConstant
  nested_eq : nested.current = restoredFirst.state.shading
  nestedSqrtScale : nested.sqrtRequested.1 = sqrtRequested.1
  nestedCanonicalWeight : nested.reentry.normalizationWeight =
    proposition63CanonicalReentryWeight delta nestedWeightLoss
  nestedCanonicalWeightUpper : nested.reentry.weightUpper =
    (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
      Kakeya.realRpowENN delta 2
  nestedCanonicalLevel : nested.reentry.levelCount =
    proposition63CanonicalNearbyLevelCount
      firstReentry.reentryNormalizationLoss
  firstMass : nested.firstRetainedFactor * nested.current.mass ≤
    nested.first.shading.mass
  nestedFirstRetainedFactor : nested.firstRetainedFactor = 1
  secondMass : nested.secondRetainedFactor *
      nested.reentry.normalization.croppedRefined.mass ≤
    nested.second.shading.mass
  nestedSecondRetainedFactor : nested.secondRetainedFactor =
    (81 / 400 : ENNReal) *
      (((Nat.log 2 nested.sqrtSticky.selected.family.card + 1 : ℕ) :
        ENNReal))⁻¹ * wz2PaperPureRefinementFraction delta 61
  preparationMass : nested.second.shading.mass ≤
    nested.prepared.preparationLoss * nested.prepared.refined.shading.mass
  nestedPreparationLoss : nested.prepared.preparationLoss ≤
    proposition63UniformPreparationLoss initialNormalized.croppedFamily

/-- Package an exact call2-rooted runtime without changing either public
schedule API.  This small constructor is also useful while the scalar
absorption hypotheses are assembled by the paper-level caller. -/
noncomputable def Proposition63FourCallPaperNestedPointCoverData.ofRuntime
    {delta sigma initialInputLoss normalizationLoss firstReentryLoss
      outerLoss targetReentryLoss targetNormalizationLoss targetLoss
      targetFirstLoss restoredFirstLoss
      reentryLoss sqrtStickyLoss secondLoss finalLoss tauScale sqrtScale
      incidenceBound : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource 0}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (firstReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := firstReentryLoss) initialNormalized current)
    (hfirstReentryLoss : 0 < firstReentryLoss)
    (robustScale targetScale sqrtRequested : WZ2PaperRequestedScale delta)
    (currentMap : PaperWZ1WeakPlaneMapData current incidenceBound)
    (tauConstant sqrtConstant : ENNReal)
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) firstReentry.normalization.croppedRefined
      (firstReentry.normalization.toPropStickyReentryData
        hfirstReentryLoss
        firstReentry.reentry_normalization_loss_pos) robustScale)
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) firstReentry.normalization
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (targetFirst : Proposition63LiftedPointCoverData
      (outputLoss := targetFirstLoss) (queryScale := delta)
      (spatialRadius := tauScale) targetReentry.normalization
      (extendShading target.data.selected target.data.refined)
      currentMap.planeMap tauConstant)
    (htargetFirst : targetFirst.retainedFactor =
      (81 / 400 : ENNReal) *
        (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
          ENNReal))⁻¹)
    (htargetNormalization : targetReentry.reentryNormalizationLoss =
      targetNormalizationLoss)
    (weightLoss : ℝ)
    (hweight : targetReentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta weightLoss)
    (hlevel : targetReentry.levelCount =
      proposition63CanonicalNearbyLevelCount
        firstReentry.reentryNormalizationLoss)
    (restoredFirst : Proposition63LiftedPointCoverData
      (outputLoss := restoredFirstLoss) (queryScale := delta)
      (spatialRadius := tauScale) firstReentry.normalization
      (extendShading outer.data.selected outer.data.refined)
      currentMap.planeMap tauConstant)
    (hrestoredUnion : restoredFirst.state.shading.union =
      targetFirst.state.shading.union)
    (hrestoredFactor : restoredFirst.retainedFactor =
      targetReentry.regularized.regularizationLoss⁻¹ *
        (((73 / 100 : ENNReal) * targetReentry.normalizationWeight) *
          (wz2PaperPureRefinementFraction delta 61 *
            targetFirst.retainedFactor)))
    (nested : Proposition63NestedPointCoverData
      (firstLoss := restoredFirstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := delta)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      firstReentry.normalization currentMap.planeMap tauConstant sqrtConstant)
    (hnested : nested.current = restoredFirst.state.shading)
    (hsqrt : nested.sqrtRequested.1 = sqrtRequested.1)
    (nestedWeightLoss : ℝ)
    (hnestedWeight : nested.reentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta nestedWeightLoss)
    (hnestedWeightUpper : nested.reentry.weightUpper =
      (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2)
    (hnestedLevel : nested.reentry.levelCount =
      proposition63CanonicalNearbyLevelCount
        firstReentry.reentryNormalizationLoss)
    (hnestedFirstFactor : nested.firstRetainedFactor = 1)
    (hnestedSecondFactor : nested.secondRetainedFactor =
      (81 / 400 : ENNReal) *
        (((Nat.log 2 nested.sqrtSticky.selected.family.card + 1 : ℕ) :
          ENNReal))⁻¹ * wz2PaperPureRefinementFraction delta 61)
    (hnestedPreparation : nested.prepared.preparationLoss ≤
      proposition63UniformPreparationLoss initialNormalized.croppedFamily) :
    Proposition63FourCallPaperNestedPointCoverData
      (outerLoss := outerLoss) (targetReentryLoss := targetReentryLoss)
      (targetNormalizationLoss := targetNormalizationLoss)
      (targetLoss := targetLoss) (targetFirstLoss := targetFirstLoss)
      (restoredFirstLoss := restoredFirstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (tauScale := tauScale)
      (sqrtScale := sqrtScale) firstReentry hfirstReentryLoss robustScale
      targetScale sqrtRequested currentMap tauConstant sqrtConstant
      weightLoss nestedWeightLoss := by
  exact {
    outer := outer
    targetReentry := targetReentry
    targetReentryLoss_pos := htargetReentryLoss
    target := target
    targetFirst := targetFirst
    targetFirstRetainedFactor := htargetFirst
    targetNormalization := htargetNormalization
    targetCanonicalWeightExact := hweight
    targetCanonicalWeight := ⟨weightLoss, hweight⟩
    targetCanonicalLevel := hlevel
    restoredFirst := restoredFirst
    restoredFirst_union := hrestoredUnion
    restoredFirstRetainedFactor := hrestoredFactor
    nested := nested
    nested_eq := hnested
    nestedSqrtScale := hsqrt
    nestedCanonicalWeight := hnestedWeight
    nestedCanonicalWeightUpper := hnestedWeightUpper
    nestedCanonicalLevel := hnestedLevel
    firstMass := nested.first_retained
    nestedFirstRetainedFactor := hnestedFirstFactor
    secondMass := nested.second_retained
    nestedSecondRetainedFactor := hnestedSecondFactor
    preparationMass := nested.prepared.mass_retention
    nestedPreparationLoss := hnestedPreparation
  }

/-- Paper-ordered rho-level producer. Call two is the persistent ancestor,
call three is run at the interval target scale, and call four is replaced by
its unweakened internal kernel at the square-root scale. -/
theorem proposition63_rho_level_four_call_paper_nested_point_cover_of_absorptions
    {delta sigma initialInputLoss normalizationLoss firstReentryLoss
      firstStageDensityLoss firstStageWeightLoss outerExtremalLoss
      paperRobustExponent tau epsilon₁ epsilon₃ parentLoss firstLoss
      ancestorRestoredLoss nextWeightLoss outputLoss discreteBudget tailBudget
      sigmaBudget secondLoss middleLoss finalLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource 0}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (firstReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := firstReentryLoss) initialNormalized current)
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss)
    (kernel : Proposition63RichInternalKernelScheduleData sigma outputLoss
      discreteBudget tailBudget sigmaBudget schedule.fourth)
    (hfirstReentryLoss : firstReentryLoss = schedule.second.sourceLoss)
    (hfirstNormalizationLoss : firstReentry.reentryNormalizationLoss =
      schedule.second.normalizationLoss)
    (hdeltaFirst : delta ≤ schedule.second.delta₀)
    (robustScale : WZ2PaperRequestedScale delta)
    (hrobustLower : Real.rpow delta
      (1 - schedule.secondOutputLoss) ≤ robustScale.1)
    (hrobustUpper : robustScale.1 ≤
      Real.rpow delta schedule.secondOutputLoss)
    (hdeltaSecond : delta ≤ schedule.third.delta₀)
    (firstStageAbsorption : Proposition63CurrentReentryAbsorptionData
      firstReentryLoss firstReentry.reentryNormalizationLoss
      firstStageDensityLoss outerExtremalLoss firstStageWeightLoss
      schedule.third.sourceLoss
      (proposition63CanonicalNearbyLevelCount
        firstReentry.reentryNormalizationLoss))
    (hdeltaFirstStage : delta ≤ firstStageAbsorption.delta₀)
    (hsourceOuter : firstReentry.reentryNormalizationLoss ≤
      outerExtremalLoss)
    (houterExtremalLoss : 0 < outerExtremalLoss)
    (houterRetention : Kakeya.realRpowENN delta outerExtremalLoss ≤
      wz2PaperPureRefinementFraction delta 61 *
        Kakeya.realRpowENN delta firstReentry.reentryNormalizationLoss)
    (houterTargetReentry : outerExtremalLoss ≤ schedule.third.sourceLoss)
    (targetScale : WZ2PaperRequestedScale delta)
    (htargetLower : Real.rpow delta
      (1 - schedule.thirdOutputLoss) ≤ targetScale.1)
    (htargetUpper : targetScale.1 ≤
      Real.rpow delta schedule.thirdOutputLoss)
    {incidenceBound : ℝ}
    (currentMap : PaperWZ1WeakPlaneMapData current incidenceBound)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient currentMap.planeMap)
    (firstGridAbsorption : Proposition63RobustGridPruningAbsorptionData
      schedule.third.normalizationLoss epsilon₁)
    (firstCrossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        paperRobustExponent schedule.secondOutputLoss
        schedule.third.normalizationLoss firstStageWeightLoss 4
        (proposition63CanonicalNearbyLevelCount
          firstReentry.reentryNormalizationLoss))
    (hdeltaFirstGrid : delta ≤ firstGridAbsorption.delta₀)
    (hdeltaFirstCross : delta ≤ firstCrossAbsorption.delta₀)
    (hrobustScale : robustScale.1 =
      Real.rpow delta paperRobustExponent)
    (hdeltaTau : delta ≤ tau) (htau : 0 < tau) (htauOne : tau ≤ 1)
    (firstBoundaryAbsorption : Proposition63RobustBoundaryAbsorptionData
      schedule.thirdOutputLoss schedule.third.normalizationLoss)
    (hdeltaFirstBoundary : delta ≤ firstBoundaryAbsorption.delta₀)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hfirstKappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
    (htargetSmall : targetScale.1 ≤ 1 / 12)
    (htargetTau : targetScale.1 ≤ 3 * tau)
    (htauSq : tau ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale → scale ≤ logScale →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (firstConstant : ENNReal)
    (hfirstArithmetic : ENNReal.ofReal
      ((proposition63RobustTauTotalVolume delta sigma
          schedule.third.normalizationLoss schedule.thirdOutputLoss
          targetScale.1 tau /
          (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
            tau ^ 2 / 200)) *
        (2 * proposition63DependentSlabWidth delta tau incidenceBound
          coefficient / delta + 2)) ≤
      firstConstant * Kakeya.realRpowENN (tau / delta) (1 - sigma))
    (hnormalizationParent : schedule.third.normalizationLoss ≤ parentLoss)
    (hparentRetention : Kakeya.realRpowENN delta parentLoss ≤
      wz2PaperPureRefinementFraction delta 61 *
        Kakeya.realRpowENN delta schedule.third.normalizationLoss)
    (hparentOutput : parentLoss ≤ firstLoss) (hfirstLoss : 0 < firstLoss)
    (firstRestoreAbsorption :
      Proposition63RobustPointCoverRestorationAbsorptionData
        parentLoss firstLoss 0)
    (hdeltaFirstRestore : delta ≤ firstRestoreAbsorption.delta₀)
    (houterAncestor : outerExtremalLoss ≤ ancestorRestoredLoss)
    (hancestorRestoredLoss : 0 < ancestorRestoredLoss)
    (ancestorDensityLiftAbsorption :
      Proposition63ReentryDensityLiftAbsorptionData firstStageWeightLoss
        firstLoss ancestorRestoredLoss
        (proposition63CanonicalNearbyLevelCount
          firstReentry.reentryNormalizationLoss))
    (hdeltaAncestorDensityLift :
      delta ≤ ancestorDensityLiftAbsorption.delta₀)
    (ancestorReentryAbsorption : Proposition63CurrentReentryAbsorptionData
      firstReentryLoss firstReentry.reentryNormalizationLoss
      firstStageDensityLoss ancestorRestoredLoss nextWeightLoss
      schedule.fourth.sourceLoss
      (proposition63CanonicalNearbyLevelCount
        firstReentry.reentryNormalizationLoss))
    (hdeltaAncestorReentry : delta ≤ ancestorReentryAbsorption.delta₀)
    (hancestorFirst : ancestorRestoredLoss ≤ schedule.fourth.sourceLoss)
    (hdeltaFourth : delta ≤ kernel.internalSchedule.delta₀)
    (sqrtRequested : WZ2PaperRequestedScale delta)
    (hsqrtLower : Real.rpow delta
      (1 - kernel.internalLoss) ≤ sqrtRequested.1)
    (hsqrtUpper : sqrtRequested.1 ≤
      Real.rpow delta kernel.internalLoss)
    (hsqrtOne : sqrtRequested.1 ≤ 1)
    (secondBoundaryAbsorption : Proposition63RobustBoundaryAbsorptionData
      kernel.internalLoss schedule.fourth.normalizationLoss)
    (hdeltaSecondBoundary : delta ≤ secondBoundaryAbsorption.delta₀)
    (secondGridAbsorption : Proposition63RobustGridPruningAbsorptionData
      schedule.fourth.normalizationLoss epsilon₁)
    (hdeltaSecondGrid : delta ≤ secondGridAbsorption.delta₀)
    (secondCrossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        paperRobustExponent schedule.secondOutputLoss
        schedule.fourth.normalizationLoss nextWeightLoss 4
        (proposition63CanonicalNearbyLevelCount
          firstReentry.reentryNormalizationLoss))
    (hdeltaSecondCross : delta ≤ secondCrossAbsorption.delta₀)
    (hsqrtSmall : sqrtRequested.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (hsqrtSq : sqrtRequested.1 ^ 2 ≤ 4 * delta)
    (finalConstant : ENNReal)
    (hfinalArithmetic : ENNReal.ofReal
      ((proposition63RobustTauTotalVolume delta sigma
          schedule.fourth.normalizationLoss kernel.internalLoss
          sqrtRequested.1 sqrtRequested.1 /
          (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
            sqrtRequested.1 ^ 2 / 200)) *
        (2 * proposition63DependentSlabWidth delta sqrtRequested.1
          incidenceBound coefficient / delta + 2)) ≤
      finalConstant * Kakeya.realRpowENN
        (sqrtRequested.1 / delta) (1 - sigma))
    (hnormalizationSecond : schedule.fourth.normalizationLoss ≤ secondLoss)
    (hsecondLoss : 0 < secondLoss)
    (secondRestoreAbsorption :
      Proposition63RobustPointCoverRestorationAbsorptionData
        schedule.fourth.normalizationLoss secondLoss 61)
    (hdeltaSecondRestore : delta ≤ secondRestoreAbsorption.delta₀)
    (hsecondMiddle : secondLoss ≤ middleLoss)
    (hmiddleLoss : 0 < middleLoss)
    (multiplicityAbsorption : Proposition63FullGrainLogAbsorptionData
      secondLoss middleLoss)
    (hdeltaMultiplicity : delta ≤ multiplicityAbsorption.delta₀)
    (hbalancingBoundary : 2 * 24000000 *
      (Kakeya.realRpowENN delta (-middleLoss) *
          wz2PaperBoundaryGeometryConstant + 1) *
      ENNReal.ofReal (Real.sqrt (delta / sqrtRequested.1)) <
        Kakeya.realRpowENN delta middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss) (hfinalLoss : 0 < finalLoss)
    (balancingAbsorption : Proposition63FullGrainBalancingAbsorptionData
      middleLoss finalLoss)
    (hdeltaBalancing : delta ≤ balancingAbsorption.delta₀) :
    Nonempty (Proposition63FourCallPaperNestedPointCoverData
      (outerLoss := schedule.secondOutputLoss)
      (targetReentryLoss := schedule.third.sourceLoss)
      (targetNormalizationLoss := schedule.third.normalizationLoss)
      (targetLoss := schedule.thirdOutputLoss)
      (targetFirstLoss := firstLoss)
      (restoredFirstLoss := ancestorRestoredLoss)
      (reentryLoss := schedule.fourth.sourceLoss)
      (sqrtStickyLoss := kernel.internalLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (tauScale := tau)
      (sqrtScale := sqrtRequested.1) firstReentry
      (by rw [hfirstReentryLoss]; exact schedule.second.sourceLoss_pos)
      robustScale targetScale sqrtRequested currentMap
      (firstConstant * Kakeya.realRpowENN (tau / delta) (1 - sigma))
      (finalConstant * Kakeya.realRpowENN
        (sqrtRequested.1 / delta) (1 - sigma)) firstStageWeightLoss
      nextWeightLoss) := by
  let root : Proposition63RootNormalizationData
      (outputLoss := firstReentry.reentryNormalizationLoss)
      firstReentry.ordinarySource 0 firstStageDensityLoss :=
    Proposition63RootNormalizationData.ofNormalization
      firstReentry.normalization
      (firstStageAbsorption.density_absorb
        firstReentry.reentry_extremal.delta_pos hdeltaFirstStage)
  have ambientTwo := firstStageAbsorption.ambient_two
    firstReentry.reentry_extremal.delta_pos hdeltaFirstStage
  have htwoNormalization : 2 * firstReentry.reentryNormalizationLoss ≤
      schedule.third.sourceLoss := by
    rw [hfirstNormalizationLoss]
    linarith [schedule.second.normalizationLoss_lt_output,
      schedule.secondOutputLoss_eq, schedule.secondOutputLoss_lt_thirdSource]
  rcases root.finiteNearbySchedule
      firstReentry.reentry_normalization_loss_pos ambientTwo
      htwoNormalization with ⟨targetNearbySchedule⟩
  have regularizationAbsorb := firstStageAbsorption.regularization_absorb
    firstReentry.normalization rfl targetNearbySchedule rfl rfl
    firstReentry.reentry_extremal.delta_pos hdeltaFirstStage
  rcases proposition63_nested_two_rich_runtime firstReentry schedule.second
      hfirstReentryLoss hfirstNormalizationLoss hdeltaFirst hrobustLower
      hrobustUpper schedule.third hdeltaSecond
      (firstStageAbsorption.density_absorb
        firstReentry.reentry_extremal.delta_pos hdeltaFirstStage)
      targetNearbySchedule ambientTwo hsourceOuter houterExtremalLoss
      houterRetention houterTargetReentry
      (firstStageAbsorption.canonical_weight_absorb
        firstReentry.reentry_extremal.delta_pos hdeltaFirstStage)
      (firstStageAbsorption.trace_fixed_absorb
        firstReentry.reentry_extremal.delta_pos hdeltaFirstStage)
      (firstStageAbsorption.paper_fixed_absorb
        firstReentry.reentry_extremal.delta_pos hdeltaFirstStage)
      regularizationAbsorb
      (hdeltaFirstStage.trans firstStageAbsorption.delta₀_le_tiny |>.trans
        (by norm_num))
      htargetLower htargetUpper with
    ⟨outer, targetReentry, htargetWeight, htargetWeightUpper, htargetLevel,
      htargetNormalization, ⟨target⟩⟩
  let firstNormalizedMap := firstReentry.normalizedPlaneMap currentMap
  let outerMap := outer.terminalPlaneMap firstNormalizedMap
  let outerAmbientMap := outer.ambientTerminalPlaneMap outerMap
  let targetNormalizedMap := targetReentry.normalizedPlaneMap outerAmbientMap
  let targetMap := target.terminalPlaneMap targetNormalizedMap
  have htargetLipschitz : LipschitzWith coefficient targetMap.planeMap := by
    change LipschitzWith coefficient currentMap.planeMap
    exact hplaneLipschitz
  have hfirstRestoreActual := firstRestoreAbsorption.absorbTargetAmbient
    targetReentry.normalization target.data.selected hdeltaFirstRestore
  have htauLower : Real.rpow delta (1 - schedule.thirdOutputLoss) ≤ 3 * tau :=
    htargetLower.trans htargetTau
  have hdeltaFirstGridActual := firstBoundaryAbsorption.grid_le
    targetReentry.reentry_extremal.delta_pos hdeltaFirstBoundary htau
      htauLower
  have hfirstPeriodic := firstBoundaryAbsorption.periodic
    targetReentry.reentry_extremal.delta_pos hdeltaFirstBoundary htau
      htauLower
  have hfirstBoundaryScalar := firstBoundaryAbsorption.absorb
    targetReentry.reentry_extremal.delta_pos hdeltaFirstBoundary htau
      htauLower
  have firstRobustPackage :=
    proposition63_first_robust_target_ambient_of_absorptions outer
      targetReentry schedule.third.sourceLoss_pos target
      htargetNormalization firstGridAbsorption firstCrossAbsorption
      hdeltaFirstGrid hdeltaFirstCross hrobustScale htargetWeight
      htargetWeightUpper htargetLevel targetMap htargetLipschitz hdeltaTau
      hdeltaFirstGridActual htau htauOne hfirstPeriodic
      (by simpa only [htargetNormalization] using hfirstBoundaryScalar)
      hrobustSmall hfirstKappa htargetSmall
      (hdeltaSmall.trans (by norm_num)) htargetTau htauSq hsigma hsigmaOne
      hepsilon₁ hepsilon₃ hepsilonSum logScale hdeltaLog hlog haxis
      firstConstant (by simpa only [htargetNormalization] using
        hfirstArithmetic)
      (by simpa only [htargetNormalization] using hnormalizationParent)
      (by simpa only [htargetNormalization] using hparentRetention)
      hparentOutput hfirstLoss hfirstRestoreActual
  rcases firstRobustPackage with ⟨firstRobust⟩
  let firstRobustFixed := firstRobust
  have houterAmbientLipschitz : LipschitzWith coefficient
      outerAmbientMap.planeMap := by
    change LipschitzWith coefficient currentMap.planeMap
    exact hplaneLipschitz
  have htwoAncestor : 2 * firstReentry.reentryNormalizationLoss ≤
      schedule.fourth.sourceLoss := htwoNormalization.trans <| by
    linarith [schedule.third.sourceLoss_le_half,
      schedule.third.normalizationLoss_lt_output,
      schedule.thirdOutputLoss_lt_fourthSource]
  let hschedule :=
    proposition63_rich_three_call_schedule_of_four_call_kernel schedule kernel
  have hkernelSource : schedule.fourth.sourceLoss =
      kernel.internalSchedule.sourceLoss := by
    simpa only [Proposition63RichStickyKernelScheduleData.mono_loss] using
      congrArg Proposition63RichStickyKernelScheduleData.sourceLoss
        kernel.public_eq
  have hkernelNormalization : schedule.fourth.normalizationLoss =
      kernel.internalSchedule.normalizationLoss := by
    simpa only [Proposition63RichStickyKernelScheduleData.mono_loss] using
      congrArg Proposition63RichStickyKernelScheduleData.normalizationLoss
        kernel.public_eq
  have hkernelSourceSchedule : schedule.fourth.sourceLoss =
      hschedule.third.sourceLoss := by
    change schedule.fourth.sourceLoss = kernel.internalSchedule.sourceLoss
    exact hkernelSource
  have hkernelNormalizationSchedule : schedule.fourth.normalizationLoss =
      hschedule.third.normalizationLoss := by
    change schedule.fourth.normalizationLoss =
      kernel.internalSchedule.normalizationLoss
    exact hkernelNormalization
  have hdeltaKernelSchedule : delta ≤ hschedule.third.delta₀ := by
    change delta ≤ kernel.internalSchedule.delta₀
    exact hdeltaFourth
  rcases proposition63_four_call_complete_sqrt_on_call2_ancestor_with_restored_first
      outer targetReentry schedule.third.sourceLoss_pos target outerAmbientMap
      houterAmbientLipschitz
      (firstConstant * Kakeya.realRpowENN (tau / delta) (1 - sigma))
      firstRobustFixed.first outerExtremalLoss
      (lt_of_le_of_lt hdeltaSmall (by norm_num)) hsourceOuter
      houterRetention houterAncestor hancestorRestoredLoss
      (targetReentry.densityLift_of_absorption
        ancestorDensityLiftAbsorption hdeltaAncestorDensityLift
        htargetWeight htargetWeightUpper htargetLevel)
      ancestorReentryAbsorption hdeltaAncestorReentry
      firstReentry.reentry_normalization_loss_pos htwoAncestor hancestorFirst
      schedule.fourth.normalizationLoss_pos schedule.fourth.sourceLoss_le_half
      hschedule hkernelSourceSchedule hkernelNormalizationSchedule
      hdeltaKernelSchedule
      sqrtRequested hsqrtLower hsqrtUpper
      hsqrtOne secondBoundaryAbsorption hdeltaSecondBoundary
      secondGridAbsorption hdeltaSecondGrid secondCrossAbsorption
      hdeltaSecondCross hrobustScale hrobustSmall hfirstKappa hsqrtSmall
      hdeltaSmall hsqrtSq hsigma hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum
      logScale hdeltaLog hlog haxis finalConstant hfinalArithmetic
      hnormalizationSecond hsecondLoss secondRestoreAbsorption
      hdeltaSecondRestore hsecondMiddle hmiddleLoss multiplicityAbsorption
      hdeltaMultiplicity hbalancingBoundary hmiddleFinal hfinalLoss
      balancingAbsorption hdeltaBalancing with ⟨witness⟩
  have hnestedPreparation : witness.nested.prepared.preparationLoss ≤
      proposition63UniformPreparationLoss initialNormalized.croppedFamily := by
    refine witness.nestedPreparationLoss.trans ?_
    have hcard : firstReentry.normalization.croppedFamily.card ≤
        initialNormalized.croppedFamily.card := by
      rw [firstReentry.normalization_croppedFamily]
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        firstReentry.regularized.selected.embedding
        firstReentry.regularized.selected.embedding.injective
    have hlog :
        ((Nat.log 2 firstReentry.normalization.croppedFamily.card + 1 : ℕ) :
            ENNReal) ≤
          ((Nat.log 2 initialNormalized.croppedFamily.card + 1 : ℕ) :
            ENNReal) := by
      exact_mod_cast Nat.add_le_add_right (Nat.log_mono_right hcard) 1
    unfold proposition63UniformPreparationLoss
    exact mul_le_mul_right' hlog _
  refine ⟨Proposition63FourCallPaperNestedPointCoverData.ofRuntime
    firstReentry (by rw [hfirstReentryLoss]; exact schedule.second.sourceLoss_pos)
    robustScale targetScale sqrtRequested currentMap
    (firstConstant * Kakeya.realRpowENN (tau / delta) (1 - sigma))
    (finalConstant * Kakeya.realRpowENN
      (sqrtRequested.1 / delta) (1 - sigma))
    outer targetReentry schedule.third.sourceLoss_pos target
    firstRobustFixed.first firstRobustFixed.firstRetainedFactor
    firstRobust.target_normalization_loss firstStageWeightLoss
    firstRobust.targetCanonicalWeight firstRobust.targetCanonicalLevel
    witness.restoredFirst witness.restored_union witness.restored_factor
    witness.nested witness.nested_current_eq
    witness.nested.sqrt_requested_eq nextWeightLoss
    witness.nestedCanonicalWeight
    witness.nestedCanonicalWeightUpper
    witness.nestedCanonicalLevel
    witness.nestedFirstRetainedFactor
    witness.nestedSecondRetainedFactor
    hnestedPreparation⟩

end Kakeya.Assouad.PureWZ2
