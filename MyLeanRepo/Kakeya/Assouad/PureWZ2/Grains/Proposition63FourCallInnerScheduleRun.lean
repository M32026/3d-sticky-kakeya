import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallOrderedPairFrozenStep

/-!
# Execute the Proposition 6.3 four-call inner schedule

Every ordered pair chooses its complete scalar and schedule package before the
runtime callback exposes the current shading.  The iterator then executes the
resulting concrete four-call transition.  This is only the M6 execution layer;
the standalone one-query export belongs to M7.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- A dependent pre-runtime choice for one ordered pair.  All losses and both
rich schedules that may vary with the pair are fields of this package. -/
structure Proposition63FourCallOrderedPairFrozenChoiceAt
    {delta sigma inputLoss normalizationLoss rootDensityLoss incidence
      discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        rootDensityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (loss : ℕ → ℝ) (leftFactor rightFactor : ℕ → ENNReal)
    (sourceCoefficient : NNReal) (index : ℕ) where
  outputLoss : ℝ
  rhoDensityLoss : ℝ
  firstStageDensityLoss : ℝ
  secondReentryDensityLoss : ℝ
  rhoWeightLoss : ℝ
  firstStageWeightLoss : ℝ
  currentWeightLoss : ℝ
  outerExtremalLoss : ℝ
  robustExponent : ℝ
  epsilon₁ : ℝ
  epsilon₃ : ℝ
  parentLoss : ℝ
  firstLoss : ℝ
  nextWeightLoss : ℝ
  secondLoss : ℝ
  middleLoss : ℝ
  finalLoss : ℝ
  schedule : Proposition63RichFourCallScheduleData sigma outputLoss
  currentSchedule : WZ2PaperPureFiniteNearbyScheduleData
    (fine := root.normalization.croppedFamily)
    (Kakeya.realRpowENN delta (-normalizationLoss))
    (Kakeya.realRpowENN delta (-schedule.first.sourceLoss))
    (proposition63CanonicalNearbyLevelCount normalizationLoss)
  frozen : Proposition63FourCallOrderedPairFrozenInputsAt
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
    currentSchedule sourceCoefficient index

/-- Turn pair-dependent frozen choices into the exact runtime transition.
The callback's current state is used only after the corresponding choice has
been fixed. -/
theorem proposition63_four_call_ordered_pair_step_of_frozen_choices
    {delta sigma inputLoss normalizationLoss rootDensityLoss incidence
      discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
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
    (choices : ∀ index,
      index < (finiteIntervalOrderedPairs gridN).length →
      Nonempty (Proposition63FourCallOrderedPairFrozenChoiceAt
        (incidence := incidence) root grid loss leftFactor rightFactor
        sourceCoefficient index)) :
    Proposition63FourCallOrderedPairStep grid
      root.normalization.croppedRefined extension.ambient.planeMap loss
      leftFactor rightFactor := by
  intro index hindex current current_sub current_cubical _currentMultiplicity
    current_extremal current_cwa _prefixMass _currentMass
  rcases choices index hindex with ⟨choice⟩
  let f := choice.frozen
  exact proposition63_four_call_ordered_pair_actual_of_scalar_bounds
    (rootDensityLoss := rootDensityLoss)
    (rhoDensityLoss := choice.rhoDensityLoss)
    (firstStageDensityLoss := choice.firstStageDensityLoss)
    (secondReentryDensityLoss := choice.secondReentryDensityLoss)
    (rhoWeightLoss := choice.rhoWeightLoss)
    (firstStageWeightLoss := choice.firstStageWeightLoss)
    root grid loss leftFactor rightFactor massSchedule sourceMap
    sourceCoefficient extension hindex current choice.schedule
    choice.currentSchedule f.ambient_two current_sub current_cubical
    current_extremal current_cwa f.currentLoss_le_reentry f.currentLoss_pos
    f.reentryLoss_le_half f.canonical_weight_absorb f.trace_fixed_absorb
    f.paper_fixed_absorb f.regularization_absorb f.delta_small
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
    f.htargetSmall f.htargetTau f.htauSq f.hsigma f.hsigmaOne f.hepsilon₁
    f.hepsilon₃ f.hepsilonSum f.logScale f.hdeltaLog f.hlog f.haxis
    f.firstConstant f.hfirstArithmetic f.hnormalizationParent
    f.hparentRetention f.hparentOutput f.hfirstLoss f.firstRestoreAbsorption
    f.hdeltaFirstRestore f.secondReentryAbsorption f.hdeltaSecondReentry
    f.hfirstReentry f.hdeltaFourth f.sqrtRequested f.hsqrtLower f.hsqrtUpper
    f.hsqrtOne f.secondBoundaryAbsorption f.hdeltaSecondBoundary
    f.secondGridAbsorption f.hdeltaSecondGrid f.secondCrossAbsorption
    f.hdeltaSecondCross f.htargetRobustSmall f.htargetKappa f.hsqrtSmall
    f.hsqrtSq f.finalConstant f.hfinalArithmetic f.hnormalizationSecond
    f.hsecondLoss f.secondRestoreAbsorption f.hdeltaSecondRestore
    f.hsecondMiddle f.hmiddleLoss f.multiplicityAbsorption
    f.hdeltaMultiplicity f.hbalancingBoundary f.hmiddleFinal f.hfinalLoss
    f.balancingAbsorption f.hdeltaBalancing f.floorLoss f.structuralBudget
    f.cellVolumeFloor f.outputCandidateLoss f.spatialScale f.critical
    f.coarseCritical f.finalStructural f.criticalTraceAbsorption
    f.cellVolumeFloor_pos f.cellBudget
    f.tau_le_sqrt f.sqrtScale_eq f.hcoefficientOne f.coverBudget
    f.hcoverBudgetPos f.hcoverBudget f.hsqrtConstantFinite f.hnormalErrorTau
    f.hhullTau f.scales.scaleFactor f.scales.scaleFactor_pos
    f.scales.rhoHat_aligned f.scales.logicalR_le_rhoHat
    f.scales.rhoHat_le_two_logicalR f.scales.tau_eq f.hnextLoss
    f.alignedAbsorption f.hdeltaAlignedAbsorption f.nestedIntervalAbsorption
    f.hdeltaNestedInterval f.uniformLevel f.hleftFactor f.hrightFactor
    f.hcurrentLevel f.hnestedLevel f.hfourRho

/-- Execute the complete inner ordered-pair schedule and return exactly the
output of `Proposition63InnerIntervalGridData.runIteration`. -/
theorem proposition63_four_call_inner_schedule_run
    {delta sigma inputLoss normalizationLoss rootDensityLoss incidence
      discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
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
    (choices : ∀ index,
      index < (finiteIntervalOrderedPairs gridN).length →
      Nonempty (Proposition63FourCallOrderedPairFrozenChoiceAt
        (incidence := incidence) root grid loss leftFactor rightFactor
        sourceCoefficient index))
    (hsourceCubical :
      WZ1PaperIsCubicalShading root.normalization.croppedRefined)
    (hsourceExtremal : WZ2PaperCroppedIsExtremal sigma (loss 0)
      root.normalization.croppedFamily root.normalization.croppedRefined)
    (hsourceCWA : WZ2PaperConvexWolffBound
      root.normalization.croppedFamily
      (Kakeya.realRpowENN delta (-(loss 0))))
    (hsourceMass : 0 < root.normalization.croppedRefined.mass)
    (hfinalLoss : loss (finiteIntervalOrderedPairs gridN).length =
      gridOutputLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    ∃ data : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := gridOutputLoss)
        (rho := queryScale) (Y := root.normalization.croppedRefined)
        (fun point => extension.ambient.planeMap point),
      (∀ point ∈ data.shading.union,
        data.shading.pointMultiplicity point =
          root.normalization.croppedRefined.pointMultiplicity point) ∧
      (∏ index ∈ Finset.range (finiteIntervalOrderedPairs gridN).length,
          leftFactor index) * root.normalization.croppedRefined.mass ≤
        (∏ index ∈ Finset.range (finiteIntervalOrderedPairs gridN).length,
          rightFactor index) * data.shading.mass ∧
      0 < data.shading.mass := by
  let step := proposition63_four_call_ordered_pair_step_of_frozen_choices
    root rootInput grid loss leftFactor rightFactor massSchedule sourceMap
    sourceCoefficient extension choices
  exact grid.runIteration root.normalization.croppedRefined
    extension.ambient.planeMap loss leftFactor rightFactor hsourceCubical
    hsourceExtremal hsourceCWA hsourceMass massSchedule.left_pos step hfinalLoss
    extension.ambient.unit hsourceExtremal.delta_pos
    hsourceExtremal.delta_le_one hsigma hsigmaOne

end Kakeya.Assouad.PureWZ2
