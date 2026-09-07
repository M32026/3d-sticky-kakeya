import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperFrozenChoiceProducer

/-!
# Paper-ordered four-call runtime assembly

This module joins the call-one source-witness prefix to the frozen paper-order
producer.  All call-one scalar hypotheses are recovered from the global frozen
receipts, while the exact runtime re-entry and its ambient plane map are kept
in the result.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- The paper nested-cover type selected by the frozen producer for an exact
call-one current re-entry and plane map. -/
abbrev Proposition63FourCallPaperNestedResult
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
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    {rhoInputLoss rhoNormalizationLoss : ℝ}
    {rhoSource : PureWZ2ExtremalConfiguration sigma rhoInputLoss
      scales.rhoHat.1}
    (rhoNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := rhoNormalizationLoss) rhoSource 0)
    (rhoCurrent : WZ1PaperTubeShading rhoNormalized.croppedFamily)
    (firstReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := (backward.seed index hindex).schedule.second.sourceLoss)
      rhoNormalized rhoCurrent)
    (currentMap : PaperWZ1WeakPlaneMapData rhoCurrent
      (proposition63DependentCoarseIncidence scales.rhoHat.1 incidence
        (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)))) :=
  let seed := backward.seed index hindex
  let paperScales := scales.choicePaperScalePackage seed
    global.discreteLoss_lt_half
  let sqrtPackage := scales.choiceSqrtScalePackage
    seed.fourthKernel.internalLoss seed.fourthKernel.internalLoss_pos
    (seed.fourthKernel.internalLoss_lt_discrete.le.trans
      global.discreteLoss_lt_half.le)
    (global.rho_small index hindex scales)
  let publicSqrt := scales.choiceSqrtScalePackage
    (backward.loss (index + 1))
    (backward.loss_pos (index + 1) (by omega))
    ((backward.loss_le_terminal (index + 1) (by omega)).trans
      global.outputLoss_le_half)
    (global.rho_small index hindex scales)
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
    scales.rhoHat_le_tau seed.sigma_lt_one
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
    sqrtPackage.sqrtRequested.property.1 seed.sigma_lt_one.le
  Proposition63FourCallPaperNestedPointCoverData
    (outerLoss := seed.schedule.secondOutputLoss)
    (targetReentryLoss := seed.schedule.third.sourceLoss)
    (targetNormalizationLoss := seed.schedule.third.normalizationLoss)
    (targetLoss := seed.schedule.thirdOutputLoss)
    (targetFirstLoss := seed.firstLoss)
    (restoredFirstLoss := seed.ancestorRestoredLoss)
    (reentryLoss := seed.schedule.fourth.sourceLoss)
    (sqrtStickyLoss := seed.fourthKernel.internalLoss)
    (secondLoss := seed.secondLoss) (finalLoss := seed.finalLoss)
    (tauScale := scales.tau) (sqrtScale := Real.sqrt scales.rhoHat.1)
    firstReentry seed.schedule.second.sourceLoss_pos
    paperScales.robustRequested paperScales.targetRequested
    sqrtPackage.sqrtRequested currentMap
    (firstChoice.firstConstant *
      Kakeya.realRpowENN (scales.tau / scales.rhoHat.1) (1 - sigma))
    (finalChoice.finalConstant * Kakeya.realRpowENN
      (Real.sqrt scales.rhoHat.1 / scales.rhoHat.1) (1 - sigma))
    seed.firstStageWeightLoss
    seed.nextWeightLoss

/-- Call-one witnesses, the exact current runtime, and the paper-ordered
call2/call3/call4 nested cover, all tied to one ambient plane map. -/
structure Proposition63FourCallPaperRuntimeAssemblyData
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
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    {family : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading family}
    (fineReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) fineShading normalizationExponent
      (backward.seed index hindex).schedule.first.sourceLoss
      (backward.seed index hindex).schedule.first.normalizationLoss)
    (rootAxialWindow : ∀ sourceIndex point,
      point ∈ fineReentry.geometry.frame ''
          fineReentry.geometry.ordinaryRefined.carrier sourceIndex →
        |point (2 : Fin 3)| ≤ 1 / 8)
    {sourceMap : PaperWZ1WeakPlaneMapData fineShading incidence}
    (extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient) where
  rich1 : Proposition63RichTerminalStickyData
    (outputLoss := (backward.seed index hindex).schedule.firstOutputLoss)
    fineShading fineReentry scales.rhoHat
  currentResult : Proposition63SourceWitnessCurrentReentryResult
    (nextSourceLoss := (backward.seed index hindex).schedule.second.sourceLoss)
    (nextNormalizationLoss :=
      (backward.seed index hindex).schedule.second.normalizationLoss)
    (incidence := incidence)
    (weightLoss := (backward.seed index hindex).rhoWeightLoss)
    ((backward.seed index hindex).schedule.callOneRhoRootNormalization
      rich1 rootAxialWindow) rich1.terminal.sourceWitness.shading
    sourceCoefficient extension.ambient.planeMap
  paperNested : Proposition63FourCallPaperNestedResult K backward root grid
    leftFactor rightFactor sourceCoefficient global index hindex scales
    (rhoInputLoss :=
      (backward.seed index hindex).schedule.second.sourceLoss / 16)
    (rhoNormalizationLoss :=
      (backward.seed index hindex).schedule.second.sourceLoss / 4)
    (rhoSource :=
      ((backward.seed index hindex).schedule.callOneRhoRootReentry
        rich1 rootAxialWindow).ordinarySource)
    (rhoNormalized :=
      (backward.seed index hindex).schedule.callOneRhoRootNormalization
        rich1 rootAxialWindow)
    rich1.terminal.sourceWitness.shading
    currentResult.currentReentry
    currentResult.currentMap
  ambientPlaneMap_eq : currentResult.currentMap.planeMap =
    extension.ambient.planeMap

/-- Assemble the paper-ordered runtime from an exact first-call re-entry. -/
theorem proposition63_four_call_paper_runtime_assembly
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
    {family : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading family}
    (fineReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) fineShading normalizationExponent
      (backward.seed index hindex).schedule.first.sourceLoss
      (backward.seed index hindex).schedule.first.normalizationLoss)
    (rootAxialWindow : ∀ sourceIndex point,
      point ∈ fineReentry.geometry.frame ''
          fineReentry.geometry.ordinaryRefined.carrier sourceIndex →
        |point (2 : Fin 3)| ≤ 1 / 8)
    {sourceMap : PaperWZ1WeakPlaneMapData fineShading incidence}
    (extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient) :
    Nonempty (Proposition63FourCallPaperRuntimeAssemblyData K backward root
      grid leftFactor rightFactor sourceCoefficient global index hindex scales
      fineReentry rootAxialWindow extension) := by
  let seed := backward.seed index hindex
  let schedule := seed.schedule
  let publicSqrt := scales.choiceSqrtScalePackage
    (backward.loss (index + 1))
    (backward.loss_pos (index + 1) (by omega))
    ((backward.loss_le_terminal (index + 1) (by omega)).trans
      global.outputLoss_le_half)
    (global.rho_small index hindex scales)
  let receipts := global.scalar_receipts index hindex scales publicSqrt
    paperCutoff hrhoCutoff
  have hrhoLower := scales.output_rpow_le_rhoHat
    schedule.firstOutputLoss_pos (global.firstOutputLoss_le_discrete index hindex)
  have hrhoUpper := scales.rhoHat_le_output_rpow global.delta_pos
    (global.firstOutputLoss_lt_discrete index hindex)
    (global.firstOutput_gap_small index hindex)
  rcases proposition63_four_call_source_witness_prefix_of_absorption
      fineReentry schedule rfl rfl receipts.hdeltaFirstCall scales.rhoHat
      hrhoLower hrhoUpper rootAxialWindow extension receipts.hcellError
      seed.rhoAbsorption receipts.hrhoAbsorption
      ((global.rho_small index hindex scales).trans (by norm_num)) with
    ⟨rich1, ⟨currentResult⟩⟩
  have hfirstNormalization :
      currentResult.currentReentry.reentryNormalizationLoss =
        schedule.second.normalizationLoss := by
    simpa only [Proposition63RichFourCallScheduleData.firstThree] using
      currentResult.currentNormalization
  rcases proposition63_four_call_paper_frozen_choice_producer K backward root
      grid leftFactor rightFactor sourceCoefficient global index hindex
      paperCutoff scales hrhoCutoff
      (schedule.callOneRhoRootNormalization rich1 rootAxialWindow)
      currentResult.currentReentry hfirstNormalization
      currentResult.currentMap currentResult.currentLipschitz with
    ⟨paperNested⟩
  exact ⟨{
    rich1 := rich1
    currentResult := currentResult
    paperNested := paperNested
    ambientPlaneMap_eq := currentResult.currentMap_eq
  }⟩

end Kakeya.Assouad.PureWZ2
