import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallOrderedPairProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperOrderedPair
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallInnerScheduleRun
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallFirstScalarEnvelope

/-!
# Actual-current wrapper for the paper-ordered four-call step

This module performs the callback-local prefix after the previous ordered pair
has finished.  In particular it re-enters from the actual current extremality,
restricts the fixed ambient plane map, and constructs the paper cutoff, the
paper runtime, the call-two-rooted final pullback, and the final-current density
lift.  The latter is deliberately separate from the mass receipt: extremality
is never recovered from the mass-ledger restoration field.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- Post-cycle global data for the paper-ordered iterator.  The legacy scalar
producer cannot import the paper cutoff module without creating an import
cycle, so the paper cutoffs are selected once here, after that producer, and
remain independent of every callback-local shading. -/
structure Proposition63FourCallPaperGlobalData
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
    (sourceCoefficient : NNReal) where
  prelude : Proposition63FourCallPaperPreludeGlobalData
    (incidence := incidence) K backward root grid leftFactor rightFactor
    sourceCoefficient
  paperCutoff : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallPaperSeedCutoffData
        (backward.seed index hindex)
        ((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient))
  rho_le_paperCutoff : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
    ∀ scales : Proposition63FourCallOrderedPairIndexScales grid index,
      scales.rhoHat.1 ≤ (paperCutoff index hindex).rhoCutoff
  firstUniformCutoff : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallFirstUniformCutoffData
        (backward.seed index hindex)
        ((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient))
  delta_le_firstUniformCutoff : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      delta ≤ (firstUniformCutoff index hindex).nested.delta₀
  currentReentryAbsorption : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63CurrentReentryAbsorptionData
        inputLoss backward.rootNormalizationLoss backward.rootDensityLoss
        (backward.loss index) (backward.currentWeightLoss index hindex)
        (backward.seed index hindex).schedule.first.sourceLoss
        (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss)
  hdeltaCurrentReentry : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      delta ≤ (currentReentryAbsorption index hindex).delta₀
  finalCandidateLiftAbsorption : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63ReentryDensityLiftAbsorptionData
        (backward.currentWeightLoss index hindex)
        (backward.seed index hindex).goodCellCandidateLoss
        (backward.loss (index + 1))
        (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss)
  delta_le_finalCurrentLift : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      delta ≤ (finalCandidateLiftAbsorption index hindex).delta₀
  delta_le_alignedAbsorption : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      delta ≤ (backward.seed index hindex).alignedAbsorption.delta₀
  /-- The fixed source incidence is already below the finest ambient scale.
  Hence it remains below every preselected ordered-pair scale. -/
  incidence_le_delta : incidence ≤ delta

/-- Transport the ordinary axial window across the paper retyping equality.
Keeping the scheduled normalization loss as a variable makes the transport
transparent and avoids exposing the implementation cast of
`paperPropStickyReentry` to callers. -/
theorem Proposition63CurrentShadingReentryData.paperRootAxialWindow
    {delta sigma inputLoss normalizationLoss scheduledNormalizationLoss
      densityLoss reentryLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss}
    {current : WZ1PaperTubeShading root.normalization.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) root.normalization current)
    (rootAxialWindow : ∀ index point,
      point ∈ root.normalization.frame ''
          root.normalization.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (hreentryLoss : 0 < reentryLoss)
    (hnormalization : data.reentryNormalizationLoss =
      scheduledNormalizationLoss) :
    ∀ index point,
      point ∈ (data.paperPropStickyReentry hreentryLoss hnormalization).geometry.frame ''
          (data.paperPropStickyReentry hreentryLoss
            hnormalization).geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8 := by
  subst scheduledNormalizationLoss
  simpa [Proposition63CurrentShadingReentryData.paperPropStickyReentry] using
    data.rootAxialWindow rootAxialWindow hreentryLoss

/-- All genuinely callback-local objects needed by the paper M5 consumer. -/
structure Proposition63FourCallPaperOrderedPairActualPrefix
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
    (index : ℕ) (hindex : index < (finiteIntervalOrderedPairs gridN).length)
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    (current : WZ1PaperTubeShading root.normalization.croppedFamily)
    (sourceMap : PaperWZ1WeakPlaneMapData current incidence)
    (extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient) where
  fineCurrentReentry : Proposition63CurrentShadingReentryData
    (reentryLoss := (backward.seed index hindex).schedule.first.sourceLoss)
    root.normalization current
  fineWeight : fineCurrentReentry.normalizationWeight =
    proposition63CanonicalReentryWeight delta
      (backward.currentWeightLoss index hindex)
  fineWeightUpper : fineCurrentReentry.weightUpper =
    (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
      Kakeya.realRpowENN delta 2
  fineLevel : fineCurrentReentry.levelCount =
    proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss
  fineNormalization : fineCurrentReentry.reentryNormalizationLoss =
    (backward.seed index hindex).schedule.first.normalizationLoss
  currentSub : PaperIsSubshading current root.normalization.croppedRefined
  currentMap : PaperWZ1WeakPlaneMapData current incidence
  currentMap_eq : currentMap = sourceMap
  restrictedExtension : PureWZ2UnitAmbientWeakPlaneMapExtension
    (fineCurrentReentry.normalizedPlaneMap currentMap) sourceCoefficient
  restrictedAmbient_eq : restrictedExtension.ambient.planeMap =
    extension.ambient.planeMap
  runtimeAxialWindow : ∀ sourceIndex point,
    point ∈ (fineCurrentReentry.paperPropStickyReentry
        (backward.seed index hindex).schedule.first.sourceLoss_pos
        fineNormalization).geometry.frame ''
        (fineCurrentReentry.paperPropStickyReentry
          (backward.seed index hindex).schedule.first.sourceLoss_pos
          fineNormalization).geometry.ordinaryRefined.carrier sourceIndex →
      |point (2 : Fin 3)| ≤ 1 / 8
  paperCutoff : Proposition63FourCallPaperSeedCutoffData
    (backward.seed index hindex)
    ((4 : NNReal) *
      (lipschitzExtensionConstant Point3 * sourceCoefficient))
  rho_le_cutoff : scales.rhoHat.1 ≤ paperCutoff.rhoCutoff
  runtime : Proposition63FourCallPaperRuntimeAssemblyData
    (fineShading := fineCurrentReentry.normalization.croppedRefined)
    (fineReentry := fineCurrentReentry.paperPropStickyReentry
      (backward.seed index hindex).schedule.first.sourceLoss_pos
      fineNormalization)
    (rootAxialWindow := runtimeAxialWindow)
    (extension := restrictedExtension) K backward root grid leftFactor
      rightFactor sourceCoefficient global index hindex scales
  assembly : Proposition63FourCallPaperFinalAssemblyData
    runtime.paperNested.nested.current runtime.rich1.data.croppedCoarseShading
    (proposition63FourCallPaperPullbackCoefficient scales.rhoHat.1
      runtime.paperNested.restoredFirst.retainedFactor
      runtime.firstPullback.retentionFactor)
  finalCurrentLiftAbsorption : Proposition63ReentryDensityLiftAbsorptionData
    (backward.currentWeightLoss index hindex)
    (backward.seed index hindex).goodCellCandidateLoss
    (backward.loss (index + 1))
    (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss)
  delta_le_finalCurrentLift : delta ≤ finalCurrentLiftAbsorption.delta₀

/-- Build the whole actual-current prefix.  The two cutoff hypotheses are
quantified over the family-free choices, so the choices themselves are still
made here rather than supplied by the callback. -/
theorem proposition63_four_call_paper_ordered_pair_actual_prefix
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
    (index : ℕ) (hindex : index < (finiteIntervalOrderedPairs gridN).length)
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    (current : WZ1PaperTubeShading root.normalization.croppedFamily)
    (currentSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := root.normalization.croppedFamily)
      (Kakeya.realRpowENN delta (-backward.rootNormalizationLoss))
      (Kakeya.realRpowENN delta
        (-(backward.seed index hindex).schedule.first.sourceLoss))
      (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss))
    (ambient_two : (2 : ENNReal) <
      Kakeya.realRpowENN delta (-backward.rootNormalizationLoss))
    (current_sub : PaperIsSubshading current
      root.normalization.croppedRefined)
    (current_cubical : WZ1PaperIsCubicalShading current)
    (current_extremal : WZ2PaperCroppedIsExtremal sigma
      (backward.loss index) root.normalization.croppedFamily current)
    (currentLoss_le_reentry : backward.loss index ≤
      (backward.seed index hindex).schedule.first.sourceLoss)
    (currentLoss_pos : 0 < backward.loss index)
    (canonical_weight_absorb :
      proposition63CanonicalReentryWeight delta
          (backward.currentWeightLoss index hindex) ≤
        (100 : ENNReal)⁻¹ *
          Kakeya.realRpowENN delta backward.rootDensityLoss *
          Kakeya.realRpowENN delta (backward.loss index + 2))
    (trace_fixed_absorb :
      (96 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta
            ((backward.seed index hindex).schedule.first.sourceLoss -
              backward.currentWeightLoss index hindex) ≤ 1)
    (paper_fixed_absorb :
      ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta
            ((backward.seed index hindex).schedule.first.sourceLoss -
              backward.currentWeightLoss index hindex) ≤
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
          (((proposition63CanonicalReentryWeight delta
                (backward.currentWeightLoss index hindex))⁻¹ *
              (Kakeya.realRpowENN delta (-backward.rootNormalizationLoss) *
                (regularizationLoss *
                  ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
                    Kakeya.realRpowENN delta 2)) * degreeConstant)) *
            Kakeya.realRpowENN delta (-backward.rootNormalizationLoss)) ≤
        Kakeya.realRpowENN delta
          (-(backward.seed index hindex).schedule.first.sourceLoss))
    (delta_small : delta ≤ 1 / 24)
    (rootAxialWindow : ∀ sourceIndex point,
      point ∈ root.normalization.frame ''
          root.normalization.ordinaryRefined.carrier sourceIndex →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (sourceMap : PaperWZ1WeakPlaneMapData current incidence)
    (extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient)
    (paperCutoff : Proposition63FourCallPaperSeedCutoffData
      (backward.seed index hindex)
      ((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)))
    (rho_le_cutoff : scales.rhoHat.1 ≤ paperCutoff.rhoCutoff)
    (finalCurrentLiftAbsorption : Proposition63ReentryDensityLiftAbsorptionData
      (backward.currentWeightLoss index hindex)
      (backward.seed index hindex).goodCellCandidateLoss
      (backward.loss (index + 1))
      (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss))
    (delta_le_finalCurrentLift : delta ≤
      finalCurrentLiftAbsorption.delta₀) :
    Nonempty (Proposition63FourCallPaperOrderedPairActualPrefix K backward root
      grid leftFactor rightFactor sourceCoefficient global index hindex scales
      current sourceMap extension) := by
  let seed := backward.seed index hindex
  rcases proposition63_four_call_ordered_pair_prepare_fresh_reentry root current
      currentSchedule ambient_two current_sub current_cubical current_extremal
      currentLoss_le_reentry currentLoss_pos
      seed.schedule.first.normalizationLoss
      seed.schedule.first.normalizationLoss_pos
      seed.schedule.first.sourceLoss_le_half canonical_weight_absorb
      trace_fixed_absorb paper_fixed_absorb regularization_absorb delta_small with
    ⟨fineCurrentReentry, hfineWeight, hfineWeightUpper, hfineLevel,
      hnormalization⟩
  let currentMap : PaperWZ1WeakPlaneMapData current incidence :=
    sourceMap
  let restrictedExtension := extension.restrictToReentry currentMap
    sourceCoefficient fineCurrentReentry
  let fineReentry := fineCurrentReentry.paperPropStickyReentry
    seed.schedule.first.sourceLoss_pos hnormalization
  let runtimeAxialWindow : ∀ sourceIndex point,
      point ∈ fineReentry.geometry.frame ''
          fineReentry.geometry.ordinaryRefined.carrier sourceIndex →
        |point (2 : Fin 3)| ≤ 1 / 8 := by
    exact fineCurrentReentry.paperRootAxialWindow rootAxialWindow
      seed.schedule.first.sourceLoss_pos hnormalization
  let runtime := Classical.choice <|
    proposition63_four_call_paper_runtime_assembly K backward root grid
      leftFactor rightFactor sourceCoefficient global index hindex paperCutoff
      scales rho_le_cutoff fineReentry runtimeAxialWindow restrictedExtension
  let assembly := Classical.choice <|
    proposition63_four_call_paper_final_assembly runtime
  exact ⟨{
    fineCurrentReentry := fineCurrentReentry
    fineWeight := hfineWeight
    fineWeightUpper := hfineWeightUpper
    fineLevel := hfineLevel
    fineNormalization := hnormalization
    currentMap := currentMap
    currentMap_eq := rfl
    currentSub := current_sub
    restrictedExtension := restrictedExtension
    restrictedAmbient_eq := rfl
    runtimeAxialWindow := runtimeAxialWindow
    paperCutoff := paperCutoff
    rho_le_cutoff := rho_le_cutoff
    runtime := runtime
    assembly := assembly
    finalCurrentLiftAbsorption := finalCurrentLiftAbsorption
    delta_le_finalCurrentLift := delta_le_finalCurrentLift
  }⟩

/-- Build the callback-local prefix from the post-cycle global package.  In
particular, no paper cutoff is selected after the current shading is exposed. -/
theorem proposition63_four_call_paper_ordered_pair_actual_prefix_from_global
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
    (paperGlobal : Proposition63FourCallPaperGlobalData K backward root grid
      leftFactor rightFactor sourceCoefficient)
    (index : ℕ) (hindex : index < (finiteIntervalOrderedPairs gridN).length)
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    (current : WZ1PaperTubeShading root.normalization.croppedFamily)
    (currentSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := root.normalization.croppedFamily)
      (Kakeya.realRpowENN delta (-backward.rootNormalizationLoss))
      (Kakeya.realRpowENN delta
        (-(backward.seed index hindex).schedule.first.sourceLoss))
      (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss))
    (ambient_two : (2 : ENNReal) <
      Kakeya.realRpowENN delta (-backward.rootNormalizationLoss))
    (current_sub : PaperIsSubshading current
      root.normalization.croppedRefined)
    (current_cubical : WZ1PaperIsCubicalShading current)
    (current_extremal : WZ2PaperCroppedIsExtremal sigma
      (backward.loss index) root.normalization.croppedFamily current)
    (currentLoss_le_reentry : backward.loss index ≤
      (backward.seed index hindex).schedule.first.sourceLoss)
    (currentLoss_pos : 0 < backward.loss index)
    (canonical_weight_absorb :
      proposition63CanonicalReentryWeight delta
          (backward.currentWeightLoss index hindex) ≤
        (100 : ENNReal)⁻¹ *
          Kakeya.realRpowENN delta backward.rootDensityLoss *
          Kakeya.realRpowENN delta (backward.loss index + 2))
    (trace_fixed_absorb :
      (96 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta
            ((backward.seed index hindex).schedule.first.sourceLoss -
              backward.currentWeightLoss index hindex) ≤ 1)
    (paper_fixed_absorb :
      ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta
            ((backward.seed index hindex).schedule.first.sourceLoss -
              backward.currentWeightLoss index hindex) ≤
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
          (((proposition63CanonicalReentryWeight delta
                (backward.currentWeightLoss index hindex))⁻¹ *
              (Kakeya.realRpowENN delta (-backward.rootNormalizationLoss) *
                (regularizationLoss *
                  ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
                    Kakeya.realRpowENN delta 2)) * degreeConstant)) *
            Kakeya.realRpowENN delta (-backward.rootNormalizationLoss)) ≤
        Kakeya.realRpowENN delta
          (-(backward.seed index hindex).schedule.first.sourceLoss))
    (delta_small : delta ≤ 1 / 24)
    (rootAxialWindow : ∀ sourceIndex point,
      point ∈ root.normalization.frame ''
          root.normalization.ordinaryRefined.carrier sourceIndex →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (sourceMap : PaperWZ1WeakPlaneMapData current incidence)
    (extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient) :
    Nonempty (Proposition63FourCallPaperOrderedPairActualPrefix K backward root
      grid leftFactor rightFactor sourceCoefficient paperGlobal.prelude index
      hindex scales current sourceMap extension) := by
  exact proposition63_four_call_paper_ordered_pair_actual_prefix K backward root
    grid leftFactor rightFactor sourceCoefficient paperGlobal.prelude index
    hindex scales current currentSchedule ambient_two current_sub
    current_cubical current_extremal currentLoss_le_reentry currentLoss_pos
    canonical_weight_absorb trace_fixed_absorb paper_fixed_absorb
    regularization_absorb delta_small rootAxialWindow sourceMap extension
    (paperGlobal.paperCutoff index hindex)
    (paperGlobal.rho_le_paperCutoff index hindex scales)
    (paperGlobal.finalCandidateLiftAbsorption index hindex)
    (paperGlobal.delta_le_finalCurrentLift index hindex)

/-- Finish an actual-current paper step once the scalar tail receipts have
been assembled.  Notice that the final-current absorption receipt is passed
directly to the paper theorem; the restoration inequality remains only a
mass-ledger field inside that theorem and is not used here to manufacture
extremality. -/
theorem Proposition63FourCallPaperOrderedPairActualPrefix.run
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    {K : ℝ}
    {backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length}
    {root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {leftFactor rightFactor : ℕ → ENNReal}
    {paperLeftFactor paperRightFactor : ℕ → ENNReal}
    {sourceCoefficient : NNReal}
    {global : Proposition63FourCallPaperPreludeGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient}
    {index : ℕ} {hindex : index < (finiteIntervalOrderedPairs gridN).length}
    {scales : Proposition63FourCallOrderedPairIndexScales grid index}
    {current : WZ1PaperTubeShading root.normalization.croppedFamily}
    {sourceMap : PaperWZ1WeakPlaneMapData current incidence}
    {extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient}
    (actual : Proposition63FourCallPaperOrderedPairActualPrefix K backward root
      grid leftFactor rightFactor sourceCoefficient global index hindex scales
      current sourceMap extension)
    (criticalInputs : Proposition63FourCallPaperCriticalTailReceipt
      (backward.seed index hindex) scales.rhoHat.1
      (Real.sqrt scales.rhoHat.1))
    (planeInputs : Proposition63FourCallPaperPlaneCoverReceipt
      actual.runtime.paperNested.nested scales.rhoHat.1 scales.tau
      ((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)))
    (currentInputs : Proposition63FourCallCurrentReceipt
      (sigma := sigma) current scales.rhoHat.1)
    (massInputs : Proposition63FourCallPaperMassReceipt
      (Proposition63NestedPointCoverData.FullGrainCells.nestedCandidateIntervalBound
        scales.rhoHat.1 scales.rhoHat.1
        (8 * (((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ) *
          scales.rhoHat.1)
        (((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ)
        (13 ^ 3)
        (proposition63PaperTauConstant actual.runtime.paperNested.nested))
      (proposition63DependentFinePullbackLeft actual.fineCurrentReentry
        actual.runtime.rich1.data actual.assembly.pullback.retentionFactor
        (ENNReal.ofReal ((criticalInputs.cellVolumeFloor / 2) /
            (4 * (2 * Real.sqrt scales.rhoHat.1) ^ 2)) *
          (((1 : ENNReal) / 2) /
            (2 * (planeInputs.coverBudget : ENNReal))) *
          (actual.runtime.paperNested.nested.secondRetainedFactor *
            ((73 / 100 : ENNReal) *
              actual.runtime.paperNested.nested.reentry.normalizationWeight) *
            actual.runtime.paperNested.nested.firstRetainedFactor)))
      (proposition63DependentFinePullbackRight actual.fineCurrentReentry
        ((actual.runtime.paperNested.nested.reentry.regularized.regularizationLoss *
            actual.runtime.paperNested.nested.prepared.preparationLoss) *
          (2 * ENNReal.ofReal (4 * scales.rhoHat.1))))
      delta criticalInputs.outputCandidateLoss currentInputs.fineCurrentLoss
      ((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient))
      criticalInputs.spatialScale criticalInputs.variationScale)
    (hincidenceRho : incidence ≤ scales.rhoHat.1)
    (hcoverUpper : (planeInputs.coverBudget : ENNReal) ≤
      (1605264998400 : ENNReal) *
        (((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient)) :
          ENNReal) ^ 3 *
        Kakeya.realRpowENN scales.rhoHat.1
          (-(proposition63FourCallPaperFinalExponent sigma
            (backward.seed index hindex).schedule.fourth.normalizationLoss
            (backward.seed index hindex).fourthKernel.internalLoss
            (backward.seed index hindex).epsilon₁
            (backward.seed index hindex).paperAngularExponent)) + 2)
    (hnextLoss : criticalInputs.outputCandidateLoss =
      backward.loss (index + 1))
    (hconstant : 2 * massInputs.targetConstant ≤
      proposition63FourCallOrderedPairConstant grid index)
    (hleft : massInputs.targetLeft = paperLeftFactor index)
    (hright : massInputs.targetRight = paperRightFactor index) :
    ∃ next : WZ1PaperTubeShading root.normalization.croppedFamily,
      PaperIsSubshading next current ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union, next.pointMultiplicity point =
        current.pointMultiplicity point) ∧
      WZ2PaperCroppedIsExtremal sigma (backward.loss (index + 1))
        root.normalization.croppedFamily next ∧
      WZ2PaperConvexWolffBound root.normalization.croppedFamily
        (Kakeya.realRpowENN delta (-(backward.loss (index + 1)))) ∧
      PureWZ2IntervalCoveringAt next
        extension.ambient.planeMap
        (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
        (grid.scale (finiteIntervalOrderedPair gridN index).1)
        (grid.scale (finiteIntervalOrderedPair gridN index).2)
        (proposition63FourCallOrderedPairConstant grid index) ∧
      paperLeftFactor index * current.mass ≤
        paperRightFactor index * next.mass := by
  have result := proposition63_four_call_paper_ordered_pair hindex
    actual.fineCurrentReentry actual.fineWeight actual.fineWeightUpper
    actual.fineLevel actual.fineNormalization actual.runtime
    actual.paperCutoff actual.rho_le_cutoff
    actual.finalCurrentLiftAbsorption actual.delta_le_finalCurrentLift
    actual.assembly criticalInputs planeInputs currentInputs massInputs
    hincidenceRho hcoverUpper hnextLoss hconstant hleft hright
  simpa only [actual.runtime.ambientPlaneMap_eq, actual.restrictedAmbient_eq]
    using result

end Kakeya.Assouad.PureWZ2
