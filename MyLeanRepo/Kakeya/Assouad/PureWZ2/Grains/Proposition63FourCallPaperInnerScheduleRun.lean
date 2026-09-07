import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperGlobalProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperScalarFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperScalarBounds

/-!
# Execute the paper-ordered Proposition 6.3 inner schedule

This module is the callback-local half of M6.  All loss, scale, cutoff, and
mass-factor choices are supplied by pre-runtime data; the current shading is
used only to build the actual re-entry and the four paper receipts.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

attribute [local instance] Classical.propDecidable

private noncomputable def paperInnerSpatialScale (rho : ℝ) : ℝ :=
  Real.sqrt rho

private noncomputable def paperInnerVariationScale
    (sourceCoefficient : NNReal) (rho : ℝ) : ℝ :=
  proposition63FourCallVariationScale sourceCoefficient
    (paperInnerSpatialScale rho)

/-- The prepared paper shading remains inside the domain on which the fixed
ambient plane map is unit-valued. -/
theorem Proposition63FourCallPaperRuntimeAssemblyData.plane_unit_on_prepared
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ} {K : ℝ}
    {backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length}
    {root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {leftFactor rightFactor : ℕ → ENNReal} {sourceCoefficient : NNReal}
    {global : Proposition63FourCallPaperPreludeGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient}
    {index : ℕ} {hindex : index < (finiteIntervalOrderedPairs gridN).length}
    {scales : Proposition63FourCallOrderedPairIndexScales grid index}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading family}
    {fineReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) fineShading normalizationExponent
      (backward.seed index hindex).schedule.first.sourceLoss
      (backward.seed index hindex).schedule.first.normalizationLoss}
    {rootAxialWindow : ∀ sourceIndex point,
      point ∈ fineReentry.geometry.frame ''
          fineReentry.geometry.ordinaryRefined.carrier sourceIndex →
        |point (2 : Fin 3)| ≤ 1 / 8}
    {sourceMap : PaperWZ1WeakPlaneMapData fineShading incidence}
    {extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient}
    (runtime : Proposition63FourCallPaperRuntimeAssemblyData K backward root
      grid leftFactor rightFactor sourceCoefficient global index hindex scales
      fineReentry rootAxialWindow extension) :
    ∀ point ∈ runtime.paperNested.nested.prepared.refined.shading.union,
      ‖runtime.currentResult.currentMap.planeMap point‖ = 1 := by
  intro point hpoint
  apply runtime.currentResult.currentMap.unit point
  apply runtime.currentResult.currentReentry.normalization_croppedRefined_union_subset_current
  have htarget : point ∈ runtime.paperNested.target.data.refined.union := by
    have hnestedCurrent : point ∈ runtime.paperNested.nested.current.union :=
      runtime.paperNested.nested.prepared_union_subset_current hpoint
    have hrestored : point ∈ runtime.paperNested.restoredFirst.state.shading.union := by
      rw [runtime.paperNested.nested_eq] at hnestedCurrent
      exact hnestedCurrent
    have htargetFirst : point ∈ runtime.paperNested.targetFirst.state.shading.union := by
      rw [runtime.paperNested.restoredFirst_union] at hrestored
      exact hrestored
    have htargetExtended : point ∈
        (extendShading runtime.paperNested.target.data.selected
          runtime.paperNested.target.data.refined).union :=
      paper_subshading_union_subset
        runtime.paperNested.targetFirst.state.subshading htargetFirst
    simpa only [extendShading_union runtime.paperNested.target.data.selected] using
      htargetExtended
  have htargetNormalized : point ∈
      runtime.paperNested.targetReentry.normalization.croppedRefined.union :=
    refined_union_subset_shading runtime.paperNested.target.data htarget
  have houterAmbient : point ∈
      (extendShading runtime.paperNested.outer.data.selected
        runtime.paperNested.outer.data.refined).union :=
    runtime.paperNested.targetReentry.normalization_croppedRefined_union_subset_current
      htargetNormalized
  have houter : point ∈ runtime.paperNested.outer.data.refined.union := by
    simpa only [extendShading_union runtime.paperNested.outer.data.selected] using
      houterAmbient
  exact refined_union_subset_shading runtime.paperNested.outer.data houter

/-- The critical-tail receipt extracted from one frozen paper scalar and its
global paper cutoff. -/
noncomputable def Proposition63FourCallPaperScalarDataAt.criticalTailReceipt
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    {backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length}
    {root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {sourceCoefficient : NNReal} {index : ℕ}
    {hindex : index < (finiteIntervalOrderedPairs gridN).length}
    (scalar : Proposition63FourCallPaperScalarDataAt (incidence := incidence)
      backward root grid sourceCoefficient index hindex)
    (paperCutoff : Proposition63FourCallPaperSeedCutoffData
      (backward.seed index hindex)
      ((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)))
    (rho_le_cutoff : scalar.scales.rhoHat.1 ≤ paperCutoff.rhoCutoff) :
    Proposition63FourCallPaperCriticalTailReceipt
      (backward.seed index hindex) scalar.scales.rhoHat.1
      (Real.sqrt scalar.scales.rhoHat.1) := by
  let seed := backward.seed index hindex
  have hrhoPos : 0 < scalar.scales.rhoHat.1 :=
    (grid.scale_pos _
      (scalar.scales.first_lt_second.le.trans
        scalar.scales.second_le_gridN)).trans_le
      scalar.scales.logicalR_le_rhoHat
  exact {
    cellVolumeFloor := scalar.cellFloor.cellVolumeFloor
    outputCandidateLoss := backward.loss (index + 1)
    spatialScale := paperInnerSpatialScale scalar.scales.rhoHat.1
    variationScale := paperInnerVariationScale sourceCoefficient
      scalar.scales.rhoHat.1
    coarseCritical := rho_le_cutoff.trans <|
      paperCutoff.rhoCutoff_le_legacy.trans
        paperCutoff.legacy.rhoCutoff_le_critical
    finalStructural := seed.finalLoss_le_structural
    traceAbsorption := seed.traceAbsorption.absorb scalar.scales.rhoHat.1
      hrhoPos <| rho_le_cutoff.trans <|
        paperCutoff.rhoCutoff_le_legacy.trans
          paperCutoff.legacy.rhoCutoff_le_traceAbsorption
    cellVolumeFloor_pos := scalar.cellFloor.positive
    cellBudget := by
      simpa only [scalar.internalSqrt_eq_sqrt] using scalar.cellFloor.budget
    query_pos := hrhoPos
    query_le_one := scalar.scales.rhoHat.property.2
  }

/-- The plane-cover receipt uses the fixed ambient plane map and the
paper-specific final constant and cover budget. -/
noncomputable def Proposition63FourCallPaperScalarDataAt.planeCoverReceipt
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ} {K : ℝ}
    {backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length}
    {root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {legacyLeft legacyRight : ℕ → ENNReal} {sourceCoefficient : NNReal}
    {paperGlobal : Proposition63FourCallPaperGlobalData K backward root grid
      legacyLeft legacyRight sourceCoefficient}
    {index : ℕ} {hindex : index < (finiteIntervalOrderedPairs gridN).length}
    {current : WZ1PaperTubeShading root.normalization.croppedFamily}
    {sourceMap : PaperWZ1WeakPlaneMapData current incidence}
    {extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient}
    (scalar : Proposition63FourCallPaperScalarDataAt (incidence := incidence)
      backward root grid sourceCoefficient index hindex)
    (actual : Proposition63FourCallPaperOrderedPairActualPrefix K backward root
      grid legacyLeft legacyRight sourceCoefficient paperGlobal.prelude index
      hindex scalar.scales current sourceMap extension) :
    Proposition63FourCallPaperPlaneCoverReceipt
      actual.runtime.paperNested.nested scalar.scales.rhoHat.1
      scalar.scales.tau
      ((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)) := by
  have hscaleSmall := scalar.scales.scale_smallness
    paperGlobal.prelude.coefficient_one paperGlobal.prelude.discreteLoss_pos.le
    paperGlobal.prelude.amplified_query_small
  exact {
    plane_unit := actual.runtime.plane_unit_on_prepared
    coefficient_one := paperGlobal.prelude.coefficient_one
    plane_lipschitz := actual.runtime.currentResult.currentLipschitz
    coverBudget := scalar.coverBudget.coverBudget
    coverBudget_pos := scalar.coverBudget.positive
    cover_budget := by
      simpa only [scalar.internalSqrt_eq_sqrt, scalar.finalConstant_value,
        Proposition63FourCallOrderedPairIndexScales.choiceSqrtScalePackage,
        proposition63_four_call_final_constant_choice] using
        scalar.coverBudget_sqrt_bound
    sqrtConstant_finite := by
      simpa only [scalar.internalSqrt_eq_sqrt, scalar.finalConstant_value,
        Proposition63FourCallOrderedPairIndexScales.choiceSqrtScalePackage,
        proposition63_four_call_final_constant_choice] using
        scalar.finalConstant_sqrt_finite
    normalErrorTau := hscaleSmall.1
    hullTau := hscaleSmall.2.1
  }

/-- The paper left factor is bounded by the exact callback-local pullback
expression. -/
theorem Proposition63FourCallPaperOrderedPairActualPrefix.paperLeft_le_actual
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ} {K : ℝ}
    {backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length}
    {root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {legacyLeft legacyRight : ℕ → ENNReal} {sourceCoefficient : NNReal}
    {paperGlobal : Proposition63FourCallPaperGlobalData K backward root grid
      legacyLeft legacyRight sourceCoefficient}
    {index : ℕ} {hindex : index < (finiteIntervalOrderedPairs gridN).length}
    {current : WZ1PaperTubeShading root.normalization.croppedFamily}
    {sourceMap : PaperWZ1WeakPlaneMapData current incidence}
    {extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient}
    (scalar : Proposition63FourCallPaperScalarDataAt (incidence := incidence)
      backward root grid sourceCoefficient index hindex)
    (actual : Proposition63FourCallPaperOrderedPairActualPrefix K backward root
      grid legacyLeft legacyRight sourceCoefficient paperGlobal.prelude index
      hindex scalar.scales current sourceMap extension) :
    scalar.paperLeft ≤
      proposition63DependentFinePullbackLeft actual.fineCurrentReentry
        actual.runtime.rich1.data actual.assembly.pullback.retentionFactor
        (ENNReal.ofReal ((scalar.cellFloor.cellVolumeFloor / 2) /
            (4 * (2 * Real.sqrt scalar.scales.rhoHat.1) ^ 2)) *
          (((1 : ENNReal) / 2) /
            (2 * (scalar.coverBudget.coverBudget : ENNReal))) *
          (actual.runtime.paperNested.nested.secondRetainedFactor *
            ((73 / 100 : ENNReal) *
              actual.runtime.paperNested.nested.reentry.normalizationWeight) *
            actual.runtime.paperNested.nested.firstRetainedFactor)) := by
  let seed := backward.seed index hindex
  have hfineCard : actual.fineCurrentReentry.normalization.croppedFamily.card ≤
      root.normalization.croppedFamily.card := by
    rw [actual.fineCurrentReentry.normalization_croppedFamily]
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      actual.fineCurrentReentry.regularized.selected.embedding
      actual.fineCurrentReentry.regularized.selected.embedding.injective
  have hassembly : actual.assembly.pullback.retentionFactor ≤
      scalar.paperAncestorUpper := by
    have h := actual.assembly.retentionFactor_le_paperUpper
      (actual.runtime.targetRetainedLower_le hfineCard)
      actual.runtime.paperNested.restoredFirstRetainedFactor
      (actual.runtime.legacyPullbackRetention_le hfineCard)
    exact h.trans_eq (by
      rw [scalar.paperAncestorUpper_eq, scalar.legacyAncestorUpper_eq]
      rfl)
  have hassembly' : actual.assembly.pullback.retentionFactor ≤
      proposition63FourCallPaperAncestorRetentionUpper
        root.normalization.croppedFamily scalar.legacyAncestorUpper := by
    simpa only [scalar.paperAncestorUpper_eq] using hassembly
  have hsecondCard := actual.runtime.nestedSqrtCard_le_root hfineCard
  rw [scalar.paperLeft_eq]
  have hleft := proposition63_four_call_paper_frozen_left_le_actual
    actual.fineCurrentReentry actual.runtime.rich1.data
    scalar.legacyAncestorUpper actual.assembly.pullback.retentionFactor
    (proposition63FourCallFrozenLineCoverBase
      scalar.cellFloor.cellVolumeFloor scalar.internalSqrt.sqrtRequested.1
      scalar.coverBudget.coverBudget)
    (ENNReal.ofReal ((scalar.cellFloor.cellVolumeFloor / 2) /
        (4 * (2 * Real.sqrt scalar.scales.rhoHat.1) ^ 2)) *
      (((1 : ENNReal) / 2) /
        (2 * (scalar.coverBudget.coverBudget : ENNReal))))
    (proposition63CanonicalReentryWeight scalar.scales.rhoHat.1
      seed.nextWeightLoss)
    actual.runtime.paperNested.nested.secondRetainedFactor
    actual.runtime.paperNested.nested.reentry.normalizationWeight
    actual.runtime.paperNested.nested.sqrtSticky.selected.family.card
    hassembly' actual.runtime.paperNested.nestedSecondRetainedFactor
    actual.runtime.paperNested.nestedCanonicalWeight hsecondCard
    actual.fineWeight (by
      exact le_of_eq <| congrArg
        (fun sqrtScale : ℝ =>
          ENNReal.ofReal ((scalar.cellFloor.cellVolumeFloor / 2) /
              (4 * (2 * sqrtScale) ^ 2)) *
            (((1 : ENNReal) / 2) /
              (2 * (scalar.coverBudget.coverBudget : ENNReal))))
        scalar.internalSqrt_eq_sqrt)
  simpa only [proposition63FourCallPaperLeftFactorAt,
    actual.runtime.paperNested.nestedFirstRetainedFactor] using hleft

/-- The exact callback-local right expression is controlled by the frozen
paper right factor. -/
theorem Proposition63FourCallPaperOrderedPairActualPrefix.actualRight_le_paperRight
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ} {K : ℝ}
    {backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length}
    {root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {legacyLeft legacyRight : ℕ → ENNReal} {sourceCoefficient : NNReal}
    {paperGlobal : Proposition63FourCallPaperGlobalData K backward root grid
      legacyLeft legacyRight sourceCoefficient}
    {index : ℕ} {hindex : index < (finiteIntervalOrderedPairs gridN).length}
    {current : WZ1PaperTubeShading root.normalization.croppedFamily}
    {sourceMap : PaperWZ1WeakPlaneMapData current incidence}
    {extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient}
    (scalar : Proposition63FourCallPaperScalarDataAt (incidence := incidence)
      backward root grid sourceCoefficient index hindex)
    (actual : Proposition63FourCallPaperOrderedPairActualPrefix K backward root
      grid legacyLeft legacyRight sourceCoefficient paperGlobal.prelude index
      hindex scalar.scales current sourceMap extension) :
    proposition63DependentFinePullbackRight actual.fineCurrentReentry
        ((actual.runtime.paperNested.nested.reentry.regularized.regularizationLoss *
            actual.runtime.paperNested.nested.prepared.preparationLoss) *
          (2 * ENNReal.ofReal (4 * scalar.scales.rhoHat.1))) ≤
      scalar.paperRight := by
  have h := proposition63_four_call_paper_actual_right_le_root
    actual.fineCurrentReentry actual.runtime.paperNested.nested.reentry
    actual.runtime.paperNested.nested.prepared.preparationLoss
    scalar.uniformLevel
    (by rw [actual.fineLevel]; exact scalar.currentLevel_le)
    (actual.runtime.currentReentryCard_le_root (by
      rw [actual.fineCurrentReentry.normalization_croppedFamily]
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        actual.fineCurrentReentry.regularized.selected.embedding
        actual.fineCurrentReentry.regularized.selected.embedding.injective))
    (actual.runtime.paperNested.nestedCanonicalLevel.le.trans <| by
      rw [actual.runtime.currentResult.currentNormalization]
      exact scalar.secondLevel_le)
    (actual.runtime.nestedPreparationLoss_le_root (by
      rw [actual.fineCurrentReentry.normalization_croppedFamily]
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        actual.fineCurrentReentry.regularized.selected.embedding
        actual.fineCurrentReentry.regularized.selected.embedding.injective))
    (by linarith [paperGlobal.prelude.rho_small index hindex scalar.scales])
  exact h.trans_eq <| by
    rw [scalar.paperRight_eq]
    rfl

/-- Freeze the nearby-scale schedule for every ordered pair before the
iteration callback exposes its current shading. -/
noncomputable def proposition63FourCallPaperCurrentScheduleFamily
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
    (legacyLeft legacyRight : ℕ → ENNReal)
    (sourceCoefficient : NNReal)
    (paperGlobal : Proposition63FourCallPaperGlobalData
      (incidence := incidence) K backward root grid
      legacyLeft legacyRight sourceCoefficient) :
    ∀ index (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      WZ2PaperPureFiniteNearbyScheduleData
        (fine := root.normalization.croppedFamily)
        (Kakeya.realRpowENN delta (-backward.rootNormalizationLoss))
        (Kakeya.realRpowENN delta
          (-(backward.seed index hindex).schedule.first.sourceLoss))
        (proposition63CanonicalNearbyLevelCount
          backward.rootNormalizationLoss) := by
  intro index hindex
  let currentData := proposition63_four_call_inner_current_reentry_schedule_at
    backward source root index hindex
  let currentAbsorption := paperGlobal.currentReentryAbsorption index hindex
  have hdeltaCurrent := paperGlobal.hdeltaCurrentReentry index hindex
  have ambientTwo := currentAbsorption.ambient_two
    paperGlobal.prelude.delta_pos hdeltaCurrent
  exact Classical.choice <| root.finiteNearbySchedule
    (by
      dsimp [Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss]
      exact div_pos backward.rootBudget_pos (by norm_num))
    ambientTwo currentData.two_normalization_le_reentry

/-- The paper ordered-pair transition obtained from one frozen scalar family,
based at an arbitrary already-restored current shading inside the frozen root.
All pair choices still come from the root-global data. -/
theorem proposition63_four_call_paper_step_of_scalar_family_from_current
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
    (rootInput : Proposition63FourCallRootInput root)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (legacyLeft legacyRight : ℕ → ENNReal)
    (sourceCoefficient : NNReal)
    (paperGlobal : Proposition63FourCallPaperGlobalData
      (incidence := incidence) K backward root grid
      legacyLeft legacyRight sourceCoefficient)
    (scalarFamily : Proposition63FourCallPaperScalarFamilyData
      (incidence := incidence) backward root grid sourceCoefficient)
    (delta_le_nested : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        delta ≤ (scalarFamily.pair index hindex).nestedInterval.delta₀)
    (delta_le_aligned : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        delta ≤ (backward.seed index hindex).alignedAbsorption.delta₀)
    (currentSchedules :
      ∀ index (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        WZ2PaperPureFiniteNearbyScheduleData
          (fine := root.normalization.croppedFamily)
          (Kakeya.realRpowENN delta (-backward.rootNormalizationLoss))
          (Kakeya.realRpowENN delta
            (-(backward.seed index hindex).schedule.first.sourceLoss))
          (proposition63CanonicalNearbyLevelCount
            backward.rootNormalizationLoss))
    (initial : WZ1PaperTubeShading root.normalization.croppedFamily)
    (sourceMap : PaperWZ1WeakPlaneMapData
      initial incidence)
    (extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient)
    (initial_sub : PaperIsSubshading initial
      root.normalization.croppedRefined) :
    Proposition63FourCallOrderedPairStep grid
      initial extension.ambient.planeMap backward.loss
      (proposition63FourCallPaperLeftFactor scalarFamily.pair)
      (proposition63FourCallPaperRightFactor scalarFamily.pair) := by
  intro index hindex current current_sub current_cubical _currentMultiplicity
    current_extremal current_cwa _prefixMass _currentMass
  let scalar := scalarFamily.pair index hindex
  let currentData := proposition63_four_call_inner_current_reentry_schedule_at
    backward source root index hindex
  let currentAbsorption := paperGlobal.currentReentryAbsorption index hindex
  have hdeltaCurrent := paperGlobal.hdeltaCurrentReentry index hindex
  have ambientTwo := currentAbsorption.ambient_two
    paperGlobal.prelude.delta_pos hdeltaCurrent
  let currentSchedule := currentSchedules index hindex
  let currentMap := paperWeakPlaneMapRestrict sourceMap current_sub
  let currentExtension := extension.restrict sourceMap sourceCoefficient
    current_sub
  rcases proposition63_four_call_paper_ordered_pair_actual_prefix_from_global
      K backward root grid legacyLeft legacyRight sourceCoefficient paperGlobal
      index hindex scalar.scales current currentSchedule ambientTwo
      (fun tube point point_mem =>
        initial_sub tube (current_sub tube point_mem))
      current_cubical current_extremal currentData.currentLoss_lt_reentry.le
      currentData.currentLoss_pos
      (currentAbsorption.canonical_weight_absorb
        paperGlobal.prelude.delta_pos hdeltaCurrent)
      (currentAbsorption.trace_fixed_absorb
        paperGlobal.prelude.delta_pos hdeltaCurrent)
      (currentAbsorption.paper_fixed_absorb
        paperGlobal.prelude.delta_pos hdeltaCurrent)
      (currentAbsorption.regularization_absorb root.normalization rfl
        currentSchedule rfl rfl paperGlobal.prelude.delta_pos hdeltaCurrent)
      (hdeltaCurrent.trans <|
        currentAbsorption.delta₀_le_tiny.trans (by norm_num))
      rootInput.ordinaryAxialWindowEighth currentMap currentExtension with ⟨actual⟩
  let criticalInputs := scalar.criticalTailReceipt actual.paperCutoff
    actual.rho_le_cutoff
  let planeInputs := scalar.planeCoverReceipt
    (paperGlobal := paperGlobal) actual
  have hdeltaNested : delta ≤ scalar.nestedInterval.delta₀ :=
    delta_le_nested index hindex
  let internalConstant : ENNReal := ENNReal.ofReal
    (Real.rpow delta
        (-(backward.seed index hindex).alignedAbsorption.internalLoss) *
      Real.rpow (scalar.scales.tau / scalar.scales.rhoHat.1) (1 - sigma))
  have hconstantLeft :
      Proposition63NestedPointCoverData.FullGrainCells.nestedCandidateIntervalBound
          scalar.scales.rhoHat.1 scalar.scales.rhoHat.1
          (8 * (((4 : NNReal) *
            (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ) *
            scalar.scales.rhoHat.1)
          (((4 : NNReal) *
            (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ)
          (13 ^ 3)
          (proposition63PaperTauConstant actual.runtime.paperNested.nested) ≤
        internalConstant := by
    have htauConstant :
        proposition63PaperTauConstant actual.runtime.paperNested.nested =
          scalar.firstConstant.firstConstant *
            Kakeya.realRpowENN
              (scalar.scales.tau / scalar.scales.rhoHat.1) (1 - sigma) := by
      let seed := backward.seed index hindex
      let paperScales := scalar.scales.choicePaperScalePackage seed
        paperGlobal.prelude.discreteLoss_lt_half
      let runtimeFirst := proposition63_four_call_first_constant_choice
        (rho := scalar.scales.rhoHat.1) (tau := scalar.scales.tau)
        (sigma := sigma)
        (normalizationLoss := seed.schedule.third.normalizationLoss)
        (outputLoss := seed.schedule.thirdOutputLoss)
        (robustScale := paperScales.targetRequested.1)
        (epsilon₁ := seed.epsilon₁)
        (epsilon₃ := seed.paperAngularExponent) (incidence := incidence)
        (coefficient :=
          4 * (lipschitzExtensionConstant Point3 * sourceCoefficient))
        (by
          exact (grid.scale_pos _
            (scalar.scales.first_lt_second.le.trans
              scalar.scales.second_le_gridN)).trans_le
                scalar.scales.logicalR_le_rhoHat)
        scalar.scales.rhoHat_le_tau seed.sigma_lt_one
      change runtimeFirst.firstConstant *
          Kakeya.realRpowENN
            (scalar.scales.tau / scalar.scales.rhoHat.1) (1 - sigma) =
        scalar.firstConstant.firstConstant *
          Kakeya.realRpowENN
            (scalar.scales.tau / scalar.scales.rhoHat.1) (1 - sigma)
      have htarget : paperScales.targetRequested =
          scalar.paperScale.targetRequested := by
        apply Subtype.ext
        rw [paperScales.targetScale_eq, scalar.paperScale.targetScale_eq]
      calc
        runtimeFirst.firstConstant *
              Kakeya.realRpowENN
                (scalar.scales.tau / scalar.scales.rhoHat.1) (1 - sigma) =
            proposition63FourCallFirstArithmeticRequirement
              scalar.scales.rhoHat.1 scalar.scales.tau sigma
              seed.schedule.third.normalizationLoss
              seed.schedule.thirdOutputLoss paperScales.targetRequested.1
              seed.epsilon₁ seed.paperAngularExponent incidence
              (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)) :=
          runtimeFirst.normalized
        _ = proposition63FourCallFirstArithmeticRequirement
              scalar.scales.rhoHat.1 scalar.scales.tau sigma
              seed.schedule.third.normalizationLoss
              seed.schedule.thirdOutputLoss scalar.paperScale.targetRequested.1
              seed.epsilon₁ seed.paperAngularExponent incidence
              (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)) := by
          rw [htarget]
        _ = scalar.firstConstant.firstConstant *
              Kakeya.realRpowENN
                (scalar.scales.tau / scalar.scales.rhoHat.1) (1 - sigma) := by
          simpa only [seed] using scalar.firstConstant_value.symm
    rw [htauConstant]
    have h := proposition63_nestedCandidateIntervalBound_le_paper
      (sigma := sigma) (tau := scalar.scales.tau)
      (discreteLoss :=
        (backward.seed index hindex).alignedAbsorption.internalLoss)
      ((((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)) : NNReal) : ℝ)
      scalar.firstConstant.firstConstant scalar.nestedInterval
      paperGlobal.prelude.delta_pos hdeltaNested
      criticalInputs.query_pos
    simpa only [internalConstant, NNReal.coe_mul, NNReal.coe_ofNat] using h
  have hconstant : 2 * internalConstant ≤
      proposition63FourCallOrderedPairConstant grid index := by
    unfold proposition63FourCallOrderedPairConstant
    exact proposition63_aligned_internal_constant_le_ordered_pair_expression
      grid (backward.seed index hindex).alignedAbsorption
      paperGlobal.prelude.delta_pos
      (delta_le_aligned index hindex)
      (grid.scale_pos _
        ((finiteIntervalOrderedPair_valid hindex).1.le.trans
          (finiteIntervalOrderedPair_valid hindex).2))
      scalar.scales.logicalR_le_rhoHat scalar.scales.tau_eq
      scalar.scales.tau_pos.le
      (by
        have hsigmaOne :=
          (backward.seed index hindex).sigma_lt_one
        linarith)
      le_rfl
  have hleftBound := actual.paperLeft_le_actual
    (paperGlobal := paperGlobal) scalar
  have hrightBound := actual.actualRight_le_paperRight
    (paperGlobal := paperGlobal) scalar
  have hpaperLeft : proposition63FourCallPaperLeftFactor
      scalarFamily.pair index = scalar.paperLeft := by
    simp only [proposition63FourCallPaperLeftFactor, dif_pos hindex]
    rfl
  have hpaperRight : proposition63FourCallPaperRightFactor
      scalarFamily.pair index = scalar.paperRight := by
    simp only [proposition63FourCallPaperRightFactor, dif_pos hindex]
    rfl
  let currentInputs : Proposition63FourCallCurrentReceipt
      (sigma := sigma) current scalar.scales.rhoHat.1 := {
    scaleFactor := scalar.scales.scaleFactor
    scaleFactor_pos := scalar.scales.scaleFactor_pos
    rho_aligned := scalar.scales.rhoHat_aligned
    fineCurrentLoss := backward.loss index
    current_extremal := current_extremal
    current_cwa := current_cwa
  }
  let massInputs : Proposition63FourCallPaperMassReceipt
      (Proposition63NestedPointCoverData.FullGrainCells.nestedCandidateIntervalBound
        scalar.scales.rhoHat.1 scalar.scales.rhoHat.1
        (8 * (((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ) *
          scalar.scales.rhoHat.1)
        (((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ)
        (13 ^ 3)
        (proposition63PaperTauConstant actual.runtime.paperNested.nested))
      (proposition63DependentFinePullbackLeft actual.fineCurrentReentry
        actual.runtime.rich1.data actual.assembly.pullback.retentionFactor
        (ENNReal.ofReal ((criticalInputs.cellVolumeFloor / 2) /
            (4 * (2 * Real.sqrt scalar.scales.rhoHat.1) ^ 2)) *
          (((1 : ENNReal) / 2) /
            (2 * (planeInputs.coverBudget : ENNReal))) *
          (actual.runtime.paperNested.nested.secondRetainedFactor *
            ((73 / 100 : ENNReal) *
              actual.runtime.paperNested.nested.reentry.normalizationWeight) *
            actual.runtime.paperNested.nested.firstRetainedFactor)))
      (proposition63DependentFinePullbackRight actual.fineCurrentReentry
        ((actual.runtime.paperNested.nested.reentry.regularized.regularizationLoss *
            actual.runtime.paperNested.nested.prepared.preparationLoss) *
          (2 * ENNReal.ofReal (4 * scalar.scales.rhoHat.1))))
      delta criticalInputs.outputCandidateLoss (backward.loss index)
      ((4 : NNReal) * (lipschitzExtensionConstant Point3 * sourceCoefficient))
      criticalInputs.spatialScale criticalInputs.variationScale := {
    targetConstant := internalConstant
    targetLeft := scalar.paperLeft
    targetRight := scalar.paperRight
    constant_bound := hconstantLeft
    left_bound := by
      change scalar.paperLeft ≤
        proposition63DependentFinePullbackLeft actual.fineCurrentReentry
          actual.runtime.rich1.data actual.assembly.pullback.retentionFactor
          (ENNReal.ofReal ((scalar.cellFloor.cellVolumeFloor / 2) /
              (4 * (2 * Real.sqrt scalar.scales.rhoHat.1) ^ 2)) *
            (((1 : ENNReal) / 2) /
              (2 * (scalar.coverBudget.coverBudget : ENNReal))) *
            (actual.runtime.paperNested.nested.secondRetainedFactor *
              ((73 / 100 : ENNReal) *
                actual.runtime.paperNested.nested.reentry.normalizationWeight) *
              actual.runtime.paperNested.nested.firstRetainedFactor))
      exact hleftBound
    right_bound := hrightBound
    targetLeft_pos := scalar.paperLeft_pos
    targetLeft_finite := scalar.paperLeft_finite
    targetRight_finite := scalar.paperRight_finite
    currentOutput := (backward.loss_lt_next index hindex).le
    outputCandidateLoss_pos := backward.loss_pos (index + 1) (by omega)
    variation := le_rfl
  }
  have result := actual.run
    (paperLeftFactor := proposition63FourCallPaperLeftFactor scalarFamily.pair)
    (paperRightFactor := proposition63FourCallPaperRightFactor scalarFamily.pair)
    criticalInputs planeInputs currentInputs massInputs
    (paperGlobal.incidence_le_delta.trans scalar.scales.rhoHat.property.1)
    (by change (scalar.coverBudget.coverBudget : ENNReal) ≤ _
        exact scalar.coverBudget_upper) rfl hconstant
    hpaperLeft.symm hpaperRight.symm
  exact result

/-- Execute the complete paper-ordered inner grid from an arbitrary restored
current shading inside the frozen root.  The ambient plane map and every
pair-indexed scalar/schedule remain those selected before this current is
exposed. -/
theorem proposition63_four_call_paper_inner_schedule_run_from_current
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
    (rootInput : Proposition63FourCallRootInput root)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (legacyLeft legacyRight : ℕ → ENNReal)
    (sourceCoefficient : NNReal)
    (paperGlobal : Proposition63FourCallPaperGlobalData
      (incidence := incidence) K backward root grid
      legacyLeft legacyRight sourceCoefficient)
    (scalarFamily : Proposition63FourCallPaperScalarFamilyData
      (incidence := incidence) backward root grid sourceCoefficient)
    (delta_le_nested : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        delta ≤ (scalarFamily.pair index hindex).nestedInterval.delta₀)
    (delta_le_aligned : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        delta ≤ (backward.seed index hindex).alignedAbsorption.delta₀)
    (initial : WZ1PaperTubeShading root.normalization.croppedFamily)
    (initial_sub : PaperIsSubshading initial
      root.normalization.croppedRefined)
    (sourceMap : PaperWZ1WeakPlaneMapData
      initial incidence)
    (extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient)
    (hsourceCubical : WZ1PaperIsCubicalShading initial)
    (hsourceExtremal : WZ2PaperCroppedIsExtremal sigma (backward.loss 0)
      root.normalization.croppedFamily initial)
    (hsourceCWA : WZ2PaperConvexWolffBound
      root.normalization.croppedFamily
      (Kakeya.realRpowENN delta (-(backward.loss 0))))
    (hsourceMass : 0 < initial.mass)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    ∃ data : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := gridOutputLoss)
        (rho := queryScale) (Y := initial)
        (fun point => extension.ambient.planeMap point),
      (∀ point ∈ data.shading.union,
        data.shading.pointMultiplicity point =
          initial.pointMultiplicity point) ∧
      (∏ index ∈ Finset.range (finiteIntervalOrderedPairs gridN).length,
          proposition63FourCallPaperLeftFactor scalarFamily.pair index) *
          initial.mass ≤
        (∏ index ∈ Finset.range (finiteIntervalOrderedPairs gridN).length,
          proposition63FourCallPaperRightFactor scalarFamily.pair index) *
          data.shading.mass ∧
      0 < data.shading.mass := by
  let currentSchedules := proposition63FourCallPaperCurrentScheduleFamily
    K backward root grid legacyLeft legacyRight sourceCoefficient paperGlobal
  let step := proposition63_four_call_paper_step_of_scalar_family_from_current
    K backward
    root rootInput grid legacyLeft legacyRight sourceCoefficient paperGlobal
    scalarFamily delta_le_nested delta_le_aligned currentSchedules initial
    sourceMap extension initial_sub
  exact grid.runIteration initial
    extension.ambient.planeMap backward.loss
    (proposition63FourCallPaperLeftFactor scalarFamily.pair)
    (proposition63FourCallPaperRightFactor scalarFamily.pair)
    hsourceCubical hsourceExtremal hsourceCWA hsourceMass
    (fun index hindex => by
      simp only [proposition63FourCallPaperLeftFactor, dif_pos hindex]
      exact (scalarFamily.pair index hindex).paperLeft_pos)
    step backward.final_loss
    extension.ambient.unit
    hsourceExtremal.delta_pos hsourceExtremal.delta_le_one hsigma hsigmaOne

/-- Root-specialized compatibility wrapper for the M6 API. -/
theorem proposition63_four_call_paper_inner_schedule_run
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
    (rootInput : Proposition63FourCallRootInput root)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (legacyLeft legacyRight : ℕ → ENNReal)
    (sourceCoefficient : NNReal)
    (paperGlobal : Proposition63FourCallPaperGlobalData
      (incidence := incidence) K backward root grid
      legacyLeft legacyRight sourceCoefficient)
    (scalarFamily : Proposition63FourCallPaperScalarFamilyData
      (incidence := incidence) backward root grid sourceCoefficient)
    (delta_le_nested : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        delta ≤ (scalarFamily.pair index hindex).nestedInterval.delta₀)
    (delta_le_aligned : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        delta ≤ (backward.seed index hindex).alignedAbsorption.delta₀)
    (sourceMap : PaperWZ1WeakPlaneMapData
      root.normalization.croppedRefined incidence)
    (extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient)
    (hsourceCubical :
      WZ1PaperIsCubicalShading root.normalization.croppedRefined)
    (hsourceExtremal : WZ2PaperCroppedIsExtremal sigma (backward.loss 0)
      root.normalization.croppedFamily root.normalization.croppedRefined)
    (hsourceCWA : WZ2PaperConvexWolffBound
      root.normalization.croppedFamily
      (Kakeya.realRpowENN delta (-(backward.loss 0))))
    (hsourceMass : 0 < root.normalization.croppedRefined.mass)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    ∃ data : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := gridOutputLoss)
        (rho := queryScale) (Y := root.normalization.croppedRefined)
        (fun point => extension.ambient.planeMap point),
      (∀ point ∈ data.shading.union,
        data.shading.pointMultiplicity point =
          root.normalization.croppedRefined.pointMultiplicity point) ∧
      (∏ index ∈ Finset.range (finiteIntervalOrderedPairs gridN).length,
          proposition63FourCallPaperLeftFactor scalarFamily.pair index) *
          root.normalization.croppedRefined.mass ≤
        (∏ index ∈ Finset.range (finiteIntervalOrderedPairs gridN).length,
          proposition63FourCallPaperRightFactor scalarFamily.pair index) *
          data.shading.mass ∧
      0 < data.shading.mass := by
  exact proposition63_four_call_paper_inner_schedule_run_from_current K
    backward root rootInput grid legacyLeft legacyRight sourceCoefficient
    paperGlobal scalarFamily delta_le_nested delta_le_aligned
    root.normalization.croppedRefined
    (fun _ _ point_mem => point_mem) sourceMap extension hsourceCubical
    hsourceExtremal hsourceCWA hsourceMass hsigma hsigmaOne

end Kakeya.Assouad.PureWZ2
