import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperRuntimeAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallFinalCandidate
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPullbackReceipt

/-!
# Final pullback assembly for the paper-ordered four-call runtime

The paper runtime has already restored the call-three point cover to the
call-two ancestor.  Consequently the final pullback must start from that
restored shading.  Reusing the legacy four-call pullback producer here would
apply the call-three refinement a second time.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- The exact retained coefficient from the call-one coarse witness to the
already restored paper nested current. -/
noncomputable def proposition63FourCallPaperPullbackCoefficient
    (delta : ℝ) (restoredFactor firstPullbackFactor : ENNReal) : ENNReal :=
  restoredFactor *
    (wz2PaperPureRefinementFraction delta 61 * firstPullbackFactor⁻¹)

/-- The unique first pullback attached to a paper runtime. -/
noncomputable def Proposition63FourCallPaperRuntimeAssemblyData.firstPullback
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
    {sourceCoefficient : NNReal}
    {global : Proposition63FourCallPaperPreludeGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient}
    {index : ℕ}
    {hindex : index < (finiteIntervalOrderedPairs gridN).length}
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
    Proposition63DependentCoarseReentryData
      (reentryLoss :=
        runtime.currentResult.currentReentry.reentryNormalizationLoss)
      runtime.rich1.data 0 :=
  proposition63_four_call_first_pullback_of_runtime_witnesses
    (backward.seed index hindex).schedule runtime.rich1 rootAxialWindow
    runtime.currentResult.currentReentry

/-- A lightweight exact pullback wrapper.  Keeping the endpoints explicit
avoids repeatedly reducing the full dependent runtime during elaboration. -/
structure Proposition63FourCallPaperFinalAssemblyData
    {delta : ℝ} {innerFamily outerFamily : Kakeya.Streamlined.TubeFamily delta}
    (inner : WZ1PaperTubeShading innerFamily)
    (outer : WZ1PaperTubeShading outerFamily) (coefficient : ENNReal) where
  pullback : Proposition63FourCallPullbackData inner outer
  retentionFactor_eq : pullback.retentionFactor = coefficient⁻¹

/-- Construct the unique call2-rooted whole-cell pullback.  The call-three
cover was already restored by `paperNested.restoredFirst`; this theorem only
composes that retained mass with call two and the call-one coarse ancestry. -/
theorem proposition63_four_call_paper_final_assembly
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
    {sourceCoefficient : NNReal}
    {global : Proposition63FourCallPaperPreludeGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient}
    {index : ℕ}
    {hindex : index < (finiteIntervalOrderedPairs gridN).length}
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
    Nonempty (Proposition63FourCallPaperFinalAssemblyData
      runtime.paperNested.nested.current
      runtime.rich1.data.croppedCoarseShading
      (proposition63FourCallPaperPullbackCoefficient scales.rhoHat.1
        runtime.paperNested.restoredFirst.retainedFactor
        runtime.firstPullback.retentionFactor)) := by
  let seed := backward.seed index hindex
  let schedule := seed.schedule
  let p1 := runtime.firstPullback
  let fraction : ENNReal :=
    wz2PaperPureRefinementFraction scales.rhoHat.1 61
  let retainedCoefficient : ENNReal :=
    runtime.paperNested.restoredFirst.retainedFactor *
      (fraction * p1.retentionFactor⁻¹)
  have hp1Normalization :
      p1.normalization = runtime.currentResult.currentReentry.normalization := by
    rfl
  let pullback : Proposition63FourCallPullbackData
      runtime.paperNested.nested.current
      runtime.rich1.data.croppedCoarseShading := {
    embedding := p1.coarseEmbedding
    tube_eq := p1.coarse_tube_eq
    subshading := by
      intro innerIndex point hpoint
      apply p1.normalized_subshading innerIndex
      apply extendShading_subshading runtime.paperNested.outer.data.selected
        runtime.paperNested.outer.data.subshading innerIndex
      apply runtime.paperNested.restoredFirst.state.subshading innerIndex
      rw [← runtime.paperNested.nested_eq]
      exact hpoint
    retentionFactor := retainedCoefficient⁻¹
    retained_mass := by
      rw [inv_inv]
      calc
        retainedCoefficient * runtime.rich1.data.croppedCoarseShading.mass =
            runtime.paperNested.restoredFirst.retainedFactor *
              (fraction *
                (p1.retentionFactor⁻¹ *
                  runtime.rich1.data.croppedCoarseShading.mass)) := by
          simp only [retainedCoefficient]
          ring
        _ ≤ runtime.paperNested.restoredFirst.retainedFactor *
              (fraction * p1.normalization.croppedRefined.mass) := by
          gcongr
          exact p1.retained_mass
        _ ≤ runtime.paperNested.restoredFirst.retainedFactor *
              (extendShading runtime.paperNested.outer.data.selected
                runtime.paperNested.outer.data.refined).mass := by
          gcongr
          rw [hp1Normalization]
          simpa only [fraction, extendShading_mass] using
            runtime.paperNested.outer.total_mass_retention
        _ ≤ runtime.paperNested.restoredFirst.state.shading.mass :=
          runtime.paperNested.restoredFirst.retained
        _ = runtime.paperNested.nested.current.mass := by
          rw [runtime.paperNested.nested_eq]
  }
  refine ⟨{
    pullback := pullback
    retentionFactor_eq := ?_
  }⟩
  rfl

/-- Consumer-facing projection with the exact type accepted by the legacy
final-candidate tail. -/
def Proposition63FourCallPaperFinalAssemblyData.finalCandidatePullback
    {delta : ℝ}
    {innerFamily outerFamily : Kakeya.Streamlined.TubeFamily delta}
    {inner : WZ1PaperTubeShading innerFamily}
    {outer : WZ1PaperTubeShading outerFamily}
    {coefficient : ENNReal}
    (assembly : Proposition63FourCallPaperFinalAssemblyData inner outer coefficient) :
    Proposition63FourCallPullbackData inner outer :=
  assembly.pullback

/-- Lightweight scalar and critical-floor receipts for the paper runtime.
They mention only the endpoints used by the final-candidate theorem, avoiding
reduction of the full dependent runtime while checking the wrapper. -/
structure Proposition63FourCallPaperCriticalTailReceipt
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed sigma outputLoss discreteLoss)
    (rho sqrtScale : ℝ) where
  cellVolumeFloor : ℝ
  outputCandidateLoss : ℝ
  spatialScale : ℝ
  variationScale : ℝ
  coarseCritical : rho ≤ seed.critical.delta₀
  finalStructural : seed.finalLoss ≤ seed.critical.structuralLoss
  traceAbsorption : Proposition63PureCriticalTailTraceAbsorption rho
    seed.critical.structuralLoss seed.schedule.fourth.sourceLoss seed.finalLoss
  cellVolumeFloor_pos : 0 < cellVolumeFloor
  cellBudget : ENNReal.ofReal cellVolumeFloor *
      Kakeya.realRpowENN sqrtScale
        (sigma - seed.fourthKernel.internalLoss) ≤
    Kakeya.realRpowENN rho (sigma + seed.floorLoss) *
      Kakeya.realRpowENN sqrtScale 3
  query_pos : 0 < rho
  query_le_one : rho ≤ 1

structure Proposition63FourCallPaperPlaneCoverReceipt
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant)
    (rho tau : ℝ) (coefficient : NNReal) where
  plane_unit : ∀ point ∈ data.prepared.refined.shading.union,
    ‖planeMap point‖ = 1
  coefficient_one : 1 ≤ (coefficient : ℝ)
  plane_lipschitz : LipschitzWith coefficient planeMap
  coverBudget : ℕ
  coverBudget_pos : 0 < coverBudget
  cover_budget : (512 : ENNReal) *
      ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
        sqrtConstant) ≤ (coverBudget : ENNReal)
  sqrtConstant_finite : sqrtConstant ≠ ⊤
  normalErrorTau : 8 * (coefficient : ℝ) * rho ≤ tau
  hullTau : rho * Real.sqrt 3 ≤ tau

structure Proposition63FourCallPaperMassReceipt
    (constantLeft leftExpression rightExpression : ENNReal)
    (delta outputCandidateLoss fineCurrentLoss coefficient spatialScale
      variationScale : ℝ) where
  targetConstant : ENNReal
  targetLeft : ENNReal
  targetRight : ENNReal
  constant_bound : constantLeft ≤ targetConstant
  left_bound : targetLeft ≤ leftExpression
  right_bound : rightExpression ≤ targetRight
  targetLeft_pos : 0 < targetLeft
  targetLeft_finite : targetLeft ≠ ⊤
  targetRight_finite : targetRight ≠ ⊤
  currentOutput : fineCurrentLoss ≤ outputCandidateLoss
  outputCandidateLoss_pos : 0 < outputCandidateLoss
  variation : coefficient * spatialScale ≤ variationScale

/-- Retype an actual current re-entry as the exact PropSticky input expected
by the frozen paper schedule. -/
noncomputable def Proposition63CurrentShadingReentryData.paperPropStickyReentry
    {delta sigma inputLoss normalizationLoss scheduledNormalizationLoss
      reentryLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {current : WZ1PaperTubeShading normalized.croppedFamily}
    (fineCurrentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) normalized current)
    (hreentryLoss : 0 < reentryLoss)
    (hnormalization : fineCurrentReentry.reentryNormalizationLoss =
      scheduledNormalizationLoss) :
    PureWZ2PropStickyReentryData (sigma := sigma)
      fineCurrentReentry.normalization.croppedRefined normalizationExponent
      reentryLoss scheduledNormalizationLoss := by
  simpa only [hnormalization] using
    (fineCurrentReentry.normalization.toPropStickyReentryData
      hreentryLoss fineCurrentReentry.reentry_normalization_loss_pos)

/-- The paper-specific final consumer.  It uses the already assembled
call2-rooted pullback and invokes the pure-critical final tail exactly once. -/
theorem Proposition63FourCallPaperFinalAssemblyData.finalCandidate
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale fineInputLoss fineNormalizationLoss : ℝ}
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
    {sourceCoefficient : NNReal}
    {global : Proposition63FourCallPaperPreludeGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient}
    {index : ℕ}
    {hindex : index < (finiteIntervalOrderedPairs gridN).length}
    {scales : Proposition63FourCallOrderedPairIndexScales grid index}
    {fineSource : PureWZ2ExtremalConfiguration sigma fineInputLoss delta}
    {fineNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := fineNormalizationLoss) fineSource normalizationExponent}
    {fineCurrent : WZ1PaperTubeShading fineNormalized.croppedFamily}
    (fineCurrentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := (backward.seed index hindex).schedule.first.sourceLoss)
      fineNormalized fineCurrent)
    (hnormalization : fineCurrentReentry.reentryNormalizationLoss =
      (backward.seed index hindex).schedule.first.normalizationLoss)
    {rootAxialWindow : ∀ sourceIndex point,
      point ∈ (fineCurrentReentry.paperPropStickyReentry
          (backward.seed index hindex).schedule.first.sourceLoss_pos
          hnormalization).geometry.frame ''
          (fineCurrentReentry.paperPropStickyReentry
            (backward.seed index hindex).schedule.first.sourceLoss_pos
            hnormalization).geometry.ordinaryRefined.carrier
              sourceIndex →
        |point (2 : Fin 3)| ≤ 1 / 8}
    {sourceMap : PaperWZ1WeakPlaneMapData
      fineCurrentReentry.normalization.croppedRefined incidence}
    {extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient}
    (runtime : Proposition63FourCallPaperRuntimeAssemblyData
      (fineShading := fineCurrentReentry.normalization.croppedRefined)
      (fineReentry := fineCurrentReentry.paperPropStickyReentry
        (backward.seed index hindex).schedule.first.sourceLoss_pos
        hnormalization)
      (rootAxialWindow := rootAxialWindow) (extension := extension) K backward
      root grid leftFactor rightFactor sourceCoefficient global index hindex
      scales)
    (assembly : Proposition63FourCallPaperFinalAssemblyData
      runtime.paperNested.nested.current runtime.rich1.data.croppedCoarseShading
      (proposition63FourCallPaperPullbackCoefficient scales.rhoHat.1
        runtime.paperNested.restoredFirst.retainedFactor
        runtime.firstPullback.retentionFactor))
    (criticalInputs : Proposition63FourCallPaperCriticalTailReceipt
      (backward.seed index hindex) scales.rhoHat.1
      (Real.sqrt scales.rhoHat.1)) :
    let seed := backward.seed index hindex
    let paperScales := scales.choicePaperScalePackage seed
      global.discreteLoss_lt_half
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
    ∀
    (planeInputs : Proposition63FourCallPaperPlaneCoverReceipt
      runtime.paperNested.nested scales.rhoHat.1 scales.tau
      (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)))
    (currentInputs : Proposition63FourCallCurrentReceipt
      (sigma := sigma) fineCurrent scales.rhoHat.1)
    (massInputs : Proposition63FourCallPaperMassReceipt
      (Proposition63NestedPointCoverData.FullGrainCells.nestedCandidateIntervalBound
        scales.rhoHat.1 scales.rhoHat.1
        (8 * (((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ) *
          scales.rhoHat.1)
        (((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ) (13 ^ 3)
        (firstChoice.firstConstant *
          Kakeya.realRpowENN (scales.tau / scales.rhoHat.1) (1 - sigma)))
      (proposition63DependentFinePullbackLeft fineCurrentReentry
        runtime.rich1.data assembly.pullback.retentionFactor
        (ENNReal.ofReal ((criticalInputs.cellVolumeFloor / 2) /
            (4 * (2 * Real.sqrt scales.rhoHat.1) ^ 2)) *
          (((1 : ENNReal) / 2) / (2 * (planeInputs.coverBudget : ENNReal))) *
          (runtime.paperNested.nested.secondRetainedFactor *
            ((73 / 100 : ENNReal) *
              runtime.paperNested.nested.reentry.normalizationWeight) *
            runtime.paperNested.nested.firstRetainedFactor)))
      (proposition63DependentFinePullbackRight fineCurrentReentry
        ((runtime.paperNested.nested.reentry.regularized.regularizationLoss *
            runtime.paperNested.nested.prepared.preparationLoss) *
          (2 * ENNReal.ofReal (4 * scales.rhoHat.1))))
      delta criticalInputs.outputCandidateLoss currentInputs.fineCurrentLoss
      ((4 : NNReal) * (lipschitzExtensionConstant Point3 * sourceCoefficient))
      criticalInputs.spatialScale
      criticalInputs.variationScale)
    (hrestore : proposition63Lemma43MassLoss
        massInputs.targetLeft massInputs.targetRight *
          Kakeya.realRpowENN delta criticalInputs.outputCandidateLoss ≤
        Kakeya.realRpowENN delta currentInputs.fineCurrentLoss),
    ∃ next : WZ1PaperTubeShading fineNormalized.croppedFamily,
      PaperIsSubshading next fineCurrent ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union, next.pointMultiplicity point =
        fineCurrent.pointMultiplicity point) ∧
      WZ2PaperCroppedIsExtremal sigma criticalInputs.outputCandidateLoss
        fineNormalized.croppedFamily next ∧
      WZ2PaperConvexWolffBound fineNormalized.croppedFamily
        (Kakeya.realRpowENN delta (-criticalInputs.outputCandidateLoss)) ∧
      PureWZ2IntervalCoveringAt next runtime.currentResult.currentMap.planeMap
        scales.rhoHat.1 (Real.toNNReal scales.rhoHat.1)
        (Real.toNNReal scales.tau) massInputs.targetConstant ∧
      massInputs.targetLeft * fineCurrent.mass ≤
        massInputs.targetRight * next.mass ∧
      (∀ first ∈ next.union, ∀ second ∈ next.union,
        dist first second ≤ criticalInputs.spatialScale →
          dist (runtime.currentResult.currentMap.planeMap first)
            (runtime.currentResult.currentMap.planeMap second) ≤
              criticalInputs.variationScale) := by
  dsimp only
  intro planeInputs currentInputs massInputs hrestore
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
  exact assembly.pullback.finalCandidate_of_pure_critical_trace
    fineCurrentReentry runtime.rich1.data
    runtime.currentResult.currentReentry.normalization
    runtime.currentResult.currentMap.planeMap
    (firstChoice.firstConstant *
      Kakeya.realRpowENN (scales.tau / scales.rhoHat.1) (1 - sigma))
    (finalChoice.finalConstant * Kakeya.realRpowENN
      (Real.sqrt scales.rhoHat.1 / scales.rhoHat.1) (1 - sigma))
    runtime.paperNested.nested
    seed.critical criticalInputs.coarseCritical
    criticalInputs.finalStructural criticalInputs.traceAbsorption
    criticalInputs.cellVolumeFloor_pos criticalInputs.cellBudget
    criticalInputs.query_pos criticalInputs.query_le_one scales.tau_pos
    scales.rhoHat_le_tau
    (scales.tau_le_sqrt_logicalR.trans (Real.sqrt_le_sqrt scales.logicalR_le_rhoHat))
    rfl planeInputs.plane_unit
    ((4 : NNReal) * (lipschitzExtensionConstant Point3 * sourceCoefficient))
    planeInputs.coefficient_one
    planeInputs.plane_lipschitz planeInputs.coverBudget
    planeInputs.coverBudget_pos planeInputs.cover_budget
    planeInputs.sqrtConstant_finite planeInputs.normalErrorTau
    planeInputs.hullTau currentInputs.scaleFactor
    currentInputs.scaleFactor_pos currentInputs.rho_aligned
    currentInputs.fineCurrentLoss currentInputs.current_extremal
    currentInputs.current_cwa massInputs.targetConstant
    massInputs.targetLeft massInputs.targetRight massInputs.constant_bound
    massInputs.left_bound massInputs.right_bound massInputs.targetLeft_pos
    massInputs.targetLeft_finite massInputs.targetRight_finite
    massInputs.currentOutput massInputs.outputCandidateLoss_pos
    hrestore massInputs.variation

end Kakeya.Assouad.PureWZ2
