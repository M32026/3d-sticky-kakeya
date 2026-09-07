import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallFinalAssembly

/-! # Full four-call final candidate assembly -/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- Run the critical-floor tail on the exact nested cover and pullback stored
in this runtime assembly. -/
theorem Proposition63FourCallRuntimeAssemblyData.finalCandidate
    {delta sigma inputLoss normalizationLoss outputLoss tau firstLoss
      secondLoss finalLoss incidence fineReentryLoss : ℝ}
    {fineSource : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {fineNormalizationExponent : ℕ}
    {fineNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) fineSource fineNormalizationExponent}
    {fineCurrent : WZ1PaperTubeShading fineNormalized.croppedFamily}
    {fineCurrentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) fineNormalized fineCurrent}
    {schedule : Proposition63RichFourCallScheduleData sigma outputLoss}
    {hfineReentryLoss : 0 < fineReentryLoss}
    {rho : WZ2PaperRequestedScale delta}
    {rootAxialWindow : ∀ index point,
      point ∈ (fineCurrentReentry.normalization.toPropStickyReentryData
          hfineReentryLoss
          fineCurrentReentry.reentry_normalization_loss_pos).geometry.frame ''
          (fineCurrentReentry.normalization.toPropStickyReentryData
            hfineReentryLoss
            fineCurrentReentry.reentry_normalization_loss_pos).geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8}
    {sourceCoefficient : NNReal}
    {robustScale targetScale sqrtRequested : WZ2PaperRequestedScale rho.1}
    {firstConstant finalConstant : ENNReal}
    (runtime : Proposition63FourCallRuntimeAssemblyData
      (tau := tau) (firstLoss := firstLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (incidence := incidence)
      fineCurrentReentry schedule hfineReentryLoss rho rootAxialWindow
      sourceCoefficient robustScale targetScale sqrtRequested
      firstConstant finalConstant)
    (criticalInputs : Proposition63FourCallCriticalTailInputs runtime)
    (planeInputs : Proposition63FourCallPlaneCoverReceipt
      runtime.currentMap.planeMap
      runtime.nested.prepared.refined.shading.union rho.1 tau
      (finalConstant * Kakeya.realRpowENN
        (sqrtRequested.1 / rho.1) (1 - sigma)))
    (currentInputs : Proposition63FourCallCurrentReceipt
      (sigma := sigma) fineCurrent rho.1)
    (massInputs : Proposition63FourCallMassReceipt
      (Proposition63NestedPointCoverData.FullGrainCells.nestedCandidateIntervalBound
        rho.1 rho.1 (8 * (planeInputs.coefficient : ℝ) * rho.1)
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
      delta criticalInputs.outputCandidateLoss currentInputs.fineCurrentLoss
      planeInputs.coefficient criticalInputs.spatialScale
      criticalInputs.variationScale) :
    ∃ next : WZ1PaperTubeShading fineNormalized.croppedFamily,
      PaperIsSubshading next fineCurrent ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union, next.pointMultiplicity point =
        fineCurrent.pointMultiplicity point) ∧
      WZ2PaperCroppedIsExtremal sigma criticalInputs.outputCandidateLoss
        fineNormalized.croppedFamily next ∧
      WZ2PaperConvexWolffBound fineNormalized.croppedFamily
        (Kakeya.realRpowENN delta (-criticalInputs.outputCandidateLoss)) ∧
      PureWZ2IntervalCoveringAt next runtime.currentMap.planeMap rho.1
        (Real.toNNReal rho.1) (Real.toNNReal tau)
          massInputs.targetConstant ∧
      massInputs.targetLeft * fineCurrent.mass ≤
        massInputs.targetRight * next.mass ∧
      (∀ first ∈ next.union, ∀ second ∈ next.union,
        dist first second ≤ criticalInputs.spatialScale →
          dist (runtime.currentMap.planeMap first)
            (runtime.currentMap.planeMap second) ≤
              criticalInputs.variationScale) := by
  exact runtime.pullback.finalCandidate_of_pure_critical_trace
    fineCurrentReentry runtime.rich1.data runtime.targetReentry.normalization
    runtime.currentMap.planeMap
    (firstConstant * Kakeya.realRpowENN (tau / rho.1) (1 - sigma))
    (finalConstant * Kakeya.realRpowENN
      (sqrtRequested.1 / rho.1) (1 - sigma))
    runtime.nested criticalInputs.critical criticalInputs.coarseCritical
    criticalInputs.finalStructural criticalInputs.traceAbsorption
    criticalInputs.cellVolumeFloor_pos criticalInputs.cellBudget
    criticalInputs.query_pos
    criticalInputs.query_le_one criticalInputs.tau_pos
    criticalInputs.query_le_tau criticalInputs.tau_le_sqrt
    criticalInputs.sqrtScale_eq planeInputs.plane_unit
    planeInputs.coefficient planeInputs.coefficient_one
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
    massInputs.restore massInputs.variation

end Kakeya.Assouad.PureWZ2
