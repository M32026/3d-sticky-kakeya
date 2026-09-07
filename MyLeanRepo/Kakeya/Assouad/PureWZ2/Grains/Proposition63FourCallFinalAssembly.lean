import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallFinalCandidate

/-! # Full four-call runtime assembly -/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- The concrete witnesses produced by the four scheduled calls, packaged in
dependency order so later numerical inputs can refer to the exact runtime. -/
structure Proposition63FourCallRuntimeAssemblyData
    {delta sigma inputLoss normalizationLoss outputLoss tau firstLoss
      secondLoss finalLoss incidence fineReentryLoss : ℝ}
    {fineSource : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {fineNormalizationExponent : ℕ}
    {fineNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) fineSource fineNormalizationExponent}
    {fineCurrent : WZ1PaperTubeShading fineNormalized.croppedFamily}
    (fineCurrentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) fineNormalized fineCurrent)
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss)
    (hfineReentryLoss : 0 < fineReentryLoss)
    (rho : WZ2PaperRequestedScale delta)
    (rootAxialWindow : ∀ index point,
      point ∈ (fineCurrentReentry.normalization.toPropStickyReentryData
          hfineReentryLoss
          fineCurrentReentry.reentry_normalization_loss_pos).geometry.frame ''
          (fineCurrentReentry.normalization.toPropStickyReentryData
            hfineReentryLoss
            fineCurrentReentry.reentry_normalization_loss_pos).geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (sourceCoefficient : NNReal)
    (robustScale targetScale sqrtRequested : WZ2PaperRequestedScale rho.1)
    (firstConstant finalConstant : ENNReal) where
  rich1 : Proposition63RichTerminalStickyData
    (outputLoss := schedule.firstOutputLoss)
    fineCurrentReentry.normalization.croppedRefined
    (fineCurrentReentry.normalization.toPropStickyReentryData
      hfineReentryLoss fineCurrentReentry.reentry_normalization_loss_pos) rho
  currentMap : PaperWZ1WeakPlaneMapData rich1.terminal.sourceWitness.shading
    (proposition63DependentCoarseIncidence rho.1 incidence
      (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)))
  currentLipschitz : LipschitzWith
    (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient))
    currentMap.planeMap
  currentReentry : Proposition63CurrentShadingReentryData
    (reentryLoss := schedule.second.sourceLoss)
    (schedule.callOneRhoRootNormalization rich1 rootAxialWindow)
    rich1.terminal.sourceWitness.shading
  currentNormalization : currentReentry.reentryNormalizationLoss =
    schedule.second.normalizationLoss
  outer : Proposition63RichTerminalStickyData
    (outputLoss := schedule.secondOutputLoss)
    currentReentry.normalization.croppedRefined
    (currentReentry.normalization.toPropStickyReentryData
      schedule.second.sourceLoss_pos
      currentReentry.reentry_normalization_loss_pos) robustScale
  targetReentry : Proposition63CurrentShadingReentryData
    (reentryLoss := schedule.third.sourceLoss) currentReentry.normalization
    (extendShading outer.data.selected outer.data.refined)
  target : Proposition63RichTerminalStickyData
    (outputLoss := schedule.thirdOutputLoss)
    targetReentry.normalization.croppedRefined
    (targetReentry.normalization.toPropStickyReentryData
      schedule.third.sourceLoss_pos
      targetReentry.reentry_normalization_loss_pos) targetScale
  targetNormalization : targetReentry.reentryNormalizationLoss =
    schedule.third.normalizationLoss
  nested : Proposition63NestedPointCoverData
    (firstLoss := firstLoss) (reentryLoss := schedule.fourth.sourceLoss)
    (sqrtStickyLoss := outputLoss) (secondLoss := secondLoss)
    (finalLoss := finalLoss) (queryScale := rho.1)
    (tauScale := tau) (sqrtScale := sqrtRequested.1)
    targetReentry.normalization currentMap.planeMap
    (firstConstant * Kakeya.realRpowENN (tau / rho.1) (1 - sigma))
    (finalConstant * Kakeya.realRpowENN
      (sqrtRequested.1 / rho.1) (1 - sigma))
  nested_eq : nested.current =
    extendShading target.data.selected target.data.refined
  pullback : Proposition63FourCallPullbackData nested.current
    rich1.data.croppedCoarseShading

/-- Numerical and critical-floor receipts for the exact runtime selected by
the four-call assembly.  No nested cover or ancestry pullback is supplied by
the caller: both are fields of `runtime`. -/
structure Proposition63FourCallCriticalTailInputs
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
      firstConstant finalConstant) where
  floorLoss : ℝ
  structuralBudget : ℝ
  cellVolumeFloor : ℝ
  outputCandidateLoss : ℝ
  spatialScale : ℝ
  variationScale : ℝ
  critical : PureWZ2CriticalFloorSelectionData
    sigma floorLoss structuralBudget
  coarseCritical : rho.1 ≤ critical.delta₀
  finalStructural : finalLoss ≤ critical.structuralLoss
  traceAbsorption : Proposition63PureCriticalTailTraceAbsorption rho.1
    critical.structuralLoss schedule.fourth.sourceLoss finalLoss
  cellVolumeFloor_pos : 0 < cellVolumeFloor
  cellBudget : ENNReal.ofReal cellVolumeFloor *
      Kakeya.realRpowENN sqrtRequested.1 (sigma - outputLoss) ≤
    Kakeya.realRpowENN rho.1 (sigma + floorLoss) *
      Kakeya.realRpowENN sqrtRequested.1 3
  query_pos : 0 < rho.1
  query_le_one : rho.1 ≤ 1
  tau_pos : 0 < tau
  query_le_tau : rho.1 ≤ tau
  tau_le_sqrt : tau ≤ Real.sqrt rho.1
  sqrtScale_eq : sqrtRequested.1 = Real.sqrt rho.1

structure Proposition63FourCallPlaneCoverReceipt
    (planeMap : Point3 → Point3) (points : Set Point3)
    (rho tau : ℝ) (sqrtConstant : ENNReal) where
  plane_unit : ∀ point ∈ points, ‖planeMap point‖ = 1
  coefficient : NNReal
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

structure Proposition63FourCallCurrentReceipt
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (current : WZ1PaperTubeShading family) (rho : ℝ) where
  scaleFactor : ℕ
  scaleFactor_pos : 0 < scaleFactor
  rho_aligned : rho = (scaleFactor : ℝ) * delta
  fineCurrentLoss : ℝ
  current_extremal : WZ2PaperCroppedIsExtremal sigma fineCurrentLoss
    family current
  current_cwa : WZ2PaperConvexWolffBound family
    (Kakeya.realRpowENN delta (-fineCurrentLoss))

structure Proposition63FourCallMassReceipt
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
  restore : proposition63Lemma43MassLoss targetLeft targetRight *
      Kakeya.realRpowENN delta outputCandidateLoss ≤
    Kakeya.realRpowENN delta fineCurrentLoss
  variation : coefficient * spatialScale ≤ variationScale



end Kakeya.Assouad.PureWZ2
