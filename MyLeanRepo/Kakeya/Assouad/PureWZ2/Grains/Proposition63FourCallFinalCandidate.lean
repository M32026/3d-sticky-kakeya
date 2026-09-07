import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPullbackReceipt

/-!
# Direct final candidate from the four-call producer

This module records the exact five-stage ancestry mass ledger carried by the
four scheduled calls and exposes the unique final-candidate invocation.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- The exact ancestry package carried from the final nested current shading
back to the coarse shading of call one. -/
structure Proposition63FourCallPullbackData
    {delta : ℝ}
    {innerFamily outerFamily : Kakeya.Streamlined.TubeFamily delta}
    (inner : WZ1PaperTubeShading innerFamily)
    (outer : WZ1PaperTubeShading outerFamily) where
  embedding : Fin innerFamily.card ↪ Fin outerFamily.card
  tube_eq : ∀ index, innerFamily.tube index =
    outerFamily.tube (embedding index)
  subshading : ∀ index, inner.carrier index ⊆
    outer.carrier (embedding index)
  retentionFactor : ENNReal
  retained_mass : retentionFactor⁻¹ * outer.mass ≤ inner.mass

/-- Start the final ancestry ledger at call one's honest coarse source witness.
The only loss here is the actual coarse multiplicity cap of that call; the
following rich calls receive the freshly restored re-entry, not this product. -/
noncomputable def proposition63_four_call_first_pullback_of_runtime_witnesses
    {delta sigma inputLoss normalizationLoss outputLoss reentryLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent : ℕ}
    {fineReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading normalizationExponent inputLoss
      normalizationLoss}
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss)
    (rich1 : Proposition63RichTerminalStickyData
      (outputLoss := schedule.firstOutputLoss) sourceShading fineReentry rho)
    (rootAxialWindow : ∀ index point,
      point ∈ fineReentry.geometry.frame ''
          fineReentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (currentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss)
      (schedule.callOneRhoRootNormalization rich1 rootAxialWindow)
      rich1.terminal.sourceWitness.shading) :
    Proposition63DependentCoarseReentryData
      (reentryLoss := currentReentry.reentryNormalizationLoss)
      rich1.data 0 := by
  let cap : ENNReal :=
    Kakeya.realRpowENN rho.1 (2 - sigma - schedule.firstOutputLoss) *
      rich1.data.coarse.enncard
  have hpowerPos :
      0 < Kakeya.realRpowENN rho.1
        (2 - sigma - schedule.firstOutputLoss) := by
    exact ENNReal.ofReal_pos.mpr <|
      Real.rpow_pos_of_pos rich1.data.coarse_extremal.delta_pos _
  have hcardPos : 0 < rich1.data.coarse.enncard := by
    change (0 : ENNReal) < (rich1.data.coarse.card : ENNReal)
    exact_mod_cast rich1.data.coarse_extremal.nonempty
  have hcapPos : 0 < cap := by
    exact ENNReal.mul_pos hpowerPos.ne' hcardPos.ne'
  have hcapTop : cap ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN])
      (by simp [Kakeya.Streamlined.TubeFamily.enncard])
  have hretained : cap⁻¹ * rich1.data.croppedCoarseShading.mass ≤
      rich1.terminal.sourceWitness.shading.mass := by
    exact source_witness_coarse_shading_mass_lower
      rich1.terminal.sourceWitness cap hcapPos.ne' hcapTop
      rich1.data.coarse_multiplicity_upper
  have hsub : ∀ index,
      rich1.terminal.sourceWitness.shading.carrier index ⊆
        rich1.data.croppedCoarseShading.carrier index := by
    intro index point hpoint
    exact rich1.terminal.sourceWitness.subshading index hpoint
  exact proposition63DependentCoarseReentryOfCurrent rich1.data
    (schedule.callOneRhoRootNormalization rich1 rootAxialWindow)
    rich1.terminal.sourceWitness.shading currentReentry
    (Function.Embedding.refl _) (fun _ => rfl) hsub cap hcapPos hcapTop
    hretained

/-- Feed the already reconstructed M4 ancestry pullback into the numerical
and geometric critical-floor tail. -/
theorem Proposition63FourCallPullbackData.finalCandidate_of_critical_floor
    {fineDelta sigma fineInputLoss fineNormalizationLoss fineReentryLoss
      outerLoss coarseInputLoss coarseNormalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss tauScale sqrtScale outputLoss
      spatialScale variationScale floorLoss structuralBudget cellVolumeFloor : ℝ}
    {fineSource : PureWZ2ExtremalConfiguration sigma fineInputLoss fineDelta}
    {fineNormalizationExponent outerLogExponent
      coarseNormalizationExponent : ℕ}
    {fineNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := fineNormalizationLoss) fineSource
      fineNormalizationExponent}
    {fineCurrent : WZ1PaperTubeShading fineNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) fineNormalized fineCurrent)
    {rho : WZ2PaperRequestedScale fineDelta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      coarseNormalizationExponent)
    (planeMap : Point3 → Point3) (tauConstant sqrtConstant : ENNReal)
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := rho.1)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      coarseNormalized planeMap tauConstant sqrtConstant)
    (pullback : Proposition63FourCallPullbackData data.current
      outer.croppedCoarseShading)
    (critical : PureWZ2CroppedCriticalFloorSelectionData
      sigma floorLoss structuralBudget)
    (hcoarseCritical : rho.1 ≤ critical.delta₀)
    (hfinalStructural : finalLoss = critical.structuralLoss)
    (hcellVolumeFloor : 0 < cellVolumeFloor)
    (hcellBudget : ENNReal.ofReal cellVolumeFloor *
        Kakeya.realRpowENN sqrtScale (sigma - sqrtStickyLoss) ≤
      Kakeya.realRpowENN rho.1 (sigma + floorLoss) *
        Kakeya.realRpowENN sqrtScale 3)
    (hquery : 0 < rho.1) (hqueryOne : rho.1 ≤ 1)
    (htau : 0 < tauScale) (hqueryTau : rho.1 ≤ tauScale)
    (htauSqrt : tauScale ≤ Real.sqrt rho.1)
    (hsqrtScale : sqrtScale = Real.sqrt rho.1)
    (hplaneUnit : ∀ point ∈ data.prepared.refined.shading.union,
      ‖planeMap point‖ = 1)
    (coefficient : NNReal) (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (hcoverBudget : (512 : ENNReal) *
        ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
          sqrtConstant) ≤ (coverBudget : ENNReal))
    (hsqrtConstantFinite : sqrtConstant ≠ ⊤)
    (hnormalErrorTau : 8 * (coefficient : ℝ) * rho.1 ≤ tauScale)
    (hhullTau : rho.1 * Real.sqrt 3 ≤ tauScale)
    (scaleFactor : ℕ) (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * fineDelta)
    (fineCurrentLoss : ℝ)
    (hcurrentExtremal : WZ2PaperCroppedIsExtremal sigma fineCurrentLoss
      fineNormalized.croppedFamily fineCurrent)
    (hcurrentCWA : WZ2PaperConvexWolffBound fineNormalized.croppedFamily
      (Kakeya.realRpowENN fineDelta (-fineCurrentLoss)))
    (targetConstant targetLeft targetRight : ENNReal)
    (hconstant : Proposition63NestedPointCoverData.FullGrainCells.nestedCandidateIntervalBound
      rho.1 rho.1 (8 * (coefficient : ℝ) * rho.1) (coefficient : ℝ)
      (13 ^ 3) tauConstant ≤ targetConstant)
    (hleft : targetLeft ≤ proposition63DependentFinePullbackLeft fineReentry
      outer pullback.retentionFactor
      (ENNReal.ofReal ((cellVolumeFloor / 2) / (4 * (2 * sqrtScale) ^ 2)) *
        (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) *
        (data.secondRetainedFactor *
          ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
          data.firstRetainedFactor)))
    (hright : proposition63DependentFinePullbackRight fineReentry
      ((data.reentry.regularized.regularizationLoss *
          data.prepared.preparationLoss) *
        (2 * ENNReal.ofReal (4 * rho.1))) ≤ targetRight)
    (hleftPos : 0 < targetLeft) (hleftTop : targetLeft ≠ ⊤)
    (hrightTop : targetRight ≠ ⊤)
    (hcurrentOutput : fineCurrentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss targetLeft targetRight *
      Kakeya.realRpowENN fineDelta outputLoss ≤
        Kakeya.realRpowENN fineDelta fineCurrentLoss)
    (hvariation : (coefficient : ℝ) * spatialScale ≤ variationScale) :
    ∃ next : WZ1PaperTubeShading fineNormalized.croppedFamily,
      PaperIsSubshading next fineCurrent ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union, next.pointMultiplicity point =
        fineCurrent.pointMultiplicity point) ∧
      WZ2PaperCroppedIsExtremal sigma outputLoss
        fineNormalized.croppedFamily next ∧
      WZ2PaperConvexWolffBound fineNormalized.croppedFamily
        (Kakeya.realRpowENN fineDelta (-outputLoss)) ∧
      PureWZ2IntervalCoveringAt next planeMap rho.1
        (Real.toNNReal rho.1) (Real.toNNReal tauScale) targetConstant ∧
      targetLeft * fineCurrent.mass ≤ targetRight * next.mass ∧
      (∀ first ∈ next.union, ∀ second ∈ next.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) := by
  exact Proposition63NestedPointCoverData.finalCandidate_for_fine_interval_iteration_of_critical_floor
    (fineReentry := fineReentry) (outer := outer)
    (coarseNormalized := coarseNormalized) (planeMap := planeMap)
    (tauConstant := tauConstant) (sqrtConstant := sqrtConstant) (data := data)
    (ancestorEmbedding := pullback.embedding)
    (ancestor_tube_eq := pullback.tube_eq)
    (current_sub_outer := pullback.subshading)
    (ancestorRetentionFactor := pullback.retentionFactor)
    (current_retained_mass := pullback.retained_mass)
    (critical := critical) (hcoarseCritical := hcoarseCritical)
    (hfinalStructural := hfinalStructural)
    (hcellVolumeFloor := hcellVolumeFloor) (hcellBudget := hcellBudget)
    (hquery := hquery) (hqueryOne := hqueryOne) (htau := htau)
    (hqueryTau := hqueryTau) (htauSqrt := htauSqrt)
    (hsqrtScale := hsqrtScale) (hplaneUnit := hplaneUnit)
    (coefficient := coefficient) (hcoefficientOne := hcoefficientOne)
    (hplaneLipschitz := hplaneLipschitz) (coverBudget := coverBudget)
    (hcoverBudgetPos := hcoverBudgetPos) (hcoverBudget := hcoverBudget)
    (hsqrtConstantFinite := hsqrtConstantFinite)
    (hnormalErrorTau := hnormalErrorTau) (hhullTau := hhullTau)
    (scaleFactor := scaleFactor) (hscaleFactor := hscaleFactor)
    (hrhoAligned := hrhoAligned) (fineCurrentLoss := fineCurrentLoss)
    (hcurrentExtremal := hcurrentExtremal) (hcurrentCWA := hcurrentCWA)
    (targetConstant := targetConstant) (targetLeft := targetLeft)
    (targetRight := targetRight) (hconstant := hconstant)
    (hleft := hleft) (hright := hright)
    (hleftPos := hleftPos) (hleftTop := hleftTop)
    (hrightTop := hrightTop) (hcurrentOutput := hcurrentOutput)
    (houtputLoss := houtputLoss) (hrestore := hrestore)
    (hvariation := hvariation)

/-- Pure-critical/local-trace variant of the final ancestry tail. -/
theorem Proposition63FourCallPullbackData.finalCandidate_of_pure_critical_trace
    {fineDelta sigma fineInputLoss fineNormalizationLoss fineReentryLoss
      outerLoss coarseInputLoss coarseNormalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss tauScale sqrtScale outputLoss
      spatialScale variationScale floorLoss structuralBudget cellVolumeFloor : ℝ}
    {fineSource : PureWZ2ExtremalConfiguration sigma fineInputLoss fineDelta}
    {fineNormalizationExponent outerLogExponent
      coarseNormalizationExponent : ℕ}
    {fineNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := fineNormalizationLoss) fineSource
      fineNormalizationExponent}
    {fineCurrent : WZ1PaperTubeShading fineNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) fineNormalized fineCurrent)
    {rho : WZ2PaperRequestedScale fineDelta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      coarseNormalizationExponent)
    (planeMap : Point3 → Point3) (tauConstant sqrtConstant : ENNReal)
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := rho.1)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      coarseNormalized planeMap tauConstant sqrtConstant)
    (pullback : Proposition63FourCallPullbackData data.current
      outer.croppedCoarseShading)
    (critical : PureWZ2CriticalFloorSelectionData
      sigma floorLoss structuralBudget)
    (hcoarseCritical : rho.1 ≤ critical.delta₀)
    (hfinalStructural : finalLoss ≤ critical.structuralLoss)
    (traceAbsorption : Proposition63PureCriticalTailTraceAbsorption rho.1
      critical.structuralLoss reentryLoss finalLoss)
    (hcellVolumeFloor : 0 < cellVolumeFloor)
    (hcellBudget : ENNReal.ofReal cellVolumeFloor *
        Kakeya.realRpowENN sqrtScale (sigma - sqrtStickyLoss) ≤
      Kakeya.realRpowENN rho.1 (sigma + floorLoss) *
        Kakeya.realRpowENN sqrtScale 3)
    (hquery : 0 < rho.1) (hqueryOne : rho.1 ≤ 1)
    (htau : 0 < tauScale) (hqueryTau : rho.1 ≤ tauScale)
    (htauSqrt : tauScale ≤ Real.sqrt rho.1)
    (hsqrtScale : sqrtScale = Real.sqrt rho.1)
    (hplaneUnit : ∀ point ∈ data.prepared.refined.shading.union,
      ‖planeMap point‖ = 1)
    (coefficient : NNReal) (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (hcoverBudget : (512 : ENNReal) *
        ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
          sqrtConstant) ≤ (coverBudget : ENNReal))
    (hsqrtConstantFinite : sqrtConstant ≠ ⊤)
    (hnormalErrorTau : 8 * (coefficient : ℝ) * rho.1 ≤ tauScale)
    (hhullTau : rho.1 * Real.sqrt 3 ≤ tauScale)
    (scaleFactor : ℕ) (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * fineDelta)
    (fineCurrentLoss : ℝ)
    (hcurrentExtremal : WZ2PaperCroppedIsExtremal sigma fineCurrentLoss
      fineNormalized.croppedFamily fineCurrent)
    (hcurrentCWA : WZ2PaperConvexWolffBound fineNormalized.croppedFamily
      (Kakeya.realRpowENN fineDelta (-fineCurrentLoss)))
    (targetConstant targetLeft targetRight : ENNReal)
    (hconstant : Proposition63NestedPointCoverData.FullGrainCells.nestedCandidateIntervalBound
      rho.1 rho.1 (8 * (coefficient : ℝ) * rho.1) (coefficient : ℝ)
      (13 ^ 3) tauConstant ≤ targetConstant)
    (hleft : targetLeft ≤ proposition63DependentFinePullbackLeft fineReentry
      outer pullback.retentionFactor
      (ENNReal.ofReal ((cellVolumeFloor / 2) / (4 * (2 * sqrtScale) ^ 2)) *
        (((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))) *
        (data.secondRetainedFactor *
          ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
          data.firstRetainedFactor)))
    (hright : proposition63DependentFinePullbackRight fineReentry
      ((data.reentry.regularized.regularizationLoss *
          data.prepared.preparationLoss) *
        (2 * ENNReal.ofReal (4 * rho.1))) ≤ targetRight)
    (hleftPos : 0 < targetLeft) (hleftTop : targetLeft ≠ ⊤)
    (hrightTop : targetRight ≠ ⊤)
    (hcurrentOutput : fineCurrentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss targetLeft targetRight *
      Kakeya.realRpowENN fineDelta outputLoss ≤
        Kakeya.realRpowENN fineDelta fineCurrentLoss)
    (hvariation : (coefficient : ℝ) * spatialScale ≤ variationScale) :
    ∃ next : WZ1PaperTubeShading fineNormalized.croppedFamily,
      PaperIsSubshading next fineCurrent ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union, next.pointMultiplicity point =
        fineCurrent.pointMultiplicity point) ∧
      WZ2PaperCroppedIsExtremal sigma outputLoss
        fineNormalized.croppedFamily next ∧
      WZ2PaperConvexWolffBound fineNormalized.croppedFamily
        (Kakeya.realRpowENN fineDelta (-outputLoss)) ∧
      PureWZ2IntervalCoveringAt next planeMap rho.1
        (Real.toNNReal rho.1) (Real.toNNReal tauScale) targetConstant ∧
      targetLeft * fineCurrent.mass ≤ targetRight * next.mass ∧
      (∀ first ∈ next.union, ∀ second ∈ next.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) := by
  exact Proposition63NestedPointCoverData.finalCandidate_for_fine_interval_iteration_of_pure_critical_trace
    (fineReentry := fineReentry) (outer := outer)
    (coarseNormalized := coarseNormalized) (planeMap := planeMap)
    (tauConstant := tauConstant) (sqrtConstant := sqrtConstant) (data := data)
    (ancestorEmbedding := pullback.embedding)
    (ancestor_tube_eq := pullback.tube_eq)
    (current_sub_outer := pullback.subshading)
    (ancestorRetentionFactor := pullback.retentionFactor)
    (current_retained_mass := pullback.retained_mass)
    (critical := critical) (hcoarseCritical := hcoarseCritical)
    (hfinalStructural := hfinalStructural)
    (traceAbsorption := traceAbsorption)
    (hcellVolumeFloor := hcellVolumeFloor) (hcellBudget := hcellBudget)
    (hquery := hquery) (hqueryOne := hqueryOne) (htau := htau)
    (hqueryTau := hqueryTau) (htauSqrt := htauSqrt)
    (hsqrtScale := hsqrtScale) (hplaneUnit := hplaneUnit)
    (coefficient := coefficient) (hcoefficientOne := hcoefficientOne)
    (hplaneLipschitz := hplaneLipschitz) (coverBudget := coverBudget)
    (hcoverBudgetPos := hcoverBudgetPos) (hcoverBudget := hcoverBudget)
    (hsqrtConstantFinite := hsqrtConstantFinite)
    (hnormalErrorTau := hnormalErrorTau) (hhullTau := hhullTau)
    (scaleFactor := scaleFactor) (hscaleFactor := hscaleFactor)
    (hrhoAligned := hrhoAligned) (fineCurrentLoss := fineCurrentLoss)
    (hcurrentExtremal := hcurrentExtremal) (hcurrentCWA := hcurrentCWA)
    (targetConstant := targetConstant) (targetLeft := targetLeft)
    (targetRight := targetRight) (hconstant := hconstant)
    (hleft := hleft) (hright := hright)
    (hleftPos := hleftPos) (hleftTop := hleftTop)
    (hrightTop := hrightTop) (hcurrentOutput := hcurrentOutput)
    (houtputLoss := houtputLoss) (hrestore := hrestore)
    (hvariation := hvariation)

/-- Extend a ready first pullback through the remaining concrete M3 witnesses. -/
theorem proposition63_four_call_pullback_of_runtime_witnesses
    {delta sigma outerLoss secondNormalizationLoss targetSourceLoss
      targetLoss thirdTargetLoss firstLoss fourthSourceLoss sqrtStickyLoss secondLoss
      finalLoss tauScale sqrtScale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rho : WZ2PaperRequestedScale delta}
    {outerLogExponent : ℕ}
    (rich1 : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss) sourceShading rho
      outerLogExponent)
    (p1 : Proposition63DependentCoarseReentryData
      (reentryLoss := secondNormalizationLoss) rich1 0)
    (hP1Source : 0 < p1.sourceLoss)
    (hSecondNorm : 0 < secondNormalizationLoss)
    {robustScale : WZ2PaperRequestedScale rho.1}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) p1.normalization.croppedRefined
      (p1.normalization.toPropStickyReentryData hP1Source hSecondNorm)
      robustScale)
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetSourceLoss) p1.normalization
      (extendShading outer.data.selected outer.data.refined))
    (hTargetSource : 0 < targetSourceLoss)
    {targetScale : WZ2PaperRequestedScale rho.1}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := thirdTargetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        hTargetSource targetReentry.reentry_normalization_loss_pos) targetScale)
    (planeMap : Point3 → Point3) (tauConstant sqrtConstant : ENNReal)
    (nested : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := fourthSourceLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := rho.1)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      targetReentry.normalization planeMap tauConstant sqrtConstant)
    (hnested : nested.current =
      extendShading target.data.selected target.data.refined)
    (hrho_lt_one : rho.1 < 1) :
    ∃ pullback : Proposition63FourCallPullbackData nested.current
        rich1.croppedCoarseShading,
      pullback.retentionFactor = proposition63FourCallPullbackRetentionFormula
        (wz2PaperPureRefinementFraction rho.1 61)
        targetReentry.regularized.regularizationLoss
        targetReentry.normalizationWeight p1.retentionFactor := by
  let fraction : ENNReal := wz2PaperPureRefinementFraction rho.1 61
  have hlogPos : 0 < Real.log (1 / rho.1) := by
    apply Real.log_pos
    exact one_lt_one_div rich1.coarse_extremal.delta_pos hrho_lt_one
  have hfractionPos : 0 < fraction := by
    dsimp only [fraction, wz2PaperPureRefinementFraction]
    exact (pow_ne_zero 61 (ENNReal.inv_ne_zero.mpr (by simp))).bot_lt
  have hfractionTop : fraction ≠ ⊤ := by
    dsimp only [fraction, wz2PaperPureRefinementFraction]
    exact ENNReal.pow_ne_top <| ENNReal.inv_ne_top.mpr
      (ENNReal.ofReal_pos.mpr hlogPos).ne'
  let call2Factor : ENNReal := (fraction * p1.retentionFactor⁻¹)⁻¹
  have hcall2Pos : 0 < call2Factor := by
    apply ENNReal.inv_pos.mpr
    exact ENNReal.mul_ne_top hfractionTop
      (ENNReal.inv_ne_top.mpr p1.retentionFactor_pos.ne')
  have hcall2Top : call2Factor ≠ ⊤ := by
    apply ENNReal.inv_ne_top.mpr
    exact (ENNReal.mul_pos
      hfractionPos.ne'
      (ENNReal.inv_ne_zero.mpr p1.retentionFactor_ne_top)).ne'
  have hcall2Mass : call2Factor⁻¹ * rich1.croppedCoarseShading.mass ≤
      (extendShading outer.data.selected outer.data.refined).mass := by
    rw [show call2Factor⁻¹ = fraction * p1.retentionFactor⁻¹ by
      simp only [call2Factor, inv_inv]]
    calc
      (fraction * p1.retentionFactor⁻¹) *
          rich1.croppedCoarseShading.mass =
        fraction * (p1.retentionFactor⁻¹ *
          rich1.croppedCoarseShading.mass) := by ring
      _ ≤ fraction * p1.normalization.croppedRefined.mass := by
        gcongr
        exact p1.retained_mass
      _ ≤ (extendShading outer.data.selected outer.data.refined).mass := by
        simpa only [extendShading_mass] using outer.total_mass_retention
  have hcall2Sub : ∀ index,
      (extendShading outer.data.selected outer.data.refined).carrier index ⊆
        rich1.croppedCoarseShading.carrier
          (p1.coarseEmbedding index) := by
    intro index point hpoint
    exact p1.normalized_subshading index
      (extendShading_subshading outer.data.selected outer.data.subshading
        index hpoint)
  let p2 := proposition63DependentCoarseReentryOfCurrent rich1
    p1.normalization
    (extendShading outer.data.selected outer.data.refined) targetReentry
    p1.coarseEmbedding p1.coarse_tube_eq
    hcall2Sub call2Factor hcall2Pos hcall2Top hcall2Mass
  let finalFactor : ENNReal := (fraction * p2.retentionFactor⁻¹)⁻¹
  have hfinalMass : finalFactor⁻¹ *
      rich1.croppedCoarseShading.mass ≤ nested.current.mass := by
    dsimp only [finalFactor]
    rw [inv_inv]
    calc
      (fraction * p2.retentionFactor⁻¹) * rich1.croppedCoarseShading.mass =
          fraction * (p2.retentionFactor⁻¹ *
            rich1.croppedCoarseShading.mass) := by ring
      _ ≤ fraction * targetReentry.normalization.croppedRefined.mass := by
        gcongr
        exact p2.retained_mass
      _ ≤ nested.current.mass := by
        rw [hnested, extendShading_mass]
        exact target.total_mass_retention
  have hfinalSub : ∀ index, nested.current.carrier index ⊆
      rich1.croppedCoarseShading.carrier
        (p2.coarseEmbedding index) := by
    intro index point hpoint
    apply p2.normalized_subshading index
    rw [hnested] at hpoint
    exact extendShading_subshading target.data.selected
      target.data.subshading index hpoint
  let pullback : Proposition63FourCallPullbackData nested.current
      rich1.croppedCoarseShading :=
    { embedding := p2.coarseEmbedding
      tube_eq := p2.coarse_tube_eq
      subshading := hfinalSub
      retentionFactor := finalFactor
      retained_mass := hfinalMass }
  refine ⟨pullback, ?_⟩
  apply proposition63_four_call_pullback_retention_formula_of_reentry_factor
      (p2Factor := p2.retentionFactor)
  · rw [proposition63_dependent_coarse_reentry_retentionFactor_eq
      rich1 p1.normalization
      (extendShading outer.data.selected outer.data.refined) targetReentry
      p1.coarseEmbedding p1.coarse_tube_eq hcall2Sub call2Factor hcall2Pos
      hcall2Top hcall2Mass]
    simp only [call2Factor, inv_inv]
    rfl
  · rfl

end Kakeya.Assouad.PureWZ2
