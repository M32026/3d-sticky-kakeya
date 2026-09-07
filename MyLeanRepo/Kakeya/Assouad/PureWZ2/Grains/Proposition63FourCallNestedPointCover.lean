import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RobustPointCoverAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SourceWitnessCoarseMass

/-!
# Four-call producer for the nested point cover

This module is the rho-level M3 runtime producer. Starting from the re-entry
created by the first scheduled call, it consumes calls two through four via
the overlapping three-call views of one preselected four-call schedule.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- Construction-time scalar provenance for the nested cover in the four-call
route.  This deliberately lives outside the generic nested-cover structure. -/
structure Proposition63FourCallNestedMassReceipt
    (delta : ℝ)
    (firstRetainedFactor normalizationWeight : ENNReal)
    (levelCount : ℕ) (secondRetainedFactor preparationLoss : ENNReal)
    (firstTargetCard secondTargetCard : ℕ)
    (canonicalWeight : ENNReal) (canonicalLevel : ℕ)
    (preparationUpper : ENNReal) where
  firstRetainedFactor_eq : firstRetainedFactor =
    (81 / 400 : ENNReal) *
      (((Nat.log 2 firstTargetCard + 1 : ℕ) : ENNReal))⁻¹
  reentryWeight_eq : normalizationWeight = canonicalWeight
  reentryLevel_eq : levelCount = canonicalLevel
  secondRetainedFactor_eq : secondRetainedFactor =
    (81 / 400 : ENNReal) *
      (((Nat.log 2 secondTargetCard + 1 : ℕ) :
        ENNReal))⁻¹ * wz2PaperPureRefinementFraction delta 61
  preparationLoss_le : preparationLoss ≤ preparationUpper

/-- The scalar equalities produced before the final whole-cell preparation. -/
structure Proposition63FourCallAnalyticMassReceipt
    (delta : ℝ)
    (firstRetainedFactor normalizationWeight : ENNReal)
    (levelCount : ℕ) (secondRetainedFactor : ENNReal)
    (firstTargetCard secondTargetCard : ℕ)
    (canonicalWeight : ENNReal) (canonicalLevel : ℕ) where
  firstRetainedFactor_eq : firstRetainedFactor =
    (81 / 400 : ENNReal) *
      (((Nat.log 2 firstTargetCard + 1 : ℕ) : ENNReal))⁻¹
  reentryWeight_eq : normalizationWeight = canonicalWeight
  reentryLevel_eq : levelCount = canonicalLevel
  secondRetainedFactor_eq : secondRetainedFactor =
    (81 / 400 : ENNReal) *
      (((Nat.log 2 secondTargetCard + 1 : ℕ) :
        ENNReal))⁻¹ * wz2PaperPureRefinementFraction delta 61

/-- The rho-level last-three-call runtime, packaged to avoid repeatedly
normalizing a deep dependent existential in downstream assembly. -/
structure Proposition63RhoLevelFourCallData
    {delta sigma initialInputLoss normalizationLoss firstReentryLoss
      outputLoss tau firstLoss weightLoss nextWeightLoss secondLoss finalLoss
      incidenceBound : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource 0}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (firstReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := firstReentryLoss) initialNormalized current)
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss)
    (hfirstReentryLoss : firstReentryLoss = schedule.second.sourceLoss)
    (robustScale targetScale sqrtRequested : WZ2PaperRequestedScale delta)
    (currentMap : PaperWZ1WeakPlaneMapData current incidenceBound)
    (firstConstant finalConstant : ENNReal) where
  outer : Proposition63RichTerminalStickyData
    (outputLoss := schedule.secondOutputLoss)
    firstReentry.normalization.croppedRefined
    (firstReentry.normalization.toPropStickyReentryData
      (by rw [hfirstReentryLoss]; exact schedule.second.sourceLoss_pos)
      firstReentry.reentry_normalization_loss_pos) robustScale
  targetReentry : Proposition63CurrentShadingReentryData
    (reentryLoss := schedule.third.sourceLoss) firstReentry.normalization
    (extendShading outer.data.selected outer.data.refined)
  target : Proposition63RichTerminalStickyData
    (outputLoss := schedule.thirdOutputLoss)
    targetReentry.normalization.croppedRefined
    (targetReentry.normalization.toPropStickyReentryData
      schedule.third.sourceLoss_pos
      targetReentry.reentry_normalization_loss_pos) targetScale
  targetNormalization : targetReentry.reentryNormalizationLoss =
    schedule.third.normalizationLoss
  targetCanonicalWeight : targetReentry.normalizationWeight =
    proposition63CanonicalReentryWeight delta weightLoss
  targetCanonicalLevel : targetReentry.levelCount =
    proposition63CanonicalNearbyLevelCount
      firstReentry.reentryNormalizationLoss
  nested : Proposition63NestedPointCoverData
    (firstLoss := firstLoss) (reentryLoss := schedule.fourth.sourceLoss)
    (sqrtStickyLoss := outputLoss) (secondLoss := secondLoss)
    (finalLoss := finalLoss) (queryScale := delta) (tauScale := tau)
    (sqrtScale := sqrtRequested.1) targetReentry.normalization
    currentMap.planeMap
    (firstConstant * Kakeya.realRpowENN (tau / delta) (1 - sigma))
    (finalConstant * Kakeya.realRpowENN
      (sqrtRequested.1 / delta) (1 - sigma))
  nested_eq : nested.current =
    extendShading target.data.selected target.data.refined
  secondTargetCard : ℕ
  secondTargetCard_le : secondTargetCard ≤
    targetReentry.normalization.croppedFamily.card
  nestedMass : Proposition63FourCallNestedMassReceipt
    delta nested.firstRetainedFactor
    nested.reentry.normalizationWeight nested.reentry.levelCount
    nested.secondRetainedFactor nested.prepared.preparationLoss
    target.data.selected.family.card secondTargetCard
    (proposition63CanonicalReentryWeight delta nextWeightLoss)
    (proposition63CanonicalNearbyLevelCount
      targetReentry.reentryNormalizationLoss)
    (proposition63UniformPreparationLoss
      (targetReentry.normalization.toPropStickyReentryData
        schedule.third.sourceLoss_pos
        targetReentry.reentry_normalization_loss_pos).toNormalizationData.croppedFamily)

private theorem gridSide_half_le_self {scale : ℝ} (hscale : 0 ≤ scale) :
    gridSide (scale / 2) ≤ scale := by
  have hsqrtThree : 1 ≤ Real.sqrt 3 := Real.one_le_sqrt.mpr (by norm_num)
  unfold gridSide
  rw [show 2 * (scale / 2) / Real.sqrt 3 = scale / Real.sqrt 3 by ring]
  exact div_le_self hscale hsqrtThree

theorem Proposition63RichFourCallScheduleData.callOneCoarseSource_le_rhoRoot
    {delta sigma inputLoss normalizationLoss outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {fineShading : WZ1PaperTubeShading family}
    {fineReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) fineShading normalizationExponent
      inputLoss normalizationLoss}
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss)
    {rho : WZ2PaperRequestedScale delta}
    (rich1 : Proposition63RichTerminalStickyData
      (outputLoss := schedule.firstOutputLoss) fineShading fineReentry rho) :
    rich1.coarseSourceLoss ≤ schedule.second.sourceLoss / 16 := by
  calc
    rich1.coarseSourceLoss ≤ schedule.firstOutputLoss / 3 := by
      linarith [rich1.coarseSourceLoss_budget]
    _ = schedule.second.sourceLoss / 48 := by
      rw [schedule.firstOutputLoss_eq]
      ring
    _ ≤ schedule.second.sourceLoss / 16 := by
      linarith [schedule.second.sourceLoss_pos]

theorem
    Proposition63RichFourCallScheduleData.callOneCoarseNormalization_le_rhoRoot
    {delta sigma inputLoss normalizationLoss outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {fineShading : WZ1PaperTubeShading family}
    {fineReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) fineShading normalizationExponent
      inputLoss normalizationLoss}
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss)
    {rho : WZ2PaperRequestedScale delta}
    (rich1 : Proposition63RichTerminalStickyData
      (outputLoss := schedule.firstOutputLoss) fineShading fineReentry rho) :
    rich1.coarseNormalizationLoss ≤ schedule.second.sourceLoss / 4 := by
  rw [rich1.coarseNormalizationLoss_eq]
  have hsource := schedule.callOneCoarseSource_le_rhoRoot rich1
  linarith [schedule.second.sourceLoss_pos]

theorem Proposition63RichFourCallScheduleData.rhoRootSource_pos
    {sigma outputLoss : ℝ}
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss) :
    0 < schedule.second.sourceLoss / 16 := by
  exact div_pos schedule.second.sourceLoss_pos (by norm_num)

theorem Proposition63RichFourCallScheduleData.rhoRootNormalization_pos
    {sigma outputLoss : ℝ}
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss) :
    0 < schedule.second.sourceLoss / 4 := by
  exact div_pos schedule.second.sourceLoss_pos (by norm_num)

theorem Proposition63RichFourCallScheduleData.rhoRootSource_le_half
    {sigma outputLoss : ℝ}
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss) :
    schedule.second.sourceLoss / 16 ≤
      (schedule.second.sourceLoss / 4) / 2 := by
  linarith [schedule.second.sourceLoss_pos]

/-- The canonical call-one coarse re-entry used by the remaining three calls. -/
noncomputable def Proposition63RichFourCallScheduleData.callOneRhoRootReentry
    {delta sigma inputLoss normalizationLoss outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {fineShading : WZ1PaperTubeShading family}
    {fineReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) fineShading normalizationExponent
      inputLoss normalizationLoss}
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss)
    {rho : WZ2PaperRequestedScale delta}
    (rich1 : Proposition63RichTerminalStickyData
      (outputLoss := schedule.firstOutputLoss) fineShading fineReentry rho)
    (rootAxialWindow : ∀ index point,
      point ∈ fineReentry.geometry.frame ''
          fineReentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8) :
    PureWZ2PropStickyReentryData
      (sigma := sigma) rich1.data.croppedCoarseShading 0
      (schedule.second.sourceLoss / 16)
      (schedule.second.sourceLoss / 4) :=
  (rich1.coarseReentry rootAxialWindow).mono_losses
    (schedule.callOneCoarseSource_le_rhoRoot rich1)
    (schedule.callOneCoarseNormalization_le_rhoRoot rich1)
    schedule.rhoRootSource_pos schedule.rhoRootNormalization_pos
    schedule.rhoRootSource_le_half

/-- The exact rho-level normalization obtained from the first rich terminal. -/
noncomputable def Proposition63RichFourCallScheduleData.callOneRhoRootNormalization
    {delta sigma inputLoss normalizationLoss outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {fineShading : WZ1PaperTubeShading family}
    {fineReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) fineShading normalizationExponent
      inputLoss normalizationLoss}
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss)
    {rho : WZ2PaperRequestedScale delta}
    (rich1 : Proposition63RichTerminalStickyData
      (outputLoss := schedule.firstOutputLoss) fineShading fineReentry rho)
    (rootAxialWindow : ∀ index point,
      point ∈ fineReentry.geometry.frame ''
          fineReentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8) :
    PureWZ2CroppedCriticalNormalizationData
      (outputLoss := schedule.second.sourceLoss / 4)
      (schedule.callOneRhoRootReentry rich1 rootAxialWindow).ordinarySource 0 :=
  (schedule.callOneRhoRootReentry rich1 rootAxialWindow).toNormalizationData

/-- All four rich calls and their nested mass provenance, with the call-one
witnesses packaged ahead of the rho-level runtime. -/
structure Proposition63FourCallNestedRuntimeData
    {delta sigma inputLoss normalizationLoss outputLoss tau firstLoss
      rhoWeightLoss firstStageWeightLoss nextWeightLoss secondLoss finalLoss
      incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {fineShading : WZ1PaperTubeShading family}
    (fineReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) fineShading normalizationExponent inputLoss
      normalizationLoss)
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss)
    (rho : WZ2PaperRequestedScale delta)
    (rootAxialWindow : ∀ index point,
      point ∈ fineReentry.geometry.frame ''
          fineReentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (sourceCoefficient : NNReal)
    (robustScale targetScale sqrtRequested : WZ2PaperRequestedScale rho.1)
    (firstConstant finalConstant : ENNReal)
    (ambientPlaneMap : Point3 → Point3) where
  rich1 : Proposition63RichTerminalStickyData
    (outputLoss := schedule.firstOutputLoss) fineShading fineReentry rho
  currentMap : PaperWZ1WeakPlaneMapData rich1.terminal.sourceWitness.shading
    (proposition63DependentCoarseIncidence rho.1 incidence
      (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)))
  currentReentry : Proposition63CurrentShadingReentryData
    (reentryLoss := schedule.second.sourceLoss)
    (schedule.callOneRhoRootNormalization rich1 rootAxialWindow)
    rich1.terminal.sourceWitness.shading
  currentNormalization : currentReentry.reentryNormalizationLoss =
    schedule.second.normalizationLoss
  currentCanonicalWeight : currentReentry.normalizationWeight =
    proposition63CanonicalReentryWeight rho.1 rhoWeightLoss
  currentCanonicalLevel : currentReentry.levelCount =
    proposition63CanonicalNearbyLevelCount (schedule.second.sourceLoss / 4)
  currentMap_eq : currentMap.planeMap = ambientPlaneMap
  rhoData : Proposition63RhoLevelFourCallData
    (tau := tau) (firstLoss := firstLoss)
    (weightLoss := firstStageWeightLoss) (nextWeightLoss := nextWeightLoss)
    (secondLoss := secondLoss)
    (finalLoss := finalLoss)
    (incidenceBound := proposition63DependentCoarseIncidence rho.1 incidence
      (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)))
    currentReentry schedule rfl robustScale targetScale sqrtRequested
    currentMap firstConstant finalConstant

/-- Execute call one and construct the exact rho-level source-witness re-entry
used by calls two through four.  The family-dependent nearby schedule is
constructed internally from the pre-runtime absorption record. -/
theorem proposition63_four_call_source_witness_prefix_of_absorption
    {delta sigma inputLoss normalizationLoss rhoDensityLoss outputLoss
      rhoWeightLoss incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {fineShading : WZ1PaperTubeShading family}
    (fineReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) fineShading normalizationExponent
      inputLoss normalizationLoss)
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss)
    (hinput : inputLoss = schedule.first.sourceLoss)
    (hnormalization : normalizationLoss = schedule.first.normalizationLoss)
    (hdeltaFirst : delta ≤ schedule.first.delta₀)
    (rho : WZ2PaperRequestedScale delta)
    (hrhoLower : Real.rpow delta (1 - schedule.firstOutputLoss) ≤ rho.1)
    (hrhoUpper : rho.1 ≤ Real.rpow delta schedule.firstOutputLoss)
    (rootAxialWindow : ∀ index point,
      point ∈ fineReentry.geometry.frame ''
          fineReentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8)
    {sourceMap : PaperWZ1WeakPlaneMapData fineShading incidence}
    {sourceCoefficient : NNReal}
    (extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient)
    (hcellError :
      ((lipschitzExtensionConstant Point3 * sourceCoefficient : NNReal) : ℝ) *
        (rho.1 * Real.sqrt 3) ≤ 1 / 2)
    (rhoAbsorption : Proposition63CurrentReentryAbsorptionData
      (schedule.second.sourceLoss / 16)
      (schedule.second.sourceLoss / 4) rhoDensityLoss
      schedule.firstOutputLoss rhoWeightLoss schedule.second.sourceLoss
      (proposition63CanonicalNearbyLevelCount
        (schedule.second.sourceLoss / 4)))
    (hrhoAbsorption : rho.1 ≤ rhoAbsorption.delta₀)
    (hrhoSmall : rho.1 ≤ 1 / 24) :
    ∃ rich1 : Proposition63RichTerminalStickyData
        (outputLoss := schedule.firstOutputLoss) fineShading fineReentry rho,
      let coarseReentry := schedule.callOneRhoRootReentry rich1 rootAxialWindow
      let coarseNormalized := schedule.callOneRhoRootNormalization rich1
        rootAxialWindow
      let current := rich1.terminal.sourceWitness.shading
      Nonempty (Proposition63SourceWitnessCurrentReentryResult
        (nextSourceLoss := schedule.firstThree.second.sourceLoss)
        (nextNormalizationLoss :=
          schedule.firstThree.second.normalizationLoss)
        (incidence := incidence) (weightLoss := rhoWeightLoss) coarseNormalized
        current sourceCoefficient extension.ambient.planeMap) := by
  have run := schedule.first.runTerminal delta
    fineReentry.toNormalizationData.final_extremal.delta_pos hdeltaFirst
  rw [← hinput, ← hnormalization] at run
  rcases run family fineShading fineReentry rho hrhoLower hrhoUpper with ⟨rich1⟩
  have hfineAmbient' : rich1.data.refined.union ⊆ fineShading.union :=
    refined_union_subset_shading rich1.data
  have hfineIncidence : ∀ index point,
      point ∈ rich1.data.refined.carrier index →
        |@Inner.inner ℝ Point3 _
          (rich1.data.selected.family.tube index).direction
          (extension.ambient.planeMap point)| ≤ incidence := by
    intro index point hpoint
    rw [extension.agrees ⟨point,
      ⟨rich1.data.selected.embedding index,
        rich1.data.subshading index hpoint⟩⟩]
    rw [rich1.data.selected.tube_eq]
    exact sourceMap.incidence (rich1.data.selected.embedding index) point
      (rich1.data.subshading index hpoint)
  let coarseReentry := schedule.callOneRhoRootReentry rich1 rootAxialWindow
  let root : Proposition63RootNormalizationData
      (outputLoss := schedule.second.sourceLoss / 4)
      coarseReentry.ordinarySource 0 rhoDensityLoss :=
    Proposition63RootNormalizationData.ofPropStickyReentry coarseReentry
      (rhoAbsorption.density_absorb rich1.data.coarse_extremal.delta_pos
        hrhoAbsorption)
  have ambientTwo := rhoAbsorption.ambient_two
    rich1.data.coarse_extremal.delta_pos hrhoAbsorption
  have htwo : 2 * (schedule.second.sourceLoss / 4) ≤
      schedule.second.sourceLoss := by
    linarith [schedule.second.sourceLoss_pos]
  rcases root.finiteNearbySchedule
      (by linarith [schedule.second.sourceLoss_pos]) ambientTwo htwo with
    ⟨nearbySchedule⟩
  have regularizationAbsorb := rhoAbsorption.regularization_absorb
    root.normalization rfl nearbySchedule rfl rfl
    rich1.data.coarse_extremal.delta_pos hrhoAbsorption
  rcases rich1.currentReentry_on_sourceWitness rootAxialWindow extension
      hfineAmbient' hfineIncidence hcellError rich1.terminalLoss_le_output
      le_rfl (schedule.callOneCoarseSource_le_rhoRoot rich1)
      (schedule.callOneCoarseNormalization_le_rhoRoot rich1)
      (by linarith [schedule.second.sourceLoss_pos])
      (by linarith [schedule.second.sourceLoss_pos])
      (by linarith [schedule.second.sourceLoss_pos])
      (rhoAbsorption.density_absorb rich1.data.coarse_extremal.delta_pos
        hrhoAbsorption) nearbySchedule ambientTwo
      (by
        exact schedule.firstOutputLoss_lt_secondSource.le)
      schedule.firstThree.second.sourceLoss_pos
      schedule.firstThree.second.normalizationLoss_pos
      schedule.firstThree.second.sourceLoss_le_half
      (rhoAbsorption.canonical_weight_absorb
        rich1.data.coarse_extremal.delta_pos hrhoAbsorption)
      (rhoAbsorption.trace_fixed_absorb
        rich1.data.coarse_extremal.delta_pos hrhoAbsorption)
      (rhoAbsorption.paper_fixed_absorb
        rich1.data.coarse_extremal.delta_pos hrhoAbsorption)
      regularizationAbsorb hrhoSmall with ⟨currentResult⟩
  exact ⟨rich1, ⟨currentResult⟩⟩

private theorem proposition63_to_nested_analytic_with_current
    {delta sigma robustExponent outerLoss outerSourceLoss
      outerNormalizationLoss firstLoss tauScale secondReentryDensityLoss reentryLoss
      reentryNormalizationLoss weightLoss sqrtStickyLoss secondLoss epsilon₁
      epsilon₃ : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {incidenceBound : ℝ}
    (currentMap : PaperWZ1WeakPlaneMapData
      (extendShading outer.data.selected outer.data.refined) incidenceBound)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient currentMap.planeMap)
    (tauConstant : ENNReal)
    (first : Proposition63LiftedPointCoverData
      (outputLoss := firstLoss) (queryScale := delta)
      (spatialRadius := tauScale) outerReentry.toNormalizationData
      (extendShading outer.data.selected outer.data.refined)
      currentMap.planeMap tauConstant)
    (firstRetainedFactor_eq : first.retainedFactor =
      (81 / 400 : ENNReal) *
        (((Nat.log 2 outer.data.selected.family.card + 1 : ℕ) : ENNReal))⁻¹)
    (absorption : Proposition63CurrentReentryAbsorptionData
      outerSourceLoss outerNormalizationLoss secondReentryDensityLoss firstLoss weightLoss
      reentryLoss
      (proposition63CanonicalNearbyLevelCount outerNormalizationLoss))
    (hdeltaAbsorption : delta ≤ absorption.delta₀)
    (houterNormalizationLoss : 0 < outerNormalizationLoss)
    (htwoNormalization : 2 * outerNormalizationLoss ≤ reentryLoss)
    (hfirstReentry : firstLoss ≤ reentryLoss)
    (hfirstLoss : 0 < firstLoss)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2)
    (richSchedule : Proposition63RichThreeCallScheduleData
      sigma sqrtStickyLoss)
    (hreentryLoss : reentryLoss = richSchedule.third.sourceLoss)
    (hthirdNormalization :
      reentryNormalizationLoss = richSchedule.third.normalizationLoss)
    (hdeltaThird : delta ≤ richSchedule.third.delta₀)
    (sqrtRequested : WZ2PaperRequestedScale delta)
    (hsqrtLower : Real.rpow delta (1 - sqrtStickyLoss) ≤ sqrtRequested.1)
    (hsqrtUpper : sqrtRequested.1 ≤ Real.rpow delta sqrtStickyLoss)
    (hsqrtOne : sqrtRequested.1 ≤ 1)
    (boundaryAbsorption : Proposition63RobustBoundaryAbsorptionData
      sqrtStickyLoss reentryNormalizationLoss)
    (hdeltaBoundary : delta ≤ boundaryAbsorption.delta₀)
    (gridAbsorption : Proposition63RobustGridPruningAbsorptionData
      reentryNormalizationLoss epsilon₁)
    (hdeltaGridAbsorption : delta ≤ gridAbsorption.delta₀)
    (crossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        robustExponent outerLoss reentryNormalizationLoss weightLoss 4
        (proposition63CanonicalNearbyLevelCount outerNormalizationLoss))
    (hdeltaCrossAbsorption : delta ≤ crossAbsorption.delta₀)
    (hrobustScale : robustScale.1 = Real.rpow delta robustExponent)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
    (htargetSmall : sqrtRequested.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (hsqrtSq : sqrtRequested.1 ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              reentryNormalizationLoss sqrtStickyLoss
              sqrtRequested.1 sqrtRequested.1 /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                sqrtRequested.1 ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta sqrtRequested.1
              incidenceBound coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN
          (sqrtRequested.1 / delta) (1 - sigma))
    (hnormalizationSecond : reentryNormalizationLoss ≤ secondLoss)
    (hsecondLoss : 0 < secondLoss)
    (restoreAbsorption :
      Proposition63RobustPointCoverRestorationAbsorptionData
        reentryNormalizationLoss secondLoss 61)
    (hdeltaRestore : delta ≤ restoreAbsorption.delta₀) :
    ∃ analytic : Proposition63NestedPointCoverAnalyticData
        (firstLoss := firstLoss) (reentryLoss := reentryLoss)
        (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
        (queryScale := delta) (tauScale := tauScale)
        (sqrtScale := sqrtRequested.1) outerReentry.toNormalizationData
        currentMap.planeMap tauConstant
        (C * Kakeya.realRpowENN
          (sqrtRequested.1 / delta) (1 - sigma)),
      analytic.current = extendShading outer.data.selected outer.data.refined ∧
      Proposition63FourCallAnalyticMassReceipt
        delta analytic.firstRetainedFactor
        analytic.reentry.normalizationWeight analytic.reentry.levelCount
        analytic.secondRetainedFactor outer.data.selected.family.card
        analytic.sqrtSticky.selected.family.card
        (proposition63CanonicalReentryWeight delta weightLoss)
        (proposition63CanonicalNearbyLevelCount outerNormalizationLoss) := by
  have firstSubNormalized : PaperIsSubshading first.state.shading
      outerReentry.toNormalizationData.croppedRefined := by
    exact fun index point hpoint =>
      extendShading_subshading outer.data.selected outer.data.subshading index <|
        first.state.subshading index hpoint
  rcases first.nextReentryAndThirdRichOfAbsorption
      outerReentry.toNormalizationData firstSubNormalized absorption
      hdeltaAbsorption houterNormalizationLoss htwoNormalization
      hfirstReentry hfirstLoss hreentryNormalizationLoss hreentryHalf
      richSchedule hreentryLoss hthirdNormalization hdeltaThird sqrtRequested
      hsqrtLower hsqrtUpper with
    ⟨reentry, ⟨target⟩, hweight, hweightUpper, hlevel, hnormalization⟩
  let firstMap : PaperWZ1WeakPlaneMapData first.state.shading incidenceBound :=
    paperWeakPlaneMapRestrict currentMap first.state.subshading
  let normalizedMap : PaperWZ1WeakPlaneMapData
      reentry.normalization.croppedRefined incidenceBound :=
    reentry.normalizedPlaneMap firstMap
  let targetMap : PaperWZ1WeakPlaneMapData
      target.data.refined incidenceBound :=
    target.terminalPlaneMap normalizedMap
  have htargetReentryLoss : 0 < reentryLoss := by
    rw [hreentryLoss]
    exact richSchedule.third.sourceLoss_pos
  have receipts :=
    Proposition63RichTerminalStickyData.robustTauRuntimeReceipts_of_absorptions
      outer reentry htargetReentryLoss target hnormalization gridAbsorption
      crossAbsorption hdeltaGridAbsorption hdeltaCrossAbsorption hrobustScale
      hweight hweightUpper hlevel
      (reentry.reentry_extremal.delta_pos.trans_le
        sqrtRequested.2.1) hsqrtOne hrobustSmall
  rcases receipts with ⟨hgridError, hcrossCall⟩
  have htargetPos : 0 < sqrtRequested.1 :=
    reentry.reentry_extremal.delta_pos.trans_le sqrtRequested.2.1
  have hsqrtLowerThree : Real.rpow delta (1 - sqrtStickyLoss) ≤
      3 * sqrtRequested.1 :=
    hsqrtLower.trans <| by nlinarith [htargetPos]
  have hdeltaGrid := boundaryAbsorption.grid_le
    reentry.reentry_extremal.delta_pos hdeltaBoundary htargetPos
      hsqrtLowerThree
  have hperiodic := boundaryAbsorption.periodic
    reentry.reentry_extremal.delta_pos hdeltaBoundary htargetPos
      hsqrtLowerThree
  have hboundaryScalarActual := boundaryAbsorption.absorb
    reentry.reentry_extremal.delta_pos hdeltaBoundary htargetPos
      hsqrtLowerThree
  have hboundaryActual := target.boundaryCWA_of_scalar htargetReentryLoss
    (hdeltaSmall.trans (by norm_num)) <| by
      simpa only [hnormalization] using hboundaryScalarActual
  have harithmeticActual :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              reentry.reentryNormalizationLoss sqrtStickyLoss
              sqrtRequested.1 sqrtRequested.1 /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                sqrtRequested.1 ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta sqrtRequested.1
              incidenceBound coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN
          (sqrtRequested.1 / delta) (1 - sigma) := by
    simpa only [hnormalization] using harithmetic
  have hrestoreActual : proposition63Lemma43MassLoss
        ((81 / 400 : ENNReal) *
          (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
            ENNReal))⁻¹ *
          wz2PaperPureRefinementFraction delta 61) 1 *
        Kakeya.realRpowENN delta secondLoss ≤
      Kakeya.realRpowENN delta reentry.reentryNormalizationLoss := by
    exact (restoreAbsorption.absorbLocal reentry.normalization
      target.data.selected hdeltaRestore
      ).trans_eq (congrArg (Kakeya.realRpowENN delta) hnormalization.symm)
  rcases proposition63_robust_tau_local_point_cover_data_of_cwa outer reentry
      first.state.subshading htargetReentryLoss target currentMap.planeMap
      incidenceBound targetMap.unit hplaneLipschitz targetMap.incidence
      sqrtRequested.2.1 hdeltaGrid htargetPos hsqrtOne hperiodic
      hboundaryActual hgridError hrobustSmall hcrossCall hkappa
      htargetSmall hdeltaSmall (by linarith [htargetPos]) hsqrtSq hsigma
      hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum logScale hdeltaLog hlog
      haxis C harithmeticActual (hdeltaSmall.trans_lt (by norm_num))
      (hnormalization.trans_le hnormalizationSecond) hsecondLoss
      hrestoreActual with
    ⟨second, hfactor, hsecondSubset⟩
  refine ⟨{
    current := extendShading outer.data.selected outer.data.refined
    first := first.state
    first_multiplicity := first.multiplicity
    firstCover := first.cover
    firstRetainedFactor := first.retainedFactor
    first_retained := first.retained
    first_retained_factor_pos := first.retained_factor_pos
    first_retained_factor_ne_top := first.retained_factor_ne_top
    reentry := reentry
    sqrtRequested := sqrtRequested
    sqrt_requested_eq := rfl
    sqrtSticky := target.data
    second := second.state
    secondCover := second.cover
    second_union_subset_sqrt_sticky := hsecondSubset
    secondRetainedFactor := second.retainedFactor
    second_retained := second.retained
    second_retained_factor_pos := second.retained_factor_pos
    second_retained_factor_ne_top := second.retained_factor_ne_top
  }, rfl, ?_⟩
  exact {
    firstRetainedFactor_eq := firstRetainedFactor_eq
    reentryWeight_eq := hweight
    reentryLevel_eq := hlevel
    secondRetainedFactor_eq := by simpa only using hfactor }


private theorem proposition63_prepare_nested_with_current
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss middleLoss finalLoss queryScale tauScale
      sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    (analytic : Proposition63NestedPointCoverAnalyticData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (queryScale := queryScale) (tauScale := tauScale)
      (sqrtScale := sqrtScale) initialNormalized planeMap tauConstant
      sqrtConstant)
    {nextWeightLoss : ℝ}
    (firstTargetCard secondTargetCard : ℕ)
    (analyticMass : Proposition63FourCallAnalyticMassReceipt
      delta analytic.firstRetainedFactor
      analytic.reentry.normalizationWeight analytic.reentry.levelCount
      analytic.secondRetainedFactor firstTargetCard secondTargetCard
      (proposition63CanonicalReentryWeight delta nextWeightLoss)
      (proposition63CanonicalNearbyLevelCount normalizationLoss))
    (hsecondMiddle : secondLoss ≤ middleLoss) (hmiddleLoss : 0 < middleLoss)
    (multiplicityAbsorption : Proposition63FullGrainLogAbsorptionData
      secondLoss middleLoss)
    (hdeltaMultiplicity : delta ≤ multiplicityAbsorption.delta₀)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hperiodicScale : 50 * delta ≤ sqrtScale)
    (hsqrtPos : 0 < sqrtScale) (hsqrtOne : sqrtScale ≤ 1)
    (hbalancingBoundary : 2 * 24000000 *
      (Kakeya.realRpowENN delta (-middleLoss) *
          wz2PaperBoundaryGeometryConstant + 1) *
      ENNReal.ofReal (Real.sqrt (delta / sqrtScale)) <
        Kakeya.realRpowENN delta middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss) (hfinalLoss : 0 < finalLoss)
    (balancingAbsorption : Proposition63FullGrainBalancingAbsorptionData
      middleLoss finalLoss)
    (hdeltaBalancing : delta ≤ balancingAbsorption.delta₀) :
    ∃ nested : Proposition63NestedPointCoverData
        (firstLoss := firstLoss) (reentryLoss := reentryLoss)
        (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
        (finalLoss := finalLoss) (queryScale := queryScale)
        (tauScale := tauScale) (sqrtScale := sqrtScale)
        initialNormalized planeMap tauConstant sqrtConstant,
      nested.current = analytic.current ∧
      Proposition63FourCallNestedMassReceipt
        delta nested.firstRetainedFactor
        nested.reentry.normalizationWeight nested.reentry.levelCount
        nested.secondRetainedFactor nested.prepared.preparationLoss
        firstTargetCard secondTargetCard
        (proposition63CanonicalReentryWeight delta nextWeightLoss)
        (proposition63CanonicalNearbyLevelCount normalizationLoss)
        (proposition63UniformPreparationLoss initialNormalized.croppedFamily) := by
  have cardLogLe :
      ((Nat.log 2 analytic.reentry.normalization.croppedFamily.card + 1 :
          ℕ) : ENNReal) ≤ proposition63OneScaleLogEnvelope delta := by
    have cardBound := proposition63_cropped_cardLog_le_oneScaleEnvelope
      analytic.reentry.normalization
      (hdeltaMultiplicity.trans multiplicityAbsorption.delta₀_le_tiny)
    exact le_trans (by
      exact_mod_cast Nat.add_le_add_right
        (Nat.log_mono_right <| Nat.le_mul_of_pos_left _ (by norm_num)) 1)
      cardBound
  have multiplicitySlack :
      (((Nat.log 2 analytic.reentry.normalization.croppedFamily.card + 1 :
          ℕ) : ENNReal) * Kakeya.realRpowENN delta middleLoss) ≤
        Kakeya.realRpowENN delta secondLoss :=
    (mul_le_mul_right' cardLogLe _).trans <|
      multiplicityAbsorption.absorbEnvelope
        analytic.reentry.reentry_extremal.delta_pos hdeltaMultiplicity
  rcases analytic.prepareFreshBalancedCells hsecondMiddle hmiddleLoss
      multiplicitySlack hdeltaSmall hperiodicScale hsqrtPos hsqrtOne
      hbalancingBoundary hmiddleFinal hfinalLoss
      (balancingAbsorption.absorb
        analytic.reentry.reentry_extremal.delta_pos hdeltaBalancing) with
    ⟨nested, hcurrent, hfirst, hweight, hlevel, hsecond, hpreparation⟩
  refine ⟨nested, hcurrent, ?_⟩
  exact {
    firstRetainedFactor_eq := hfirst.trans analyticMass.firstRetainedFactor_eq
    reentryWeight_eq := hweight.trans analyticMass.reentryWeight_eq
    reentryLevel_eq := hlevel.trans analyticMass.reentryLevel_eq
    secondRetainedFactor_eq := by
      rw [hsecond]
      exact analyticMass.secondRetainedFactor_eq
    preparationLoss_le := hpreparation }

/-- Starting at the rho-level re-entry created by call one, execute calls two
through four and the two robust localizations encoded by the preselected
four-call schedule, returning the concrete nested point cover. -/
theorem proposition63_rho_level_last_three_nested_point_cover_of_absorptions
    {delta sigma initialInputLoss normalizationLoss firstReentryLoss
      firstStageDensityLoss secondReentryDensityLoss firstStageWeightLoss
      outerExtremalLoss robustExponent tau epsilon₁ epsilon₃ parentLoss
      firstLoss nextWeightLoss outputLoss secondLoss middleLoss finalLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource 0}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (firstReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := firstReentryLoss) initialNormalized current)
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss)
    (hfirstReentryLoss : firstReentryLoss = schedule.firstThree.second.sourceLoss)
    (hfirstNormalizationLoss : firstReentry.reentryNormalizationLoss =
      schedule.firstThree.second.normalizationLoss)
    (hdeltaFirst : delta ≤ schedule.firstThree.second.delta₀)
    (robustScale : WZ2PaperRequestedScale delta)
    (hrobustLower : Real.rpow delta
      (1 - schedule.firstThree.secondOutputLoss) ≤ robustScale.1)
    (hrobustUpper : robustScale.1 ≤
      Real.rpow delta schedule.firstThree.secondOutputLoss)
    (hdeltaSecond : delta ≤ schedule.firstThree.third.delta₀)
    (firstStageAbsorption : Proposition63CurrentReentryAbsorptionData
      firstReentryLoss firstReentry.reentryNormalizationLoss firstStageDensityLoss
      outerExtremalLoss firstStageWeightLoss schedule.firstThree.third.sourceLoss
      (proposition63CanonicalNearbyLevelCount
        firstReentry.reentryNormalizationLoss))
    (hdeltaFirstStage : delta ≤ firstStageAbsorption.delta₀)
    (hsourceOuter : firstReentry.reentryNormalizationLoss ≤ outerExtremalLoss)
    (houterExtremalLoss : 0 < outerExtremalLoss)
    (houterRetention : Kakeya.realRpowENN delta outerExtremalLoss ≤
      wz2PaperPureRefinementFraction delta 61 *
        Kakeya.realRpowENN delta firstReentry.reentryNormalizationLoss)
    (houterTargetReentry : outerExtremalLoss ≤
      schedule.firstThree.third.sourceLoss)
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
      schedule.firstThree.third.normalizationLoss epsilon₁)
    (firstCrossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        robustExponent schedule.firstThree.secondOutputLoss
        schedule.firstThree.third.normalizationLoss firstStageWeightLoss 4
        (proposition63CanonicalNearbyLevelCount
          firstReentry.reentryNormalizationLoss))
    (hdeltaFirstGrid : delta ≤ firstGridAbsorption.delta₀)
    (hdeltaFirstCross : delta ≤ firstCrossAbsorption.delta₀)
    (hrobustScale : robustScale.1 = Real.rpow delta robustExponent)
    (htargetScale : targetScale.1 = Real.rpow delta robustExponent)
    (hdeltaTau : delta ≤ tau) (htau : 0 < tau) (htauOne : tau ≤ 1)
    (firstBoundaryAbsorption : Proposition63RobustBoundaryAbsorptionData
      schedule.thirdOutputLoss
      schedule.firstThree.third.normalizationLoss)
    (hdeltaFirstBoundary : delta ≤ firstBoundaryAbsorption.delta₀)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
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
          schedule.firstThree.third.normalizationLoss
          schedule.thirdOutputLoss targetScale.1 tau /
          (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) * tau ^ 2 / 200)) *
        (2 * proposition63DependentSlabWidth delta tau incidenceBound
          coefficient / delta + 2)) ≤
      firstConstant * Kakeya.realRpowENN (tau / delta) (1 - sigma))
    (hnormalizationParent : schedule.firstThree.third.normalizationLoss ≤
      parentLoss)
    (hparentRetention : Kakeya.realRpowENN delta parentLoss ≤
      wz2PaperPureRefinementFraction delta 61 * Kakeya.realRpowENN delta
        schedule.firstThree.third.normalizationLoss)
    (hparentOutput : parentLoss ≤ firstLoss) (hfirstLoss : 0 < firstLoss)
    (firstRestoreAbsorption :
      Proposition63RobustPointCoverRestorationAbsorptionData
        parentLoss firstLoss 0)
    (hdeltaFirstRestore : delta ≤ firstRestoreAbsorption.delta₀)
    (secondReentryAbsorption : Proposition63CurrentReentryAbsorptionData
      schedule.lastThree.second.sourceLoss
      schedule.lastThree.second.normalizationLoss secondReentryDensityLoss firstLoss
      nextWeightLoss schedule.lastThree.third.sourceLoss
      (proposition63CanonicalNearbyLevelCount
        schedule.lastThree.second.normalizationLoss))
    (hdeltaSecondReentry : delta ≤ secondReentryAbsorption.delta₀)
    (hfirstReentry : firstLoss ≤ schedule.lastThree.third.sourceLoss)
    (hdeltaFourth : delta ≤ schedule.lastThree.third.delta₀)
    (sqrtRequested : WZ2PaperRequestedScale delta)
    (hsqrtLower : Real.rpow delta (1 - outputLoss) ≤ sqrtRequested.1)
    (hsqrtUpper : sqrtRequested.1 ≤ Real.rpow delta outputLoss)
    (hsqrtOne : sqrtRequested.1 ≤ 1)
    (secondBoundaryAbsorption : Proposition63RobustBoundaryAbsorptionData
      outputLoss schedule.lastThree.third.normalizationLoss)
    (hdeltaSecondBoundary : delta ≤ secondBoundaryAbsorption.delta₀)
    (secondGridAbsorption : Proposition63RobustGridPruningAbsorptionData
      schedule.lastThree.third.normalizationLoss epsilon₁)
    (hdeltaSecondGrid : delta ≤ secondGridAbsorption.delta₀)
    (secondCrossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        robustExponent schedule.lastThree.secondOutputLoss
        schedule.lastThree.third.normalizationLoss nextWeightLoss 4
        (proposition63CanonicalNearbyLevelCount
          schedule.lastThree.second.normalizationLoss))
    (hdeltaSecondCross : delta ≤ secondCrossAbsorption.delta₀)
    (htargetRobustSmall : targetScale.1 ≤ 1 / 10000)
    (htargetKappa : Real.rpow delta epsilon₃ ≤ targetScale.1)
    (hsqrtSmall : sqrtRequested.1 ≤ 1 / 12)
    (hsqrtSq : sqrtRequested.1 ^ 2 ≤ 4 * delta)
    (finalConstant : ENNReal)
    (hfinalArithmetic : ENNReal.ofReal
      ((proposition63RobustTauTotalVolume delta sigma
          schedule.lastThree.third.normalizationLoss outputLoss
          sqrtRequested.1 sqrtRequested.1 /
          (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
            sqrtRequested.1 ^ 2 / 200)) *
        (2 * proposition63DependentSlabWidth delta sqrtRequested.1
          incidenceBound coefficient / delta + 2)) ≤
      finalConstant * Kakeya.realRpowENN
        (sqrtRequested.1 / delta) (1 - sigma))
    (hnormalizationSecond : schedule.lastThree.third.normalizationLoss ≤
      secondLoss)
    (hsecondLoss : 0 < secondLoss)
    (secondRestoreAbsorption :
      Proposition63RobustPointCoverRestorationAbsorptionData
        schedule.lastThree.third.normalizationLoss secondLoss 61)
    (hdeltaSecondRestore : delta ≤ secondRestoreAbsorption.delta₀)
    (hsecondMiddle : secondLoss ≤ middleLoss) (hmiddleLoss : 0 < middleLoss)
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
    Nonempty (Proposition63RhoLevelFourCallData
      (tau := tau) (firstLoss := firstLoss)
      (weightLoss := firstStageWeightLoss) (nextWeightLoss := nextWeightLoss)
      (secondLoss := secondLoss)
      (finalLoss := finalLoss) firstReentry schedule hfirstReentryLoss
      robustScale targetScale sqrtRequested currentMap firstConstant
      finalConstant) := by
  let firstThree := schedule.firstThree
  let root : Proposition63RootNormalizationData
      (outputLoss := firstReentry.reentryNormalizationLoss)
      firstReentry.ordinarySource 0 firstStageDensityLoss :=
    Proposition63RootNormalizationData.ofNormalization
      firstReentry.normalization
      (firstStageAbsorption.density_absorb
        firstReentry.reentry_extremal.delta_pos hdeltaFirstStage)
  have ambientTwo := firstStageAbsorption.ambient_two
    firstReentry.reentry_extremal.delta_pos hdeltaFirstStage
  have htwoNormalization :
      2 * firstReentry.reentryNormalizationLoss ≤ firstThree.third.sourceLoss := by
    rw [hfirstNormalizationLoss]
    have hnormalizationLt := firstThree.second.normalizationLoss_lt_output
    have houtputEq := firstThree.secondOutputLoss_eq
    have houtputLt := firstThree.secondOutputLoss_lt_thirdSource
    linarith
  rcases root.finiteNearbySchedule
      firstReentry.reentry_normalization_loss_pos ambientTwo
      htwoNormalization with ⟨targetNearbySchedule⟩
  have regularizationAbsorb := firstStageAbsorption.regularization_absorb
    firstReentry.normalization rfl targetNearbySchedule rfl rfl
    firstReentry.reentry_extremal.delta_pos hdeltaFirstStage
  rcases proposition63_first_robust_target_ambient_runtime_of_absorptions
      firstReentry firstThree.second hfirstReentryLoss
      hfirstNormalizationLoss hdeltaFirst robustScale hrobustLower
      hrobustUpper firstThree.third hdeltaSecond
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
      (hdeltaFirstStage.trans firstStageAbsorption.delta₀_le_tiny)
      targetScale htargetLower htargetUpper currentMap hplaneLipschitz
      firstGridAbsorption firstCrossAbsorption hdeltaFirstGrid
      hdeltaFirstCross hrobustScale hdeltaTau htau htauOne
      firstBoundaryAbsorption hdeltaFirstBoundary hrobustSmall hkappa
      htargetSmall htargetTau htauSq hsigma hsigmaOne hepsilon₁ hepsilon₃
      hepsilonSum logScale hdeltaLog hlog haxis firstConstant
      hfirstArithmetic hnormalizationParent hparentRetention hparentOutput
      hfirstLoss firstRestoreAbsorption hdeltaFirstRestore with
    ⟨outer, targetReentry, target, targetMap, htargetMap,
      htargetLipschitz, ⟨firstRobust⟩⟩
  let fixedTargetMap : PaperWZ1WeakPlaneMapData target.data.refined
      incidenceBound :=
    { planeMap := currentMap.planeMap
      measurable := by rw [← htargetMap]; exact targetMap.measurable
      unit := by
        intro point hpoint
        rw [← htargetMap]
        exact targetMap.unit point hpoint
      incidence := by
        intro index point hpoint
        rw [← htargetMap]
        exact targetMap.incidence index point hpoint }
  let firstRobustFixed := htargetMap ▸ firstRobust
  let ambientTargetMap := target.ambientTerminalPlaneMap fixedTargetMap
  have hambientLipschitz : LipschitzWith coefficient
      ambientTargetMap.planeMap := by
    change LipschitzWith coefficient currentMap.planeMap
    rw [← htargetMap]
    exact htargetLipschitz
  have htwoTarget : 2 * targetReentry.reentryNormalizationLoss ≤
      schedule.fourth.sourceLoss := by
    change 2 * targetReentry.reentryNormalizationLoss ≤
      schedule.fourth.sourceLoss
    rw [firstRobust.target_normalization_loss]
    change 2 * schedule.third.normalizationLoss ≤ schedule.fourth.sourceLoss
    linarith [schedule.third.normalizationLoss_lt_output,
      schedule.thirdOutputLoss_eq, schedule.thirdOutputLoss_lt_fourthSource]
  have secondReentryPackage :
      ∃ actual : Proposition63CurrentReentryAbsorptionData
          schedule.third.sourceLoss targetReentry.reentryNormalizationLoss
          secondReentryDensityLoss firstLoss nextWeightLoss schedule.fourth.sourceLoss
          (proposition63CanonicalNearbyLevelCount
            targetReentry.reentryNormalizationLoss),
        delta ≤ actual.delta₀ := by
    rw [firstRobust.target_normalization_loss]
    exact ⟨secondReentryAbsorption, hdeltaSecondReentry⟩
  rcases secondReentryPackage with
    ⟨secondReentryActual, hdeltaSecondReentryActual⟩
  have secondCrossPackage :
      ∃ actual : Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
          robustExponent schedule.thirdOutputLoss
          schedule.fourth.normalizationLoss nextWeightLoss 4
          (proposition63CanonicalNearbyLevelCount
            targetReentry.reentryNormalizationLoss),
        delta ≤ actual.delta₀ := by
    rw [firstRobust.target_normalization_loss]
    exact ⟨secondCrossAbsorption, hdeltaSecondCross⟩
  rcases secondCrossPackage with ⟨secondCrossActual, hdeltaSecondCrossActual⟩
  rcases proposition63_to_nested_analytic_with_current
      target ambientTargetMap hambientLipschitz
      (firstConstant * Kakeya.realRpowENN (tau / delta) (1 - sigma))
      firstRobustFixed.first firstRobustFixed.firstRetainedFactor
      secondReentryActual hdeltaSecondReentryActual
      targetReentry.reentry_normalization_loss_pos htwoTarget hfirstReentry
      hfirstLoss schedule.fourth.normalizationLoss_pos
      schedule.fourth.sourceLoss_le_half schedule.lastThree rfl rfl
      hdeltaFourth sqrtRequested hsqrtLower hsqrtUpper hsqrtOne
      secondBoundaryAbsorption hdeltaSecondBoundary secondGridAbsorption
      hdeltaSecondGrid secondCrossActual hdeltaSecondCrossActual htargetScale
      htargetRobustSmall htargetKappa hsqrtSmall
      (hdeltaFirstStage.trans
        (firstStageAbsorption.delta₀_le_tiny.trans (by norm_num)))
      hsqrtSq hsigma hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum logScale
      hdeltaLog hlog haxis finalConstant hfinalArithmetic
      hnormalizationSecond hsecondLoss secondRestoreAbsorption
      hdeltaSecondRestore with
    ⟨analytic, hanalyticCurrent, analyticMass⟩
  have htargetPos : 0 < sqrtRequested.1 :=
    analytic.reentry.reentry_extremal.delta_pos.trans_le sqrtRequested.2.1
  have hperiodicGrid := secondBoundaryAbsorption.periodic
    analytic.reentry.reentry_extremal.delta_pos hdeltaSecondBoundary
    htargetPos (hsqrtLower.trans (by nlinarith [htargetPos]))
  have hgridSideLeTarget : gridSide (sqrtRequested.1 / 2) ≤
      sqrtRequested.1 := gridSide_half_le_self htargetPos.le
  rcases proposition63_prepare_nested_with_current analytic
      target.data.selected.family.card analytic.sqrtSticky.selected.family.card
      analyticMass hsecondMiddle
      hmiddleLoss multiplicityAbsorption hdeltaMultiplicity
      (hdeltaFirstStage.trans
        (firstStageAbsorption.delta₀_le_tiny.trans (by norm_num)))
      (hperiodicGrid.trans hgridSideLeTarget) htargetPos hsqrtOne
      hbalancingBoundary hmiddleFinal hfinalLoss balancingAbsorption
      hdeltaBalancing with ⟨nested, hcurrent, nestedMass⟩
  refine ⟨{ outer := outer,
             targetReentry := targetReentry,
             target := target,
             targetNormalization := firstRobust.target_normalization_loss,
             targetCanonicalWeight := firstRobust.targetCanonicalWeight,
             targetCanonicalLevel := firstRobust.targetCanonicalLevel,
             nested := ?_,
             nested_eq := ?_,
             secondTargetCard := analytic.sqrtSticky.selected.family.card,
             secondTargetCard_le := by
               let secondEmbedding :
                   Fin analytic.sqrtSticky.selected.family.card ↪
                     Fin targetReentry.normalization.croppedFamily.card :=
                 analytic.sqrtSticky.selected.embedding.trans
                   analytic.reentry.regularized.selected.embedding
               convert Fintype.card_le_of_injective secondEmbedding
                 secondEmbedding.injective using 1 <;>
                   simp only [Fintype.card_fin] <;> rfl,
             nestedMass := ?_ }⟩
  · exact nested
  · exact hcurrent.trans hanalyticCurrent
  · exact nestedMass

/-- Execute all four scheduled rich calls, beginning with the original fine
configuration and retaining the exact source-witness re-entry needed for the
whole-cell pullback after the nested point cover has been produced. -/
theorem proposition63_four_call_nested_point_cover_of_absorptions
    {delta sigma inputLoss normalizationLoss rhoDensityLoss
      firstStageDensityLoss secondReentryDensityLoss outputLoss rhoWeightLoss
      firstStageWeightLoss
      outerExtremalLoss robustExponent tau epsilon₁ epsilon₃ parentLoss firstLoss
      nextWeightLoss secondLoss middleLoss finalLoss incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {fineShading : WZ1PaperTubeShading family}
    (fineReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) fineShading normalizationExponent
      inputLoss normalizationLoss)
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss)
    (hinput : inputLoss = schedule.first.sourceLoss)
    (hnormalization : normalizationLoss = schedule.first.normalizationLoss)
    (hdeltaFirstCall : delta ≤ schedule.first.delta₀)
    (rho : WZ2PaperRequestedScale delta)
    (hrhoLower : Real.rpow delta (1 - schedule.firstOutputLoss) ≤ rho.1)
    (hrhoUpper : rho.1 ≤ Real.rpow delta schedule.firstOutputLoss)
    (rootAxialWindow : ∀ index point,
      point ∈ fineReentry.geometry.frame ''
          fineReentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8)
    {sourceMap : PaperWZ1WeakPlaneMapData fineShading incidence}
    {sourceCoefficient : NNReal}
    (extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient)
    (hcellError :
      ((lipschitzExtensionConstant Point3 * sourceCoefficient : NNReal) : ℝ) *
        (rho.1 * Real.sqrt 3) ≤ 1 / 2)
    (rhoAbsorption : Proposition63CurrentReentryAbsorptionData
      (schedule.second.sourceLoss / 16) (schedule.second.sourceLoss / 4)
      rhoDensityLoss schedule.firstOutputLoss rhoWeightLoss schedule.second.sourceLoss
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
    (hdeltaTau : rho.1 ≤ tau) (htau : 0 < tau) (htauOne : tau ≤ 1)
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
    (hdeltaBalancing : rho.1 ≤ balancingAbsorption.delta₀) :
    Nonempty (Proposition63FourCallNestedRuntimeData
      (tau := tau) (firstLoss := firstLoss)
      (rhoWeightLoss := rhoWeightLoss)
      (firstStageWeightLoss := firstStageWeightLoss)
      (nextWeightLoss := nextWeightLoss)
      (secondLoss := secondLoss)
      (finalLoss := finalLoss) (incidence := incidence) fineReentry schedule rho
      rootAxialWindow sourceCoefficient robustScale targetScale sqrtRequested
      firstConstant finalConstant extension.ambient.planeMap) := by
  rcases proposition63_four_call_source_witness_prefix_of_absorption
      fineReentry schedule hinput hnormalization hdeltaFirstCall rho
      hrhoLower hrhoUpper rootAxialWindow extension hcellError rhoAbsorption
      hrhoAbsorption hrhoSmall with
    ⟨rich1, ⟨currentResult⟩⟩
  have firstStagePackage :
      ∃ actual : Proposition63CurrentReentryAbsorptionData
          schedule.second.sourceLoss
          currentResult.currentReentry.reentryNormalizationLoss
          firstStageDensityLoss outerExtremalLoss firstStageWeightLoss
          schedule.third.sourceLoss
          (proposition63CanonicalNearbyLevelCount
            currentResult.currentReentry.reentryNormalizationLoss),
        rho.1 ≤ actual.delta₀ := by
    rw [currentResult.currentNormalization]
    exact ⟨firstStageAbsorption, hdeltaFirstStage⟩
  rcases firstStagePackage with ⟨firstStageActual, hdeltaFirstStageActual⟩
  have firstCrossPackage :
      ∃ actual : Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
          robustExponent schedule.secondOutputLoss
          schedule.third.normalizationLoss firstStageWeightLoss 4
          (proposition63CanonicalNearbyLevelCount
            currentResult.currentReentry.reentryNormalizationLoss),
        rho.1 ≤ actual.delta₀ := by
    rw [currentResult.currentNormalization]
    exact ⟨firstCrossAbsorption, hdeltaFirstCross⟩
  rcases firstCrossPackage with ⟨firstCrossActual, hdeltaFirstCrossActual⟩
  rcases proposition63_rho_level_last_three_nested_point_cover_of_absorptions
      currentResult.currentReentry schedule rfl
      currentResult.currentNormalization hdeltaSecondCall
      robustScale hrobustLower hrobustUpper hdeltaThirdCall
      firstStageActual hdeltaFirstStageActual
      (by
        simpa only [Proposition63RichFourCallScheduleData.firstThree,
          currentResult.currentNormalization] using hsourceOuter)
      houterExtremalLoss
      (by
        simpa only [Proposition63RichFourCallScheduleData.firstThree,
          currentResult.currentNormalization] using houterRetention)
      houterTargetReentry targetScale htargetLower
      htargetUpper currentResult.currentMap currentResult.currentLipschitz
      firstGridAbsorption
      firstCrossActual hdeltaFirstGrid hdeltaFirstCrossActual hrobustScale
      htargetScale hdeltaTau htau htauOne firstBoundaryAbsorption
      hdeltaFirstBoundary hrobustSmall hkappa htargetSmall htargetTau htauSq
      hsigma hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum logScale hdeltaLog
      hlog haxis firstConstant hfirstArithmetic hnormalizationParent
      hparentRetention hparentOutput hfirstLoss firstRestoreAbsorption
      hdeltaFirstRestore secondReentryAbsorption hdeltaSecondReentry
      hfirstReentry hdeltaFourth sqrtRequested hsqrtLower hsqrtUpper hsqrtOne
      secondBoundaryAbsorption hdeltaSecondBoundary secondGridAbsorption
      hdeltaSecondGrid secondCrossAbsorption hdeltaSecondCross
      htargetRobustSmall htargetKappa hsqrtSmall hsqrtSq finalConstant
      hfinalArithmetic hnormalizationSecond hsecondLoss
      secondRestoreAbsorption hdeltaSecondRestore hsecondMiddle hmiddleLoss
      multiplicityAbsorption hdeltaMultiplicity hbalancingBoundary
      hmiddleFinal hfinalLoss balancingAbsorption hdeltaBalancing with
    ⟨rhoData⟩
  exact ⟨{ rich1 := rich1
           currentMap := currentResult.currentMap
           currentReentry := currentResult.currentReentry
           currentNormalization := currentResult.currentNormalization
           currentCanonicalWeight := currentResult.currentCanonicalWeight
           currentCanonicalLevel := currentResult.currentCanonicalLevel
           currentMap_eq := currentResult.currentMap_eq
           rhoData := rhoData }⟩

end Kakeya.Assouad.PureWZ2
