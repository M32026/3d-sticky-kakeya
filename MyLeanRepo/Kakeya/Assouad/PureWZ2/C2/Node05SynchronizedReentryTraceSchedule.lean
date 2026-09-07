import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05SynchronizedOwnerSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ReentryTraceFloorSchedule

/-!
# Scheduled synchronized post-grain re-entry

This adapter instantiates the local ordinary-trace critical-floor conversion
from one uniform schedule.  The selected family, shading, and re-entry remain
the projections of the same synchronized core.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Select the synchronized next source using one preselected trace-floor
schedule.  Runtime hypotheses retain only the genuinely source-dependent
geometric and mass bounds. -/
theorem exists_pureWZ2Node05SynchronizedOwnerSelection_of_reentryTraceSchedule
    {delta sigma ambientLoss sourceLoss normalizationLoss grainLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent ancestorNormalizationExponent : ℕ}
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent)
    (ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      ancestorNormalizationExponent sourceLoss normalizationLoss)
    (coarseGrains : PureWZ2GrainRefinementData
      ambient.croppedCoarseShading sigma grainLoss)
    (inputEta outputEta selectedLoss structuralBudget : ℝ)
    (selectedNormalizationExponent : ℕ)
    (croppedMassFraction : ENNReal)
    (schedule : PureWZ2ReentryTraceFloorSchedule
      sigma selectedLoss structuralBudget)
    (hdeltaSchedule : rhoRequested.1 ≤ schedule.delta₀)
    (hsourceLoss : sourceLoss ≤ schedule.traceSourceCeiling)
    (densitySeparation :
      Kakeya.realRpowENN rhoRequested.1 outputEta ≤
        (1 / 2 : ENNReal) * Kakeya.realRpowENN rhoRequested.1 inputEta)
    (inputDensityAbsorption :
      Kakeya.realRpowENN rhoRequested.1 inputEta ≤
        (100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
          Kakeya.realRpowENN rhoRequested.1 grainLoss)
    (croppedMassAbsorption :
      croppedMassFraction ≤
        (100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity)
    (grainLoss_le_density : grainLoss ≤ schedule.densityLoss)
    (nearby : ∀ core : PureWZ2Node05SynchronizedPostGrainCore
      (pureWZ2Node05AmbientCoarseIdentityRefinement ambient)
      ancestor coarseGrains outputEta croppedMassFraction,
      WZ2PaperPureCWAAtNearbyScales
        (pureWZ2Node05PostGrainSelectedSubfamily
          ambient.coarse core.retained).family
        (Kakeya.realRpowENN rhoRequested.1 (-schedule.densityLoss)))
    (densityAbsorption :
      (13824 : ENNReal) *
          Kakeya.realRpowENN rhoRequested.1 schedule.densityLoss ≤
        Kakeya.realRpowENN rhoRequested.1 outputEta)
    (topLevelAbsorption :
      ((Kakeya.realRpowENN rhoRequested.1 outputEta)⁻¹ * 1) *
          Kakeya.realRpowENN rhoRequested.1 (-grainLoss) ≤
        Kakeya.realRpowENN rhoRequested.1 (-selectedLoss))
    (normalizationLoss_le : normalizationLoss ≤ selectedLoss)
    (retainedMassAbsorption :
      2 * wz2PaperPureRefinementFraction rhoRequested.1
          selectedNormalizationExponent ≤
        ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
          Kakeya.realRpowENN rhoRequested.1 grainLoss) *
            wz2PaperPureRefinementFraction rhoRequested.1
              ancestorNormalizationExponent)
    (densityBudget : Kakeya.realRpowENN rhoRequested.1 sourceLoss / 2 ≤
      Kakeya.realRpowENN rhoRequested.1 outputEta) :
    Nonempty (PureWZ2Node05SynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      ambient ancestor coarseGrains croppedMassFraction) := by
  have traceAbsorption : (schedule.lossConstant rhoRequested.1)⁻¹ ≤
      (100 : ENNReal)⁻¹ *
        Kakeya.realRpowENN rhoRequested.1 outputEta :=
    (schedule.trace_absorption rhoRequested.1
      ancestor.cropped_extremal.delta_pos hdeltaSchedule sourceLoss
      ancestor.sourceLoss_pos.le hsourceLoss).trans
        (by
          simpa [mul_comm] using
            (mul_le_mul_right densityBudget (100 : ENNReal)⁻¹))
  exact exists_pureWZ2Node05SynchronizedOwnerSelection_of_reentryTrace
    ambient ancestor coarseGrains inputEta outputEta schedule.densityLoss
    selectedLoss structuralBudget selectedNormalizationExponent
    croppedMassFraction (schedule.lossConstant rhoRequested.1)
    (hdeltaSchedule.trans schedule.delta₀_le_twelve) densitySeparation
    inputDensityAbsorption croppedMassAbsorption schedule.criticalFloor
    (schedule.lossConstant_one ancestor.cropped_extremal.delta_pos
      hdeltaSchedule)
    (schedule.lossConstant_ne_top rhoRequested.1) grainLoss_le_density
    schedule.densityLoss_le_floor
    (hdeltaSchedule.trans schedule.delta₀_le_floor) nearby
    densityAbsorption topLevelAbsorption traceAbsorption
    (schedule.cwa_absorption ancestor.cropped_extremal.delta_pos).le
    (schedule.density_absorption ancestor.cropped_extremal.delta_pos).le
    normalizationLoss_le retainedMassAbsorption densityBudget

/-- Scheduled selected-owner construction using the jointly regularized
post-grain core.  Unlike the compatibility theorem above, this route does not
ask for nearby CWA on every hypothetical core: the weighted regularizer
returns one core together with the certificate on that exact selected family. -/
theorem exists_pureWZ2Node05SynchronizedOwnerSelection_of_regularized_reentryTraceSchedule
    {delta sigma ambientLoss sourceLoss normalizationLoss grainLoss : ℝ}
    {ambientConstant : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent ancestorNormalizationExponent : ℕ}
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent)
    (ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      ancestorNormalizationExponent sourceLoss normalizationLoss)
    (coarseGrains : PureWZ2GrainRefinementData
      ambient.croppedCoarseShading sigma grainLoss)
    (inputEta outputEta selectedLoss structuralBudget epsilon : ℝ)
    (selectedNormalizationExponent : ℕ)
    (croppedMassFraction : ENNReal)
    (schedule : PureWZ2ReentryTraceFloorSchedule
      sigma selectedLoss structuralBudget)
    (hdeltaSchedule : rhoRequested.1 ≤ schedule.delta₀)
    (hsourceLoss : sourceLoss ≤ schedule.traceSourceCeiling)
    (ambientNearby : WZ2PaperPureCWAAtNearbyScales
      (pureWZ2Node05AmbientCoarseIdentityRefinement ambient).selected.family
      ambientConstant)
    (epsilon_pos : 0 < epsilon)
    (densitySeparation :
      Kakeya.realRpowENN rhoRequested.1 outputEta ≤
        (1 / 2 : ENNReal) * Kakeya.realRpowENN rhoRequested.1 inputEta)
    (inputDensityAbsorption :
      Kakeya.realRpowENN rhoRequested.1 inputEta ≤
        (100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
          Kakeya.realRpowENN rhoRequested.1 grainLoss)
    (croppedMassAbsorption :
      croppedMassFraction ≤
        (100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity)
    (roundingAbsorption :
      ENNReal.ofReal (Real.rpow rhoRequested.1 (-epsilon)) *
          ambientConstant ≤
        Kakeya.realRpowENN rhoRequested.1 (-schedule.densityLoss))
    (restrictionAbsorption :
      wz2PaperPureNearbyRestrictionConstant
          ambientConstant
          (Kakeya.realRpowENN rhoRequested.1 inputEta *
            Kakeya.deltaTubeVolume rhoRequested.1)
          (pureWZ2SpatialCellDegreeConstant epsilon
            (pureWZ2Node05AmbientCoarseIdentityRefinement
              ambient).selected.family.card)
          (pureWZ2SpatialCellRegularizationLoss epsilon
              (pureWZ2Node05AmbientCoarseIdentityRefinement
                ambient).selected.family.card *
            Kakeya.deltaTubeVolume rhoRequested.1) ≤
        Kakeya.realRpowENN rhoRequested.1 (-schedule.densityLoss))
    (cardinalityAbsorption :
      Kakeya.realRpowENN rhoRequested.1 outputEta *
          pureWZ2SpatialCellRegularizationLoss epsilon
            (pureWZ2Node05AmbientCoarseIdentityRefinement
              ambient).selected.family.card ≤
        Kakeya.realRpowENN rhoRequested.1 inputEta)
    (grainLoss_le_density : grainLoss ≤ schedule.densityLoss)
    (densityAbsorption :
      (13824 : ENNReal) *
          Kakeya.realRpowENN rhoRequested.1 schedule.densityLoss ≤
        Kakeya.realRpowENN rhoRequested.1 outputEta)
    (topLevelAbsorption :
      ((Kakeya.realRpowENN rhoRequested.1 outputEta)⁻¹ * 1) *
          Kakeya.realRpowENN rhoRequested.1 (-grainLoss) ≤
        Kakeya.realRpowENN rhoRequested.1 (-selectedLoss))
    (normalizationLoss_le : normalizationLoss ≤ selectedLoss)
    (retainedMassAbsorption :
      pureWZ2SpatialCellRegularizationLoss epsilon
            (pureWZ2Node05AmbientCoarseIdentityRefinement
              ambient).selected.family.card *
          wz2PaperPureRefinementFraction rhoRequested.1
            selectedNormalizationExponent ≤
        ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
          Kakeya.realRpowENN rhoRequested.1 grainLoss) *
            wz2PaperPureRefinementFraction rhoRequested.1
              ancestorNormalizationExponent)
    (densityBudget : Kakeya.realRpowENN rhoRequested.1 sourceLoss / 2 ≤
      Kakeya.realRpowENN rhoRequested.1 outputEta) :
    Nonempty (PureWZ2Node05SynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      ambient ancestor coarseGrains croppedMassFraction) := by
  have traceAbsorption : (schedule.lossConstant rhoRequested.1)⁻¹ ≤
      (100 : ENNReal)⁻¹ *
        Kakeya.realRpowENN rhoRequested.1 outputEta :=
    (schedule.trace_absorption rhoRequested.1
      ancestor.cropped_extremal.delta_pos hdeltaSchedule sourceLoss
      ancestor.sourceLoss_pos.le hsourceLoss).trans
        (by
          simpa [mul_comm] using
            (mul_le_mul_right densityBudget (100 : ENNReal)⁻¹))
  exact exists_pureWZ2Node05SynchronizedOwnerSelection_of_regularized_reentryTrace
    ambient ancestor coarseGrains croppedMassFraction
    (schedule.lossConstant rhoRequested.1) ambientNearby
    (hdeltaSchedule.trans schedule.delta₀_le_twelve) densitySeparation
    inputDensityAbsorption croppedMassAbsorption epsilon_pos
    (lt_of_le_of_lt (hdeltaSchedule.trans schedule.delta₀_le_twelve)
      (by norm_num))
    roundingAbsorption restrictionAbsorption cardinalityAbsorption
    schedule.criticalFloor
    (schedule.lossConstant_one ancestor.cropped_extremal.delta_pos
      hdeltaSchedule)
    (schedule.lossConstant_ne_top rhoRequested.1) grainLoss_le_density
    schedule.densityLoss_le_floor
    (hdeltaSchedule.trans schedule.delta₀_le_floor) densityAbsorption
    topLevelAbsorption traceAbsorption
    (schedule.cwa_absorption ancestor.cropped_extremal.delta_pos).le
    (schedule.density_absorption ancestor.cropped_extremal.delta_pos).le
    normalizationLoss_le retainedMassAbsorption densityBudget

end Kakeya.Assouad

end
