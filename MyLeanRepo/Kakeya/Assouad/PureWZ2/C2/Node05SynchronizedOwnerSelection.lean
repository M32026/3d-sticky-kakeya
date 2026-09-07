import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05SynchronizedCompleteParentOverlay
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyRegularizedNearbyCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureCriticalFloorSelection

/-!
# Owner output synchronized with the post-grain selection

This module binds the synchronized post-grain core to the exact coarse family
of one existing Node-5 owner output.  The selected coarse family, selected
grain shading, selected re-entry, complete-parent fine pullback, and spatial
fine overlay are all projections of one dependent record.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- The identity refinement used only to index the post-grain synchronization
on the exact coarse shading of `ambient`. -/
noncomputable abbrev pureWZ2Node05AmbientCoarseIdentityRefinement
    {delta sigma ambientLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent : ℕ}
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent) :=
  pureWZ2Node05PostGrainIdentityRefinement ambient.croppedCoarseShading

/-- Compatibility-only structural source used by earlier anchored modules.
The production `PreScheduledAnchored` route below does not consume this type:
its structural shading is definitionally `ambient.croppedCoarseShading`. -/
structure PureWZ2Node05AnchoredCoarseSource
    {delta sigma ambientLoss grainLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent : ℕ}
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent) where
  shading : WZ1PaperTubeShading ambient.coarse
  subshading : PureWZ2PaperIsSubshading shading
    ambient.croppedCoarseShading
  line_class : WZ1PaperIsLineClass ambient.coarse
  cubical : WZ1PaperIsCubicalShading shading
  extremal : WZ2PaperCroppedIsExtremal sigma grainLoss
    ambient.coarse shading
  top_level_cwa : WZ2PaperConvexWolffBound ambient.coarse
    (Kakeya.realRpowENN rhoRequested.1 (-grainLoss))
  volume_lower : Kakeya.realRpowENN rhoRequested.1
      (sigma + grainLoss) ≤ volume shading.union

/-- One synchronized selection on the literal coarse output of an owner call.
No family or shading is reselected after `core`. -/
structure PureWZ2Node05SynchronizedOwnerSelection
    {delta sigma ambientLoss sourceLoss normalizationLoss grainLoss
      outputEta selectedLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent ancestorNormalizationExponent
      selectedNormalizationExponent : ℕ}
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent)
    (ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      ancestorNormalizationExponent sourceLoss normalizationLoss)
    (coarseGrains : PureWZ2GrainRefinementData
      ambient.croppedCoarseShading sigma grainLoss)
    (croppedMassFraction : ENNReal) where
  core : PureWZ2Node05SynchronizedPostGrainCore
    (pureWZ2Node05AmbientCoarseIdentityRefinement ambient)
    ancestor coarseGrains outputEta croppedMassFraction
  receipt : PureWZ2Node05SelectedReentryReceipt core selectedLoss
    selectedNormalizationExponent

namespace PureWZ2Node05RegularizedPostGrainCore

/-- Turn one jointly regularized post-grain core into the selected owner
source using a cropped critical floor.  The nearby-CWA certificate and the
selected family are projections of the same `regularized` witness; no
family-valued callback is used and no second core is selected. -/
noncomputable def toSynchronizedOwnerSelectionOfCriticalFloor
    {delta sigma ambientLoss sourceLoss normalizationLoss grainLoss
      outputEta epsilon selectedLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent ancestorNormalizationExponent
      selectedNormalizationExponent : ℕ}
    {ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent}
    {ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      ancestorNormalizationExponent sourceLoss normalizationLoss}
    {coarseGrains : PureWZ2GrainRefinementData
      ambient.croppedCoarseShading sigma grainLoss}
    {croppedMassFraction : ENNReal}
    (criticalFloor : PureWZ2CroppedCriticalFloorSelectionData
      sigma selectedLoss selectedLoss)
    (regularized : PureWZ2Node05RegularizedPostGrainCore
      (outputEta := outputEta)
      (pureWZ2Node05AmbientCoarseIdentityRefinement ambient) ancestor
      coarseGrains croppedMassFraction
      (Kakeya.realRpowENN rhoRequested.1
        (-criticalFloor.structuralLoss)) epsilon)
    (grainLoss_le : grainLoss ≤ selectedLoss)
    (hdeltaSmall : rhoRequested.1 ≤ 1 / 12)
    (hdeltaCutoff : rhoRequested.1 ≤ criticalFloor.delta₀)
    (densityAbsorption :
      (13824 : ENNReal) *
          Kakeya.realRpowENN rhoRequested.1 criticalFloor.structuralLoss ≤
        Kakeya.realRpowENN rhoRequested.1 outputEta)
    (topLevelAbsorption :
      ((Kakeya.realRpowENN rhoRequested.1 outputEta)⁻¹ * 1) *
          Kakeya.realRpowENN rhoRequested.1 (-grainLoss) ≤
        Kakeya.realRpowENN rhoRequested.1 (-selectedLoss))
    (normalizationLoss_le : normalizationLoss ≤ selectedLoss)
    (retainedMassAbsorption :
      regularized.core.retentionLoss *
          wz2PaperPureRefinementFraction rhoRequested.1
            selectedNormalizationExponent ≤
        ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
          Kakeya.realRpowENN rhoRequested.1 grainLoss) *
            wz2PaperPureRefinementFraction rhoRequested.1
              ancestorNormalizationExponent)
    (densityBudget : Kakeya.realRpowENN rhoRequested.1 sourceLoss / 2 ≤
      Kakeya.realRpowENN rhoRequested.1 outputEta) :
    PureWZ2Node05SynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      ambient ancestor coarseGrains croppedMassFraction := by
  let receipt : PureWZ2Node05SelectedReentryReceipt regularized.core
      selectedLoss selectedNormalizationExponent :=
    PureWZ2Node05SelectedReentryReceipt.ofCriticalFloorAndScalars
      criticalFloor grainLoss_le hdeltaSmall hdeltaCutoff regularized.nearby
      densityAbsorption topLevelAbsorption normalizationLoss_le
      retainedMassAbsorption densityBudget
  exact { core := regularized.core, receipt := receipt }

/-- Re-entry-trace version of the same-witness bridge.  It consumes the
nearby-CWA proof already stored by the regularized core and preserves that
exact core through the ordinary critical-floor conversion. -/
noncomputable def toSynchronizedOwnerSelectionOfReentryTrace
    {delta sigma ambientLoss sourceLoss normalizationLoss grainLoss
      outputEta epsilon selectedLoss densityLoss structuralBudget : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent ancestorNormalizationExponent
      selectedNormalizationExponent : ℕ}
    {ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent}
    {ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      ancestorNormalizationExponent sourceLoss normalizationLoss}
    {coarseGrains : PureWZ2GrainRefinementData
      ambient.croppedCoarseShading sigma grainLoss}
    {croppedMassFraction : ENNReal}
    (criticalFloor : PureWZ2CriticalFloorSelectionData
      sigma selectedLoss structuralBudget)
    (regularized : PureWZ2Node05RegularizedPostGrainCore
      (outputEta := outputEta)
      (pureWZ2Node05AmbientCoarseIdentityRefinement ambient) ancestor
      coarseGrains croppedMassFraction
      (Kakeya.realRpowENN rhoRequested.1 (-densityLoss)) epsilon)
    (lossConstant : ENNReal)
    (lossConstantOne : 1 ≤ lossConstant)
    (lossConstantTop : lossConstant ≠ ⊤)
    (grainLoss_le_density : grainLoss ≤ densityLoss)
    (densityLoss_le : densityLoss ≤ selectedLoss)
    (hdeltaSmall : rhoRequested.1 ≤ 1 / 12)
    (hdeltaCutoff : rhoRequested.1 ≤ criticalFloor.delta₀)
    (densityAbsorption :
      (13824 : ENNReal) * Kakeya.realRpowENN rhoRequested.1 densityLoss ≤
        Kakeya.realRpowENN rhoRequested.1 outputEta)
    (topLevelAbsorption :
      ((Kakeya.realRpowENN rhoRequested.1 outputEta)⁻¹ * 1) *
          Kakeya.realRpowENN rhoRequested.1 (-grainLoss) ≤
        Kakeya.realRpowENN rhoRequested.1 (-selectedLoss))
    (traceAbsorption : lossConstant⁻¹ ≤
      (100 : ENNReal)⁻¹ *
        Kakeya.realRpowENN rhoRequested.1 outputEta)
    (cwaAbsorption :
      lossConstant * Kakeya.realRpowENN rhoRequested.1 (-densityLoss) ≤
        Kakeya.realRpowENN rhoRequested.1
          (-criticalFloor.structuralLoss))
    (criticalDensityAbsorption :
      Kakeya.realRpowENN rhoRequested.1 criticalFloor.structuralLoss ≤
        lossConstant⁻¹ * Kakeya.realRpowENN rhoRequested.1 densityLoss)
    (normalizationLoss_le : normalizationLoss ≤ selectedLoss)
    (retainedMassAbsorption :
      regularized.core.retentionLoss *
          wz2PaperPureRefinementFraction rhoRequested.1
            selectedNormalizationExponent ≤
        ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
          Kakeya.realRpowENN rhoRequested.1 grainLoss) *
            wz2PaperPureRefinementFraction rhoRequested.1
              ancestorNormalizationExponent)
    (densityBudget : Kakeya.realRpowENN rhoRequested.1 sourceLoss / 2 ≤
      Kakeya.realRpowENN rhoRequested.1 outputEta) :
    PureWZ2Node05SynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      ambient ancestor coarseGrains croppedMassFraction := by
  let receipt : PureWZ2Node05SelectedReentryReceipt regularized.core
      selectedLoss selectedNormalizationExponent :=
    PureWZ2Node05SelectedReentryReceipt.ofReentryTraceAndPureCriticalFloorAndScalars
      criticalFloor lossConstant lossConstantOne lossConstantTop
      grainLoss_le_density densityLoss_le hdeltaSmall hdeltaCutoff
      regularized.nearby densityAbsorption topLevelAbsorption traceAbsorption
      cwaAbsorption criticalDensityAbsorption normalizationLoss_le
      retainedMassAbsorption densityBudget
  exact { core := regularized.core, receipt := receipt }

end PureWZ2Node05RegularizedPostGrainCore

/-- Jointly select the post-grain family, prove nearby CWA on that exact
family, and construct the cropped-critical-floor owner source.  This is the
same-witness replacement for the older `nearby : ∀ core, ...` callback. -/
theorem exists_pureWZ2Node05SynchronizedOwnerSelection_of_regularized
    {delta sigma ambientLoss sourceLoss normalizationLoss grainLoss
      inputEta outputEta epsilon selectedLoss : ℝ}
    {ambientConstant : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent ancestorNormalizationExponent
      selectedNormalizationExponent : ℕ}
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent)
    (ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      ancestorNormalizationExponent sourceLoss normalizationLoss)
    (coarseGrains : PureWZ2GrainRefinementData
      ambient.croppedCoarseShading sigma grainLoss)
    (croppedMassFraction : ENNReal)
    (ambientNearby : WZ2PaperPureCWAAtNearbyScales
      (pureWZ2Node05AmbientCoarseIdentityRefinement ambient).selected.family
      ambientConstant)
    (hdeltaSmall : rhoRequested.1 ≤ 1 / 12)
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
    (epsilon_pos : 0 < epsilon)
    (delta_lt_one : rhoRequested.1 < 1)
    (criticalFloor : PureWZ2CroppedCriticalFloorSelectionData
      sigma selectedLoss selectedLoss)
    (roundingAbsorption :
      ENNReal.ofReal (Real.rpow rhoRequested.1 (-epsilon)) *
          ambientConstant ≤
        Kakeya.realRpowENN rhoRequested.1
          (-criticalFloor.structuralLoss))
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
        Kakeya.realRpowENN rhoRequested.1
          (-criticalFloor.structuralLoss))
    (cardinalityAbsorption :
      Kakeya.realRpowENN rhoRequested.1 outputEta *
          pureWZ2SpatialCellRegularizationLoss epsilon
            (pureWZ2Node05AmbientCoarseIdentityRefinement
              ambient).selected.family.card ≤
        Kakeya.realRpowENN rhoRequested.1 inputEta)
    (grainLoss_le : grainLoss ≤ selectedLoss)
    (hdeltaCutoff : rhoRequested.1 ≤ criticalFloor.delta₀)
    (densityAbsorption :
      (13824 : ENNReal) *
          Kakeya.realRpowENN rhoRequested.1 criticalFloor.structuralLoss ≤
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
  rcases exists_pureWZ2Node05RegularizedPostGrainCore
      (pureWZ2Node05AmbientCoarseIdentityRefinement ambient) ancestor
      coarseGrains croppedMassFraction
      (Kakeya.realRpowENN rhoRequested.1
        (-criticalFloor.structuralLoss)) ambientNearby hdeltaSmall
      densitySeparation inputDensityAbsorption croppedMassAbsorption
      epsilon_pos delta_lt_one (by simp [Kakeya.realRpowENN])
      roundingAbsorption restrictionAbsorption cardinalityAbsorption with
    ⟨regularized⟩
  apply Nonempty.intro
  apply regularized.toSynchronizedOwnerSelectionOfCriticalFloor criticalFloor
    grainLoss_le hdeltaSmall hdeltaCutoff densityAbsorption topLevelAbsorption
    normalizationLoss_le
  · simpa [regularized.retentionLoss_eq] using retainedMassAbsorption
  · exact densityBudget

/-- Joint regularization for the active ordinary-trace route.  The weighted
nearby-CWA selector chooses the core once, and the local critical-floor
conversion is then run on that exact core. -/
theorem exists_pureWZ2Node05SynchronizedOwnerSelection_of_regularized_reentryTrace
    {delta sigma ambientLoss sourceLoss normalizationLoss grainLoss
      inputEta outputEta epsilon densityLoss selectedLoss
      structuralBudget : ℝ}
    {ambientConstant : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent ancestorNormalizationExponent
      selectedNormalizationExponent : ℕ}
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent)
    (ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      ancestorNormalizationExponent sourceLoss normalizationLoss)
    (coarseGrains : PureWZ2GrainRefinementData
      ambient.croppedCoarseShading sigma grainLoss)
    (croppedMassFraction lossConstant : ENNReal)
    (ambientNearby : WZ2PaperPureCWAAtNearbyScales
      (pureWZ2Node05AmbientCoarseIdentityRefinement ambient).selected.family
      ambientConstant)
    (hdeltaSmall : rhoRequested.1 ≤ 1 / 12)
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
    (epsilon_pos : 0 < epsilon)
    (delta_lt_one : rhoRequested.1 < 1)
    (roundingAbsorption :
      ENNReal.ofReal (Real.rpow rhoRequested.1 (-epsilon)) *
          ambientConstant ≤
        Kakeya.realRpowENN rhoRequested.1 (-densityLoss))
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
        Kakeya.realRpowENN rhoRequested.1 (-densityLoss))
    (cardinalityAbsorption :
      Kakeya.realRpowENN rhoRequested.1 outputEta *
          pureWZ2SpatialCellRegularizationLoss epsilon
            (pureWZ2Node05AmbientCoarseIdentityRefinement
              ambient).selected.family.card ≤
        Kakeya.realRpowENN rhoRequested.1 inputEta)
    (criticalFloor : PureWZ2CriticalFloorSelectionData
      sigma selectedLoss structuralBudget)
    (lossConstantOne : 1 ≤ lossConstant)
    (lossConstantTop : lossConstant ≠ ⊤)
    (grainLoss_le_density : grainLoss ≤ densityLoss)
    (densityLoss_le : densityLoss ≤ selectedLoss)
    (hdeltaCutoff : rhoRequested.1 ≤ criticalFloor.delta₀)
    (densityAbsorption :
      (13824 : ENNReal) * Kakeya.realRpowENN rhoRequested.1 densityLoss ≤
        Kakeya.realRpowENN rhoRequested.1 outputEta)
    (topLevelAbsorption :
      ((Kakeya.realRpowENN rhoRequested.1 outputEta)⁻¹ * 1) *
          Kakeya.realRpowENN rhoRequested.1 (-grainLoss) ≤
        Kakeya.realRpowENN rhoRequested.1 (-selectedLoss))
    (traceAbsorption : lossConstant⁻¹ ≤
      (100 : ENNReal)⁻¹ *
        Kakeya.realRpowENN rhoRequested.1 outputEta)
    (cwaAbsorption :
      lossConstant * Kakeya.realRpowENN rhoRequested.1 (-densityLoss) ≤
        Kakeya.realRpowENN rhoRequested.1
          (-criticalFloor.structuralLoss))
    (criticalDensityAbsorption :
      Kakeya.realRpowENN rhoRequested.1 criticalFloor.structuralLoss ≤
        lossConstant⁻¹ * Kakeya.realRpowENN rhoRequested.1 densityLoss)
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
  rcases exists_pureWZ2Node05RegularizedPostGrainCore
      (pureWZ2Node05AmbientCoarseIdentityRefinement ambient) ancestor
      coarseGrains croppedMassFraction
      (Kakeya.realRpowENN rhoRequested.1 (-densityLoss)) ambientNearby
      hdeltaSmall densitySeparation inputDensityAbsorption
      croppedMassAbsorption epsilon_pos delta_lt_one
      (by simp [Kakeya.realRpowENN]) roundingAbsorption
      restrictionAbsorption cardinalityAbsorption with
    ⟨regularized⟩
  apply Nonempty.intro
  apply regularized.toSynchronizedOwnerSelectionOfReentryTrace criticalFloor
    lossConstant lossConstantOne lossConstantTop grainLoss_le_density
    densityLoss_le hdeltaSmall hdeltaCutoff densityAbsorption
    topLevelAbsorption traceAbsorption cwaAbsorption
    criticalDensityAbsorption normalizationLoss_le
  · simpa [regularized.retentionLoss_eq] using retainedMassAbsorption
  · exact densityBudget

/-- Produce the synchronized owner selection from the already proved overlap
estimate, one critical floor, and scalar absorptions.  The sole family-indexed
input is nearby CWA on the family selected by the constructed core. -/
theorem exists_pureWZ2Node05SynchronizedOwnerSelection_of_scalars
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
    (inputEta outputEta selectedLoss : ℝ)
    (selectedNormalizationExponent : ℕ)
    (croppedMassFraction : ENNReal)
    (hdeltaSmall : rhoRequested.1 ≤ 1 / 12)
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
    (criticalFloor : PureWZ2CroppedCriticalFloorSelectionData
      sigma selectedLoss selectedLoss)
    (grainLoss_le : grainLoss ≤ selectedLoss)
    (hdeltaCutoff : rhoRequested.1 ≤ criticalFloor.delta₀)
    (nearby : ∀ core : PureWZ2Node05SynchronizedPostGrainCore
      (pureWZ2Node05AmbientCoarseIdentityRefinement ambient)
      ancestor coarseGrains outputEta croppedMassFraction,
      WZ2PaperPureCWAAtNearbyScales
        (pureWZ2Node05PostGrainSelectedSubfamily
          ambient.coarse core.retained).family
        (Kakeya.realRpowENN rhoRequested.1
          (-criticalFloor.structuralLoss)))
    (densityAbsorption :
      (13824 : ENNReal) *
          Kakeya.realRpowENN rhoRequested.1 criticalFloor.structuralLoss ≤
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
  rcases exists_pureWZ2Node05SynchronizedPostGrainCore_of_scalars_with_loss_two
      (pureWZ2Node05AmbientCoarseIdentityRefinement ambient) ancestor
      coarseGrains inputEta outputEta croppedMassFraction hdeltaSmall
      densitySeparation inputDensityAbsorption croppedMassAbsorption with
    ⟨core, coreRetentionLoss⟩
  let receipt : PureWZ2Node05SelectedReentryReceipt core selectedLoss
      selectedNormalizationExponent :=
    PureWZ2Node05SelectedReentryReceipt.ofCriticalFloorAndScalars
      criticalFloor grainLoss_le hdeltaSmall hdeltaCutoff (nearby core)
      densityAbsorption topLevelAbsorption normalizationLoss_le
      (by simpa [coreRetentionLoss] using retainedMassAbsorption) densityBudget
  exact ⟨{ core := core, receipt := receipt }⟩

/-- The synchronized owner selection with its volume floor derived locally
from the ancestor re-entry trace and Node 2's ordinary critical floor.  This
keeps the exact selected family while avoiding a global cropped-model
reduction premise. -/
theorem exists_pureWZ2Node05SynchronizedOwnerSelection_of_reentryTrace
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
    (inputEta outputEta densityLoss selectedLoss structuralBudget : ℝ)
    (selectedNormalizationExponent : ℕ)
    (croppedMassFraction lossConstant : ENNReal)
    (hdeltaSmall : rhoRequested.1 ≤ 1 / 12)
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
    (criticalFloor : PureWZ2CriticalFloorSelectionData
      sigma selectedLoss structuralBudget)
    (lossConstantOne : 1 ≤ lossConstant)
    (lossConstantTop : lossConstant ≠ ⊤)
    (grainLoss_le_density : grainLoss ≤ densityLoss)
    (densityLoss_le : densityLoss ≤ selectedLoss)
    (hdeltaCutoff : rhoRequested.1 ≤ criticalFloor.delta₀)
    (nearby : ∀ core : PureWZ2Node05SynchronizedPostGrainCore
      (pureWZ2Node05AmbientCoarseIdentityRefinement ambient)
      ancestor coarseGrains outputEta croppedMassFraction,
      WZ2PaperPureCWAAtNearbyScales
        (pureWZ2Node05PostGrainSelectedSubfamily
          ambient.coarse core.retained).family
        (Kakeya.realRpowENN rhoRequested.1 (-densityLoss)))
    (densityAbsorption :
      (13824 : ENNReal) *
          Kakeya.realRpowENN rhoRequested.1 densityLoss ≤
        Kakeya.realRpowENN rhoRequested.1 outputEta)
    (topLevelAbsorption :
      ((Kakeya.realRpowENN rhoRequested.1 outputEta)⁻¹ * 1) *
          Kakeya.realRpowENN rhoRequested.1 (-grainLoss) ≤
        Kakeya.realRpowENN rhoRequested.1 (-selectedLoss))
    (traceAbsorption : lossConstant⁻¹ ≤
      (100 : ENNReal)⁻¹ *
        Kakeya.realRpowENN rhoRequested.1 outputEta)
    (cwaAbsorption :
      lossConstant * Kakeya.realRpowENN rhoRequested.1 (-densityLoss) ≤
        Kakeya.realRpowENN rhoRequested.1
          (-criticalFloor.structuralLoss))
    (criticalDensityAbsorption :
      Kakeya.realRpowENN rhoRequested.1 criticalFloor.structuralLoss ≤
        lossConstant⁻¹ *
          Kakeya.realRpowENN rhoRequested.1 densityLoss)
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
  rcases exists_pureWZ2Node05SynchronizedPostGrainCore_of_scalars_with_loss_two
      (pureWZ2Node05AmbientCoarseIdentityRefinement ambient) ancestor
      coarseGrains inputEta outputEta croppedMassFraction hdeltaSmall
      densitySeparation inputDensityAbsorption croppedMassAbsorption with
    ⟨core, coreRetentionLoss⟩
  let receipt : PureWZ2Node05SelectedReentryReceipt core selectedLoss
      selectedNormalizationExponent :=
    PureWZ2Node05SelectedReentryReceipt.ofReentryTraceAndPureCriticalFloorAndScalars
        criticalFloor lossConstant lossConstantOne lossConstantTop
        grainLoss_le_density densityLoss_le hdeltaSmall hdeltaCutoff
        (nearby core) densityAbsorption topLevelAbsorption traceAbsorption
        cwaAbsorption criticalDensityAbsorption normalizationLoss_le
        (by simpa [coreRetentionLoss] using retainedMassAbsorption)
        densityBudget
  exact ⟨{ core := core, receipt := receipt }⟩

namespace PureWZ2Node05SynchronizedOwnerSelection

variable
    {delta sigma ambientLoss sourceLoss normalizationLoss grainLoss
      outputEta selectedLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent ancestorNormalizationExponent
      selectedNormalizationExponent : ℕ}
    {ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent}
    {ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      ancestorNormalizationExponent sourceLoss normalizationLoss}
    {coarseGrains : PureWZ2GrainRefinementData
      ambient.croppedCoarseShading sigma grainLoss}
    {croppedMassFraction : ENNReal}
    (selection : PureWZ2Node05SynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      ambient ancestor coarseGrains croppedMassFraction)

/-- The one coarse subfamily selected by synchronized post-grain pruning. -/
noncomputable abbrev selectedCoarse :
    Kakeya.Streamlined.TubeSubfamily ambient.coarse :=
  pureWZ2Node05PostGrainSelectedSubfamily
    ambient.coarse selection.core.retained

/-- The literal selected post-grain coarse shading. -/
noncomputable abbrev overlay :
    WZ1PaperTubeShading selection.selectedCoarse.family :=
  restrictPaperShading selection.selectedCoarse coarseGrains.shading

/-- The selected grain configuration at the honest selected loss. -/
noncomputable abbrev selectedGrains :
    PureWZ2GrainConfiguration sigma selectedLoss rhoRequested.1 :=
  selection.receipt.toGrainConfiguration

/-- The selected exact ordinary/cropped re-entry, indexed by the same
retained coarse family and shading as `selectedGrains`. -/
noncomputable abbrev selectedReentry :
    PureWZ2PropStickyReentryData
      (sigma := sigma) selection.overlay selectedNormalizationExponent
      sourceLoss selectedLoss :=
  selection.receipt.toReentryData

/-- Canonically retain every ambient fine tube in the complete fibers of the
synchronized coarse parents. -/
noncomputable def pullback :
    PureWZ2Node05CompleteParentPullbackData
      ambient.cover ambient.refined ambient.croppedCoarseShading
      selection.selectedCoarse :=
  Classical.choice <| exists_pureWZ2Node05CompleteParentPullbackData
    ambient.cover ambient.refined ambient.croppedCoarseShading
    ambient.data.balanced selection.selectedCoarse
    selection.receipt.extremal.nonempty

/-- The selected post-grain shading is an honest subshading of the ambient
selected coarse shading produced by `pullback`. -/
theorem overlay_subshading :
    PureWZ2PaperIsSubshading selection.overlay
      selection.pullback.selectedCoarseShading := by
  intro index point hpoint
  rw [selection.pullback.selectedCoarseShading_eq]
  exact coarseGrains.subshading
    (selection.selectedCoarse.embedding index) hpoint

/-- The complete-parent fine shading after intersection with the exact
selected post-grain union. -/
noncomputable abbrev overlayFine :
    WZ1PaperTubeShading selection.pullback.selectedFine.family :=
  pureWZ2Node05CompleteParentOverlayFineShading
    selection.pullback selection.overlay

/-- The core's retained-cardinality estimate upgrades a scalar comparison of
the power factors to the coarse multiplicity absorption required by the
selected-family public output. -/
theorem coarse_cardinality_absorption_of_scalar
    (ambientPowerAbsorption :
      Kakeya.realRpowENN rhoRequested.1
          (2 - sigma - ambientLoss) ≤
        Kakeya.realRpowENN rhoRequested.1
            (2 - sigma - selectedLoss) *
          Kakeya.realRpowENN rhoRequested.1 outputEta) :
    Kakeya.realRpowENN rhoRequested.1 (2 - sigma - ambientLoss) *
        ambient.coarse.enncard ≤
      Kakeya.realRpowENN rhoRequested.1 (2 - sigma - selectedLoss) *
        selection.selectedCoarse.family.enncard := by
  calc
    Kakeya.realRpowENN rhoRequested.1 (2 - sigma - ambientLoss) *
          ambient.coarse.enncard ≤
        (Kakeya.realRpowENN rhoRequested.1
            (2 - sigma - selectedLoss) *
          Kakeya.realRpowENN rhoRequested.1 outputEta) *
            ambient.coarse.enncard := by gcongr
    _ = Kakeya.realRpowENN rhoRequested.1
          (2 - sigma - selectedLoss) *
        (Kakeya.realRpowENN rhoRequested.1 outputEta *
          ambient.coarse.enncard) := by ring
    _ ≤ Kakeya.realRpowENN rhoRequested.1
          (2 - sigma - selectedLoss) *
        selection.selectedCoarse.family.enncard := by
      exact mul_le_mul_left' selection.core.cardinality_retention _

/-- Unique coarse ownership and ambient exact multiplicity close the complete
structural Node-5 balanced receipt on the synchronized overlay. -/
noncomputable def overlayNode5Balanced
    (coarseMultiplicityOne : ∀ point,
      (ambient.croppedCoarseShading.pointMultiplicity point : ENNReal) ≤ 1)
    (m : ℕ) (hm : 0 < m)
    (ambientExact : ambient.refined.HasConstantMultiplicity m m) :
    PureWZ2Node5BalancedCoverData
      (selection.pullback.toOverlayBalanced selection.overlay
        ambient.data.balanced coarseMultiplicityOne
        selection.overlay_subshading selection.receipt.extremal.cubical
        ambient.coarse_extremal.delta_pos) :=
  selection.pullback.toOverlayNode5BalancedOfExactMultiplicity
    selection.overlay ambient.balanced coarseMultiplicityOne
    selection.overlay_subshading ambient.refined_cubical
    selection.receipt.extremal.cubical ambient.coarse_extremal.delta_pos
    m hm ambientExact

end PureWZ2Node05SynchronizedOwnerSelection

/-- Compatibility ABI for the already developed anchored CommonBin modules.
It is not the production selection producer below: compatibility callers must
supply an anchored source explicitly. -/
structure PureWZ2Node05AnchoredSynchronizedOwnerSelection
    {delta sigma ambientLoss grainLoss outputEta selectedLoss sourceLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent selectedNormalizationExponent : ℕ}
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent)
    (anchored : PureWZ2Node05AnchoredCoarseSource
      (grainLoss := grainLoss) ambient) where
  retained : Finset (Fin ambient.coarse.card)
  retained_nonempty : retained.Nonempty
  cardinality_retention :
    Kakeya.realRpowENN rhoRequested.1 outputEta * ambient.coarse.enncard ≤
      (pureWZ2Node05PostGrainSelectedSubfamily
        ambient.coarse retained).family.enncard
  selectedReentry : PureWZ2PropStickyReentryData
    (sigma := sigma)
    (restrictPaperShading
      (pureWZ2Node05PostGrainSelectedSubfamily ambient.coarse retained)
      anchored.shading)
    selectedNormalizationExponent sourceLoss selectedLoss

namespace PureWZ2Node05AnchoredSynchronizedOwnerSelection

variable
    {delta sigma ambientLoss grainLoss outputEta selectedLoss sourceLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent selectedNormalizationExponent : ℕ}
    {ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent}
    {anchored : PureWZ2Node05AnchoredCoarseSource
      (grainLoss := grainLoss) ambient}
    (selection : PureWZ2Node05AnchoredSynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (sourceLoss := sourceLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      ambient anchored)

noncomputable abbrev selectedCoarse :
    Kakeya.Streamlined.TubeSubfamily ambient.coarse :=
  pureWZ2Node05PostGrainSelectedSubfamily ambient.coarse selection.retained

noncomputable abbrev overlay :
    WZ1PaperTubeShading selection.selectedCoarse.family :=
  restrictPaperShading selection.selectedCoarse anchored.shading

noncomputable def pullback :
    PureWZ2Node05CompleteParentPullbackData
      ambient.cover ambient.refined ambient.croppedCoarseShading
      selection.selectedCoarse :=
  Classical.choice <| exists_pureWZ2Node05CompleteParentPullbackData
    ambient.cover ambient.refined ambient.croppedCoarseShading
    ambient.data.balanced selection.selectedCoarse
    selection.selectedReentry.cropped_extremal.nonempty

theorem overlay_subshading :
    PureWZ2PaperIsSubshading selection.overlay
      selection.pullback.selectedCoarseShading := by
  intro index point hpoint
  rw [selection.pullback.selectedCoarseShading_eq]
  exact anchored.subshading (selection.selectedCoarse.embedding index) hpoint

end PureWZ2Node05AnchoredSynchronizedOwnerSelection

/-- All numerical choices for the anchored selection and the second owner
call.  A leaf accepts this record and its admissibility proof before either
owner input or call is produced. -/
structure PureWZ2Node05AnchoredSelectionSchedule where
  inputEta : ℝ
  outputEta : ℝ
  selectedLoss : ℝ
  firstOutputLoss : ℝ
  firstSeedLoss : ℝ
  firstStructuralBudget : ℝ
  firstSourceFineLoss : ℝ
  firstSeedLogExponent : ℕ
  firstFineExponent : ℕ
  firstOutputLogExponent : ℕ
  reentrySourceLoss : ℝ
  reentryNormalizationLoss : ℝ
  ancestorNormalizationExponent : ℕ
  structuralBudget : ℝ
  epsilon : ℝ
  seedLoss : ℝ
  sourceFineLoss : ℝ
  secondOutputLoss : ℝ
  selectedNormalizationExponent : ℕ
  secondSeedLogExponent : ℕ
  secondFineExponent : ℕ
  outputLogExponent : ℕ
  delta₀ : ℝ
  rho₀ : ℝ

namespace PureWZ2Node05AnchoredSelectionSchedule

/-- Family-independent numerical validity of an anchored two-call schedule.

This record contains no family, shading, selected core, CWA witness, critical
floor, universal input, or owner call.  Scale-dependent inequalities are
uniform below the stored cutoffs and hence are fixed before runtime. -/
structure IsAdmissible
    (schedule : PureWZ2Node05AnchoredSelectionSchedule) : Prop where
  inputEta_pos : 0 < schedule.inputEta
  outputEta_pos : 0 < schedule.outputEta
  inputEta_lt_outputEta : schedule.inputEta < schedule.outputEta
  outputEta_lt_selectedLoss : schedule.outputEta < schedule.selectedLoss
  selectedLoss_pos : 0 < schedule.selectedLoss
  firstOutputLoss_pos : 0 < schedule.firstOutputLoss
  firstOutputLoss_le_inputEta :
    schedule.firstOutputLoss ≤ schedule.inputEta
  firstOutputLoss_le_selectedLoss :
    schedule.firstOutputLoss ≤ schedule.selectedLoss
  firstSeedLoss_pos : 0 < schedule.firstSeedLoss
  firstSeedLoss_le_output :
    schedule.firstSeedLoss ≤ schedule.firstOutputLoss
  firstStructuralBudget_pos : 0 < schedule.firstStructuralBudget
  firstStructuralBudget_le_output :
    schedule.firstStructuralBudget ≤ schedule.firstOutputLoss
  firstSourceFineLoss_pos : 0 < schedule.firstSourceFineLoss
  firstSourceFineLoss_lt_budget :
    schedule.firstSourceFineLoss < schedule.firstStructuralBudget
  reentrySourceLoss_pos : 0 < schedule.reentrySourceLoss
  reentryNormalizationLoss_pos : 0 < schedule.reentryNormalizationLoss
  reentrySourceLoss_le_half :
    schedule.reentrySourceLoss ≤ schedule.reentryNormalizationLoss / 2
  reentryNormalizationLoss_le_selected :
    schedule.reentryNormalizationLoss ≤ schedule.selectedLoss
  epsilon_pos : 0 < schedule.epsilon
  structuralBudget_pos : 0 < schedule.structuralBudget
  structuralBudget_le_output :
    schedule.structuralBudget ≤ schedule.secondOutputLoss
  seedLoss_pos : 0 < schedule.seedLoss
  seedLoss_le_output : schedule.seedLoss ≤ schedule.secondOutputLoss
  sourceFineLoss_pos : 0 < schedule.sourceFineLoss
  sourceFineLoss_lt_budget :
    schedule.sourceFineLoss < schedule.structuralBudget
  secondOutputLoss_pos : 0 < schedule.secondOutputLoss
  firstFineExponent_pos : 0 < schedule.firstFineExponent
  firstLogSplit :
    schedule.firstSeedLogExponent + schedule.firstFineExponent =
      schedule.firstOutputLogExponent
  secondFineExponent_pos : 0 < schedule.secondFineExponent
  secondLogSplit :
    schedule.secondSeedLogExponent + schedule.secondFineExponent =
      schedule.outputLogExponent
  delta₀_pos : 0 < schedule.delta₀
  delta₀_le_one : schedule.delta₀ ≤ 1
  rho₀_pos : 0 < schedule.rho₀
  rho₀_le_one : schedule.rho₀ ≤ 1
  selectionSeparation :
    ∀ rho : ℝ, 0 < rho → rho ≤ schedule.rho₀ →
      Kakeya.realRpowENN rho schedule.outputEta ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN rho schedule.inputEta
  selectedDensityAbsorption :
    ∀ rho : ℝ, 0 < rho → rho ≤ schedule.rho₀ →
      (13824 : ENNReal) *
          Kakeya.realRpowENN rho schedule.selectedLoss ≤
        Kakeya.realRpowENN rho schedule.outputEta
  selectedTopLevelAbsorption :
    ∀ rho : ℝ, 0 < rho → rho ≤ schedule.rho₀ →
      (Kakeya.realRpowENN rho schedule.outputEta)⁻¹ *
          Kakeya.realRpowENN rho (-schedule.firstOutputLoss) ≤
        Kakeya.realRpowENN rho (-schedule.selectedLoss)
  selectedDensityBudget :
    ∀ rho : ℝ, 0 < rho → rho ≤ schedule.rho₀ →
      Kakeya.realRpowENN rho schedule.reentrySourceLoss / 2 ≤
        Kakeya.realRpowENN rho schedule.outputEta
  selectedNormalizationRetention :
    ∀ rho : ℝ, 0 < rho → rho ≤ schedule.rho₀ →
      2 * wz2PaperPureRefinementFraction rho
          schedule.selectedNormalizationExponent ≤
        wz2PaperPureRefinementFraction rho
          schedule.ancestorNormalizationExponent
  firstRefinementScalar :
    ∀ delta : ℝ, 0 < delta → delta ≤ schedule.delta₀ →
      2 * wz1PaperRefinementFraction delta schedule.firstFineExponent ≤ 1
  secondRefinementScalar :
    ∀ rho : ℝ, 0 < rho → rho ≤ schedule.rho₀ →
      2 * wz1PaperRefinementFraction rho schedule.secondFineExponent ≤ 1

/-- Runtime scales certified against a pre-runtime admissible schedule.
This remains purely scalar and contains no mathematical output witness. -/
structure RuntimeAdmissible
    (schedule : PureWZ2Node05AnchoredSelectionSchedule)
    (delta rho sqrtRho : ℝ) : Prop where
  delta_pos : 0 < delta
  delta_le_cutoff : delta ≤ schedule.delta₀
  rho_pos : 0 < rho
  rho_le_cutoff : rho ≤ schedule.rho₀
  delta_le_rho : delta ≤ rho
  sqrt_eq : sqrtRho = Real.sqrt rho
  firstRatioSmall : delta / rho ≤ 1 / 24
  secondRatioSmall : rho / sqrtRho ≤ 1 / 24

end PureWZ2Node05AnchoredSelectionSchedule

/-- First unresolved runtime geometric leaf for direct anchored selection.

It asks for the aggregate mass of the *literal* affine-ordinary/cropped
overlap already defined by the frozen re-entry API.  This is a conclusion to
be produced from the paper geometry, not an admissibility hypothesis. -/
def PureWZ2Node05PreScheduledAnchoredOverlapLowerLeafAt
    {delta sigma : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    (schedule : PureWZ2Node05AnchoredSelectionSchedule)
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := schedule.firstOutputLoss)
      sourceShading rhoRequested schedule.firstOutputLogExponent)
    (ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      schedule.ancestorNormalizationExponent schedule.reentrySourceLoss
      schedule.reentryNormalizationLoss) : Prop :=
  max
      (max
        (Kakeya.realRpowENN rhoRequested.1 schedule.inputEta *
          ambient.coarse.toBodyFamily.mass)
        (2 * wz2PaperPureRefinementFraction rhoRequested.1
            schedule.selectedNormalizationExponent *
          ancestor.ordinarySource.shading.mass))
      (wz2PaperPureRefinementFraction rhoRequested.1
          schedule.selectedNormalizationExponent *
        ambient.croppedCoarseShading.mass) ≤
    ancestor.toNormalizationData.literalOverlapShading.mass

/-- Once the genuine overlap lower bound is produced, the existing closed
indexed-pruning theorem gives one core carrying cardinality, overlap mass,
cropped shading mass, and per-tube ordinary density on the same finset. -/
theorem
    exists_pureWZ2Node05PreScheduledAnchoredSynchronizedPerTubeCore_of_overlap
    {delta sigma : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    (schedule : PureWZ2Node05AnchoredSelectionSchedule)
    (admissible : schedule.IsAdmissible)
    (runtime : schedule.RuntimeAdmissible
      delta rhoRequested.1 (Real.sqrt rhoRequested.1))
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := schedule.firstOutputLoss)
      sourceShading rhoRequested schedule.firstOutputLogExponent)
    (ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      schedule.ancestorNormalizationExponent schedule.reentrySourceLoss
      schedule.reentryNormalizationLoss)
    (overlap :
      PureWZ2Node05PreScheduledAnchoredOverlapLowerLeafAt
        schedule ambient ancestor) :
    Nonempty
      (PureWZ2CroppedCriticalNormalizationData.NormalizationSynchronizedPerTubeCore
        ancestor.toNormalizationData schedule.outputEta
        (wz2PaperPureRefinementFraction rhoRequested.1
          schedule.selectedNormalizationExponent)) := by
  apply ancestor.toNormalizationData
    |>.exists_normalizationSynchronizedPerTubeCore
      schedule.inputEta schedule.outputEta
      (wz2PaperPureRefinementFraction rhoRequested.1
        schedule.selectedNormalizationExponent)
      (admissible.selectionSeparation rhoRequested.1 runtime.rho_pos
        runtime.rho_le_cutoff)
  calc
    max
          (Kakeya.realRpowENN rhoRequested.1 schedule.inputEta *
            ambient.coarse.toBodyFamily.mass)
          (wz2PaperPureRefinementFraction rhoRequested.1
            schedule.selectedNormalizationExponent *
            ambient.croppedCoarseShading.mass) ≤
        max
          (max
            (Kakeya.realRpowENN rhoRequested.1 schedule.inputEta *
              ambient.coarse.toBodyFamily.mass)
            (2 * wz2PaperPureRefinementFraction rhoRequested.1
              schedule.selectedNormalizationExponent *
              ancestor.ordinarySource.shading.mass))
          (wz2PaperPureRefinementFraction rhoRequested.1
            schedule.selectedNormalizationExponent *
            ambient.croppedCoarseShading.mass) := by
              gcongr
              exact le_max_left _ _
    _ ≤ ancestor.toNormalizationData.literalOverlapShading.mass := overlap

/-- The same pruned overlap core retains exactly the ordinary source mass
needed by the selected normalization exponent. -/
theorem pureWZ2Node05PreScheduledAnchoredCore_ordinary_retained_mass
    {delta sigma : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    (schedule : PureWZ2Node05AnchoredSelectionSchedule)
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := schedule.firstOutputLoss)
      sourceShading rhoRequested schedule.firstOutputLogExponent)
    (ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      schedule.ancestorNormalizationExponent schedule.reentrySourceLoss
      schedule.reentryNormalizationLoss)
    (overlap :
      PureWZ2Node05PreScheduledAnchoredOverlapLowerLeafAt
        schedule ambient ancestor)
    (core :
      PureWZ2CroppedCriticalNormalizationData.NormalizationSynchronizedPerTubeCore
        ancestor.toNormalizationData schedule.outputEta
        (wz2PaperPureRefinementFraction rhoRequested.1
          schedule.selectedNormalizationExponent)) :
    wz2PaperPureRefinementFraction rhoRequested.1
          schedule.selectedNormalizationExponent *
        ancestor.ordinarySource.shading.mass ≤
      (ancestor.toNormalizationData.synchronizedOverlapShading
        core.retained).mass := by
  rw [← ENNReal.mul_le_mul_iff_left
    (c := (2 : ENNReal)) (by norm_num) (by norm_num)]
  calc
    wz2PaperPureRefinementFraction rhoRequested.1
          schedule.selectedNormalizationExponent *
        ancestor.ordinarySource.shading.mass * 2 =
      2 * wz2PaperPureRefinementFraction rhoRequested.1
          schedule.selectedNormalizationExponent *
        ancestor.ordinarySource.shading.mass := by ring
    _ ≤
      max
        (max
          (Kakeya.realRpowENN rhoRequested.1 schedule.inputEta *
            ambient.coarse.toBodyFamily.mass)
          (2 * wz2PaperPureRefinementFraction rhoRequested.1
            schedule.selectedNormalizationExponent *
            ancestor.ordinarySource.shading.mass))
        (wz2PaperPureRefinementFraction rhoRequested.1
          schedule.selectedNormalizationExponent *
          ambient.croppedCoarseShading.mass) := by
            exact
              (le_max_right
                  (Kakeya.realRpowENN rhoRequested.1 schedule.inputEta *
                    ambient.coarse.toBodyFamily.mass)
                  (2 * wz2PaperPureRefinementFraction rhoRequested.1
                    schedule.selectedNormalizationExponent *
                    ancestor.ordinarySource.shading.mass)).trans
                (le_max_left _ _)
    _ ≤ ancestor.toNormalizationData.literalOverlapShading.mass := overlap
    _ ≤ 2 * (ancestor.toNormalizationData.synchronizedOverlapShading
          core.retained).mass := core.overlap_mass_retention
    _ = (ancestor.toNormalizationData.synchronizedOverlapShading
          core.retained).mass * 2 := by ring

/-- Synchronized selected owner source on the paper-faithful anchored ABI.

The structural coarse source is definitionally the first owner output
`ambient.croppedCoarseShading`.  There is no reconstructed coarse shading and
no coarse grain loss.  The selected re-entry is required to keep the first
owner's ordinary extremizer and rigid frame, so it cannot be an independent
existential witness. -/
structure PureWZ2Node05PreScheduledAnchoredSynchronizedOwnerSelection
    {delta sigma : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    (schedule : PureWZ2Node05AnchoredSelectionSchedule)
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := schedule.firstOutputLoss)
      sourceShading rhoRequested schedule.firstOutputLogExponent)
    (ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      schedule.ancestorNormalizationExponent schedule.reentrySourceLoss
      schedule.reentryNormalizationLoss) where
  retained : Finset (Fin ambient.coarse.card)
  retained_nonempty : retained.Nonempty
  cardinality_retention :
    Kakeya.realRpowENN rhoRequested.1 schedule.outputEta *
        ambient.coarse.enncard ≤
      (pureWZ2Node05PostGrainSelectedSubfamily
        ambient.coarse retained).family.enncard
  selectedReentry : PureWZ2PropStickyReentryData
    (sigma := sigma)
    (restrictPaperShading
      (pureWZ2Node05PostGrainSelectedSubfamily ambient.coarse retained)
      ambient.croppedCoarseShading)
    schedule.selectedNormalizationExponent schedule.reentrySourceLoss
      schedule.selectedLoss
  ordinarySource_eq :
    selectedReentry.ordinarySource = ancestor.ordinarySource
  frame_eq : selectedReentry.geometry.frame = ancestor.geometry.frame

namespace PureWZ2Node05PreScheduledAnchoredSynchronizedOwnerSelection

variable
    {delta sigma : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {schedule : PureWZ2Node05AnchoredSelectionSchedule}
    {ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := schedule.firstOutputLoss)
      sourceShading rhoRequested schedule.firstOutputLogExponent}
    {ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      schedule.ancestorNormalizationExponent schedule.reentrySourceLoss
      schedule.reentryNormalizationLoss}
    (selection : PureWZ2Node05PreScheduledAnchoredSynchronizedOwnerSelection
      schedule ambient ancestor)

noncomputable abbrev selectedCoarse :
    Kakeya.Streamlined.TubeSubfamily ambient.coarse :=
  pureWZ2Node05PostGrainSelectedSubfamily ambient.coarse selection.retained

noncomputable abbrev overlay :
    WZ1PaperTubeShading selection.selectedCoarse.family :=
  restrictPaperShading selection.selectedCoarse
    ambient.croppedCoarseShading

/-- The production structural source is the literal first-owner coarse
shading. -/
noncomputable def structuralShading
    (_selection : PureWZ2Node05PreScheduledAnchoredSynchronizedOwnerSelection
      schedule ambient ancestor) :
    WZ1PaperTubeShading ambient.coarse :=
  ambient.croppedCoarseShading

@[simp]
theorem structuralShading_eq :
    selection.structuralShading = ambient.croppedCoarseShading :=
  rfl

/-- Structural extremality is inherited from the first Proposition-6.2 call,
not reconstructed from occupied source anchors. -/
theorem structural_extremal :
    WZ2PaperCroppedIsExtremal sigma schedule.firstOutputLoss ambient.coarse
      ambient.croppedCoarseShading :=
  ambient.coarse_extremal

/-- Complete-parent provenance depends only on the selected family and ambient
balanced cover, not on global/local coarse grains. -/
noncomputable def pullback :
    PureWZ2Node05CompleteParentPullbackData
      ambient.cover ambient.refined ambient.croppedCoarseShading
      selection.selectedCoarse :=
  Classical.choice <| exists_pureWZ2Node05CompleteParentPullbackData
    ambient.cover ambient.refined ambient.croppedCoarseShading
    ambient.data.balanced selection.selectedCoarse
    selection.selectedReentry.cropped_extremal.nonempty

theorem overlay_subshading :
    PureWZ2PaperIsSubshading selection.overlay
      selection.pullback.selectedCoarseShading := by
  intro index point hpoint
  rw [selection.pullback.selectedCoarseShading_eq]
  exact hpoint

end PureWZ2Node05PreScheduledAnchoredSynchronizedOwnerSelection

/-- Minimal fixed-schedule/runtime leaf for the direct anchored selection.

The schedule and its family-independent admissibility are explicit inputs.
Closed combinatorics
(`pure_wz2_indexed_per_tube_pruning`) constructs the retained finite core;
the remaining non-hereditary obligation is the exact selected re-entry, whose
nearby CWA and volume floor must be rebuilt on that same core. -/
def PureWZ2Node05PreScheduledAnchoredSynchronizedSelectionLeafAt
    {delta sigma : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    (schedule : PureWZ2Node05AnchoredSelectionSchedule)
    (_admissible : schedule.IsAdmissible)
    (_runtime : schedule.RuntimeAdmissible
      delta rhoRequested.1 (Real.sqrt rhoRequested.1))
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := schedule.firstOutputLoss)
      sourceShading rhoRequested schedule.firstOutputLogExponent)
    (ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      schedule.ancestorNormalizationExponent schedule.reentrySourceLoss
      schedule.reentryNormalizationLoss) : Prop :=
  Nonempty
    (PureWZ2Node05PreScheduledAnchoredSynchronizedOwnerSelection
      schedule ambient ancestor)

/-- Quantitative receipts remaining after the synchronized selection has
already fixed all families, shadings, and complete-parent provenance. -/
structure PureWZ2Node05SynchronizedOverlayQuantitativeReceipt
    {delta sigma ambientLoss sourceLoss normalizationLoss grainLoss outputEta
      selectedLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent ancestorNormalizationExponent
      selectedNormalizationExponent : ℕ}
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent)
    (ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      ancestorNormalizationExponent sourceLoss normalizationLoss)
    (coarseGrains : PureWZ2GrainRefinementData
      ambient.croppedCoarseShading sigma grainLoss)
    (croppedMassFraction : ENNReal)
    (selection : PureWZ2Node05SynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      ambient ancestor coarseGrains croppedMassFraction)
    (outputLogExponent : ℕ) where
  ambientCoarseMultiplicityOne : ∀ point,
    (ambient.croppedCoarseShading.pointMultiplicity point : ENNReal) ≤ 1
  exactMultiplicity : ℕ
  exactMultiplicity_pos : 0 < exactMultiplicity
  ambientExactMultiplicity :
    ambient.refined.HasConstantMultiplicity
      exactMultiplicity exactMultiplicity
  fineRefinementExponent : ℕ
  fineRefinement :
    WZ1PaperRefinement ambient.seed.data.refined fineRefinementExponent
  coarseRefinementExponent : ℕ
  coarseRefinement : WZ1PaperRefinement
    ambient.seed.data.croppedCoarseShading coarseRefinementExponent
  logExponent_eq :
    outputLogExponent = ambient.seedLogExponent + fineRefinementExponent
  selected_eq :
    ambient.selected.comp selection.pullback.selectedFine =
      ambient.seed.data.selected.comp fineRefinement.selected
  refined_eq : HEq selection.overlayFine fineRefinement.refined
  coarse_eq :
    selection.selectedCoarse.family = coarseRefinement.selected.family
  croppedCoarseShading_eq : HEq selection.overlay coarseRefinement.refined
  retained_mass :
    wz2PaperPureRefinementFraction delta outputLogExponent *
        sourceShading.mass ≤ selection.overlayFine.mass
  refined_extremal : WZ2PaperCroppedIsExtremal sigma selectedLoss
    selection.pullback.selectedFine.family selection.overlayFine
  refined_volume_lower :
    Kakeya.realRpowENN delta (sigma + selectedLoss) ≤
      volume selection.overlayFine.union
  rescaledFiber :
    ∀ parent : Fin selection.selectedCoarse.family.card,
      Nonempty
        (WZ2PaperPureRescaledFullFiberOutput
          (sigma := sigma) (loss := selectedLoss)
          (restrictPaperShading
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              selection.pullback.selectedFine.family
              (wz2PaperFullFiberIndices
                selection.pullback.selectedFine.family
                selection.selectedCoarse.family parent))
            selection.overlayFine)
          (selection.selectedCoarse.family.tube parent)
          selection.receipt.extremal.delta_pos)
  ambientLoss_le : ambientLoss ≤ selectedLoss
  ambientPowerAbsorption :
    Kakeya.realRpowENN rhoRequested.1
        (2 - sigma - ambientLoss) ≤
      Kakeya.realRpowENN rhoRequested.1
          (2 - sigma - selectedLoss) *
        Kakeya.realRpowENN rhoRequested.1 outputEta

namespace PureWZ2Node05SynchronizedOverlayQuantitativeReceipt

open MeasureTheory

variable
    {delta sigma ambientLoss sourceLoss normalizationLoss grainLoss outputEta
      selectedLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent outputLogExponent ancestorNormalizationExponent
      selectedNormalizationExponent : ℕ}
    {ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent}
    {ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      ancestorNormalizationExponent sourceLoss normalizationLoss}
    {coarseGrains : PureWZ2GrainRefinementData
      ambient.croppedCoarseShading sigma grainLoss}
    {croppedMassFraction : ENNReal}
    {selection : PureWZ2Node05SynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      ambient ancestor coarseGrains croppedMassFraction}

/-- Convert the specialized synchronized ledger to the generic overlay
repackaging receipt. -/
noncomputable def toOverlayReceipt
    (receipt : PureWZ2Node05SynchronizedOverlayQuantitativeReceipt
      ambient ancestor coarseGrains croppedMassFraction selection
      outputLogExponent) :
    PureWZ2Node05CompleteParentOverlayReceipt
      (outputLoss := selectedLoss) ambient selection.selectedCoarse
      selection.pullback selection.overlay outputLogExponent where
  overlaySubshading := selection.overlay_subshading
  overlayCubical := selection.receipt.extremal.cubical
  ambientCoarseMultiplicityOne := receipt.ambientCoarseMultiplicityOne
  exactMultiplicity := receipt.exactMultiplicity
  exactMultiplicity_pos := receipt.exactMultiplicity_pos
  ambientExactMultiplicity := receipt.ambientExactMultiplicity
  fineRefinementExponent := receipt.fineRefinementExponent
  fineRefinement := receipt.fineRefinement
  coarseRefinementExponent := receipt.coarseRefinementExponent
  coarseRefinement := receipt.coarseRefinement
  logExponent_eq := receipt.logExponent_eq
  selected_eq := receipt.selected_eq
  refined_eq := receipt.refined_eq
  coarse_eq := receipt.coarse_eq
  croppedCoarseShading_eq := receipt.croppedCoarseShading_eq
  retained_mass := receipt.retained_mass
  refined_extremal := receipt.refined_extremal
  refined_volume_lower := receipt.refined_volume_lower
  coarse_extremal := selection.receipt.extremal
  rescaledFiber := receipt.rescaledFiber
  ambientLoss_le := receipt.ambientLoss_le
  coarse_cardinality_absorption :=
    selection.coarse_cardinality_absorption_of_scalar
      receipt.ambientPowerAbsorption
  coarse_volume_lower := selection.receipt.volume_lower

end PureWZ2Node05SynchronizedOverlayQuantitativeReceipt

end Kakeya.Assouad

end
