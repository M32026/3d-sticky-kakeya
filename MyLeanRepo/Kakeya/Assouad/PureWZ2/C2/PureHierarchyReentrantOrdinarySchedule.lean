import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantOrdinaryProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyNearbyCWASchedule

/-!
# Scheduled inputs for the re-entrant ordinary hierarchy producer

The ordinary hierarchy transition has one closed scalar schedule, supplied by
`PureWZ2CriticalPackage.reentryTraceFloorSchedule`.  This module separates the
remaining inputs into:

* one record containing the actual dependent family-valued constructions; and
* one record containing the runtime scalar compatibility with the selected
  trace-floor schedule.

The selected-family nearby-CWA transfer is produced internally by synchronized
weighted regularization.  Its finite losses are discharged by a cutoff chosen
before the runtime family.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The actual dependent constructions which are not selected by a scalar
schedule.  The owner calls remain on one exact two-call chain, and the
ordinary all-bin output is indexed by that chain. -/
structure PureWZ2HierarchyReentrantOrdinaryFamilyInputs
    {sigma inputLoss delta grainLoss stickyRho outputLoss outputEta
      structuralBudget inputEta : ℝ}
    {normalizationExponent logExponent : ℕ}
    (current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent)
    (middleLoss stickyLoss : ℝ)
    (croppedMassFraction : ENNReal)
    (schedule : PureWZ2ReentryTraceFloorSchedule
      sigma outputLoss structuralBudget) where
  twoScale : PureWZ2OneScaleTwoScaleStickyData
    current.grain stickyRho middleLoss stickyLoss logExponent
  ordinaryAllBins :
    ∀ pullback : PureWZ2TwoScaleCellPullbackData twoScale,
      ∀ _prepared : PureWZ2SourceCarrierPreparation pullback,
        Nonempty (PureWZ2LocallyLinearOneScaleData current.grain grainLoss
          (pureWZ2SourceHorizontalFinalScale stickyRho))

/-- Runtime scalar compatibility with one already selected trace-floor
schedule.  Keeping these inequalities in one dependent receipt prevents a
caller from combining scalar witnesses selected for different owner data. -/
structure PureWZ2HierarchyReentrantOrdinaryScalarReceipt
    {sigma inputLoss delta grainLoss outputLoss outputEta structuralBudget
      inputEta : ℝ}
    {normalizationExponent : ℕ}
    (current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent)
    (croppedMassFraction : ENNReal)
    (schedule : PureWZ2ReentryTraceFloorSchedule
      sigma outputLoss structuralBudget)
    (cwaNormalizationLoss : ℝ) : Prop where
  input_loss_le : inputLoss ≤ grainLoss
  delta_le_schedule : delta ≤ schedule.delta₀
  densitySeparation :
    Kakeya.realRpowENN delta outputEta ≤
      (1 / 2 : ENNReal) * Kakeya.realRpowENN delta inputEta
  inputDensityAbsorption :
    Kakeya.realRpowENN delta inputEta ≤
      (100 : ENNReal)⁻¹ * current.reentry.geometry.ordinaryDensity *
        Kakeya.realRpowENN delta grainLoss
  croppedMassAbsorption :
    croppedMassFraction ≤
      (100 : ENNReal)⁻¹ * current.reentry.geometry.ordinaryDensity
  input_loss_le_cwa : inputLoss ≤ cwaNormalizationLoss
  cwa_epsilon_pos :
    0 < schedule.densityLoss - cwaNormalizationLoss
  cwaRestrictionAbsorption :
    wz2PaperPureNearbyRestrictionConstant
        (Kakeya.realRpowENN delta (-cwaNormalizationLoss))
        (Kakeya.realRpowENN delta inputEta * Kakeya.deltaTubeVolume delta)
        (pureWZ2SpatialCellDegreeConstant
          (schedule.densityLoss - cwaNormalizationLoss)
            current.grain.family.card)
        (pureWZ2SpatialCellRegularizationLoss
            (schedule.densityLoss - cwaNormalizationLoss)
              current.grain.family.card *
          Kakeya.deltaTubeVolume delta) ≤
      Kakeya.realRpowENN delta (-schedule.densityLoss)
  cwaCardinalityAbsorption :
    Kakeya.realRpowENN delta outputEta *
        pureWZ2SpatialCellRegularizationLoss
          (schedule.densityLoss - cwaNormalizationLoss)
            current.grain.family.card ≤
      Kakeya.realRpowENN delta inputEta
  grainLoss_le_density : grainLoss ≤ schedule.densityLoss
  densityLoss_le_half : schedule.densityLoss ≤ outputLoss / 2
  outputEta_le_structural :
    outputEta ≤ schedule.criticalFloor.structuralLoss
  densityAbsorption :
    (13824 : ENNReal) *
        Kakeya.realRpowENN delta schedule.densityLoss ≤
      Kakeya.realRpowENN delta outputEta
  topLevelAbsorption :
    ((Kakeya.realRpowENN delta outputEta)⁻¹ * 1) *
        Kakeya.realRpowENN delta (-grainLoss) ≤
      Kakeya.realRpowENN delta (-outputLoss)

/-- Assemble the ordinary producer from one scheduled scalar receipt and the
minimal actual dependent inputs. -/
noncomputable def PureWZ2HierarchyReentrantOrdinaryFamilyInputs.toProducer
    {sigma inputLoss delta grainLoss stickyRho outputLoss outputEta
      structuralBudget inputEta : ℝ}
    {normalizationExponent logExponent : ℕ}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    {middleLoss stickyLoss : ℝ}
    {croppedMassFraction : ENNReal}
    {schedule : PureWZ2ReentryTraceFloorSchedule
      sigma outputLoss structuralBudget}
    (familyInputs : PureWZ2HierarchyReentrantOrdinaryFamilyInputs
      (grainLoss := grainLoss) (stickyRho := stickyRho)
      (outputEta := outputEta) (inputEta := inputEta)
      (logExponent := logExponent)
      current middleLoss stickyLoss croppedMassFraction schedule)
    (cwaNormalizationLoss : ℝ)
    (scalar : PureWZ2HierarchyReentrantOrdinaryScalarReceipt
      (grainLoss := grainLoss) (outputEta := outputEta)
      (inputEta := inputEta)
      current croppedMassFraction schedule cwaNormalizationLoss) :
    PureWZ2HierarchyReentrantOrdinaryProducer
      (grainLoss := grainLoss) (stickyRho := stickyRho) current where
  middleLoss := middleLoss
  stickyLoss := stickyLoss
  logExponent := logExponent
  twoScale := familyInputs.twoScale
  ordinaryAllBins := familyInputs.ordinaryAllBins
  input_loss_le := scalar.input_loss_le
  outputLoss := outputLoss
  outputEta := outputEta
  croppedMassFraction := croppedMassFraction
  structuralBudget := structuralBudget
  stepSchedule := schedule
  delta_le_stepSchedule := scalar.delta_le_schedule
  inputEta := inputEta
  densitySeparation := scalar.densitySeparation
  inputDensityAbsorption := scalar.inputDensityAbsorption
  croppedMassAbsorption := scalar.croppedMassAbsorption
  cwaNormalizationLoss := cwaNormalizationLoss
  input_loss_le_cwa := scalar.input_loss_le_cwa
  cwa_epsilon_pos := scalar.cwa_epsilon_pos
  cwaRestrictionAbsorption := scalar.cwaRestrictionAbsorption
  cwaCardinalityAbsorption := scalar.cwaCardinalityAbsorption
  grainLoss_le_density := scalar.grainLoss_le_density
  densityLoss_le_half := scalar.densityLoss_le_half
  outputEta_le_structural := scalar.outputEta_le_structural
  densityAbsorption := scalar.densityAbsorption
  topLevelAbsorption := scalar.topLevelAbsorption

/-- Select the closed trace-floor schedule from the critical package and then
consume one dependent package of actual family inputs and scalar
compatibility. -/
theorem PureWZ2CriticalPackage.exists_reentrantOrdinaryProducer_of_scheduled
    {sigma inputLoss delta grainLoss stickyRho outputLoss outputEta
      structuralBudget inputEta : ℝ}
    {normalizationExponent logExponent : ℕ}
    (critical : PureWZ2CriticalPackage sigma)
    (current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent)
    (middleLoss stickyLoss : ℝ)
    (croppedMassFraction : ENNReal)
    (outputLoss_pos : 0 < outputLoss)
    (structuralBudget_pos : 0 < structuralBudget)
    (structuralBudget_le_output : structuralBudget ≤ outputLoss)
    (inputs :
      ∀ schedule : PureWZ2ReentryTraceFloorSchedule
          sigma outputLoss structuralBudget,
        ∃ familyInputs : PureWZ2HierarchyReentrantOrdinaryFamilyInputs
            (grainLoss := grainLoss) (stickyRho := stickyRho)
            (outputEta := outputEta) (inputEta := inputEta)
            (logExponent := logExponent)
            current middleLoss stickyLoss croppedMassFraction schedule,
          PureWZ2HierarchyReentrantOrdinaryScalarReceipt
            (grainLoss := grainLoss) (outputEta := outputEta)
            (inputEta := inputEta)
            current croppedMassFraction schedule inputLoss) :
    Nonempty (PureWZ2HierarchyReentrantOrdinaryProducer
      (grainLoss := grainLoss) (stickyRho := stickyRho) current) := by
  rcases critical.reentryTraceFloorSchedule outputLoss_pos structuralBudget_pos
      structuralBudget_le_output with ⟨schedule⟩
  rcases inputs schedule with ⟨familyInputs, scalar⟩
  exact ⟨familyInputs.toProducer inputLoss scalar⟩

end Kakeya.Assouad

end
