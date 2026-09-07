import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryAllBinCriticalFloorScheduledProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantStepSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantPrefix
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05OwnerTwoCallAssembly

/-!
# Source-parametric ordinary producer for the re-entrant hierarchy

This module is the narrow wiring boundary between the concrete ordinary
all-bin construction and one re-entry-preserving hierarchy transition.  The
two Node-5 calls determine the dependent two-scale source, after which the
standard cell pullback and source-carrier preparation are canonical.

All scalar obligations of the synchronized transition are stored once.  The
nearby-CWA certificate already present in `current.grain.extremal` is
transported internally to the literal subfamily selected by the synchronized
weighted regularization; no family-valued CWA callback remains.
-/

noncomputable section

namespace Kakeya.Assouad

/-- A concrete ordinary all-bin producer on the exact current re-entry source.

`ordinaryAllBins` is deliberately a single packaged producer rather than a
second copy of the long scalar ledger of
`PureWZ2SourceCarrierPreparation.toOneScaleOfScheduledAllBinsReentryTrace`.
Its intended implementation is precisely that theorem, specialized to
`current.reentry`. -/
structure PureWZ2HierarchyReentrantOrdinaryProducer
    {sigma inputLoss delta grainLoss stickyRho : ℝ}
    {normalizationExponent : ℕ}
    (current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent) where
  middleLoss : ℝ
  stickyLoss : ℝ
  logExponent : ℕ
  twoScale : PureWZ2OneScaleTwoScaleStickyData
    current.grain stickyRho middleLoss stickyLoss logExponent
  ordinaryAllBins :
    ∀ pullback : PureWZ2TwoScaleCellPullbackData twoScale,
      ∀ _prepared : PureWZ2SourceCarrierPreparation pullback,
        Nonempty (PureWZ2LocallyLinearOneScaleData current.grain grainLoss
          (pureWZ2SourceHorizontalFinalScale stickyRho))
  input_loss_le : inputLoss ≤ grainLoss
  outputLoss : ℝ
  outputEta : ℝ
  croppedMassFraction : ENNReal
  structuralBudget : ℝ
  stepSchedule : PureWZ2ReentryTraceFloorSchedule
    sigma outputLoss structuralBudget
  delta_le_stepSchedule : delta ≤ stepSchedule.delta₀
  inputEta : ℝ
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
  cwaNormalizationLoss : ℝ
  input_loss_le_cwa : inputLoss ≤ cwaNormalizationLoss
  cwa_epsilon_pos :
    0 < stepSchedule.densityLoss - cwaNormalizationLoss
  cwaRestrictionAbsorption :
    wz2PaperPureNearbyRestrictionConstant
        (Kakeya.realRpowENN delta (-cwaNormalizationLoss))
        (Kakeya.realRpowENN delta inputEta * Kakeya.deltaTubeVolume delta)
        (pureWZ2SpatialCellDegreeConstant
          (stepSchedule.densityLoss - cwaNormalizationLoss)
            current.grain.family.card)
        (pureWZ2SpatialCellRegularizationLoss
            (stepSchedule.densityLoss - cwaNormalizationLoss)
              current.grain.family.card *
          Kakeya.deltaTubeVolume delta) ≤
      Kakeya.realRpowENN delta (-stepSchedule.densityLoss)
  cwaCardinalityAbsorption :
    Kakeya.realRpowENN delta outputEta *
        pureWZ2SpatialCellRegularizationLoss
          (stepSchedule.densityLoss - cwaNormalizationLoss)
            current.grain.family.card ≤
      Kakeya.realRpowENN delta inputEta
  grainLoss_le_density : grainLoss ≤ stepSchedule.densityLoss
  densityLoss_le_half : stepSchedule.densityLoss ≤ outputLoss / 2
  outputEta_le_structural :
    outputEta ≤ stepSchedule.criticalFloor.structuralLoss
  densityAbsorption :
    (13824 : ENNReal) *
        Kakeya.realRpowENN delta stepSchedule.densityLoss ≤
      Kakeya.realRpowENN delta outputEta
  topLevelAbsorption :
    ((Kakeya.realRpowENN delta outputEta)⁻¹ * 1) *
        Kakeya.realRpowENN delta (-grainLoss) ≤
      Kakeya.realRpowENN delta (-outputLoss)

/-- The canonical dependent data selected before the all-bin producer is
called.  Keeping these witnesses in one record makes it impossible to combine
a pullback or source carrier from a different pair of owner calls. -/
structure PureWZ2HierarchyReentrantOrdinaryOneScaleData
    {sigma inputLoss delta grainLoss stickyRho : ℝ}
    {normalizationExponent : ℕ}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    (producer : PureWZ2HierarchyReentrantOrdinaryProducer
      (grainLoss := grainLoss) (stickyRho := stickyRho) current) where
  pullback : PureWZ2TwoScaleCellPullbackData
    producer.twoScale
  prepared : PureWZ2SourceCarrierPreparation pullback
  oneScale : PureWZ2LocallyLinearOneScaleData current.grain grainLoss
    (pureWZ2SourceHorizontalFinalScale stickyRho)

namespace PureWZ2HierarchyReentrantOrdinaryProducer

variable
    {sigma inputLoss delta grainLoss stickyRho : ℝ}
    {normalizationExponent : ℕ}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}

/-- Run the owner two-call output through the canonical cell pullback and
source-carrier preparation, then invoke the packaged scheduled all-bin
producer on that exact dependent chain. -/
theorem oneScaleData_nonempty
    (producer : PureWZ2HierarchyReentrantOrdinaryProducer
      (grainLoss := grainLoss) (stickyRho := stickyRho) current)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2HierarchyReentrantOrdinaryOneScaleData producer) := by
  let twoScale := producer.twoScale
  rcases twoScale.pullbackSelectedCells with ⟨pullback⟩
  rcases pullback.prepareSourceCarrier hbridge with ⟨prepared⟩
  rcases producer.ordinaryAllBins pullback prepared with ⟨oneScale⟩
  exact ⟨{
    pullback := pullback
    prepared := prepared
    oneScale := oneScale
  }⟩

/-- Produce one complete source-parametric ordinary hierarchy transition.
The synchronized nearby-CWA argument is obtained by applying the sole
family-valued transfer leaf to the certificate already stored in the current
grain extremality record. -/
theorem step_nonempty
    (producer : PureWZ2HierarchyReentrantOrdinaryProducer
      (grainLoss := grainLoss) (stickyRho := stickyRho) current)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2ReentrantOneScaleStepData current grainLoss
      producer.outputLoss (pureWZ2SourceHorizontalFinalScale stickyRho)
      producer.outputEta producer.croppedMassFraction) := by
  rcases producer.oneScaleData_nonempty hbridge with ⟨data⟩
  apply exists_pureWZ2ReentrantOneScaleStep_of_traceSchedule
    data.oneScale producer.input_loss_le producer.stepSchedule
    producer.delta_le_stepSchedule
    producer.inputEta producer.croppedMassFraction
    producer.densitySeparation producer.inputDensityAbsorption
    producer.croppedMassAbsorption producer.cwaNormalizationLoss
    producer.input_loss_le_cwa producer.cwa_epsilon_pos
    producer.cwaRestrictionAbsorption producer.cwaCardinalityAbsorption
    producer.grainLoss_le_density
    producer.densityAbsorption producer.topLevelAbsorption
    producer.densityLoss_le_half
    producer.outputEta_le_structural

/-- Package the selected transition in the ordinary-prefix interface.  The
step refreshes its ordinary source before exposing the next re-entry. -/
theorem output_nonempty
    (producer : PureWZ2HierarchyReentrantOrdinaryProducer
      (grainLoss := grainLoss) (stickyRho := stickyRho) current)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2ReentrantOneScaleOutput current producer.outputLoss
      (pureWZ2SourceHorizontalFinalScale stickyRho)) := by
  rcases producer.step_nonempty hbridge with ⟨step⟩
  refine ⟨{
    grainLoss := grainLoss
    outputEta := producer.outputEta
    croppedMassFraction := producer.croppedMassFraction
    step := ?_
  }⟩
  exact step

/-- A canonical selected step, useful to a dependent iterator which must keep
the next grain source and its exact re-entry definitionally synchronized. -/
noncomputable def step
    (producer : PureWZ2HierarchyReentrantOrdinaryProducer
      (grainLoss := grainLoss) (stickyRho := stickyRho) current)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    PureWZ2ReentrantOneScaleStepData current grainLoss producer.outputLoss
      (pureWZ2SourceHorizontalFinalScale stickyRho) producer.outputEta
      producer.croppedMassFraction :=
  Classical.choice (producer.step_nonempty hbridge)

end PureWZ2HierarchyReentrantOrdinaryProducer

end Kakeya.Assouad

end
