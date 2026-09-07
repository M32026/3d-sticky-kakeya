import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantOrdinarySchedule

/-!
# Quantifier-ordered front end for the re-entrant ordinary producer

This module packages the remaining dependent family constructions and runtime
scalar receipts under a trace-floor schedule chosen before the runtime source
and requested scale.  Nearby CWA on the synchronized selected family is now
constructed internally by weighted simultaneous regularization.
-/

noncomputable section

namespace Kakeya.Assouad

/-- All dependent family inputs of the ordinary step except nearby CWA.  The
two owner calls, their pullback, and the ordinary output remain indexed by the
literal current source and internal sticky scale. -/
structure PureWZ2HierarchyReentrantOrdinaryNonCWAInputs
    {sigma inputLoss delta grainLoss stickyRho : ℝ}
    {normalizationExponent logExponent : ℕ}
    (current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent)
    (middleLoss stickyLoss : ℝ) where
  twoScale : PureWZ2OneScaleTwoScaleStickyData
    current.grain stickyRho middleLoss stickyLoss logExponent
  ordinaryAllBins :
    ∀ pullback : PureWZ2TwoScaleCellPullbackData twoScale,
      ∀ _prepared : PureWZ2SourceCarrierPreparation pullback,
        Nonempty (PureWZ2LocallyLinearOneScaleData current.grain grainLoss
          (pureWZ2SourceHorizontalFinalScale stickyRho))

namespace PureWZ2HierarchyReentrantOrdinaryNonCWAInputs

/-- Package the dependent non-CWA geometry for the ordinary producer.  The
selected-family nearby-CWA certificate is constructed later from the source
certificate and the scalar schedule. -/
noncomputable def toFamilyInputs
    {sigma inputLoss delta grainLoss stickyRho outputLoss outputEta
      structuralBudget inputEta : ℝ}
    {normalizationExponent logExponent : ℕ}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    {middleLoss stickyLoss : ℝ}
    {croppedMassFraction : ENNReal}
    {schedule : PureWZ2ReentryTraceFloorSchedule
      sigma outputLoss structuralBudget}
    (nonCWA : PureWZ2HierarchyReentrantOrdinaryNonCWAInputs
      (grainLoss := grainLoss) (stickyRho := stickyRho)
      (logExponent := logExponent) current middleLoss stickyLoss) :
    PureWZ2HierarchyReentrantOrdinaryFamilyInputs
      (grainLoss := grainLoss) (stickyRho := stickyRho)
      (outputEta := outputEta) (inputEta := inputEta)
      (logExponent := logExponent) current middleLoss stickyLoss
      croppedMassFraction schedule where
  twoScale := nonCWA.twoScale
  ordinaryAllBins := nonCWA.ordinaryAllBins

/-- Proposition-level packaging theorem for callers which retain their
dependent family inputs under `Nonempty`. -/
theorem familyInputs_nonempty
    {sigma inputLoss delta grainLoss stickyRho outputLoss outputEta
      structuralBudget inputEta : ℝ}
    {normalizationExponent logExponent : ℕ}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    {middleLoss stickyLoss : ℝ}
    {croppedMassFraction : ENNReal}
    {schedule : PureWZ2ReentryTraceFloorSchedule
      sigma outputLoss structuralBudget}
    (nonCWA : PureWZ2HierarchyReentrantOrdinaryNonCWAInputs
      (grainLoss := grainLoss) (stickyRho := stickyRho)
      (logExponent := logExponent) current middleLoss stickyLoss) :
    Nonempty (PureWZ2HierarchyReentrantOrdinaryFamilyInputs
      (grainLoss := grainLoss) (stickyRho := stickyRho)
      (outputEta := outputEta) (inputEta := inputEta)
      (logExponent := logExponent) current middleLoss stickyLoss
      croppedMassFraction schedule) :=
  ⟨nonCWA.toFamilyInputs⟩

end PureWZ2HierarchyReentrantOrdinaryNonCWAInputs

/-- The exact runtime package with every dependent geometric construction and
the scalar receipt required to run the internal CWA regularizer. -/
structure PureWZ2HierarchyReentrantOrdinaryRuntimeNonCWAInputs
    {sigma inputLoss delta outputLoss rho structuralBudget : ℝ}
    {normalizationExponent : ℕ}
    (current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent)
    (schedule : PureWZ2ReentryTraceFloorSchedule
      sigma outputLoss structuralBudget) where
  grainLoss : ℝ
  stickyRho : ℝ
  middleLoss : ℝ
  stickyLoss : ℝ
  outputEta : ℝ
  inputEta : ℝ
  logExponent : ℕ
  croppedMassFraction : ENNReal
  cwaNormalizationLoss : ℝ
  output_scale_eq :
    pureWZ2SourceHorizontalFinalScale stickyRho = rho
  nonCWA : PureWZ2HierarchyReentrantOrdinaryNonCWAInputs
    (grainLoss := grainLoss) (stickyRho := stickyRho)
    (logExponent := logExponent) current middleLoss stickyLoss
  scalar : PureWZ2HierarchyReentrantOrdinaryScalarReceipt
    (grainLoss := grainLoss) (outputEta := outputEta)
    (inputEta := inputEta)
    current croppedMassFraction schedule cwaNormalizationLoss

/-- Runtime inputs left after the trace-floor schedule has been selected.
Every scalar inequality remains explicit.  The normalization exponent stays
fixed because the ordinary source is refreshed on the selected family after
each step, rather than because an ancestor-relative mass loss is iterated. -/
structure PureWZ2HierarchyReentrantOrdinaryRuntimeInputs
    {sigma inputLoss delta outputLoss rho structuralBudget : ℝ}
    {normalizationExponent : ℕ}
    (current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent)
    (schedule : PureWZ2ReentryTraceFloorSchedule
      sigma outputLoss structuralBudget) where
  grainLoss : ℝ
  stickyRho : ℝ
  middleLoss : ℝ
  stickyLoss : ℝ
  outputEta : ℝ
  inputEta : ℝ
  logExponent : ℕ
  croppedMassFraction : ENNReal
  cwaNormalizationLoss : ℝ
  output_scale_eq :
    pureWZ2SourceHorizontalFinalScale stickyRho = rho
  nonCWA : PureWZ2HierarchyReentrantOrdinaryNonCWAInputs
    (grainLoss := grainLoss) (stickyRho := stickyRho)
    (logExponent := logExponent) current middleLoss stickyLoss
  scalar : PureWZ2HierarchyReentrantOrdinaryScalarReceipt
    (grainLoss := grainLoss) (outputEta := outputEta)
    (inputEta := inputEta)
    current croppedMassFraction schedule cwaNormalizationLoss

namespace PureWZ2HierarchyReentrantOrdinaryRuntimeNonCWAInputs

/-- Repackage the runtime inputs after the internal CWA producer has been
installed. -/
noncomputable def toRuntimeInputs
    {sigma inputLoss delta outputLoss rho structuralBudget : ℝ}
    {normalizationExponent : ℕ}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    {schedule : PureWZ2ReentryTraceFloorSchedule
      sigma outputLoss structuralBudget}
    (inputs : PureWZ2HierarchyReentrantOrdinaryRuntimeNonCWAInputs
      (rho := rho) current schedule) :
    PureWZ2HierarchyReentrantOrdinaryRuntimeInputs
      (rho := rho) current schedule where
  grainLoss := inputs.grainLoss
  stickyRho := inputs.stickyRho
  middleLoss := inputs.middleLoss
  stickyLoss := inputs.stickyLoss
  outputEta := inputs.outputEta
  inputEta := inputs.inputEta
  logExponent := inputs.logExponent
  croppedMassFraction := inputs.croppedMassFraction
  cwaNormalizationLoss := inputs.cwaNormalizationLoss
  output_scale_eq := inputs.output_scale_eq
  nonCWA := inputs.nonCWA
  scalar := inputs.scalar

end PureWZ2HierarchyReentrantOrdinaryRuntimeNonCWAInputs

namespace PureWZ2HierarchyReentrantOrdinaryRuntimeInputs

/-- Assemble the split inputs and invoke the existing ordinary producer.  The
result is transported only across the recorded equality of output scales. -/
theorem output_nonempty
    {sigma inputLoss delta outputLoss rho structuralBudget : ℝ}
    {normalizationExponent : ℕ}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    {schedule : PureWZ2ReentryTraceFloorSchedule
      sigma outputLoss structuralBudget}
    (inputs : PureWZ2HierarchyReentrantOrdinaryRuntimeInputs
      (rho := rho) current schedule)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2ReentrantOneScaleOutput current outputLoss rho) := by
  let familyInputs : PureWZ2HierarchyReentrantOrdinaryFamilyInputs
      (grainLoss := inputs.grainLoss) (stickyRho := inputs.stickyRho)
      (outputEta := inputs.outputEta) (inputEta := inputs.inputEta)
      (logExponent := inputs.logExponent) current inputs.middleLoss
      inputs.stickyLoss inputs.croppedMassFraction schedule :=
    inputs.nonCWA.toFamilyInputs
  let producer := familyInputs.toProducer inputs.cwaNormalizationLoss inputs.scalar
  have output := producer.output_nonempty hbridge
  simpa only [producer, familyInputs,
    PureWZ2HierarchyReentrantOrdinaryFamilyInputs.toProducer,
    inputs.output_scale_eq] using output

end PureWZ2HierarchyReentrantOrdinaryRuntimeInputs

/-- One output-loss schedule selected before the runtime source and `rho`.
Only the family-dependent and runtime scalar receipts remain under `runtime`. -/
structure PureWZ2HierarchyReentrantOrdinaryFrontEndSchedule
    (sigma outputLoss sourceLossCeiling deltaThreshold : ℝ)
    (normalizationExponent : ℕ) where
  structuralBudget : ℝ
  schedule : PureWZ2ReentryTraceFloorSchedule
    sigma outputLoss structuralBudget
  runtime :
    ∀ inputLoss : ℝ,
      0 < inputLoss → inputLoss ≤ sourceLossCeiling →
      ∀ delta : ℝ, 0 < delta → delta ≤ deltaThreshold →
        ∀ current : PureWZ2ReentrantGrainSource
            sigma inputLoss delta normalizationExponent,
          ∀ rho : ℝ,
            delta ≤ rho → rho ≤ 1 →
            Real.rpow delta (1 - outputLoss) ≤ rho →
            rho ≤ Real.rpow delta outputLoss →
              Nonempty
                (PureWZ2HierarchyReentrantOrdinaryRuntimeInputs
                  (rho := rho) current schedule)

/-- Select the scalar trace-floor schedule from the critical package before
any runtime source, while leaving all runtime receipts explicit. -/
theorem PureWZ2CriticalPackage.reentrantOrdinaryFrontEndSchedule
    {sigma outputLoss sourceLossCeiling deltaThreshold structuralBudget : ℝ}
    {normalizationExponent : ℕ}
    (critical : PureWZ2CriticalPackage sigma)
    (outputLoss_pos : 0 < outputLoss)
    (structuralBudget_pos : 0 < structuralBudget)
    (structuralBudget_le_output : structuralBudget ≤ outputLoss)
    (runtime :
      ∀ schedule : PureWZ2ReentryTraceFloorSchedule
          sigma outputLoss structuralBudget,
        ∀ inputLoss : ℝ,
          0 < inputLoss → inputLoss ≤ sourceLossCeiling →
          ∀ delta : ℝ, 0 < delta → delta ≤ deltaThreshold →
            ∀ current : PureWZ2ReentrantGrainSource
                sigma inputLoss delta normalizationExponent,
              ∀ rho : ℝ,
                delta ≤ rho → rho ≤ 1 →
                Real.rpow delta (1 - outputLoss) ≤ rho →
                rho ≤ Real.rpow delta outputLoss →
                  Nonempty
                    (PureWZ2HierarchyReentrantOrdinaryRuntimeInputs
                      (rho := rho) current schedule)) :
    Nonempty (PureWZ2HierarchyReentrantOrdinaryFrontEndSchedule
      sigma outputLoss sourceLossCeiling deltaThreshold
      normalizationExponent) := by
  rcases critical.reentryTraceFloorSchedule outputLoss_pos
      structuralBudget_pos structuralBudget_le_output with ⟨schedule⟩
  exact ⟨{
    structuralBudget := structuralBudget
    schedule := schedule
    runtime := runtime schedule
  }⟩

/-- Quantifier-ordered conditional front end for one fixed critical exponent
and normalization exponent.  The uniform losses and scale threshold precede
the runtime reentrant source and requested scale. -/
def PureWZ2HierarchyReentrantOrdinaryFrontEndAt
    (sigma : ℝ) (normalizationExponent : ℕ) : Prop :=
  ∀ outputLoss : ℝ,
    0 < sigma → sigma < 1 → 0 < outputLoss →
      ∃ sourceLossCeiling delta₀ : ℝ,
        0 < sourceLossCeiling ∧
        sourceLossCeiling ≤ outputLoss / 100 ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        Nonempty (PureWZ2HierarchyReentrantOrdinaryFrontEndSchedule
          sigma outputLoss sourceLossCeiling delta₀ normalizationExponent)

/-- The high-level schedule with no nearby-CWA callback.  The trace-floor
schedule is selected before `inputLoss`, `delta`, the exact current source,
and `rho`; the runtime callback returns only dependent geometry and scalar
receipts. -/
structure PureWZ2HierarchyReentrantOrdinaryNonCWAFrontEndSchedule
    (sigma outputLoss sourceLossCeiling deltaThreshold : ℝ)
    (normalizationExponent : ℕ) where
  structuralBudget : ℝ
  schedule : PureWZ2ReentryTraceFloorSchedule
    sigma outputLoss structuralBudget
  runtime :
    ∀ inputLoss : ℝ,
      0 < inputLoss → inputLoss ≤ sourceLossCeiling →
      ∀ delta : ℝ, 0 < delta → delta ≤ deltaThreshold →
        ∀ current : PureWZ2ReentrantGrainSource
            sigma inputLoss delta normalizationExponent,
          ∀ rho : ℝ,
            delta ≤ rho → rho ≤ 1 →
            Real.rpow delta (1 - outputLoss) ≤ rho →
            rho ≤ Real.rpow delta outputLoss →
              Nonempty
                (PureWZ2HierarchyReentrantOrdinaryRuntimeNonCWAInputs
                  (rho := rho) current schedule)

/-- Quantifier-ordered non-CWA front end.  In particular, its schedule is not
allowed to depend on the runtime source or requested scale. -/
def PureWZ2HierarchyReentrantOrdinaryNonCWAFrontEndAt
    (sigma : ℝ) (normalizationExponent : ℕ) : Prop :=
  ∀ outputLoss : ℝ,
    0 < sigma → sigma < 1 → 0 < outputLoss →
      ∃ sourceLossCeiling delta₀ : ℝ,
        0 < sourceLossCeiling ∧
        sourceLossCeiling ≤ outputLoss / 100 ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        Nonempty (PureWZ2HierarchyReentrantOrdinaryNonCWAFrontEndSchedule
          sigma outputLoss sourceLossCeiling delta₀ normalizationExponent)

/-- Select a trace-floor schedule before runtime data. -/
theorem PureWZ2CriticalPackage.reentrantOrdinaryNonCWAFrontEndSchedule
    {sigma outputLoss sourceLossCeiling deltaThreshold structuralBudget : ℝ}
    {normalizationExponent : ℕ}
    (critical : PureWZ2CriticalPackage sigma)
    (outputLoss_pos : 0 < outputLoss)
    (structuralBudget_pos : 0 < structuralBudget)
    (structuralBudget_le_output : structuralBudget ≤ outputLoss)
    (runtime :
      ∀ schedule : PureWZ2ReentryTraceFloorSchedule
          sigma outputLoss structuralBudget,
        ∀ inputLoss : ℝ,
          0 < inputLoss → inputLoss ≤ sourceLossCeiling →
          ∀ delta : ℝ, 0 < delta → delta ≤ deltaThreshold →
            ∀ current : PureWZ2ReentrantGrainSource
                sigma inputLoss delta normalizationExponent,
              ∀ rho : ℝ,
                delta ≤ rho → rho ≤ 1 →
                Real.rpow delta (1 - outputLoss) ≤ rho →
                rho ≤ Real.rpow delta outputLoss →
                  Nonempty
                    (PureWZ2HierarchyReentrantOrdinaryRuntimeNonCWAInputs
                      (rho := rho) current schedule)) :
    Nonempty
      (PureWZ2HierarchyReentrantOrdinaryNonCWAFrontEndSchedule
        sigma outputLoss sourceLossCeiling deltaThreshold
        normalizationExponent) := by
  rcases critical.reentryTraceFloorSchedule outputLoss_pos
      structuralBudget_pos structuralBudget_le_output with ⟨schedule⟩
  exact ⟨{
    structuralBudget := structuralBudget
    schedule := schedule
    runtime := runtime schedule
  }⟩

/-- The geometric front end now suffices: nearby CWA is produced internally
from the current source certificate on the exact selected family. -/
theorem pureWZ2_ordinaryFrontEndAt_of_nonCWA
    {sigma : ℝ} {normalizationExponent : ℕ}
    (nonCWAFrontEnd :
      PureWZ2HierarchyReentrantOrdinaryNonCWAFrontEndAt
        sigma normalizationExponent) :
    PureWZ2HierarchyReentrantOrdinaryFrontEndAt
      sigma normalizationExponent := by
  intro outputLoss hsigma hsigmaOne houtputLoss
  rcases nonCWAFrontEnd outputLoss hsigma hsigmaOne houtputLoss with
    ⟨sourceLossCeiling, delta₀, hsourceLossCeiling,
      hsourceLossCeilingOutput, hdelta₀, hdelta₀One, ⟨frontEnd⟩⟩
  refine ⟨sourceLossCeiling, delta₀, hsourceLossCeiling,
    hsourceLossCeilingOutput, hdelta₀, hdelta₀One, ?_⟩
  refine ⟨{
    structuralBudget := frontEnd.structuralBudget
    schedule := frontEnd.schedule
    runtime := ?_
  }⟩
  intro inputLoss hinputLoss hinputLossCeiling delta hdelta hdeltaSmall
    current rho hdeltaRho hrhoOne hrhoLower hrhoUpper
  rcases frontEnd.runtime inputLoss hinputLoss hinputLossCeiling delta
      hdelta hdeltaSmall current rho hdeltaRho hrhoOne hrhoLower hrhoUpper with
    ⟨inputs⟩
  exact ⟨inputs.toRuntimeInputs⟩

/-- The split, quantifier-ordered front end implies exactly the existing
reentrant ordinary one-scale statement, without strengthening or generalizing
that public interface. -/
theorem pureWZ2_reentrantOneScaleAt_of_ordinaryFrontEnd
    {sigma : ℝ} {normalizationExponent : ℕ}
    (frontEnd : PureWZ2HierarchyReentrantOrdinaryFrontEndAt
      sigma normalizationExponent)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    PureWZ2ReentrantOneScaleAtStatement sigma normalizationExponent := by
  intro outputLoss hsigma hsigmaOne houtputLoss
  rcases frontEnd outputLoss hsigma hsigmaOne houtputLoss with
    ⟨sourceLossCeiling, delta₀, hsourceLossCeiling,
      hsourceLossCeilingOutput, hdelta₀, hdelta₀One, ⟨schedule⟩⟩
  refine ⟨sourceLossCeiling, delta₀, hsourceLossCeiling,
    hsourceLossCeilingOutput, hdelta₀, hdelta₀One, ?_⟩
  intro inputLoss hinputLoss hinputLossCeiling delta hdelta hdeltaSmall
    current rho hdeltaRho hrhoOne hrhoLower hrhoUpper
  rcases schedule.runtime inputLoss hinputLoss hinputLossCeiling delta
      hdelta hdeltaSmall current rho hdeltaRho hrhoOne hrhoLower hrhoUpper with
    ⟨inputs⟩
  exact inputs.output_nonempty hbridge

/-- The callback-free geometric front end implies the existing
source-parametric ordinary statement. -/
theorem pureWZ2_reentrantOneScaleAt_of_nonCWA
    {sigma : ℝ} {normalizationExponent : ℕ}
    (nonCWAFrontEnd :
      PureWZ2HierarchyReentrantOrdinaryNonCWAFrontEndAt
        sigma normalizationExponent)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    PureWZ2ReentrantOneScaleAtStatement sigma normalizationExponent :=
  pureWZ2_reentrantOneScaleAt_of_ordinaryFrontEnd
    (pureWZ2_ordinaryFrontEndAt_of_nonCWA nonCWAFrontEnd) hbridge

end Kakeya.Assouad

end
