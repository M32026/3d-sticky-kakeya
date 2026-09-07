import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantTerminalRuntime
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularExactMultiWindow
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularPaperOrderVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularProjection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPairGoodBlocks
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ReentrantTerminalSelectedPostDeletionThresholds

/-!
# Paper-order reentrant terminal producer

For every good source block, `PureWZ2TerminalPopularExactWindowOutput` keeps
the complete dependent route from the outer-popular carrier through the joint
four-cycle graph and the final source-height refill.  The delta-scale
`baseGlobalBin` is selected only inside that graph.

The final height restriction stays on the sticky-selected family, where the
constant multiplicity band is still available.  A mod-16 class is selected by
its indexed mass and only then extended by zero to the original source family.
Consequently the terminal volume lower bound follows directly from one
paper-facing, slabwise mass-retention statement.  No ordinary trace or critical
floor is used in this terminal closure.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The fixed combinatorial coefficient reserved for the joint
mass/cardinality Actual-John selection.  It depends only on the already
scheduled number of coordinates, never on a runtime tube family. -/
def pureWZ2ReentrantTerminalActualJohnCoefficient
    (coordinateCount : ℕ) : ENNReal :=
  (185193 : ENNReal) *
    (16 * (coordinateCount : ENNReal)) *
      ((((pureWZ2ReentrantTerminalUniformConflictDegree + 1 : ℕ) :
          ENNReal) ^ coordinateCount) * 8)

theorem pureWZ2ReentrantTerminalActualJohnCoefficient_ne_top
    (coordinateCount : ℕ) :
    pureWZ2ReentrantTerminalActualJohnCoefficient coordinateCount ≠ ⊤ := by
  unfold pureWZ2ReentrantTerminalActualJohnCoefficient
  exact
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (by norm_num)
        (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)))
      (ENNReal.mul_ne_top
        (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
        (by norm_num))

/--
Family-independent scalars for the future joint Actual-John owner route.

This record reserves the caller, fibre, and simultaneous-selection losses and
absorbs their fixed combinatorial/logarithmic envelope.  It deliberately
contains no family, owner, CWA datum, or selection witness: a later producer
must still construct the one joint witness and prove that its concrete
constants are bounded by this envelope.
-/
structure PureWZ2ReentrantTerminalActualJohnScalarSchedule
    (capability : PureWZ2PropStickyCapability)
    (internalLossCeiling publicLoss : ℝ) where
  ownerEpsilon : ℝ
  ownerEpsilon_eq : ownerEpsilon = publicLoss / 16
  ownerEpsilon_pos : 0 < ownerEpsilon
  coordinateCount : ℕ
  coordinateCount_eq :
    coordinateCount = geometricScaleCount ownerEpsilon
  coordinateCount_pos : 0 < coordinateCount
  callerLoss : ℝ
  callerLoss_eq : callerLoss = publicLoss / 16
  callerLoss_pos : 0 < callerLoss
  fiberLoss : ℝ
  fiberLoss_eq : fiberLoss = publicLoss / 16
  fiberLoss_pos : 0 < fiberLoss
  selectionLoss : ℝ
  selectionLoss_eq :
    selectionLoss = publicLoss / 32 - internalLossCeiling
  selectionLoss_pos : 0 < selectionLoss
  fixedBalancingGap :
    16 * (internalLossCeiling + selectionLoss) < publicLoss
  totalLoss : ℝ
  totalLoss_eq :
    totalLoss = ownerEpsilon + callerLoss + fiberLoss + selectionLoss
  totalLoss_lt_public : totalLoss < publicLoss
  fineExponent : ℕ
  fineExponent_eq : fineExponent = 1
  fineExponent_pos : 0 < fineExponent
  outputLogExponent : ℕ
  outputLogSplit :
    capability.logExponent + fineExponent = outputLogExponent
  outputLogExponent_le_successor :
    outputLogExponent ≤ capability.logExponent + 1
  outputLogExponent_le_coordinates :
    outputLogExponent ≤ capability.logExponent + coordinateCount
  jointLogPower : ℕ
  jointLogPower_eq : jointLogPower = 2 * coordinateCount + 9
  jointLogPower_pos : 0 < jointLogPower
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  actualJohn_absorption :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      Kakeya.realRpowENN delta selectionLoss *
          (pureWZ2ReentrantTerminalActualJohnCoefficient coordinateCount *
            pureWZ2ReentrantTerminalSelectedPostDeletionEnvelope delta ^
              jointLogPower) ≤
        1

/-- Select the complete terminal Actual-John scalar ledger before the runtime
source loss, scale, family, or owner is known. -/
theorem pureWZ2_reentrantTerminal_actualJohnScalarSchedule
    (capability : PureWZ2PropStickyCapability)
    {internalLossCeiling publicLoss : ℝ}
    (selectedPostDeletionThresholds :
      PureWZ2ReentrantTerminalSelectedPostDeletionThresholds
        internalLossCeiling publicLoss)
    (hinternalLossCeiling : 0 < internalLossCeiling)
    (hpublicLoss : 0 < publicLoss) :
    Nonempty
      (PureWZ2ReentrantTerminalActualJohnScalarSchedule
        capability internalLossCeiling publicLoss) := by
  let ownerEpsilon := publicLoss / 16
  let coordinateCount := geometricScaleCount ownerEpsilon
  let callerLoss := publicLoss / 16
  let fiberLoss := publicLoss / 16
  let selectionLoss := selectedPostDeletionThresholds.selectionLossFloor
  let totalLoss := ownerEpsilon + callerLoss + fiberLoss + selectionLoss
  let fineExponent : ℕ := 1
  let outputLogExponent := capability.logExponent + fineExponent
  let jointLogPower := 2 * coordinateCount + 9
  have hownerEpsilon : 0 < ownerEpsilon := by
    dsimp only [ownerEpsilon]
    positivity
  have hcoordinateCount : 0 < coordinateCount := by
    dsimp only [coordinateCount, geometricScaleCount]
    omega
  have hcallerLoss : 0 < callerLoss := by
    dsimp only [callerLoss]
    positivity
  have hfiberLoss : 0 < fiberLoss := by
    dsimp only [fiberLoss]
    positivity
  have hselectionLoss : 0 < selectionLoss := by
    dsimp only [selectionLoss]
    exact selectedPostDeletionThresholds.selectionLossFloor_pos
  have hselectionLossEq :
      selectionLoss = publicLoss / 32 - internalLossCeiling := by
    dsimp only [selectionLoss]
    rw [selectedPostDeletionThresholds.selectionLossFloor_eq,
      selectedPostDeletionThresholds.combinedLoss_eq]
  have hfixedBalancingGap :
      16 * (internalLossCeiling + selectionLoss) < publicLoss := by
    rw [hselectionLossEq]
    linarith
  have htotalLoss : totalLoss < publicLoss := by
    dsimp only [totalLoss, ownerEpsilon, callerLoss, fiberLoss]
    rw [hselectionLossEq]
    linarith [hselectionLoss]
  have hfineExponent : 0 < fineExponent := by
    dsimp only [fineExponent]
    omega
  have hjointLogPower : 0 < jointLogPower := by
    dsimp only [jointLogPower]
    omega
  have hlogCoefficient :
      0 ≤ pureWZ2ReentrantTerminalSelectedPostDeletionLogCoefficient := by
    unfold pureWZ2ReentrantTerminalSelectedPostDeletionLogCoefficient
      wz2PaperBoundaryLogCoefficient
      pureWZ2BoundedSourceCardLogConstant
    positivity
  rcases
      exists_delta_C_pow_log_absorbed_ennreal
        (pureWZ2ReentrantTerminalActualJohnCoefficient coordinateCount)
        (pureWZ2ReentrantTerminalActualJohnCoefficient_ne_top coordinateCount)
        pureWZ2ReentrantTerminalSelectedPostDeletionLogCoefficient
        hlogCoefficient hselectionLoss hjointLogPower
    with
    ⟨actualJohnDelta₀, hactualJohnDelta₀, hactualJohnDelta₀One,
      hactualJohnAbsorption⟩
  refine
    ⟨{
      ownerEpsilon := ownerEpsilon
      ownerEpsilon_eq := rfl
      ownerEpsilon_pos := hownerEpsilon
      coordinateCount := coordinateCount
      coordinateCount_eq := rfl
      coordinateCount_pos := hcoordinateCount
      callerLoss := callerLoss
      callerLoss_eq := rfl
      callerLoss_pos := hcallerLoss
      fiberLoss := fiberLoss
      fiberLoss_eq := rfl
      fiberLoss_pos := hfiberLoss
      selectionLoss := selectionLoss
      selectionLoss_eq := hselectionLossEq
      selectionLoss_pos := hselectionLoss
      fixedBalancingGap := hfixedBalancingGap
      totalLoss := totalLoss
      totalLoss_eq := rfl
      totalLoss_lt_public := htotalLoss
      fineExponent := fineExponent
      fineExponent_eq := rfl
      fineExponent_pos := hfineExponent
      outputLogExponent := outputLogExponent
      outputLogSplit := rfl
      outputLogExponent_le_successor := by
        simp [outputLogExponent, fineExponent]
      outputLogExponent_le_coordinates := by
        simp only [outputLogExponent, fineExponent]
        omega
      jointLogPower := jointLogPower
      jointLogPower_eq := rfl
      jointLogPower_pos := hjointLogPower
      delta₀ := actualJohnDelta₀
      delta₀_pos := hactualJohnDelta₀
      delta₀_le_one := hactualJohnDelta₀One
      actualJohn_absorption := ?_
    }⟩
  intro delta hdelta hdeltaSmall
  have hbound :=
    hactualJohnAbsorption delta hdelta hdeltaSmall
  have hbound' :
      pureWZ2ReentrantTerminalActualJohnCoefficient coordinateCount *
          pureWZ2ReentrantTerminalSelectedPostDeletionEnvelope delta ^
            jointLogPower ≤
        Kakeya.realRpowENN delta (-selectionLoss) := by
    simpa only [
      pureWZ2ReentrantTerminalSelectedPostDeletionEnvelope] using hbound
  calc
    Kakeya.realRpowENN delta selectionLoss *
          (pureWZ2ReentrantTerminalActualJohnCoefficient coordinateCount *
            pureWZ2ReentrantTerminalSelectedPostDeletionEnvelope delta ^
              jointLogPower) ≤
        Kakeya.realRpowENN delta selectionLoss *
          Kakeya.realRpowENN delta (-selectionLoss) := by
      gcongr
    _ = 1 := by
      rw [← realRpowENN_add hdelta]
      simp [Kakeya.realRpowENN]

/-- Source-independent terminal schedule with the small power loss reserved
for the local good-slab mass theorem. -/
structure PureWZ2ReentrantTerminalPaperOrderSchedule
    (capability : PureWZ2PropStickyCapability)
    (sigma outputLoss : ℝ) where
  kernel : PureWZ2ReentrantTerminalKernelSchedule capability sigma outputLoss
  actualJohn :
    PureWZ2ReentrantTerminalActualJohnScalarSchedule
      capability kernel.sourceLossCeiling kernel.terminal.sourceLossCeiling
  localMassLoss : ℝ
  localMassLoss_pos : 0 < localMassLoss
  output_half_lt_localMassLoss :
    kernel.terminal.workingLoss / 2 < localMassLoss
  localMassLoss_lt_gap :
    localMassLoss < kernel.terminal.workingLoss - kernel.terminal.stickyLoss
  selectedPostDeletionThresholds :
    PureWZ2ReentrantTerminalSelectedPostDeletionThresholds
      kernel.sourceLossCeiling kernel.terminal.sourceLossCeiling
  sourceLossCeiling : ℝ := kernel.sourceLossCeiling
  sourceLossCeiling_eq : sourceLossCeiling = kernel.sourceLossCeiling
  sourceLossCeiling_pos : 0 < sourceLossCeiling
  sourceLossCeiling_le_output : sourceLossCeiling ≤ outputLoss / 100
  sourceLossCeiling_kernel : sourceLossCeiling ≤ kernel.sourceLossCeiling
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_kernel : delta₀ ≤ kernel.delta₀
  delta₀_selectedPostDeletion :
    delta₀ ≤ selectedPostDeletionThresholds.delta₀
  delta₀_actualJohn : delta₀ ≤ actualJohn.delta₀
  actualJohn_selectionLoss_eq :
    actualJohn.selectionLoss =
      selectedPostDeletionThresholds.selectionLossFloor
  outputRefinementScalar :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      2 * wz1PaperRefinementFraction delta actualJohn.fineExponent ≤ 1
  delta₀_outerHeight :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      ∀ {inputLoss stickyLoss : ℝ} {logExponent : ℕ}
        {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
        {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
        {terminalSource : PureWZ2TerminalPreparedSource source terminal}
        {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
        {window : PureWZ2TerminalWindow prepared}
        (data : PureWZ2TerminalWindowHeightPopularData window),
          16 * Kakeya.realRpowENN delta localMassLoss *
              (data.popular.bins : ENNReal) *
              (data.popular.heightIndices.card : ENNReal) ≤
            pureWZ2TerminalPopularRichFloor delta kernel.terminal.workingLoss
  popularCReal :
    ∀ inputLoss delta : ℝ, 0 < inputLoss →
      inputLoss ≤ sourceLossCeiling → 0 < delta → delta ≤ delta₀ →
        (pureWZ2TerminalPopularGraphConstant delta inputLoss).toReal ≤
          Real.rpow delta (-kernel.terminal.constantLoss)
  popularExtra :
    ∀ {inputLoss delta : ℝ} {logExponent : ℕ}
      {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
      {terminal : PureWZ2TerminalScaleStickyData
        source kernel.terminal.stickyLoss logExponent}
      {terminalSource : PureWZ2TerminalPreparedSource source terminal}
      {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
      {window : PureWZ2TerminalWindow prepared}
      {heightData : PureWZ2TerminalWindowHeightPopularData window}
      {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
      {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
      {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
      {restrictedPrepared :
        PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
      {line : PureWZ2HorizontalFixedBinCore
        restrictedPrepared.windowed source.globalGrains.slope}
      {parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line}
      {selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents}
      {selectedCarrier :
        PureWZ2TerminalPopularSelectedParentCarrierData selection}
      {sources : PureWZ2TerminalPopularCoarseSourceFamily selection}
      {localized : PureWZ2TerminalPopularLocalizedPieceData
        (selectedCarrier := selectedCarrier) sources}
      {prep : PureWZ2TerminalPopularGraphPreparation localized}
      {graphParents : PureWZ2TerminalPopularGraphParentData prep}
      {localCells : PureWZ2TerminalPopularLocalCellData
        (eta := kernel.terminal.eta) graphParents}
      (preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells),
      0 < delta → delta ≤ delta₀ →
        (preparedGraph.graph.residue.extraCost : ℝ) ≤
          Real.rpow delta (-kernel.terminal.extraLoss)
  normalTransferSmall :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      1000 * Real.sqrt delta ≤ 1
  weightedSliceBudget :
    ∀ inputLoss delta, 0 < inputLoss →
      inputLoss ≤ sourceLossCeiling → 0 < delta → delta ≤ delta₀ →
        pureWZ2TerminalPairWeightedSliceLogCost delta *
            Kakeya.realRpowENN delta
              (1 + sigma / 2 + kernel.terminal.volumeLoss) *
            pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
          (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
            (2 + 3 * sigma / 2 + 5 * kernel.terminal.stickyLoss / 2)
  pairSourceMassAbsorption :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      pureWZ2TerminalPairSourceMassLogCost delta *
          Kakeya.realRpowENN delta
            (sigma + kernel.terminal.workingLoss) ≤
        Kakeya.realRpowENN delta localMassLoss *
          Kakeya.realRpowENN delta
            (sigma + kernel.terminal.stickyLoss)

/-- The frozen Actual-John selection loss is immediately usable by the
fixed-balancing construction at every runtime input below the scheduled
internal ceiling. -/
theorem PureWZ2ReentrantTerminalPaperOrderSchedule.actualJohn_fixedBalancingScalars
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss : ℝ}
    (schedule : PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss)
    {inputLoss delta : ℝ}
    (hinputLoss : inputLoss ≤ schedule.sourceLossCeiling)
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ schedule.delta₀) :
    schedule.actualJohn.selectionLoss =
        schedule.selectedPostDeletionThresholds.selectionLossFloor ∧
      0 < schedule.actualJohn.selectionLoss ∧
      16 * (inputLoss + schedule.actualJohn.selectionLoss) <
        schedule.kernel.terminal.sourceLossCeiling ∧
      delta ≤ schedule.selectedPostDeletionThresholds.numerical.delta₀ ∧
      delta ≤ pureWZ2PostDeletionFinalBalancingScale ∧
      delta ≤ 1 / 24 ∧
      50 * delta ≤
        Real.rpow delta
          (1 - schedule.kernel.terminal.sourceLossCeiling) := by
  have hselected :
      delta ≤ schedule.selectedPostDeletionThresholds.delta₀ :=
    hdeltaSmall.trans schedule.delta₀_selectedPostDeletion
  refine
    ⟨schedule.actualJohn_selectionLoss_eq,
      schedule.actualJohn.selectionLoss_pos, ?_,
      hselected.trans schedule.selectedPostDeletionThresholds.delta₀_numerical,
      hselected.trans schedule.selectedPostDeletionThresholds.delta₀_final,
      hselected.trans
        schedule.selectedPostDeletionThresholds.delta₀_le_twenty_four,
      schedule.selectedPostDeletionThresholds.periodic_scale
        hdelta hselected⟩
  have hinputKernel :
      inputLoss ≤ schedule.kernel.sourceLossCeiling := by
    simpa only [schedule.sourceLossCeiling_eq] using hinputLoss
  have hscaled :
      16 * (inputLoss + schedule.actualJohn.selectionLoss) ≤
        16 *
          (schedule.kernel.sourceLossCeiling +
            schedule.actualJohn.selectionLoss) :=
    mul_le_mul_of_nonneg_left
      (by linarith)
      (by norm_num)
  exact hscaled.trans_lt schedule.actualJohn.fixedBalancingGap

/-- Freeze the terminal kernel and the local mass-loss budget before the
runtime hierarchy source is known. -/
theorem pureWZ2_reentrantTerminal_paperOrderSchedule
    (capability : PureWZ2PropStickyCapability)
    {sigma : ℝ} (critical : PureWZ2CriticalPackage sigma)
    {outputLoss : ℝ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (houtput : 0 < outputLoss) :
    Nonempty (PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss) := by
  rcases pureWZ2_reentrantTerminal_kernelSchedule capability critical
      hsigma hsigmaOne houtput with ⟨kernel⟩
  rcases
      pureWZ2_reentrantTerminal_selectedPostDeletionThresholds
        kernel.sourceLossCeiling_pos
        kernel.terminal.sourceLossCeiling_pos
        kernel.sourceLossCeiling_seed_gap
    with
    ⟨selectedPostDeletionThresholds⟩
  rcases
      pureWZ2_reentrantTerminal_actualJohnScalarSchedule
        capability selectedPostDeletionThresholds
        kernel.sourceLossCeiling_pos
        kernel.terminal.sourceLossCeiling_pos
    with
    ⟨actualJohn⟩
  let localMassLoss :=
    3 * (kernel.terminal.workingLoss - kernel.terminal.stickyLoss) / 4
  have hlocalMassLoss : 0 < localMassLoss := by
    dsimp only [localMassLoss]
    linarith [kernel.terminal.stickyLoss_lt_working]
  have hlocalMassGap : localMassLoss <
      kernel.terminal.workingLoss - kernel.terminal.stickyLoss := by
    dsimp only [localMassLoss]
    linarith [kernel.terminal.stickyLoss_lt_working]
  have houtputHalfLocal : kernel.terminal.workingLoss / 2 <
      localMassLoss := by
    have hstickyQuarter : kernel.terminal.stickyLoss ≤
        kernel.terminal.workingLoss / 4 := by
      exact kernel.terminal.stickyLoss_le_working_quarter
    dsimp only [localMassLoss]
    linarith
  have hpowerGap : kernel.terminal.stickyLoss + localMassLoss <
      kernel.terminal.workingLoss := by
    linarith
  rcases exists_delta_rpow_le_single (1 / 2 : ℝ) (1 / 1000)
      (by norm_num) (by norm_num) (by norm_num) with
    ⟨normalDelta₀, hnormalDelta₀, hnormalDelta₀One, hnormalAbsorption⟩
  rcases pureWZ2_terminalPopular_outerHeight_schedule
      kernel.terminal.workingLoss_lt_one houtputHalfLocal with
    ⟨outerHeightDelta₀, houterHeightDelta₀, houterHeightDelta₀One,
      houterHeight⟩
  let sourceLossCeiling := kernel.sourceLossCeiling
  have hsourceConstant : sourceLossCeiling < kernel.terminal.constantLoss := by
    have hle : sourceLossCeiling ≤ kernel.terminal.constantLoss / 8 :=
      kernel.sourceLossCeiling_terminal.trans
        kernel.terminal.sourceLossCeiling_constant
    dsimp only [sourceLossCeiling]
    linarith [kernel.terminal.constantLoss_pos]
  rcases exists_scale_absorb_constant (40000 : ENNReal) (by norm_num)
      kernel.sourceLossCeiling_pos.le hsourceConstant with
    ⟨popularCDelta₀, hpopularCDelta₀, hpopularCDelta₀One, hpopularC⟩
  rcases pureWZ2_terminalPopular_extraCost_schedule
      kernel.terminal.extraLoss_pos with
    ⟨popularExtraDelta₀, hpopularExtraDelta₀, hpopularExtraDelta₀One,
      hpopularExtra⟩
  rcases pureWZ2_terminalPair_weightedSlice_budget_schedule
      (hgap := lt_of_le_of_lt
        (by
          simpa only [add_comm] using
            add_le_add_right kernel.sourceLossCeiling_terminal
              (5 * kernel.terminal.stickyLoss / 2))
        kernel.terminal.sourceLossCeiling_sticky_volume) with
    ⟨weightedDelta₀, hweightedDelta₀, hweightedDelta₀One, hweighted⟩
  rcases pureWZ2_terminalPair_sourceMass_budget_schedule hpowerGap with
    ⟨pairMassDelta₀, hpairMassDelta₀, hpairMassDelta₀One, hpairMass⟩
  let delta₀ := min kernel.delta₀
    (min selectedPostDeletionThresholds.delta₀
      (min actualJohn.delta₀
        (min normalDelta₀ (min outerHeightDelta₀
          (min popularCDelta₀ (min popularExtraDelta₀
            (min weightedDelta₀ pairMassDelta₀)))))))
  have hsourceOutput : sourceLossCeiling ≤ outputLoss / 100 := by
    calc
      sourceLossCeiling ≤ kernel.sourceLossCeiling := le_rfl
      _ ≤ kernel.terminal.sourceLossCeiling :=
        kernel.sourceLossCeiling_terminal
      _ ≤ kernel.terminal.workingLoss / 100 :=
        kernel.terminal.sourceLossCeiling_working
      _ ≤ outputLoss / 100 := by
        gcongr
        exact kernel.terminal.workingLoss_le_output
  exact ⟨{
    kernel := kernel
    actualJohn := actualJohn
    localMassLoss := localMassLoss
    localMassLoss_pos := hlocalMassLoss
    output_half_lt_localMassLoss := houtputHalfLocal
    localMassLoss_lt_gap := hlocalMassGap
    selectedPostDeletionThresholds := selectedPostDeletionThresholds
    sourceLossCeiling := sourceLossCeiling
    sourceLossCeiling_eq := rfl
    sourceLossCeiling_pos := kernel.sourceLossCeiling_pos
    sourceLossCeiling_le_output := hsourceOutput
    sourceLossCeiling_kernel := le_rfl
    delta₀ := delta₀
    delta₀_pos := lt_min kernel.delta₀_pos
      (lt_min selectedPostDeletionThresholds.delta₀_pos
        (lt_min actualJohn.delta₀_pos
          (lt_min hnormalDelta₀
            (lt_min houterHeightDelta₀
              (lt_min hpopularCDelta₀
                (lt_min hpopularExtraDelta₀
                  (lt_min hweightedDelta₀ hpairMassDelta₀)))))))
    delta₀_le_one := (min_le_left _ _).trans kernel.delta₀_le_one
    delta₀_kernel := min_le_left _ _
    delta₀_selectedPostDeletion :=
      (min_le_right _ _).trans (min_le_left _ _)
    delta₀_actualJohn :=
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
    actualJohn_selectionLoss_eq := by
      rw [actualJohn.selectionLoss_eq,
        selectedPostDeletionThresholds.selectionLossFloor_eq,
        selectedPostDeletionThresholds.combinedLoss_eq]
    outputRefinementScalar := by
      intro delta hdelta hdeltaSmall
      have hfraction :=
        kernel.postDeletionThresholds.deletion_fraction_small hdelta <|
          (hdeltaSmall.trans (min_le_left _ _)).trans
            kernel.delta₀_postDeletion
      rw [actualJohn.fineExponent_eq]
      calc
        2 * wz1PaperRefinementFraction delta 1 ≤
            2 * (1 / 2 : ENNReal) := by
          gcongr
        _ = 1 := by
          rw [one_div]
          exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    delta₀_outerHeight := by
      intro delta hdelta hdeltaSmall inputLoss stickyLoss logExponent source
        terminal terminalSource prepared window data
      exact houterHeight data hdelta
        (hdeltaSmall.trans (by simp [delta₀]))
    popularCReal := by
      intro inputLoss delta hinput hinputCeiling hdelta hdeltaSmall
      have hdeltaOne : delta ≤ 1 := hdeltaSmall.trans <|
        (min_le_left _ _).trans kernel.delta₀_le_one
      have hmono : Kakeya.realRpowENN delta (-inputLoss) ≤
          Kakeya.realRpowENN delta (-sourceLossCeiling) :=
        realRpowENN_antitone hdelta hdeltaOne (by linarith)
      have hbound := hpopularC delta hdelta
        (hdeltaSmall.trans (by simp [delta₀]))
      have hENN : pureWZ2TerminalPopularGraphConstant delta inputLoss ≤
          Kakeya.realRpowENN delta (-kernel.terminal.constantLoss) := by
        unfold pureWZ2TerminalPopularGraphConstant
        exact (mul_le_mul_left' hmono 40000).trans hbound
      have htop : Kakeya.realRpowENN delta
          (-kernel.terminal.constantLoss) ≠ ⊤ := by
        simp [Kakeya.realRpowENN]
      have hreal := ENNReal.toReal_mono htop hENN
      simpa [pureWZ2TerminalPopularGraphConstant, Kakeya.realRpowENN,
        ENNReal.toReal_ofReal (Real.rpow_nonneg hdelta.le _)] using hreal
    popularExtra := by
      intro inputLoss delta logExponent source terminal terminalSource prepared
        window heightData carrier weightClass restricted restrictedPrepared line
        parents selection selectedCarrier sources localized prep graphParents
        localCells preparedGraph hdelta hdeltaSmall
      exact hpopularExtra preparedGraph hdelta
        (hdeltaSmall.trans (by simp [delta₀]))
    normalTransferSmall := by
      intro delta hdelta hdeltaSmall
      have hsmall : delta ≤ normalDelta₀ :=
        hdeltaSmall.trans (by simp [delta₀])
      have hp := hnormalAbsorption delta hdelta hsmall
      rw [show Real.rpow delta (1 / 2 : ℝ) = Real.sqrt delta by
        exact (Real.sqrt_eq_rpow delta).symm] at hp
      nlinarith
    weightedSliceBudget := by
      intro inputLoss delta hinput hinputCeiling hdelta hdeltaSmall
      have hweightedSmall : delta ≤ weightedDelta₀ :=
        hdeltaSmall.trans (by simp [delta₀])
      have hdeltaOne : delta ≤ 1 := hdeltaSmall.trans <|
        (min_le_left _ _).trans kernel.delta₀_le_one
      have hcost :
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
            pureWZ2TerminalExactVolumeCost delta sigma sourceLossCeiling := by
        unfold pureWZ2TerminalExactVolumeCost
        gcongr
        exact realRpowENN_antitone hdelta hdeltaOne (by linarith)
      calc
        pureWZ2TerminalPairWeightedSliceLogCost delta *
              Kakeya.realRpowENN delta
                (1 + sigma / 2 + kernel.terminal.volumeLoss) *
              pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
            pureWZ2TerminalPairWeightedSliceLogCost delta *
              Kakeya.realRpowENN delta
                (1 + sigma / 2 + kernel.terminal.volumeLoss) *
              pureWZ2TerminalExactVolumeCost delta sigma sourceLossCeiling := by
          gcongr
        _ ≤ _ := hweighted (sigma := sigma) hdelta hweightedSmall
    pairSourceMassAbsorption := by
      intro delta hdelta hdeltaSmall
      exact hpairMass hdelta
        (hdeltaSmall.trans (by simp [delta₀])) }⟩

/-- The complete paper-order terminal runtime beginning from an already
constructed terminal sticky datum.  The concrete residue is retained so that
later quantitative packaging refers to the same final shading. -/
structure PureWZ2TerminalPaperOrderRuntimeData
    {sigma inputLoss delta outputLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {logExponent : ℕ}
    (terminal : PureWZ2TerminalScaleStickyData
      source schedule.kernel.terminal.stickyLoss logExponent) where
  terminalSource : PureWZ2TerminalPreparedSource source terminal
  prepared : PureWZ2TerminalLemma23Prepared terminalSource
  pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared
  good : PureWZ2TerminalPopularGoodBlockFamilyData
    (eta := schedule.kernel.terminal.eta)
    (theoremEta := schedule.kernel.terminal.theoremEta)
    (outputLoss := schedule.kernel.terminal.workingLoss)
    (localMassLoss := schedule.localMassLoss) prepared
  residue : PureWZ2TerminalPopularBlockResidueData good
  sourceMassCost_eq : good.sourceMassCost = 8 * pairClass.bins
  inputLoss_le_working : inputLoss ≤ schedule.kernel.terminal.workingLoss
  terminal_volume_scalar :
    32 * good.sourceMassCost * Kakeya.realRpowENN delta
          (sigma + schedule.kernel.terminal.workingLoss) ≤
      Kakeya.realRpowENN delta schedule.localMassLoss *
        Kakeya.realRpowENN delta
          (sigma + schedule.kernel.terminal.stickyLoss)

namespace PureWZ2TerminalPaperOrderRuntimeData

private theorem exactWindowOfPaperOrderSchedule
    {sigma inputLoss delta outputLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {logExponent : ℕ}
    {terminal : PureWZ2TerminalScaleStickyData
      source schedule.kernel.terminal.stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {pairClass : PureWZ2TerminalBlockParentPairWeightClassData prepared}
    {block : ℤ} (_hblock : block ∈ pairClass.goodBlocks)
    (pairData : PureWZ2TerminalPairBlockPopularData pairClass block)
    (hinput : 0 < inputLoss)
    (hinputCeiling : inputLoss ≤ schedule.sourceLossCeiling)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ schedule.delta₀)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (budget : PureWZ2TerminalChainBudget sigma inputLoss delta
      schedule.kernel.terminal.stickyLoss schedule.kernel.terminal.eta
      schedule.kernel.terminal.theoremEta
      schedule.kernel.terminal.workingLoss)
    (hsourceVolume :
      (512 : ENNReal) * Kakeya.realRpowENN delta
          (3 / 2 + sigma / 2 + schedule.kernel.terminal.eta) ≤
        terminal.sticky.balanced.cellMass)
    (hGraphCOne : (1 : ENNReal) ≤
      pureWZ2TerminalPopularGraphConstant delta inputLoss)
    (houtputTheorem : schedule.kernel.terminal.workingLoss +
      schedule.kernel.terminal.theoremEta ≤ 1)
    (hinputKernel : inputLoss ≤ schedule.kernel.sourceLossCeiling)
    (hdeltaTerminal : delta ≤ schedule.kernel.terminal.delta₀) :
    Nonempty (PureWZ2TerminalPopularExactWindowOutput
      (eta := schedule.kernel.terminal.eta)
      (theoremEta := schedule.kernel.terminal.theoremEta)
      (outputLoss := schedule.kernel.terminal.workingLoss)
      pairData.windowData.window) := by
  let preline : PureWZ2TerminalPopularPrefixData
      pairData.windowData.window := {
    heightData := pairData.heightData
    carrier := pairData.carrier
    weightClass := pairData.weightClass }
  apply pureWZ2_terminalPopular_exactWindow_of_prefix_and_certificates
    pairData.windowData.window preline hbridge
    schedule.kernel.terminal.sigma_pos
    schedule.kernel.terminal.sigma_lt_one
    budget.eta_pos budget.eta_sigma
    schedule.kernel.terminal.workingLoss_pos houtputTheorem
    budget.c_power budget.planar budget.root budget.localization
    (schedule.normalTransferSmall delta hdelta hdeltaSmall)
    hsourceVolume hGraphCOne
    (schedule.popularCReal inputLoss delta hinput hinputCeiling hdelta hdeltaSmall)
    (fun prep => pairData.weightedSlice
      (schedule.weightedSliceBudget inputLoss delta hinput hinputCeiling
        hdelta hdeltaSmall) _)
    (fun preparedGraph => schedule.popularExtra preparedGraph hdelta hdeltaSmall)
    (schedule.kernel.terminal.edge delta hdelta hdeltaTerminal)
    (schedule.kernel.terminal.refined_edge delta hdelta hdeltaTerminal)
    (schedule.kernel.terminal.katz delta hdelta hdeltaTerminal)
    (schedule.kernel.terminal.refined_katz delta hdelta hdeltaTerminal)
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ready
  exact schedule.kernel.terminal.projection.alternativeA_popular ready
    schedule.kernel.terminal.theoremEta_eq
    schedule.kernel.terminal.sigma_pos
    schedule.kernel.terminal.sigma_lt_one
    schedule.kernel.terminal.workingLoss_pos
    schedule.kernel.terminal.workingLoss_sigma hinput.le
    (hinputKernel.trans schedule.kernel.sourceLossCeiling_terminal |>.trans
      schedule.kernel.terminal.sourceLossCeiling_projection)
    (hdeltaTerminal.trans schedule.kernel.terminal.delta₀_projection)

end PureWZ2TerminalPaperOrderRuntimeData

/-- Run the existing paper-order terminal geometry directly on a supplied
terminal datum.  No sticky kernel or owner constructor is called here. -/
theorem pureWZ2_terminalScaleSticky_paperOrderRuntime
    {sigma inputLoss delta outputLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {logExponent : ℕ}
    (terminal : PureWZ2TerminalScaleStickyData
      source schedule.kernel.terminal.stickyLoss logExponent)
    (hinput : 0 < inputLoss)
    (hinputCeiling : inputLoss ≤ schedule.sourceLossCeiling)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ schedule.delta₀)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2TerminalPaperOrderRuntimeData
      (schedule := schedule) terminal) := by
  have hinputKernel : inputLoss ≤ schedule.kernel.sourceLossCeiling :=
    hinputCeiling.trans schedule.sourceLossCeiling_kernel
  have hdeltaKernel : delta ≤ schedule.kernel.delta₀ :=
    hdeltaSmall.trans schedule.delta₀_kernel
  have hdeltaTerminal : delta ≤ schedule.kernel.terminal.delta₀ :=
    hdeltaKernel.trans schedule.kernel.delta₀_terminal
  rcases terminal.prepareSource with ⟨terminalSource⟩
  rcases terminalSource.toLemma23Prepared hbridge with ⟨prepared⟩
  rcases pureWZ2Terminal_regularizeBlockParentPairs prepared with ⟨pairClass⟩
  let budget := schedule.kernel.terminal.budget inputLoss delta hinput
    (hinputKernel.trans schedule.kernel.sourceLossCeiling_terminal)
    hdelta hdeltaTerminal
  have hGraphCOne : (1 : ENNReal) ≤
      pureWZ2TerminalPopularGraphConstant delta inputLoss := by
    have hpower : (1 : ENNReal) ≤
        Kakeya.realRpowENN delta (-inputLoss) := by
      rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num,
        Kakeya.realRpowENN]
      exact ENNReal.ofReal_mono
        (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta
          (hdeltaSmall.trans schedule.delta₀_le_one) (by linarith))
    unfold pureWZ2TerminalPopularGraphConstant
    exact hpower.trans (le_mul_of_one_le_left' (by norm_num))
  have hsourceVolume :
      (512 : ENNReal) * Kakeya.realRpowENN delta
          (3 / 2 + sigma / 2 + schedule.kernel.terminal.eta) ≤
        terminal.sticky.balanced.cellMass := by
    calc
      _ ≤ (512 : ENNReal) * (2 * 512 * 57) *
          Kakeya.realRpowENN delta
            (3 / 2 + sigma / 2 + schedule.kernel.terminal.eta) := by
        gcongr
        norm_num
      _ ≤ Kakeya.realRpowENN delta
          (3 / 2 + sigma / 2 + 3 * schedule.kernel.terminal.stickyLoss / 2) :=
        budget.source_volume
      _ ≤ terminal.sticky.balanced.cellMass := terminal.source_floor_power
  have houtputTheorem : schedule.kernel.terminal.workingLoss +
      schedule.kernel.terminal.theoremEta ≤ 1 := by
    rw [schedule.kernel.terminal.theoremEta_eq]
    linarith [schedule.kernel.terminal.workingLoss_le_half,
      schedule.kernel.terminal.projection.theoremEta_small]
  have outputFor : ∀ {block : ℤ}
      (hblock : block ∈ pairClass.goodBlocks),
      ∀ pairData : PureWZ2TerminalPairBlockPopularData pairClass block,
        Nonempty (PureWZ2TerminalPopularExactWindowOutput
          (eta := schedule.kernel.terminal.eta)
          (theoremEta := schedule.kernel.terminal.theoremEta)
          (outputLoss := schedule.kernel.terminal.workingLoss)
          pairData.windowData.window) := by
    intro block hblock pairData
    exact PureWZ2TerminalPaperOrderRuntimeData.exactWindowOfPaperOrderSchedule
      hblock pairData hinput
      hinputCeiling hdelta hdeltaSmall hbridge budget hsourceVolume hGraphCOne
      houtputTheorem hinputKernel hdeltaTerminal
  rcases pairClass.buildGoodBlockFamily outputFor
      (fun {block} hblock pairData output => by
        have hretained := output.chain.window_volume_retention
          schedule.localMassLoss
          (schedule.delta₀_outerHeight delta hdelta hdeltaSmall
            output.chain.heightData)
        rw [pairData.windowData.source_union_eq]
        exact hretained) with ⟨good, hgoodCost⟩
  rcases good.selectResidue with ⟨data⟩
  have hinputWorking : inputLoss ≤ schedule.kernel.terminal.workingLoss :=
    hinputKernel.trans <| schedule.kernel.sourceLossCeiling_terminal.trans <|
      schedule.kernel.terminal.sourceLossCeiling_working.trans <|
        div_le_self schedule.kernel.terminal.workingLoss_pos.le (by norm_num)
  have hsourceMassAbsorption :
      32 * good.sourceMassCost * Kakeya.realRpowENN delta
          (sigma + schedule.kernel.terminal.workingLoss) ≤
        Kakeya.realRpowENN delta schedule.localMassLoss *
          Kakeya.realRpowENN delta
            (sigma + schedule.kernel.terminal.stickyLoss) := by
    calc
      32 * good.sourceMassCost * Kakeya.realRpowENN delta
            (sigma + schedule.kernel.terminal.workingLoss) =
          (256 * pairClass.bins : ENNReal) * Kakeya.realRpowENN delta
            (sigma + schedule.kernel.terminal.workingLoss) := by
        rw [hgoodCost]
        ring
      _ ≤ pureWZ2TerminalPairSourceMassLogCost delta *
          Kakeya.realRpowENN delta
            (sigma + schedule.kernel.terminal.workingLoss) := by
        gcongr
        exact pairClass.sourceMassCost_le
      _ ≤ _ := schedule.pairSourceMassAbsorption delta hdelta hdeltaSmall
  exact ⟨{
    terminalSource := terminalSource
    prepared := prepared
    pairClass := pairClass
    good := good
    residue := data
    sourceMassCost_eq := hgoodCost
    inputLoss_le_working := hinputWorking
    terminal_volume_scalar := hsourceMassAbsorption }⟩

namespace PureWZ2TerminalPaperOrderRuntimeData

/-- Forget the retained runtime witnesses only after constructing the exact
terminal level. -/
theorem toExactTerminal
    {sigma inputLoss delta outputLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {logExponent : ℕ}
    {terminal : PureWZ2TerminalScaleStickyData
      source schedule.kernel.terminal.stickyLoss logExponent}
    (runtime : PureWZ2TerminalPaperOrderRuntimeData
      (schedule := schedule) terminal) :
    Nonempty (PureWZ2ExactTerminalLevelData source outputLoss) := by
  rcases runtime.residue.toExactTerminalLevel
      runtime.inputLoss_le_working runtime.terminal_volume_scalar with
    ⟨workingTerminal⟩
  exact ⟨workingTerminal.mono_loss
    schedule.kernel.terminal.workingLoss_le_output⟩

/-- The same paper-order mass ledger gives an indexed-mass lower bound for
the concrete final residue.  The target exponent is kept explicit so that its
polylogarithmic refinement loss is selected by the outer schedule. -/
theorem finalShading_source_body_mass_lower
    {sigma inputLoss delta outputLoss densityLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {logExponent : ℕ}
    {terminal : PureWZ2TerminalScaleStickyData
      source schedule.kernel.terminal.stickyLoss logExponent}
    (runtime : PureWZ2TerminalPaperOrderRuntimeData
      (schedule := schedule) terminal)
    (hscalar :
      (32 * runtime.good.sourceMassCost *
          Kakeya.realRpowENN delta densityLoss) ≤
        Kakeya.realRpowENN delta schedule.localMassLoss *
          wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta inputLoss) :
    Kakeya.realRpowENN delta densityLoss *
        (wz1PaperBodyFamily source.family).mass ≤
      runtime.residue.finalShading.mass := by
  have hsourceDense : Kakeya.realRpowENN delta inputLoss *
      (wz1PaperBodyFamily source.family).mass ≤ source.shading.mass :=
    source.extremal.dense
  have hterminalMass : wz2PaperPureRefinementFraction delta logExponent *
      source.shading.mass ≤ runtime.terminalSource.shading.mass := by
    calc
      wz2PaperPureRefinementFraction delta logExponent * source.shading.mass ≤
          terminal.sticky.refined.mass := terminal.sticky.retained_mass
      _ = runtime.terminalSource.shading.mass := by
        rw [runtime.terminalSource.shading_eq]
  have hterminalGood : runtime.terminalSource.shading.mass ≤
      runtime.good.sourceMassCost *
        ∑ index : Fin runtime.good.indexCount,
          (runtime.good.sourceShading index).mass :=
    runtime.good.source_mass_control
  have hlocal : ∀ index : Fin runtime.good.indexCount,
      Kakeya.realRpowENN delta schedule.localMassLoss *
          (runtime.good.sourceShading index).mass ≤
        (runtime.good.blockShading index).mass := by
    intro index
    have hsourceUpper := constant_multiplicity_mass_volume_generic
      (runtime.good.sourceShading_constant_multiplicity index) |>.2
    have htargetLower := constant_multiplicity_mass_volume_generic
      (runtime.good.blockShading_constant_multiplicity index) |>.1
    calc
      Kakeya.realRpowENN delta schedule.localMassLoss *
          (runtime.good.sourceShading index).mass ≤
        Kakeya.realRpowENN delta schedule.localMassLoss *
          ((2 * runtime.terminalSource.multiplicity : ENNReal) *
            MeasureTheory.volume (runtime.good.sourceShading index).union) := by gcongr
      _ = (runtime.terminalSource.multiplicity : ENNReal) *
          (2 * Kakeya.realRpowENN delta schedule.localMassLoss *
            MeasureTheory.volume
              (runtime.good.sourceShading index).union) := by ring
      _ ≤ (runtime.terminalSource.multiplicity : ENNReal) *
          MeasureTheory.volume (runtime.good.blockShading index).union := by
        gcongr
        exact runtime.good.block_volume_retention index
      _ ≤ (runtime.good.blockShading index).mass := htargetLower
  have hlocalSum : Kakeya.realRpowENN delta schedule.localMassLoss *
      (∑ index : Fin runtime.good.indexCount,
        (runtime.good.sourceShading index).mass) ≤
      ∑ index : Fin runtime.good.indexCount,
        (runtime.good.blockShading index).mass := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun index _ => hlocal index
  have hchain :
      (Kakeya.realRpowENN delta schedule.localMassLoss *
          wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta inputLoss) *
          (wz1PaperBodyFamily source.family).mass ≤
        (32 * runtime.good.sourceMassCost) *
          runtime.residue.finalShading.mass := by
    calc
      _ = Kakeya.realRpowENN delta schedule.localMassLoss *
          (wz2PaperPureRefinementFraction delta logExponent *
            (Kakeya.realRpowENN delta inputLoss *
              (wz1PaperBodyFamily source.family).mass)) := by ring
      _ ≤ Kakeya.realRpowENN delta schedule.localMassLoss *
          (wz2PaperPureRefinementFraction delta logExponent *
            source.shading.mass) := by gcongr
      _ ≤ Kakeya.realRpowENN delta schedule.localMassLoss *
          runtime.terminalSource.shading.mass := by gcongr
      _ ≤ Kakeya.realRpowENN delta schedule.localMassLoss *
          (runtime.good.sourceMassCost *
            ∑ index : Fin runtime.good.indexCount,
              (runtime.good.sourceShading index).mass) := by gcongr
      _ = runtime.good.sourceMassCost *
          (Kakeya.realRpowENN delta schedule.localMassLoss *
            ∑ index : Fin runtime.good.indexCount,
              (runtime.good.sourceShading index).mass) := by ring
      _ ≤ runtime.good.sourceMassCost *
          ∑ index : Fin runtime.good.indexCount,
            (runtime.good.blockShading index).mass := by gcongr
      _ ≤ runtime.good.sourceMassCost *
          (16 * ∑ index ∈ runtime.residue.selected,
            (runtime.good.blockShading index).mass) :=
        mul_le_mul_right runtime.residue.total_mass_le
          runtime.good.sourceMassCost
      _ = (16 * runtime.good.sourceMassCost) *
          runtime.residue.finalShading.mass := by
        rw [runtime.residue.finalShading_mass_eq_sum]
        ring
      _ ≤ (32 * runtime.good.sourceMassCost) *
          runtime.residue.finalShading.mass := by
        gcongr
        norm_num
  let cost : ENNReal := 32 * runtime.good.sourceMassCost
  have hcostZero : cost ≠ 0 := by
    exact mul_ne_zero (by norm_num) runtime.good.sourceMassCost_pos.ne'
  have hcostTop : cost ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) runtime.good.sourceMassCost_ne_top
  apply (ENNReal.mul_le_mul_iff_left hcostZero hcostTop).mp
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    (show cost * (Kakeya.realRpowENN delta densityLoss *
          (wz1PaperBodyFamily source.family).mass) ≤
        cost * runtime.residue.finalShading.mass by
      calc
        cost * (Kakeya.realRpowENN delta densityLoss *
            (wz1PaperBodyFamily source.family).mass) =
          (cost * Kakeya.realRpowENN delta densityLoss) *
            (wz1PaperBodyFamily source.family).mass := by ring
        _ ≤ (Kakeya.realRpowENN delta schedule.localMassLoss *
              wz2PaperPureRefinementFraction delta logExponent *
              Kakeya.realRpowENN delta inputLoss) *
            (wz1PaperBodyFamily source.family).mass := by gcongr
        _ ≤ cost * runtime.residue.finalShading.mass := hchain)

end PureWZ2TerminalPaperOrderRuntimeData

/-- The paper-order terminal route retains the exact actual-owner invocation.
The weighted fixed-slice receipt and all later finite-grid, projection,
rich-height, and multi-window steps are constructed internally. -/
structure PureWZ2ReentrantTerminalPaperOrderReceipts
    {sigma inputLoss delta outputLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    (invocation : PureWZ2ReentrantTerminalKernelInvocation
      (schedule := schedule.kernel) current) where
  owner : PureWZ2ReentrantTerminalKernelOwnerReceipt invocation

namespace PureWZ2ReentrantTerminalPaperOrderReceipts

/-- Package a genuine actual-owner invocation. -/
noncomputable def ofInvocation
    {sigma inputLoss delta outputLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    (invocation : PureWZ2ReentrantTerminalKernelInvocation
      (schedule := schedule.kernel) current) :
    PureWZ2ReentrantTerminalPaperOrderReceipts invocation :=
  { owner := PureWZ2ReentrantTerminalKernelOwnerReceipt.ofInvocation invocation }

/-- Select a mass-good mod-16 class from the dependent paper-order block
outputs and close the terminal volume bound directly from constant
multiplicity. -/
theorem toExactTerminal
    {sigma inputLoss delta outputLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {invocation : PureWZ2ReentrantTerminalKernelInvocation
      (schedule := schedule.kernel) current}
    (hinput : 0 < inputLoss)
    (hinputCeiling : inputLoss ≤ schedule.sourceLossCeiling)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ schedule.delta₀)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (receipts : PureWZ2ReentrantTerminalPaperOrderReceipts invocation) :
    Nonempty (PureWZ2ExactTerminalLevelData current.grain outputLoss) := by
  let owner := receipts.owner.toOwner
  let terminal := owner.toTerminalScaleStickyData
  rcases pureWZ2_terminalScaleSticky_paperOrderRuntime terminal hinput
      hinputCeiling hdelta hdeltaSmall hbridge with ⟨runtime⟩
  exact runtime.toExactTerminal

end PureWZ2ReentrantTerminalPaperOrderReceipts

/-- Quantifier-ordered paper-facing terminal boundary.  The outer coarse line
is part of the Lemma-23 carrier construction; the delta-scale global bin used
by Theorem 22 is selected internally after the joint four-cycle count. -/
def PureWZ2ReentrantTerminalPaperOrderLeavesAt
    (capability : PureWZ2PropStickyCapability) (sigma : ℝ) : Prop :=
  ∀ outputLoss : ℝ,
    ∀ schedule : PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss,
      ∀ inputLoss : ℝ,
        0 < inputLoss → inputLoss ≤ schedule.sourceLossCeiling →
        ∀ delta : ℝ, 0 < delta → delta ≤ schedule.delta₀ →
          ∀ current : PureWZ2ReentrantGrainSource sigma inputLoss delta
              capability.normalizationExponent,
            Nonempty (Sigma fun invocation :
              PureWZ2ReentrantTerminalKernelInvocation
                (schedule := schedule.kernel) current =>
              PureWZ2ReentrantTerminalPaperOrderReceipts invocation)

/-- Construction-dependent terminal obligation.  Producing this value
requires the exact post-deletion witness, canonical actual-owner receipts, and
the concrete Node-5 owner call stored by the private invocation ABI. -/
def PureWZ2ReentrantTerminalOwnerLeavesAt
    (capability : PureWZ2PropStickyCapability) (sigma : ℝ) : Prop :=
  ∀ outputLoss : ℝ,
    ∀ schedule : PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss,
      ∀ inputLoss : ℝ,
        0 < inputLoss → inputLoss ≤ schedule.sourceLossCeiling →
        ∀ delta : ℝ, 0 < delta → delta ≤ schedule.delta₀ →
          ∀ current : PureWZ2ReentrantGrainSource sigma inputLoss delta
              capability.normalizationExponent,
            Nonempty (PureWZ2ReentrantTerminalKernelInvocation
              (schedule := schedule.kernel) current)

theorem pureWZ2_reentrantTerminal_paperOrderLeaves_of_owner
    {capability : PureWZ2PropStickyCapability} {sigma : ℝ}
    (ownerLeaves : PureWZ2ReentrantTerminalOwnerLeavesAt capability sigma) :
    PureWZ2ReentrantTerminalPaperOrderLeavesAt capability sigma := by
  intro outputLoss schedule inputLoss hinput hinputCeiling delta hdelta
    hdeltaSmall current
  rcases ownerLeaves outputLoss schedule inputLoss hinput hinputCeiling delta
      hdelta hdeltaSmall current with ⟨invocation⟩
  exact ⟨⟨invocation,
    PureWZ2ReentrantTerminalPaperOrderReceipts.ofInvocation invocation⟩⟩

/-- The scheduled paper-order receipts imply the exact terminal statement. -/
theorem pureWZ2_reentrantExactTerminalScaleAt_of_paperOrder
    (capability : PureWZ2PropStickyCapability)
    {sigma : ℝ} (critical : PureWZ2CriticalPackage sigma)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (leaves : PureWZ2ReentrantTerminalPaperOrderLeavesAt capability sigma) :
    PureWZ2ReentrantExactTerminalScaleAtStatement
      sigma capability.normalizationExponent := by
  intro outputLoss hsigma hsigmaOne houtput
  rcases pureWZ2_reentrantTerminal_paperOrderSchedule capability critical
      hsigma hsigmaOne houtput with ⟨schedule⟩
  refine ⟨schedule.sourceLossCeiling, schedule.delta₀,
    schedule.sourceLossCeiling_pos, schedule.sourceLossCeiling_le_output,
    schedule.delta₀_pos, schedule.delta₀_le_one, ?_⟩
  intro inputLoss hinput hinputCeiling delta hdelta hdeltaSmall current
  rcases leaves outputLoss schedule inputLoss hinput hinputCeiling delta
      hdelta hdeltaSmall current with ⟨⟨invocation, receipts⟩⟩
  exact receipts.toExactTerminal hinput hinputCeiling hdelta hdeltaSmall hbridge

end Kakeya.Assouad
