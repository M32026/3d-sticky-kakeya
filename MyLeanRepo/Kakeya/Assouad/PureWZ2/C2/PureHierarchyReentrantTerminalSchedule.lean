import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantTerminalProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalChainNumericSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyExactTerminalLossMonotonicity

/-!
# Scheduled reentrant terminal leaf

All numerical terminal parameters are selected before the runtime reentrant
source.  The conditional boundary keeps only the source-indexed owner call
and the final actual-mass absorption.  Every good-block window retains its own
certified supply, so no universal prepared-volume receipt is needed.  The paper
bridge is supplied by the canonical hierarchy statement and is not duplicated
inside every runtime receipt.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2ReentrantTerminalScalarSchedule
    (sigma outputLoss : ℝ) where
  workingLoss : ℝ
  stickyLoss : ℝ
  eta : ℝ
  theoremEta : ℝ
  volumeLoss : ℝ
  constantLoss : ℝ
  constantLoss_pos : 0 < constantLoss
  extraLoss : ℝ
  extraLoss_pos : 0 < extraLoss
  sourceLossCeiling : ℝ
  delta₀ : ℝ
  sigma_pos : 0 < sigma
  sigma_lt_one : sigma < 1
  output_pos : 0 < outputLoss
  workingLoss_pos : 0 < workingLoss
  workingLoss_le_output : workingLoss ≤ outputLoss
  workingLoss_le_half : workingLoss ≤ 1 / 2
  workingLoss_lt_one : workingLoss < 1
  workingLoss_sigma : workingLoss / 2 < sigma
  stickyLoss_lt_working : stickyLoss < workingLoss
  stickyLoss_le_working_quarter : stickyLoss ≤ workingLoss / 4
  projection : PureWZ2TerminalExactProjectionThreshold sigma workingLoss
  theoremEta_eq : theoremEta = projection.theoremEta
  sourceLossCeiling_pos : 0 < sourceLossCeiling
  sourceLossCeiling_lt_stickyLoss : sourceLossCeiling < stickyLoss
  sourceLossCeiling_working : sourceLossCeiling ≤ workingLoss / 100
  sourceLossCeiling_constant : sourceLossCeiling ≤ constantLoss / 8
  sourceLossCeiling_sticky_volume :
    sourceLossCeiling + 5 * stickyLoss / 2 < volumeLoss
  sourceLossCeiling_projection :
    sourceLossCeiling ≤ projection.sourceLossCeiling
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_projection : delta₀ ≤ projection.delta₀
  budget :
    ∀ inputLoss delta, 0 < inputLoss → inputLoss ≤ sourceLossCeiling →
      0 < delta → delta ≤ delta₀ →
      PureWZ2TerminalChainBudget sigma inputLoss delta stickyLoss eta
        theoremEta workingLoss
  c_real :
    ∀ inputLoss delta, 0 < inputLoss → inputLoss ≤ sourceLossCeiling →
      0 < delta → delta ≤ delta₀ →
      (10 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
        Real.rpow delta (-constantLoss)
  volume_budget :
    ∀ inputLoss delta, 0 < inputLoss → inputLoss ≤ sourceLossCeiling →
      0 < delta → delta ≤ delta₀ →
      Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) *
          pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
        (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
          (2 + 3 * sigma / 2 + 5 * stickyLoss / 2)
  extra :
    ∀ {inputLoss delta : ℝ} {logExponent : ℕ}
      {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
      {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
      {terminalSource : PureWZ2TerminalPreparedSource source terminal}
      {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
      {window : PureWZ2TerminalWindow prepared}
      {line : PureWZ2HorizontalFixedBinCore
        window.windowed source.globalGrains.slope}
      {parents : PureWZ2TerminalFixedBinParentData line}
      {selection : PureWZ2TerminalBinParentYSelection parents}
      {residue : PureWZ2TerminalBinParentYResidueData selection}
      {retained : PureWZ2TerminalBinRetainedShadingData residue}
      {sources : PureWZ2TerminalBinSourceFamily retained}
      {band : PureWZ2TerminalBinFixedBandSelection sources}
      {phase : PureWZ2TerminalBinHeightPhaseSelection band}
      {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
      {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
      {graphParents : PureWZ2TerminalExactGraphParentData prep}
      {localCells : PureWZ2TerminalExactLocalCellData
        (eta := eta) graphParents}
      (preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells),
      0 < delta → delta ≤ delta₀ →
        (preparedGraph.graph.residue.extraCost : ℝ) ≤
          Real.rpow delta (-extraLoss)
  edge :
    ∀ delta, 0 < delta → delta ≤ delta₀ →
      Real.rpow (wz1Lemma23Theorem22Scale delta) (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ * Real.rpow delta
          (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss)
  refined_edge :
    ∀ delta, 0 < delta → delta ≤ delta₀ →
      Real.rpow (wz1Lemma23Theorem22Scale (delta / 625))
          (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ * Real.rpow delta
          (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss)
  katz :
    ∀ delta, 0 < delta → delta ≤ delta₀ →
      (4 : ENNReal) ≤ Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale delta) (-theoremEta)
  refined_katz :
    ∀ delta, 0 < delta → delta ≤ delta₀ →
      (4 : ENNReal) ≤ Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale (delta / 625)) (-theoremEta)
  alternativeA :
    ∀ {inputLoss delta : ℝ} {logExponent : ℕ}
      {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
      {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
      {terminalSource : PureWZ2TerminalPreparedSource source terminal}
      {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
      {window : PureWZ2TerminalWindow prepared}
      {line : PureWZ2HorizontalFixedLineCore
        window.windowed source.globalGrains.slope}
      {parents : PureWZ2TerminalFixedLineParentData line}
      {selection : PureWZ2TerminalParentYSelection parents}
      {residue : PureWZ2TerminalParentYResidueData selection}
      {retained : PureWZ2TerminalRetainedShadingData residue}
      {sources : PureWZ2TerminalSourceFamily retained}
      {band : PureWZ2TerminalFixedBandSelection sources}
      {phase : PureWZ2TerminalHeightPhaseSelection band}
      {anchored : PureWZ2TerminalAnchoredPieceData phase}
      {prep : PureWZ2TerminalExactGraphPreparation anchored}
      {graphParents : PureWZ2TerminalExactGraphParentData prep}
      {localCells : PureWZ2TerminalExactLocalCellData
        (eta := eta) graphParents}
      {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
      {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
      {first : PureWZ2TerminalExactReadyGraph
        (theoremEta := theoremEta) sharp}
      (ready : PureWZ2TerminalExactRefinedReadyGraph first),
      0 ≤ inputLoss → inputLoss ≤ sourceLossCeiling →
        delta ≤ delta₀ →
          WZ1Proposition8_9AlternativeAUnion
            ready.ready.deltaGraph workingLoss
            ready.common.F ready.common.G₁ ready.common.G₁

namespace PureWZ2ReentrantTerminalScalarSchedule

/-- The source-to-sticky loss gap is positive, but strictly smaller than one.
Consequently it cannot absorb a full extra factor of the square-root caller
scale arising from reverse literal-rescaling density. -/
theorem source_to_sticky_gap_lt_one
    {sigma outputLoss : ℝ}
    (schedule : PureWZ2ReentrantTerminalScalarSchedule sigma outputLoss) :
    schedule.stickyLoss - schedule.sourceLossCeiling < 1 := by
  linarith [schedule.stickyLoss_lt_working, schedule.workingLoss_lt_one,
    schedule.sourceLossCeiling_pos]

end PureWZ2ReentrantTerminalScalarSchedule

theorem pureWZ2_reentrantTerminal_scalarSchedule
    {sigma outputLoss : ℝ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (houtput : 0 < outputLoss) :
    Nonempty (PureWZ2ReentrantTerminalScalarSchedule sigma outputLoss) := by
  let workingLoss := min (outputLoss / 2) (min (1 / 2 : ℝ) sigma)
  have hworkingLoss : 0 < workingLoss := by
    dsimp only [workingLoss]
    exact lt_min (div_pos houtput (by norm_num))
      (lt_min (by norm_num) hsigma)
  have hworkingOutput : workingLoss ≤ outputLoss := by
    have h := min_le_left (outputLoss / 2) (min (1 / 2 : ℝ) sigma)
    nlinarith
  have hworkingOne : workingLoss < 1 := by
    have h := min_le_right (outputLoss / 2) (min (1 / 2 : ℝ) sigma)
    have hhalf := min_le_left (1 / 2 : ℝ) sigma
    nlinarith
  have hworkingHalf : workingLoss ≤ 1 / 2 :=
    (min_le_right (outputLoss / 2) (min (1 / 2 : ℝ) sigma)).trans
      (min_le_left (1 / 2 : ℝ) sigma)
  have hworkingSigma : workingLoss / 2 < sigma := by
    have h := min_le_right (outputLoss / 2) (min (1 / 2 : ℝ) sigma)
    have hsigmaBound := min_le_right (1 / 2 : ℝ) sigma
    nlinarith
  rcases pureWZ2_terminalExact_projection_threshold
      hsigma hworkingLoss hworkingOne hworkingSigma with ⟨projection⟩
  let theoremEta := projection.theoremEta
  let volumeLoss := theoremEta / 64
  let constantLoss := theoremEta / 64
  let extraLoss := theoremEta / 64
  have htheoremEta : 0 < theoremEta := projection.theoremEta_pos
  have hvolumeLoss : 0 < volumeLoss := by
    dsimp only [volumeLoss]
    positivity
  have hconstantLoss : 0 < constantLoss := by
    dsimp only [constantLoss]
    positivity
  have hextraLoss : 0 < extraLoss := by
    dsimp only [extraLoss]
    positivity
  let eta := min (sigma / 16) (theoremEta / 1024)
  have heta : 0 < eta := by
    dsimp only [eta]
    positivity
  have hetaSigma : 4 * eta < sigma := by
    have h := min_le_left (sigma / 16) (theoremEta / 1024)
    nlinarith
  have hetaSigmaEight : 8 * eta < sigma := by
    have h := min_le_left (sigma / 16) (theoremEta / 1024)
    nlinarith
  have hetaTheorem : eta ≤ theoremEta / 1024 :=
    min_le_right _ _
  have hetaVolume : eta ≤ volumeLoss / 16 := by
    dsimp only [volumeLoss]
    convert hetaTheorem using 1
    ring
  let stickyLoss := min (eta / 4) (workingLoss / 4)
  have hstickyLoss : 0 < stickyLoss := by
    dsimp only [stickyLoss]
    exact lt_min (div_pos heta (by norm_num))
      (div_pos hworkingLoss (by norm_num))
  have hstickyWorking : stickyLoss < workingLoss := by
    have h := min_le_right (eta / 4) (workingLoss / 4)
    dsimp only [stickyLoss]
    nlinarith
  have hstickyEta : 3 * stickyLoss / 2 < eta := by
    have h := min_le_left (eta / 4) (workingLoss / 4)
    dsimp only [stickyLoss]
    nlinarith
  let sourceLossCeiling := min (workingLoss / 100)
    (min (eta / 8) (min (constantLoss / 8)
      (min (volumeLoss / 8) projection.sourceLossCeiling)))
  have hsourceLossCeiling : 0 < sourceLossCeiling := by
    dsimp only [sourceLossCeiling]
    exact lt_min (div_pos hworkingLoss (by norm_num))
      (lt_min (div_pos heta (by norm_num))
        (lt_min (div_pos hconstantLoss (by norm_num))
          (lt_min (div_pos hvolumeLoss (by norm_num))
            projection.sourceLossCeiling_pos)))
  have hsourceWorking : sourceLossCeiling ≤ workingLoss / 100 :=
    min_le_left _ _
  have hsourceEta : sourceLossCeiling ≤ eta / 8 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hsourceConstant : sourceLossCeiling ≤ constantLoss / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsourceVolume : sourceLossCeiling ≤ volumeLoss / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hsourceProjection : sourceLossCeiling ≤ projection.sourceLossCeiling :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hsourceSticky : sourceLossCeiling < stickyLoss := by
    dsimp only [stickyLoss]
    apply lt_min
    · linarith [hsourceEta]
    · linarith [hsourceWorking]
  have hsourceEtaStrict : sourceLossCeiling < eta := by
    nlinarith
  have hsourceConstantStrict : sourceLossCeiling < constantLoss := by
    nlinarith
  have hvolumeGap : sourceLossCeiling + 5 * stickyLoss / 2 < volumeLoss := by
    dsimp only [stickyLoss]
    nlinarith [hetaVolume]
  have hedgeBudget :
      8 * ((volumeLoss + extraLoss) + constantLoss) < theoremEta / 2 := by
    dsimp only [volumeLoss, extraLoss, constantLoss]
    linarith
  rcases pureWZ2_terminal_chain_numeric_threshold
      hsigma hsigmaOne hsourceLossCeiling hstickyLoss heta hetaSigma hetaSigmaEight
      hsourceEtaStrict hsourceConstantStrict hvolumeLoss hconstantLoss hextraLoss
      hstickyEta hvolumeGap htheoremEta
      (projection.theoremEta_small.trans (by norm_num))
      hworkingLoss hworkingOne hworkingSigma hedgeBudget with ⟨numeric⟩
  rcases pureWZ2_terminalExact_extraCost_schedule hextraLoss with
    ⟨extraDelta₀, hextraDelta₀, hextraDelta₀One, hextra⟩
  let delta₀ := min (min numeric.delta₀ projection.delta₀) extraDelta₀
  have hdelta₀ : 0 < delta₀ :=
    lt_min (lt_min numeric.delta₀_pos projection.delta₀_pos) hextraDelta₀
  have hdelta₀One : delta₀ ≤ 1 :=
    ((min_le_left _ _).trans (min_le_left _ _)).trans numeric.delta₀_le_one
  refine ⟨{
    workingLoss := workingLoss
    stickyLoss := stickyLoss
    eta := eta
    theoremEta := theoremEta
    theoremEta_eq := rfl
    volumeLoss := volumeLoss
    constantLoss := constantLoss
    constantLoss_pos := hconstantLoss
    extraLoss := extraLoss
    extraLoss_pos := hextraLoss
    sourceLossCeiling := sourceLossCeiling
    delta₀ := delta₀
    sigma_pos := hsigma
    sigma_lt_one := hsigmaOne
    output_pos := houtput
    workingLoss_pos := hworkingLoss
    workingLoss_le_output := hworkingOutput
    workingLoss_le_half := hworkingHalf
    workingLoss_lt_one := hworkingOne
    workingLoss_sigma := hworkingSigma
    stickyLoss_lt_working := hstickyWorking
    stickyLoss_le_working_quarter := by
      dsimp only [stickyLoss]
      exact min_le_right _ _
    projection := projection
    sourceLossCeiling_pos := hsourceLossCeiling
    sourceLossCeiling_lt_stickyLoss := hsourceSticky
    sourceLossCeiling_working := hsourceWorking
    sourceLossCeiling_constant := hsourceConstant
    sourceLossCeiling_sticky_volume := hvolumeGap
    sourceLossCeiling_projection := hsourceProjection
    delta₀_pos := hdelta₀
    delta₀_le_one := hdelta₀One
    delta₀_projection := (min_le_left _ _).trans (min_le_right _ _)
    budget := ?_
    c_real := ?_
    volume_budget := ?_
    extra := ?_
    edge := ?_
    refined_edge := ?_
    katz := ?_
    refined_katz := ?_
    alternativeA := ?_ }⟩
  · intro inputLoss delta hinput hinputCeiling hdelta hdeltaSmall
    have hdeltaNumeric : delta ≤ numeric.delta₀ :=
      hdeltaSmall.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hcPower :
        10 * Kakeya.realRpowENN delta (-inputLoss) ≤
          Kakeya.realRpowENN delta (-eta) := by
      have hmono :
          Kakeya.realRpowENN delta (-inputLoss) ≤
            Kakeya.realRpowENN delta (-sourceLossCeiling) :=
        realRpowENN_antitone hdelta
          (hdeltaSmall.trans hdelta₀One) (by linarith)
      calc
        10 * Kakeya.realRpowENN delta (-inputLoss) ≤
            10 * Kakeya.realRpowENN delta (-sourceLossCeiling) := by gcongr
        _ ≤ Kakeya.realRpowENN delta (-eta) :=
          numeric.c_power delta hdelta hdeltaNumeric
    let ceilingBudget :=
      numeric.chain_budget delta hdelta hdeltaNumeric
    exact {
      sigma_pos := ceilingBudget.sigma_pos
      sigma_lt_one := ceilingBudget.sigma_lt_one
      eta_pos := ceilingBudget.eta_pos
      eta_sigma := ceilingBudget.eta_sigma
      output_pos := ceilingBudget.output_pos
      output_lt_one := ceilingBudget.output_lt_one
      output_sigma := ceilingBudget.output_sigma
      c_power := hcPower
      planar := ceilingBudget.planar
      root := ceilingBudget.root
      localization := ceilingBudget.localization
      source_volume := ceilingBudget.source_volume
      scale_one := ceilingBudget.scale_one
      length_lower := ceilingBudget.length_lower }
  · intro inputLoss delta hinput hinputCeiling hdelta hdeltaSmall
    have hdeltaNumeric : delta ≤ numeric.delta₀ :=
      hdeltaSmall.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hmono :
        Kakeya.realRpowENN delta (-inputLoss) ≤
          Kakeya.realRpowENN delta (-sourceLossCeiling) :=
      realRpowENN_antitone hdelta
        (hdeltaSmall.trans hdelta₀One) (by linarith)
    have hrightTop :
        Kakeya.realRpowENN delta (-sourceLossCeiling) ≠ ⊤ := by
      simp [Kakeya.realRpowENN]
    have htoReal := ENNReal.toReal_mono hrightTop hmono
    have hceiling :=
      numeric.c_real delta hdelta hdeltaNumeric
    exact (show
      (10 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
        (10 * Kakeya.realRpowENN delta (-sourceLossCeiling)).toReal by
      simpa [Kakeya.realRpowENN,
        ENNReal.toReal_ofReal (Real.rpow_nonneg hdelta.le _)] using htoReal).trans
      hceiling
  · intro inputLoss delta _hinput hinputCeiling hdelta hdeltaSmall
    have hdeltaOne : delta ≤ 1 := hdeltaSmall.trans hdelta₀One
    have hcost : pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
        pureWZ2TerminalExactVolumeCost delta sigma sourceLossCeiling := by
      unfold pureWZ2TerminalExactVolumeCost
      gcongr
      exact realRpowENN_antitone hdelta hdeltaOne (by linarith)
    calc
      Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) *
            pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
          Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) *
            pureWZ2TerminalExactVolumeCost delta sigma sourceLossCeiling := by
        gcongr
      _ ≤ (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
            (2 + 3 * sigma / 2 + 5 * stickyLoss / 2) :=
        numeric.volume_budget delta hdelta
          (hdeltaSmall.trans ((min_le_left _ _).trans (min_le_left _ _)))
  · intro inputLoss delta logExponent source terminal terminalSource prepared
      window line parents selection residue retained sources band phase anchored
      prep graphParents localCells preparedGraph hdelta hdeltaSmall
    exact hextra preparedGraph hdelta
      (hdeltaSmall.trans (min_le_right _ _))
  · intro delta hdelta hdeltaSmall
    exact numeric.edge delta hdelta
      (hdeltaSmall.trans ((min_le_left _ _).trans (min_le_left _ _)))
  · intro delta hdelta hdeltaSmall
    exact numeric.refined_edge delta hdelta
      (hdeltaSmall.trans ((min_le_left _ _).trans (min_le_left _ _)))
  · intro delta hdelta hdeltaSmall
    exact numeric.katz delta hdelta
      (hdeltaSmall.trans ((min_le_left _ _).trans (min_le_left _ _)))
  · intro delta hdelta hdeltaSmall
    exact numeric.refined_katz delta hdelta
      (hdeltaSmall.trans ((min_le_left _ _).trans (min_le_left _ _)))
  · intro inputLoss delta logExponent source terminal terminalSource prepared
      window line parents selection residue retained sources band phase anchored
      prep graphParents localCells preparedGraph sharp first ready hinput
      hinputCeiling hdeltaSmall
    exact projection.alternativeA ready hsigma hsigmaOne hworkingLoss
      hworkingSigma hinput
      (hinputCeiling.trans hsourceProjection)
      (hdeltaSmall.trans ((min_le_left _ _).trans (min_le_right _ _)))

structure PureWZ2ReentrantTerminalRuntimeReceipt
    {sigma inputLoss delta outputLoss : ℝ}
    {normalizationExponent : ℕ}
    (schedule : PureWZ2ReentrantTerminalScalarSchedule sigma outputLoss)
    (current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent) where
  owner : PureWZ2ReentrantTerminalOwnerCall current schedule.stickyLoss
  volume :
    ∀ {terminalSource : PureWZ2TerminalPreparedSource
          current.grain owner.toTerminalScaleStickyData}
      {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
      {window : PureWZ2TerminalWindow prepared}
      {line : PureWZ2HorizontalFixedBinCore
        window.windowed current.grain.globalGrains.slope}
      {parents : PureWZ2TerminalFixedBinParentData line}
      {selection : PureWZ2TerminalBinParentYSelection parents}
      {residue : PureWZ2TerminalBinParentYResidueData selection}
      {retained : PureWZ2TerminalBinRetainedShadingData residue}
      {sources : PureWZ2TerminalBinSourceFamily retained}
      {band : PureWZ2TerminalBinFixedBandSelection sources}
      {phase : PureWZ2TerminalBinHeightPhaseSelection band}
      {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
      (prep : PureWZ2TerminalBinExactGraphPreparation anchored),
      Kakeya.realRpowENN delta (1 + sigma / 2 + schedule.volumeLoss) ≤
        MeasureTheory.volume prep.shadow.union
  finalAbsorption :
    ∀ {terminalSource : PureWZ2TerminalPreparedSource
          current.grain owner.toTerminalScaleStickyData}
      (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
      {good : PureWZ2TerminalExactGoodBlockFamilyData
        (eta := schedule.eta) (theoremEta := schedule.theoremEta)
        (outputLoss := schedule.workingLoss) prepared}
      (_data : PureWZ2TerminalExactBlockFamilyData good),
      64 * pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
          pureWZ2TerminalExactHeightRetentionCost delta good.extraLoss *
          Kakeya.realRpowENN delta (sigma + schedule.workingLoss) ≤
        MeasureTheory.volume prepared.shadow.union *
          owner.toTerminalScaleStickyData.sticky.balanced.cellMass *
            pureWZ2TerminalExactRichFloor delta schedule.workingLoss

theorem PureWZ2ReentrantTerminalRuntimeReceipt.toLiftedLeaf
    {sigma inputLoss delta outputLoss : ℝ}
    {normalizationExponent : ℕ}
    {schedule : PureWZ2ReentrantTerminalScalarSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    (hinput : 0 < inputLoss)
    (hinputCeiling : inputLoss ≤ schedule.sourceLossCeiling)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ schedule.delta₀)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (receipt : PureWZ2ReentrantTerminalRuntimeReceipt schedule current) :
    Nonempty (PureWZ2ReentrantTerminalLiftedLeaf
      (outputLoss := schedule.workingLoss) current) := by
  have hCOne : (1 : ENNReal) ≤
      10 * Kakeya.realRpowENN delta (-inputLoss) := by
    have hpower : (1 : ENNReal) ≤
        Kakeya.realRpowENN delta (-inputLoss) := by
      rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num,
        Kakeya.realRpowENN]
      exact ENNReal.ofReal_mono
        (Real.one_le_rpow_of_pos_of_le_one_of_nonpos
          hdelta (hdeltaSmall.trans schedule.delta₀_le_one) (by linarith))
    exact hpower.trans (le_mul_of_one_le_left' (by norm_num))
  rcases pureWZ2_terminalExact_ready_pair_of_certificates
      schedule.sigma_pos schedule.sigma_lt_one hCOne
      (schedule.c_real inputLoss delta hinput hinputCeiling hdelta hdeltaSmall)
      receipt.volume
      (fun preparedGraph =>
        schedule.extra preparedGraph hdelta hdeltaSmall)
      (schedule.edge delta hdelta hdeltaSmall)
      (schedule.refined_edge delta hdelta hdeltaSmall)
      (schedule.katz delta hdelta hdeltaSmall)
      (schedule.refined_katz delta hdelta hdeltaSmall) with
    ⟨readyProducer, refinedProducer⟩
  refine ⟨{
    stickyLoss := schedule.stickyLoss
    eta := schedule.eta
    theoremEta := schedule.theoremEta
    extraLoss := schedule.extraLoss
    owner := receipt.owner
    paperADBridge := hbridge
    budget := schedule.budget inputLoss delta hinput hinputCeiling hdelta hdeltaSmall
    certificates := {
      readyProducer := readyProducer
      refinedProducer := refinedProducer
      alternativeA := ?_ }
    extraCost := ?_
    input_loss_le := hinputCeiling.trans
      (schedule.sourceLossCeiling_working.trans
        (div_le_self schedule.workingLoss_pos.le (by norm_num)))
    finalAbsorption := receipt.finalAbsorption }⟩
  · intro terminalSource prepared window line parents selection residue retained
      sources band phase anchored prep graphParents localCells preparedGraph
      sharp first ready
    exact schedule.alternativeA ready hinput.le hinputCeiling hdeltaSmall
  · intro terminalSource prepared window chain
    exact schedule.extra chain.preparedGraph hdelta hdeltaSmall

theorem PureWZ2ReentrantTerminalRuntimeReceipt.toExactTerminal
    {sigma inputLoss delta outputLoss : ℝ}
    {normalizationExponent : ℕ}
    {schedule : PureWZ2ReentrantTerminalScalarSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    (hinput : 0 < inputLoss)
    (hinputCeiling : inputLoss ≤ schedule.sourceLossCeiling)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ schedule.delta₀)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (receipt : PureWZ2ReentrantTerminalRuntimeReceipt schedule current) :
    Nonempty (PureWZ2ExactTerminalLevelData
      current.grain schedule.workingLoss) := by
  rcases receipt.toLiftedLeaf hinput hinputCeiling hdelta hdeltaSmall hbridge with
    ⟨leaf⟩
  exact leaf.exactTerminal_nonempty

/-- Quantifier-ordered conditional terminal front end.  Scalar losses and
thresholds are selected before the runtime source, which then produces the
source-indexed terminal receipt. -/
def PureWZ2ReentrantTerminalFrontEndAt
    (sigma : ℝ) (normalizationExponent : ℕ) : Prop :=
  ∀ outputLoss : ℝ,
    0 < sigma → sigma < 1 → 0 < outputLoss →
      ∃ schedule : PureWZ2ReentrantTerminalScalarSchedule sigma outputLoss,
        ∀ inputLoss : ℝ,
          0 < inputLoss → inputLoss ≤ schedule.sourceLossCeiling →
          ∀ delta : ℝ, 0 < delta → delta ≤ schedule.delta₀ →
            ∀ current : PureWZ2ReentrantGrainSource
                sigma inputLoss delta normalizationExponent,
              Nonempty
                (PureWZ2ReentrantTerminalRuntimeReceipt schedule current)

theorem pureWZ2_reentrantExactTerminalScaleAt_of_scheduledReceipt
    {sigma : ℝ} {normalizationExponent : ℕ}
    (frontEnd : PureWZ2ReentrantTerminalFrontEndAt
      sigma normalizationExponent)
    (hbridge : PureWZ2PaperADBridgeStatement)
    : PureWZ2ReentrantExactTerminalScaleAtStatement
      sigma normalizationExponent := by
  intro outputLoss hsigma hsigmaOne houtputLoss
  rcases frontEnd outputLoss hsigma hsigmaOne houtputLoss with
    ⟨schedule, produce⟩
  refine ⟨schedule.sourceLossCeiling, schedule.delta₀,
    schedule.sourceLossCeiling_pos, ?_, schedule.delta₀_pos,
    schedule.delta₀_le_one, ?_⟩
  · exact schedule.sourceLossCeiling_working.trans
      (div_le_div_of_nonneg_right schedule.workingLoss_le_output (by norm_num))
  · intro inputLoss hinput hinputCeiling delta hdelta hdeltaSmall current
    rcases produce inputLoss hinput hinputCeiling delta hdelta hdeltaSmall
        current with ⟨receipt⟩
    rcases receipt.toExactTerminal hinput hinputCeiling hdelta hdeltaSmall
        hbridge with
      ⟨terminalWorking⟩
    exact ⟨terminalWorking.mono_loss schedule.workingLoss_le_output⟩

end Kakeya.Assouad

end
