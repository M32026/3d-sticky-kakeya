import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalChainAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalExactReadySchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalExactProjectionSchedule

/-!
# Uniform numerical schedule for the terminal dependent chain
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2TerminalChainGeometricThreshold
    (sigma inputLoss stickyLoss eta theoremEta outputLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  budget : ∀ delta, 0 < delta → delta ≤ delta₀ →
    (10 * Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-eta)) →
    PureWZ2TerminalChainBudget
      sigma inputLoss delta stickyLoss eta theoremEta outputLoss

theorem pureWZ2_terminal_chain_geometric_threshold
    {sigma inputLoss stickyLoss eta theoremEta outputLoss : ℝ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hsticky : 0 < stickyLoss)
    (heta : 0 < eta)
    (hetaSigma : 4 * eta < sigma)
    (hetaSigmaEight : 8 * eta < sigma)
    (hstickyEta : 3 * stickyLoss / 2 < eta)
    (houtput : 0 < outputLoss) (houtputOne : outputLoss < 1)
    (houtputSigma : outputLoss / 2 < sigma) :
    Nonempty (PureWZ2TerminalChainGeometricThreshold
      sigma inputLoss stickyLoss eta theoremEta outputLoss) := by
  rcases exists_delta_rpow_le_single eta (1 / 32)
      heta (by norm_num) (by norm_num) with
    ⟨planarDelta₀, hplanarDelta₀, hplanarDelta₀One, hplanar⟩
  rcases exists_delta_rpow_le_single (1 / 2 : ℝ) (1 / 20)
      (by norm_num) (by norm_num) (by norm_num) with
    ⟨rootDelta₀, hrootDelta₀, hrootDelta₀One, hroot⟩
  let localExp := 1 / 2 - 4 * eta / sigma
  have hlocalExp : 0 < localExp := by
    dsimp only [localExp]
    rw [sub_pos, div_lt_iff₀ hsigma]
    nlinarith [hetaSigmaEight]
  rcases exists_delta_rpow_le_single localExp (1 / 14)
      hlocalExp (by norm_num) (by norm_num) with
    ⟨localDelta₀, hlocalDelta₀, hlocalDelta₀One, hlocal⟩
  let sourceConstant : ℝ := 512 * (2 * 512 * 57)
  rcases exists_delta₀_const_mul_rpow_le sourceConstant
      (by norm_num [sourceConstant])
      (3 / 2 + sigma / 2 + 3 * stickyLoss / 2)
      (3 / 2 + sigma / 2 + eta) (by linarith) with
    ⟨sourceDelta₀, hsourceDelta₀, hsourceDelta₀One, hsource⟩
  rcases exists_delta_rpow_le_single outputLoss (1 / 6)
      houtput (by norm_num) (by norm_num) with
    ⟨lengthDelta₀, hlengthDelta₀, hlengthDelta₀One, hlength⟩
  let delta₀ := min (1 / 6 : ℝ)
    (min planarDelta₀ (min rootDelta₀
      (min localDelta₀ (min sourceDelta₀ (lengthDelta₀ / 6)))))
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    exact lt_min (by norm_num)
      (lt_min hplanarDelta₀
        (lt_min hrootDelta₀
          (lt_min hlocalDelta₀
            (lt_min hsourceDelta₀ (div_pos hlengthDelta₀ (by norm_num))))))
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans (by norm_num)
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := hdelta₀
    delta₀_le_one := hdelta₀One
    budget := ?_ }⟩
  intro delta hdelta hdeltaSmall hcPower
  have hdeltaSixth : delta ≤ 1 / 6 :=
    hdeltaSmall.trans (min_le_left _ _)
  have hrest : delta ≤ min planarDelta₀ (min rootDelta₀
      (min localDelta₀ (min sourceDelta₀ (lengthDelta₀ / 6)))) :=
    hdeltaSmall.trans (min_le_right _ _)
  have hdeltaPlanar : delta ≤ planarDelta₀ := hrest.trans (min_le_left _ _)
  have hdeltaRoot : delta ≤ rootDelta₀ :=
    hrest.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaLocal : delta ≤ localDelta₀ :=
    hrest.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hdeltaSource : delta ≤ sourceDelta₀ :=
    hrest.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hdeltaLength : delta ≤ lengthDelta₀ / 6 :=
    hrest.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hplanarSmall : 32 * Real.rpow delta eta ≤ 1 := by
    have hp := hplanar delta hdelta hdeltaPlanar
    nlinarith
  have hrootSmall : 20 * Real.sqrt delta ≤ 1 := by
    have hp := hroot delta hdelta hdeltaRoot
    have hsqrtEq : Real.rpow delta (1 / 2 : ℝ) = Real.sqrt delta :=
      (Real.sqrt_eq_rpow delta).symm
    rw [hsqrtEq] at hp
    nlinarith
  have hlocalSmall : Real.rpow delta (1 - 4 * eta / sigma) ≤
      Real.sqrt delta / 14 := by
    have hp := hlocal delta hdelta hdeltaLocal
    have hsplit : Real.rpow delta (1 - 4 * eta / sigma) =
        Real.sqrt delta * Real.rpow delta localExp := by
      calc
        Real.rpow delta (1 - 4 * eta / sigma) =
            Real.rpow delta ((1 / 2 : ℝ) + localExp) := by
          congr 1
          dsimp only [localExp]
          ring
        _ = Real.rpow delta (1 / 2 : ℝ) *
            Real.rpow delta localExp := Real.rpow_add hdelta _ _
        _ = Real.sqrt delta * Real.rpow delta localExp := by
          have hsqrtEq : Real.rpow delta (1 / 2 : ℝ) = Real.sqrt delta :=
            (Real.sqrt_eq_rpow delta).symm
          rw [hsqrtEq]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg delta) |>.trans_eq
      (by ring)
  have hsourceSmall :
      (512 : ENNReal) * (2 * 512 * 57) *
          Kakeya.realRpowENN delta (3 / 2 + sigma / 2 + eta) ≤
        Kakeya.realRpowENN delta
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) := by
    simpa [sourceConstant, mul_assoc] using hsource delta hdelta hdeltaSource
  have hscaleOne : 6 * delta ≤ 1 := by linarith
  have hscaled : 6 * delta ≤ lengthDelta₀ := by linarith
  have hp := hlength (6 * delta) (by positivity) hscaled
  have hsplitLength : Real.rpow (6 * delta) (1 / 2 + outputLoss) =
      Real.sqrt (6 * delta) * Real.rpow (6 * delta) outputLoss := by
    calc
      Real.rpow (6 * delta) (1 / 2 + outputLoss) =
          Real.rpow (6 * delta) (1 / 2 : ℝ) *
            Real.rpow (6 * delta) outputLoss :=
        Real.rpow_add (by positivity) _ _
      _ = Real.sqrt (6 * delta) * Real.rpow (6 * delta) outputLoss := by
        have hsqrtEq : Real.rpow (6 * delta) (1 / 2 : ℝ) =
            Real.sqrt (6 * delta) := (Real.sqrt_eq_rpow (6 * delta)).symm
        rw [hsqrtEq]
  have hsqrtScale : Real.sqrt (6 * delta) / 6 ≤ Real.sqrt delta := by
    have hleft := Real.sq_sqrt (by positivity : 0 ≤ 6 * delta)
    have hright := Real.sq_sqrt hdelta.le
    have hnonnegLeft : 0 ≤ Real.sqrt (6 * delta) / 6 := by positivity
    have hnonnegRight : 0 ≤ Real.sqrt delta := Real.sqrt_nonneg delta
    nlinarith
  have hlengthSmall :
      Real.rpow (6 * delta) (1 / 2 + outputLoss) ≤ Real.sqrt delta := by
    rw [hsplitLength]
    calc
      Real.sqrt (6 * delta) * Real.rpow (6 * delta) outputLoss ≤
          Real.sqrt (6 * delta) * (1 / 6) := by gcongr
      _ = Real.sqrt (6 * delta) / 6 := by ring
      _ ≤ Real.sqrt delta := hsqrtScale
  exact {
    sigma_pos := hsigma
    sigma_lt_one := hsigmaOne
    eta_pos := heta
    eta_sigma := hetaSigma
    output_pos := houtput
    output_lt_one := houtputOne
    output_sigma := houtputSigma
    c_power := hcPower
    planar := hplanarSmall
    root := hrootSmall
    localization := hlocalSmall
    source_volume := hsourceSmall
    scale_one := hscaleOne
    length_lower := hlengthSmall }

structure PureWZ2TerminalChainNumericThreshold
    (sigma inputLoss stickyLoss eta theoremEta outputLoss
      volumeLoss constantLoss extraLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  c_power : ∀ delta, 0 < delta → delta ≤ delta₀ →
    10 * Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-eta)
  c_real : ∀ delta, 0 < delta → delta ≤ delta₀ →
    (10 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
      Real.rpow delta (-constantLoss)
  volume_budget : ∀ delta, 0 < delta → delta ≤ delta₀ →
    Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) *
        pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≤
      (16 : ENNReal)⁻¹ * Kakeya.realRpowENN delta
        (2 + 3 * sigma / 2 + 5 * stickyLoss / 2)
  extra : ∀ delta, 0 < delta → delta ≤ delta₀ →
    ∀ {logExponent : ℕ}
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
      (preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells),
      (preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow delta (-extraLoss)
  edge : ∀ delta, 0 < delta → delta ≤ delta₀ →
    Real.rpow (wz1Lemma23Theorem22Scale delta) (theoremEta - 3) ≤
      (wz1Lemma23EdgeConstant : ℝ)⁻¹ * Real.rpow delta
        (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss)
  refined_edge : ∀ delta, 0 < delta → delta ≤ delta₀ →
    Real.rpow (wz1Lemma23Theorem22Scale (delta / 625))
        (theoremEta - 3) ≤
      (wz1Lemma23EdgeConstant : ℝ)⁻¹ * Real.rpow delta
        (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss)
  katz : ∀ delta, 0 < delta → delta ≤ delta₀ →
    (4 : ENNReal) ≤ Kakeya.realRpowENN
      (wz1Lemma23Theorem22Scale delta) (-theoremEta)
  refined_katz : ∀ delta, 0 < delta → delta ≤ delta₀ →
    (4 : ENNReal) ≤ Kakeya.realRpowENN
      (wz1Lemma23Theorem22Scale (delta / 625)) (-theoremEta)
  chain_budget : ∀ delta, 0 < delta → delta ≤ delta₀ →
    PureWZ2TerminalChainBudget
      sigma inputLoss delta stickyLoss eta theoremEta outputLoss

theorem pureWZ2_terminal_chain_numeric_threshold
    {sigma inputLoss stickyLoss eta theoremEta outputLoss
      volumeLoss constantLoss extraLoss : ℝ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hinput : 0 < inputLoss)
    (hsticky : 0 < stickyLoss)
    (heta : 0 < eta)
    (hetaSigma : 4 * eta < sigma)
    (hetaSigmaEight : 8 * eta < sigma)
    (hinputEta : inputLoss < eta)
    (hinputConstant : inputLoss < constantLoss)
    (hvolumeLoss : 0 < volumeLoss)
    (hconstantLoss : 0 < constantLoss)
    (hextraLoss : 0 < extraLoss)
    (hstickyEta : 3 * stickyLoss / 2 < eta)
    (hvolumeGap : inputLoss + 5 * stickyLoss / 2 < volumeLoss)
    (htheoremEta : 0 < theoremEta) (htheoremEtaOne : theoremEta ≤ 1)
    (houtput : 0 < outputLoss) (houtputOne : outputLoss < 1)
    (houtputSigma : outputLoss / 2 < sigma)
    (hedgeBudget :
      8 * ((volumeLoss + extraLoss) + constantLoss) < theoremEta / 2) :
    Nonempty (PureWZ2TerminalChainNumericThreshold
      sigma inputLoss stickyLoss eta theoremEta outputLoss
        volumeLoss constantLoss extraLoss) := by
  rcases exists_scale_absorb_constant (10 : ENNReal) (by norm_num)
      hinput.le hinputEta with
    ⟨cDelta₀, hcDelta₀, hcDelta₀One, hc⟩
  rcases exists_scale_absorb_constant (10 : ENNReal) (by norm_num)
      hinput.le hinputConstant with
    ⟨realDelta₀, hrealDelta₀, hrealDelta₀One, hreal⟩
  rcases pureWZ2_terminalExact_volume_budget_schedule hvolumeGap with
    ⟨volumeDelta₀, hvolumeDelta₀, hvolumeDelta₀One, hvolume⟩
  rcases pureWZ2_terminalExact_extraCost_schedule (extraLoss := extraLoss)
      hextraLoss with
    ⟨extraDelta₀, hextraDelta₀, hextraDelta₀One, hextra⟩
  rcases pureWZ2_terminalExact_edge_threshold htheoremEta htheoremEtaOne
      hedgeBudget with ⟨edge⟩
  rcases pureWZ2_terminal_chain_geometric_threshold
      (inputLoss := inputLoss) (theoremEta := theoremEta)
      hsigma hsigmaOne hsticky heta hetaSigma hetaSigmaEight
      hstickyEta houtput houtputOne houtputSigma with ⟨geometric⟩
  let analyticDelta₀ := min cDelta₀
    (min realDelta₀ (min volumeDelta₀ (min extraDelta₀ edge.delta₀)))
  let delta₀ := min analyticDelta₀ geometric.delta₀
  have hanalyticDelta₀ : 0 < analyticDelta₀ := by
    dsimp only [analyticDelta₀]
    exact lt_min hcDelta₀
      (lt_min hrealDelta₀
        (lt_min hvolumeDelta₀ (lt_min hextraDelta₀ edge.delta₀_pos)))
  have hdelta₀ : 0 < delta₀ := by
    exact lt_min hanalyticDelta₀ geometric.delta₀_pos
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans ((min_le_left _ _).trans hcDelta₀One)
  have hdeltaAnalytic : delta₀ ≤ analyticDelta₀ := min_le_left _ _
  have hdeltaGeometric : delta₀ ≤ geometric.delta₀ := min_le_right _ _
  have hdeltaC : delta₀ ≤ cDelta₀ :=
    hdeltaAnalytic.trans (min_le_left _ _)
  have hdeltaReal : delta₀ ≤ realDelta₀ :=
    hdeltaAnalytic.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaVolume : delta₀ ≤ volumeDelta₀ :=
    hdeltaAnalytic.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hdeltaExtra : delta₀ ≤ extraDelta₀ :=
    hdeltaAnalytic.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hdeltaEdge : delta₀ ≤ edge.delta₀ :=
    hdeltaAnalytic.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := hdelta₀
    delta₀_le_one := hdelta₀One
    c_power := ?_
    c_real := ?_
    volume_budget := ?_
    extra := ?_
    edge := ?_
    refined_edge := ?_
    katz := ?_
    refined_katz := ?_
    chain_budget := ?_ }⟩
  · intro delta hdelta hdeltaSmall
    exact hc delta hdelta (hdeltaSmall.trans hdeltaC)
  · intro delta hdelta hdeltaSmall
    have hENN := hreal delta hdelta
      (hdeltaSmall.trans hdeltaReal)
    have hrightTop : Kakeya.realRpowENN delta (-constantLoss) ≠ ⊤ := by
      simp [Kakeya.realRpowENN]
    have htoReal := ENNReal.toReal_mono hrightTop hENN
    simpa [Kakeya.realRpowENN,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hdelta.le _)] using htoReal
  · intro delta hdelta hdeltaSmall
    exact hvolume hdelta
      (hdeltaSmall.trans hdeltaVolume)
  · intro delta hdelta hdeltaSmall logExponent source terminal terminalSource
      prepared window line parents selection residue retained sources band phase
      anchored prep graphParents localCells preparedGraph
    exact hextra preparedGraph hdelta
      (hdeltaSmall.trans hdeltaExtra)
  · intro delta hdelta hdeltaSmall
    exact edge.edge delta hdelta
      (hdeltaSmall.trans hdeltaEdge)
  · intro delta hdelta hdeltaSmall
    exact edge.refined_edge delta hdelta
      (hdeltaSmall.trans hdeltaEdge)
  · intro delta hdelta hdeltaSmall
    exact edge.katzTao delta hdelta
      (hdeltaSmall.trans hdeltaEdge)
  · intro delta hdelta hdeltaSmall
    exact edge.refined_katzTao delta hdelta
      (hdeltaSmall.trans hdeltaEdge)
  · intro delta hdelta hdeltaSmall
    exact geometric.budget delta hdelta
      (hdeltaSmall.trans hdeltaGeometric)
      (hc delta hdelta (hdeltaSmall.trans hdeltaC))

end Kakeya.Assouad

end
