import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalExactVolumeSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalExactAnalyticSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalUniformBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactRefinedReadyGraph

/-!
# Uniform first and refined ready-graph schedule at the terminal scale
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2TerminalExactEdgeThreshold
    (theoremEta volumeLoss constantLoss extraLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  edge : ∀ delta, 0 < delta → delta ≤ delta₀ →
    Real.rpow (wz1Lemma23Theorem22Scale delta) (theoremEta - 3) ≤
      (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
        Real.rpow delta
          (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss)
  refined_edge : ∀ delta, 0 < delta → delta ≤ delta₀ →
    Real.rpow (wz1Lemma23Theorem22Scale (delta / 625))
        (theoremEta - 3) ≤
      (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
        Real.rpow delta
          (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss)
  katzTao : ∀ delta, 0 < delta → delta ≤ delta₀ →
    (4 : ENNReal) ≤ Kakeya.realRpowENN
      (wz1Lemma23Theorem22Scale delta) (-theoremEta)
  refined_katzTao : ∀ delta, 0 < delta → delta ≤ delta₀ →
    (4 : ENNReal) ≤ Kakeya.realRpowENN
      (wz1Lemma23Theorem22Scale (delta / 625)) (-theoremEta)

private theorem pureWZ2_terminal_refined_graph_scale_eq
    {delta : ℝ} (hdelta : 0 ≤ delta) :
    wz1Lemma23Theorem22Scale (delta / 625) =
      wz1Lemma23Theorem22Scale delta / 25 := by
  dsimp only [wz1Lemma23Theorem22Scale]
  rw [Real.sqrt_div hdelta]
  norm_num
  ring

private theorem pureWZ2_terminal_refined_edge_le_half
    {delta theoremEta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (htheoremEta : 0 < theoremEta) (htheoremEtaOne : theoremEta ≤ 1)
    (hsmall : Real.rpow delta (theoremEta / 4) ≤ 1 / 15625) :
    Real.rpow (wz1Lemma23Theorem22Scale (delta / 625))
        (theoremEta - 3) ≤
      Real.rpow (wz1Lemma23Theorem22Scale delta)
        (theoremEta / 2 - 3) := by
  let graph := wz1Lemma23Theorem22Scale delta
  have hgraph : 0 < graph := by
    dsimp only [graph, wz1Lemma23Theorem22Scale]
    positivity
  have hdenom : 1 ≤ 5 * Real.sqrt 3 := by
    have hsqrtThree : 1 ≤ Real.sqrt 3 :=
      (Real.one_le_sqrt).2 (by norm_num)
    nlinarith
  have hgraphRoot : graph ≤ Real.sqrt delta := by
    dsimp only [graph, wz1Lemma23Theorem22Scale]
    exact div_le_self (Real.sqrt_nonneg delta) hdenom
  have hgraphOne : graph ≤ 1 :=
    hgraphRoot.trans (Real.sqrt_le_one.mpr hdeltaOne)
  have hgraphPower : Real.rpow graph (theoremEta / 2) ≤
      Real.rpow delta (theoremEta / 4) := by
    calc
      Real.rpow graph (theoremEta / 2) ≤
          Real.rpow (Real.sqrt delta) (theoremEta / 2) :=
        Real.rpow_le_rpow hgraph.le hgraphRoot (by positivity)
      _ = Real.rpow delta (theoremEta / 4) := by
        rw [Real.sqrt_eq_rpow]
        calc
          (Real.rpow delta (1 / 2)).rpow (theoremEta / 2) =
              Real.rpow delta ((1 / 2) * (theoremEta / 2)) :=
            (Real.rpow_mul hdelta.le (1 / 2) (theoremEta / 2)).symm
          _ = Real.rpow delta (theoremEta / 4) := by
            congr 1
            ring
  have hconstant : Real.rpow 25 (3 - theoremEta) ≤ 15625 := by
    calc
      Real.rpow 25 (3 - theoremEta) ≤ Real.rpow 25 3 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 15625 := by norm_num
  have hfactor :
      Real.rpow 25 (3 - theoremEta) *
          Real.rpow graph (theoremEta / 2) ≤ 1 := by
    calc
      Real.rpow 25 (3 - theoremEta) *
            Real.rpow graph (theoremEta / 2) ≤
          15625 * Real.rpow graph (theoremEta / 2) := by
        gcongr
        exact Real.rpow_nonneg hgraph.le _
      _ ≤ 15625 * (1 / 15625 : ℝ) := by
        gcongr
        exact hgraphPower.trans hsmall
      _ = 1 := by norm_num
  have hrefined : wz1Lemma23Theorem22Scale (delta / 625) = graph / 25 := by
    simpa [graph] using pureWZ2_terminal_refined_graph_scale_eq hdelta.le
  have htwentyFive : 0 < (25 : ℝ) := by norm_num
  have hsplit :
      Real.rpow (graph / 25) (theoremEta - 3) =
        Real.rpow graph (theoremEta / 2 - 3) *
          (Real.rpow 25 (3 - theoremEta) *
            Real.rpow graph (theoremEta / 2)) := by
    calc
      Real.rpow (graph / 25) (theoremEta - 3) =
          Real.rpow graph (theoremEta - 3) /
            Real.rpow 25 (theoremEta - 3) :=
        Real.div_rpow hgraph.le htwentyFive.le _
      _ = Real.rpow graph (theoremEta - 3) *
          (Real.rpow 25 (theoremEta - 3))⁻¹ := by
        rw [div_eq_mul_inv]
      _ = Real.rpow graph (theoremEta - 3) *
          Real.rpow 25 (3 - theoremEta) := by
        congr 1
        calc
          (Real.rpow 25 (theoremEta - 3))⁻¹ =
              Real.rpow 25 (-(theoremEta - 3)) :=
            (Real.rpow_neg htwentyFive.le (theoremEta - 3)).symm
          _ = Real.rpow 25 (3 - theoremEta) := by
            congr 1
            ring
      _ = Real.rpow graph (theoremEta / 2 - 3) *
          (Real.rpow 25 (3 - theoremEta) *
            Real.rpow graph (theoremEta / 2)) := by
        have hgraphSplit : Real.rpow graph (theoremEta - 3) =
            Real.rpow graph (theoremEta / 2 - 3) *
              Real.rpow graph (theoremEta / 2) := by
          calc
            Real.rpow graph (theoremEta - 3) =
                Real.rpow graph
                  ((theoremEta / 2 - 3) + theoremEta / 2) := by
              congr 1
              ring
            _ = Real.rpow graph (theoremEta / 2 - 3) *
                Real.rpow graph (theoremEta / 2) :=
              Real.rpow_add hgraph _ _
        rw [hgraphSplit]
        ring
  rw [hrefined, hsplit]
  exact mul_le_of_le_one_right
    (Real.rpow_nonneg hgraph.le _) hfactor

theorem pureWZ2_terminalExact_edge_threshold
    {theoremEta volumeLoss constantLoss extraLoss : ℝ}
    (htheoremEta : 0 < theoremEta)
    (htheoremEtaOne : theoremEta ≤ 1)
    (hbudget :
      8 * ((volumeLoss + extraLoss) + constantLoss) < theoremEta / 2) :
    Nonempty (PureWZ2TerminalExactEdgeThreshold
      theoremEta volumeLoss constantLoss extraLoss) := by
  rcases wz1_lemma23_theorem22_absorption
      (theoremEta / 2) (volumeLoss + extraLoss) constantLoss
      (by positivity) hbudget with
    ⟨edgeDelta₀, hedgeDelta₀, hedgeDelta₀One, hedge⟩
  rcases wz1_lemma23_katzTao_constant_absorption theoremEta htheoremEta with
    ⟨katzDelta₀, hkatzDelta₀, hkatzDelta₀One, hkatz⟩
  rcases exists_delta_rpow_le_single (theoremEta / 4) (1 / 15625)
      (by positivity) (by norm_num) (by norm_num) with
    ⟨refinedDelta₀, hrefinedDelta₀, hrefinedDelta₀One, hrefined⟩
  let delta₀ := min edgeDelta₀ (min katzDelta₀ refinedDelta₀)
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min hedgeDelta₀ (lt_min hkatzDelta₀ hrefinedDelta₀)
    delta₀_le_one := (min_le_left _ _).trans hedgeDelta₀One
    edge := ?_
    refined_edge := ?_
    katzTao := ?_
    refined_katzTao := ?_ }⟩
  · intro delta hdelta hdeltaSmall
    have hhalf := (hedge delta hdelta
      (hdeltaSmall.trans (min_le_left _ _))).edge
    have hgraphOne : wz1Lemma23Theorem22Scale delta ≤ 1 := by
      dsimp only [wz1Lemma23Theorem22Scale]
      have hroot := Real.sqrt_le_one.mpr
        (hdeltaSmall.trans ((min_le_left _ _).trans hedgeDelta₀One))
      have hdenom : 1 ≤ 5 * Real.sqrt 3 := by
        have hsqrtThree : 1 ≤ Real.sqrt 3 :=
          (Real.one_le_sqrt).2 (by norm_num)
        nlinarith
      exact (div_le_self (Real.sqrt_nonneg delta) hdenom).trans hroot
    have hmono :
        Real.rpow (wz1Lemma23Theorem22Scale delta) (theoremEta - 3) ≤
          Real.rpow (wz1Lemma23Theorem22Scale delta)
            (theoremEta / 2 - 3) :=
      Real.rpow_le_rpow_of_exponent_ge
        (by dsimp [wz1Lemma23Theorem22Scale]; positivity)
        hgraphOne (by linarith)
    simpa only [show
      -3 / 2 + 4 * (volumeLoss + extraLoss) + 4 * constantLoss =
        -3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss by ring]
      using hmono.trans hhalf
  · intro delta hdelta hdeltaSmall
    have hdeltaOne : delta ≤ 1 :=
      hdeltaSmall.trans ((min_le_left _ _).trans hedgeDelta₀One)
    have hcompare := pureWZ2_terminal_refined_edge_le_half
      hdelta hdeltaOne htheoremEta htheoremEtaOne
      (hrefined delta hdelta
        (hdeltaSmall.trans ((min_le_right _ _).trans (min_le_right _ _))))
    have hhalf := (hedge delta hdelta
      (hdeltaSmall.trans (min_le_left _ _))).edge
    simpa only [show
      -3 / 2 + 4 * (volumeLoss + extraLoss) + 4 * constantLoss =
        -3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss by ring]
      using hcompare.trans hhalf
  · intro delta hdelta hdeltaSmall
    exact hkatz delta hdelta
      (hdeltaSmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  · intro delta hdelta hdeltaSmall
    apply hkatz (delta / 625) (by positivity)
    calc
      delta / 625 ≤ delta := by
        exact div_le_self hdelta.le (by norm_num)
      _ ≤ katzDelta₀ :=
        hdeltaSmall.trans ((min_le_right _ _).trans (min_le_left _ _))

theorem PureWZ2TerminalExactReadyGraph.refine_of_certificates
    {sigma inputLoss delta stickyLoss eta theoremEta
      volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
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
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
    (first : PureWZ2TerminalExactReadyGraph
      (theoremEta := theoremEta) sharp)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCOne : (1 : ENNReal) ≤
      10 * Kakeya.realRpowENN delta (-inputLoss))
    (hCpower :
      (10 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
        Real.rpow delta (-constantLoss))
    (hvolume : Kakeya.realRpowENN delta
        (1 + sigma / 2 + volumeLoss) ≤
      MeasureTheory.volume prep.shadow.union)
    (hextraPower : (preparedGraph.graph.residue.extraCost : ℝ) ≤
      Real.rpow delta (-extraLoss))
    (hRefinedEdge :
      Real.rpow (wz1Lemma23Theorem22Scale (delta / 625))
          (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow delta
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss))
    (hRefinedKatzTao : (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale (delta / 625)) (-theoremEta)) :
    Nonempty (PureWZ2TerminalExactRefinedReadyGraph first) := by
  have hcoord : ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hambient := prep.subshading.union_subset hpoint
    have hpaper : point ∈ retained.shading.union := by
      rwa [prep.ambient_union] at hambient
    have hbox := shading_union_subset_axisBox hpaper
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  let C : ENNReal := 10 * Kakeya.realRpowENN delta (-inputLoss)
  have hCtop : C ≠ ⊤ := ENNReal.mul_ne_top (by norm_num)
    (by simp [Kakeya.realRpowENN])
  have hedgeReal :
      Real.rpow (wz1Lemma23Theorem22Scale (delta / 625))
          (theoremEta - 3) ≤
        (sharp.sharp.normalized.H.card : ℝ) := by
    apply hRefinedEdge.trans
    exact sharp.sharp.power_edge_bound_of_coord
      source.extremal.delta_le_one hsigma hsigmaOne hcoord
      hCOne hCtop volumeLoss constantLoss extraLoss
      (by simpa [Kakeya.realRpowENN] using hvolume)
      hCpower hextraPower
  have hedgeNormalized :
      Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale (delta / 625))
          (theoremEta - 3) ≤
        (sharp.sharp.normalized.H.card : ENNReal) := by
    rw [Kakeya.realRpowENN]
    have hcast : (sharp.sharp.normalized.H.card : ENNReal) =
        ENNReal.ofReal (sharp.sharp.normalized.H.card : ℝ) := by
      norm_cast
    rw [hcast]
    exact ENNReal.ofReal_le_ofReal hedgeReal
  have hedgeCommon :
      Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale (delta / 625))
          (theoremEta - 3) ≤
        (first.common.H.card : ENNReal) := by
    rw [first.common.edge_card]
    exact hedgeNormalized
  exact first.refineForExactTrapezoid hedgeCommon hRefinedKatzTao

theorem pureWZ2_terminalExact_ready_pair_of_certificates
    {sigma inputLoss delta stickyLoss eta theoremEta
      volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCOne : (1 : ENNReal) ≤
      10 * Kakeya.realRpowENN delta (-inputLoss))
    (hCpower :
      (10 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
        Real.rpow delta (-constantLoss))
    (hvolume : ∀
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
        (prep : PureWZ2TerminalBinExactGraphPreparation anchored),
      Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) ≤
        MeasureTheory.volume prep.shadow.union)
    (hextra : ∀
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
      (preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow delta (-extraLoss))
    (hedge :
      Real.rpow (wz1Lemma23Theorem22Scale delta) (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow delta
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss))
    (hrefinedEdge :
      Real.rpow (wz1Lemma23Theorem22Scale (delta / 625))
          (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow delta
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss))
    (hkatz : (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale delta) (-theoremEta))
    (hrefinedKatz : (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale (delta / 625)) (-theoremEta)) :
    (∀
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
      {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
      (sharp : PureWZ2TerminalExactSharpGeometry preparedGraph),
        Nonempty (PureWZ2TerminalExactReadyGraph
          (theoremEta := theoremEta) sharp)) ∧
    (∀
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
      {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
      {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
      (first : PureWZ2TerminalExactReadyGraph
        (theoremEta := theoremEta) sharp),
        Nonempty (PureWZ2TerminalExactRefinedReadyGraph first)) := by
  constructor
  · intro terminalSource prepared window line parents selection residue retained
      sources band phase anchored prep graphParents localCells preparedGraph sharp
    exact sharp.toReadyGraph hsigma hsigmaOne hCOne hCpower
      (by simpa [Kakeya.realRpowENN] using hvolume prep)
      (hextra preparedGraph) hedge hkatz
  · intro terminalSource prepared window line parents selection residue retained
      sources band phase anchored prep graphParents localCells preparedGraph sharp first
    exact first.refine_of_certificates hsigma hsigmaOne hCOne hCpower
      (hvolume prep) (hextra preparedGraph) hrefinedEdge hrefinedKatz

end Kakeya.Assouad

end
