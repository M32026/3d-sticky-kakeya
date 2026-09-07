import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalChainNumericSchedule

/-!
# Scheduled exact-terminal chain on one graph window

This is the numerical wrapper used after the paper's source-volume height
popularity step.  Its volume premise concerns the actual dependent graph
produced from the supplied window; it does not require the window to retain a
fixed fraction of the earlier ambient window.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- Run the complete exact-terminal chain on one fixed graph window. -/
theorem pureWZ2_terminal_window_chain_of_numerical_certificates
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss
      volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (window : PureWZ2TerminalWindow prepared)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (budget : PureWZ2TerminalChainBudget
      sigma inputLoss delta stickyLoss eta theoremEta outputLoss)
    (hCOne : (1 : ENNReal) ≤
      10 * Kakeya.realRpowENN delta (-inputLoss))
    (hCpower :
      (10 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
        Real.rpow delta (-constantLoss))
    (hvolume : ∀
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
      (prep : PureWZ2TerminalExactGraphPreparation anchored),
        Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) ≤
          MeasureTheory.volume prep.shadow.union)
    (hextra : ∀
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
        (wz1Lemma23Theorem22Scale (delta / 625)) (-theoremEta))
    (alternativeA : ∀
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
        WZ1Proposition8_9AlternativeAUnion
          ready.ready.deltaGraph outputLoss
          ready.common.F ready.common.G₁ ready.common.G₁) :
    Nonempty (PureWZ2TerminalWindowChainOutput
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) window) := by
  rcases window.selectHorizontalFixedLine with ⟨line⟩
  rcases line.toTerminalParents with ⟨parents⟩
  rcases parents.selectOnePerY with ⟨selection⟩
  rcases selection.selectResidue with ⟨residue⟩
  rcases residue.retainSourceShading with ⟨retained⟩
  rcases retained.sources with ⟨sources⟩
  rcases sources.selectFixedBand with ⟨band⟩
  rcases band.selectHeightPhase with ⟨phase⟩
  rcases phase.anchorPieces with ⟨anchored⟩
  rcases anchored.prepareExactGraph hbridge with ⟨prep⟩
  rcases prep.graphParents with ⟨graphParents⟩
  have hsourceVolume :
      (512 : ENNReal) * (2 * 512 * 57) *
          Kakeya.realRpowENN delta (3 / 2 + sigma / 2 + eta) ≤
        terminal.sticky.balanced.cellMass :=
    budget.source_volume.trans terminal.source_floor_power
  rcases graphParents.localCells budget.sigma_pos budget.sigma_lt_one
      budget.eta_pos budget.eta_sigma budget.c_power budget.planar
      budget.root budget.localization hsourceVolume with ⟨localCells⟩
  rcases localCells.prepareGraph with ⟨preparedGraph⟩
  rcases preparedGraph.toSharpGeometry with ⟨sharp⟩
  rcases sharp.toReadyGraph budget.sigma_pos budget.sigma_lt_one hCOne hCpower
      (by simpa [Kakeya.realRpowENN] using hvolume prep)
      (hextra preparedGraph) hedge hkatz with ⟨first⟩
  rcases first.refine_of_certificates budget.sigma_pos budget.sigma_lt_one
      hCOne hCpower (hvolume prep) (hextra preparedGraph)
      hrefinedEdge hrefinedKatz with ⟨ready⟩
  rcases ready.alternativeAHeights (alternativeA ready) with ⟨rich⟩
  rcases rich.toRichHeightCells with ⟨weighted⟩
  rcases weighted.toWeightedTrapezoid budget.scale_one
      budget.length_lower with ⟨trapezoid⟩
  rcases weighted.toExactRichSetTrapezoid budget.output_pos with
    ⟨exactTrapezoid⟩
  exact ⟨{
    line := line
    parents := parents
    selection := selection
    residue := residue
    retained := retained
    sources := sources
    band := band
    phase := phase
    anchored := anchored
    prep := prep
    graphParents := graphParents
    localCells := localCells
    preparedGraph := preparedGraph
    sharp := sharp
    first := first
    ready := ready
    rich := rich
    weighted := weighted
    trapezoid := trapezoid
    exactTrapezoid := exactTrapezoid }⟩

end Kakeya.Assouad

end
