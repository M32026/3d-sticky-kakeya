import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactWeightedOneScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactRichSetTrapezoid
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.BoundedGridLogCost

/-!
# Dependent assembly of the exact terminal chain

This module performs all choice-dependent geometry from one terminal sticky
output through the weighted terminal trapezoid.  The outer schedule supplies
only the explicit numerical certificates below.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2TerminalChainBudget
    (sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ) where
  sigma_pos : 0 < sigma
  sigma_lt_one : sigma < 1
  eta_pos : 0 < eta
  eta_sigma : 4 * eta < sigma
  output_pos : 0 < outputLoss
  output_lt_one : outputLoss < 1
  output_sigma : outputLoss / 2 < sigma
  c_power :
    10 * Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-eta)
  planar : 32 * Real.rpow delta eta ≤ 1
  root : 20 * Real.sqrt delta ≤ 1
  localization :
    Real.rpow delta (1 - 4 * eta / sigma) ≤ Real.sqrt delta / 14
  source_volume :
    (512 : ENNReal) * (2 * 512 * 57) *
        Kakeya.realRpowENN delta (3 / 2 + sigma / 2 + eta) ≤
      Kakeya.realRpowENN delta
        (3 / 2 + sigma / 2 + 3 * stickyLoss / 2)
  scale_one : 6 * delta ≤ 1
  length_lower :
    Real.rpow (6 * delta) (1 / 2 + outputLoss) ≤ Real.sqrt delta

structure PureWZ2TerminalChainOutput
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (terminal : PureWZ2TerminalScaleStickyData
      source stickyLoss logExponent) where
  terminalSource : PureWZ2TerminalPreparedSource source terminal
  prepared : PureWZ2TerminalLemma23Prepared terminalSource
  window : PureWZ2TerminalWindow prepared
  line : PureWZ2HorizontalFixedLineCore
    window.windowed source.globalGrains.slope
  parents : PureWZ2TerminalFixedLineParentData line
  selection : PureWZ2TerminalParentYSelection parents
  residue : PureWZ2TerminalParentYResidueData selection
  retained : PureWZ2TerminalRetainedShadingData residue
  sources : PureWZ2TerminalSourceFamily retained
  band : PureWZ2TerminalFixedBandSelection sources
  phase : PureWZ2TerminalHeightPhaseSelection band
  anchored : PureWZ2TerminalAnchoredPieceData phase
  prep : PureWZ2TerminalExactGraphPreparation anchored
  graphParents : PureWZ2TerminalExactGraphParentData prep
  localCells : PureWZ2TerminalExactLocalCellData (eta := eta) graphParents
  preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells
  sharp : PureWZ2TerminalExactSharpGeometry preparedGraph
  first : PureWZ2TerminalExactReadyGraph
    (theoremEta := theoremEta) sharp
  ready : PureWZ2TerminalExactRefinedReadyGraph first
  rich : PureWZ2TerminalExactAlternativeAHeightData ready outputLoss
  weighted : PureWZ2TerminalExactRichHeightCellData rich
  trapezoid : PureWZ2TerminalExactWeightedTrapezoid weighted
  exactTrapezoid : PureWZ2TerminalExactRichSetTrapezoid weighted

/-- The three graph-facing certificates shared by every terminal window on
one fixed source configuration. -/
structure PureWZ2TerminalChainCertificates
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (eta theoremEta outputLoss : ℝ)
    (terminal : PureWZ2TerminalScaleStickyData
      source stickyLoss logExponent) where
  readyProducer :
    ∀ {terminalSource : PureWZ2TerminalPreparedSource source terminal}
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
      (sharp : PureWZ2TerminalExactSharpGeometry preparedGraph),
      Nonempty (PureWZ2TerminalExactReadyGraph
        (theoremEta := theoremEta) sharp)
  refinedProducer :
    ∀ {terminalSource : PureWZ2TerminalPreparedSource source terminal}
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
      (first : PureWZ2TerminalExactReadyGraph
        (theoremEta := theoremEta) sharp),
      Nonempty (PureWZ2TerminalExactRefinedReadyGraph first)
  alternativeA :
    ∀ {terminalSource : PureWZ2TerminalPreparedSource source terminal}
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
      WZ1Proposition8_9AlternativeAUnion
        ready.ready.deltaGraph outputLoss
        ready.common.F ready.common.G₁ ready.common.G₁

/-- All choice-dependent terminal output after a caller-specified window. -/
structure PureWZ2TerminalWindowChainOutput
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (window : PureWZ2TerminalWindow prepared) where
  line : PureWZ2HorizontalFixedLineCore
    window.windowed source.globalGrains.slope
  parents : PureWZ2TerminalFixedLineParentData line
  selection : PureWZ2TerminalParentYSelection parents
  residue : PureWZ2TerminalParentYResidueData selection
  retained : PureWZ2TerminalRetainedShadingData residue
  sources : PureWZ2TerminalSourceFamily retained
  band : PureWZ2TerminalFixedBandSelection sources
  phase : PureWZ2TerminalHeightPhaseSelection band
  anchored : PureWZ2TerminalAnchoredPieceData phase
  prep : PureWZ2TerminalExactGraphPreparation anchored
  graphParents : PureWZ2TerminalExactGraphParentData prep
  localCells : PureWZ2TerminalExactLocalCellData (eta := eta) graphParents
  preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells
  sharp : PureWZ2TerminalExactSharpGeometry preparedGraph
  first : PureWZ2TerminalExactReadyGraph
    (theoremEta := theoremEta) sharp
  ready : PureWZ2TerminalExactRefinedReadyGraph first
  rich : PureWZ2TerminalExactAlternativeAHeightData ready outputLoss
  weighted : PureWZ2TerminalExactRichHeightCellData rich
  trapezoid : PureWZ2TerminalExactWeightedTrapezoid weighted
  exactTrapezoid : PureWZ2TerminalExactRichSetTrapezoid weighted

/-- Run the complete dependent chain from one fixed terminal window. -/
theorem pureWZ2_terminal_window_chain_of_certificates
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (window : PureWZ2TerminalWindow prepared)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (budget : PureWZ2TerminalChainBudget
      sigma inputLoss delta stickyLoss eta theoremEta outputLoss)
    (certificates : PureWZ2TerminalChainCertificates
      eta theoremEta outputLoss terminal) :
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
  rcases certificates.readyProducer sharp with ⟨first⟩
  rcases certificates.refinedProducer first with ⟨ready⟩
  rcases ready.alternativeAHeights (certificates.alternativeA ready) with ⟨rich⟩
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

/-- Assemble every geometric choice once the ready-graph and projection
certificates have been supplied for the resulting dependent graph. -/
theorem pureWZ2_terminal_chain_of_certificates
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (terminal : PureWZ2TerminalScaleStickyData
      source stickyLoss logExponent)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (budget : PureWZ2TerminalChainBudget
      sigma inputLoss delta stickyLoss eta theoremEta outputLoss)
    (readyProducer :
      ∀ {terminalSource : PureWZ2TerminalPreparedSource source terminal}
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
        (sharp : PureWZ2TerminalExactSharpGeometry preparedGraph),
        Nonempty (PureWZ2TerminalExactReadyGraph
          (theoremEta := theoremEta) sharp))
    (refinedProducer :
      ∀ {terminalSource : PureWZ2TerminalPreparedSource source terminal}
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
        (first : PureWZ2TerminalExactReadyGraph
          (theoremEta := theoremEta) sharp),
        Nonempty (PureWZ2TerminalExactRefinedReadyGraph first))
    (alternativeA :
      ∀ {terminalSource : PureWZ2TerminalPreparedSource source terminal}
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
        WZ1Proposition8_9AlternativeAUnion
          ready.ready.deltaGraph outputLoss
          ready.common.F ready.common.G₁ ready.common.G₁) :
    Nonempty (PureWZ2TerminalChainOutput
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) terminal) := by
  rcases terminal.prepareSource with ⟨terminalSource⟩
  rcases terminalSource.toLemma23Prepared hbridge with ⟨prepared⟩
  rcases prepared.selectWindow with ⟨certifiedWindow⟩
  let window := certifiedWindow.toGraphWindow
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
  rcases readyProducer sharp with ⟨first⟩
  rcases refinedProducer first with ⟨ready⟩
  rcases ready.alternativeAHeights (alternativeA ready) with ⟨rich⟩
  rcases rich.toRichHeightCells with ⟨weighted⟩
  rcases weighted.toWeightedTrapezoid budget.scale_one
      budget.length_lower with ⟨trapezoid⟩
  rcases weighted.toExactRichSetTrapezoid budget.output_pos with
    ⟨exactTrapezoid⟩
  exact ⟨{
    terminalSource := terminalSource
    prepared := prepared
    window := window
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
