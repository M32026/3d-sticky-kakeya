import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularOuterHeightLift
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularGraphVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactRichSetTrapezoid

/-!
# One-window paper-order terminal chain with heterogeneous parents

The outer-popular carrier selects the fixed horizontal line and official sticky
parents and remains the measured Lemma-23 graph carrier.  Complete terminal
parents enter only as local-normal and heavy-fibre witnesses.  All dependent
choices below are stored in one record, so no witness can be imported from the
older terminal chain by a type cast.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- The three dependent choices made before the terminal fixed line.  Keeping
them in one record lets the global block--parent regularization prescribe the
exact support used by the downstream chain. -/
structure PureWZ2TerminalPopularPrefixData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (window : PureWZ2TerminalWindow prepared) where
  heightData : PureWZ2TerminalWindowHeightPopularData window
  carrier : PureWZ2TerminalPopularSourceCarrierData heightData
  weightClass : PureWZ2TerminalPopularParentWeightClassData carrier

theorem PureWZ2TerminalWindow.popularPrefix
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (window : PureWZ2TerminalWindow prepared) :
    Nonempty (PureWZ2TerminalPopularPrefixData window) := by
  rcases window.heightPopularBeforeFixedLine with ⟨heightData⟩
  rcases heightData.toSourceCarrier with ⟨carrier⟩
  rcases carrier.regularizeParentWeights with ⟨weightClass⟩
  exact ⟨{
    heightData := heightData
    carrier := carrier
    weightClass := weightClass
  }⟩

/-- The complete one-window dependent chain through the rich-height refill. -/
structure PureWZ2TerminalPopularPaperOrderChain
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (window : PureWZ2TerminalWindow prepared) where
  heightData : PureWZ2TerminalWindowHeightPopularData window
  carrier : PureWZ2TerminalPopularSourceCarrierData heightData
  weightClass : PureWZ2TerminalPopularParentWeightClassData carrier
  restricted : PureWZ2TerminalPopularParentRestrictionData weightClass
  restrictedPrepared :
    PureWZ2TerminalPopularParentRestrictedPreparedData restricted
  line : PureWZ2HorizontalFixedBinCore
    restrictedPrepared.windowed source.globalGrains.slope
  parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line
  selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents
  selectedCarrier :
    PureWZ2TerminalPopularSelectedParentCarrierData selection
  sources : PureWZ2TerminalPopularCoarseSourceFamily selection
  localized : PureWZ2TerminalPopularLocalizedPieceData
    (selectedCarrier := selectedCarrier) sources
  prep : PureWZ2TerminalPopularGraphPreparation localized
  graphParents : PureWZ2TerminalPopularGraphParentData prep
  localCells : PureWZ2TerminalPopularLocalCellData
    (eta := eta) graphParents
  preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells
  sharp : PureWZ2TerminalPopularSharpGeometry preparedGraph
  first : PureWZ2TerminalPopularReadyGraph
    (theoremEta := theoremEta) sharp
  ready : PureWZ2CommonRefinedReadyGraph
    delta theoremEta first.common first.ready
  rich : PureWZ2TerminalPopularAlternativeAHeightData ready outputLoss
  outerHeightLift : PureWZ2TerminalPopularOuterHeightLift rich
  richFloor_four : (4 : ENNReal) ≤
    pureWZ2TerminalPopularRichFloor delta outputLoss

/-- Assemble the heterogeneous chain from one terminal window and explicit
numerical certificates.  In particular, the volume premise concerns the
outer-popular graph shadow produced by this very dependent chain. -/
theorem pureWZ2_terminalPopular_paperOrderChain_of_certificates
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss
      volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (window : PureWZ2TerminalWindow prepared)
    (preline : PureWZ2TerminalPopularPrefixData window)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (houtputTheorem : outputLoss + theoremEta ≤ 1)
    (hCpower : 10 * Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-eta))
    (hPlanarSmall : 32 * Real.rpow delta eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt delta ≤ 1)
    (hlocalization : Real.rpow delta (1 - 4 * eta / sigma) ≤
      Real.sqrt delta / 14)
    (htransferSmall : 1000 * Real.sqrt delta ≤ 1)
    (hsourceVolume :
      (512 : ENNReal) * Kakeya.realRpowENN delta
          (3 / 2 + sigma / 2 + eta) ≤
        terminal.sticky.balanced.cellMass)
    (hGraphCOne : (1 : ENNReal) ≤
      pureWZ2TerminalPopularGraphConstant delta inputLoss)
    (hGraphCpower :
      (pureWZ2TerminalPopularGraphConstant delta inputLoss).toReal ≤
        Real.rpow delta (-constantLoss))
    (hvolume : ∀
      {restricted : PureWZ2TerminalPopularParentRestrictionData
        preline.weightClass}
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
      (_prep : PureWZ2TerminalPopularGraphPreparation localized),
        pureWZ2TerminalPopularLocalizedPieceCost *
            Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) ≤
          (localized.selectedParents.card : ENNReal) *
            preline.weightClass.weightFloor)
    (hextra : ∀
      {restricted : PureWZ2TerminalPopularParentRestrictionData
        preline.weightClass}
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
        (eta := eta) graphParents}
      (preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells),
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
      {restricted : PureWZ2TerminalPopularParentRestrictionData
        preline.weightClass}
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
        (eta := eta) graphParents}
      {preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells}
      {sharp : PureWZ2TerminalPopularSharpGeometry preparedGraph}
      {first : PureWZ2TerminalPopularReadyGraph
        (theoremEta := theoremEta) sharp}
      (ready : PureWZ2CommonRefinedReadyGraph
        delta theoremEta first.common first.ready),
        WZ1Proposition8_9AlternativeAUnion
          ready.ready.deltaGraph outputLoss
          ready.common.F ready.common.G₁ ready.common.G₁) :
    Nonempty (PureWZ2TerminalPopularPaperOrderChain
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) window) := by
  let heightData := preline.heightData
  let carrier := preline.carrier
  let weightClass := preline.weightClass
  let restricted := weightClass.restrictCarrier
  rcases restricted.prepareWindow hbridge with ⟨restrictedPrepared⟩
  rcases restrictedPrepared.selectHorizontalFixedLine with ⟨fixedLine⟩
  let line := fixedLine.toPureWZ2HorizontalFixedBinCore
  rcases restrictedPrepared.toParents fixedLine with ⟨parents⟩
  rcases parents.selectWeightedParents with ⟨selection⟩
  let selectedCarrier := selection.toCarrier
  rcases selection.coarseSources with ⟨sources⟩
  rcases sources.localize (selectedCarrier := selectedCarrier) with ⟨localized⟩
  rcases localized.prepareGraph hbridge with ⟨prep⟩
  rcases prep.graphParents with ⟨graphParents⟩
  rcases graphParents.fullParentLocalBins hbridge hsigma hsigmaOne
      heta hetaSigma hCpower hPlanarSmall hrootSmall20 hlocalization
      htransferSmall hsourceVolume with ⟨localCells⟩
  rcases PureWZ2TerminalPopularLocalCellData.preparePopularGraph localCells with
    ⟨preparedGraph⟩
  rcases preparedGraph.toSharpGeometry with ⟨sharp⟩
  have hgraphVolume : Kakeya.realRpowENN delta
        (1 + sigma / 2 + volumeLoss) ≤ volume prep.shadow.union :=
    prep.power_volume_lower (hvolume prep)
  rcases sharp.toReadyGraph hsigma hsigmaOne hGraphCOne hGraphCpower
      hgraphVolume (hextra preparedGraph) hedge hkatz with ⟨first⟩
  have hcoord : ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hsource := prep.shadow_source hpoint
    have hbox := shading_union_subset_axisBox hsource
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hGraphCTop :
      pureWZ2TerminalPopularGraphConstant delta inputLoss ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (by simp [pureWZ2TerminalPopularGraphConstant, Kakeya.realRpowENN])
  have hrefinedReal :
      Real.rpow (wz1Lemma23Theorem22Scale (delta / 625))
          (theoremEta - 3) ≤ (sharp.sharp.normalized.H.card : ℝ) := by
    apply hrefinedEdge.trans
    exact sharp.sharp.power_edge_bound_of_coord
      source.extremal.delta_le_one hsigma hsigmaOne hcoord
      hGraphCOne hGraphCTop volumeLoss constantLoss extraLoss
      (by simpa [Kakeya.realRpowENN] using hgraphVolume)
      hGraphCpower (hextra preparedGraph)
  have hrefinedNormalized : Kakeya.realRpowENN
      (wz1Lemma23Theorem22Scale (delta / 625)) (theoremEta - 3) ≤
        (sharp.sharp.normalized.H.card : ENNReal) := by
    rw [Kakeya.realRpowENN]
    have hcast : (sharp.sharp.normalized.H.card : ENNReal) =
        ENNReal.ofReal (sharp.sharp.normalized.H.card : ℝ) := by norm_cast
    rw [hcast]
    exact ENNReal.ofReal_le_ofReal hrefinedReal
  have hrefinedCommon : Kakeya.realRpowENN
      (wz1Lemma23Theorem22Scale (delta / 625)) (theoremEta - 3) ≤
        (first.common.H.card : ENNReal) := by
    rw [first.common.edge_card]
    exact hrefinedNormalized
  rcases first.refineForExactTrapezoid hrefinedCommon hrefinedKatz with
    ⟨ready⟩
  rcases ready.alternativeAHeights (alternativeA ready) with ⟨rich⟩
  rcases rich.toOuterHeightLift with ⟨outerHeightLift⟩
  have hrichFloorFour : (4 : ENNReal) ≤
      pureWZ2TerminalPopularRichFloor delta outputLoss :=
    pureWZ2_terminalPopular_richFloor_four source.extremal.delta_pos
      source.extremal.delta_le_one houtputTheorem hrefinedKatz
  exact ⟨{
    heightData := heightData
    carrier := carrier
    weightClass := weightClass
    restricted := restricted
    restrictedPrepared := restrictedPrepared
    line := line
    parents := parents
    selection := selection
    selectedCarrier := selectedCarrier
    sources := sources
    localized := localized
    prep := prep
    graphParents := graphParents
    localCells := localCells
    preparedGraph := preparedGraph
    sharp := sharp
    first := first
    ready := ready
    rich := rich
    outerHeightLift := outerHeightLift
    richFloor_four := hrichFloorFour }⟩

end Kakeya.Assouad

end
