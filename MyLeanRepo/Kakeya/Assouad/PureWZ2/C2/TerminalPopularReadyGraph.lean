import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularPreparedGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23CommonEndpointGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23PowerEdgeBound

/-!
# Common-endpoint ready graph on the terminal outer-popular shadow

The graph in this file uses the volume-popular, height-regularized residue
stored by `PureWZ2TerminalPopularPreparedGraphData`.  In particular it does
not replace that residue by the independent residue selected by a convenience
Theorem-22 wrapper.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

structure PureWZ2TerminalPopularReadyGraph
    {sigma inputLoss delta stickyLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
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
      (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells}
    (sharp : PureWZ2TerminalPopularSharpGeometry preparedGraph) where
  common : WZ1Lemma23UnitBallGraph delta sharp.sharp.normalized.F
    (wz1Lemma23CommonLocalVertices delta sharp.sharp.selectedLocal.g
      preparedGraph.graph.residue.cells)
    (wz1Lemma23CommonLocalVertices delta sharp.sharp.selectedLocal.g
      preparedGraph.graph.residue.cells) sharp.sharp.normalized.H
  ready : WZ1Lemma23Theorem22ReadyGraph delta theoremEta common
  heightFiberCost_eq : preparedGraph.graph.residue.heightFiberCost = 2

theorem PureWZ2TerminalPopularSharpGeometry.toReadyGraph
    {sigma inputLoss delta stickyLoss eta theoremEta
      volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
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
      (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells}
    (sharp : PureWZ2TerminalPopularSharpGeometry preparedGraph)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCOne : (1 : ENNReal) ≤
      pureWZ2TerminalPopularGraphConstant delta inputLoss)
    (hCpower :
      (pureWZ2TerminalPopularGraphConstant delta inputLoss).toReal ≤
        Real.rpow delta (-constantLoss))
    (hvolume : Kakeya.realRpowENN delta
        (1 + sigma / 2 + volumeLoss) ≤ volume prep.shadow.union)
    (hextraPower : (preparedGraph.graph.residue.extraCost : ℝ) ≤
      Real.rpow delta (-extraLoss))
    (hedgeAbsorb :
      Real.rpow (wz1Lemma23Theorem22Scale delta) (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow delta (-3 / 2 + 4 * volumeLoss +
            4 * constantLoss + 4 * extraLoss))
    (hKatzTao : (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale delta) (-theoremEta)) :
    Nonempty (PureWZ2TerminalPopularReadyGraph
      (theoremEta := theoremEta) sharp) := by
  let C := pureWZ2TerminalPopularGraphConstant delta inputLoss
  have hCtop : C ≠ ⊤ := by
    dsimp only [C, pureWZ2TerminalPopularGraphConstant]
    exact ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN])
  have hcoord : ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hsource := prep.shadow_source hpoint
    have hbox := shading_union_subset_axisBox hsource
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hpower := sharp.sharp.power_edge_bound_of_coord
    source.extremal.delta_le_one hsigma hsigmaOne hcoord
    hCOne hCtop volumeLoss constantLoss extraLoss
    (by simpa [Kakeya.realRpowENN] using hvolume) hCpower hextraPower
  have hedgeReal : Real.rpow (wz1Lemma23Theorem22Scale delta)
      (theoremEta - 3) ≤ (sharp.sharp.normalized.H.card : ℝ) := by
    exact hedgeAbsorb.trans hpower
  have hedgeNormalized : Kakeya.realRpowENN
      (wz1Lemma23Theorem22Scale delta) (theoremEta - 3) ≤
        (sharp.sharp.normalized.H.card : ENNReal) := by
    rw [Kakeya.realRpowENN]
    have hcast : (sharp.sharp.normalized.H.card : ENNReal) =
        ENNReal.ofReal (sharp.sharp.normalized.H.card : ℝ) := by norm_cast
    rw [hcast]
    exact ENNReal.ofReal_le_ofReal hedgeReal
  have hedgeUnit : Kakeya.realRpowENN
      (wz1Lemma23Theorem22Scale delta) (theoremEta - 3) ≤
        (sharp.geometry.unitBall.H.card : ENNReal) := by
    rw [sharp.geometry.unitBall.edge_card]
    exact hedgeNormalized
  rcases sharp.geometry.toCommonEndpointReadyGraph
      source.extremal.delta_le_one hcoord hedgeUnit hKatzTao with
    ⟨common, ready⟩
  exact ⟨{
    common := common
    ready := Classical.choice ready
    heightFiberCost_eq := preparedGraph.heightFiberCost_eq }⟩

/-- A ready outer-popular graph has a genuine residue base height. -/
theorem PureWZ2TerminalPopularReadyGraph.base_height_mem
    {sigma inputLoss delta stickyLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
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
      (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells}
    {sharp : PureWZ2TerminalPopularSharpGeometry preparedGraph}
    (data : PureWZ2TerminalPopularReadyGraph
      (theoremEta := theoremEta) sharp) :
    sharp.sharp.baseHeightIndex ∈
      wz1Lemma23SnappedHeights preparedGraph.graph.residue.cells := by
  classical
  rcases data.ready.H_nonempty with ⟨edge, hedge⟩
  have hedgeCommon : edge ∈ data.common.H := hedge
  rw [data.common.H_eq] at hedgeCommon
  rcases Finset.mem_image.mp hedgeCommon with
    ⟨normalizedEdge, hnormalizedEdge, _⟩
  have hsourceNormalized : normalizedEdge ∈ sharp.sharp.normalized.H := by
    simpa using hnormalizedEdge
  rw [sharp.sharp.normalized.H_eq] at hsourceNormalized
  rcases Finset.mem_image.mp hsourceNormalized with
    ⟨actualEdge, hactualEdge, _⟩
  rw [sharp.sharp.normalized_sourceH, sharp.sharp.actual.H_eq] at hactualEdge
  rcases Finset.mem_image.mp hactualEdge with ⟨path, hpath, _⟩
  have hpathBase := hpath
  rw [sharp.sharp.actual.cycles_eq] at hpathBase
  have hfilter := Finset.mem_filter.mp hpathBase
  have hbase : wz1Lemma23SnappedHeight path.1 =
      sharp.sharp.baseHeightIndex := hfilter.2.1
  have hfour := hfilter.1
  have hcell : path.1 ∈ preparedGraph.graph.residue.cells := by
    have hrelations :
        (path.1 ∈ preparedGraph.graph.residue.cells ∧
          path.2.1 ∈ preparedGraph.graph.residue.cells ∧
          path.2.2.1 ∈ preparedGraph.graph.residue.cells ∧
          path.2.2.2 ∈ preparedGraph.graph.residue.cells) ∧
        wz1Lemma23SameSnappedLocalGrain delta
          sharp.sharp.selectedLocal.g path.1 path.2.1 ∧
        wz1Lemma23SameSnappedLocalGrain delta
          sharp.sharp.selectedLocal.g path.2.2.2 path.2.2.1 ∧
        wz1Lemma23SnappedHeight path.1 = wz1Lemma23SnappedHeight path.2.2.2 ∧
        wz1Lemma23SnappedHeight path.2.1 = wz1Lemma23SnappedHeight path.2.2.1 ∧
        wz1Lemma23SnappedGlobalBin delta prep.windowed.global.extendedSlope
          path.2.1 =
        wz1Lemma23SnappedGlobalBin delta prep.windowed.global.extendedSlope
          path.2.2.1 := by
      simpa [wz1Lemma23SnappedFourCycles, wz1Lemma23FourCycles,
        Finset.mem_filter, Finset.mem_product] using hfour
    exact hrelations.1.1
  exact Finset.mem_image.mpr ⟨path.1, hcell, hbase⟩

end Kakeya.Assouad
