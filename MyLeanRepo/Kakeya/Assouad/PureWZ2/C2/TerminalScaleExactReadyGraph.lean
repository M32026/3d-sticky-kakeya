import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactPreparedGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23CommonEndpointGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.LocallyLinearOneScale.BaseSliceValuesAD
import MyLeanRepo.Kakeya.Assouad.WZ1.LocallyLinearOneScale.DotDifferenceAD324

/-! # Theorem-22-ready graph at exact terminal scale -/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2TerminalExactReadyGraph
    {sigma inputLoss delta stickyLoss eta theoremEta : ℝ} {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore window.windowed source.globalGrains.slope}
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
    {localCells : PureWZ2TerminalExactLocalCellData (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    (sharp : PureWZ2TerminalExactSharpGeometry preparedGraph) where
  common : WZ1Lemma23UnitBallGraph delta sharp.sharp.normalized.F
    (wz1Lemma23CommonLocalVertices delta sharp.sharp.selectedLocal.g
      preparedGraph.graph.residue.cells)
    (wz1Lemma23CommonLocalVertices delta sharp.sharp.selectedLocal.g
      preparedGraph.graph.residue.cells) sharp.sharp.normalized.H
  ready : WZ1Lemma23Theorem22ReadyGraph delta theoremEta common
  heightFiberCost_eq : preparedGraph.graph.residue.heightFiberCost = 2

theorem PureWZ2TerminalExactSharpGeometry.toReadyGraph
    {sigma inputLoss delta stickyLoss eta theoremEta
      volumeLoss constantLoss extraLoss : ℝ} {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore window.windowed source.globalGrains.slope}
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
    {localCells : PureWZ2TerminalExactLocalCellData (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    (sharp : PureWZ2TerminalExactSharpGeometry preparedGraph)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCOne : (1 : ENNReal) ≤ 10 * Kakeya.realRpowENN delta (-inputLoss))
    (hCpower : (10 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
      Real.rpow delta (-constantLoss))
    (hvolume : ENNReal.ofReal
      (Real.rpow delta (1 + sigma / 2 + volumeLoss)) ≤
        MeasureTheory.volume prep.shadow.union)
    (hextraPower : (preparedGraph.graph.residue.extraCost : ℝ) ≤
      Real.rpow delta (-extraLoss))
    (hedgeAbsorb :
      Real.rpow (wz1Lemma23Theorem22Scale delta) (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow delta (-3 / 2 + 4 * volumeLoss +
            4 * constantLoss + 4 * extraLoss))
    (hKatzTao : (4 : ENNReal) ≤
      Kakeya.realRpowENN (wz1Lemma23Theorem22Scale delta) (-theoremEta)) :
    Nonempty (PureWZ2TerminalExactReadyGraph (theoremEta := theoremEta) sharp) := by
  let C : ENNReal := 10 * Kakeya.realRpowENN delta (-inputLoss)
  have hCtop : C ≠ ⊤ := ENNReal.mul_ne_top (by norm_num)
    (by simp [Kakeya.realRpowENN])
  have hcoord : ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hambient := prep.subshading.union_subset hpoint
    have hpaper : point ∈ retained.shading.union := by rwa [prep.ambient_union] at hambient
    have hbox := shading_union_subset_axisBox hpaper
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hedgeReal : Real.rpow (wz1Lemma23Theorem22Scale delta)
      (theoremEta - 3) ≤ (sharp.sharp.normalized.H.card : ℝ) := by
    apply hedgeAbsorb.trans
    exact sharp.sharp.power_edge_bound_of_coord source.extremal.delta_le_one
      hsigma hsigmaOne hcoord hCOne hCtop volumeLoss constantLoss extraLoss
      hvolume hCpower hextraPower
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
  rcases sharp.geometry.toCommonEndpointReadyGraph source.extremal.delta_le_one
      hcoord hedgeUnit hKatzTao with ⟨common, ready⟩
  exact ⟨{
    common := common
    ready := Classical.choice ready
    heightFiberCost_eq := preparedGraph.heightFiberCost_eq }⟩

/-- An exact-terminal ready graph has a genuine residue base height. -/
theorem PureWZ2TerminalExactReadyGraph.base_height_mem
    {sigma inputLoss delta stickyLoss eta theoremEta : ℝ} {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore window.windowed source.globalGrains.slope}
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
    {localCells : PureWZ2TerminalExactLocalCellData (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
    (data : PureWZ2TerminalExactReadyGraph (theoremEta := theoremEta) sharp) :
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
        wz1Lemma23SnappedGlobalBin delta prep.windowed.global.extendedSlope path.2.1 =
          wz1Lemma23SnappedGlobalBin delta prep.windowed.global.extendedSlope path.2.2.1 := by
      simpa [wz1Lemma23SnappedFourCycles, wz1Lemma23FourCycles,
        Finset.mem_filter, Finset.mem_product] using hfour
    exact hrelations.1.1
  exact Finset.mem_image.mpr ⟨path.1, hcell, hbase⟩

end Kakeya.Assouad
