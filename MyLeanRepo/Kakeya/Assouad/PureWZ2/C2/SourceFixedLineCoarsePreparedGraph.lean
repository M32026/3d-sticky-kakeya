import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseLocalBins
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.VolumePopularResidue
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23WindowedPreparedGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23HeightPopularity

/-!
# Prepared Lemma-23 graph on the genuine coarse carrier

This is the internal `Z_popular` stage of Lemma 23.  Height layers are
selected by their actual three-dimensional union volume in the genuine
first-sticky coarse carrier.  Only afterwards do we select a separated
y-residue and regularize the surviving height fibres.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- The genuine-coarse prepared graph, retaining both the union-volume
height selection and the later finite height-fibre regularization. -/
structure PureWZ2SourceFixedBinCoarsePreparedGraphData
    {sigma inputLoss delta rho middleLoss stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    (graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep)
    (normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
      (eta := eta) fineWitnesses) where
  localBins : WZ1Lemma23LocalBinPackage
    (rho := prep.graphScale) (sigma := sigma)
    (10 * Kakeya.realRpowENN rho (-middleLoss))
    prep.windowed.global.cells
  heightPopular : PureWZ2HeightVolumePopularData
    prep.shadow prep.graphScale
  popularSource : PureWZ2VolumePopularResidueData
    prep.windowed.global heightPopular
  rawResidue : WZ1Lemma23YResiduePackage prep.windowed.global
  raw_residue_eq : rawResidue = popularSource.residue
  popularResidue : WZ1Lemma23HeightPopularResidueData rawResidue
  graph : WZ1Lemma23WindowedPreparedGraph prep.windowed
  graph_residue_eq : graph.residue = popularResidue.residue
  heightFiberCost_eq : graph.residue.heightFiberCost = 2
  extraCost_eq : graph.residue.extraCost =
    2 * heightPopular.bins * (Nat.log 2 rawResidue.cells.card + 1)
  volumeCost_eq : graph.residue.volumeCost =
    wz1Lemma23YStride prep.graphScale * graph.residue.extraCost

abbrev PureWZ2SourceFixedLineCoarsePreparedGraphData
    {sigma inputLoss delta rho middleLoss stickyLoss eta : ℝ} {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {original : PureWZ2SourceFixedLineCoarseOriginalSlopeData carriers.coarseCarrier carriers.fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedLineCoarsePreparationData original}
    (graphParents : PureWZ2SourceFixedLineCoarseGraphParentData prep)
    (normalFirst : PureWZ2SourceHorizontalNormalFirstCertificate (eta := eta) carriers.fineWitnesses) : Type :=
  PureWZ2SourceFixedBinCoarsePreparedGraphData graphParents normalFirst

/-- Build the finite graph after genuine union-volume height popularity. -/
theorem PureWZ2SourceFixedBinCoarseGraphParentData.prepareGraphFixedBin
    {sigma inputLoss delta rho middleLoss stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    (graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep)
    (normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate (eta := eta) fineWitnesses)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hconstant :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * Kakeya.realRpowENN rho (-middleLoss)))
    (hvolumePos : 0 < volume prep.shadow.union) :
    Nonempty (PureWZ2SourceFixedBinCoarsePreparedGraphData
      graphParents normalFirst) := by
  rcases graphParents.localBinsFixedBin normalFirst hbridge hconstant with
    ⟨localBins⟩
  have hball : prep.shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hcarrier : point ∈ carrier.shading.union := by
      exact prep.shadow_union_subset hpoint
    have hcoarse := carrier.subshading.union_subset hcarrier
    have hnorm := norm_le_two_of_mem_paperShading hcoarse
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hvolumeTop : volume prep.shadow.union ≠ ⊤ :=
    ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
      (measure_mono hball)
  rcases pureWZ2_heightVolumePopularity prep.shadow prep.graphScale
      prep.graphScale_pos hball hvolumePos hvolumeTop with ⟨heightPopular⟩
  rcases heightPopular.toVolumePopularResidue prep.windowed.global
      prep.graphScale_one hball with ⟨popularSource⟩
  let rawResidue := popularSource.residue
  rcases rawResidue.regularizeHeights popularSource.cells_nonempty with
    ⟨popularResidue⟩
  let graphResidue := popularResidue.residue
  rcases wz1_lemma23_y_residue_prepared_package
      prep.windowed.global graphResidue localBins with ⟨graphPackage⟩
  have hcoord : ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hcarrier : point ∈ carrier.shading.union := by
      exact prep.shadow_union_subset hpoint
    have hbox := shading_union_subset_axisBox
      (carrier.subshading.union_subset hcarrier)
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  let graph : WZ1Lemma23WindowedPreparedGraph prep.windowed := {
    localBins := localBins
    residue := graphResidue
    graph := graphPackage
    vertex_separation := graphPackage.vertex_separation
    vertex_bounds := graphPackage.vertex_bounds_of_coord
      prep.graphScale_one hcoord
  }
  have hextra : graph.residue.extraCost =
      2 * heightPopular.bins *
        (Nat.log 2 rawResidue.cells.card + 1) := by
    dsimp only [graph]
    rw [popularResidue.extraCost_eq, popularSource.extraCost_eq,
      popularResidue.logarithmicCost_eq]
  have hvolumeCost : graph.residue.volumeCost =
      wz1Lemma23YStride prep.graphScale * graph.residue.extraCost := by
    dsimp only [graph]
    have hrawVolume : rawResidue.volumeCost =
        wz1Lemma23YStride prep.graphScale * rawResidue.extraCost := by
      simpa [rawResidue] using popularSource.volumeCost_eq
    rw [popularResidue.volumeCost_eq, hrawVolume,
      popularResidue.extraCost_eq]
    ring
  exact ⟨{
    localBins := localBins
    heightPopular := heightPopular
    popularSource := popularSource
    rawResidue := rawResidue
    raw_residue_eq := rfl
    popularResidue := popularResidue
    graph := graph
    graph_residue_eq := rfl
    heightFiberCost_eq := popularResidue.heightFiberCost_eq
    extraCost_eq := hextra
    volumeCost_eq := hvolumeCost
  }⟩

/-- Backwards-compatible maximal-bin constructor for the prepared graph. -/
theorem PureWZ2SourceFixedLineCoarseGraphParentData.prepareGraph
    {sigma inputLoss delta rho middleLoss stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {original : PureWZ2SourceFixedLineCoarseOriginalSlopeData
      carriers.coarseCarrier carriers.fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedLineCoarsePreparationData original}
    (graphParents : PureWZ2SourceFixedLineCoarseGraphParentData prep)
    (normalFirst : PureWZ2SourceHorizontalNormalFirstCertificate
      (eta := eta) carriers.fineWitnesses)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hconstant :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * Kakeya.realRpowENN rho (-middleLoss)))
    (hvolumePos : 0 < volume prep.shadow.union) :
    Nonempty (PureWZ2SourceFixedLineCoarsePreparedGraphData
      graphParents normalFirst) :=
  PureWZ2SourceFixedBinCoarseGraphParentData.prepareGraphFixedBin
    graphParents normalFirst hbridge hconstant hvolumePos

end Kakeya.Assouad

end
