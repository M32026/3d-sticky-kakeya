import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalLocalBins
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalPopularResidue
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23WindowedPreparedGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23HeightPopularity

/-!
# Prepared finite graph on the source-slope residue
-/

noncomputable section

namespace Kakeya.Assouad

theorem PureWZ2SourceHorizontalFixedBinGraphParentData.preparedGraphFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalFixedBinResiduePreparation retained}
    (graphParents : PureWZ2SourceHorizontalFixedBinGraphParentData prep)
    (fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained)
    (normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
      (eta := eta) fineWitnesses)
    (hshadowVolume : 0 < MeasureTheory.volume prep.shadow.union) :
    ∃ rawResidue : WZ1Lemma23YResiduePackage prep.windowed.global,
      ∃ heightPopular : PureWZ2SourceHorizontalFixedBinHeightPopularShadow
          retained prep.shadow prep.graphScale,
        ∃ popularSource : PureWZ2SourceHorizontalFixedBinPopularResidueData heightPopular,
          ∃ popularResidue : WZ1Lemma23HeightPopularResidueData rawResidue,
            ∃ graph : WZ1Lemma23WindowedPreparedGraph prep.windowed,
              rawResidue = popularSource.residue ∧
                graph.residue = popularResidue.residue ∧
                graph.residue.heightFiberCost = 2 ∧
                  graph.residue.extraCost =
                    2 * heightPopular.bins *
                      (Nat.log 2 rawResidue.cells.card + 1) ∧
                    graph.residue.volumeCost =
                      wz1Lemma23YStride prep.graphScale *
                        graph.residue.extraCost := by
  rcases graphParents.localBinsFixedBin fineWitnesses normalFirst with ⟨localBins⟩
  rcases retained.heightPopularShadowFixedBin prep.shadow prep.shadow_union_subset
      hshadowVolume prep.graphScale prep.graphScale_pos with ⟨heightPopular⟩
  rcases heightPopular.toPopularResidueFixedBin with ⟨popularSource⟩
  let rawResidue := popularSource.residue
  have hrawNonempty : rawResidue.cells.Nonempty :=
    popularSource.cells_nonempty
  rcases rawResidue.regularizeHeights hrawNonempty with ⟨popularResidue⟩
  let graphResidue := popularResidue.residue
  have hheightFiberCost : graphResidue.heightFiberCost = 2 :=
    popularResidue.heightFiberCost_eq
  have hextraCost : graphResidue.extraCost =
      2 * heightPopular.bins *
        (Nat.log 2 rawResidue.cells.card + 1) := by
    rw [popularResidue.extraCost_eq, popularSource.extraCost_eq,
      popularResidue.logarithmicCost_eq]
  have hvolumeCost : graphResidue.volumeCost =
      wz1Lemma23YStride prep.graphScale * graphResidue.extraCost := by
    have hrawVolume : rawResidue.volumeCost =
        wz1Lemma23YStride prep.graphScale * rawResidue.extraCost := by
      simpa [rawResidue] using popularSource.volumeCost_eq
    rw [popularResidue.volumeCost_eq, hrawVolume,
      popularResidue.extraCost_eq]
    ring
  rcases wz1_lemma23_y_residue_prepared_package
      prep.windowed.global graphResidue localBins with
    ⟨graph⟩
  have hcoord :
      ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hpaper : point ∈ retained.shading.union := by
      exact prep.shadow_union_subset hpoint
    have hbox := shading_union_subset_axisBox hpaper
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  let output : WZ1Lemma23WindowedPreparedGraph prep.windowed := {
    localBins := localBins
    residue := graphResidue
    graph := graph
    vertex_separation := graph.vertex_separation
    vertex_bounds := graph.vertex_bounds_of_coord prep.graphScale_one hcoord
  }
  exact ⟨rawResidue, heightPopular, popularSource, popularResidue, output, rfl,
    rfl, hheightFiberCost, hextraCost, hvolumeCost⟩

/-- Compatibility wrapper for the former maximal-bin prepared-graph API. -/
theorem PureWZ2SourceHorizontalGraphParentData.preparedGraph
    {sigma inputLoss delta rho middleLoss outputLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    (graphParents : PureWZ2SourceHorizontalGraphParentData prep)
    (fineWitnesses : PureWZ2SourceHorizontalFineWitnessData retained)
    (normalFirst : PureWZ2SourceHorizontalNormalFirstCertificate
      (eta := eta) fineWitnesses)
    (hshadowVolume : 0 < MeasureTheory.volume prep.shadow.union) :
    ∃ rawResidue : WZ1Lemma23YResiduePackage prep.windowed.global,
      ∃ heightPopular : PureWZ2SourceHorizontalHeightPopularShadow
          retained prep.shadow prep.graphScale,
        ∃ popularSource : PureWZ2SourceHorizontalPopularResidueData heightPopular,
          ∃ popularResidue : WZ1Lemma23HeightPopularResidueData rawResidue,
            ∃ graph : WZ1Lemma23WindowedPreparedGraph prep.windowed,
              rawResidue = popularSource.residue ∧
                graph.residue = popularResidue.residue ∧
                graph.residue.heightFiberCost = 2 ∧
                  graph.residue.extraCost =
                    2 * heightPopular.bins *
                      (Nat.log 2 rawResidue.cells.card + 1) ∧
                    graph.residue.volumeCost =
                      wz1Lemma23YStride prep.graphScale *
                        graph.residue.extraCost :=
  PureWZ2SourceHorizontalFixedBinGraphParentData.preparedGraphFixedBin
    graphParents fineWitnesses normalFirst hshadowVolume

end Kakeya.Assouad
