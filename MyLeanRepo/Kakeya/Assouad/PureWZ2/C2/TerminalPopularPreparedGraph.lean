import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularLocalCells
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.VolumePopularResidue
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23HeightPopularity
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedPreparedGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedGlobalBinPackage

/-!
# Height-popular prepared graph on the terminal outer-popular shadow

This is the paper-order finite graph attached to the localized
outer-popular carrier.  Height popularity is measured on the current graph
shadow before the y-residue and finite height-fibre regularizations.  The
sharp graph is then rebuilt on exactly that surviving residue.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

structure PureWZ2TerminalPopularPreparedGraphData
    {sigma inputLoss delta stickyLoss eta : ℝ}
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
    (localCells : PureWZ2TerminalPopularLocalCellData
      (eta := eta) graphParents) where
  heightPopular : PureWZ2HeightVolumePopularData prep.shadow delta
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
    wz1Lemma23YStride delta * graph.residue.extraCost

theorem PureWZ2TerminalPopularLocalCellData.preparePopularGraph
    {sigma inputLoss delta stickyLoss eta : ℝ}
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
    (localCells : PureWZ2TerminalPopularLocalCellData
      (eta := eta) graphParents) :
    Nonempty (PureWZ2TerminalPopularPreparedGraphData localCells) := by
  have hvolumePos : 0 < volume prep.shadow.union := by
    rcases localized.selected_nonempty with ⟨parent, hparent⟩
    have hpiecePos : 0 < volume (localized.piece parent hparent) := by
      have hbound := localized.piece_volume parent hparent
      by_contra hzero
      have hz : volume (localized.piece parent hparent) = 0 :=
        le_zero_iff.mp (not_lt.mp hzero)
      rw [hz] at hbound
      exact (not_le_of_gt weightClass.weightFloor_pos)
        (by simpa using hbound)
    apply hpiecePos.trans_le
    apply measure_mono
    rw [prep.shadow_union, prep.region_eq]
    exact fun point hpoint => Set.mem_iUnion.mpr
      ⟨⟨parent, hparent⟩, hpoint⟩
  have hball : prep.shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hsource := prep.shadow_source hpoint
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hvolumeTop : volume prep.shadow.union ≠ ⊤ :=
    ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
      (measure_mono hball)
  rcases pureWZ2_heightVolumePopularity prep.shadow delta
      source.extremal.delta_pos hball hvolumePos hvolumeTop with
    ⟨heightPopular⟩
  rcases heightPopular.toVolumePopularResidue prep.windowed.global
      source.extremal.delta_le_one hball with ⟨popularSource⟩
  let rawResidue := popularSource.residue
  rcases rawResidue.regularizeHeights popularSource.cells_nonempty with
    ⟨popularResidue⟩
  let graphResidue := popularResidue.residue
  rcases wz1_lemma23_y_residue_prepared_package prep.windowed.global
      graphResidue localCells.localBins with ⟨graphPackage⟩
  have hcoord : ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hsource := prep.shadow_source hpoint
    have hbox := shading_union_subset_axisBox hsource
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  let graph : WZ1Lemma23WindowedPreparedGraph prep.windowed := {
    localBins := localCells.localBins
    residue := graphResidue
    graph := graphPackage
    vertex_separation := graphPackage.vertex_separation
    vertex_bounds := graphPackage.vertex_bounds_of_coord
      source.extremal.delta_le_one hcoord
  }
  have hextra : graph.residue.extraCost =
      2 * heightPopular.bins * (Nat.log 2 rawResidue.cells.card + 1) := by
    dsimp only [graph]
    rw [popularResidue.extraCost_eq, popularSource.extraCost_eq,
      popularResidue.logarithmicCost_eq]
  have hvolumeCost : graph.residue.volumeCost =
      wz1Lemma23YStride delta * graph.residue.extraCost := by
    dsimp only [graph]
    have hrawVolume : rawResidue.volumeCost =
        wz1Lemma23YStride delta * rawResidue.extraCost := by
      simpa [rawResidue] using popularSource.volumeCost_eq
    rw [popularResidue.volumeCost_eq, hrawVolume,
      popularResidue.extraCost_eq]
    ring
  exact ⟨{
    heightPopular := heightPopular
    popularSource := popularSource
    rawResidue := rawResidue
    raw_residue_eq := rfl
    popularResidue := popularResidue
    graph := graph
    graph_residue_eq := rfl
    heightFiberCost_eq := popularResidue.heightFiberCost_eq
    extraCost_eq := hextra
    volumeCost_eq := hvolumeCost }⟩

structure PureWZ2TerminalPopularSharpGeometry
    {sigma inputLoss delta stickyLoss eta : ℝ}
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
    (preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells) where
  localized : WZ1Lemma23LocalizedGlobalBinPackage prep.windowed.global
  sharp : WZ1Lemma23LocalizedPreparedPackage prep.windowed localized
    preparedGraph.graph.residue preparedGraph.graph.localBins
  geometry : WZ1Lemma23LocalizedPreparedGeometry sharp

theorem PureWZ2TerminalPopularPreparedGraphData.toSharpGeometry
    {sigma inputLoss delta stickyLoss eta : ℝ}
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
    (preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells) :
    Nonempty (PureWZ2TerminalPopularSharpGeometry preparedGraph) := by
  have hcoord : ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hsource := prep.shadow_source hpoint
    have hbox := shading_union_subset_axisBox hsource
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hCtop : pureWZ2TerminalPopularGraphConstant delta inputLoss ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (by simp [pureWZ2TerminalPopularGraphConstant, Kakeya.realRpowENN])
  rcases wz1_lemma23_localized_global_bin_package_of_coord_of_exact
      prep.windowed.global source.extremal.delta_le_one hcoord prep.exactAD
      hCtop prep.localization.center prep.localization.localization with
    ⟨localizedGlobal, _⟩
  rcases wz1_lemma23_localized_prepared_package prep.windowed localizedGlobal
      preparedGraph.graph.residue preparedGraph.graph.localBins with
    ⟨sharp⟩
  rcases wz1_lemma23_localized_prepared_geometry_of_coord
      source.extremal.delta_le_one hcoord sharp with ⟨geometry⟩
  exact ⟨{ localized := localizedGlobal, sharp := sharp, geometry := geometry }⟩

end Kakeya.Assouad
