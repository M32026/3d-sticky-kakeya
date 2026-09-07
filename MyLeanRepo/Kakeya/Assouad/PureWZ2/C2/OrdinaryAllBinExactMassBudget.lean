import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseExactMassBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryAllBinSelectedProducer

/-!
# Exact indexed-mass budget for the scheduled all-bin ordinary construction

The chosen graph bin is selected only after the full genuine-coarse all-bin
aggregate has been formed.  This module transports that same-bin graph mass
through `Z_lin` and the exact first-cover pullback, and then sums over the
source-relative regularized blocks.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData

/-- The exact source pullback has precisely the `Z_lin` owner cells as active
cells. -/
theorem sourcePullback_selectedCells_eq
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta : ℝ}
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
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
      (normalEta := normalEta) prep}
    (rich : PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData
      (finalLoss := finalLoss) (theoremEta := theoremEta) pipeline) :
    rich.sourcePullback.selectedCells = rich.richCells.cells := by
  apply Finset.Subset.antisymm
  · intro cell hcell
    rw [rich.sourcePullback.selectedCells_eq, mem_wz1PaperActiveCells] at hcell
    rcases hcell.2 with ⟨point, hpointRich, hpointCellBase⟩
    have hpointCell : point ∈ wz1PaperGridCube rho cell := by
      simpa only [twoScale.rhoRequested_eq] using hpointCellBase
    rw [rich.richShading.union_eq, rich.richShading.region_eq] at hpointRich
    rcases Set.mem_iUnion₂.mp hpointRich with
      ⟨owner, howner, hpointOwner⟩
    have heq : owner = cell :=
      ((mem_wz1PaperGridCube rho owner point).mp hpointOwner).symm.trans
        ((mem_wz1PaperGridCube rho cell point).mp hpointCell)
    rwa [heq] at howner
  · intro cell hcell
    rw [rich.sourcePullback.selectedCells_eq, mem_wz1PaperActiveCells]
    have hactive := rich.richCells.cells_active_carrier hcell
    rw [mem_wz1PaperActiveCells] at hactive
    refine ⟨hactive.1, ?_⟩
    rcases hactive.2 with ⟨point, _hcarrier, hpointCell⟩
    have hpointCellRho : point ∈ wz1PaperGridCube rho cell := by
      simpa only [twoScale.rhoRequested_eq] using hpointCell
    refine ⟨point, ?_, hpointCell⟩
    rw [rich.richShading.union_eq, rich.richShading.region_eq]
    exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCellRho⟩

/-- The graph shadow is bounded by its actual graph-cell count after paying
the explicit `extraCost` power bound. -/
theorem graph_shadow_volume_le_cells
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta extraLoss : ℝ}
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
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
      (normalEta := normalEta) prep}
    (rich : PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData
      (finalLoss := finalLoss) (theoremEta := theoremEta) pipeline)
    (hextraPower :
      (pipeline.preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow prep.graphScale (-extraLoss)) :
    volume prep.shadow.union ≤
      PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost rho extraLoss *
        (pipeline.preparedGraph.graph.residue.cells.card : ENNReal) := by
  let scale := prep.graphScale
  let volumeValue := volume prep.shadow.union
  have hscale : 0 < scale := prep.graphScale_pos
  have hball : prep.shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hcarrier : point ∈ carrier.shading.union := by
      exact prep.shadow_union_subset hpoint
    have hcoarse := carrier.subshading.union_subset hcarrier
    have hnorm := norm_le_two_of_mem_paperShading hcoarse
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hvolumeTop : volumeValue ≠ ⊤ :=
    ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
      (measure_mono hball)
  have hvolumeOfReal : ENNReal.ofReal volumeValue.toReal = volumeValue :=
    ENNReal.ofReal_toReal hvolumeTop
  have hraw := pipeline.preparedGraph.graph.residue.cell_count_from_volume
    prep.graphScale_one volumeValue.toReal ENNReal.toReal_nonneg
    (by simpa [volumeValue] using hvolumeOfReal.le)
  have hextraPos :
      0 < (pipeline.preparedGraph.graph.residue.extraCost : ℝ) := by
    exact_mod_cast pipeline.preparedGraph.graph.residue.extraCost_pos
  have hpowerPos : 0 < Real.rpow scale (5 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hscale _
  have hactualPos :
      0 < 8 * (pipeline.preparedGraph.graph.residue.extraCost : ℝ) *
        Real.rpow scale (5 / 2 : ℝ) := by positivity
  have hreal : volumeValue.toReal ≤
      (8 * Real.rpow scale (-extraLoss) *
          Real.rpow scale (5 / 2 : ℝ)) *
        (pipeline.preparedGraph.graph.residue.cells.card : ℝ) := by
    calc
      volumeValue.toReal ≤
          (8 * (pipeline.preparedGraph.graph.residue.extraCost : ℝ) *
            Real.rpow scale (5 / 2 : ℝ)) *
            (pipeline.preparedGraph.graph.residue.cells.card : ℝ) :=
        by simpa [mul_comm] using (div_le_iff₀ hactualPos).mp hraw
      _ ≤ (8 * Real.rpow scale (-extraLoss) *
            Real.rpow scale (5 / 2 : ℝ)) *
            (pipeline.preparedGraph.graph.residue.cells.card : ℝ) := by
        gcongr
  have hcoefficientNonneg :
      0 ≤ 8 * Real.rpow scale (-extraLoss) *
        Real.rpow scale (5 / 2 : ℝ) :=
    mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hscale.le _))
      hpowerPos.le
  calc
    volume prep.shadow.union = ENNReal.ofReal volumeValue.toReal := by
      rw [hvolumeOfReal]
    _ ≤ ENNReal.ofReal
        ((8 * Real.rpow scale (-extraLoss) *
            Real.rpow scale (5 / 2 : ℝ)) *
          (pipeline.preparedGraph.graph.residue.cells.card : ℝ)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost rho extraLoss *
        (pipeline.preparedGraph.graph.residue.cells.card : ENNReal) := by
      rw [ENNReal.ofReal_mul hcoefficientNonneg, ENNReal.ofReal_natCast]
      simp [PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost,
        scale, prep.graphScale_eq]

/-- The snapped-height count of one chosen-bin graph obeys the common
`O(rho⁻¹/²)` cap. -/
theorem snapped_heights_le_cap
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta : ℝ}
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
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
      (normalEta := normalEta) prep}
    (rich : PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData
      (finalLoss := finalLoss) (theoremEta := theoremEta) pipeline) :
    ((wz1Lemma23SnappedHeights
      pipeline.preparedGraph.graph.residue.cells).card : ENNReal) ≤
      PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho := by
  have hreal := wz1Lemma23_height_layer_count
    prep.graphScale_pos prep.graphScale_one
    (prep.windowed.residue_cells_window pipeline.preparedGraph.graph.residue)
  have henn := ENNReal.natCast_le_ofReal
    (by
      intro hzero
      have : (wz1Lemma23SnappedHeights
          pipeline.preparedGraph.graph.residue.cells).Nonempty := by
        rcases rich.richCells.graphCells_nonempty with ⟨cell, hcell⟩
        exact ⟨cell.2.2, Finset.mem_image.mpr
          ⟨cell, rich.richCells.graphCells_subset hcell, rfl⟩⟩
      exact this.card_ne_zero hzero) |>.mpr hreal
  simpa [PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap,
    prep.graphScale_eq] using henn

/-- The actual graph-cell count, after the `Z_lin` height floor, controls the
exact chosen-bin source-pullback indexed mass. -/
theorem graph_cells_to_source_mass
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta : ℝ}
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
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
      (normalEta := normalEta) prep}
    (rich : PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData
      (finalLoss := finalLoss) (theoremEta := theoremEta) pipeline) :
    pureWZ2SourceHorizontalRichFloor rho finalLoss *
          (pipeline.preparedGraph.graph.residue.cells.card : ENNReal) *
          twoScale.coarse.balanced.incidenceMass ≤
      54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho *
        rich.sourcePullback.shading.mass := by
  let floor := pureWZ2SourceHorizontalRichFloor rho finalLoss
  let heightCap :=
    PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho
  have hfloor : floor =
      Kakeya.realRpowENN rich.ready.ready.deltaGraph (finalLoss - 1) := by
    dsimp only [floor]
    unfold pureWZ2SourceHorizontalRichFloor
    rw [rich.ready.ready.deltaGraph_eq, prep.graphScale_eq]
  have hownerNat : rich.rich.heightIndices.card *
        pipeline.preparedGraph.graph.residue.cells.card ≤
      54 * (wz1Lemma23SnappedHeights
        pipeline.preparedGraph.graph.residue.cells).card *
          rich.richCells.cells.card := by
    calc
      rich.rich.heightIndices.card *
            pipeline.preparedGraph.graph.residue.cells.card ≤
          pipeline.preparedGraph.graph.residue.heightFiberCost *
            (wz1Lemma23SnappedHeights
              pipeline.preparedGraph.graph.residue.cells).card *
                rich.richCells.graphCells.card :=
        rich.richCells.graphCells_card_lower
      _ ≤ 2 * (wz1Lemma23SnappedHeights
            pipeline.preparedGraph.graph.residue.cells).card *
              rich.richCells.graphCells.card := by
        rw [rich.ready.heightFiberCost_eq]
      _ ≤ 2 * (wz1Lemma23SnappedHeights
            pipeline.preparedGraph.graph.residue.cells).card *
              (27 * rich.richCells.cells.card) := by
        exact Nat.mul_le_mul_left
          (2 * (wz1Lemma23SnappedHeights
            pipeline.preparedGraph.graph.residue.cells).card)
          rich.richCells.graphCells_card
      _ = 54 * (wz1Lemma23SnappedHeights
            pipeline.preparedGraph.graph.residue.cells).card *
              rich.richCells.cells.card := by ring
  have howner :
      ((rich.rich.heightIndices.card : ENNReal) *
        (pipeline.preparedGraph.graph.residue.cells.card : ENNReal)) ≤
      54 * (wz1Lemma23SnappedHeights
          pipeline.preparedGraph.graph.residue.cells).card *
        (rich.richCells.cells.card : ENNReal) := by
    exact_mod_cast hownerNat
  have hheight := rich.snapped_heights_le_cap
  calc
    floor * (pipeline.preparedGraph.graph.residue.cells.card : ENNReal) *
          twoScale.coarse.balanced.incidenceMass ≤
        (rich.rich.heightIndices.card : ENNReal) *
          (pipeline.preparedGraph.graph.residue.cells.card : ENNReal) *
          twoScale.coarse.balanced.incidenceMass := by
      gcongr
      rw [hfloor]
      simpa [rich.rich.heightIndices_card] using rich.rich.richF_card
    _ ≤ (54 * (wz1Lemma23SnappedHeights
          pipeline.preparedGraph.graph.residue.cells).card *
        (rich.richCells.cells.card : ENNReal)) *
          twoScale.coarse.balanced.incidenceMass := by gcongr
    _ ≤ (54 * heightCap * (rich.richCells.cells.card : ENNReal)) *
          twoScale.coarse.balanced.incidenceMass := by gcongr
    _ = 54 * heightCap * rich.sourcePullback.shading.mass := by
      rw [rich.sourcePullback.mass_eq, rich.sourcePullback_selectedCells_eq]
      ring

/-- One chosen genuine graph shadow controls its exact source indexed mass. -/
theorem graph_to_source_mass_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta extraLoss : ℝ}
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
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
      (normalEta := normalEta) prep}
    (rich : PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData
      (finalLoss := finalLoss) (theoremEta := theoremEta) pipeline)
    (hextraPower :
      (pipeline.preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow prep.graphScale (-extraLoss)) :
    volume prep.shadow.union * pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass ≤
      PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost rho extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
        rich.sourcePullback.shading.mass := by
  calc
    _ ≤ (PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho extraLoss *
        (pipeline.preparedGraph.graph.residue.cells.card : ENNReal)) *
        pureWZ2SourceHorizontalRichFloor rho finalLoss *
        twoScale.coarse.balanced.incidenceMass := by
      gcongr
      exact rich.graph_shadow_volume_le_cells hextraPower
    _ = PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost rho extraLoss *
        (pureWZ2SourceHorizontalRichFloor rho finalLoss *
          (pipeline.preparedGraph.graph.residue.cells.card : ENNReal) *
          twoScale.coarse.balanced.incidenceMass) := by ring
    _ ≤ PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost rho extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho *
          rich.sourcePullback.shading.mass) := by
      exact mul_le_mul_left' rich.graph_cells_to_source_mass _
    _ = _ := by ring

end PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData

namespace PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData

/-- On one regularized source block, the outer-popular source volume reaches
the canonical maximum graph-good bin after paying only the explicit outer-bin
and all-global-bin costs. -/
theorem source_window_to_chosen_graph
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {allBins : PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers}
    {coarseBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins}
    {selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
      (volumeLoss := volumeLoss) coarseBins}
    (rich : PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) selected)
    (block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe})
    (outerCost binCost : ENNReal)
    (houterCost :
      (2 * (carriers.carrier block.1).outerPopular.popular.bins : ENNReal) ≤
        outerCost)
    (hbinCost :
      ((allBins.binFamily block.1).line.globalBins.card : ENNReal) *
          pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta ≤ binCost) :
    volume (safe.blockWindow block.1).shading.union *
        twoScale.fine.balanced.cellMass ≤
      2 * outerCost * binCost *
        volume ((coarseBins.coarseFamily block.1).prep
          (selected.chosenBin block)).shadow.union := by
  let blockCarrier := carriers.carrier block.1
  have hsource : volume (safe.blockWindow block.1).shading.union ≤
      outerCost * blockCarrier.outerPopular.popularWindow.volumeSupply := by
    calc
      volume (safe.blockWindow block.1).shading.union =
          volume (safe.blockWindow block.1).window.shading.union := by
        rw [(safe.blockWindow block.1).window_shading]
      _ ≤ (2 * blockCarrier.outerPopular.popular.bins : ENNReal) *
          blockCarrier.outerPopular.popularWindow.volumeSupply := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          blockCarrier.source_volume_retention
      _ ≤ outerCost * blockCarrier.outerPopular.popularWindow.volumeSupply := by
        gcongr
  have haggregate :=
    (coarseBins.coarseFamily block.1).aggregate_graph_volume_supply_le
  have hchosen := (selected.good block).total_volume_le_chosenBin
  have hpopularToChosen :
      blockCarrier.outerPopular.popularWindow.volumeSupply *
          twoScale.fine.balanced.cellMass ≤
        2 * binCost *
          volume ((coarseBins.coarseFamily block.1).prep
            (selected.chosenBin block)).shadow.union := by
    calc
      _ ≤ pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta *
          ∑ bin : {bin // bin ∈
              (allBins.binFamily block.1).line.globalBins},
            volume ((coarseBins.coarseFamily block.1).prep bin).shadow.union :=
        haggregate
      _ ≤ pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta *
          (2 * ((allBins.binFamily block.1).line.globalBins.card : ENNReal) *
            volume ((coarseBins.coarseFamily block.1).prep
              (selected.chosenBin block)).shadow.union) := by
        apply mul_le_mul_left'
        simpa [PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData.chosenBin]
          using hchosen
      _ = 2 * (((allBins.binFamily block.1).line.globalBins.card : ENNReal) *
          pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta) *
            volume ((coarseBins.coarseFamily block.1).prep
              (selected.chosenBin block)).shadow.union := by
        ring
      _ ≤ 2 * binCost *
          volume ((coarseBins.coarseFamily block.1).prep
            (selected.chosenBin block)).shadow.union := by gcongr
  calc
    volume (safe.blockWindow block.1).shading.union *
          twoScale.fine.balanced.cellMass ≤
        (outerCost * blockCarrier.outerPopular.popularWindow.volumeSupply) *
          twoScale.fine.balanced.cellMass := by gcongr
    _ = outerCost *
        (blockCarrier.outerPopular.popularWindow.volumeSupply *
          twoScale.fine.balanced.cellMass) := by ring
    _ ≤ outerCost *
        (2 * binCost * volume ((coarseBins.coarseFamily block.1).prep
          (selected.chosenBin block)).shadow.union) := by gcongr
    _ = 2 * outerCost * binCost *
        volume ((coarseBins.coarseFamily block.1).prep
          (selected.chosenBin block)).shadow.union := by ring

/-- The same source block controls the exact selected-bin source-pullback mass
after the graph-cell and height costs. -/
theorem block_source_to_exact_mass
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {allBins : PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers}
    {coarseBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins}
    {selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
      (volumeLoss := volumeLoss) coarseBins}
    (rich : PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) selected)
    (block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe})
    (outerCost binCost : ENNReal)
    (houterCost :
      (2 * (carriers.carrier block.1).outerPopular.popular.bins : ENNReal) ≤
        outerCost)
    (hbinCost :
      ((allBins.binFamily block.1).line.globalBins.card : ENNReal) *
          pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta ≤ binCost)
    (hextraPower :
      ((rich.pipeline block).preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow
          ((coarseBins.coarseFamily block.1).prep
            (selected.chosenBin block)).graphScale (-extraLoss)) :
    volume (safe.blockWindow block.1).shading.union *
          twoScale.fine.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass ≤
      2 * outerCost * binCost *
        PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost rho extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
        (rich.rich block).sourcePullback.shading.mass := by
  have hsource := rich.source_window_to_chosen_graph
    block outerCost binCost houterCost hbinCost
  have hgraph := (rich.rich block).graph_to_source_mass_bound hextraPower
  calc
    _ ≤ (2 * outerCost * binCost *
        volume ((coarseBins.coarseFamily block.1).prep
          (selected.chosenBin block)).shadow.union) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass := by gcongr
    _ = 2 * outerCost * binCost *
        (volume ((coarseBins.coarseFamily block.1).prep
          (selected.chosenBin block)).shadow.union *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass) := by ring
    _ ≤ 2 * outerCost * binCost *
        (PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost rho extraLoss *
          (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
          (rich.rich block).sourcePullback.shading.mass) := by gcongr
    _ = _ := by ring

/-- Sum the same-block chosen-bin estimates over all source-relative
regularized blocks. -/
theorem aggregate_source_to_exact_mass
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {allBins : PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers}
    {coarseBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins}
    {selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
      (volumeLoss := volumeLoss) coarseBins}
    (rich : PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) selected)
    (outerCost binCost : ENNReal)
    (houterCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      (2 * (carriers.carrier block.1).outerPopular.popular.bins : ENNReal) ≤
        outerCost)
    (hbinCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((allBins.binFamily block.1).line.globalBins.card : ENNReal) *
          pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta ≤ binCost)
    (hextraPower : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((rich.pipeline block).preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow
          ((coarseBins.coarseFamily block.1).prep
            (selected.chosenBin block)).graphScale (-extraLoss)) :
    volume prepared.shadow.union * twoScale.fine.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass ≤
      8 * outerCost * binCost *
        PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost rho extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
        ∑ block :
          {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
          (rich.rich block).sourcePullback.shading.mass := by
  let blocks := pureWZ2OrdinaryPaperOrderRegularizedBlocks safe
  let fineMass := twoScale.fine.balanced.cellMass
  let floor := pureWZ2SourceHorizontalRichFloor rho finalLoss
  let incidenceMass := twoScale.coarse.balanced.incidenceMass
  let cost := 2 * outerCost * binCost *
    PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost rho extraLoss *
    (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho)
  have hsource : volume prepared.shadow.union ≤
      4 * ∑ block : {block // block ∈ blocks},
        volume (safe.blockWindow block.1).shading.union := by
    calc
      volume prepared.shadow.union ≤
          4 * ∑ block ∈ blocks,
            volume (safe.blockWindow block).shading.union := by
        simpa [blocks] using safe.regularizedBlocks_retains_quarter
      _ = 4 * ∑ block : {block // block ∈ blocks},
          volume (safe.blockWindow block.1).shading.union := by
        rw [Finset.sum_subtype blocks (fun _ => Iff.rfl)]
  have hlocal :
      (∑ block : {block // block ∈ blocks},
          volume (safe.blockWindow block.1).shading.union) *
          fineMass * floor * incidenceMass ≤
        cost * ∑ block : {block // block ∈ blocks},
          (rich.rich block).sourcePullback.shading.mass := by
    calc
      _ = ∑ block : {block // block ∈ blocks},
          (volume (safe.blockWindow block.1).shading.union *
            fineMass * floor * incidenceMass) := by
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      _ ≤ ∑ block : {block // block ∈ blocks},
          cost * (rich.rich block).sourcePullback.shading.mass := by
        exact Finset.sum_le_sum fun block _ => by
          simpa [blocks, fineMass, floor, incidenceMass, cost] using
            rich.block_source_to_exact_mass block outerCost binCost
              (houterCost block) (hbinCost block) (hextraPower block)
      _ = cost * ∑ block : {block // block ∈ blocks},
          (rich.rich block).sourcePullback.shading.mass := by
        rw [Finset.mul_sum]
  calc
    volume prepared.shadow.union * fineMass * floor * incidenceMass ≤
        (4 * ∑ block : {block // block ∈ blocks},
          volume (safe.blockWindow block.1).shading.union) *
            fineMass * floor * incidenceMass := by gcongr
    _ = 4 * ((∑ block : {block // block ∈ blocks},
          volume (safe.blockWindow block.1).shading.union) *
            fineMass * floor * incidenceMass) := by ring
    _ ≤ 4 * (cost * ∑ block : {block // block ∈ blocks},
          (rich.rich block).sourcePullback.shading.mass) := by gcongr
    _ = 8 * outerCost * binCost *
        PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost rho extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
        ∑ block : {block // block ∈
          pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
          (rich.rich block).sourcePullback.shading.mass := by
      simp only [cost, blocks]
      ring

/-- The mod-64 chosen-bin shading inherits the exact aggregate indexed-mass
bound. -/
theorem SelectedBlockResidueData.aggregate_source_to_shading_mass
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {allBins : PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers}
    {coarseBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins}
    {selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
      (volumeLoss := volumeLoss) coarseBins}
    {rich : PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) selected}
    (residueData : rich.SelectedBlockResidueData)
    (outerCost binCost : ENNReal)
    (houterCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      (2 * (carriers.carrier block.1).outerPopular.popular.bins : ENNReal) ≤
        outerCost)
    (hbinCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((allBins.binFamily block.1).line.globalBins.card : ENNReal) *
          pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta ≤ binCost)
    (hextraPower : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((rich.pipeline block).preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow
          ((coarseBins.coarseFamily block.1).prep
            (selected.chosenBin block)).graphScale (-extraLoss)) :
    volume prepared.shadow.union * twoScale.fine.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass ≤
      512 * outerCost * binCost *
        PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost rho extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
        residueData.shading.mass := by
  calc
    _ ≤ 8 * outerCost * binCost *
        PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost rho extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
        ∑ block :
          {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
          (rich.rich block).sourcePullback.shading.mass :=
      rich.aggregate_source_to_exact_mass outerCost binCost
        houterCost hbinCost hextraPower
    _ ≤ 8 * outerCost * binCost *
        PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost rho extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
        (64 * residueData.shading.mass) := by
      gcongr
      exact residueData.total_mass_le_shading_mass
    _ = _ := by ring

/-- Cancel the complete chosen-bin aggregate cost and run the final
same-extremizer grain refinement exactly once. -/
theorem SelectedBlockResidueData.toOneScaleOfAllBinExactBudgets
    {sigma inputLoss delta rho middleLoss stickyLoss secondEta finalLoss
      normalEta theoremEta volumeLoss extraLoss structuralLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {allBins : PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers}
    {coarseBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins}
    {selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
      (volumeLoss := volumeLoss) coarseBins}
    {rich : PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) selected}
    (residueData : rich.SelectedBlockResidueData)
    (outerCost binCost : ENNReal)
    (houterCostPos : 0 < outerCost) (houterCostTop : outerCost ≠ ⊤)
    (hbinCostPos : 0 < binCost) (hbinCostTop : binCost ≠ ⊤)
    (houterCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      (2 * (carriers.carrier block.1).outerPopular.popular.bins : ENNReal) ≤
        outerCost)
    (hbinCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((allBins.binFamily block.1).line.globalBins.card : ENNReal) *
          pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta ≤ binCost)
    (hextraPower : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((rich.pipeline block).preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow
          ((coarseBins.coarseFamily block.1).prep
            (selected.chosenBin block)).graphScale (-extraLoss))
    (hrhoSmall : twoScale.rhoRequested.1 ≤ 1 / 12)
    (hsecondFraction :
      Kakeya.realRpowENN twoScale.rhoRequested.1 secondEta ≤
        wz2PaperPureRefinementFraction
          twoScale.rhoRequested.1 logExponent)
    (hcoarseSigma : twoScale.coarseLoss ≤ sigma)
    (hinputStructural : inputLoss ≤ structuralLoss)
    (hstructuralFinal : structuralLoss ≤ finalLoss)
    (grainProducer :
      ∀ targetFamily : Kakeya.Streamlined.TubeFamily delta,
        ∀ targetShading : WZ1PaperTubeShading targetFamily,
          WZ1PaperIsLineClass targetFamily →
          WZ2PaperCroppedIsExtremal
              sigma structuralLoss targetFamily targetShading →
            Nonempty
              (PureWZ2GrainRefinementData targetShading sigma finalLoss))
    (hfinalPower :
      2 * (512 * outerCost * binCost *
          PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost rho extraLoss *
          (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho)) *
          Kakeya.realRpowENN delta structuralLoss ≤
        Kakeya.realRpowENN rho
            (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
          wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta inputLoss *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          volume (wz1PaperGridCube rho (0, 0, 0)) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss) :
    Nonempty (PureWZ2LocallyLinearOneScaleData source finalLoss
      (pureWZ2SourceHorizontalFinalScale rho)) := by
  let common : ENNReal :=
    512 * outerCost * binCost *
      PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost rho extraLoss *
      (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho)
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hcellCostPos : 0 <
      PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
        rho extraLoss := by
    unfold PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
    apply ENNReal.ofReal_pos.mpr
    have hscale : 0 < 256 * rho := by positivity
    exact mul_pos
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos hscale _))
      (Real.rpow_pos_of_pos hscale _)
  have hheightCapPos : 0 <
      PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho := by
    unfold PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap
    apply ENNReal.ofReal_pos.mpr
    have hroot : 0 < Real.sqrt (256 * rho) := by positivity
    positivity
  have hcommonZero : common ≠ 0 := by
    dsimp only [common]
    positivity
  have hcellCostTop :
      PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
        rho extraLoss ≠ ⊤ := by
    unfold PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
    exact ENNReal.ofReal_ne_top
  have hheightCapTop :
      PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho ≠ ⊤ := by
    unfold PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap
    exact ENNReal.ofReal_ne_top
  have hcommonTop : common ≠ ⊤ := by
    dsimp only [common]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num) houterCostTop) hbinCostTop)
        hcellCostTop)
      (ENNReal.mul_ne_top (by norm_num) hheightCapTop)
  have haggregate := residueData.aggregate_source_to_shading_mass
    outerCost binCost houterCost hbinCost hextraPower
  have hfinal := prepared.final_mass_of_exact_incidence_budget
    hrhoSmall hsecondFraction hcoarseSigma common
    (by simpa [common] using hfinalPower)
  have hdense :
      Kakeya.realRpowENN delta structuralLoss *
          (wz1PaperBodyFamily source.family).mass ≤
        residueData.shading.mass := by
    apply (ENNReal.mul_le_mul_iff_right hcommonZero hcommonTop).mp
    calc
      common * (Kakeya.realRpowENN delta structuralLoss *
          (wz1PaperBodyFamily source.family).mass) ≤
        volume prepared.shadow.union * twoScale.fine.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass := hfinal
      _ ≤ common * residueData.shading.mass := by
        simpa [common, mul_comm, mul_left_comm, mul_assoc] using haggregate
  exact residueData.toOneScaleOfGrainProducer
    hinputStructural hstructuralFinal grainProducer hdense

end PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData

end Kakeya.Assouad

end
