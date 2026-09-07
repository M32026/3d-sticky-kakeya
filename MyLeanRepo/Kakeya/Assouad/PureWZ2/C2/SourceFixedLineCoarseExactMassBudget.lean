import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseAggregateBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.BalancedSafeCoarsePullbackBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalRelativeMassBudget

/-!
# Exact indexed-mass budget for the genuine-coarse construction

This sharpened form identifies the active cells of each exact source pullback
with the corresponding `Z_lin` owner cells.  It therefore converts graph-cell
count directly to original-family indexed mass, without an auxiliary physical
cube-volume factor.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The exact coarse-pullback structural supply forces at least half of the
genuine-coarse graph volume into graph-good blocks. -/
theorem PureWZ2SourceFixedLineCoarseAllBlockData.goodGraphBudget_of_coarse_pullback_power
    {sigma inputLoss delta rho middleLoss stickyLoss secondEta normalEta
      volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    (all : PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family)
    (hrhoSmall : twoScale.rhoRequested.1 ≤ 1 / 12)
    (hsecondFraction :
      Kakeya.realRpowENN twoScale.rhoRequested.1 secondEta ≤
        wz2PaperPureRefinementFraction
          twoScale.rhoRequested.1 logExponent)
    (hcoarseSigma : twoScale.coarseLoss ≤ sigma)
    (outerCost : ENNReal)
    (houterCostPos : 0 < outerCost)
    (houterCostTop : outerCost ≠ ⊤)
    (houterCost : ∀ block : {block // block ∈ safe.blocks},
      (2 * (family.carrierData block).outerPopular.popular.bins : ENNReal) ≤
        outerCost)
    (hpower :
      4 * outerCost *
          pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          (safe.blocks.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss) *
          volume twoScale.coarse.refined.union ≤
        Kakeya.realRpowENN rho
            (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss)) :
    2 * ((safe.blocks.card : ENNReal) *
        Kakeya.realRpowENN (256 * rho)
          (1 + sigma / 2 + volumeLoss)) ≤
      ∑ block : {block // block ∈ safe.blocks},
        volume (all.pipeline block).prep.shadow.union := by
  let cost := pureWZ2SourceHorizontalVolumeCost
    rho delta sigma inputLoss
  let threshold := Kakeya.realRpowENN (256 * rho)
    (1 + sigma / 2 + volumeLoss)
  let refinedVolume := volume twoScale.coarse.refined.union
  let allGraph := ∑ block : {block // block ∈ safe.blocks},
    volume (all.pipeline block).prep.shadow.union
  let common : ENNReal := 2 * outerCost * cost * refinedVolume
  have hstruct := prepared.coarse_pullback_graph_supply_lower
    hrhoSmall hsecondFraction hcoarseSigma
  have hallRaw := all.aggregate_graph_supply
  have hweighted :
      2 * ∑ block : {block // block ∈ safe.blocks},
          (2 * (family.carrierData block).outerPopular.popular.bins : ℕ) *
            (cost * volume (all.pipeline block).prep.shadow.union) ≤
        2 * outerCost * cost * allGraph := by
    calc
      _ ≤ 2 * ∑ block : {block // block ∈ safe.blocks},
          outerCost * (cost * volume (all.pipeline block).prep.shadow.union) := by
        gcongr with block
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using houterCost block
      _ = 2 * outerCost * cost * allGraph := by
        calc
          _ = ∑ block : {block // block ∈ safe.blocks},
              (2 * outerCost * cost) *
                volume (all.pipeline block).prep.shadow.union := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro _ _
              ring
          _ = (2 * outerCost * cost) * allGraph := by
            rw [Finset.mul_sum]
          _ = _ := by ring
  have hall : volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
          volume twoScale.coarse.refined.union ≤
        2 * outerCost * cost * allGraph * refinedVolume := by
    calc
      _ ≤ (2 * ∑ block : {block // block ∈ safe.blocks},
          (2 * (family.carrierData block).outerPopular.popular.bins : ℕ) *
            (cost * volume (all.pipeline block).prep.shadow.union)) *
          volume twoScale.coarse.refined.union := by gcongr
      _ ≤ (2 * outerCost * cost * allGraph) *
          volume twoScale.coarse.refined.union := by gcongr
      _ = (2 * outerCost * cost * allGraph) * refinedVolume := rfl
  have hscaled :
      common * (2 * ((safe.blocks.card : ENNReal) * threshold)) ≤
        common * allGraph := by
    calc
      common * (2 * ((safe.blocks.card : ENNReal) * threshold)) =
          4 * outerCost * cost * (safe.blocks.card : ENNReal) * threshold *
            refinedVolume := by simp only [common]; ring
      _ ≤ Kakeya.realRpowENN rho
            (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) := by
        simpa [cost, threshold, refinedVolume, mul_assoc] using hpower
      _ ≤ volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
          volume twoScale.coarse.refined.union := hstruct
      _ ≤ 2 * outerCost * cost * allGraph * refinedVolume := hall
      _ = common * allGraph := by simp only [common]; ring
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hcostPos : 0 < cost := by
    exact pureWZ2SourceHorizontalVolumeCost_pos
      hrho source.extremal.delta_pos
  have hrefinedVolumePos : 0 < refinedVolume := by
    have hpowerPos : 0 < Kakeya.realRpowENN delta
        (sigma + twoScale.coarseLoss) :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos source.extremal.delta_pos _)
    exact hpowerPos.trans_le (by
      simpa [refinedVolume] using twoScale.coarse.refined_volume_lower)
  have hcommonZero : common ≠ 0 := by
    dsimp only [common]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) houterCostPos.ne') hcostPos.ne')
      hrefinedVolumePos.ne'
  have hcostTop : cost ≠ ⊤ :=
    pureWZ2SourceHorizontalVolumeCost_ne_top _ _ _ _
  have hrefinedVolumeTop : refinedVolume ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (by simp [Kakeya.realRpowENN])
      twoScale.coarse.refined_extremal.volume_upper
  have hcommonTop : common ≠ ⊤ := by
    dsimp only [common]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) houterCostTop) hcostTop)
      hrefinedVolumeTop
  exact (ENNReal.mul_le_mul_iff_right hcommonZero hcommonTop).mp hscaled

/-- The existing same-relative-density structural bound already supplies the
exact incidence-mass target: the first balanced multiplicity lower band turns
`coarseCellMass * fineMultiplicity` into `incidenceMass`. -/
theorem PureWZ2SourceCarrierPreparation.final_mass_of_exact_incidence_budget
    {sigma inputLoss delta rho middleLoss stickyLoss secondEta finalLoss
      structuralLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (hrhoSmall : twoScale.rhoRequested.1 ≤ 1 / 12)
    (hsecondFraction :
      Kakeya.realRpowENN twoScale.rhoRequested.1 secondEta ≤
        wz2PaperPureRefinementFraction
          twoScale.rhoRequested.1 logExponent)
    (hcoarseSigma : twoScale.coarseLoss ≤ sigma)
    (cost : ENNReal)
    (hpower :
      2 * cost * Kakeya.realRpowENN delta structuralLoss ≤
        Kakeya.realRpowENN rho
            (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
          wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta inputLoss *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          volume (wz1PaperGridCube rho (0, 0, 0)) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss) :
    cost *
          (Kakeya.realRpowENN delta structuralLoss *
            (wz1PaperBodyFamily source.family).mass) ≤
      volume prepared.shadow.union * twoScale.fine.balanced.cellMass *
        pureWZ2SourceHorizontalRichFloor rho finalLoss *
        twoScale.coarse.balanced.incidenceMass := by
  have hbase := prepared.final_mass_of_relative_budget
    hrhoSmall hsecondFraction hcoarseSigma cost hpower
  have hband := twoScale.coarse.balanced_incidenceMass_band.1
  calc
    cost *
          (Kakeya.realRpowENN delta structuralLoss *
            (wz1PaperBodyFamily source.family).mass) ≤
        volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
          twoScale.coarse.balanced.cellMass *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss := hbase
    _ = volume prepared.shadow.union *
        twoScale.fine.balanced.cellMass *
        pureWZ2SourceHorizontalRichFloor rho finalLoss *
        ((twoScale.coarse.fineMultiplicity : ENNReal) *
          twoScale.coarse.balanced.cellMass) := by ring
    _ ≤ volume prepared.shadow.union *
        twoScale.fine.balanced.cellMass *
        pureWZ2SourceHorizontalRichFloor rho finalLoss *
        twoScale.coarse.balanced.incidenceMass := by gcongr

namespace PureWZ2SourceFixedLineCoarseGoodBlockFamilyData

/-- The exact pullback has precisely the `Z_lin` owner cells as active cells. -/
theorem sourcePullback_selectedCells_eq
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family}
    (data : PureWZ2SourceFixedLineCoarseGoodBlockFamilyData
      (finalLoss := finalLoss) (theoremEta := theoremEta)
      (volumeLoss := volumeLoss) all)
    (index : Fin data.indexCount) :
    (data.rich index).sourcePullback.selectedCells =
      (data.rich index).richCells.cells := by
  let rich := data.rich index
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

/-- The actual graph-cell count, after the `Z_lin` height floor, controls the
exact source-pullback indexed mass. -/
theorem graph_cells_to_source_mass
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family}
    (data : PureWZ2SourceFixedLineCoarseGoodBlockFamilyData
      (finalLoss := finalLoss) (theoremEta := theoremEta)
      (volumeLoss := volumeLoss) all)
    (index : Fin data.indexCount) :
    pureWZ2SourceHorizontalRichFloor rho finalLoss *
          ((all.pipeline
            (data.safeBlock index)).preparedGraph.graph.residue.cells.card :
              ENNReal) *
          twoScale.coarse.balanced.incidenceMass ≤
      54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho *
        (data.rich index).sourcePullback.shading.mass := by
  let pipeline := all.pipeline (data.safeBlock index)
  let rich := data.rich index
  let floor := pureWZ2SourceHorizontalRichFloor rho finalLoss
  let heightCap :=
    PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho
  have hfloor : floor =
      Kakeya.realRpowENN rich.ready.ready.deltaGraph (finalLoss - 1) := by
    dsimp only [floor]
    unfold pureWZ2SourceHorizontalRichFloor
    rw [rich.ready.ready.deltaGraph_eq, pipeline.prep.graphScale_eq]
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
  have hheight :
      ((wz1Lemma23SnappedHeights
          pipeline.preparedGraph.graph.residue.cells).card : ENNReal) ≤
        heightCap := by
    simpa [heightCap] using data.snapped_heights_le_cap index
  calc
    floor *
          (pipeline.preparedGraph.graph.residue.cells.card : ENNReal) *
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
      rw [rich.sourcePullback.mass_eq, data.sourcePullback_selectedCells_eq index]
      ring

/-- One genuine graph shadow controls its exact source indexed mass without
an extra physical cube-volume factor. -/
theorem block_graph_to_exact_source_mass_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family}
    (data : PureWZ2SourceFixedLineCoarseGoodBlockFamilyData
      (finalLoss := finalLoss) (theoremEta := theoremEta)
      (volumeLoss := volumeLoss) all)
    (index : Fin data.indexCount) :
    volume (all.pipeline (data.safeBlock index)).prep.shadow.union *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass ≤
      PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho data.extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
        (data.rich index).sourcePullback.shading.mass := by
  calc
    _ ≤ (PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho data.extraLoss *
        ((all.pipeline
          (data.safeBlock index)).preparedGraph.graph.residue.cells.card :
            ENNReal)) *
        pureWZ2SourceHorizontalRichFloor rho finalLoss *
        twoScale.coarse.balanced.incidenceMass := by
      gcongr
      exact data.graph_shadow_volume_le_cells index
    _ = PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho data.extraLoss *
        (pureWZ2SourceHorizontalRichFloor rho finalLoss *
          ((all.pipeline
            (data.safeBlock index)).preparedGraph.graph.residue.cells.card :
              ENNReal) * twoScale.coarse.balanced.incidenceMass) := by ring
    _ ≤ PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho data.extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho *
          (data.rich index).sourcePullback.shading.mass) := by
      exact mul_le_mul_left' (data.graph_cells_to_source_mass index) _
    _ = _ := by ring

/-- Sum the exact source-mass bounds over all good genuine-coarse blocks. -/
theorem aggregate_exact_source_mass_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family}
    (data : PureWZ2SourceFixedLineCoarseGoodBlockFamilyData
      (finalLoss := finalLoss) (theoremEta := theoremEta)
      (volumeLoss := volumeLoss) all)
    (hbad :
      2 * ((safe.blocks.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) ≤
        ∑ block : {block // block ∈ safe.blocks},
          volume (all.pipeline block).prep.shadow.union)
    (outerCost : ENNReal)
    (houterCost : ∀ block : {block // block ∈ safe.blocks},
      (2 * (family.carrierData block).outerPopular.popular.bins : ENNReal) ≤
        outerCost) :
    volume prepared.shadow.union * twoScale.fine.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass ≤
      4 * outerCost *
        pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho data.extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
        ∑ index : Fin data.indexCount,
          (data.rich index).sourcePullback.shading.mass := by
  let cost := pureWZ2SourceHorizontalVolumeCost
    rho delta sigma inputLoss
  let cellCost :=
    PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
      rho data.extraLoss
  let heightCap :=
    PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho
  let floor := pureWZ2SourceHorizontalRichFloor rho finalLoss
  let incidenceMass := twoScale.coarse.balanced.incidenceMass
  let allGraph := ∑ block : {block // block ∈ safe.blocks},
    volume (all.pipeline block).prep.shadow.union
  let goodGraph := ∑ block ∈
      pureWZ2SourceFixedLineCoarseGoodGraphBlocks all volumeLoss,
    volume (all.pipeline block).prep.shadow.union
  have hallRaw := all.aggregate_graph_supply
  have hweighted :
      2 * ∑ block : {block // block ∈ safe.blocks},
          (2 * (family.carrierData block).outerPopular.popular.bins : ℕ) *
            (cost * volume (all.pipeline block).prep.shadow.union) ≤
        2 * outerCost * cost * allGraph := by
    calc
      2 * ∑ block : {block // block ∈ safe.blocks},
          (2 * (family.carrierData block).outerPopular.popular.bins : ℕ) *
            (cost * volume (all.pipeline block).prep.shadow.union) ≤
        2 * ∑ block : {block // block ∈ safe.blocks},
          outerCost * (cost * volume (all.pipeline block).prep.shadow.union) := by
        gcongr with block
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using houterCost block
      _ = 2 * outerCost * cost * allGraph := by
        calc
          _ = ∑ block : {block // block ∈ safe.blocks},
              (2 * outerCost * cost) *
                volume (all.pipeline block).prep.shadow.union := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro block _
              ring
          _ = (2 * outerCost * cost) * allGraph := by
            rw [Finset.mul_sum]
          _ = _ := by ring
  have hall :
      volume prepared.shadow.union * twoScale.fine.balanced.cellMass ≤
        2 * outerCost * cost * allGraph :=
    hallRaw.trans (by simpa [cost, allGraph] using hweighted)
  have hgood : allGraph ≤ 2 * goodGraph := by
    simpa [allGraph, goodGraph] using all.goodGraphBlocks_retains_half hbad
  have hgoodIndexed : goodGraph =
      ∑ index : Fin data.indexCount,
        volume (all.pipeline
          (data.safeBlock index)).prep.shadow.union := by
    symm
    dsimp only [goodGraph]
    apply Finset.sum_bij (fun index _ => data.safeBlock index)
    · exact fun index _ => data.block_mem index
    · exact fun first _ second _ heq => data.safeBlock_injective heq
    · intro block hblock
      rcases data.block_surjective block hblock with ⟨index, heq⟩
      exact ⟨index, Finset.mem_univ index, heq⟩
    · intro _ _
      rfl
  have hlocal :
      (∑ index : Fin data.indexCount,
          volume (all.pipeline (data.safeBlock index)).prep.shadow.union) *
            floor * incidenceMass ≤
        cellCost * (54 * heightCap) *
          ∑ index : Fin data.indexCount,
            (data.rich index).sourcePullback.shading.mass := by
    calc
      _ = ∑ index : Fin data.indexCount,
          (volume (all.pipeline (data.safeBlock index)).prep.shadow.union *
            floor * incidenceMass) := by
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ ∑ index : Fin data.indexCount,
          (cellCost * (54 * heightCap) *
            (data.rich index).sourcePullback.shading.mass) := by
        exact Finset.sum_le_sum fun index _ => by
          simpa [cellCost, heightCap, floor, incidenceMass] using
            data.block_graph_to_exact_source_mass_bound index
      _ = cellCost * (54 * heightCap) *
          ∑ index : Fin data.indexCount,
            (data.rich index).sourcePullback.shading.mass := by
        rw [Finset.mul_sum]
  calc
    volume prepared.shadow.union * twoScale.fine.balanced.cellMass *
          floor * incidenceMass ≤
        (2 * outerCost * cost * allGraph) * floor * incidenceMass := by
      gcongr
    _ ≤ (2 * outerCost * cost * (2 * goodGraph)) * floor *
          incidenceMass := by gcongr
    _ = 4 * outerCost * cost *
        (goodGraph * floor * incidenceMass) := by ring
    _ = 4 * outerCost * cost *
        ((∑ index : Fin data.indexCount,
          volume (all.pipeline (data.safeBlock index)).prep.shadow.union) *
            floor * incidenceMass) := by rw [hgoodIndexed]
    _ ≤ 4 * outerCost * cost *
        (cellCost * (54 * heightCap) *
          ∑ index : Fin data.indexCount,
            (data.rich index).sourcePullback.shading.mass) := by
      gcongr
    _ = _ := by
      simp only [cost, cellCost, heightCap]
      ring

/-- The final mod-64 source shading inherits the exact aggregate indexed-mass
bound. -/
theorem PureWZ2SourceFixedLineCoarseBlockResidueData.aggregate_exact_source_mass_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family}
    {data : PureWZ2SourceFixedLineCoarseGoodBlockFamilyData
      (finalLoss := finalLoss) (theoremEta := theoremEta)
      (volumeLoss := volumeLoss) all}
    (residueData : PureWZ2SourceFixedLineCoarseBlockResidueData data)
    (hbad :
      2 * ((safe.blocks.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) ≤
        ∑ block : {block // block ∈ safe.blocks},
          volume (all.pipeline block).prep.shadow.union)
    (outerCost : ENNReal)
    (houterCost : ∀ block : {block // block ∈ safe.blocks},
      (2 * (family.carrierData block).outerPopular.popular.bins : ENNReal) ≤
        outerCost) :
    volume prepared.shadow.union * twoScale.fine.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass ≤
      256 * outerCost *
        pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho data.extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
        residueData.shading.mass := by
  calc
    _ ≤ 4 * outerCost *
        pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho data.extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
        ∑ index : Fin data.indexCount,
          (data.rich index).sourcePullback.shading.mass :=
      data.aggregate_exact_source_mass_bound hbad outerCost houterCost
    _ ≤ 4 * outerCost *
        pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho data.extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
        (64 * residueData.shading.mass) := by
      gcongr
      exact residueData.total_mass_le_shading_mass
    _ = _ := by ring

/-- Cancel the exact aggregate cost and run the single final grain refinement
on the selected original-family shading. -/
theorem PureWZ2SourceFixedLineCoarseBlockResidueData.toOneScaleOfExactAggregateBudgets
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss structuralLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2SourceFixedLineCoarseAllBlockData
      (normalEta := normalEta) family}
    {data : PureWZ2SourceFixedLineCoarseGoodBlockFamilyData
      (finalLoss := finalLoss) (theoremEta := theoremEta)
      (volumeLoss := volumeLoss) all}
    (residueData : PureWZ2SourceFixedLineCoarseBlockResidueData data)
    (outerCost : ENNReal)
    (houterCostPos : 0 < outerCost)
    (houterCostTop : outerCost ≠ ⊤)
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
    (haggregate :
      volume prepared.shadow.union * twoScale.fine.balanced.cellMass *
            pureWZ2SourceHorizontalRichFloor rho finalLoss *
            twoScale.coarse.balanced.incidenceMass ≤
        256 * outerCost *
          pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
            rho data.extraLoss *
          (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
          residueData.shading.mass)
    (hfinalAbsorb :
      (256 * outerCost *
          pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
            rho data.extraLoss *
          (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho)) *
          (Kakeya.realRpowENN delta structuralLoss *
            (wz1PaperBodyFamily source.family).mass) ≤
        volume prepared.shadow.union * twoScale.fine.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass) :
    Nonempty (PureWZ2LocallyLinearOneScaleData source finalLoss
      (pureWZ2SourceHorizontalFinalScale rho)) := by
  let common : ENNReal :=
    256 * outerCost *
      pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
      PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
        rho data.extraLoss *
      (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho)
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hvolumeCostPos : 0 <
      pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss :=
    pureWZ2SourceHorizontalVolumeCost_pos hrho source.extremal.delta_pos
  have hcellCostPos : 0 <
      PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
        rho data.extraLoss := by
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
  have hvolumeCostTop :
      pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss ≠ ⊤ :=
    pureWZ2SourceHorizontalVolumeCost_ne_top _ _ _ _
  have hcellCostTop :
      PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
        rho data.extraLoss ≠ ⊤ := by
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
          (ENNReal.mul_ne_top (by norm_num) houterCostTop) hvolumeCostTop)
        hcellCostTop)
      (ENNReal.mul_ne_top (by norm_num) hheightCapTop)
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
          twoScale.coarse.balanced.incidenceMass := by
        simpa [common, mul_comm, mul_left_comm, mul_assoc] using hfinalAbsorb
      _ ≤ common * residueData.shading.mass := by
        simpa [common, mul_comm, mul_left_comm, mul_assoc] using haggregate
  exact residueData.toOneScaleOfGrainProducer
    hinputStructural hstructuralFinal grainProducer hdense

end PureWZ2SourceFixedLineCoarseGoodBlockFamilyData

end Kakeya.Assouad

end
