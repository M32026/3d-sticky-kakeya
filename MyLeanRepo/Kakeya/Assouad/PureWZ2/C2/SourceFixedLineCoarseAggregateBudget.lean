import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseMultiWindow

/-!
# Aggregate genuine-coarse Lemma-24 mass budget

The graph-volume supply is converted to `Z_lin` volume on the genuine coarse
carrier and then to original-family indexed mass by the exact first-cover
pullback identity.  No union volume is substituted for indexed mass.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2SourceFixedLineCoarseGoodBlockFamilyData

/-- The actual graph shadow volume is controlled by its actual graph-cell
count and the stored bound for that graph's `extraCost`. -/
theorem graph_shadow_volume_le_cells
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
    volume (all.pipeline (data.safeBlock index)).prep.shadow.union ≤
      PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho data.extraLoss *
        (((all.pipeline
          (data.safeBlock index)).preparedGraph.graph.residue.cells.card : ℕ) :
          ENNReal) := by
  let pipeline := all.pipeline (data.safeBlock index)
  let scale := pipeline.prep.graphScale
  let volumeValue := volume pipeline.prep.shadow.union
  have hscale : 0 < scale := pipeline.prep.graphScale_pos
  have hball : pipeline.prep.shadow.union ⊆
      Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hcarrier : point ∈
        (family.carrierData (data.safeBlock index)).coarseCarrier.shading.union := by
      exact pipeline.prep.shadow_union_subset hpoint
    have hcoarse :=
      (family.carrierData
        (data.safeBlock index)).coarseCarrier.subshading.union_subset hcarrier
    have hnorm := norm_le_two_of_mem_paperShading hcoarse
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hvolumeTop : volumeValue ≠ ⊤ :=
    ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
      (measure_mono hball)
  have hvolumeOfReal : ENNReal.ofReal volumeValue.toReal = volumeValue :=
    ENNReal.ofReal_toReal hvolumeTop
  have hraw := pipeline.preparedGraph.graph.residue.cell_count_from_volume
    pipeline.prep.graphScale_one volumeValue.toReal ENNReal.toReal_nonneg
    (by simpa [volumeValue] using hvolumeOfReal.le)
  have hextraPos :
      0 < (pipeline.preparedGraph.graph.residue.extraCost : ℝ) := by
    exact_mod_cast pipeline.preparedGraph.graph.residue.extraCost_pos
  have hpowerPos : 0 < Real.rpow scale (5 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hscale _
  have hactualPos :
      0 < 8 * (pipeline.preparedGraph.graph.residue.extraCost : ℝ) *
        Real.rpow scale (5 / 2 : ℝ) := by positivity
  have hdenominatorLe :
      8 * (pipeline.preparedGraph.graph.residue.extraCost : ℝ) *
          Real.rpow scale (5 / 2 : ℝ) ≤
        8 * Real.rpow scale (-data.extraLoss) *
          Real.rpow scale (5 / 2 : ℝ) := by
    gcongr
    exact data.extraCost_power index
  have hreal : volumeValue.toReal ≤
      (8 * Real.rpow scale (-data.extraLoss) *
          Real.rpow scale (5 / 2 : ℝ)) *
        ((pipeline.preparedGraph.graph.residue.cells.card : ℕ) : ℝ) := by
    calc
      volumeValue.toReal ≤
          (8 * (pipeline.preparedGraph.graph.residue.extraCost : ℝ) *
            Real.rpow scale (5 / 2 : ℝ)) *
            ((pipeline.preparedGraph.graph.residue.cells.card : ℕ) : ℝ) :=
        by simpa [mul_comm] using (div_le_iff₀ hactualPos).mp hraw
      _ ≤ (8 * Real.rpow scale (-data.extraLoss) *
            Real.rpow scale (5 / 2 : ℝ)) *
            ((pipeline.preparedGraph.graph.residue.cells.card : ℕ) : ℝ) := by
        gcongr
  have hscaleEq : scale = 256 * rho := by
    dsimp only [scale]
    exact pipeline.prep.graphScale_eq
  have hcoefficientNonneg :
      0 ≤ 8 * Real.rpow scale (-data.extraLoss) *
        Real.rpow scale (5 / 2 : ℝ) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hscale.le _))
      (Real.rpow_nonneg hscale.le _)
  calc
    volume pipeline.prep.shadow.union =
        ENNReal.ofReal volumeValue.toReal := by rw [hvolumeOfReal]
    _ ≤ ENNReal.ofReal
        ((8 * Real.rpow scale (-data.extraLoss) *
            Real.rpow scale (5 / 2 : ℝ)) *
          ((pipeline.preparedGraph.graph.residue.cells.card : ℕ) : ℝ)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho data.extraLoss *
        ((pipeline.preparedGraph.graph.residue.cells.card : ℕ) : ENNReal) := by
      rw [ENNReal.ofReal_mul hcoefficientNonneg, ENNReal.ofReal_natCast]
      simp [PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost, hscaleEq]

/-- Snapped graph heights lie in the common graph window and hence have the
usual `O(rho^-1/2)` bound. -/
theorem snapped_heights_le_cap
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
    (((wz1Lemma23SnappedHeights
      (all.pipeline
        (data.safeBlock index)).preparedGraph.graph.residue.cells).card : ℕ) :
        ENNReal) ≤
      PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho := by
  let pipeline := all.pipeline (data.safeBlock index)
  have hreal := wz1Lemma23_height_layer_count
    pipeline.prep.graphScale_pos pipeline.prep.graphScale_one
    (pipeline.prep.windowed.residue_cells_window
      pipeline.preparedGraph.graph.residue)
  have hscaleEq : pipeline.prep.graphScale = 256 * rho :=
    pipeline.prep.graphScale_eq
  have henn := ENNReal.natCast_le_ofReal
    (by
      intro hzero
      have : (wz1Lemma23SnappedHeights
          pipeline.preparedGraph.graph.residue.cells).Nonempty := by
        rcases (data.rich index).richCells.graphCells_nonempty with
          ⟨cell, hcell⟩
        exact ⟨cell.2.2, Finset.mem_image.mpr
          ⟨cell, (data.rich index).richCells.graphCells_subset hcell, rfl⟩⟩
      exact this.card_ne_zero hzero) |>.mpr hreal
  simpa [PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap,
    hscaleEq] using henn

/-- One actual graph shadow controls the indexed mass of its exact source
pullback after the graph-cell, `Z_lin`, and first-cover cross identities. -/
theorem block_graph_to_source_mass_bound
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
          volume (wz1PaperGridCube rho (0, 0, 0)) *
          twoScale.coarse.refined.mass ≤
      PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho data.extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
        (data.rich index).sourcePullback.shading.mass *
        volume twoScale.coarse.croppedCoarseShading.union := by
  let pipeline := all.pipeline (data.safeBlock index)
  let rich := data.rich index
  let cellCost :=
    PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
      rho data.extraLoss
  let heightCap :=
    PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho
  let floor := pureWZ2SourceHorizontalRichFloor rho finalLoss
  let cubeVolume := volume (wz1PaperGridCube rho (0, 0, 0))
  have hvolumeCells := data.graph_shadow_volume_le_cells index
  have hfloor : floor =
      Kakeya.realRpowENN rich.ready.ready.deltaGraph (finalLoss - 1) := by
    dsimp only [floor]
    unfold pureWZ2SourceHorizontalRichFloor
    rw [rich.ready.ready.deltaGraph_eq, pipeline.prep.graphScale_eq]
  have hweightedGraph :
      floor * (pipeline.preparedGraph.graph.residue.cells.card : ENNReal) *
          cubeVolume ≤
        54 * (wz1Lemma23SnappedHeights
            pipeline.preparedGraph.graph.residue.cells).card *
          volume rich.richShading.shading.union := by
    calc
      floor * (pipeline.preparedGraph.graph.residue.cells.card : ENNReal) *
            cubeVolume ≤
          (rich.rich.heightIndices.card : ENNReal) *
            (pipeline.preparedGraph.graph.residue.cells.card : ENNReal) *
              cubeVolume := by
        gcongr
        rw [hfloor]
        simpa [rich.rich.heightIndices_card] using rich.rich.richF_card
      _ = (((rich.rich.heightIndices.card *
              pipeline.preparedGraph.graph.residue.cells.card : ℕ) : ENNReal) *
            cubeVolume) := by
        push_cast
        ring
      _ ≤ 54 * (wz1Lemma23SnappedHeights
            pipeline.preparedGraph.graph.residue.cells).card *
          volume rich.richShading.shading.union := by
        simpa [cubeVolume] using rich.richShading.graph_weighted_volume_lower
  have hheight :
      54 * (wz1Lemma23SnappedHeights
            pipeline.preparedGraph.graph.residue.cells).card *
          volume rich.richShading.shading.union ≤
        (54 * heightCap) * volume rich.richShading.shading.union := by
    gcongr
    simpa [heightCap] using data.snapped_heights_le_cap index
  have hcross :
      volume rich.richShading.shading.union *
          twoScale.coarse.refined.mass =
        rich.sourcePullback.shading.mass *
          volume twoScale.coarse.croppedCoarseShading.union := by
    symm
    simpa [rich.sourcePullback.selectedRegion_eq_coarse] using
      rich.sourcePullback.mass_cross
  calc
    volume pipeline.prep.shadow.union * floor * cubeVolume *
          twoScale.coarse.refined.mass ≤
        (cellCost *
          (pipeline.preparedGraph.graph.residue.cells.card : ENNReal)) *
            floor * cubeVolume * twoScale.coarse.refined.mass := by
      gcongr
    _ = cellCost *
        (floor *
          (pipeline.preparedGraph.graph.residue.cells.card : ENNReal) *
            cubeVolume) * twoScale.coarse.refined.mass := by ring
    _ ≤ cellCost *
        (54 * (wz1Lemma23SnappedHeights
            pipeline.preparedGraph.graph.residue.cells).card *
          volume rich.richShading.shading.union) *
            twoScale.coarse.refined.mass := by
      gcongr
    _ ≤ cellCost * ((54 * heightCap) *
          volume rich.richShading.shading.union) *
            twoScale.coarse.refined.mass := by
      gcongr
    _ = cellCost * (54 * heightCap) *
        rich.sourcePullback.shading.mass *
          volume twoScale.coarse.croppedCoarseShading.union := by
      calc
        _ = cellCost * (54 * heightCap) *
            (volume rich.richShading.shading.union *
              twoScale.coarse.refined.mass) := by ring
        _ = _ := by rw [hcross]; ring

/-- Sum the exact graph supplies through genuine coarse `Z_lin` regions and
their exact original-family pullbacks. -/
theorem aggregate_source_mass_bound
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
          volume (wz1PaperGridCube rho (0, 0, 0)) *
          twoScale.coarse.refined.mass ≤
      4 * outerCost *
        pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho data.extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
        (∑ index : Fin data.indexCount,
          (data.rich index).sourcePullback.shading.mass) *
        volume twoScale.coarse.croppedCoarseShading.union := by
  let cost := pureWZ2SourceHorizontalVolumeCost
    rho delta sigma inputLoss
  let cellCost :=
    PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
      rho data.extraLoss
  let heightCap :=
    PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho
  let floor := pureWZ2SourceHorizontalRichFloor rho finalLoss
  let cubeVolume := volume (wz1PaperGridCube rho (0, 0, 0))
  let coarseMass := twoScale.coarse.refined.mass
  let coarseVolume := volume twoScale.coarse.croppedCoarseShading.union
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
            floor * cubeVolume * coarseMass ≤
        cellCost * (54 * heightCap) *
          (∑ index : Fin data.indexCount,
            (data.rich index).sourcePullback.shading.mass) * coarseVolume := by
    calc
      _ = ∑ index : Fin data.indexCount,
          (volume (all.pipeline (data.safeBlock index)).prep.shadow.union *
            floor * cubeVolume * coarseMass) := by
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      _ ≤ ∑ index : Fin data.indexCount,
          (cellCost * (54 * heightCap) *
            (data.rich index).sourcePullback.shading.mass * coarseVolume) := by
        exact Finset.sum_le_sum fun index _ => by
          simpa [cellCost, heightCap, floor, cubeVolume, coarseMass,
            coarseVolume] using data.block_graph_to_source_mass_bound index
      _ = cellCost * (54 * heightCap) *
          (∑ index : Fin data.indexCount,
            (data.rich index).sourcePullback.shading.mass) * coarseVolume := by
        rw [← Finset.sum_mul, Finset.mul_sum]
  calc
    volume prepared.shadow.union * twoScale.fine.balanced.cellMass *
          floor * cubeVolume * coarseMass ≤
        (2 * outerCost * cost * allGraph) * floor * cubeVolume *
          coarseMass := by gcongr
    _ ≤ (2 * outerCost * cost * (2 * goodGraph)) * floor * cubeVolume *
          coarseMass := by gcongr
    _ = 4 * outerCost * cost *
        (goodGraph * floor * cubeVolume * coarseMass) := by ring
    _ = 4 * outerCost * cost *
        ((∑ index : Fin data.indexCount,
          volume (all.pipeline (data.safeBlock index)).prep.shadow.union) *
            floor * cubeVolume * coarseMass) := by rw [hgoodIndexed]
    _ ≤ 4 * outerCost * cost *
        (cellCost * (54 * heightCap) *
          (∑ index : Fin data.indexCount,
            (data.rich index).sourcePullback.shading.mass) * coarseVolume) := by
      gcongr
    _ = 4 * outerCost *
        pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho data.extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
        (∑ index : Fin data.indexCount,
          (data.rich index).sourcePullback.shading.mass) *
        volume twoScale.coarse.croppedCoarseShading.union := by
      simp only [cost, cellCost, heightCap, coarseVolume]
      ring

/-- The final mod-64 residue inherits the aggregate exact-pullback mass
bound. -/
theorem PureWZ2SourceFixedLineCoarseBlockResidueData.aggregate_source_mass_bound
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
          volume (wz1PaperGridCube rho (0, 0, 0)) *
          twoScale.coarse.refined.mass ≤
      256 * outerCost *
        pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho data.extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
        residueData.shading.mass *
        volume twoScale.coarse.croppedCoarseShading.union := by
  calc
    _ ≤ 4 * outerCost *
        pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho data.extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
        (∑ index : Fin data.indexCount,
          (data.rich index).sourcePullback.shading.mass) *
        volume twoScale.coarse.croppedCoarseShading.union :=
      data.aggregate_source_mass_bound hbad outerCost houterCost
    _ ≤ 4 * outerCost *
        pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho data.extraLoss *
        (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
        (64 * residueData.shading.mass) *
        volume twoScale.coarse.croppedCoarseShading.union := by
      gcongr
      exact residueData.total_mass_le_shading_mass
    _ = _ := by ring

/-- Cancel the finite graph, height, and coarse-volume costs only after the
exact source-pullback mass has been assembled, then perform the single final
same-extremizer grain refinement. -/
theorem PureWZ2SourceFixedLineCoarseBlockResidueData.toOneScaleOfAggregateBudgets
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
            volume (wz1PaperGridCube rho (0, 0, 0)) *
            twoScale.coarse.refined.mass ≤
        256 * outerCost *
          pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
            rho data.extraLoss *
          (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
          residueData.shading.mass *
          volume twoScale.coarse.croppedCoarseShading.union)
    (hfinalAbsorb :
      (256 * outerCost *
          pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
            rho data.extraLoss *
          (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho)) *
          (Kakeya.realRpowENN delta structuralLoss *
            (wz1PaperBodyFamily source.family).mass) *
          volume twoScale.coarse.croppedCoarseShading.union ≤
        volume prepared.shadow.union * twoScale.fine.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          volume (wz1PaperGridCube rho (0, 0, 0)) *
          twoScale.coarse.refined.mass) :
    Nonempty (PureWZ2LocallyLinearOneScaleData source finalLoss
      (pureWZ2SourceHorizontalFinalScale rho)) := by
  let common : ENNReal :=
    256 * outerCost *
      pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
      PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
        rho data.extraLoss *
      (54 * PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho) *
      volume twoScale.coarse.croppedCoarseShading.union
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
    have hfirst : 0 < Real.rpow (256 * rho) (-data.extraLoss) :=
      Real.rpow_pos_of_pos hscale _
    have hsecond : 0 < Real.rpow (256 * rho) (5 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hscale _
    positivity
  have hheightCapPos : 0 <
      PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho := by
    unfold PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap
    apply ENNReal.ofReal_pos.mpr
    have hroot : 0 < Real.sqrt (256 * rho) := by positivity
    positivity
  have hcoarseVolumePos : 0 <
      volume twoScale.coarse.croppedCoarseShading.union := by
    have hpowerPos : 0 < Kakeya.realRpowENN
        twoScale.rhoRequested.1 (sigma + twoScale.coarseLoss) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos
        twoScale.coarseGrains.extremal.delta_pos _)
    exact hpowerPos.trans_le twoScale.coarse.coarse_volume_lower
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
  have hcoarseVolumeTop :
      volume twoScale.coarse.croppedCoarseShading.union ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (by simp [Kakeya.realRpowENN])
      twoScale.coarse.coarse_extremal.volume_upper
  have hcommonTop : common ≠ ⊤ := by
    dsimp only [common]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top (by norm_num) houterCostTop) hvolumeCostTop)
          hcellCostTop)
        (ENNReal.mul_ne_top (by norm_num) hheightCapTop))
      hcoarseVolumeTop
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
          volume (wz1PaperGridCube rho (0, 0, 0)) *
          twoScale.coarse.refined.mass := by
        simpa [common, mul_comm, mul_left_comm, mul_assoc] using hfinalAbsorb
      _ ≤ common * residueData.shading.mass := by
        simpa [common, mul_comm, mul_left_comm, mul_assoc] using haggregate
  exact residueData.toOneScaleOfGrainProducer
    hinputStructural hstructuralFinal grainProducer hdense

end PureWZ2SourceFixedLineCoarseGoodBlockFamilyData

end Kakeya.Assouad

end
