import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseHorizontalGoodBlocks

/-!
# Dependent rich outputs on every popular genuine-coarse block
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2CoarseHorizontalGoodBlockFamilyData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale)
    (volumeLoss : ℝ) where
  indexCount : ℕ
  indexCount_pos : 0 < indexCount
  block : Fin indexCount → ℤ
  block_injective : Function.Injective block
  pipeline : Fin indexCount →
    PureWZ2CoarseHorizontalPipelineData (eta := eta) twoScale
  rich : ∀ index, PureWZ2CoarseHorizontalRichPipelineData
    (finalLoss := finalLoss) (theoremEta := theoremEta) (pipeline index)
  extraLoss : ℝ
  extraCost_power : ∀ index,
    ((pipeline index).graph.residue.extraCost : ℝ) ≤
      Real.rpow (pipeline index).prep.graphScale (-extraLoss)
  block_mem : ∀ index, block index ∈
    pureWZ2GoodCoarseCarrierBlocks prepared volumeLoss
  block_surjective : ∀ target ∈
    pureWZ2GoodCoarseCarrierBlocks prepared volumeLoss,
      ∃ index, block index = target
  left_eq : ∀ index, (pipeline index).window.left =
    pureWZ2SourceCarrierBlockLeft rho (block index)
  volumeSupply_eq : ∀ index, (pipeline index).window.volumeSupply =
    MeasureTheory.volume
      (pureWZ2CoarseCarrierBlockShading prepared (block index)).union

namespace PureWZ2CoarseHorizontalGoodBlockFamilyData

/-- Uniform Alternative-A rich-height floor on every coarse block graph. -/
def richFloor (rho finalLoss : ℝ) : ENNReal :=
  Kakeya.realRpowENN
    (wz1Lemma23Theorem22Scale (256 * rho)) (finalLoss - 1)

/-- Uniform graph-cell floor obtained from the final residue volume. -/
def graphCellFloor
    (rho sigma volumeLoss extraLoss : ℝ) : ENNReal :=
  ENNReal.ofReal
    (Real.rpow (256 * rho) (1 + sigma / 2 + volumeLoss) /
      (8 * Real.rpow (256 * rho) (-extraLoss) *
        Real.rpow (256 * rho) (5 / 2 : ℝ)))

/-- Uniform cost converting actual graph cells back to final residue volume. -/
def graphCellCost (rho extraLoss : ℝ) : ENNReal :=
  ENNReal.ofReal
    (8 * Real.rpow (256 * rho) (-extraLoss) *
      Real.rpow (256 * rho) (5 / 2 : ℝ))

/-- Uniform upper bound for the number of snapped heights in one slab. -/
def snappedHeightCap (rho : ℝ) : ENNReal :=
  ENNReal.ofReal (3 / Real.sqrt (256 * rho))

theorem indexCount_eq_goodCard
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta
      volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    (data : PureWZ2CoarseHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      prepared volumeLoss) :
    data.indexCount =
      (pureWZ2GoodCoarseCarrierBlocks prepared volumeLoss).card := by
  let image := Finset.univ.image data.block
  have himage : image =
      pureWZ2GoodCoarseCarrierBlocks prepared volumeLoss := by
    apply Finset.ext
    intro target
    constructor
    · intro htarget
      rcases Finset.mem_image.mp htarget with ⟨index, _hindex, rfl⟩
      exact data.block_mem index
    · intro htarget
      rcases data.block_surjective target htarget with ⟨index, rfl⟩
      exact Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩
  have hcard : image.card = data.indexCount := by
    rw [Finset.card_image_of_injective _ data.block_injective]
    simp [image]
  rw [← hcard, himage]

/--
The final residue graph has the genuine number of cells forced by its volume.
The denominator uses the stored power bound for that graph's actual
`extraCost`; in particular this is not a nonemptiness/cardinality surrogate.
-/
theorem graph_cells_floor
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta
      volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    (data : PureWZ2CoarseHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      prepared volumeLoss)
    (index : Fin data.indexCount) :
    graphCellFloor rho sigma volumeLoss data.extraLoss ≤
      ((data.pipeline index).graph.residue.cells.card : ENNReal) := by
  let pipeline := data.pipeline index
  let scale := pipeline.prep.graphScale
  have hscale : 0 < scale := pipeline.prep.graphScale_pos
  have hbudget :
      Kakeya.realRpowENN pipeline.prep.graphScale
            (1 + sigma / 2 + volumeLoss) *
          pureWZ2HorizontalFixedLineVolumeCost
            twoScale.rhoRequested.1 sigma middleLoss ≤
        pureWZ2HorizontalFixedLineVolumeSupply
          pipeline.window.volumeSupply
          twoScale.rhoRequested.1 sigma stickyLoss := by
    have hgood := pureWZ2GoodCoarseCarrierBlock_budget
      (data.block_mem index)
    rw [pipeline.prep.graphScale_eq, data.volumeSupply_eq index]
    simpa [pureWZ2HorizontalFixedLineVolumeSupply,
      pureWZ2CoarseHorizontalBlockSupplyFactor,
      twoScale.rhoRequested_eq] using hgood
  have hvolumePower := pipeline.prep.power_volume_lower hbudget
  have hvolume :
      ENNReal.ofReal
          (Real.rpow scale (1 + sigma / 2 + volumeLoss)) ≤
        MeasureTheory.volume pipeline.prep.shadow.union := by
    simpa [scale, Kakeya.realRpowENN] using hvolumePower
  have hraw := pipeline.graph.residue.cell_count_from_volume
    pipeline.prep.graphScale_one
    (Real.rpow scale (1 + sigma / 2 + volumeLoss))
    (Real.rpow_nonneg hscale.le _) hvolume
  have hextraPos : 0 < (pipeline.graph.residue.extraCost : ℝ) := by
    exact_mod_cast pipeline.graph.residue.extraCost_pos
  have hupperPos :
      0 < Real.rpow scale (-data.extraLoss) :=
    Real.rpow_pos_of_pos hscale _
  have hpowerPos : 0 < Real.rpow scale (5 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hscale _
  have hdenominator :
      0 < 8 * (pipeline.graph.residue.extraCost : ℝ) *
        Real.rpow scale (5 / 2 : ℝ) := by positivity
  have hdenominatorLe :
      8 * (pipeline.graph.residue.extraCost : ℝ) *
          Real.rpow scale (5 / 2 : ℝ) ≤
        8 * Real.rpow scale (-data.extraLoss) *
          Real.rpow scale (5 / 2 : ℝ) := by
    gcongr
    exact data.extraCost_power index
  have hreal :
      Real.rpow scale (1 + sigma / 2 + volumeLoss) /
          (8 * Real.rpow scale (-data.extraLoss) *
            Real.rpow scale (5 / 2 : ℝ)) ≤
        ((pipeline.graph.residue.cells.card : ℕ) : ℝ) := by
    exact (div_le_div_of_nonneg_left
      (Real.rpow_nonneg hscale.le _) hdenominator hdenominatorLe).trans hraw
  have hscaleEq : scale = 256 * rho := by
    dsimp only [scale]
    rw [pipeline.prep.graphScale_eq, twoScale.rhoRequested_eq]
  simpa [graphCellFloor, hscaleEq] using
    (ENNReal.ofReal_le_natCast.mpr hreal)

/-- The snapped-height denominator is controlled inside the same window. -/
theorem snapped_heights_le_cap
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta
      volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    (data : PureWZ2CoarseHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      prepared volumeLoss)
    (index : Fin data.indexCount) :
    (((wz1Lemma23SnappedHeights
        (data.pipeline index).graph.residue.cells).card : ℕ) : ENNReal) ≤
      snappedHeightCap rho := by
  let pipeline := data.pipeline index
  have hreal := wz1Lemma23_height_layer_count
    pipeline.prep.graphScale_pos pipeline.prep.graphScale_one
    (pipeline.prep.windowed.residue_cells_window pipeline.graph.residue)
  have hscaleEq : pipeline.prep.graphScale = 256 * rho := by
    rw [pipeline.prep.graphScale_eq, twoScale.rhoRequested_eq]
  have henn := ENNReal.natCast_le_ofReal
    (by
      intro hzero
      have : (wz1Lemma23SnappedHeights
          pipeline.graph.residue.cells).Nonempty := by
        rcases (data.rich index).richCells.graphCells_nonempty with
          ⟨cell, hcell⟩
        exact ⟨cell.2.2, Finset.mem_image.mpr
          ⟨cell, (data.rich index).richCells.graphCells_subset hcell, rfl⟩⟩
      exact this.card_ne_zero hzero) |>.mpr hreal
  simpa [snappedHeightCap, hscaleEq] using henn

/--
The final residue volume is bounded by the actual graph-cell count.  This is
the upper-bound form of `cell_count_from_volume`, with the stored power bound
used only for the genuine graph residue's `extraCost`.
-/
theorem graph_shadow_volume_le_cells
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta
      volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    (data : PureWZ2CoarseHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      prepared volumeLoss)
    (index : Fin data.indexCount) :
    MeasureTheory.volume (data.pipeline index).prep.shadow.union ≤
      graphCellCost rho data.extraLoss *
        ((data.pipeline index).graph.residue.cells.card : ENNReal) := by
  let pipeline := data.pipeline index
  let scale := pipeline.prep.graphScale
  let volumeValue := MeasureTheory.volume pipeline.prep.shadow.union
  have hscale : 0 < scale := pipeline.prep.graphScale_pos
  have hball : pipeline.prep.shadow.union ⊆
      Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hpaper : point ∈ pipeline.residueShading.shading.union := by
      rwa [pipeline.prep.shadow_union] at hpoint
    have hnorm := norm_le_two_of_mem_paperShading hpaper
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hvolumeTop : volumeValue ≠ ⊤ :=
    ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
      (MeasureTheory.measure_mono hball)
  have hvolumeOfReal : ENNReal.ofReal volumeValue.toReal = volumeValue :=
    ENNReal.ofReal_toReal hvolumeTop
  have hraw := pipeline.graph.residue.cell_count_from_volume
    pipeline.prep.graphScale_one volumeValue.toReal ENNReal.toReal_nonneg
    (by simpa [volumeValue] using hvolumeOfReal.le)
  have hextraPos : 0 < (pipeline.graph.residue.extraCost : ℝ) := by
    exact_mod_cast pipeline.graph.residue.extraCost_pos
  have hpowerPos : 0 < Real.rpow scale (5 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hscale _
  have hactualPos :
      0 < 8 * (pipeline.graph.residue.extraCost : ℝ) *
        Real.rpow scale (5 / 2 : ℝ) := by positivity
  have hupperPos : 0 < Real.rpow scale (-data.extraLoss) :=
    Real.rpow_pos_of_pos hscale _
  have hdenominatorLe :
      8 * (pipeline.graph.residue.extraCost : ℝ) *
          Real.rpow scale (5 / 2 : ℝ) ≤
        8 * Real.rpow scale (-data.extraLoss) *
          Real.rpow scale (5 / 2 : ℝ) := by
    gcongr
    exact data.extraCost_power index
  have hreal : volumeValue.toReal ≤
      (8 * Real.rpow scale (-data.extraLoss) *
          Real.rpow scale (5 / 2 : ℝ)) *
        ((pipeline.graph.residue.cells.card : ℕ) : ℝ) := by
    calc
      volumeValue.toReal ≤
          (8 * (pipeline.graph.residue.extraCost : ℝ) *
            Real.rpow scale (5 / 2 : ℝ)) *
            ((pipeline.graph.residue.cells.card : ℕ) : ℝ) :=
        by simpa [mul_comm] using (div_le_iff₀ hactualPos).mp hraw
      _ ≤ (8 * Real.rpow scale (-data.extraLoss) *
            Real.rpow scale (5 / 2 : ℝ)) *
            ((pipeline.graph.residue.cells.card : ℕ) : ℝ) := by
        gcongr
  have hscaleEq : scale = 256 * rho := by
    dsimp only [scale]
    rw [pipeline.prep.graphScale_eq, twoScale.rhoRequested_eq]
  calc
    MeasureTheory.volume pipeline.prep.shadow.union =
        ENNReal.ofReal volumeValue.toReal := by
      rw [hvolumeOfReal]
    _ ≤ ENNReal.ofReal
        ((8 * Real.rpow scale (-data.extraLoss) *
            Real.rpow scale (5 / 2 : ℝ)) *
          ((pipeline.graph.residue.cells.card : ℕ) : ℝ)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = graphCellCost rho data.extraLoss *
          ((pipeline.graph.residue.cells.card : ℕ) : ENNReal) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      simp [graphCellCost, hscaleEq]

/-- Each completed slab carries its true graph-weighted mass floor. -/
theorem rich_mass_floor
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta
      volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    (data : PureWZ2CoarseHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      prepared volumeLoss)
    (index : Fin data.indexCount) :
    richFloor rho finalLoss *
          graphCellFloor rho sigma volumeLoss data.extraLoss *
          ((twoScale.fine.fineMultiplicity : ENNReal) *
            MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) ≤
      54 * snappedHeightCap rho *
        (data.rich index).richShading.shading.mass := by
  let rich := data.rich index
  have hfloor : richFloor rho finalLoss =
      Kakeya.realRpowENN rich.ready.ready.deltaGraph (finalLoss - 1) := by
    unfold richFloor
    rw [rich.ready.ready.deltaGraph_eq,
      (data.pipeline index).prep.graphScale_eq,
      twoScale.rhoRequested_eq]
  rw [hfloor]
  calc
    Kakeya.realRpowENN rich.ready.ready.deltaGraph (finalLoss - 1) *
          graphCellFloor rho sigma volumeLoss data.extraLoss *
          ((twoScale.fine.fineMultiplicity : ENNReal) *
            MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) ≤
        (rich.rich.heightIndices.card : ENNReal) *
          ((data.pipeline index).graph.residue.cells.card : ENNReal) *
          ((twoScale.fine.fineMultiplicity : ENNReal) *
            MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) := by
      gcongr
      · simpa [rich.rich.heightIndices_card] using rich.rich.richF_card
      · exact data.graph_cells_floor index
    _ = (((rich.rich.heightIndices.card *
            (data.pipeline index).graph.residue.cells.card : ℕ) : ENNReal) *
          ((twoScale.fine.fineMultiplicity : ENNReal) *
            MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0)))) := by
      push_cast
      ring
    _ ≤ 54 *
          ((wz1Lemma23SnappedHeights
            (data.pipeline index).graph.residue.cells).card : ENNReal) *
          rich.richShading.shading.mass :=
      rich.richShading.graph_weighted_mass_lower
    _ ≤ 54 * snappedHeightCap rho *
          rich.richShading.shading.mass := by
      gcongr
      exact data.snapped_heights_le_cap index

/--
One exact coarse-block supply is charged to the actual graph cells and then
to the rich mass.  Both the block volume and graph-cell cardinality remain
visible until the final inequality.
-/
theorem block_weighted_mass_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta
      volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    (data : PureWZ2CoarseHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      prepared volumeLoss)
    (index : Fin data.indexCount) :
    (data.pipeline index).window.volumeSupply *
          pureWZ2CoarseHorizontalBlockSupplyFactor rho sigma stickyLoss *
          richFloor rho finalLoss *
          ((twoScale.fine.fineMultiplicity : ENNReal) *
            MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) ≤
      pureWZ2HorizontalFixedLineVolumeCost rho sigma middleLoss *
          graphCellCost rho data.extraLoss *
          (54 * snappedHeightCap rho) *
          (data.rich index).richShading.shading.mass := by
  let pipeline := data.pipeline index
  let rich := data.rich index
  let cost := pureWZ2HorizontalFixedLineVolumeCost rho sigma middleLoss
  let cellCost := graphCellCost rho data.extraLoss
  let heightCap := snappedHeightCap rho
  let weightedUnit := (twoScale.fine.fineMultiplicity : ENNReal) *
    MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))
  let floor := richFloor rho finalLoss
  have hsupply := pipeline.prep.volume_supply_le
  have hsupplyRho :
      pipeline.window.volumeSupply *
          pureWZ2CoarseHorizontalBlockSupplyFactor rho sigma stickyLoss ≤
        cost * MeasureTheory.volume pipeline.prep.shadow.union := by
    simpa [cost, pureWZ2HorizontalFixedLineVolumeSupply,
      pureWZ2CoarseHorizontalBlockSupplyFactor, twoScale.rhoRequested_eq]
      using hsupply
  have hvolumeCells := data.graph_shadow_volume_le_cells index
  have hfloor : floor =
      Kakeya.realRpowENN rich.ready.ready.deltaGraph (finalLoss - 1) := by
    dsimp only [floor]
    unfold richFloor
    rw [rich.ready.ready.deltaGraph_eq, pipeline.prep.graphScale_eq,
      twoScale.rhoRequested_eq]
  have hweightedGraph :
      floor * (pipeline.graph.residue.cells.card : ENNReal) * weightedUnit ≤
        54 * (wz1Lemma23SnappedHeights
            pipeline.graph.residue.cells).card *
          rich.richShading.shading.mass := by
    calc
      floor * (pipeline.graph.residue.cells.card : ENNReal) * weightedUnit ≤
          (rich.rich.heightIndices.card : ENNReal) *
            (pipeline.graph.residue.cells.card : ENNReal) * weightedUnit := by
        gcongr
        rw [hfloor]
        simpa [rich.rich.heightIndices_card] using rich.rich.richF_card
      _ = (((rich.rich.heightIndices.card *
              pipeline.graph.residue.cells.card : ℕ) : ENNReal) *
            weightedUnit) := by
        push_cast
        ring
      _ ≤ 54 * (wz1Lemma23SnappedHeights
            pipeline.graph.residue.cells).card *
          rich.richShading.shading.mass := by
        simpa [weightedUnit] using rich.richShading.graph_weighted_mass_lower
  have hheightMass :
      54 * (wz1Lemma23SnappedHeights
            pipeline.graph.residue.cells).card *
          rich.richShading.shading.mass ≤
        (54 * heightCap) * rich.richShading.shading.mass := by
    exact mul_le_mul_right'
      (mul_le_mul_left'
        (by simpa [heightCap] using data.snapped_heights_le_cap index) 54)
      rich.richShading.shading.mass
  calc
    pipeline.window.volumeSupply *
          pureWZ2CoarseHorizontalBlockSupplyFactor rho sigma stickyLoss *
          floor * weightedUnit ≤
        (cost * MeasureTheory.volume pipeline.prep.shadow.union) *
          floor * weightedUnit := by gcongr
    _ ≤ (cost *
          (cellCost * (pipeline.graph.residue.cells.card : ENNReal))) *
          floor * weightedUnit := by
      exact mul_le_mul_right'
        (mul_le_mul_right'
          (mul_le_mul_left' (by simpa [cellCost] using hvolumeCells) cost)
          floor) weightedUnit
    _ = cost * cellCost *
          (floor * (pipeline.graph.residue.cells.card : ENNReal) *
            weightedUnit) := by
      ring
    _ ≤ cost * cellCost *
          (54 * (wz1Lemma23SnappedHeights
              pipeline.graph.residue.cells).card *
            rich.richShading.shading.mass) := by
      exact mul_le_mul_left' hweightedGraph (cost * cellCost)
    _ ≤ cost * cellCost * (54 * heightCap) *
          rich.richShading.shading.mass := by
      calc
        _ ≤ cost * cellCost *
            ((54 * heightCap) * rich.richShading.shading.mass) :=
          mul_le_mul_left' hheightMass (cost * cellCost)
        _ = _ := by ring

/--
Sum the exact popular-block supplies through their actual graph-cell counts.
No unweighted block cardinality or uniform slab-volume cap is introduced.
-/
theorem aggregate_mass_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta
      volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    (data : PureWZ2CoarseHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      prepared volumeLoss)
    (hsmall :
      2 *
          ((pureWZ2PositiveCoarseCarrierBlocks prepared).card : ENNReal) *
          pureWZ2CoarseHorizontalBlockThreshold
            rho sigma middleLoss volumeLoss ≤
        MeasureTheory.volume prepared.shadow.union *
          pureWZ2CoarseHorizontalBlockSupplyFactor
            rho sigma stickyLoss) :
    MeasureTheory.volume prepared.shadow.union *
          pureWZ2CoarseHorizontalBlockSupplyFactor
            rho sigma stickyLoss *
          richFloor rho finalLoss *
          ((twoScale.fine.fineMultiplicity : ENNReal) *
            MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) ≤
      2 * pureWZ2HorizontalFixedLineVolumeCost rho sigma middleLoss *
        graphCellCost rho data.extraLoss *
        (54 * snappedHeightCap rho) *
        ∑ index : Fin data.indexCount,
          (data.rich index).richShading.shading.mass := by
  let good := pureWZ2GoodCoarseCarrierBlocks prepared volumeLoss
  let supplyFactor :=
    pureWZ2CoarseHorizontalBlockSupplyFactor rho sigma stickyLoss
  let weightedUnit := (twoScale.fine.fineMultiplicity : ENNReal) *
    MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))
  let floor := richFloor rho finalLoss
  let heightCap := snappedHeightCap rho
  let cost := pureWZ2HorizontalFixedLineVolumeCost rho sigma middleLoss
  let cellCost := graphCellCost rho data.extraLoss
  have hhalfScaled :=
    pureWZ2GoodCoarseCarrierBlocks_weightedSupply_half prepared hsmall
  have hsupplyZero : supplyFactor ≠ 0 := by
    dsimp only [supplyFactor, pureWZ2CoarseHorizontalBlockSupplyFactor]
    exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos (by
        rw [← twoScale.rhoRequested_eq]
        exact twoScale.coarseGrains.extremal.delta_pos) _)).ne'
  have hsupplyTop : supplyFactor ≠ ⊤ := by
    dsimp only [supplyFactor, pureWZ2CoarseHorizontalBlockSupplyFactor]
    simp [Kakeya.realRpowENN]
  have hhalf : MeasureTheory.volume prepared.shadow.union ≤
      2 * ∑ block ∈ good, MeasureTheory.volume
        (pureWZ2CoarseCarrierBlockShading prepared block).union := by
    apply (ENNReal.mul_le_mul_iff_right hsupplyZero hsupplyTop).mp
    calc
      supplyFactor * MeasureTheory.volume prepared.shadow.union ≤
          2 * ∑ block ∈ good, MeasureTheory.volume
            (pureWZ2CoarseCarrierBlockShading prepared block).union *
              supplyFactor := by
        simpa [good, supplyFactor, mul_comm] using hhalfScaled
      _ = supplyFactor *
          (2 * ∑ block ∈ good, MeasureTheory.volume
            (pureWZ2CoarseCarrierBlockShading prepared block).union) := by
        rw [← Finset.sum_mul]
        ring
  have hvolumeIndexed :
      (∑ block ∈ good, MeasureTheory.volume
          (pureWZ2CoarseCarrierBlockShading prepared block).union) =
        ∑ index : Fin data.indexCount,
          (data.pipeline index).window.volumeSupply := by
    symm
    apply Finset.sum_bij (fun index _ => data.block index)
    · intro index _
      exact data.block_mem index
    · intro first _ second _ heq
      exact data.block_injective heq
    · intro block hblock
      rcases data.block_surjective block hblock with ⟨index, rfl⟩
      exact ⟨index, Finset.mem_univ index, rfl⟩
    · intro index _
      exact data.volumeSupply_eq index
  have hlocal :
      (∑ index : Fin data.indexCount,
          (data.pipeline index).window.volumeSupply) * supplyFactor *
            floor * weightedUnit ≤
        cost * cellCost * (54 * heightCap) *
          ∑ index : Fin data.indexCount,
            (data.rich index).richShading.shading.mass := by
    calc
      (∑ index : Fin data.indexCount,
            (data.pipeline index).window.volumeSupply) * supplyFactor *
              floor * weightedUnit =
          ∑ index : Fin data.indexCount,
            ((data.pipeline index).window.volumeSupply * supplyFactor *
              floor * weightedUnit) := by
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      _ ≤ ∑ index : Fin data.indexCount,
          (cost * cellCost * (54 * heightCap) *
            (data.rich index).richShading.shading.mass) := by
        exact Finset.sum_le_sum fun index _ => by
          simpa [cost, cellCost, heightCap, floor, weightedUnit] using
            data.block_weighted_mass_bound index
      _ = cost * cellCost * (54 * heightCap) *
          ∑ index : Fin data.indexCount,
            (data.rich index).richShading.shading.mass := by
        rw [Finset.mul_sum]
  calc
    MeasureTheory.volume prepared.shadow.union * supplyFactor * floor *
          weightedUnit ≤
        (2 * ∑ block ∈ good, MeasureTheory.volume
          (pureWZ2CoarseCarrierBlockShading prepared block).union) *
            supplyFactor * floor * weightedUnit := by
      exact mul_le_mul_right'
        (mul_le_mul_right'
          (mul_le_mul_right' hhalf supplyFactor) floor) weightedUnit
    _ = 2 * (((∑ index : Fin data.indexCount,
          (data.pipeline index).window.volumeSupply) * supplyFactor *
            floor * weightedUnit)) := by
      rw [hvolumeIndexed]
      ring
    _ ≤ 2 * (cost * cellCost * (54 * heightCap) *
          ∑ index : Fin data.indexCount,
            (data.rich index).richShading.shading.mass) := by
      exact mul_le_mul_left' hlocal 2
    _ = 2 * cost * cellCost * (54 * heightCap) *
          ∑ index : Fin data.indexCount,
          (data.rich index).richShading.shading.mass := by ring

end PureWZ2CoarseHorizontalGoodBlockFamilyData

theorem PureWZ2Lemma23PreparedCoarse.buildGoodCoarseBlockFamily
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta
      volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hgraphOne : 256 * twoScale.rhoRequested.1 ≤ 1)
    (hheightAbsorb :
      256 * twoScale.rhoRequested.1 +
          2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1)
    (hsourceAbsorb :
      (512 : ENNReal) *
          Kakeya.realRpowENN (256 * twoScale.rhoRequested.1)
            (3 / 2 + sigma / 2 + eta) ≤
        Kakeya.realRpowENN twoScale.rhoRequested.1
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))
    (hconstantPower :
      10 * Kakeya.realRpowENN
          twoScale.rhoRequested.1 (-middleLoss) ≤
        Kakeya.realRpowENN
          (256 * twoScale.rhoRequested.1) (-eta))
    (hPlanarSmall :
      32 * Real.rpow (256 * twoScale.rhoRequested.1) eta ≤ 1)
    (hrootSmall20 :
      20 * Real.sqrt (256 * twoScale.rhoRequested.1) ≤ 1)
    (habsorb :
      Real.rpow (256 * twoScale.rhoRequested.1)
          (1 - 4 * eta / sigma) ≤
        Real.sqrt (256 * twoScale.rhoRequested.1) / 14)
    (hCOne :
      (1 : ENNReal) ≤ 10 * Kakeya.realRpowENN
        twoScale.rhoRequested.1 (-middleLoss))
    (hCpower : ∀ pipeline : PureWZ2CoarseHorizontalPipelineData
        (eta := eta) twoScale,
      (10 * Kakeya.realRpowENN
        twoScale.rhoRequested.1 (-middleLoss)).toReal ≤
        Real.rpow pipeline.prep.graphScale (-constantLoss))
    (hextraPower : ∀ pipeline : PureWZ2CoarseHorizontalPipelineData
        (eta := eta) twoScale,
      (pipeline.graph.residue.extraCost : ℝ) ≤
        Real.rpow pipeline.prep.graphScale (-extraLoss))
    (hedgeAbsorb : ∀ pipeline : PureWZ2CoarseHorizontalPipelineData
        (eta := eta) twoScale,
      Real.rpow (wz1Lemma23Theorem22Scale pipeline.prep.graphScale)
          (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow pipeline.prep.graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss +
              4 * extraLoss))
    (hKatzTao : ∀ pipeline : PureWZ2CoarseHorizontalPipelineData
        (eta := eta) twoScale,
      (4 : ENNReal) ≤ Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale pipeline.prep.graphScale)
        (-theoremEta))
    (hprojection : ∀ pipeline : PureWZ2CoarseHorizontalPipelineData
        (eta := eta) twoScale,
      ∀ data : PureWZ2HorizontalFixedLineReadyGraph
          (eta := eta) (theoremEta := theoremEta)
          (graphParents := pipeline.graphParents)
          (sources := pipeline.sources) (fullGrains := pipeline.fullGrains)
          pipeline.sharp,
        WZ1Proposition8_9AlternativeAUnion
          data.ready.deltaGraph finalLoss
          data.common.F data.common.G₁ data.common.G₁)
    (hscaleOne : 5 * (256 * twoScale.rhoRequested.1) ≤ 1)
    (hlengthLower :
      Real.rpow (5 * (256 * twoScale.rhoRequested.1))
          (1 / 2 + finalLoss) ≤ twoScale.sqrtRequested.1)
    (hgoodNonempty :
      (pureWZ2GoodCoarseCarrierBlocks prepared volumeLoss).Nonempty) :
    ∃ data : PureWZ2CoarseHorizontalGoodBlockFamilyData
        (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
        prepared volumeLoss,
      data.extraLoss = extraLoss := by
  let good := pureWZ2GoodCoarseCarrierBlocks prepared volumeLoss
  let goodEquiv := good.equivFin
  let block : Fin good.card → ℤ := fun index => (goodEquiv.symm index).1
  have hblockMem : ∀ index, block index ∈ good := fun index =>
    (goodEquiv.symm index).2
  have hblockInjective : Function.Injective block := by
    intro first second heq
    apply goodEquiv.symm.injective
    exact Subtype.ext heq
  let windowData : ∀ index : Fin good.card,
      PureWZ2CoarseCarrierBlockWindowData prepared (block index) := fun index =>
    Classical.choice (prepared.windowDataOfGoodBlock (hblockMem index))
  have hpipelineExists : ∀ index,
      ∃ pipeline : PureWZ2CoarseHorizontalPipelineData (eta := eta) twoScale,
        pipeline.window.left = (windowData index).window.left ∧
          pipeline.window.volumeSupply =
            (windowData index).window.volumeSupply := by
    intro index
    exact (windowData index).window.coarseHorizontalPipelineWithWindow
      hbridge hsigma hsigmaOne heta hetaSigma hgraphOne hheightAbsorb
      hsourceAbsorb hconstantPower hPlanarSmall hrootSmall20 habsorb
  let pipeline : Fin good.card →
      PureWZ2CoarseHorizontalPipelineData (eta := eta) twoScale := fun index =>
    Classical.choose (hpipelineExists index)
  have hpipelineLeft : ∀ index, (pipeline index).window.left =
      (windowData index).window.left := fun index =>
    (Classical.choose_spec (hpipelineExists index)).1
  have hpipelineSupply : ∀ index, (pipeline index).window.volumeSupply =
      (windowData index).window.volumeSupply := fun index =>
    (Classical.choose_spec (hpipelineExists index)).2
  have hvolumeBudget : ∀ index,
      Kakeya.realRpowENN (pipeline index).prep.graphScale
            (1 + sigma / 2 + volumeLoss) *
          pureWZ2HorizontalFixedLineVolumeCost
            twoScale.rhoRequested.1 sigma middleLoss ≤
        pureWZ2HorizontalFixedLineVolumeSupply
          (pipeline index).window.volumeSupply
          twoScale.rhoRequested.1 sigma stickyLoss := by
    intro index
    rw [(pipeline index).prep.graphScale_eq, hpipelineSupply index,
      (windowData index).volumeSupply_eq, (windowData index).shading_eq]
    simpa [pureWZ2HorizontalFixedLineVolumeSupply,
      pureWZ2CoarseHorizontalBlockSupplyFactor,
      twoScale.rhoRequested_eq] using
      pureWZ2GoodCoarseCarrierBlock_budget (hblockMem index)
  have hrichExists : ∀ index, Nonempty
      (PureWZ2CoarseHorizontalRichPipelineData
        (finalLoss := finalLoss) (theoremEta := theoremEta)
        (pipeline index)) := by
    intro index
    apply (pipeline index).toRichPipeline hsigma hsigmaOne hCOne
      (hCpower (pipeline index)) (hvolumeBudget index)
      (hextraPower (pipeline index)) (hedgeAbsorb (pipeline index))
      (hKatzTao (pipeline index)) (hprojection (pipeline index))
    · simpa [(pipeline index).prep.graphScale_eq] using hscaleOne
    · simpa [(pipeline index).prep.graphScale_eq] using hlengthLower
  let rich : ∀ index, PureWZ2CoarseHorizontalRichPipelineData
      (finalLoss := finalLoss) (theoremEta := theoremEta)
      (pipeline index) := fun index => Classical.choice (hrichExists index)
  exact ⟨{
    indexCount := good.card
    indexCount_pos := Finset.card_pos.mpr hgoodNonempty
    block := block
    block_injective := hblockInjective
    pipeline := pipeline
    rich := rich
    extraLoss := extraLoss
    extraCost_power := fun index => hextraPower (pipeline index)
    block_mem := hblockMem
    block_surjective := by
      intro target htarget
      let index := goodEquiv ⟨target, htarget⟩
      refine ⟨index, ?_⟩
      change (goodEquiv.symm index).1 = target
      simp [index]
    left_eq := by
      intro index
      rw [hpipelineLeft index, (windowData index).left_eq]
    volumeSupply_eq := by
      intro index
      rw [hpipelineSupply index, (windowData index).volumeSupply_eq,
        (windowData index).shading_eq]
  }, rfl⟩

end Kakeya.Assouad
