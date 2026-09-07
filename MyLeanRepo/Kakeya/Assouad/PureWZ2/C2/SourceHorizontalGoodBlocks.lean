import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalBlockResidue

/-!
# Popular source blocks for the local graph budget

The local ready-graph theorem has one block-dependent premise: the block
volume supply times the first-sticky balanced cell mass must dominate a fixed
threshold.  This file isolates the finite popularity algebra used to discard
blocks below that threshold.
-/

noncomputable section

namespace Kakeya.Assouad

/-- If the total contribution of blocks below a fixed threshold is at most
half of the total weighted supply, then the good blocks retain the other
half.  The theorem is phrased without division or subtraction in `ENNReal`. -/
theorem finset_good_weighted_supply_retains_half
    {alpha : Type*} [DecidableEq alpha]
    (blocks : Finset alpha)
    (supply : alpha → ENNReal)
    (cellMass threshold : ENNReal)
    (hthresholdTop : threshold ≠ ⊤)
    (hbad :
      2 * ((blocks.card : ENNReal) * threshold) ≤
        ∑ block ∈ blocks, supply block * cellMass) :
    (∑ block ∈ blocks, supply block * cellMass) ≤
      2 * ∑ block ∈ blocks.filter (fun block =>
          threshold ≤ supply block * cellMass),
        supply block * cellMass := by
  let good := blocks.filter fun block =>
    threshold ≤ supply block * cellMass
  let bad := blocks.filter fun block =>
    ¬ threshold ≤ supply block * cellMass
  have hbadPointwise : ∀ block ∈ bad,
      supply block * cellMass ≤ threshold := by
    intro block hblock
    have hnot := (Finset.mem_filter.mp hblock).2
    exact le_of_lt (lt_of_not_ge hnot)
  have hbadSum :
      (∑ block ∈ bad, supply block * cellMass) ≤
        (blocks.card : ENNReal) * threshold := by
    calc
      (∑ block ∈ bad, supply block * cellMass) ≤
          ∑ _block ∈ bad, threshold := by
        exact Finset.sum_le_sum hbadPointwise
      _ = (bad.card : ENNReal) * threshold := by
        simp [Finset.sum_const]
      _ ≤ (blocks.card : ENNReal) * threshold := by
        apply mul_le_mul_right'
        exact_mod_cast
          (show bad.card ≤ blocks.card from
            Finset.card_le_card (Finset.filter_subset _ _))
  have hbadTop : (∑ block ∈ bad, supply block * cellMass) ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hthresholdTop)
      hbadSum
  have hbadGood :
      (∑ block ∈ bad, supply block * cellMass) ≤
        ∑ block ∈ good, supply block * cellMass := by
    apply (ENNReal.add_le_add_iff_right hbadTop).mp
    calc
      (∑ block ∈ bad, supply block * cellMass) +
            ∑ block ∈ bad, supply block * cellMass =
          2 * ∑ block ∈ bad, supply block * cellMass := by ring
      _ ≤ 2 * ((blocks.card : ENNReal) * threshold) := by gcongr
      _ ≤ ∑ block ∈ blocks, supply block * cellMass := hbad
      _ = (∑ block ∈ good, supply block * cellMass) +
            ∑ block ∈ bad, supply block * cellMass := by
        simpa [good, bad] using
          (Finset.sum_filter_add_sum_filter_not blocks
            (fun block => threshold ≤ supply block * cellMass)
            (fun block => supply block * cellMass)).symm
  have hpartition :
      (∑ block ∈ blocks, supply block * cellMass) =
        (∑ block ∈ good, supply block * cellMass) +
          ∑ block ∈ bad, supply block * cellMass := by
    simpa [good, bad] using
      (Finset.sum_filter_add_sum_filter_not blocks
        (fun block => threshold ≤ supply block * cellMass)
        (fun block => supply block * cellMass)).symm
  rw [hpartition]
  calc
    (∑ block ∈ good, supply block * cellMass) +
          ∑ block ∈ bad, supply block * cellMass ≤
        (∑ block ∈ good, supply block * cellMass) +
          ∑ block ∈ good, supply block * cellMass := by
      gcongr
    _ = 2 * ∑ block ∈ good, supply block * cellMass := by ring

/-- The common local ready-graph threshold for every source block. -/
def pureWZ2SourceHorizontalBlockThreshold
    (rho delta sigma inputLoss volumeLoss : ℝ) : ENNReal :=
  Kakeya.realRpowENN (256 * rho) (1 + sigma / 2 + volumeLoss) *
    (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
      MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0)))

/-- Uniform Alternative-A rich-height floor for every local block graph. -/
def pureWZ2SourceHorizontalRichFloor
    (rho outputLoss : ℝ) : ENNReal :=
  Kakeya.realRpowENN
    (wz1Lemma23Theorem22Scale (256 * rho)) (outputLoss - 1)

theorem pureWZ2SourceHorizontalVolumeCost_ne_top
    (rho delta sigma inputLoss : ℝ) :
    pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss ≠ ⊤ := by
  unfold pureWZ2SourceHorizontalVolumeCost
  repeat' apply ENNReal.mul_ne_top
  all_goals first | exact ENNReal.ofReal_ne_top | exact ENNReal.natCast_ne_top _ |
    simp [Kakeya.realRpowENN]

/-- Positive source blocks whose exact local supply reaches the graph
threshold. -/
def pureWZ2GoodSourceCarrierBlocks
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (volumeLoss : ℝ) : Finset ℤ :=
  (pureWZ2PositiveSourceCarrierBlocks prepared).filter fun block =>
    pureWZ2SourceHorizontalBlockThreshold
        rho delta sigma inputLoss volumeLoss ≤
      MeasureTheory.volume
          (pureWZ2SourceCarrierBlockShading prepared block).union *
        (twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass)

/-- A good source block supplies the exact local graph budget. -/
theorem pureWZ2GoodSourceCarrierBlock_budget
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {block : ℤ}
    (hblock : block ∈ pureWZ2GoodSourceCarrierBlocks prepared volumeLoss) :
    Kakeya.realRpowENN (256 * rho)
          (1 + sigma / 2 + volumeLoss) *
        (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) ≤
      MeasureTheory.volume
          (pureWZ2SourceCarrierBlockShading prepared block).union *
        (twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass) := by
  exact (Finset.mem_filter.mp hblock).2

/-- Good blocks have positive source volume and hence canonical block-window
data with exact supply. -/
theorem PureWZ2SourceCarrierPreparation.windowDataOfGoodBlock
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    {block : ℤ}
    (hblock : block ∈ pureWZ2GoodSourceCarrierBlocks prepared volumeLoss) :
    Nonempty (PureWZ2SourceCarrierBlockWindowData prepared block) := by
  have hpositive : 0 < MeasureTheory.volume
      (pureWZ2SourceCarrierBlockShading prepared block).union :=
    pureWZ2PositiveSourceCarrierBlock_volume_pos
      (Finset.mem_filter.mp hblock).1
  exact prepared.windowDataOfBlock block hpositive

/-- Apply the generic half-retention lemma to the exact source block
partition.  The remaining premise is the outer small-scale budget. -/
theorem pureWZ2GoodSourceCarrierBlocks_weightedSupply_half
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (hsmall :
      2 *
          ((pureWZ2PositiveSourceCarrierBlocks prepared).card : ENNReal) *
          pureWZ2SourceHorizontalBlockThreshold
            rho delta sigma inputLoss volumeLoss ≤
        MeasureTheory.volume prepared.shadow.union *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass)) :
    MeasureTheory.volume prepared.shadow.union *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass) ≤
      2 * ∑ block ∈ pureWZ2GoodSourceCarrierBlocks prepared volumeLoss,
        MeasureTheory.volume
            (pureWZ2SourceCarrierBlockShading prepared block).union *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass) := by
  have hrho : 0 < rho := source.extremal.delta_pos.trans_le (by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1)
  have hthresholdTop : pureWZ2SourceHorizontalBlockThreshold
      rho delta sigma inputLoss volumeLoss ≠ ⊤ := by
    unfold pureWZ2SourceHorizontalBlockThreshold
    exact ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN])
      (ENNReal.mul_ne_top
        (pureWZ2SourceHorizontalVolumeCost_ne_top _ _ _ _)
        (by rw [wz1PaperGridCube_volume_exact hrho]
            exact ENNReal.ofReal_ne_top))
  have hraw := finset_good_weighted_supply_retains_half
    (pureWZ2PositiveSourceCarrierBlocks prepared)
    (fun block => MeasureTheory.volume
      (pureWZ2SourceCarrierBlockShading prepared block).union)
    (twoScale.coarse.balanced.cellMass *
      twoScale.fine.balanced.cellMass)
    (pureWZ2SourceHorizontalBlockThreshold
      rho delta sigma inputLoss volumeLoss)
    hthresholdTop
  have hsupplyBoth :
      (∑ block ∈ pureWZ2PositiveSourceCarrierBlocks prepared,
          MeasureTheory.volume
              (pureWZ2SourceCarrierBlockShading prepared block).union *
            (twoScale.coarse.balanced.cellMass *
              twoScale.fine.balanced.cellMass)) =
        MeasureTheory.volume prepared.shadow.union *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass) := by
    rw [← Finset.sum_mul, ←
      pureWZ2PositiveSourceCarrierBlocks_volume_eq_sum prepared]
  rw [hsupplyBoth] at hraw
  exact hraw (by simpa [mul_assoc] using hsmall)

/-- Positive exact pullback supply forces a nonempty good source-block set. -/
theorem pureWZ2GoodSourceCarrierBlocks_nonempty
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (hsmall :
      2 * ((pureWZ2PositiveSourceCarrierBlocks prepared).card : ENNReal) *
          pureWZ2SourceHorizontalBlockThreshold
            rho delta sigma inputLoss volumeLoss ≤
        MeasureTheory.volume prepared.shadow.union *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass)) :
    (pureWZ2GoodSourceCarrierBlocks prepared volumeLoss).Nonempty := by
  have hretained := pureWZ2GoodSourceCarrierBlocks_weightedSupply_half
    prepared hsmall
  have hvolumePos : 0 < MeasureTheory.volume prepared.shadow.union := by
    rw [prepared.shadow_union, pullback.volume_eq]
    have hcount : 0 < (pullback.selectedCells.card : ENNReal) := by
      have hselected : pullback.selectedCells.Nonempty := by
        by_contra hempty
        have hcells : pullback.selectedCells = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hempty
        have hvolumeZero : MeasureTheory.volume twoScale.fine.refined.union = 0 := by
          rw [← pullback.selected_count_mul_coarse_volume, hcells]
          simp
        have hpowerPos : 0 < Kakeya.realRpowENN
            twoScale.rhoRequested.1 (sigma + stickyLoss) :=
          ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos
            twoScale.coarseGrains.extremal.delta_pos _)
        have hlower := twoScale.fine.refined_volume_lower
        rw [hvolumeZero] at hlower
        exact (not_le_of_gt hpowerPos) hlower
      exact_mod_cast hselected.card_pos
    exact ENNReal.mul_pos hcount.ne'
      twoScale.coarse.balanced.cellMass_pos.ne'
  have hsupplyPos : 0 <
      twoScale.coarse.balanced.cellMass *
        twoScale.fine.balanced.cellMass :=
    ENNReal.mul_pos twoScale.coarse.balanced.cellMass_pos.ne'
      twoScale.fine.balanced.cellMass_pos.ne'
  have hleftPos : 0 < MeasureTheory.volume prepared.shadow.union *
      (twoScale.coarse.balanced.cellMass *
        twoScale.fine.balanced.cellMass) :=
    ENNReal.mul_pos hvolumePos.ne' hsupplyPos.ne'
  by_contra hempty
  have hgoodEmpty : pureWZ2GoodSourceCarrierBlocks prepared volumeLoss = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  rw [hgoodEmpty] at hretained
  simp only [Finset.sum_empty, mul_zero] at hretained
  exact (not_le_of_gt hleftPos) hretained

/-- Completed local outputs indexed by every good source block. -/
structure PureWZ2SourceHorizontalGoodBlockFamilyData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (volumeLoss : ℝ) where
  outputs : PureWZ2SourceHorizontalBlockFamilyData
    (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta) twoScale
  block_mem : ∀ index, outputs.block index ∈
    pureWZ2GoodSourceCarrierBlocks prepared volumeLoss
  block_surjective : ∀ block ∈
    pureWZ2GoodSourceCarrierBlocks prepared volumeLoss,
      ∃ index, outputs.block index = block
  volumeSupply_eq : ∀ index, (outputs.pipeline index).window.volumeSupply =
    MeasureTheory.volume
      (pureWZ2SourceCarrierBlockShading prepared
        (outputs.block index)).union
  extraLoss : ℝ
  extraCost_power : ∀ index,
    ((outputs.pipeline index).graph.residue.extraCost : ℝ) ≤
      Real.rpow (outputs.pipeline index).prep.graphScale (-extraLoss)

namespace PureWZ2SourceHorizontalGoodBlockFamilyData

/-- Uniform cost converting actual graph cells back to source residue volume. -/
def graphCellCost (rho extraLoss : ℝ) : ENNReal :=
  ENNReal.ofReal
    (8 * Real.rpow (256 * rho) (-extraLoss) *
      Real.rpow (256 * rho) (5 / 2 : ℝ))

/-- Uniform snapped-height cap for every source block graph. -/
def snappedHeightCap (rho : ℝ) : ENNReal :=
  ENNReal.ofReal (3 / Real.sqrt (256 * rho))

/-- Uniform loss in passing from source-volume popular layers to the final
rich height lift.  It contains only the two logarithmic selections and the
number of source-popular height layers. -/
def heightRetentionCost (rho extraLoss : ℝ) : ENNReal :=
  ENNReal.ofReal (2 * Real.rpow (256 * rho) (-extraLoss)) *
    snappedHeightCap rho

/-- Actual final residue volume is bounded by its graph cell count. -/
theorem graph_shadow_volume_le_cells
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (data : PureWZ2SourceHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) prepared volumeLoss)
    (index : Fin data.outputs.indexCount) :
    MeasureTheory.volume (data.outputs.pipeline index).prep.shadow.union ≤
      graphCellCost rho data.extraLoss *
        ((data.outputs.pipeline index).graph.residue.cells.card : ENNReal) := by
  let pipeline := data.outputs.pipeline index
  let scale := pipeline.prep.graphScale
  let volumeValue := MeasureTheory.volume pipeline.prep.shadow.union
  have hscale : 0 < scale := pipeline.prep.graphScale_pos
  have hball : pipeline.prep.shadow.union ⊆
      Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hpaper : point ∈ pipeline.retained.shading.union := by
      exact pipeline.prep.shadow_union_subset hpoint
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
    exact pipeline.prep.graphScale_eq
  calc
    MeasureTheory.volume pipeline.prep.shadow.union =
        ENNReal.ofReal volumeValue.toReal := by rw [hvolumeOfReal]
    _ ≤ ENNReal.ofReal
        ((8 * Real.rpow scale (-data.extraLoss) *
            Real.rpow scale (5 / 2 : ℝ)) *
          ((pipeline.graph.residue.cells.card : ℕ) : ℝ)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = graphCellCost rho data.extraLoss *
          ((pipeline.graph.residue.cells.card : ℕ) : ENNReal) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      simp [graphCellCost, hscaleEq]

/-- The actual snapped heights remain inside one graph window. -/
theorem snapped_heights_le_cap
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (data : PureWZ2SourceHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) prepared volumeLoss)
    (index : Fin data.outputs.indexCount) :
    (((wz1Lemma23SnappedHeights
      (data.outputs.pipeline index).graph.residue.cells).card : ℕ) : ENNReal) ≤
      snappedHeightCap rho := by
  let pipeline := data.outputs.pipeline index
  have hreal := wz1Lemma23_height_layer_count
    pipeline.prep.graphScale_pos pipeline.prep.graphScale_one
    (pipeline.prep.windowed.residue_cells_window pipeline.graph.residue)
  have hscaleEq : pipeline.prep.graphScale = 256 * rho :=
    pipeline.prep.graphScale_eq
  have henn := ENNReal.natCast_le_ofReal
    (by
      intro hzero
      have : (wz1Lemma23SnappedHeights
          pipeline.graph.residue.cells).Nonempty := by
        rcases (data.outputs.rich index).richCells.graphCells_nonempty with
          ⟨cell, hcell⟩
        exact ⟨cell.2.2, Finset.mem_image.mpr
          ⟨cell, (data.outputs.rich index).richCells.graphCells_subset hcell,
            rfl⟩⟩
      exact this.card_ne_zero hzero) |>.mpr hreal
  simpa [snappedHeightCap, hscaleEq] using henn

/-- Source-volume popular heights lie in the same graph window and obey the
same `O(rho^-1/2)` cap. -/
theorem popular_heights_le_cap
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (data : PureWZ2SourceHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) prepared volumeLoss)
    (index : Fin data.outputs.indexCount) :
    ((data.outputs.pipeline index).heightPopular.heightIndices.card :
        ENNReal) ≤ snappedHeightCap rho := by
  let pipeline := data.outputs.pipeline index
  have hsubset : pipeline.heightPopular.heightIndices ⊆
      wz1Lemma23SnappedHeights pipeline.prep.windowed.global.cells := by
    intro heightIndex hheight
    have hglobal : heightIndex ∈ pipeline.prep.windowed.global.heightIndices := by
      rw [pipeline.prep.windowed.global.heightIndices_eq]
      exact pipeline.heightPopular.heightIndices_subset hheight
    have hlayerNonempty :
        (pipeline.prep.windowed.global.layerCells heightIndex).Nonempty := by
      have hlayerPos : 0 < MeasureTheory.volume
          (pipeline.prep.shadow.union ∩
            wz1Lemma23HeightSlab pipeline.prep.graphScale heightIndex) :=
        pipeline.heightPopular.layerMass_pos.trans_le
          (pipeline.heightPopular.layer_volume_band heightIndex hheight).1
      by_contra hempty
      have hlayerEmpty := Finset.not_nonempty_iff_eq_empty.mp hempty
      have hbound := pipeline.prep.windowed.global.layer_volume_bound
        heightIndex hglobal
      have harea := wz1_lemma23_exactSlice_area_le_two pipeline.prep.shadow
        pipeline.prep.graphScale_pos
        (by
          intro point hpoint
          have hpaper : point ∈ pipeline.retained.shading.union := by
            exact pipeline.prep.shadow_union_subset hpoint
          have hnorm := norm_le_two_of_mem_paperShading hpaper
          simpa [Metric.mem_closedBall, dist_zero_right] using hnorm)
        (pipeline.prep.windowed.global.selectedHeight heightIndex)
      rw [← pipeline.prep.windowed.global.layerCells_eq heightIndex,
        hlayerEmpty] at harea
      norm_num at harea
      have hsidePos : 0 < ENNReal.ofReal
          (gridSide (pipeline.prep.graphScale / 2)) := by
        apply ENNReal.ofReal_pos.mpr
        dsimp [gridSide]
        apply div_pos
        · nlinarith [pipeline.prep.graphScale_pos]
        · exact Real.sqrt_pos.mpr (by norm_num)
      have hzero : MeasureTheory.volume
          (pipeline.prep.shadow.union ∩
            wz1Lemma23HeightSlab pipeline.prep.graphScale heightIndex) = 0 := by
        apply le_zero_iff.mp
        have hdiv : MeasureTheory.volume
              (pipeline.prep.shadow.union ∩
                wz1Lemma23HeightSlab pipeline.prep.graphScale heightIndex) /
              ENNReal.ofReal (gridSide (pipeline.prep.graphScale / 2)) ≤ 0 :=
          hbound.trans harea.le
        have hmul := (ENNReal.div_le_iff hsidePos.ne'
          ENNReal.ofReal_ne_top).mp hdiv
        simpa using hmul
      exact (ne_of_gt hlayerPos) hzero
    rcases hlayerNonempty with ⟨cell, hcell⟩
    have hcellGlobal : cell ∈ pipeline.prep.windowed.global.cells := by
      rw [pipeline.prep.windowed.global.cells_eq]
      exact Finset.mem_biUnion.mpr ⟨heightIndex, hglobal, hcell⟩
    exact Finset.mem_image.mpr ⟨cell, hcellGlobal,
      (pipeline.prep.windowed.global.layer_height
        heightIndex hglobal cell hcell)⟩
  have hreal := wz1Lemma23_height_layer_count
    pipeline.prep.graphScale_pos pipeline.prep.graphScale_one
    pipeline.prep.windowed.global_cells_window
  have hcardReal :
      (pipeline.heightPopular.heightIndices.card : ℝ) ≤
        3 / Real.sqrt pipeline.prep.graphScale := by
    have hcast : (pipeline.heightPopular.heightIndices.card : ℝ) ≤
        ((wz1Lemma23SnappedHeights
          pipeline.prep.windowed.global.cells).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    exact hcast.trans hreal
  have hscaleEq : pipeline.prep.graphScale = 256 * rho :=
    pipeline.prep.graphScale_eq
  have henn := ENNReal.natCast_le_ofReal
    pipeline.heightPopular.heightIndices_nonempty.card_ne_zero |>.mpr hcardReal
  simpa [snappedHeightCap, hscaleEq] using henn

/-- One exact source-block supply controls its actual rich indexed mass. -/
theorem block_height_mass_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (data : PureWZ2SourceHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) prepared volumeLoss)
    (index : Fin data.outputs.indexCount) :
    (data.outputs.pipeline index).window.volumeSupply *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass) *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
      (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
        (4 * (data.outputs.pipeline index).heightPopular.bins *
          ((data.outputs.pipeline index).heightPopular.heightIndices.card :
            ENNReal)) *
        (data.outputs.rich index).heightLift.shading.mass := by
  let pipeline := data.outputs.pipeline index
  let rich := data.outputs.rich index
  let cost := pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
    MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))
  let floor := pureWZ2SourceHorizontalRichFloor rho finalLoss
  have hsupply : pipeline.window.volumeSupply *
        (twoScale.coarse.balanced.cellMass *
          twoScale.fine.balanced.cellMass) ≤
      cost * MeasureTheory.volume pipeline.prep.shadow.union := by
    simpa [cost, mul_assoc] using
      pipeline.prep.volume_supply_le pipeline.shadow_union
  have hpopular : MeasureTheory.volume pipeline.prep.shadow.union ≤
      2 * pipeline.heightPopular.bins *
        MeasureTheory.volume pipeline.heightPopular.shading.union := by
    have h := (ENNReal.div_le_iff (by norm_num) (by norm_num)).mp
      pipeline.heightPopular.retained_volume
    simpa [mul_comm, mul_left_comm,
      mul_assoc] using h
  have hfloor : floor ≤ (rich.rich.heightIndices.card : ENNReal) := by
    have hfloorEq : floor = Kakeya.realRpowENN
        rich.ready.ready.deltaGraph (finalLoss - 1) := by
      dsimp only [floor]
      unfold pureWZ2SourceHorizontalRichFloor
      rw [rich.ready.ready.deltaGraph_eq, pipeline.prep.graphScale_eq]
    rw [hfloorEq]
    simpa [rich.rich.heightIndices_card] using rich.rich.richF_card
  have hrelative := rich.heightVolume.relative_volume_lower
  have hpopularLayer : MeasureTheory.volume
        pipeline.heightPopular.shading.union ≤
      2 * (pipeline.heightPopular.heightIndices.card : ENNReal) *
        pipeline.heightPopular.layerMass := by
    rw [pipeline.heightPopular.volume_eq_sum]
    calc
      (∑ heightIndex ∈ pipeline.heightPopular.heightIndices,
          MeasureTheory.volume (pipeline.prep.shadow.union ∩
            wz1Lemma23HeightSlab pipeline.prep.graphScale heightIndex)) ≤
        ∑ _heightIndex ∈ pipeline.heightPopular.heightIndices,
          2 * pipeline.heightPopular.layerMass := by
        exact Finset.sum_le_sum fun heightIndex hheight =>
          (pipeline.heightPopular.layer_volume_band heightIndex hheight).2
      _ = 2 * (pipeline.heightPopular.heightIndices.card : ENNReal) *
          pipeline.heightPopular.layerMass := by
        simp [Finset.sum_const]
        ring
  have hweightedMass :
      floor * MeasureTheory.volume pipeline.prep.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) ≤
        4 * pipeline.heightPopular.bins *
          (pipeline.heightPopular.heightIndices.card : ENNReal) *
            rich.heightLift.shading.mass := by
    calc
      floor * MeasureTheory.volume pipeline.prep.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) ≤
        floor * (2 * pipeline.heightPopular.bins *
          MeasureTheory.volume pipeline.heightPopular.shading.union) *
            (twoScale.coarse.fineMultiplicity : ENNReal) := by
        gcongr
      _ ≤ floor * (2 * pipeline.heightPopular.bins *
          (2 * (pipeline.heightPopular.heightIndices.card : ENNReal) *
            pipeline.heightPopular.layerMass)) *
            (twoScale.coarse.fineMultiplicity : ENNReal) := by gcongr
      _ ≤ (rich.rich.heightIndices.card : ENNReal) *
          (2 * pipeline.heightPopular.bins *
            (2 * (pipeline.heightPopular.heightIndices.card : ENNReal) *
              pipeline.heightPopular.layerMass)) *
            (twoScale.coarse.fineMultiplicity : ENNReal) := by
        gcongr
      _ = 4 * pipeline.heightPopular.bins *
          (pipeline.heightPopular.heightIndices.card : ENNReal) *
          ((twoScale.coarse.fineMultiplicity : ENNReal) *
            ((rich.rich.heightIndices.card : ENNReal) *
              pipeline.heightPopular.layerMass)) := by ring
      _ ≤ 4 * pipeline.heightPopular.bins *
          (pipeline.heightPopular.heightIndices.card : ENNReal) *
            rich.heightLift.shading.mass := by
        exact mul_le_mul_left' rich.heightVolume.mass_lower
          (4 * pipeline.heightPopular.bins *
            (pipeline.heightPopular.heightIndices.card : ENNReal))
  calc
    pipeline.window.volumeSupply *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass) *
          (twoScale.coarse.fineMultiplicity : ENNReal) * floor ≤
      (cost * MeasureTheory.volume pipeline.prep.shadow.union) *
          (twoScale.coarse.fineMultiplicity : ENNReal) * floor := by gcongr
    _ = cost * (floor * MeasureTheory.volume pipeline.prep.shadow.union) *
          (twoScale.coarse.fineMultiplicity : ENNReal) := by ring
    _ ≤ cost *
        (4 * pipeline.heightPopular.bins *
          (pipeline.heightPopular.heightIndices.card : ENNReal)) *
        rich.heightLift.shading.mass := by
      simpa [mul_assoc] using mul_le_mul_left' hweightedMass cost

/-- Uniformize the exact source-height cost by the analytic extra-cost power
and the common height cap. -/
theorem block_height_mass_bound_uniform
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (data : PureWZ2SourceHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) prepared volumeLoss)
    (index : Fin data.outputs.indexCount) :
    (data.outputs.pipeline index).window.volumeSupply *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass) *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
      (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
        heightRetentionCost rho data.extraLoss *
        (data.outputs.rich index).heightLift.shading.mass := by
  let pipeline := data.outputs.pipeline index
  have hlogPos : 1 ≤ Nat.log 2 pipeline.rawResidue.cells.card + 1 := by omega
  have hbinsNat : 4 * pipeline.heightPopular.bins ≤
      2 * pipeline.graph.residue.extraCost := by
    rw [pipeline.extraCost_eq]
    nlinarith
  have hbinsENN : (4 * pipeline.heightPopular.bins : ENNReal) ≤
      2 * (pipeline.graph.residue.extraCost : ENNReal) := by
    exact_mod_cast hbinsNat
  have hextraENN : (pipeline.graph.residue.extraCost : ENNReal) ≤
      ENNReal.ofReal (Real.rpow pipeline.prep.graphScale (-data.extraLoss)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (data.extraCost_power index)
  have hheight := data.popular_heights_le_cap index
  have hcost :
      (4 * pipeline.heightPopular.bins : ENNReal) *
          (pipeline.heightPopular.heightIndices.card : ENNReal) ≤
        heightRetentionCost rho data.extraLoss := by
    calc
      (4 * pipeline.heightPopular.bins : ENNReal) *
          (pipeline.heightPopular.heightIndices.card : ENNReal) ≤
        (2 * (pipeline.graph.residue.extraCost : ENNReal)) *
          (pipeline.heightPopular.heightIndices.card : ENNReal) := by gcongr
      _ ≤ (2 * ENNReal.ofReal
          (Real.rpow pipeline.prep.graphScale (-data.extraLoss))) *
          snappedHeightCap rho := by gcongr
      _ = heightRetentionCost rho data.extraLoss := by
        rw [pipeline.prep.graphScale_eq]
        unfold heightRetentionCost
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  exact (data.block_height_mass_bound index).trans (by gcongr)

theorem block_weighted_mass_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (data : PureWZ2SourceHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) prepared volumeLoss)
    (index : Fin data.outputs.indexCount) :
    (data.outputs.pipeline index).window.volumeSupply *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass ≤
      (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
        graphCellCost rho data.extraLoss *
        (54 * snappedHeightCap rho) *
        (data.outputs.rich index).richShading.shading.mass := by
  let pipeline := data.outputs.pipeline index
  let rich := data.outputs.rich index
  let cost := pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
    MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))
  let cellCost := graphCellCost rho data.extraLoss
  let heightCap := snappedHeightCap rho
  let floor := pureWZ2SourceHorizontalRichFloor rho finalLoss
  let incidenceMass := twoScale.coarse.balanced.incidenceMass
  have hsupply := pipeline.prep.volume_supply_le pipeline.shadow_union
  have hsupply' :
      pipeline.window.volumeSupply *
            (twoScale.coarse.balanced.cellMass *
              twoScale.fine.balanced.cellMass) ≤
        cost * MeasureTheory.volume pipeline.prep.shadow.union := by
    simpa [cost, mul_assoc] using hsupply
  have hvolumeCells := data.graph_shadow_volume_le_cells index
  have hfloor : floor =
      Kakeya.realRpowENN rich.ready.ready.deltaGraph (finalLoss - 1) := by
    dsimp only [floor]
    unfold pureWZ2SourceHorizontalRichFloor
    rw [rich.ready.ready.deltaGraph_eq, pipeline.prep.graphScale_eq]
  have hweightedGraph :
      floor * (pipeline.graph.residue.cells.card : ENNReal) * incidenceMass ≤
        54 * (wz1Lemma23SnappedHeights
            pipeline.graph.residue.cells).card *
          rich.richShading.shading.mass := by
    calc
      floor * (pipeline.graph.residue.cells.card : ENNReal) * incidenceMass ≤
          (rich.rich.heightIndices.card : ENNReal) *
            (pipeline.graph.residue.cells.card : ENNReal) * incidenceMass := by
        gcongr
        rw [hfloor]
        simpa [rich.rich.heightIndices_card] using rich.rich.richF_card
      _ = (((rich.rich.heightIndices.card *
              pipeline.graph.residue.cells.card : ℕ) : ENNReal) *
            incidenceMass) := by
        push_cast
        ring
      _ ≤ 54 * (wz1Lemma23SnappedHeights
            pipeline.graph.residue.cells).card *
          rich.richShading.shading.mass := by
        simpa [incidenceMass] using rich.richShading.graph_weighted_mass_lower
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
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass) *
          floor * incidenceMass ≤
        (cost * MeasureTheory.volume pipeline.prep.shadow.union) *
          floor * incidenceMass := by
      exact mul_le_mul_right'
        (mul_le_mul_right' hsupply' floor) incidenceMass
    _ ≤ (cost *
          (cellCost * (pipeline.graph.residue.cells.card : ENNReal))) *
          floor * incidenceMass := by
      exact mul_le_mul_right'
        (mul_le_mul_right'
          (mul_le_mul_left' (by simpa [cellCost] using hvolumeCells) cost)
          floor) incidenceMass
    _ = cost * cellCost *
          (floor * (pipeline.graph.residue.cells.card : ENNReal) *
            incidenceMass) := by ring
    _ ≤ cost * cellCost *
          (54 * (wz1Lemma23SnappedHeights
              pipeline.graph.residue.cells).card *
            rich.richShading.shading.mass) :=
      mul_le_mul_left' hweightedGraph (cost * cellCost)
    _ ≤ cost * cellCost * (54 * heightCap) *
          rich.richShading.shading.mass := by
      calc
        _ ≤ cost * cellCost *
            ((54 * heightCap) * rich.richShading.shading.mass) :=
          mul_le_mul_left' hheightMass (cost * cellCost)
        _ = _ := by ring

/-- Sum exact source-block supplies through actual graph-cell weights. -/
theorem aggregate_mass_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta
      volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (data : PureWZ2SourceHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta)
      prepared volumeLoss)
    (hsmall :
      2 *
          ((pureWZ2PositiveSourceCarrierBlocks prepared).card : ENNReal) *
          pureWZ2SourceHorizontalBlockThreshold
            rho delta sigma inputLoss volumeLoss ≤
        MeasureTheory.volume prepared.shadow.union *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass)) :
    MeasureTheory.volume prepared.shadow.union *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass ≤
      2 * (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
        graphCellCost rho data.extraLoss *
        (54 * snappedHeightCap rho) *
        ∑ index : Fin data.outputs.indexCount,
          (data.outputs.rich index).richShading.shading.mass := by
  let good := pureWZ2GoodSourceCarrierBlocks prepared volumeLoss
  let cellSupply := twoScale.coarse.balanced.cellMass *
    twoScale.fine.balanced.cellMass
  let incidenceMass := twoScale.coarse.balanced.incidenceMass
  let floor := pureWZ2SourceHorizontalRichFloor rho finalLoss
  let cost := pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
    MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))
  let cellCost := graphCellCost rho data.extraLoss
  let heightCap := snappedHeightCap rho
  have hhalfWithFine := pureWZ2GoodSourceCarrierBlocks_weightedSupply_half
    prepared hsmall
  have hhalf :
      MeasureTheory.volume prepared.shadow.union * cellSupply ≤
        2 * ∑ block ∈ good, MeasureTheory.volume
            (pureWZ2SourceCarrierBlockShading prepared block).union *
              cellSupply := by
    simpa [good, cellSupply, mul_assoc] using hhalfWithFine
  have hhalf' :
      MeasureTheory.volume prepared.shadow.union * cellSupply ≤
        (2 * ∑ block ∈ good, MeasureTheory.volume
          (pureWZ2SourceCarrierBlockShading prepared block).union) *
            cellSupply := by
    calc
      _ ≤ 2 * ∑ block ∈ good, MeasureTheory.volume
          (pureWZ2SourceCarrierBlockShading prepared block).union *
            cellSupply := hhalf
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hvolumeIndexed :
      (∑ block ∈ good, MeasureTheory.volume
          (pureWZ2SourceCarrierBlockShading prepared block).union) =
        ∑ index : Fin data.outputs.indexCount,
          (data.outputs.pipeline index).window.volumeSupply := by
    symm
    apply Finset.sum_bij (fun index _ => data.outputs.block index)
    · intro index _
      exact data.block_mem index
    · intro first _ second _ heq
      exact data.outputs.block_injective heq
    · intro block hblock
      rcases data.block_surjective block hblock with ⟨index, rfl⟩
      exact ⟨index, Finset.mem_univ index, rfl⟩
    · intro index _
      exact data.volumeSupply_eq index
  have hlocal :
      (∑ index : Fin data.outputs.indexCount,
          (data.outputs.pipeline index).window.volumeSupply) *
            cellSupply * floor * incidenceMass ≤
        cost * cellCost * (54 * heightCap) *
          ∑ index : Fin data.outputs.indexCount,
            (data.outputs.rich index).richShading.shading.mass := by
    calc
      (∑ index : Fin data.outputs.indexCount,
            (data.outputs.pipeline index).window.volumeSupply) *
              cellSupply * floor * incidenceMass =
          ∑ index : Fin data.outputs.indexCount,
            ((data.outputs.pipeline index).window.volumeSupply *
              cellSupply * floor * incidenceMass) := by
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      _ ≤ ∑ index : Fin data.outputs.indexCount,
          (cost * cellCost * (54 * heightCap) *
            (data.outputs.rich index).richShading.shading.mass) := by
        exact Finset.sum_le_sum fun index _ => by
          simpa [cost, cellCost, heightCap, cellSupply, floor, incidenceMass]
            using data.block_weighted_mass_bound index
      _ = cost * cellCost * (54 * heightCap) *
          ∑ index : Fin data.outputs.indexCount,
            (data.outputs.rich index).richShading.shading.mass := by
        rw [Finset.mul_sum]
  calc
    MeasureTheory.volume prepared.shadow.union * cellSupply * floor *
          incidenceMass ≤
        (2 * ∑ block ∈ good, MeasureTheory.volume
          (pureWZ2SourceCarrierBlockShading prepared block).union) *
            cellSupply * floor * incidenceMass := by
      exact mul_le_mul_right'
        (mul_le_mul_right' hhalf' floor) incidenceMass
    _ = 2 * (((∑ index : Fin data.outputs.indexCount,
          (data.outputs.pipeline index).window.volumeSupply) *
            cellSupply * floor * incidenceMass)) := by
      rw [hvolumeIndexed]
      ring
    _ ≤ 2 * (cost * cellCost * (54 * heightCap) *
          ∑ index : Fin data.outputs.indexCount,
            (data.outputs.rich index).richShading.shading.mass) :=
      mul_le_mul_left' hlocal 2
    _ = 2 * cost * cellCost * (54 * heightCap) *
          ∑ index : Fin data.outputs.indexCount,
          (data.outputs.rich index).richShading.shading.mass := by ring

/-- Aggregate the genuine source-height mass bounds over all good blocks. -/
theorem aggregate_height_mass_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta
      volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (data : PureWZ2SourceHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta)
      prepared volumeLoss)
    (hsmall :
      2 * ((pureWZ2PositiveSourceCarrierBlocks prepared).card : ENNReal) *
          pureWZ2SourceHorizontalBlockThreshold
            rho delta sigma inputLoss volumeLoss ≤
        MeasureTheory.volume prepared.shadow.union *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass)) :
    MeasureTheory.volume prepared.shadow.union *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass) *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
      2 * (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
        heightRetentionCost rho data.extraLoss *
        ∑ index : Fin data.outputs.indexCount,
          (data.outputs.rich index).heightLift.shading.mass := by
  let good := pureWZ2GoodSourceCarrierBlocks prepared volumeLoss
  let cellSupply := twoScale.coarse.balanced.cellMass *
    twoScale.fine.balanced.cellMass
  let multiplicity : ENNReal := twoScale.coarse.fineMultiplicity
  let floor := pureWZ2SourceHorizontalRichFloor rho finalLoss
  let cost := pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
    MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))
  let heightCost := heightRetentionCost rho data.extraLoss
  have hhalfWithFine := pureWZ2GoodSourceCarrierBlocks_weightedSupply_half
    prepared hsmall
  have hhalf : MeasureTheory.volume prepared.shadow.union * cellSupply ≤
      (2 * ∑ block ∈ good, MeasureTheory.volume
        (pureWZ2SourceCarrierBlockShading prepared block).union) * cellSupply := by
    calc
      _ ≤ 2 * ∑ block ∈ good, MeasureTheory.volume
          (pureWZ2SourceCarrierBlockShading prepared block).union *
            cellSupply := by
        simpa [good, cellSupply, mul_assoc] using hhalfWithFine
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hvolumeIndexed :
      (∑ block ∈ good, MeasureTheory.volume
          (pureWZ2SourceCarrierBlockShading prepared block).union) =
        ∑ index : Fin data.outputs.indexCount,
          (data.outputs.pipeline index).window.volumeSupply := by
    symm
    apply Finset.sum_bij (fun index _ => data.outputs.block index)
    · intro index _; exact data.block_mem index
    · intro first _ second _ heq; exact data.outputs.block_injective heq
    · intro block hblock
      rcases data.block_surjective block hblock with ⟨index, rfl⟩
      exact ⟨index, Finset.mem_univ index, rfl⟩
    · intro index _; exact data.volumeSupply_eq index
  have hlocal :
      (∑ index : Fin data.outputs.indexCount,
          (data.outputs.pipeline index).window.volumeSupply) *
            cellSupply * multiplicity * floor ≤
        cost * heightCost *
          ∑ index : Fin data.outputs.indexCount,
            (data.outputs.rich index).heightLift.shading.mass := by
    calc
      _ = ∑ index : Fin data.outputs.indexCount,
          ((data.outputs.pipeline index).window.volumeSupply *
            cellSupply * multiplicity * floor) := by
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      _ ≤ ∑ index : Fin data.outputs.indexCount,
          (cost * heightCost *
            (data.outputs.rich index).heightLift.shading.mass) := by
        exact Finset.sum_le_sum fun index _ => by
          simpa [cost, heightCost, cellSupply, multiplicity, floor] using
            data.block_height_mass_bound_uniform index
      _ = cost * heightCost *
          ∑ index : Fin data.outputs.indexCount,
            (data.outputs.rich index).heightLift.shading.mass := by
        rw [Finset.mul_sum]
  calc
    MeasureTheory.volume prepared.shadow.union * cellSupply * multiplicity * floor ≤
        (2 * ∑ block ∈ good, MeasureTheory.volume
          (pureWZ2SourceCarrierBlockShading prepared block).union) *
            cellSupply * multiplicity * floor := by gcongr
    _ = 2 * ((∑ index : Fin data.outputs.indexCount,
          (data.outputs.pipeline index).window.volumeSupply) *
            cellSupply * multiplicity * floor) := by
      rw [hvolumeIndexed]
      ring
    _ ≤ 2 * (cost * heightCost *
          ∑ index : Fin data.outputs.indexCount,
            (data.outputs.rich index).heightLift.shading.mass) :=
      mul_le_mul_left' hlocal 2
    _ = 2 * cost * heightCost *
          ∑ index : Fin data.outputs.indexCount,
            (data.outputs.rich index).heightLift.shading.mass := by ring

/-- Select separated windows using the actual final height-lift masses. -/
theorem selectResidue_height_mass_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta
      volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (data : PureWZ2SourceHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta)
      prepared volumeLoss)
    (hsmall :
      2 * ((pureWZ2PositiveSourceCarrierBlocks prepared).card : ENNReal) *
          pureWZ2SourceHorizontalBlockThreshold
            rho delta sigma inputLoss volumeLoss ≤
        MeasureTheory.volume prepared.shadow.union *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass)) :
    ∃ residueData : PureWZ2SourceHorizontalBlockResidueData data.outputs,
      MeasureTheory.volume prepared.shadow.union *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass) *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
        128 * (pureWZ2SourceHorizontalVolumeCost
            rho delta sigma inputLoss *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
          heightRetentionCost rho data.extraLoss *
          residueData.family.shading.mass := by
  rcases data.outputs.selectResidue with ⟨residueData⟩
  refine ⟨residueData, (data.aggregate_height_mass_bound hsmall).trans ?_⟩
  calc
    2 * (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
          heightRetentionCost rho data.extraLoss *
          ∑ index : Fin data.outputs.indexCount,
            (data.outputs.rich index).heightLift.shading.mass ≤
      2 * (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
          heightRetentionCost rho data.extraLoss *
          (64 * residueData.family.shading.mass) := by
        gcongr
        exact residueData.total_mass_le
    _ = 128 * (pureWZ2SourceHorizontalVolumeCost
          rho delta sigma inputLoss *
        MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
        heightRetentionCost rho data.extraLoss *
        residueData.family.shading.mass := by ring

/-- Mass-weighted mod-64 selection after exact source-block aggregation. -/
theorem selectResidue_mass_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta
      volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (data : PureWZ2SourceHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta) (theoremEta := theoremEta)
      prepared volumeLoss)
    (hsmall :
      2 *
          ((pureWZ2PositiveSourceCarrierBlocks prepared).card : ENNReal) *
          pureWZ2SourceHorizontalBlockThreshold
            rho delta sigma inputLoss volumeLoss ≤
        MeasureTheory.volume prepared.shadow.union *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass)) :
    ∃ residueData : PureWZ2SourceHorizontalBlockResidueData data.outputs,
      MeasureTheory.volume prepared.shadow.union *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass ≤
        128 * (pureWZ2SourceHorizontalVolumeCost
            rho delta sigma inputLoss *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
          graphCellCost rho data.extraLoss *
          (54 * snappedHeightCap rho) *
          residueData.family.shading.mass := by
  rcases data.outputs.selectResidue with ⟨residueData⟩
  refine ⟨residueData, (data.aggregate_mass_bound hsmall).trans ?_⟩
  calc
    2 * (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
          graphCellCost rho data.extraLoss * (54 * snappedHeightCap rho) *
          ∑ index : Fin data.outputs.indexCount,
            (data.outputs.rich index).richShading.shading.mass ≤
        2 * (pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
          graphCellCost rho data.extraLoss * (54 * snappedHeightCap rho) *
          (64 * residueData.family.shading.mass) := by
      gcongr
      calc
        (∑ index : Fin data.outputs.indexCount,
            (data.outputs.rich index).richShading.shading.mass) ≤
          ∑ index : Fin data.outputs.indexCount,
            (data.outputs.rich index).heightLift.shading.mass :=
          Finset.sum_le_sum fun index _ =>
            (data.outputs.rich index).heightLift.mass_lower
        _ ≤ 64 * residueData.family.shading.mass :=
          residueData.total_mass_le
    _ = 128 * (pureWZ2SourceHorizontalVolumeCost
          rho delta sigma inputLoss *
        MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
        graphCellCost rho data.extraLoss * (54 * snappedHeightCap rho) *
        residueData.family.shading.mass := by ring

/-- Exact-weighted Lemma-24 exit on the original `delta` family. -/
theorem toOneScaleOfWeightedProducer
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss structuralLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {data : PureWZ2SourceHorizontalGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) prepared volumeLoss}
    (residueData : PureWZ2SourceHorizontalBlockResidueData data.outputs)
    (hinputStructural : inputLoss ≤ structuralLoss)
    (hstructuralFinal : structuralLoss ≤ finalLoss)
    (grainProducer :
      ∀ targetFamily : Kakeya.Streamlined.TubeFamily delta,
        ∀ targetShading : WZ1PaperTubeShading targetFamily,
          WZ1PaperIsLineClass targetFamily →
          WZ2PaperCroppedIsExtremal
              sigma structuralLoss targetFamily targetShading →
            Nonempty
              (PureWZ2GrainRefinementData
                targetShading sigma finalLoss))
    (haggregate :
      MeasureTheory.volume prepared.shadow.union *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass) *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
        128 * (pureWZ2SourceHorizontalVolumeCost
            rho delta sigma inputLoss *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
          heightRetentionCost rho data.extraLoss *
          residueData.family.shading.mass)
    (hfinalAbsorb :
      128 * (pureWZ2SourceHorizontalVolumeCost
            rho delta sigma inputLoss *
          MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
          heightRetentionCost rho data.extraLoss *
          (Kakeya.realRpowENN delta structuralLoss *
            (wz1PaperBodyFamily source.family).mass) ≤
        MeasureTheory.volume prepared.shadow.union *
          (twoScale.coarse.balanced.cellMass *
            twoScale.fine.balanced.cellMass) *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss) :
    Nonempty (PureWZ2LocallyLinearOneScaleData source finalLoss
      (pureWZ2SourceHorizontalFinalScale rho)) := by
  let cost := 128 * (pureWZ2SourceHorizontalVolumeCost
      rho delta sigma inputLoss *
    MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0))) *
    heightRetentionCost rho data.extraLoss
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hlocalCostPos : 0 < pureWZ2SourceHorizontalVolumeCost
      rho delta sigma inputLoss :=
    pureWZ2SourceHorizontalVolumeCost_pos hrho source.extremal.delta_pos
  have hlocalCostTop : pureWZ2SourceHorizontalVolumeCost
      rho delta sigma inputLoss ≠ ⊤ :=
    pureWZ2SourceHorizontalVolumeCost_ne_top _ _ _ _
  have hcubePos : 0 < MeasureTheory.volume
      (wz1PaperGridCube rho (0, 0, 0)) := by
    rw [wz1PaperGridCube_volume_exact hrho]
    positivity
  have hcubeTop : MeasureTheory.volume
      (wz1PaperGridCube rho (0, 0, 0)) ≠ ⊤ := by
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_ne_top
  have hcellCostPos : 0 < heightRetentionCost rho data.extraLoss := by
    unfold heightRetentionCost snappedHeightCap
    have hscale : 0 < 256 * rho := by positivity
    have hfirst : 0 < Real.rpow (256 * rho) (-data.extraLoss) :=
      Real.rpow_pos_of_pos hscale _
    apply ENNReal.mul_pos
    · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hcellCostTop : heightRetentionCost rho data.extraLoss ≠ ⊤ := by
    unfold heightRetentionCost snappedHeightCap
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hcostZero : cost ≠ 0 := by
    dsimp only [cost]
    positivity
  have hcostTop : cost ≠ ⊤ := by
    dsimp only [cost]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top hlocalCostTop hcubeTop)) hcellCostTop
  have hdenseBudget :
      Kakeya.realRpowENN delta structuralLoss *
          (wz1PaperBodyFamily source.family).mass ≤
        residueData.family.shading.mass := by
    apply (ENNReal.mul_le_mul_iff_left hcostZero hcostTop).mp
    calc
      (Kakeya.realRpowENN delta structuralLoss *
            (wz1PaperBodyFamily source.family).mass) * cost ≤
          MeasureTheory.volume prepared.shadow.union *
            (twoScale.coarse.balanced.cellMass *
              twoScale.fine.balanced.cellMass) *
            (twoScale.coarse.fineMultiplicity : ENNReal) *
            pureWZ2SourceHorizontalRichFloor rho finalLoss := by
        simpa [cost, mul_comm, mul_left_comm, mul_assoc] using hfinalAbsorb
      _ ≤ residueData.family.shading.mass * cost := by
        simpa [cost, mul_comm, mul_left_comm, mul_assoc] using haggregate
  have hdense : residueData.family.shading.IsLambdaDense
      (Kakeya.realRpowENN delta structuralLoss) := hdenseBudget
  exact residueData.family.toOneScaleOfGrainProducer
    hinputStructural hstructuralFinal grainProducer hdense

end PureWZ2SourceHorizontalGoodBlockFamilyData

end Kakeya.Assouad
