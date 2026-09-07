import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSaturatedResidue
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderReentryTrace

/-!
# Relative indexed mass for the saturated all-heavy-slab route

This module keeps the WZ Lemma-5.4 mass calculation division-free.  It first
compares one original heavy slab with the exact complete-height restriction
selected by the same saturated Theorem-5.2 graph, and only then sums over
slabs and pays the single mod-`64` separation loss.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2Node05V4RichTwoScaleCellPullbackData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)

/-- The two direct-rich calls retain relative indexed mass on their exact
dependent witness.  The first fine and coarse multiplicity bands are used on
the two sides of the volume cross-identity, so two copies of the first V4
regularity remain. -/
theorem mass_relative_lower
    (hrhoSmall : rhoRequested.1 ≤ 1 / 12) :
    wz2PaperPureRefinementFraction delta 61 *
          wz2PaperPureRefinementFraction rhoRequested.1 61 *
          current.grain.shading.mass ≤
      (twoScale.first.fourDegreeReceipts.regularity : ENNReal) ^ 2 *
        pullback.shading.mass := by
  let coarseVolume : ENNReal :=
    volume twoScale.first.finalCoarseShading.union
  let fineMultiplicity : ENNReal :=
    (twoScale.first.fourDegreeReceipts.fineDegreeFloor *
      twoScale.first.fourDegreeReceipts.muFine : ℕ)
  let regularity : ENNReal :=
    twoScale.first.fourDegreeReceipts.regularity
  have hfirstRetention :
      wz2PaperPureRefinementFraction delta 61 *
          current.grain.shading.mass ≤
        twoScale.first.refinedFineShading.mass :=
    twoScale.first.rich.total_mass_retention
  have hsecondVolume :
      wz2PaperPureRefinementFraction rhoRequested.1 61 * coarseVolume ≤
        regularity * volume twoScale.secondRefinedFineShading.union := by
    simpa only [coarseVolume, regularity] using
      twoScale.second_refined_volume_relative_lower
  have hfirstMassUpper :
      twoScale.first.refinedFineShading.mass ≤
        regularity * fineMultiplicity *
          volume twoScale.first.refinedFineShading.union := by
    simpa only [regularity, fineMultiplicity, Nat.cast_mul, mul_assoc] using
      twoScale.first.fourDegreeReceipts.fine_mass_le_degree_mul_volume
  have hpullbackMassLower :
      fineMultiplicity * volume pullback.shading.union ≤
        pullback.shading.mass := by
    apply multiplicity_floor_le_mass
    intro point hpoint
    dsimp only [fineMultiplicity]
    exact_mod_cast (pullback.source_constantMultiplicity point hpoint).1
  have hcross := pullback.balanced_volume_cross
  have hscaled :
      coarseVolume *
          (wz2PaperPureRefinementFraction delta 61 *
            wz2PaperPureRefinementFraction rhoRequested.1 61 *
            current.grain.shading.mass) ≤
        coarseVolume * (regularity ^ 2 * pullback.shading.mass) := by
    calc
      _ = wz2PaperPureRefinementFraction rhoRequested.1 61 *
          (wz2PaperPureRefinementFraction delta 61 *
            current.grain.shading.mass) * coarseVolume := by ring
      _ ≤ wz2PaperPureRefinementFraction rhoRequested.1 61 *
          twoScale.first.refinedFineShading.mass * coarseVolume := by gcongr
      _ ≤ wz2PaperPureRefinementFraction rhoRequested.1 61 *
          (regularity * fineMultiplicity *
            volume twoScale.first.refinedFineShading.union) *
          coarseVolume := by gcongr
      _ = regularity * fineMultiplicity *
          volume twoScale.first.refinedFineShading.union *
          (wz2PaperPureRefinementFraction rhoRequested.1 61 *
            coarseVolume) := by ring
      _ ≤ regularity * fineMultiplicity *
          volume twoScale.first.refinedFineShading.union *
          (regularity *
            volume twoScale.secondRefinedFineShading.union) := by gcongr
      _ = regularity ^ 2 * fineMultiplicity *
          (volume twoScale.first.refinedFineShading.union *
            volume twoScale.secondRefinedFineShading.union) := by ring
      _ = regularity ^ 2 * fineMultiplicity *
          (volume pullback.shading.union * coarseVolume) := by rw [hcross]
      _ = coarseVolume *
          (regularity ^ 2 *
            (fineMultiplicity * volume pullback.shading.union)) := by ring
      _ ≤ coarseVolume * (regularity ^ 2 * pullback.shading.mass) := by gcongr
  have hcoarsePos : 0 < coarseVolume := by
    have hpowerPos : 0 < Kakeya.realRpowENN rhoRequested.1
        (sigma + 2 * schedule.firstOutputLoss) :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos
          twoScale.first.publicSticky.coarse_extremal.delta_pos _)
    exact hpowerPos.trans_le (by
      simpa only [coarseVolume] using
        PureWZ2.proposition63_sticky_coarse_union_volume_lower
          twoScale.first.publicSticky hrhoSmall)
  have hcoarseTop : coarseVolume ≠ ⊤ := by
    have hpowerTop :
        Kakeya.realRpowENN rhoRequested.1
            (sigma - schedule.firstOutputLoss) ≠ ⊤ := by
      simp [Kakeya.realRpowENN]
    exact ne_top_of_le_ne_top hpowerTop <| by
      simpa only [coarseVolume] using
        twoScale.first.publicSticky.coarse_extremal.volume_upper
  apply (ENNReal.mul_le_mul_iff_right hcoarsePos.ne' hcoarseTop).mp
  simpa only [mul_comm] using hscaled

end PureWZ2Node05V4RichTwoScaleCellPullbackData

namespace PureWZ2Node05V4RichHeavySlabSaturatedTailFamily

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss neighborhoodLoss finalLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {family : PureWZ2Node05V4RichHeavySlabNeighborhoodFamily
      pullback neighborhoodLoss}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {projection : PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (tail : PureWZ2Node05V4RichHeavySlabSaturatedTailFamily
      (eta := eta) family hbridge projection)

def saturationFloor
    (_tail : PureWZ2Node05V4RichHeavySlabSaturatedTailFamily
      (eta := eta) family hbridge projection) : ENNReal :=
  Kakeya.realRpowENN (4 * rhoRequested.1)
    (3 / 2 + sigma / 2 + eta)

def blockRichHeightFloor
    (_tail : PureWZ2Node05V4RichHeavySlabSaturatedTailFamily
      (eta := eta) family hbridge projection)
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}) : ENNReal :=
  Kakeya.realRpowENN
    (wz1Lemma23Theorem22Scale
      (family.block heightIndex).neighborhood.graphScale)
    (finalLoss - 1)

def richHeightFloor
    (_tail : PureWZ2Node05V4RichHeavySlabSaturatedTailFamily
      (eta := eta) family hbridge projection) : ENNReal :=
  Kakeya.realRpowENN
    (wz1Lemma23Theorem22Scale (256 * rho)) (finalLoss - 1)

def sourceMultiplicityFloor
    (_tail : PureWZ2Node05V4RichHeavySlabSaturatedTailFamily
      (eta := eta) family hbridge projection) : ENNReal :=
  ((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
    twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal)

theorem complete_multiplicityFloor_eq
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}) :
    ((tail.complete heightIndex).multiplicityFloor : ENNReal) =
      tail.sourceMultiplicityFloor := by
  rw [(tail.complete heightIndex).multiplicityFloor_eq]
  rfl

def uniformRelativeMassCost
    (_tail : PureWZ2Node05V4RichHeavySlabSaturatedTailFamily
      (eta := eta) family hbridge projection)
    (extraLoss : ℝ) : ENNReal :=
  54 * ENNReal.ofReal (Real.sqrt rho) *
    pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
      1 sigma inputLoss delta rho *
    PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost rho extraLoss *
    PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho

theorem blockRichHeightFloor_eq
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}) :
    tail.blockRichHeightFloor heightIndex = tail.richHeightFloor := by
  simp [blockRichHeightFloor, richHeightFloor,
    PureWZ2PreCommonBinGlobalGrainNeighborhoodData.graphScale,
    PureWZ2PreCommonBinGlobalGrainNeighborhoodData.saturatedGraphScale]

def blockGraphCellVolumeCost
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}) : ENNReal :=
  ((tail.scheduled heightIndex).finite.finiteGraph.graph.residue.volumeCost :
      ENNReal) *
    ENNReal.ofReal (gridSide
      ((family.block heightIndex).neighborhood.graphScale / 2)) *
    (ENNReal.ofReal (family.block heightIndex).neighborhood.graphScale ^ 2 *
      ENNReal.ofReal Real.pi)

def blockSnappedHeightCount
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}) : ENNReal :=
  ((wz1Lemma23SnappedHeights
    (tail.scheduled heightIndex).finite.finiteGraph.graph.residue.cells).card :
      ℕ)

/-- Exact cell-volume upper bound for one saturated finite graph.  Its
`volumeCost` already contains both finite regularization losses. -/
theorem graphShadow_volume_le_cells
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}) :
    volume (family.block heightIndex).neighborhood.graphShadow.union ≤
      tail.blockGraphCellVolumeCost heightIndex *
        ((tail.scheduled heightIndex).finite.finiteGraph.graph.residue.cells.card :
          ENNReal) := by
  have h :=
    (tail.scheduled heightIndex).finite.finiteGraph.graph.residue.volume_cell_bound
  calc
    _ ≤ (((tail.scheduled heightIndex).finite.finiteGraph.graph.residue.volumeCost *
          (tail.scheduled heightIndex).finite.finiteGraph.graph.residue.cells.card :
            ℕ) : ENNReal) *
        ENNReal.ofReal (gridSide
          ((family.block heightIndex).neighborhood.graphScale / 2)) *
        (ENNReal.ofReal (family.block heightIndex).neighborhood.graphScale ^ 2 *
          ENNReal.ofReal Real.pi) := h
    _ = _ := by
      simp only [blockGraphCellVolumeCost, Nat.cast_mul]
      ring

/-- The snapped graph heights of every saturated block stay in its single
paper height window. -/
theorem snappedHeights_card_le
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}) :
    ((wz1Lemma23SnappedHeights
      (tail.scheduled heightIndex).finite.finiteGraph.graph.residue.cells).card :
        ℝ) ≤
      3 / Real.sqrt (family.block heightIndex).neighborhood.graphScale := by
  let scheduled := tail.scheduled heightIndex
  exact wz1Lemma23_height_layer_count
    (family.block heightIndex).neighborhood.graphScale_pos
    (tail.graphScale_le_one heightIndex)
    (scheduled.finite.prep.windowed.residue_cells_window
      scheduled.finite.finiteGraph.graph.residue)

/-- Uniform graph-cell volume cost after applying the pre-runtime analytic
bound to the actual finite residue. -/
theorem graphShadow_volume_le_uniformCells
    (analytic : PureWZ2SourceHorizontalAnalyticThreshold projection.theoremEta)
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback})
    (hrhoSmall : rho ≤ analytic.rho0) :
    volume (family.block heightIndex).neighborhood.graphShadow.union ≤
      PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho analytic.budget.extraLoss *
        ((tail.scheduled heightIndex).finite.finiteGraph.graph.residue.cells.card :
          ENNReal) := by
  let neighborhood := (family.block heightIndex).neighborhood
  let scheduled := tail.scheduled heightIndex
  let scale := neighborhood.graphScale
  let volumeValue := volume neighborhood.graphShadow.union
  have hscale : 0 < scale := neighborhood.graphScale_pos
  have hvolumeTop : volumeValue ≠ ⊤ :=
    ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
      (measure_mono (neighborhood.graphInput hbridge
        (tail.graphScale_le_one heightIndex)).shadow_ball)
  have hvolumeOfReal : ENNReal.ofReal volumeValue.toReal = volumeValue :=
    ENNReal.ofReal_toReal hvolumeTop
  have hraw := scheduled.finite.finiteGraph.graph.residue.cell_count_from_volume
    (tail.graphScale_le_one heightIndex) volumeValue.toReal ENNReal.toReal_nonneg
    (by simpa only [volumeValue] using hvolumeOfReal.le)
  have hextra := analytic.extra_saturatedFiniteGraph scheduled.finite
    (by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos)
    hrhoSmall
  have hextraPos :
      0 < (scheduled.finite.finiteGraph.graph.residue.extraCost : ℝ) := by
    exact_mod_cast
      scheduled.finite.finiteGraph.graph.residue.extraCost_pos
  have hscalePowerPos : 0 < Real.rpow scale (5 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hscale _
  have hactualPos : 0 < 8 *
      (scheduled.finite.finiteGraph.graph.residue.extraCost : ℝ) *
      Real.rpow scale (5 / 2 : ℝ) := by
    exact mul_pos (mul_pos (by norm_num) hextraPos) hscalePowerPos
  have hreal : volumeValue.toReal ≤
      (8 * Real.rpow scale (-analytic.budget.extraLoss) *
        Real.rpow scale (5 / 2 : ℝ)) *
      ((scheduled.finite.finiteGraph.graph.residue.cells.card : ℕ) : ℝ) := by
    calc
      volumeValue.toReal ≤
          (8 * (scheduled.finite.finiteGraph.graph.residue.extraCost : ℝ) *
            Real.rpow scale (5 / 2 : ℝ)) *
          ((scheduled.finite.finiteGraph.graph.residue.cells.card : ℕ) : ℝ) :=
        by simpa [mul_comm] using (div_le_iff₀ hactualPos).mp hraw
      _ ≤ (8 * Real.rpow scale (-analytic.budget.extraLoss) *
            Real.rpow scale (5 / 2 : ℝ)) *
          ((scheduled.finite.finiteGraph.graph.residue.cells.card : ℕ) : ℝ) := by
        gcongr
  calc
    volume neighborhood.graphShadow.union = ENNReal.ofReal volumeValue.toReal := by
      rw [hvolumeOfReal]
    _ ≤ ENNReal.ofReal
        ((8 * Real.rpow scale (-analytic.budget.extraLoss) *
          Real.rpow scale (5 / 2 : ℝ)) *
        ((scheduled.finite.finiteGraph.graph.residue.cells.card : ℕ) : ℝ)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho analytic.budget.extraLoss *
        ((scheduled.finite.finiteGraph.graph.residue.cells.card : ℕ) : ENNReal) := by
      rw [ENNReal.ofReal_mul (by
        exact mul_nonneg (mul_nonneg (by norm_num)
          (Real.rpow_nonneg hscale.le _)) hscalePowerPos.le),
        ENNReal.ofReal_natCast]
      simp [PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost, scale,
        neighborhood,
        PureWZ2PreCommonBinGlobalGrainNeighborhoodData.saturatedGraphScale]

/-- Family-free version of the single-window snapped-height bound. -/
theorem snappedHeights_le_cap
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}) :
    tail.blockSnappedHeightCount heightIndex ≤
      PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho := by
  have hreal := tail.snappedHeights_card_le heightIndex
  have henn := ENNReal.ofReal_le_ofReal hreal
  have hcast : tail.blockSnappedHeightCount heightIndex =
      ENNReal.ofReal
        (((wz1Lemma23SnappedHeights
          (tail.scheduled heightIndex).finite.finiteGraph.graph.residue.cells).card :
            ℕ) : ℝ) := by
    simp [blockSnappedHeightCount]
  rw [hcast]
  simpa [PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap,
    PureWZ2PreCommonBinGlobalGrainNeighborhoodData.graphScale,
    PureWZ2PreCommonBinGlobalGrainNeighborhoodData.saturatedGraphScale]
    using henn

/-- The sharp division-free block estimate before converting the incoming
source volume to indexed mass.  Keeping the multiplicity floor on the left
allows the all-slab sum to pay the first-V4 regularity only once. -/
theorem sourceSlab_volume_mul_gains_le
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}) :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) *
          tail.saturationFloor *
          tail.richHeightFloor *
          ((tail.complete heightIndex).multiplicityFloor : ENNReal) *
          pullback.firstPostBalanced.cellMass ≤
      54 * ENNReal.ofReal (Real.sqrt rho) *
        pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
          1 sigma inputLoss delta rho *
        tail.blockGraphCellVolumeCost heightIndex *
        tail.blockSnappedHeightCount heightIndex *
        (tail.complete heightIndex).sourceRestriction.mass := by
  let block := family.block heightIndex
  let neighborhood := block.neighborhood
  let scheduled := tail.scheduled heightIndex
  let complete := tail.complete heightIndex
  let slabVolume :=
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1)
  let saturationFloor := tail.saturationFloor
  let richFloor := tail.richHeightFloor
  let multiplicityFloor : ENNReal := complete.multiplicityFloor
  let firstCellMass := pullback.firstPostBalanced.cellMass
  let root := ENNReal.ofReal (Real.sqrt rho)
  let neighborhoodCost :=
    pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
      1 sigma inputLoss delta rho
  let graphVolume := volume neighborhood.graphShadow.union
  let graphCellCost := tail.blockGraphCellVolumeCost heightIndex
  let graphCellCount : ENNReal :=
    scheduled.finite.finiteGraph.graph.residue.cells.card
  let heightCount := tail.blockSnappedHeightCount heightIndex
  let retainedMass := complete.sourceRestriction.mass
  have hslab : slabVolume ≤ root * neighborhoodCost *
      (neighborhood.K : ENNReal) := by
    simpa only [slabVolume, root, neighborhoodCost, neighborhood, block]
      using block.source_slab_volume_upper
  have hsaturation : (neighborhood.K : ENNReal) * saturationFloor ≤
      graphVolume := by
    rw [show graphVolume = volume neighborhood.saturatedUnion by
      dsimp only [graphVolume]
      rw [neighborhood.graphShadow_union]]
    apply neighborhood.saturatedUnion_volume_lower
    intro y hy
    let grain := scheduled.finite.saturated.fullGrainFor y hy
    simpa only [saturationFloor,
      PureWZ2Node05V4RichHeavySlabSaturatedTailFamily.saturationFloor,
      grain.certificateScale_eq, grain.saturatedSource_eq] using
        grain.saturatedSource_volume_lower
  have hgraphVolume : graphVolume ≤ graphCellCost * graphCellCount := by
    simpa only [graphVolume, graphCellCost, graphCellCount, neighborhood, block,
      scheduled] using tail.graphShadow_volume_le_cells heightIndex
  have hgraphMass : richFloor * graphCellCount * multiplicityFloor *
        firstCellMass ≤ 54 * heightCount * retainedMass := by
    dsimp only [richFloor]
    rw [← tail.blockRichHeightFloor_eq heightIndex]
    simpa only [blockRichHeightFloor, graphCellCount, multiplicityFloor,
      firstCellMass, heightCount, blockSnappedHeightCount, retainedMass, complete,
      scheduled, neighborhood, block] using complete.graph_cells_to_source_mass
  calc
    slabVolume * saturationFloor * richFloor * multiplicityFloor *
          firstCellMass ≤
        (root * neighborhoodCost * (neighborhood.K : ENNReal)) *
          saturationFloor * richFloor * multiplicityFloor * firstCellMass := by
      gcongr
    _ = root * neighborhoodCost *
          ((neighborhood.K : ENNReal) * saturationFloor) *
          (richFloor * multiplicityFloor * firstCellMass) := by ring
    _ ≤ root * neighborhoodCost * graphVolume *
          (richFloor * multiplicityFloor * firstCellMass) := by gcongr
    _ ≤ root * neighborhoodCost * (graphCellCost * graphCellCount) *
          (richFloor * multiplicityFloor * firstCellMass) := by gcongr
    _ = root * neighborhoodCost * graphCellCost *
          (richFloor * graphCellCount * multiplicityFloor * firstCellMass) := by
      ring
    _ ≤ root * neighborhoodCost * graphCellCost *
          (54 * heightCount * retainedMass) := by gcongr
    _ = 54 * root * neighborhoodCost * graphCellCost * heightCount *
          retainedMass := by ring

/-- Uniform form of the sharp block estimate.  The graph regularization cost
and the number of snapped graph heights are bounded before summing the heavy
slabs. -/
theorem sourceSlab_volume_mul_uniform_gains_le
    (analytic : PureWZ2SourceHorizontalAnalyticThreshold projection.theoremEta)
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback})
    (hrhoSmall : rho ≤ analytic.rho0) :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) *
          tail.saturationFloor * tail.richHeightFloor *
          ((tail.complete heightIndex).multiplicityFloor : ENNReal) *
          pullback.firstPostBalanced.cellMass ≤
      54 * ENNReal.ofReal (Real.sqrt rho) *
        pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
          1 sigma inputLoss delta rho *
        PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho analytic.budget.extraLoss *
        PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho *
        (tail.complete heightIndex).sourceRestriction.mass := by
  let block := family.block heightIndex
  let neighborhood := block.neighborhood
  let scheduled := tail.scheduled heightIndex
  let complete := tail.complete heightIndex
  let slabVolume :=
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1)
  let saturationFloor := tail.saturationFloor
  let richFloor := tail.richHeightFloor
  let multiplicityFloor : ENNReal := complete.multiplicityFloor
  let firstCellMass := pullback.firstPostBalanced.cellMass
  let root := ENNReal.ofReal (Real.sqrt rho)
  let neighborhoodCost :=
    pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
      1 sigma inputLoss delta rho
  let graphVolume := volume neighborhood.graphShadow.union
  let graphCellCost :=
    PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
      rho analytic.budget.extraLoss
  let graphCellCount : ENNReal :=
    scheduled.finite.finiteGraph.graph.residue.cells.card
  let heightCap :=
    PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho
  let retainedMass := complete.sourceRestriction.mass
  have hslab : slabVolume ≤ root * neighborhoodCost *
      (neighborhood.K : ENNReal) := by
    simpa only [slabVolume, root, neighborhoodCost, neighborhood, block]
      using block.source_slab_volume_upper
  have hsaturation : (neighborhood.K : ENNReal) * saturationFloor ≤
      graphVolume := by
    rw [show graphVolume = volume neighborhood.saturatedUnion by
      dsimp only [graphVolume]
      rw [neighborhood.graphShadow_union]]
    apply neighborhood.saturatedUnion_volume_lower
    intro y hy
    let grain := scheduled.finite.saturated.fullGrainFor y hy
    simpa only [saturationFloor,
      PureWZ2Node05V4RichHeavySlabSaturatedTailFamily.saturationFloor,
      grain.certificateScale_eq, grain.saturatedSource_eq] using
        grain.saturatedSource_volume_lower
  have hgraphVolume : graphVolume ≤ graphCellCost * graphCellCount := by
    simpa only [graphVolume, graphCellCost, graphCellCount, neighborhood, block,
      scheduled] using
        tail.graphShadow_volume_le_uniformCells analytic heightIndex hrhoSmall
  have hgraphMass : richFloor * graphCellCount * multiplicityFloor *
        firstCellMass ≤ 54 * heightCap * retainedMass := by
    have hraw := complete.graph_cells_to_source_mass
    have hheight := tail.snappedHeights_le_cap heightIndex
    calc
      richFloor * graphCellCount * multiplicityFloor * firstCellMass =
          tail.blockRichHeightFloor heightIndex * graphCellCount *
            multiplicityFloor * firstCellMass := by
        rw [tail.blockRichHeightFloor_eq heightIndex]
      _ ≤ 54 * tail.blockSnappedHeightCount heightIndex * retainedMass := by
        simpa only [blockRichHeightFloor, graphCellCount, multiplicityFloor,
          firstCellMass, blockSnappedHeightCount, retainedMass, complete,
          scheduled, neighborhood, block] using hraw
      _ ≤ 54 * heightCap * retainedMass := by gcongr
  calc
    slabVolume * saturationFloor * richFloor * multiplicityFloor *
          firstCellMass ≤
        (root * neighborhoodCost * (neighborhood.K : ENNReal)) *
          saturationFloor * richFloor * multiplicityFloor * firstCellMass := by
      gcongr
    _ = root * neighborhoodCost *
          ((neighborhood.K : ENNReal) * saturationFloor) *
          (richFloor * multiplicityFloor * firstCellMass) := by ring
    _ ≤ root * neighborhoodCost * graphVolume *
          (richFloor * multiplicityFloor * firstCellMass) := by gcongr
    _ ≤ root * neighborhoodCost * (graphCellCost * graphCellCount) *
          (richFloor * multiplicityFloor * firstCellMass) := by gcongr
    _ = root * neighborhoodCost * graphCellCost *
          (richFloor * graphCellCount * multiplicityFloor * firstCellMass) := by
      ring
    _ ≤ root * neighborhoodCost * graphCellCost *
          (54 * heightCap * retainedMass) := by gcongr
    _ = 54 * root * neighborhoodCost * graphCellCost * heightCap *
          retainedMass := by ring

/-- Common-multiplier form used for the finite all-heavy-slab sum. -/
theorem sourceSlab_volume_mul_common_gains_le
    (analytic : PureWZ2SourceHorizontalAnalyticThreshold projection.theoremEta)
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback})
    (hrhoSmall : rho ≤ analytic.rho0) :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) *
          (tail.saturationFloor * tail.richHeightFloor *
            tail.sourceMultiplicityFloor *
            pullback.firstPostBalanced.cellMass) ≤
      tail.uniformRelativeMassCost analytic.budget.extraLoss *
        (tail.complete heightIndex).sourceRestriction.mass := by
  have h := tail.sourceSlab_volume_mul_uniform_gains_le
    analytic heightIndex hrhoSmall
  rw [← tail.complete_multiplicityFloor_eq heightIndex]
  simpa [uniformRelativeMassCost, mul_assoc] using h

/-- Exact same-witness relative mass estimate in one heavy slab.  The first-V4
multiplicity ceiling controls the incoming slab mass, while its matching floor
is consumed by `graph_cells_to_source_mass`; hence only one regularity factor
remains. -/
theorem sourceSlab_mass_mul_gains_le
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}) :
    (pullback.standardSqrtSlabSourceShading heightIndex.1).mass *
          tail.saturationFloor *
          tail.blockRichHeightFloor heightIndex *
          pullback.firstPostBalanced.cellMass ≤
      54 * (twoScale.first.fourDegreeReceipts.regularity : ENNReal) *
        ENNReal.ofReal (Real.sqrt rho) *
        pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
          1 sigma inputLoss delta rho *
        tail.blockGraphCellVolumeCost heightIndex *
        tail.blockSnappedHeightCount heightIndex *
        (tail.complete heightIndex).sourceRestriction.mass := by
  let block := family.block heightIndex
  let neighborhood := block.neighborhood
  let scheduled := tail.scheduled heightIndex
  let complete := tail.complete heightIndex
  let sourceMass :=
    (pullback.standardSqrtSlabSourceShading heightIndex.1).mass
  let slabVolume :=
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1)
  let regularity : ENNReal :=
    twoScale.first.fourDegreeReceipts.regularity
  let multiplicityFloor : ENNReal := complete.multiplicityFloor
  let multiplicityCeiling : ENNReal := complete.multiplicityCeiling
  let saturationFloor := tail.saturationFloor
  let richFloor := tail.blockRichHeightFloor heightIndex
  let firstCellMass := pullback.firstPostBalanced.cellMass
  let root := ENNReal.ofReal (Real.sqrt rho)
  let neighborhoodCost :=
    pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
      1 sigma inputLoss delta rho
  let graphVolume := volume neighborhood.graphShadow.union
  let graphCellCost := tail.blockGraphCellVolumeCost heightIndex
  let graphCellCount : ENNReal :=
    scheduled.finite.finiteGraph.graph.residue.cells.card
  let heightCount := tail.blockSnappedHeightCount heightIndex
  let retainedMass := complete.sourceRestriction.mass
  have hceiling : multiplicityCeiling = regularity * multiplicityFloor := by
    dsimp only [multiplicityCeiling, regularity, multiplicityFloor]
    rw [complete.multiplicityCeiling_eq, complete.multiplicityFloor_eq]
    push_cast
    ring
  have hsourceMass : sourceMass ≤ multiplicityCeiling * slabVolume := by
    rw [show multiplicityCeiling =
        (((twoScale.first.fourDegreeReceipts.regularity *
          twoScale.first.fourDegreeReceipts.fineDegreeFloor) *
            twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) by
      dsimp only [multiplicityCeiling]
      rw [complete.multiplicityCeiling_eq]]
    exact pullback.standardSqrtSlabSourceShading_mass_upper heightIndex.1
  have hslab : slabVolume ≤ root * neighborhoodCost *
      (neighborhood.K : ENNReal) := by
    simpa only [slabVolume, root, neighborhoodCost, neighborhood, block]
      using block.source_slab_volume_upper
  have hsaturation : (neighborhood.K : ENNReal) * saturationFloor ≤
      graphVolume := by
    rw [show graphVolume = volume neighborhood.saturatedUnion by
      dsimp only [graphVolume]
      rw [neighborhood.graphShadow_union]]
    apply neighborhood.saturatedUnion_volume_lower
    intro y hy
    let grain := scheduled.finite.saturated.fullGrainFor y hy
    simpa only [saturationFloor,
      PureWZ2Node05V4RichHeavySlabSaturatedTailFamily.saturationFloor,
      grain.certificateScale_eq, grain.saturatedSource_eq] using
        grain.saturatedSource_volume_lower
  have hgraphVolume : graphVolume ≤ graphCellCost * graphCellCount := by
    simpa only [graphVolume, graphCellCost, graphCellCount, neighborhood, block,
      scheduled] using tail.graphShadow_volume_le_cells heightIndex
  have hgraphMass : richFloor * graphCellCount * multiplicityFloor *
        firstCellMass ≤ 54 * heightCount * retainedMass := by
    simpa only [richFloor, blockRichHeightFloor, graphCellCount,
      multiplicityFloor, firstCellMass, heightCount, blockSnappedHeightCount,
      retainedMass, complete, scheduled, neighborhood, block] using
        complete.graph_cells_to_source_mass
  calc
    sourceMass * saturationFloor * richFloor * firstCellMass ≤
        (multiplicityCeiling * slabVolume) * saturationFloor *
          richFloor * firstCellMass := by gcongr
    _ ≤ (multiplicityCeiling *
          (root * neighborhoodCost * (neighborhood.K : ENNReal))) *
          saturationFloor * richFloor * firstCellMass := by gcongr
    _ = regularity * root * neighborhoodCost *
          ((neighborhood.K : ENNReal) * saturationFloor) *
          (richFloor * multiplicityFloor * firstCellMass) := by
      rw [hceiling]
      ring
    _ ≤ regularity * root * neighborhoodCost * graphVolume *
          (richFloor * multiplicityFloor * firstCellMass) := by gcongr
    _ ≤ regularity * root * neighborhoodCost *
          (graphCellCost * graphCellCount) *
          (richFloor * multiplicityFloor * firstCellMass) := by gcongr
    _ = regularity * root * neighborhoodCost * graphCellCost *
          (richFloor * graphCellCount * multiplicityFloor * firstCellMass) := by
      ring
    _ ≤ regularity * root * neighborhoodCost * graphCellCost *
          (54 * heightCount * retainedMass) := by gcongr
    _ = 54 * regularity * root * neighborhoodCost * graphCellCost *
          heightCount * retainedMass := by ring

end PureWZ2Node05V4RichHeavySlabSaturatedTailFamily

namespace PureWZ2Node05V4RichSaturatedResidueData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss neighborhoodLoss finalLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {family : PureWZ2Node05V4RichHeavySlabNeighborhoodFamily
      pullback neighborhoodLoss}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {projection : PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    {tail : PureWZ2Node05V4RichHeavySlabSaturatedTailFamily
      (eta := eta) family hbridge projection}
    {trapezoids : PureWZ2Node05V4RichSaturatedTrapezoidFamily tail}
    (residueData : PureWZ2Node05V4RichSaturatedResidueData trapezoids)

/-- Complete fixed/runtime cost in the all-heavy-slab relative-mass return.
The three regularity factors are respectively the two-call source pullback
and the conversion of heavy union volume to source indexed mass.  This is the
literal positive product from the paper ledger: adjoining `1` here would lose
the scale powers that must cancel against the gains in the final scalar
absorption. -/
def totalRelativeMassCost
    (_residueData : PureWZ2Node05V4RichSaturatedResidueData trapezoids)
    (analytic : PureWZ2SourceHorizontalAnalyticThreshold projection.theoremEta) :
    ENNReal :=
  128 * (twoScale.first.fourDegreeReceipts.regularity : ENNReal) ^ 3 *
    tail.uniformRelativeMassCost analytic.budget.extraLoss

/-- WZ Lemma-5.4 relative indexed-mass estimate after the single heavy-slab
selection and the single mod-`64` separation.  The first-V4 multiplicity band
is used globally, so only one regularity factor is paid. -/
theorem pullback_mass_mul_gains_le
    (analytic : PureWZ2SourceHorizontalAnalyticThreshold projection.theoremEta)
    (hrhoSmall : rho ≤ analytic.rho0) :
    pullback.shading.mass * tail.saturationFloor * tail.richHeightFloor *
          pullback.firstPostBalanced.cellMass ≤
      128 * (twoScale.first.fourDegreeReceipts.regularity : ENNReal) *
        tail.uniformRelativeMassCost analytic.budget.extraLoss *
        residueData.shading.mass := by
  let HeavySlab := {heightIndex //
    heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}
  let regularity : ENNReal := twoScale.first.fourDegreeReceipts.regularity
  let multiplicityFloor := tail.sourceMultiplicityFloor
  let gain := tail.saturationFloor * tail.richHeightFloor *
    multiplicityFloor * pullback.firstPostBalanced.cellMass
  let cost := tail.uniformRelativeMassCost analytic.budget.extraLoss
  have hsourceUpper : pullback.shading.mass ≤
      (regularity * multiplicityFloor) * volume pullback.shading.union := by
    apply mass_le_of_pointMultiplicity_le
    intro point hpoint
    have hband := pullback.source_constantMultiplicity point hpoint
    have hcast :
        (pullback.shading.pointMultiplicity point : ENNReal) ≤
          (((twoScale.first.fourDegreeReceipts.regularity *
            twoScale.first.fourDegreeReceipts.fineDegreeFloor) *
              twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) := by
      exact_mod_cast hband.2
    simpa [regularity, multiplicityFloor,
      PureWZ2Node05V4RichHeavySlabSaturatedTailFamily.sourceMultiplicityFloor,
      Nat.cast_mul, mul_assoc] using hcast
  have hheavy := pullback.heavySlabs_retains_half_volume
  have hheavy' : volume pullback.shading.union ≤
      2 * ∑ heightIndex : HeavySlab,
        volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) := by
    have hsum :
        (∑ heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback,
          volume (pullback.standardSqrtSlabSourceRegion heightIndex)) =
        ∑ heightIndex : HeavySlab,
          volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) :=
      Finset.sum_subtype
        (pureWZ2Node05V4RichHeavySlabs pullback) (fun _ => Iff.rfl) _
    exact hheavy.trans_eq (congrArg (fun value => 2 * value) hsum)
  have hblock : ∀ heightIndex : HeavySlab,
      volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) * gain ≤
        cost * (tail.complete heightIndex).sourceRestriction.mass := by
    intro heightIndex
    simpa only [HeavySlab, gain, cost] using
      tail.sourceSlab_volume_mul_common_gains_le
        analytic heightIndex hrhoSmall
  have hsum :
      (∑ heightIndex : HeavySlab,
        volume (pullback.standardSqrtSlabSourceRegion heightIndex.1)) * gain ≤
      cost * ∑ heightIndex : HeavySlab,
        (tail.complete heightIndex).sourceRestriction.mass := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_le_sum fun heightIndex _ => hblock heightIndex
  have hresidue := residueData.total_completeMass_le_shading_mass
  calc
    pullback.shading.mass * tail.saturationFloor * tail.richHeightFloor *
          pullback.firstPostBalanced.cellMass ≤
        ((regularity * multiplicityFloor) *
          volume pullback.shading.union) * tail.saturationFloor *
            tail.richHeightFloor * pullback.firstPostBalanced.cellMass := by
      gcongr
    _ ≤ ((regularity * multiplicityFloor) *
          (2 * ∑ heightIndex : HeavySlab,
            volume (pullback.standardSqrtSlabSourceRegion heightIndex.1))) *
          tail.saturationFloor * tail.richHeightFloor *
            pullback.firstPostBalanced.cellMass := by
      gcongr
    _ = 2 * regularity *
          ((∑ heightIndex : HeavySlab,
            volume (pullback.standardSqrtSlabSourceRegion heightIndex.1)) *
              gain) := by
      dsimp only [gain]
      ring
    _ ≤ 2 * regularity *
          (cost * ∑ heightIndex : HeavySlab,
            (tail.complete heightIndex).sourceRestriction.mass) := by gcongr
    _ ≤ 2 * regularity * (cost * (64 * residueData.shading.mass)) := by
      gcongr
    _ = 128 * regularity * cost * residueData.shading.mass := by
      ring
    _ = _ := rfl

/-- Compose the two direct-rich relative mass transfers with the all-heavy-slab
Theorem-5.2 residue.  Every factor is attached to the same dependent two-call
witness and the literal current-source restriction. -/
theorem source_mass_mul_total_gains_le
    (analytic : PureWZ2SourceHorizontalAnalyticThreshold projection.theoremEta)
    (hrhoSmall : rho ≤ analytic.rho0)
    (hrhoRequestedSmall : rhoRequested.1 ≤ 1 / 12) :
    wz2PaperPureRefinementFraction delta 61 *
          wz2PaperPureRefinementFraction rhoRequested.1 61 *
          current.grain.shading.mass * tail.saturationFloor *
          tail.richHeightFloor * pullback.firstPostBalanced.cellMass ≤
      residueData.totalRelativeMassCost analytic * residueData.shading.mass := by
  have hsource := pullback.mass_relative_lower hrhoRequestedSmall
  have hresidue := residueData.pullback_mass_mul_gains_le analytic hrhoSmall
  calc
    _ = (wz2PaperPureRefinementFraction delta 61 *
          wz2PaperPureRefinementFraction rhoRequested.1 61 *
          current.grain.shading.mass) *
        (tail.saturationFloor * tail.richHeightFloor *
          pullback.firstPostBalanced.cellMass) := by ring
    _ ≤ ((twoScale.first.fourDegreeReceipts.regularity : ENNReal) ^ 2 *
          pullback.shading.mass) *
        (tail.saturationFloor * tail.richHeightFloor *
          pullback.firstPostBalanced.cellMass) :=
      mul_le_mul_right' hsource _
    _ = (twoScale.first.fourDegreeReceipts.regularity : ENNReal) ^ 2 *
          (pullback.shading.mass * tail.saturationFloor *
            tail.richHeightFloor * pullback.firstPostBalanced.cellMass) := by ring
    _ ≤ (twoScale.first.fourDegreeReceipts.regularity : ENNReal) ^ 2 *
          (128 * (twoScale.first.fourDegreeReceipts.regularity : ENNReal) *
            tail.uniformRelativeMassCost analytic.budget.extraLoss *
              residueData.shading.mass) :=
      mul_le_mul_left' hresidue _
    _ = (128 * (twoScale.first.fourDegreeReceipts.regularity : ENNReal) ^ 3 *
          tail.uniformRelativeMassCost analytic.budget.extraLoss) *
        residueData.shading.mass := by ring
    _ = residueData.totalRelativeMassCost analytic *
          residueData.shading.mass := by
      rfl

/-- Density of the literal complete-source-height residue after one scalar
absorption.  The source density, both direct-rich refinements, saturation,
Theorem-5.2 height selection, and mod-`64` separation are all visible in the
premise. -/
theorem dense_of_total_budget
    (analytic : PureWZ2SourceHorizontalAnalyticThreshold projection.theoremEta)
    (hrhoSmall : rho ≤ analytic.rho0)
    (hrhoRequestedSmall : rhoRequested.1 ≤ 1 / 12)
    (densityLoss : ℝ)
    (hscalar :
      Kakeya.realRpowENN delta densityLoss *
          residueData.totalRelativeMassCost analytic ≤
        wz2PaperPureRefinementFraction delta 61 *
          wz2PaperPureRefinementFraction rhoRequested.1 61 *
          Kakeya.realRpowENN delta inputLoss * tail.saturationFloor *
          tail.richHeightFloor * pullback.firstPostBalanced.cellMass) :
    residueData.shading.IsLambdaDense
      (Kakeya.realRpowENN delta densityLoss) := by
  have hsourceDensity :
      Kakeya.realRpowENN delta inputLoss *
          (wz1PaperBodyFamily current.grain.family).mass ≤
        current.grain.shading.mass :=
    current.grain.extremal.dense
  have hrelative := residueData.source_mass_mul_total_gains_le
    analytic hrhoSmall hrhoRequestedSmall
  unfold Kakeya.Streamlined.Shading.IsLambdaDense
  let cost := residueData.totalRelativeMassCost analytic
  have hcostPos : 0 < cost := by
    let regularity : ENNReal := twoScale.first.fourDegreeReceipts.regularity
    have hregularityPos : 0 < regularity := by
      change (0 : ENNReal) <
        (twoScale.first.fourDegreeReceipts.regularity : ENNReal)
      exact_mod_cast twoScale.first.fourDegreeReceipts.regularity_pos
    have hrho : 0 < rho := by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos
    have hrootPos : 0 < ENNReal.ofReal (Real.sqrt rho) := by
      apply ENNReal.ofReal_pos.mpr
      exact Real.sqrt_pos.2 hrho
    have hneighborhoodPos :
        0 < pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
          1 sigma inputLoss delta rho := by
      have hfirstPower :
          0 < Kakeya.realRpowENN delta (-inputLoss) :=
        ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos current.grain.extremal.delta_pos _)
      have hsecondPower :
          0 < Kakeya.realRpowENN (1 / delta) (1 - sigma) :=
        ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos
            (one_div_pos.mpr current.grain.extremal.delta_pos) _)
      have hslabWidth :
          0 < ENNReal.ofReal (4 * Real.sqrt rho * delta) :=
        ENNReal.ofReal_pos.mpr <| by
          exact mul_pos
            (mul_pos (by norm_num) (Real.sqrt_pos.2 hrho))
            current.grain.extremal.delta_pos
      have hregularityBound :
          (twoScale.first.fourDegreeReceipts.regularity : ENNReal) ≤
            Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 :=
        twoScale.first.rich.terminal_regularity_bound
      have hlogPower :
          0 < Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 :=
        hregularityPos.trans_le hregularityBound
      unfold pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
      positivity
    have hgraphPos :
        0 < PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
          rho analytic.budget.extraLoss := by
      unfold PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
      apply ENNReal.ofReal_pos.mpr
      have hscale : 0 < 256 * rho := mul_pos (by norm_num) hrho
      exact mul_pos
        (mul_pos (by norm_num) (Real.rpow_pos_of_pos hscale _))
        (Real.rpow_pos_of_pos hscale _)
    have hheightPos :
        0 < PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho := by
      unfold PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap
      apply ENNReal.ofReal_pos.mpr
      have hscale : 0 < 256 * rho := mul_pos (by norm_num) hrho
      exact div_pos (by norm_num) (Real.sqrt_pos.2 hscale)
    have huniformPos :
        0 < tail.uniformRelativeMassCost analytic.budget.extraLoss := by
      unfold PureWZ2Node05V4RichHeavySlabSaturatedTailFamily.uniformRelativeMassCost
      positivity
    dsimp only [cost, totalRelativeMassCost]
    positivity
  have hcostTop : cost ≠ ⊤ := by
    let regularity : ENNReal := twoScale.first.fourDegreeReceipts.regularity
    let root : ENNReal := ENNReal.ofReal (Real.sqrt rho)
    let neighborhoodCost : ENNReal :=
      pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
        1 sigma inputLoss delta rho
    let graphCellCost : ENNReal :=
      PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost
        rho analytic.budget.extraLoss
    let heightCap : ENNReal :=
      PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho
    have hregularityTop : regularity ≠ ⊤ := by simp [regularity]
    have hrootTop : root ≠ ⊤ := ENNReal.ofReal_ne_top
    have hneighborhoodTop : neighborhoodCost ≠ ⊤ := by
      let firstPower := Kakeya.realRpowENN delta (-inputLoss)
      let secondPower := Kakeya.realRpowENN (1 / delta) (1 - sigma)
      let slabWidth := ENNReal.ofReal (4 * Real.sqrt rho * delta)
      let logLoss := Prop62PaperAudit.V4.logarithmicLoss delta
      have hfirstTop : firstPower ≠ ⊤ := by
        simp [firstPower, Kakeya.realRpowENN]
      have hsecondTop : secondPower ≠ ⊤ := by
        simp [secondPower, Kakeya.realRpowENN]
      have hslabTop : slabWidth ≠ ⊤ := ENNReal.ofReal_ne_top
      have hlogTop : logLoss ≠ ⊤ := by
        simp [logLoss, Prop62PaperAudit.V4.logarithmicLoss]
      have hinner :
          132 * (10 * firstPower) * secondPower ≠ (⊤ : ENNReal) :=
        ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num)
            (ENNReal.mul_ne_top (by norm_num) hfirstTop)) hsecondTop
      have h0 : (2 : ENNReal) * 1 *
          (132 * (10 * firstPower) * secondPower) ≠ ⊤ :=
        ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num) (by norm_num)) hinner
      have h1 : (2 : ENNReal) * 1 *
          (132 * (10 * firstPower) * secondPower) * slabWidth ≠ ⊤ :=
        ENNReal.mul_ne_top h0 hslabTop
      have h2 : (2 : ENNReal) * 1 *
          (132 * (10 * firstPower) * secondPower) * slabWidth * 13 ≠ ⊤ :=
        ENNReal.mul_ne_top h1 (by norm_num)
      have h3 : (2 : ENNReal) * 1 *
          (132 * (10 * firstPower) * secondPower) * slabWidth * 13 * 512 ≠ ⊤ :=
        ENNReal.mul_ne_top h2 (by norm_num)
      dsimp only [neighborhoodCost,
        pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor]
      exact ENNReal.mul_ne_top h3 (ENNReal.pow_ne_top hlogTop)
    have hgraphTop : graphCellCost ≠ ⊤ := by
      simp [graphCellCost,
        PureWZ2SourceHorizontalGoodBlockFamilyData.graphCellCost]
    have hheightTop : heightCap ≠ ⊤ := by
      simp [heightCap,
        PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap]
    have huniformTop :
        tail.uniformRelativeMassCost analytic.budget.extraLoss ≠ ⊤ := by
      change 54 * root * neighborhoodCost * graphCellCost * heightCap ≠ ⊤
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top (by norm_num) hrootTop) hneighborhoodTop)
          hgraphTop) hheightTop
    have hrawTop :
        128 * regularity ^ 3 *
            tail.uniformRelativeMassCost analytic.budget.extraLoss ≠ ⊤ :=
      ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num)
          (ENNReal.pow_ne_top hregularityTop)) huniformTop
    simpa only [cost, totalRelativeMassCost] using hrawTop
  have hscaled : cost *
        (Kakeya.realRpowENN delta densityLoss *
          (wz1PaperBodyFamily current.grain.family).mass) ≤
      cost * residueData.shading.mass := by
    calc
      _ = (Kakeya.realRpowENN delta densityLoss * cost) *
          (wz1PaperBodyFamily current.grain.family).mass := by ring
      _ ≤ (wz2PaperPureRefinementFraction delta 61 *
            wz2PaperPureRefinementFraction rhoRequested.1 61 *
            Kakeya.realRpowENN delta inputLoss * tail.saturationFloor *
            tail.richHeightFloor * pullback.firstPostBalanced.cellMass) *
          (wz1PaperBodyFamily current.grain.family).mass := by gcongr
      _ = wz2PaperPureRefinementFraction delta 61 *
            wz2PaperPureRefinementFraction rhoRequested.1 61 *
            (Kakeya.realRpowENN delta inputLoss *
              (wz1PaperBodyFamily current.grain.family).mass) *
            tail.saturationFloor * tail.richHeightFloor *
            pullback.firstPostBalanced.cellMass := by ring
      _ ≤ wz2PaperPureRefinementFraction delta 61 *
            wz2PaperPureRefinementFraction rhoRequested.1 61 *
            current.grain.shading.mass * tail.saturationFloor *
            tail.richHeightFloor * pullback.firstPostBalanced.cellMass := by gcongr
      _ ≤ cost * residueData.shading.mass := by
        simpa only [cost] using hrelative
  apply (ENNReal.mul_le_mul_iff_right hcostPos.ne' hcostTop).mp
  simpa only [mul_comm] using hscaled

/-- Close the ordinary one-scale output on the exact current source after the
single all-heavy-slab scalar budget has been discharged. -/
theorem toOneScaleOfReentryTraceBudgets
    {structuralBudget : ℝ}
    (analytic : PureWZ2SourceHorizontalAnalyticThreshold projection.theoremEta)
    (hrhoSmall : rho ≤ analytic.rho0)
    (hrhoRequestedSmall : rhoRequested.1 ≤ 1 / 12)
    (floorSchedule : PureWZ2ReentryTraceFloorSchedule
      sigma finalLoss structuralBudget)
    (hinputDensity : inputLoss ≤ floorSchedule.densityLoss)
    (htraceSource :
      current.ordinaryLoss ≤ floorSchedule.traceSourceCeiling)
    (hdeltaSchedule : delta ≤ floorSchedule.delta₀)
    (hscalar :
      Kakeya.realRpowENN delta floorSchedule.densityLoss *
          residueData.totalRelativeMassCost analytic ≤
        wz2PaperPureRefinementFraction delta 61 *
          wz2PaperPureRefinementFraction rhoRequested.1 61 *
          Kakeya.realRpowENN delta inputLoss * tail.saturationFloor *
          tail.richHeightFloor * pullback.firstPostBalanced.cellMass) :
    Nonempty (PureWZ2LocallyLinearOneScaleData current.grain finalLoss
      (pureWZ2SourceHorizontalFinalScale rho)) := by
  have hdense := residueData.dense_of_total_budget analytic hrhoSmall
    hrhoRequestedSmall floorSchedule.densityLoss hscalar
  rcases residueData.geometry with ⟨geometry⟩
  exact pureWZ2_literalCurrentSourceOneScale_of_reentryTrace
    residueData.shading residueData.subshading residueData.cubical
    floorSchedule hinputDensity htraceSource hdeltaSchedule hdense
    current.reentry geometry

end PureWZ2Node05V4RichSaturatedResidueData

end Kakeya.Assouad

end
