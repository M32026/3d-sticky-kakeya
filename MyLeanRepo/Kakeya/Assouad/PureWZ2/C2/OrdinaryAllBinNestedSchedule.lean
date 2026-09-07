import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryAllBinNestedMultiWindowCore

/-!
# Uniform numerical schedule for the nested ordinary all-bin producer

This module packages the three finite selection costs used by the concrete
nested regional producer.  It also specializes the pointwise nested graph
budget to the source-independent nested-bin cost.  The final schedule receipt
deliberately retains the first-cover `cellMass`: that factor is incidence data
from the first balanced cover, not the volume of a physical `rho` cube.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set
open PureWZ2OrdinaryAllBinNestedRegionalData.SelectedBlockResidueData

namespace PureWZ2OrdinaryAllBinNestedRegionalData
namespace SelectedBlockResidueData

variable
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta finalLoss
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {companions : PureWZ2OrdinaryAllBinOuterPopularCompanionData carriers}
    {regional : PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions}

/-- One receipt carrying all source-independent finite-cardinality bounds
used by the two maximum selections in the nested regional producer. -/
structure UniformBinCostReceipt where
  parent_bound : ∀ block : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    ((regional.weightClass block).bins : ENNReal) ≤ parentBinCost rho
  source_bound : ∀ block : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    ((regional.sourceBins block).line.globalBins.card : ENNReal) ≤
      sourceBinCost delta rho sigma inputLoss
  nested_bound : ∀ block : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    ∀ bin : {bin // bin ∈ (regional.sourceBins block).line.globalBins},
      (((regional.family block).good bin).selected.card : ENNReal) ≤
        nestedBinCost rho sigma middleLoss

/-- The canonical bin-cost receipt is available for every concrete nested
regional output; it contains no source-family cardinality. -/
theorem uniformBinCostReceipt : UniformBinCostReceipt (regional := regional) where
  parent_bound block := parentBinCost_bound (regional := regional) block
  source_bound block := sourceBinCost_bound (regional := regional) block
  nested_bound block bin :=
    nestedBinCost_bound (regional := regional) block bin

end SelectedBlockResidueData
end PureWZ2OrdinaryAllBinNestedRegionalData

namespace PureWZ2OrdinaryAllBinNestedRegionalPreparationData

variable
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {companions : PureWZ2OrdinaryAllBinOuterPopularCompanionData carriers}

/-- The synchronized source-bin carrier contains enough literal side-`rho`
volume to pay half a physical cube.  This is the geometric input behind the
uniform pointwise nested graph budget. -/
theorem cube_volume_le_two_mul_sync_volume
    (preparedRegional :
      PureWZ2OrdinaryAllBinNestedRegionalPreparationData carriers companions)
    (block : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe})
    (bin : {bin //
      bin ∈ (preparedRegional.sourceBins block).line.globalBins}) :
    volume (wz1PaperGridCube rho (0, 0, 0)) ≤
      2 * volume
        (preparedRegional.sync block bin).parentRestriction.cellRestriction.shading.union := by
  exact PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData.cube_volume_le_two_mul_volume
    (preparedRegional.sync block bin)

/-- Specialize `nested_graph_budget_of_cost` to the canonical uniform nested
bin count.  The sole scalar premise is independent of the source family and
of the selected block and source bin. -/
theorem nested_graph_budget
    (preparedRegional :
      PureWZ2OrdinaryAllBinNestedRegionalPreparationData carriers companions)
    {volumeLoss : ℝ}
    (hbudget :
      4 *
          (nestedBinCost rho sigma middleLoss *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss)) *
          pureWZ2BalancedSafeNestedCoarseVolumeCost rho ≤
        volume (wz1PaperGridCube rho (0, 0, 0)))
    (block : {block //
      block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe})
    (bin : {bin //
      bin ∈ (preparedRegional.sourceBins block).line.globalBins}) :
    2 * ((((preparedRegional.nested block bin).fixedLine.line.globalBins.card :
            ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss))) *
          pureWZ2BalancedSafeNestedCoarseVolumeCost rho ≤
      volume
        (preparedRegional.sync block bin).parentRestriction.cellRestriction.shading.union := by
  apply PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData.nested_graph_budget_of_cost
    (preparedRegional.sync block bin) (preparedRegional.nested block bin)
    (nestedBinCost rho sigma middleLoss)
  · simpa [nestedBinCost, twoScale.rhoRequested_eq] using
        (preparedRegional.nested block bin).fixedLine.line.global_bin_count
  · exact hbudget

end PureWZ2OrdinaryAllBinNestedRegionalPreparationData

/-- Runtime numerical receipt for the concrete nested producer.  The graph
budget is source-independent.  The density budget retains the exact
first-cover `cellMass`, so downstream cancellation uses the same balanced
cover witness instead of replacing incidence mass by cube volume. -/
structure PureWZ2OrdinaryAllBinNestedScheduleReceipt
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss : ℝ}
    {logExponent : ℕ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent)
    (volumeLoss outerLoss extraLoss structuralLoss : ℝ) where
  nested_graph_budget :
    4 *
        (nestedBinCost rho sigma middleLoss *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) *
        pureWZ2BalancedSafeNestedCoarseVolumeCost rho ≤
      volume (wz1PaperGridCube rho (0, 0, 0))
  final_power :
    2 *
        totalCost delta rho sigma inputLoss middleLoss outerLoss extraLoss *
        Kakeya.realRpowENN delta structuralLoss ≤
      Kakeya.realRpowENN rho (stickyLoss + twoScale.coarseLoss) *
        wz2PaperPureRefinementFraction delta logExponent *
        Kakeya.realRpowENN delta inputLoss *
        twoScale.coarse.balanced.cellMass *
        pureWZ2SourceHorizontalRichFloor rho finalLoss

end Kakeya.Assouad

end
