import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryAllBinNestedRegionalProducer

/-!
# Nested ordinary regional aggregate mass

Sum the synchronized regional estimate while retaining the exact first-cover
cell mass.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

namespace PureWZ2OrdinaryAllBinNestedRegionalData

/-- Sum the synchronized nested regional estimate over the source-regularized
blocks.  The output is the exact aggregate interface needed before the final
mod-64 selection.  In particular the first-cover balanced `cellMass` remains
on the left and must be paid by the scalar schedule. -/
theorem aggregate_heightLift_mass_bound
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta finalLoss
      theoremEta volumeLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {companions : PureWZ2OrdinaryAllBinOuterPopularCompanionData carriers}
    (regional : PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions)
    (outerCost parentCost : ENNReal)
    (houterCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      (2 * (carriers.carrier block.1).outerPopular.popular.bins : ENNReal) ≤
        outerCost)
    (hparentCost : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((regional.weightClass block).bins : ENNReal) ≤ parentCost)
    (hextraPower : ∀ block :
        {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ∀ bin : {bin // bin ∈ (regional.sourceBins block).line.globalBins},
      ∀ nestedBin : {nestedBin //
          nestedBin ∈ ((regional.family block).good bin).selected},
        ((((regional.family block).rich bin).pipeline nestedBin).preparedGraph.graph.residue.extraCost :
            ℝ) ≤
          Real.rpow
            (((regional.family block).nested bin).preparation
              nestedBin.1).prep.graphScale (-extraLoss)) :
    volume prepared.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          twoScale.coarse.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
      64 * outerCost * parentCost *
        pureWZ2BalancedSafeSourceBinVolumeCost rho delta *
        pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss *
        ∑ block :
            {block // block ∈
              pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
          ∑ bin : {bin //
              bin ∈ (regional.sourceBins block).line.globalBins},
            ∑ nestedBin : {nestedBin //
                nestedBin ∈ ((regional.family block).good bin).selected},
              (((regional.family block).rich bin).rich nestedBin).heightLift.shading.mass := by
  let cellMass : ENNReal := twoScale.coarse.balanced.cellMass
  let floor : ENNReal := pureWZ2SourceHorizontalRichFloor rho finalLoss
  let sourceCost : ENNReal :=
    pureWZ2BalancedSafeSourceBinVolumeCost rho delta
  let nestedCost : ENNReal :=
    pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho
  let heightCost : ENNReal :=
    PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
      rho extraLoss
  let blockMass :
      {block // block ∈
        pureWZ2OrdinaryPaperOrderRegularizedBlocks safe} → ENNReal :=
    fun block =>
      ∑ bin : {bin //
          bin ∈ (regional.sourceBins block).line.globalBins},
        ∑ nestedBin : {nestedBin //
            nestedBin ∈ ((regional.family block).good bin).selected},
          (((regional.family block).rich bin).rich
            nestedBin).heightLift.shading.mass
  let totalMass : ENNReal := ∑ block, blockMass block
  have hbase := companions.companions.aggregate_regularized_source_mass_lower
  have hlocal :
      (∑ block :
          {block // block ∈
            pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
        (companions.companions.companion block.1).sourcePullback.shading.mass) *
          cellMass * floor ≤
      16 * outerCost * parentCost * sourceCost * nestedCost * heightCost *
        totalMass := by
    calc
      _ = ∑ block :
          {block // block ∈
            pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
        ((companions.companions.companion block.1).sourcePullback.shading.mass *
          cellMass * floor) := by
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ ∑ block :
          {block // block ∈
            pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
        (16 * outerCost * parentCost * sourceCost * nestedCost * heightCost *
          blockMass block) := by
        exact Finset.sum_le_sum fun block _ => by
          calc
            _ ≤ 16 *
                (2 * (carriers.carrier block.1).outerPopular.popular.bins :
                  ENNReal) *
                ((regional.weightClass block).bins : ENNReal) *
                sourceCost * nestedCost * heightCost *
                blockMass block := by
              simpa [cellMass, floor, sourceCost, nestedCost, heightCost,
                blockMass] using
                PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseNestedBlockRichFamilyData.block_source_mass_bound
                  (regional.family block) (hextraPower block)
            _ ≤ 16 * outerCost * parentCost * sourceCost * nestedCost *
                heightCost * blockMass block := by
              gcongr
              · exact houterCost block
              · exact hparentCost block
      _ = 16 * outerCost * parentCost * sourceCost * nestedCost * heightCost *
          totalMass := by
        dsimp only [totalMass]
        rw [Finset.mul_sum]
  calc
    volume prepared.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) * cellMass * floor ≤
        (4 * ∑ block :
          {block // block ∈
            pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
          (companions.companions.companion block.1).sourcePullback.shading.mass) *
            cellMass * floor := by
      exact mul_le_mul_right' (mul_le_mul_right' (by
        simpa using hbase) cellMass) floor
    _ = 4 *
        ((∑ block :
          {block // block ∈
            pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
          (companions.companions.companion block.1).sourcePullback.shading.mass) *
            cellMass * floor) := by ring
    _ ≤ 4 * (16 * outerCost * parentCost * sourceCost * nestedCost *
        heightCost * totalMass) := by
      exact mul_le_mul_left' hlocal 4
    _ = _ := by
      simp only [sourceCost, nestedCost, heightCost, totalMass, blockMass]
      ring

end PureWZ2OrdinaryAllBinNestedRegionalData

end Kakeya.Assouad

end
