import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinStandardSlabGraphFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinStandardSlabHeavySelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinPreBinFamily

/-!
# Common-bin graph family on source-heavy standard slabs

This is the production index set for the common-bin graph argument.  Light
standard slabs have already been removed with half-mass retention, so one
uniform natural cell count `K` can be used on every remaining block.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

abbrev PureWZ2SourceHeavyStandardSqrtSlabIndex
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale) :=
  {heightIndex // heightIndex ∈
    pureWZ2SourceHeavyStandardSqrtSlabs pullback}

structure PureWZ2SourceHeavyStandardSlabCommonBinGraphFamilyData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)
    (threshold :
      PureWZ2SourceHeavyStandardSqrtSlabIndex pullback → ENNReal)
    (K : ℕ) where
  preBinFamily : PureWZ2SourceHeavyPreBinRhoHeightFamilyData pullback
  blockData : ∀ heightIndex,
    PureWZ2StandardSlabCommonBinGraphBlockData
      pullback heightIndex.1 (threshold heightIndex) K
  block_preBin_eq : ∀ heightIndex,
    (blockData heightIndex).preBin = preBinFamily.blockData heightIndex

theorem PureWZ2TwoScaleCellPullbackData.sourceHeavyStandardSlabCommonBinGraphFamily
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)
    (preBinFamily :
      PureWZ2SourceHeavyPreBinRhoHeightFamilyData pullback)
    (B₀ : ENNReal)
    (threshold :
      PureWZ2SourceHeavyStandardSqrtSlabIndex pullback → ENNReal)
    (K : ℕ)
    (hB₀ :
      264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget : ∀ heightIndex,
      2 * B₀ * threshold heightIndex ≤
        pureWZ2SourceCommonBinPopularThreshold
          (preBinFamily.blockData heightIndex).sourceSet
          (Real.sqrt rho))
    (hK : ∀ heightIndex,
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤
        threshold heightIndex) :
    Nonempty
      {graph : PureWZ2SourceHeavyStandardSlabCommonBinGraphFamilyData
          pullback threshold K //
        graph.preBinFamily = preBinFamily} := by
  have hblock : ∀ heightIndex,
      Nonempty
        {block : PureWZ2StandardSlabCommonBinGraphBlockData
            pullback heightIndex.1 (threshold heightIndex) K //
          block.preBin = preBinFamily.blockData heightIndex} := by
    intro heightIndex
    rcases (preBinFamily.blockData heightIndex)
        |>.exists_integratedRichCommonBin_graphEnvelope
          B₀ (threshold heightIndex) K hB₀
          (hthresholdBudget heightIndex) (hK heightIndex)
      with
      ⟨referenceHeight, hreference, bin, hbin, hreceipts⟩
    exact ⟨⟨{
      preBin := preBinFamily.blockData heightIndex
      referenceHeight := referenceHeight
      referenceHeight_mem := hreference
      bin := bin
      bin_mem := hbin
      graph_lower := hreceipts.1
      source_average := hreceipts.2
    }, rfl⟩⟩
  exact ⟨⟨{
    preBinFamily := preBinFamily
    blockData := fun heightIndex => (Classical.choice (hblock heightIndex)).1
    block_preBin_eq := fun heightIndex =>
      (Classical.choice (hblock heightIndex)).2
  }, rfl⟩⟩

namespace PureWZ2SourceHeavyStandardSlabCommonBinGraphFamilyData

variable
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {threshold :
      PureWZ2SourceHeavyStandardSqrtSlabIndex pullback → ENNReal}
    {K : ℕ}
    (data : PureWZ2SourceHeavyStandardSlabCommonBinGraphFamilyData
      pullback threshold K)

def graphEnvelope
    (heightIndex : PureWZ2SourceHeavyStandardSqrtSlabIndex pullback) :
    Set Point3 :=
  (data.blockData heightIndex).preBin.fixedBinWholeCellEnvelope
    (data.blockData heightIndex).referenceHeight
    (data.blockData heightIndex).bin

def graphSupply
    (heightIndex : PureWZ2SourceHeavyStandardSqrtSlabIndex pullback) :
    ENNReal :=
  volume (data.graphEnvelope heightIndex)

def heightCost
    (heightIndex : PureWZ2SourceHeavyStandardSqrtSlabIndex pullback) :
    ENNReal :=
  (data.blockData heightIndex).preBin.logarithmicCost

def totalGraphSupply : ENNReal :=
  ∑ heightIndex, data.graphSupply heightIndex

def graphThreshold
    (_data : PureWZ2SourceHeavyStandardSlabCommonBinGraphFamilyData
      pullback threshold K)
    (volumeLoss : ℝ) : ENNReal :=
  Kakeya.realRpowENN (256 * rho) (1 + sigma / 2 + volumeLoss)

def GraphBudget (volumeLoss : ℝ) : Prop :=
  2 *
      ((pureWZ2SourceHeavyStandardSqrtSlabs pullback).card : ENNReal) *
      data.graphThreshold volumeLoss ≤
    data.totalGraphSupply

theorem graph_lower
    (heightIndex : PureWZ2SourceHeavyStandardSqrtSlabIndex pullback) :
    (K : ENNReal) * twoScale.fine.balanced.cellMass ≤
      20 * data.heightCost heightIndex * data.graphSupply heightIndex := by
  simpa [heightCost, graphSupply, graphEnvelope] using
    (data.blockData heightIndex).graph_lower

theorem graphBudget_of_commonBin
    (volumeLoss : ℝ)
    (hscalar : ∀ heightIndex,
      40 * data.heightCost heightIndex * data.graphThreshold volumeLoss ≤
        (K : ENNReal) * twoScale.fine.balanced.cellMass) :
    data.GraphBudget volumeLoss := by
  have hblock : ∀ heightIndex,
      2 * data.graphThreshold volumeLoss ≤
        data.graphSupply heightIndex := by
    intro heightIndex
    have hheightCostPos : 0 < data.heightCost heightIndex := by
      unfold heightCost
      exact_mod_cast (show 0 <
        (data.blockData heightIndex).preBin.logarithmicCost by
          rw [(data.blockData heightIndex).preBin.logarithmicCost_eq]
          omega)
    have hheightCostTop : data.heightCost heightIndex ≠ ⊤ := by
      unfold heightCost
      exact ENNReal.natCast_ne_top _
    let cancel : ENNReal := 20 * data.heightCost heightIndex
    have hcancelPos : 0 < cancel :=
      ENNReal.mul_pos (by norm_num) hheightCostPos.ne'
    have hcancelTop : cancel ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) hheightCostTop
    apply
      (ENNReal.mul_le_mul_iff_right
        hcancelPos.ne' hcancelTop).mp
    calc
      cancel * (2 * data.graphThreshold volumeLoss) =
          40 * data.heightCost heightIndex *
            data.graphThreshold volumeLoss := by
        unfold cancel
        ring
      _ ≤ (K : ENNReal) * twoScale.fine.balanced.cellMass :=
        hscalar heightIndex
      _ ≤ 20 * data.heightCost heightIndex *
          data.graphSupply heightIndex :=
        data.graph_lower heightIndex
      _ = cancel * data.graphSupply heightIndex := by
        unfold cancel
        rfl
  unfold GraphBudget totalGraphSupply
  calc
    2 *
          ((pureWZ2SourceHeavyStandardSqrtSlabs pullback).card : ENNReal) *
          data.graphThreshold volumeLoss =
      ∑ heightIndex :
          PureWZ2SourceHeavyStandardSqrtSlabIndex pullback,
        2 * data.graphThreshold volumeLoss := by
          simp [Finset.sum_const]
          ring
    _ ≤ ∑ heightIndex, data.graphSupply heightIndex :=
      Finset.sum_le_sum fun heightIndex _ => hblock heightIndex

end PureWZ2SourceHeavyStandardSlabCommonBinGraphFamilyData

end Kakeya.Assouad

end
