import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinPreBinIntegrated

/-!
# Aggregate graph supply on standard common-bin slabs

The block index here is the literal occupied unshifted standard slab.  Each
block stores its own popular reference height and integrated fixed bin, while
the lower cell count `K` is uniform across the family.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The common-bin choices and whole-cell lower bound on one occupied
standard slab. -/
structure PureWZ2StandardSlabCommonBinGraphBlockData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)
    (heightIndex : {heightIndex // heightIndex ∈
      pullback.standardSqrtSlabIndices})
    (threshold : ENNReal)
    (K : ℕ) where
  preBin :
    PureWZ2StandardSlabPreBinRhoHeightRegularizedData pullback heightIndex
  referenceHeight : ℝ
  referenceHeight_mem :
    referenceHeight ∈ preBin.popularHeights
  bin : ℤ
  bin_mem :
    bin ∈ preBin.distinctRichCommonBinLabels referenceHeight threshold
  graph_lower :
    (K : ENNReal) * twoScale.fine.balanced.cellMass ≤
      20 * (preBin.logarithmicCost : ENNReal) *
        volume (preBin.fixedBinWholeCellEnvelope referenceHeight bin)
  source_average :
    volume preBin.sourceSet ≤
      4 *
        ((preBin.distinctRichCommonBinLabels
          referenceHeight threshold).card : ENNReal) *
        preBin.integratedBinMass referenceHeight bin

/-- The complete standard-slab graph family. -/
structure PureWZ2StandardSlabCommonBinGraphFamilyData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)
    (threshold : {heightIndex // heightIndex ∈
      pullback.standardSqrtSlabIndices} → ENNReal)
    (K : ℕ) where
  blockData : ∀ heightIndex,
    PureWZ2StandardSlabCommonBinGraphBlockData pullback heightIndex
      (threshold heightIndex) K

/-- Construct the whole standard-slab family from the common-bin scalar
budgets.  No geometric family or graph output is assumed. -/
theorem PureWZ2TwoScaleCellPullbackData.standardSlabCommonBinGraphFamily
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)
    (preBin : ∀ heightIndex : {heightIndex // heightIndex ∈
      pullback.standardSqrtSlabIndices},
      PureWZ2StandardSlabPreBinRhoHeightRegularizedData
        pullback heightIndex)
    (B₀ : ENNReal)
    (threshold : {heightIndex // heightIndex ∈
      pullback.standardSqrtSlabIndices} → ENNReal)
    (K : ℕ)
    (hB₀ :
      264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget : ∀ heightIndex,
      2 * B₀ * threshold heightIndex ≤
        pureWZ2SourceCommonBinPopularThreshold
          (preBin heightIndex).sourceSet
          (Real.sqrt rho))
    (hK : ∀ heightIndex,
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤
        threshold heightIndex) :
    Nonempty
      (PureWZ2StandardSlabCommonBinGraphFamilyData
        pullback threshold K) := by
  have hblock : ∀ heightIndex,
      Nonempty
        (PureWZ2StandardSlabCommonBinGraphBlockData pullback heightIndex
          (threshold heightIndex) K) := by
    intro heightIndex
    rcases (preBin heightIndex).exists_integratedRichCommonBin_graphEnvelope
          B₀ (threshold heightIndex) K hB₀
          (hthresholdBudget heightIndex) (hK heightIndex)
      with
      ⟨referenceHeight, hreference, bin, hbin, hreceipts⟩
    exact ⟨{
      preBin := preBin heightIndex
      referenceHeight := referenceHeight
      referenceHeight_mem := hreference
      bin := bin
      bin_mem := hbin
      graph_lower := hreceipts.1
      source_average := hreceipts.2
    }⟩
  exact ⟨{
    blockData := fun heightIndex => Classical.choice (hblock heightIndex)
  }⟩

namespace PureWZ2StandardSlabCommonBinGraphFamilyData

variable
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {threshold : {heightIndex // heightIndex ∈
      pullback.standardSqrtSlabIndices} → ENNReal}
    {K : ℕ}
    (data : PureWZ2StandardSlabCommonBinGraphFamilyData
      pullback threshold K)

def graphEnvelope
    (heightIndex : {heightIndex // heightIndex ∈
      pullback.standardSqrtSlabIndices}) : Set Point3 :=
  (data.blockData heightIndex).preBin.fixedBinWholeCellEnvelope
    (data.blockData heightIndex).referenceHeight
    (data.blockData heightIndex).bin

def graphSupply
    (heightIndex : {heightIndex // heightIndex ∈
      pullback.standardSqrtSlabIndices}) : ENNReal :=
  volume (data.graphEnvelope heightIndex)

def heightCost
    (heightIndex : {heightIndex // heightIndex ∈
      pullback.standardSqrtSlabIndices}) : ENNReal :=
  (data.blockData heightIndex).preBin.logarithmicCost

def totalGraphSupply : ENNReal :=
  ∑ heightIndex, data.graphSupply heightIndex

def graphThreshold
    (_data : PureWZ2StandardSlabCommonBinGraphFamilyData
      pullback threshold K)
    (volumeLoss : ℝ) : ENNReal :=
  Kakeya.realRpowENN (256 * rho) (1 + sigma / 2 + volumeLoss)

def GraphBudget (volumeLoss : ℝ) : Prop :=
  2 * ((pullback.standardSqrtSlabIndices.card : ENNReal) *
    data.graphThreshold volumeLoss) ≤ data.totalGraphSupply

theorem graph_lower
    (heightIndex : {heightIndex // heightIndex ∈
      pullback.standardSqrtSlabIndices}) :
    (K : ENNReal) * twoScale.fine.balanced.cellMass ≤
      20 * data.heightCost heightIndex * data.graphSupply heightIndex := by
  simpa [heightCost, graphSupply, graphEnvelope] using
    (data.blockData heightIndex).graph_lower

/-- The exact source slab is controlled by the same selected fixed-bin
whole-cell envelope.  The only loss is the geometric count of labels in the
fixed `u_*` grid; no joint source/envelope density is assumed. -/
theorem source_volume_le_labelCost_mul_graphSupply
    (heightIndex : {heightIndex // heightIndex ∈
      pullback.standardSqrtSlabIndices}) :
    volume (data.blockData heightIndex).preBin.sourceSet ≤
      (48 * ENNReal.ofReal (1 / Real.sqrt rho)) *
        data.graphSupply heightIndex := by
  let block := data.blockData heightIndex
  let binMass := block.preBin.integratedBinMass
    block.referenceHeight block.bin
  have hcard := block.preBin.distinctRichCommonBinLabels_card_le
    block.referenceHeight (threshold heightIndex)
  have hbinRegion : binMass = volume
      (block.preBin.fixedBinHeightRegion
        block.referenceHeight block.bin) := by
    simpa [binMass] using
      (block.preBin.fixedBinHeightRegion_volume
        block.referenceHeight block.bin).symm
  have hregionEnvelope : binMass ≤ data.graphSupply heightIndex := by
    rw [hbinRegion]
    apply measure_mono
    simpa [graphSupply, graphEnvelope]
      using block.preBin.fixedBinHeightRegion_subset_envelope
        block.referenceHeight block.bin
  calc
    volume block.preBin.sourceSet ≤
        4 *
          ((block.preBin.distinctRichCommonBinLabels block.referenceHeight
            (threshold heightIndex)).card : ENNReal) * binMass := by
      simpa [block, binMass] using block.source_average
    _ ≤ 4 * ENNReal.ofReal (12 / Real.sqrt rho) * binMass := by gcongr
    _ ≤ 4 * ENNReal.ofReal (12 / Real.sqrt rho) *
          data.graphSupply heightIndex := by gcongr
    _ = (48 * ENNReal.ofReal (1 / Real.sqrt rho)) *
          data.graphSupply heightIndex := by
      rw [show (12 : ℝ) / Real.sqrt rho =
        12 * (1 / Real.sqrt rho) by ring,
        ENNReal.ofReal_mul (by norm_num)]
      norm_num
      ring

/-- A family-free comparison between the analytic graph threshold and the
uniform common-bin cell count gives the aggregate graph budget directly. -/
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
    2 * ((pullback.standardSqrtSlabIndices.card : ENNReal) *
        data.graphThreshold volumeLoss) =
      ∑ heightIndex :
          {heightIndex // heightIndex ∈
            pullback.standardSqrtSlabIndices},
        2 * data.graphThreshold volumeLoss := by
          simp [Finset.sum_const]
          ring
    _ ≤ ∑ heightIndex, data.graphSupply heightIndex :=
      Finset.sum_le_sum fun heightIndex _ => hblock heightIndex

end PureWZ2StandardSlabCommonBinGraphFamilyData

end Kakeya.Assouad

end
