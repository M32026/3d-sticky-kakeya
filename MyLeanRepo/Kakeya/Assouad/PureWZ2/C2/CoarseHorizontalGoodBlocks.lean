import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseHorizontalRichPipeline
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalGoodBlocks

/-!
# Popular genuine-coarse blocks for Lemma 24

The local Lemma-23 graph consumes the exact volume of one coarse carrier
block, multiplied by the second-sticky cell-volume floor.  Consequently the
popularity test below is weighted by actual block volume.  No first-sticky
cell mass, unweighted block count, or original-source carrier is inserted.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The block-independent left side of the local ready-graph volume budget. -/
def pureWZ2CoarseHorizontalBlockThreshold
    (rho sigma middleLoss volumeLoss : ℝ) : ENNReal :=
  Kakeya.realRpowENN (256 * rho) (1 + sigma / 2 + volumeLoss) *
    pureWZ2HorizontalFixedLineVolumeCost rho sigma middleLoss

/-- The second-sticky power supply carried by every unit of block volume. -/
def pureWZ2CoarseHorizontalBlockSupplyFactor
    (rho sigma stickyLoss : ℝ) : ENNReal :=
  Kakeya.realRpowENN rho
    (3 / 2 + sigma / 2 + 3 * stickyLoss / 2)

theorem pureWZ2HorizontalFixedLineVolumeCost_ne_top
    (rho sigma middleLoss : ℝ) :
    pureWZ2HorizontalFixedLineVolumeCost rho sigma middleLoss ≠ ⊤ := by
  unfold pureWZ2HorizontalFixedLineVolumeCost
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.ofReal_ne_top
        · exact ENNReal.mul_ne_top
            (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
            ENNReal.ofReal_ne_top
      · exact ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num)
            (ENNReal.mul_ne_top (by norm_num)
              (by simp [Kakeya.realRpowENN])))
          (by simp [Kakeya.realRpowENN])
    · exact ENNReal.natCast_ne_top _
  · norm_num

theorem pureWZ2CoarseHorizontalBlockThreshold_ne_top
    (rho sigma middleLoss volumeLoss : ℝ) :
    pureWZ2CoarseHorizontalBlockThreshold
      rho sigma middleLoss volumeLoss ≠ ⊤ := by
  exact ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN])
    (pureWZ2HorizontalFixedLineVolumeCost_ne_top _ _ _)

/-- Positive coarse blocks whose exact local supply reaches the graph budget. -/
def pureWZ2GoodCoarseCarrierBlocks
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale)
    (volumeLoss : ℝ) : Finset ℤ :=
  (pureWZ2PositiveCoarseCarrierBlocks prepared).filter fun block =>
    pureWZ2CoarseHorizontalBlockThreshold
        rho sigma middleLoss volumeLoss ≤
      MeasureTheory.volume
          (pureWZ2CoarseCarrierBlockShading prepared block).union *
        pureWZ2CoarseHorizontalBlockSupplyFactor rho sigma stickyLoss

/-- Membership in the good set is exactly the per-block ready-graph budget. -/
theorem pureWZ2GoodCoarseCarrierBlock_budget
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {block : ℤ}
    (hblock : block ∈
      pureWZ2GoodCoarseCarrierBlocks prepared volumeLoss) :
    Kakeya.realRpowENN (256 * rho)
          (1 + sigma / 2 + volumeLoss) *
        pureWZ2HorizontalFixedLineVolumeCost rho sigma middleLoss ≤
      MeasureTheory.volume
          (pureWZ2CoarseCarrierBlockShading prepared block).union *
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) := by
  exact (Finset.mem_filter.mp hblock).2

/-- Every good block has canonical block-window data with exact local supply. -/
theorem PureWZ2Lemma23PreparedCoarse.windowDataOfGoodBlock
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale)
    {block : ℤ}
    (hblock : block ∈
      pureWZ2GoodCoarseCarrierBlocks prepared volumeLoss) :
    Nonempty (PureWZ2CoarseCarrierBlockWindowData prepared block) := by
  have hpositive : 0 < MeasureTheory.volume
      (pureWZ2CoarseCarrierBlockShading prepared block).union :=
    pureWZ2PositiveCoarseCarrierBlock_volume_pos
      (Finset.mem_filter.mp hblock).1
  exact prepared.windowDataOfBlock block hpositive

/--
The good blocks retain half of the genuine coarse volume supply.  The only
outer premise is the smallness comparison between the total bad-block budget
and the actual decomposed carrier volume.
-/
theorem pureWZ2GoodCoarseCarrierBlocks_weightedSupply_half
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale)
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
            rho sigma stickyLoss ≤
      2 * ∑ block ∈ pureWZ2GoodCoarseCarrierBlocks prepared volumeLoss,
        MeasureTheory.volume
            (pureWZ2CoarseCarrierBlockShading prepared block).union *
          pureWZ2CoarseHorizontalBlockSupplyFactor
            rho sigma stickyLoss := by
  have hraw := finset_good_weighted_supply_retains_half
    (pureWZ2PositiveCoarseCarrierBlocks prepared)
    (fun block => MeasureTheory.volume
      (pureWZ2CoarseCarrierBlockShading prepared block).union)
    (pureWZ2CoarseHorizontalBlockSupplyFactor rho sigma stickyLoss)
    (pureWZ2CoarseHorizontalBlockThreshold
      rho sigma middleLoss volumeLoss)
    (pureWZ2CoarseHorizontalBlockThreshold_ne_top _ _ _ _)
  have hsupply :
      (∑ block ∈ pureWZ2PositiveCoarseCarrierBlocks prepared,
          MeasureTheory.volume
              (pureWZ2CoarseCarrierBlockShading prepared block).union *
            pureWZ2CoarseHorizontalBlockSupplyFactor
              rho sigma stickyLoss) =
        MeasureTheory.volume prepared.shadow.union *
          pureWZ2CoarseHorizontalBlockSupplyFactor
            rho sigma stickyLoss := by
    rw [← Finset.sum_mul, ←
      pureWZ2PositiveCoarseCarrierBlocks_volume_eq_sum prepared]
  rw [hsupply] at hraw
  simpa [pureWZ2GoodCoarseCarrierBlocks] using
    hraw (by simpa [mul_assoc] using hsmall)

/-- Positive retained supply forces at least one good genuine-coarse block. -/
theorem pureWZ2GoodCoarseCarrierBlocks_nonempty
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (prepared : PureWZ2Lemma23PreparedCoarse twoScale)
    (hsmall :
      2 *
          ((pureWZ2PositiveCoarseCarrierBlocks prepared).card : ENNReal) *
          pureWZ2CoarseHorizontalBlockThreshold
            rho sigma middleLoss volumeLoss ≤
        MeasureTheory.volume prepared.shadow.union *
          pureWZ2CoarseHorizontalBlockSupplyFactor
            rho sigma stickyLoss) :
    (pureWZ2GoodCoarseCarrierBlocks prepared volumeLoss).Nonempty := by
  have hretained :=
    pureWZ2GoodCoarseCarrierBlocks_weightedSupply_half prepared hsmall
  have hvolumePos : 0 < MeasureTheory.volume prepared.shadow.union := by
    rw [prepared.shadow_union]
    have hrho : 0 < twoScale.rhoRequested.1 :=
      twoScale.coarseGrains.extremal.delta_pos
    have hpower : 0 < Kakeya.realRpowENN twoScale.rhoRequested.1
        (sigma + stickyLoss) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hrho _)
    exact hpower.trans_le twoScale.fine.refined_volume_lower
  have hsupplyPos : 0 <
      pureWZ2CoarseHorizontalBlockSupplyFactor
        rho sigma stickyLoss := by
    unfold pureWZ2CoarseHorizontalBlockSupplyFactor
    apply ENNReal.ofReal_pos.mpr
    have hrho : 0 < rho := by
      rw [← twoScale.rhoRequested_eq]
      exact twoScale.coarseGrains.extremal.delta_pos
    exact Real.rpow_pos_of_pos hrho _
  have hleftPos : 0 < MeasureTheory.volume prepared.shadow.union *
      pureWZ2CoarseHorizontalBlockSupplyFactor
        rho sigma stickyLoss :=
    ENNReal.mul_pos hvolumePos.ne' hsupplyPos.ne'
  by_contra hempty
  have hgoodEmpty : pureWZ2GoodCoarseCarrierBlocks prepared volumeLoss = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  rw [hgoodEmpty] at hretained
  simp only [Finset.sum_empty, mul_zero] at hretained
  exact (not_le_of_gt hleftPos) hretained

end Kakeya.Assouad
