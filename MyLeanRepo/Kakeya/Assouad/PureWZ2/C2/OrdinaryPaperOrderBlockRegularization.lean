import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderAllBlockFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.BalancedSafeCoarseCompanion
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalGoodBlocks

/-!
# Source-relative block regularization for the ordinary paper order

The local Lemma-23 graph needs an absolute volume floor, but that floor is
required only on the `sqrt rho` slabs which carry a substantial part of the
source.  We therefore regularize the balanced safe blocks by their actual
source-window volume before using the fixed-line and graph constructions.

The threshold below is one eighth of the canonical average source volume.
The factor eight pays for the safe-phase factor two and for the elementary
upper bound on the number of `sqrt rho` blocks.  Consequently the selected
blocks retain a fixed fraction of the original prepared carrier.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The source-relative volume threshold used before the local graph. -/
def pureWZ2OrdinaryPaperOrderBlockThreshold
    (sourceVolume : ENNReal) (rho : ℝ) : ENNReal :=
  (8 : ENNReal)⁻¹ *
    pureWZ2SourceHorizontalWindowSupply sourceVolume rho

/-- Safe blocks carrying at least the source-relative average volume. -/
def pureWZ2OrdinaryPaperOrderRegularizedBlocks
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (safe : PureWZ2BalancedSafeBlockFamilyData prepared) :
    Finset {block // block ∈ safe.blocks} :=
  safe.blocks.attach.filter fun block =>
    pureWZ2OrdinaryPaperOrderBlockThreshold
        (volume prepared.shadow.union) rho ≤
      volume (safe.blockWindow block).shading.union

theorem pureWZ2OrdinaryPaperOrderRegularizedBlock_volume_lower
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    (hblock : block ∈
      pureWZ2OrdinaryPaperOrderRegularizedBlocks safe) :
    pureWZ2OrdinaryPaperOrderBlockThreshold
        (volume prepared.shadow.union) rho ≤
      volume (safe.blockWindow block).shading.union :=
  (Finset.mem_filter.mp hblock).2

/-- The source-relative regularized blocks retain one quarter of the full
prepared carrier volume.  No graph volume or coarse-family density is used in
this selection. -/
theorem PureWZ2BalancedSafeBlockFamilyData.regularizedBlocks_retains_quarter
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (safe : PureWZ2BalancedSafeBlockFamilyData prepared) :
    volume prepared.shadow.union ≤
      4 * ∑ block ∈
          pureWZ2OrdinaryPaperOrderRegularizedBlocks safe,
        volume (safe.blockWindow block).shading.union := by
  let blocks := safe.blocks.attach
  let sourceVolume : ENNReal := volume prepared.shadow.union
  let root : ENNReal := ENNReal.ofReal (Real.sqrt rho)
  let denom : ENNReal := ENNReal.ofReal (2 + rho + Real.sqrt rho)
  let threshold : ENNReal :=
    pureWZ2OrdinaryPaperOrderBlockThreshold sourceVolume rho
  let allSupply : ENNReal := ∑ block ∈ blocks,
    volume (safe.blockWindow block).shading.union
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hsourceTop : sourceVolume ≠ ⊤ := by
    have hsub : prepared.shadow.union ⊆ source.shading.union := by
      rw [prepared.shadow_union]
      exact pullback.subshading.union_subset
    have hupper : sourceVolume ≤
        Kakeya.realRpowENN delta (sigma - inputLoss) := by
      exact (measure_mono hsub).trans source.extremal.volume_upper
    exact ne_top_of_le_ne_top (by simp [Kakeya.realRpowENN]) hupper
  have hthresholdTop : threshold ≠ ⊤ := by
    dsimp only [threshold, pureWZ2OrdinaryPaperOrderBlockThreshold,
      pureWZ2SourceHorizontalWindowSupply, sourceVolume, root, denom]
    exact ENNReal.mul_ne_top (by simp) <|
      ENNReal.div_ne_top
        (ENNReal.mul_ne_top hsourceTop ENNReal.ofReal_ne_top)
        (ENNReal.ofReal_pos.mpr (by
          nlinarith [hrho, Real.sqrt_nonneg rho])).ne'
  have hdenomZero : denom ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by
      nlinarith [hrho, Real.sqrt_nonneg rho])).ne'
  have hdenomTop : denom ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdenomReal : 2 + rho + 2 * Real.sqrt rho ≤
      2 * (2 + rho + Real.sqrt rho) := by
    nlinarith [hrho, Real.sqrt_nonneg rho]
  have hdenomBound : ENNReal.ofReal
        (2 + rho + 2 * Real.sqrt rho) ≤ 2 * denom := by
    calc
      _ ≤ ENNReal.ofReal (2 * (2 + rho + Real.sqrt rho)) :=
        ENNReal.ofReal_mono hdenomReal
      _ = 2 * denom := by
        dsimp only [denom]
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
  have hcardDenom : (blocks.card : ENNReal) * root ≤ 2 * denom := by
    have hcard := safe.blocks_card_mul_sqrtENN_le
    have hcardEq : blocks.card = safe.blocks.card := by simp [blocks]
    rw [hcardEq]
    exact hcard.trans hdenomBound
  have htwoEighth : (2 : ENNReal) * (8 : ENNReal)⁻¹ =
      (4 : ENNReal)⁻¹ := by
    rw [show (8 : ENNReal) = 2 * 4 by norm_num]
    rw [ENNReal.mul_inv (by norm_num) (by norm_num)]
    calc
      (2 : ENNReal) * (2⁻¹ * 4⁻¹) = (2 * 2⁻¹) * 4⁻¹ := by ac_rfl
      _ = 4⁻¹ := by rw [ENNReal.mul_inv_cancel] <;> norm_num
  have htwoQuarter : (2 : ENNReal) * (4 : ENNReal)⁻¹ =
      (2 : ENNReal)⁻¹ := by
    rw [show (4 : ENNReal) = 2 * 2 by norm_num]
    rw [ENNReal.mul_inv (by norm_num) (by norm_num)]
    calc
      (2 : ENNReal) * (2⁻¹ * 2⁻¹) = (2 * 2⁻¹) * 2⁻¹ := by ac_rfl
      _ = 2⁻¹ := by rw [ENNReal.mul_inv_cancel] <;> norm_num
  have hquarterCard : (4 : ENNReal)⁻¹ *
        ((blocks.card : ENNReal) * root) ≤ (2 : ENNReal)⁻¹ * denom := by
    calc
      (4 : ENNReal)⁻¹ * ((blocks.card : ENNReal) * root) ≤
          (4 : ENNReal)⁻¹ * (2 * denom) := by gcongr
      _ = (2 : ENNReal)⁻¹ * denom := by
        calc
          (4 : ENNReal)⁻¹ * (2 * denom) =
              (2 * (4 : ENNReal)⁻¹) * denom := by ac_rfl
          _ = (2 : ENNReal)⁻¹ * denom := by rw [htwoQuarter]
  have hsmallSource :
      2 * ((blocks.card : ENNReal) * threshold) ≤
        (2 : ENNReal)⁻¹ * sourceVolume := by
    have hscaled :
        (2 * ((blocks.card : ENNReal) * threshold)) * denom ≤
          ((2 : ENNReal)⁻¹ * sourceVolume) * denom := by
      dsimp only [threshold, pureWZ2OrdinaryPaperOrderBlockThreshold,
        pureWZ2SourceHorizontalWindowSupply, sourceVolume, root, denom]
      calc
        (2 * ((blocks.card : ENNReal) *
            ((8 : ENNReal)⁻¹ *
              (volume prepared.shadow.union *
                ENNReal.ofReal (Real.sqrt rho) /
                  ENNReal.ofReal (2 + rho + Real.sqrt rho))))) *
              ENNReal.ofReal (2 + rho + Real.sqrt rho) =
          ((2 * (8 : ENNReal)⁻¹) *
            ((blocks.card : ENNReal) *
              ENNReal.ofReal (Real.sqrt rho)) *
                volume prepared.shadow.union) *
              (ENNReal.ofReal (2 + rho + Real.sqrt rho))⁻¹ *
                ENNReal.ofReal (2 + rho + Real.sqrt rho) := by
            rw [div_eq_mul_inv]
            ring
        _ = ((4 : ENNReal)⁻¹ *
            ((blocks.card : ENNReal) * root)) * sourceVolume := by
          simp only [root, sourceVolume, denom]
          calc
            2 * 8⁻¹ *
                  ((blocks.card : ENNReal) * ENNReal.ofReal (Real.sqrt rho)) *
                  volume prepared.shadow.union *
                  (ENNReal.ofReal (2 + rho + Real.sqrt rho))⁻¹ *
                  ENNReal.ofReal (2 + rho + Real.sqrt rho) =
              (2 * 8⁻¹) *
                ((blocks.card : ENNReal) * ENNReal.ofReal (Real.sqrt rho)) *
                volume prepared.shadow.union *
                ((ENNReal.ofReal (2 + rho + Real.sqrt rho))⁻¹ *
                  ENNReal.ofReal (2 + rho + Real.sqrt rho)) := by ring
            _ = (2 * 8⁻¹) *
                ((blocks.card : ENNReal) * ENNReal.ofReal (Real.sqrt rho)) *
                volume prepared.shadow.union := by
              rw [ENNReal.inv_mul_cancel hdenomZero hdenomTop, mul_one]
            _ = 4⁻¹ *
                ((blocks.card : ENNReal) * ENNReal.ofReal (Real.sqrt rho)) *
                volume prepared.shadow.union := by rw [htwoEighth]
        _ ≤ ((2 : ENNReal)⁻¹ * denom) * sourceVolume := by gcongr
        _ = ((2 : ENNReal)⁻¹ * sourceVolume) * denom := by ring
    exact (ENNReal.mul_le_mul_iff_right hdenomZero hdenomTop).mp (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
  have hhalfSource : (2 : ENNReal)⁻¹ * sourceVolume ≤ allSupply := by
    calc
      (2 : ENNReal)⁻¹ * sourceVolume ≤
          (2 : ENNReal)⁻¹ * (2 * allSupply) := by
        gcongr
        simpa [sourceVolume, allSupply, blocks] using safe.volume_half
      _ = allSupply := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel] <;> norm_num
  have hsmall : 2 * ((blocks.card : ENNReal) * threshold) ≤ allSupply :=
    hsmallSource.trans hhalfSource
  have hhalf := finset_good_weighted_supply_retains_half
    blocks
    (fun block => volume (safe.blockWindow block).shading.union)
    1 threshold hthresholdTop (by simpa [allSupply] using hsmall)
  have hallToGood : allSupply ≤
      2 * ∑ block ∈
          pureWZ2OrdinaryPaperOrderRegularizedBlocks safe,
        volume (safe.blockWindow block).shading.union := by
    simpa [blocks, threshold, allSupply,
      pureWZ2OrdinaryPaperOrderRegularizedBlocks, sourceVolume, mul_one]
      using hhalf
  calc
    volume prepared.shadow.union ≤ 2 * allSupply := by
      simpa [sourceVolume, allSupply, blocks] using safe.volume_half
    _ ≤ 2 * (2 * ∑ block ∈
          pureWZ2OrdinaryPaperOrderRegularizedBlocks safe,
        volume (safe.blockWindow block).shading.union) := by gcongr
    _ = 4 * ∑ block ∈
          pureWZ2OrdinaryPaperOrderRegularizedBlocks safe,
        volume (safe.blockWindow block).shading.union := by ring

/-- The regularized safe blocks retain one quarter of the original indexed
mass after translating every block through its exact same-cell coarse
companion. -/
theorem PureWZ2BalancedSafeCoarseCompanionFamilyData.aggregate_regularized_source_mass_lower
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (data : PureWZ2BalancedSafeCoarseCompanionFamilyData safe) :
    volume prepared.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) ≤
      4 * ∑ block :
          {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
        (data.companion block.1).sourcePullback.shading.mass := by
  have hquarter := safe.regularizedBlocks_retains_quarter
  have hquarter' : volume prepared.shadow.union ≤
      4 * ∑ block :
          {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
        volume (safe.blockWindow block.1).shading.union := by
    calc
      volume prepared.shadow.union ≤
          4 * ∑ block ∈
            pureWZ2OrdinaryPaperOrderRegularizedBlocks safe,
              volume (safe.blockWindow block).shading.union := hquarter
      _ = 4 * ∑ block :
          {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
            volume (safe.blockWindow block.1).shading.union := by
        congr 1
        exact Finset.sum_subtype
          (pureWZ2OrdinaryPaperOrderRegularizedBlocks safe)
          (fun _ => Iff.rfl) _
  calc
    volume prepared.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) ≤
        (4 * ∑ block :
          {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
          volume (safe.blockWindow block.1).shading.union) *
            (twoScale.coarse.fineMultiplicity : ENNReal) := by
      exact mul_le_mul_right' hquarter' _
    _ = 4 * ∑ block :
          {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
        volume (safe.blockWindow block.1).shading.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ 4 * ∑ block :
          {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
        (data.companion block.1).sourcePullback.shading.mass := by
      gcongr with block
      exact
        PureWZ2BalancedSafeCoarseCompanionData.block_volume_mul_multiplicity_le_source_mass
          (data.companion block.1)

/-- The source-relative regularized family is nonempty. -/
theorem PureWZ2BalancedSafeBlockFamilyData.regularizedBlocks_nonempty
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (safe : PureWZ2BalancedSafeBlockFamilyData prepared) :
    (pureWZ2OrdinaryPaperOrderRegularizedBlocks safe).Nonempty := by
  rcases safe.blocks_nonempty with ⟨blockValue, hblockMem⟩
  let block : {block // block ∈ safe.blocks} := ⟨blockValue, hblockMem⟩
  have hblock : 0 < volume (safe.blockWindow block).shading.union := by
    rw [← (safe.blockWindow block).window_shading]
    exact (safe.blockWindow block).window.volumeSupply_pos.trans_le
      (safe.blockWindow block).window.volume_lower
  have hsource : 0 < volume prepared.shadow.union := by
    exact hblock.trans_le
      (measure_mono (safe.blockWindow block).subshading.union_subset)
  by_contra hempty
  have hzero : ∑ block ∈
      pureWZ2OrdinaryPaperOrderRegularizedBlocks safe,
        volume (safe.blockWindow block).shading.union = 0 := by
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
    simp
  have hle := safe.regularizedBlocks_retains_quarter
  rw [hzero, mul_zero] at hle
  exact (not_le_of_gt hsource) hle

/-!
## Remaining same-block bridge

The next geometric step is deliberately not postulated here. It must turn
the source-relative lower bound on each retained window into the actual
outer-popular graph-volume floor, using the same fixed-line choice and its
same-family provenance. Only after that bridge is proved may these blocks be
fed to `buildGraphGoodBlocks`.

The obsolete global-power implementation passed through the uncut spatial
coarse pullback. That loses the outer-popular height restriction and cannot
prove the final source-mass estimate.
-/

end Kakeya.Assouad

end
