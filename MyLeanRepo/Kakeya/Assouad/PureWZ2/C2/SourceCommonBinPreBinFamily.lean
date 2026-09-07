import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinPreBinIntegrated
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinStandardSlabHeavySelection

/-!
# Simultaneous pre-bin height regularization on source-heavy slabs
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

structure PureWZ2SourceHeavyPreBinRhoHeightFamilyData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale) where
  blockData : ∀ heightIndex :
      {heightIndex // heightIndex ∈
        pureWZ2SourceHeavyStandardSqrtSlabs pullback},
    PureWZ2StandardSlabPreBinRhoHeightRegularizedData
      pullback heightIndex.1

theorem PureWZ2TwoScaleCellPullbackData.sourceHeavyPreBinRhoHeightFamily
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale) :
    Nonempty (PureWZ2SourceHeavyPreBinRhoHeightFamilyData pullback) := by
  have hblock : ∀ heightIndex :
      {heightIndex // heightIndex ∈
        pureWZ2SourceHeavyStandardSqrtSlabs pullback},
      Nonempty (PureWZ2StandardSlabPreBinRhoHeightRegularizedData
        pullback heightIndex.1) := by
    intro heightIndex
    exact pullback.preBinRhoHeightRegularization heightIndex.1
  exact ⟨{
    blockData := fun heightIndex => Classical.choice (hblock heightIndex)
  }⟩

namespace PureWZ2SourceHeavyPreBinRhoHeightFamilyData

variable
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (family : PureWZ2SourceHeavyPreBinRhoHeightFamilyData pullback)

def sourceMass
    (heightIndex : {heightIndex // heightIndex ∈
      pureWZ2SourceHeavyStandardSqrtSlabs pullback}) :
    ENNReal :=
  (family.blockData heightIndex).sourcePullback.shading.mass

def totalSourceMass : ENNReal :=
  ∑ heightIndex, family.sourceMass heightIndex

/-- Uniform lower bound for the popular-slice threshold after the one
pre-bin dyadic height refinement. -/
def popularFloor
    (_family : PureWZ2SourceHeavyPreBinRhoHeightFamilyData pullback) :
    ENNReal :=
  volume pullback.shading.union /
    (20 * pureWZ2CommonBinPreBinHeightCost rho)

theorem popularFloor_le
    (heightIndex : {heightIndex // heightIndex ∈
      pureWZ2SourceHeavyStandardSqrtSlabs pullback})
    (hrhoOne : rho ≤ 1) :
    family.popularFloor ≤
      pureWZ2SourceCommonBinPopularThreshold
        (family.blockData heightIndex).sourceSet (Real.sqrt rho) := by
  let L := pureWZ2CommonBinPreBinHeightCost rho
  let fullVolume := volume
    (pullback.standardSqrtSlabSourceRegion heightIndex.1.1)
  let retainedVolume := volume (family.blockData heightIndex).sourceSet
  let root := ENNReal.ofReal (Real.sqrt rho)
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hLPos : 0 < L :=
    pureWZ2CommonBinPreBinHeightCost_pos hrho hrhoOne
  have hLTop : L ≠ ⊤ := pureWZ2CommonBinPreBinHeightCost_ne_top rho
  have hrootPos : 0 < root :=
    ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hrho)
  have hrootTop : root ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfullHeavy :
      (10 : ENNReal)⁻¹ * volume pullback.shading.union * root ≤
        fullVolume := by
    simpa [fullVolume, root, pureWZ2StandardSqrtSlabHeavyThreshold] using
      pullback.standardSqrtSlabHeavyThreshold_le heightIndex.2
  have hretention : fullVolume ≤ L * retainedVolume := by
    calc
      fullVolume ≤
          ((family.blockData heightIndex).logarithmicCost : ENNReal) *
            retainedVolume := by
        simpa [fullVolume, retainedVolume,
          PureWZ2StandardSlabPreBinRhoHeightRegularizedData.sourceSet] using
          (family.blockData heightIndex).sourceVolume_retention
      _ ≤ L * retainedVolume := by
        gcongr
        exact (family.blockData heightIndex).logarithmicCost_le_heightCost
          hrhoOne
  have hbase :
      volume pullback.shading.union * root ≤
        10 * L * retainedVolume := by
    have hten : (10 : ENNReal) * 10⁻¹ = 1 :=
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    calc
      volume pullback.shading.union * root =
          1 * (volume pullback.shading.union * root) := by rw [one_mul]
      _ = (10 * (10 : ENNReal)⁻¹) *
          (volume pullback.shading.union * root) := by rw [hten]
      _ =
          10 * ((10 : ENNReal)⁻¹ * volume pullback.shading.union * root) := by
        ring
      _ ≤ 10 * fullVolume := by gcongr
      _ ≤ 10 * (L * retainedVolume) := by gcongr
      _ = 10 * L * retainedVolume := by ring
  have hdenomPos : 0 < 20 * L :=
    ENNReal.mul_pos (by norm_num) hLPos.ne'
  have hdenomTop : 20 * L ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hLTop
  have hpopularDenomPos : 0 < 2 * root :=
    ENNReal.mul_pos (by norm_num) hrootPos.ne'
  have hpopularDenomTop : 2 * root ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hrootTop
  rw [popularFloor, pureWZ2SourceCommonBinPopularThreshold,
    pureWZ2CommonBinPopularThreshold_eq]
  apply (ENNReal.div_le_iff hdenomPos.ne' hdenomTop).2
  apply (ENNReal.mul_le_mul_iff_right hrootPos.ne' hrootTop).mp
  have hpopularCancel :
      retainedVolume / (2 * root) * (2 * root) = retainedVolume :=
    ENNReal.div_mul_cancel hpopularDenomPos.ne' hpopularDenomTop
  calc
    root * volume pullback.shading.union =
        volume pullback.shading.union * root := by ring
    _ ≤ 10 * L * retainedVolume := hbase
    _ = 10 * L *
        ((retainedVolume / (2 * root)) * (2 * root)) := by
      rw [hpopularCancel]
    _ = root *
        ((volume (family.blockData heightIndex).sourceSet / (2 * root)) *
          (20 * L)) := by
      dsimp only [retainedVolume]
      ring

theorem block_sourceWeight_le
    (heightIndex : {heightIndex // heightIndex ∈
      pureWZ2SourceHeavyStandardSqrtSlabs pullback})
    (hrhoOne : rho ≤ 1) :
    pullback.standardSqrtSlabSourceWeight heightIndex.1.1 ≤
      pureWZ2CommonBinPreBinHeightCost rho *
        family.sourceMass heightIndex := by
  calc
    pullback.standardSqrtSlabSourceWeight heightIndex.1.1 ≤
        ((family.blockData heightIndex).logarithmicCost : ENNReal) *
          (family.blockData heightIndex).sourcePullback.shading.mass :=
      (family.blockData heightIndex).sourceWeight_retention
    _ ≤ pureWZ2CommonBinPreBinHeightCost rho *
          (family.blockData heightIndex).sourcePullback.shading.mass := by
      gcongr
      exact (family.blockData heightIndex).logarithmicCost_le_heightCost
        hrhoOne
    _ = pureWZ2CommonBinPreBinHeightCost rho *
          family.sourceMass heightIndex := rfl

/-- The original two-scale pullback is controlled by the simultaneous
pre-bin family.  This is the source-relative replacement for the old
runtime `hsourceScalar` premise. -/
theorem pullback_mass_le_two_heightCost_mul_totalSourceMass
    (hrhoOne : rho ≤ 1) :
    pullback.shading.mass ≤
      2 * pureWZ2CommonBinPreBinHeightCost rho * family.totalSourceMass := by
  have hheavy := pullback.sourceHeavyStandardSqrtSlabs_retains_half_mass
  calc
    pullback.shading.mass ≤
        2 * ∑ heightIndex ∈ pureWZ2SourceHeavyStandardSqrtSlabs pullback,
          pullback.standardSqrtSlabSourceWeight heightIndex.1 := hheavy
    _ = 2 * ∑ heightIndex :
          {heightIndex // heightIndex ∈
            pureWZ2SourceHeavyStandardSqrtSlabs pullback},
          pullback.standardSqrtSlabSourceWeight heightIndex.1.1 := by
      rw [Finset.sum_subtype
        (pureWZ2SourceHeavyStandardSqrtSlabs pullback) (fun _ => Iff.rfl)]
    _ ≤ 2 * ∑ heightIndex :
          {heightIndex // heightIndex ∈
            pureWZ2SourceHeavyStandardSqrtSlabs pullback},
          pureWZ2CommonBinPreBinHeightCost rho *
            family.sourceMass heightIndex := by
      gcongr with heightIndex
      exact family.block_sourceWeight_le heightIndex hrhoOne
    _ = 2 * pureWZ2CommonBinPreBinHeightCost rho *
          family.totalSourceMass := by
      unfold totalSourceMass
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro heightIndex _
      ring

end PureWZ2SourceHeavyPreBinRhoHeightFamilyData

end Kakeya.Assouad

end
