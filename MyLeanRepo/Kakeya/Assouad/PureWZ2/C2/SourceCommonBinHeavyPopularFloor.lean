import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinSourceHeavyGraphFamily

/-!
# Uniform popular-height floor on source-heavy standard slabs
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

def pureWZ2SourceHeavyStandardSlabPopularFloor
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale) : ENNReal :=
  volume pullback.shading.union / 20

namespace PureWZ2TwoScaleCellPullbackData

variable
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)

/-- Every retained source-heavy standard slab has a common-bin popular
threshold bounded below by the same source-relative scalar. -/
theorem sourceHeavyStandardSqrtSlab_popularThreshold_lower
    {heightIndex :
      PureWZ2SourceHeavyStandardSqrtSlabIndex pullback} :
    pureWZ2SourceHeavyStandardSlabPopularFloor pullback ≤
      pureWZ2SourceCommonBinPopularThreshold
        (pullback.standardSqrtSlabSourceRegion heightIndex.1.1)
        (Real.sqrt rho) := by
  let root := ENNReal.ofReal (Real.sqrt rho)
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hrootZero : root ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hrho)).ne'
  have hrootTop : root ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdenomZero : 2 * root ≠ 0 :=
    mul_ne_zero (by norm_num) hrootZero
  have hdenomTop : 2 * root ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hrootTop
  have hcoefficient :
      (20 : ENNReal)⁻¹ * 2 = (10 : ENNReal)⁻¹ := by
    rw [show (20 : ENNReal) = 2 * 10 by norm_num]
    rw [ENNReal.mul_inv (by norm_num) (by norm_num)]
    calc
      ((2 : ENNReal)⁻¹ * (10 : ENNReal)⁻¹) * 2 =
          (10 : ENNReal)⁻¹ * ((2 : ENNReal)⁻¹ * 2) := by ring
      _ = (10 : ENNReal)⁻¹ := by
        rw [ENNReal.inv_mul_cancel] <;> norm_num
  rw [pureWZ2SourceCommonBinPopularThreshold,
    pureWZ2CommonBinPopularThreshold_eq]
  apply
    (ENNReal.le_div_iff_mul_le
      (Or.inl hdenomZero) (Or.inl hdenomTop)).2
  calc
    pureWZ2SourceHeavyStandardSlabPopularFloor pullback *
          (2 * ENNReal.ofReal (Real.sqrt rho)) =
        ((20 : ENNReal)⁻¹ * 2) *
          volume pullback.shading.union * root := by
      simp only [pureWZ2SourceHeavyStandardSlabPopularFloor,
        div_eq_mul_inv, root]
      ring
    _ =
        (10 : ENNReal)⁻¹ *
          volume pullback.shading.union * root := by
      rw [hcoefficient]
    _ =
        pureWZ2StandardSqrtSlabHeavyThreshold pullback := by
      rfl
    _ ≤
        volume
          (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) :=
      pullback.standardSqrtSlabHeavyThreshold_le heightIndex.2

end PureWZ2TwoScaleCellPullbackData

end Kakeya.Assouad

end
