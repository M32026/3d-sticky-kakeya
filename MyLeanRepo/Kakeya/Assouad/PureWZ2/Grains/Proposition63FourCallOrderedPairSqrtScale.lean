import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallOrderedPairCallback

/-!
# Pre-runtime square-root scale for a Proposition 6.3 ordered pair

This module constructs the final requested scale used by the four-call
ordered-pair callback.  The construction depends only on the index-owned
scale package and scalar hypotheses fixed before runtime.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- The square-root requested scale and all of its scalar receipts needed by
the actual ordered-pair callback. -/
structure Proposition63FourCallOrderedPairSqrtScalePackage
    {delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN}
    (scales : Proposition63FourCallOrderedPairIndexScales grid index) where
  outputLoss_pos : 0 < outputLoss
  outputLoss_le_half : outputLoss ≤ 1 / 2
  rhoHat_le_one_div_144 : scales.rhoHat.1 ≤ 1 / 144
  sqrtRequested : WZ2PaperRequestedScale scales.rhoHat.1
  hsqrtLower :
    Real.rpow scales.rhoHat.1 (1 - outputLoss) ≤ sqrtRequested.1
  hsqrtUpper : sqrtRequested.1 ≤ Real.rpow scales.rhoHat.1 outputLoss
  hsqrtOne : sqrtRequested.1 ≤ 1
  hsqrtSmall : sqrtRequested.1 ≤ 1 / 12
  hsqrtSq : sqrtRequested.1 ^ 2 ≤ 4 * scales.rhoHat.1
  sqrtScale_eq : sqrtRequested.1 = Real.sqrt scales.rhoHat.1

/-- Construct the callback's square-root scale before runtime.  The loss range
places the exponent `1 / 2` inside the requested output window, while the
smallness premise gives the numerical `1 / 12` bound. -/
noncomputable def Proposition63FourCallOrderedPairIndexScales.sqrtScalePackage
    {delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN}
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    (houtputLoss : 0 < outputLoss)
    (houtputLossHalf : outputLoss ≤ 1 / 2)
    (hrhoSmall : scales.rhoHat.1 ≤ 1 / 144) :
    Proposition63FourCallOrderedPairSqrtScalePackage scales := by
  have hrhoPos : 0 < scales.rhoHat.1 := by
    exact (grid.scale_pos _
      (scales.first_lt_second.le.trans scales.second_le_gridN)).trans_le
        scales.logicalR_le_rhoHat
  have hrhoNonneg : 0 ≤ scales.rhoHat.1 := hrhoPos.le
  have hrhoOne : scales.rhoHat.1 ≤ 1 := scales.rhoHat.property.2
  have hrhoLeSqrt : scales.rhoHat.1 ≤ Real.sqrt scales.rhoHat.1 := by
    nlinarith [Real.sqrt_nonneg scales.rhoHat.1,
      Real.sq_sqrt hrhoNonneg]
  have hsqrtOne : Real.sqrt scales.rhoHat.1 ≤ 1 := by
    nlinarith [Real.sqrt_nonneg scales.rhoHat.1,
      Real.sq_sqrt hrhoNonneg]
  let sqrtRequested : WZ2PaperRequestedScale scales.rhoHat.1 :=
    ⟨Real.sqrt scales.rhoHat.1, hrhoLeSqrt, hsqrtOne⟩
  have hsqrtLower :
      Real.rpow scales.rhoHat.1 (1 - outputLoss) ≤ sqrtRequested.1 := by
    change Real.rpow scales.rhoHat.1 (1 - outputLoss) ≤
      Real.sqrt scales.rhoHat.1
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hrhoPos hrhoOne (by linarith)
  have hsqrtUpper :
      sqrtRequested.1 ≤ Real.rpow scales.rhoHat.1 outputLoss := by
    change Real.sqrt scales.rhoHat.1 ≤
      Real.rpow scales.rhoHat.1 outputLoss
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hrhoPos hrhoOne houtputLossHalf
  have hsqrtSmall : sqrtRequested.1 ≤ 1 / 12 := by
    change Real.sqrt scales.rhoHat.1 ≤ 1 / 12
    nlinarith [Real.sqrt_nonneg scales.rhoHat.1,
      Real.sq_sqrt hrhoNonneg]
  have hsqrtSq : sqrtRequested.1 ^ 2 ≤ 4 * scales.rhoHat.1 := by
    change (Real.sqrt scales.rhoHat.1) ^ 2 ≤ 4 * scales.rhoHat.1
    rw [Real.sq_sqrt hrhoNonneg]
    linarith
  exact {
    outputLoss_pos := houtputLoss
    outputLoss_le_half := houtputLossHalf
    rhoHat_le_one_div_144 := hrhoSmall
    sqrtRequested := sqrtRequested
    hsqrtLower := hsqrtLower
    hsqrtUpper := hsqrtUpper
    hsqrtOne := by exact sqrtRequested.property.2
    hsqrtSmall := hsqrtSmall
    hsqrtSq := hsqrtSq
    sqrtScale_eq := rfl
  }

end Kakeya.Assouad.PureWZ2
