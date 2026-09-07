import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallOrderedPairCallback

/-!
# Pre-runtime smallness consequences for ordered-pair scales

This file records only numerical consequences of the frozen interval grid, a
valid ordered-pair index, and scalar smallness fixed before the M5 runtime.
No shading, mass ledger, pullback, or runtime-selected object occurs here.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- A positive scale below `sqrt queryScale` gains the half-exponent appearing
in the global smallness condition. -/
private theorem rpow_le_query_half
    {queryScale x discreteLoss : ℝ}
    (hqueryPos : 0 < queryScale)
    (hx : 0 < x)
    (hxTop : x ≤ Real.sqrt queryScale)
    (hdiscreteLoss : 0 ≤ discreteLoss) :
    Real.rpow x discreteLoss ≤
      Real.rpow queryScale (discreteLoss / 2) := by
  calc
    Real.rpow x discreteLoss ≤
        Real.rpow (Real.sqrt queryScale) discreteLoss :=
      Real.rpow_le_rpow hx.le hxTop hdiscreteLoss
    _ = Real.rpow queryScale (discreteLoss / 2) := by
      rw [Real.sqrt_eq_rpow]
      calc
        Real.rpow (Real.rpow queryScale (1 / 2)) discreteLoss =
            Real.rpow queryScale ((1 / 2) * discreteLoss) :=
          (Real.rpow_mul hqueryPos.le (1 / 2) discreteLoss).symm
        _ = Real.rpow queryScale (discreteLoss / 2) := by ring_nf

/-- Scalar cancellation behind both constant-amplified scale inequalities. -/
private theorem mul_scale_le_pair_lower
    {queryScale x tau discreteLoss C : ℝ}
    (hqueryPos : 0 < queryScale)
    (hx : 0 < x)
    (hxTop : x ≤ Real.sqrt queryScale)
    (hdiscreteLoss : 0 ≤ discreteLoss)
    (hC : 0 ≤ C)
    (hsmall : C * Real.rpow queryScale (discreteLoss / 2) ≤ 1)
    (hpairLower : Real.rpow x (1 - discreteLoss) ≤ tau) :
    C * x ≤ tau := by
  have hxPower := rpow_le_query_half hqueryPos hx hxTop hdiscreteLoss
  have hCxPower : C * Real.rpow x discreteLoss ≤ 1 :=
    (mul_le_mul_of_nonneg_left hxPower hC).trans hsmall
  have hmul : (C * x) * Real.rpow x discreteLoss ≤
      Real.rpow x (1 - discreteLoss) * Real.rpow x discreteLoss := by
    calc
      (C * x) * Real.rpow x discreteLoss =
          x * (C * Real.rpow x discreteLoss) := by ring
      _ ≤ x * 1 := mul_le_mul_of_nonneg_left hCxPower hx.le
      _ = Real.rpow x (1 - discreteLoss) *
          Real.rpow x discreteLoss := by
        calc
          x * 1 = Real.rpow x 1 := by simp
          _ = Real.rpow x ((1 - discreteLoss) + discreteLoss) := by
            congr 1
            ring
          _ = Real.rpow x (1 - discreteLoss) *
              Real.rpow x discreteLoss := Real.rpow_add hx _ _
  exact (le_of_mul_le_mul_right hmul
    (Real.rpow_pos_of_pos hx discreteLoss)).trans hpairLower

/-- The four geometric scale inequalities needed by the M5 callback follow
from index-owned data and one half-exponent global smallness receipt. -/
theorem Proposition63FourCallOrderedPairIndexScales.scale_smallness
    {delta sigma discreteLoss intervalLoss outputLoss queryScale A : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN}
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    (hA : 1 ≤ A)
    (hdiscreteLoss : 0 ≤ discreteLoss)
    (hquerySmall :
      Real.rpow queryScale (discreteLoss / 2) ≤ 1 / (16 * A)) :
    8 * A * scales.rhoHat.1 ≤ scales.tau ∧
      scales.rhoHat.1 * Real.sqrt 3 ≤ scales.tau ∧
      scales.tau ≤ Real.sqrt scales.rhoHat.1 ∧
      scales.tau ^ 2 ≤ 4 * scales.rhoHat.1 := by
  let logicalR : ℝ :=
    (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
  have hlogicalPos : 0 < logicalR :=
    grid.scale_pos _
      (scales.first_lt_second.le.trans scales.second_le_gridN)
  have hlogicalTop : logicalR ≤ Real.sqrt queryScale := by
    rw [← grid.scale_top]
    have hk : (finiteIntervalOrderedPair gridN index).1 ≤ gridN :=
      scales.first_lt_second.le.trans scales.second_le_gridN
    have hmono : ∀ offset : ℕ,
        (finiteIntervalOrderedPair gridN index).1 + offset ≤ gridN →
        (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ) ≤
          grid.scale ((finiteIntervalOrderedPair gridN index).1 + offset) := by
      intro offset
      induction offset with
      | zero => simp
      | succ offset ih =>
          intro hsum
          exact (ih (by omega)).trans (grid.scale_mono _ (by omega))
    dsimp only [logicalR]
    simpa only [Nat.add_sub_of_le hk] using
      hmono (gridN - (finiteIntervalOrderedPair gridN index).1)
        (Nat.add_sub_of_le hk).le
  have h16Apos : 0 < 16 * A := by positivity
  have h16small :
      (16 * A) * Real.rpow queryScale (discreteLoss / 2) ≤ 1 := by
    calc
      (16 * A) * Real.rpow queryScale (discreteLoss / 2) ≤
          (16 * A) * (1 / (16 * A)) :=
        mul_le_mul_of_nonneg_left hquerySmall h16Apos.le
      _ = 1 := by field_simp
  have hamplified : (16 * A) * logicalR ≤ scales.tau :=
    mul_scale_le_pair_lower grid.query_pos hlogicalPos hlogicalTop
      hdiscreteLoss h16Apos.le h16small scales.pair_lower_window
  have hEight : 8 * A * scales.rhoHat.1 ≤ scales.tau := by
    calc
      8 * A * scales.rhoHat.1 ≤ 8 * A * (2 * logicalR) := by
        apply mul_le_mul_of_nonneg_left
        · simpa only [logicalR] using scales.rhoHat_le_two_logicalR
        · positivity
      _ = (16 * A) * logicalR := by ring
      _ ≤ scales.tau := hamplified
  have hsqrtThreeLeA : Real.sqrt 3 ≤ 8 * A := by
    have hsqrtThreeLeTwo : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sqrt_nonneg 3,
        Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    linarith
  have hSqrtThree :
      scales.rhoHat.1 * Real.sqrt 3 ≤ scales.tau := by
    calc
      scales.rhoHat.1 * Real.sqrt 3 ≤
          scales.rhoHat.1 * (8 * A) := by
        gcongr
        exact scales.logicalR_le_rhoHat.trans' hlogicalPos.le
      _ = 8 * A * scales.rhoHat.1 := by ring
      _ ≤ scales.tau := hEight
  have hTauSqrt : scales.tau ≤ Real.sqrt scales.rhoHat.1 := by
    exact scales.tau_le_sqrt_logicalR.trans
      (Real.sqrt_le_sqrt scales.logicalR_le_rhoHat)
  have hTauSq : scales.tau ^ 2 ≤ 4 * scales.rhoHat.1 := by
    have hnonneg : 0 ≤ Real.sqrt scales.rhoHat.1 := Real.sqrt_nonneg _
    have hsquare : scales.tau ^ 2 ≤
        (Real.sqrt scales.rhoHat.1) ^ 2 := by nlinarith [scales.tau_pos]
    have hrhoNonneg : 0 ≤ scales.rhoHat.1 :=
      scales.logicalR_le_rhoHat.trans' hlogicalPos.le
    rw [Real.sq_sqrt hrhoNonneg] at hsquare
    nlinarith
  exact ⟨hEight, hSqrtThree, hTauSqrt, hTauSq⟩

/-- The upper output window follows from the discrete grid window and the
pre-runtime loss-gap absorption. -/
theorem Proposition63FourCallOrderedPairIndexScales.rhoHat_le_output_rpow
    {delta sigma discreteLoss intervalLoss outputLoss queryScale
      firstOutputLoss : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN}
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    (hdelta : 0 < delta)
    (hfirstLt : firstOutputLoss < discreteLoss)
    (hgapSmall :
      Real.rpow delta (discreteLoss - firstOutputLoss) ≤ 1 / 2) :
    scales.rhoHat.1 ≤ Real.rpow delta firstOutputLoss := by
  have hdeltaOne : delta ≤ 1 :=
    scales.rhoHat.property.1.trans scales.rhoHat.property.2
  by_cases hdiscretePos : 0 < discreteLoss
  · have hlogicalUpper :
        (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ) ≤
          Real.rpow delta discreteLoss :=
      (grid.scale_window discreteLoss hdiscretePos (le_refl _) _
        (scales.first_lt_second.le.trans scales.second_le_gridN)).2
    have hrpowSplit : Real.rpow delta discreteLoss =
        Real.rpow delta firstOutputLoss *
          Real.rpow delta (discreteLoss - firstOutputLoss) := by
      calc
        Real.rpow delta discreteLoss =
            Real.rpow delta
              (firstOutputLoss + (discreteLoss - firstOutputLoss)) := by
          congr 1
          ring
        _ = Real.rpow delta firstOutputLoss *
            Real.rpow delta (discreteLoss - firstOutputLoss) :=
          Real.rpow_add hdelta _ _
    calc
      scales.rhoHat.1 ≤
          2 * (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ) :=
        scales.rhoHat_le_two_logicalR
      _ ≤ 2 * Real.rpow delta discreteLoss := by gcongr
      _ = 2 * (Real.rpow delta firstOutputLoss *
          Real.rpow delta (discreteLoss - firstOutputLoss)) := by
        rw [hrpowSplit]
      _ ≤ 2 * (Real.rpow delta firstOutputLoss * (1 / 2)) := by
        gcongr
        exact Real.rpow_nonneg hdelta.le _
      _ = Real.rpow delta firstOutputLoss := by ring
  · have hfirstNeg : firstOutputLoss < 0 := by linarith
    calc
      scales.rhoHat.1 ≤ 1 := scales.rhoHat.property.2
      _ = Real.rpow delta 0 := by simp
      _ ≤ Real.rpow delta firstOutputLoss :=
        Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne hfirstNeg.le

/-- Every valid index-owned aligned scale lies above the requested lower
output window. -/
theorem Proposition63FourCallOrderedPairIndexScales.output_rpow_le_rhoHat
    {delta sigma discreteLoss intervalLoss outputLoss queryScale
      firstOutputLoss : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN}
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    (hfirstPos : 0 < firstOutputLoss)
    (hfirstLe : firstOutputLoss ≤ discreteLoss) :
    Real.rpow delta (1 - firstOutputLoss) ≤ scales.rhoHat.1 := by
  exact (grid.scale_window firstOutputLoss hfirstPos hfirstLe _
    (scales.first_lt_second.le.trans scales.second_le_gridN)).1.trans
      scales.logicalR_le_rhoHat

end Kakeya.Assouad.PureWZ2
