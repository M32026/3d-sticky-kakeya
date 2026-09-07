import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63CoarseGlobalGrain
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.AbsorptionArithmetic

/-!
# Proposition 6.3 M9: uniform global-AD absorption

The global slice constant produced after Lemma 4.4 depends on the runtime
Lipschitz coefficient.  In the first chart that coefficient is at most one
negative power of the fine scale.  This file records the resulting cubic
power envelope and freezes the remaining numerical constant before runtime.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2
namespace Proposition63ChartSelectionData

/-- A deliberately rounded, family-independent majorant for the constants in
the coarse global slice argument. -/
def proposition63M9CoarseGlobalPolynomialConstant : ENNReal :=
  500 * (3600000 : ENNReal) ^ 2 * 2100000000

theorem proposition63M9CoarseGlobalPolynomialConstant_ne_top :
    proposition63M9CoarseGlobalPolynomialConstant ≠ ⊤ := by
  unfold proposition63M9CoarseGlobalPolynomialConstant
  norm_num

/-- The real error entering the coarse thickening is linear in the chart
coefficient, up to the same negative power which also dominates `1`. -/
private theorem proposition63_coarse_error_ratio_le
    {q Delta localLoss : ℝ} (coefficient : NNReal)
    (qPos : 0 < q) (qOne : q ≤ 1)
    (DeltaPos : 0 < Delta)
    (qDelta : q ≤ Delta ^ 2)
    (localLossPos : 0 < localLoss)
    (coefficientBound : (coefficient : ℝ) ≤ Real.rpow q (-localLoss)) :
    proposition63CoarseExactSliceError q Delta Delta (coefficient : ℝ) / Delta ≤
      1774096 * Real.rpow q (-localLoss) := by
  have ratioLe : q / Delta ≤ Delta := by
    exact (div_le_iff₀ DeltaPos).2 (by simpa [pow_two] using qDelta)
  have ratioNonneg : 0 ≤ q / Delta := (div_pos qPos DeltaPos).le
  have coefficientNonneg : 0 ≤ (coefficient : ℝ) := by positivity
  have powerOne : 1 ≤ Real.rpow q (-localLoss) := by
    have := Real.rpow_le_rpow_of_exponent_ge
      (x := q) (y := 0) (z := -localLoss) qPos qOne
        (by linarith : -localLoss ≤ 0)
    simpa using this
  have sqrtThree : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sqrt_nonneg 3,
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have errorLe :
      proposition63CoarseExactSliceError q Delta Delta (coefficient : ℝ) ≤
        (1774080 * (coefficient : ℝ) + 16) * Delta := by
    have coefficientNN :
        ((Real.toNNReal (coefficient : ℝ) : NNReal) : ℝ) =
          (coefficient : ℝ) := by
      simpa using Real.coe_toNNReal (coefficient : ℝ) coefficientNonneg
    have deltaPlus : Delta + 100 * (q / Delta) ≤ 101 * Delta := by
      linarith
    have firstTerm :
        4 * (2520 * (coefficient : ℝ)) *
            (Delta + 100 * (q / Delta)) ≤
          1018080 * (coefficient : ℝ) * Delta := by
      calc
        4 * (2520 * (coefficient : ℝ)) *
              (Delta + 100 * (q / Delta)) ≤
            4 * (2520 * (coefficient : ℝ)) * (101 * Delta) := by
          gcongr
        _ = 1018080 * (coefficient : ℝ) * Delta := by ring
    have ratioSqrt :
        4 * (q / Delta) * Real.sqrt 3 ≤ 8 * Delta := by
      calc
        4 * (q / Delta) * Real.sqrt 3 ≤ 4 * Delta * 2 := by gcongr
        _ = 8 * Delta := by ring
    have deltaSqrt : 4 * (Real.sqrt 3 * Delta) ≤ 8 * Delta := by
      calc
        4 * (Real.sqrt 3 * Delta) ≤ 4 * (2 * Delta) := by gcongr
        _ = 8 * Delta := by ring
    unfold proposition63CoarseExactSliceError proposition63ExactSliceError
    rw [coefficientNN]
    have combined' :
        4 * (2520 * (coefficient : ℝ) *
              (Delta + 100 * (q / Delta))) +
            4 * (q / Delta) * Real.sqrt 3 +
          4 * (Real.sqrt 3 * Delta) +
          3 * (252000 * (coefficient : ℝ) * Delta) ≤
        (1018080 * (coefficient : ℝ) * Delta) + 8 * Delta +
          8 * Delta + 3 * (252000 * (coefficient : ℝ) * Delta) := by
      nlinarith [firstTerm, ratioSqrt, deltaSqrt]
    calc
      4 * (2520 * (coefficient : ℝ) *
              (Delta + 100 * (q / Delta))) +
            4 * (q / Delta) * Real.sqrt 3 +
          4 * (Real.sqrt 3 * Delta) +
          3 * (252000 * (coefficient : ℝ) * Delta) ≤
        (1018080 * (coefficient : ℝ) * Delta) + 8 * Delta +
          8 * Delta + 3 * (252000 * (coefficient : ℝ) * Delta) := combined'
      _ = (1774080 * (coefficient : ℝ) + 16) * Delta := by ring
  calc
    proposition63CoarseExactSliceError q Delta Delta (coefficient : ℝ) / Delta ≤
        ((1774080 * (coefficient : ℝ) + 16) * Delta) / Delta := by
      exact div_le_div_of_nonneg_right errorLe DeltaPos.le
    _ = 1774080 * (coefficient : ℝ) + 16 := by field_simp
    _ ≤ 1774080 * Real.rpow q (-localLoss) +
          16 * Real.rpow q (-localLoss) := by
      apply add_le_add
      · gcongr
      · nlinarith
    _ = 1774096 * Real.rpow q (-localLoss) := by ring

/-- The full coarse global AD constant costs at most three copies of the
first-chart local loss. -/
theorem proposition63_coarse_global_ad_constant_le_three_local
    {q Delta localLoss : ℝ} (coefficient : NNReal)
    (qPos : 0 < q) (qOne : q ≤ 1)
    (DeltaPos : 0 < Delta)
    (qDelta : q ≤ Delta ^ 2)
    (localLossPos : 0 < localLoss)
    (coefficientBound :
      (coefficient : ENNReal) ≤ Kakeya.realRpowENN q (-localLoss)) :
    proposition63CoarseGlobalADConstant q Delta Delta localLoss
        (coefficient : ℝ) ≤
      proposition63M9CoarseGlobalPolynomialConstant *
        (Kakeya.realRpowENN q (-localLoss)) ^ 3 := by
  let power : ℝ := Real.rpow q (-localLoss)
  have powerPos : 0 < power := Real.rpow_pos_of_pos qPos _
  have powerOneReal : 1 ≤ power := by
    have := Real.rpow_le_rpow_of_exponent_ge
      (x := q) (y := 0) (z := -localLoss) qPos qOne
        (by linarith : -localLoss ≤ 0)
    simpa [power] using this
  have powerENN : ENNReal.ofReal power =
      Kakeya.realRpowENN q (-localLoss) := by
    rfl
  have coefficientBoundReal : (coefficient : ℝ) ≤ power := by
    calc
      (coefficient : ℝ) = (coefficient : ENNReal).toReal := by simp
      _ ≤ (ENNReal.ofReal power).toReal := by
        apply ENNReal.toReal_mono (by simp)
        simpa only [powerENN] using coefficientBound
      _ = power := ENNReal.toReal_ofReal powerPos.le
  let errorRatio : ℝ :=
    proposition63CoarseExactSliceError q Delta Delta (coefficient : ℝ) / Delta
  have errorRatioNonneg : 0 ≤ errorRatio := by
    dsimp only [errorRatio]
    apply div_nonneg
    · unfold proposition63CoarseExactSliceError proposition63ExactSliceError
      positivity
    · exact DeltaPos.le
  have errorRatioBound : errorRatio ≤ 1774096 * power := by
    exact proposition63_coarse_error_ratio_le coefficient qPos qOne DeltaPos
      qDelta localLossPos coefficientBoundReal
  have ceilBound : (Nat.ceil errorRatio : ℝ) <
      1774096 * power + 1 :=
    by linarith [Nat.ceil_lt_add_one errorRatioNonneg, errorRatioBound]
  have factorBoundReal :
      2 * (Nat.ceil errorRatio : ℝ) + 2 ≤ 3600000 * power := by
    have powerNonneg : 0 ≤ power := powerPos.le
    nlinarith
  have factorBound :
      2 * ((Nat.ceil errorRatio : ENNReal) + 1) ≤
        3600000 * Kakeya.realRpowENN q (-localLoss) := by
    have lifted := ENNReal.ofReal_mono factorBoundReal
    have rearranged :
        2 * (Nat.ceil errorRatio : ENNReal) + 2 =
          2 * ((Nat.ceil errorRatio : ENNReal) + 1) := by ring
    rw [← rearranged]
    calc
      2 * (Nat.ceil errorRatio : ENNReal) + 2 =
          ENNReal.ofReal
            (2 * (Nat.ceil errorRatio : ℝ) + 2) := by
        norm_num [ENNReal.ofReal_add, ENNReal.ofReal_mul]
      _ ≤ ENNReal.ofReal (3600000 * power) := lifted
      _ = 3600000 * Kakeya.realRpowENN q (-localLoss) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
        exact congrArg (fun z : ENNReal => 3600000 * z) powerENN
  have oneLePower : (1 : ENNReal) ≤
      Kakeya.realRpowENN q (-localLoss) := by
    calc
      (1 : ENNReal) = ENNReal.ofReal 1 := by norm_num
      _ ≤ ENNReal.ofReal power := ENNReal.ofReal_mono powerOneReal
      _ = Kakeya.realRpowENN q (-localLoss) := powerENN
  have slabEq : proposition63SlabADConstant q localLoss =
      2000000000 * Kakeya.realRpowENN q (-localLoss) := by
    unfold proposition63SlabADConstant
    rw [show ENNReal.ofReal (25000 : ℝ) = 25000 by norm_num]
    ring
  have slabBound :
      1 + proposition63SlabADConstant q localLoss ≤
        2100000000 * Kakeya.realRpowENN q (-localLoss) := by
    rw [slabEq]
    calc
      1 + 2000000000 * Kakeya.realRpowENN q (-localLoss) ≤
          Kakeya.realRpowENN q (-localLoss) +
            2000000000 * Kakeya.realRpowENN q (-localLoss) :=
        add_le_add oneLePower (le_refl _)
      _ = 2000000001 * Kakeya.realRpowENN q (-localLoss) := by ring
      _ ≤ 2100000000 * Kakeya.realRpowENN q (-localLoss) := by gcongr <;> norm_num
  unfold proposition63CoarseGlobalADConstant
  change (2 * ((Nat.ceil errorRatio : ENNReal) + 1)) ^ 2 *
      (404 * (1 + proposition63SlabADConstant q localLoss)) ≤ _
  calc
    (2 * ((Nat.ceil errorRatio : ENNReal) + 1)) ^ 2 *
          (404 * (1 + proposition63SlabADConstant q localLoss)) ≤
        (3600000 * Kakeya.realRpowENN q (-localLoss)) ^ 2 *
          (404 * (2100000000 *
            Kakeya.realRpowENN q (-localLoss))) := by gcongr
    _ ≤ proposition63M9CoarseGlobalPolynomialConstant *
          (Kakeya.realRpowENN q (-localLoss)) ^ 3 := by
      unfold proposition63M9CoarseGlobalPolynomialConstant
      ring_nf
      gcongr <;> norm_num

/-- Fine-point error for the common whole-cell source.  It includes one
target-grid displacement and the contracted image of one original-grid
displacement. -/
def proposition63WholeCellExactSliceError
    (delta rho Delta coefficient : ℝ) : ℝ :=
  4 * ((2520 * (Real.toNNReal coefficient : ℝ)) *
      (Delta + 100 * (delta / rho) + delta * Real.sqrt 3)) +
    4 * ((101 / 100 : ℝ) * (delta / rho) * Real.sqrt 3)

/-- Total whole-cell error after the later Lemma-4.4 same-cell replacement. -/
def proposition63WholeCellCoarseExactSliceError
    (delta rho Delta coefficient : ℝ) : ℝ :=
  proposition63WholeCellExactSliceError delta rho Delta coefficient +
    4 * (Real.sqrt 3 * Delta) +
    3 * (252000 * (Real.toNNReal coefficient : ℝ) * Delta)

/-- Global AD constant for the canonical whole-cell chart source. -/
def proposition63WholeCellCoarseGlobalADConstant
    (delta rho Delta localLoss coefficient : ℝ) : ENNReal :=
  (2 * (Nat.ceil
      (proposition63WholeCellCoarseExactSliceError
        delta rho Delta coefficient / Delta) + 1) : ENNReal) ^ 2 *
    (500 * (1 + proposition63SlabADConstant delta localLoss))

/-- The whole-cell version obeys the same cubic loss envelope. -/
theorem proposition63_wholeCell_coarse_global_ad_constant_le_three_local
    {q Delta localLoss : ℝ} (coefficient : NNReal)
    (qPos : 0 < q) (qOne : q ≤ 1)
    (DeltaPos : 0 < Delta) (DeltaSmall : Delta ≤ 1 / 200)
    (qDelta : q ≤ Delta ^ 2)
    (localLossPos : 0 < localLoss)
    (coefficientBound :
      (coefficient : ENNReal) ≤ Kakeya.realRpowENN q (-localLoss)) :
    proposition63WholeCellCoarseGlobalADConstant q Delta Delta localLoss
        (coefficient : ℝ) ≤
      proposition63M9CoarseGlobalPolynomialConstant *
        (Kakeya.realRpowENN q (-localLoss)) ^ 3 := by
  let power : ℝ := Real.rpow q (-localLoss)
  have powerPos : 0 < power := Real.rpow_pos_of_pos qPos _
  have powerOneReal : 1 ≤ power := by
    have := Real.rpow_le_rpow_of_exponent_ge
      (x := q) (y := 0) (z := -localLoss) qPos qOne
        (by linarith : -localLoss ≤ 0)
    simpa [power] using this
  have powerENN : ENNReal.ofReal power =
      Kakeya.realRpowENN q (-localLoss) := rfl
  have coefficientBoundReal : (coefficient : ℝ) ≤ power := by
    calc
      (coefficient : ℝ) = (coefficient : ENNReal).toReal := by simp
      _ ≤ (ENNReal.ofReal power).toReal := by
        apply ENNReal.toReal_mono (by simp)
        simpa only [powerENN] using coefficientBound
      _ = power := ENNReal.toReal_ofReal powerPos.le
  have ratioLe : q / Delta ≤ Delta :=
    (div_le_iff₀ DeltaPos).2 (by simpa [pow_two] using qDelta)
  have ratioNonneg : 0 ≤ q / Delta := (div_pos qPos DeltaPos).le
  have sqrtThree : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sqrt_nonneg 3,
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have qSqrtLe : q * Real.sqrt 3 ≤ Delta / 100 := by
    have qLe : q ≤ Delta / 200 := by
      calc
        q ≤ Delta ^ 2 := qDelta
        _ ≤ Delta / 200 := by
          nlinarith [DeltaPos, DeltaSmall]
    nlinarith [qPos]
  have heightLe :
      Delta + 100 * (q / Delta) + q * Real.sqrt 3 ≤ 102 * Delta := by
    nlinarith
  have coefficientNonneg : 0 ≤ (coefficient : ℝ) := by positivity
  have coefficientNN :
      ((Real.toNNReal (coefficient : ℝ) : NNReal) : ℝ) =
        (coefficient : ℝ) := by
    simpa using Real.coe_toNNReal (coefficient : ℝ) coefficientNonneg
  have errorBound :
      proposition63WholeCellCoarseExactSliceError
          q Delta Delta (coefficient : ℝ) ≤
        (1784160 * (coefficient : ℝ) + 18) * Delta := by
    unfold proposition63WholeCellCoarseExactSliceError
      proposition63WholeCellExactSliceError
    rw [coefficientNN]
    have slopePart :
        4 * (2520 * (coefficient : ℝ)) *
            (Delta + 100 * (q / Delta) + q * Real.sqrt 3) ≤
          1028160 * (coefficient : ℝ) * Delta := by
      calc
        _ ≤ 4 * (2520 * (coefficient : ℝ)) * (102 * Delta) := by
          gcongr
        _ = _ := by ring
    have fineSpatial :
        4 * ((101 / 100 : ℝ) * (q / Delta) * Real.sqrt 3) ≤
          9 * Delta := by
      nlinarith
    have coarseSpatial : 4 * (Real.sqrt 3 * Delta) ≤ 8 * Delta := by
      nlinarith [DeltaPos]
    nlinarith
  let errorRatio := proposition63WholeCellCoarseExactSliceError
    q Delta Delta (coefficient : ℝ) / Delta
  have errorRatioNonneg : 0 ≤ errorRatio := by
    dsimp only [errorRatio]
    apply div_nonneg
    · unfold proposition63WholeCellCoarseExactSliceError
        proposition63WholeCellExactSliceError
      positivity
    · exact DeltaPos.le
  have errorRatioBound : errorRatio ≤ 1784178 * power := by
    calc
      errorRatio ≤ 1784160 * (coefficient : ℝ) + 18 := by
        dsimp only [errorRatio]
        calc
          _ ≤ ((1784160 * (coefficient : ℝ) + 18) * Delta) / Delta := by
            exact div_le_div_of_nonneg_right errorBound DeltaPos.le
          _ = _ := by field_simp
      _ ≤ 1784160 * power + 18 * power := by
        apply add_le_add
        · gcongr
        · nlinarith
      _ = _ := by ring
  have ceilBound : (Nat.ceil errorRatio : ℝ) <
      1784178 * power + 1 := by
    linarith [Nat.ceil_lt_add_one errorRatioNonneg, errorRatioBound]
  have factorBoundReal :
      2 * (Nat.ceil errorRatio : ℝ) + 2 ≤ 3600000 * power := by
    nlinarith
  have factorBound :
      2 * ((Nat.ceil errorRatio : ENNReal) + 1) ≤
        3600000 * Kakeya.realRpowENN q (-localLoss) := by
    have lifted := ENNReal.ofReal_mono factorBoundReal
    have rearranged :
        2 * (Nat.ceil errorRatio : ENNReal) + 2 =
          2 * ((Nat.ceil errorRatio : ENNReal) + 1) := by ring
    rw [← rearranged]
    calc
      2 * (Nat.ceil errorRatio : ENNReal) + 2 =
          ENNReal.ofReal (2 * (Nat.ceil errorRatio : ℝ) + 2) := by
        norm_num [ENNReal.ofReal_add, ENNReal.ofReal_mul]
      _ ≤ ENNReal.ofReal (3600000 * power) := lifted
      _ = 3600000 * Kakeya.realRpowENN q (-localLoss) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
        exact congrArg (fun z : ENNReal => 3600000 * z) powerENN
  have oneLePower : (1 : ENNReal) ≤
      Kakeya.realRpowENN q (-localLoss) := by
    calc
      (1 : ENNReal) = ENNReal.ofReal 1 := by norm_num
      _ ≤ ENNReal.ofReal power := ENNReal.ofReal_mono powerOneReal
      _ = Kakeya.realRpowENN q (-localLoss) := powerENN
  have slabEq : proposition63SlabADConstant q localLoss =
      2000000000 * Kakeya.realRpowENN q (-localLoss) := by
    unfold proposition63SlabADConstant
    rw [show ENNReal.ofReal (25000 : ℝ) = 25000 by norm_num]
    ring
  have slabBound :
      1 + proposition63SlabADConstant q localLoss ≤
        2100000000 * Kakeya.realRpowENN q (-localLoss) := by
    rw [slabEq]
    calc
      1 + 2000000000 * Kakeya.realRpowENN q (-localLoss) ≤
          Kakeya.realRpowENN q (-localLoss) +
            2000000000 * Kakeya.realRpowENN q (-localLoss) :=
        add_le_add oneLePower (le_refl _)
      _ = 2000000001 * Kakeya.realRpowENN q (-localLoss) := by ring
      _ ≤ 2100000000 * Kakeya.realRpowENN q (-localLoss) := by
        gcongr <;> norm_num
  unfold proposition63WholeCellCoarseGlobalADConstant
  change (2 * ((Nat.ceil errorRatio : ENNReal) + 1)) ^ 2 *
      (500 * (1 + proposition63SlabADConstant q localLoss)) ≤ _
  calc
    _ ≤ (3600000 * Kakeya.realRpowENN q (-localLoss)) ^ 2 *
          (500 * (2100000000 *
            Kakeya.realRpowENN q (-localLoss))) := by gcongr
    _ = proposition63M9CoarseGlobalPolynomialConstant *
          (Kakeya.realRpowENN q (-localLoss)) ^ 3 := by
      unfold proposition63M9CoarseGlobalPolynomialConstant
      ring

/-- Pre-runtime absorption of the one remaining fixed global-AD constant. -/
structure Proposition63M9CoarseGlobalAbsorptionCutoffData
    (localLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  constant_absorb : ∀ {q : ℝ}, 0 < q → q ≤ delta₀ →
    proposition63M9CoarseGlobalPolynomialConstant ≤
      Kakeya.realRpowENN q (-localLoss)

theorem proposition63_m9_coarse_global_absorption_cutoff
    {localLoss : ℝ} (localLossPos : 0 < localLoss) :
    Nonempty (Proposition63M9CoarseGlobalAbsorptionCutoffData localLoss) := by
  rcases exists_delta_realRpowENN_bound
      proposition63M9CoarseGlobalPolynomialConstant
      proposition63M9CoarseGlobalPolynomialConstant_ne_top localLossPos with
    ⟨delta₀, delta₀Pos, delta₀One, bound⟩
  exact ⟨{
    delta₀ := delta₀
    delta₀_pos := delta₀Pos
    delta₀_le_one := delta₀One
    constant_absorb := fun {q} qPos qLe => bound q qPos qLe
  }⟩

/-- Four copies of the local loss absorb both the cubic polynomial envelope
and its fixed coefficient. -/
theorem Proposition63M9CoarseGlobalAbsorptionCutoffData.global_constant_le_four
    {q Delta localLoss : ℝ}
    (cutoff : Proposition63M9CoarseGlobalAbsorptionCutoffData localLoss)
    (coefficient : NNReal)
    (qPos : 0 < q) (qLe : q ≤ cutoff.delta₀)
    (DeltaPos : 0 < Delta) (qDelta : q ≤ Delta ^ 2)
    (localLossPos : 0 < localLoss)
    (coefficientBound :
      (coefficient : ENNReal) ≤ Kakeya.realRpowENN q (-localLoss)) :
    proposition63CoarseGlobalADConstant q Delta Delta localLoss
        (coefficient : ℝ) ≤
      Kakeya.realRpowENN q (-(4 * localLoss)) := by
  have qOne : q ≤ 1 := qLe.trans cutoff.delta₀_le_one
  calc
    proposition63CoarseGlobalADConstant q Delta Delta localLoss
          (coefficient : ℝ) ≤
        proposition63M9CoarseGlobalPolynomialConstant *
          (Kakeya.realRpowENN q (-localLoss)) ^ 3 :=
      proposition63_coarse_global_ad_constant_le_three_local coefficient
        qPos qOne DeltaPos qDelta localLossPos coefficientBound
    _ ≤ Kakeya.realRpowENN q (-localLoss) *
          (Kakeya.realRpowENN q (-localLoss)) ^ 3 := by
      gcongr
      exact cutoff.constant_absorb qPos qLe
    _ = Kakeya.realRpowENN q (-(4 * localLoss)) := by
      rw [pow_three, ← realRpowENN_add qPos, ← realRpowENN_add qPos,
        ← realRpowENN_add qPos]
      congr 1
      ring

/-- Whole-cell counterpart of `global_constant_le_four`. -/
theorem Proposition63M9CoarseGlobalAbsorptionCutoffData.wholeCell_global_constant_le_four
    {q Delta localLoss : ℝ}
    (cutoff : Proposition63M9CoarseGlobalAbsorptionCutoffData localLoss)
    (coefficient : NNReal)
    (qPos : 0 < q) (qLe : q ≤ cutoff.delta₀)
    (DeltaPos : 0 < Delta) (DeltaSmall : Delta ≤ 1 / 200)
    (qDelta : q ≤ Delta ^ 2)
    (localLossPos : 0 < localLoss)
    (coefficientBound :
      (coefficient : ENNReal) ≤ Kakeya.realRpowENN q (-localLoss)) :
    proposition63WholeCellCoarseGlobalADConstant q Delta Delta localLoss
        (coefficient : ℝ) ≤
      Kakeya.realRpowENN q (-(4 * localLoss)) := by
  have qOne : q ≤ 1 := qLe.trans cutoff.delta₀_le_one
  calc
    proposition63WholeCellCoarseGlobalADConstant q Delta Delta localLoss
          (coefficient : ℝ) ≤
        proposition63M9CoarseGlobalPolynomialConstant *
          (Kakeya.realRpowENN q (-localLoss)) ^ 3 :=
      proposition63_wholeCell_coarse_global_ad_constant_le_three_local
        coefficient qPos qOne DeltaPos DeltaSmall qDelta localLossPos
          coefficientBound
    _ ≤ Kakeya.realRpowENN q (-localLoss) *
          (Kakeya.realRpowENN q (-localLoss)) ^ 3 := by
      gcongr
      exact cutoff.constant_absorb qPos qLe
    _ = Kakeya.realRpowENN q (-(4 * localLoss)) := by
      rw [pow_three, ← realRpowENN_add qPos, ← realRpowENN_add qPos,
        ← realRpowENN_add qPos]
      congr 1
      ring

/-- A negative power coming from an earlier, smaller loss is dominated by
the first-chart local-loss power. -/
theorem coefficient_power_le_local_power
    {q coefficientLoss localLoss : ℝ}
    (qPos : 0 < q) (qOne : q ≤ 1)
    (coefficientLossLe : coefficientLoss ≤ localLoss) :
    (Real.toNNReal (Real.rpow q (-coefficientLoss)) : ENNReal) ≤
      Kakeya.realRpowENN q (-localLoss) := by
  have realLe : Real.rpow q (-coefficientLoss) ≤
      Real.rpow q (-localLoss) :=
    Real.rpow_le_rpow_of_exponent_ge qPos qOne (by linarith)
  have powerNonneg : 0 ≤ Real.rpow q (-coefficientLoss) :=
    Real.rpow_nonneg qPos.le _
  calc
    (Real.toNNReal (Real.rpow q (-coefficientLoss)) : ENNReal) =
        ENNReal.ofReal (Real.rpow q (-coefficientLoss)) := by
      rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ powerNonneg]
    _ ≤ ENNReal.ofReal (Real.rpow q (-localLoss)) :=
      ENNReal.ofReal_mono realLe
    _ = Kakeya.realRpowENN q (-localLoss) := rfl

/-- Convert the four-local-loss envelope at the fine chart scale into the
required coarse-scale pre-grain loss. -/
theorem Proposition63M9CoarseGlobalAbsorptionCutoffData.global_cost
    {q Delta sigma localLoss preGrainLoss : ℝ}
    (cutoff : Proposition63M9CoarseGlobalAbsorptionCutoffData localLoss)
    (coefficient : NNReal)
    (qPos : 0 < q) (qLe : q ≤ cutoff.delta₀)
    (DeltaPos : 0 < Delta) (qDelta : q ≤ Delta ^ 2)
    (localLossPos : 0 < localLoss)
    (coefficientBound :
      (coefficient : ENNReal) ≤ Kakeya.realRpowENN q (-localLoss))
    (DeltaEq : Delta = Real.rpow q (sigma / (2 + sigma)))
    (gap : 4 * localLoss <
      (sigma / (2 + sigma)) * preGrainLoss) :
    proposition63CoarseGlobalADConstant q Delta Delta localLoss
        (coefficient : ℝ) ≤
      Kakeya.realRpowENN Delta (-preGrainLoss) := by
  have qOne : q ≤ 1 := qLe.trans cutoff.delta₀_le_one
  have exponentLe :
      -(sigma / (2 + sigma) * preGrainLoss) < -(4 * localLoss) := by
    linarith
  have powerLeReal : Real.rpow q (-(4 * localLoss)) ≤
      Real.rpow q (-(sigma / (2 + sigma) * preGrainLoss)) :=
    Real.rpow_le_rpow_of_exponent_ge qPos qOne exponentLe.le
  have targetEq :
      Kakeya.realRpowENN Delta (-preGrainLoss) =
        Kakeya.realRpowENN q
          (-(sigma / (2 + sigma) * preGrainLoss)) := by
    unfold Kakeya.realRpowENN
    rw [DeltaEq]
    congr 1
    calc
      (Real.rpow q (sigma / (2 + sigma))).rpow (-preGrainLoss) =
          Real.rpow q ((sigma / (2 + sigma)) * (-preGrainLoss)) :=
        (Real.rpow_mul qPos.le _ _).symm
      _ = Real.rpow q (-(sigma / (2 + sigma) * preGrainLoss)) := by
        congr 1
        ring
  calc
    proposition63CoarseGlobalADConstant q Delta Delta localLoss
          (coefficient : ℝ) ≤
        Kakeya.realRpowENN q (-(4 * localLoss)) :=
      cutoff.global_constant_le_four coefficient qPos qLe DeltaPos qDelta
        localLossPos coefficientBound
    _ ≤ Kakeya.realRpowENN q
          (-(sigma / (2 + sigma) * preGrainLoss)) :=
      ENNReal.ofReal_mono powerLeReal
    _ = Kakeya.realRpowENN Delta (-preGrainLoss) := targetEq.symm

/-- Final whole-cell global cost at the distinguished coarse scale. -/
theorem Proposition63M9CoarseGlobalAbsorptionCutoffData.wholeCell_global_cost
    {q Delta sigma localLoss preGrainLoss : ℝ}
    (cutoff : Proposition63M9CoarseGlobalAbsorptionCutoffData localLoss)
    (coefficient : NNReal)
    (qPos : 0 < q) (qLe : q ≤ cutoff.delta₀)
    (DeltaPos : 0 < Delta) (DeltaSmall : Delta ≤ 1 / 200)
    (qDelta : q ≤ Delta ^ 2)
    (localLossPos : 0 < localLoss)
    (coefficientBound :
      (coefficient : ENNReal) ≤ Kakeya.realRpowENN q (-localLoss))
    (DeltaEq : Delta = Real.rpow q (sigma / (2 + sigma)))
    (gap : 4 * localLoss <
      (sigma / (2 + sigma)) * preGrainLoss) :
    proposition63WholeCellCoarseGlobalADConstant q Delta Delta localLoss
        (coefficient : ℝ) ≤
      Kakeya.realRpowENN Delta (-preGrainLoss) := by
  have qOne : q ≤ 1 := qLe.trans cutoff.delta₀_le_one
  have exponentLe :
      -(sigma / (2 + sigma) * preGrainLoss) < -(4 * localLoss) := by
    linarith
  have powerLeReal : Real.rpow q (-(4 * localLoss)) ≤
      Real.rpow q (-(sigma / (2 + sigma) * preGrainLoss)) :=
    Real.rpow_le_rpow_of_exponent_ge qPos qOne exponentLe.le
  have targetEq :
      Kakeya.realRpowENN Delta (-preGrainLoss) =
        Kakeya.realRpowENN q
          (-(sigma / (2 + sigma) * preGrainLoss)) := by
    unfold Kakeya.realRpowENN
    rw [DeltaEq]
    congr 1
    calc
      (Real.rpow q (sigma / (2 + sigma))).rpow (-preGrainLoss) =
          Real.rpow q ((sigma / (2 + sigma)) * (-preGrainLoss)) :=
        (Real.rpow_mul qPos.le _ _).symm
      _ = Real.rpow q (-(sigma / (2 + sigma) * preGrainLoss)) := by
        congr 1
        ring
  calc
    proposition63WholeCellCoarseGlobalADConstant q Delta Delta localLoss
          (coefficient : ℝ) ≤
        Kakeya.realRpowENN q (-(4 * localLoss)) :=
      cutoff.wholeCell_global_constant_le_four coefficient qPos qLe DeltaPos
        DeltaSmall qDelta localLossPos coefficientBound
    _ ≤ Kakeya.realRpowENN q
          (-(sigma / (2 + sigma) * preGrainLoss)) :=
      ENNReal.ofReal_mono powerLeReal
    _ = Kakeya.realRpowENN Delta (-preGrainLoss) := targetEq.symm

end Proposition63ChartSelectionData
end Kakeya.Assouad.PureWZ2

end
