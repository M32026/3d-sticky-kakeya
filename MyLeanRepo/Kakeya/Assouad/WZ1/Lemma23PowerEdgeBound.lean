import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23EdgeCardinalityFromBounds
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LayerCounts
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23QuantitativeBinBounds
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SelectedCellCount

/-!
# Power-form edge lower bound for WZ1 Lemma 23

This module simplifies the exact quantitative edge bound to the paper's
power form.  If the retained window has volume at least

`rho^(1 + sigma/2 + volumeLoss)`

and the AD constant is at most `rho^(-constantLoss)`, then the sharp
localized normalized graph has at least

`D⁻¹ * rho^(-3/2 + 4*volumeLoss + 4*constantLoss)`

edges, where `D = 15294608179200` is the explicit product of all finite
counting constants.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Explicit absolute denominator in the power-form Lemma 23 edge bound. -/
def wz1Lemma23EdgeConstant : ℝ :=
  15294608179200

private lemma wz1Lemma23_sqrt_div_rho_rpow
    {rho sigma : ℝ} (hrho : 0 < rho) :
    Real.rpow (Real.sqrt rho / rho) (1 - sigma) =
      Real.rpow rho (-(1 - sigma) / 2) := by
  have hsqrt :
      Real.sqrt rho = Real.rpow rho (1 / 2 : ℝ) :=
    Real.sqrt_eq_rpow rho
  have hone : Real.rpow rho (1 : ℝ) = rho :=
    Real.rpow_one rho
  have hratio :
      Real.sqrt rho / rho =
        Real.rpow rho (-1 / 2 : ℝ) := by
    calc
      Real.sqrt rho / rho =
          Real.rpow rho (1 / 2 : ℝ) /
            Real.rpow rho (1 : ℝ) := by
        rw [hsqrt, hone]
      _ = Real.rpow rho ((1 / 2 : ℝ) - 1) :=
        (Real.rpow_sub hrho (1 / 2 : ℝ) 1).symm
      _ = Real.rpow rho (-1 / 2 : ℝ) := by
        congr 1
        ring
  rw [hratio]
  calc
    Real.rpow (Real.rpow rho (-1 / 2 : ℝ)) (1 - sigma)
        = Real.rpow rho ((-1 / 2 : ℝ) * (1 - sigma)) := by
      exact
        (Real.rpow_mul hrho.le (-1 / 2 : ℝ) (1 - sigma)).symm
    _ = Real.rpow rho (-(1 - sigma) / 2) := by
      congr 1
      ring

private lemma wz1Lemma23_cell_lower_identity
    {rho sigma volumeLoss : ℝ} (hrho : 0 < rho) :
    Real.rpow rho (1 + sigma / 2 + volumeLoss) /
        (8 * Real.rpow rho (5 / 2 : ℝ)) =
      (1 / 8 : ℝ) *
        Real.rpow rho (-3 / 2 + sigma / 2 + volumeLoss) := by
  have hexp :
      1 + sigma / 2 + volumeLoss - 5 / 2 =
        -3 / 2 + sigma / 2 + volumeLoss := by
    ring
  calc
    Real.rpow rho (1 + sigma / 2 + volumeLoss) /
          (8 * Real.rpow rho (5 / 2 : ℝ))
        = (1 / 8 : ℝ) *
            (Real.rpow rho (1 + sigma / 2 + volumeLoss) /
              Real.rpow rho (5 / 2 : ℝ)) := by
          ring
    _ = (1 / 8 : ℝ) *
          Real.rpow rho
            ((1 + sigma / 2 + volumeLoss) - 5 / 2) := by
      exact congrArg (fun value : ℝ => (1 / 8 : ℝ) * value)
        (Real.rpow_sub hrho
          (1 + sigma / 2 + volumeLoss) (5 / 2 : ℝ)).symm
    _ = (1 / 8 : ℝ) *
          Real.rpow rho
            (-3 / 2 + sigma / 2 + volumeLoss) := by
      rw [hexp]

private lemma wz1Lemma23_cell_lower_with_extra
    {rho sigma volumeLoss extraLoss extraCost : ℝ}
    (hrho : 0 < rho) (hextra : 0 < extraCost)
    (hextraPower : extraCost ≤ Real.rpow rho (-extraLoss)) :
    (1 / 8 : ℝ) *
        Real.rpow rho
          (-3 / 2 + sigma / 2 + volumeLoss + extraLoss) ≤
      Real.rpow rho (1 + sigma / 2 + volumeLoss) /
        (8 * extraCost * Real.rpow rho (5 / 2 : ℝ)) := by
  have hbase := wz1Lemma23_cell_lower_identity
    (rho := rho) (sigma := sigma) (volumeLoss := volumeLoss) hrho
  have hextraInv :
      Real.rpow rho extraLoss ≤ extraCost⁻¹ := by
    have hpowPos : 0 < Real.rpow rho (-extraLoss) :=
      Real.rpow_pos_of_pos hrho _
    have hinv := (inv_le_inv₀ hpowPos hextra).mpr hextraPower
    have hrpowInv :
        (Real.rpow rho (-extraLoss))⁻¹ = Real.rpow rho extraLoss := by
      have hneg := Real.rpow_neg hrho.le extraLoss
      calc
        (Real.rpow rho (-extraLoss))⁻¹ =
            ((Real.rpow rho extraLoss)⁻¹)⁻¹ :=
          congrArg Inv.inv hneg
        _ = Real.rpow rho extraLoss := inv_inv _
    rw [hrpowInv] at hinv
    exact hinv
  have hsplit :
      Real.rpow rho
          (-3 / 2 + sigma / 2 + volumeLoss + extraLoss) =
        Real.rpow rho (-3 / 2 + sigma / 2 + volumeLoss) *
          Real.rpow rho extraLoss := by
    exact Real.rpow_add hrho _ _
  rw [hsplit]
  calc
    (1 / 8 : ℝ) *
          (Real.rpow rho (-3 / 2 + sigma / 2 + volumeLoss) *
            Real.rpow rho extraLoss)
        ≤ (1 / 8 : ℝ) *
          (Real.rpow rho (-3 / 2 + sigma / 2 + volumeLoss) *
            extraCost⁻¹) := by
      gcongr
      exact Real.rpow_nonneg hrho.le _
    _ = ((1 / 8 : ℝ) *
          Real.rpow rho (-3 / 2 + sigma / 2 + volumeLoss)) /
        extraCost := by rw [div_eq_mul_inv]; ring
    _ = (Real.rpow rho (1 + sigma / 2 + volumeLoss) /
          (8 * Real.rpow rho (5 / 2 : ℝ))) / extraCost := by rw [hbase]
    _ = Real.rpow rho (1 + sigma / 2 + volumeLoss) /
        (8 * extraCost * Real.rpow rho (5 / 2 : ℝ)) := by
      field_simp [hextra.ne', (Real.rpow_pos_of_pos hrho (5 / 2 : ℝ)).ne']

private lemma wz1Lemma23_denominator_power_identity
    {rho sigma constantLoss : ℝ} (hrho : 0 < rho) :
    ((4 * Real.rpow rho (-1 / 2 : ℝ)) *
        (21 * Real.rpow rho (-(1 - sigma) / 2 - constantLoss))) ^ 2 *
      (((3 * Real.rpow rho (-1 / 2 : ℝ)) ^ 2) *
        (35 * Real.rpow rho (-(1 - sigma) / 2 - constantLoss))) *
      ((3 * Real.rpow rho (-1 / 2 : ℝ)) *
        (35 * Real.rpow rho (-(1 - sigma) / 2 - constantLoss))) *
      16 =
    3734035200 *
      Real.rpow rho
        (-9 / 2 + 2 * sigma - 4 * constantLoss) := by
  have hq2 :
      (Real.rpow rho (-1 / 2 : ℝ)) ^ 2 =
        Real.rpow rho (2 * (-1 / 2 : ℝ)) :=
    rpow_nat_pow hrho (-1 / 2 : ℝ) 2
  have hq5 :
      (Real.rpow rho (-1 / 2 : ℝ)) ^ 5 =
        Real.rpow rho (5 * (-1 / 2 : ℝ)) :=
    rpow_nat_pow hrho (-1 / 2 : ℝ) 5
  have hb4 :
      (Real.rpow rho
        (-(1 - sigma) / 2 - constantLoss)) ^ 4 =
        Real.rpow rho
          (4 * (-(1 - sigma) / 2 - constantLoss)) :=
    rpow_nat_pow hrho
      (-(1 - sigma) / 2 - constantLoss) 4
  have hcombine :
      Real.rpow rho (5 * (-1 / 2 : ℝ)) *
          Real.rpow rho
            (4 * (-(1 - sigma) / 2 - constantLoss)) =
        Real.rpow rho
          (-9 / 2 + 2 * sigma - 4 * constantLoss) := by
    calc
      Real.rpow rho (5 * (-1 / 2 : ℝ)) *
            Real.rpow rho
              (4 * (-(1 - sigma) / 2 - constantLoss))
          = Real.rpow rho
              (5 * (-1 / 2 : ℝ) +
                4 * (-(1 - sigma) / 2 - constantLoss)) :=
        (Real.rpow_add hrho _ _).symm
      _ = Real.rpow rho
          (-9 / 2 + 2 * sigma - 4 * constantLoss) := by
        congr 1
        ring
  calc
    ((4 * Real.rpow rho (-1 / 2 : ℝ)) *
          (21 * Real.rpow rho
            (-(1 - sigma) / 2 - constantLoss))) ^ 2 *
        (((3 * Real.rpow rho (-1 / 2 : ℝ)) ^ 2) *
          (35 * Real.rpow rho
            (-(1 - sigma) / 2 - constantLoss))) *
        ((3 * Real.rpow rho (-1 / 2 : ℝ)) *
          (35 * Real.rpow rho
            (-(1 - sigma) / 2 - constantLoss))) *
        16
        =
      3734035200 *
        (Real.rpow rho (-1 / 2 : ℝ)) ^ 5 *
        (Real.rpow rho
          (-(1 - sigma) / 2 - constantLoss)) ^ 4 := by
      ring
    _ =
      3734035200 *
        Real.rpow rho (5 * (-1 / 2 : ℝ)) *
        Real.rpow rho
          (4 * (-(1 - sigma) / 2 - constantLoss)) := by
      rw [hq5, hb4]
    _ =
      3734035200 *
        Real.rpow rho
          (-9 / 2 + 2 * sigma - 4 * constantLoss) := by
      calc
        3734035200 *
              Real.rpow rho (5 * (-1 / 2 : ℝ)) *
              Real.rpow rho
                (4 * (-(1 - sigma) / 2 - constantLoss))
            =
          3734035200 *
            (Real.rpow rho (5 * (-1 / 2 : ℝ)) *
              Real.rpow rho
                (4 * (-(1 - sigma) / 2 - constantLoss))) := by
          ring
        _ = 3734035200 *
            Real.rpow rho
              (-9 / 2 + 2 * sigma - 4 * constantLoss) := by
          rw [hcombine]

private lemma wz1Lemma23_power_budget
    {rho sigma volumeLoss constantLoss : ℝ}
    (hrho : 0 < rho) :
    ((wz1Lemma23EdgeConstant : ℝ)⁻¹ *
        Real.rpow rho
          (-3 / 2 + 4 * volumeLoss + 4 * constantLoss)) *
      ((((4 * Real.rpow rho (-1 / 2 : ℝ)) *
          (21 * Real.rpow rho
            (-(1 - sigma) / 2 - constantLoss))) ^ 2) *
        (((3 * Real.rpow rho (-1 / 2 : ℝ)) ^ 2) *
          (35 * Real.rpow rho
            (-(1 - sigma) / 2 - constantLoss))) *
        ((3 * Real.rpow rho (-1 / 2 : ℝ)) *
          (35 * Real.rpow rho
            (-(1 - sigma) / 2 - constantLoss))) *
        16) =
      ((1 / 8 : ℝ) *
        Real.rpow rho
          (-3 / 2 + sigma / 2 + volumeLoss)) ^ 4 := by
  have hden :=
    wz1Lemma23_denominator_power_identity
      (rho := rho) (sigma := sigma)
      (constantLoss := constantLoss) hrho
  rw [hden]
  have hleft :
      Real.rpow rho
          (-3 / 2 + 4 * volumeLoss + 4 * constantLoss) *
        Real.rpow rho
          (-9 / 2 + 2 * sigma - 4 * constantLoss) =
      Real.rpow rho
        (-6 + 2 * sigma + 4 * volumeLoss) := by
    calc
      Real.rpow rho
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss) *
          Real.rpow rho
            (-9 / 2 + 2 * sigma - 4 * constantLoss)
          = Real.rpow rho
              ((-3 / 2 + 4 * volumeLoss + 4 * constantLoss) +
                (-9 / 2 + 2 * sigma - 4 * constantLoss)) :=
        (Real.rpow_add hrho _ _).symm
      _ = Real.rpow rho
          (-6 + 2 * sigma + 4 * volumeLoss) := by
        congr 1
        ring
  have hright :
      (Real.rpow rho
        (-3 / 2 + sigma / 2 + volumeLoss)) ^ 4 =
      Real.rpow rho
        (-6 + 2 * sigma + 4 * volumeLoss) := by
    rw [rpow_nat_pow hrho
      (-3 / 2 + sigma / 2 + volumeLoss) 4]
    congr 1
    ring
  calc
    (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow rho
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss) *
        (3734035200 *
          Real.rpow rho
            (-9 / 2 + 2 * sigma - 4 * constantLoss))
        =
      ((wz1Lemma23EdgeConstant : ℝ)⁻¹ * 3734035200) *
        (Real.rpow rho
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss) *
          Real.rpow rho
            (-9 / 2 + 2 * sigma - 4 * constantLoss)) := by
      ring
    _ = (1 / 4096 : ℝ) *
        Real.rpow rho
          (-6 + 2 * sigma + 4 * volumeLoss) := by
      rw [hleft]
      norm_num [wz1Lemma23EdgeConstant]
    _ = (1 / 4096 : ℝ) *
        (Real.rpow rho
          (-3 / 2 + sigma / 2 + volumeLoss)) ^ 4 := by
      rw [hright]
    _ = ((1 / 8 : ℝ) *
        Real.rpow rho
          (-3 / 2 + sigma / 2 + volumeLoss)) ^ 4 := by
      ring

/--
Power-form lower bound for the sharp localized normalized edge set.
-/
theorem WZ1Lemma23LocalizedPreparedPackage.power_edge_bound_of_coord
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C}
    {localized :
      WZ1Lemma23LocalizedGlobalBinPackage windowed.global}
    {residue :
      WZ1Lemma23YResiduePackage windowed.global}
    {localBins :
      WZ1Lemma23LocalBinPackage
        (rho := rho) (sigma := sigma) C windowed.global.cells}
    (package :
      WZ1Lemma23LocalizedPreparedPackage
        windowed localized residue localBins)
    (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hcoord : ∀ point ∈ Y.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1)
    (hC : 1 ≤ C) (hCtop : C ≠ ⊤)
    (volumeLoss constantLoss extraLoss : ℝ)
    (hvolume :
      ENNReal.ofReal
          (Real.rpow rho
            (1 + sigma / 2 + volumeLoss)) ≤
        MeasureTheory.volume Y.union)
    (hCpower :
      C.toReal ≤ Real.rpow rho (-constantLoss))
    (hextraPower :
      (residue.extraCost : ℝ) ≤ Real.rpow rho (-extraLoss)) :
    (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
        Real.rpow rho
          (-3 / 2 + 4 * volumeLoss + 4 * constantLoss +
            4 * extraLoss) ≤
      (package.normalized.H.card : ℝ) := by
  let cellLower :=
    (1 / 8 : ℝ) *
      Real.rpow rho
        (-3 / 2 + sigma / 2 + volumeLoss + extraLoss)
  let yLayerUpper :=
    4 * Real.rpow rho (-1 / 2 : ℝ)
  let localBinUpper :=
    21 * Real.rpow rho
      (-(1 - sigma) / 2 - constantLoss)
  let heightUpper :=
    3 * Real.rpow rho (-1 / 2 : ℝ)
  let globalBinUpper :=
    35 * Real.rpow rho
      (-(1 - sigma) / 2 - constantLoss)
  let target :=
    (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
      Real.rpow rho
        (-3 / 2 + 4 * volumeLoss + 4 * constantLoss +
          4 * extraLoss)
  have hrho := windowed.global.rho_pos
  have hsqrt : 0 < Real.sqrt rho :=
    Real.sqrt_pos.mpr hrho
  have hcellLower : 0 ≤ cellLower := by
    dsimp only [cellLower]
    exact mul_nonneg (by norm_num)
      (Real.rpow_nonneg hrho.le _)
  have hyLayerUpper : 0 < yLayerUpper := by
    dsimp only [yLayerUpper]
    exact mul_pos (by norm_num)
      (Real.rpow_pos_of_pos hrho _)
  have hlocalBinUpper : 0 < localBinUpper := by
    dsimp only [localBinUpper]
    exact mul_pos (by norm_num)
      (Real.rpow_pos_of_pos hrho _)
  have hheightUpper : 0 < heightUpper := by
    dsimp only [heightUpper]
    exact mul_pos (by norm_num)
      (Real.rpow_pos_of_pos hrho _)
  have hglobalBinUpper : 0 < globalBinUpper := by
    dsimp only [globalBinUpper]
    exact mul_pos (by norm_num)
      (Real.rpow_pos_of_pos hrho _)
  have hcells :
      cellLower ≤ (residue.cells.card : ℝ) := by
    have hraw :=
      residue.cell_count_from_volume
        hrho_one
        (Real.rpow rho (1 + sigma / 2 + volumeLoss))
        (Real.rpow_nonneg hrho.le _) hvolume
    exact (wz1Lemma23_cell_lower_with_extra hrho
      (by exact_mod_cast residue.extraCost_pos) hextraPower).trans hraw
  have hsqrtInv :
      1 / Real.sqrt rho =
        Real.rpow rho (-1 / 2 : ℝ) := by
    have hsqrtEq :
        Real.sqrt rho = Real.rpow rho (1 / 2 : ℝ) :=
      Real.sqrt_eq_rpow rho
    calc
      1 / Real.sqrt rho =
          (Real.rpow rho (1 / 2 : ℝ))⁻¹ := by
        rw [hsqrtEq, one_div]
      _ = Real.rpow rho (-(1 / 2 : ℝ)) :=
        (Real.rpow_neg hrho.le (1 / 2 : ℝ)).symm
      _ = Real.rpow rho (-1 / 2 : ℝ) := by
        congr 1
        ring
  have hyLayers :
      ((wz1Lemma23SnappedYLayers residue.cells).card : ℝ) ≤
        yLayerUpper := by
    have h :=
      wz1Lemma23_y_layer_count_of_coord
        hrho hrho_one hcoord
        residue.cells_active residue.y_separated
    rw [show (4 / Real.sqrt rho : ℝ) =
      4 * Real.rpow rho (-1 / 2 : ℝ) by
        rw [div_eq_mul_inv, ← one_div, hsqrtInv]] at h
    exact h
  have hratioRpow :
      Real.rpow (Real.sqrt rho / rho) (1 - sigma) =
        Real.rpow rho (-(1 - sigma) / 2) :=
    wz1Lemma23_sqrt_div_rho_rpow
      (rho := rho) (sigma := sigma) hrho
  have hbinPower :
      C.toReal *
          Real.rpow (Real.sqrt rho / rho) (1 - sigma) ≤
        Real.rpow rho
          (-(1 - sigma) / 2 - constantLoss) := by
    rw [hratioRpow]
    have hrpowNonneg :
        0 ≤ Real.rpow rho (-(1 - sigma) / 2) :=
      Real.rpow_nonneg hrho.le _
    calc
      C.toReal * Real.rpow rho (-(1 - sigma) / 2)
          ≤ Real.rpow rho (-constantLoss) *
              Real.rpow rho (-(1 - sigma) / 2) := by
        exact mul_le_mul_of_nonneg_right hCpower hrpowNonneg
      _ = Real.rpow rho
          (-(1 - sigma) / 2 - constantLoss) := by
        calc
          Real.rpow rho (-constantLoss) *
                Real.rpow rho (-(1 - sigma) / 2)
              = Real.rpow rho
                  ((-constantLoss) + (-(1 - sigma) / 2)) :=
            (Real.rpow_add hrho _ _).symm
          _ = Real.rpow rho
              (-(1 - sigma) / 2 - constantLoss) := by
            congr 1
            ring
  have hlocalBins :
      (package.selectedLocal.localBinBound : ℝ) ≤
        localBinUpper := by
    have h :=
      package.selectedLocal.localBinBound_real_le
        hrho hrho_one hsigma hsigma_one hC hCtop
    dsimp only [localBinUpper]
    calc
      (package.selectedLocal.localBinBound : ℝ)
          ≤ 21 * (C.toReal *
            Real.rpow (Real.sqrt rho / rho) (1 - sigma)) := by
        simpa [mul_assoc] using h
      _ ≤ 21 * Real.rpow rho
          (-(1 - sigma) / 2 - constantLoss) := by
        gcongr
  have hheights :
      ((wz1Lemma23SnappedHeights residue.cells).card : ℝ) ≤
        heightUpper := by
    have h :=
      wz1Lemma23_height_layer_count
        hrho hrho_one
        (windowed.residue_cells_window residue)
    rw [show (3 / Real.sqrt rho : ℝ) =
      3 * Real.rpow rho (-1 / 2 : ℝ) by
        rw [div_eq_mul_inv, ← one_div, hsqrtInv]] at h
    exact h
  have hglobalBins :
      (localized.globalBinBound : ℝ) ≤
        globalBinUpper := by
    have h :=
      localized.globalBinBound_real_le
        hrho_one hsigma hsigma_one hC hCtop
    dsimp only [globalBinUpper]
    calc
      (localized.globalBinBound : ℝ)
          ≤ 35 * (C.toReal *
            Real.rpow (Real.sqrt rho / rho) (1 - sigma)) := by
        simpa [mul_assoc] using h
      _ ≤ 35 * Real.rpow rho
          (-(1 - sigma) / 2 - constantLoss) := by
        gcongr
  have hbudget :
      target *
          ((yLayerUpper * localBinUpper) ^ 2 *
            (heightUpper ^ 2 * globalBinUpper) *
            (heightUpper * globalBinUpper) * 16) ≤
        cellLower ^ 4 := by
    have heq :=
      wz1Lemma23_power_budget
        (rho := rho) (sigma := sigma)
        (volumeLoss := volumeLoss + extraLoss)
        (constantLoss := constantLoss) hrho
    dsimp only [target, cellLower, yLayerUpper,
      localBinUpper, heightUpper, globalBinUpper]
    have htargetExp :
        -3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss =
          -3 / 2 + 4 * (volumeLoss + extraLoss) + 4 * constantLoss := by ring
    have hcellExp :
        -3 / 2 + sigma / 2 + volumeLoss + extraLoss =
          -3 / 2 + sigma / 2 + (volumeLoss + extraLoss) := by ring
    rw [htargetExp, hcellExp]
    exact heq.le
  exact
    package.edge_cardinality_from_bounds
      cellLower yLayerUpper localBinUpper
      heightUpper globalBinUpper target
      hcellLower hyLayerUpper hlocalBinUpper
      hheightUpper hglobalBinUpper
      hcells hyLayers hlocalBins hheights hglobalBins hbudget

/-- Historical unit-ball wrapper for the paper-coordinate-crop edge bound. -/
theorem WZ1Lemma23LocalizedPreparedPackage.power_edge_bound
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) Y C}
    {localized : WZ1Lemma23LocalizedGlobalBinPackage windowed.global}
    {residue : WZ1Lemma23YResiduePackage windowed.global}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C windowed.global.cells}
    (package : WZ1Lemma23LocalizedPreparedPackage
      windowed localized residue localBins)
    (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    (hC : 1 ≤ C) (hCtop : C ≠ ⊤)
    (volumeLoss constantLoss extraLoss : ℝ)
    (hvolume :
      ENNReal.ofReal (Real.rpow rho (1 + sigma / 2 + volumeLoss)) ≤
        MeasureTheory.volume Y.union)
    (hCpower : C.toReal ≤ Real.rpow rho (-constantLoss))
    (hextraPower :
      (residue.extraCost : ℝ) ≤ Real.rpow rho (-extraLoss)) :
    (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
        Real.rpow rho
          (-3 / 2 + 4 * volumeLoss + 4 * constantLoss +
            4 * extraLoss) ≤
      (package.normalized.H.card : ℝ) := by
  apply package.power_edge_bound_of_coord
    hrho_one hsigma hsigma_one _ hC hCtop
    volumeLoss constantLoss extraLoss hvolume hCpower hextraPower
  intro point hpoint coordinate
  have hnorm : ‖point‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hball hpoint
  exact (PiLp.norm_apply_le point coordinate).trans hnorm

end

end Kakeya.Assouad
