import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallOrderedPairSqrtScale
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# Family-free balancing-boundary absorption for a four-call pair

At the final requested scale `sqrt rho`, the boundary square-root contributes
the exact gain `rho^(1/4)`.  This module absorbs the remaining fixed constant
using only the numerical hypothesis `middleLoss < 1/8`; no Phase-1 lower
window or runtime-selected object is used.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- A family-free cutoff for the balancing-boundary inequality at the exact
square-root requested scale. -/
structure Proposition63FourCallBalancingBoundaryAbsorptionData
    (middleLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one_div_144 : delta₀ ≤ 1 / 144
  absorb : ∀ {rho : ℝ}, 0 < rho → rho ≤ delta₀ →
    ∀ sqrtRequested : WZ2PaperRequestedScale rho,
      sqrtRequested.1 = Real.sqrt rho →
      2 * 24000000 *
          (Kakeya.realRpowENN rho (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (rho / sqrtRequested.1)) <
        Kakeya.realRpowENN rho middleLoss

/-- Choose the balancing-boundary cutoff before the family and runtime.
The strict upper bound `middleLoss < 1/8` is exactly the positive-exponent
condition left after the square-root requested scale supplies a `1/4` gain. -/
theorem proposition63_four_call_balancing_boundary_absorption
    (middleLoss : ℝ) (hmiddleLoss : 0 < middleLoss)
    (hmiddleLoss_lt : middleLoss < 1 / 8) :
    Nonempty (Proposition63FourCallBalancingBoundaryAbsorptionData
      middleLoss) := by
  let gain : ℝ := 1 / 4
  let gap : ℝ := gain - 2 * middleLoss
  have gapPos : 0 < gap := by
    dsimp only [gap, gain]
    linarith
  let fixed : ENNReal :=
    (2 : ENNReal) * 24000000 * (wz2PaperBoundaryGeometryConstant + 1)
  have fixedTop : fixed ≠ ⊤ := by
    dsimp only [fixed, wz2PaperBoundaryGeometryConstant]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (by norm_num))
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top,
          by norm_num⟩)
  rcases exists_delta_realRpowENN_bound fixed fixedTop
      (show 0 < gap / 2 by positivity) with
    ⟨constantDelta, constantDeltaPos, constantDeltaOne, constantAbsorb⟩
  let delta₀ : ℝ :=
    min constantDelta (min (1 / 144) (Real.exp (-1)))
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min constantDeltaPos
      (lt_min (by norm_num) (by positivity))
    delta₀_le_one_div_144 :=
      (min_le_right constantDelta _).trans (min_le_left _ _)
    absorb := ?_
  }⟩
  intro rho rhoPos rhoLe sqrtRequested hsqrtRequested
  have rhoLeConstant : rho ≤ constantDelta :=
    rhoLe.trans (min_le_left _ _)
  have rhoOne : rho ≤ 1 := rhoLeConstant.trans constantDeltaOne
  have rhoLtOne : rho < 1 :=
    rhoLe.trans_lt <| (min_le_right _ _).trans_lt <|
      (min_le_right _ _).trans_lt
        (Real.exp_lt_one_iff.mpr (by norm_num))
  have ratioPower : rho / Real.sqrt rho = rho ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      rho / rho ^ (1 / 2 : ℝ) =
          rho ^ (1 - (1 / 2 : ℝ)) := by
        simpa only [Real.rpow_one] using
          (Real.rpow_sub rhoPos (1 : ℝ) (1 / 2 : ℝ)).symm
      _ = rho ^ (1 / 2 : ℝ) := by norm_num
  have rootPowerReal :
      Real.sqrt (rho / sqrtRequested.1) = Real.rpow rho gain := by
    rw [hsqrtRequested, ratioPower, Real.sqrt_eq_rpow]
    calc
      (rho ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) =
          rho ^ ((1 / 2 : ℝ) * (1 / 2 : ℝ)) :=
        (Real.rpow_mul rhoPos.le (1 / 2 : ℝ) (1 / 2 : ℝ)).symm
      _ = Real.rpow rho gain := by
        congr 1
        norm_num [gain]
  have rootPower :
      ENNReal.ofReal (Real.sqrt (rho / sqrtRequested.1)) =
        Kakeya.realRpowENN rho gain := by
    rw [rootPowerReal]
    rfl
  have oneLeNegative :
      (1 : ENNReal) ≤ Kakeya.realRpowENN rho (-middleLoss) := by
    rw [Kakeya.realRpowENN, ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_mono
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      rhoPos rhoOne (by linarith)
  have bracketBound :
      Kakeya.realRpowENN rho (-middleLoss) *
            wz2PaperBoundaryGeometryConstant + 1 ≤
        Kakeya.realRpowENN rho (-middleLoss) *
          (wz2PaperBoundaryGeometryConstant + 1) := by
    calc
      Kakeya.realRpowENN rho (-middleLoss) *
            wz2PaperBoundaryGeometryConstant + 1 ≤
          Kakeya.realRpowENN rho (-middleLoss) *
              wz2PaperBoundaryGeometryConstant +
            Kakeya.realRpowENN rho (-middleLoss) := by gcongr
      _ = Kakeya.realRpowENN rho (-middleLoss) *
          (wz2PaperBoundaryGeometryConstant + 1) := by ring
  have fixedAbsorb :
      fixed ≤ Kakeya.realRpowENN rho (-(gap / 2)) :=
    constantAbsorb rho rhoPos rhoLeConstant
  have exponentIdentity :
      -(gap / 2) + (-middleLoss) + gain =
        middleLoss + gap / 2 := by
    dsimp only [gap]
    ring
  have powerStrict :
      Kakeya.realRpowENN rho (middleLoss + gap / 2) <
        Kakeya.realRpowENN rho middleLoss := by
    apply (ENNReal.ofReal_lt_ofReal_iff
      (Real.rpow_pos_of_pos rhoPos middleLoss)).2
    exact Real.rpow_lt_rpow_of_exponent_gt rhoPos rhoLtOne (by
      linarith [gapPos])
  calc
    2 * 24000000 *
          (Kakeya.realRpowENN rho (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (rho / sqrtRequested.1)) ≤
        fixed * Kakeya.realRpowENN rho (-middleLoss) *
          Kakeya.realRpowENN rho gain := by
      rw [rootPower]
      dsimp only [fixed]
      calc
        2 * 24000000 *
              (Kakeya.realRpowENN rho (-middleLoss) *
                  wz2PaperBoundaryGeometryConstant + 1) *
              Kakeya.realRpowENN rho gain ≤
            2 * 24000000 *
              (Kakeya.realRpowENN rho (-middleLoss) *
                (wz2PaperBoundaryGeometryConstant + 1)) *
              Kakeya.realRpowENN rho gain := by gcongr
        _ = (2 * 24000000 *
              (wz2PaperBoundaryGeometryConstant + 1)) *
            Kakeya.realRpowENN rho (-middleLoss) *
              Kakeya.realRpowENN rho gain := by ring
    _ ≤ Kakeya.realRpowENN rho (-(gap / 2)) *
          Kakeya.realRpowENN rho (-middleLoss) *
            Kakeya.realRpowENN rho gain := by
      exact mul_le_mul_left (mul_le_mul_left fixedAbsorb _) _
    _ = Kakeya.realRpowENN rho (middleLoss + gap / 2) := by
      rw [← realRpowENN_add rhoPos, ← realRpowENN_add rhoPos]
      rw [exponentIdentity]
    _ < Kakeya.realRpowENN rho middleLoss := powerStrict

end Kakeya.Assouad.PureWZ2
