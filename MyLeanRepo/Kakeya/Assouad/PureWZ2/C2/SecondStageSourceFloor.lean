import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleTwoScaleSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Section6CoverAdapter
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGridCubeVolume
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Source-volume floors in the second sticky balanced cover

Proposition 5 supplies an extremal fine refinement and an extremal coarse
cover on the same balanced configuration.  Their exact cell-count identity
turns those two volume bounds into a lower bound for every active coarse
cell.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- Exact balanced-cover cancellation before simplifying square-root powers. -/
theorem PureWZ2OneScaleTwoScaleStickyData.second_source_floor_raw
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent) :
    Kakeya.realRpowENN twoScale.rhoRequested.1
          (sigma + outputLoss) *
        MeasureTheory.volume
          (wz1PaperGridCube twoScale.sqrtRequested.1 (0, 0, 0)) ≤
      Kakeya.realRpowENN twoScale.sqrtRequested.1
          (sigma - outputLoss) *
        twoScale.fine.balanced.cellMass := by
  let balanced := twoScale.fine.balanced.toWZ1PaperBalancedCoverData
  let count : ENNReal := balanced.activeCells.card
  let cubeVolume := MeasureTheory.volume
    (wz1PaperGridCube twoScale.sqrtRequested.1 (0, 0, 0))
  let fineVolume := MeasureTheory.volume twoScale.fine.refined.union
  let coarseVolume :=
    MeasureTheory.volume twoScale.fine.croppedCoarseShading.union
  have hfine :
      Kakeya.realRpowENN twoScale.rhoRequested.1
          (sigma + outputLoss) ≤ fineVolume := by
    exact twoScale.fine.refined_volume_lower
  have hcoarse :
      coarseVolume ≤
        Kakeya.realRpowENN twoScale.sqrtRequested.1
          (sigma - outputLoss) := by
    exact twoScale.fine.coarse_extremal.volume_upper
  have hfineEq : fineVolume = count * balanced.cellMass := by
    exact balanced.fine_union_volume
  have hcoarseEq : coarseVolume = count * cubeVolume := by
    exact balanced.coarse_union_volume
      twoScale.fine.coarse_extremal.delta_pos
  have hscaled :
      count *
          (Kakeya.realRpowENN twoScale.rhoRequested.1
            (sigma + outputLoss) * cubeVolume) ≤
        count *
          (Kakeya.realRpowENN twoScale.sqrtRequested.1
            (sigma - outputLoss) * balanced.cellMass) := by
    calc
      count *
            (Kakeya.realRpowENN twoScale.rhoRequested.1
              (sigma + outputLoss) * cubeVolume) =
          Kakeya.realRpowENN twoScale.rhoRequested.1
              (sigma + outputLoss) *
            (count * cubeVolume) := by ring
      _ = Kakeya.realRpowENN twoScale.rhoRequested.1
              (sigma + outputLoss) * coarseVolume := by rw [← hcoarseEq]
      _ ≤ fineVolume *
            Kakeya.realRpowENN twoScale.sqrtRequested.1
              (sigma - outputLoss) := by gcongr
      _ = count *
            (Kakeya.realRpowENN twoScale.sqrtRequested.1
              (sigma - outputLoss) * balanced.cellMass) := by
        rw [hfineEq]
        ring
  have hcountZero : count ≠ 0 := by
    have hnonempty : balanced.activeCells.Nonempty := by
      by_contra hempty
      have hcells : balanced.activeCells = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hempty
      have hzero : fineVolume = 0 := by simp [hfineEq, count, hcells]
      have hpositive :
          0 < Kakeya.realRpowENN twoScale.rhoRequested.1
            (sigma + outputLoss) :=
        ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos
            twoScale.coarseGrains.extremal.delta_pos _)
      rw [hzero] at hfine
      exact (not_le_of_gt hpositive) hfine
    change (balanced.activeCells.card : ENNReal) ≠ 0
    exact_mod_cast Finset.card_ne_zero.mpr hnonempty
  have hcountTop : count ≠ ⊤ := by
    simp [count]
  have hcellMass : balanced.cellMass = twoScale.fine.balanced.cellMass := rfl
  rw [hcellMass] at hscaled
  apply (ENNReal.mul_le_mul_iff_left hcountZero hcountTop).mp
  convert hscaled using 1 <;>
    dsimp only [count, cubeVolume] <;> ring

/-- Every active second-stage source has the paper `rho^(3/2+sigma/2)` floor. -/
theorem PureWZ2OneScaleTwoScaleStickyData.second_source_floor_power
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent) :
    Kakeya.realRpowENN twoScale.rhoRequested.1
        (3 / 2 + sigma / 2 + 3 * outputLoss / 2) ≤
      twoScale.fine.balanced.cellMass := by
  let scale := twoScale.rhoRequested.1
  have hscale : 0 < scale := twoScale.coarseGrains.extremal.delta_pos
  have hsqrt : twoScale.sqrtRequested.1 = Real.sqrt scale := by
    calc
      twoScale.sqrtRequested.1 = Real.sqrt rho := twoScale.sqrtRequested_eq
      _ = Real.sqrt scale := by
        congr 1
        exact twoScale.rhoRequested_eq.symm
  have hcube :
      MeasureTheory.volume
          (wz1PaperGridCube twoScale.sqrtRequested.1 (0, 0, 0)) =
        Kakeya.realRpowENN scale (3 / 2) := by
    rw [wz1PaperGridCube_volume_exact
      twoScale.fine.coarse_extremal.delta_pos, hsqrt]
    simp only [Kakeya.realRpowENN, Real.sqrt_eq_rpow]
    apply congrArg ENNReal.ofReal
    calc
      (Real.rpow scale (1 / 2)) ^ 3 =
          Real.rpow scale ((1 / 2 : ℝ) * (3 : ℕ)) :=
        (Real.rpow_mul_natCast hscale.le (1 / 2) 3).symm
      _ = Real.rpow scale (3 / 2) := by congr 1 <;> ring
  have hcoarsePower :
      Kakeya.realRpowENN twoScale.sqrtRequested.1
          (sigma - outputLoss) =
        Kakeya.realRpowENN scale ((sigma - outputLoss) / 2) := by
    rw [hsqrt]
    simp only [Kakeya.realRpowENN, Real.sqrt_eq_rpow]
    apply congrArg ENNReal.ofReal
    calc
      (Real.rpow scale (1 / 2)).rpow (sigma - outputLoss) =
          Real.rpow scale ((1 / 2) * (sigma - outputLoss)) :=
        (Real.rpow_mul hscale.le (1 / 2) (sigma - outputLoss)).symm
      _ = Real.rpow scale ((sigma - outputLoss) / 2) := by
        congr 1 <;> ring
  have hraw := twoScale.second_source_floor_raw
  rw [hcube, hcoarsePower, ← realRpowENN_add hscale] at hraw
  let denominator :=
    Kakeya.realRpowENN scale ((sigma - outputLoss) / 2)
  have hdenomZero : denominator ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hscale _))
  have hdenomTop : denominator ≠ ⊤ := by
    simp [denominator, Kakeya.realRpowENN]
  have htarget :
      Kakeya.realRpowENN scale
            (3 / 2 + sigma / 2 + 3 * outputLoss / 2) * denominator =
        Kakeya.realRpowENN scale (sigma + outputLoss + 3 / 2) := by
    dsimp only [denominator]
    rw [← realRpowENN_add hscale]
    congr 1
    ring
  apply (ENNReal.mul_le_mul_iff_left hdenomZero hdenomTop).mp
  rw [htarget]
  simpa [denominator, add_comm, add_left_comm, add_assoc, mul_comm] using hraw

end Kakeya.Assouad
