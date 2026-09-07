import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryLineConflictPacking
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PreselectedSeparatedCallerMerge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.BoundedSourceCardLog
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Uniform thresholds for terminal selected post-deletion production

The selected-only terminal route pays three logarithmic losses before fixed
balancing: caller-weight preselection, complete-parent regularization, and
ordinary source separation.  The caller-center coloring uses the fixed
geometric conflict degree, so its color-vector factor is a genuine constant
rather than a negative power of the runtime scale.

This module freezes one combined balancing loss and all scale cutoffs before
the runtime family is known.  Runtime `inputLoss` only determines the split
between the normalized source loss and the remaining selection loss.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The fixed caller-center degree, duplicated here as a scalar definition so
the threshold receipt remains independent of the geometric coloring proof. -/
def pureWZ2ReentrantTerminalUniformConflictDegree : ℕ :=
  max
    ((2 * 76000 + 1) ^ 2 *
      (2 * 364800 + 1) *
      (2 * 60800 + 1) ^ 2)
    ((2 * 132864 + 1) ^ 3 *
      (2 * 64000 + 1) ^ 3)

/-- Fixed loss of the two-coordinate uniform caller-color vector and its
weight-band selection. -/
def pureWZ2ReentrantTerminalUniformPreselectionCoefficient : ENNReal :=
  ((pureWZ2ReentrantTerminalUniformConflictDegree + 1 : ℕ) : ENNReal) ^ 2 * 8

/-- Fixed coefficient in the complete selected-and-separated mass ledger.
Each of its three family-dependent factors has logarithmic degree three. -/
def pureWZ2ReentrantTerminalSelectedPostDeletionLossCoefficient : ENNReal :=
  (pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
    pureWZ2ReentrantTerminalUniformPreselectionCoefficient *
    8 * (pureWZ2OrdinarySeparationLoss * 8)

/-- Fixed coefficient in one parentwise source-separation loss. -/
def pureWZ2ReentrantTerminalSeparationCoefficient : ENNReal :=
  pureWZ2OrdinarySeparationLoss * 8

/-- One logarithmic coefficient valid both for ordinary centered-containment
distinct source families and for the later line-separated balancing families. -/
def pureWZ2ReentrantTerminalSelectedPostDeletionLogCoefficient : ℝ :=
  max wz2PaperBoundaryLogCoefficient
    pureWZ2BoundedSourceCardLogConstant

def pureWZ2ReentrantTerminalSelectedPostDeletionEnvelope
    (delta : ℝ) : ENNReal :=
  ENNReal.ofReal
    (pureWZ2ReentrantTerminalSelectedPostDeletionLogCoefficient *
      (1 + Real.log delta⁻¹))

theorem pureWZ2ReentrantTerminalSelectedPostDeletionLossCoefficient_ne_top :
    pureWZ2ReentrantTerminalSelectedPostDeletionLossCoefficient ≠ ⊤ := by
  unfold pureWZ2ReentrantTerminalSelectedPostDeletionLossCoefficient
    pureWZ2ReentrantTerminalUniformPreselectionCoefficient
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        ENNReal.coe_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.pow_ne_top ENNReal.coe_ne_top)
          (by norm_num)))
      (by norm_num))
    (ENNReal.mul_ne_top
      (by
        unfold pureWZ2OrdinarySeparationLoss
        exact ENNReal.coe_ne_top)
      (by norm_num))

theorem pureWZ2ReentrantTerminalSeparationCoefficient_ne_top :
    pureWZ2ReentrantTerminalSeparationCoefficient ≠ ⊤ := by
  unfold pureWZ2ReentrantTerminalSeparationCoefficient
    pureWZ2OrdinarySeparationLoss
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top (by norm_num)

/-- The source-independent receipt consumed by selected post-deletion
production.  The fixed separation exponent is eight: three logarithmic
powers are bounded by `log^6`, while the fixed coefficient is bounded by
`log^2`. -/
structure PureWZ2ReentrantTerminalSelectedPostDeletionThresholds
    (internalLossCeiling publicLoss : ℝ) where
  combinedLoss : ℝ
  combinedLoss_eq : combinedLoss = publicLoss / 32
  selectionLossFloor : ℝ
  selectionLossFloor_eq :
    selectionLossFloor = combinedLoss - internalLossCeiling
  selectionLossFloor_pos : 0 < selectionLossFloor
  numerical :
    WZ2PaperFinalGeometricNumericalData
      combinedLoss publicLoss publicLoss 0 0
  separationExponent : ℕ
  separationExponent_eq : separationExponent = 8
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_numerical : delta₀ ≤ numerical.delta₀
  delta₀_final : delta₀ ≤ pureWZ2PostDeletionFinalBalancingScale
  delta₀_le_twenty_four : delta₀ ≤ 1 / 24
  periodic_scale :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      50 * delta ≤ Real.rpow delta (1 - publicLoss)
  selection_absorption :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      Kakeya.realRpowENN delta selectionLossFloor *
          (pureWZ2ReentrantTerminalSelectedPostDeletionLossCoefficient *
            pureWZ2ReentrantTerminalSelectedPostDeletionEnvelope delta ^ 9) ≤
        1
  separation_absorption :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      wz1PaperRefinementFraction delta separationExponent *
          (pureWZ2ReentrantTerminalSeparationCoefficient *
            pureWZ2ReentrantTerminalSelectedPostDeletionEnvelope delta ^ 3) ≤
        1

/-- Select the complete selected post-deletion threshold receipt before the
runtime source family. -/
theorem pureWZ2_reentrantTerminal_selectedPostDeletionThresholds
    {internalLossCeiling publicLoss : ℝ}
    (internalLossCeiling_pos : 0 < internalLossCeiling)
    (publicLoss_pos : 0 < publicLoss)
    (internalLossCeiling_le : internalLossCeiling ≤ publicLoss / 100) :
    Nonempty
      (PureWZ2ReentrantTerminalSelectedPostDeletionThresholds
        internalLossCeiling publicLoss) := by
  let selectionLossFloor := publicLoss / 32 - internalLossCeiling
  let combinedLoss := internalLossCeiling + selectionLossFloor
  have selectionLossFloorPos : 0 < selectionLossFloor := by
    dsimp only [selectionLossFloor]
    linarith
  have sourcePublicGap :
      16 * (internalLossCeiling + selectionLossFloor) < publicLoss := by
    dsimp only [selectionLossFloor]
    linarith
  rcases
      pureWZ2_postDeletion_fixed_balancing_input_uniform_scales
        internalLossCeiling selectionLossFloor publicLoss
        internalLossCeiling_pos selectionLossFloorPos publicLoss_pos
        sourcePublicGap
    with
    ⟨numerical, balancingScale, balancingScalePos, balancingScaleOne,
      balancingNumerical, balancingFinal, balancingTwentyFour,
      balancingPeriodic⟩
  have boundaryNonnegative : 0 ≤ wz2PaperBoundaryLogCoefficient := by
    unfold wz2PaperBoundaryLogCoefficient
    positivity
  have logCoefficientNonnegative :
      0 ≤ pureWZ2ReentrantTerminalSelectedPostDeletionLogCoefficient := by
    exact boundaryNonnegative.trans (le_max_left _ _)
  rcases
      exists_delta_C_pow_log_absorbed_ennreal
        pureWZ2ReentrantTerminalSelectedPostDeletionLossCoefficient
        pureWZ2ReentrantTerminalSelectedPostDeletionLossCoefficient_ne_top
        pureWZ2ReentrantTerminalSelectedPostDeletionLogCoefficient
        logCoefficientNonnegative
        selectionLossFloorPos (show 0 < (9 : ℕ) by norm_num)
    with
    ⟨selectionScale, selectionScalePos, selectionScaleOne,
      selectionBound⟩
  let separationLogCoefficient :=
    max pureWZ2ReentrantTerminalSelectedPostDeletionLogCoefficient
      pureWZ2ReentrantTerminalSeparationCoefficient.toReal
  have separationLogCoefficientNonnegative :
      0 ≤ separationLogCoefficient := by
    exact logCoefficientNonnegative.trans (le_max_left _ _)
  rcases
      exists_delta_boundary_log_square
        separationLogCoefficient separationLogCoefficientNonnegative
    with
    ⟨separationScale, separationScalePos, separationScaleOne,
      separationBound⟩
  let delta₀ := min balancingScale (min selectionScale separationScale)
  have delta₀Pos : 0 < delta₀ := by
    exact lt_min balancingScalePos
      (lt_min selectionScalePos separationScalePos)
  have delta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans balancingScaleOne
  refine
    ⟨{
      combinedLoss := combinedLoss
      combinedLoss_eq := by
        dsimp only [combinedLoss, selectionLossFloor]
        ring
      selectionLossFloor := selectionLossFloor
      selectionLossFloor_eq := by
        dsimp only [combinedLoss]
        ring
      selectionLossFloor_pos := selectionLossFloorPos
      numerical := numerical
      separationExponent := 8
      separationExponent_eq := rfl
      delta₀ := delta₀
      delta₀_pos := delta₀Pos
      delta₀_le_one := delta₀One
      delta₀_numerical :=
        (min_le_left _ _).trans balancingNumerical
      delta₀_final :=
        (min_le_left _ _).trans balancingFinal
      delta₀_le_twenty_four :=
        (min_le_left _ _).trans balancingTwentyFour
      periodic_scale := ?_
      selection_absorption := ?_
      separation_absorption := ?_
    }⟩
  · intro delta hdelta hdeltaSmall
    exact balancingPeriodic delta hdelta
      (hdeltaSmall.trans (min_le_left _ _))
  · intro delta hdelta hdeltaSmall
    have hselectionSmall : delta ≤ selectionScale :=
      hdeltaSmall.trans <|
        (min_le_right _ _).trans (min_le_left _ _)
    have hbound := selectionBound delta hdelta hselectionSmall
    have hbound' :
        pureWZ2ReentrantTerminalSelectedPostDeletionLossCoefficient *
            pureWZ2ReentrantTerminalSelectedPostDeletionEnvelope delta ^ 9 ≤
          Kakeya.realRpowENN delta (-selectionLossFloor) := by
      simpa only [
        pureWZ2ReentrantTerminalSelectedPostDeletionEnvelope] using hbound
    calc
      Kakeya.realRpowENN delta selectionLossFloor *
            (pureWZ2ReentrantTerminalSelectedPostDeletionLossCoefficient *
              pureWZ2ReentrantTerminalSelectedPostDeletionEnvelope delta ^ 9) ≤
          Kakeya.realRpowENN delta selectionLossFloor *
            Kakeya.realRpowENN delta (-selectionLossFloor) := by
        gcongr
      _ = 1 := by
        rw [← realRpowENN_add hdelta]
        simp [Kakeya.realRpowENN]
  · intro delta hdelta hdeltaSmall
    have hseparationSmall : delta ≤ separationScale :=
      hdeltaSmall.trans <|
        (min_le_right _ _).trans (min_le_right _ _)
    have hlog := separationBound delta hdelta hseparationSmall
    let logScale : ENNReal := ENNReal.ofReal (Real.log delta⁻¹)
    have hlogPos : 0 < Real.log delta⁻¹ := by
      linarith [hlog.1]
    have hlogZero : logScale ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hlogPos).ne'
    have hlogTop : logScale ≠ ⊤ := ENNReal.ofReal_ne_top
    have envelopeLe :
        pureWZ2ReentrantTerminalSelectedPostDeletionEnvelope delta ≤
          logScale ^ 2 := by
      unfold pureWZ2ReentrantTerminalSelectedPostDeletionEnvelope
      calc
        ENNReal.ofReal
              (pureWZ2ReentrantTerminalSelectedPostDeletionLogCoefficient *
                (1 + Real.log delta⁻¹)) ≤
            ENNReal.ofReal
              (separationLogCoefficient *
                (1 + Real.log delta⁻¹)) := by
          apply ENNReal.ofReal_mono
          gcongr
          exact le_max_left _ _
        _ ≤ ENNReal.ofReal ((Real.log delta⁻¹) ^ 2) :=
          ENNReal.ofReal_mono hlog.2
        _ = logScale ^ 2 := by
          dsimp only [logScale]
          rw [← ENNReal.ofReal_pow hlogPos.le]
    have coefficientLe :
        pureWZ2ReentrantTerminalSeparationCoefficient ≤
          logScale ^ 2 := by
      rw [← ENNReal.ofReal_toReal
        pureWZ2ReentrantTerminalSeparationCoefficient_ne_top]
      calc
        ENNReal.ofReal
              pureWZ2ReentrantTerminalSeparationCoefficient.toReal ≤
            ENNReal.ofReal
              (separationLogCoefficient *
                (1 + Real.log delta⁻¹)) := by
          apply ENNReal.ofReal_mono
          calc
            pureWZ2ReentrantTerminalSeparationCoefficient.toReal ≤
                separationLogCoefficient :=
              le_max_right _ _
            _ ≤
                separationLogCoefficient *
                  (1 + Real.log delta⁻¹) := by
              nlinarith [hlog.1, separationLogCoefficientNonnegative]
        _ ≤ ENNReal.ofReal ((Real.log delta⁻¹) ^ 2) :=
          ENNReal.ofReal_mono hlog.2
        _ = logScale ^ 2 := by
          dsimp only [logScale]
          rw [← ENNReal.ofReal_pow hlogPos.le]
    have hlogEq :
        Real.log (1 / delta) = Real.log delta⁻¹ := by
      congr 1
      field_simp [hdelta.ne']
    have fractionEq :
        wz1PaperRefinementFraction delta (8 : ℕ) = logScale⁻¹ ^ 8 := by
      unfold wz1PaperRefinementFraction
      rw [hlogEq]
    rw [fractionEq]
    calc
      logScale⁻¹ ^ 8 *
            (pureWZ2ReentrantTerminalSeparationCoefficient *
              pureWZ2ReentrantTerminalSelectedPostDeletionEnvelope delta ^ 3) ≤
          logScale⁻¹ ^ 8 * (logScale ^ 2 * (logScale ^ 2) ^ 3) := by
        gcongr
      _ = (logScale⁻¹ * logScale) ^ 8 := by ring
      _ = 1 := by
        rw [ENNReal.inv_mul_cancel hlogZero hlogTop]
        norm_num

end Kakeya.Assouad

end
