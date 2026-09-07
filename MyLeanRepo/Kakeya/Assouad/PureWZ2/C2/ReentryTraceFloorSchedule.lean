import MyLeanRepo.Kakeya.Assouad.PureWZ2.CroppedCriticalFloorLocalReduction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Uniform scalar schedule for local re-entry critical floors

The ordinary critical floor is selected before any runtime family.  Its
structural loss is split into a density loss and a trace-conversion loss.
At runtime the conversion constant is the corresponding negative power of
`delta`; the CWA and density comparisons are exact power identities, while a
single small-scale threshold absorbs the fixed dense-cubical trace factor.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2ReentryTraceFloorSchedule
    (sigma floorLoss structuralBudget : ℝ) where
  criticalFloor : PureWZ2CriticalFloorSelectionData
    sigma floorLoss structuralBudget
  densityLoss : ℝ := criticalFloor.structuralLoss / 4
  densityLoss_eq : densityLoss = criticalFloor.structuralLoss / 4
  densityLoss_pos : 0 < densityLoss
  densityLoss_le_floor : densityLoss ≤ floorLoss
  traceSourceCeiling : ℝ := criticalFloor.structuralLoss / 8
  traceSourceCeiling_eq :
    traceSourceCeiling = criticalFloor.structuralLoss / 8
  traceSourceCeiling_pos : 0 < traceSourceCeiling
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_floor : delta₀ ≤ criticalFloor.delta₀
  delta₀_le_twelve : delta₀ ≤ 1 / 12
  trace_absorption :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      ∀ traceSourceLoss : ℝ, 0 ≤ traceSourceLoss →
        traceSourceLoss ≤ traceSourceCeiling →
          (Kakeya.realRpowENN delta
              (-(criticalFloor.structuralLoss - densityLoss)))⁻¹ ≤
            (100 : ENNReal)⁻¹ *
              (Kakeya.realRpowENN delta traceSourceLoss / 2)

namespace PureWZ2ReentryTraceFloorSchedule

variable {sigma floorLoss structuralBudget : ℝ}
    (schedule : PureWZ2ReentryTraceFloorSchedule
      sigma floorLoss structuralBudget)

/-- Runtime loss constant used by the local ordinary-trace reduction. -/
def lossConstant (delta : ℝ) : ENNReal :=
  Kakeya.realRpowENN delta
    (-(schedule.criticalFloor.structuralLoss - schedule.densityLoss))

theorem lossConstant_one
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaSmall : delta ≤ schedule.delta₀) :
    1 ≤ schedule.lossConstant delta := by
  unfold lossConstant
  have hdeltaOne := hdeltaSmall.trans schedule.delta₀_le_one
  apply ENNReal.one_le_ofReal.mpr
  apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdeltaOne
  rw [schedule.densityLoss_eq]
  linarith [schedule.criticalFloor.structuralLoss_pos]

theorem lossConstant_ne_top (delta : ℝ) :
    schedule.lossConstant delta ≠ ⊤ := by
  simp [lossConstant, Kakeya.realRpowENN]

theorem cwa_absorption
    {delta : ℝ} (hdelta : 0 < delta) :
    schedule.lossConstant delta *
        Kakeya.realRpowENN delta (-schedule.densityLoss) =
      Kakeya.realRpowENN delta
        (-schedule.criticalFloor.structuralLoss) := by
  unfold lossConstant
  rw [← realRpowENN_add hdelta]
  congr 2
  ring

theorem density_absorption
    {delta : ℝ} (hdelta : 0 < delta) :
    Kakeya.realRpowENN delta schedule.criticalFloor.structuralLoss =
      (schedule.lossConstant delta)⁻¹ *
        Kakeya.realRpowENN delta schedule.densityLoss := by
  unfold lossConstant
  rw [pure_wz2_realRpowENN_inv hdelta, ← realRpowENN_add hdelta]
  congr 2
  ring

end PureWZ2ReentryTraceFloorSchedule

/-- Choose the ordinary floor and every scalar absorption before the runtime
source/re-entry pair is known. -/
theorem PureWZ2CriticalPackage.reentryTraceFloorSchedule
    {sigma floorLoss structuralBudget : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (floorLoss_pos : 0 < floorLoss)
    (structuralBudget_pos : 0 < structuralBudget)
    (structuralBudget_le_floor : structuralBudget ≤ floorLoss) :
    Nonempty (PureWZ2ReentryTraceFloorSchedule
      sigma floorLoss structuralBudget) := by
  rcases critical.select_pure_floor
      (floorLoss := floorLoss) (structuralBudget := structuralBudget)
      floorLoss_pos structuralBudget_pos with ⟨criticalFloor⟩
  let densityLoss := criticalFloor.structuralLoss / 4
  let traceSourceCeiling := criticalFloor.structuralLoss / 8
  let conversionGap := criticalFloor.structuralLoss - densityLoss
  have densityLossPos : 0 < densityLoss := by
    dsimp only [densityLoss]
    linarith [criticalFloor.structuralLoss_pos]
  have densityLossFloor : densityLoss ≤ floorLoss := by
    have hstructuralFloor := criticalFloor.structuralLoss_le.trans
      structuralBudget_le_floor
    dsimp only [densityLoss]
    linarith [criticalFloor.structuralLoss_pos]
  have traceSourceCeilingPos : 0 < traceSourceCeiling := by
    dsimp only [traceSourceCeiling]
    linarith [criticalFloor.structuralLoss_pos]
  have traceGap : traceSourceCeiling < conversionGap := by
    dsimp only [traceSourceCeiling, conversionGap, densityLoss]
    linarith [criticalFloor.structuralLoss_pos]
  rcases exists_scale_absorb_constant (200 : ENNReal) (by norm_num)
      traceSourceCeilingPos.le traceGap with
    ⟨absorptionDelta₀, absorptionDelta₀Pos, absorptionDelta₀One, absorb⟩
  let delta₀ := min criticalFloor.delta₀ (min absorptionDelta₀ (1 / 12))
  have delta₀Pos : 0 < delta₀ := by
    dsimp only [delta₀]
    exact lt_min criticalFloor.delta₀_pos
      (lt_min absorptionDelta₀Pos (by norm_num))
  refine ⟨{
    criticalFloor := criticalFloor
    densityLoss := densityLoss
    densityLoss_eq := rfl
    densityLoss_pos := densityLossPos
    densityLoss_le_floor := densityLossFloor
    traceSourceCeiling := traceSourceCeiling
    traceSourceCeiling_eq := rfl
    traceSourceCeiling_pos := traceSourceCeilingPos
    delta₀ := delta₀
    delta₀_pos := delta₀Pos
    delta₀_le_one := (min_le_left _ _).trans criticalFloor.delta₀_le_one
    delta₀_le_floor := min_le_left _ _
    delta₀_le_twelve := (min_le_right _ _).trans (min_le_right _ _)
    trace_absorption := ?_
  }⟩
  intro delta deltaPos deltaSmall traceSourceLoss traceSourceLossNonneg
    traceSourceLossLe
  have deltaAbsorption : delta ≤ absorptionDelta₀ :=
    deltaSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have absorbed :
      200 * Kakeya.realRpowENN delta (-traceSourceCeiling) ≤
        Kakeya.realRpowENN delta (-conversionGap) :=
    absorb delta deltaPos deltaAbsorption
  have inverted :
      (Kakeya.realRpowENN delta (-conversionGap))⁻¹ ≤
        (200 * Kakeya.realRpowENN delta (-traceSourceCeiling))⁻¹ :=
    ENNReal.inv_le_inv.mpr absorbed
  have sourcePower : Kakeya.realRpowENN delta traceSourceCeiling ≤
      Kakeya.realRpowENN delta traceSourceLoss :=
    pure_wz2_rpowENN_antitone deltaPos
      (deltaSmall.trans ((min_le_left _ _).trans criticalFloor.delta₀_le_one))
      traceSourceLossLe
  have divided : Kakeya.realRpowENN delta conversionGap ≤
      Kakeya.realRpowENN delta traceSourceCeiling / 200 := by
    rw [pure_wz2_realRpowENN_inv deltaPos] at inverted
    rw [ENNReal.mul_inv (Or.inl (by norm_num))
      (Or.inl (by simp))] at inverted
    rw [pure_wz2_realRpowENN_inv deltaPos] at inverted
    simpa [div_eq_mul_inv, mul_comm] using inverted
  rw [pure_wz2_realRpowENN_inv deltaPos]
  have exponentIdentity :
      - -(criticalFloor.structuralLoss - densityLoss) = conversionGap := by
    dsimp only [conversionGap]
    ring
  rw [exponentIdentity]
  calc
    Kakeya.realRpowENN delta conversionGap ≤
        Kakeya.realRpowENN delta traceSourceCeiling / 200 := divided
    _ ≤ Kakeya.realRpowENN delta traceSourceLoss / 200 := by
      exact ENNReal.div_le_div_right sourcePower 200
    _ = (100 : ENNReal)⁻¹ *
        (Kakeya.realRpowENN delta traceSourceLoss / 2) := by
      rw [show (200 : ENNReal) = 100 * 2 by norm_num,
        div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      simp only [div_eq_mul_inv]
      ring

end Kakeya.Assouad

end
