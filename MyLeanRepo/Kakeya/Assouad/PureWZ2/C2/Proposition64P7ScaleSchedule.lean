import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64GeometricEDProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62RequestedScaleScheduleProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CroppedCriticalFloorSelection
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6Absorption

/-!
# Proposition 6.4 target-scale schedule

The final finite grid is a target-side nearby-CWA device.  It is selected
before the runtime source scale and is independent of the cropped critical
volume floor.  The strict gap between source transport, grid rounding, and
the final nearby loss is stored explicitly.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Family-independent P7 losses for target-scale rounding. -/
structure PureWZ2Proposition64P7ScaleSchedule
    (outputLoss : ℝ) where
  outputLoss_pos : 0 < outputLoss
  gridLoss : ℝ
  nearbyLoss : ℝ
  gridLoss_eq : gridLoss = outputLoss / 16
  nearbyLoss_eq : nearbyLoss = 3 * outputLoss / 4
  gridLoss_pos : 0 < gridLoss
  inputCeiling_add_grid_lt_nearby :
    outputLoss / 20 + gridLoss < nearbyLoss
  nearbyLoss_lt_output : nearbyLoss < outputLoss

/-- Minimal interface shared by the production P7 grid and legacy
critical-floor callers that used the floor loss only as a grid step. -/
class PureWZ2Proposition64TargetGrid (Grid : Type*) where
  loss : Grid → ℝ
  loss_pos : ∀ grid, 0 < loss grid

def pureWZ2Proposition64TargetGridLoss
    {Grid : Type*} [PureWZ2Proposition64TargetGrid Grid]
    (grid : Grid) : ℝ :=
  PureWZ2Proposition64TargetGrid.loss grid

theorem pureWZ2Proposition64TargetGridLoss_pos
    {Grid : Type*} [PureWZ2Proposition64TargetGrid Grid]
    (grid : Grid) :
    0 < pureWZ2Proposition64TargetGridLoss grid :=
  PureWZ2Proposition64TargetGrid.loss_pos grid

instance {outputLoss : ℝ} :
    PureWZ2Proposition64TargetGrid
      (PureWZ2Proposition64P7ScaleSchedule outputLoss) where
  loss := PureWZ2Proposition64P7ScaleSchedule.gridLoss
  loss_pos := PureWZ2Proposition64P7ScaleSchedule.gridLoss_pos

instance {sigma floorLoss structuralBudget : ℝ} :
    PureWZ2Proposition64TargetGrid
      (PureWZ2CroppedCriticalFloorSelectionData
        sigma floorLoss structuralBudget) where
  loss := PureWZ2CroppedCriticalFloorSelectionData.structuralLoss
  loss_pos := PureWZ2CroppedCriticalFloorSelectionData.structuralLoss_pos

namespace PureWZ2Proposition64P7ScaleSchedule

/-- A fixed allocation leaving room both for source transport and for the
final nearby-to-public constant absorption. -/
def canonical
    {outputLoss : ℝ}
    (houtputLoss : 0 < outputLoss) :
    PureWZ2Proposition64P7ScaleSchedule outputLoss where
  outputLoss_pos := houtputLoss
  gridLoss := outputLoss / 16
  nearbyLoss := 3 * outputLoss / 4
  gridLoss_eq := rfl
  nearbyLoss_eq := rfl
  gridLoss_pos := div_pos houtputLoss (by norm_num)
  inputCeiling_add_grid_lt_nearby := by
    linarith
  nearbyLoss_lt_output := by
    linarith

theorem nearbyLoss_pos
    {outputLoss : ℝ}
    (schedule : PureWZ2Proposition64P7ScaleSchedule outputLoss) :
    0 < schedule.nearbyLoss :=
  lt_trans (by
    exact add_pos_of_nonneg_of_pos
      (by linarith [schedule.outputLoss_pos])
      schedule.gridLoss_pos)
    schedule.inputCeiling_add_grid_lt_nearby

/-- Runtime source losses below the preselected `outputLoss / 20` ceiling
retain the strict positive rounding gap. -/
theorem inputLoss_add_grid_lt_nearby
    {outputLoss inputLoss : ℝ}
    (schedule : PureWZ2Proposition64P7ScaleSchedule outputLoss)
    (hinputLoss : inputLoss ≤ outputLoss / 20) :
    inputLoss + schedule.gridLoss < schedule.nearbyLoss :=
  lt_of_le_of_lt
    (by
      simpa [add_comm] using
        add_le_add_right hinputLoss schedule.gridLoss)
    schedule.inputCeiling_add_grid_lt_nearby

theorem inputLoss_add_grid_nonnegative_gap
    {outputLoss inputLoss : ℝ}
    (schedule : PureWZ2Proposition64P7ScaleSchedule outputLoss)
    (hinputLoss : inputLoss ≤ outputLoss / 20) :
    0 < schedule.nearbyLoss - inputLoss - schedule.gridLoss := by
  linarith [schedule.inputLoss_add_grid_lt_nearby hinputLoss]

/-- The strict P7 loss gap absorbs the exact transported-quotient constant
uniformly before the runtime source scale and input loss are known. -/
theorem exists_roundingAbsorptionCutoff
    {outputLoss : ℝ}
    (schedule : PureWZ2Proposition64P7ScaleSchedule outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ sourceDelta inputLoss : ℝ,
        0 < sourceDelta → sourceDelta ≤ delta₀ →
        0 ≤ inputLoss → inputLoss ≤ outputLoss / 20 →
        ENNReal.ofReal 57600004 *
            Kakeya.realRpowENN sourceDelta (-inputLoss) *
            Kakeya.realRpowENN
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
              (-schedule.gridLoss) ≤
          Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (-schedule.nearbyLoss) := by
  let scale : ℝ := 45 * pureWZ2Proposition64Lemma35Scale
  let constant : ℝ :=
    57600004 * Real.rpow scale schedule.nearbyLoss
  have hscalePos : 0 < scale := by
    dsimp only [scale]
    exact mul_pos (by norm_num) pureWZ2Proposition64Lemma35Scale_pos
  have hscaleOne : 1 ≤ scale := by
    dsimp only [scale]
    nlinarith [pureWZ2Proposition64Lemma35Scale_one]
  have hconstant : 0 ≤ constant := by
    dsimp only [constant]
    exact mul_nonneg (by norm_num)
      (Real.rpow_nonneg hscalePos.le _)
  have hgap :
      -schedule.nearbyLoss <
        -(outputLoss / 20 + schedule.gridLoss) := by
    linarith [schedule.inputCeiling_add_grid_lt_nearby]
  rcases exists_delta_mul_rpow_le_rpow constant hconstant hgap with
    ⟨delta₀, hdelta₀Pos, hdelta₀One, hcutoff⟩
  refine ⟨delta₀, hdelta₀Pos, hdelta₀One, ?_⟩
  intro sourceDelta inputLoss hsourceDelta hsourceCutoff
    hinputLossNonneg hinputLoss
  have hsourceOne : sourceDelta ≤ 1 :=
    hsourceCutoff.trans hdelta₀One
  have hfinalEq :
      pureWZ2Proposition64Lemma35FinalDelta sourceDelta =
        scale * sourceDelta := by
    rfl
  have hfinalPos :
      0 < pureWZ2Proposition64Lemma35FinalDelta sourceDelta := by
    rw [hfinalEq]
    exact mul_pos hscalePos hsourceDelta
  have hsourceFinal : sourceDelta ≤
      pureWZ2Proposition64Lemma35FinalDelta sourceDelta := by
    rw [hfinalEq]
    nlinarith
  have hinputPower :
      Real.rpow sourceDelta (-inputLoss) ≤
        Real.rpow sourceDelta (-(outputLoss / 20)) := by
    exact Real.rpow_le_rpow_of_exponent_ge hsourceDelta hsourceOne
      (by linarith)
  have hgridPower :
      Real.rpow
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-schedule.gridLoss) ≤
        Real.rpow sourceDelta (-schedule.gridLoss) := by
    exact Real.rpow_le_rpow_of_nonpos hsourceDelta hsourceFinal
      (by linarith [schedule.gridLoss_pos])
  have hsourceCombined :
      Real.rpow sourceDelta (-(outputLoss / 20)) *
          Real.rpow sourceDelta (-schedule.gridLoss) =
        Real.rpow sourceDelta
          (-(outputLoss / 20 + schedule.gridLoss)) := by
    calc
      Real.rpow sourceDelta (-(outputLoss / 20)) *
          Real.rpow sourceDelta (-schedule.gridLoss) =
        Real.rpow sourceDelta
          (-(outputLoss / 20) + -schedule.gridLoss) :=
        (Real.rpow_add hsourceDelta _ _).symm
      _ = Real.rpow sourceDelta
          (-(outputLoss / 20 + schedule.gridLoss)) := by
        congr 1
        ring
  have hleftBound :
      57600004 * Real.rpow sourceDelta (-inputLoss) *
          Real.rpow
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (-schedule.gridLoss) ≤
        57600004 *
          Real.rpow sourceDelta
            (-(outputLoss / 20 + schedule.gridLoss)) := by
    calc
      57600004 * Real.rpow sourceDelta (-inputLoss) *
          Real.rpow
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (-schedule.gridLoss) ≤
          57600004 * Real.rpow sourceDelta (-(outputLoss / 20)) *
            Real.rpow
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
              (-schedule.gridLoss) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hinputPower (by norm_num))
          (Real.rpow_nonneg hfinalPos.le _)
      _ ≤ 57600004 * Real.rpow sourceDelta (-(outputLoss / 20)) *
            Real.rpow sourceDelta (-schedule.gridLoss) := by
        exact mul_le_mul_of_nonneg_left hgridPower
          (mul_nonneg (by norm_num)
            (Real.rpow_nonneg hsourceDelta.le _))
      _ = 57600004 *
          (Real.rpow sourceDelta (-(outputLoss / 20)) *
            Real.rpow sourceDelta (-schedule.gridLoss)) := by ring
      _ = 57600004 *
          Real.rpow sourceDelta
            (-(outputLoss / 20 + schedule.gridLoss)) := by
        rw [hsourceCombined]
  have hscalePowerPos : 0 < Real.rpow scale schedule.nearbyLoss :=
    Real.rpow_pos_of_pos hscalePos _
  have hfinalCancel :
      Real.rpow scale schedule.nearbyLoss *
          Real.rpow
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (-schedule.nearbyLoss) =
        Real.rpow sourceDelta (-schedule.nearbyLoss) := by
    have hmul :
        Real.rpow (scale * sourceDelta) (-schedule.nearbyLoss) =
          Real.rpow scale (-schedule.nearbyLoss) *
            Real.rpow sourceDelta (-schedule.nearbyLoss) :=
      Real.mul_rpow hscalePos.le hsourceDelta.le
    have hscaleCancel :
        Real.rpow scale schedule.nearbyLoss *
            Real.rpow scale (-schedule.nearbyLoss) = 1 := by
      calc
        Real.rpow scale schedule.nearbyLoss *
            Real.rpow scale (-schedule.nearbyLoss) =
          Real.rpow scale
            (schedule.nearbyLoss + -schedule.nearbyLoss) :=
          (Real.rpow_add hscalePos _ _).symm
        _ = 1 := by simp
    rw [hfinalEq, hmul]
    calc
      Real.rpow scale schedule.nearbyLoss *
          (Real.rpow scale (-schedule.nearbyLoss) *
            Real.rpow sourceDelta (-schedule.nearbyLoss)) =
          (Real.rpow scale schedule.nearbyLoss *
            Real.rpow scale (-schedule.nearbyLoss)) *
              Real.rpow sourceDelta (-schedule.nearbyLoss) := by ring
      _ = Real.rpow sourceDelta (-schedule.nearbyLoss) := by
        rw [hscaleCancel, one_mul]
  have hscaled :
      Real.rpow scale schedule.nearbyLoss *
          (57600004 * Real.rpow sourceDelta (-inputLoss) *
            Real.rpow
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
              (-schedule.gridLoss)) ≤
        Real.rpow scale schedule.nearbyLoss *
          Real.rpow
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (-schedule.nearbyLoss) := by
    calc
      Real.rpow scale schedule.nearbyLoss *
          (57600004 * Real.rpow sourceDelta (-inputLoss) *
            Real.rpow
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
              (-schedule.gridLoss)) ≤
          Real.rpow scale schedule.nearbyLoss *
            (57600004 *
              Real.rpow sourceDelta
                (-(outputLoss / 20 + schedule.gridLoss))) := by
        gcongr
      _ = constant *
          Real.rpow sourceDelta
            (-(outputLoss / 20 + schedule.gridLoss)) := by
        simp only [constant]
        ring
      _ ≤ Real.rpow sourceDelta (-schedule.nearbyLoss) :=
        hcutoff sourceDelta hsourceDelta hsourceCutoff
      _ = Real.rpow scale schedule.nearbyLoss *
          Real.rpow
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (-schedule.nearbyLoss) := hfinalCancel.symm
  have hreal :
      57600004 * Real.rpow sourceDelta (-inputLoss) *
          Real.rpow
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (-schedule.gridLoss) ≤
        Real.rpow
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-schedule.nearbyLoss) :=
    (mul_le_mul_iff_of_pos_left hscalePowerPos).mp hscaled
  calc
    ENNReal.ofReal 57600004 *
          Kakeya.realRpowENN sourceDelta (-inputLoss) *
          Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (-schedule.gridLoss) =
        ENNReal.ofReal
          (57600004 * Real.rpow sourceDelta (-inputLoss) *
            Real.rpow
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
              (-schedule.gridLoss)) := by
      simp only [Kakeya.realRpowENN]
      rw [← ENNReal.ofReal_mul (by norm_num)]
      exact (ENNReal.ofReal_mul
        (mul_nonneg (by norm_num)
          (Real.rpow_nonneg hsourceDelta.le _))).symm
    _ ≤ ENNReal.ofReal
          (Real.rpow
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (-schedule.nearbyLoss)) :=
      ENNReal.ofReal_mono hreal
    _ = Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-schedule.nearbyLoss) := rfl

/-- Frozen pre-runtime cutoff associated to one P7 loss allocation. -/
structure RoundingCutoff
    {outputLoss : ℝ}
    (schedule : PureWZ2Proposition64P7ScaleSchedule outputLoss) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorption :
    ∀ sourceDelta inputLoss : ℝ,
      0 < sourceDelta → sourceDelta ≤ delta₀ →
      0 ≤ inputLoss → inputLoss ≤ outputLoss / 20 →
      ENNReal.ofReal 57600004 *
          Kakeya.realRpowENN sourceDelta (-inputLoss) *
          Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (-schedule.gridLoss) ≤
        Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-schedule.nearbyLoss)

theorem exists_roundingCutoff
    {outputLoss : ℝ}
    (schedule : PureWZ2Proposition64P7ScaleSchedule outputLoss) :
    Nonempty schedule.RoundingCutoff := by
  rcases schedule.exists_roundingAbsorptionCutoff with
    ⟨delta₀, hdelta₀Pos, hdelta₀One, absorption⟩
  exact ⟨{
    delta₀ := delta₀
    delta₀_pos := hdelta₀Pos
    delta₀_le_one := hdelta₀One
    absorption := absorption }⟩

/-- Frozen cutoff for the final union-volume upper power conversion. -/
structure VolumeCutoff
    (sigma outputLoss epsilon₂ : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorption :
    ∀ sourceDelta inputLoss : ℝ,
      0 < sourceDelta → sourceDelta ≤ delta₀ →
      0 ≤ inputLoss → inputLoss ≤ epsilon₂ →
      (117 : ENNReal) *
            ENNReal.ofReal
              ((45 * pureWZ2Proposition64Lemma35Scale) ^ 3) *
            Kakeya.realRpowENN sourceDelta (-3 * epsilon₂) *
            Kakeya.realRpowENN sourceDelta (sigma - inputLoss) ≤
        Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (sigma - outputLoss)

/-- A fixed positive gap `outputLoss - 4 * epsilon₂` absorbs the exact
cell-count loss and the source-to-final base change. -/
theorem exists_volumeCutoff
    {sigma outputLoss epsilon₂ : ℝ}
    (_houtputLoss : 0 < outputLoss)
    (_hepsilon₂ : 0 < epsilon₂)
    (hgap : 4 * epsilon₂ < outputLoss) :
    Nonempty (VolumeCutoff sigma outputLoss epsilon₂) := by
  let scale : ℝ := 45 * pureWZ2Proposition64Lemma35Scale
  let fixed : ℝ := 117 * scale ^ 3
  let compensation : ℝ := Real.rpow scale (outputLoss - sigma)
  let constant : ℝ := fixed * compensation
  have hscalePos : 0 < scale := by
    dsimp only [scale]
    exact mul_pos (by norm_num) pureWZ2Proposition64Lemma35Scale_pos
  have hfixedPos : 0 < fixed := by
    dsimp only [fixed]
    positivity
  have hcompensationPos : 0 < compensation :=
    Real.rpow_pos_of_pos hscalePos _
  have hconstant : 0 ≤ constant := by
    dsimp only [constant]
    exact mul_nonneg hfixedPos.le hcompensationPos.le
  have hexponent :
      sigma - outputLoss < sigma - 4 * epsilon₂ := by
    linarith
  rcases exists_delta_mul_rpow_le_rpow
      constant hconstant hexponent with
    ⟨delta₀, hdelta₀Pos, hdelta₀One, hcutoff⟩
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := hdelta₀Pos
    delta₀_le_one := hdelta₀One
    absorption := ?_ }⟩
  intro sourceDelta inputLoss hsourceDelta hsourceCutoff
    hinputLossNonneg hinputLoss
  have hsourceOne : sourceDelta ≤ 1 :=
    hsourceCutoff.trans hdelta₀One
  have hcombined :
      Real.rpow sourceDelta (-3 * epsilon₂) *
          Real.rpow sourceDelta (sigma - inputLoss) =
        Real.rpow sourceDelta (sigma - inputLoss - 3 * epsilon₂) := by
    calc
      Real.rpow sourceDelta (-3 * epsilon₂) *
          Real.rpow sourceDelta (sigma - inputLoss) =
        Real.rpow sourceDelta
          ((-3 * epsilon₂) + (sigma - inputLoss)) :=
        (Real.rpow_add hsourceDelta _ _).symm
      _ = Real.rpow sourceDelta
          (sigma - inputLoss - 3 * epsilon₂) := by
        congr 1
        ring
  have hpower :
      Real.rpow sourceDelta (sigma - inputLoss - 3 * epsilon₂) ≤
        Real.rpow sourceDelta (sigma - 4 * epsilon₂) := by
    exact Real.rpow_le_rpow_of_exponent_ge hsourceDelta hsourceOne
      (by linarith)
  have hfinalEq :
      pureWZ2Proposition64Lemma35FinalDelta sourceDelta =
        scale * sourceDelta := by rfl
  have hfinalCancel :
      compensation *
          Real.rpow
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (sigma - outputLoss) =
        Real.rpow sourceDelta (sigma - outputLoss) := by
    have hmul :
        Real.rpow (scale * sourceDelta) (sigma - outputLoss) =
          Real.rpow scale (sigma - outputLoss) *
            Real.rpow sourceDelta (sigma - outputLoss) :=
      Real.mul_rpow hscalePos.le hsourceDelta.le
    have hscaleCancel :
        compensation * Real.rpow scale (sigma - outputLoss) = 1 := by
      dsimp only [compensation]
      calc
        Real.rpow scale (outputLoss - sigma) *
            Real.rpow scale (sigma - outputLoss) =
          Real.rpow scale
            ((outputLoss - sigma) + (sigma - outputLoss)) :=
          (Real.rpow_add hscalePos _ _).symm
        _ = 1 := by simp
    rw [hfinalEq, hmul]
    calc
      compensation *
          (Real.rpow scale (sigma - outputLoss) *
            Real.rpow sourceDelta (sigma - outputLoss)) =
        (compensation * Real.rpow scale (sigma - outputLoss)) *
          Real.rpow sourceDelta (sigma - outputLoss) := by ring
      _ = Real.rpow sourceDelta (sigma - outputLoss) := by
        rw [hscaleCancel, one_mul]
  have hscaled :
      compensation *
          (fixed * Real.rpow sourceDelta (-3 * epsilon₂) *
            Real.rpow sourceDelta (sigma - inputLoss)) ≤
        compensation *
          Real.rpow
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (sigma - outputLoss) := by
    calc
      compensation *
          (fixed * Real.rpow sourceDelta (-3 * epsilon₂) *
            Real.rpow sourceDelta (sigma - inputLoss)) =
        constant *
          (Real.rpow sourceDelta (-3 * epsilon₂) *
            Real.rpow sourceDelta (sigma - inputLoss)) := by
        dsimp only [constant]
        ring
      _ = constant *
          Real.rpow sourceDelta
            (sigma - inputLoss - 3 * epsilon₂) := by rw [hcombined]
      _ ≤ constant *
          Real.rpow sourceDelta (sigma - 4 * epsilon₂) := by
        exact mul_le_mul_of_nonneg_left hpower hconstant
      _ ≤ Real.rpow sourceDelta (sigma - outputLoss) :=
        hcutoff sourceDelta hsourceDelta hsourceCutoff
      _ = compensation *
          Real.rpow
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (sigma - outputLoss) := hfinalCancel.symm
  have hreal :
      fixed * Real.rpow sourceDelta (-3 * epsilon₂) *
          Real.rpow sourceDelta (sigma - inputLoss) ≤
        Real.rpow
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (sigma - outputLoss) :=
    (mul_le_mul_iff_of_pos_left hcompensationPos).mp hscaled
  calc
    (117 : ENNReal) *
          ENNReal.ofReal
            ((45 * pureWZ2Proposition64Lemma35Scale) ^ 3) *
          Kakeya.realRpowENN sourceDelta (-3 * epsilon₂) *
          Kakeya.realRpowENN sourceDelta (sigma - inputLoss) =
        ENNReal.ofReal
          (fixed * Real.rpow sourceDelta (-3 * epsilon₂) *
            Real.rpow sourceDelta (sigma - inputLoss)) := by
      dsimp only [fixed, scale]
      simp only [Kakeya.realRpowENN]
      rw [show (117 : ENNReal) = ENNReal.ofReal (117 : ℝ) by norm_num]
      rw [← ENNReal.ofReal_mul (by norm_num)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact (ENNReal.ofReal_mul
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (pow_nonneg
              (mul_nonneg (by norm_num)
                pureWZ2Proposition64Lemma35Scale_pos.le) 3))
          (Real.rpow_nonneg hsourceDelta.le _))).symm
    _ ≤ ENNReal.ofReal
          (Real.rpow
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (sigma - outputLoss)) :=
      ENNReal.ofReal_mono hreal
    _ = Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (sigma - outputLoss) := rfl

/-- Generic fixed-constant source-to-final absorption used by both Node-6 and
the Node-5 local/global terminal wrappers. -/
theorem exists_fixedFinalAbsorption
    (constant : ENNReal) (hconstant : constant ≠ ⊤)
    {sourceLoss outputLoss : ℝ}
    (hloss : sourceLoss < outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ sourceDelta : ℝ, 0 < sourceDelta → sourceDelta ≤ delta₀ →
        constant * Kakeya.realRpowENN sourceDelta (-sourceLoss) ≤
          Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (-outputLoss) := by
  let scale : ℝ := 45 * pureWZ2Proposition64Lemma35Scale
  let scalePower : ENNReal := Kakeya.realRpowENN scale outputLoss
  let compensated : ENNReal := scalePower * constant
  have hscale : 0 < scale := by
    dsimp only [scale]
    exact mul_pos (by norm_num) pureWZ2Proposition64Lemma35Scale_pos
  have hscalePowerZero : scalePower ≠ 0 := by
    dsimp only [scalePower, Kakeya.realRpowENN]
    exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hscale _)).ne'
  have hscalePowerTop : scalePower ≠ ⊤ := by
    simp [scalePower, Kakeya.realRpowENN]
  have hcompensated : compensated ≠ ⊤ :=
    ENNReal.mul_ne_top hscalePowerTop hconstant
  rcases exists_delta_constant_mul_power_le_power compensated hcompensated
      (-outputLoss) (-sourceLoss) (by linarith) with
    ⟨delta₀, hdelta₀Pos, hdelta₀One, hbound⟩
  refine ⟨delta₀, hdelta₀Pos, hdelta₀One, ?_⟩
  intro sourceDelta hsourceDelta hsourceSmall
  have hraw := hbound hsourceDelta hsourceSmall
  have hscaleCancel :
      scalePower * Kakeya.realRpowENN scale (-outputLoss) = 1 := by
    dsimp only [scalePower]
    rw [← realRpowENN_add hscale]
    simp [Kakeya.realRpowENN]
  have hfinal :
      scalePower *
          Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (-outputLoss) =
        Kakeya.realRpowENN sourceDelta (-outputLoss) := by
    unfold pureWZ2Proposition64Lemma35FinalDelta
    rw [realRpowENN_mul hscale hsourceDelta]
    calc
      scalePower *
          (Kakeya.realRpowENN scale (-outputLoss) *
            Kakeya.realRpowENN sourceDelta (-outputLoss)) =
        (scalePower * Kakeya.realRpowENN scale (-outputLoss)) *
          Kakeya.realRpowENN sourceDelta (-outputLoss) := by ring
      _ = Kakeya.realRpowENN sourceDelta (-outputLoss) := by
        rw [hscaleCancel, one_mul]
  apply (ENNReal.mul_le_mul_iff_right
    hscalePowerZero hscalePowerTop).mp
  calc
    scalePower *
        (constant * Kakeya.realRpowENN sourceDelta (-sourceLoss)) =
      compensated * Kakeya.realRpowENN sourceDelta (-sourceLoss) := by
        simp only [compensated]
        ring
    _ ≤ Kakeya.realRpowENN sourceDelta (-outputLoss) := hraw
    _ = scalePower *
        Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-outputLoss) := hfinal.symm

/-- Prop-6.5-style terminal cutoff for top-level CWA and the final
global/local grain constants on one target scale. -/
structure TerminalCutoff
    (sourceLoss nearbyLoss outputLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  top_level_absorption :
    ∀ sourceDelta : ℝ, 0 < sourceDelta → sourceDelta ≤ delta₀ →
      (4 : ENNReal) *
          Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (-nearbyLoss) ≤
        Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-outputLoss)
  local_absorption :
    ∀ sourceDelta : ℝ, 0 < sourceDelta → sourceDelta ≤ delta₀ →
      (192 : ENNReal) *
          Kakeya.realRpowENN sourceDelta (-sourceLoss) ≤
        Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-outputLoss)
  global_absorption :
    ∀ sourceDelta : ℝ, 0 < sourceDelta → sourceDelta ≤ delta₀ →
      (7077888 : ENNReal) *
          (24000 * Kakeya.realRpowENN sourceDelta (-sourceLoss)) ≤
        Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-outputLoss)

theorem exists_terminalCutoff
    {sourceLoss nearbyLoss outputLoss : ℝ}
    (hsourceLoss : sourceLoss < outputLoss)
    (hnearbyLoss : nearbyLoss < outputLoss) :
    Nonempty (TerminalCutoff sourceLoss nearbyLoss outputLoss) := by
  let scale : ℝ := 45 * pureWZ2Proposition64Lemma35Scale
  let topConstant : ENNReal :=
    4 * Kakeya.realRpowENN scale (outputLoss - nearbyLoss)
  have hscale : 0 < scale := by
    dsimp only [scale]
    exact mul_pos (by norm_num) pureWZ2Proposition64Lemma35Scale_pos
  have htopConstant : topConstant ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN])
  rcases exists_delta_constant_mul_power_le_power topConstant htopConstant
      0 (outputLoss - nearbyLoss) (by linarith) with
    ⟨topDelta₀, htopPos, htopOne, htop⟩
  rcases exists_fixedFinalAbsorption (192 : ENNReal) (by norm_num)
      hsourceLoss with
    ⟨localDelta₀, hlocalPos, hlocalOne, hlocal⟩
  let globalConstant : ENNReal := 7077888 * 24000
  have hglobalConstant : globalConstant ≠ ⊤ := by
    dsimp only [globalConstant]
    norm_num
  rcases exists_fixedFinalAbsorption globalConstant hglobalConstant
      hsourceLoss with
    ⟨globalDelta₀, hglobalPos, hglobalOne, hglobal⟩
  let delta₀ := min topDelta₀ (min localDelta₀ globalDelta₀)
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min htopPos (lt_min hlocalPos hglobalPos)
    delta₀_le_one := (min_le_left _ _).trans htopOne
    top_level_absorption := ?_
    local_absorption := ?_
    global_absorption := ?_ }⟩
  · intro sourceDelta hsourceDelta hsourceSmall
    have hsmall : sourceDelta ≤ topDelta₀ :=
      hsourceSmall.trans (min_le_left _ _)
    have hbound := htop hsourceDelta hsmall
    have hfinalPower :
        Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (outputLoss - nearbyLoss) =
          Kakeya.realRpowENN scale (outputLoss - nearbyLoss) *
            Kakeya.realRpowENN sourceDelta
              (outputLoss - nearbyLoss) := by
      unfold pureWZ2Proposition64Lemma35FinalDelta
      exact realRpowENN_mul hscale hsourceDelta _
    have hgap :
        (4 : ENNReal) *
            Kakeya.realRpowENN
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
              (outputLoss - nearbyLoss) ≤ 1 := by
      rw [hfinalPower]
      simpa [topConstant, mul_assoc, Kakeya.realRpowENN] using hbound
    have htargetPos :
        Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            outputLoss ≠ 0 := by
      exact (ENNReal.ofReal_pos.mpr <|
        Real.rpow_pos_of_pos
          (by
            unfold pureWZ2Proposition64Lemma35FinalDelta
            positivity) _).ne'
    have htargetTop :
        Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            outputLoss ≠ ⊤ := by
      simp [Kakeya.realRpowENN]
    apply (ENNReal.mul_le_mul_iff_right htargetPos htargetTop).mp
    calc
      Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          outputLoss *
        ((4 : ENNReal) *
          Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (-nearbyLoss)) =
        4 *
          (Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (-nearbyLoss) *
          Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            outputLoss) := by ring
      _ = 4 *
          (Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (outputLoss - nearbyLoss)) := by
        rw [← realRpowENN_add]
        · congr 2 <;> ring
        · unfold pureWZ2Proposition64Lemma35FinalDelta
          positivity
      _ ≤ 1 := hgap
      _ = Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          outputLoss *
        Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-outputLoss) := by
        rw [← realRpowENN_add]
        · simp [Kakeya.realRpowENN]
        · unfold pureWZ2Proposition64Lemma35FinalDelta
          positivity
  · intro sourceDelta hsourceDelta hsourceSmall
    exact hlocal sourceDelta hsourceDelta
      (hsourceSmall.trans <|
        (min_le_right _ _).trans (min_le_left _ _))
  · intro sourceDelta hsourceDelta hsourceSmall
    have hraw := hglobal sourceDelta hsourceDelta
      (hsourceSmall.trans <|
        (min_le_right _ _).trans (min_le_right _ _))
    simpa [globalConstant, mul_assoc] using hraw

end PureWZ2Proposition64P7ScaleSchedule

namespace PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

variable
    {sigma workLoss sourceDelta targetDelta₀ : ℝ}
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀}
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)

/-- The geometric target net at an arbitrary positive grid loss.  The
ambient separation constant is zero because target-parent separation is
proved later by the transported quotient and combined selection. -/
noncomputable def quantitativeVerticalRequestedScaleScheduleOfLoss
    (gridLoss : ℝ)
    (hgridLoss : 0 < gridLoss) :=
  pureWZ2Prop62RequestedScaleSchedule
    (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
    gridLoss 0
    geometry.scales.finalDelta_pos
    (geometry.scales.finalDelta_le_one_ninety_six.trans_lt (by norm_num))
    hgridLoss
    (by
      simp only [ENNReal.toReal_zero, mul_zero]
      exact (Real.rpow_pos_of_pos geometry.scales.finalDelta_pos _).le)

/-- Target grid attached to any object implementing only the positive grid
loss interface. -/
noncomputable def quantitativeVerticalRequestedScaleScheduleFor
    {Grid : Type*} [PureWZ2Proposition64TargetGrid Grid]
    (grid : Grid) :=
  quantitativeVerticalRequestedScaleScheduleOfLoss quantitativeOutput geometry
    (pureWZ2Proposition64TargetGridLoss grid)
    (pureWZ2Proposition64TargetGridLoss_pos grid)

/-- Canonical P7 target grid, selected without any critical-floor witness. -/
noncomputable def quantitativeVerticalP7RequestedScaleSchedule
    {outputLoss : ℝ}
    (schedule : PureWZ2Proposition64P7ScaleSchedule outputLoss) :=
  quantitativeVerticalRequestedScaleScheduleFor
    quantitativeOutput geometry schedule

end PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

end Kakeya.Assouad

end
