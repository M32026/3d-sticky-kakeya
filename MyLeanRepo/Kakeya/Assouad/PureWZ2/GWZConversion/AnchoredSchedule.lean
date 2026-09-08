import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.AnchoredAbsorption

/-!
# Fixed-depth schedule for the anchored nearby-scale assembly

The number of reference coordinates is chosen before the source family and
the fine scale.  For each later `delta`, the common ratio is
`delta ^ (-1 / N)`, so the last formal endpoint is exactly one.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Number of simultaneous reference coordinates. -/
def pureWZ2AnchoredCoordinateCount (outputLoss : ℝ) : ℕ :=
  Nat.ceil (1 / outputLoss) + 1

/-- Common ratio of the fixed-depth schedule. -/
def pureWZ2AnchoredScheduleRatio
    (delta : ℝ) (coordinateCount : ℕ) : ℝ :=
  Real.rpow delta (-(1 / (coordinateCount : ℝ)))

/-- Fine-scale threshold forcing the last small coordinate below `1/(200A)`. -/
def pureWZ2AnchoredScheduleThreshold
    (A : ℝ) (coordinateCount : ℕ) : ℝ :=
  Real.rpow (200 * A) (-(coordinateCount : ℝ))

theorem pureWZ2_anchored_coordinate_count
    {outputLoss : ℝ}
    (houtputLoss : 0 < outputLoss) :
    let coordinateCount :=
      pureWZ2AnchoredCoordinateCount outputLoss
    0 < coordinateCount ∧
      1 / (coordinateCount : ℝ) < outputLoss := by
  dsimp only [pureWZ2AnchoredCoordinateCount]
  constructor
  · omega
  · have hceil :
        1 / outputLoss ≤
          (Nat.ceil (1 / outputLoss) : ℝ) :=
      Nat.le_ceil _
    have hcount :
        1 / outputLoss <
          ((Nat.ceil (1 / outputLoss) + 1 : ℕ) : ℝ) := by
      exact_mod_cast
        (show
          1 / outputLoss <
            (Nat.ceil (1 / outputLoss) : ℝ) + 1 by
          linarith)
    have hcountPos :
        0 <
          ((Nat.ceil (1 / outputLoss) + 1 : ℕ) : ℝ) := by
      positivity
    rw [div_lt_iff₀ hcountPos]
    have hscaled :
        1 <
          outputLoss *
            ((Nat.ceil (1 / outputLoss) + 1 : ℕ) : ℝ) := by
      have hinverse :
          outputLoss * (1 / outputLoss) = 1 := by
        exact mul_one_div_cancel houtputLoss.ne'
      calc
        1 = outputLoss * (1 / outputLoss) := hinverse.symm
        _ < outputLoss *
              ((Nat.ceil (1 / outputLoss) + 1 : ℕ) : ℝ) :=
          mul_lt_mul_of_pos_left hcount houtputLoss
    simpa [mul_comm] using hscaled

theorem pureWZ2_anchored_schedule
    {delta A outputLoss : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta < 1)
    (hA : 1 ≤ A)
    (houtputLoss : 0 < outputLoss)
    (coordinateCount : ℕ)
    (coordinateCountPos : 0 < coordinateCount)
    (hcoordinateLoss :
      1 / (coordinateCount : ℝ) < outputLoss)
    (hdeltaSchedule :
      delta ≤
        pureWZ2AnchoredScheduleThreshold A coordinateCount) :
    let ratio :=
      pureWZ2AnchoredScheduleRatio delta coordinateCount
    1 < ratio ∧
      delta * ratio ^ coordinateCount = 1 ∧
      200 * A ≤ ratio ∧
      ENNReal.ofReal ratio <
        Kakeya.realRpowENN delta (-outputLoss) := by
  let countReal : ℝ := coordinateCount
  have hcountReal : 0 < countReal := by
    dsimp only [countReal]
    exact_mod_cast coordinateCountPos
  let ratio :=
    pureWZ2AnchoredScheduleRatio delta coordinateCount
  have hexponentNeg :
      -(1 / countReal) < 0 := by
    exact neg_neg_iff_pos.mpr (one_div_pos.mpr hcountReal)
  have hratioOne : 1 < ratio := by
    dsimp only [ratio, pureWZ2AnchoredScheduleRatio,
      countReal]
    exact
      Real.one_lt_rpow_of_pos_of_lt_one_of_neg
        hdelta hdeltaOne hexponentNeg
  have hratioPower :
      ratio ^ coordinateCount = 1 / delta := by
    calc
      ratio ^ coordinateCount =
          ratio ^ (coordinateCount : ℝ) := by
        exact (Real.rpow_natCast ratio coordinateCount).symm
      _ =
          Real.rpow delta
            ((-(1 / countReal)) *
              (coordinateCount : ℝ)) := by
        dsimp only [ratio, pureWZ2AnchoredScheduleRatio]
        exact
          (Real.rpow_mul hdelta.le
            (-(1 / (coordinateCount : ℝ)))
            (coordinateCount : ℝ)).symm
      _ = Real.rpow delta (-1) := by
        congr 1
        dsimp only [countReal]
        field_simp [show (coordinateCount : ℝ) ≠ 0 by positivity]
      _ = 1 / delta := by
        calc
          Real.rpow delta (-1) =
              (Real.rpow delta 1)⁻¹ := by
            exact Real.rpow_neg hdelta.le 1
          _ = delta⁻¹ := by
            exact congrArg Inv.inv (Real.rpow_one delta)
          _ = 1 / delta := inv_eq_one_div delta
  have hschedule :
      delta * ratio ^ coordinateCount = 1 := by
    rw [hratioPower]
    field_simp [hdelta.ne']
  have hbasePos : 0 < 200 * A := by
    positivity
  have hbasePower :
      Real.rpow
          (pureWZ2AnchoredScheduleThreshold
            A coordinateCount)
          (-(1 / countReal)) =
        200 * A := by
    dsimp only [pureWZ2AnchoredScheduleThreshold]
    calc
      Real.rpow
            (Real.rpow (200 * A)
              (-(coordinateCount : ℝ)))
            (-(1 / countReal)) =
          Real.rpow (200 * A)
            ((-(coordinateCount : ℝ)) *
              (-(1 / countReal))) := by
        exact
          (Real.rpow_mul hbasePos.le
            (-(coordinateCount : ℝ))
            (-(1 / countReal))).symm
      _ = Real.rpow (200 * A) 1 := by
        congr 1
        dsimp only [countReal]
        field_simp [show (coordinateCount : ℝ) ≠ 0 by positivity]
      _ = 200 * A := Real.rpow_one _
  have hsmallScale : 200 * A ≤ ratio := by
    rw [← hbasePower]
    dsimp only [ratio, pureWZ2AnchoredScheduleRatio]
    exact
      Real.rpow_le_rpow_of_nonpos
        hdelta hdeltaSchedule hexponentNeg.le
  have hratioReal :
      ratio < Real.rpow delta (-outputLoss) := by
    dsimp only [ratio, pureWZ2AnchoredScheduleRatio]
    exact
      Real.rpow_lt_rpow_of_exponent_gt
        hdelta hdeltaOne (by linarith)
  have hratioOutput :
      ENNReal.ofReal ratio <
        Kakeya.realRpowENN delta (-outputLoss) := by
    dsimp only [Kakeya.realRpowENN]
    exact
      (ENNReal.ofReal_lt_ofReal_iff
        (Real.rpow_pos_of_pos hdelta _)).mpr hratioReal
  exact
    ⟨hratioOne, hschedule, hsmallScale,
      hratioOutput⟩

end Kakeya.Assouad

end
