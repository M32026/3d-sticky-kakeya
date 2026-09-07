import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62IndependentPureSchedule
import Mathlib.Tactic

/-!
# Concrete requested-scale schedule for Proposition 6.2

This module constructs the finite separated requested-scale net used before
applying public nearby-scale CWA.  It uses only the public requested-scale
interface.

For a positive exponent step `step`, the schedule is

`r_i = delta ^ (step * i)`, `0 ≤ i ≤ floor (1 / step)`.

Thus the scales decrease with the index.  The final scale remains above
`delta`, while it is less than `delta ^ (-step) * delta`; this supplies the
last rounding interval without inserting a duplicate endpoint at `delta`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Number of coordinates in the top-down geometric requested-scale net. -/
def pureWZ2Prop62RequestedScaleLevelCount (step : ℝ) : ℕ :=
  Nat.floor (1 / step) + 1

/-- The uncapped top-down scale at coordinate `index`. -/
def pureWZ2Prop62RequestedScaleValue
    (delta step : ℝ) (index : ℕ) : ℝ :=
  Real.rpow delta (step * (index : ℝ))

lemma pureWZ2Prop62RequestedScaleValue_zero
    (delta step : ℝ) :
    pureWZ2Prop62RequestedScaleValue delta step 0 = 1 := by
  simp [pureWZ2Prop62RequestedScaleValue]

lemma pureWZ2Prop62RequestedScaleValue_succ
    {delta step : ℝ}
    (deltaPos : 0 < delta)
    (index : ℕ) :
    pureWZ2Prop62RequestedScaleValue delta step index =
      Real.rpow delta (-step) *
        pureWZ2Prop62RequestedScaleValue delta step (index + 1) := by
  unfold pureWZ2Prop62RequestedScaleValue
  calc
    Real.rpow delta (step * (index : ℝ)) =
        Real.rpow delta
          (-step + step * (((index + 1 : ℕ) : ℝ))) := by
      congr 1
      push_cast
      ring
    _ =
        Real.rpow delta (-step) *
          Real.rpow delta
            (step * (((index + 1 : ℕ) : ℝ))) :=
      Real.rpow_add deltaPos (-step)
        (step * (((index + 1 : ℕ) : ℝ)))

lemma pureWZ2Prop62RequestedScaleLevelCount_pos
    (step : ℝ) :
    0 < pureWZ2Prop62RequestedScaleLevelCount step := by
  simp [pureWZ2Prop62RequestedScaleLevelCount]

lemma pureWZ2Prop62RequestedScaleLevelCount_le
    {step : ℝ}
    (stepPos : 0 < step) :
    pureWZ2Prop62RequestedScaleLevelCount step ≤
      Nat.ceil (1 / step) + 1 := by
  unfold pureWZ2Prop62RequestedScaleLevelCount
  exact Nat.add_le_add_right (Nat.floor_le_ceil _) 1

lemma pureWZ2Prop62RequestedScaleLevelCount_cast_le
    {step : ℝ}
    (stepPos : 0 < step) :
    (pureWZ2Prop62RequestedScaleLevelCount step : ℝ) ≤
      1 / step + 1 := by
  have reciprocalNonnegative : 0 ≤ 1 / step := by positivity
  have floorLe :
      (Nat.floor (1 / step) : ℝ) ≤ 1 / step :=
    Nat.floor_le reciprocalNonnegative
  simpa [pureWZ2Prop62RequestedScaleLevelCount] using
    add_le_add_right floorLe 1

private lemma pureWZ2Prop62RequestedScale_exponent_le_one
    {step : ℝ}
    (stepPos : 0 < step)
    {index : ℕ}
    (indexLt :
      index < pureWZ2Prop62RequestedScaleLevelCount step) :
    step * (index : ℝ) ≤ 1 := by
  have indexLe :
      index ≤ Nat.floor (1 / step) := by
    simpa [pureWZ2Prop62RequestedScaleLevelCount] using indexLt
  have castIndexLe :
      (index : ℝ) ≤ Nat.floor (1 / step) := by
    exact_mod_cast indexLe
  have floorLe :
      (Nat.floor (1 / step) : ℝ) ≤ 1 / step :=
    Nat.floor_le (by positivity)
  calc
    step * (index : ℝ) ≤
        step * (Nat.floor (1 / step) : ℝ) := by
      gcongr
    _ ≤ step * (1 / step) := by
      gcongr
    _ = 1 := by
      field_simp [stepPos.ne']

private lemma pureWZ2Prop62RequestedScaleValue_mem
    {delta step : ℝ}
    (deltaPos : 0 < delta)
    (deltaLtOne : delta < 1)
    (stepPos : 0 < step)
    {index : ℕ}
    (indexLt :
      index < pureWZ2Prop62RequestedScaleLevelCount step) :
    delta ≤ pureWZ2Prop62RequestedScaleValue delta step index ∧
      pureWZ2Prop62RequestedScaleValue delta step index ≤ 1 := by
  have exponentNonnegative :
      0 ≤ step * (index : ℝ) := by positivity
  have exponentLeOne :
      step * (index : ℝ) ≤ 1 :=
    pureWZ2Prop62RequestedScale_exponent_le_one stepPos indexLt
  constructor
  · unfold pureWZ2Prop62RequestedScaleValue
    calc
      delta = Real.rpow delta 1 := (Real.rpow_one delta).symm
      _ ≤ Real.rpow delta (step * (index : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge
          deltaPos deltaLtOne.le exponentLeOne
  · exact
      Real.rpow_le_one deltaPos.le deltaLtOne.le exponentNonnegative

/-- Requested scale at one coordinate of the concrete top-down net. -/
def pureWZ2Prop62RequestedScale
    (delta step : ℝ)
    (deltaPos : 0 < delta)
    (deltaLtOne : delta < 1)
    (stepPos : 0 < step)
    (coordinate :
      Fin (pureWZ2Prop62RequestedScaleLevelCount step)) :
    WZ2PaperRequestedScale delta :=
  ⟨pureWZ2Prop62RequestedScaleValue delta step coordinate.1,
    pureWZ2Prop62RequestedScaleValue_mem
      deltaPos deltaLtOne stepPos coordinate.2⟩

@[simp] lemma pureWZ2Prop62RequestedScale_val
    (delta step : ℝ)
    (deltaPos : 0 < delta)
    (deltaLtOne : delta < 1)
    (stepPos : 0 < step)
    (coordinate :
      Fin (pureWZ2Prop62RequestedScaleLevelCount step)) :
    (pureWZ2Prop62RequestedScale
      delta step deltaPos deltaLtOne stepPos coordinate).1 =
      pureWZ2Prop62RequestedScaleValue delta step coordinate.1 :=
  rfl

private lemma pureWZ2Prop62RequestedScaleValue_antitone
    {delta step : ℝ}
    (deltaPos : 0 < delta)
    (deltaLtOne : delta < 1)
    (stepPos : 0 < step)
    {first second : ℕ}
    (firstLeSecond : first ≤ second) :
    pureWZ2Prop62RequestedScaleValue delta step second ≤
      pureWZ2Prop62RequestedScaleValue delta step first := by
  apply
    Real.rpow_le_rpow_of_exponent_ge
      deltaPos deltaLtOne.le
  exact mul_le_mul_of_nonneg_left
    (by exact_mod_cast firstLeSecond) stepPos.le

private lemma pureWZ2Prop62RequestedScaleValue_separated
    {delta step : ℝ}
    (deltaPos : 0 < delta)
    (deltaLtOne : delta < 1)
    (stepPos : 0 < step)
    {first second : ℕ}
    (firstLtSecond : first < second) :
    Real.rpow delta (-step) *
        pureWZ2Prop62RequestedScaleValue delta step second ≤
      pureWZ2Prop62RequestedScaleValue delta step first := by
  have secondPos : 0 < second := by omega
  have firstLePrevious : first ≤ second - 1 :=
    Nat.le_sub_one_of_lt firstLtSecond
  have secondEq : second - 1 + 1 = second :=
    Nat.sub_add_cancel (by omega)
  rw [show
    Real.rpow delta (-step) *
        pureWZ2Prop62RequestedScaleValue delta step second =
      pureWZ2Prop62RequestedScaleValue delta step (second - 1) by
    rw [pureWZ2Prop62RequestedScaleValue_succ
      deltaPos (second - 1)]
    congr 1
    exact congrArg
      (pureWZ2Prop62RequestedScaleValue delta step)
      secondEq.symm]
  exact
    pureWZ2Prop62RequestedScaleValue_antitone
      deltaPos deltaLtOne stepPos firstLePrevious

private lemma pureWZ2Prop62RequestedScaleValue_last_lt_window_delta
    {delta step : ℝ}
    (deltaPos : 0 < delta)
    (deltaLtOne : delta < 1)
    (stepPos : 0 < step) :
    pureWZ2Prop62RequestedScaleValue delta step
        (Nat.floor (1 / step)) <
      Real.rpow delta (-step) * delta := by
  have reciprocalLt :
      1 / step <
        (Nat.floor (1 / step) : ℝ) + 1 :=
    Nat.lt_floor_add_one (1 / step)
  have exponentLt :
      1 - step <
        step * (Nat.floor (1 / step) : ℝ) := by
    have := mul_lt_mul_of_pos_left reciprocalLt stepPos
    field_simp [stepPos.ne'] at this
    linarith
  have powerLt :
      Real.rpow delta
          (step * (Nat.floor (1 / step) : ℝ)) <
        Real.rpow delta (1 - step) :=
    Real.rpow_lt_rpow_of_exponent_gt
      deltaPos deltaLtOne exponentLt
  calc
    pureWZ2Prop62RequestedScaleValue delta step
        (Nat.floor (1 / step)) <
        Real.rpow delta (1 - step) := powerLt
    _ = Real.rpow delta (-step) * delta := by
      rw [show (1 - step : ℝ) = -step + 1 by ring]
      calc
        Real.rpow delta (-step + 1) =
            Real.rpow delta (-step) *
              Real.rpow delta 1 :=
          Real.rpow_add deltaPos (-step) 1
        _ = Real.rpow delta (-step) * delta := by
          congr 1
          exact Real.rpow_one delta

private lemma pureWZ2Prop62RequestedScale_rounding
    {delta step : ℝ}
    (deltaPos : 0 < delta)
    (deltaLtOne : delta < 1)
    (stepPos : 0 < step)
    (target : WZ2PaperRequestedScale delta) :
    ∃ coordinate :
        Fin (pureWZ2Prop62RequestedScaleLevelCount step),
      target.1 ≤
          (pureWZ2Prop62RequestedScale
            delta step deltaPos deltaLtOne stepPos coordinate).1 ∧
        ENNReal.ofReal
            (pureWZ2Prop62RequestedScale
              delta step deltaPos deltaLtOne stepPos coordinate).1 <
          ENNReal.ofReal (Real.rpow delta (-step)) *
            ENNReal.ofReal target.1 := by
  let last := Nat.floor (1 / step)
  let scale := pureWZ2Prop62RequestedScaleValue delta step
  have targetPos : 0 < target.1 :=
    deltaPos.trans_le target.2.1
  have windowPos : 0 < Real.rpow delta (-step) :=
    Real.rpow_pos_of_pos deltaPos _
  have lastLtCount :
      last < pureWZ2Prop62RequestedScaleLevelCount step := by
    simp [last, pureWZ2Prop62RequestedScaleLevelCount]
  by_cases lastBelow : scale last < target.1
  · let predicate : ℕ → Prop := fun index => scale index < target.1
    have existsBelow : ∃ index, predicate index :=
      ⟨last, lastBelow⟩
    let crossing := Nat.find existsBelow
    have crossingBelow : scale crossing < target.1 :=
      Nat.find_spec existsBelow
    have crossingLeLast : crossing ≤ last :=
      Nat.find_min' existsBelow lastBelow
    have crossingNeZero : crossing ≠ 0 := by
      intro crossingZero
      have : (1 : ℝ) < target.1 := by
        simpa [crossingZero, scale,
          pureWZ2Prop62RequestedScaleValue_zero] using crossingBelow
      exact (not_lt_of_ge target.2.2) this
    let previous := crossing - 1
    have previousLtCrossing : previous < crossing := by
      simp [previous, Nat.pos_of_ne_zero crossingNeZero]
    have previousLtCount :
        previous <
          pureWZ2Prop62RequestedScaleLevelCount step := by
      omega
    let coordinate :
        Fin (pureWZ2Prop62RequestedScaleLevelCount step) :=
      ⟨previous, previousLtCount⟩
    have targetLePrevious : target.1 ≤ scale previous := by
      have notBelow :
          ¬predicate previous :=
        Nat.find_min existsBelow previousLtCrossing
      simpa [predicate] using not_lt.mp notBelow
    have previousScale :
        scale previous =
          Real.rpow delta (-step) * scale crossing := by
      have crossingEq : crossing = previous + 1 := by omega
      rw [crossingEq]
      exact
        pureWZ2Prop62RequestedScaleValue_succ
          deltaPos previous
    have upperReal :
        scale previous <
          Real.rpow delta (-step) * target.1 := by
      rw [previousScale]
      exact mul_lt_mul_of_pos_left crossingBelow windowPos
    refine ⟨coordinate, ?_, ?_⟩
    · exact targetLePrevious
    · have upperPos :
          0 < Real.rpow delta (-step) * target.1 :=
        mul_pos windowPos targetPos
      have upperENN :=
        (ENNReal.ofReal_lt_ofReal_iff upperPos).mpr upperReal
      rw [ENNReal.ofReal_mul windowPos.le] at upperENN
      exact upperENN
  · have targetLeLast : target.1 ≤ scale last :=
      le_of_not_gt lastBelow
    let coordinate :
        Fin (pureWZ2Prop62RequestedScaleLevelCount step) :=
      ⟨last, lastLtCount⟩
    have lastWindowDelta :
        scale last < Real.rpow delta (-step) * delta :=
      pureWZ2Prop62RequestedScaleValue_last_lt_window_delta
        deltaPos deltaLtOne stepPos
    have upperReal :
        scale last <
          Real.rpow delta (-step) * target.1 :=
      lastWindowDelta.trans_le <|
        mul_le_mul_of_nonneg_left target.2.1 windowPos.le
    refine ⟨coordinate, targetLeLast, ?_⟩
    have upperPos :
        0 < Real.rpow delta (-step) * target.1 :=
      mul_pos windowPos targetPos
    have upperENN :=
      (ENNReal.ofReal_lt_ofReal_iff upperPos).mpr upperReal
    rw [ENNReal.ofReal_mul windowPos.le] at upperENN
    exact upperENN

/--
Concrete finite separated requested-scale net for the public Proposition 6.2
schedule interface.

The only interaction with the ambient CWA constant is the explicit gap
hypothesis `4 * ambientConstant.toReal ≤ delta ^ (-step)`.
-/
def pureWZ2Prop62RequestedScaleSchedule
    (delta step : ℝ)
    (ambientConstant : ENNReal)
    (deltaPos : 0 < delta)
    (deltaLtOne : delta < 1)
    (stepPos : 0 < step)
    (separation :
      4 * ambientConstant.toReal ≤
        Real.rpow delta (-step)) :
    PureWZ2Prop62RequestedScaleSchedule
      delta ambientConstant
        (ENNReal.ofReal (Real.rpow delta (-step))) where
  scaleWindow_finite := by
    constructor
    · have windowOne :
          1 ≤ Real.rpow delta (-step) := by
        exact
          Real.one_le_rpow_of_pos_of_le_one_of_nonpos
            deltaPos deltaLtOne.le (by linarith)
      simpa using ENNReal.ofReal_mono windowOne
    · exact ENNReal.ofReal_ne_top
  levelCount := pureWZ2Prop62RequestedScaleLevelCount step
  levelCount_pos :=
    pureWZ2Prop62RequestedScaleLevelCount_pos step
  requested :=
    pureWZ2Prop62RequestedScale
      delta step deltaPos deltaLtOne stepPos
  requested_separated := by
    intro first second firstLtSecond
    have scaleSeparated :=
      pureWZ2Prop62RequestedScaleValue_separated
        deltaPos deltaLtOne stepPos firstLtSecond
    have secondPositive :
        0 <
          pureWZ2Prop62RequestedScaleValue
            delta step second.1 :=
      Real.rpow_pos_of_pos deltaPos _
    calc
      4 * ambientConstant.toReal *
          (pureWZ2Prop62RequestedScale
            delta step deltaPos deltaLtOne stepPos second).1 ≤
          Real.rpow delta (-step) *
            pureWZ2Prop62RequestedScaleValue
              delta step second.1 := by
        change
          4 * ambientConstant.toReal *
              pureWZ2Prop62RequestedScaleValue
                delta step second.1 ≤
            Real.rpow delta (-step) *
              pureWZ2Prop62RequestedScaleValue
                delta step second.1
        exact
          mul_le_mul_of_nonneg_right
            separation secondPositive.le
      _ ≤
          pureWZ2Prop62RequestedScaleValue
            delta step first.1 :=
        scaleSeparated
      _ =
          (pureWZ2Prop62RequestedScale
            delta step deltaPos deltaLtOne stepPos first).1 :=
        rfl
  rounding :=
    pureWZ2Prop62RequestedScale_rounding
      deltaPos deltaLtOne stepPos

@[simp] theorem pureWZ2Prop62RequestedScaleSchedule_levelCount
    (delta step : ℝ)
    (ambientConstant : ENNReal)
    (deltaPos : 0 < delta)
    (deltaLtOne : delta < 1)
    (stepPos : 0 < step)
    (separation :
      4 * ambientConstant.toReal ≤
        Real.rpow delta (-step)) :
    (pureWZ2Prop62RequestedScaleSchedule
      delta step ambientConstant deltaPos deltaLtOne stepPos
      separation).levelCount =
        pureWZ2Prop62RequestedScaleLevelCount step :=
  rfl

theorem pureWZ2Prop62RequestedScaleSchedule_requested_antitone
    (delta step : ℝ)
    (ambientConstant : ENNReal)
    (deltaPos : 0 < delta)
    (deltaLtOne : delta < 1)
    (stepPos : 0 < step)
    (separation :
      4 * ambientConstant.toReal ≤
        Real.rpow delta (-step))
    (first second :
      Fin
        (pureWZ2Prop62RequestedScaleSchedule
          delta step ambientConstant deltaPos deltaLtOne stepPos
          separation).levelCount)
    (firstLeSecond : first.1 ≤ second.1) :
    (pureWZ2Prop62RequestedScaleSchedule
        delta step ambientConstant deltaPos deltaLtOne stepPos
        separation).requested second ≤
      (pureWZ2Prop62RequestedScaleSchedule
        delta step ambientConstant deltaPos deltaLtOne stepPos
        separation).requested first := by
  apply Subtype.coe_le_coe.mp
  exact
    pureWZ2Prop62RequestedScaleValue_antitone
      deltaPos deltaLtOne stepPos firstLeSecond

theorem pureWZ2Prop62RequestedScaleSchedule_levelCount_le
    (delta step : ℝ)
    (ambientConstant : ENNReal)
    (deltaPos : 0 < delta)
    (deltaLtOne : delta < 1)
    (stepPos : 0 < step)
    (separation :
      4 * ambientConstant.toReal ≤
        Real.rpow delta (-step)) :
    (pureWZ2Prop62RequestedScaleSchedule
      delta step ambientConstant deltaPos deltaLtOne stepPos
      separation).levelCount ≤
        Nat.ceil (1 / step) + 1 := by
  exact pureWZ2Prop62RequestedScaleLevelCount_le stepPos

theorem pureWZ2Prop62RequestedScaleSchedule_levelCount_cast_le
    (delta step : ℝ)
    (ambientConstant : ENNReal)
    (deltaPos : 0 < delta)
    (deltaLtOne : delta < 1)
    (stepPos : 0 < step)
    (separation :
      4 * ambientConstant.toReal ≤
        Real.rpow delta (-step)) :
    ((pureWZ2Prop62RequestedScaleSchedule
      delta step ambientConstant deltaPos deltaLtOne stepPos
      separation).levelCount : ℝ) ≤
        1 / step + 1 := by
  exact pureWZ2Prop62RequestedScaleLevelCount_cast_le stepPos

/--
Apply public nearby-scale CWA to the concrete requested-scale net.  The
resulting actual witnesses are assembled by the public laminar-schedule
constructor; no aligned exact-source interface is used.
-/
noncomputable def pureWZ2Prop62LaminarScheduleOfGeometricRequestedScales
    {delta step : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (deltaLtOne : delta < 1)
    (stepPos : 0 < step)
    (separation :
      4 * ambientConstant.toReal ≤
        Real.rpow delta (-step)) :
    PureWZ2Prop62LaminarPureSchedule
      fine ambientConstant
        (ambientConstant *
          ENNReal.ofReal (Real.rpow delta (-step))) :=
  ambient.toProp62LaminarSchedule <|
    pureWZ2Prop62RequestedScaleSchedule
      delta step ambientConstant ambient.1 deltaLtOne stepPos
      separation

end Kakeya.Assouad

end
