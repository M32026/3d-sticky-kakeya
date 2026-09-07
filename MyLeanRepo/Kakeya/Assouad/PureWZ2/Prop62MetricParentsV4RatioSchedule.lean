import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62IndependentPureSchedule

/-!
# Ratio schedules above a prescribed metric-parent scale

Starting at scale one, use the exact geometric grid `R⁻ⁱ` and stop immediately
before its first term below `rho`.  This avoids the repeated top endpoint
created by reversing a capped grid and avoids an unseparated final copy of
`rho`.  Maximality of the retained last term gives the required one-step
rounding window.
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya.Streamlined

attribute [local instance] Classical.propDecidable

private def pureWZ2Prop62RatioScale (R : ℝ) (index : ℕ) : ℝ :=
  1 / R ^ index

private theorem pureWZ2Prop62RatioScale_pos
    {R : ℝ} (RPos : 0 < R) (index : ℕ) :
    0 < pureWZ2Prop62RatioScale R index := by
  unfold pureWZ2Prop62RatioScale
  positivity

private theorem pureWZ2Prop62RatioScale_zero (R : ℝ) :
    pureWZ2Prop62RatioScale R 0 = 1 := by
  simp [pureWZ2Prop62RatioScale]

private theorem pureWZ2Prop62RatioScale_succ
    {R : ℝ} (RPos : 0 < R) (index : ℕ) :
    R * pureWZ2Prop62RatioScale R (index + 1) =
      pureWZ2Prop62RatioScale R index := by
  unfold pureWZ2Prop62RatioScale
  rw [pow_succ]
  field_simp [RPos.ne']

private theorem pureWZ2Prop62RatioScale_antitone
    {R : ℝ} (ROne : 1 ≤ R)
    {first second : ℕ} (firstLeSecond : first ≤ second) :
    pureWZ2Prop62RatioScale R second ≤
      pureWZ2Prop62RatioScale R first := by
  unfold pureWZ2Prop62RatioScale
  apply one_div_le_one_div_of_le
  · positivity
  · exact pow_le_pow_right₀ ROne firstLeSecond

private theorem pureWZ2Prop62RatioScale_strict
    {R : ℝ} (ROne : 1 < R)
    {first second : ℕ} (firstLtSecond : first < second) :
    R * pureWZ2Prop62RatioScale R second ≤
      pureWZ2Prop62RatioScale R first := by
  calc
    R * pureWZ2Prop62RatioScale R second ≤
        R * pureWZ2Prop62RatioScale R (first + 1) := by
      gcongr
      exact
        pureWZ2Prop62RatioScale_antitone ROne.le
          (Nat.succ_le_of_lt firstLtSecond)
    _ = pureWZ2Prop62RatioScale R first :=
      pureWZ2Prop62RatioScale_succ (by linarith) first

private theorem pureWZ2Prop62RatioScale_N_add_one_lt
    {rho R : ℝ} {N : ℕ}
    (_rhoPos : 0 < rho)
    (RPos : 1 < R)
    (reaches : 1 ≤ rho * R ^ N) :
    pureWZ2Prop62RatioScale R (N + 1) < rho := by
  have powerPos : 0 < R ^ N := by positivity
  have inverseLe : (R ^ N)⁻¹ ≤ rho := by
    have quotientLe : 1 / R ^ N ≤ rho :=
      (div_le_iff₀ powerPos).2 (by nlinarith)
    simpa only [one_div] using quotientLe
  have inverseR : R⁻¹ < 1 := by
    exact inv_lt_one₀ (by linarith) |>.2 RPos
  calc
    pureWZ2Prop62RatioScale R (N + 1) =
        (R ^ N)⁻¹ * R⁻¹ := by
      unfold pureWZ2Prop62RatioScale
      rw [pow_succ]
      simp only [one_div, mul_inv_rev]
      ring
    _ < (R ^ N)⁻¹ * 1 := by
      exact mul_lt_mul_of_pos_left inverseR (inv_pos.mpr powerPos)
    _ = (R ^ N)⁻¹ := by ring
    _ ≤ rho := inverseLe

private noncomputable def pureWZ2Prop62RatioCrossing
    (rho R : ℝ) (N : ℕ)
    (rhoPos : 0 < rho)
    (RPos : 1 < R)
    (reaches : 1 ≤ rho * R ^ N) : ℕ :=
  Nat.find
    (show
      ∃ index : ℕ, pureWZ2Prop62RatioScale R index < rho from
        ⟨N + 1,
          pureWZ2Prop62RatioScale_N_add_one_lt
            rhoPos RPos reaches⟩)

private theorem pureWZ2Prop62RatioCrossing_spec
    {rho R : ℝ} {N : ℕ}
    (rhoPos : 0 < rho)
    (RPos : 1 < R)
    (reaches : 1 ≤ rho * R ^ N) :
    pureWZ2Prop62RatioScale R
        (pureWZ2Prop62RatioCrossing
          rho R N rhoPos RPos reaches) < rho :=
  by
    unfold pureWZ2Prop62RatioCrossing
    exact
      Nat.find_spec
        (show
          ∃ index : ℕ, pureWZ2Prop62RatioScale R index < rho from
            ⟨N + 1,
              pureWZ2Prop62RatioScale_N_add_one_lt
                rhoPos RPos reaches⟩)

private theorem pureWZ2Prop62RatioCrossing_pos
    {rho R : ℝ} {N : ℕ}
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (RPos : 1 < R)
    (reaches : 1 ≤ rho * R ^ N) :
    0 <
      pureWZ2Prop62RatioCrossing
        rho R N rhoPos RPos reaches := by
  apply Nat.pos_of_ne_zero
  intro crossingZero
  have crossingSpec :=
    pureWZ2Prop62RatioCrossing_spec rhoPos RPos reaches
  rw [crossingZero, pureWZ2Prop62RatioScale_zero] at crossingSpec
  linarith

private theorem pureWZ2Prop62RatioCrossing_le
    {rho R : ℝ} {N : ℕ}
    (rhoPos : 0 < rho)
    (RPos : 1 < R)
    (reaches : 1 ≤ rho * R ^ N) :
    pureWZ2Prop62RatioCrossing
        rho R N rhoPos RPos reaches ≤ N + 1 :=
  by
    unfold pureWZ2Prop62RatioCrossing
    exact
      Nat.find_min'
        (show
          ∃ index : ℕ, pureWZ2Prop62RatioScale R index < rho from
            ⟨N + 1,
              pureWZ2Prop62RatioScale_N_add_one_lt
                rhoPos RPos reaches⟩)
        (pureWZ2Prop62RatioScale_N_add_one_lt
          rhoPos RPos reaches)

private theorem pureWZ2Prop62RatioScale_before_crossing
    {rho R : ℝ} {N index : ℕ}
    (rhoPos : 0 < rho)
    (RPos : 1 < R)
    (reaches : 1 ≤ rho * R ^ N)
    (indexLt :
      index <
        pureWZ2Prop62RatioCrossing
          rho R N rhoPos RPos reaches) :
    rho ≤ pureWZ2Prop62RatioScale R index := by
  let crossingExists :
      ∃ coordinate : ℕ,
        pureWZ2Prop62RatioScale R coordinate < rho :=
    ⟨N + 1,
      pureWZ2Prop62RatioScale_N_add_one_lt
        rhoPos RPos reaches⟩
  have notCrossed :=
    Nat.find_min
      (H := crossingExists)
      indexLt
  simpa only [
    pureWZ2Prop62RatioCrossing, crossingExists, not_lt
  ] using notCrossed

/-- The top-down ratio net from scale one to the last `R`-step above `rho`. -/
noncomputable def pureWZ2Prop62RatioRequestedScaleSchedule
    (rho R : ℝ)
    (ambientConstant : ENNReal)
    (N : ℕ)
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (RPos : 1 < R)
    (separation : 4 * ambientConstant.toReal ≤ R)
    (reaches : 1 ≤ rho * R ^ N) :
    PureWZ2Prop62RequestedScaleSchedule
      rho ambientConstant (ENNReal.ofReal R) where
  scaleWindow_finite := by
    constructor
    · simpa using ENNReal.ofReal_mono RPos.le
    · exact ENNReal.ofReal_ne_top
  levelCount :=
    pureWZ2Prop62RatioCrossing
      rho R N rhoPos RPos reaches
  levelCount_pos :=
    pureWZ2Prop62RatioCrossing_pos
      rhoPos rhoLeOne RPos reaches
  requested := fun coordinate =>
    ⟨pureWZ2Prop62RatioScale R coordinate.1,
      pureWZ2Prop62RatioScale_before_crossing
        rhoPos RPos reaches coordinate.2,
      (pureWZ2Prop62RatioScale_antitone RPos.le
        (Nat.zero_le coordinate.1)).trans_eq
          (pureWZ2Prop62RatioScale_zero R)⟩
  requested_separated := by
    intro first second firstLtSecond
    have secondPos :
        0 ≤ pureWZ2Prop62RatioScale R second.1 :=
      (pureWZ2Prop62RatioScale_pos (by linarith) second.1).le
    calc
      4 * ambientConstant.toReal *
            pureWZ2Prop62RatioScale R second.1 ≤
          R * pureWZ2Prop62RatioScale R second.1 := by
        exact mul_le_mul_of_nonneg_right separation secondPos
      _ ≤ pureWZ2Prop62RatioScale R first.1 :=
        pureWZ2Prop62RatioScale_strict RPos firstLtSecond
  rounding := by
    intro target
    let crossing :=
      pureWZ2Prop62RatioCrossing
        rho R N rhoPos RPos reaches
    let predicate : ℕ → Prop :=
      fun index => pureWZ2Prop62RatioScale R index < target.1
    have existsCrossing : ∃ index, predicate index :=
      ⟨crossing,
        (pureWZ2Prop62RatioCrossing_spec
          rhoPos RPos reaches).trans_le target.2.1⟩
    let firstBelow := Nat.find existsCrossing
    have firstBelowSpec :
        pureWZ2Prop62RatioScale R firstBelow < target.1 :=
      Nat.find_spec (H := existsCrossing)
    have firstBelowPos : 0 < firstBelow := by
      apply Nat.pos_of_ne_zero
      intro firstBelowZero
      rw [firstBelowZero, pureWZ2Prop62RatioScale_zero] at firstBelowSpec
      exact (not_lt_of_ge target.2.2) firstBelowSpec
    have firstBelowLe : firstBelow ≤ crossing :=
      Nat.find_min'
        (H := existsCrossing)
        ((pureWZ2Prop62RatioCrossing_spec
          rhoPos RPos reaches).trans_le target.2.1)
    let coordinate :
        Fin
          (pureWZ2Prop62RatioCrossing
            rho R N rhoPos RPos reaches) :=
      ⟨firstBelow - 1, by
        dsimp only [crossing] at firstBelowLe
        omega⟩
    have targetLe :
        target.1 ≤
          pureWZ2Prop62RatioScale R coordinate.1 := by
      have notBelow :=
        Nat.find_min
          (H := existsCrossing)
          (m := firstBelow - 1) (by omega)
      simpa only [predicate, not_lt] using notBelow
    have previousEq :
        pureWZ2Prop62RatioScale R coordinate.1 =
          R * pureWZ2Prop62RatioScale R firstBelow := by
      have indexEq : firstBelow = (firstBelow - 1) + 1 := by omega
      have recurrence :=
        pureWZ2Prop62RatioScale_succ
          (show 0 < R by linarith) (firstBelow - 1)
      rw [← indexEq] at recurrence
      exact recurrence.symm
    have withinReal :
        pureWZ2Prop62RatioScale R coordinate.1 <
          R * target.1 := by
      rw [previousEq]
      exact mul_lt_mul_of_pos_left firstBelowSpec (by linarith)
    refine ⟨coordinate, targetLe, ?_⟩
    have targetPos : 0 < target.1 :=
      rhoPos.trans_le target.2.1
    have upperPos : 0 < R * target.1 := by positivity
    have withinENN :=
      (ENNReal.ofReal_lt_ofReal_iff upperPos).mpr withinReal
    rw [ENNReal.ofReal_mul (show 0 ≤ R by linarith)] at withinENN
    exact withinENN

@[simp] theorem pureWZ2Prop62RatioRequestedScaleSchedule_levelCount
    (rho R : ℝ)
    (ambientConstant : ENNReal)
    (N : ℕ)
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (RPos : 1 < R)
    (separation : 4 * ambientConstant.toReal ≤ R)
    (reaches : 1 ≤ rho * R ^ N) :
    (pureWZ2Prop62RatioRequestedScaleSchedule
      rho R ambientConstant N rhoPos rhoLeOne RPos separation
      reaches).levelCount =
        pureWZ2Prop62RatioCrossing
          rho R N rhoPos RPos reaches :=
  rfl

theorem pureWZ2Prop62RatioRequestedScaleSchedule_levelCount_le
    (rho R : ℝ)
    (ambientConstant : ENNReal)
    (N : ℕ)
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (RPos : 1 < R)
    (separation : 4 * ambientConstant.toReal ≤ R)
    (reaches : 1 ≤ rho * R ^ N) :
    (pureWZ2Prop62RatioRequestedScaleSchedule
      rho R ambientConstant N rhoPos rhoLeOne RPos separation
      reaches).levelCount ≤ N + 1 :=
  pureWZ2Prop62RatioCrossing_le rhoPos RPos reaches

/-- Apply public nearby-scale CWA to the ratio net. -/
noncomputable def pureWZ2Prop62RatioLaminarSchedule
    {rho R : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily rho}
    {ambientConstant : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (N : ℕ)
    (rhoLeOne : rho ≤ 1)
    (RPos : 1 < R)
    (separation : 4 * ambientConstant.toReal ≤ R)
    (reaches : 1 ≤ rho * R ^ N) :
    PureWZ2Prop62LaminarPureSchedule
      fine ambientConstant
        (ambientConstant * ENNReal.ofReal R) :=
  ambient.toProp62LaminarSchedule <|
    pureWZ2Prop62RatioRequestedScaleSchedule
      rho R ambientConstant N ambient.1 rhoLeOne RPos separation
      reaches

@[simp] theorem pureWZ2Prop62RatioLaminarSchedule_levelCount
    {rho R : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily rho}
    {ambientConstant : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (N : ℕ)
    (rhoLeOne : rho ≤ 1)
    (RPos : 1 < R)
    (separation : 4 * ambientConstant.toReal ≤ R)
    (reaches : 1 ≤ rho * R ^ N) :
    (pureWZ2Prop62RatioLaminarSchedule
      ambient N rhoLeOne RPos separation reaches).levelCount =
      (pureWZ2Prop62RatioRequestedScaleSchedule
        rho R ambientConstant N ambient.1 rhoLeOne RPos separation
        reaches).levelCount :=
  rfl

theorem pureWZ2Prop62RatioLaminarSchedule_levelCount_le
    {rho R : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily rho}
    {ambientConstant : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (N : ℕ)
    (rhoLeOne : rho ≤ 1)
    (RPos : 1 < R)
    (separation : 4 * ambientConstant.toReal ≤ R)
    (reaches : 1 ≤ rho * R ^ N) :
    (pureWZ2Prop62RatioLaminarSchedule
      ambient N rhoLeOne RPos separation reaches).levelCount ≤ N + 1 := by
  exact
    pureWZ2Prop62RatioRequestedScaleSchedule_levelCount_le
      rho R ambientConstant N ambient.1 rhoLeOne RPos separation
      reaches

end Kakeya.Assouad

end
