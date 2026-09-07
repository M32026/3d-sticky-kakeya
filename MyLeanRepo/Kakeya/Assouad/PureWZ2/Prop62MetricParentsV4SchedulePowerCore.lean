import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4RatioSchedule
import Mathlib.Tactic

/-!
# Power-controlled parent schedules

For an input parent CWA constant bounded by `delta ^ (-B * eta)`, enlarge the
public witness to

`C1 = delta ^ (-((B + 1) * eta))`.

The requested scales use the exact ratio `R = 4 * C1.toReal` and the fixed
reach depth `N = ceil (1 / ((B + 1) * eta))`.  The resulting laminar window
is exactly `4 * C1 ^ 2`.  A threshold chosen from `D`, `B`, and `eta` before
the runtime scale absorbs its fixed factor four into
`delta ^ (-((D + 2 * B + 3) * eta))`.

This module contains no dependency on the frozen V4 statements.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The power step in the four-degree parent schedule. -/
def pureWZ2Prop62MetricParentsV4FourDegreeScheduleStep
    (B : ℕ) (eta : ℝ) : ℝ :=
  ((B : ℝ) + 1) * eta

/-- The enlarged public parent-CWA constant `C1`. -/
def pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
    (B : ℕ) (eta delta : ℝ) : ENNReal :=
  Kakeya.realRpowENN delta
    (-pureWZ2Prop62MetricParentsV4FourDegreeScheduleStep B eta)

/-- The exact requested-scale ratio `R = 4 * C1.toReal`. -/
def pureWZ2Prop62MetricParentsV4FourDegreeRatio
    (B : ℕ) (eta delta : ℝ) : ℝ :=
  4 *
    (pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
      B eta delta).toReal

/-- The fixed exponent depth which makes the ratio net reach `delta`. -/
def pureWZ2Prop62MetricParentsV4FourDegreeReachDepth
    (B : ℕ) (eta : ℝ) : ℕ :=
  Nat.ceil
    (1 / pureWZ2Prop62MetricParentsV4FourDegreeScheduleStep B eta)

/--
The schedule itself contains at most one coordinate beyond the reach depth.
`D` is retained in the signature so this bound can be fixed at the same
quantifier point as the complete four-degree package.
-/
def pureWZ2Prop62MetricParentsV4FourDegreeDepthBound
    (_D B : ℕ) (eta : ℝ) : ℕ :=
  pureWZ2Prop62MetricParentsV4FourDegreeReachDepth B eta + 1

/-- Final power exponent paying for the density and parent-schedule losses. -/
def pureWZ2Prop62MetricParentsV4FourDegreeWindowPower
    (D B : ℕ) : ℕ :=
  D + 2 * B + 3

/--
Small-scale data fixed after `D`, `B`, and `eta`, and before `delta`.
Only the final factor four needs threshold absorption.
-/
structure PureWZ2Prop62MetricParentsV4SchedulePowerCertificate
    (D B : ℕ) (eta : ℝ) where
  delta0 : ℝ
  delta0_pos : 0 < delta0
  delta0_le_one_hundred : delta0 ≤ 1 / 100
  four_le_density_gap :
    ∀ {delta : ℝ},
      0 < delta →
      delta ≤ delta0 →
        (4 : ENNReal) ≤
          Kakeya.realRpowENN delta
            (-(((D + 1 : ℕ) : ℝ) * eta))

theorem exists_pureWZ2Prop62MetricParentsV4SchedulePowerCertificate
    (D B : ℕ) (eta : ℝ)
    (eta_pos : 0 < eta) :
    Nonempty
      (PureWZ2Prop62MetricParentsV4SchedulePowerCertificate
        D B eta) := by
  have gap_pos : 0 < ((D + 1 : ℕ) : ℝ) * eta := by
    positivity
  rcases
      exists_delta_realRpowENN_bound
        (4 : ENNReal) (by norm_num) gap_pos with
    ⟨absorptionScale, absorptionScale_pos,
      absorptionScale_le_one, absorbed⟩
  let delta0 := min (1 / 100 : ℝ) absorptionScale
  refine
    ⟨{
      delta0 := delta0
      delta0_pos := lt_min (by norm_num) absorptionScale_pos
      delta0_le_one_hundred := min_le_left _ _
      four_le_density_gap := ?_
    }⟩
  intro delta delta_pos delta_le
  exact
    absorbed delta delta_pos
      (delta_le.trans (min_le_right _ _))

namespace PureWZ2Prop62MetricParentsV4SchedulePowerCertificate

variable
    {D B : ℕ} {eta : ℝ}
    (power :
      PureWZ2Prop62MetricParentsV4SchedulePowerCertificate
        D B eta)

include power

theorem delta_lt_one
    {delta : ℝ}
    (delta_le : delta ≤ power.delta0) :
    delta < 1 :=
  lt_of_le_of_lt
    (delta_le.trans power.delta0_le_one_hundred)
    (by norm_num)

theorem step_pos
    (eta_pos : 0 < eta) :
    0 <
      pureWZ2Prop62MetricParentsV4FourDegreeScheduleStep B eta := by
  unfold pureWZ2Prop62MetricParentsV4FourDegreeScheduleStep
  positivity

theorem ambientConstant_finite
    {delta : ℝ} :
    pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
        B eta delta ≠ ⊤ := by
  simp [pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant,
    Kakeya.realRpowENN]

theorem ambientConstant_toReal
    {delta : ℝ}
    (delta_pos : 0 < delta) :
    (pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
        B eta delta).toReal =
      Real.rpow delta
        (-pureWZ2Prop62MetricParentsV4FourDegreeScheduleStep B eta) := by
  unfold pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
    Kakeya.realRpowENN
  exact
    ENNReal.toReal_ofReal
      (Real.rpow_nonneg delta_pos.le _)

theorem one_le_ambientConstant
    {delta : ℝ}
    (eta_pos : 0 < eta)
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ power.delta0) :
    1 ≤
      pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
        B eta delta := by
  have exponent_le :
      -pureWZ2Prop62MetricParentsV4FourDegreeScheduleStep B eta ≤ 0 := by
    linarith [power.step_pos eta_pos]
  calc
    (1 : ENNReal) = Kakeya.realRpowENN delta 0 := by
      simp [Kakeya.realRpowENN]
    _ ≤
        Kakeya.realRpowENN delta
          (-pureWZ2Prop62MetricParentsV4FourDegreeScheduleStep B eta) :=
      pure_wz2_rpowENN_antitone
        delta_pos (power.delta_lt_one delta_le).le exponent_le
    _ =
        pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
          B eta delta := rfl

theorem parentConstant_le_ambientConstant
    {delta : ℝ}
    (eta_pos : 0 < eta)
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ power.delta0)
    {parentConstant : ENNReal}
    (parentConstant_le :
      parentConstant ≤
        Kakeya.realRpowENN delta (-((B : ℝ) * eta))) :
    parentConstant ≤
      pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
        B eta delta := by
  refine parentConstant_le.trans ?_
  unfold pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
  apply
    pure_wz2_rpowENN_antitone
      delta_pos (power.delta_lt_one delta_le).le
  unfold pureWZ2Prop62MetricParentsV4FourDegreeScheduleStep
  nlinarith

theorem ratio_pos
    {delta : ℝ}
    (delta_pos : 0 < delta) :
    0 <
      pureWZ2Prop62MetricParentsV4FourDegreeRatio B eta delta := by
  unfold pureWZ2Prop62MetricParentsV4FourDegreeRatio
  rw [power.ambientConstant_toReal delta_pos]
  exact
    mul_pos (by norm_num)
      (Real.rpow_pos_of_pos delta_pos _)

theorem ratio_gt_one
    {delta : ℝ}
    (eta_pos : 0 < eta)
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ power.delta0) :
    1 <
      pureWZ2Prop62MetricParentsV4FourDegreeRatio B eta delta := by
  have one_le_real :
      1 ≤
        (pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
          B eta delta).toReal := by
    simpa only [ENNReal.toReal_one] using
      ENNReal.toReal_mono
        power.ambientConstant_finite
        (power.one_le_ambientConstant eta_pos delta_pos delta_le)
  unfold pureWZ2Prop62MetricParentsV4FourDegreeRatio
  nlinarith

theorem requested_separation
    {delta : ℝ} :
    4 *
        (pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
          B eta delta).toReal ≤
      pureWZ2Prop62MetricParentsV4FourDegreeRatio B eta delta := by
  rfl

theorem reachDepth_pos
    (eta_pos : 0 < eta) :
    0 <
      pureWZ2Prop62MetricParentsV4FourDegreeReachDepth B eta := by
  unfold pureWZ2Prop62MetricParentsV4FourDegreeReachDepth
  exact Nat.ceil_pos.mpr (one_div_pos.mpr (power.step_pos eta_pos))

theorem depth_reaches
    {delta : ℝ}
    (eta_pos : 0 < eta)
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ power.delta0)
    (rho : Kakeya.Streamlined.AdmissibleScale delta) :
    1 ≤
      rho.1 *
        pureWZ2Prop62MetricParentsV4FourDegreeRatio B eta delta ^
          pureWZ2Prop62MetricParentsV4FourDegreeReachDepth B eta := by
  let step :=
    pureWZ2Prop62MetricParentsV4FourDegreeScheduleStep B eta
  let depth :=
    pureWZ2Prop62MetricParentsV4FourDegreeReachDepth B eta
  let C1 :=
    pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
      B eta delta
  let ratio :=
    pureWZ2Prop62MetricParentsV4FourDegreeRatio B eta delta
  have step_pos : 0 < step := power.step_pos eta_pos
  have ceil_ge :
      1 / step ≤ (depth : ℝ) := by
    exact Nat.le_ceil _
  have exponent_ge_one :
      1 ≤ step * (depth : ℝ) := by
    calc
      1 = step * (1 / step) := by
        field_simp [step_pos.ne']
      _ ≤ step * (depth : ℝ) := by
        gcongr
  have C1_real :
      C1.toReal = Real.rpow delta (-step) := by
    exact power.ambientConstant_toReal delta_pos
  have C1_real_pos : 0 < C1.toReal := by
    rw [C1_real]
    exact Real.rpow_pos_of_pos delta_pos _
  have C1_le_ratio : C1.toReal ≤ ratio := by
    dsimp only [ratio,
      pureWZ2Prop62MetricParentsV4FourDegreeRatio]
    nlinarith
  have C1_power :
      C1.toReal ^ depth =
        Real.rpow delta (-(step * (depth : ℝ))) := by
    rw [C1_real, rpow_nat_pow delta_pos]
    congr 1
    ring
  have ratio_power_lower :
      C1.toReal ^ depth ≤ ratio ^ depth := by
    exact pow_le_pow_left₀ C1_real_pos.le C1_le_ratio depth
  have inverse_le_C1_power :
      1 / delta ≤ C1.toReal ^ depth := by
    rw [C1_power]
    calc
      1 / delta = delta⁻¹ := one_div delta
      _ = Real.rpow delta (-1) := by
        calc
          delta⁻¹ = (Real.rpow delta 1)⁻¹ := by
            congr 1
            exact (Real.rpow_one delta).symm
          _ = Real.rpow delta (-1) :=
            (Real.rpow_neg delta_pos.le 1).symm
      _ ≤ Real.rpow delta (-(step * (depth : ℝ))) := by
        exact
          Real.rpow_le_rpow_of_exponent_ge
            delta_pos (power.delta_lt_one delta_le).le
            (by linarith)
  have inverse_le_ratio_power :
      1 / delta ≤ ratio ^ depth :=
    inverse_le_C1_power.trans ratio_power_lower
  have product_le :
      delta * (1 / delta) ≤ rho.1 * ratio ^ depth := by
    exact
      mul_le_mul rho.2.1 inverse_le_ratio_power
        (by positivity) (delta_pos.le.trans rho.2.1)
  simpa [depth, ratio, delta_pos.ne'] using product_le

theorem ratio_ennreal_eq
    {delta : ℝ}
    (delta_pos : 0 < delta) :
    ENNReal.ofReal
        (pureWZ2Prop62MetricParentsV4FourDegreeRatio B eta delta) =
      4 *
        pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
          B eta delta := by
  unfold pureWZ2Prop62MetricParentsV4FourDegreeRatio
  rw [ENNReal.ofReal_mul (by norm_num)]
  simp only [ENNReal.ofReal_ofNat]
  rw [ENNReal.ofReal_toReal power.ambientConstant_finite]

theorem exact_scaleWindow
    {delta : ℝ}
    (delta_pos : 0 < delta) :
    pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
          B eta delta *
        ENNReal.ofReal
          (pureWZ2Prop62MetricParentsV4FourDegreeRatio B eta delta) =
      4 *
        pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
          B eta delta ^ 2 := by
  rw [power.ratio_ennreal_eq delta_pos]
  ring

theorem scaleWindow_le
    {delta : ℝ}
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ power.delta0) :
    4 *
        pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
          B eta delta ^ 2 ≤
      Kakeya.realRpowENN delta
        (-((pureWZ2Prop62MetricParentsV4FourDegreeWindowPower
          D B : ℝ) * eta)) := by
  have combined :
      Kakeya.realRpowENN delta
            (-(((D + 1 : ℕ) : ℝ) * eta)) *
          pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
              B eta delta ^ 2 =
        Kakeya.realRpowENN delta
          (-((pureWZ2Prop62MetricParentsV4FourDegreeWindowPower
            D B : ℝ) * eta)) := by
    unfold pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
      pureWZ2Prop62MetricParentsV4FourDegreeScheduleStep
      pureWZ2Prop62MetricParentsV4FourDegreeWindowPower
    rw [pow_two, ← realRpowENN_add delta_pos,
      ← realRpowENN_add delta_pos]
    congr 1
    push_cast
    ring
  calc
    4 *
          pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
            B eta delta ^ 2 ≤
        Kakeya.realRpowENN delta
              (-(((D + 1 : ℕ) : ℝ) * eta)) *
            pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
              B eta delta ^ 2 := by
      gcongr
      exact power.four_le_density_gap delta_pos delta_le
    _ =
        Kakeya.realRpowENN delta
          (-((pureWZ2Prop62MetricParentsV4FourDegreeWindowPower
            D B : ℝ) * eta)) :=
      combined

noncomputable def requestedScaleSchedule
    {delta : ℝ}
    (eta_pos : 0 < eta)
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ power.delta0)
    (rho : Kakeya.Streamlined.AdmissibleScale delta) :
    PureWZ2Prop62RequestedScaleSchedule
      rho.1
      (pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
        B eta delta)
      (ENNReal.ofReal
        (pureWZ2Prop62MetricParentsV4FourDegreeRatio B eta delta)) :=
  pureWZ2Prop62RatioRequestedScaleSchedule
    rho.1
    (pureWZ2Prop62MetricParentsV4FourDegreeRatio B eta delta)
    (pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
      B eta delta)
    (pureWZ2Prop62MetricParentsV4FourDegreeReachDepth B eta)
    (delta_pos.trans_le rho.2.1)
    rho.2.2
    (power.ratio_gt_one eta_pos delta_pos delta_le)
    power.requested_separation
    (power.depth_reaches eta_pos delta_pos delta_le rho)

theorem requestedScaleSchedule_levelCount_le
    {delta : ℝ}
    (eta_pos : 0 < eta)
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ power.delta0)
    (rho : Kakeya.Streamlined.AdmissibleScale delta) :
    (power.requestedScaleSchedule eta_pos delta_pos delta_le rho
      ).levelCount ≤
      pureWZ2Prop62MetricParentsV4FourDegreeDepthBound D B eta := by
  exact
    pureWZ2Prop62RatioRequestedScaleSchedule_levelCount_le
      rho.1
      (pureWZ2Prop62MetricParentsV4FourDegreeRatio B eta delta)
      (pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
        B eta delta)
      (pureWZ2Prop62MetricParentsV4FourDegreeReachDepth B eta)
      (delta_pos.trans_le rho.2.1)
      rho.2.2
      (power.ratio_gt_one eta_pos delta_pos delta_le)
      power.requested_separation
      (power.depth_reaches eta_pos delta_pos delta_le rho)

end PureWZ2Prop62MetricParentsV4SchedulePowerCertificate

end Kakeya.Assouad

end
