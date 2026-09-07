import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CallerParameterAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientDensityPower
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientBaseSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientSourceColor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientAllScaleColorPreCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62RepresentativeParentScaledPacking
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientUpperCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyCenterCopyPacking
import Mathlib.Tactic

/-!
# Proposition 6.2 metric-parent master threshold

This module combines the four scalar thresholds used by the final
metric-parent construction:

* caller-parameter absorption;
* quotient-ledger mass absorption;
* quotient CWA power absorption;
* the downstream density-power threshold.

All four certificates are selected from their concrete public producers.
All fixed parameters occur before the resulting `delta0`; runtime scales and
caller radii occur only in the extraction lemmas.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The final CWA exponent depends only on `A`. -/
def pureWZ2Prop62MetricParentsV4CWAPower (A : ℕ) : ℕ :=
  8 * A

@[simp] theorem pureWZ2Prop62MetricParentsV4CWAPower_eq
    (A : ℕ) :
    pureWZ2Prop62MetricParentsV4CWAPower A = 8 * A :=
  rfl

theorem pureWZ2Prop62MetricParentsV4CWAPower_pos
    {A : ℕ} (A_ge_one : 1 ≤ A) :
    1 ≤ pureWZ2Prop62MetricParentsV4CWAPower A := by
  unfold pureWZ2Prop62MetricParentsV4CWAPower
  omega

/--
The existing quotient power budget lands at `6 * A`; on scales at most one,
that target is bounded by the corrected final target `8 * A`.
-/
theorem pureWZ2Prop62MetricParentsV4ProxyTarget_le_target
    {A : ℕ} {eta delta : ℝ}
    (eta_pos : 0 < eta)
    (delta_pos : 0 < delta)
    (delta_le_one : delta ≤ 1) :
    Kakeya.realRpowENN delta
        (-(pureWZ2Prop62ProxyQuotientCWAPower A : ℝ) * eta) ≤
      Kakeya.realRpowENN delta
        (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta) := by
  apply pure_wz2_rpowENN_antitone delta_pos delta_le_one
  unfold pureWZ2Prop62MetricParentsV4CWAPower
    pureWZ2Prop62ProxyQuotientCWAPower
  push_cast
  have A_nonneg : 0 ≤ (A : ℝ) := by positivity
  nlinarith

/-- Depth bound of the canonical caller-anchored geometric schedule. -/
def pureWZ2Prop62MetricParentsV4DepthBound
    (A : ℕ) (eta : ℝ) : ℕ :=
  pureWZ2Prop62CallerAnchoredDepthBound A eta

/--
Fixed all-scale source-color type.  It reserves one representative-parent
color at every possible coordinate of the canonical schedule, followed by the
original fine source-conflict color.
-/
abbrev PureWZ2Prop62MetricParentsV4AllScaleSourceColor
    (A : ℕ) (eta : ℝ) :=
  (Fin (pureWZ2Prop62MetricParentsV4DepthBound A eta) →
      Fin (pureWZ2Prop62RepresentativeParentScaledConflictDegree + 1)) ×
    PureWZ2Prop62ProxyQuotientSourceColor

/-- Fixed cardinality budget for the all-scale source color. -/
def pureWZ2Prop62MetricParentsV4AllScaleSourceColorBound
    (A : ℕ) (eta : ℝ) : ENNReal :=
  ((pureWZ2Prop62RepresentativeParentScaledConflictDegree + 1 : ℕ) :
      ENNReal) ^ pureWZ2Prop62MetricParentsV4DepthBound A eta *
    ((pureWZ2OrdinaryLineConflictDegree + 1 : ℕ) : ENNReal)

@[simp] theorem pureWZ2Prop62MetricParentsV4AllScaleSourceColor_card
    (A : ℕ) (eta : ℝ) :
    (Fintype.card
      (PureWZ2Prop62MetricParentsV4AllScaleSourceColor A eta) : ENNReal) =
        pureWZ2Prop62MetricParentsV4AllScaleSourceColorBound A eta := by
  simp [PureWZ2Prop62MetricParentsV4AllScaleSourceColor,
    pureWZ2Prop62MetricParentsV4AllScaleSourceColorBound]

theorem pureWZ2Prop62MetricParentsV4AllScaleSourceColorBound_ne_top
    (A : ℕ) (eta : ℝ) :
    pureWZ2Prop62MetricParentsV4AllScaleSourceColorBound A eta ≠ ⊤ := by
  unfold pureWZ2Prop62MetricParentsV4AllScaleSourceColorBound
  exact ENNReal.mul_ne_top
    (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    ENNReal.coe_ne_top

/-- Fixed base-selection loss for the canonical depth and caller stride. -/
def pureWZ2Prop62MetricParentsV4BaseStructural
    (A : ℕ) (eta c0 : ℝ) : ENNReal :=
  pureWZ2Prop62ProxyQuotientBaseSelectionFixedBound
    (pureWZ2Prop62MetricParentsV4DepthBound A eta)
    (pureWZ2Prop62CallerStrideBase c0)

theorem pureWZ2Prop62MetricParentsV4BaseStructural_ne_top
    (A : ℕ) (eta c0 : ℝ) :
    pureWZ2Prop62MetricParentsV4BaseStructural A eta c0 ≠ ⊤ := by
  unfold pureWZ2Prop62MetricParentsV4BaseStructural
  unfold pureWZ2Prop62ProxyQuotientBaseSelectionFixedBound
  exact ENNReal.mul_ne_top
    (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    (ENNReal.pow_ne_top ENNReal.coe_ne_top)

/-- The six canonical fixed bounds used by the actual quotient mass ledger. -/
noncomputable def pureWZ2Prop62MetricParentsV4MassBounds
    (A : ℕ) (eta c0 : ℝ) :
    PureWZ2Prop62ProxyQuotientMassFixedBounds A eta c0 :=
  pureWZ2Prop62ProxyQuotientGeometryMassBounds
    A eta c0
    (pureWZ2Prop62MetricParentsV4DepthBound A eta)
    (PureWZ2Prop62MetricParentsV4AllScaleSourceColor A eta)
    (pureWZ2Prop62MetricParentsV4BaseStructural A eta c0)
    (pureWZ2Prop62MetricParentsV4BaseStructural_ne_top A eta c0)

@[simp] theorem pureWZ2Prop62MetricParentsV4MassBounds_sourceColor
    (A : ℕ) (eta c0 : ℝ) :
    (pureWZ2Prop62MetricParentsV4MassBounds A eta c0).sourceColor =
      pureWZ2Prop62MetricParentsV4AllScaleSourceColorBound A eta := by
  unfold pureWZ2Prop62MetricParentsV4MassBounds
  change
    (Fintype.card
      (PureWZ2Prop62MetricParentsV4AllScaleSourceColor A eta) : ENNReal) =
        pureWZ2Prop62MetricParentsV4AllScaleSourceColorBound A eta
  exact pureWZ2Prop62MetricParentsV4AllScaleSourceColor_card A eta

/--
The cardinality of an all-scale source color for any schedule below the
canonical depth is bounded by the fixed source-color entry of `massBounds`.
-/
theorem pureWZ2Prop62MetricParentsV4AllScaleSourceColor_card_le
    (A : ℕ) (eta c0 : ℝ)
    {levelCount : ℕ}
    (levelCount_le :
      levelCount ≤ pureWZ2Prop62MetricParentsV4DepthBound A eta) :
    (Fintype.card
      ((Fin levelCount →
          Fin (pureWZ2Prop62RepresentativeParentScaledConflictDegree + 1)) ×
        PureWZ2Prop62ProxyQuotientSourceColor) : ENNReal) ≤
      (pureWZ2Prop62MetricParentsV4MassBounds A eta c0).sourceColor := by
  rw [pureWZ2Prop62MetricParentsV4MassBounds_sourceColor]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_pow]
  exact mul_le_mul_right' (pow_le_pow_right₀ (by simp) levelCount_le) _

/--
The concrete all-scale pre-core source loss fits the canonical fixed mass
budget whenever its schedule has canonical depth and every coordinate uses
the representative-parent packing degree.
-/
theorem
    PureWZ2Prop62ProxyQuotientAllScaleColorPreCoreData.sourceColorLoss_le_metricParentsV4MassBounds
    {A : ℕ} {eta c0 delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    {metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {upperColoring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {conflictScale : Fin schedule.levelCount → ℝ}
    (data :
      PureWZ2Prop62ProxyQuotientAllScaleColorPreCoreData
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metric upperColoring conflictScale
          (fun _ =>
            pureWZ2Prop62RepresentativeParentScaledConflictDegree))
    (levelCount_le :
      schedule.levelCount ≤
        pureWZ2Prop62MetricParentsV4DepthBound A eta) :
    data.adapter.preCore.retention.sourceColorLoss ≤
      (pureWZ2Prop62MetricParentsV4MassBounds A eta c0).sourceColor := by
  rw [pureWZ2Prop62MetricParentsV4MassBounds_sourceColor]
  exact
    data.sourceColorLoss_le_depthBound
      (fun _ => le_rfl) levelCount_le

/-- Fixed density coefficient produced from the same canonical mass ledger. -/
def pureWZ2Prop62MetricParentsV4DensityFixedLoss
    (A : ℕ) (eta c0 : ℝ) : ENNReal :=
  pureWZ2Prop62ProxyQuotientDensityFixedLoss
    A eta c0 (pureWZ2Prop62MetricParentsV4MassBounds A eta c0)

theorem pureWZ2Prop62MetricParentsV4DensityFixedLoss_ne_top
    (A : ℕ) (eta c0 : ℝ) :
    pureWZ2Prop62MetricParentsV4DensityFixedLoss A eta c0 ≠ ⊤ :=
  pureWZ2Prop62ProxyQuotientDensityFixedLoss_ne_top
    A eta c0 (pureWZ2Prop62MetricParentsV4MassBounds A eta c0)

/-- The fixed inserted-fibre coefficient, including the final rescaling loss. -/
def pureWZ2Prop62MetricParentsV4InsertedCoefficient : ENNReal :=
  81000000 * 4000000

/--
The John loss for the representative middle family, stated here from the
fixed packing factor to avoid an import cycle through the middle route.
-/
def pureWZ2Prop62MetricParentsV4RepresentativeMiddleJohnLoss : ENNReal :=
  27 * ENNReal.ofReal
    (pureWZ2Prop62RepresentativeParentScaledFactor ^ 3)

@[simp] theorem
    pureWZ2Prop62MetricParentsV4RepresentativeMiddleJohnLoss_eq :
    pureWZ2Prop62MetricParentsV4RepresentativeMiddleJohnLoss =
      27 * ENNReal.ofReal
        (pureWZ2Prop62RepresentativeParentScaledFactor ^ 3) :=
  rfl

/-- Fixed coefficient for paying the representative-middle John loss. -/
def pureWZ2Prop62MetricParentsV4RepresentativeMiddleCoefficient : ENNReal :=
  81000000 *
    pureWZ2Prop62MetricParentsV4RepresentativeMiddleJohnLoss

/-- The fixed geometric coefficient in the upper-parent body CWA. -/
def pureWZ2Prop62MetricParentsV4UpperCoefficient : ENNReal :=
  max
    (pureWZ2Prop62UpperEnvelopeGeometricLoss * 2)
    pureWZ2Prop62MetricParentsV4RepresentativeMiddleCoefficient

/-- The fixed coefficient in upper strict-fibre uniformity. -/
def pureWZ2Prop62MetricParentsV4UniformityCoefficient : ENNReal :=
  2 * (pureWZ2Prop62ProxyCenterCopyPackingBound : ENNReal)

/-- Fixed coefficient required by the scaled requested-scale route. -/
def pureWZ2Prop62MetricParentsV4ScaledWindowCoefficient : ENNReal :=
  100 *
    ENNReal.ofReal pureWZ2Prop62RepresentativeParentScaledFactor

/--
Fixed coefficient absorbing both the old caller-anchored fifth-power window
and the representative-scaled route window.
-/
def pureWZ2Prop62MetricParentsV4WindowCoefficient : ENNReal :=
  max 81000000 pureWZ2Prop62MetricParentsV4ScaledWindowCoefficient

theorem pureWZ2Prop62MetricParentsV4RepresentativeMiddleCoefficient_le_upper :
    pureWZ2Prop62MetricParentsV4RepresentativeMiddleCoefficient ≤
      pureWZ2Prop62MetricParentsV4UpperCoefficient :=
  le_max_right _ _

theorem pureWZ2Prop62MetricParentsV4ScaledWindowCoefficient_le_window :
    pureWZ2Prop62MetricParentsV4ScaledWindowCoefficient ≤
      pureWZ2Prop62MetricParentsV4WindowCoefficient :=
  le_max_right _ _

/-- All data fixed before choosing the final small scale. -/
structure PureWZ2Prop62MetricParentsV4ThresholdInput
    (A : ℕ) (epsilon eta c0 : ℝ) where
  A_ge_one : 1 ≤ A
  epsilon_pos : 0 < epsilon
  eta_pos : 0 < eta
  loss_small :
    (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta ≤
      epsilon / 100
  c0_pos : 0 < c0
  massBounds :
    PureWZ2Prop62ProxyQuotientMassFixedBounds A eta c0
  powerFixedLoss : ENNReal
  powerInsertedCoefficient : ENNReal
  powerUpperCoefficient : ENNReal
  powerUniformityCoefficient : ENNReal
  powerWindowCoefficient : ENNReal
  powerFixedLoss_ne_top : powerFixedLoss ≠ ⊤
  powerInsertedCoefficient_ne_top :
    powerInsertedCoefficient ≠ ⊤
  powerUpperCoefficient_ne_top :
    powerUpperCoefficient ≠ ⊤
  powerUniformityCoefficient_ne_top :
    powerUniformityCoefficient ≠ ⊤
  powerWindowCoefficient_ne_top :
    powerWindowCoefficient ≠ ⊤
  representativeMiddleCoefficient_le_upper :
    pureWZ2Prop62MetricParentsV4RepresentativeMiddleCoefficient ≤
      powerUpperCoefficient
  scaledWindowCoefficient_le_window :
    pureWZ2Prop62MetricParentsV4ScaledWindowCoefficient ≤
      powerWindowCoefficient

/--
Canonical fixed input for the master threshold.

Every coefficient is determined by `A`, `eta`, and `c0`.  In particular the
power budget uses the density loss produced from the very same mass bounds.
-/
noncomputable def pureWZ2Prop62MetricParentsV4ThresholdInput
    (A : ℕ) (epsilon eta c0 : ℝ)
    (A_ge_one : 1 ≤ A)
    (epsilon_pos : 0 < epsilon)
    (eta_pos : 0 < eta)
    (loss_small :
      (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta ≤
        epsilon / 100)
    (c0_pos : 0 < c0) :
    PureWZ2Prop62MetricParentsV4ThresholdInput A epsilon eta c0 where
  A_ge_one := A_ge_one
  epsilon_pos := epsilon_pos
  eta_pos := eta_pos
  loss_small := loss_small
  c0_pos := c0_pos
  massBounds :=
    pureWZ2Prop62MetricParentsV4MassBounds A eta c0
  powerFixedLoss :=
    pureWZ2Prop62MetricParentsV4DensityFixedLoss A eta c0
  powerInsertedCoefficient :=
    pureWZ2Prop62MetricParentsV4InsertedCoefficient
  powerUpperCoefficient :=
    pureWZ2Prop62MetricParentsV4UpperCoefficient
  powerUniformityCoefficient :=
    pureWZ2Prop62MetricParentsV4UniformityCoefficient
  powerWindowCoefficient :=
    pureWZ2Prop62MetricParentsV4WindowCoefficient
  powerFixedLoss_ne_top :=
    pureWZ2Prop62MetricParentsV4DensityFixedLoss_ne_top A eta c0
  powerInsertedCoefficient_ne_top := by
    unfold pureWZ2Prop62MetricParentsV4InsertedCoefficient
    exact ENNReal.mul_ne_top (by norm_num) (by norm_num)
  powerUpperCoefficient_ne_top := by
    unfold pureWZ2Prop62MetricParentsV4UpperCoefficient
    apply max_ne_top
    · unfold pureWZ2Prop62UpperEnvelopeGeometricLoss
      unfold pureWZ2Prop62UpperEnvelopeJohnLoss
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
          (by norm_num))
        (by norm_num)
    · unfold
        pureWZ2Prop62MetricParentsV4RepresentativeMiddleCoefficient
        pureWZ2Prop62MetricParentsV4RepresentativeMiddleJohnLoss
      exact ENNReal.mul_ne_top
        (by norm_num)
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
  powerUniformityCoefficient_ne_top := by
    unfold pureWZ2Prop62MetricParentsV4UniformityCoefficient
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
  powerWindowCoefficient_ne_top := by
    unfold pureWZ2Prop62MetricParentsV4WindowCoefficient
    apply max_ne_top (by norm_num)
    unfold pureWZ2Prop62MetricParentsV4ScaledWindowCoefficient
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  representativeMiddleCoefficient_le_upper :=
    pureWZ2Prop62MetricParentsV4RepresentativeMiddleCoefficient_le_upper
  scaledWindowCoefficient_le_window :=
    pureWZ2Prop62MetricParentsV4ScaledWindowCoefficient_le_window

@[simp] theorem pureWZ2Prop62MetricParentsV4ThresholdInput_massBounds
    (A : ℕ) (epsilon eta c0 : ℝ)
    (A_ge_one : 1 ≤ A)
    (epsilon_pos : 0 < epsilon)
    (eta_pos : 0 < eta)
    (loss_small :
      (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta ≤
        epsilon / 100)
    (c0_pos : 0 < c0) :
    (pureWZ2Prop62MetricParentsV4ThresholdInput
      A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos
      ).massBounds =
        pureWZ2Prop62MetricParentsV4MassBounds A eta c0 :=
  rfl

@[simp] theorem pureWZ2Prop62MetricParentsV4ThresholdInput_powerFixedLoss
    (A : ℕ) (epsilon eta c0 : ℝ)
    (A_ge_one : 1 ≤ A)
    (epsilon_pos : 0 < epsilon)
    (eta_pos : 0 < eta)
    (loss_small :
      (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta ≤
        epsilon / 100)
    (c0_pos : 0 < c0) :
    (pureWZ2Prop62MetricParentsV4ThresholdInput
      A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos
      ).powerFixedLoss =
        pureWZ2Prop62ProxyQuotientDensityFixedLoss A eta c0
          (pureWZ2Prop62MetricParentsV4MassBounds A eta c0) :=
  rfl

@[simp] theorem pureWZ2Prop62MetricParentsV4ThresholdInput_powerCoefficients
    (A : ℕ) (epsilon eta c0 : ℝ)
    (A_ge_one : 1 ≤ A)
    (epsilon_pos : 0 < epsilon)
    (eta_pos : 0 < eta)
    (loss_small :
      (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta ≤
        epsilon / 100)
    (c0_pos : 0 < c0) :
    let input :=
      pureWZ2Prop62MetricParentsV4ThresholdInput
        A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos
    input.powerInsertedCoefficient =
        pureWZ2Prop62MetricParentsV4InsertedCoefficient ∧
      input.powerUpperCoefficient =
        pureWZ2Prop62MetricParentsV4UpperCoefficient ∧
      input.powerUniformityCoefficient =
        pureWZ2Prop62MetricParentsV4UniformityCoefficient ∧
      input.powerWindowCoefficient =
        pureWZ2Prop62MetricParentsV4WindowCoefficient :=
  ⟨rfl, rfl, rfl, rfl⟩

namespace PureWZ2Prop62MetricParentsV4ThresholdInput

variable
    {A : ℕ} {epsilon eta c0 : ℝ}
    (input :
      PureWZ2Prop62MetricParentsV4ThresholdInput
        A epsilon eta c0)

/--
The corrected `8 * A` loss hypothesis supplies the legacy `6 * A` hypothesis
used internally by the caller-parameter threshold.
-/
theorem caller_loss_small
    (input :
      PureWZ2Prop62MetricParentsV4ThresholdInput
        A epsilon eta c0) :
    6 * (A : ℝ) * eta ≤ epsilon / 100 := by
  calc
    6 * (A : ℝ) * eta ≤
        (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta := by
      rw [pureWZ2Prop62MetricParentsV4CWAPower_eq]
      push_cast
      have A_nonneg : 0 ≤ (A : ℝ) := by positivity
      nlinarith [input.eta_pos]
    _ ≤ epsilon / 100 := input.loss_small

/-- Positivity of the caller-dependent constant used by the power budget. -/
theorem callerK_pos
    (input :
      PureWZ2Prop62MetricParentsV4ThresholdInput
        A epsilon eta c0) :
    0 < pureWZ2Prop62CallerK c0 := by
  unfold pureWZ2Prop62CallerK
  exact div_pos (by norm_num) <|
    lt_min input.c0_pos zero_lt_one

/-- Threshold supplied by caller-parameter absorption. -/
noncomputable def callerThreshold : ℝ :=
  Classical.choose <|
    exists_pureWZ2Prop62CallerParameterAbsorption
      A input.A_ge_one epsilon eta c0 input.epsilon_pos
      input.eta_pos input.caller_loss_small input.c0_pos

theorem callerThreshold_pos :
    0 < input.callerThreshold :=
  (Classical.choose_spec <|
    exists_pureWZ2Prop62CallerParameterAbsorption
      A input.A_ge_one epsilon eta c0 input.epsilon_pos
      input.eta_pos input.caller_loss_small input.c0_pos).1

theorem callerThreshold_le_one_hundred :
    input.callerThreshold ≤ 1 / 100 :=
  (Classical.choose_spec <|
    exists_pureWZ2Prop62CallerParameterAbsorption
      A input.A_ge_one epsilon eta c0 input.epsilon_pos
      input.eta_pos input.caller_loss_small input.c0_pos).2.1

/--
Threshold at which the fixed caller factor `4 * K` is absorbed by the
representative-parent enlargement factor times one copy of `Cstar`.
-/
noncomputable def representativeOverlapThreshold : ℝ :=
  Classical.choose <|
    exists_delta_realRpowENN_bound
      (ENNReal.ofReal
        (4 * pureWZ2Prop62CallerK c0 /
          pureWZ2Prop62RepresentativeParentScaledFactor))
      ENNReal.ofReal_ne_top
      (pureWZ2Prop62CallerLoss_pos input.A_ge_one input.eta_pos)

theorem representativeOverlapThreshold_pos :
    0 < input.representativeOverlapThreshold :=
  (Classical.choose_spec <|
    exists_delta_realRpowENN_bound
      (ENNReal.ofReal
        (4 * pureWZ2Prop62CallerK c0 /
          pureWZ2Prop62RepresentativeParentScaledFactor))
      ENNReal.ofReal_ne_top
      (pureWZ2Prop62CallerLoss_pos input.A_ge_one input.eta_pos)).1

theorem representativeOverlapThreshold_le_one :
    input.representativeOverlapThreshold ≤ 1 :=
  (Classical.choose_spec <|
    exists_delta_realRpowENN_bound
      (ENNReal.ofReal
        (4 * pureWZ2Prop62CallerK c0 /
          pureWZ2Prop62RepresentativeParentScaledFactor))
      ENNReal.ofReal_ne_top
      (pureWZ2Prop62CallerLoss_pos input.A_ge_one input.eta_pos)).2.1

/--
Threshold at which one copy of `Cstar` absorbs the factor `400 * K`.  This is
the fixed gate needed both for the strict route floor and for the top case.
-/
noncomputable def routeFloorThreshold : ℝ :=
  Classical.choose <|
    exists_delta_realRpowENN_bound
      (ENNReal.ofReal (400 * pureWZ2Prop62CallerK c0))
      ENNReal.ofReal_ne_top
      (pureWZ2Prop62CallerLoss_pos input.A_ge_one input.eta_pos)

theorem routeFloorThreshold_pos :
    0 < input.routeFloorThreshold :=
  (Classical.choose_spec <|
    exists_delta_realRpowENN_bound
      (ENNReal.ofReal (400 * pureWZ2Prop62CallerK c0))
      ENNReal.ofReal_ne_top
      (pureWZ2Prop62CallerLoss_pos input.A_ge_one input.eta_pos)).1

theorem routeFloorThreshold_le_one :
    input.routeFloorThreshold ≤ 1 :=
  (Classical.choose_spec <|
    exists_delta_realRpowENN_bound
      (ENNReal.ofReal (400 * pureWZ2Prop62CallerK c0))
      ENNReal.ofReal_ne_top
      (pureWZ2Prop62CallerLoss_pos input.A_ge_one input.eta_pos)).2.1

/-- Threshold supplied by the quotient power budget. -/
noncomputable def powerThreshold : ℝ :=
  Classical.choose <|
    exists_pureWZ2Prop62ProxyQuotientPowerBudget
      A input.A_ge_one eta (pureWZ2Prop62CallerK c0) input.eta_pos
      input.callerK_pos.le
      input.powerFixedLoss input.powerInsertedCoefficient
      input.powerUpperCoefficient input.powerUniformityCoefficient
      input.powerWindowCoefficient input.powerFixedLoss_ne_top
      input.powerInsertedCoefficient_ne_top
      input.powerUpperCoefficient_ne_top
      input.powerUniformityCoefficient_ne_top
      input.powerWindowCoefficient_ne_top

theorem powerThreshold_pos :
    0 < input.powerThreshold :=
  (Classical.choose_spec <|
    exists_pureWZ2Prop62ProxyQuotientPowerBudget
      A input.A_ge_one eta (pureWZ2Prop62CallerK c0) input.eta_pos
      input.callerK_pos.le
      input.powerFixedLoss input.powerInsertedCoefficient
      input.powerUpperCoefficient input.powerUniformityCoefficient
      input.powerWindowCoefficient input.powerFixedLoss_ne_top
      input.powerInsertedCoefficient_ne_top
      input.powerUpperCoefficient_ne_top
      input.powerUniformityCoefficient_ne_top
      input.powerWindowCoefficient_ne_top).1

theorem powerThreshold_le_one :
    input.powerThreshold ≤ 1 :=
  (Classical.choose_spec <|
    exists_pureWZ2Prop62ProxyQuotientPowerBudget
      A input.A_ge_one eta (pureWZ2Prop62CallerK c0) input.eta_pos
      input.callerK_pos.le
      input.powerFixedLoss input.powerInsertedCoefficient
      input.powerUpperCoefficient input.powerUniformityCoefficient
      input.powerWindowCoefficient input.powerFixedLoss_ne_top
      input.powerInsertedCoefficient_ne_top
      input.powerUpperCoefficient_ne_top
      input.powerUniformityCoefficient_ne_top
      input.powerWindowCoefficient_ne_top).2.1

/-- Concrete quotient density-power certificate selected before runtime scales. -/
noncomputable def densityPowerCertificate :
    PureWZ2Prop62ProxyQuotientDensityPowerCertificate A eta c0 :=
  Classical.choice <|
    exists_pureWZ2Prop62ProxyQuotientDensityPowerCertificate
      A input.A_ge_one eta c0 input.eta_pos

/-- Threshold supplied by the concrete quotient density-power certificate. -/
noncomputable def densityPowerThreshold : ℝ :=
  input.densityPowerCertificate.delta0

theorem densityPowerThreshold_pos :
    0 < input.densityPowerThreshold :=
  input.densityPowerCertificate.delta0_pos

theorem densityPowerThreshold_le_one :
    input.densityPowerThreshold ≤ 1 :=
  input.densityPowerCertificate.delta0_le_one

/-- One threshold below every scalar threshold used by the final caller. -/
noncomputable def threshold : ℝ :=
  min input.callerThreshold <|
    min
      (pureWZ2Prop62ProxyQuotientMassThreshold
        A eta c0 input.massBounds) <|
      min input.powerThreshold <|
        min input.densityPowerThreshold
          (min input.representativeOverlapThreshold
            input.routeFloorThreshold)

theorem threshold_pos :
    0 < input.threshold := by
  exact
    lt_min input.callerThreshold_pos <|
      lt_min
        (pureWZ2Prop62ProxyQuotientMassThreshold_pos
          A eta c0 input.massBounds) <|
        lt_min input.powerThreshold_pos
          (lt_min input.densityPowerThreshold_pos
            (lt_min input.representativeOverlapThreshold_pos
              input.routeFloorThreshold_pos))

theorem threshold_le_one_hundred :
    input.threshold ≤ 1 / 100 := by
  exact
    (min_le_left _ _).trans
      input.callerThreshold_le_one_hundred

theorem threshold_le_caller :
    input.threshold ≤ input.callerThreshold :=
  min_le_left _ _

theorem threshold_le_mass :
    input.threshold ≤
      pureWZ2Prop62ProxyQuotientMassThreshold
        A eta c0 input.massBounds :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem threshold_le_power :
    input.threshold ≤ input.powerThreshold :=
  (min_le_right _ _).trans <|
    (min_le_right _ _).trans (min_le_left _ _)

theorem threshold_le_densityPower :
    input.threshold ≤ input.densityPowerThreshold :=
  (min_le_right _ _).trans <|
    (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)

theorem threshold_le_representativeOverlap :
    input.threshold ≤ input.representativeOverlapThreshold :=
  (min_le_right _ _).trans <|
    (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)

theorem threshold_le_routeFloor :
    input.threshold ≤ input.routeFloorThreshold :=
  (min_le_right _ _).trans <|
    (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)

/-- Extract the complete caller-parameter certificate below the master threshold. -/
theorem caller_certificate
    {delta rho : ℝ}
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ input.threshold)
    (rho_pos : 0 < rho)
    (rho_le_one : rho ≤ 1)
    (rho_lower :
      Real.rpow delta (1 - epsilon) ≤ rho) :
    Nonempty
      (PureWZ2Prop62CallerParameterAbsorptionData
        A epsilon eta c0 delta rho) := by
  exact
    (Classical.choose_spec <|
      exists_pureWZ2Prop62CallerParameterAbsorption
        A input.A_ge_one epsilon eta c0 input.epsilon_pos
        input.eta_pos input.caller_loss_small input.c0_pos).2.2
      delta_pos (delta_le.trans input.threshold_le_caller)
      rho_pos rho_le_one rho_lower

/--
The fixed representative enlargement absorbs the caller factor required at
the top/descendant overlap.
-/
theorem representativeOverlap
    {delta : ℝ}
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ input.threshold) :
    4 * pureWZ2Prop62CallerK c0 ≤
      pureWZ2Prop62RepresentativeParentScaledFactor *
        (pureWZ2Prop62CallerCstar delta A eta).toReal := by
  have fixedBound :
      ENNReal.ofReal
          (4 * pureWZ2Prop62CallerK c0 /
            pureWZ2Prop62RepresentativeParentScaledFactor) ≤
        pureWZ2Prop62CallerCstar delta A eta := by
    simpa [pureWZ2Prop62CallerCstar] using
      (Classical.choose_spec <|
        exists_delta_realRpowENN_bound
          (ENNReal.ofReal
            (4 * pureWZ2Prop62CallerK c0 /
              pureWZ2Prop62RepresentativeParentScaledFactor))
          ENNReal.ofReal_ne_top
          (pureWZ2Prop62CallerLoss_pos input.A_ge_one input.eta_pos)).2.2
        delta delta_pos
          (delta_le.trans input.threshold_le_representativeOverlap)
  have CstarFinite :
      pureWZ2Prop62CallerCstar delta A eta ≠ ⊤ := by
    simp [pureWZ2Prop62CallerCstar, Kakeya.realRpowENN]
  have fixedRealBound :
      4 * pureWZ2Prop62CallerK c0 /
          pureWZ2Prop62RepresentativeParentScaledFactor ≤
        (pureWZ2Prop62CallerCstar delta A eta).toReal := by
    have converted := ENNReal.toReal_mono CstarFinite fixedBound
    rw [ENNReal.toReal_ofReal] at converted
    · exact converted
    · exact div_nonneg
        (mul_nonneg (by norm_num) input.callerK_pos.le)
        (by positivity)
  have factorPos :
      0 <
        (pureWZ2Prop62RepresentativeParentScaledFactor : ℝ) := by
    rw [pureWZ2Prop62RepresentativeParentScaledFactor_eq]
    norm_num
  rw [div_le_iff₀ factorPos] at fixedRealBound
  simpa [mul_comm] using fixedRealBound

/--
Caller-record form of the representative overlap gate, ready for the
anchored schedule pipeline.
-/
theorem representativeOverlap_of_caller
    {delta rho : ℝ}
    (caller :
      PureWZ2Prop62CallerParameterAbsorptionData
        A epsilon eta c0 delta rho)
    (delta_le : delta ≤ input.threshold) :
    4 * caller.parameters.K ≤
      pureWZ2Prop62RepresentativeParentScaledFactor *
        (pureWZ2Prop62CallerCstar delta A eta).toReal := by
  rw [caller.parameters.K_eq]
  exact input.representativeOverlap caller.delta_pos delta_le

/--
The stronger fixed route gate: one copy of `Cstar` absorbs `400 * K`.
-/
theorem routeCallerFactor_le_Cstar
    {delta rho : ℝ}
    (caller :
      PureWZ2Prop62CallerParameterAbsorptionData
        A epsilon eta c0 delta rho)
    (delta_le : delta ≤ input.threshold) :
    400 * caller.parameters.K ≤
      (pureWZ2Prop62CallerCstar delta A eta).toReal := by
  have fixedBound :
      ENNReal.ofReal (400 * pureWZ2Prop62CallerK c0) ≤
        pureWZ2Prop62CallerCstar delta A eta := by
    simpa [pureWZ2Prop62CallerCstar] using
      (Classical.choose_spec <|
        exists_delta_realRpowENN_bound
          (ENNReal.ofReal (400 * pureWZ2Prop62CallerK c0))
          ENNReal.ofReal_ne_top
          (pureWZ2Prop62CallerLoss_pos input.A_ge_one input.eta_pos)).2.2
        delta caller.delta_pos
          (delta_le.trans input.threshold_le_routeFloor)
  have CstarFinite :
      pureWZ2Prop62CallerCstar delta A eta ≠ ⊤ :=
    caller.Cstar_finite
  have converted := ENNReal.toReal_mono CstarFinite fixedBound
  rw [ENNReal.toReal_ofReal] at converted
  · simpa [caller.parameters.K_eq] using converted
  · exact mul_nonneg (by norm_num) input.callerK_pos.le

/-- The corrected final loss is strictly smaller than `epsilon`. -/
theorem finalLoss_lt_epsilon
    (input :
      PureWZ2Prop62MetricParentsV4ThresholdInput
        A epsilon eta c0) :
    (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta <
      epsilon := by
  exact input.loss_small.trans_lt (by
    nlinarith [input.epsilon_pos])

/--
The strict scalar inequality underlying the route floor: after the caller
factor is absorbed, seven copies of `Cstar` leave a strict exponent gap.  The
public `8 * A` loss hypothesis is stronger than the seven-copy bound used
here.
-/
theorem caller_mul_Cstar_six_mul_delta_lt_rho
    {delta rho : ℝ}
    (caller :
      PureWZ2Prop62CallerParameterAbsorptionData
        A epsilon eta c0 delta rho)
    (delta_le : delta ≤ input.threshold)
    (rho_lower : Real.rpow delta (1 - epsilon) ≤ rho) :
    caller.parameters.K *
          (pureWZ2Prop62CallerCstar delta A eta).toReal ^ 6 * delta <
      rho := by
  let CstarReal :=
    (pureWZ2Prop62CallerCstar delta A eta).toReal
  have CstarReal_pos : 0 < CstarReal :=
    ENNReal.toReal_pos
      (ne_of_gt <| (show (0 : ENNReal) < 4 by norm_num).trans_le
        caller.Cstar_four)
      caller.Cstar_finite
  have K_le_Cstar :
      caller.parameters.K ≤ CstarReal := by
    have strong := input.routeCallerFactor_le_Cstar caller delta_le
    dsimp only [CstarReal]
    nlinarith [caller.parameters.K_pos]
  have product_le :
      caller.parameters.K * CstarReal ^ 6 * delta ≤
        CstarReal ^ 7 * delta := by
    have first :
        caller.parameters.K * CstarReal ^ 6 ≤
          CstarReal * CstarReal ^ 6 :=
      mul_le_mul_of_nonneg_right K_le_Cstar
        (pow_nonneg CstarReal_pos.le 6)
    exact
      mul_le_mul_of_nonneg_right
        (first.trans_eq (by ring)) caller.delta_pos.le
  have CstarReal_eq :
      CstarReal =
        Real.rpow delta (-((A : ℝ) * eta)) := by
    unfold CstarReal pureWZ2Prop62CallerCstar Kakeya.realRpowENN
    exact
      ENNReal.toReal_ofReal
        (Real.rpow_nonneg caller.delta_pos.le _)
  have sevenLoss_lt_epsilon :
      7 * (A : ℝ) * eta < epsilon := by
    calc
      7 * (A : ℝ) * eta ≤
          (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta := by
        rw [pureWZ2Prop62MetricParentsV4CWAPower_eq]
        push_cast
        have A_nonneg : 0 ≤ (A : ℝ) := by positivity
        nlinarith [input.eta_pos]
      _ ≤ epsilon / 100 := input.loss_small
      _ < epsilon := by nlinarith [input.epsilon_pos]
  have seventhPower :
      CstarReal ^ 7 * delta =
        Real.rpow delta
          (1 - 7 * (A : ℝ) * eta) := by
    rw [CstarReal_eq]
    have powerEq :
        (Real.rpow delta (-((A : ℝ) * eta))) ^ 7 =
          Real.rpow delta (-((A : ℝ) * eta) * (7 : ℝ)) :=
      (Real.rpow_mul_natCast caller.delta_pos.le _ 7).symm
    calc
      (Real.rpow delta (-((A : ℝ) * eta))) ^ 7 * delta =
          Real.rpow delta (-((A : ℝ) * eta) * (7 : ℝ)) *
            delta := by rw [powerEq]
      _ =
          Real.rpow delta (-((A : ℝ) * eta) * (7 : ℝ)) *
            Real.rpow delta 1 := by
        rw [show Real.rpow delta 1 = delta from Real.rpow_one delta]
      _ =
          Real.rpow delta
            (-((A : ℝ) * eta) * (7 : ℝ) + 1) :=
        (Real.rpow_add caller.delta_pos _ _).symm
      _ =
          Real.rpow delta
            (1 - 7 * (A : ℝ) * eta) := by
        congr 1 <;> ring
  have exponent_lt :
      1 - epsilon <
        1 - 7 * (A : ℝ) * eta := by
    linarith
  have power_lt :
      Real.rpow delta
          (1 - 7 * (A : ℝ) * eta) <
        Real.rpow delta (1 - epsilon) :=
    Real.rpow_lt_rpow_of_exponent_gt
      caller.delta_pos caller.delta_lt_one exponent_lt
  exact product_le.trans_lt <|
    seventhPower.symm ▸ power_lt.trans_le rho_lower

/--
Route floor gate from the literal caller-anchor lower bound.  This is stated
for an arbitrary packet scale so it can be used directly after constructing
the anchored laminar schedule.
-/
theorem routeFloorGate
    {delta rho packetScale : ℝ}
    (caller :
      PureWZ2Prop62CallerParameterAbsorptionData
        A epsilon eta c0 delta rho)
    (delta_le : delta ≤ input.threshold)
    (rho_lower : Real.rpow delta (1 - epsilon) ≤ rho)
    (packetScale_pos : 0 < packetScale)
    (q0_le_packetScale :
      rho /
          (caller.parameters.K *
            (pureWZ2Prop62CallerCstar delta A eta).toReal) ≤
        packetScale) :
    (pureWZ2Prop62CallerCstar delta A eta) ^ 5 *
        ENNReal.ofReal delta <
      ENNReal.ofReal packetScale := by
  let CstarReal :=
    (pureWZ2Prop62CallerCstar delta A eta).toReal
  have CstarReal_pos : 0 < CstarReal :=
    ENNReal.toReal_pos
      (ne_of_gt <| (show (0 : ENNReal) < 4 by norm_num).trans_le
        caller.Cstar_four)
      caller.Cstar_finite
  have denominator_pos :
      0 < caller.parameters.K * CstarReal :=
    mul_pos caller.parameters.K_pos CstarReal_pos
  have beforeAnchor :
      CstarReal ^ 5 * delta <
        rho / (caller.parameters.K * CstarReal) := by
    apply (lt_div_iff₀ denominator_pos).2
    have strict :=
      input.caller_mul_Cstar_six_mul_delta_lt_rho
        caller delta_le rho_lower
    calc
      (CstarReal ^ 5 * delta) *
            (caller.parameters.K * CstarReal) =
          caller.parameters.K * CstarReal ^ 6 * delta := by ring
      _ < rho := strict
  have beforePacket :
      CstarReal ^ 5 * delta < packetScale :=
    beforeAnchor.trans_le q0_le_packetScale
  calc
    (pureWZ2Prop62CallerCstar delta A eta) ^ 5 *
          ENNReal.ofReal delta =
        ENNReal.ofReal (CstarReal ^ 5 * delta) := by
      rw [← ENNReal.ofReal_toReal caller.Cstar_finite,
        ← ENNReal.ofReal_pow CstarReal_pos.le,
        ← ENNReal.ofReal_mul (pow_nonneg CstarReal_pos.le 5)]
    _ < ENNReal.ofReal packetScale :=
      (ENNReal.ofReal_lt_ofReal_iff packetScale_pos).2 beforePacket

/-- Route-shaped floor gate for a schedule whose window is `Cstar^5`. -/
theorem routeFloorGate_of_scaleWindow_eq
    {delta rho packetScale : ℝ}
    {scaleWindow : ENNReal}
    (caller :
      PureWZ2Prop62CallerParameterAbsorptionData
        A epsilon eta c0 delta rho)
    (delta_le : delta ≤ input.threshold)
    (scheduleWindowEq :
      scaleWindow =
        (pureWZ2Prop62CallerCstar delta A eta) ^ 5)
    (rho_lower :
      Real.rpow delta (1 - epsilon) ≤ rho)
    (packetScale_pos : 0 < packetScale)
    (q0_le_packetScale :
      rho /
          (caller.parameters.K *
            (pureWZ2Prop62CallerCstar delta A eta).toReal) ≤
        packetScale) :
    scaleWindow * ENNReal.ofReal delta <
      ENNReal.ofReal packetScale := by
  rw [scheduleWindowEq]
  exact
    input.routeFloorGate caller delta_le rho_lower
      packetScale_pos q0_le_packetScale

/-- Extract the complete quotient power budget below the master threshold. -/
theorem power_certificate
    {delta : ℝ}
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ input.threshold) :
    PureWZ2Prop62ProxyQuotientPowerBudgetData
      A eta delta (pureWZ2Prop62CallerK c0) input.powerFixedLoss
      input.powerInsertedCoefficient input.powerUpperCoefficient
      input.powerUniformityCoefficient
      input.powerWindowCoefficient := by
  exact
    (Classical.choose_spec <|
      exists_pureWZ2Prop62ProxyQuotientPowerBudget
        A input.A_ge_one eta (pureWZ2Prop62CallerK c0) input.eta_pos
        input.callerK_pos.le
        input.powerFixedLoss input.powerInsertedCoefficient
        input.powerUpperCoefficient input.powerUniformityCoefficient
        input.powerWindowCoefficient input.powerFixedLoss_ne_top
        input.powerInsertedCoefficient_ne_top
        input.powerUpperCoefficient_ne_top
        input.powerUniformityCoefficient_ne_top
        input.powerWindowCoefficient_ne_top).2.2
      delta delta_pos (delta_le.trans input.threshold_le_power)

/--
The target produced by the legacy quotient power budget is below the
corrected final `8 * A` target.
-/
theorem proxyPowerTarget_le_target
    {delta : ℝ}
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ input.threshold) :
    Kakeya.realRpowENN delta (-6 * (A : ℝ) * eta) ≤
      Kakeya.realRpowENN delta
        (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta) := by
  have budget := input.power_certificate delta_pos delta_le
  simpa [pureWZ2Prop62ProxyQuotientCWAPower] using
    pureWZ2Prop62MetricParentsV4ProxyTarget_le_target
      input.eta_pos delta_pos budget.delta_le_one

/-- Inserted-fibre output of the legacy budget, weakened to the final target. -/
theorem inserted_fiber_to_target
    {delta ratio : ℝ} {Λ : ENNReal}
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ input.threshold)
    (ratio_nonneg : 0 ≤ ratio)
    (ratio_le :
      ratio ≤ pureWZ2Prop62CallerK c0 *
        (Kakeya.realRpowENN delta (-((A : ℝ) * eta))).toReal)
    (Lambda_le :
      Λ ≤ input.powerFixedLoss *
        (Kakeya.realRpowENN delta (-((A : ℝ) * eta))) ^ 2) :
    input.powerInsertedCoefficient * ENNReal.ofReal (ratio ^ 2) *
          Kakeya.realRpowENN delta (-((A : ℝ) * eta)) * Λ ≤
      Kakeya.realRpowENN delta
        (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta) := by
  exact
    ((input.power_certificate delta_pos delta_le).inserted_fiber
      ratio_nonneg ratio_le Lambda_le).trans
      (input.proxyPowerTarget_le_target delta_pos delta_le)

/-- Upper-parent output of the legacy budget, weakened to the final target. -/
theorem upper_parent_to_target
    {delta : ℝ} {Λ : ENNReal}
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ input.threshold)
    (Lambda_le :
      Λ ≤ input.powerFixedLoss *
        (Kakeya.realRpowENN delta (-((A : ℝ) * eta))) ^ 2) :
    (Λ * Kakeya.realRpowENN delta (-((A : ℝ) * eta))) *
          input.powerUpperCoefficient ≤
      Kakeya.realRpowENN delta
        (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta) := by
  exact
    ((input.power_certificate delta_pos delta_le).upper_parent
      Lambda_le).trans
      (input.proxyPowerTarget_le_target delta_pos delta_le)

/-- Upper-uniformity output of the legacy budget, weakened to the final target. -/
theorem upper_uniformity_to_target
    {delta : ℝ} {Λ : ENNReal}
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ input.threshold)
    (Lambda_le :
      Λ ≤ input.powerFixedLoss *
        (Kakeya.realRpowENN delta (-((A : ℝ) * eta))) ^ 2) :
    input.powerUniformityCoefficient *
          Kakeya.realRpowENN delta (-((A : ℝ) * eta)) * Λ ≤
      Kakeya.realRpowENN delta
        (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta) := by
  exact
    ((input.power_certificate delta_pos delta_le).upper_uniformity
      Lambda_le).trans
      (input.proxyPowerTarget_le_target delta_pos delta_le)

/-- Fifth-power window output of the legacy budget, weakened to the final target. -/
theorem scale_window_to_target
    {delta : ℝ}
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ input.threshold) :
    input.powerWindowCoefficient *
          (Kakeya.realRpowENN delta (-((A : ℝ) * eta))) ^ 5 ≤
      Kakeya.realRpowENN delta
        (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta) := by
  exact
    ((input.power_certificate delta_pos delta_le).scale_window).trans
      (input.proxyPowerTarget_le_target delta_pos delta_le)

/--
The representative-scaled route window is absorbed by the final target.
The sole coefficient hypothesis is definitional for the canonical input.
-/
theorem representativeScaledWindow_to_target
    {delta : ℝ} {scaleWindow : ENNReal}
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ input.threshold)
    (scaleWindow_eq :
      scaleWindow =
        (pureWZ2Prop62CallerCstar delta A eta) ^ 5) :
    (100 : ENNReal) *
          ENNReal.ofReal pureWZ2Prop62RepresentativeParentScaledFactor *
          scaleWindow ≤
      Kakeya.realRpowENN delta
        (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta) := by
  rw [scaleWindow_eq]
  exact
    (mul_le_mul_right' input.scaledWindowCoefficient_le_window
      ((pureWZ2Prop62CallerCstar delta A eta) ^ 5)).trans
      (input.scale_window_to_target delta_pos delta_le)

/--
Route field form of the representative-scaled window absorption.
-/
theorem routeScaledWindowAbsorption
    {delta : ℝ} {scaleWindow sourceConstant : ENNReal}
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ input.threshold)
    (scheduleWindowEq :
      scaleWindow =
        (pureWZ2Prop62CallerCstar delta A eta) ^ 5)
    (fiberTarget :
      (81000000 : ENNReal) * sourceConstant =
        Kakeya.realRpowENN delta
          (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta)) :
    (100 : ENNReal) *
          ENNReal.ofReal pureWZ2Prop62RepresentativeParentScaledFactor *
          scaleWindow ≤
      (81000000 : ENNReal) * sourceConstant := by
  rw [fiberTarget]
  exact
    input.representativeScaledWindow_to_target
      delta_pos delta_le scheduleWindowEq

/--
The representative-middle John loss, including the final factor `81000000`,
is absorbed by the corrected final target.
-/
theorem representativeMiddle_to_target
    {delta : ℝ} {Λ : ENNReal}
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ input.threshold)
    (Lambda_le :
      Λ ≤ input.powerFixedLoss *
        (pureWZ2Prop62CallerCstar delta A eta) ^ 2) :
    (81000000 : ENNReal) *
          (pureWZ2Prop62MetricParentsV4RepresentativeMiddleJohnLoss *
            (pureWZ2Prop62CallerCstar delta A eta * Λ)) ≤
      Kakeya.realRpowENN delta
        (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta) := by
  calc
    (81000000 : ENNReal) *
          (pureWZ2Prop62MetricParentsV4RepresentativeMiddleJohnLoss *
            (pureWZ2Prop62CallerCstar delta A eta * Λ)) =
        (Λ * pureWZ2Prop62CallerCstar delta A eta) *
          pureWZ2Prop62MetricParentsV4RepresentativeMiddleCoefficient := by
      unfold
        pureWZ2Prop62MetricParentsV4RepresentativeMiddleCoefficient
      ring
    _ ≤
        (Λ * pureWZ2Prop62CallerCstar delta A eta) *
          input.powerUpperCoefficient :=
      mul_le_mul_left' input.representativeMiddleCoefficient_le_upper _
    _ ≤
        Kakeya.realRpowENN delta
          (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta) :=
      input.upper_parent_to_target delta_pos delta_le Lambda_le

/--
Source-constant form of representative-middle absorption.  Downstream may
discharge `source_target` using its exact source-constant provenance.
-/
theorem representativeMiddleJohnLoss_mul_le_sourceConstant
    {delta : ℝ} {Λ sourceConstant : ENNReal}
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ input.threshold)
    (Lambda_le :
      Λ ≤ input.powerFixedLoss *
        (pureWZ2Prop62CallerCstar delta A eta) ^ 2)
    (fiberTarget :
      (81000000 : ENNReal) * sourceConstant =
        Kakeya.realRpowENN delta
          (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta)) :
    pureWZ2Prop62MetricParentsV4RepresentativeMiddleJohnLoss *
          (pureWZ2Prop62CallerCstar delta A eta * Λ) ≤
      sourceConstant := by
  have multiplied :
      (81000000 : ENNReal) *
          (pureWZ2Prop62MetricParentsV4RepresentativeMiddleJohnLoss *
            (pureWZ2Prop62CallerCstar delta A eta * Λ)) ≤
        (81000000 : ENNReal) * sourceConstant := by
    rw [fiberTarget]
    exact
      input.representativeMiddle_to_target
        delta_pos delta_le Lambda_le
  have divided :
      pureWZ2Prop62MetricParentsV4RepresentativeMiddleJohnLoss *
            (pureWZ2Prop62CallerCstar delta A eta * Λ) ≤
        ((81000000 : ENNReal) * sourceConstant) / 81000000 :=
    (ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num)) (Or.inl (by norm_num))).2 <| by
        simpa [mul_comm] using multiplied
  calc
    pureWZ2Prop62MetricParentsV4RepresentativeMiddleJohnLoss *
          (pureWZ2Prop62CallerCstar delta A eta * Λ) ≤
        ((81000000 : ENNReal) * sourceConstant) / 81000000 :=
      divided
    _ = sourceConstant := by
      rw [mul_comm]
      exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)

/--
Top-case gate for the route.  It uses the same fixed `400 * K` absorption as
the floor gate and the exact equality between the route output and the final
target.
-/
theorem routeTopGate
    {delta rho packetScale : ℝ}
    {scaleWindow sourceConstant : ENNReal}
    (caller :
      PureWZ2Prop62CallerParameterAbsorptionData
        A epsilon eta c0 delta rho)
    (delta_le : delta ≤ input.threshold)
    (scheduleWindowEq :
      scaleWindow =
        (pureWZ2Prop62CallerCstar delta A eta) ^ 5)
    (q0_le_packetScale :
      rho /
          (caller.parameters.K *
            (pureWZ2Prop62CallerCstar delta A eta).toReal) ≤
        packetScale)
    (fiberTarget :
      (81000000 : ENNReal) * sourceConstant =
        Kakeya.realRpowENN delta
          (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta)) :
    (4 : ENNReal) *
          ((100 : ENNReal) * scaleWindow * ENNReal.ofReal rho) ≤
      ((81000000 : ENNReal) * sourceConstant) *
        ENNReal.ofReal packetScale := by
  let CstarReal :=
    (pureWZ2Prop62CallerCstar delta A eta).toReal
  have CstarReal_pos : 0 < CstarReal :=
    ENNReal.toReal_pos
      (ne_of_gt <| (show (0 : ENNReal) < 4 by norm_num).trans_le
        caller.Cstar_four)
      caller.Cstar_finite
  have coefficient :
      400 * CstarReal ^ 5 ≤
        CstarReal ^ 6 / caller.parameters.K := by
    apply (le_div_iff₀ caller.parameters.K_pos).2
    calc
      (400 * CstarReal ^ 5) * caller.parameters.K =
          (400 * caller.parameters.K) * CstarReal ^ 5 := by ring
      _ ≤ CstarReal * CstarReal ^ 5 := by
        exact mul_le_mul_of_nonneg_right
          (input.routeCallerFactor_le_Cstar caller delta_le)
          (pow_nonneg CstarReal_pos.le 5)
      _ = CstarReal ^ 6 := by ring
  have realBoundSeven :
      400 * CstarReal ^ 5 * rho ≤
        CstarReal ^ 7 * packetScale := by
    calc
      400 * CstarReal ^ 5 * rho ≤
          (CstarReal ^ 6 / caller.parameters.K) * rho := by
        exact mul_le_mul_of_nonneg_right coefficient caller.rho_pos.le
      _ =
          CstarReal ^ 7 *
            (rho / (caller.parameters.K * CstarReal)) := by
        field_simp [caller.parameters.K_pos.ne', CstarReal_pos.ne']
      _ ≤ CstarReal ^ 7 * packetScale := by
        exact mul_le_mul_of_nonneg_left q0_le_packetScale
          (pow_nonneg CstarReal_pos.le 7)
  have realBound :
      400 * CstarReal ^ 5 * rho ≤
        CstarReal ^ 8 * packetScale := by
    have CstarReal_one : 1 ≤ CstarReal := by
      have converted :=
        ENNReal.toReal_mono caller.Cstar_finite caller.Cstar_four
      norm_num at converted ⊢
      exact (show (1 : ℝ) ≤ 4 by norm_num).trans converted
    have powerSevenLeEight : CstarReal ^ 7 ≤ CstarReal ^ 8 := by
      calc
        CstarReal ^ 7 = CstarReal ^ 7 * 1 := by simp
        _ ≤ CstarReal ^ 7 * CstarReal :=
          mul_le_mul_of_nonneg_left CstarReal_one
            (pow_nonneg CstarReal_pos.le 7)
        _ = CstarReal ^ 8 := by ring
    have packetScale_nonneg : 0 ≤ packetScale := by
      have anchor_nonneg :
          0 ≤
            rho /
              (caller.parameters.K *
                (pureWZ2Prop62CallerCstar delta A eta).toReal) := by
        exact (div_pos caller.rho_pos <|
          mul_pos caller.parameters.K_pos CstarReal_pos).le
      exact anchor_nonneg.trans q0_le_packetScale
    calc
      400 * CstarReal ^ 5 * rho ≤
          CstarReal ^ 7 * packetScale :=
        realBoundSeven
      _ ≤ CstarReal ^ 8 * packetScale :=
        mul_le_mul_of_nonneg_right powerSevenLeEight packetScale_nonneg
  have targetEq :
      Kakeya.realRpowENN delta
          (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta) =
        (pureWZ2Prop62CallerCstar delta A eta) ^ 8 := by
    rw [pureWZ2Prop62CallerCstar,
      pureWZ2Prop62_realRpowENN_pow caller.delta_pos]
    congr 1
    rw [pureWZ2Prop62MetricParentsV4CWAPower_eq]
    unfold pureWZ2Prop62CallerLoss
    push_cast
    ring
  have packetScale_pos : 0 < packetScale := by
    have anchor_pos :
        0 <
          rho /
            (caller.parameters.K *
              (pureWZ2Prop62CallerCstar delta A eta).toReal) :=
      div_pos caller.rho_pos <|
        mul_pos caller.parameters.K_pos CstarReal_pos
    exact anchor_pos.trans_le q0_le_packetScale
  rw [scheduleWindowEq, fiberTarget, targetEq]
  let lhs : ENNReal :=
    (4 : ENNReal) *
      ((100 : ENNReal) *
        (pureWZ2Prop62CallerCstar delta A eta) ^ 5 *
          ENNReal.ofReal rho)
  let rhs : ENNReal :=
    (pureWZ2Prop62CallerCstar delta A eta) ^ 8 *
      ENNReal.ofReal packetScale
  change lhs ≤ rhs
  apply
    (ENNReal.toReal_le_toReal
      (by
        dsimp only [lhs]
        exact ENNReal.mul_ne_top
          (by norm_num)
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top (by norm_num)
              (ENNReal.pow_ne_top caller.Cstar_finite))
            ENNReal.ofReal_ne_top))
      (by
        dsimp only [rhs]
        exact ENNReal.mul_ne_top
          (ENNReal.pow_ne_top caller.Cstar_finite)
          ENNReal.ofReal_ne_top)).1
  dsimp only [lhs, rhs]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal caller.rho_pos.le,
    ENNReal.toReal_ofReal packetScale_pos.le]
  change 4 * (100 * CstarReal ^ 5 * rho) ≤
    CstarReal ^ 8 * packetScale
  convert realBound using 1 <;> ring

/--
Extract the concrete density-power logarithmic absorption below the master
threshold.
-/
theorem densityPower_certificate
    {delta : ℝ}
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ input.threshold) :
    (ENNReal.ofReal (1 + Real.log delta⁻¹)) ^ 2 ≤
      pureWZ2Prop62CallerCstar delta A eta :=
  input.densityPowerCertificate.log_square_le_Cstar
    delta delta_pos <|
      delta_le.trans input.threshold_le_densityPower

/--
Extract the generic six-factor mass certificate below the master threshold.
The concrete ledger geometry theorem in `Prop62ProxyQuotientMassAbsorption`
can then discharge all non-base factor bounds automatically.
-/
theorem mass_certificate
    {delta : ℝ}
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ input.threshold)
    {baseLoss upperColorLoss fiberBinLoss
      sourceColorLoss leafBinLoss cleanupLoss totalLoss : ENNReal}
    (totalLoss_eq :
      totalLoss =
        baseLoss * upperColorLoss * fiberBinLoss *
          sourceColorLoss * leafBinLoss * cleanupLoss)
    (baseLoss_le :
      baseLoss ≤ input.massBounds.baseStructural)
    (upperColorLoss_le :
      upperColorLoss ≤ input.massBounds.strongUpperVector)
    (fiberBinLoss_le :
      fiberBinLoss ≤
        ENNReal.ofReal
          (input.massBounds.fiberBinCoefficient *
            (1 + Real.log delta⁻¹)))
    (sourceColorLoss_le :
      sourceColorLoss ≤ input.massBounds.sourceColor)
    (leafBinLoss_le :
      leafBinLoss ≤
        ENNReal.ofReal
          (input.massBounds.leafBinCoefficient *
            (1 + Real.log delta⁻¹)))
    (cleanupLoss_le :
      cleanupLoss ≤ input.massBounds.weightedCleanup) :
    wz1PaperRefinementFraction delta 10 * totalLoss ≤ 1 := by
  exact
    (Classical.choose_spec <|
      exists_pureWZ2Prop62ProxyQuotientMassAbsorption
        A eta c0 input.massBounds).2.2
      delta_pos (delta_le.trans input.threshold_le_mass)
      totalLoss_eq baseLoss_le upperColorLoss_le fiberBinLoss_le
      sourceColorLoss_le leafBinLoss_le cleanupLoss_le

/-- The internal quotient exponent `6 * A` is below the final `8 * A`. -/
theorem proxyCWAPower_le_cwaPower :
    pureWZ2Prop62ProxyQuotientCWAPower A ≤
      pureWZ2Prop62MetricParentsV4CWAPower A := by
  unfold pureWZ2Prop62ProxyQuotientCWAPower
    pureWZ2Prop62MetricParentsV4CWAPower
  omega

end PureWZ2Prop62MetricParentsV4ThresholdInput

/-- Canonical master-threshold input built entirely from fixed parameters. -/
noncomputable def pureWZ2Prop62MetricParentsV4CanonicalInput
    (A : ℕ) (epsilon eta c0 : ℝ)
    (A_ge_one : 1 ≤ A)
    (epsilon_pos : 0 < epsilon)
    (eta_pos : 0 < eta)
    (loss_small :
      (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta ≤
        epsilon / 100)
    (c0_pos : 0 < c0) :
    PureWZ2Prop62MetricParentsV4ThresholdInput A epsilon eta c0 :=
  pureWZ2Prop62MetricParentsV4ThresholdInput
    A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos

/--
The canonical small-scale threshold.  Its data depend only on
`A`, `epsilon`, `eta`, and `c0`.
-/
noncomputable def pureWZ2Prop62MetricParentsV4Threshold
    (A : ℕ) (epsilon eta c0 : ℝ)
    (A_ge_one : 1 ≤ A)
    (epsilon_pos : 0 < epsilon)
    (eta_pos : 0 < eta)
    (loss_small :
      (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta ≤
        epsilon / 100)
    (c0_pos : 0 < c0) : ℝ :=
  (pureWZ2Prop62MetricParentsV4CanonicalInput
    A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos).threshold

theorem pureWZ2Prop62MetricParentsV4Threshold_pos
    (A : ℕ) (epsilon eta c0 : ℝ)
    (A_ge_one : 1 ≤ A)
    (epsilon_pos : 0 < epsilon)
    (eta_pos : 0 < eta)
    (loss_small :
      (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta ≤
        epsilon / 100)
    (c0_pos : 0 < c0) :
    0 <
      pureWZ2Prop62MetricParentsV4Threshold
        A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos :=
  (pureWZ2Prop62MetricParentsV4CanonicalInput
    A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos
    ).threshold_pos

theorem pureWZ2Prop62MetricParentsV4Threshold_le_one_hundred
    (A : ℕ) (epsilon eta c0 : ℝ)
    (A_ge_one : 1 ≤ A)
    (epsilon_pos : 0 < epsilon)
    (eta_pos : 0 < eta)
    (loss_small :
      (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta ≤
        epsilon / 100)
    (c0_pos : 0 < c0) :
    pureWZ2Prop62MetricParentsV4Threshold
        A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos ≤
      1 / 100 :=
  (pureWZ2Prop62MetricParentsV4CanonicalInput
    A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos
    ).threshold_le_one_hundred

/-- The canonical master threshold is below the concrete mass threshold. -/
theorem pureWZ2Prop62MetricParentsV4_deltaMassSmall
    (A : ℕ) (epsilon eta c0 : ℝ)
    (A_ge_one : 1 ≤ A)
    (epsilon_pos : 0 < epsilon)
    (eta_pos : 0 < eta)
    (loss_small :
      (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta ≤
        epsilon / 100)
    (c0_pos : 0 < c0)
    {delta : ℝ}
    (delta_le :
      delta ≤
        pureWZ2Prop62MetricParentsV4Threshold
          A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos) :
    delta ≤
      pureWZ2Prop62ProxyQuotientMassThreshold
        A eta c0 (pureWZ2Prop62MetricParentsV4MassBounds A eta c0) := by
  let input :=
    pureWZ2Prop62MetricParentsV4CanonicalInput
      A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos
  have thresholdMass := input.threshold_le_mass
  simpa [input, pureWZ2Prop62MetricParentsV4Threshold,
    pureWZ2Prop62MetricParentsV4CanonicalInput,
    pureWZ2Prop62MetricParentsV4ThresholdInput] using
      delta_le.trans thresholdMass

/-- Caller-parameter certificate below the canonical master threshold. -/
theorem pureWZ2Prop62MetricParentsV4_caller_certificate
    (A : ℕ) (epsilon eta c0 : ℝ)
    (A_ge_one : 1 ≤ A)
    (epsilon_pos : 0 < epsilon)
    (eta_pos : 0 < eta)
    (loss_small :
      (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta ≤
        epsilon / 100)
    (c0_pos : 0 < c0)
    {delta rho : ℝ}
    (delta_pos : 0 < delta)
    (delta_le :
      delta ≤
        pureWZ2Prop62MetricParentsV4Threshold
          A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos)
    (rho_pos : 0 < rho)
    (rho_le_one : rho ≤ 1)
    (rho_lower : Real.rpow delta (1 - epsilon) ≤ rho) :
    Nonempty
      (PureWZ2Prop62CallerParameterAbsorptionData
        A epsilon eta c0 delta rho) :=
  (pureWZ2Prop62MetricParentsV4CanonicalInput
    A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos
    ).caller_certificate delta_pos delta_le rho_pos rho_le_one rho_lower

/-- Quotient power-budget certificate below the canonical threshold. -/
theorem pureWZ2Prop62MetricParentsV4_power_certificate
    (A : ℕ) (epsilon eta c0 : ℝ)
    (A_ge_one : 1 ≤ A)
    (epsilon_pos : 0 < epsilon)
    (eta_pos : 0 < eta)
    (loss_small :
      (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta ≤
        epsilon / 100)
    (c0_pos : 0 < c0)
    {delta : ℝ}
    (delta_pos : 0 < delta)
    (delta_le :
      delta ≤
        pureWZ2Prop62MetricParentsV4Threshold
          A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos) :
    PureWZ2Prop62ProxyQuotientPowerBudgetData
      A eta delta (pureWZ2Prop62CallerK c0)
      (pureWZ2Prop62MetricParentsV4DensityFixedLoss A eta c0)
      pureWZ2Prop62MetricParentsV4InsertedCoefficient
      pureWZ2Prop62MetricParentsV4UpperCoefficient
      pureWZ2Prop62MetricParentsV4UniformityCoefficient
      pureWZ2Prop62MetricParentsV4WindowCoefficient :=
  (pureWZ2Prop62MetricParentsV4CanonicalInput
    A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos
    ).power_certificate delta_pos delta_le

/--
The canonical threshold supplies the scale inequality needed to compare the
top packet and every representative-parent middle scale.
-/
theorem pureWZ2Prop62MetricParentsV4_representativeOverlap
    (A : ℕ) (epsilon eta c0 : ℝ)
    (A_ge_one : 1 ≤ A)
    (epsilon_pos : 0 < epsilon)
    (eta_pos : 0 < eta)
    (loss_small :
      (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta ≤
        epsilon / 100)
    (c0_pos : 0 < c0)
    {delta : ℝ}
    (delta_pos : 0 < delta)
    (delta_le :
      delta ≤
        pureWZ2Prop62MetricParentsV4Threshold
          A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos) :
    4 * pureWZ2Prop62CallerK c0 ≤
      pureWZ2Prop62RepresentativeParentScaledFactor *
        (pureWZ2Prop62CallerCstar delta A eta).toReal :=
  (pureWZ2Prop62MetricParentsV4CanonicalInput
    A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos
    ).representativeOverlap delta_pos delta_le

/-- Density logarithm absorption below the canonical threshold. -/
theorem pureWZ2Prop62MetricParentsV4_densityPower_certificate
    (A : ℕ) (epsilon eta c0 : ℝ)
    (A_ge_one : 1 ≤ A)
    (epsilon_pos : 0 < epsilon)
    (eta_pos : 0 < eta)
    (loss_small :
      (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta ≤
        epsilon / 100)
    (c0_pos : 0 < c0)
    {delta : ℝ}
    (delta_pos : 0 < delta)
    (delta_le :
      delta ≤
        pureWZ2Prop62MetricParentsV4Threshold
          A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos) :
    (ENNReal.ofReal (1 + Real.log delta⁻¹)) ^ 2 ≤
      pureWZ2Prop62CallerCstar delta A eta :=
  (pureWZ2Prop62MetricParentsV4CanonicalInput
    A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos
    ).densityPower_certificate delta_pos delta_le

/-- Six-factor mass absorption below the canonical master threshold. -/
theorem pureWZ2Prop62MetricParentsV4_mass_certificate
    (A : ℕ) (epsilon eta c0 : ℝ)
    (A_ge_one : 1 ≤ A)
    (epsilon_pos : 0 < epsilon)
    (eta_pos : 0 < eta)
    (loss_small :
      (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta ≤
        epsilon / 100)
    (c0_pos : 0 < c0)
    {delta : ℝ}
    (delta_pos : 0 < delta)
    (delta_le :
      delta ≤
        pureWZ2Prop62MetricParentsV4Threshold
          A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos)
    {baseLoss upperColorLoss fiberBinLoss
      sourceColorLoss leafBinLoss cleanupLoss totalLoss : ENNReal}
    (totalLoss_eq :
      totalLoss =
        baseLoss * upperColorLoss * fiberBinLoss *
          sourceColorLoss * leafBinLoss * cleanupLoss)
    (baseLoss_le :
      baseLoss ≤
        (pureWZ2Prop62MetricParentsV4MassBounds
          A eta c0).baseStructural)
    (upperColorLoss_le :
      upperColorLoss ≤
        (pureWZ2Prop62MetricParentsV4MassBounds
          A eta c0).strongUpperVector)
    (fiberBinLoss_le :
      fiberBinLoss ≤
        ENNReal.ofReal
          ((pureWZ2Prop62MetricParentsV4MassBounds
              A eta c0).fiberBinCoefficient *
            (1 + Real.log delta⁻¹)))
    (sourceColorLoss_le :
      sourceColorLoss ≤
        (pureWZ2Prop62MetricParentsV4MassBounds
          A eta c0).sourceColor)
    (leafBinLoss_le :
      leafBinLoss ≤
        ENNReal.ofReal
          ((pureWZ2Prop62MetricParentsV4MassBounds
              A eta c0).leafBinCoefficient *
            (1 + Real.log delta⁻¹)))
    (cleanupLoss_le :
      cleanupLoss ≤
        (pureWZ2Prop62MetricParentsV4MassBounds
          A eta c0).weightedCleanup) :
    wz1PaperRefinementFraction delta 10 * totalLoss ≤ 1 :=
  (pureWZ2Prop62MetricParentsV4CanonicalInput
    A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos
    ).mass_certificate delta_pos delta_le totalLoss_eq
      baseLoss_le upperColorLoss_le fiberBinLoss_le
      sourceColorLoss_le leafBinLoss_le cleanupLoss_le

end Kakeya.Assouad

end
