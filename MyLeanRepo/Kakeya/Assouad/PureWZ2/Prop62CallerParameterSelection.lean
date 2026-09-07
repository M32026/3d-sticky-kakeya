import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyAncestryMetricOutput
import Mathlib.Tactic

/-!
# Proposition 6.2 caller parameters

Choose the packet-mesh width and residue stride from an arbitrary positive
caller constant `c0`.  These parameters depend only on `c0` and the caller
scale `rho`; the later smallness choice is isolated in the hypothesis
`packetScale < rho / K`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The caller constant truncated to the interval `(0, 1]`. -/
def pureWZ2Prop62CallerTheta (c0 : ℝ) : ℝ :=
  min c0 1

/-- Scale-separation factor chosen before the fine-scale threshold. -/
def pureWZ2Prop62CallerK (c0 : ℝ) : ℝ :=
  2400000 / pureWZ2Prop62CallerTheta c0

/-- Four-dimensional proxy-mesh width at caller scale `rho`. -/
def pureWZ2Prop62CallerWidth (c0 rho : ℝ) : ℝ :=
  pureWZ2Prop62CallerTheta c0 * rho / 24

/--
Residue stride forcing enough separation between retained mesh cells for
literal doubled-fiber partitioning of the final radius-`rho` parents.
-/
def pureWZ2Prop62CallerStrideBase (c0 : ℝ) : ℕ :=
  Nat.ceil (230400 / pureWZ2Prop62CallerTheta c0) + 1

/--
Concrete caller parameters chosen before any small-scale threshold.
-/
structure PureWZ2Prop62CallerParameterData
    (c0 rho : ℝ) where
  rho_pos :
    0 < rho
  theta : ℝ
  theta_eq :
    theta = pureWZ2Prop62CallerTheta c0
  theta_pos :
    0 < theta
  theta_le_c0 :
    theta ≤ c0
  theta_le_one :
    theta ≤ 1
  K : ℝ
  K_eq :
    K = pureWZ2Prop62CallerK c0
  K_pos :
    0 < K
  width : ℝ
  width_eq :
    width = pureWZ2Prop62CallerWidth c0 rho
  width_pos :
    0 < width
  strideBase : ℕ
  strideBase_eq :
    strideBase = pureWZ2Prop62CallerStrideBase c0
  six_width_le :
    6 * width ≤ rho / 2
  strict_separation :
    6 * rho <
      (((strideBase + 1 : ℕ) : ℝ) - 1) * width
  upper_strong_separation :
    360 * rho <
      (((strideBase + 1 : ℕ) : ℝ) - 1) * width
  literal_strong_separation :
    9600 * rho <
      (((strideBase + 1 : ℕ) : ℝ) - 1) * width

/-- Construct the caller parameters from `c0` and `rho` alone. -/
def pureWZ2Prop62CallerParameters
    (c0 rho : ℝ)
    (c0Pos : 0 < c0)
    (rhoPos : 0 < rho) :
    PureWZ2Prop62CallerParameterData c0 rho := by
  let theta := pureWZ2Prop62CallerTheta c0
  let K := pureWZ2Prop62CallerK c0
  let width := pureWZ2Prop62CallerWidth c0 rho
  let strideBase := pureWZ2Prop62CallerStrideBase c0
  have thetaPos : 0 < theta := by
    exact lt_min c0Pos zero_lt_one
  have thetaLeC0 : theta ≤ c0 := by
    exact min_le_left _ _
  have thetaLeOne : theta ≤ 1 := by
    exact min_le_right _ _
  have KPos : 0 < K := by
    dsimp only [K, pureWZ2Prop62CallerK]
    exact div_pos (by norm_num) thetaPos
  have widthPos : 0 < width := by
    dsimp only [width, pureWZ2Prop62CallerWidth]
    positivity
  have sixWidthLe : 6 * width ≤ rho / 2 := by
    dsimp only [width, pureWZ2Prop62CallerWidth]
    have scaled :
        theta * rho ≤ 1 * rho :=
      mul_le_mul_of_nonneg_right thetaLeOne rhoPos.le
    nlinarith
  have strideStrict :
      230400 / theta < (strideBase : ℝ) := by
    have ceilingLower :
        230400 / theta ≤
          (Nat.ceil (230400 / theta) : ℝ) :=
      Nat.le_ceil _
    dsimp only [strideBase, pureWZ2Prop62CallerStrideBase]
    push_cast
    linarith
  have literalStrongSeparation :
      9600 * rho <
        (((strideBase + 1 : ℕ) : ℝ) - 1) * width := by
    have positiveFactor : 0 < theta * rho / 24 := by
      positivity
    have multiplied :=
      mul_lt_mul_of_pos_right strideStrict positiveFactor
    have leftIdentity :
        (230400 / theta) * (theta * rho / 24) =
          9600 * rho := by
      field_simp [thetaPos.ne']
      ring
    have rightIdentity :
        (strideBase : ℝ) * (theta * rho / 24) =
          (((strideBase + 1 : ℕ) : ℝ) - 1) * width := by
      dsimp only [width, pureWZ2Prop62CallerWidth]
      push_cast
      ring
    rwa [leftIdentity, rightIdentity] at multiplied
  have upperStrongSeparation :
      360 * rho <
        (((strideBase + 1 : ℕ) : ℝ) - 1) * width := by
    nlinarith [literalStrongSeparation, rhoPos]
  have strictSeparation :
      6 * rho <
        (((strideBase + 1 : ℕ) : ℝ) - 1) * width := by
    nlinarith [upperStrongSeparation, rhoPos]
  exact
    {
      rho_pos := rhoPos
      theta := theta
      theta_eq := rfl
      theta_pos := thetaPos
      theta_le_c0 := thetaLeC0
      theta_le_one := thetaLeOne
      K := K
      K_eq := rfl
      K_pos := KPos
      width := width
      width_eq := rfl
      width_pos := widthPos
      strideBase := strideBase
      strideBase_eq := rfl
      six_width_le := sixWidthLe
      strict_separation := strictSeparation
      upper_strong_separation := upperStrongSeparation
      literal_strong_separation := literalStrongSeparation
    }

namespace PureWZ2Prop62CallerParameterData

variable
    {c0 rho : ℝ}
    (parameters : PureWZ2Prop62CallerParameterData c0 rho)

theorem packet_metric_bound_lt
    {packetScale : ℝ}
    (packetScaleLt : packetScale < rho / parameters.K) :
    600000 * packetScale + 6 * parameters.width <
      parameters.theta * rho / 2 := by
  have firstTerm :
      600000 * packetScale <
        parameters.theta * rho / 4 := by
    have scaled :=
      mul_lt_mul_of_pos_left packetScaleLt
        (by norm_num : (0 : ℝ) < 600000)
    rw [parameters.K_eq, pureWZ2Prop62CallerK] at scaled
    have scaledRightEq :
        600000 *
            (rho /
              (2400000 /
                pureWZ2Prop62CallerTheta c0)) =
          parameters.theta * rho / 4 := by
      rw [parameters.theta_eq]
      field_simp [
        (show
          pureWZ2Prop62CallerTheta c0 ≠ 0 by
            rw [← parameters.theta_eq]
            exact parameters.theta_pos.ne')]
      ring
    rw [scaledRightEq] at scaled
    exact scaled
  have widthTerm :
      6 * parameters.width =
        parameters.theta * rho / 4 := by
    rw [parameters.width_eq, pureWZ2Prop62CallerWidth,
      parameters.theta_eq]
    ring
  rw [widthTerm]
  linarith

theorem packet_metric_bound
    {packetScale : ℝ}
    (packetScaleLt : packetScale < rho / parameters.K) :
    600000 * packetScale + 6 * parameters.width ≤
      rho / 2 := by
  have strict := parameters.packet_metric_bound_lt packetScaleLt
  exact strict.le.trans <| by
    have scaled :
        parameters.theta * rho ≤ 1 * rho :=
      mul_le_mul_of_nonneg_right
        parameters.theta_le_one
        parameters.rho_pos.le
    nlinarith

theorem packet_metric_bound_c0
    {packetScale : ℝ}
    (packetScaleLt : packetScale < rho / parameters.K) :
    600000 * packetScale + 6 * parameters.width ≤
      c0 * rho := by
  have strict := parameters.packet_metric_bound_lt packetScaleLt
  exact strict.le.trans <| by
    have scaled :
        parameters.theta * rho ≤ c0 * rho :=
      mul_le_mul_of_nonneg_right
        parameters.theta_le_c0 parameters.rho_pos.le
    have productPositive :
        0 < parameters.theta * rho :=
      mul_pos parameters.theta_pos parameters.rho_pos
    nlinarith

/--
The metric producer's direct packet-to-proxy estimate inherits the stronger
caller-relative `c0 * rho` bound.
-/
theorem fine_parent_close
    {delta packetScale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {packetCoordinate : Fin schedule.levelCount}
    {weight : Fin fine.card → ENNReal}
    (packetScaleEq :
      packetScale = schedule.actualScale packetCoordinate)
    (packetScaleLt :
      packetScale < rho / parameters.K)
    (metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient
          parameters.width packetCoordinate parameters.strideBase weight)
    (parent :
      Fin metric.mesh.restrictedOldData.coarse.card)
    (source : Fin metric.selectedFine.card)
    (sourceMem :
      source ∈
        wz2PaperOrdinaryFullFiberIndices
          metric.selectedFine
          metric.mesh.restrictedOldData.coarse parent) :
    wz1PaperLineDistance
        (metric.selectedFine.tube source)
        (metric.metricParents.tube
          (metric.metricInput.packetParent parent)) ≤
      c0 * rho := by
  have close :=
    metric.metricInput.packet_proxy_close parent source sourceMem
  have radiusBound :
      600000 * schedule.actualScale packetCoordinate +
          6 * parameters.width ≤
        c0 * rho := by
    rw [← packetScaleEq]
    exact parameters.packet_metric_bound_c0 packetScaleLt
  exact close.trans radiusBound

end PureWZ2Prop62CallerParameterData

end Kakeya.Assouad

end
