import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CallerParameterSelection
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import Mathlib.Tactic

/-!
# Proposition 6.2 caller-parameter absorption

This module collects the scalar choices made outside the geometric proof.
For a fixed integer `A`, the input CWA loss is `a = A * eta`, the requested
scale step is `2 * a`, and the final CWA exponent is `6 * A`.  In particular,
the exponent does not depend on the arbitrary caller constant `c0`.

The common small-scale threshold absorbs the `c0`-dependent constant `K`,
makes the input CWA constant at least four, and supplies the separation
inequality for the geometric requested-scale schedule.  The resulting record
also packages the two endpoint inequalities which make

`rho / (K * Cstar.toReal)`

a legal requested scale.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The input CWA/density loss `A * eta`. -/
def pureWZ2Prop62CallerLoss (A : ℕ) (eta : ℝ) : ℝ :=
  (A : ℝ) * eta

/-- Exponent step used by the geometric requested-scale net. -/
def pureWZ2Prop62CallerStep (A : ℕ) (eta : ℝ) : ℝ :=
  2 * pureWZ2Prop62CallerLoss A eta

@[simp] lemma pureWZ2Prop62CallerStep_eq
    (A : ℕ) (eta : ℝ) :
    pureWZ2Prop62CallerStep A eta =
      2 * (A : ℝ) * eta := by
  unfold pureWZ2Prop62CallerStep pureWZ2Prop62CallerLoss
  ring

/--
The output CWA power.  Its arguments deliberately contain only the fixed
integer `A`, not the arbitrary caller constant.
-/
def pureWZ2Prop62CallerCWAPower (A : ℕ) : ℕ :=
  6 * A

/-- The input all-scale CWA constant `delta ^ (-A * eta)`. -/
def pureWZ2Prop62CallerCstar
    (delta : ℝ) (A : ℕ) (eta : ℝ) : ENNReal :=
  Kakeya.realRpowENN delta (-pureWZ2Prop62CallerLoss A eta)

/-- The requested caller anchor before public nearby-scale rounding. -/
def pureWZ2Prop62CallerQ0
    (delta rho c0 : ℝ) (A : ℕ) (eta : ℝ) : ℝ :=
  rho /
    (pureWZ2Prop62CallerK c0 *
      (pureWZ2Prop62CallerCstar delta A eta).toReal)

lemma pureWZ2Prop62CallerLoss_pos
    {A : ℕ} (A_ge_one : 1 ≤ A)
    {eta : ℝ} (eta_pos : 0 < eta) :
    0 < pureWZ2Prop62CallerLoss A eta := by
  unfold pureWZ2Prop62CallerLoss
  positivity

lemma pureWZ2Prop62CallerStep_pos
    {A : ℕ} (A_ge_one : 1 ≤ A)
    {eta : ℝ} (eta_pos : 0 < eta) :
    0 < pureWZ2Prop62CallerStep A eta := by
  unfold pureWZ2Prop62CallerStep
  exact mul_pos (by norm_num) <|
    pureWZ2Prop62CallerLoss_pos A_ge_one eta_pos

lemma pureWZ2Prop62CallerCWAPower_pos
    {A : ℕ} (A_ge_one : 1 ≤ A) :
    1 ≤ pureWZ2Prop62CallerCWAPower A := by
  unfold pureWZ2Prop62CallerCWAPower
  omega

@[simp] lemma pureWZ2Prop62CallerCWAPower_mul_eta
    (A : ℕ) (eta : ℝ) :
    (pureWZ2Prop62CallerCWAPower A : ℝ) * eta =
      6 * pureWZ2Prop62CallerLoss A eta := by
  unfold pureWZ2Prop62CallerCWAPower
    pureWZ2Prop62CallerLoss
  push_cast
  ring

/--
The quantitative hypothesis with `cwaPower = 6 * A` leaves a strict gap
between the input loss `a = A * eta` and the public exponent `epsilon`.
-/
lemma pureWZ2Prop62CallerLoss_lt_epsilon
    {A : ℕ} (A_ge_one : 1 ≤ A)
    {epsilon eta : ℝ}
    (eta_pos : 0 < eta)
    (loss_small :
      6 * (A : ℝ) * eta ≤ epsilon / 100) :
    pureWZ2Prop62CallerLoss A eta < epsilon := by
  have loss_pos :
      0 < pureWZ2Prop62CallerLoss A eta :=
    pureWZ2Prop62CallerLoss_pos A_ge_one eta_pos
  unfold pureWZ2Prop62CallerLoss at loss_pos ⊢
  nlinarith

/--
All scalar hypotheses needed after choosing a caller scale `rho`.

The first three caller inequalities are restated directly, while the two
packet-radius estimates are exposed as methods below.  The schedule fields
are exactly the separation and endpoint hypotheses used by the geometric
requested-scale net and its caller anchor.
-/
structure PureWZ2Prop62CallerParameterAbsorptionData
    (A : ℕ) (epsilon eta c0 delta rho : ℝ) where
  delta_pos :
    0 < delta
  delta_le_one_hundred :
    delta ≤ 1 / 100
  rho_pos :
    0 < rho
  rho_le_one :
    rho ≤ 1
  epsilon_pos :
    0 < epsilon
  loss_pos :
    0 < pureWZ2Prop62CallerLoss A eta
  loss_lt_epsilon :
    pureWZ2Prop62CallerLoss A eta < epsilon
  step_pos :
    0 < pureWZ2Prop62CallerStep A eta
  cwaPower_pos :
    1 ≤ pureWZ2Prop62CallerCWAPower A
  parameters :
    PureWZ2Prop62CallerParameterData c0 rho
  Cstar_four :
    4 ≤ pureWZ2Prop62CallerCstar delta A eta
  Cstar_finite :
    pureWZ2Prop62CallerCstar delta A eta ≠ ⊤
  requested_separation :
    4 * (pureWZ2Prop62CallerCstar delta A eta).toReal ≤
      Real.rpow delta (-pureWZ2Prop62CallerStep A eta)
  constant_absorption :
    parameters.K *
        Real.rpow delta
          (1 - pureWZ2Prop62CallerLoss A eta) ≤
      Real.rpow delta (1 - epsilon)
  q0_lower :
    delta ≤ pureWZ2Prop62CallerQ0 delta rho c0 A eta
  q0_upper :
    pureWZ2Prop62CallerQ0 delta rho c0 A eta ≤ 1
  width_pos :
    0 < parameters.width
  six_width_le :
    6 * parameters.width ≤ rho / 2
  strict_separation :
    6 * rho <
      (((parameters.strideBase + 1 : ℕ) : ℝ) - 1) *
        parameters.width
  upper_strong_separation :
    360 * rho <
      (((parameters.strideBase + 1 : ℕ) : ℝ) - 1) *
        parameters.width

namespace PureWZ2Prop62CallerParameterAbsorptionData

variable
    {A : ℕ} {epsilon eta c0 delta rho : ℝ}
    (data :
      PureWZ2Prop62CallerParameterAbsorptionData
        A epsilon eta c0 delta rho)

include data

/-- The input CWA constant is a valid finite Definition 2.12 constant. -/
theorem Cstar_valid :
    WZ2PaperFiniteErrorConstant
      (pureWZ2Prop62CallerCstar delta A eta) :=
  ⟨(show (1 : ENNReal) ≤ 4 by norm_num).trans data.Cstar_four,
    data.Cstar_finite⟩

/-- The common smallness threshold puts the source scale strictly below one. -/
theorem delta_lt_one : delta < 1 :=
  data.delta_le_one_hundred.trans_lt (by norm_num)

/-- The packaged endpoint inequalities define a requested caller scale. -/
def q0RequestedScale : WZ2PaperRequestedScale delta :=
  ⟨pureWZ2Prop62CallerQ0 delta rho c0 A eta,
    data.q0_lower, data.q0_upper⟩

/--
The concrete caller denominator is large enough to place the literal anchor
below the top separation gap.
-/
theorem q0_top_gap :
    4 * (pureWZ2Prop62CallerCstar delta A eta).toReal *
        pureWZ2Prop62CallerQ0 delta rho c0 A eta ≤ 1 := by
  have thetaPos :
      0 < pureWZ2Prop62CallerTheta c0 := by
    rw [← data.parameters.theta_eq]
    exact data.parameters.theta_pos
  have fourLeK : 4 ≤ data.parameters.K := by
    rw [data.parameters.K_eq, pureWZ2Prop62CallerK]
    apply (le_div_iff₀ thetaPos).2
    have thetaLeOne :
        pureWZ2Prop62CallerTheta c0 ≤ 1 := by
      rw [← data.parameters.theta_eq]
      exact data.parameters.theta_le_one
    nlinarith
  have CstarRealPos :
      0 < (pureWZ2Prop62CallerCstar delta A eta).toReal := by
    exact ENNReal.toReal_pos
      (ne_of_gt <| (show (0 : ENNReal) < 4 by norm_num).trans_le
        data.Cstar_four)
      data.Cstar_finite
  have fourRhoLeK : 4 * rho ≤ data.parameters.K := by
    calc
      4 * rho ≤ 4 * 1 := by
        exact mul_le_mul_of_nonneg_left data.rho_le_one (by norm_num)
      _ ≤ data.parameters.K := by simpa using fourLeK
  unfold pureWZ2Prop62CallerQ0
  rw [← data.parameters.K_eq]
  calc
    4 * (pureWZ2Prop62CallerCstar delta A eta).toReal *
          (rho /
            (data.parameters.K *
              (pureWZ2Prop62CallerCstar delta A eta).toReal)) =
        (4 * rho) / data.parameters.K := by
      field_simp [data.parameters.K_pos.ne', CstarRealPos.ne']
    _ ≤ 1 := (div_le_one data.parameters.K_pos).2 fourRhoLeK

/-- The first packet-radius estimate supplied by the caller parameters. -/
theorem packet_metric_bound
    {packetScale : ℝ}
    (packetScale_lt :
      packetScale < rho / data.parameters.K) :
    600000 * packetScale + 6 * data.parameters.width ≤
      rho / 2 :=
  data.parameters.packet_metric_bound packetScale_lt

/-- The stronger caller-relative packet-radius estimate. -/
theorem packet_metric_bound_c0
    {packetScale : ℝ}
    (packetScale_lt :
      packetScale < rho / data.parameters.K) :
    600000 * packetScale + 6 * data.parameters.width ≤
      c0 * rho :=
  data.parameters.packet_metric_bound_c0 packetScale_lt

end PureWZ2Prop62CallerParameterAbsorptionData

/--
Choose one threshold which simultaneously:

* lies below `1 / 100`;
* makes `Cstar = delta ^ (-A * eta)` at least four;
* separates the geometric schedule with step `2 * A * eta`;
* absorbs the caller-dependent `K`;
* makes the caller anchor a legal requested scale; and
* carries all caller-width and residue-stride estimates.

The threshold may depend on `c0`, while `pureWZ2Prop62CallerCWAPower A`
depends only on `A`.
-/
theorem exists_pureWZ2Prop62CallerParameterAbsorption
    (A : ℕ) (A_ge_one : 1 ≤ A)
    (epsilon eta c0 : ℝ)
    (epsilon_pos : 0 < epsilon)
    (eta_pos : 0 < eta)
    (loss_small :
      6 * (A : ℝ) * eta ≤ epsilon / 100)
    (c0_pos : 0 < c0) :
    ∃ delta0 : ℝ,
      0 < delta0 ∧
      delta0 ≤ 1 / 100 ∧
      ∀ {delta rho : ℝ},
        0 < delta →
        delta ≤ delta0 →
        0 < rho →
        rho ≤ 1 →
        Real.rpow delta (1 - epsilon) ≤ rho →
        Nonempty
          (PureWZ2Prop62CallerParameterAbsorptionData
            A epsilon eta c0 delta rho) := by
  let loss := pureWZ2Prop62CallerLoss A eta
  let step := pureWZ2Prop62CallerStep A eta
  let K := pureWZ2Prop62CallerK c0
  have lossPos : 0 < loss := by
    exact pureWZ2Prop62CallerLoss_pos A_ge_one eta_pos
  have lossLtEpsilon : loss < epsilon := by
    exact
      pureWZ2Prop62CallerLoss_lt_epsilon
        A_ge_one eta_pos loss_small
  have stepPos : 0 < step := by
    exact pureWZ2Prop62CallerStep_pos A_ge_one eta_pos
  have KPos : 0 < K := by
    unfold K pureWZ2Prop62CallerK
    exact div_pos (by norm_num) <|
      lt_min c0_pos zero_lt_one
  rcases
      exists_delta_realRpowENN_bound
        (4 : ENNReal) (by norm_num) lossPos with
    ⟨fourScale, fourScalePos, fourScaleLeOne, fourBound⟩
  rcases
      exists_delta_mul_rpow_le_rpow
        4 (by norm_num)
        (alpha := -loss) (beta := -step)
        (by
          dsimp only [step, pureWZ2Prop62CallerStep]
          linarith) with
    ⟨separationScale, separationScalePos,
      separationScaleLeOne, separationBound⟩
  rcases
      exists_delta_mul_rpow_le_rpow
        K KPos.le
        (alpha := 1 - loss) (beta := 1 - epsilon)
        (by linarith) with
    ⟨absorptionScale, absorptionScalePos,
      absorptionScaleLeOne, absorptionBound⟩
  let delta0 :=
    min (1 / 100 : ℝ)
      (min fourScale
        (min separationScale absorptionScale))
  have delta0Pos : 0 < delta0 := by
    exact
      lt_min (by norm_num)
        (lt_min fourScalePos
          (lt_min separationScalePos absorptionScalePos))
  have delta0LeOneHundred :
      delta0 ≤ 1 / 100 := min_le_left _ _
  refine ⟨delta0, delta0Pos, delta0LeOneHundred, ?_⟩
  intro delta rho deltaPos deltaLe rhoPos rhoLeOne rhoLower
  have deltaLeFour : delta ≤ fourScale :=
    deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeSeparation : delta ≤ separationScale :=
    deltaLe.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeAbsorption : delta ≤ absorptionScale :=
    deltaLe.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
  have deltaLeOneHundred :
      delta ≤ 1 / 100 :=
    deltaLe.trans delta0LeOneHundred
  have deltaLeOne : delta ≤ 1 := by
    exact deltaLeOneHundred.trans (by norm_num)
  let parameters :=
    pureWZ2Prop62CallerParameters c0 rho c0_pos rhoPos
  have constantAbsorption :
      parameters.K * Real.rpow delta (1 - loss) ≤
        Real.rpow delta (1 - epsilon) := by
    rw [parameters.K_eq]
    exact
      absorptionBound delta deltaPos deltaLeAbsorption
  have CstarFinite :
      pureWZ2Prop62CallerCstar delta A eta ≠ ⊤ := by
    simp [pureWZ2Prop62CallerCstar,
      Kakeya.realRpowENN]
  have CstarReal :
      (pureWZ2Prop62CallerCstar delta A eta).toReal =
        Real.rpow delta (-loss) := by
    simpa [pureWZ2Prop62CallerCstar, Kakeya.realRpowENN,
      loss] using
      ENNReal.toReal_ofReal
        (Real.rpow_nonneg deltaPos.le
          (-pureWZ2Prop62CallerLoss A eta))
  have CstarFour :
      4 ≤ pureWZ2Prop62CallerCstar delta A eta := by
    simpa [pureWZ2Prop62CallerCstar, loss] using
      fourBound delta deltaPos deltaLeFour
  have requestedSeparation :
      4 * (pureWZ2Prop62CallerCstar delta A eta).toReal ≤
        Real.rpow delta (-pureWZ2Prop62CallerStep A eta) := by
    rw [CstarReal]
    simpa [step] using
      separationBound delta deltaPos deltaLeSeparation
  have CstarRealFour :
      4 ≤
        (pureWZ2Prop62CallerCstar delta A eta).toReal := by
    have converted :=
      ENNReal.toReal_mono CstarFinite CstarFour
    norm_num at converted ⊢
    exact converted
  have oneLeK : 1 ≤ parameters.K := by
    rw [parameters.K_eq, pureWZ2Prop62CallerK]
    have thetaPos : 0 <
        pureWZ2Prop62CallerTheta c0 := by
      rw [← parameters.theta_eq]
      exact parameters.theta_pos
    apply (le_div_iff₀ thetaPos).2
    have thetaLeOne :
        pureWZ2Prop62CallerTheta c0 ≤ 1 := by
      rw [← parameters.theta_eq]
      exact parameters.theta_le_one
    nlinarith
  have denominatorPos :
      0 <
        parameters.K *
          (pureWZ2Prop62CallerCstar delta A eta).toReal := by
    exact mul_pos parameters.K_pos <| lt_of_lt_of_le (by norm_num) CstarRealFour
  have oneLeDenominator :
      1 ≤
        parameters.K *
          (pureWZ2Prop62CallerCstar delta A eta).toReal := by
    nlinarith [oneLeK, CstarRealFour]
  have powerIdentity :
      Real.rpow delta (1 - loss) =
        Real.rpow delta (-loss) * delta := by
    calc
      Real.rpow delta (1 - loss) =
          Real.rpow delta (-loss + 1) := by ring_nf
      _ =
          Real.rpow delta (-loss) *
            Real.rpow delta 1 :=
        Real.rpow_add deltaPos (-loss) 1
      _ = Real.rpow delta (-loss) * delta := by
        congr 1
        exact Real.rpow_one delta
  have q0Lower :
      delta ≤ pureWZ2Prop62CallerQ0 delta rho c0 A eta := by
    unfold pureWZ2Prop62CallerQ0
    rw [← parameters.K_eq]
    apply (le_div_iff₀ denominatorPos).2
    calc
      delta *
          (parameters.K *
            (pureWZ2Prop62CallerCstar delta A eta).toReal) =
          parameters.K * Real.rpow delta (1 - loss) := by
        rw [CstarReal, powerIdentity]
        ring
      _ ≤ Real.rpow delta (1 - epsilon) :=
        constantAbsorption
      _ ≤ rho := rhoLower
  have q0Upper :
      pureWZ2Prop62CallerQ0 delta rho c0 A eta ≤ 1 := by
    unfold pureWZ2Prop62CallerQ0
    rw [← parameters.K_eq]
    exact
      (div_le_self rhoPos.le oneLeDenominator).trans rhoLeOne
  exact
    ⟨{
      delta_pos := deltaPos
      delta_le_one_hundred := deltaLeOneHundred
      rho_pos := rhoPos
      rho_le_one := rhoLeOne
      epsilon_pos := epsilon_pos
      loss_pos := lossPos
      loss_lt_epsilon := lossLtEpsilon
      step_pos := stepPos
      cwaPower_pos :=
        pureWZ2Prop62CallerCWAPower_pos A_ge_one
      parameters := parameters
      Cstar_four := CstarFour
      Cstar_finite := CstarFinite
      requested_separation := requestedSeparation
      constant_absorption := constantAbsorption
      q0_lower := q0Lower
      q0_upper := q0Upper
      width_pos := parameters.width_pos
      six_width_le := parameters.six_width_le
      strict_separation := parameters.strict_separation
      upper_strong_separation := parameters.upper_strong_separation
    }⟩

end Kakeya.Assouad

end
