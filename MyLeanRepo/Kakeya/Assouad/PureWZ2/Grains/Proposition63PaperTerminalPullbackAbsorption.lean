import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PaperTerminalPullbackDensity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63CrossDegreeAbsorption

/-!
# Pre-runtime absorption for the terminal whole-cell pullback

The terminal density lift loses one terminal regularity factor and the
sixty-one logarithmic factors in the sticky refinement fraction.  The
requested-scale lower window converts the remaining coarse density power
back to the fine scale.  Thus the exact positive power available for
absorption is

`densityLoss - normalizationLoss -
  (1 - stickyLoss) * (coarseLoss + 2 * stickyLoss)`.

The cutoff below is chosen before `delta`, `rho`, the tube family, and the
terminal regularity are exposed.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

open Prop62PaperAudit.V4

/-- Family-free pre-runtime receipt for the scalar hypothesis of
`Proposition63RichTerminalStickyData.terminal_commonHull_candidateExtremal_densityLift`.
-/
structure Proposition63PaperTerminalPullbackAbsorptionData
    (normalizationLoss stickyLoss coarseLoss densityLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_lt_one : delta₀ < 1
  absorb :
    ∀ {delta rho : ℝ},
      0 < delta → delta ≤ delta₀ →
      0 < rho →
      Real.rpow delta (1 - stickyLoss) ≤ rho →
      ∀ {regularity : ℕ},
        0 < regularity →
        (regularity : ENNReal) ≤ logarithmicLoss delta ^ 10 →
        ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN delta densityLoss *
              Kakeya.realRpowENN delta 2 ≤
          (regularity : ENNReal)⁻¹ *
              Kakeya.realRpowENN rho
                (coarseLoss + 2 * stickyLoss) *
              wz2PaperPureRefinementFraction delta 61 *
              Kakeya.realRpowENN delta (normalizationLoss + 2)

/-- Choose the terminal pullback cutoff from the exact strict exponent gap.
The logarithmic exponent is `10 + 61 = 71`: ten powers bound terminal
regularity and sixty-one powers invert the refinement fraction. -/
theorem proposition63_paper_terminal_pullback_absorption
    (normalizationLoss stickyLoss coarseLoss densityLoss : ℝ)
    (coarsePowerNonnegative : 0 ≤ coarseLoss + 2 * stickyLoss)
    (gap : 0 <
      densityLoss - normalizationLoss -
        (1 - stickyLoss) * (coarseLoss + 2 * stickyLoss)) :
    Nonempty (Proposition63PaperTerminalPullbackAbsorptionData
      normalizationLoss stickyLoss coarseLoss densityLoss) := by
  let exponentGap : ℝ :=
    densityLoss - normalizationLoss -
      (1 - stickyLoss) * (coarseLoss + 2 * stickyLoss)
  have exponentGapPos : 0 < exponentGap := by
    simpa [exponentGap] using gap
  let fixed : ENNReal :=
    (55296 : ENNReal) * Kakeya.deltaTubeVolume 1
  have fixedTop : fixed ≠ ⊤ := by
    dsimp only [fixed]
    exact ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top
  rcases exists_delta_C_pow_log_absorbed_ennreal
      fixed fixedTop 2 (by norm_num) exponentGapPos
      (show 0 < (71 : ℕ) by norm_num) with
    ⟨logDelta, logDeltaPos, logDeltaLeOne, logarithmicAbsorption⟩
  let delta₀ : ℝ := min logDelta (Real.exp (-1))
  have delta₀Pos : 0 < delta₀ :=
    lt_min logDeltaPos (Real.exp_pos _)
  have delta₀LeOne : delta₀ ≤ 1 :=
    (min_le_left _ _).trans logDeltaLeOne
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := delta₀Pos
    delta₀_le_one := delta₀LeOne
    delta₀_lt_one :=
      (min_le_right _ _).trans_lt
        (Real.exp_lt_one_iff.mpr (by norm_num))
    absorb := ?_
  }⟩
  intro delta rho deltaPos deltaLe rhoPos requestedLower regularity
    regularityPos regularityLe
  have deltaLeOne : delta ≤ 1 := deltaLe.trans delta₀LeOne
  have deltaLtOne : delta < 1 := deltaLe.trans_lt <|
    (min_le_right _ _).trans_lt
      (Real.exp_lt_one_iff.mpr (by norm_num))
  let envelope : ENNReal :=
    ENNReal.ofReal (2 * (1 + Real.log delta⁻¹))
  have logarithmicLe : logarithmicLoss delta ≤ envelope := by
    have bound := proposition63_logarithmicLoss_le_two_logEnvelope
      deltaPos deltaLeOne
    change
      (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ≤
        ENNReal.ofReal (2 * (1 + Real.log delta⁻¹))
    calc
      (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ≤
          2 * ENNReal.ofReal (1 + Real.log delta⁻¹) := bound
      _ = ENNReal.ofReal (2 * (1 + Real.log delta⁻¹)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  let logTerm : ENNReal :=
    ENNReal.ofReal (Real.log (1 / delta))
  have logTermLe : logTerm ≤ envelope := by
    dsimp only [logTerm, envelope]
    apply ENNReal.ofReal_mono
    rw [show 1 / delta = delta⁻¹ by simp]
    have logNonnegative : 0 ≤ Real.log delta⁻¹ :=
      Real.log_nonneg ((one_le_inv₀ deltaPos).mpr deltaLeOne)
    linarith
  have regularityLog :
      (regularity : ENNReal) * logTerm ^ 61 ≤ envelope ^ 71 := by
    calc
      (regularity : ENNReal) * logTerm ^ 61 ≤
          logarithmicLoss delta ^ 10 * envelope ^ 61 := by
        gcongr
      _ ≤ envelope ^ 10 * envelope ^ 61 := by gcongr
      _ = envelope ^ 71 := by ring
  have envelopeAbsorption :
      fixed * envelope ^ 71 ≤
        Kakeya.realRpowENN delta (-exponentGap) := by
    simpa [envelope] using
      logarithmicAbsorption delta deltaPos
        (deltaLe.trans (min_le_left _ _))
  have fixedLog :
      fixed * ((regularity : ENNReal) * logTerm ^ 61) ≤
        Kakeya.realRpowENN delta (-exponentGap) := by
    exact (mul_le_mul_left' regularityLog fixed).trans envelopeAbsorption
  have coarsePowerLower :
      Kakeya.realRpowENN delta
          ((1 - stickyLoss) * (coarseLoss + 2 * stickyLoss)) ≤
        Kakeya.realRpowENN rho (coarseLoss + 2 * stickyLoss) := by
    have realMonotone := Real.rpow_le_rpow
      (Real.rpow_nonneg deltaPos.le (1 - stickyLoss))
      requestedLower coarsePowerNonnegative
    calc
      Kakeya.realRpowENN delta
          ((1 - stickyLoss) * (coarseLoss + 2 * stickyLoss)) =
          ENNReal.ofReal
            (Real.rpow (Real.rpow delta (1 - stickyLoss))
              (coarseLoss + 2 * stickyLoss)) := by
        apply congrArg ENNReal.ofReal
        exact Real.rpow_mul deltaPos.le _ _
      _ ≤ Kakeya.realRpowENN rho
          (coarseLoss + 2 * stickyLoss) := by
        exact ENNReal.ofReal_mono realMonotone
  have multiplied :
      (fixed * Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta 2) *
          ((regularity : ENNReal) * logTerm ^ 61) ≤
        Kakeya.realRpowENN rho (coarseLoss + 2 * stickyLoss) *
          Kakeya.realRpowENN delta (normalizationLoss + 2) := by
    have powerSplit :
        Kakeya.realRpowENN delta densityLoss *
            Kakeya.realRpowENN delta 2 =
          (Kakeya.realRpowENN delta
              ((1 - stickyLoss) * (coarseLoss + 2 * stickyLoss)) *
            Kakeya.realRpowENN delta (normalizationLoss + 2)) *
            Kakeya.realRpowENN delta exponentGap := by
      rw [← realRpowENN_add deltaPos, ← realRpowENN_add deltaPos,
        ← realRpowENN_add deltaPos]
      congr 1
      dsimp only [exponentGap]
      ring
    calc
      (fixed * Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta 2) *
          ((regularity : ENNReal) * logTerm ^ 61) =
        Kakeya.realRpowENN delta
            ((1 - stickyLoss) * (coarseLoss + 2 * stickyLoss)) *
          Kakeya.realRpowENN delta (normalizationLoss + 2) *
          (Kakeya.realRpowENN delta exponentGap *
            (fixed * ((regularity : ENNReal) * logTerm ^ 61))) := by
        rw [show fixed * Kakeya.realRpowENN delta densityLoss *
              Kakeya.realRpowENN delta 2 =
            fixed * (Kakeya.realRpowENN delta densityLoss *
              Kakeya.realRpowENN delta 2) by ring,
          powerSplit]
        ring
      _ ≤ Kakeya.realRpowENN delta
            ((1 - stickyLoss) * (coarseLoss + 2 * stickyLoss)) *
          Kakeya.realRpowENN delta (normalizationLoss + 2) * 1 := by
        gcongr
        calc
          Kakeya.realRpowENN delta exponentGap *
                (fixed * ((regularity : ENNReal) * logTerm ^ 61)) ≤
              Kakeya.realRpowENN delta exponentGap *
                Kakeya.realRpowENN delta (-exponentGap) := by
            gcongr
          _ = 1 := by
            rw [← realRpowENN_add deltaPos]
            simp [Kakeya.realRpowENN]
      _ ≤ Kakeya.realRpowENN rho
            (coarseLoss + 2 * stickyLoss) *
          Kakeya.realRpowENN delta (normalizationLoss + 2) := by
        simpa using mul_le_mul_right' coarsePowerLower
          (Kakeya.realRpowENN delta (normalizationLoss + 2))
  have regularityTop : (regularity : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have logTermPos : 0 < logTerm := by
    apply ENNReal.ofReal_pos.mpr
    exact Real.log_pos (one_lt_one_div deltaPos deltaLtOne)
  have logTermTop : logTerm ≠ ⊤ := ENNReal.ofReal_ne_top
  have logPowerPos : 0 < logTerm ^ 61 := by positivity
  have logPowerTop : logTerm ^ 61 ≠ ⊤ :=
    ENNReal.pow_ne_top logTermTop
  rw [wz2PaperPureRefinementFraction, ← ENNReal.inv_pow]
  have regularityZero : (regularity : ENNReal) ≠ 0 := by
    exact_mod_cast regularityPos.ne'
  have productZero :
      (regularity : ENNReal) * logTerm ^ 61 ≠ 0 :=
    mul_ne_zero regularityZero logPowerPos.ne'
  have productTop :
      (regularity : ENNReal) * logTerm ^ 61 ≠ ⊤ :=
    ENNReal.mul_ne_top regularityTop logPowerTop
  have scaled := mul_le_mul_right' multiplied
    (((regularity : ENNReal) * logTerm ^ 61)⁻¹)
  have cancel :
      ((regularity : ENNReal) * logTerm ^ 61) *
          ((regularity : ENNReal) * logTerm ^ 61)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel productZero productTop
  rw [show
      (fixed * Kakeya.realRpowENN delta densityLoss *
            Kakeya.realRpowENN delta 2 *
          ((regularity : ENNReal) * logTerm ^ 61)) *
          ((regularity : ENNReal) * logTerm ^ 61)⁻¹ =
        fixed * Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta 2 *
          (((regularity : ENNReal) * logTerm ^ 61) *
            ((regularity : ENNReal) * logTerm ^ 61)⁻¹) by ring,
    cancel, mul_one] at scaled
  change
    fixed * Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta 2 ≤
      (regularity : ENNReal)⁻¹ *
          Kakeya.realRpowENN rho (coarseLoss + 2 * stickyLoss) *
          (logTerm ^ 61)⁻¹ *
          Kakeya.realRpowENN delta (normalizationLoss + 2)
  rw [show
      (regularity : ENNReal)⁻¹ *
            Kakeya.realRpowENN rho (coarseLoss + 2 * stickyLoss) *
            (logTerm ^ 61)⁻¹ *
            Kakeya.realRpowENN delta (normalizationLoss + 2) =
        (Kakeya.realRpowENN rho (coarseLoss + 2 * stickyLoss) *
            Kakeya.realRpowENN delta (normalizationLoss + 2)) *
          ((regularity : ENNReal) * logTerm ^ 61)⁻¹ by
    rw [ENNReal.mul_inv
      (Or.inl regularityZero) (Or.inl regularityTop)]
    ring]
  exact scaled

/-- A schedule-facing constructor which exposes the simpler sufficient
budget

`normalizationLoss + coarseLoss + 2 * stickyLoss < densityLoss`.

For the staged choices `coarseLoss = 7/8 * outputLoss` and
`densityLoss = 15/16 * outputLoss`, this leaves exactly `outputLoss / 16`
for normalization and the two sticky losses. -/
theorem proposition63_paper_terminal_pullback_absorption_of_linear_budget
    (normalizationLoss stickyLoss coarseLoss densityLoss : ℝ)
    (stickyLossNonnegative : 0 ≤ stickyLoss)
    (coarsePowerNonnegative : 0 ≤ coarseLoss + 2 * stickyLoss)
    (linearBudget :
      normalizationLoss + coarseLoss + 2 * stickyLoss < densityLoss) :
    Nonempty (Proposition63PaperTerminalPullbackAbsorptionData
      normalizationLoss stickyLoss coarseLoss densityLoss) := by
  apply proposition63_paper_terminal_pullback_absorption
    normalizationLoss stickyLoss coarseLoss densityLoss
    coarsePowerNonnegative
  have contraction :
      (1 - stickyLoss) * (coarseLoss + 2 * stickyLoss) ≤
        coarseLoss + 2 * stickyLoss := by
    nlinarith
  linarith

/-- Specialize the family-free receipt to the regularity certificate carried
by one rich terminal output. -/
theorem Proposition63RichTerminalStickyData.terminal_pullback_scalar_of_absorption
    {delta sigma sourceLoss normalizationLoss stickyLoss densityLoss
      coarseLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := stickyLoss) croppedShading reentry rho)
    (absorption : Proposition63PaperTerminalPullbackAbsorptionData
      normalizationLoss stickyLoss coarseLoss densityLoss)
    (deltaSmall : delta ≤ absorption.delta₀)
    (requestedLower :
      Real.rpow delta (1 - stickyLoss) ≤ rho.1) :
    ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta 2 ≤
      (rich.terminal.regularity : ENNReal)⁻¹ *
          Kakeya.realRpowENN rho.1 (coarseLoss + 2 * stickyLoss) *
          wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta (normalizationLoss + 2) := by
  exact absorption.absorb reentry.cropped_extremal.delta_pos deltaSmall
    rich.data.coarse_extremal.delta_pos requestedLower
    rich.terminal.regularity_pos rich.terminal_regularity_bound

end Kakeya.Assouad.PureWZ2

end
