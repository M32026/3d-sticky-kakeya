import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalCleanupWeightPower
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalLocalConflictPacking
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.BoundedSourceCardLog
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBoundaryLogCoefficient
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Source-power bound for direct half-offset cleanup regularization

The external weight has the genuine target-tube-area factor
`targetDelta ^ 2`.  This file keeps it paired with the inverse mass-per-source
normalization and feeds that ratio directly to
`outputConstant_le_externalWeightRatioOutputEnvelope`.  In particular, the
target-area gain is not discarded before the source-power ledger is formed.

The schedule depth is supplied explicitly before the runtime source (and is
specialized below to `pureWZ2FixedScheduleLevelCount epsilon`).  Its remaining
logarithmic cost is absorbed by an arbitrary positive `logLoss`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

namespace PureWZ2DirectCommonYSourceAssembly
namespace TerminalGeometry
namespace PureWZ2ExternalWeightRegularizationData

variable {logExponent : ℕ} {sigma epsilon delta : ℝ}
  {commonSource : PureWZ2DirectCommonYSourceAssembly
    logExponent sigma epsilon delta}

/-- The coefficient in the literal per-source terminal-area upper bound. -/
def terminalCleanupWeightUpperCoefficient : ENNReal :=
  55296 * Kakeya.deltaTubeVolume 1

theorem terminalCleanupWeightUpperCoefficient_ne_top :
    terminalCleanupWeightUpperCoefficient ≠ ⊤ := by
  unfold terminalCleanupWeightUpperCoefficient
  exact ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top

/-- Fixed coefficient left after the cleanup normalization and terminal area
are paired. -/
def terminalCleanupNormalizationWeightRatioCoefficient
    (degreeCoefficient : ENNReal) : ENNReal :=
  (terminalMassCoefficient / degreeCoefficient)⁻¹ *
    terminalCleanupWeightUpperCoefficient

theorem terminalCleanupNormalizationWeightRatioCoefficient_ne_top
    {degreeCoefficient : ENNReal}
    (_hdegreeZero : degreeCoefficient ≠ 0)
    (hdegreeTop : degreeCoefficient ≠ ⊤) :
    terminalCleanupNormalizationWeightRatioCoefficient degreeCoefficient ≠ ⊤ := by
  have hlowerZero : terminalMassCoefficient / degreeCoefficient ≠ 0 :=
    (ENNReal.div_ne_zero).2 ⟨terminalMassCoefficient_ne_zero, hdegreeTop⟩
  unfold terminalCleanupNormalizationWeightRatioCoefficient
  exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hlowerZero)
    terminalCleanupWeightUpperCoefficient_ne_top

/-- The actual cleanup normalization inherits the centered-terminal mass
lower bound after division by a generic source-power degree envelope. -/
theorem cleanupNormalizationWeight_lower_of_separate_degree_power
    {degreeBound degreeCoefficient : ENNReal}
    {degreeLoss : ℝ}
    (terminal : commonSource.TerminalGeometry)
    (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound)
    (hdegree : degreeBound + 1 ≤
      degreeCoefficient * Kakeya.realRpowENN delta (-degreeLoss))
    (hdegreeZero : degreeCoefficient ≠ 0)
    (hdegreeTop : degreeCoefficient ≠ ⊤) :
    (terminalMassCoefficient / degreeCoefficient) *
        Kakeya.realRpowENN delta
          (commonSource.halfOffsetAssembly.technicalLoss + 2 + 2 * epsilon +
            degreeLoss) ≤
      cleanupNormalizationWeight (commonSource := commonSource) cleanup := by
  have hdelta : 0 < delta :=
    commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hpowPos : 0 < Kakeya.realRpowENN delta degreeLoss :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)
  have hpowTop : Kakeya.realRpowENN delta degreeLoss ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have hneg : Kakeya.realRpowENN delta (-degreeLoss) =
      (Kakeya.realRpowENN delta degreeLoss)⁻¹ :=
    (pure_wz2_realRpowENN_inv hdelta).symm
  have hpow : Kakeya.realRpowENN delta
      (commonSource.halfOffsetAssembly.technicalLoss + 2 + 2 * epsilon +
        degreeLoss) =
      Kakeya.realRpowENN delta
          (commonSource.halfOffsetAssembly.technicalLoss + 2 + 2 * epsilon) *
        Kakeya.realRpowENN delta degreeLoss := by
    rw [← realRpowENN_add hdelta]
  have hmass := centeredCubicalShading_mass_lower_source_power
    (commonSource := commonSource) terminal
  have hcleanup : terminal.centeredCubicalShading.mass ≤
      (degreeBound + 1) * cleanup.shading.mass := cleanup.mass_lower
  have hdegreeMass := mul_le_mul_right' hdegree cleanup.shading.mass
  have hbound := hmass.trans (hcleanup.trans hdegreeMass)
  have hscaled := mul_le_mul_right hbound
    (Kakeya.realRpowENN delta degreeLoss)
  have hcancel :
      Kakeya.realRpowENN delta degreeLoss *
          ((degreeCoefficient * Kakeya.realRpowENN delta (-degreeLoss)) *
            cleanup.shading.mass) =
        degreeCoefficient * cleanup.shading.mass := by
    rw [hneg]
    calc
      Kakeya.realRpowENN delta degreeLoss *
            (degreeCoefficient *
              (Kakeya.realRpowENN delta degreeLoss)⁻¹ *
                cleanup.shading.mass) =
          (Kakeya.realRpowENN delta degreeLoss *
              (Kakeya.realRpowENN delta degreeLoss)⁻¹) *
            (degreeCoefficient * cleanup.shading.mass) := by ring
      _ = degreeCoefficient * cleanup.shading.mass := by
        rw [ENNReal.mul_inv_cancel hpowPos.ne' hpowTop, one_mul]
  rw [hcancel] at hscaled
  have hcore :
      ((Kakeya.realRpowENN delta degreeLoss) *
        (terminalMassCoefficient *
          Kakeya.realRpowENN delta
            (commonSource.halfOffsetAssembly.technicalLoss + 2 + 2 * epsilon) *
          commonSource.halfOffsetAssembly.cfg.family.enncard)) /
        degreeCoefficient ≤ cleanup.shading.mass := by
    apply (ENNReal.div_le_iff hdegreeZero hdegreeTop).mpr
    simpa [mul_comm] using hscaled
  unfold cleanupNormalizationWeight
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (by
      change (commonSource.halfOffsetAssembly.cfg.family.card : ENNReal) ≠ 0
      exact_mod_cast commonSource.halfOffsetAssembly.cfg.extremal.nonempty.ne'))
    (Or.inl (by simp [Kakeya.Streamlined.TubeFamily.enncard]))).mpr
  rw [ENNReal.div_eq_inv_mul] at hcore
  rw [hpow, ENNReal.div_eq_inv_mul]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcore

/-- Ratio-aware cancellation for the actual external weight.  The
`targetDelta ^ 2` gain cancels the `delta ^ 2` part of the inverse cleanup
normalization, leaving the explicit source loss
`technicalLoss + degreeLoss + 6 * epsilon`. -/
theorem cleanupNormalizationWeight_inv_mul_weightUpper_le_source_power
    {degreeBound degreeCoefficient : ENNReal}
    {degreeLoss : ℝ}
    (terminal : commonSource.TerminalGeometry)
    (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound)
    (htarget : terminal.targetDelta ≤ Real.rpow delta (1 - 2 * epsilon))
    (hdegree : degreeBound + 1 ≤
      degreeCoefficient * Kakeya.realRpowENN delta (-degreeLoss))
    (hdegreeZero : degreeCoefficient ≠ 0)
    (hdegreeTop : degreeCoefficient ≠ ⊤) :
    (cleanupNormalizationWeight (commonSource := commonSource) cleanup)⁻¹ *
        (terminalCleanupWeightUpperCoefficient *
          Kakeya.realRpowENN terminal.targetDelta 2) ≤
      terminalCleanupNormalizationWeightRatioCoefficient degreeCoefficient *
        Kakeya.realRpowENN delta
          (-(commonSource.halfOffsetAssembly.technicalLoss + degreeLoss +
            6 * epsilon)) := by
  let lowerCoefficient := terminalMassCoefficient / degreeCoefficient
  let sourceExponent :=
    commonSource.halfOffsetAssembly.technicalLoss + 2 + 2 * epsilon +
      degreeLoss
  have hdelta : 0 < delta :=
    commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hlower := cleanupNormalizationWeight_lower_of_separate_degree_power
    (commonSource := commonSource) terminal cleanup hdegree hdegreeZero hdegreeTop
  have hlowerCoefficientZero : lowerCoefficient ≠ 0 :=
    (ENNReal.div_ne_zero).2 ⟨terminalMassCoefficient_ne_zero, hdegreeTop⟩
  have hlowerCoefficientTop : lowerCoefficient ≠ ⊤ :=
    ENNReal.div_ne_top terminalMassCoefficient_ne_top hdegreeZero
  have hpowerPos : 0 < Kakeya.realRpowENN delta sourceExponent :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)
  have hpowerTop : Kakeya.realRpowENN delta sourceExponent ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have hinverse :
      (cleanupNormalizationWeight (commonSource := commonSource) cleanup)⁻¹ ≤
        lowerCoefficient⁻¹ *
          Kakeya.realRpowENN delta (-sourceExponent) := by
    calc
      (cleanupNormalizationWeight (commonSource := commonSource) cleanup)⁻¹ ≤
          (lowerCoefficient *
            Kakeya.realRpowENN delta sourceExponent)⁻¹ :=
        ENNReal.inv_le_inv.mpr (by simpa [lowerCoefficient, sourceExponent] using hlower)
      _ = lowerCoefficient⁻¹ *
            (Kakeya.realRpowENN delta sourceExponent)⁻¹ := by
        rw [ENNReal.mul_inv (Or.inl hlowerCoefficientZero)
          (Or.inl hlowerCoefficientTop)]
      _ = lowerCoefficient⁻¹ *
            Kakeya.realRpowENN delta (-sourceExponent) := by
        rw [pure_wz2_realRpowENN_inv hdelta]
  have htargetPower :
      Kakeya.realRpowENN terminal.targetDelta 2 ≤
        Kakeya.realRpowENN delta ((1 - 2 * epsilon) * 2) :=
    pure_wz2_target_power_upper hdelta
      commonSource.halfOffsetLineClassTargetDelta_pos.le htarget (by norm_num)
  have hpower :
      Kakeya.realRpowENN delta (-sourceExponent) *
          Kakeya.realRpowENN delta ((1 - 2 * epsilon) * 2) =
        Kakeya.realRpowENN delta
          (-(commonSource.halfOffsetAssembly.technicalLoss + degreeLoss +
            6 * epsilon)) := by
    rw [← realRpowENN_add hdelta]
    dsimp only [sourceExponent]
    congr 1
    ring
  calc
    (cleanupNormalizationWeight (commonSource := commonSource) cleanup)⁻¹ *
          (terminalCleanupWeightUpperCoefficient *
            Kakeya.realRpowENN terminal.targetDelta 2) ≤
        (lowerCoefficient⁻¹ *
          Kakeya.realRpowENN delta (-sourceExponent)) *
            (terminalCleanupWeightUpperCoefficient *
              Kakeya.realRpowENN delta ((1 - 2 * epsilon) * 2)) := by
      gcongr
    _ = (lowerCoefficient⁻¹ * terminalCleanupWeightUpperCoefficient) *
          (Kakeya.realRpowENN delta (-sourceExponent) *
            Kakeya.realRpowENN delta ((1 - 2 * epsilon) * 2)) := by ring
    _ = terminalCleanupNormalizationWeightRatioCoefficient degreeCoefficient *
          Kakeya.realRpowENN delta
            (-(commonSource.halfOffsetAssembly.technicalLoss + degreeLoss +
              6 * epsilon)) := by
      rw [hpower]
      rfl

/-- Fixed coefficient for a ratio-aware external-weight output envelope. -/
def terminalCleanupOutputFixedCoefficient (levelCount : ℕ) : ENNReal :=
  let degreeCoefficient : ENNReal :=
    16 * ((levelCount + 1 : ℕ) : ENNReal)
  1 + degreeCoefficient + 8 * degreeCoefficient

theorem terminalCleanupOutputFixedCoefficient_ne_top (levelCount : ℕ) :
    terminalCleanupOutputFixedCoefficient levelCount ≠ ⊤ := by
  have hdegree : (16 * ((levelCount + 1 : ℕ) : ENNReal)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)
  unfold terminalCleanupOutputFixedCoefficient
  exact ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨by norm_num, hdegree⟩,
      ENNReal.mul_ne_top (by norm_num) hdegree⟩

/-- A ratio-aware envelope is bounded by two ambient powers, the retained
normalization-weight ratio, and the common fixed-depth logarithmic power. -/
theorem externalWeightRatioOutputEnvelope_le_terminalCleanupMaster
    (ambient ratio logEnvelope : ENNReal) (levelCount : ℕ)
    (hambient : 1 ≤ ambient) (hratio : 1 ≤ ratio)
    (hlog : 1 ≤ logEnvelope) :
    Kakeya.Assouad.PureWZ2ExternalWeightRegularizationData.pureWZ2ExternalWeightRatioOutputEnvelope
        ambient (ambient ^ 2) ratio
        logEnvelope levelCount ≤
      terminalCleanupOutputFixedCoefficient levelCount *
        ambient ^ 2 * ratio * logEnvelope ^ (2 * levelCount + 3) := by
  let degreeCoefficient : ENNReal :=
    16 * ((levelCount + 1 : ℕ) : ENNReal)
  let ratioCoefficient : ENNReal := 8 * degreeCoefficient
  have hcoefficientOne :
      1 ≤ terminalCleanupOutputFixedCoefficient levelCount := by
    unfold terminalCleanupOutputFixedCoefficient
    exact le_add_right (le_add_right le_rfl)
  have hdegreeCoefficient : degreeCoefficient ≤
      terminalCleanupOutputFixedCoefficient levelCount := by
    unfold terminalCleanupOutputFixedCoefficient
    dsimp only [degreeCoefficient]
    exact le_add_right (le_add_left le_rfl)
  have hratioCoefficient : ratioCoefficient ≤
      terminalCleanupOutputFixedCoefficient levelCount := by
    unfold terminalCleanupOutputFixedCoefficient
    dsimp only [ratioCoefficient, degreeCoefficient]
    exact le_add_left le_rfl
  have hambientSquare : ambient ≤ ambient ^ 2 := by
    simpa [pow_two] using mul_le_mul_right' hambient ambient
  have hdegreePower : logEnvelope ^ (levelCount + 1) ≤
      logEnvelope ^ (2 * levelCount + 3) :=
    pow_le_pow_right' hlog (by omega)
  have hratioPower :
      logEnvelope ^ (levelCount + 2) *
          logEnvelope ^ (levelCount + 1) =
        logEnvelope ^ (2 * levelCount + 3) := by
    rw [← pow_add]
    congr 1
    omega
  unfold Kakeya.Assouad.PureWZ2ExternalWeightRegularizationData.pureWZ2ExternalWeightRatioOutputEnvelope
  apply max_le
  · calc
      ambient ^ 2 = 1 * ambient ^ 2 * 1 * 1 := by simp
      _ ≤ terminalCleanupOutputFixedCoefficient levelCount *
            ambient ^ 2 * ratio *
              logEnvelope ^ (2 * levelCount + 3) := by
        gcongr
        exact one_le_pow₀ hlog
  · apply max_le
    · calc
        ambient ≤ ambient ^ 2 := hambientSquare
        _ = 1 * ambient ^ 2 * 1 * 1 := by simp
        _ ≤ terminalCleanupOutputFixedCoefficient levelCount *
              ambient ^ 2 * ratio *
                logEnvelope ^ (2 * levelCount + 3) := by
          gcongr
          exact one_le_pow₀ hlog
    · apply max_le
      · calc
          16 * ((levelCount + 1 : ℕ) : ENNReal) *
                logEnvelope ^ (levelCount + 1) =
              degreeCoefficient * 1 * 1 *
                logEnvelope ^ (levelCount + 1) := by
            simp [degreeCoefficient]
          _ ≤ terminalCleanupOutputFixedCoefficient levelCount *
                ambient ^ 2 * ratio *
                  logEnvelope ^ (2 * levelCount + 3) := by
            gcongr
            exact one_le_pow₀ hambient
      · calc
          ((ratio *
                (ambient * (8 * logEnvelope ^ (levelCount + 2)) *
                  (16 * ((levelCount + 1 : ℕ) : ENNReal) *
                    logEnvelope ^ (levelCount + 1)))) * ambient) =
              ratioCoefficient * ambient ^ 2 * ratio *
                logEnvelope ^ (2 * levelCount + 3) := by
            rw [← hratioPower]
            simp only [ratioCoefficient, degreeCoefficient, pow_two]
            ring
          _ ≤ terminalCleanupOutputFixedCoefficient levelCount *
                ambient ^ 2 * ratio *
                  logEnvelope ^ (2 * levelCount + 3) := by gcongr

/-- The complete fixed coefficient in the cleanup output bound. -/
def terminalCleanupOutputPowerCoefficient
    (degreeCoefficient : ENNReal) (levelCount : ℕ) : ENNReal :=
  terminalCleanupOutputFixedCoefficient levelCount *
    (1 + terminalCleanupNormalizationWeightRatioCoefficient degreeCoefficient)

theorem terminalCleanupOutputPowerCoefficient_ne_top
    {degreeCoefficient : ENNReal}
    (hdegreeZero : degreeCoefficient ≠ 0)
    (hdegreeTop : degreeCoefficient ≠ ⊤)
    (levelCount : ℕ) :
    terminalCleanupOutputPowerCoefficient degreeCoefficient levelCount ≠ ⊤ := by
  unfold terminalCleanupOutputPowerCoefficient
  exact ENNReal.mul_ne_top
    (terminalCleanupOutputFixedCoefficient_ne_top levelCount)
    (ENNReal.add_ne_top.mpr ⟨by norm_num,
      terminalCleanupNormalizationWeightRatioCoefficient_ne_top
        hdegreeZero hdegreeTop⟩)

/-- Runtime-independent source-power bound for the actual cleanup
regularization.  A generic degree envelope with loss `degreeLoss` gives the
explicit total output loss
`3 * technicalLoss + degreeLoss + 6 * epsilon + logLoss`. -/
theorem exists_delta_for_cleanup_output_source_power
    (epsilon degreeLoss logLoss : ℝ)
    (degreeCoefficient : ENNReal) (levelCount : ℕ)
    (hepsilon : 0 < epsilon)
    (hdegreeLoss : 0 ≤ degreeLoss)
    (hlogLoss : 0 < logLoss)
    (hdegreeZero : degreeCoefficient ≠ 0)
    (hdegreeTop : degreeCoefficient ≠ ⊤) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {sigma delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        ∀ technicalLoss : ℝ,
        commonSource.halfOffsetAssembly.technicalLoss = technicalLoss →
        0 < delta → delta ≤ delta₀ →
        ∀ {degreeBound : ENNReal}
          (terminal : commonSource.TerminalGeometry)
          (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
            commonSource terminal degreeBound)
          (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
            cleanup
            (Kakeya.realRpowENN delta (-technicalLoss))
            ((Kakeya.realRpowENN delta (-technicalLoss)) ^ 2)
            (cleanupNormalizationWeight (commonSource := commonSource) cleanup)
            levelCount),
          degreeBound + 1 ≤ degreeCoefficient *
              Kakeya.realRpowENN delta (-degreeLoss) →
          regularization.outputConstant ≤
            Kakeya.realRpowENN delta
              (-(3 * technicalLoss + degreeLoss + 6 * epsilon + logLoss)) := by
  let ratioCoefficient :=
    terminalCleanupNormalizationWeightRatioCoefficient degreeCoefficient
  let coefficient :=
    terminalCleanupOutputPowerCoefficient degreeCoefficient levelCount
  have hboundaryCoefficient :
      0 ≤ 2 * pureWZ2BoundedSourceCardLogConstant := by
    unfold pureWZ2BoundedSourceCardLogConstant
    positivity
  rcases exists_delta_boundary_log_square
      (2 * pureWZ2BoundedSourceCardLogConstant) hboundaryCoefficient with
    ⟨boundaryScale, hboundaryScale, hboundaryScaleOne, hboundary⟩
  have hcoefficientTop : coefficient ≠ ⊤ := by
    exact terminalCleanupOutputPowerCoefficient_ne_top
      hdegreeZero hdegreeTop levelCount
  have hlogExponent : 0 < 2 * (2 * levelCount + 3) := by omega
  rcases exists_delta_log_absorbed_ennreal coefficient hcoefficientTop
      hlogLoss hlogExponent with
    ⟨absorptionScale, habsorptionScale, habsorptionScaleOne, habsorb⟩
  rcases exists_delta_for_halfOffsetLineClassTargetDelta_power_upper
      epsilon hepsilon with
    ⟨targetScale, htargetScale, htargetScaleOne, htarget⟩
  let delta₀ := min boundaryScale (min absorptionScale targetScale)
  refine ⟨delta₀, lt_min hboundaryScale (lt_min habsorptionScale htargetScale),
    (min_le_left _ _).trans hboundaryScaleOne, ?_⟩
  intro logExponent sigma delta commonSource technicalLoss htechnical hdelta hdeltaBound
    degreeBound terminal cleanup regularization hdegree
  have hdeltaBoundary : delta ≤ boundaryScale :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaAbsorption : delta ≤ absorptionScale :=
    hdeltaBound.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaTarget : delta ≤ targetScale :=
    hdeltaBound.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdeltaOne : delta ≤ 1 := hdeltaBoundary.trans hboundaryScaleOne
  have htechnicalLoss : 0 < technicalLoss := by
    exact hepsilon.trans_le <|
      commonSource.epsilon_le_halfOffsetAssembly_technicalLoss.trans_eq htechnical
  have htargetPower := htarget commonSource hdelta hdeltaTarget
  have hlogData := hboundary delta hdelta hdeltaBoundary
  have hlogIdentity : Real.log (1 / delta) = Real.log delta⁻¹ := by
    congr 1
    field_simp [hdelta.ne']
  let logBase : ENNReal := ENNReal.ofReal (Real.log (1 / delta))
  let logEnvelope : ENNReal := logBase ^ 2
  have hlogBaseOne : (1 : ENNReal) ≤ logBase := by
    dsimp only [logBase]
    exact ENNReal.one_le_ofReal.mpr (by
      rw [hlogIdentity]
      linarith [hlogData.1])
  have hlogOne : (1 : ENNReal) ≤ logEnvelope := by
    dsimp only [logEnvelope]
    exact one_le_pow₀ hlogBaseOne
  have hrawAbsorption :
      ENNReal.ofReal
          ((2 * pureWZ2BoundedSourceCardLogConstant) *
            (1 + Real.log delta⁻¹)) ≤ logEnvelope := by
    dsimp only [logEnvelope, logBase]
    calc
      ENNReal.ofReal
            ((2 * pureWZ2BoundedSourceCardLogConstant) *
              (1 + Real.log delta⁻¹)) ≤
          ENNReal.ofReal ((Real.log delta⁻¹) ^ 2) :=
        ENNReal.ofReal_mono hlogData.2
      _ = (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 := by
        rw [hlogIdentity]
        exact ENNReal.ofReal_pow (by linarith [hlogData.1]) 2
  have hlog :
      (Nat.log 2
          (2 * commonSource.halfOffsetAssembly.cfg.family.card) + 1 : ENNReal) ≤
        logEnvelope := by
    calc
      (Nat.log 2
          (2 * commonSource.halfOffsetAssembly.cfg.family.card) + 1 : ENNReal) ≤
          2 * (Nat.log 2
            (2 * commonSource.halfOffsetAssembly.cfg.family.card) + 1 :
              ENNReal) := by
        simpa [two_mul] using
          (self_le_add_left
            (Nat.log 2
              (2 * commonSource.halfOffsetAssembly.cfg.family.card) + 1 :
                ENNReal))
      _ ≤ logEnvelope :=
        pureWZ2_bounded_source_ambient_dyadic_le_logSquare_of_raw
          hdelta hdeltaOne
          commonSource.halfOffsetAssembly.cfg.extremal.nonempty
          commonSource.halfOffsetAssembly.cfg.extremal.cwa_nearby_scales.2.2.1
          commonSource.halfOffsetAssembly.cfg.bounded_base hrawAbsorption
  have hratioRaw :=
    cleanupNormalizationWeight_inv_mul_weightUpper_le_source_power
      (commonSource := commonSource) terminal cleanup htargetPower hdegree
        hdegreeZero hdegreeTop
  have hratioLossNonnegative :
      0 ≤ technicalLoss + degreeLoss + 6 * epsilon := by linarith
  have hratioPowerOne : (1 : ENNReal) ≤
      Kakeya.realRpowENN delta
        (-(technicalLoss + degreeLoss + 6 * epsilon)) := by
    simpa [Kakeya.realRpowENN] using
      realRpowENN_antitone hdelta hdeltaOne
        (show -(technicalLoss + degreeLoss + 6 * epsilon) ≤ 0 by linarith)
  have hratioOne : (1 : ENNReal) ≤
      (1 + ratioCoefficient) *
        Kakeya.realRpowENN delta
          (-(technicalLoss + degreeLoss + 6 * epsilon)) := by
    calc
      (1 : ENNReal) = 1 * 1 := by simp
      _ ≤ (1 + ratioCoefficient) *
          Kakeya.realRpowENN delta
            (-(technicalLoss + degreeLoss + 6 * epsilon)) := by
        gcongr
        exact le_add_right le_rfl
  have hratio :
      (cleanupNormalizationWeight (commonSource := commonSource) cleanup)⁻¹ *
          (terminalCleanupWeightUpperCoefficient *
            Kakeya.realRpowENN terminal.targetDelta 2) ≤
        (1 + ratioCoefficient) *
          Kakeya.realRpowENN delta
            (-(technicalLoss + degreeLoss + 6 * epsilon)) := by
    subst technicalLoss
    exact hratioRaw.trans (by
      dsimp only [ratioCoefficient]
      gcongr
      exact le_add_left le_rfl)
  have hsourceOne : (1 : ENNReal) ≤
      Kakeya.realRpowENN delta (-technicalLoss) := by
    simpa [Kakeya.realRpowENN] using
      realRpowENN_antitone hdelta hdeltaOne
        (show -technicalLoss ≤ 0 by linarith)
  have houtputEnvelope :=
    regularization.outputConstant_le_externalWeightRatioOutputEnvelope
      le_rfl le_rfl hratio hlog hlogOne
  have hmaster :=
    externalWeightRatioOutputEnvelope_le_terminalCleanupMaster
      (Kakeya.realRpowENN delta (-technicalLoss))
      ((1 + ratioCoefficient) *
        Kakeya.realRpowENN delta
          (-(technicalLoss + degreeLoss + 6 * epsilon)))
      logEnvelope levelCount hsourceOne hratioOne hlogOne
  have hlogBaseEnvelope : logBase ≤
      ENNReal.ofReal (1 + Real.log delta⁻¹) := by
    dsimp only [logBase]
    apply ENNReal.ofReal_mono
    rw [hlogIdentity]
    linarith
  have hlogPower : logEnvelope ^ (2 * levelCount + 3) ≤
      (ENNReal.ofReal (1 + Real.log delta⁻¹)) ^
        (2 * (2 * levelCount + 3)) := by
    dsimp only [logEnvelope]
    rw [← pow_mul]
    exact pow_le_pow_left' hlogBaseEnvelope _
  have habsorbed : coefficient *
        (ENNReal.ofReal (1 + Real.log delta⁻¹)) ^
          (2 * (2 * levelCount + 3)) ≤
      Kakeya.realRpowENN delta (-logLoss) :=
    habsorb delta hdelta hdeltaAbsorption
  have hsourceRatio :
      Kakeya.realRpowENN delta (-technicalLoss) ^ 2 *
          Kakeya.realRpowENN delta
            (-(technicalLoss + degreeLoss + 6 * epsilon)) =
        Kakeya.realRpowENN delta
          (-(3 * technicalLoss + degreeLoss + 6 * epsilon)) := by
    rw [pow_two, ← realRpowENN_add hdelta, ← realRpowENN_add hdelta]
    congr 1
    ring
  calc
    regularization.outputConstant ≤
        Kakeya.Assouad.PureWZ2ExternalWeightRegularizationData.pureWZ2ExternalWeightRatioOutputEnvelope
          (Kakeya.realRpowENN delta (-technicalLoss))
          ((Kakeya.realRpowENN delta (-technicalLoss)) ^ 2)
          ((1 + ratioCoefficient) *
            Kakeya.realRpowENN delta
              (-(technicalLoss + degreeLoss + 6 * epsilon)))
          logEnvelope
          levelCount := houtputEnvelope
    _ ≤ terminalCleanupOutputFixedCoefficient levelCount *
          (Kakeya.realRpowENN delta (-technicalLoss)) ^ 2 *
          ((1 + ratioCoefficient) *
            Kakeya.realRpowENN delta
              (-(technicalLoss + degreeLoss + 6 * epsilon))) *
          logEnvelope ^ (2 * levelCount + 3) := by
      exact hmaster
    _ = coefficient *
          Kakeya.realRpowENN delta
            (-(3 * technicalLoss + degreeLoss + 6 * epsilon)) *
          logEnvelope ^ (2 * levelCount + 3) := by
      rw [← hsourceRatio]
      dsimp only [coefficient, terminalCleanupOutputPowerCoefficient]
      ring
    _ ≤ coefficient *
          Kakeya.realRpowENN delta
            (-(3 * technicalLoss + degreeLoss + 6 * epsilon)) *
          (ENNReal.ofReal (1 + Real.log delta⁻¹)) ^
            (2 * (2 * levelCount + 3)) := by gcongr
    _ ≤ Kakeya.realRpowENN delta
          (-(3 * technicalLoss + degreeLoss + 6 * epsilon)) *
        Kakeya.realRpowENN delta (-logLoss) := by
      calc
        coefficient *
              Kakeya.realRpowENN delta
                (-(3 * technicalLoss + degreeLoss + 6 * epsilon)) *
              (ENNReal.ofReal (1 + Real.log delta⁻¹)) ^
                (2 * (2 * levelCount + 3)) =
            Kakeya.realRpowENN delta
                (-(3 * technicalLoss + degreeLoss + 6 * epsilon)) *
              (coefficient *
                (ENNReal.ofReal (1 + Real.log delta⁻¹)) ^
                  (2 * (2 * levelCount + 3))) := by ring
        _ ≤ _ := by gcongr
    _ = Kakeya.realRpowENN delta
          (-(3 * technicalLoss + degreeLoss + 6 * epsilon + logLoss)) := by
      rw [← realRpowENN_add hdelta]
      congr 1
      ring

/-- Actual local-packing specialization.  The six-dimensional packing lemma
costs `30 * epsilon`; the target-area cancellation returns `6 * epsilon`; and
all fixed-depth logarithms spend one arbitrarily small copy of `epsilon`.
Thus the complete nearby-CWA output costs exactly
`3 * technicalLoss + 37 * epsilon`. -/
theorem exists_delta_for_actualLocal_cleanup_output_source_power
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {sigma delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        ∀ technicalLoss : ℝ,
        commonSource.halfOffsetAssembly.technicalLoss = technicalLoss →
        0 < delta → delta ≤ delta₀ →
        ∀ (terminal : commonSource.TerminalGeometry)
          (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
            commonSource terminal
              (actualLocalConflictDegreeBound commonSource terminal))
          (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
            cleanup
            (Kakeya.realRpowENN delta (-technicalLoss))
            ((Kakeya.realRpowENN delta (-technicalLoss)) ^ 2)
            (cleanupNormalizationWeight (commonSource := commonSource) cleanup)
            (pureWZ2FixedScheduleLevelCount epsilon)),
          regularization.outputConstant ≤
            Kakeya.realRpowENN delta
              (-(3 * technicalLoss + 37 * epsilon)) := by
  have hdegreeZero : actualLocalConflictPackingCoefficient + 1 ≠ 0 := by
    positivity
  have hdegreeTop : actualLocalConflictPackingCoefficient + 1 ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, by norm_num⟩
  rcases exists_delta_for_cleanup_output_source_power
      epsilon (30 * epsilon) epsilon
      (actualLocalConflictPackingCoefficient + 1)
      (pureWZ2FixedScheduleLevelCount epsilon)
      hepsilon (by positivity) hepsilon hdegreeZero hdegreeTop with
    ⟨outputScale, houtputScale, houtputScaleOne, houtput⟩
  rcases exists_delta_for_halfOffsetLineClassTargetDelta_power_upper
      epsilon hepsilon with
    ⟨targetScale, htargetScale, htargetScaleOne, htarget⟩
  refine ⟨min outputScale targetScale, lt_min houtputScale htargetScale,
    (min_le_left _ _).trans houtputScaleOne, ?_⟩
  intro logExponent sigma delta commonSource technicalLoss htechnical hdelta hdeltaBound
    terminal cleanup regularization
  have hdeltaOutput : delta ≤ outputScale :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaTarget : delta ≤ targetScale :=
    hdeltaBound.trans (min_le_right _ _)
  have htargetPower := htarget commonSource hdelta hdeltaTarget
  have hdegree := actualLocalConflictDegreeBound_add_one_le_source_power
    commonSource terminal htargetPower
  have hresult := houtput commonSource technicalLoss htechnical hdelta hdeltaOutput terminal
    cleanup regularization (by simpa only [neg_mul] using hdegree)
  convert hresult using 1 <;> ring

end PureWZ2ExternalWeightRegularizationData
end TerminalGeometry
end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
