import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalCWALogRetentionBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalCWAAffineFactorBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalCWARadiusRatioBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalCWAScaleWindowBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalScalarBudget

/-!
# Concrete scalar closure for the direct half-offset terminal CWA

This file combines the literal factors in bodyConstant.  The selected
weight inverse cancels the matching retention factor before any power
estimate.  For cleanup-output loss q = 3 * technicalLoss + 37 * epsilon,
the three output-constant occurrences, affine cube, radius determinant, and
two fixed-depth logarithmic factors cost

3q + 3 epsilon + 3 epsilon + epsilon
  = 9 technicalLoss + 118 epsilon.

All schedule depths and coefficients are fixed before the runtime scale.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2DirectCommonYSourceAssembly
namespace TerminalGeometry
namespace PureWZ2ExternalWeightRegularizationData
namespace DirectHalfOffsetTerminalCWAScheduleData

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}

/-- Fixed coefficient for the literal body after the actual line factor is
specialized. -/
def actualBodyCoefficient : ENNReal :=
  packetFactorCubicFiniteConstant *
    radiusRatioDeterminantCoefficient directHalfOffsetTerminalLineFactor

/-- One coefficient dominating the canonical scale window, cover, and body. -/
def actualRequestedCWACoefficient : ENNReal :=
  max
    (directHalfOffsetTerminalScaleWindowCoefficient
      directHalfOffsetTerminalLineFactor)
    (max 1 actualBodyCoefficient)

theorem actualBodyCoefficient_ne_top : actualBodyCoefficient ≠ ⊤ := by
  exact ENNReal.mul_ne_top packetFactorCubicFiniteConstant_ne_top <|
    ENNReal.ofReal_ne_top

theorem actualRequestedCWACoefficient_ne_top :
    actualRequestedCWACoefficient ≠ ⊤ := by
  unfold actualRequestedCWACoefficient
  rw [← lt_top_iff_ne_top]
  apply max_lt
  · exact lt_top_iff_ne_top.mpr <|
      directHalfOffsetTerminalScaleWindowCoefficient_ne_top _
  · apply max_lt
    · exact ENNReal.one_lt_top
    · exact lt_top_iff_ne_top.mpr actualBodyCoefficient_ne_top

/-- Literal multiplication of the four proved receipts for bodyConstant.
No residual packet envelope is assumed. -/
theorem bodyConstant_le_source_power
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (scheduleData : DirectHalfOffsetTerminalCWAScheduleData
      (sourceScheduleConstant := sourceScheduleConstant)
      (parentLevelCount := parentLevelCount) regularization)
    (coordinate : Fin scheduleData.sourceSchedule.scaleCount)
    (hlineFactor : scheduleData.lineFactor =
      directHalfOffsetTerminalLineFactor)
    {outputConstantLoss logLoss : ℝ}
    (houtput : regularization.outputConstant ≤
      Kakeya.realRpowENN delta (-outputConstantLoss))
    (hlog :
      max (scheduleData.coverConstant coordinate)
          (regularization.selectedWeightLevel⁻¹ *
            scheduleData.retentionConstant) ≤
        Kakeya.realRpowENN delta (-logLoss)) :
    scheduleData.bodyConstant coordinate ≤
      actualBodyCoefficient *
        Kakeya.realRpowENN delta
          (-(3 * outputConstantLoss + 6 * epsilon + 2 * logLoss)) := by
  have hdelta : 0 < delta :=
    commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have haffine := scheduleData.packetFactor_cubic_le_source_power coordinate
  have hradius := scheduleData.radiusRatioDeterminantEnvelope_le_sourcePower
    coordinate
  have hcover : scheduleData.coverConstant coordinate ≤
      Kakeya.realRpowENN delta (-logLoss) :=
    (le_max_left _ _).trans hlog
  have hretention :
      regularization.selectedWeightLevel⁻¹ *
          scheduleData.retentionConstant ≤
        Kakeya.realRpowENN delta (-logLoss) :=
    (le_max_right _ _).trans hlog
  have hinner :
      (regularization.selectedWeightLevel⁻¹ *
          (regularization.outputConstant * scheduleData.retentionConstant *
            scheduleData.coverConstant coordinate)) *
          regularization.outputConstant ≤
        Kakeya.realRpowENN delta (-logLoss) *
          Kakeya.realRpowENN delta (-logLoss) *
          (Kakeya.realRpowENN delta (-outputConstantLoss) *
            Kakeya.realRpowENN delta (-outputConstantLoss)) := by
    calc
      (regularization.selectedWeightLevel⁻¹ *
          (regularization.outputConstant * scheduleData.retentionConstant *
            scheduleData.coverConstant coordinate)) *
          regularization.outputConstant =
        (regularization.selectedWeightLevel⁻¹ *
            scheduleData.retentionConstant) *
          scheduleData.coverConstant coordinate *
          (regularization.outputConstant *
            regularization.outputConstant) := by ring
      _ ≤ Kakeya.realRpowENN delta (-logLoss) *
          Kakeya.realRpowENN delta (-logLoss) *
          (Kakeya.realRpowENN delta (-outputConstantLoss) *
            Kakeya.realRpowENN delta (-outputConstantLoss)) := by
        gcongr
  unfold bodyConstant
  calc
    ENNReal.ofReal (27 * (2 * scheduleData.packetFactor - 1) ^ 3) *
          ((432 : ENNReal) *
            Kakeya.realRpowENN
              (scheduleData.quotientSchedule.callerRho coordinate) 2 *
            ENNReal.ofReal
              (1 + 2 * scheduleData.quotientSchedule.callerRho coordinate) *
            ENNReal.ofReal
              (1 /
                (commonSource.halfOffsetAssembly.horizontalSource.m *
                  pureWZ2DirectHalfOffsetTerminalLambda ^ 2 *
                  scheduleData.representativeSchedule.sourceRho coordinate ^ 2))) *
          ((regularization.selectedWeightLevel⁻¹ *
            (regularization.outputConstant * scheduleData.retentionConstant *
              scheduleData.coverConstant coordinate)) *
            regularization.outputConstant) ≤
        (packetFactorCubicFiniteConstant *
          Kakeya.realRpowENN delta (-3 * epsilon)) *
        (radiusRatioDeterminantCoefficient scheduleData.lineFactor *
          regularization.outputConstant *
          Kakeya.realRpowENN delta (-3 * epsilon)) *
        (Kakeya.realRpowENN delta (-logLoss) *
          Kakeya.realRpowENN delta (-logLoss) *
          (Kakeya.realRpowENN delta (-outputConstantLoss) *
            Kakeya.realRpowENN delta (-outputConstantLoss))) := by
      gcongr
    _ ≤ (packetFactorCubicFiniteConstant *
          Kakeya.realRpowENN delta (-3 * epsilon)) *
        (radiusRatioDeterminantCoefficient scheduleData.lineFactor *
          Kakeya.realRpowENN delta (-outputConstantLoss) *
          Kakeya.realRpowENN delta (-3 * epsilon)) *
        (Kakeya.realRpowENN delta (-logLoss) *
          Kakeya.realRpowENN delta (-logLoss) *
          (Kakeya.realRpowENN delta (-outputConstantLoss) *
            Kakeya.realRpowENN delta (-outputConstantLoss))) := by
      gcongr
    _ = actualBodyCoefficient *
        Kakeya.realRpowENN delta
          (-(3 * outputConstantLoss + 6 * epsilon + 2 * logLoss)) := by
      rw [hlineFactor]
      unfold actualBodyCoefficient
      have hpowerIdentity :
          Kakeya.realRpowENN delta (-3 * epsilon) *
              Kakeya.realRpowENN delta (-3 * epsilon) *
              Kakeya.realRpowENN delta (-outputConstantLoss) *
              (Kakeya.realRpowENN delta (-logLoss) *
                Kakeya.realRpowENN delta (-logLoss) *
                (Kakeya.realRpowENN delta (-outputConstantLoss) *
                  Kakeya.realRpowENN delta (-outputConstantLoss))) =
            Kakeya.realRpowENN delta
              (-(3 * outputConstantLoss + 6 * epsilon + 2 * logLoss)) := by
        repeat' rw [← realRpowENN_add hdelta]
        congr 1
        ring
      rw [← hpowerIdentity]
      ring

/-- At one sufficiently small source scale, the actual schedule's cover,
body, and canonical scale-window constants all fit one source-power envelope.
The loss is exactly 9 * technicalLoss + 118 * epsilon. -/
theorem exists_delta_for_actual_requested_cwa_source_power
    (epsilon : ℝ) (parentLevelCount : ℕ)
    (hepsilon : 0 < epsilon) :
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
            (pureWZ2FixedScheduleLevelCount epsilon))
          (scheduleData : DirectHalfOffsetTerminalCWAScheduleData
            (sourceScheduleConstant := regularization.outputConstant ^ 2)
            (parentLevelCount := parentLevelCount) regularization),
          scheduleData.lineFactor = directHalfOffsetTerminalLineFactor →
          horizontalNormalizedQuotientScaleWindowConstant
              scheduleData.lineFactor (regularization.outputConstant ^ 2) ≤
              actualRequestedCWACoefficient *
                Kakeya.realRpowENN delta
                  (-(9 * technicalLoss + 118 * epsilon)) ∧
            ∀ coordinate,
              max (scheduleData.coverConstant coordinate)
                  (scheduleData.bodyConstant coordinate) ≤
                actualRequestedCWACoefficient *
                  Kakeya.realRpowENN delta
                    (-(9 * technicalLoss + 118 * epsilon)) := by
  rcases exists_delta_for_actualLocal_cleanup_output_source_power
      epsilon hepsilon with
    ⟨outputScale, houtputScale, houtputScaleOne, houtput⟩
  rcases exists_delta_for_cover_and_cancelledRetention_source_power
      parentLevelCount (q := epsilon / 2) (by positivity) with
    ⟨logScale, hlogScale, hlogScaleOne, hlog⟩
  refine ⟨min outputScale logScale, lt_min houtputScale hlogScale,
    (min_le_left _ _).trans houtputScaleOne, ?_⟩
  intro logExponent sigma delta commonSource technicalLoss htechnical
    hdelta hdeltaBound
    terminal cleanup regularization scheduleData hlineFactor
  have hdeltaOutput : delta ≤ outputScale :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaLog : delta ≤ logScale :=
    hdeltaBound.trans (min_le_right _ _)
  have hdeltaOne : delta ≤ 1 := hdeltaOutput.trans houtputScaleOne
  let q : ℝ := 3 * technicalLoss + 37 * epsilon
  let totalLoss : ℝ := 9 * technicalLoss + 118 * epsilon
  have htechnicalPos : 0 < technicalLoss := by
    rw [← htechnical]
    exact hepsilon.trans_le
      commonSource.epsilon_le_halfOffsetAssembly_technicalLoss
  have hq : 0 ≤ q := by dsimp only [q]; linarith
  have houtputBound : regularization.outputConstant ≤
      Kakeya.realRpowENN delta (-q) := by
    dsimp only [q]
    exact houtput commonSource technicalLoss htechnical hdelta hdeltaOutput terminal cleanup
      regularization
  have hscale := canonicalScaleWindow_le_coefficient_sourcePower
    (lineFactor := scheduleData.lineFactor) hdelta hdeltaOne hq houtputBound
  have hscaleLoss : 2 * q ≤ totalLoss := by
    dsimp only [q, totalLoss]
    linarith
  have hscalePower : Kakeya.realRpowENN delta (-(2 * q)) ≤
      Kakeya.realRpowENN delta (-totalLoss) :=
    realRpowENN_antitone hdelta hdeltaOne (by linarith)
  constructor
  · calc
      horizontalNormalizedQuotientScaleWindowConstant
            scheduleData.lineFactor (regularization.outputConstant ^ 2) ≤
          directHalfOffsetTerminalScaleWindowCoefficient scheduleData.lineFactor *
            Kakeya.realRpowENN delta (-(2 * q)) := hscale
      _ ≤ directHalfOffsetTerminalScaleWindowCoefficient scheduleData.lineFactor *
            Kakeya.realRpowENN delta (-totalLoss) := by gcongr
      _ ≤ actualRequestedCWACoefficient *
            Kakeya.realRpowENN delta (-totalLoss) := by
        rw [hlineFactor]
        gcongr
        exact le_max_left _ _
      _ = _ := by rfl
  · intro coordinate
    have hlogBound := hlog scheduleData hdelta hdeltaLog coordinate
    have hbody := scheduleData.bodyConstant_le_source_power coordinate
      hlineFactor houtputBound hlogBound
    have hbodyLoss : 3 * q + 6 * epsilon + 2 * (epsilon / 2) =
        totalLoss := by
      dsimp only [q, totalLoss]
      ring
    have hbody' : scheduleData.bodyConstant coordinate ≤
        actualBodyCoefficient * Kakeya.realRpowENN delta (-totalLoss) := by
      simpa only [hbodyLoss] using hbody
    have hcoverLoss : epsilon / 2 ≤ totalLoss := by
      dsimp only [totalLoss]
      linarith
    have hcoverPower : Kakeya.realRpowENN delta (-(epsilon / 2)) ≤
        Kakeya.realRpowENN delta (-totalLoss) :=
      realRpowENN_antitone hdelta hdeltaOne (by linarith)
    apply max_le
    · calc
        scheduleData.coverConstant coordinate ≤
            Kakeya.realRpowENN delta (-(epsilon / 2)) :=
          (le_max_left _ _).trans hlogBound
        _ ≤ Kakeya.realRpowENN delta (-totalLoss) := hcoverPower
        _ ≤ actualRequestedCWACoefficient *
            Kakeya.realRpowENN delta (-totalLoss) := by
          exact le_mul_of_one_le_left (by positivity) <|
            (le_max_left (1 : ENNReal) actualBodyCoefficient).trans <|
              le_max_right _ _
    · exact hbody'.trans <| by
        gcongr
        exact (le_max_right (1 : ENNReal) actualBodyCoefficient).trans <|
          le_max_right _ _

/-- Final source-to-target conversion for both scalar premises of
toRequestedCWAData. -/
theorem exists_delta_for_actual_requested_cwa_budgets
    (epsilon nearbyLoss : ℝ) (parentLevelCount : ℕ)
    (hepsilon : 0 < epsilon)
    (hnearbyLoss : 0 ≤ nearbyLoss)
    (hgap : 136 * epsilon <
      (1 - 2 * epsilon) * nearbyLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {sigma delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        ∀ technicalLoss : ℝ,
        commonSource.halfOffsetAssembly.technicalLoss = technicalLoss →
        technicalLoss ≤ 2 * epsilon →
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
            (pureWZ2FixedScheduleLevelCount epsilon))
          (scheduleData : DirectHalfOffsetTerminalCWAScheduleData
            (sourceScheduleConstant := regularization.outputConstant ^ 2)
            (parentLevelCount := parentLevelCount) regularization),
          scheduleData.lineFactor = directHalfOffsetTerminalLineFactor →
          horizontalNormalizedQuotientScaleWindowConstant
              scheduleData.lineFactor (regularization.outputConstant ^ 2) ≤
              Kakeya.realRpowENN terminal.targetDelta (-nearbyLoss) ∧
            ∀ coordinate,
              max (scheduleData.coverConstant coordinate)
                  (scheduleData.bodyConstant coordinate) ≤
                Kakeya.realRpowENN terminal.targetDelta (-nearbyLoss) := by
  let totalLoss : ℝ := 136 * epsilon
  rcases exists_delta_for_actual_requested_cwa_source_power
      epsilon parentLevelCount hepsilon with
    ⟨sourceScale, hsourceScale, hsourceScaleOne, hsource⟩
  rcases exists_delta_for_halfOffsetLineClass_constant_source_negative_le_target_negative
      epsilon totalLoss nearbyLoss actualRequestedCWACoefficient
      actualRequestedCWACoefficient_ne_top hepsilon hnearbyLoss
      (by
        dsimp only [totalLoss]
        nlinarith) with
    ⟨targetScale, htargetScale, htargetScaleOne, htarget⟩
  refine ⟨min sourceScale targetScale, lt_min hsourceScale htargetScale,
    (min_le_left _ _).trans hsourceScaleOne, ?_⟩
  intro logExponent sigma delta commonSource technicalLoss htechnical htechnicalUpper
    hdelta hdeltaBound
    terminal cleanup regularization scheduleData hlineFactor
  have hsourceBound := hsource commonSource technicalLoss htechnical hdelta
    (hdeltaBound.trans (min_le_left _ _)) terminal cleanup regularization
      scheduleData hlineFactor
  have hactualPower : Kakeya.realRpowENN delta
        (-(9 * technicalLoss + 118 * epsilon)) ≤
      Kakeya.realRpowENN delta (-totalLoss) :=
    realRpowENN_antitone hdelta
      ((hdeltaBound.trans (min_le_left _ _)).trans hsourceScaleOne) (by
        dsimp only [totalLoss]
        nlinarith)
  have hsourceFixed :
      horizontalNormalizedQuotientScaleWindowConstant
            scheduleData.lineFactor (regularization.outputConstant ^ 2) ≤
          actualRequestedCWACoefficient *
            Kakeya.realRpowENN delta (-totalLoss) ∧
        ∀ coordinate,
          max (scheduleData.coverConstant coordinate)
              (scheduleData.bodyConstant coordinate) ≤
            actualRequestedCWACoefficient *
              Kakeya.realRpowENN delta (-totalLoss) := by
    constructor
    · exact hsourceBound.1.trans (mul_le_mul_left' hactualPower _)
    · intro coordinate
      exact (hsourceBound.2 coordinate).trans
        (mul_le_mul_left' hactualPower _)
  have htargetBound := htarget commonSource hdelta
    (hdeltaBound.trans (min_le_right _ _))
  constructor
  · exact hsourceFixed.1.trans htargetBound
  · intro coordinate
    exact (hsourceFixed.2 coordinate).trans htargetBound

end DirectHalfOffsetTerminalCWAScheduleData
end PureWZ2ExternalWeightRegularizationData
end TerminalGeometry
end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
