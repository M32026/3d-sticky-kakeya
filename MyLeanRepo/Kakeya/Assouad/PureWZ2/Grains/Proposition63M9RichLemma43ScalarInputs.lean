import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RobustTransversality
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ExtremalOneScalePlaneMap

/-!
# Proposition 6.3 M9: rich Lemma 4.3 scalar inputs

This module supplies the family-independent density input for the first rich
terminal.  The terminal regularity contributes ten logarithmic powers and
the rich mass retention contributes 61 more.  It deliberately has no import
of the two-call schedule, so the schedule may contain this cutoff without an
import cycle.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

private theorem proposition63_m9_directionLevelCount_le_logEnvelope
    {delta : ℝ} (deltaPos : 0 < delta) (deltaLeOne : delta ≤ 1) :
    (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ≤
      2 * ENNReal.ofReal (1 + Real.log delta⁻¹) := by
  have logNonneg : 0 ≤ Real.log delta⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ deltaPos).mpr deltaLeOne)
  have quotientNonneg :
      0 ≤ Real.log delta⁻¹ / Real.log 2 := by positivity
  have floorLe :
      (Nat.floor (Real.log delta⁻¹ / Real.log 2) : ℝ) ≤
        Real.log delta⁻¹ / Real.log 2 :=
    Nat.floor_le quotientNonneg
  have logTwoHalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have bound : Real.log (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have rewrite : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num)]
      simp
    rw [rewrite] at bound
    linarith
  have quotientLe :
      Real.log delta⁻¹ / Real.log 2 ≤ 2 * Real.log delta⁻¹ := by
    rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    nlinarith
  have realBound :
      (pureWZ2Prop62DirectionLevelCount delta : ℝ) ≤
        2 * (1 + Real.log delta⁻¹) := by
    change
      ((Nat.floor (Real.log (1 / delta) / Real.log 2) + 1 : ℕ) : ℝ) ≤
        2 * (1 + Real.log delta⁻¹)
    rw [show 1 / delta = delta⁻¹ by simp]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have converted := ENNReal.ofReal_mono realBound
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at converted
  norm_num at converted ⊢
  simpa using converted

/-- A family-independent cutoff absorbing the terminal regularity loss and
the 61-log rich-retention loss in the scalar density input.  This cutoff must
be included in the two-call schedule's root cutoff before runtime. -/
structure Proposition63M9RichLemma43DensityCutoffData
    (sigma normalizationLoss densityLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_tiny : delta₀ ≤ 1 / 100000
  density_absorb : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    Kakeya.realRpowENN delta densityLoss *
        (Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 *
          Kakeya.realRpowENN delta (sigma - normalizationLoss)) ≤
      wz2PaperPureRefinementFraction delta 61 *
        Kakeya.realRpowENN delta (normalizationLoss + 2)

/-- Freeze the density cutoff before the runtime family is known.  The gap is
exactly the power left after paying the target density exponent, the source
volume exponent, and both normalization exponents. -/
theorem proposition63_m9_rich_lemma43_density_cutoff
    (sigma normalizationLoss densityLoss : ℝ)
    (hgap : 0 < densityLoss + sigma - 2 * normalizationLoss - 2) :
    Nonempty (Proposition63M9RichLemma43DensityCutoffData
      sigma normalizationLoss densityLoss) := by
  let gap : ℝ := densityLoss + sigma - 2 * normalizationLoss - 2
  rcases exists_delta_C_pow_log_absorbed_ennreal
      (1 : ENNReal) (by norm_num) proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg (B := gap)
      (by simpa only [gap] using hgap)
      (show 0 < (71 : ℕ) by norm_num) with
    ⟨logCutoff, logCutoffPos, logCutoffOne, logAbsorb⟩
  let delta₀ : ℝ := min logCutoff (1 / 100000)
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min logCutoffPos (by norm_num)
    delta₀_le_one := (min_le_left _ _).trans logCutoffOne
    delta₀_le_tiny := min_le_right _ _
    density_absorb := ?_ }⟩
  intro delta deltaPos deltaLe
  have deltaLeLog : delta ≤ logCutoff :=
    deltaLe.trans (min_le_left _ _)
  have deltaSmall : delta ≤ 1 / 100000 :=
    deltaLe.trans (min_le_right _ _)
  have deltaOne : delta ≤ 1 := deltaLeLog.trans logCutoffOne
  have deltaLtOne : delta < 1 := deltaSmall.trans_lt (by norm_num)
  let envelope := proposition63OneScaleLogEnvelope delta
  let logTerm : ENNReal := ENNReal.ofReal (Real.log (1 / delta))
  let fraction := wz2PaperPureRefinementFraction delta 61
  have levelLe :
      Prop62PaperAudit.V4.logarithmicLoss delta ≤ envelope := by
    have raw := proposition63_m9_directionLevelCount_le_logEnvelope
      deltaPos deltaOne
    dsimp only [Prop62PaperAudit.V4.logarithmicLoss, envelope,
      proposition63OneScaleLogEnvelope]
    exact raw.trans <| by
      have coefficientTwo :
          2 ≤ proposition63OneScaleLogCoefficient := le_max_left _ _
      rw [ENNReal.ofReal_mul proposition63OneScaleLogCoefficient_nonneg]
      have coefficientTwoENN :
          (2 : ENNReal) ≤
            ENNReal.ofReal proposition63OneScaleLogCoefficient := by
        rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num]
        exact ENNReal.ofReal_mono coefficientTwo
      simpa [mul_comm] using
        mul_le_mul_right coefficientTwoENN
          (ENNReal.ofReal (1 + Real.log delta⁻¹))
  have logTermLe : logTerm ≤ envelope := by
    dsimp only [logTerm, envelope, proposition63OneScaleLogEnvelope]
    apply ENNReal.ofReal_mono
    have logNonnegative : 0 ≤ Real.log delta⁻¹ :=
      Real.log_nonneg ((one_le_inv₀ deltaPos).mpr deltaOne)
    have coefficientOne : 1 ≤ proposition63OneScaleLogCoefficient :=
      (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
    rw [show 1 / delta = delta⁻¹ by simp]
    nlinarith [mul_nonneg (sub_nonneg.mpr coefficientOne)
      (show 0 ≤ 1 + Real.log delta⁻¹ by linarith)]
  have envelopeAbsorb : envelope ^ 71 ≤
      Kakeya.realRpowENN delta (-gap) := by
    simpa only [envelope, proposition63OneScaleLogEnvelope, one_mul] using
      logAbsorb delta deltaPos deltaLeLog
  have fractionBounds :=
    pure_refinement_fraction_pos_ne_top deltaPos deltaLtOne 61
  have fractionInverse : fraction⁻¹ = logTerm ^ 61 := by
    dsimp only [fraction, logTerm, wz2PaperPureRefinementFraction]
    rw [ENNReal.inv_pow]
    simp
  have scaled : fraction⁻¹ *
        (Kakeya.realRpowENN delta densityLoss *
          (Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 *
            Kakeya.realRpowENN delta (sigma - normalizationLoss))) ≤
      Kakeya.realRpowENN delta (normalizationLoss + 2) := by
    rw [fractionInverse]
    have powerCombined :
        Kakeya.realRpowENN delta densityLoss *
            Kakeya.realRpowENN delta (sigma - normalizationLoss) =
          Kakeya.realRpowENN delta
            (densityLoss + sigma - normalizationLoss) := by
      rw [← Kakeya.Assouad.realRpowENN_add deltaPos]
      congr 1
      ring
    calc
      logTerm ^ 61 *
          (Kakeya.realRpowENN delta densityLoss *
            (Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 *
              Kakeya.realRpowENN delta (sigma - normalizationLoss))) =
          (logTerm ^ 61 *
            Prop62PaperAudit.V4.logarithmicLoss delta ^ 10) *
            Kakeya.realRpowENN delta
              (densityLoss + sigma - normalizationLoss) := by
        rw [← powerCombined]
        ring
      _ ≤ envelope ^ 71 * Kakeya.realRpowENN delta
          (densityLoss + sigma - normalizationLoss) := by
        gcongr
        calc
          logTerm ^ 61 *
                Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 ≤
              envelope ^ 61 * envelope ^ 10 := by gcongr
          _ = envelope ^ 71 := by rw [← pow_add]
      _ ≤ Kakeya.realRpowENN delta (-gap) *
          Kakeya.realRpowENN delta
            (densityLoss + sigma - normalizationLoss) := by gcongr
      _ = Kakeya.realRpowENN delta (normalizationLoss + 2) := by
        rw [← Kakeya.Assouad.realRpowENN_add deltaPos]
        congr 1
        dsimp only [gap]
        ring
  calc
    Kakeya.realRpowENN delta densityLoss *
          (Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 *
            Kakeya.realRpowENN delta (sigma - normalizationLoss)) =
        (fraction * fraction⁻¹) *
          (Kakeya.realRpowENN delta densityLoss *
            (Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 *
              Kakeya.realRpowENN delta (sigma - normalizationLoss))) := by
      rw [ENNReal.mul_inv_cancel fractionBounds.1.ne' fractionBounds.2]
      simp
    _ = fraction *
        (fraction⁻¹ *
          (Kakeya.realRpowENN delta densityLoss *
            (Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 *
              Kakeya.realRpowENN delta (sigma - normalizationLoss)))) := by
      ring
    _ ≤ fraction * Kakeya.realRpowENN delta (normalizationLoss + 2) := by
      gcongr
    _ = wz2PaperPureRefinementFraction delta 61 *
        Kakeya.realRpowENN delta (normalizationLoss + 2) := rfl

/-- The density cutoff turns the terminal regularity bound into the exact
scalar inequality consumed by the rich Lemma 4.3 preparation. -/
theorem Proposition63M9RichLemma43DensityCutoffData.density_scalar
    {delta sigma outputLoss sourceLoss normalizationLoss densityLoss : ℝ}
    (cutoff : Proposition63M9RichLemma43DensityCutoffData
      sigma normalizationLoss densityLoss)
    (hdelta : 0 < delta) (hdeltaCutoff : delta ≤ cutoff.delta₀)
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho) :
    Kakeya.realRpowENN delta densityLoss *
        ((rich.terminal.regularity : ENNReal) *
          Kakeya.realRpowENN delta (sigma - normalizationLoss)) ≤
      wz2PaperPureRefinementFraction delta 61 *
        Kakeya.realRpowENN delta (normalizationLoss + 2) := by
  calc
    Kakeya.realRpowENN delta densityLoss *
          ((rich.terminal.regularity : ENNReal) *
            Kakeya.realRpowENN delta (sigma - normalizationLoss)) ≤
        Kakeya.realRpowENN delta densityLoss *
          (Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 *
            Kakeya.realRpowENN delta (sigma - normalizationLoss)) := by
      gcongr
      exact rich.terminal_regularity_bound
    _ ≤ wz2PaperPureRefinementFraction delta 61 *
        Kakeya.realRpowENN delta (normalizationLoss + 2) :=
      cutoff.density_absorb hdelta hdeltaCutoff

/-- The two scalar receipts required by rich Lemma 4.3 preparation. -/
structure Proposition63M9RichLemma43ScalarInputs
    {delta sigma outputLoss sourceLoss normalizationLoss densityLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho) where
  degree : (96 : ENNReal) * stickyCoarseCloseCount ≤
    (rich.terminal.fineDegreeFloor : ENNReal)
  density : Kakeya.realRpowENN delta densityLoss *
      ((rich.terminal.regularity : ENNReal) *
        Kakeya.realRpowENN delta (sigma - normalizationLoss)) ≤
    wz2PaperPureRefinementFraction delta 61 *
      Kakeya.realRpowENN delta (normalizationLoss + 2)

end Kakeya.Assouad.PureWZ2

end
