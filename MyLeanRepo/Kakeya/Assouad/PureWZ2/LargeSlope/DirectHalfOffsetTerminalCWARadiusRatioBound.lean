import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalCWASchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalGeometry

/-!
# Radius-ratio determinant bound for the direct half-offset terminal CWA

The square of the quotient caller radius is paired with the inverse square
of its source radius before any source-power accounting.  The remaining
losses are one copy of `delta ^ (-epsilon)` from the raw target/source ratio
and one copy from the inverse slope scale.  Thus the complete determinant
envelope, excluding the packet factor, costs exactly three epsilon powers.
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

/-- The coordinate-independent coefficient for the caller/source radius
ratio and the literal total-map inverse determinant. -/
def radiusRatioDeterminantCoefficient (lineFactor : ℝ) : ENNReal :=
  ENNReal.ofReal
    (432 *
      (1 + 2 * (2400000 * lineFactor + 2)) *
      (2400000 * lineFactor +
        2560000 * pureWZ2DirectHorizontalScale) ^ 2 *
      50)

private theorem radiusRatioDeterminantCoefficient_nonneg
    {lineFactor : ℝ} (hlineFactor : 0 ≤ lineFactor) :
    0 ≤ (432 : ℝ) *
      (1 + 2 * (2400000 * lineFactor + 2)) *
      (2400000 * lineFactor +
        2560000 * pureWZ2DirectHorizontalScale) ^ 2 *
      50 := by
  positivity [pureWZ2DirectHorizontalScale_pos]

/-- Every source-scale witness in the finite schedule stays above the
original source radius `delta`. -/
theorem sourceDelta_le_sourceRho
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
    (coordinate : Fin scheduleData.sourceSchedule.scaleCount) :
    delta ≤ scheduleData.representativeSchedule.sourceRho coordinate := by
  calc
    delta ≤ (scheduleData.sourceSchedule.requested coordinate).1 :=
      (scheduleData.sourceSchedule.requested coordinate).2.1
    _ ≤ (scheduleData.sourceSchedule.witness coordinate).rho :=
      (scheduleData.sourceSchedule.witness coordinate).requested_le
    _ = scheduleData.representativeSchedule.sourceRho coordinate :=
      (scheduleData.sourceRho_eq coordinate).symm

private theorem radius_ratio_determinant_real_bound
    {targetDelta lineFactor sourceRho sourceUpper m : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hepsilon : 0 ≤ epsilon)
    (hlineFactor : 1 ≤ lineFactor)
    (htargetDelta : 0 < targetDelta)
    (htargetOne : targetDelta ≤ 1)
    (htarget : targetDelta <
      (1280000 * pureWZ2DirectHorizontalScale) *
        Real.rpow delta (1 - epsilon))
    (hsourceLower : delta ≤ sourceRho)
    (hsourceUpperOne : 1 ≤ sourceUpper)
    (hsourceUpper : sourceRho ≤ sourceUpper)
    (hmLower : Real.rpow delta epsilon / 50 ≤ m) :
    let callerRho := horizontalNormalizedQuotientCallerScale
      targetDelta lineFactor sourceRho
    432 * callerRho ^ 2 * (1 + 2 * callerRho) *
        (1 / (m * pureWZ2DirectHalfOffsetTerminalLambda ^ 2 *
          sourceRho ^ 2)) ≤
      (432 *
        (1 + 2 * (2400000 * lineFactor + 2)) *
        (2400000 * lineFactor +
          2560000 * pureWZ2DirectHorizontalScale) ^ 2 *
        50) * sourceUpper * Real.rpow delta (-3 * epsilon) := by
  dsimp only
  let callerRho := horizontalNormalizedQuotientCallerScale
    targetDelta lineFactor sourceRho
  let targetCoefficient : ℝ := 1280000 * pureWZ2DirectHorizontalScale
  let ratioCoefficient : ℝ :=
    2400000 * lineFactor + 2 * targetCoefficient
  let callerCoefficient : ℝ := 2400000 * lineFactor + 2
  have hlineFactorNonneg : 0 ≤ lineFactor := le_trans (by norm_num) hlineFactor
  have hsourcePos : 0 < sourceRho := hdelta.trans_le hsourceLower
  have hmPos : 0 < m := by
    have hpowerPos : 0 < Real.rpow delta epsilon :=
      Real.rpow_pos_of_pos hdelta _
    exact (div_pos hpowerPos (by norm_num)).trans_le hmLower
  have hlambdaPos : 0 < pureWZ2DirectHalfOffsetTerminalLambda :=
    pureWZ2DirectHalfOffsetTerminalLambda_pos
  have hcallerNonneg : 0 ≤ callerRho := by
    dsimp only [callerRho]
    unfold horizontalNormalizedQuotientCallerScale
      horizontalNormalizedRepresentativeLineBound
    positivity
  have hcallerUpper : callerRho ≤ callerCoefficient * sourceUpper := by
    have hsourceTerm :
        2400000 * lineFactor * sourceRho ≤
          2400000 * lineFactor * sourceUpper := by
      gcongr
    have htargetTerm : 2 * targetDelta ≤ 2 * sourceUpper := by
      calc
        2 * targetDelta ≤ 2 * 1 := by gcongr
        _ ≤ 2 * sourceUpper := by gcongr
    dsimp only [callerRho, callerCoefficient]
    unfold horizontalNormalizedQuotientCallerScale
      horizontalNormalizedRepresentativeLineBound
    calc
      4 * (lineFactor * (600000 * sourceRho)) + 2 * targetDelta =
          2400000 * lineFactor * sourceRho + 2 * targetDelta := by ring
      _ ≤ 2400000 * lineFactor * sourceUpper + 2 * sourceUpper :=
        add_le_add hsourceTerm htargetTerm
      _ = (2400000 * lineFactor + 2) * sourceUpper := by ring
  have hpowerOne : 1 ≤ Real.rpow delta (-epsilon) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdeltaOne (by linarith)
  have htargetRatio : targetDelta / sourceRho ≤
      targetCoefficient * Real.rpow delta (-epsilon) := by
    apply (div_le_iff₀ hsourcePos).2
    calc
      targetDelta ≤ targetCoefficient * Real.rpow delta (1 - epsilon) :=
        htarget.le
      _ = delta *
          (targetCoefficient * Real.rpow delta (-epsilon)) := by
        have hpower : Real.rpow delta (1 - epsilon) =
            delta * Real.rpow delta (-epsilon) := by
          calc
            Real.rpow delta (1 - epsilon) =
                Real.rpow delta (1 + (-epsilon)) := by congr 1
            _ = Real.rpow delta 1 * Real.rpow delta (-epsilon) :=
              Real.rpow_add hdelta 1 (-epsilon)
            _ = delta * Real.rpow delta (-epsilon) := by
              rw [show Real.rpow delta 1 = delta by
                exact Real.rpow_one delta]
        rw [hpower]
        ring
      _ ≤ sourceRho *
          (targetCoefficient * Real.rpow delta (-epsilon)) := by
        gcongr
        positivity [pureWZ2DirectHorizontalScale_pos]
      _ = targetCoefficient * Real.rpow delta (-epsilon) * sourceRho := by ring
  have hcallerRatio : callerRho / sourceRho ≤
      ratioCoefficient * Real.rpow delta (-epsilon) := by
    have hfixed : 2400000 * lineFactor ≤
        (2400000 * lineFactor) * Real.rpow delta (-epsilon) := by
      exact le_mul_of_one_le_right
        (mul_nonneg (by norm_num) hlineFactorNonneg) hpowerOne
    have hformula : callerRho / sourceRho =
        2400000 * lineFactor + 2 * (targetDelta / sourceRho) := by
      dsimp only [callerRho]
      unfold horizontalNormalizedQuotientCallerScale
        horizontalNormalizedRepresentativeLineBound
      field_simp [hsourcePos.ne']
      ring
    rw [hformula]
    calc
      2400000 * lineFactor + 2 * (targetDelta / sourceRho) ≤
          2400000 * lineFactor +
            2 * (targetCoefficient * Real.rpow delta (-epsilon)) := by
        gcongr
      _ ≤ (2400000 * lineFactor) * Real.rpow delta (-epsilon) +
            2 * (targetCoefficient * Real.rpow delta (-epsilon)) := by
        exact add_le_add hfixed le_rfl
      _ = ratioCoefficient * Real.rpow delta (-epsilon) := by
        dsimp only [ratioCoefficient]
        ring
  have hratioNonneg : 0 ≤ callerRho / sourceRho :=
    div_nonneg hcallerNonneg hsourcePos.le
  have hratioCoefficientNonneg : 0 ≤ ratioCoefficient := by
    dsimp only [ratioCoefficient, targetCoefficient]
    positivity [pureWZ2DirectHorizontalScale_pos]
  have hratioSquare : (callerRho / sourceRho) ^ 2 ≤
      ratioCoefficient ^ 2 * Real.rpow delta (-epsilon) ^ 2 := by
    calc
      (callerRho / sourceRho) ^ 2 ≤
          (ratioCoefficient * Real.rpow delta (-epsilon)) ^ 2 := by
        gcongr
      _ = ratioCoefficient ^ 2 * Real.rpow delta (-epsilon) ^ 2 := by ring
  have hinverseSlope :
      1 / (m * pureWZ2DirectHalfOffsetTerminalLambda ^ 2) ≤
        50 * Real.rpow delta (-epsilon) := by
    have hlambdaSquare : 1 ≤ pureWZ2DirectHalfOffsetTerminalLambda ^ 2 := by
      nlinarith [pureWZ2DirectHalfOffsetTerminalLambda_one_le]
    have hmLambdaLower : Real.rpow delta epsilon / 50 ≤
        m * pureWZ2DirectHalfOffsetTerminalLambda ^ 2 := by
      calc
        Real.rpow delta epsilon / 50 ≤ m := hmLower
        _ ≤ m * pureWZ2DirectHalfOffsetTerminalLambda ^ 2 := by
          exact le_mul_of_one_le_right hmPos.le hlambdaSquare
    have hpowerPos : 0 < Real.rpow delta epsilon :=
      Real.rpow_pos_of_pos hdelta _
    calc
      1 / (m * pureWZ2DirectHalfOffsetTerminalLambda ^ 2) ≤
          1 / (Real.rpow delta epsilon / 50) :=
        one_div_le_one_div_of_le (div_pos hpowerPos (by norm_num)) hmLambdaLower
      _ = 50 * Real.rpow delta (-epsilon) := by
        calc
          1 / (Real.rpow delta epsilon / 50) =
              50 * (Real.rpow delta epsilon)⁻¹ := by
            field_simp [hpowerPos.ne']
          _ = 50 * Real.rpow delta (-epsilon) := by
            exact congrArg (fun value : ℝ => 50 * value)
              (Real.rpow_neg hdelta.le epsilon).symm
  have hcallerFactor : 1 + 2 * callerRho ≤
      (1 + 2 * callerCoefficient) * sourceUpper := by
    calc
      1 + 2 * callerRho ≤ 1 + 2 * (callerCoefficient * sourceUpper) := by
        gcongr
      _ ≤ sourceUpper + 2 * (callerCoefficient * sourceUpper) := by
        gcongr
      _ = (1 + 2 * callerCoefficient) * sourceUpper := by ring
  have hrealIdentity :
      432 * callerRho ^ 2 * (1 + 2 * callerRho) *
          (1 / (m * pureWZ2DirectHalfOffsetTerminalLambda ^ 2 *
            sourceRho ^ 2)) =
        432 * (1 + 2 * callerRho) * (callerRho / sourceRho) ^ 2 *
          (1 / (m * pureWZ2DirectHalfOffsetTerminalLambda ^ 2)) := by
    field_simp [hsourcePos.ne', hmPos.ne', hlambdaPos.ne']
  rw [hrealIdentity]
  calc
    432 * (1 + 2 * callerRho) * (callerRho / sourceRho) ^ 2 *
          (1 / (m * pureWZ2DirectHalfOffsetTerminalLambda ^ 2)) ≤
        432 * ((1 + 2 * callerCoefficient) * sourceUpper) *
          (ratioCoefficient ^ 2 * Real.rpow delta (-epsilon) ^ 2) *
          (50 * Real.rpow delta (-epsilon)) := by
      gcongr
    _ = (432 *
          (1 + 2 * (2400000 * lineFactor + 2)) *
          (2400000 * lineFactor +
            2560000 * pureWZ2DirectHorizontalScale) ^ 2 *
          50) * sourceUpper * Real.rpow delta (-3 * epsilon) := by
      have hpowerThree : Real.rpow delta (-epsilon) ^ 2 *
          Real.rpow delta (-epsilon) = Real.rpow delta (-3 * epsilon) := by
        calc
          Real.rpow delta (-epsilon) ^ 2 * Real.rpow delta (-epsilon) =
              (Real.rpow delta (-epsilon) * Real.rpow delta (-epsilon)) *
                Real.rpow delta (-epsilon) := by rw [pow_two]
          _ = Real.rpow delta ((-epsilon) + (-epsilon)) *
                Real.rpow delta (-epsilon) := by
              exact congrArg (fun value : ℝ =>
                value * Real.rpow delta (-epsilon))
                (Real.rpow_add hdelta (-epsilon) (-epsilon)).symm
          _ = Real.rpow delta
                (((-epsilon) + (-epsilon)) + (-epsilon)) := by
              exact (Real.rpow_add hdelta
                ((-epsilon) + (-epsilon)) (-epsilon)).symm
          _ = Real.rpow delta (-3 * epsilon) := by congr 1; ring_nf
      dsimp only [callerCoefficient, ratioCoefficient, targetCoefficient]
      rw [← hpowerThree]
      ring

/-- For every schedule coordinate, the determinant part of `bodyConstant`
(with the packet factor omitted) is bounded by a fixed coefficient, one copy
of the source nearby-CWA output constant, and `delta ^ (-3 * epsilon)`. -/
theorem radiusRatioDeterminantEnvelope_le_sourcePower
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
    (coordinate : Fin scheduleData.sourceSchedule.scaleCount) :
    (432 : ENNReal) *
        Kakeya.realRpowENN
          (scheduleData.quotientSchedule.callerRho coordinate) 2 *
        ENNReal.ofReal
          (1 + 2 * scheduleData.quotientSchedule.callerRho coordinate) *
        ENNReal.ofReal
          (1 /
            (commonSource.halfOffsetAssembly.horizontalSource.m *
              pureWZ2DirectHalfOffsetTerminalLambda ^ 2 *
              scheduleData.representativeSchedule.sourceRho coordinate ^ 2)) ≤
      radiusRatioDeterminantCoefficient scheduleData.lineFactor *
        regularization.outputConstant *
        Kakeya.realRpowENN delta (-3 * epsilon) := by
  let sourceRho := scheduleData.representativeSchedule.sourceRho coordinate
  let callerRho := scheduleData.quotientSchedule.callerRho coordinate
  let m := commonSource.halfOffsetAssembly.horizontalSource.m
  have hdelta : 0 < delta :=
    commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hdeltaOne : delta ≤ 1 :=
    commonSource.halfOffsetAssembly.cfg.extremal.delta_le_one
  have hepsilon : 0 ≤ epsilon := commonSource.lemma31.epsilon_pos.le
  have houtputOne : 1 ≤ regularization.outputConstant :=
    regularization.cwa_nearby.2.1.1
  have houtputTop : regularization.outputConstant ≠ ⊤ :=
    regularization.cwa_nearby.2.1.2
  have hsourceLower : delta ≤ sourceRho := by
    dsimp only [sourceRho]
    exact scheduleData.sourceDelta_le_sourceRho coordinate
  have hmLower : Real.rpow delta epsilon / 50 ≤ m := by
    dsimp only [m]
    rw [← commonSource.halfOffsetAssembly_rho_eq_power_div,
      ← commonSource.halfOffsetAssembly.horizontalSource_scale]
    exact commonSource.halfOffsetAssembly.horizontalSource.slopeScale_lower
  have hsourceRhoENN : ENNReal.ofReal sourceRho ≤
      regularization.outputConstant := by
    dsimp only [sourceRho]
    rw [scheduleData.sourceRho_eq coordinate]
    apply le_trans
      (scheduleData.sourceSchedule.witness coordinate).within_factor.le
    calc
      regularization.outputConstant *
            ENNReal.ofReal
              (scheduleData.sourceSchedule.requested coordinate).1 ≤
          regularization.outputConstant * 1 := by
        gcongr
        simpa only [ENNReal.ofReal_one] using
          ENNReal.ofReal_mono
            (scheduleData.sourceSchedule.requested coordinate).2.2
      _ = regularization.outputConstant := by simp
  have hsourcePos : 0 < sourceRho := hdelta.trans_le hsourceLower
  have hsourceUpper : sourceRho ≤ regularization.outputConstant.toReal := by
    have htoReal :=
      (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top houtputTop).2
        hsourceRhoENN
    simpa [ENNReal.toReal_ofReal hsourcePos.le] using htoReal
  have houtputRealOne : 1 ≤ regularization.outputConstant.toReal := by
    have htoReal :=
      (ENNReal.toReal_le_toReal (by norm_num) houtputTop).2 houtputOne
    simpa using htoReal
  have hreal := radius_ratio_determinant_real_bound
    hdelta hdeltaOne hepsilon scheduleData.lineFactor_one
    commonSource.halfOffsetLineClassTargetDelta_pos
    (commonSource.halfOffsetLineClassTargetDelta_small.le.trans (by norm_num))
    commonSource.halfOffsetLineClassTargetDelta_lt_source_power
    hsourceLower houtputRealOne hsourceUpper hmLower
  have hcallerNonneg : 0 ≤
      horizontalNormalizedQuotientCallerScale terminal.targetDelta
        scheduleData.lineFactor sourceRho := by
    rw [← scheduleData.callerRho_eq coordinate]
    exact (scheduleData.quotientSchedule.quotient coordinate).caller_rho_pos.le
  rw [scheduleData.callerRho_eq coordinate]
  change (432 : ENNReal) *
      Kakeya.realRpowENN
        (horizontalNormalizedQuotientCallerScale terminal.targetDelta
          scheduleData.lineFactor sourceRho) 2 *
      ENNReal.ofReal
        (1 + 2 * horizontalNormalizedQuotientCallerScale terminal.targetDelta
          scheduleData.lineFactor sourceRho) *
      ENNReal.ofReal
        (1 / (m * pureWZ2DirectHalfOffsetTerminalLambda ^ 2 * sourceRho ^ 2)) ≤
    radiusRatioDeterminantCoefficient scheduleData.lineFactor *
      regularization.outputConstant *
      Kakeya.realRpowENN delta (-3 * epsilon)
  rw [show Kakeya.realRpowENN
      (horizontalNormalizedQuotientCallerScale terminal.targetDelta
        scheduleData.lineFactor sourceRho) 2 =
        ENNReal.ofReal
          ((horizontalNormalizedQuotientCallerScale terminal.targetDelta
            scheduleData.lineFactor sourceRho) ^ 2) by
    simp [Kakeya.realRpowENN]]
  unfold radiusRatioDeterminantCoefficient
  rw [← ENNReal.ofReal_ofNat (n := 432)]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 432)]
  rw [← ENNReal.ofReal_mul (by positivity :
    0 ≤ (432 : ℝ) *
      (horizontalNormalizedQuotientCallerScale terminal.targetDelta
        scheduleData.lineFactor sourceRho) ^ 2)]
  rw [← ENNReal.ofReal_mul (mul_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 432) (sq_nonneg _))
    (by nlinarith [hcallerNonneg]) :
    0 ≤ (432 : ℝ) *
      (horizontalNormalizedQuotientCallerScale terminal.targetDelta
        scheduleData.lineFactor sourceRho) ^ 2 *
      (1 + 2 * horizontalNormalizedQuotientCallerScale terminal.targetDelta
        scheduleData.lineFactor sourceRho))]
  refine (ENNReal.ofReal_mono hreal).trans_eq ?_
  rw [← ENNReal.ofReal_toReal houtputTop]
  simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  unfold Kakeya.realRpowENN
  rw [ENNReal.ofReal_mul
      (mul_nonneg
        (radiusRatioDeterminantCoefficient_nonneg
          (le_trans (by norm_num) scheduleData.lineFactor_one))
        ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul
      (radiusRatioDeterminantCoefficient_nonneg
        (le_trans (by norm_num) scheduleData.lineFactor_one))]

end DirectHalfOffsetTerminalCWAScheduleData
end PureWZ2ExternalWeightRegularizationData
end TerminalGeometry
end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
