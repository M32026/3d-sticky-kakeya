import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalCleanupOutputPower
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalCWAGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalNormalizationRepresentativeSchedule
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# Canonical scale-window bound for the direct half-offset terminal CWA

For the canonical choice `sourceScheduleConstant = outputConstant ^ 2`, the
horizontal quotient scale-window constant costs twice the source-power loss
of the cleanup output constant.  A further arbitrarily small positive loss
absorbs the fixed horizontal line-distortion coefficient.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2DirectCommonYSourceAssembly
namespace TerminalGeometry
namespace PureWZ2ExternalWeightRegularizationData

/-- The fixed coefficient left after the canonical square of the source CWA
output constant is bounded by a source power. -/
def directHalfOffsetTerminalScaleWindowCoefficient
    (lineFactor : ℝ) : ENNReal :=
  ENNReal.ofReal (2400000 * lineFactor) + 2

theorem directHalfOffsetTerminalScaleWindowCoefficient_ne_top
    (lineFactor : ℝ) :
    directHalfOffsetTerminalScaleWindowCoefficient lineFactor ≠ ⊤ := by
  unfold directHalfOffsetTerminalScaleWindowCoefficient
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, by norm_num⟩

/-- Generic canonical scale-window estimate.  If the source CWA output
constant costs `q`, then its canonical square costs exactly `2 * q`; the
additive constant is absorbed into the same power because that negative power
is at least one. -/
theorem canonicalScaleWindow_le_coefficient_sourcePower
    {delta q lineFactor : ℝ} {outputConstant : ENNReal}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hq : 0 ≤ q)
    (houtput : outputConstant ≤
      Kakeya.realRpowENN delta (-q)) :
    horizontalNormalizedQuotientScaleWindowConstant
        lineFactor (outputConstant ^ 2) ≤
      directHalfOffsetTerminalScaleWindowCoefficient lineFactor *
        Kakeya.realRpowENN delta (-(2 * q)) := by
  let sourcePower := Kakeya.realRpowENN delta (-q)
  have hsourcePowerOne : 1 ≤ sourcePower := by
    dsimp only [sourcePower, Kakeya.realRpowENN]
    rw [ENNReal.one_le_ofReal]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hdelta hdeltaOne (by linarith)
  have hsourcePowerSqOne : 1 ≤ sourcePower ^ 2 :=
    one_le_pow₀ hsourcePowerOne
  have houtputSq : outputConstant ^ 2 ≤ sourcePower ^ 2 :=
    pow_le_pow_left' houtput 2
  have hpowerIdentity : sourcePower ^ 2 =
      Kakeya.realRpowENN delta (-(2 * q)) := by
    calc
      sourcePower ^ 2 = sourcePower * sourcePower := by rw [pow_two]
      _ = Kakeya.realRpowENN delta ((-q) + (-q)) := by
        exact (realRpowENN_add hdelta (-q) (-q)).symm
      _ = Kakeya.realRpowENN delta (-(2 * q)) := by
        congr 1
        ring
  unfold horizontalNormalizedQuotientScaleWindowConstant
    directHalfOffsetTerminalScaleWindowCoefficient
  calc
    ENNReal.ofReal (2400000 * lineFactor) * outputConstant ^ 2 + 2 ≤
        ENNReal.ofReal (2400000 * lineFactor) * sourcePower ^ 2 +
          2 * sourcePower ^ 2 := by
      apply add_le_add
      · gcongr
      · calc
          (2 : ENNReal) = 2 * 1 := by simp
          _ ≤ 2 * sourcePower ^ 2 := by gcongr
    _ = (ENNReal.ofReal (2400000 * lineFactor) + 2) *
          sourcePower ^ 2 := by ring
    _ = (ENNReal.ofReal (2400000 * lineFactor) + 2) *
          Kakeya.realRpowENN delta (-(2 * q)) := by rw [hpowerIdentity]

/-- The actual cleanup-output receipt closes the canonical scale window
uniformly for every runtime technical loss bounded by `2 * epsilon`.
The fixed coefficient spends one additional `scaleWindowLoss`. -/
theorem exists_delta_for_actualLocal_canonicalScaleWindow_sourcePower
    (epsilon scaleWindowLoss lineFactor : ℝ)
    (hepsilon : 0 < epsilon)
    (hscaleWindowLoss : 0 < scaleWindowLoss) :
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
            (pureWZ2FixedScheduleLevelCount epsilon)),
          horizontalNormalizedQuotientScaleWindowConstant lineFactor
              (regularization.outputConstant ^ 2) ≤
            Kakeya.realRpowENN delta
              (-(86 * epsilon + scaleWindowLoss)) := by
  let coefficient := directHalfOffsetTerminalScaleWindowCoefficient lineFactor
  rcases exists_delta_for_actualLocal_cleanup_output_source_power
      epsilon hepsilon with
    ⟨outputScale, houtputScale, houtputScaleOne, houtput⟩
  rcases exists_delta_realRpowENN_bound coefficient
      (directHalfOffsetTerminalScaleWindowCoefficient_ne_top lineFactor)
      hscaleWindowLoss with
    ⟨coefficientScale, hcoefficientScale, hcoefficientScaleOne, hcoefficient⟩
  let delta₀ := min outputScale coefficientScale
  refine ⟨delta₀, lt_min houtputScale hcoefficientScale,
    (min_le_left _ _).trans houtputScaleOne, ?_⟩
  intro logExponent sigma delta commonSource technicalLoss htechnical
    htechnicalUpper hdelta hdeltaBound
    terminal cleanup regularization
  have hdeltaOutput : delta ≤ outputScale :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaCoefficient : delta ≤ coefficientScale :=
    hdeltaBound.trans (min_le_right _ _)
  have hdeltaOne : delta ≤ 1 :=
    hdeltaOutput.trans houtputScaleOne
  let outputLoss : ℝ := 3 * technicalLoss + 37 * epsilon
  have houtputLoss : 0 ≤ outputLoss := by
    dsimp only [outputLoss]
    nlinarith [commonSource.epsilon_le_halfOffsetAssembly_technicalLoss]
  have houtput : regularization.outputConstant ≤
      Kakeya.realRpowENN delta (-outputLoss) := by
    dsimp only [outputLoss]
    exact houtput commonSource technicalLoss htechnical hdelta hdeltaOutput terminal cleanup
      regularization
  have hwindow := canonicalScaleWindow_le_coefficient_sourcePower
    (lineFactor := lineFactor)
    hdelta hdeltaOne houtputLoss houtput
  have hcoefficient : coefficient ≤
      Kakeya.realRpowENN delta (-scaleWindowLoss) :=
    hcoefficient delta hdelta hdeltaCoefficient
  calc
    horizontalNormalizedQuotientScaleWindowConstant lineFactor
          (regularization.outputConstant ^ 2) ≤
        coefficient * Kakeya.realRpowENN delta (-(2 * outputLoss)) := by
      simpa only [coefficient] using hwindow
    _ ≤ Kakeya.realRpowENN delta (-scaleWindowLoss) *
          Kakeya.realRpowENN delta (-(2 * outputLoss)) := by gcongr
    _ = Kakeya.realRpowENN delta
          (-(2 * outputLoss + scaleWindowLoss)) := by
      rw [← realRpowENN_add hdelta]
      congr 1
      ring
    _ ≤ Kakeya.realRpowENN delta
          (-(86 * epsilon + scaleWindowLoss)) := by
      exact realRpowENN_antitone hdelta hdeltaOne (by
        dsimp only [outputLoss]
        nlinarith)

/-- Specialization to the fixed line-distortion factor used by the actual
direct half-offset terminal schedule. -/
theorem exists_delta_for_actualLocal_directHalfOffsetScaleWindow_sourcePower
    (epsilon scaleWindowLoss : ℝ)
    (hepsilon : 0 < epsilon)
    (hscaleWindowLoss : 0 < scaleWindowLoss) :
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
            (pureWZ2FixedScheduleLevelCount epsilon)),
          horizontalNormalizedQuotientScaleWindowConstant
              directHalfOffsetTerminalLineFactor
              (regularization.outputConstant ^ 2) ≤
            Kakeya.realRpowENN delta
              (-(86 * epsilon + scaleWindowLoss)) := by
  exact exists_delta_for_actualLocal_canonicalScaleWindow_sourcePower
    epsilon scaleWindowLoss
      directHalfOffsetTerminalLineFactor hepsilon
        hscaleWindowLoss

end PureWZ2ExternalWeightRegularizationData
end TerminalGeometry
end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
