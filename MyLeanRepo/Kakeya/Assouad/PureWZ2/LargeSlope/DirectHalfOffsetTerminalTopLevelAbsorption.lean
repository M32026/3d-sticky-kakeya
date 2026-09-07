import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalAssembly

/-!
# Top-level absorption for the direct half-offset terminal

The actual terminal radius tends to zero uniformly over all runtime source
assemblies.  This file combines that geometric radius bound with fixed-constant
absorption and supplies the top-level scalar inequality without accepting a
runtime radius receipt.
-/

noncomputable section

namespace Kakeya.Assouad
namespace PureWZ2DirectCommonYSourceAssembly

/-- Every actual common source already forces the exponent used in its
power-scale construction to be at most one eighth. -/
theorem epsilon_le_one_eighth
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta) :
    epsilon ≤ 1 / 8 := by
  have hdelta := commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hdeltaLtOne : delta < 1 :=
    commonSource.lemma31.delta_small.trans_lt (by norm_num)
  have hpower := commonSource.lemma31.delta_le_rho_eight
  rw [commonSource.lemma31.data.rho_eq_power] at hpower
  have hrpow : (Real.rpow delta epsilon) ^ 8 =
      Real.rpow delta (8 * epsilon) := by
    exact rpow_nat_pow hdelta epsilon 8
  rw [hrpow] at hpower
  have hpowerFinal : Real.rpow delta 1 ≤
      Real.rpow delta (8 * epsilon) := by
    simpa using hpower
  by_contra hnot
  have hlt : 1 < 8 * epsilon := by linarith
  exact (not_lt_of_ge hpowerFinal)
    (Real.rpow_lt_rpow_of_exponent_gt hdelta hdeltaLtOne hlt)

/-- The fixed coefficient in the raw actual-terminal radius estimate. -/
def halfOffsetLineClassTargetDeltaCoefficient : ℝ :=
  1280000 * pureWZ2DirectHorizontalScale

theorem halfOffsetLineClassTargetDeltaCoefficient_nonneg :
    0 ≤ halfOffsetLineClassTargetDeltaCoefficient := by
  unfold halfOffsetLineClassTargetDeltaCoefficient
  positivity [pureWZ2DirectHorizontalScale_pos]

/-- A source-scale threshold, chosen before every runtime source, puts the
actual terminal radius below the fixed power `delta ^ (1/2)`. -/
theorem exists_delta_for_halfOffsetLineClassTargetDelta_half_power_upper :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ}
        {sigma epsilon delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        0 < delta → delta ≤ delta₀ →
        commonSource.halfOffsetLineClassTargetDelta ≤
          Real.rpow delta (1 / 2) := by
  rcases exists_delta_mul_rpow_le_rpow
      halfOffsetLineClassTargetDeltaCoefficient
      halfOffsetLineClassTargetDeltaCoefficient_nonneg
      (show (1 / 2 : ℝ) < 3 / 4 by norm_num) with
    ⟨delta₀, hdelta₀, hdelta₀One, habsorb⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro logExponent sigma epsilon delta commonSource hdelta hdeltaSmall
  have hdeltaOne : delta ≤ 1 := hdeltaSmall.trans hdelta₀One
  have hepsilon : epsilon ≤ 1 / 8 := epsilon_le_one_eighth commonSource
  have hexponent : (3 / 4 : ℝ) ≤ 1 - epsilon := by linarith
  have hpower : Real.rpow delta (1 - epsilon) ≤
      Real.rpow delta (3 / 4) :=
    Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne hexponent
  calc
    commonSource.halfOffsetLineClassTargetDelta ≤
        halfOffsetLineClassTargetDeltaCoefficient *
          Real.rpow delta (1 - epsilon) :=
      commonSource.halfOffsetLineClassTargetDelta_lt_source_power.le
    _ ≤ halfOffsetLineClassTargetDeltaCoefficient *
        Real.rpow delta (3 / 4) := by
      exact mul_le_mul_of_nonneg_left hpower
        halfOffsetLineClassTargetDeltaCoefficient_nonneg
    _ ≤ Real.rpow delta (1 / 2) := habsorb delta hdelta hdeltaSmall

/-- Runtime-independent top-level absorption for every actual terminal.
The threshold depends only on the positive loss gap and is fixed before the
runtime source, family, or terminal is selected. -/
theorem exists_delta_for_directHalfOffsetTerminal_top_level_absorption
    (nearbyLoss outputLoss : ℝ)
    (hgap : 0 < outputLoss - 3 * nearbyLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ}
        {sigma epsilon delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        0 < delta → delta ≤ delta₀ →
        ∀ terminal : commonSource.TerminalGeometry,
          (4 : ENNReal) * Kakeya.realRpowENN terminal.targetDelta
              (outputLoss - 3 * nearbyLoss) ≤ 1 := by
  let lossGap := outputLoss - 3 * nearbyLoss
  rcases exists_delta_for_halfOffsetLineClassTargetDelta_half_power_upper with
    ⟨radiusScale, hradiusScale, hradiusScaleOne, hradius⟩
  rcases exists_delta_constant_mul_power_le_power (4 : ENNReal) (by norm_num)
      0 (lossGap / 2) (by dsimp only [lossGap]; linarith) with
    ⟨absorptionScale, habsorptionScale, habsorptionScaleOne, habsorb⟩
  let delta₀ := min radiusScale absorptionScale
  refine ⟨delta₀, lt_min hradiusScale habsorptionScale,
    (min_le_left _ _).trans hradiusScaleOne, ?_⟩
  intro logExponent sigma epsilon delta commonSource hdelta hdeltaSmall
    terminal
  have hdeltaRadius : delta ≤ radiusScale :=
    hdeltaSmall.trans (min_le_left _ _)
  have hdeltaAbsorption : delta ≤ absorptionScale :=
    hdeltaSmall.trans (min_le_right _ _)
  have htarget := hradius commonSource hdelta hdeltaRadius
  have htargetPowerReal :
      Real.rpow terminal.targetDelta lossGap ≤
        Real.rpow (Real.rpow delta (1 / 2)) lossGap :=
    Real.rpow_le_rpow commonSource.halfOffsetLineClassTargetDelta_pos.le
      htarget (by dsimp only [lossGap]; linarith)
  have htargetPower :
      Kakeya.realRpowENN terminal.targetDelta lossGap ≤
        Kakeya.realRpowENN delta (lossGap / 2) := by
    apply (ENNReal.ofReal_le_ofReal htargetPowerReal).trans_eq
    unfold Kakeya.realRpowENN
    congr 1
    exact (Real.rpow_mul hdelta.le (1 / 2) lossGap).symm.trans <| by
      congr 1
      ring
  calc
    (4 : ENNReal) * Kakeya.realRpowENN terminal.targetDelta lossGap ≤
        4 * Kakeya.realRpowENN delta (lossGap / 2) := by gcongr
    _ ≤ Kakeya.realRpowENN delta 0 :=
      habsorb hdelta hdeltaAbsorption
    _ = 1 := by simp [Kakeya.realRpowENN]

end PureWZ2DirectCommonYSourceAssembly
end Kakeya.Assouad

end
