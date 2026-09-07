import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalFinalRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalFiniteSliceGlobalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalScalarBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperGlobalADVolumeUpper
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SmallTwistedProjectionVolumeBound

/-!
# Volume wrapper for the direct half-offset final target

This file performs only the final analytic volume step.  The global AD input
is first restricted to the literal final shading, and the public slope is
bounded by its finite-slice envelope.  All remaining arithmetic is exposed as
one scalar inequality.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

namespace PureWZ2DirectCommonYSourceAssembly
namespace TerminalGeometry

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}

/-- The sole scalar inequality left after the final shading has inherited
global AD and the safe public slope has been given its finite-slice bound. -/
def DirectHalfOffsetTerminalFinalVolumeScalarBudget
    (terminal : commonSource.TerminalGeometry)
    (globalConstant : ENNReal) (outputLoss : ℝ) : Prop :=
  8 * (globalConstant *
      Kakeya.realRpowENN
        ((2 * (1 + finiteSlicePublicSlopeBound commonSource terminal)) /
          terminal.targetDelta) (1 - sigma) *
      ENNReal.ofReal (2 * terminal.targetDelta)) ≤
    Kakeya.realRpowENN terminal.targetDelta (sigma - outputLoss)

namespace PureWZ2ExternalWeightRegularizationData

/-- The final-family volume wrapper.  It uses only global AD on the ambient
terminal, restriction to `data.finalShading`, the safe-public-slope bound, and
the one explicit scalar budget above. -/
theorem DirectHalfOffsetTerminalRequestedCWAData.finalShading_volume_upper
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant C : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant)
    (outputLoss : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCTop : C ≠ ⊤)
    (ambientGlobalAD : ∀ z : ℝ, ∀ _ : z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (safePublicSlope commonSource terminal z))
          (horizontalSlice terminal.cubicalShading.union z))
        terminal.targetDelta (1 - sigma) C)
    (budget : DirectHalfOffsetTerminalFinalVolumeScalarBudget
      terminal C outputLoss) :
    volume data.finalShading.union ≤
      Kakeya.realRpowENN terminal.targetDelta (sigma - outputLoss) := by
  apply (pureWZ2_paperShading_volume_le_of_global_ad
    data.finalShading (safePublicSlope commonSource terminal)
    commonSource.halfOffsetLineClassTargetDelta_pos
    (commonSource.halfOffsetLineClassTargetDelta_small.le.trans (by norm_num))
    hsigma hsigmaOne hCTop
    (finiteSlicePublicSlopeBound_nonneg commonSource terminal)
    (fun _ hz => safePublicSlope_abs_le_finiteSlicePublicSlopeBound
      commonSource terminal hz)
    (data.finalShading_global_ad
      (safePublicSlope commonSource terminal) ambientGlobalAD)).trans
  exact budget

/-- The same pre-frozen scalar budget gives the immediate twisted-projection
consequence of the large-slope configuration.  Unlike the old fixed-24
argument, this keeps the ambient slope offset and does not assume `slope 0 = 0`. -/
theorem DirectHalfOffsetTerminalRequestedCWAData.finalShading_projection_upper
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant C : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant)
    (outputLoss : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCTop : C ≠ ⊤)
    (ambientGlobalAD : ∀ z : ℝ, ∀ _ : z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (safePublicSlope commonSource terminal z))
          (horizontalSlice terminal.cubicalShading.union z))
        terminal.targetDelta (1 - sigma) C)
    (budget : DirectHalfOffsetTerminalFinalVolumeScalarBudget
      terminal C outputLoss) :
    volume (twistedProjection (safePublicSlope commonSource terminal) ''
        data.finalShading.union) ≤
      Kakeya.realRpowENN terminal.targetDelta (sigma - outputLoss) := by
  apply pure_wz2_small_twisted_projection_of_global_ad_scalar_budget
    data.finalShading (safePublicSlope commonSource terminal)
    commonSource.halfOffsetLineClassTargetDelta_pos
    (commonSource.halfOffsetLineClassTargetDelta_small.le.trans (by norm_num))
    hsigma hsigmaOne hCTop data.finalShading_cubical
    (finiteSlicePublicSlopeBound_nonneg commonSource terminal)
    (fun _ hz => safePublicSlope_abs_le_finiteSlicePublicSlopeBound
      commonSource terminal hz)
    (data.finalShading_global_ad
      (safePublicSlope commonSource terminal) ambientGlobalAD)
  exact budget

end PureWZ2ExternalWeightRegularizationData

/-- A fixed real coefficient which dominates twice one plus the absorbable
finite-slice slope envelope after `rho = delta ^ epsilon / 50` is inserted. -/
def finalVolumeSlopeSourceCoefficient : ℝ :=
  2 * (1 +
    (pureWZ2DirectHalfOffsetTerminalLambda * (2 + 400 * 2500) + 2))

theorem finalVolumeSlopeSourceCoefficient_pos :
    0 < finalVolumeSlopeSourceCoefficient := by
  unfold finalVolumeSlopeSourceCoefficient
  positivity [pureWZ2DirectHalfOffsetTerminalLambda_pos]

/-- The source-power loss contributed by the public-slope factor in the
volume estimate. -/
def finalVolumeSlopeSourceLoss (epsilon sigma : ℝ) : ℝ :=
  2 * epsilon * (1 - sigma)

/-- Runtime-independent finite coefficient left by the final volume formula. -/
def finalVolumeFiniteConstant (sigma : ℝ) : ENNReal :=
  16 * Kakeya.realRpowENN finalVolumeSlopeSourceCoefficient (1 - sigma)

theorem finalVolumeFiniteConstant_ne_top (sigma : ℝ) :
    finalVolumeFiniteConstant sigma ≠ ⊤ := by
  unfold finalVolumeFiniteConstant
  exact ENNReal.mul_ne_top (by norm_num) (by simp [Kakeya.realRpowENN])

private theorem halfOffset_rho_inv_sq_eq_source_power
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta) :
    commonSource.halfOffsetAssembly.rho.1⁻¹ ^ 2 =
      2500 * Real.rpow delta (-(2 * epsilon)) := by
  have hdelta := commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hp := Real.rpow_pos_of_pos hdelta epsilon
  have hnegative : Real.rpow delta (-(2 * epsilon)) =
      (Real.rpow delta epsilon * Real.rpow delta epsilon)⁻¹ := by
    rw [show 2 * epsilon = epsilon + epsilon by ring]
    exact (Real.rpow_neg hdelta.le _).trans
      (congrArg Inv.inv (Real.rpow_add hdelta epsilon epsilon))
  rw [commonSource.halfOffsetAssembly_rho_eq_power_div, hnegative]
  field_simp [hp.ne]
  norm_num

/-- The finite-slice public slope contributes exactly the displayed
source-scale power. -/
theorem two_mul_one_add_finiteSlicePublicSlopeBound_le_source_power
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)
    (terminal : commonSource.TerminalGeometry)
    (hepsilon : 0 < epsilon) :
    2 * (1 + finiteSlicePublicSlopeBound commonSource terminal) ≤
      finalVolumeSlopeSourceCoefficient *
        Real.rpow delta (-(2 * epsilon)) := by
  have hdelta := commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hdeltaOne := commonSource.halfOffsetAssembly.cfg.extremal.delta_le_one
  have hpowerOne : 1 ≤ Real.rpow delta (-(2 * epsilon)) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne
      (by linarith : -(2 * epsilon) ≤ 0)
  have hslope := finiteSlicePublicSlopeBound_le_sourcePower commonSource terminal
  rw [finiteSliceAbsorbableSlopeBound,
    halfOffset_rho_inv_sq_eq_source_power commonSource] at hslope
  unfold finalVolumeSlopeSourceCoefficient
  nlinarith [pureWZ2DirectHalfOffsetTerminalLambda_pos]

/-- The dynamic slope coefficient in the final volume bound is dominated by
a fixed coefficient times its exact source-scale power loss. -/
theorem finalVolumeSlopeCoefficient_le_source_power
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)
    (terminal : commonSource.TerminalGeometry)
    (hepsilon : 0 < epsilon) (hsigmaOne : sigma < 1) :
    16 * Kakeya.realRpowENN
        (2 * (1 + finiteSlicePublicSlopeBound commonSource terminal))
          (1 - sigma) ≤
      finalVolumeFiniteConstant sigma *
        Kakeya.realRpowENN delta
          (-(finalVolumeSlopeSourceLoss epsilon sigma)) := by
  have hdelta := commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hbase := two_mul_one_add_finiteSlicePublicSlopeBound_le_source_power
    commonSource terminal hepsilon
  have hleftNonneg :
      0 ≤ 2 * (1 + finiteSlicePublicSlopeBound commonSource terminal) := by
    positivity [finiteSlicePublicSlopeBound_nonneg commonSource terminal]
  have hsourceFactorPos : 0 < Real.rpow delta (-(2 * epsilon)) :=
    Real.rpow_pos_of_pos hdelta _
  have hpowReal := Real.rpow_le_rpow hleftNonneg hbase
    (by linarith : 0 ≤ 1 - sigma)
  have hpowENN :
      Kakeya.realRpowENN
          (2 * (1 + finiteSlicePublicSlopeBound commonSource terminal))
            (1 - sigma) ≤
        Kakeya.realRpowENN
          (finalVolumeSlopeSourceCoefficient *
            Real.rpow delta (-(2 * epsilon))) (1 - sigma) :=
    ENNReal.ofReal_le_ofReal hpowReal
  have hsourcePower :
      Kakeya.realRpowENN (Real.rpow delta (-(2 * epsilon))) (1 - sigma) =
        Kakeya.realRpowENN delta
          (-(finalVolumeSlopeSourceLoss epsilon sigma)) := by
    unfold Kakeya.realRpowENN finalVolumeSlopeSourceLoss
    congr 1
    exact (Real.rpow_mul hdelta.le (-(2 * epsilon)) (1 - sigma)).symm.trans <| by
      congr 1
      ring
  calc
    16 * Kakeya.realRpowENN
        (2 * (1 + finiteSlicePublicSlopeBound commonSource terminal))
          (1 - sigma) ≤
      16 * Kakeya.realRpowENN
        (finalVolumeSlopeSourceCoefficient *
          Real.rpow delta (-(2 * epsilon))) (1 - sigma) := by gcongr
    _ = finalVolumeFiniteConstant sigma *
        Kakeya.realRpowENN delta
          (-(finalVolumeSlopeSourceLoss epsilon sigma)) := by
      rw [realRpowENN_mul finalVolumeSlopeSourceCoefficient_pos
        hsourceFactorPos (1 - sigma), hsourcePower]
      unfold finalVolumeFiniteConstant
      ring

/-- Algebraic normal form of the scalar volume expression. -/
theorem directHalfOffsetFinalVolume_expression_eq
    {radius sigma globalLoss slopeBound : ℝ}
    (hradius : 0 < radius) (_hsigmaOne : sigma < 1)
    (hslopeBound : 0 ≤ slopeBound) :
    8 * (Kakeya.realRpowENN radius (-globalLoss) *
        Kakeya.realRpowENN ((2 * (1 + slopeBound)) / radius)
          (1 - sigma) * ENNReal.ofReal (2 * radius)) =
      (16 * Kakeya.realRpowENN (2 * (1 + slopeBound)) (1 - sigma)) *
        Kakeya.realRpowENN radius (sigma - globalLoss) := by
  have hbase : 0 < 2 * (1 + slopeBound) := by positivity
  have hinv : Kakeya.realRpowENN radius⁻¹ (1 - sigma) =
      Kakeya.realRpowENN radius (-(1 - sigma)) := by
    exact congrArg ENNReal.ofReal <|
      (Real.inv_rpow hradius.le (1 - sigma)).trans
        (Real.rpow_neg hradius.le (1 - sigma)).symm
  have htwo : ENNReal.ofReal (2 * radius) =
      (2 : ENNReal) * Kakeya.realRpowENN radius 1 := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    simp [Kakeya.realRpowENN]
  rw [show (2 * (1 + slopeBound)) / radius =
      (2 * (1 + slopeBound)) * radius⁻¹ by ring,
    realRpowENN_mul hbase (inv_pos.mpr hradius), hinv, htwo]
  have hpower : Kakeya.realRpowENN radius (-globalLoss) *
        Kakeya.realRpowENN radius (-(1 - sigma)) *
        Kakeya.realRpowENN radius 1 =
      Kakeya.realRpowENN radius (sigma - globalLoss) := by
    rw [← realRpowENN_add hradius, ← realRpowENN_add hradius]
    congr 1
    ring
  rw [show
    8 * (Kakeya.realRpowENN radius (-globalLoss) *
        (Kakeya.realRpowENN (2 * (1 + slopeBound)) (1 - sigma) *
          Kakeya.realRpowENN radius (-(1 - sigma))) *
        (2 * Kakeya.realRpowENN radius 1)) =
      (16 * Kakeya.realRpowENN (2 * (1 + slopeBound)) (1 - sigma)) *
        (Kakeya.realRpowENN radius (-globalLoss) *
          Kakeya.realRpowENN radius (-(1 - sigma)) *
          Kakeya.realRpowENN radius 1) by ring, hpower]

/-- One threshold, chosen before any runtime family or terminal, absorbs the
entire dynamic public-slope factor when the global-AD output constant is
`targetDelta ^ (-globalLoss)`.  The displayed strict gap is the actual cost
of the `rho⁻²` slope envelope; no stronger unconditional claim is made. -/
theorem exists_delta_for_directHalfOffsetFinalVolume_source_power_absorption
    (epsilon sigma globalLoss outputLoss : ℝ)
    (hepsilon : 0 < epsilon) (hsigmaOne : sigma < 1)
    (houtputGap : 0 ≤ outputLoss - globalLoss)
    (hgap : finalVolumeSlopeSourceLoss epsilon sigma <
      (1 - 2 * epsilon) * (outputLoss - globalLoss)) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        0 < delta → delta ≤ delta₀ →
        ∀ terminal : commonSource.TerminalGeometry,
          DirectHalfOffsetTerminalFinalVolumeScalarBudget terminal
            (Kakeya.realRpowENN terminal.targetDelta (-globalLoss))
            outputLoss := by
  rcases exists_delta_for_halfOffsetLineClass_constant_source_negative_le_target_negative
      epsilon (finalVolumeSlopeSourceLoss epsilon sigma)
      (outputLoss - globalLoss) (finalVolumeFiniteConstant sigma)
      (finalVolumeFiniteConstant_ne_top sigma) hepsilon houtputGap hgap with
    ⟨delta₀, hdelta₀, hdelta₀One, habsorb⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro logExponent delta commonSource _hdelta hdeltaSmall terminal
  have hslopeAbsorb :
      16 * Kakeya.realRpowENN
          (2 * (1 + finiteSlicePublicSlopeBound commonSource terminal))
            (1 - sigma) ≤
        Kakeya.realRpowENN terminal.targetDelta
          (-(outputLoss - globalLoss)) :=
    (finalVolumeSlopeCoefficient_le_source_power commonSource terminal
      hepsilon hsigmaOne).trans
        (habsorb commonSource
          commonSource.halfOffsetAssembly.cfg.extremal.delta_pos hdeltaSmall)
  unfold DirectHalfOffsetTerminalFinalVolumeScalarBudget
  rw [directHalfOffsetFinalVolume_expression_eq
    commonSource.halfOffsetLineClassTargetDelta_pos hsigmaOne
      (finiteSlicePublicSlopeBound_nonneg commonSource terminal)]
  calc
    (16 * Kakeya.realRpowENN
        (2 * (1 + finiteSlicePublicSlopeBound commonSource terminal))
          (1 - sigma)) *
        Kakeya.realRpowENN terminal.targetDelta (sigma - globalLoss) ≤
      Kakeya.realRpowENN terminal.targetDelta
          (-(outputLoss - globalLoss)) *
        Kakeya.realRpowENN terminal.targetDelta (sigma - globalLoss) := by
          gcongr
    _ = Kakeya.realRpowENN terminal.targetDelta (sigma - outputLoss) := by
      rw [← realRpowENN_add commonSource.halfOffsetLineClassTargetDelta_pos]
      congr 1
      ring

end TerminalGeometry
end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
