import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalCleanupWeightPower
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalLocalConflictPacking

/-!
# Pre-runtime scalar closure for actual final half-offset density

This closes the literal local-packing cleanup weight floor against the final
selected-family density budget.  No abstract scalar receipt is introduced.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2DirectCommonYSourceAssembly
namespace TerminalGeometry
namespace PureWZ2ExternalWeightRegularizationData

variable {epsilon : ℝ}

/-- The fixed density coefficient in the affine-diagonal mass budget. -/
def finalDensityCoefficient : ENNReal :=
  55296 * Kakeya.deltaTubeVolume 1

theorem finalDensityCoefficient_ne_top : finalDensityCoefficient ≠ ⊤ := by
  unfold finalDensityCoefficient
  exact ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top

/-- The actual local-packing coefficient is positive and finite after its
additive cleanup slack. -/
theorem actualLocalPackingCoefficient_add_one_ne_zero :
    actualLocalConflictPackingCoefficient + 1 ≠ 0 := by
  positivity

theorem actualLocalPackingCoefficient_add_one_ne_top :
    actualLocalConflictPackingCoefficient + 1 ≠ ⊤ := by
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, by norm_num⟩

/-- A runtime-independent small-scale threshold turns the literal local
packing selected-weight floor into exactly the final selected-family density
budget.  The runtime technical loss is bounded by `2ε`; terminal mass
transport therefore costs at most `2 + 4ε`, while local packing adds
`30ε`. -/
theorem exists_delta_for_actualLocalPacking_final_density_budget
    (outputLoss : ℝ)
    (hepsilon : 0 < epsilon)
    (houtput : 0 ≤ outputLoss + 2)
    (hgap : 2 + 34 * epsilon <
      (1 - 2 * epsilon) * (outputLoss + 2)) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {sigma delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        commonSource.halfOffsetAssembly.technicalLoss ≤ 2 * epsilon →
        0 < delta → delta ≤ delta₀ →
        ∀ (terminal : commonSource.TerminalGeometry)
          (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
            commonSource terminal
              (actualLocalConflictDegreeBound commonSource terminal))
          (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
            cleanup
            (Kakeya.realRpowENN delta
              (-commonSource.halfOffsetAssembly.technicalLoss))
            ((Kakeya.realRpowENN delta
              (-commonSource.halfOffsetAssembly.technicalLoss)) ^ 2)
            (cleanupNormalizationWeight (commonSource := commonSource) cleanup)
            (pureWZ2FixedScheduleLevelCount epsilon)),
          Kakeya.realRpowENN terminal.targetDelta outputLoss *
              (finalDensityCoefficient *
                Kakeya.realRpowENN terminal.targetDelta 2) ≤
            regularization.selectedWeightLevel := by
  let degreeCoefficient : ENNReal :=
    actualLocalConflictPackingCoefficient + 1
  let floorCoefficient : ENNReal :=
    terminalMassCoefficient / (4 * degreeCoefficient)
  have hdegreeZero : degreeCoefficient ≠ 0 :=
    actualLocalPackingCoefficient_add_one_ne_zero
  have hdegreeTop : degreeCoefficient ≠ ⊤ :=
    actualLocalPackingCoefficient_add_one_ne_top
  have hfloorZero : floorCoefficient ≠ 0 := by
    change terminalMassCoefficient / (4 * degreeCoefficient) ≠ 0
    rw [ENNReal.div_ne_zero]
    exact ⟨terminalMassCoefficient_ne_zero,
      ENNReal.mul_ne_top (by norm_num) hdegreeTop⟩
  have hfloorTop : floorCoefficient ≠ ⊤ := by
    change terminalMassCoefficient / (4 * degreeCoefficient) ≠ ⊤
    apply ENNReal.div_ne_top
    · exact terminalMassCoefficient_ne_top
    · exact mul_ne_zero (by norm_num) hdegreeZero
  have hfloorQuotientTop : finalDensityCoefficient / floorCoefficient ≠ ⊤ := by
    apply ENNReal.div_ne_top
    · exact finalDensityCoefficient_ne_top
    · exact hfloorZero
  rcases exists_delta_constant_mul_power_le_power
      (finalDensityCoefficient / floorCoefficient)
      hfloorQuotientTop
      (2 + 34 * epsilon)
      ((1 - 2 * epsilon) * (outputLoss + 2)) hgap with
    ⟨absorbScale, habsorbPos, habsorbOne, habsorb⟩
  rcases exists_delta_for_halfOffsetLineClassTargetDelta_power_upper
      epsilon hepsilon with
    ⟨targetScale, htargetPos, htargetOne, htarget⟩
  refine ⟨min absorbScale targetScale, lt_min habsorbPos htargetPos,
    (min_le_left _ _).trans habsorbOne, ?_⟩
  intro logExponent sigma delta commonSource htechnicalUpper hdelta hsmall
    terminal cleanup regularization
  have hdeltaAbsorb : delta ≤ absorbScale :=
    hsmall.trans (min_le_left _ _)
  have hdeltaTarget : delta ≤ targetScale :=
    hsmall.trans (min_le_right _ _)
  have htargetPower := htarget commonSource hdelta hdeltaTarget
  have hdegree := actualLocalConflictDegreeBound_add_one_le_source_power
    commonSource terminal htargetPower
  have hfloor := selectedWeightLevel_lower_of_separate_degree_power
    (commonSource := commonSource) terminal cleanup regularization
    (by simpa only [neg_mul] using hdegree) hdegreeZero hdegreeTop
  have habsorb' := habsorb hdelta hdeltaAbsorb
  have htargetBound := pure_wz2_target_power_upper
    commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
    commonSource.halfOffsetLineClassTargetDelta_pos.le
    htargetPower houtput
  change Kakeya.realRpowENN terminal.targetDelta (outputLoss + 2) ≤ _ at htargetBound
  have hpower :
      Kakeya.realRpowENN terminal.targetDelta outputLoss *
          Kakeya.realRpowENN terminal.targetDelta 2 =
        Kakeya.realRpowENN terminal.targetDelta (outputLoss + 2) := by
    rw [← realRpowENN_add commonSource.halfOffsetLineClassTargetDelta_pos]
  have hsourceExponent :
      commonSource.halfOffsetAssembly.technicalLoss + 2 + 2 * epsilon +
          30 * epsilon =
        commonSource.halfOffsetAssembly.technicalLoss + 2 + 32 * epsilon := by ring
  have hsourceBound :
      commonSource.halfOffsetAssembly.technicalLoss + 2 + 32 * epsilon ≤
        2 + 34 * epsilon := by linarith
  calc
    Kakeya.realRpowENN terminal.targetDelta outputLoss *
        (finalDensityCoefficient *
          Kakeya.realRpowENN terminal.targetDelta 2) =
      finalDensityCoefficient *
        Kakeya.realRpowENN terminal.targetDelta (outputLoss + 2) := by
          rw [← hpower]
          ring
    _ ≤ finalDensityCoefficient *
        Kakeya.realRpowENN delta
          ((1 - 2 * epsilon) * (outputLoss + 2)) := by gcongr
    _ = ((finalDensityCoefficient / floorCoefficient) *
          Kakeya.realRpowENN delta
            ((1 - 2 * epsilon) * (outputLoss + 2))) * floorCoefficient := by
          calc
            _ = (finalDensityCoefficient / floorCoefficient *
                floorCoefficient) *
                Kakeya.realRpowENN delta
                  ((1 - 2 * epsilon) * (outputLoss + 2)) := by
              rw [ENNReal.div_mul_cancel hfloorZero hfloorTop]
            _ = _ := by ring
    _ ≤ Kakeya.realRpowENN delta (2 + 34 * epsilon) *
          floorCoefficient := by
          exact (mul_le_mul_left habsorb' floorCoefficient).trans
            (by gcongr)
    _ = floorCoefficient *
        Kakeya.realRpowENN delta (2 + 34 * epsilon) := by ring
    _ ≤ regularization.selectedWeightLevel := by
      calc
        _ ≤ floorCoefficient *
            Kakeya.realRpowENN delta
              (commonSource.halfOffsetAssembly.technicalLoss + 2 + 2 * epsilon +
                30 * epsilon) := by
              rw [hsourceExponent]
              gcongr
              exact realRpowENN_antitone
                commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
                commonSource.halfOffsetAssembly.cfg.extremal.delta_le_one hsourceBound
        _ ≤ _ := hfloor

end PureWZ2ExternalWeightRegularizationData
end TerminalGeometry
end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
