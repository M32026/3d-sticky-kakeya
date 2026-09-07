import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalCleanupScalarClosure
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalDensityScalarClosure

/-!
# Separate-coefficient cleanup-weight power receipts

The terminal mass coefficient and cleanup conflict-degree coefficient have
different mathematical roles.  This file keeps them separate and derives a
selected external-weight floor for the literal direct half-offset terminal.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

namespace PureWZ2DirectCommonYSourceAssembly
namespace TerminalGeometry
namespace PureWZ2ExternalWeightRegularizationData

variable {logExponent : ℕ} {sigma epsilon delta : ℝ}
  {commonSource : PureWZ2DirectCommonYSourceAssembly logExponent sigma epsilon delta}

/-- The fixed literal coefficient in the terminal source-to-centered-mass
transport. -/
def terminalMassCoefficient : ENNReal :=
  (ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
    (ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalWidth ^ 2 / 9) *
      (ENNReal.ofReal (((1 / 8 : ℝ) ^ 3) / 27) *
        ENNReal.ofReal (Real.pi / 4)))) / 250000

theorem terminalMassCoefficient_ne_zero : terminalMassCoefficient ≠ 0 := by
  unfold terminalMassCoefficient
  rw [ENNReal.div_ne_zero]
  constructor
  · apply mul_ne_zero
    · exact ENNReal.ofReal_pos.mpr (sq_pos_of_pos
        pureWZ2DirectHalfOffsetTerminalLambda_pos) |>.ne'
    apply mul_ne_zero
    · exact ENNReal.ofReal_pos.mpr (div_pos
        (sq_pos_of_pos pureWZ2DirectHalfOffsetTerminalWidth_pos)
        (by norm_num)) |>.ne'
    apply mul_ne_zero
    · norm_num
    exact ENNReal.ofReal_pos.mpr (by positivity) |>.ne'
  · norm_num

theorem terminalMassCoefficient_ne_top : terminalMassCoefficient ≠ ⊤ := by
  unfold terminalMassCoefficient
  apply ENNReal.div_ne_top
  · repeat' apply ENNReal.mul_ne_top
    all_goals exact ENNReal.ofReal_ne_top
  · norm_num

private lemma realRpowENN_inv_eq
    {x : ℝ} (hx : 0 < x) (a : ℝ) :
    (Kakeya.realRpowENN x a)⁻¹ = Kakeya.realRpowENN x (-a) := by
  simp only [Kakeya.realRpowENN]
  calc
    (ENNReal.ofReal (Real.rpow x a))⁻¹ =
        ENNReal.ofReal ((Real.rpow x a)⁻¹) :=
      (ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hx a)).symm
    _ = ENNReal.ofReal (Real.rpow x (-a)) :=
      congrArg ENNReal.ofReal (Real.rpow_neg hx.le a).symm

/-- Literal terminal mass lower bound before cleanup.  The two horizontal
source factors contribute the additional `2 * epsilon` power. -/
theorem centeredCubicalShading_mass_lower_source_power
    (terminal : commonSource.TerminalGeometry) :
    terminalMassCoefficient *
        Kakeya.realRpowENN delta
          (commonSource.halfOffsetAssembly.technicalLoss + 2 + 2 * epsilon) *
        commonSource.halfOffsetAssembly.cfg.family.enncard ≤
      terminal.centeredCubicalShading.mass := by
  let C : ENNReal :=
    ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
      (ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalWidth ^ 2 / 9) *
        (ENNReal.ofReal (((1 / 8 : ℝ) ^ 3) / 27) *
          ENNReal.ofReal (Real.pi / 4)))
  have hsource := terminal.retubing.popular.source_mass_card
  have hinterval := source_interval_slope_product_lower commonSource
  have hscaled := mul_le_mul_right hinterval
    (C *
      (Kakeya.realRpowENN delta
        (commonSource.halfOffsetAssembly.technicalLoss + 2) *
        commonSource.halfOffsetAssembly.cfg.family.enncard))
  have hpower :
      Kakeya.realRpowENN delta
          (commonSource.halfOffsetAssembly.technicalLoss + 2 + 2 * epsilon) =
        Kakeya.realRpowENN delta
          (commonSource.halfOffsetAssembly.technicalLoss + 2) *
        Kakeya.realRpowENN delta (2 * epsilon) := by
    rw [← realRpowENN_add commonSource.halfOffsetAssembly.cfg.extremal.delta_pos]
  rw [hpower]
  rw [terminal.centeredCubicalShading_mass]
  calc
    terminalMassCoefficient *
          (Kakeya.realRpowENN delta
            (commonSource.halfOffsetAssembly.technicalLoss + 2) *
            Kakeya.realRpowENN delta (2 * epsilon)) *
          commonSource.halfOffsetAssembly.cfg.family.enncard =
        C *
          (Kakeya.realRpowENN delta
            (commonSource.halfOffsetAssembly.technicalLoss + 2) *
            commonSource.halfOffsetAssembly.cfg.family.enncard) *
          (Kakeya.realRpowENN delta (2 * epsilon) / 250000) := by
            dsimp [terminalMassCoefficient, C]
            rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
            ring
    _ ≤ C *
          (Kakeya.realRpowENN delta
            (commonSource.halfOffsetAssembly.technicalLoss + 2) *
            commonSource.halfOffsetAssembly.cfg.family.enncard) *
          (ENNReal.ofReal commonSource.halfOffsetAssembly.horizontalSource.m *
            ENNReal.ofReal
              (commonSource.halfOffsetAssembly.horizontalSource.d -
                commonSource.halfOffsetAssembly.horizontalSource.c)) := by
          gcongr
    _ ≤ ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
          (ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalWidth ^ 2 / 9) *
            (ENNReal.ofReal commonSource.halfOffsetAssembly.horizontalSource.m *
              terminal.retubing.popular.sourceShading.mass)) := by
          dsimp [C] at hsource ⊢
          have hs := mul_le_mul_right hsource
            (ENNReal.ofReal commonSource.halfOffsetAssembly.horizontalSource.m)
          convert (mul_le_mul_right hs
            (ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
              ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalWidth ^ 2 / 9))) using 1 <;>
            norm_num [ENNReal.ofReal_mul] <;> ring
    _ ≤ terminal.cubicalShading.mass := by
      have hretubing :
          ENNReal.ofReal commonSource.halfOffsetAssembly.horizontalSource.m *
              terminal.retubing.popular.sourceShading.mass =
            terminal.retubing.raw.exactShading.mass := by
        rw [terminal.retubing.raw.exactShading_mass]
        rw [terminal.retubing.popular.openSourceShading_mass]
      calc
        _ = ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
            (ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalWidth ^ 2 / 9) *
              terminal.retubing.raw.exactShading.mass) := by rw [hretubing]
        _ ≤ ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
            terminal.box.restricted.mass := by
              gcongr
              exact terminal.box.mass_lower
        _ ≤ _ := terminal.mass_lower

/-- A generic cleanup-degree envelope converts the literal centered-terminal
mass floor into a selected external-weight floor.  The terminal mass and
degree coefficients are independent parameters. -/
theorem selectedWeightLevel_lower_of_separate_degree_power
    {degreeBound sourceConstant scheduleConstant degreeCoefficient : ENNReal}
    {degreeLoss : ℝ} {levelCount : ℕ}
    (terminal : commonSource.TerminalGeometry)
    (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound)
    (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant
        (cleanupNormalizationWeight (commonSource := commonSource) cleanup) levelCount)
    (hdegree : degreeBound + 1 ≤
      degreeCoefficient * Kakeya.realRpowENN delta (-degreeLoss))
    (hdegreeZero : degreeCoefficient ≠ 0)
    (hdegreeTop : degreeCoefficient ≠ ⊤) :
    (terminalMassCoefficient / (4 * degreeCoefficient)) *
        Kakeya.realRpowENN delta
          (commonSource.halfOffsetAssembly.technicalLoss + 2 + 2 * epsilon +
            degreeLoss) ≤ regularization.selectedWeightLevel := by
  have hdelta : 0 < delta :=
    commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hpowPos : 0 < Kakeya.realRpowENN delta degreeLoss := by
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)
  have hpowTop : Kakeya.realRpowENN delta degreeLoss ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have hneg : Kakeya.realRpowENN delta (-degreeLoss) =
      (Kakeya.realRpowENN delta degreeLoss)⁻¹ :=
    (realRpowENN_inv_eq hdelta degreeLoss).symm
  have hpow : Kakeya.realRpowENN delta
      (commonSource.halfOffsetAssembly.technicalLoss + 2 + 2 * epsilon +
        degreeLoss) =
      Kakeya.realRpowENN delta
        (commonSource.halfOffsetAssembly.technicalLoss + 2 + 2 * epsilon) *
      Kakeya.realRpowENN delta degreeLoss := by
    rw [← realRpowENN_add hdelta]
  apply le_trans _
    (regularization.normalization_div_four_le_selectedWeightLevel
      (by
        rw [cleanupNormalizationWeight_mul_ambient_enncard
          (commonSource := commonSource) cleanup]
        exact (cleanup.sourceWeight_sum (commonSource := commonSource)).symm.le))
  unfold cleanupNormalizationWeight
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
    (Or.inl (by norm_num))).mpr
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (by
      change (commonSource.halfOffsetAssembly.cfg.family.card : ENNReal) ≠ 0
      exact_mod_cast commonSource.halfOffsetAssembly.cfg.extremal.nonempty.ne'))
    (Or.inl (by simp [Kakeya.Streamlined.TubeFamily.enncard]))).mpr
  have hmass := centeredCubicalShading_mass_lower_source_power
    (commonSource := commonSource) terminal
  have hcleanup : terminal.centeredCubicalShading.mass ≤
      (degreeBound + 1) * cleanup.shading.mass := cleanup.mass_lower
  have hdegreeMass := mul_le_mul_left hdegree cleanup.shading.mass
  have hbound := hmass.trans (hcleanup.trans hdegreeMass)
  have hscaled := mul_le_mul_right hbound
    (Kakeya.realRpowENN delta degreeLoss)
  have hcancel :
      (Kakeya.realRpowENN delta degreeLoss) *
          ((degreeCoefficient *
            Kakeya.realRpowENN delta (-degreeLoss)) * cleanup.shading.mass) =
        degreeCoefficient * cleanup.shading.mass := by
    rw [hneg]
    calc
      _ = (Kakeya.realRpowENN delta degreeLoss *
          (Kakeya.realRpowENN delta degreeLoss)⁻¹) *
          (degreeCoefficient * cleanup.shading.mass) := by ring
      _ = _ := by rw [ENNReal.mul_inv_cancel hpowPos.ne' hpowTop, one_mul]
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
  rw [hpow, ENNReal.div_eq_inv_mul]
  have hfour : (4 : ENNReal) ≠ 0 := by norm_num
  have hfourTop : (4 : ENNReal) ≠ ⊤ := by norm_num
  apply (ENNReal.mul_le_mul_iff_right hdegreeZero hdegreeTop).mp
  calc
    degreeCoefficient *
        ((4 * degreeCoefficient)⁻¹ * terminalMassCoefficient *
          (Kakeya.realRpowENN delta
            (commonSource.halfOffsetAssembly.technicalLoss + 2 + 2 * epsilon) *
            Kakeya.realRpowENN delta degreeLoss) * 4 *
          commonSource.halfOffsetAssembly.cfg.family.enncard) =
      (Kakeya.realRpowENN delta degreeLoss) *
        (terminalMassCoefficient *
          Kakeya.realRpowENN delta
            (commonSource.halfOffsetAssembly.technicalLoss + 2 + 2 * epsilon) *
          commonSource.halfOffsetAssembly.cfg.family.enncard) := by
        have hdegreeFourZero : degreeCoefficient * 4 ≠ 0 :=
          mul_ne_zero hdegreeZero hfour
        have hdegreeFourTop : degreeCoefficient * 4 ≠ ⊤ :=
          ENNReal.mul_ne_top hdegreeTop hfourTop
        calc
          _ = ((degreeCoefficient * 4)⁻¹ *
              (degreeCoefficient * 4)) *
              (terminalMassCoefficient *
                Kakeya.realRpowENN delta
                  (commonSource.halfOffsetAssembly.technicalLoss + 2 + 2 * epsilon) *
                Kakeya.realRpowENN delta degreeLoss *
                commonSource.halfOffsetAssembly.cfg.family.enncard) := by ring
          _ = _ := by
            rw [ENNReal.inv_mul_cancel hdegreeFourZero hdegreeFourTop, one_mul]
            ring
    _ ≤ degreeCoefficient * cleanup.shading.mass := hscaled

end PureWZ2ExternalWeightRegularizationData
end TerminalGeometry
end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
