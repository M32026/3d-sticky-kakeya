import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalCleanupSourceRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalConflictCleanupClosure
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.BoundedSourceCardLog
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FiniteScheduleParameters
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PaperShadingMassFinite

/-!
# Scalar leaves for direct half-offset terminal cleanup

This module keeps the ambient cardinality estimate, the actual conflict-degree
envelope, and the fixed-depth schedule separate from the terminal geometry.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2DirectCommonYSourceAssembly

variable {logExponent : ℕ} {sigma epsilon delta : ℝ}
  {commonSource : PureWZ2DirectCommonYSourceAssembly logExponent sigma epsilon delta}

namespace TerminalGeometry

/-- Polynomial ambient-cardinality bridge for the actual common source. -/
theorem ambient_enncard_le_polynomial :
    commonSource.halfOffsetAssembly.cfg.family.enncard ≤
      ENNReal.ofReal ((643 : ℝ) ^ 6) *
        Kakeya.realRpowENN delta (-6) := by
  let family := commonSource.halfOffsetAssembly.cfg.family
  have hdelta : 0 < delta := commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hdeltaOne : delta ≤ 1 := commonSource.halfOffsetAssembly.cfg.extremal.delta_le_one
  have hraw : family.card ≤ (2 * Nat.ceil (320 / delta) + 1) ^ 6 :=
    pureWZ2_bounded_source_card_le hdelta
      commonSource.halfOffsetAssembly.cfg.extremal.cwa_nearby_scales.2.2.1
      commonSource.halfOffsetAssembly.cfg.bounded_base
  have hceil : (Nat.ceil (320 / delta) : ℝ) < 320 / delta + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hbase : ((2 * Nat.ceil (320 / delta) + 1 : ℕ) : ℝ) ≤ 643 / delta := by
    have hthree : (3 : ℝ) ≤ 3 / delta := by
      calc
        (3 : ℝ) = 3 / 1 := by norm_num
        _ ≤ 3 / delta := by gcongr
    have hmiddle : ((2 * Nat.ceil (320 / delta) + 1 : ℕ) : ℝ) <
        640 / delta + 3 := by
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      calc
        2 * (Nat.ceil (320 / delta) : ℝ) + 1 <
            2 * (320 / delta + 1) + 1 := by gcongr
        _ = 640 / delta + 3 := by ring
    calc
      ((2 * Nat.ceil (320 / delta) + 1 : ℕ) : ℝ) ≤ 640 / delta + 3 := hmiddle.le
      _ ≤ 640 / delta + 3 / delta := by gcongr
      _ = 643 / delta := by field_simp [hdelta.ne']; ring
  have hreal : (family.card : ℝ) ≤ (643 / delta) ^ 6 := by
    calc
      (family.card : ℝ) ≤ ((2 * Nat.ceil (320 / delta) + 1 : ℕ) : ℝ) ^ 6 := by
        exact_mod_cast hraw
      _ ≤ (643 / delta) ^ 6 := by gcongr
  have hpow : (643 / delta) ^ 6 = (643 : ℝ) ^ 6 * delta ^ (-6 : ℝ) := by
    have hinv : delta ^ (-6 : ℝ) = (delta ^ 6)⁻¹ := by
      rw [Real.rpow_neg hdelta.le]
      norm_cast
    rw [hinv]
    field_simp [hdelta.ne']
  change (family.card : ENNReal) ≤ _
  rw [show (family.card : ENNReal) = ENNReal.ofReal (family.card : ℝ) by simp]
  rw [Kakeya.realRpowENN]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (643 : ℝ) ^ 6)]
  exact ENNReal.ofReal_mono (hreal.trans_eq hpow)

/-- Fixed coefficient in the source-power envelope for the actual conflict
degree after the ambient six-parameter card bound has been inserted. -/
def actualConflictDegreeCoefficient : ENNReal :=
  3200 * ENNReal.ofReal (actualConflictWidthCoefficient ^ 2) *
    ENNReal.ofReal ((643 : ℝ) ^ 6)

theorem actualConflictDegreeCoefficient_ne_top :
    actualConflictDegreeCoefficient ≠ ⊤ := by
  unfold actualConflictDegreeCoefficient
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
    ENNReal.ofReal_ne_top

/-- The literal mass-per-ambient-source normalization used by the external
weight cleanup.  This is fixed from the actual cleaned shading, rather than
from a surrogate terminal family. -/
def cleanupNormalizationWeight
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound) : ENNReal :=
  cleanup.shading.mass / commonSource.halfOffsetAssembly.cfg.family.enncard

theorem cleanupNormalizationWeight_mul_ambient_enncard
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound) :
    cleanupNormalizationWeight (commonSource := commonSource) cleanup *
        commonSource.halfOffsetAssembly.cfg.family.enncard =
      cleanup.shading.mass := by
  unfold cleanupNormalizationWeight
  apply ENNReal.div_mul_cancel
  · change (commonSource.halfOffsetAssembly.cfg.family.card : ENNReal) ≠ 0
    exact_mod_cast
      commonSource.halfOffsetAssembly.cfg.extremal.nonempty.ne'
  · simp [Kakeya.Streamlined.TubeFamily.enncard]

theorem cleanupNormalizationWeight_ne_zero
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound)
    (hmass : cleanup.shading.mass ≠ 0) :
    cleanupNormalizationWeight (commonSource := commonSource) cleanup ≠ 0 := by
  intro hzero
  have hbudget := cleanupNormalizationWeight_mul_ambient_enncard
    (commonSource := commonSource) cleanup
  rw [hzero, zero_mul] at hbudget
  exact hmass hbudget.symm

theorem cleanupNormalizationWeight_ne_top
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound) :
    cleanupNormalizationWeight (commonSource := commonSource) cleanup ≠ ⊤ := by
  unfold cleanupNormalizationWeight
  apply ENNReal.div_ne_top
  · exact wz1PaperTubeShading_mass_ne_top cleanup.shading
  · change (commonSource.halfOffsetAssembly.cfg.family.card : ENNReal) ≠ 0
    exact_mod_cast
      commonSource.halfOffsetAssembly.cfg.extremal.nonempty.ne'

/-- The literal centered terminal retains positive mass from the direct
source: positive source mass passes through anisotropic retubing, the
line-class popular box, cubical saturation, and the zero-loss centering. -/
theorem centeredCubicalShading_mass_pos
    (terminal : commonSource.TerminalGeometry) :
    0 < terminal.centeredCubicalShading.mass := by
  have hdelta : 0 < delta := commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hlength : 0 < commonSource.halfOffsetAssembly.horizontalSource.d -
      commonSource.halfOffsetAssembly.horizontalSource.c :=
    sub_pos.mpr commonSource.halfOffsetAssembly.horizontalSource.ordered
  have hambientSource : 0 <
      commonSource.halfOffsetAssembly.horizontalSource.sourceShading.mass := by
    have hsourceLower :=
      commonSource.halfOffsetAssembly.horizontalSource.source_mass_lower
    have hpower : 0 < Kakeya.realRpowENN delta
        (commonSource.halfOffsetAssembly.technicalLoss + 3) := by
      exact ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hdelta _)
    have hsourceFactor : 0 <
        Kakeya.realRpowENN delta
          (commonSource.halfOffsetAssembly.technicalLoss + 3) *
          ENNReal.ofReal
            (commonSource.halfOffsetAssembly.horizontalSource.d -
              commonSource.halfOffsetAssembly.horizontalSource.c) :=
      ENNReal.mul_pos
        hpower.ne'
        (ENNReal.ofReal_pos.mpr hlength).ne'
    exact hsourceFactor.trans_le hsourceLower
  have hsource : 0 < terminal.retubing.popular.sourceShading.mass := by
    rw [terminal.retubing.popular.source_mass_eq]
    exact terminal.retubing.popular.restricted_mass_pos
  have hretubing : 0 < terminal.retubing.raw.exactShading.mass := by
    rw [terminal.retubing.raw.exactShading_mass]
    rw [terminal.retubing.popular.openSourceShading_mass]
    exact ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr
        commonSource.halfOffsetAssembly.horizontalSource.slopeScale_pos).ne'
      hsource.ne'
  have hbox : 0 < terminal.box.restricted.mass := by
    have hfactor : 0 < ENNReal.ofReal
        (pureWZ2DirectHalfOffsetTerminalWidth ^ 2 / 9) :=
      ENNReal.ofReal_pos.mpr (div_pos
        (sq_pos_of_pos pureWZ2DirectHalfOffsetTerminalWidth_pos)
        (by norm_num))
    exact (ENNReal.mul_pos hfactor.ne' hretubing.ne').trans_le
      terminal.box.mass_lower
  have hterminal : 0 < terminal.cubicalShading.mass := by
    have hfactor : 0 < ENNReal.ofReal
        (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) :=
      ENNReal.ofReal_pos.mpr
        (sq_pos_of_pos pureWZ2DirectHalfOffsetTerminalLambda_pos)
    exact (ENNReal.mul_pos hfactor.ne' hbox.ne').trans_le terminal.mass_lower
  rw [terminal.centeredCubicalShading_mass]
  exact hterminal

/-- The weighted centered cleanup cannot have zero mass, since its mass
retention inequality begins with the positive literal centered terminal. -/
theorem cleanup_shading_mass_ne_zero
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound) :
    cleanup.shading.mass ≠ 0 := by
  intro hzero
  have hterminal := centeredCubicalShading_mass_pos
    (commonSource := commonSource) terminal
  have hretained := cleanup.mass_lower
  change (restrictPaperShading
    (Kakeya.Streamlined.TubeSubfamily.fromFinset terminal.centeredFamily
      cleanup.selected) terminal.centeredCubicalShading).mass = 0 at hzero
  rw [hzero, mul_zero] at hretained
  exact (not_lt_of_ge hretained) hterminal

/-- The actual conflict degree is controlled by a source-scale power once the
terminal radius has been put in its pre-runtime scale window. -/
theorem actualConflictDegreeBound_le_source_power
    (terminal : commonSource.TerminalGeometry)
    (htarget : terminal.targetDelta ≤ Real.rpow delta (1 - 2 * epsilon)) :
    actualConflictDegreeBound commonSource terminal ≤
      actualConflictDegreeCoefficient *
        Kakeya.realRpowENN delta
          (-(commonSource.halfOffsetAssembly.technicalLoss) +
            2 * (1 - 5 * epsilon) - 6) := by
  have hdelta : 0 < delta := commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hwidth := actualConflictWidth_le_source_power commonSource terminal htarget
  have hwidthNonneg : 0 ≤ actualConflictWidth commonSource terminal := by
    exact commonSource.halfOffsetAssembly.cfg.extremal.delta_pos.le.trans
      (delta_le_actualConflictWidth commonSource terminal)
  have hcoefficientNonneg : 0 ≤ actualConflictWidthCoefficient :=
    actualConflictWidthCoefficient_pos.le
  have hwidthSq :
      Kakeya.realRpowENN (actualConflictWidth commonSource terminal) 2 ≤
        ENNReal.ofReal (actualConflictWidthCoefficient ^ 2) *
          Kakeya.realRpowENN delta (2 * (1 - 5 * epsilon)) := by
    simp only [Kakeya.realRpowENN]
    rw [← ENNReal.ofReal_mul (sq_nonneg actualConflictWidthCoefficient)]
    apply ENNReal.ofReal_mono
    have hright : 0 ≤ actualConflictWidthCoefficient *
        Real.rpow delta (1 - 5 * epsilon) :=
      mul_nonneg hcoefficientNonneg (Real.rpow_nonneg hdelta.le _)
    have hsq := mul_self_le_mul_self hwidthNonneg hwidth
    calc
      (actualConflictWidth commonSource terminal) ^ (2 : ℝ) =
          actualConflictWidth commonSource terminal *
            actualConflictWidth commonSource terminal := by
              rw [Real.rpow_two, pow_two]
      _ ≤ actualConflictWidthCoefficient * Real.rpow delta (1 - 5 * epsilon) *
          (actualConflictWidthCoefficient *
            Real.rpow delta (1 - 5 * epsilon)) := hsq
      _ = actualConflictWidthCoefficient ^ 2 *
          Real.rpow delta (2 * (1 - 5 * epsilon)) := by
        calc
          actualConflictWidthCoefficient * Real.rpow delta (1 - 5 * epsilon) *
              (actualConflictWidthCoefficient *
                Real.rpow delta (1 - 5 * epsilon)) =
              actualConflictWidthCoefficient ^ 2 *
                (Real.rpow delta (1 - 5 * epsilon) *
                  Real.rpow delta (1 - 5 * epsilon)) := by
                    rw [pow_two]
                    ac_rfl
          _ = actualConflictWidthCoefficient ^ 2 *
              Real.rpow delta ((1 - 5 * epsilon) + (1 - 5 * epsilon)) := by
                congr 1
                exact (Real.rpow_add hdelta _ _).symm
          _ = _ := by
            congr 1
            ring
  calc
    actualConflictDegreeBound commonSource terminal =
        (3200 * Kakeya.realRpowENN delta
          (-commonSource.halfOffsetAssembly.technicalLoss)) *
          Kakeya.realRpowENN (actualConflictWidth commonSource terminal) 2 *
            commonSource.halfOffsetAssembly.cfg.family.enncard := rfl
    _ ≤ (3200 * Kakeya.realRpowENN delta
          (-commonSource.halfOffsetAssembly.technicalLoss)) *
          (ENNReal.ofReal (actualConflictWidthCoefficient ^ 2) *
            Kakeya.realRpowENN delta (2 * (1 - 5 * epsilon))) *
            commonSource.halfOffsetAssembly.cfg.family.enncard := by
          gcongr
    _ ≤ (3200 * Kakeya.realRpowENN delta
          (-commonSource.halfOffsetAssembly.technicalLoss)) *
          (ENNReal.ofReal (actualConflictWidthCoefficient ^ 2) *
            Kakeya.realRpowENN delta (2 * (1 - 5 * epsilon))) *
            (ENNReal.ofReal ((643 : ℝ) ^ 6) *
              Kakeya.realRpowENN delta (-6)) := by
          gcongr
          exact ambient_enncard_le_polynomial (commonSource := commonSource)
    _ = actualConflictDegreeCoefficient *
        Kakeya.realRpowENN delta
          (-(commonSource.halfOffsetAssembly.technicalLoss) +
            2 * (1 - 5 * epsilon) - 6) := by
      unfold actualConflictDegreeCoefficient
      have hpows :
          Kakeya.realRpowENN delta
              (-commonSource.halfOffsetAssembly.technicalLoss) *
            Kakeya.realRpowENN delta (2 * (1 - 5 * epsilon)) *
            Kakeya.realRpowENN delta (-6) =
          Kakeya.realRpowENN delta
            (-(commonSource.halfOffsetAssembly.technicalLoss) +
              2 * (1 - 5 * epsilon) - 6) := by
        rw [← realRpowENN_add hdelta, ← realRpowENN_add hdelta]
        congr 1
      calc
        3200 * Kakeya.realRpowENN delta
            (-commonSource.halfOffsetAssembly.technicalLoss) *
              (ENNReal.ofReal (actualConflictWidthCoefficient ^ 2) *
                Kakeya.realRpowENN delta (2 * (1 - 5 * epsilon))) *
              (ENNReal.ofReal ((643 : ℝ) ^ 6) *
                Kakeya.realRpowENN delta (-6)) =
            (3200 * ENNReal.ofReal (actualConflictWidthCoefficient ^ 2) *
              ENNReal.ofReal ((643 : ℝ) ^ 6)) *
              (Kakeya.realRpowENN delta
                (-commonSource.halfOffsetAssembly.technicalLoss) *
                Kakeya.realRpowENN delta (2 * (1 - 5 * epsilon)) *
                Kakeya.realRpowENN delta (-6)) := by ring
        _ = _ := by rw [hpows]

/-- With the concrete ambient mass-per-source normalization, the external
weight regularization uses the epsilon-fixed schedule depth.  The
actual cleaned mass is nonzero by the terminal-to-cleanup mass-retention
certificate above, so it is not exposed as a public hypothesis. -/
theorem cleanup_source_regularization_fixed_schedule
    {degreeBound : ENNReal}
    (terminal : commonSource.TerminalGeometry)
    (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound)
    (hepsilon : 0 < epsilon)
    (hsourceTwo : 2 < Kakeya.realRpowENN delta
      (-commonSource.halfOffsetAssembly.technicalLoss)) :
    Nonempty (PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup
      (Kakeya.realRpowENN delta
        (-commonSource.halfOffsetAssembly.technicalLoss))
      ((Kakeya.realRpowENN delta
        (-commonSource.halfOffsetAssembly.technicalLoss)) ^ 2)
      (cleanupNormalizationWeight (commonSource := commonSource) cleanup)
      (pureWZ2FixedScheduleLevelCount epsilon)) := by
  let sourceConstant : ENNReal :=
    Kakeya.realRpowENN delta
      (-commonSource.halfOffsetAssembly.technicalLoss)
  have hdelta : 0 < delta := commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hdeltaOne : delta ≤ 1 :=
    commonSource.halfOffsetAssembly.cfg.extremal.delta_le_one
  have hsourceTop : sourceConstant ≠ ⊤ := by
    simp [sourceConstant, Kakeya.realRpowENN]
  have hepsilonLevels : ENNReal.ofReal (1 / delta) ≤
      Kakeya.realRpowENN delta (-epsilon) ^
        pureWZ2FixedScheduleLevelCount epsilon :=
    pureWZ2FixedScheduleLevelCount_covers_inv
      hdelta hdeltaOne hepsilon
  have hsourceLower : Kakeya.realRpowENN delta (-epsilon) ≤
      sourceConstant := by
    dsimp only [sourceConstant]
    exact realRpowENN_antitone hdelta hdeltaOne
      (neg_le_neg commonSource.epsilon_le_halfOffsetAssembly_technicalLoss)
  have hlevels : ENNReal.ofReal (1 / delta) ≤
      sourceConstant ^ pureWZ2FixedScheduleLevelCount
        epsilon := by
    exact hepsilonLevels.trans <| pow_le_pow_left' hsourceLower _
  apply cleanup_source_regularization cleanup rfl
    (cleanupNormalizationWeight_ne_zero (commonSource := commonSource) cleanup
      (cleanup_shading_mass_ne_zero (commonSource := commonSource) cleanup))
    (cleanupNormalizationWeight_ne_top (commonSource := commonSource) cleanup)
  · rw [cleanupNormalizationWeight_mul_ambient_enncard
      (commonSource := commonSource) cleanup]
  · exact hsourceTwo
  · simpa [sourceConstant] using hlevels
  · exact finite_error_constant_sq hsourceTwo hsourceTop
  · simp [pow_two]

/-- An epsilon-only pre-runtime threshold makes the actual source constant
exceed two.  Since the technical loss dominates epsilon, the same epsilon-fixed
depth reaches the inverse runtime scale. -/
theorem exists_delta_for_cleanup_source_regularization_fixed_schedule
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {sigma delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        0 < delta → delta ≤ delta₀ →
        ∀ {degreeBound : ENNReal} (terminal : commonSource.TerminalGeometry)
          (cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
            commonSource terminal degreeBound),
          ∃ regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
            cleanup
            (Kakeya.realRpowENN delta
              (-commonSource.halfOffsetAssembly.technicalLoss))
            ((Kakeya.realRpowENN delta
              (-commonSource.halfOffsetAssembly.technicalLoss)) ^ 2)
            (cleanupNormalizationWeight (commonSource := commonSource) cleanup)
            (pureWZ2FixedScheduleLevelCount epsilon),
            2 < regularization.outputConstant := by
  rcases exists_delta_realRpowENN_bound (3 : ENNReal) (by norm_num)
      (gamma := epsilon) hepsilon with
    ⟨delta₀, hdelta₀Pos, hdelta₀One, hbound⟩
  refine ⟨delta₀, hdelta₀Pos, hdelta₀One, ?_⟩
  intro logExponent sigma delta commonSource hdelta hdeltaBound
    degreeBound terminal cleanup
  have hepsilonThree : (3 : ENNReal) ≤
      Kakeya.realRpowENN delta (-epsilon) :=
    hbound delta hdelta hdeltaBound
  have hsourceLower : Kakeya.realRpowENN delta (-epsilon) ≤
      Kakeya.realRpowENN delta
        (-commonSource.halfOffsetAssembly.technicalLoss) :=
    realRpowENN_antitone hdelta (hdeltaBound.trans hdelta₀One)
      (neg_le_neg commonSource.epsilon_le_halfOffsetAssembly_technicalLoss)
  have hsourceTwo : (2 : ENNReal) <
      Kakeya.realRpowENN delta
        (-commonSource.halfOffsetAssembly.technicalLoss) :=
    lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) hepsilonThree) hsourceLower
  rcases cleanup_source_regularization_fixed_schedule
      (commonSource := commonSource) terminal cleanup
      hepsilon hsourceTwo with
    ⟨regularization⟩
  refine ⟨regularization, ?_⟩
  exact regularization.outputConstant_gt_two hsourceTwo (by simp [pow_two])

end TerminalGeometry

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
