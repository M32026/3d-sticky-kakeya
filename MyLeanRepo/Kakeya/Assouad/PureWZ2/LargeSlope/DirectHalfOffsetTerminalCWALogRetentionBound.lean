import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalRequestedCWAConstructor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.BoundedSourceCardLog
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Fixed-depth logarithmic and retention bounds for the actual terminal CWA schedule

This is the scalar ledger for the finite actual-terminal schedule used in the
TeX `682--686` rescaling and the TeX `407--408` nearby-CWA output.  The depth
is bounded by the caller's fixed `parentLevelCount`; the separated terminal
family inherits the ambient six-parameter packing bound; and the apparently
dangerous selected-weight inverse in `bodyConstant` cancels the matching
selected-weight factor in `retentionConstant`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2DirectCommonYSourceAssembly
namespace TerminalGeometry
namespace PureWZ2ExternalWeightRegularizationData
namespace DirectHalfOffsetTerminalCWAScheduleData

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}

/-- The fixed depth available to every actual terminal CWA schedule built with
`parentLevelCount`. -/
def fixedDepth (parentLevelCount : ℕ) : ℕ :=
  parentLevelCount + 1

/-- One exponent large enough for both the cover logarithm and the cancelled
retention logarithm. -/
def fixedLogExponent (parentLevelCount : ℕ) : ℕ :=
  fixedDepth parentLevelCount + fixedDepth parentLevelCount + 1

/-- An enlarged version of the bounded-source logarithmic coefficient.  The
extra one makes the corresponding ENNReal logarithmic envelope at least one. -/
def sourceLogCoefficient : ℝ :=
  1 + pureWZ2BoundedSourceCardLogConstant

/-- Fixed coefficient for the complete-fiber cover loss. -/
def fixedCoverCoefficient (parentLevelCount : ℕ) : ENNReal :=
  16 * (((fixedDepth parentLevelCount + fixedDepth parentLevelCount : ℕ) : ENNReal))

/-- Fixed coefficient left after the selected-weight level cancels from the
two-stage retention loss. -/
def fixedCancelledRetentionCoefficient (parentLevelCount : ℕ) : ENNReal :=
  16 *
    (pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) ^
      fixedDepth parentLevelCount

/-- One fixed coefficient simultaneously dominating the cover and cancelled
retention losses. -/
def fixedCWACoefficient (parentLevelCount : ℕ) : ENNReal :=
  max (fixedCoverCoefficient parentLevelCount)
    (fixedCancelledRetentionCoefficient parentLevelCount)

theorem sourceLogCoefficient_nonneg : 0 ≤ sourceLogCoefficient := by
  unfold sourceLogCoefficient pureWZ2BoundedSourceCardLogConstant
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogLarge : 0 ≤ Real.log (2 * (643 : ℝ) ^ 6) :=
    Real.log_nonneg (by norm_num)
  positivity

theorem fixedCWACoefficient_ne_top (parentLevelCount : ℕ) :
    fixedCWACoefficient parentLevelCount ≠ ⊤ := by
  unfold fixedCWACoefficient fixedCoverCoefficient
    fixedCancelledRetentionCoefficient
  rw [← lt_top_iff_ne_top]
  apply max_lt
  · exact (lt_top_iff_ne_top.mpr <|
      ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _))
  · exact (lt_top_iff_ne_top.mpr <|
      ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))

/-- The runtime number of scheduled scales is bounded by a number fixed before
the runtime scale `delta`. -/
theorem scaleCount_le_fixedDepth
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
      (parentLevelCount := parentLevelCount) regularization) :
    scheduleData.sourceSchedule.scaleCount ≤ fixedDepth parentLevelCount := by
  exact scheduleData.sourceSchedule.scaleCount_le

/-- The first finite selection is nonempty.  This follows quantitatively from
the positive selected source weight and the two-stage retention receipt. -/
theorem separatedFine_nonempty
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
      (parentLevelCount := parentLevelCount) regularization) :
    (scheduleData.quotientSchedule.separatedFine
      (directHalfOffsetTerminalJointWeight
        (commonSource := commonSource) regularization)
      scheduleData.selection).family.Nonempty := by
  let weight := directHalfOffsetTerminalJointWeight
    (commonSource := commonSource) regularization
  let separated := scheduleData.quotientSchedule.separatedFine
    weight scheduleData.selection
  let finalFine := scheduleData.quotientSchedule.jointlyRegularizedFine
    weight scheduleData.selection scheduleData.joint.selected
  have hsourceCard : 0 < regularization.selected.family.enncard := by
    change (0 : ENNReal) < (regularization.selected.family.card : ENNReal)
    exact_mod_cast regularization.selected_nonempty
  have hlhs : 0 < regularization.selectedWeightLevel *
      regularization.selected.family.enncard :=
    ENNReal.mul_pos regularization.selectedWeightLevel_pos.ne' hsourceCard.ne'
  have hretained := scheduleData.source_cardinality_retention
  have hfinal : finalFine.family.Nonempty := by
    by_contra hempty
    have hzero : finalFine.family.enncard = 0 := by
      change (finalFine.family.card : ENNReal) = 0
      have hnat : finalFine.family.card = 0 := by
        simpa [Kakeya.Streamlined.TubeFamily.Nonempty] using hempty
      simp [hnat]
    rw [hzero, mul_zero] at hretained
    exact (not_le_of_gt hlhs) hretained
  have hcard : finalFine.family.card ≤ separated.family.card := by
    simpa using Fintype.card_le_of_injective
      finalFine.embedding finalFine.embedding.injective
  exact hfinal.trans_le hcard

/-- The actual separated terminal family is no larger than the ambient
ordinary source, hence satisfies the ambient six-parameter polynomial bound. -/
theorem separatedFine_card_le_source_polynomial
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
      (parentLevelCount := parentLevelCount) regularization) :
    (scheduleData.quotientSchedule.separatedFine
      (directHalfOffsetTerminalJointWeight
        (commonSource := commonSource) regularization)
      scheduleData.selection).family.card ≤
      (2 * Nat.ceil (320 / delta) + 1) ^ 6 := by
  have hselected : scheduleData.selection.selected.card ≤
      regularization.selected.family.card := by
    calc
      scheduleData.selection.selected.card ≤
          Fintype.card (Fin regularization.selected.family.card) :=
        scheduleData.selection.selected.card_le_univ
      _ = regularization.selected.family.card := Fintype.card_fin _
  have hambient : regularization.selected.family.card ≤
      commonSource.halfOffsetAssembly.cfg.family.card := by
    simpa using Fintype.card_le_of_injective
      regularization.selected.embedding regularization.selected.embedding.injective
  change scheduleData.selection.selected.card ≤ _
  exact hselected.trans <| hambient.trans <|
    pureWZ2_bounded_source_card_le
      commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
      commonSource.halfOffsetAssembly.cfg.extremal.cwa_nearby_scales.2.2.1
      commonSource.halfOffsetAssembly.cfg.bounded_base

/-- Source-scale logarithmic upper bound for the actual separated terminal
family. -/
theorem separatedFine_log_le_source_log
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
      (parentLevelCount := parentLevelCount) regularization) :
    (Nat.log 2
        (2 * (scheduleData.quotientSchedule.separatedFine
          (directHalfOffsetTerminalJointWeight
            (commonSource := commonSource) regularization)
          scheduleData.selection).family.card) + 1 : ENNReal) ≤
      ENNReal.ofReal
        (sourceLogCoefficient * (1 + Real.log delta⁻¹)) := by
  have hdelta := commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hdeltaOne := commonSource.halfOffsetAssembly.cfg.extremal.delta_le_one
  have hraw := pureWZ2_bounded_source_card_log_bound hdelta hdeltaOne
    scheduleData.separatedFine_nonempty
    scheduleData.separatedFine_card_le_source_polynomial
  have hlogNonneg : 0 ≤ 1 + Real.log delta⁻¹ := by
    have hinv : 1 ≤ delta⁻¹ := (one_le_inv₀ hdelta).mpr hdeltaOne
    linarith [Real.log_nonneg hinv]
  have henlarge :
      pureWZ2BoundedSourceCardLogConstant * (1 + Real.log delta⁻¹) ≤
        sourceLogCoefficient * (1 + Real.log delta⁻¹) := by
    unfold sourceLogCoefficient
    nlinarith
  have hconverted := ENNReal.ofReal_mono (hraw.trans henlarge)
  have hcast :
      ENNReal.ofReal
          (Nat.log 2
            (2 * (scheduleData.quotientSchedule.separatedFine
              (directHalfOffsetTerminalJointWeight
                (commonSource := commonSource) regularization)
              scheduleData.selection).family.card) + 1 : ℝ) =
        (Nat.log 2
          (2 * (scheduleData.quotientSchedule.separatedFine
            (directHalfOffsetTerminalJointWeight
              (commonSource := commonSource) regularization)
            scheduleData.selection).family.card) + 1 : ENNReal) := by
    rw [ENNReal.ofReal_add (by positivity)]
    norm_num
    positivity
  rwa [hcast] at hconverted

/-- Exact cancellation of the selected weight level in the factor appearing
inside `bodyConstant`. -/
theorem selectedWeightLevel_inv_mul_retentionConstant
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
      (parentLevelCount := parentLevelCount) regularization) :
    regularization.selectedWeightLevel⁻¹ * scheduleData.retentionConstant =
      (pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) ^
          scheduleData.sourceSchedule.scaleCount *
        (16 *
          (Nat.log 2
            (2 * (scheduleData.quotientSchedule.separatedFine
              (directHalfOffsetTerminalJointWeight
                (commonSource := commonSource) regularization)
              scheduleData.selection).family.card) + 1 : ENNReal) ^
            (scheduleData.sourceSchedule.scaleCount +
              scheduleData.sourceSchedule.scaleCount + 1)) := by
  unfold retentionConstant
  have hcancel : regularization.selectedWeightLevel⁻¹ *
      regularization.selectedWeightLevel = 1 :=
    ENNReal.inv_mul_cancel regularization.selectedWeightLevel_pos.ne'
      regularization.selectedWeightLevel_ne_top
  calc
    regularization.selectedWeightLevel⁻¹ *
        ((pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) ^
            scheduleData.sourceSchedule.scaleCount *
          (8 *
            (Nat.log 2
              (2 * (scheduleData.quotientSchedule.separatedFine
                (directHalfOffsetTerminalJointWeight
                  (commonSource := commonSource) regularization)
                scheduleData.selection).family.card) + 1 : ENNReal) ^
              (scheduleData.sourceSchedule.scaleCount +
                scheduleData.sourceSchedule.scaleCount + 1)) *
          (2 * regularization.selectedWeightLevel)) =
        (regularization.selectedWeightLevel⁻¹ *
            regularization.selectedWeightLevel) *
          ((pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) ^
              scheduleData.sourceSchedule.scaleCount *
            (16 *
              (Nat.log 2
                (2 * (scheduleData.quotientSchedule.separatedFine
                  (directHalfOffsetTerminalJointWeight
                    (commonSource := commonSource) regularization)
                  scheduleData.selection).family.card) + 1 : ENNReal) ^
                (scheduleData.sourceSchedule.scaleCount +
                  scheduleData.sourceSchedule.scaleCount + 1))) := by ring
    _ = _ := by rw [hcancel, one_mul]

/-- Before the final small-scale absorption, both the cover loss and the
weight-cancelled retention loss are bounded by one fixed coefficient times
one fixed power of the source logarithm. -/
theorem cover_and_cancelledRetention_le_fixed_log_power
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
    max (scheduleData.coverConstant coordinate)
        (regularization.selectedWeightLevel⁻¹ * scheduleData.retentionConstant) ≤
      fixedCWACoefficient parentLevelCount *
        (ENNReal.ofReal
          (sourceLogCoefficient * (1 + Real.log delta⁻¹))) ^
            fixedLogExponent parentLevelCount := by
  let logTerm : ENNReal :=
    (Nat.log 2
      (2 * (scheduleData.quotientSchedule.separatedFine
        (directHalfOffsetTerminalJointWeight
          (commonSource := commonSource) regularization)
        scheduleData.selection).family.card) + 1 : ENNReal)
  let sourceLog : ENNReal := ENNReal.ofReal
    (sourceLogCoefficient * (1 + Real.log delta⁻¹))
  have hlog : logTerm ≤ sourceLog :=
    scheduleData.separatedFine_log_le_source_log
  have hdelta := commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hdeltaOne := commonSource.halfOffsetAssembly.cfg.extremal.delta_le_one
  have hlogInv : 0 ≤ Real.log delta⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ hdelta).mpr hdeltaOne)
  have hcoefficientOne : 1 ≤ sourceLogCoefficient := by
    unfold sourceLogCoefficient pureWZ2BoundedSourceCardLogConstant
    have hfirst : 0 ≤
        Real.log (2 * (643 : ℝ) ^ 6) / Real.log 2 + 1 := by
      have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlogLarge : 0 ≤ Real.log (2 * (643 : ℝ) ^ 6) :=
        Real.log_nonneg (by norm_num)
      positivity
    nlinarith [le_max_left
      (Real.log (2 * (643 : ℝ) ^ 6) / Real.log 2 + 1)
      (6 / Real.log 2)]
  have hsourceLogOne : (1 : ENNReal) ≤ sourceLog := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_mono
    have honeLog : 1 ≤ 1 + Real.log delta⁻¹ := by linarith
    nlinarith [sourceLogCoefficient_nonneg]
  have hdepth := scheduleData.scaleCount_le_fixedDepth
  have hcoverExponent :
      scheduleData.sourceSchedule.scaleCount +
          scheduleData.sourceSchedule.scaleCount ≤
        fixedLogExponent parentLevelCount := by
    unfold fixedLogExponent
    omega
  have hretentionExponent :
      scheduleData.sourceSchedule.scaleCount +
          scheduleData.sourceSchedule.scaleCount + 1 ≤
        fixedLogExponent parentLevelCount := by
    unfold fixedLogExponent
    omega
  have hcount :
      ((scheduleData.sourceSchedule.scaleCount +
          scheduleData.sourceSchedule.scaleCount : ℕ) : ENNReal) ≤
        ((fixedDepth parentLevelCount +
          fixedDepth parentLevelCount : ℕ) : ENNReal) := by
    exact_mod_cast (by omega :
      scheduleData.sourceSchedule.scaleCount +
          scheduleData.sourceSchedule.scaleCount ≤
        fixedDepth parentLevelCount + fixedDepth parentLevelCount)
  have hdegree : (1 : ENNReal) ≤
      (pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) := by
    norm_num [pureWZ2AnisotropicQuotientCenterConflictDegree]
  apply max_le
  · calc
      scheduleData.coverConstant coordinate =
          16 *
            ((scheduleData.sourceSchedule.scaleCount +
              scheduleData.sourceSchedule.scaleCount : ℕ) : ENNReal) *
            logTerm ^
              (scheduleData.sourceSchedule.scaleCount +
                scheduleData.sourceSchedule.scaleCount) := by
        rfl
      _ ≤ fixedCoverCoefficient parentLevelCount *
          sourceLog ^ fixedLogExponent parentLevelCount := by
        unfold fixedCoverCoefficient
        gcongr
      _ ≤ fixedCWACoefficient parentLevelCount *
          sourceLog ^ fixedLogExponent parentLevelCount := by
        gcongr
        exact le_max_left _ _
  · rw [scheduleData.selectedWeightLevel_inv_mul_retentionConstant]
    calc
      (pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) ^
            scheduleData.sourceSchedule.scaleCount *
          (16 * logTerm ^
            (scheduleData.sourceSchedule.scaleCount +
              scheduleData.sourceSchedule.scaleCount + 1)) =
        (16 *
          (pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) ^
            scheduleData.sourceSchedule.scaleCount) *
          logTerm ^
            (scheduleData.sourceSchedule.scaleCount +
              scheduleData.sourceSchedule.scaleCount + 1) := by ring
      _ ≤ fixedCancelledRetentionCoefficient parentLevelCount *
          sourceLog ^ fixedLogExponent parentLevelCount := by
        unfold fixedCancelledRetentionCoefficient
        gcongr
      _ ≤ fixedCWACoefficient parentLevelCount *
          sourceLog ^ fixedLogExponent parentLevelCount := by
        gcongr
        exact le_max_right _ _

/-- Any prescribed positive source-power absorbs the complete fixed-depth
cover and cancelled-retention loss below one threshold chosen before all
runtime terminal and schedule data. -/
theorem exists_delta_for_cover_and_cancelledRetention_source_power
    (parentLevelCount : ℕ) {q : ℝ} (hq : 0 < q) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ}
        {sigma epsilon delta : ℝ}
        {commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta}
        {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
        {sourceConstant scheduleConstant normalizationWeight
          sourceScheduleConstant : ENNReal}
        {levelCount : ℕ}
        {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
          commonSource terminal degreeBound}
        {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
          cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
        (scheduleData : DirectHalfOffsetTerminalCWAScheduleData
          (sourceScheduleConstant := sourceScheduleConstant)
          (parentLevelCount := parentLevelCount) regularization),
        0 < delta → delta ≤ delta₀ →
        ∀ coordinate : Fin scheduleData.sourceSchedule.scaleCount,
          max (scheduleData.coverConstant coordinate)
              (regularization.selectedWeightLevel⁻¹ *
                scheduleData.retentionConstant) ≤
            Kakeya.realRpowENN delta (-q) := by
  have hexponent : 0 < fixedLogExponent parentLevelCount := by
    unfold fixedLogExponent fixedDepth
    omega
  rcases exists_delta_C_pow_log_absorbed_ennreal
      (fixedCWACoefficient parentLevelCount)
      (fixedCWACoefficient_ne_top parentLevelCount)
      sourceLogCoefficient sourceLogCoefficient_nonneg hq hexponent with
    ⟨delta₀, hdelta₀, hdelta₀One, habsorb⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro logExponent sigma epsilon delta commonSource terminal degreeBound sourceConstant
    scheduleConstant normalizationWeight sourceScheduleConstant levelCount
    cleanup regularization scheduleData hdelta hdeltaBound coordinate
  exact (scheduleData.cover_and_cancelledRetention_le_fixed_log_power
    coordinate).trans (habsorb delta hdelta hdeltaBound)

end DirectHalfOffsetTerminalCWAScheduleData
end PureWZ2ExternalWeightRegularizationData
end TerminalGeometry
end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
