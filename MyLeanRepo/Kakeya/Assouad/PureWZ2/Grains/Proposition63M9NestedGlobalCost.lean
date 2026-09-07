import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9NestedFirstChart
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9CoarseGlobalAbsorption

/-!
# Proposition 6.3 M9: global-AD cost on the nested first chart

The coefficient of the outer chart is the Lipschitz constant produced by the
inner robust middle.  Its loss is strictly smaller than the outer chart local
loss.  The family-free global-AD cutoff therefore absorbs the complete coarse
slice constant before the outer runtime family is selected.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2
namespace Proposition63M9RobustInitialPreliminaryData

variable
    {sigma outputLoss : ℝ}
    {critical : PureWZ2CriticalPackage sigma}
    {schedule : Proposition63M9NestedScheduleData sigma outputLoss critical}
    {externalCutoff : ℝ}
    (data : Proposition63M9RobustInitialPreliminaryData critical
      schedule.inner schedule.innerCutoff externalCutoff)

private abbrev q : ℝ :=
  (schedule.innerCutoff.twoCall.secondQRequested data.r_pos
    data.r_le_robustCutoff).1

/-- The inherited inner Lipschitz coefficient costs less than one copy of the
outer local loss. -/
theorem outerPreliminary_coefficient_bound
    (hqOuter : data.q ≤ schedule.outerCutoff.outerScaleCeiling) :
    (data.outerPreliminary.lipschitz : ENNReal) ≤
      Kakeya.realRpowENN data.q
        (-schedule.outerCutoff.initial.localLoss) := by
  have qPos : 0 < data.q :=
    data.middle.second.lemma412.extremal.delta_pos
  have qOne : data.q ≤ 1 :=
    hqOuter.trans schedule.outerCutoff.outerScaleCeiling_le_one
  have lossLe : schedule.inner.lemma47Loss ≤
      schedule.outerCutoff.initial.localLoss :=
    schedule.inner.lemma47Loss_lt_preGrain.le.trans
      schedule.inner_preGrain_lt_outer_local.le
  change
    (Real.toNNReal (Real.rpow data.q (-schedule.inner.lemma47Loss)) :
        ENNReal) ≤
      Kakeya.realRpowENN data.q
        (-schedule.outerCutoff.initial.localLoss)
  exact Proposition63ChartSelectionData.coefficient_power_le_local_power
    qPos qOne lossLe

/-- The global slice constant of the outer chart is absorbed by the outer
pre-grain loss.  This is the exact scalar premise consumed by
`Proposition63M9RobustMiddleData.preGrain`. -/
theorem outerGlobalCost
    {hqOuter : data.q ≤ schedule.outerCutoff.outerScaleCeiling}
    (first : Proposition63GenericFirstRichBoundaryData
      (reentryLoss := schedule.outerCutoff.firstRichSchedule.sourceLoss)
      (data.outerRoot hqOuter) (data.outerPreliminaryOnRoot hqOuter)
      schedule.outerCutoff.firstRichSchedule) :
    Proposition63ChartSelectionData.proposition63WholeCellCoarseGlobalADConstant
        data.q first.power.requested.1 first.power.Delta
          schedule.outerCutoff.initial.localLoss
          (data.outerPreliminary.lipschitz : ℝ) ≤
      Kakeya.realRpowENN first.power.Delta
        (-schedule.outer.preGrainLoss) := by
  have qPos : 0 < data.q :=
    first.current.normalization.final_extremal.delta_pos
  have qGlobal : data.q ≤
      schedule.outerCutoff.globalADAbsorption.delta₀ :=
    hqOuter.trans
      schedule.outerCutoff.outerScaleCeiling_le_globalADAbsorption
  rw [first.power.requested_eq]
  exact schedule.outerCutoff.globalADAbsorption.wholeCell_global_cost
    data.outerPreliminary.lipschitz qPos qGlobal
    (by
      rw [first.power.Delta_eq]
      exact Real.rpow_pos_of_pos qPos _)
    (by
      rw [first.power.Delta_eq]
      exact schedule.outerCutoff.preliminaryAnalytic.first_power_small qPos <|
        hqOuter.trans
          schedule.outerCutoff.outerScaleCeiling_le_preliminaryPropertyP)
    first.power.tau_le_Delta_sq
    (schedule.outerCutoff.initial.sticky_pos.trans
      schedule.outerCutoff.initial.sticky_lt_local)
    (data.outerPreliminary_coefficient_bound hqOuter)
    first.power.Delta_eq
    schedule.outerCutoff.initial_local_global_gap

end Proposition63M9RobustInitialPreliminaryData
end Kakeya.Assouad.PureWZ2

end
