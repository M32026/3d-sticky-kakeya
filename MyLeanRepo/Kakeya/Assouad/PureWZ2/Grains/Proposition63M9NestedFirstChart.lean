import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9NestedFirstRich
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9GenericFirstChart

/-!
# Proposition 6.3 M9: first chart on the nested robust preliminary output
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

/-- Run the canonical first-chart construction on the outer first-rich
terminal.  All smallness and density receipts are discharged from the outer
pre-runtime hierarchy; the chart parameters unused by the record indices are
fixed to zero. -/
theorem runOuterFirstChart
    {hqOuter : data.q ≤ schedule.outerCutoff.outerScaleCeiling}
    (first : Proposition63GenericFirstRichBoundaryData
      (reentryLoss := schedule.outerCutoff.firstRichSchedule.sourceLoss)
      (data.outerRoot hqOuter) (data.outerPreliminaryOnRoot hqOuter)
      schedule.outerCutoff.firstRichSchedule) :
    ∃ chart : Proposition63FirstChartData
        (localLoss := schedule.outerCutoff.initial.localLoss)
        (commonSliceLoss := schedule.outerCutoff.initial.localLoss)
        (chartLoss := schedule.outerCutoff.initial.lemma43SourceLoss)
        (tau := (0 : ℝ)) (epsilon₁ := (0 : ℝ)) (epsilon₃ := (0 : ℝ))
        (coefficient := (data.outerPreliminary.lipschitz : ℝ))
        first.terminal.data first.power.Delta (1 : ENNReal),
      proposition63FirstChartTerminalDensity first.power.requested.1
          schedule.outerCutoff.initial.stickyLoss ≤ chart.sliceDensity := by
  let bundle := data.outerTerminalBundle first
  have qPos : 0 < data.q :=
    first.current.normalization.final_extremal.delta_pos
  have qSmall : data.q ≤ 1 / 24 :=
    hqOuter.trans schedule.outerCutoff.outerScaleCeiling_le_preliminaryReentry
      |>.trans
        schedule.outerCutoff.preliminaryReentryAbsorption.delta₀_le_tiny
      |>.trans (by norm_num)
  have DeltaPos : 0 < first.power.Delta := by
    rw [first.power.Delta_eq]
    exact Real.rpow_pos_of_pos qPos _
  have DeltaSmall : first.power.Delta ≤ 1 / 200 := by
    rw [first.power.Delta_eq]
    exact schedule.outerCutoff.preliminaryAnalytic.first_power_small qPos <|
      hqOuter.trans
        schedule.outerCutoff.outerScaleCeiling_le_preliminaryPropertyP
  have ratioSmall : data.q / first.power.requested.1 ≤ 1 / 24 := by
    rw [first.power.requested_eq]
    calc
      data.q / first.power.Delta ≤ first.power.Delta := by
        apply (div_le_iff₀ DeltaPos).2
        simpa [pow_two] using first.power.tau_le_Delta_sq
      _ ≤ 1 / 200 := DeltaSmall
      _ ≤ 1 / 24 := by norm_num
  have ratioQuarter : data.q / first.power.Delta ≤ 1 / 4 := by
    rw [← first.power.requested_eq]
    exact ratioSmall.trans (by norm_num)
  have incidenceHalf : data.outerPreliminary.incidence ≤
      first.power.requested.1 / 2 := by
    change data.q ≤ first.power.requested.1 / 2
    rw [first.power.requested_eq]
    have DeltaNonnegative : 0 ≤ first.power.Delta := DeltaPos.le
    have DeltaHalf : first.power.Delta ≤ 1 / 2 :=
      DeltaSmall.trans (by norm_num)
    calc
      data.q ≤ first.power.Delta ^ 2 := first.power.tau_le_Delta_sq
      _ ≤ first.power.Delta / 2 := by nlinarith
  have ratioEq : data.q / first.power.requested.1 = first.power.h := by
    rw [first.power.requested_eq, first.power.h_eq]
  have hratioCutoff : first.power.h ≤
      schedule.outerCutoff.firstChartDensity.delta₀ := by
    calc
      first.power.h = data.q / first.power.requested.1 := ratioEq.symm
      _ ≤ first.power.Delta := by
        rw [first.power.requested_eq]
        apply (div_le_iff₀ DeltaPos).2
        simpa [pow_two] using first.power.tau_le_Delta_sq
      _ ≤ schedule.outerCutoff.firstChartDensity.delta₀ := by
        rw [first.power.Delta_eq]
        exact schedule.outerCutoff.firstChartPower_le_densityCutoff qPos hqOuter
  have commonDensity :
      Kakeya.realRpowENN (data.q / first.power.requested.1)
            schedule.outerCutoff.initial.localLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          proposition63FirstChartTerminalDensity first.power.requested.1
            schedule.outerCutoff.initial.stickyLoss := by
    rw [ratioEq, first.terminalDensity_eq_ratio_power]
    exact schedule.outerCutoff.firstChartDensity.common_density
      first.power.h_pos hratioCutoff
  have chartDensity :
      Kakeya.realRpowENN (data.q / first.power.requested.1)
            schedule.outerCutoff.initial.lemma43SourceLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          (proposition63FirstChartTerminalDensity first.power.requested.1
            schedule.outerCutoff.initial.stickyLoss / 2) := by
    rw [ratioEq, first.terminalDensity_eq_ratio_power]
    exact schedule.outerCutoff.firstChartDensity.chart_density
      first.power.h_pos hratioCutoff
  exact first.firstChartData bundle first.localGrains
    (data.outerNormalizedMap_cellwise first) (1 : ENNReal) qSmall
    incidenceHalf DeltaPos DeltaSmall first.power.tau_le_Delta_sq
    ratioQuarter first.power.requested.2.2 ratioSmall
    schedule.outerCutoff.initial.sticky_lt_local.le
    (schedule.outerCutoff.initial.sticky_pos.trans
      schedule.outerCutoff.initial.sticky_lt_local)
    (schedule.outerCutoff.initial.sticky_lt_local.le.trans
      schedule.outerCutoff.initial.local_lt_lemma43.le)
    (schedule.outerCutoff.initial.sticky_pos.trans
      (schedule.outerCutoff.initial.sticky_lt_local.trans
        schedule.outerCutoff.initial.local_lt_lemma43))
    commonDensity chartDensity

end Proposition63M9RobustInitialPreliminaryData

end Kakeya.Assouad.PureWZ2

end
