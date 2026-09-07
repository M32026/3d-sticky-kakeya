import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63IntervalLocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteWeightedLabelSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63IntervalRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperTubeHeightDistance
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63AnchorHeightComparison
import MyLeanRepo.Kakeya.Assouad.WZ1.TransportedRatioSlopeExtension

/-!
# Unified horizontal chart for Proposition 6.3

Each retained interval has at least one valid horizontal chart.  Select the
heavier of the two chart classes using the actual interval shaded masses.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

attribute [local instance] Classical.propDecidable

inductive Proposition63ChartLabel where
  | first
  | second
  deriving DecidableEq, Fintype

namespace Proposition63ChartLabel

def chart : Proposition63ChartLabel → WZ1HorizontalChart
  | first => WZ1HorizontalChart.first
  | second => WZ1HorizontalChart.second

end Proposition63ChartLabel

def proposition63IntervalChart
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    (data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity)
    (hDelta : 0 < Delta) (hDeltaSmall : Delta ≤ 1 / 200)
    (hdeltaDelta : delta ≤ Delta ^ 2)
    (hdeltaRatio : delta / Delta ≤ 1 / 4)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta))
    (hinterval : interval ∈ data.retainedIntervals) :
    Proposition63ChartLabel := by
  classical
  exact if 1 / 3 ≤ |(data.intervalTransportedNormal interval hinterval) 0|
    then .first else .second

lemma proposition63IntervalChart_bound
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    (data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity)
    (hDelta : 0 < Delta) (hDeltaSmall : Delta ≤ 1 / 200)
    (hdeltaDelta : delta ≤ Delta ^ 2)
    (hdeltaRatio : delta / Delta ≤ 1 / 4)
    (hrhoDelta : rho = Delta)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta))
    (hinterval : interval ∈ data.retainedIntervals) :
    match proposition63IntervalChart data hDelta hDeltaSmall
        hdeltaDelta hdeltaRatio interval hinterval with
    | .first => 1 / 3 ≤
        |(data.intervalTransportedNormal interval hinterval) 0|
    | .second => 1 / 3 ≤
        |(data.intervalTransportedNormal interval hinterval) 1| := by
  classical
  let certificate := Classical.choice
    (proposition63_interval_local_ad data hDelta hDeltaSmall
      hdeltaDelta hdeltaRatio hrhoDelta interval hinterval)
  unfold proposition63IntervalChart
  split_ifs with hfirst
  · exact hfirst
  · exact certificate.chart_available.resolve_left hfirst

def proposition63IntervalChartLabel
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    (data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity)
    (hDelta : 0 < Delta) (hDeltaSmall : Delta ≤ 1 / 200)
    (hdeltaDelta : delta ≤ Delta ^ 2)
    (hdeltaRatio : delta / Delta ≤ 1 / 4)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta)) : Proposition63ChartLabel := by
  classical
  by_cases hinterval : interval ∈ data.retainedIntervals
  · exact proposition63IntervalChart data hDelta hDeltaSmall
      hdeltaDelta hdeltaRatio interval hinterval
  · exact .first

structure Proposition63ChartSelectionData
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    (data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity)
    (hDelta : 0 < Delta) (hDeltaSmall : Delta ≤ 1 / 200)
    (hdeltaDelta : delta ≤ Delta ^ 2)
    (hdeltaRatio : delta / Delta ≤ 1 / 4) where
  chartLabel : Proposition63ChartLabel
  retained_weight :
    (∑ interval, if interval ∈ data.retainedIntervals then
      proposition63AxialPartitionMass input.selectedFiber
        (coarse.tube input.parent) hrho interval else 0) ≤
      2 * ∑ interval,
        if proposition63IntervalChartLabel data hDelta hDeltaSmall
            hdeltaDelta hdeltaRatio interval = chartLabel then
          (if interval ∈ data.retainedIntervals then
            proposition63AxialPartitionMass input.selectedFiber
              (coarse.tube input.parent) hrho interval else 0)
        else 0

namespace Proposition63ChartSelectionData

def intervals
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    {data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity}
    {hDelta : 0 < Delta} {hDeltaSmall : Delta ≤ 1 / 200}
    {hdeltaDelta : delta ≤ Delta ^ 2}
    {hdeltaRatio : delta / Delta ≤ 1 / 4}
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) :
    Finset (commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta)) :=
  data.retainedIntervals.filter fun interval =>
    proposition63IntervalChartLabel data hDelta hDeltaSmall
      hdeltaDelta hdeltaRatio interval = selection.chartLabel

variable
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    {data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity}
    {hDelta : 0 < Delta} {hDeltaSmall : Delta ≤ 1 / 200}
    {hdeltaDelta : delta ≤ Delta ^ 2}
    {hdeltaRatio : delta / Delta ≤ 1 / 4}

lemma intervals_subset
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) :
    selection.intervals ⊆ data.retainedIntervals :=
  Finset.filter_subset _ _

lemma interval_chart_bound
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (hrhoDelta : rho = Delta)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta))
    (hinterval : interval ∈ selection.intervals) :
    match selection.chartLabel.chart with
    | WZ1HorizontalChart.first =>
        1 / 3 ≤ |(data.intervalTransportedNormal interval
          (selection.intervals_subset hinterval)) 0|
    | WZ1HorizontalChart.second =>
        1 / 3 ≤ |(data.intervalTransportedNormal interval
          (selection.intervals_subset hinterval)) 1| := by
  have hretained := selection.intervals_subset hinterval
  have hlabel := (Finset.mem_filter.mp hinterval).2
  have hlabel' : proposition63IntervalChart data hDelta hDeltaSmall
      hdeltaDelta hdeltaRatio interval hretained = selection.chartLabel := by
    simpa [proposition63IntervalChartLabel, hretained] using hlabel
  have hbound := proposition63IntervalChart_bound data hDelta hDeltaSmall
    hdeltaDelta hdeltaRatio hrhoDelta interval hretained
  rw [hlabel'] at hbound
  cases hchart : selection.chartLabel <;>
    simp [Proposition63ChartLabel.chart, hchart] at hbound ⊢ <;>
    exact hbound

lemma interval_meets
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta))
    (hinterval : interval ∈ selection.intervals) :
    proposition63AxialPartitionMeets input.selectedFiber
      (coarse.tube input.parent) hrho data.commonSlice.distinguished interval :=
  (data.mem_retainedIntervals_iff interval).1
    (selection.intervals_subset hinterval)

theorem restriction_mass
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) :
    (proposition63IntervalRestriction input.selectedFiber
      (coarse.tube input.parent) hrho selection.intervals).mass =
      ∑ interval ∈ selection.intervals,
        proposition63AxialPartitionMass input.selectedFiber
          (coarse.tube input.parent) hrho interval := by
  exact proposition63IntervalRestriction_mass input.selectedFiber
    (coarse.tube input.parent) hrho
    (by
      unfold proposition63LiteralSliceWidth
      exact div_pos hDelta (by norm_num))
    selection.intervals

theorem commonSlice_mass_le_twice_restriction
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) :
    data.commonSlice.shading.mass ≤
      2 * (proposition63IntervalRestriction input.selectedFiber
        (coarse.tube input.parent) hrho selection.intervals).mass := by
  have hretainedMass :
      (∑ interval, if interval ∈ data.retainedIntervals then
        proposition63AxialPartitionMass input.selectedFiber
          (coarse.tube input.parent) hrho interval else 0) =
        data.commonSlice.shading.mass := by
    simpa [Proposition63CommonSliceRescaledData.retainedIntervals,
      Proposition63AxialCommonSliceData.shading, commonSliceRetainedMass]
      using (proposition63AxialAnchorShading_mass
        input.selectedFiber (coarse.tube input.parent) hrho
        (by
          unfold proposition63LiteralSliceWidth
          exact div_pos hDelta (by norm_num))
        data.commonSlice.distinguished).symm
  have hselectedMass :
      (∑ interval,
        if proposition63IntervalChartLabel data hDelta hDeltaSmall
            hdeltaDelta hdeltaRatio interval = selection.chartLabel then
          (if interval ∈ data.retainedIntervals then
            proposition63AxialPartitionMass input.selectedFiber
              (coarse.tube input.parent) hrho interval else 0)
        else 0) =
      (proposition63IntervalRestriction input.selectedFiber
        (coarse.tube input.parent) hrho selection.intervals).mass := by
    rw [selection.restriction_mass]
    simp only [intervals, Finset.sum_filter]
    calc
      (∑ interval,
          if proposition63IntervalChartLabel data hDelta hDeltaSmall
              hdeltaDelta hdeltaRatio interval = selection.chartLabel then
            (if interval ∈ data.retainedIntervals then
              proposition63AxialPartitionMass input.selectedFiber
                (coarse.tube input.parent) hrho interval else 0)
          else 0) =
          ∑ interval, if interval ∈ data.retainedIntervals then
            (if proposition63IntervalChartLabel data hDelta hDeltaSmall
                hdeltaDelta hdeltaRatio interval = selection.chartLabel then
              proposition63AxialPartitionMass input.selectedFiber
                (coarse.tube input.parent) hrho interval else 0) else 0 := by
            apply Finset.sum_congr rfl
            intro interval _
            by_cases hretained : interval ∈ data.retainedIntervals <;>
              by_cases hlabel : proposition63IntervalChartLabel data hDelta
                hDeltaSmall hdeltaDelta hdeltaRatio interval =
                  selection.chartLabel <;>
              simp only [hretained, hlabel, if_true, if_false]
      _ = ∑ interval ∈ data.retainedIntervals,
            if proposition63IntervalChartLabel data hDelta hDeltaSmall
                hdeltaDelta hdeltaRatio interval = selection.chartLabel then
              proposition63AxialPartitionMass input.selectedFiber
                (coarse.tube input.parent) hrho interval else 0 :=
          Finset.sum_ite_mem_eq _ _
  rw [← hretainedMass, ← hselectedMass]
  simpa only using selection.retained_weight

theorem half_commonSlice_mass_le_restriction
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) :
    (1 / 2 : ENNReal) * data.commonSlice.shading.mass ≤
      (proposition63IntervalRestriction input.selectedFiber
        (coarse.tube input.parent) hrho selection.intervals).mass := by
  calc
    (1 / 2 : ENNReal) * data.commonSlice.shading.mass ≤
        (1 / 2 : ENNReal) *
          (2 * (proposition63IntervalRestriction input.selectedFiber
            (coarse.tube input.parent) hrho selection.intervals).mass) :=
      mul_le_mul_left' selection.commonSlice_mass_le_twice_restriction _
    _ = (proposition63IntervalRestriction input.selectedFiber
          (coarse.tube input.parent) hrho selection.intervals).mass := by
      rw [← mul_assoc]
      have hhalf : (1 / 2 : ENNReal) * 2 = 1 := by
        have h : (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by
          simp [one_div]
        rw [h, ENNReal.inv_mul_cancel] <;> norm_num
      rw [hhalf, one_mul]

end Proposition63ChartSelectionData

theorem proposition63_select_chart
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    (data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity)
    (hDelta : 0 < Delta) (hDeltaSmall : Delta ≤ 1 / 200)
    (hdeltaDelta : delta ≤ Delta ^ 2)
    (hdeltaRatio : delta / Delta ≤ 1 / 4) :
    Nonempty (Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) := by
  let weight : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta) → ENNReal := fun interval =>
    if interval ∈ data.retainedIntervals then
      proposition63AxialPartitionMass input.selectedFiber
        (coarse.tube input.parent) hrho interval
    else 0
  let label := proposition63IntervalChartLabel data hDelta hDeltaSmall
    hdeltaDelta hdeltaRatio
  letI : Nonempty Proposition63ChartLabel := ⟨.first⟩
  rcases exists_weighted_label_retaining_average weight label with
    ⟨chartLabel, hchosen⟩
  have hcard : Fintype.card Proposition63ChartLabel = 2 := by decide
  rw [hcard] at hchosen
  refine ⟨{ chartLabel := chartLabel, retained_weight := ?_ }⟩
  simpa [weight, label] using hchosen

end Kakeya.Assouad.PureWZ2

end
