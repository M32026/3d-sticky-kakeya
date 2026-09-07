import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9GenericFirstRichBoundary
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9GenericFirstRichTerminalBundle
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FirstStage
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MetricFiberInput
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9FirstChartDensity

/-!
# Generic first chart from an arbitrary first-rich terminal

This module packages the exact terminal object, arbitrary source local grains,
and the canonical mass-maximal metric fibre into the interface consumed by the
first chart.  Scalar cutoff choices remain explicit inputs.
-/

noncomputable section
namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

namespace Proposition63GenericFirstRichBoundaryData

variable
    {delta sigma inputLoss normalizationLoss densityLoss currentLoss localLoss
      reentryLoss stickyLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
      densityLoss}
    {preliminary : Proposition63PreliminaryLocalGrainData
      (localLoss := localLoss) (reentryLoss := currentLoss)
      root.normalization}
    {schedule : Proposition63RichStickyKernelScheduleData sigma stickyLoss}
    (first : Proposition63GenericFirstRichBoundaryData
      (reentryLoss := reentryLoss) root preliminary schedule)

/-- The exact rich-terminal shading has positive mass. -/
theorem terminalMassPos (hdeltaSmall : delta ≤ 1 / 24) :
    0 < first.terminal.data.refined.mass := by
  have sourceMass : 0 < first.current.normalization.croppedRefined.mass :=
    cropped_extremal_shading_mass_pos
      first.current.normalization.final_extremal
      first.current.normalization.line_class hdeltaSmall
  have hdeltaOne : delta < 1 := hdeltaSmall.trans_lt (by norm_num)
  have fractionPos := (pure_refinement_fraction_pos_ne_top
    first.current.normalization.final_extremal.delta_pos hdeltaOne 61).1
  exact (ENNReal.mul_pos fractionPos.ne' sourceMass.ne').trans_le
    first.terminal.data.retained_mass

/-- Canonical metric-fibre input, tied to the same terminal and accompanied
by the terminal's stored unit-ball receipt. -/
theorem metricFiberInputCanonical_exists
    {incidence : ℝ} {coefficient : NNReal}
    {rootPlaneMap : PaperWZ1WeakPlaneMapData
      first.current.normalization.croppedRefined incidence}
    (bundle : Proposition63M9GenericFirstRichTerminalBundle
      first.terminal rootPlaneMap coefficient)
    (sourceLocalGrains : Proposition63InitialWeakLocalGrainData
      (incidence := incidence) first.current.normalization.croppedRefined sigma
        (Kakeya.realRpowENN delta (-localLoss)) coefficient)
    (rootCellwise : ∀ left right,
      wz1PaperGridIndex delta left = wz1PaperGridIndex delta right →
        rootPlaneMap.planeMap left = rootPlaneMap.planeMap right)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hincidence : incidence ≤ first.power.requested.1 / 2) :
    let rebalanced := bundle.initialRebalanced sourceLocalGrains rootCellwise
      (first.terminalMassPos hdeltaSmall)
      first.current.normalization.final_extremal.delta_pos hincidence
    ∃ input : Proposition63MetricFiberInputData
        (stickyLoss := stickyLoss) (localLoss := localLoss)
        (coefficient := (coefficient : ℝ)) rebalanced
        first.terminal.data.coarse_extremal.delta_pos,
      input.frozenRescaled.rescalingCertificate.publicFamily.IsInUnitBall := by
  dsimp only
  let initial := bundle.initialLocalData sourceLocalGrains rootCellwise
    (first.terminalMassPos hdeltaSmall)
  let rebalanced := bundle.initialRebalanced sourceLocalGrains rootCellwise
    (first.terminalMassPos hdeltaSmall)
    first.current.normalization.final_extremal.delta_pos hincidence
  let sourceDensity := proposition63CanonicalAmbientDensity initial
  have sourceDensitySpec :
      sourceDensity * first.terminal.data.selected.family.enncard *
          Kakeya.realRpowENN delta 2 =
        first.terminal.data.refined.mass :=
    proposition63CanonicalAmbientDensity_spec initial
      first.current.normalization.final_extremal.delta_pos
      first.terminal.data.selected_nonempty
  exact proposition63_metric_fiber_input_with_unit_ball
    first.terminal.canonical_rescaled_fiber
    first.terminal.canonical_rescaled_fiber_unit_ball rebalanced sourceDensity
    sourceDensitySpec.le first.terminal.data.coarse_extremal.nonempty

/-- The terminal density is bounded by the canonical density of every metric
fibre input constructed on the generic identity rebalancing. -/
theorem terminalDensity_le_canonical
    {incidence : ℝ} {coefficient : NNReal}
    {rootPlaneMap : PaperWZ1WeakPlaneMapData
      first.current.normalization.croppedRefined incidence}
    (bundle : Proposition63M9GenericFirstRichTerminalBundle
      first.terminal rootPlaneMap coefficient)
    (sourceLocalGrains : Proposition63InitialWeakLocalGrainData
      (incidence := incidence) first.current.normalization.croppedRefined sigma
        (Kakeya.realRpowENN delta (-localLoss)) coefficient)
    (rootCellwise : ∀ left right,
      wz1PaperGridIndex delta left = wz1PaperGridIndex delta right →
        rootPlaneMap.planeMap left = rootPlaneMap.planeMap right)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hincidence : incidence ≤ first.power.requested.1 / 2)
    (hDeltaSmall : first.power.requested.1 ≤ 1 / 200)
    (input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) (localLoss := localLoss)
      (coefficient := (coefficient : ℝ))
      (bundle.initialRebalanced sourceLocalGrains rootCellwise
        (first.terminalMassPos hdeltaSmall)
        first.current.normalization.final_extremal.delta_pos hincidence)
      first.terminal.data.coarse_extremal.delta_pos) :
    proposition63FirstChartTerminalDensity first.power.requested.1 stickyLoss ≤
      proposition63CanonicalSliceDensity
        (Delta := first.power.requested.1) input := by
  have hmass := first.terminal.terminal_fiber_mass_lower input.parent
  have hmassEq : input.selectedFiber.mass =
      first.terminal.data.cover.toPaperTubeCover.fiberShadedMass
        first.terminal.data.refined input.parent := by
    exact completeFiberShading_mass_eq_fiberShadedMass
      first.terminal.data.cover first.terminal.data.refined input.parent
  have hmass' : Kakeya.realRpowENN first.power.requested.1 stickyLoss *
          (first.terminal.terminal.fiberFloor : ENNReal) *
          Kakeya.realRpowENN delta 2 ≤ input.selectedFiber.mass := by
    exact hmass.trans_eq hmassEq.symm
  have hcard : input.fiberFamily.family.enncard ≤
      2 * (first.terminal.terminal.fiberFloor : ENNReal) :=
    (first.terminal.terminal.fiber_cardinality input.parent).2.le
  exact proposition63FirstChartTerminalDensity_le_canonical input stickyLoss
    first.terminal.terminal.fiberFloor
    first.terminal.terminal.fiberFloor_pos hDeltaSmall
    (by simpa only [first.power.requested_eq] using
      first.power.tau_le_Delta_sq) hmass' hcard

/-- Exact ratio-power form of the generic terminal density. -/
theorem terminalDensity_eq_ratio_power :
    proposition63FirstChartTerminalDensity first.power.requested.1 stickyLoss =
      (400000000 : ENNReal)⁻¹ *
        Kakeya.realRpowENN first.power.h (sigma * stickyLoss) := by
  unfold proposition63FirstChartTerminalDensity
  congr 1
  have hDeltaEq : first.power.requested.1 =
      Real.rpow first.power.h (sigma / 2) :=
    first.power.requested_eq.trans first.power.scale_identity.symm
  rw [hDeltaEq]
  have hreal :
      (Real.rpow (Real.rpow first.power.h (sigma / 2)) stickyLoss) ^ 2 =
        Real.rpow first.power.h (sigma * stickyLoss) := by
    calc
      _ = Real.rpow
          (Real.rpow (Real.rpow first.power.h (sigma / 2)) stickyLoss)
          (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = Real.rpow (Real.rpow first.power.h (sigma / 2))
          (stickyLoss * 2) :=
        (Real.rpow_mul
          (Real.rpow_nonneg first.power.h_pos.le _) _ _).symm
      _ = Real.rpow first.power.h ((sigma / 2) * (stickyLoss * 2)) :=
        (Real.rpow_mul first.power.h_pos.le _ _).symm
      _ = Real.rpow first.power.h (sigma * stickyLoss) := by
        congr 1
        ring
  unfold Kakeya.realRpowENN
  calc
    ENNReal.ofReal
          (Real.rpow (Real.rpow first.power.h (sigma / 2)) stickyLoss) ^ 2 =
        ENNReal.ofReal
          ((Real.rpow (Real.rpow first.power.h (sigma / 2)) stickyLoss) ^ 2) := by
      rw [ENNReal.ofReal_pow]
      exact Real.rpow_nonneg (Real.rpow_nonneg first.power.h_pos.le _) _
    _ = ENNReal.ofReal (Real.rpow first.power.h (sigma * stickyLoss)) :=
      congrArg _ hreal

/-- Build the first chart from the same generic terminal and its canonical
metric fibre.  All scalar cutoff consequences are explicit hypotheses; this
module makes no schedule or cutoff choice. -/
theorem firstChartData
    {incidence commonSliceLoss chartLoss tau epsilon₁ epsilon₃ : ℝ}
    {coefficient : NNReal}
    {rootPlaneMap : PaperWZ1WeakPlaneMapData
      first.current.normalization.croppedRefined incidence}
    (bundle : Proposition63M9GenericFirstRichTerminalBundle
      first.terminal rootPlaneMap coefficient)
    (sourceLocalGrains : Proposition63InitialWeakLocalGrainData
      (incidence := incidence) first.current.normalization.croppedRefined sigma
        (Kakeya.realRpowENN delta (-localLoss)) coefficient)
    (rootCellwise : ∀ left right,
      wz1PaperGridIndex delta left = wz1PaperGridIndex delta right →
        rootPlaneMap.planeMap left = rootPlaneMap.planeMap right)
    (retainedFactor : ENNReal)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hincidence : incidence ≤ first.power.requested.1 / 2)
    (hDeltaPos : 0 < first.power.Delta)
    (hDeltaSmall : first.power.Delta ≤ 1 / 200)
    (hdeltaDelta : delta ≤ first.power.Delta ^ 2)
    (hdeltaRatio : delta / first.power.Delta ≤ 1 / 4)
    (hrhoOne : first.power.requested.1 ≤ 1)
    (hscaleSmall : delta / first.power.requested.1 ≤ 1 / 24)
    (hcommonLoss : stickyLoss ≤ commonSliceLoss)
    (hcommonLossPos : 0 < commonSliceLoss)
    (hchartLoss : stickyLoss ≤ chartLoss)
    (hchartLossPos : 0 < chartLoss)
    (hcommonDensityAbsorb :
      Kakeya.realRpowENN (delta / first.power.requested.1) commonSliceLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          proposition63FirstChartTerminalDensity
            first.power.requested.1 stickyLoss)
    (hchartDensityAbsorb :
      Kakeya.realRpowENN (delta / first.power.requested.1) chartLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          (proposition63FirstChartTerminalDensity
            first.power.requested.1 stickyLoss / 2)) :
    ∃ chart : Proposition63FirstChartData
        (localLoss := localLoss)
        (commonSliceLoss := commonSliceLoss)
        (chartLoss := chartLoss)
        (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
        (coefficient := (coefficient : ℝ)) first.terminal.data
        first.power.Delta retainedFactor,
      proposition63FirstChartTerminalDensity first.power.requested.1
          stickyLoss ≤ chart.sliceDensity := by
  let initial := bundle.initialLocalData sourceLocalGrains rootCellwise
    (first.terminalMassPos hdeltaSmall)
  let rebalanced := bundle.initialRebalanced sourceLocalGrains rootCellwise
    (first.terminalMassPos hdeltaSmall)
    first.current.normalization.final_extremal.delta_pos hincidence
  rcases first.metricFiberInputCanonical_exists bundle sourceLocalGrains
      rootCellwise hdeltaSmall hincidence with ⟨input, publicUnitBall⟩
  let sliceDensity := proposition63CanonicalSliceDensity
    (Delta := first.power.Delta) input
  have haggregate := proposition63CanonicalSliceDensity_spec
    (Delta := first.power.Delta) input
  have hterminalDensity :
      proposition63FirstChartTerminalDensity first.power.requested.1
          stickyLoss ≤ sliceDensity := by
    simpa only [sliceDensity, first.power.requested_eq] using
      first.terminalDensity_le_canonical bundle sourceLocalGrains rootCellwise
        hdeltaSmall hincidence
        (by simpa only [first.power.requested_eq] using hDeltaSmall) input
  have hcommonAbsorb :
      Kakeya.realRpowENN (delta / first.power.requested.1) commonSliceLoss *
            (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) * sliceDensity :=
    hcommonDensityAbsorb.trans (mul_le_mul_right hterminalDensity _)
  have hchartAbsorb :
      Kakeya.realRpowENN (delta / first.power.requested.1) chartLoss *
            (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) * (sliceDensity / 2) :=
    hchartDensityAbsorb.trans <| mul_le_mul_right
      (ENNReal.div_le_div_right hterminalDensity _) _
  rcases proposition63_common_slice_rescaled input hdeltaSmall hDeltaPos
      sliceDensity haggregate hcommonLoss hcommonLossPos hrhoOne hscaleSmall
      hcommonAbsorb with ⟨commonSlice⟩
  rcases proposition63_select_chart commonSlice hDeltaPos hDeltaSmall
      hdeltaDelta hdeltaRatio with ⟨chartSelection⟩
  rcases proposition63_chart_rescaled chartSelection hrhoOne hscaleSmall
      hchartLoss hchartLossPos hchartAbsorb with ⟨chartRescaled⟩
  let chart : Proposition63FirstChartData
      (localLoss := localLoss)
      (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss)
      (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
      (coefficient := (coefficient : ℝ)) first.terminal.data
      first.power.Delta retainedFactor := {
    delta_pos := first.current.normalization.final_extremal.delta_pos
    initial := initial
    rebalanced := rebalanced
    metricFiber := input
    public_unit_ball := publicUnitBall
    sliceDensity := sliceDensity
    commonSlice := commonSlice
    Delta_pos := hDeltaPos
    Delta_small := hDeltaSmall
    delta_le_Delta_sq := hdeltaDelta
    delta_div_Delta_small := hdeltaRatio
    chartSelection := chartSelection
    chartRescaled := chartRescaled
  }
  exact ⟨chart, by simpa [chart, sliceDensity] using hterminalDensity⟩

end Proposition63GenericFirstRichBoundaryData
end Kakeya.Assouad.PureWZ2
end
