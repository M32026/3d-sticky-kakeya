import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryAllBinNestedCriticalFloor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ReentryTraceFloorSchedule

/-!
# Scheduled ordinary all-bin closure from an exact re-entry trace

This bridge keeps the scalar schedule independent of the ordinary all-bin
geometry.  Once the runtime selected residue and its exact source re-entry are
known, it instantiates every critical-floor conversion scalar from the single
preselected schedule.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

namespace PureWZ2OrdinaryAllBinNestedRegionalData.SelectedBlockResidueData

variable
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta finalLoss
      theoremEta volumeLoss structuralBudget traceSourceLoss : ℝ}
    {logExponent normalizationExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {companions : PureWZ2OrdinaryAllBinOuterPopularCompanionData carriers}
    {regional : PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions}

/-- Apply the uniform scalar schedule to the exact ordinary trace of the
runtime source.  The only runtime loss obligations are that the current
cropped loss fits the scheduled density loss and that the retained ordinary
trace loss fits the scheduled source ceiling. -/
theorem toOneScaleDataOfReentryTraceSchedule
    (residueData : regional.SelectedBlockResidueData)
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) source.shading normalizationExponent
      traceSourceLoss inputLoss)
    (schedule : PureWZ2ReentryTraceFloorSchedule
      sigma finalLoss structuralBudget)
    (hinputDensity : inputLoss ≤ schedule.densityLoss)
    (htraceSource : traceSourceLoss ≤ schedule.traceSourceCeiling)
    (hdeltaSchedule : delta ≤ schedule.delta₀)
    (hdense : residueData.shading.IsLambdaDense
      (Kakeya.realRpowENN delta schedule.densityLoss)) :
    Nonempty (OneScaleData residueData) := by
  exact residueData.toOneScaleDataOfReentryTraceAndPureCriticalFloor
    reentry schedule.criticalFloor (schedule.lossConstant delta)
    (schedule.lossConstant_one source.extremal.delta_pos hdeltaSchedule)
    (schedule.lossConstant_ne_top delta) hinputDensity
    schedule.densityLoss_le_floor
    (hdeltaSchedule.trans schedule.delta₀_le_floor)
    (hdeltaSchedule.trans schedule.delta₀_le_twelve) hdense
    (schedule.trace_absorption delta source.extremal.delta_pos
      hdeltaSchedule traceSourceLoss reentry.sourceLoss_pos.le htraceSource)
    (schedule.cwa_absorption source.extremal.delta_pos).le
    (schedule.density_absorption source.extremal.delta_pos).le

/-- Compatibility projection which forgets the concrete selected residue. -/
theorem toOneScaleOfReentryTraceSchedule
    (residueData : regional.SelectedBlockResidueData)
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) source.shading normalizationExponent
      traceSourceLoss inputLoss)
    (schedule : PureWZ2ReentryTraceFloorSchedule
      sigma finalLoss structuralBudget)
    (hinputDensity : inputLoss ≤ schedule.densityLoss)
    (htraceSource : traceSourceLoss ≤ schedule.traceSourceCeiling)
    (hdeltaSchedule : delta ≤ schedule.delta₀)
    (hdense : residueData.shading.IsLambdaDense
      (Kakeya.realRpowENN delta schedule.densityLoss)) :
    Nonempty (PureWZ2LocallyLinearOneScaleData source finalLoss
      (pureWZ2SourceHorizontalFinalScale rho)) := by
  rcases residueData.toOneScaleDataOfReentryTraceSchedule reentry schedule
      hinputDensity htraceSource hdeltaSchedule hdense with ⟨data⟩
  exact ⟨data.oneScale⟩

end PureWZ2OrdinaryAllBinNestedRegionalData.SelectedBlockResidueData

end Kakeya.Assouad

end
