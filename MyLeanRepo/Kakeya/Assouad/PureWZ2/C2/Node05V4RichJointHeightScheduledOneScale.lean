import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightScalarSchedule

/-!
# Scheduled production call for the assembled joint-height one-scale output

This module is the first production consumer of the joint density threshold.
It discharges the complete aggregate `habsorb` and calls the assembled
re-entry-trace one-scale theorem.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

namespace PureWZ2Node05V4RichJointAggregatedShadingData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta finalLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {B₀ threshold : ENNReal}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    {family : PureWZ2Node05V4RichJointBlockFamily
      (eta := eta) pullback B₀ threshold hbridge projection}
    {residue : PureWZ2Node05V4RichJointBlockResidueData family}
    (aggregated : PureWZ2Node05V4RichJointAggregatedShadingData residue)

/-- Execute the assembled P3 output using only pre-runtime scalar schedules
and the actual direct-rich runtime witnesses. -/
theorem scheduledOneScale
    {sourceLossCeiling scaleLoss structuralBudget requestedLoss
      densityFinalLoss : ℝ}
    (geometry : PureWZ2Node05V4RichJointAggregatedGeometryData aggregated)
    (floorSchedule : PureWZ2ReentryTraceFloorSchedule
      sigma requestedLoss structuralBudget)
    (densityThreshold : PureWZ2Node05V4RichJointDensityThreshold
      sourceLossCeiling floorSchedule.densityLoss densityFinalLoss scaleLoss)
    (hdensityFinal : densityFinalLoss = finalLoss)
    (hfinalRequested : finalLoss ≤ requestedLoss)
    (hinputSource : inputLoss ≤ sourceLossCeiling)
    (hinputDensity : inputLoss ≤ floorSchedule.densityLoss)
    (htraceSource :
      current.ordinaryLoss ≤ floorSchedule.traceSourceCeiling)
    (hdeltaFloor : delta ≤ floorSchedule.delta₀)
    (hdeltaThreshold : delta ≤ densityThreshold.delta₀)
    (hrhoThreshold : rho ≤ densityThreshold.rho₀)
    (hdeltaRho : delta ≤ rho)
    (hscaleLower : Real.rpow delta (1 - scaleLoss) ≤ rho)
    (hgraphOne : 256 * rho ≤ 1)
    (hrhoSmall : rhoRequested.1 ≤ 1 / 12) :
    Nonempty (PureWZ2LocallyLinearOneScaleData
      current.grain requestedLoss geometry.scale) := by
  subst densityFinalLoss
  have hregularity :
      (twoScale.first.fourDegreeReceipts.regularity : ENNReal) ≤
        Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 :=
    twoScale.first.rich.terminal_regularity_bound
  have habsorbRuntime :=
    densityThreshold.absorb hinputSource current.grain.extremal.delta_pos
      hdeltaThreshold
      (by
        rw [← pullback.rhoRequested_eq]
        exact twoScale.first.publicSticky.coarse_extremal.delta_pos)
      hrhoThreshold hdeltaRho hscaleLower hregularity
  have habsorb :
      (128 *
          (twoScale.first.fourDegreeReceipts.regularity : ENNReal) ^ 4 *
          pureWZ2Node05V4RichJointBlockCost rho) *
          Kakeya.realRpowENN delta floorSchedule.densityLoss ≤
        (wz2PaperPureRefinementFraction delta 61 *
          wz2PaperPureRefinementFraction rhoRequested.1 61 *
          Kakeya.realRpowENN delta inputLoss) *
          pureWZ2Node05V4RichJointGain rho finalLoss := by
    simpa only [pullback.rhoRequested_eq] using habsorbRuntime
  have hdense := aggregated.dense_of_relative_mass hrhoSmall
    floorSchedule.densityLoss
    (pureWZ2Node05V4RichJointGain rho finalLoss)
    (pureWZ2Node05V4RichJointBlockCost rho)
    (fun heightIndex => (family.theorem52 heightIndex).gain_eq.le)
    (fun heightIndex =>
      (family.prepared heightIndex).volumePopular.blockCost_le hgraphOne)
    (pureWZ2Node05V4RichJointBlockCost_pos
      (by
        rw [← pullback.rhoRequested_eq]
        exact twoScale.first.publicSticky.coarse_extremal.delta_pos)
      hgraphOne)
    (pureWZ2Node05V4RichJointBlockCost_ne_top rho) habsorb
  exact pureWZ2_literalCurrentSourceOneScale_of_reentryTrace
    aggregated.shading aggregated.subshading_current aggregated.whole_cells
    floorSchedule hinputDensity htraceSource hdeltaFloor hdense current.reentry
    (PureWZ2Node05V4RichJointBlockResidueData.toLiteralGeometryMono
      residue geometry hfinalRequested)

end PureWZ2Node05V4RichJointAggregatedShadingData

end Kakeya.Assouad

end
