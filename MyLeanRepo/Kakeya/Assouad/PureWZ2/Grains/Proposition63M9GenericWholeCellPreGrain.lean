import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9WholeCellCoarseGlobalGrain

/-! # Generic whole-cell dense root to pre-grain -/

noncomputable section
namespace Kakeya.Assouad.PureWZ2
namespace Proposition63GenericFirstRichBoundaryData

variable
    {delta sigma inputLoss normalizationLoss densityLoss currentLoss localLoss
      reentryLoss stickyLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent densityLoss}
    {preliminary : Proposition63PreliminaryLocalGrainData
      (localLoss := localLoss) (reentryLoss := currentLoss) root.normalization}
    {schedule : Proposition63RichStickyKernelScheduleData sigma stickyLoss}
    (first : Proposition63GenericFirstRichBoundaryData
      (reentryLoss := reentryLoss) root preliminary schedule)

/-- Attach an already constructed whole-cell dense root to a robust middle.
The generic first-rich boundary fixes every source and normalization index, so
the low-level whole-cell constructor never has to reconstruct them backwards
from the public rescaling output. -/
theorem GenericFirstChartDenseRootOutput.preGrainWholeCell
    {commonSliceLoss chartLoss targetLoss targetNormalizationLoss
      tau epsilon₁ epsilon₃ outputLoss : ℝ}
    {coefficient : NNReal} {retainedFactor : ENNReal}
    (chart : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := (coefficient : ℝ))
      first.terminal.data first.power.Delta retainedFactor)
    {denseNormalizationExponent : ℕ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    (dense : GenericFirstChartDenseRootOutput
      (targetLoss := targetLoss)
      (targetNormalizationLoss := targetNormalizationLoss)
      first chart denseNormalizationExponent)
    (hsourceLoss : targetLoss = cutoff.twoCall.schedule.first.sourceLoss)
    (hnormalizationLoss :
      targetNormalizationLoss =
        cutoff.twoCall.schedule.first.normalizationLoss)
    {pre : Proposition63PreLemma43DenseRootData
      (chart.wholeCellTraceOrdinarySource first.current.normalization
        dense.output dense.massLower)
      (chart.wholeCellTraceAmbient first.current.normalization
        dense.output dense.massLower)
      cutoff.twoCall.schedule.first.sourceLoss
      cutoff.twoCall.schedule.first.normalizationLoss denseNormalizationExponent}
    {hr : 0 < delta / first.power.requested.1}
    {hrRobust : delta / first.power.requested.1 ≤ cutoff.twoCall.rootCutoff}
    (middle : Proposition63M9RobustMiddleData cutoff
      (pre.robustRoot cutoff hr hrRobust) hr hrRobust)
    (slopes : chart.chartSelection.Proposition63SlopeData)
    (hsecondScale :
      (cutoff.twoCall.secondQRequested hr hrRobust).1 = first.power.Delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hglobalCost :
      Proposition63ChartSelectionData.proposition63WholeCellCoarseGlobalADConstant
          delta first.power.requested.1 first.power.Delta localLoss
            (coefficient : ℝ) ≤
        Kakeya.realRpowENN
          (cutoff.twoCall.secondQRequested hr hrRobust).1
          (-hierarchy.preGrainLoss)) :
    Nonempty (PureWZ2GeneralPreGrainData
      middle.second.lemma412.shading sigma hierarchy.preGrainLoss
      (Real.toNNReal (Real.rpow
        (cutoff.twoCall.secondQRequested hr hrRobust).1
        (-hierarchy.lemma47Loss)))
      (252000 * coefficient) 1) := by
  subst targetLoss
  subst targetNormalizationLoss
  simpa using Proposition63M9RobustMiddleData.preGrainWholeCell
    (delta := delta) (Delta := first.power.Delta) (sigma := sigma)
    (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
    (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
    (epsilon₃ := epsilon₃) (coefficient := (coefficient : ℝ))
    (firstScale := first.power.requested)
    (normalizationExponent := normalizationExponent)
    (denseNormalizationExponent := denseNormalizationExponent)
    (initialNormalized := first.current.normalization)
    (firstSticky := first.terminal.data) (retainedFactor := retainedFactor)
    (first := chart) (hierarchy := hierarchy) (cutoff := cutoff)
    (output := dense.output) (massLower := dense.massLower)
    (pre := pre) (hr := hr) (hrRobust := hrRobust) middle slopes
    first.power.requested_eq hsecondScale hsigma hsigmaOne hglobalCost

end Proposition63GenericFirstRichBoundaryData
end Kakeya.Assouad.PureWZ2
end
