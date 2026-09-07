import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9NestedFirstChart
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9GenericDenseRootScalarBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9GenericWholeCellPreGrain
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9NestedGlobalCost
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9NestedTailScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RobustMiddleSourceGeometry

/-! # Stable source output of the nested M9 pre-grain construction -/

noncomputable section
namespace Kakeya.Assouad.PureWZ2

/-- The paper-ordered construction through Lemma 4.12 and the honest
whole-cell global estimate, with only the data needed by the final mild
rescaling exposed. -/
structure Proposition63M9NestedPreGrainSourceData
    (sigma sourceLoss sourceDeltaCutoff : ℝ) where
  delta : ℝ
  delta_pos : 0 < delta
  delta_le_cutoff : delta ≤ sourceDeltaCutoff
  family : Kakeya.Streamlined.TubeFamily delta
  shading : WZ1PaperTubeShading family
  Lplane : NNReal
  Lslope : NNReal
  preGrain : PureWZ2GeneralPreGrainData shading sigma sourceLoss
    Lplane Lslope 1
  slope_bound : ∀ height, |preGrain.slope height| ≤ 3
  planeMap_vertical_bound : ∀ point,
    |preGrain.planeMap point (2 : Fin 3)| ≤ 1 / 2
  ancestorSourceLoss : ℝ
  ancestorSourceLoss_le_sourceLoss :
    ancestorSourceLoss ≤ sourceLoss
  ancestorNormalizationLoss : ℝ
  ancestorShading : WZ1PaperTubeShading family
  ancestorReentry : PureWZ2PropStickyReentryData
    (sigma := sigma) ancestorShading 0 ancestorSourceLoss
    ancestorNormalizationLoss
  shading_sub_ancestor : PaperIsSubshading shading
    ancestorShading
  extremal : WZ2PaperCroppedIsExtremal sigma sourceLoss family shading
  lineClass : WZ1PaperIsLineClass family
  essentiallyDistinct : WZ1PaperIsEssentiallyDistinct family
  midpoint_le_three : ∀ index,
    ‖wz2PaperTubeMidpoint (family.tube index)‖ ≤ 3
  plane_le_power : Lplane ≤
    Real.toNNReal (Real.rpow delta (-sourceLoss))
  slope_le_power : Lslope ≤
    Real.toNNReal (Real.rpow delta (-sourceLoss))

namespace Proposition63M9NestedPreGrainSourceData

variable {sigma sourceLoss sourceDeltaCutoff : ℝ}
    (data : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)

/-- Common Lipschitz bound used by the final power-scale rescaling. -/
noncomputable def tailLipschitz : NNReal :=
  Real.toNNReal (Real.rpow data.delta (-sourceLoss))

/-- The source loss paid by the final mild-rescaling stage. -/
def tailSourceLoss (_data : Proposition63M9NestedPreGrainSourceData
    sigma sourceLoss sourceDeltaCutoff) : ℝ := 4 * sourceLoss

theorem sourceLoss_le_tailSourceLoss (hsourceLoss : 0 < sourceLoss) :
    sourceLoss ≤ data.tailSourceLoss := by
  unfold tailSourceLoss
  linarith

/-- Loss-weakened extremality on the exact same source family and shading. -/
theorem tailExtremal (hsourceLoss : 0 < sourceLoss) :
    WZ2PaperCroppedIsExtremal sigma data.tailSourceLoss
      data.family data.shading :=
  data.extremal.mono_loss (data.sourceLoss_le_tailSourceLoss hsourceLoss)

/-- Tail-ready pre-grain: same maps and shading, with both Lipschitz constants
weakened to the common power bound and the AD loss relabelled from `p` to
`4p`. -/
def tailPreGrain (hsourceLoss : 0 < sourceLoss) :
    PureWZ2GeneralPreGrainData data.shading sigma data.tailSourceLoss
      data.tailLipschitz data.tailLipschitz 1 :=
  (data.preGrain.weakenLoss data.delta_pos data.extremal.delta_le_one
    (data.sourceLoss_le_tailSourceLoss hsourceLoss)).weakenLipschitz
      data.plane_le_power data.slope_le_power

/-- Loss and Lipschitz weakening do not replace the source plane map. -/
theorem tailPreGrain_planeMap_vertical_bound
    (hsourceLoss : 0 < sourceLoss) :
    ∀ point, |(data.tailPreGrain hsourceLoss).planeMap point (2 : Fin 3)| ≤
      1 / 2 := by
  intro point
  exact data.planeMap_vertical_bound point

/-- Loss and Lipschitz weakening do not replace the chart-normalized slope. -/
theorem tailPreGrain_slope_bound
    (hsourceLoss : 0 < sourceLoss) :
    ∀ height, |(data.tailPreGrain hsourceLoss).slope height| ≤ 3 := by
  intro height
  exact data.slope_bound height

end Proposition63M9NestedPreGrainSourceData

/-- Run the complete nested robust construction up to the source pre-grain.
The supplied cutoff bounds the final source scale, not the earlier critical
root; its power preimage is chosen before the critical sequence is queried. -/
theorem proposition63_m9_nested_preGrain_source
    {sigma outputLoss sourceDeltaCutoff : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (schedule : Proposition63M9NestedScheduleData sigma outputLoss critical)
    (hsourceDeltaCutoff : 0 < sourceDeltaCutoff) :
    Nonempty (Proposition63M9NestedPreGrainSourceData
      sigma schedule.outer.preGrainLoss sourceDeltaCutoff) := by
  have powerExponentPos : 0 < sigma / (2 + sigma) := by
    exact div_pos critical.sigma_pos (by linarith [critical.sigma_pos])
  rcases pure_wz2_exists_delta₀_rpow_le hsourceDeltaCutoff powerExponentPos with
    ⟨qCutoff, qCutoffPos, _qCutoffOne, qPowerLe⟩
  let externalCutoff := min schedule.outerCutoff.outerScaleCeiling <|
    min schedule.outerRootCutoff qCutoff
  have externalCutoffPos : 0 < externalCutoff := by
    exact lt_min schedule.outerCutoff.outerScaleCeiling_pos <|
      lt_min schedule.outerRootCutoff_pos qCutoffPos
  rcases proposition63_m9_robust_initial_preliminary critical schedule.inner
      schedule.innerCutoff externalCutoff externalCutoffPos with ⟨data⟩
  let q := (schedule.innerCutoff.twoCall.secondQRequested data.r_pos
    data.r_le_robustCutoff).1
  have hqOuter : q ≤ schedule.outerCutoff.outerScaleCeiling :=
    data.q_le_external.trans (min_le_left _ _)
  have hqOuterRoot : q ≤ schedule.outerRootCutoff :=
    data.q_le_external.trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have hqTailRoot : q ≤ qCutoff :=
    data.q_le_external.trans <|
      (min_le_right _ _).trans (min_le_right _ _)
  rcases data.runOuterFirstRich hqOuter with ⟨first⟩
  rcases data.runOuterFirstChart first with ⟨chart, terminalDensity⟩
  rcases first.firstChartDenseRootCanonical schedule.outerCutoff chart
      terminalDensity hqOuter critical.sigma_lt_one with ⟨dense⟩
  let pre := Classical.choice dense.denseRoot
  have ratioEq : q / first.power.requested.1 = first.power.h := by
    rw [first.power.requested_eq]
    exact first.power.h_eq.symm
  have radiusPos : 0 < q / first.power.requested.1 := by
    simpa only [ratioEq] using first.power.h_pos
  have radiusScale : q / first.power.requested.1 ≤
      schedule.outerCutoff.scaleCeiling := by
    simpa only [ratioEq] using schedule.firstChart_h_le_outer_scale
      first.current.normalization.final_extremal.delta_pos hqOuterRoot
      first.power
  have radiusRobust : q / first.power.requested.1 ≤
      schedule.outerCutoff.twoCall.rootCutoff := by
    simpa only [ratioEq] using schedule.firstChart_h_le_outer_robust
      first.current.normalization.final_extremal.delta_pos hqOuterRoot
      first.power
  have robustIncidenceOuter :
      proposition63M9RobustLemma43Incidence
          (q / first.power.requested.1) sigma ≤
        schedule.outerCutoff.outerScaleCeiling :=
    schedule.outerCutoff.robustIncidence_le_outerScaleCeiling radiusPos
      radiusScale
  rcases schedule.outerCutoff.runRobustMiddleOfPreVertical pre radiusPos
      radiusRobust robustIncidenceOuter with ⟨middle, middleVertical⟩
  rcases chart.chartSelection.slope_extension first.power.requested_eq with
    ⟨slopes⟩
  have secondScaleEq :
      (schedule.outerCutoff.twoCall.secondQRequested
        radiusPos radiusRobust).1 = first.power.Delta := by
    rw [schedule.outerCutoff.twoCall.secondQRequested_value]
    simpa only [proposition63M9RobustLemma43Incidence, ratioEq] using
      first.power.scale_identity
  have globalCost :
      Proposition63ChartSelectionData.proposition63WholeCellCoarseGlobalADConstant
          q first.power.requested.1 first.power.Delta
          schedule.outerCutoff.initial.localLoss
          (data.outerPreliminary.lipschitz : ℝ) ≤
        Kakeya.realRpowENN
          (schedule.outerCutoff.twoCall.secondQRequested
            radiusPos radiusRobust).1
          (-schedule.outer.preGrainLoss) := by
    rw [secondScaleEq]
    exact data.outerGlobalCost first
  rcases middle.preGrainWholeCellWithPlaneMap slopes
      first.power.requested_eq secondScaleEq
      critical.sigma_pos critical.sigma_lt_one globalCost with
    ⟨preGrain, preGrainPlaneMap, preGrainSlope⟩
  have deltaLe : first.power.Delta ≤ sourceDeltaCutoff := by
    rw [first.power.Delta_eq]
    exact qPowerLe q
      first.current.normalization.final_extremal.delta_pos hqTailRoot
  have coefficientLe := data.outerPreliminary_coefficient_bound hqOuter
  exact ⟨{
    delta := (schedule.outerCutoff.twoCall.secondQRequested
      radiusPos radiusRobust).1
    delta_pos := middle.second.lemma412.extremal.delta_pos
    delta_le_cutoff := by simpa only [secondScaleEq] using deltaLe
    family := middle.second.sticky.coarse
    shading := middle.second.lemma412.shading
    Lplane := Real.toNNReal
      (Real.rpow
        (schedule.outerCutoff.twoCall.secondQRequested
          radiusPos radiusRobust).1
        (-schedule.outer.lemma47Loss))
    Lslope := 252000 * Real.toNNReal
      (data.outerPreliminary.lipschitz : ℝ)
    preGrain := preGrain
    slope_bound := by
      intro height
      rw [preGrainSlope height]
      exact slopes.bounded (100 * height)
    planeMap_vertical_bound := by
      intro point
      rw [preGrainPlaneMap point]
      exact middle.lemma412_planeMap_vertical_bound middleVertical point
    ancestorSourceLoss := middle.secondTerminal.coarseSourceLoss
    ancestorSourceLoss_le_sourceLoss := by
      have coarseLeSticky :
          middle.secondTerminal.coarseSourceLoss ≤
            schedule.outer.stickyLoss := by
        linarith [middle.secondTerminal.coarseSourceLoss_budget,
          middle.secondTerminal.coarseSourceLoss_pos]
      exact coarseLeSticky.trans <|
        (schedule.outer.sticky_lt_lemma44.trans <|
          schedule.outer.lemma44_lt_lemma47.trans
            schedule.outer.lemma47Loss_lt_preGrain).le
    ancestorNormalizationLoss :=
      middle.secondTerminal.coarseNormalizationLoss
    ancestorShading := middle.second.sticky.croppedCoarseShading
    ancestorReentry := middle.terminalCoarseReentry
    shading_sub_ancestor := by
      intro index point pointMem
      exact middle.second.lemma44.coarse_subshading index
        (middle.second.lemma47.subshading index
          (middle.second.lemma412.subshading index pointMem))
    extremal := middle.second.lemma412.extremal
    lineClass := middle.lemma412Source_lineClass
    essentiallyDistinct := middle.lemma412Source_essentiallyDistinct
    midpoint_le_three := middle.lemma412Source_midpoint_le_three
    plane_le_power := by
      rw [secondScaleEq]
      exact data.outerPlaneLipschitz_le_preGrainPower first
    slope_le_power := by
      rw [secondScaleEq]
      simpa using data.outerSlopeLipschitz_le_preGrainPower first
        data.outerPreliminary.lipschitz coefficientLe
  }⟩

end Kakeya.Assouad.PureWZ2
end
