import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9SampledFirstRich
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FirstStage
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.NormalizedCardinalityFloor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9FirstChartDensity

/-!
# Metric-fibre input from the exact first-rich output

The preliminary M8 plane map is restricted through its current re-entry and
the first rich refinement.  This supplies the measurable, cellwise planiness
map without selecting a new witness.  The local-grain map is retained
separately, as allowed by `PropertyThreeSelectedInitialLocalData`.
-/

noncomputable section
namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

namespace Proposition63M9SampledFirstRichBoundaryData

variable
    {sigma outputLoss : Real}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    {aligned : Proposition63M9AlignedSampledStickyData cutoff}
    {normalizationWeight weightUpper : ENNReal}
    {nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := aligned.sticky.data.coarse)
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.stickyLoss))
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.selectedLoss))
      (proposition63CanonicalNearbyLevelCount
        cutoff.sampledM8RootLosses.stickyLoss)}
    {regularized : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) aligned.sticky.data nearbySchedule}
    {coefficient : Real} {K : Nat}
    {sampled : RegularizedAlignedSampledPlaninessData
      (coefficient := coefficient)
      (regularizedCompleteFiberCompatibleCover regularized)
      aligned.rootDelta_pos K}
    {preliminary : Proposition63M9SampledPreliminaryData
      cutoff regularized sampled}
    (first : Proposition63M9SampledFirstRichBoundaryData preliminary)

/-- The first power scale is small enough for the chart construction. -/
theorem powerDelta_small : first.power.Delta ≤ 1 / 200 := by
  rw [first.power.Delta_eq]
  exact cutoff.preliminaryAnalytic.first_power_small
    aligned.sticky.data.coarse_extremal.delta_pos <|
      aligned.scale_le_outerScaleCeiling.trans
        cutoff.outerScaleCeiling_le_preliminaryPropertyP

theorem powerDelta_pos : 0 < first.power.Delta := by
  rw [first.power.Delta_eq]
  exact Real.rpow_pos_of_pos
    aligned.sticky.data.coarse_extremal.delta_pos _

/-- The inherited preliminary incidence fits inside half of the first rich
coarse scale. -/
theorem preliminary_incidence_le_power_half :
    preliminary.preliminary.incidence ≤ first.power.Delta / 2 := by
  rw [preliminary.preliminary_incidence_eq]
  calc
    aligned.aligned.requested.1 ≤ first.power.Delta ^ 2 :=
      first.power.tau_le_Delta_sq
    _ ≤ first.power.Delta / 2 := by
      have hDelta := first.powerDelta_small
      have hDeltaNonnegative := first.powerDelta_pos.le
      nlinarith

/-- The first rich refinement has positive mass. -/
theorem refined_mass_pos : 0 < first.sticky.data.refined.mass := by
  have sourceSmall : aligned.aligned.requested.1 ≤ 1 / 24 :=
    aligned.scale_le_outerScaleCeiling.trans
      cutoff.outerScaleCeiling_le_preliminaryPropertyP |>.trans
        cutoff.preliminaryAnalytic.propertyPScale_small |>.trans (by norm_num)
  have sourceMass : 0 < first.current.normalization.croppedRefined.mass :=
    cropped_extremal_shading_mass_pos first.current.normalization.final_extremal
      first.current.normalization.line_class sourceSmall
  have sourceOne : aligned.aligned.requested.1 < 1 :=
    sourceSmall.trans_lt (by norm_num)
  have fractionPos := (pure_refinement_fraction_pos_ne_top
    aligned.sticky.data.coarse_extremal.delta_pos sourceOne 61).1
  exact (ENNReal.mul_pos fractionPos.ne' sourceMass.ne').trans_le
    first.sticky.data.retained_mass

/-- The preliminary root map restricted to the exact first-rich refinement. -/
noncomputable def restrictedRootPlaneMap : PaperWZ1WeakPlaneMapData
    first.sticky.data.refined aligned.aligned.requested.1 := by
  let currentMap := paperWeakPlaneMapRestrict preliminary.rootMap.planeMap
    preliminary.preliminary.subshading
  let selectedCurrentMap :=
    PaperWZ1WeakPlaneMapData.restrictSubfamily currentMap
      first.current.regularized.selected
  let normalizedMap := paperWeakPlaneMapRestrict selectedCurrentMap
    first.current.denseSubshading
  let selectedMap :=
    PaperWZ1WeakPlaneMapData.restrictSubfamily normalizedMap
      first.sticky.data.selected
  exact paperWeakPlaneMapRestrict selectedMap first.sticky.data.subshading

theorem refined_union_subset_root :
    first.sticky.data.refined.union ⊆
      preliminary.rootMap.root.normalization.croppedRefined.union := by
  intro point hpoint
  apply paperSubshading_union preliminary.preliminary.subshading
  apply first.current.normalization_croppedRefined_union_subset_current
  rcases hpoint with ⟨index, hindex⟩
  exact ⟨first.sticky.data.selected.embedding index,
    first.sticky.data.subshading index hindex⟩

theorem restrictedRootPlaneMap_lipschitz : LipschitzWith 1
    (fun point : {point : Point3 // point ∈ first.sticky.data.refined.union} =>
      first.restrictedRootPlaneMap.planeMap point) := by
  apply LipschitzWith.of_dist_le_mul
  intro left right
  simpa only [restrictedRootPlaneMap, paperWeakPlaneMapRestrict,
    PaperWZ1WeakPlaneMapData.restrictSubfamily, Subtype.dist_eq] using
      preliminary.rootMap.lipschitz.dist_le_mul
        ⟨left, first.refined_union_subset_root left.prop⟩
        ⟨right, first.refined_union_subset_root right.prop⟩

theorem restrictedRootPlaneMap_cellwise : ∀ left right,
    wz1PaperGridIndex aligned.aligned.requested.1 left =
        wz1PaperGridIndex aligned.aligned.requested.1 right →
      first.restrictedRootPlaneMap.planeMap left =
        first.restrictedRootPlaneMap.planeMap right := by
  intro left right sameCell
  simpa only [restrictedRootPlaneMap, paperWeakPlaneMapRestrict,
    PaperWZ1WeakPlaneMapData.restrictSubfamily] using
      preliminary.rootMap.cellwise left right sameCell

/-- Identity finite planiness on the exact first-rich refined shading.  It
uses the already fixed preliminary root map and loses no mass. -/
noncomputable def identityPlaniness : BalancedFinitePlaninessData
    (coefficient := (1 : ℝ)) first.sticky.data.refined where
  incidence := aligned.aligned.requested.1
  leftFactor := 1
  rightFactor := 1
  leftFactor_pos := by norm_num
  leftFactor_ne_top := by norm_num
  rightFactor_ne_top := by norm_num
  refinement := {
    shading := first.sticky.data.refined
    subshading := fun _ => Set.Subset.rfl
    cubical := first.sticky.data.refined_cubical
    planeMap := first.restrictedRootPlaneMap
    planeMap_cellwise := first.restrictedRootPlaneMap_cellwise
    lipschitz := by
      simpa using first.restrictedRootPlaneMap_lipschitz
    mass_retention := by simp
  }

/-- Package the original local-grain map and the restricted root map under
the shared preliminary incidence budget. -/
noncomputable def initialLocalData : PropertyThreeSelectedInitialLocalData
    (sigma := sigma) (outputLoss := cutoff.initial.localLoss)
    (coefficient := (1 : ℝ)) first.sticky.data.refined where
  planiness := first.identityPlaniness
  planiness_mass_pos := first.refined_mass_pos
  incidence := aligned.aligned.requested.1
  planiness_incidence_le := le_rfl
  incidence_nonnegative := aligned.sticky.data.coarse_extremal.delta_pos.le
  localGrains := by
    let restricted :=
      (first.localGrains.restrictSubfamily first.sticky.data.selected).restrict
        first.sticky.data.subshading
    simpa [identityPlaniness, preliminary.preliminary_incidence_eq,
      preliminary.preliminary_lipschitz_eq] using restricted

/-- The identity rebalancing used by the first metric-fibre selector.  Naming
it keeps the terminal mass/cardinality receipts definitionally attached to
the same rich shading. -/
noncomputable def initialRebalanced : Proposition63InitialRebalancedData
    first.sticky.data.balanced first.initialLocalData
    aligned.sticky.data.coarse_extremal.delta_pos where
  shading := first.sticky.data.refined
  subshading := fun _ => Set.Subset.rfl
  cubical := first.sticky.data.refined_cubical
  mass_pos := first.refined_mass_pos
  incidence_le_parent_half := by
    change aligned.aligned.requested.1 ≤ first.power.requested.1 / 2
    calc
      aligned.aligned.requested.1 = preliminary.preliminary.incidence :=
        preliminary.preliminary_incidence_eq.symm
      _ ≤ first.power.Delta / 2 :=
        first.preliminary_incidence_le_power_half
      _ = first.power.requested.1 / 2 := by
        rw [first.power.requested_eq]
  localGrains := first.initialLocalData.localGrains

/-- Select the complete metric fibre on the named identity rebalancing. -/
theorem metricFiberInputOnRebalanced_exists :
    ∃ input : Proposition63MetricFiberInputData
        (stickyLoss := cutoff.initial.stickyLoss)
        (localLoss := cutoff.initial.localLoss)
        (coefficient := (1 : ℝ)) first.initialRebalanced
        first.sticky.data.coarse_extremal.delta_pos,
      input.frozenRescaled.rescalingCertificate.publicFamily.IsInUnitBall := by
  let initial := first.initialLocalData
  let sourceDensity := proposition63CanonicalAmbientDensity initial
  have sourceDensitySpec :
      sourceDensity * first.sticky.data.selected.family.enncard *
          Kakeya.realRpowENN aligned.aligned.requested.1 2 =
        first.sticky.data.refined.mass :=
    proposition63CanonicalAmbientDensity_spec initial
      aligned.sticky.data.coarse_extremal.delta_pos
      first.sticky.data.selected_nonempty
  exact proposition63_metric_fiber_input_with_unit_ball
    first.terminal.canonical_rescaled_fiber
    first.terminal.canonical_rescaled_fiber_unit_ball
    first.initialRebalanced sourceDensity
      sourceDensitySpec.le first.sticky.data.coarse_extremal.nonempty

/-- The named mass-maximal metric fibre, with the canonical rich-terminal
rescaling witness selected in the same dependent choice. -/
noncomputable def metricFiberInputOnRebalanced :
    Proposition63MetricFiberInputData
      (stickyLoss := cutoff.initial.stickyLoss)
      (localLoss := cutoff.initial.localLoss)
      (coefficient := (1 : ℝ)) first.initialRebalanced
      first.sticky.data.coarse_extremal.delta_pos :=
  Classical.choose first.metricFiberInputOnRebalanced_exists

theorem metricFiberInputOnRebalanced_unit_ball :
    first.metricFiberInputOnRebalanced.frozenRescaled.rescalingCertificate.publicFamily.IsInUnitBall :=
  Classical.choose_spec first.metricFiberInputOnRebalanced_exists

/-- Compatibility existential form of the metric-fibre entry. -/
theorem metricFiberInput :
    ∃ rebalanced : Proposition63InitialRebalancedData
        first.sticky.data.balanced first.initialLocalData
        aligned.sticky.data.coarse_extremal.delta_pos,
      Nonempty (Proposition63MetricFiberInputData
        (stickyLoss := cutoff.initial.stickyLoss)
        (localLoss := cutoff.initial.localLoss)
        (coefficient := (1 : ℝ)) rebalanced
        first.sticky.data.coarse_extremal.delta_pos) := by
  exact ⟨first.initialRebalanced, ⟨first.metricFiberInputOnRebalanced⟩⟩

/-- The canonical common-slice density of the actual selected metric fibre
dominates the family-free terminal density.  Both the mass floor and the
cardinality upper bound come from the retained terminal of the same first
rich call. -/
theorem terminalDensity_le_canonical
    (input : Proposition63MetricFiberInputData
      (stickyLoss := cutoff.initial.stickyLoss)
      (localLoss := cutoff.initial.localLoss)
      (coefficient := (1 : ℝ)) first.initialRebalanced
      first.sticky.data.coarse_extremal.delta_pos) :
    proposition63FirstChartTerminalDensity first.power.requested.1
        cutoff.initial.stickyLoss ≤
      proposition63CanonicalSliceDensity
        (Delta := first.power.requested.1) input := by
  have hmass := first.terminal.terminal_fiber_mass_lower input.parent
  have hmassEq : input.selectedFiber.mass =
      first.sticky.data.cover.toPaperTubeCover.fiberShadedMass
        first.sticky.data.refined input.parent := by
    change (restrictPaperShading
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          first.sticky.data.selected.family
          (wz2PaperFullFiberIndices first.sticky.data.selected.family
            first.sticky.data.coarse input.parent))
        first.sticky.data.refined).mass = _
    exact completeFiberShading_mass_eq_fiberShadedMass
      first.sticky.data.cover first.sticky.data.refined input.parent
  have hmass' :
      Kakeya.realRpowENN first.power.requested.1
            cutoff.initial.stickyLoss *
            (first.terminal.terminal.fiberFloor : ENNReal) *
            Kakeya.realRpowENN aligned.aligned.requested.1 2 ≤
        input.selectedFiber.mass := by
    calc
      _ ≤ first.sticky.data.cover.toPaperTubeCover.fiberShadedMass
          first.sticky.data.refined input.parent := hmass
      _ = input.selectedFiber.mass := hmassEq.symm
  have hcard : input.fiberFamily.family.enncard ≤
      2 * (first.terminal.terminal.fiberFloor : ENNReal) := by
    exact (first.terminal.terminal.fiber_cardinality input.parent).2.le
  exact proposition63FirstChartTerminalDensity_le_canonical input
    cutoff.initial.stickyLoss first.terminal.terminal.fiberFloor
    first.terminal.terminal.fiberFloor_pos
    (by simpa only [first.power.requested_eq] using first.powerDelta_small)
    (by simpa only [first.power.requested_eq] using
      first.power.tau_le_Delta_sq) hmass' hcard

/-- Express the terminal density at the exact first-chart ratio
`h = tau / Delta`. -/
theorem terminalDensity_eq_ratio_power :
    proposition63FirstChartTerminalDensity first.power.requested.1
        cutoff.initial.stickyLoss =
      (400000000 : ENNReal)⁻¹ *
        Kakeya.realRpowENN first.power.h
          (sigma * cutoff.initial.stickyLoss) := by
  unfold proposition63FirstChartTerminalDensity
  congr 1
  have hDeltaEq : first.power.requested.1 =
      Real.rpow first.power.h (sigma / 2) :=
    first.power.requested_eq.trans first.power.scale_identity.symm
  rw [hDeltaEq]
  have hreal :
      (Real.rpow (Real.rpow first.power.h (sigma / 2))
          cutoff.initial.stickyLoss) ^ 2 =
        Real.rpow first.power.h
          (sigma * cutoff.initial.stickyLoss) := by
    calc
      (Real.rpow (Real.rpow first.power.h (sigma / 2))
          cutoff.initial.stickyLoss) ^ 2 =
        Real.rpow
          (Real.rpow (Real.rpow first.power.h (sigma / 2))
            cutoff.initial.stickyLoss) (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
      _ = Real.rpow (Real.rpow first.power.h (sigma / 2))
          (cutoff.initial.stickyLoss * 2) :=
        (Real.rpow_mul
          (Real.rpow_nonneg first.power.h_pos.le _) _ _).symm
      _ = Real.rpow first.power.h
          ((sigma / 2) * (cutoff.initial.stickyLoss * 2)) :=
        (Real.rpow_mul first.power.h_pos.le _ _).symm
      _ = Real.rpow first.power.h
          (sigma * cutoff.initial.stickyLoss) := by congr 1 <;> ring
  unfold Kakeya.realRpowENN
  calc
    ENNReal.ofReal
          (Real.rpow (Real.rpow first.power.h (sigma / 2))
            cutoff.initial.stickyLoss) ^ 2 =
        ENNReal.ofReal
          ((Real.rpow (Real.rpow first.power.h (sigma / 2))
            cutoff.initial.stickyLoss) ^ 2) := by
              rw [ENNReal.ofReal_pow]
              exact Real.rpow_nonneg (Real.rpow_nonneg first.power.h_pos.le _) _
    _ = ENNReal.ofReal
          (Real.rpow first.power.h
            (sigma * cutoff.initial.stickyLoss)) := congrArg _ hreal

/-- Build the retained first-chart package directly from the exact first-rich
output.  Both density absorptions are paid by the pre-runtime M9 cutoff and
the retained terminal fibre certificate. -/
theorem firstChartData
    {tau epsilon₁ epsilon₃ : ℝ}
    (retainedFactor : ENNReal) :
    ∃ chart : Proposition63FirstChartData
        (localLoss := cutoff.initial.localLoss)
        (commonSliceLoss := cutoff.initial.localLoss)
        (chartLoss := cutoff.initial.lemma43SourceLoss)
        (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
        (coefficient := (1 : ℝ)) first.sticky.data first.power.Delta
        retainedFactor,
      proposition63FirstChartTerminalDensity first.power.requested.1
          cutoff.initial.stickyLoss ≤ chart.sliceDensity := by
  let rebalanced := first.initialRebalanced
  let input := first.metricFiberInputOnRebalanced
  let sliceDensity := proposition63CanonicalSliceDensity
    (Delta := first.power.Delta) input
  have hdeltaSmall : aligned.aligned.requested.1 ≤ 1 / 24 :=
    aligned.scale_le_outerScaleCeiling.trans
      cutoff.outerScaleCeiling_le_preliminaryPropertyP |>.trans
        cutoff.preliminaryAnalytic.propertyPScale_small |>.trans (by norm_num)
  have hscaleSmall :
      aligned.aligned.requested.1 / first.power.requested.1 ≤ 1 / 24 := by
    rw [first.power.requested_eq]
    calc
      aligned.aligned.requested.1 / first.power.Delta ≤
          first.power.Delta := by
        apply (div_le_iff₀ first.powerDelta_pos).2
        simpa [pow_two] using first.power.tau_le_Delta_sq
      _ ≤ 1 / 200 := first.powerDelta_small
      _ ≤ 1 / 24 := by norm_num
  have hdeltaRatio :
      aligned.aligned.requested.1 / first.power.Delta ≤ 1 / 4 := by
    rw [← first.power.requested_eq]
    exact hscaleSmall.trans (by norm_num : (1 / 24 : ℝ) ≤ 1 / 4)
  have hrhoOne : first.power.requested.1 ≤ 1 :=
    first.power.requested.2.2
  have hcommonLoss : cutoff.initial.stickyLoss ≤
      cutoff.initial.localLoss := cutoff.initial.sticky_lt_local.le
  have hcommonLossPos : 0 < cutoff.initial.localLoss :=
    cutoff.initial.sticky_pos.trans cutoff.initial.sticky_lt_local
  have hchartLoss : cutoff.initial.stickyLoss ≤
      cutoff.initial.lemma43SourceLoss :=
    cutoff.initial.sticky_lt_local.le.trans
      cutoff.initial.local_lt_lemma43.le
  have hchartLossPos : 0 < cutoff.initial.lemma43SourceLoss :=
    hcommonLossPos.trans cutoff.initial.local_lt_lemma43
  have haggregate := proposition63CanonicalSliceDensity_spec
    (Delta := first.power.Delta) input
  have hterminalDensity :
      proposition63FirstChartTerminalDensity first.power.requested.1
          cutoff.initial.stickyLoss ≤ sliceDensity :=
    by
      simpa only [sliceDensity, first.power.requested_eq] using
        first.terminalDensity_le_canonical input
  have hterminalRatio :
      proposition63FirstChartTerminalDensity first.power.requested.1
          cutoff.initial.stickyLoss =
        (400000000 : ENNReal)⁻¹ *
          Kakeya.realRpowENN first.power.h
            (sigma * cutoff.initial.stickyLoss) :=
    first.terminalDensity_eq_ratio_power
  have hratioEq : aligned.aligned.requested.1 /
      first.power.requested.1 = first.power.h := by
    rw [first.power.requested_eq, first.power.h_eq]
  have hratioCutoff : first.power.h ≤
      cutoff.firstChartDensity.delta₀ := by
    calc
      first.power.h = aligned.aligned.requested.1 /
          first.power.requested.1 := hratioEq.symm
      _ ≤ first.power.Delta := by
        rw [first.power.requested_eq]
        apply (div_le_iff₀ first.powerDelta_pos).2
        simpa [pow_two] using first.power.tau_le_Delta_sq
      _ ≤ cutoff.firstChartDensity.delta₀ := by
        rw [first.power.Delta_eq]
        exact cutoff.firstChartPower_le_densityCutoff
          aligned.sticky.data.coarse_extremal.delta_pos
          aligned.scale_le_outerScaleCeiling
  have hcommonDensityAbsorb :
      Kakeya.realRpowENN first.power.h cutoff.initial.localLoss *
            (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) * sliceDensity := by
    calc
      _ ≤ ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ((400000000 : ENNReal)⁻¹ *
              Kakeya.realRpowENN first.power.h
                (sigma * cutoff.initial.stickyLoss)) :=
        cutoff.firstChartDensity.common_density first.power.h_pos hratioCutoff
      _ = ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            proposition63FirstChartTerminalDensity first.power.requested.1
              cutoff.initial.stickyLoss := by rw [hterminalRatio]
      _ ≤ _ := mul_le_mul_left' hterminalDensity _
  have hchartDensityAbsorb :
      Kakeya.realRpowENN first.power.h
            cutoff.initial.lemma43SourceLoss *
            (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) * (sliceDensity / 2) := by
    calc
      _ ≤ ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            (((400000000 : ENNReal)⁻¹ *
              Kakeya.realRpowENN first.power.h
                (sigma * cutoff.initial.stickyLoss)) / 2) :=
        cutoff.firstChartDensity.chart_density first.power.h_pos hratioCutoff
      _ = ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            (proposition63FirstChartTerminalDensity first.power.requested.1
              cutoff.initial.stickyLoss / 2) := by rw [hterminalRatio]
      _ ≤ _ := mul_le_mul_left'
        (ENNReal.div_le_div_right hterminalDensity _) _
  rcases proposition63_common_slice_rescaled input hdeltaSmall
      first.powerDelta_pos sliceDensity haggregate hcommonLoss
      hcommonLossPos hrhoOne hscaleSmall
      (by simpa only [hratioEq] using hcommonDensityAbsorb) with
    ⟨commonSlice⟩
  rcases proposition63_select_chart commonSlice first.powerDelta_pos
      first.powerDelta_small first.power.tau_le_Delta_sq hdeltaRatio with
    ⟨chartSelection⟩
  rcases proposition63_chart_rescaled chartSelection hrhoOne hscaleSmall
      hchartLoss hchartLossPos
      (by simpa only [hratioEq] using hchartDensityAbsorb) with
    ⟨chartRescaled⟩
  have publicUnitBall :
      input.frozenRescaled.rescalingCertificate.publicFamily.IsInUnitBall := by
    exact first.metricFiberInputOnRebalanced_unit_ball
  let chart : Proposition63FirstChartData
      (localLoss := cutoff.initial.localLoss)
      (commonSliceLoss := cutoff.initial.localLoss)
      (chartLoss := cutoff.initial.lemma43SourceLoss)
      (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
      (coefficient := (1 : ℝ)) first.sticky.data first.power.Delta
      retainedFactor := {
    delta_pos := aligned.sticky.data.coarse_extremal.delta_pos
    initial := first.initialLocalData
    rebalanced := rebalanced
    metricFiber := input
    public_unit_ball := publicUnitBall
    sliceDensity := sliceDensity
    commonSlice := commonSlice
    Delta_pos := first.powerDelta_pos
    Delta_small := first.powerDelta_small
    delta_le_Delta_sq := first.power.tau_le_Delta_sq
    delta_div_Delta_small := hdeltaRatio
    chartSelection := chartSelection
    chartRescaled := chartRescaled
  }
  exact ⟨chart, by simpa [chart, sliceDensity] using hterminalDensity⟩

/-- The trace-aware density absorption for the actual first chart.  The
outer root loss appearing in the normalization is converted to the exact
post-chart ratio by `Proposition63PowerScale.root_power_eq_ratio_power`. -/
theorem firstChartTraceDensityAbsorb
    {tau epsilon₁ epsilon₃ : ℝ}
    {retainedFactor : ENNReal}
    (chart : Proposition63FirstChartData
      (localLoss := cutoff.initial.localLoss)
      (commonSliceLoss := cutoff.initial.localLoss)
      (chartLoss := cutoff.initial.lemma43SourceLoss)
      (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
      (coefficient := (1 : ℝ)) first.sticky.data first.power.Delta
      retainedFactor)
    (terminalDensity :
      proposition63FirstChartTerminalDensity first.power.requested.1
          cutoff.initial.stickyLoss ≤ chart.sliceDensity) :
    Kakeya.realRpowENN first.power.h
          cutoff.initial.lemma43SourceLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
      ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
        ((100 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN aligned.aligned.requested.1
            cutoff.firstRichSchedule.sourceLoss / 2) *
          (chart.sliceDensity / 2)) := by
  have hratioCutoff : first.power.h ≤
      cutoff.firstChartTraceDensity.delta₀ := by
    calc
      first.power.h = aligned.aligned.requested.1 /
          first.power.requested.1 := by
        rw [first.power.requested_eq, first.power.h_eq]
      _ ≤ first.power.Delta := by
        rw [first.power.requested_eq]
        apply (div_le_iff₀ first.powerDelta_pos).2
        simpa [pow_two] using first.power.tau_le_Delta_sq
      _ ≤ cutoff.firstChartTraceDensity.delta₀ := by
        rw [first.power.Delta_eq]
        exact cutoff.firstChartPower_le_traceDensityCutoff
          aligned.sticky.data.coarse_extremal.delta_pos
          aligned.scale_le_outerScaleCeiling
  have traceBound := cutoff.firstChartTraceDensity.trace_density
    first.power.h_pos hratioCutoff
  have inputPower :
      Kakeya.realRpowENN aligned.aligned.requested.1
          cutoff.firstRichSchedule.sourceLoss =
        Kakeya.realRpowENN first.power.h
          ((1 + sigma / 2) * cutoff.firstRichSchedule.sourceLoss) :=
    first.power.root_power_eq_ratio_power
  have terminalDensity :
      ((400000000 : ENNReal)⁻¹ *
          Kakeya.realRpowENN first.power.h
            (sigma * cutoff.initial.stickyLoss)) ≤
        chart.sliceDensity := by
    simpa only [← first.terminalDensity_eq_ratio_power] using terminalDensity
  calc
    _ ≤ ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
        ((100 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN first.power.h
            ((1 + sigma / 2) * cutoff.firstRichSchedule.sourceLoss) / 2) *
          (((400000000 : ENNReal)⁻¹ *
            Kakeya.realRpowENN first.power.h
              (sigma * cutoff.initial.stickyLoss)) / 2)) := traceBound
    _ ≤ _ := by
      rw [inputPower]
      gcongr

end Proposition63M9SampledFirstRichBoundaryData

end Kakeya.Assouad.PureWZ2
end
