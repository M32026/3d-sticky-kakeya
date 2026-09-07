import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9GenericFirstChart
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9WholeCellTraceRoot
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9FirstChartCardinality
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9FirstChartCutoff

/-! # Generic dense-root output for the first chart -/

noncomputable section
namespace Kakeya.Assouad.PureWZ2
open MeasureTheory Set

private theorem genericTubeSubfamily_card_le_ambient
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family) :
    selected.family.card ≤ family.card := by
  simpa using
    Fintype.card_le_of_injective selected.embedding selected.embedding.injective

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

abbrev GenericFirstChartWholeCellOutput
    {commonSliceLoss chartLoss tau epsilon₁ epsilon₃ : ℝ}
    {coefficient : NNReal} {retainedFactor : ENNReal}
    (chart : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := (coefficient : ℝ))
      first.terminal.data first.power.Delta retainedFactor) :=
  WZ2PaperPureRescaledFullFiberOutput
    (sigma := sigma) (loss := chartLoss)
    (chart.wholeCellShading first.current.normalization)
    (first.terminal.data.coarse.tube chart.metricFiber.parent)
    first.terminal.data.coarse_extremal.delta_pos

abbrev GenericFirstChartTraceMassLower
    {commonSliceLoss chartLoss tau epsilon₁ epsilon₃ : ℝ}
    {coefficient : NNReal} {retainedFactor : ENNReal}
    (chart : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := (coefficient : ℝ))
      first.terminal.data first.power.Delta retainedFactor)
    (output : GenericFirstChartWholeCellOutput first chart) :=
  Kakeya.realRpowENN (delta / first.power.requested.1) chartLoss *
        output.rescalingCertificate.publicFamily.toBodyFamily.mass ≤
    (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
        ENNReal.ofReal ((1 / first.power.requested.1 : ℝ) ^ 2)) *
      (chart.wholeCellOrdinaryTrace first.current.normalization).mass

/-- Generic equivalent of the sampled dense-root output record. -/
structure GenericFirstChartDenseRootOutput
    {commonSliceLoss chartLoss targetLoss targetNormalizationLoss
      tau epsilon₁ epsilon₃ : ℝ}
    {coefficient : NNReal} {retainedFactor : ENNReal}
    (chart : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := (coefficient : ℝ))
      first.terminal.data first.power.Delta retainedFactor)
    (denseNormalizationExponent : ℕ) where
  output : GenericFirstChartWholeCellOutput first chart
  massLower : GenericFirstChartTraceMassLower first chart output
  denseRoot : Nonempty (Proposition63PreLemma43DenseRootData
    (chart.wholeCellTraceOrdinarySource first.current.normalization
      output massLower)
    (chart.wholeCellTraceAmbient first.current.normalization output massLower)
    targetLoss targetNormalizationLoss denseNormalizationExponent)

/-- Construct the canonical whole-cell output and its honest trace receipt
from generic first-chart data. -/
theorem firstChartWholeCellTrace
    {commonSliceLoss chartLoss tau epsilon₁ epsilon₃ : ℝ}
    {coefficient : NNReal} {retainedFactor : ENNReal}
    (chart : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := (coefficient : ℝ))
      first.terminal.data first.power.Delta retainedFactor)
    (hscaleOne : first.power.requested.1 ≤ 1)
    (hratioSmall : delta / first.power.requested.1 ≤ 1 / 24)
    (hstickyChart : stickyLoss ≤ chartLoss)
    (hchartLoss : 0 < chartLoss)
    (houtputDensityAbsorb :
      Kakeya.realRpowENN (delta / first.power.requested.1) chartLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          (chart.sliceDensity / 2))
    (htraceDensityAbsorb :
      Kakeya.realRpowENN (delta / first.power.requested.1) chartLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ((100 : ENNReal)⁻¹ *
            (Kakeya.realRpowENN delta reentryLoss / 2) *
            (chart.sliceDensity / 2))) :
    ∃ output : GenericFirstChartWholeCellOutput first chart,
      GenericFirstChartTraceMassLower first chart output := by
  rcases chart.wholeCellFullFiberOutput_nonempty first.current.normalization
      hstickyChart hchartLoss hscaleOne hratioSmall houtputDensityAbsorb with
    ⟨output⟩
  refine ⟨output, chart.wholeCell_trace_massLower
    first.current.normalization output
    (hratioSmall.trans (by norm_num)) ?_⟩
  exact htraceDensityAbsorb

/-- The canonical unit-ball fibre gives the generic first chart its sharp
top-level CWA constant, independently of the sampled hierarchy. -/
theorem firstChartNormalizedTopLevelCWA
    {commonSliceLoss chartLoss tau epsilon₁ epsilon₃ : ℝ}
    {coefficient : NNReal} {retainedFactor : ENNReal}
    (chart : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := (coefficient : ℝ))
      first.terminal.data first.power.Delta retainedFactor)
    (hratioSmall : delta / first.power.requested.1 ≤ 1 / 24) :
    WZ2PaperConvexWolffBound
      (chart.chartSelection.normalizedFamily chart.chartRescaled)
      ((4 : ENNReal) * Kakeya.realRpowENN first.power.h (-stickyLoss)) := by
  have ratioPos : 0 < delta / first.power.requested.1 :=
    div_pos first.current.normalization.final_extremal.delta_pos
      (first.current.normalization.final_extremal.delta_pos.trans_le
        first.power.requested.2.1)
  have publicCWA : WZ2PaperConvexWolffBound
      chart.metricFiber.frozenRescaled.rescalingCertificate.publicFamily
      ((4 : ENNReal) * Kakeya.realRpowENN
        (delta / first.power.requested.1) (-stickyLoss)) :=
    pure_nearby_to_top_level ratioPos hratioSmall chart.public_unit_ball
      chart.metricFiber.frozenRescaled.extremal.cwa_nearby_scales
  have transported : WZ2PaperConvexWolffBound
      (chart.chartSelection.normalizedFamily chart.chartRescaled)
      ((4 : ENNReal) * Kakeya.realRpowENN
        (delta / first.power.requested.1) (-stickyLoss)) := by
    apply publicCWA.image_affineIsometry_of_carrier_eq
      chart.chartSelection.chartLabel.chart.affineIsometry
    intro index
    exact (chart.chartSelection.chartLabel.chart.image_paperTubeCarrier
      (chart.metricFiber.frozenRescaled.rescalingCertificate.publicFamily.tube
        index)).symm
  have ratioEq : delta / first.power.requested.1 = first.power.h := by
    rw [first.power.requested_eq, first.power.h_eq]
  exact ratioEq ▸ transported

/-- Family-free ninth-power cardinality bound for any generic first-chart
whole-cell output. -/
theorem firstChartPublicCardinalityNinthPower
    {commonSliceLoss chartLoss tau epsilon₁ epsilon₃ : ℝ}
    {coefficient : NNReal} {retainedFactor : ENNReal}
    (chart : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := (coefficient : ℝ))
      first.terminal.data first.power.Delta retainedFactor)
    (output : GenericFirstChartWholeCellOutput first chart)
    (hsigmaOne : sigma ≤ 1) :
    (output.rescalingCertificate.publicFamily.card : ℝ) ≤
      (259 : ℝ)^3 * (67 : ℝ)^3 * Real.rpow first.power.h (-9) := by
  have ambientBound := wz2_ed_packing_bound_boundedBase_four
    first.current.normalization.final_extremal.delta_pos
    first.current.normalization.final_extremal.delta_le_one
    first.current.normalization.final_extremal.cwa_nearby_scales.2.2.1
    first.current.normalization.ordinary_bounded_base
  have selectedCard : chart.metricFiber.fiberFamily.family.card ≤
      first.current.normalization.croppedFamily.card := by
    let selected := first.terminal.data.selected.comp
      chart.metricFiber.fiberFamily
    exact genericTubeSubfamily_card_le_ambient selected
  have rootBound : (output.rescalingCertificate.publicFamily.card : ℝ) ≤
      (259 : ℝ)^3 * (67 : ℝ)^3 * delta^(-6 : ℝ) := by
    have sourceCard : output.rescalingCertificate.publicFamily.card =
        chart.metricFiber.fiberFamily.family.card := by
      have sourceCardENN := output.source_cardinality_eq
      exact Nat.cast_inj.mp sourceCardENN
    rw [sourceCard]
    have selectedCardReal :
        (chart.metricFiber.fiberFamily.family.card : ℝ) ≤
          (first.current.normalization.croppedFamily.card : ℝ) := by
      exact_mod_cast selectedCard
    exact selectedCardReal.trans ambientBound
  have rootPower : delta = Real.rpow first.power.h (1 + sigma / 2) := by
    have hDeltaPos : 0 < first.power.Delta := by
      rw [← first.power.scale_identity]
      exact Real.rpow_pos_of_pos first.power.h_pos _
    calc
      delta = first.power.h * first.power.Delta := by
        rw [first.power.h_eq]
        field_simp [hDeltaPos.ne']
      _ = Real.rpow first.power.h 1 *
          Real.rpow first.power.h (sigma / 2) := by
        rw [first.power.scale_identity]
        congr 1
        exact (Real.rpow_one first.power.h).symm
      _ = Real.rpow first.power.h (1 + sigma / 2) :=
        (Real.rpow_add first.power.h_pos 1 (sigma / 2)).symm
  calc
    (output.rescalingCertificate.publicFamily.card : ℝ) ≤
        (259 : ℝ)^3 * (67 : ℝ)^3 * delta^(-6 : ℝ) := rootBound
    _ = (259 : ℝ)^3 * (67 : ℝ)^3 *
          Real.rpow first.power.h ((1 + sigma / 2) * (-6 : ℝ)) := by
      congr 1
      calc
        delta ^ (-6 : ℝ) =
            (Real.rpow first.power.h (1 + sigma / 2)) ^ (-6 : ℝ) :=
          congrArg (fun value : ℝ => value ^ (-6 : ℝ)) rootPower
        _ = Real.rpow first.power.h ((1 + sigma / 2) * (-6 : ℝ)) :=
          (Real.rpow_mul first.power.h_pos.le _ _).symm
    _ ≤ (259 : ℝ)^3 * (67 : ℝ)^3 *
          Real.rpow first.power.h (-9 : ℝ) := by
      gcongr
      apply Real.rpow_le_rpow_of_exponent_ge
        first.power.h_pos first.power.h_le_one
      linarith

/-- Package a named whole-cell trace and the dense-root receipt produced from
that exact trace.  This is the generic output boundary consumed downstream. -/
theorem firstChartDenseRootOfOutput
    {commonSliceLoss chartLoss targetLoss targetNormalizationLoss
      tau epsilon₁ epsilon₃ : ℝ}
    {coefficient : NNReal} {retainedFactor : ENNReal}
    (chart : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := (coefficient : ℝ))
      first.terminal.data first.power.Delta retainedFactor)
    (denseNormalizationExponent : ℕ)
    (output : GenericFirstChartWholeCellOutput first chart)
    (massLower : GenericFirstChartTraceMassLower first chart output)
    (denseRoot : Nonempty (Proposition63PreLemma43DenseRootData
      (chart.wholeCellTraceOrdinarySource first.current.normalization
        output massLower)
      (chart.wholeCellTraceAmbient first.current.normalization output massLower)
      targetLoss targetNormalizationLoss denseNormalizationExponent)) :
    Nonempty (GenericFirstChartDenseRootOutput
      (targetLoss := targetLoss)
      (targetNormalizationLoss := targetNormalizationLoss)
      first chart denseNormalizationExponent) :=
  ⟨{ output := output, massLower := massLower, denseRoot := denseRoot }⟩

end Proposition63GenericFirstRichBoundaryData
end Kakeya.Assouad.PureWZ2
end
