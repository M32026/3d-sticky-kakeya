import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9PreRuntimeHierarchy

/-!
# Proposition 6.3 same-extremizer assembly

The ordinary exact image produced by the first metric fibre must be
regularized before Lemma 4.3.  This file packages that ordering explicitly:
the selected ordinary source is dense-cubicalized, Lemma 4.3 runs on that
crop, and the later ordinary trace is therefore taken inside the same
extremizer.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- The external weight used before Lemma 4.3: the full mass of the exact
ordinary image on one tube. -/
def proposition63OrdinaryCarrierWeight
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (index : Fin family.card) : ENNReal :=
  volume (ordinary.carrier index)

/-- The charted exact ordinary image is contained carrierwise in the
first charted public cropped shading.  This is stronger than the union-level
inclusion exported by the critical witness and is what lets the pre-Lemma-4.3
dense crop remain a genuine subshading of the first chart output. -/
theorem proposition63ChartOrdinaryExtremalSourceOfTraceMass_sub_normalized
    {sigma initialInputLoss initialOutputLoss fineDelta firstScale
      ordinaryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration
      sigma initialInputLoss fineDelta}
    {initialNormalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := initialOutputLoss) initialSource
      initialNormalizationExponent)
    (selected : Kakeya.Streamlined.TubeSubfamily
      initialNormalized.croppedFamily)
    (finalShading : WZ1PaperTubeShading selected.family)
    (parentTube : Kakeya.DeltaTube firstScale)
    (hfirstScale : 0 < firstScale)
    (output : WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := ordinaryLoss)
      finalShading parentTube hfirstScale)
    (massLower :
      Kakeya.realRpowENN (fineDelta / firstScale) ordinaryLoss *
            output.rescalingCertificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / firstScale : ℝ) ^ 2)) *
          (initialNormalized.finalOrdinaryTrace
            selected finalShading).mass)
    (chart : WZ1HorizontalChart) :
    ∀ index,
      (proposition63ChartOrdinaryExtremalSourceOfTraceMass
        initialNormalized selected finalShading parentTube hfirstScale
        output massLower chart).shading.carrier index ⊆
      (chart.transportPaperShading
        (output.rescalingCertificate.publicShading
          output.literalShading.targetShading)).carrier index := by
  intro index point point_mem
  rcases point_mem with ⟨literalPoint, literalPointMem, rfl⟩
  rcases literalPointMem with ⟨sourcePoint, sourcePointMem, rfl⟩
  refine ⟨wz2PaperLiteralUnitRescalingMap parentTube hfirstScale
      sourcePoint, ?_, rfl⟩
  let target := output.rescalingCertificate.section6Index.symm index
  change wz2PaperLiteralUnitRescalingMap parentTube hfirstScale sourcePoint ∈
    (output.rescalingCertificate.publicShading
      output.literalShading.targetShading).carrier index
  change wz2PaperLiteralUnitRescalingMap parentTube hfirstScale sourcePoint ∈
    output.literalShading.targetShading.carrier target
  rw [output.literalShading.target_carrier_eq target]
  exact ⟨wz2PaperLiteralUnitRescalingMap parentTube hfirstScale sourcePoint,
    ⟨sourcePoint, sourcePointMem.2, rfl⟩, rfl⟩

/-- The first charted ordinary source is supported by the literal public
cropped extremizer on every indexed tube, not merely at union level. -/
theorem proposition63ChartOrdinaryExtremalSourceOfTraceMass_sub_firstChart
    {delta Delta sigma stickyLoss localLoss commonSliceLoss chartLoss
      tau epsilon₁ epsilon₃ coefficient initialInputLoss
      initialOutputLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration
      sigma initialInputLoss delta}
    {firstScale : WZ2PaperRequestedScale delta}
    {logExponent normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := initialOutputLoss) initialSource
      normalizationExponent)
    {firstSticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      initialNormalized.croppedRefined firstScale logExponent}
    {retainedFactor : ENNReal}
    (first : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := coefficient)
      firstSticky Delta retainedFactor)
    (massLower :
      Kakeya.realRpowENN (delta / firstScale.1) chartLoss *
            (first.chartRescaled.refreshedFullFiberOutput
              ).rescalingCertificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / firstScale.1 : ℝ) ^ 2)) *
          (initialNormalized.finalOrdinaryTrace
            (firstSticky.selected.comp first.metricFiber.fiberFamily)
            first.chartSelection.sourceShading).mass) :
    ∀ index,
      (proposition63ChartOrdinaryExtremalSourceOfTraceMass
        initialNormalized
        (firstSticky.selected.comp first.metricFiber.fiberFamily)
        first.chartSelection.sourceShading
        (firstSticky.coarse.tube first.metricFiber.parent)
        firstSticky.coarse_extremal.delta_pos
        first.chartRescaled.refreshedFullFiberOutput massLower
        first.chartSelection.chartLabel.chart).shading.carrier index ⊆
      (first.chartSelection.normalizedShading first.chartRescaled).carrier
        index :=
  proposition63ChartOrdinaryExtremalSourceOfTraceMass_sub_normalized
    initialNormalized
    (firstSticky.selected.comp first.metricFiber.fiberFamily)
    first.chartSelection.sourceShading
    (firstSticky.coarse.tube first.metricFiber.parent)
    firstSticky.coarse_extremal.delta_pos
    first.chartRescaled.refreshedFullFiberOutput massLower
    first.chartSelection.chartLabel.chart

/-- First-stage regularization of the charted exact ordinary image.  The
ordinary source and the cubical source of Lemma 4.3 are selected together,
so every later Lemma 4.3 refinement has genuine overlap with the retained
ordinary source. -/
structure Proposition63PreLemma43DenseRootData
    {delta sigma sourceLoss : ℝ}
    (source : PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (ambient : WZ1PaperTubeShading source.family)
    (targetLoss normalizationLoss : ℝ)
    (normalizationExponent : ℕ) where
  ambientConstant : ENNReal
  outputConstant : ENNReal
  normalizationWeight : ENNReal
  weightUpper : ENNReal
  levelCount : ℕ
  schedule : WZ2PaperPureFiniteNearbyScheduleData
    (fine := source.family) ambientConstant outputConstant levelCount
  regularized : WZ2PaperPureExternalWeightRegularizationData
    schedule normalizationWeight weightUpper
      (proposition63OrdinaryCarrierWeight source.shading)
  source_loss_le : sourceLoss ≤ targetLoss
  target_loss_pos : 0 < targetLoss
  normalization_loss_pos : 0 < normalizationLoss
  target_loss_le_half : targetLoss ≤ normalizationLoss / 2
  normalization_weight_ne_zero : normalizationWeight ≠ 0
  normalization_weight_ne_top : normalizationWeight ≠ ⊤
  output_le : outputConstant ≤
    Kakeya.realRpowENN delta (-targetLoss)
  trace_level :
    Kakeya.realRpowENN delta targetLoss *
        Kakeya.deltaTubeVolume delta ≤ regularized.weightLevel
  dense_level : ∀ index : Fin regularized.selected.family.card,
    Kakeya.realRpowENN delta targetLoss *
        volume (wz1PaperTubeCarrier
          (regularized.selected.family.tube index)) ≤
      (73 / 100 : ENNReal) * regularized.weightLevel
  ordinary_sub_ambient : ∀ index,
    source.shading.carrier index ⊆ ambient.carrier index
  ambient_cubical : WZ1PaperIsCubicalShading ambient
  ambient_extremal : WZ2PaperCroppedIsExtremal
    sigma targetLoss source.family ambient
  ordinary_axial_window : ∀ index point,
    point ∈ source.shading.carrier index → |point (2 : Fin 3)| ≤ 1 / 25
  line_class : WZ1PaperIsLineClass source.family
  direction_vertical : ∀ index,
    Real.sqrt 3 / 2 ≤
      wz1PaperDirection (source.family.tube index) (2 : Fin 3)
  delta_small : delta ≤ 1 / 24
  ambient_top_level_constant : ENNReal
  ambient_top_level_cwa :
    WZ2PaperConvexWolffBound source.family ambient_top_level_constant
  top_level_absorb :
    (normalizationWeight⁻¹ *
        (regularized.regularizationLoss * weightUpper)) *
        ambient_top_level_constant ≤
      Kakeya.realRpowENN delta (-normalizationLoss)

/-- Assemble the pre-Lemma-4.3 package from one finite nearby schedule and
the scalar receipts for ordinary-mass regularization. -/
theorem proposition63_preLemma43_dense_root
    {delta sigma sourceLoss targetLoss normalizationLoss : ℝ}
    (source : PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (ambient : WZ1PaperTubeShading source.family)
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount normalizationExponent : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := source.family) ambientConstant outputConstant levelCount)
    (ambient_cwa : WZ2PaperPureCWAAtNearbyScales
      source.family ambientConstant)
    (source_loss_le : sourceLoss ≤ targetLoss)
    (target_loss_pos : 0 < targetLoss)
    (normalization_loss_pos : 0 < normalizationLoss)
    (target_loss_le_half : targetLoss ≤ normalizationLoss / 2)
    (normalization_weight_ne_zero : normalizationWeight ≠ 0)
    (normalization_weight_ne_top : normalizationWeight ≠ ⊤)
    (weightUpper_ne_top : weightUpper ≠ ⊤)
    (regularization_mass_lower :
      normalizationWeight * source.family.enncard ≤ source.shading.mass)
    (weight_upper : ∀ index : Fin source.family.card,
      proposition63OrdinaryCarrierWeight source.shading index ≤ weightUpper)
    (output_finite : WZ2PaperFiniteErrorConstant outputConstant)
    (regularization_absorb :
      let degreeConstant :=
        16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * source.family.card) + 1 : ENNReal) ^
            schedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * source.family.card) + 1 : ENNReal) ^
            (schedule.scaleCount + 1)
      max degreeConstant
          ((normalizationWeight⁻¹ *
              (ambientConstant *
                (regularizationLoss * weightUpper) *
                degreeConstant)) *
            ambientConstant) ≤
        outputConstant)
    (output_le : outputConstant ≤
      Kakeya.realRpowENN delta (-targetLoss))
    (trace_scale_absorb :
      4 * (Kakeya.realRpowENN delta targetLoss *
        Kakeya.deltaTubeVolume delta) ≤ normalizationWeight)
    (paper_scale_absorb : ∀ index : Fin source.family.card,
      4 * (Kakeya.realRpowENN delta targetLoss *
          volume (wz1PaperTubeCarrier (source.family.tube index))) ≤
        (73 / 100 : ENNReal) * normalizationWeight)
    (ordinary_sub_ambient : ∀ index,
      source.shading.carrier index ⊆ ambient.carrier index)
    (ambient_cubical : WZ1PaperIsCubicalShading ambient)
    (ambient_extremal : WZ2PaperCroppedIsExtremal
      sigma targetLoss source.family ambient)
    (ordinary_axial_window : ∀ index point,
      point ∈ source.shading.carrier index → |point (2 : Fin 3)| ≤ 1 / 25)
    (line_class : WZ1PaperIsLineClass source.family)
    (direction_vertical : ∀ index,
      Real.sqrt 3 / 2 ≤
        wz1PaperDirection (source.family.tube index) (2 : Fin 3))
    (delta_small : delta ≤ 1 / 24)
    (ambient_top_level_constant : ENNReal)
    (ambient_top_level_cwa :
      WZ2PaperConvexWolffBound source.family ambient_top_level_constant)
    (top_level_absorb :
      (normalizationWeight⁻¹ *
          (((8 : ENNReal) *
              (Nat.log 2 (2 * source.family.card) + 1 : ENNReal) ^
                (schedule.scaleCount + 1)) * weightUpper)) *
          ambient_top_level_constant ≤
        Kakeya.realRpowENN delta (-normalizationLoss)) :
    Nonempty (Proposition63PreLemma43DenseRootData source ambient
      targetLoss normalizationLoss normalizationExponent) := by
  rcases schedule.regularizeExternalWeight ambient_cwa
      source.extremal.nonempty
      (proposition63OrdinaryCarrierWeight source.shading)
      normalization_weight_ne_zero normalization_weight_ne_top
      weightUpper_ne_top (by
        change normalizationWeight * source.family.enncard ≤
          ∑ index : Fin source.family.card,
            volume (source.shading.carrier index)
        exact regularization_mass_lower) weight_upper
      output_finite regularization_absorb with
    ⟨regularized⟩
  have four_ne_zero : (4 : ENNReal) ≠ 0 := by norm_num
  have four_ne_top : (4 : ENNReal) ≠ ⊤ := by norm_num
  have trace_level :
      Kakeya.realRpowENN delta targetLoss *
          Kakeya.deltaTubeVolume delta ≤ regularized.weightLevel := by
    apply (ENNReal.mul_le_mul_iff_right four_ne_zero four_ne_top).mp
    exact trace_scale_absorb.trans
      regularized.normalizationWeight_le_four_weightLevel
  have dense_level : ∀ index : Fin regularized.selected.family.card,
      Kakeya.realRpowENN delta targetLoss *
          volume (wz1PaperTubeCarrier
            (regularized.selected.family.tube index)) ≤
        (73 / 100 : ENNReal) * regularized.weightLevel := by
    intro index
    apply (ENNReal.mul_le_mul_iff_right four_ne_zero four_ne_top).mp
    calc
      4 * (Kakeya.realRpowENN delta targetLoss *
            volume (wz1PaperTubeCarrier
              (regularized.selected.family.tube index))) ≤
          (73 / 100 : ENNReal) * normalizationWeight := by
        rw [regularized.selected.tube_eq]
        exact paper_scale_absorb (regularized.selected.embedding index)
      _ ≤ (73 / 100 : ENNReal) *
          (4 * regularized.weightLevel) := by
        gcongr
        exact regularized.normalizationWeight_le_four_weightLevel
      _ = 4 * ((73 / 100 : ENNReal) * regularized.weightLevel) := by
        ring
  exact ⟨{
    ambientConstant := ambientConstant
    outputConstant := outputConstant
    normalizationWeight := normalizationWeight
    weightUpper := weightUpper
    levelCount := levelCount
    schedule := schedule
    regularized := regularized
    source_loss_le := source_loss_le
    target_loss_pos := target_loss_pos
    normalization_loss_pos := normalization_loss_pos
    target_loss_le_half := target_loss_le_half
    normalization_weight_ne_zero := normalization_weight_ne_zero
    normalization_weight_ne_top := normalization_weight_ne_top
    output_le := output_le
    trace_level := trace_level
    dense_level := dense_level
    ordinary_sub_ambient := ordinary_sub_ambient
    ambient_cubical := ambient_cubical
    ambient_extremal := ambient_extremal
    ordinary_axial_window := ordinary_axial_window
    line_class := line_class
    direction_vertical := direction_vertical
    delta_small := delta_small
    ambient_top_level_constant := ambient_top_level_constant
    ambient_top_level_cwa := ambient_top_level_cwa
    top_level_absorb := by
      rw [regularized.regularizationLoss_eq]
      exact top_level_absorb
  }⟩

/-- A charted exact ordinary source has the bounded-base property required
by the next frozen normalization whenever the concrete public rescaling
family was centred at its literal image midpoint.  This is stated as an
explicit equality because the abstract public certificate permits arbitrary
coaxial recentering. -/
theorem proposition63_chart_ordinary_bounded_base_of_canonical_public
    {delta sigma sourceLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    (chart : WZ1HorizontalChart)
    (public_midpoint_bound : HasBoundedBase source.family 4) :
    HasBoundedBase
      (transportFamily chart.isometry source.family) 4 := by
  intro index
  change ‖chart.isometry (source.family.tube index).base‖ ≤ 4
  rw [chart.isometry.norm_map]
  exact public_midpoint_bound index

/-- The concrete public ordinary tube used by the closed rescaling producer
has base norm at most four.  The midpoint is bounded by three, and the stored
base is exactly half a unit direction from that midpoint. -/
theorem proposition63_literal_ordinary_public_bounded_base
    {delta rho : ℝ}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (sourceFamily : Kakeya.Streamlined.TubeFamily delta)
    (anchor : Kakeya.DeltaTube rho)
    (sourceLine : WZ1PaperIsLineClass sourceFamily)
    (sourceBoundedBase : HasBoundedBase sourceFamily 4)
    (covered : ∀ index,
      WZ1PaperTubeCovers (sourceFamily.tube index) anchor) :
    HasBoundedBase
      { card := sourceFamily.card
        tube := fun index =>
          wz2PaperLiteralOrdinaryRescaledTube
            (sourceFamily.tube index) anchor hrho } 4 := by
  intro index
  let target := wz2PaperLiteralOrdinaryRescaledTube
    (sourceFamily.tube index) anchor hrho
  have midpoint_bound : ‖wz2PaperTubeMidpoint target‖ ≤ 3 := by
    exact wz2PaperLiteralOrdinaryRescaledTube_midpoint_norm_le_three_of_boundedBase
      hrho hrhoOne (sourceFamily.tube index) anchor
      (sourceLine index) (sourceBoundedBase index) (covered index)
  have base_eq : target.base =
      wz2PaperTubeMidpoint target - (1 / 2 : ℝ) • target.direction := by
    simp [target, wz2PaperTubeMidpoint]
  rw [base_eq]
  calc
    ‖wz2PaperTubeMidpoint target - (1 / 2 : ℝ) • target.direction‖ ≤
        ‖wz2PaperTubeMidpoint target‖ +
          ‖(1 / 2 : ℝ) • target.direction‖ := norm_sub_le _ _
    _ = ‖wz2PaperTubeMidpoint target‖ + 1 / 2 := by
      rw [norm_smul, target.direction_unit]
      norm_num
    _ ≤ 4 := by linarith

/-- Specialize the pre-Lemma-4.3 regularization to the exact charted ordinary
source carried by `Proposition63FirstChartData`.  All geometric premises are
discharged internally; the remaining arguments are precisely the scalar
receipts that the outer M9 cutoff must freeze. -/
theorem proposition63_preLemma43_dense_root_of_firstChart
    {delta Delta sigma stickyLoss localLoss commonSliceLoss chartLoss
      targetLoss normalizationLoss tau epsilon₁ epsilon₃ coefficient
      initialInputLoss initialOutputLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration
      sigma initialInputLoss delta}
    {firstScale : WZ2PaperRequestedScale delta}
    {logExponent initialNormalizationExponent normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := initialOutputLoss) initialSource
      initialNormalizationExponent)
    {firstSticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      initialNormalized.croppedRefined firstScale logExponent}
    {retainedFactor : ENNReal}
    (first : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := coefficient)
      firstSticky Delta retainedFactor)
    (massLower :
      Kakeya.realRpowENN (delta / firstScale.1) chartLoss *
            (first.chartRescaled.refreshedFullFiberOutput
              ).rescalingCertificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / firstScale.1 : ℝ) ^ 2)) *
          (initialNormalized.finalOrdinaryTrace
            (firstSticky.selected.comp first.metricFiber.fiberFamily)
            first.chartSelection.sourceShading).mass)
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := (proposition63ChartOrdinaryExtremalSourceOfTraceMass
        initialNormalized
        (firstSticky.selected.comp first.metricFiber.fiberFamily)
        first.chartSelection.sourceShading
        (firstSticky.coarse.tube first.metricFiber.parent)
        firstSticky.coarse_extremal.delta_pos
        first.chartRescaled.refreshedFullFiberOutput massLower
        first.chartSelection.chartLabel.chart).family)
      ambientConstant outputConstant levelCount)
    (ambient_cwa : WZ2PaperPureCWAAtNearbyScales
      (proposition63ChartOrdinaryExtremalSourceOfTraceMass
        initialNormalized
        (firstSticky.selected.comp first.metricFiber.fiberFamily)
        first.chartSelection.sourceShading
        (firstSticky.coarse.tube first.metricFiber.parent)
        firstSticky.coarse_extremal.delta_pos
        first.chartRescaled.refreshedFullFiberOutput massLower
        first.chartSelection.chartLabel.chart).family ambientConstant)
    (source_loss_le : chartLoss ≤ targetLoss)
    (target_loss_pos : 0 < targetLoss)
    (normalization_loss_pos : 0 < normalizationLoss)
    (target_loss_le_half : targetLoss ≤ normalizationLoss / 2)
    (normalization_weight_ne_zero : normalizationWeight ≠ 0)
    (normalization_weight_ne_top : normalizationWeight ≠ ⊤)
    (weightUpper_ne_top : weightUpper ≠ ⊤)
    (weight_upper : ∀ index,
      proposition63OrdinaryCarrierWeight
          (proposition63ChartOrdinaryExtremalSourceOfTraceMass
            initialNormalized
            (firstSticky.selected.comp first.metricFiber.fiberFamily)
            first.chartSelection.sourceShading
            (firstSticky.coarse.tube first.metricFiber.parent)
            firstSticky.coarse_extremal.delta_pos
            first.chartRescaled.refreshedFullFiberOutput massLower
            first.chartSelection.chartLabel.chart).shading index ≤
        weightUpper)
    (output_finite : WZ2PaperFiniteErrorConstant outputConstant)
    (regularization_mass_lower :
      normalizationWeight *
          (proposition63ChartOrdinaryExtremalSourceOfTraceMass
            initialNormalized
            (firstSticky.selected.comp first.metricFiber.fiberFamily)
            first.chartSelection.sourceShading
            (firstSticky.coarse.tube first.metricFiber.parent)
            firstSticky.coarse_extremal.delta_pos
            first.chartRescaled.refreshedFullFiberOutput massLower
            first.chartSelection.chartLabel.chart).family.enncard ≤
        (proposition63ChartOrdinaryExtremalSourceOfTraceMass
          initialNormalized
          (firstSticky.selected.comp first.metricFiber.fiberFamily)
          first.chartSelection.sourceShading
          (firstSticky.coarse.tube first.metricFiber.parent)
          firstSticky.coarse_extremal.delta_pos
          first.chartRescaled.refreshedFullFiberOutput massLower
          first.chartSelection.chartLabel.chart).shading.mass)
    (regularization_absorb :
      let ordinarySource := proposition63ChartOrdinaryExtremalSourceOfTraceMass
        initialNormalized
        (firstSticky.selected.comp first.metricFiber.fiberFamily)
        first.chartSelection.sourceShading
        (firstSticky.coarse.tube first.metricFiber.parent)
        firstSticky.coarse_extremal.delta_pos
        first.chartRescaled.refreshedFullFiberOutput massLower
        first.chartSelection.chartLabel.chart
      let degreeConstant :=
        16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * ordinarySource.family.card) + 1 : ENNReal) ^
            schedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * ordinarySource.family.card) + 1 : ENNReal) ^
            (schedule.scaleCount + 1)
      max degreeConstant
          ((normalizationWeight⁻¹ *
              (ambientConstant *
                (regularizationLoss * weightUpper) *
                degreeConstant)) *
            ambientConstant) ≤ outputConstant)
    (output_le : outputConstant ≤
      Kakeya.realRpowENN (delta / firstScale.1) (-targetLoss))
    (trace_scale_absorb :
      4 * (Kakeya.realRpowENN (delta / firstScale.1) targetLoss *
        Kakeya.deltaTubeVolume (delta / firstScale.1)) ≤
          normalizationWeight)
    (paper_scale_absorb : ∀ index,
      4 * (Kakeya.realRpowENN (delta / firstScale.1) targetLoss *
          volume (wz1PaperTubeCarrier
            ((proposition63ChartOrdinaryExtremalSourceOfTraceMass
              initialNormalized
              (firstSticky.selected.comp first.metricFiber.fiberFamily)
              first.chartSelection.sourceShading
              (firstSticky.coarse.tube first.metricFiber.parent)
              firstSticky.coarse_extremal.delta_pos
              first.chartRescaled.refreshedFullFiberOutput massLower
              first.chartSelection.chartLabel.chart).family.tube index))) ≤
        (73 / 100 : ENNReal) * normalizationWeight)
    (ratio_small : delta / firstScale.1 ≤ 1 / 24)
    (ambient_top_level_constant : ENNReal)
    (ambient_top_level_cwa : WZ2PaperConvexWolffBound
      (first.chartSelection.normalizedFamily first.chartRescaled)
      ambient_top_level_constant)
    (top_level_absorb :
      (normalizationWeight⁻¹ *
          (((8 : ENNReal) *
              (Nat.log 2 (2 *
                (proposition63ChartOrdinaryExtremalSourceOfTraceMass
                  initialNormalized
                  (firstSticky.selected.comp first.metricFiber.fiberFamily)
                  first.chartSelection.sourceShading
                  (firstSticky.coarse.tube first.metricFiber.parent)
                  firstSticky.coarse_extremal.delta_pos
                  first.chartRescaled.refreshedFullFiberOutput massLower
                  first.chartSelection.chartLabel.chart).family.card) + 1 :
                    ENNReal) ^ (schedule.scaleCount + 1)) * weightUpper)) *
          ambient_top_level_constant ≤
        Kakeya.realRpowENN (delta / firstScale.1) (-normalizationLoss)) :
    Nonempty (Proposition63PreLemma43DenseRootData
      (proposition63ChartOrdinaryExtremalSourceOfTraceMass
        initialNormalized
        (firstSticky.selected.comp first.metricFiber.fiberFamily)
        first.chartSelection.sourceShading
        (firstSticky.coarse.tube first.metricFiber.parent)
        firstSticky.coarse_extremal.delta_pos
        first.chartRescaled.refreshedFullFiberOutput massLower
        first.chartSelection.chartLabel.chart)
      (first.chartSelection.normalizedShading first.chartRescaled)
      targetLoss normalizationLoss normalizationExponent) := by
  let ordinarySource := proposition63ChartOrdinaryExtremalSourceOfTraceMass
    initialNormalized
    (firstSticky.selected.comp first.metricFiber.fiberFamily)
    first.chartSelection.sourceShading
    (firstSticky.coarse.tube first.metricFiber.parent)
    firstSticky.coarse_extremal.delta_pos
    first.chartRescaled.refreshedFullFiberOutput massLower
    first.chartSelection.chartLabel.chart
  let ambient := first.chartSelection.normalizedShading first.chartRescaled
  have ordinary_sub_ambient : ∀ index,
      ordinarySource.shading.carrier index ⊆ ambient.carrier index :=
    proposition63ChartOrdinaryExtremalSourceOfTraceMass_sub_firstChart
      initialNormalized first massLower
  have ambient_extremal : WZ2PaperCroppedIsExtremal sigma targetLoss
      ordinarySource.family ambient :=
    (first.chartSelection.normalizedExtremal first.chartRescaled).mono_loss
      source_loss_le
  apply proposition63_preLemma43_dense_root ordinarySource ambient schedule
    ambient_cwa source_loss_le target_loss_pos
    normalization_loss_pos target_loss_le_half
    normalization_weight_ne_zero normalization_weight_ne_top
    weightUpper_ne_top regularization_mass_lower weight_upper
    output_finite
    regularization_absorb output_le trace_scale_absorb paper_scale_absorb
    ordinary_sub_ambient ambient_extremal.cubical ambient_extremal
    (proposition63ChartOrdinaryExtremalSourceOfTraceMass_axial_window
      initialNormalized
      (firstSticky.selected.comp first.metricFiber.fiberFamily)
      first.chartSelection.sourceShading
      (firstSticky.coarse.tube first.metricFiber.parent)
      firstSticky.coarse_extremal.delta_pos
      (firstSticky.cover.coarse_line_class first.metricFiber.parent)
      first.chartRescaled.refreshedFullFiberOutput massLower
      first.chartSelection.chartLabel.chart)
    (first.chartSelection.normalizedFamily_lineClass first.chartRescaled)
    (first.chartSelection.normalizedFamily_direction_vertical
      first.chartRescaled firstScale.2.2)
    ratio_small ambient_top_level_constant ambient_top_level_cwa
    top_level_absorb

namespace Proposition63PreLemma43DenseRootData

/-- Positive ordinary mass on a tube inside the fixed cropped box places its
base in the radius-four parameter window.  This is derived on the exact
regularized family; no recentering property of the abstract rescaling
certificate is assumed. -/
theorem ordinaryBoundedBase
    {delta sigma sourceLoss targetLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (data : Proposition63PreLemma43DenseRootData source ambient
      targetLoss normalizationLoss normalizationExponent) :
    HasBoundedBase data.regularized.selected.family 4 := by
  intro index
  have carrier_volume_pos : 0 < volume
      (source.shading.carrier
        (data.regularized.selected.embedding index)) :=
    data.regularized.weightLevel_pos.trans_le
      (data.regularized.weight_band index).1
  rcases MeasureTheory.nonempty_of_measure_ne_zero carrier_volume_pos.ne' with
    ⟨point, point_mem⟩
  have point_ambient : point ∈
      ambient.carrier (data.regularized.selected.embedding index) :=
    data.ordinary_sub_ambient _ point_mem
  have point_box : point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
    (ambient.subset_body _ point_ambient).2
  have coordinates :
      |point (0 : Fin 3)| ≤ 1 ∧ |point (1 : Fin 3)| ≤ 1 ∧
        |point (2 : Fin 3)| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using point_box
  have coordinate_square : ∀ coordinate : Fin 3,
      point coordinate ^ 2 ≤ 1 := by
    intro coordinate
    have bound : |point coordinate| ≤ 1 := by
      fin_cases coordinate <;> simp_all
    nlinarith [abs_le.mp bound]
  have point_norm_sq : ‖point‖ ^ 2 =
      point 0 ^ 2 + point 1 ^ 2 + point 2 ^ 2 := by
    have identity := EuclideanSpace.real_norm_sq_eq point
    simpa [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] using identity
  have point_norm_le_two : ‖point‖ ≤ 2 := by
    have point_norm_nonnegative := norm_nonneg point
    have norm_square_le : ‖point‖ ^ 2 ≤ 3 := by
      rw [point_norm_sq]
      linarith [coordinate_square 0, coordinate_square 1,
        coordinate_square 2]
    nlinarith [sq_nonneg ‖point‖]
  let tube := source.family.tube
    (data.regularized.selected.embedding index)
  have point_tube : point ∈ tube.carrier := source.shading.subset_body _ point_mem
  rcases exists_closest_on_axis source.extremal.delta_pos.le tube point
      point_tube with ⟨parameter, parameter_mem, point_axis⟩
  have axis_error :
      ‖(tube.base + parameter • tube.direction) - point‖ ≤ delta := by
    rw [norm_sub_rev, ← dist_eq_norm]
    exact point_axis
  have parameter_norm : ‖parameter • tube.direction‖ ≤ 1 := by
    rw [norm_smul, tube.direction_unit, mul_one, Real.norm_eq_abs,
      abs_of_nonneg parameter_mem.1]
    exact parameter_mem.2
  have base_decomposition : tube.base =
      point + ((tube.base + parameter • tube.direction) - point) -
        parameter • tube.direction := by
    module
  rw [data.regularized.selected.tube_eq, base_decomposition]
  calc
    ‖point + ((tube.base + parameter • tube.direction) - point) -
          parameter • tube.direction‖ ≤
        ‖point + ((tube.base + parameter • tube.direction) - point)‖ +
          ‖parameter • tube.direction‖ := norm_sub_le _ _
    _ ≤ (‖point‖ +
          ‖(tube.base + parameter • tube.direction) - point‖) +
          ‖parameter • tube.direction‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (2 : ℝ) + delta + 1 := by gcongr
    _ ≤ 4 := by linarith [data.delta_small]

noncomputable def ordinarySource
    {delta sigma sourceLoss targetLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (data : Proposition63PreLemma43DenseRootData source ambient
      targetLoss normalizationLoss normalizationExponent) :
    PureWZ2ExtremalConfiguration sigma targetLoss delta where
  family := data.regularized.selected.family
  shading := data.regularized.selected.restrictShading source.shading
  extremal :=
    { delta_pos := source.extremal.delta_pos
      delta_le_one := source.extremal.delta_le_one
      nonempty := data.regularized.selected_nonempty
      cwa_nearby_scales := data.regularized.pure_cwa_nearby.mono
        data.output_le (by simp [Kakeya.realRpowENN])
      dense := by
        rw [Kakeya.Streamlined.Shading.IsLambdaDense,
          tubeFamily_mass_eq_nominal]
        calc
          Kakeya.realRpowENN delta targetLoss *
                data.regularized.selected.family.nominalMass =
              ∑ _index : Fin data.regularized.selected.family.card,
                Kakeya.realRpowENN delta targetLoss *
                  Kakeya.deltaTubeVolume delta := by
            simp [Kakeya.Streamlined.TubeFamily.nominalMass,
              Kakeya.Streamlined.TubeFamily.enncard, Finset.sum_const]
            ring
          _ ≤ ∑ _index : Fin data.regularized.selected.family.card,
                data.regularized.weightLevel := by
            exact Finset.sum_le_sum fun _ _ => data.trace_level
          _ ≤ (data.regularized.selected.restrictShading
                source.shading).mass := by
            apply Finset.sum_le_sum
            intro index _
            exact (data.regularized.weight_band index).1
      volume_upper := by
        apply (measure_mono ?_).trans
          (source.extremal.mono_loss data.source_loss_le).volume_upper
        rintro point ⟨index, point_mem⟩
        exact ⟨data.regularized.selected.embedding index, point_mem⟩ }

noncomputable def denseShading
    {delta sigma sourceLoss targetLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (data : Proposition63PreLemma43DenseRootData source ambient
      targetLoss normalizationLoss normalizationExponent) :
    WZ1PaperTubeShading data.ordinarySource.family :=
  pureWZ2DenseCubicalShading
    (data.regularized.selected.restrictShading source.shading)

theorem cellContained
    {delta sigma sourceLoss targetLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (data : Proposition63PreLemma43DenseRootData source ambient
      targetLoss normalizationLoss normalizationExponent)
    (index : Fin data.regularized.selected.family.card)
    (cell : ℤ × ℤ × ℤ)
    (cell_meets :
      (data.ordinarySource.shading.carrier index ∩
        wz1PaperGridCube delta cell).Nonempty) :
    wz1PaperGridCube delta cell ⊆
      wz1PaperTubeCarrier
        (data.regularized.selected.family.tube index) := by
  rcases cell_meets with ⟨point, point_ordinary, point_cell⟩
  have point_ambient : point ∈
      ambient.carrier (data.regularized.selected.embedding index) :=
    data.ordinary_sub_ambient _ point_ordinary
  have whole := data.ambient_cubical
    (data.regularized.selected.embedding index) point point_ambient
  intro other other_cell
  rw [data.regularized.selected.tube_eq]
  exact ambient.subset_body _ (whole <| by
    have index_eq : wz1PaperGridIndex delta other =
        wz1PaperGridIndex delta point :=
      ((mem_wz1PaperGridCube delta cell other).mp other_cell).trans
        ((mem_wz1PaperGridCube delta cell point).mp point_cell).symm
    exact (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta point) other).mpr index_eq)

theorem denseCroppedDense
    {delta sigma sourceLoss targetLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (data : Proposition63PreLemma43DenseRootData source ambient
      targetLoss normalizationLoss normalizationExponent) :
    data.denseShading.IsLambdaDense
      (Kakeya.realRpowENN delta targetLoss) := by
  rw [Kakeya.Streamlined.Shading.IsLambdaDense]
  change
    Kakeya.realRpowENN delta targetLoss *
        (∑ index : Fin data.regularized.selected.family.card,
          volume (wz1PaperTubeCarrier
            (data.regularized.selected.family.tube index))) ≤
      ∑ index : Fin data.regularized.selected.family.card,
        volume (data.denseShading.carrier index)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro index _
  calc
    Kakeya.realRpowENN delta targetLoss *
          volume (wz1PaperTubeCarrier
            (data.regularized.selected.family.tube index)) ≤
        (73 / 100 : ENNReal) * data.regularized.weightLevel :=
      data.dense_level index
    _ ≤ (73 / 100 : ENNReal) *
          volume (data.ordinarySource.shading.carrier index) := by
      gcongr
      exact (data.regularized.weight_band index).1
    _ ≤ volume (data.denseShading.carrier index) := by
      apply (pureWZ2DenseCubicalization_trace_retention
        source.extremal.delta_pos
        (by
          have sqrt_bound : Real.sqrt 3 ≤ 2 := by
            nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
              Real.sqrt_nonneg 3]
          calc
            delta * (1 + Real.sqrt 3) ≤ delta * 3 := by
              apply mul_le_mul_of_nonneg_left (by linarith)
              exact source.extremal.delta_pos.le
            _ ≤ 1 := by nlinarith [data.delta_small])
        (data.ordinarySource.family.tube index)
        (data.ordinarySource.shading.carrier index)
        (data.ordinarySource.shading.measurable_carrier index)
        (data.ordinarySource.shading.subset_body index)
        (data.cellContained index)).trans
      exact measure_mono Set.inter_subset_right

theorem denseSubshading
    {delta sigma sourceLoss targetLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (data : Proposition63PreLemma43DenseRootData source ambient
      targetLoss normalizationLoss normalizationExponent) :
    PaperIsSubshading data.denseShading
      (restrictPaperShading data.regularized.selected ambient) := by
  apply pureWZ2DenseCubicalShading_sub_cubical
    data.ordinarySource.shading
    (restrictPaperShading data.regularized.selected ambient)
    source.extremal.delta_pos
  · intro index point point_mem
    exact data.ordinary_sub_ambient _ point_mem
  · exact restrictPaperShading_cubical data.regularized.selected
      data.ambient_cubical
  · intro index
    exact data.regularized.weightLevel_pos.trans_le
      (data.regularized.weight_band index).1

/-- The selected dense Lemma-4.3 source remains inside the ambient first
chart shading.  The index is transported through the exact regularizer
embedding; this is the union-level provenance needed by the global-slice
pre-grain theorem. -/
theorem denseUnionSubsetAmbient
    {delta sigma sourceLoss targetLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (data : Proposition63PreLemma43DenseRootData source ambient
      targetLoss normalizationLoss normalizationExponent) :
    data.denseShading.union ⊆ ambient.union := by
  rintro point ⟨index, point_mem⟩
  exact ⟨data.regularized.selected.embedding index,
    data.denseSubshading index point_mem⟩

theorem croppedExtremal
    {delta sigma sourceLoss targetLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (data : Proposition63PreLemma43DenseRootData source ambient
      targetLoss normalizationLoss normalizationExponent) :
    WZ2PaperCroppedIsExtremal sigma targetLoss
      data.regularized.selected.family data.denseShading := by
  refine
    { delta_pos := source.extremal.delta_pos
      delta_le_one := source.extremal.delta_le_one
      nonempty := data.regularized.selected_nonempty
      cwa_nearby_scales := data.regularized.pure_cwa_nearby.mono
        data.output_le (by simp [Kakeya.realRpowENN])
      cubical := pureWZ2DenseCubicalShading_cubical
        data.ordinarySource.shading
      dense := data.denseCroppedDense
      volume_upper := ?_ }
  apply (measure_mono ?_).trans
    data.ambient_extremal.volume_upper
  rintro point ⟨index, point_mem⟩
  have point_restricted : point ∈
      (restrictPaperShading data.regularized.selected ambient).carrier index :=
    data.denseSubshading index point_mem
  exact ⟨data.regularized.selected.embedding index, point_restricted⟩

noncomputable def normalization
    {delta sigma sourceLoss targetLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (data : Proposition63PreLemma43DenseRootData source ambient
      targetLoss normalizationLoss normalizationExponent) :
    PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) data.ordinarySource
      normalizationExponent := by
  have log_one : 1 ≤ Real.log (1 / delta) := by
    apply (Real.le_log_iff_exp_le (one_div_pos.mpr
      source.extremal.delta_pos)).2
    have twenty_four : (24 : ℝ) ≤ 1 / delta := by
      apply (le_div_iff₀ source.extremal.delta_pos).2
      nlinarith [data.delta_small]
    exact (Real.exp_one_lt_three.trans (by norm_num)).le.trans twenty_four
  have retained :
      wz2PaperPureRefinementFraction delta normalizationExponent *
          data.ordinarySource.shading.mass ≤
        data.ordinarySource.shading.mass :=
    proposition63PureRefinementFraction_mul_le_self
      normalizationExponent log_one data.ordinarySource.shading.mass
  have top_level : WZ2PaperConvexWolffBound
      data.regularized.selected.family
      (Kakeya.realRpowENN delta (-normalizationLoss)) :=
    proposition63RegularizedTrace_topLevelCWA_from_ambient data.schedule
      data.regularized data.normalization_weight_ne_zero
      data.normalization_weight_ne_top data.ambient_top_level_cwa
      data.top_level_absorb
  have normalized_extremal : WZ2PaperCroppedIsExtremal sigma
      normalizationLoss data.regularized.selected.family data.denseShading :=
    data.croppedExtremal.mono_loss (by
      linarith [data.target_loss_le_half, data.normalization_loss_pos])
  apply proposition63IdentityFullOrdinaryNormalization
    (source := data.ordinarySource) data.target_loss_le_half
    normalizationExponent data.denseShading
    (pureWZ2DenseCubicalShading_cubical data.ordinarySource.shading)
  · intro index
    rfl
  · exact retained
  · intro index
    have tube_volume :
        volume (data.ordinarySource.family.tube index).carrier =
          Kakeya.deltaTubeVolume delta :=
      tube_volume_scaling.1 delta (data.ordinarySource.family.tube index)
    calc
      (Kakeya.realRpowENN delta targetLoss / 2) *
            volume (data.ordinarySource.family.tube index).carrier ≤
          Kakeya.realRpowENN delta targetLoss *
            volume (data.ordinarySource.family.tube index).carrier := by
        apply mul_le_mul_left
        rw [div_eq_mul_inv]
        exact mul_le_of_le_one_right bot_le (by norm_num)
      _ = Kakeya.realRpowENN delta targetLoss *
            Kakeya.deltaTubeVolume delta := by rw [tube_volume]
      _ ≤ data.regularized.weightLevel := data.trace_level
      _ ≤ volume (data.ordinarySource.shading.carrier index) :=
        (data.regularized.weight_band index).1
  · intro index point point_mem
    exact (data.ordinary_axial_window
      (data.regularized.selected.embedding index) point point_mem).trans
        (by norm_num)
  · exact data.line_class.subfamily data.regularized.selected
  · exact top_level
  · exact normalized_extremal
  · exact data.cellContained
  · exact data.ordinaryBoundedBase

/-- The tight literal-image axial window is retained across the identity
normalization.  The generic normalization field only advertises `1 / 4`; M9
keeps this stronger fact separately for the second requested scale. -/
theorem normalizationAxialWindowTwentyFifth
    {delta sigma sourceLoss targetLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (data : Proposition63PreLemma43DenseRootData source ambient
      targetLoss normalizationLoss normalizationExponent) :
    ∀ index point,
      point ∈ data.normalization.frame ''
          data.normalization.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 25 := by
  intro index point point_mem
  dsimp [normalization, proposition63IdentityFullOrdinaryNormalization]
    at point_mem
  rcases point_mem with ⟨sourcePoint, sourcePointMem, rfl⟩
  simpa using data.ordinary_axial_window
    (data.regularized.selected.embedding index) sourcePoint sourcePointMem

/-- The identity normalization retains the sharp first-chart direction
margin on its exact regularized subfamily. -/
theorem normalizationDirectionVertical
    {delta sigma sourceLoss targetLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (data : Proposition63PreLemma43DenseRootData source ambient
      targetLoss normalizationLoss normalizationExponent) :
    ∀ index, Real.sqrt 3 / 2 ≤
      wz1PaperDirection (data.normalization.croppedFamily.tube index)
        (2 : Fin 3) := by
  intro index
  change Real.sqrt 3 / 2 ≤
    wz1PaperDirection
      (data.regularized.selected.family.tube index) (2 : Fin 3)
  rw [data.regularized.selected.tube_eq]
  exact data.direction_vertical (data.regularized.selected.embedding index)

/-- Root companion for the dense pre-Lemma-4.3 normalization. -/
noncomputable def root
    {delta sigma sourceLoss targetLoss normalizationLoss densityLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (data : Proposition63PreLemma43DenseRootData source ambient
      targetLoss normalizationLoss normalizationExponent)
    (density_absorb :
      Kakeya.realRpowENN delta densityLoss ≤
        Kakeya.realRpowENN delta targetLoss / 2) :
    Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) data.ordinarySource
      normalizationExponent densityLoss :=
  Proposition63RootNormalizationData.ofNormalization
    data.normalization density_absorb

end Proposition63PreLemma43DenseRootData

/-- Convert a post-Lemma-4.3 current-shading re-entry into the existing
second-call package.  Both records use the identical selected family, trace
weight, dense crop, and normalization; this adapter makes that provenance
available to the M8 runner without another selection. -/
noncomputable def Proposition63CurrentShadingReentryData.toRegularizedReentry
    {delta sigma initialInputLoss rootNormalizationLoss
      lemma43SourceLoss lemma43Loss reentryLoss incidenceBudget : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {root : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := rootNormalizationLoss) initialSource
      normalizationExponent}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) root.croppedRefined
      incidenceBudget}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) root lemma43.shading)
    (reentry_loss_pos : 0 < reentryLoss)
    (lemma43_loss_le : lemma43Loss ≤ reentryLoss) :
    Proposition63RegularizedReentryData lemma43 data.ordinary
      reentryLoss data.reentryNormalizationLoss normalizationExponent where
  ambientConstant := data.ambientConstant
  outputConstant := data.outputConstant
  normalizationWeight := data.normalizationWeight
  weightUpper := data.weightUpper
  levelCount := data.levelCount
  schedule := data.schedule
  regularized := data.regularized
  lemma43_loss_le := lemma43_loss_le
  target_loss_pos := reentry_loss_pos
  normalization_loss_pos := data.reentry_normalization_loss_pos
  target_loss_le_half := data.reentry_loss_le_half
  normalization_weight_ne_zero := data.normalization_weight_ne_zero
  normalization_weight_ne_top := data.normalization_weight_ne_top
  output_le := data.output_le
  trace_level := data.trace_level
  dense_level := data.dense_level
  line_class := data.line_class
  ordinary_axial_window := data.ordinaryAxialWindow
  ordinary_bounded_base := data.ordinaryBoundedBase
  delta_small := data.delta_small
  ambient_top_level_constant := data.ambient_top_level_constant
  ambient_top_level_cwa := data.ambient_top_level_cwa
  top_level_absorb := data.top_level_absorb

/-- Lemma 4.3 run after the exact ordinary source has already been
regularized and dense-cubicalized. -/
structure Proposition63SameExtremizerThroughLemma43Data
    {delta sigma sourceLoss targetLoss normalizationLoss lemma43Loss
      incidenceBudget : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (pre : Proposition63PreLemma43DenseRootData source ambient
      targetLoss normalizationLoss normalizationExponent) where
  lemma43 : Proposition63Lemma43Data
    (sigma := sigma) (sourceLoss := targetLoss)
    (targetLoss := lemma43Loss) pre.denseShading incidenceBudget

/-- View the quarter-loss Lemma 4.3 output at the final re-entry loss. -/
noncomputable def Proposition63SameExtremizerThroughLemma43Data.reentryLemma43
    {delta sigma sourceLoss targetLoss normalizationLoss reentryLoss
      incidenceBudget : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    {pre : Proposition63PreLemma43DenseRootData source ambient
      targetLoss normalizationLoss normalizationExponent}
    (same : Proposition63M9SameExtremizerCutoffData
      targetLoss normalizationLoss reentryLoss)
    (through : Proposition63SameExtremizerThroughLemma43Data
      (lemma43Loss := same.losses.lemma43OutputLoss)
      (incidenceBudget := incidenceBudget) pre) :
    Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := targetLoss)
      (targetLoss := reentryLoss) pre.denseShading incidenceBudget where
  shading := through.lemma43.shading
  subshading := through.lemma43.subshading
  cubical := through.lemma43.cubical
  planeMap := through.lemma43.planeMap
  leftFactor := through.lemma43.leftFactor
  rightFactor := through.lemma43.rightFactor
  leftFactor_pos := through.lemma43.leftFactor_pos
  leftFactor_ne_top := through.lemma43.leftFactor_ne_top
  rightFactor_ne_top := through.lemma43.rightFactor_ne_top
  mass_retention := through.lemma43.mass_retention
  extremal := through.lemma43.extremal.mono_loss
    same.losses.lemma43_output_le_reentry

/-- Promote a prepared quarter-loss Lemma 4.3 record to the final re-entry
loss without changing its selected family, shading, weights, or receipts. -/
noncomputable def Proposition63RegularizedReentryData.promoteLemma43
    {delta sigma sourceLoss targetLoss rootNormalizationLoss reentryLoss
      normalizationLoss
      incidenceBudget : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    {pre : Proposition63PreLemma43DenseRootData source ambient
      targetLoss rootNormalizationLoss normalizationExponent}
    (same : Proposition63M9SameExtremizerCutoffData
      targetLoss rootNormalizationLoss reentryLoss)
    (through : Proposition63SameExtremizerThroughLemma43Data
      (lemma43Loss := same.losses.lemma43OutputLoss)
      (incidenceBudget := incidenceBudget) pre)
    {ordinary : Kakeya.Streamlined.TubeShading pre.ordinarySource.family}
    (prepared : Proposition63RegularizedReentryData through.lemma43 ordinary
      reentryLoss normalizationLoss normalizationExponent)
    :
    Proposition63RegularizedReentryData (through.reentryLemma43 same) ordinary
      reentryLoss normalizationLoss normalizationExponent := by
  exact {
    ambientConstant := prepared.ambientConstant
    outputConstant := prepared.outputConstant
    normalizationWeight := prepared.normalizationWeight
    weightUpper := prepared.weightUpper
    levelCount := prepared.levelCount
    schedule := prepared.schedule
    regularized := prepared.regularized
    lemma43_loss_le := le_rfl
    target_loss_pos := prepared.target_loss_pos
    normalization_loss_pos := prepared.normalization_loss_pos
    target_loss_le_half := prepared.target_loss_le_half
    normalization_weight_ne_zero := prepared.normalization_weight_ne_zero
    normalization_weight_ne_top := prepared.normalization_weight_ne_top
    output_le := prepared.output_le
    trace_level := prepared.trace_level
    dense_level := prepared.dense_level
    line_class := prepared.line_class
    ordinary_axial_window := prepared.ordinary_axial_window
    ordinary_bounded_base := prepared.ordinary_bounded_base
    delta_small := prepared.delta_small
    ambient_top_level_constant := prepared.ambient_top_level_constant
    ambient_top_level_cwa := prepared.ambient_top_level_cwa
    top_level_absorb := prepared.top_level_absorb
  }

/-- Invoke the literal paper Lemma 4.3 on the same dense root that retains
the exact ordinary image. -/
theorem Proposition63PreLemma43DenseRootData.runPaperLemma43
    {delta sigma sourceLoss targetLoss normalizationLoss reentryLoss
      densityLoss kappa tau incidenceBudget : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (pre : Proposition63PreLemma43DenseRootData source ambient
      targetLoss normalizationLoss normalizationExponent)
    (same : Proposition63M9SameExtremizerCutoffData
      targetLoss normalizationLoss reentryLoss)
    {C : ENNReal}
    (hsourceCWA : WZ2PaperConvexWolffBound
      pre.ordinarySource.family C)
    (hCTop : C ≠ ⊤)
    (hCV : ∀ (E : Set Point3), MeasurableSet E →
      E ⊆ pre.denseShading.union → ∀ (L : ENNReal),
        (∀ point ∈ E, L ≤
          (paperShadingTrilinearMultiplicity
            pre.denseShading point) ^ (1 / 2 : ℝ)) →
        L * volume E ≤
          C * (ENNReal.ofReal (delta ^ 2) *
            pre.ordinarySource.family.enncard) ^ (3 / 2 : ℝ))
    (hdensityLoss : densityLoss = 2 - sigma + 3 * targetLoss)
    (hsourceLoss : 0 < targetLoss)
    (hdeltaSmall : delta ≤ 1 / 10000)
    (hsmall : Kakeya.realRpowENN delta targetLoss < 1 / 4)
    (hkappa : 0 < kappa)
    (hkappaOne : kappa ≤ 1)
    (hdeltaKappa : delta ≤ kappa)
    (htau : 0 < tau)
    (hincidence : tau / kappa ≤ incidenceBudget)
    (hfixedAbsorb :
      (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * targetLoss))
    (hcloseBudget : ∀
      (high : WZ1PaperTubeShading pre.ordinarySource.family)
      (band : WZ2PaperGlobalMultiplicityBandData high),
        let X := C * ENNReal.ofReal (10000 * kappa ^ 2) *
          pre.ordinarySource.family.enncard
        let R := Nat.ceil X.toReal + 1
        12 * R ≤ 2 ^ band.level)
    (hbroadAbsorb : ∀
      (high : WZ1PaperTubeShading pre.ordinarySource.family)
      (band : WZ2PaperGlobalMultiplicityBandData high),
        let m := 2 ^ band.level
        let Q : ℕ := m ^ 3 / 4
        (2 : ENNReal) * (2 * m : ℕ) * C *
            (ENNReal.ofReal (delta ^ 2) *
              pre.ordinarySource.family.enncard) ^ (3 / 2 : ℝ) ≤
          (((Q : ENNReal) * ENNReal.ofReal tau) ^
            (1 / 2 : ℝ)) * band.band.mass)
    (hrestore : ∀
      (high : WZ1PaperTubeShading pre.ordinarySource.family)
      (band : WZ2PaperGlobalMultiplicityBandData high),
        proposition63PaperLemma43MassLoss
            (source := pre.denseShading) high band *
          Kakeya.realRpowENN delta same.losses.lemma43OutputLoss ≤
            Kakeya.realRpowENN delta targetLoss) :
    Nonempty (Proposition63SameExtremizerThroughLemma43Data
      (lemma43Loss := same.losses.lemma43OutputLoss)
      (incidenceBudget := incidenceBudget) pre) := by
  rcases proposition63_paper_lemma43_weak_plane_map pre.croppedExtremal
      (pre.line_class.subfamily pre.regularized.selected) hsourceCWA hCTop
      hCV hdensityLoss hsourceLoss same.losses.lemma43_output_pos
      same.losses.lemma43_source_le_output hdeltaSmall
      hsmall hkappa hkappaOne hdeltaKappa htau hincidence
      hfixedAbsorb hcloseBudget hbroadAbsorb hrestore with
    ⟨lemma43⟩
  exact ⟨⟨lemma43⟩⟩

/-- Run the post-Lemma-4.3 ordinary-trace regularization against the root
normalization built from the same pre-Lemma-4.3 ordinary source. -/
theorem Proposition63SameExtremizerThroughLemma43Data.prepareSecondCall
    {delta sigma sourceLoss targetLoss rootNormalizationLoss reentryLoss
      reentryNormalizationLoss incidenceBudget : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    {pre : Proposition63PreLemma43DenseRootData source ambient
      targetLoss rootNormalizationLoss normalizationExponent}
    (same : Proposition63M9SameExtremizerCutoffData
      targetLoss rootNormalizationLoss reentryLoss)
    (through : Proposition63SameExtremizerThroughLemma43Data
      (lemma43Loss := same.losses.lemma43OutputLoss)
      (incidenceBudget := incidenceBudget) pre)
    (delta_le_absorption : delta ≤ same.absorption.delta₀)
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := (pre.root (same.absorption.density_absorb
        pre.ordinarySource.extremal.delta_pos delta_le_absorption)
          ).normalization.croppedFamily)
      (Kakeya.realRpowENN delta (-rootNormalizationLoss))
      (Kakeya.realRpowENN delta (-reentryLoss))
      (proposition63CanonicalNearbyLevelCount rootNormalizationLoss))
    (ambient_two : (2 : ENNReal) <
      Kakeya.realRpowENN delta (-rootNormalizationLoss))
    (reentry_loss_pos : 0 < reentryLoss)
    (reentryNormalizationLoss_pos : 0 < reentryNormalizationLoss)
    (reentry_loss_le_half :
      reentryLoss ≤ reentryNormalizationLoss / 2)
    (rho : WZ2PaperRequestedScale delta)
    (rho_le : rho.1 ≤ 1 / 24) :
    ∃ current : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss)
        (pre.root (same.absorption.density_absorb
          pre.ordinarySource.extremal.delta_pos delta_le_absorption)
        ).normalization through.lemma43.shading,
      current.reentryNormalizationLoss = reentryNormalizationLoss ∧
        Nonempty (Proposition63SecondCallPreparationData through.lemma43
          current.ordinary reentryLoss current.reentryNormalizationLoss
          normalizationExponent rho) := by
  have delta_pos : 0 < delta := pre.ordinarySource.extremal.delta_pos
  have density_absorb := same.absorption.density_absorb
    delta_pos delta_le_absorption
  let root := pre.root density_absorb
  rcases root.currentShadingReentryFromExtremal through.lemma43.shading
      schedule ambient_two through.lemma43.extremal
      same.losses.lemma43_output_le_reentry
      same.losses.lemma43_output_pos
      reentryNormalizationLoss reentryNormalizationLoss_pos
      reentry_loss_le_half
      (same.absorption.canonical_weight_absorb delta_pos delta_le_absorption)
      (same.absorption.trace_fixed_absorb delta_pos delta_le_absorption)
      (same.absorption.paper_fixed_absorb delta_pos delta_le_absorption)
      (same.absorption.regularization_absorb root.normalization rfl schedule
        rfl rfl delta_pos delta_le_absorption) through.lemma43.subshading
      through.lemma43.cubical pre.delta_small with
    ⟨current, _, _, _, normalization_loss_eq⟩
  let prepared := current.toRegularizedReentry
    reentry_loss_pos same.losses.lemma43_output_le_reentry
  have tight_root := pre.normalizationAxialWindowTwentyFifth
  have tight_current : ∀ index point,
      point ∈ current.ordinary.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 25 :=
    fun index point point_mem => tight_root _ point point_mem.1
  exact ⟨current, normalization_loss_eq,
    ⟨Proposition63SecondCallPreparationData.ofPrepared
      prepared tight_current rho_le⟩⟩

/-- The complete same-extremizer second stage through Lemma 4.12.  The
dependent fields prevent replacing either the root ordinary source or the
post-Lemma-4.3 trace by an independently selected refinement. -/
structure Proposition63SameExtremizerThroughLemma412Data
    {sigma outputLoss delta sourceLoss densityLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    (pre : Proposition63PreLemma43DenseRootData source ambient
      cutoff.initial.lemma43SourceLoss
      cutoff.sameExtremizerRootNormalizationLoss normalizationExponent)
    (density_absorb :
      Kakeya.realRpowENN delta densityLoss ≤
        Kakeya.realRpowENN delta cutoff.initial.lemma43SourceLoss / 2)
    (rho : WZ2PaperRequestedScale delta) where
  lemma43 : Proposition63SameExtremizerThroughLemma43Data
    (lemma43Loss := cutoff.sameExtremizer.losses.lemma43OutputLoss)
    (incidenceBudget := rho.1 / 2) pre
  current : Proposition63CurrentShadingReentryData
    (reentryLoss := cutoff.richSchedule.sourceLoss)
    (pre.root density_absorb).normalization
    lemma43.lemma43.shading
  normalization_loss_eq :
    current.reentryNormalizationLoss = cutoff.richSchedule.normalizationLoss
  preparation : Proposition63SecondCallPreparationData
    lemma43.lemma43
    current.ordinary cutoff.richSchedule.sourceLoss
    cutoff.richSchedule.normalizationLoss normalizationExponent rho
  second : Proposition63ThroughLemma412Data
    (sigma := sigma)
    (lemma43SourceLoss := cutoff.initial.lemma43SourceLoss)
    (inputLoss := cutoff.richSchedule.sourceLoss)
    (normalizationLoss := cutoff.richSchedule.normalizationLoss)
    (normalizationExponent := normalizationExponent)
    (logExponent := 61) (lemma43.reentryLemma43 cutoff.sameExtremizer)
    current.ordinary
    (preparation.prepared.promoteLemma43 cutoff.sameExtremizer lemma43)
    hierarchy.stickyLoss hierarchy.lemma44Loss
    hierarchy.lemma47Loss hierarchy.preGrainLoss
    (Real.rpow rho.1 (-hierarchy.lemma47Loss))
  coarse_midpoint_local : ∀ parent,
    ‖wz2PaperTubeMidpoint (second.sticky.coarse.tube parent)‖ ≤ 3

/-- Close the genuine second rich call, Lemmas 4.4 and 4.7, and the M8
Lemma-4.12 schedule from the same pre-Lemma-4.3 ordinary extremizer. -/
theorem Proposition63SameExtremizerThroughLemma43Data.runSecondCallThroughLemma412
    {sigma outputLoss delta sourceLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {ambient : WZ1PaperTubeShading source.family}
    {normalizationExponent : ℕ}
    {pre : Proposition63PreLemma43DenseRootData source ambient
      cutoff.initial.lemma43SourceLoss
      cutoff.sameExtremizerRootNormalizationLoss normalizationExponent}
    (rho : WZ2PaperRequestedScale delta)
    (through : Proposition63SameExtremizerThroughLemma43Data
      (lemma43Loss := cutoff.sameExtremizer.losses.lemma43OutputLoss)
      (incidenceBudget := rho.1 / 2) pre)
    (delta_le_same_absorption :
      delta ≤ cutoff.sameExtremizer.absorption.delta₀)
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := (pre.root
        (cutoff.sameExtremizer.absorption.density_absorb
          pre.ordinarySource.extremal.delta_pos delta_le_same_absorption)
        ).normalization.croppedFamily)
      (Kakeya.realRpowENN delta
        (-cutoff.sameExtremizerRootNormalizationLoss))
      (Kakeya.realRpowENN delta (-cutoff.richSchedule.sourceLoss))
      (proposition63CanonicalNearbyLevelCount
        cutoff.sameExtremizerRootNormalizationLoss))
    (ambient_two : (2 : ENNReal) <
      Kakeya.realRpowENN delta
        (-cutoff.sameExtremizerRootNormalizationLoss))
    (delta_le : delta ≤ cutoff.outerScaleCeiling)
    (rho_lower : Real.rpow delta (1 - hierarchy.stickyLoss) ≤ rho.1)
    (rho_upper : rho.1 ≤ Real.rpow delta hierarchy.stickyLoss)
    (rho_le : rho.1 ≤ cutoff.outerScaleCeiling)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    Nonempty (Proposition63SameExtremizerThroughLemma412Data
      cutoff pre
        (cutoff.sameExtremizer.absorption.density_absorb
          pre.ordinarySource.extremal.delta_pos delta_le_same_absorption)
        rho) := by
  rcases through.prepareSecondCall cutoff.sameExtremizer
      delta_le_same_absorption schedule ambient_two
      cutoff.richSchedule.sourceLoss_pos
      cutoff.richSchedule.normalizationLoss_pos
      cutoff.richSchedule.sourceLoss_le_half rho
      (rho_le.trans cutoff.outerScaleCeiling_le_lemma412 |>.trans
        cutoff.lemma412Cutoff.rho_small) with
    ⟨current, normalization_loss_eq, ⟨preparation⟩⟩
  rw [normalization_loss_eq] at preparation
  let reentryLemma43 := through.reentryLemma43 cutoff.sameExtremizer
  let reentryPrepared := preparation.prepared.promoteLemma43
    cutoff.sameExtremizer through
  let reentryPreparation : Proposition63SecondCallPreparationData
      reentryLemma43 current.ordinary cutoff.richSchedule.sourceLoss
      cutoff.richSchedule.normalizationLoss normalizationExponent rho := {
    prepared := reentryPrepared
    root_axial_margin := preparation.root_axial_margin
  }
  rcases cutoff.runSecondCallThroughLemma412
      (_incidenceBudget := rho.1 / 2) reentryPreparation delta_le
      rho_lower rho_upper rho_le hsigma hsigmaOne with
    ⟨second, coarse_midpoint_local⟩
  exact ⟨{
    lemma43 := through
    current := current
    normalization_loss_eq := normalization_loss_eq
    preparation := preparation
    second := second
    coarse_midpoint_local := coarse_midpoint_local
  }⟩

/-- Reattach the first-chart global slice estimate to the selected dense
Lemma-4.3 source.  The source inclusion is the composite of the second-call
trace restriction and the pre-Lemma-4.3 dense-root inclusion, so no
definitionally equal source or independently selected refinement is used. -/
theorem Proposition63SameExtremizerThroughLemma412Data.preGrain
    {delta Delta sigma sticky1Loss localLoss commonSliceLoss chartLoss
      densityLoss tau epsilon₁ epsilon₃
      coefficient retainedLoss outputLoss initialInputLoss
      initialOutputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    {initialSource : PureWZ2ExtremalConfiguration
      sigma initialInputLoss delta}
    {firstScale : WZ2PaperRequestedScale delta}
    {firstLogExponent initialNormalizationExponent normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := initialOutputLoss) initialSource
      initialNormalizationExponent)
    {firstSticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := sticky1Loss)
      initialNormalized.croppedRefined firstScale firstLogExponent}
    {retainedFactor : ENNReal}
    (first : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := coefficient)
      firstSticky Delta retainedFactor)
    (massLower :
      Kakeya.realRpowENN (delta / firstScale.1) chartLoss *
            (first.chartRescaled.refreshedFullFiberOutput
              ).rescalingCertificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / firstScale.1 : ℝ) ^ 2)) *
          (initialNormalized.finalOrdinaryTrace
            (firstSticky.selected.comp first.metricFiber.fiberFamily)
            first.chartSelection.sourceShading).mass)
    (slopes : first.chartSelection.Proposition63SlopeData)
    {pre : Proposition63PreLemma43DenseRootData
      (proposition63ChartOrdinaryExtremalSourceOfTraceMass
        initialNormalized
        (firstSticky.selected.comp first.metricFiber.fiberFamily)
        first.chartSelection.sourceShading
        (firstSticky.coarse.tube first.metricFiber.parent)
        firstSticky.coarse_extremal.delta_pos
        first.chartRescaled.refreshedFullFiberOutput massLower
        first.chartSelection.chartLabel.chart)
      (first.chartSelection.normalizedShading first.chartRescaled)
      cutoff.initial.lemma43SourceLoss
      cutoff.sameExtremizerRootNormalizationLoss normalizationExponent}
    {density_absorb :
      Kakeya.realRpowENN (delta / firstScale.1) densityLoss ≤
        Kakeya.realRpowENN (delta / firstScale.1)
          cutoff.initial.lemma43SourceLoss / 2}
    {secondScale : WZ2PaperRequestedScale (delta / firstScale.1)}
    (data : Proposition63SameExtremizerThroughLemma412Data
      cutoff pre density_absorb secondScale)
    (hsecondDelta : secondScale.1 = Delta)
    (hrhoDelta : firstScale.1 = Delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hglobalCost :
      Proposition63ChartSelectionData.proposition63CoarseGlobalADConstant
          delta firstScale.1 Delta localLoss coefficient ≤
        Kakeya.realRpowENN secondScale.1 (-hierarchy.preGrainLoss)) :
    Nonempty (PureWZ2GeneralPreGrainData data.second.lemma412.shading sigma
      hierarchy.preGrainLoss
      (Real.toNNReal (Real.rpow secondScale.1 (-hierarchy.lemma47Loss)))
      (252000 * Real.toNNReal coefficient) 1) := by
  apply Proposition63ThroughLemma412Data.preGrain
    (retainedLoss := retainedLoss) first slopes data.current.ordinary
      (data.preparation.prepared.promoteLemma43
        cutoff.sameExtremizer data.lemma43) data.second
  · exact (data.preparation.prepared.promoteLemma43
        cutoff.sameExtremizer data.lemma43
      ).restrictedLemma43_union_subset_source.trans
      pre.denseUnionSubsetAmbient
  · exact hsecondDelta
  · exact hrhoDelta
  · exact hsigma
  · exact hsigmaOne
  · exact hglobalCost

end Kakeya.Assouad.PureWZ2

end
