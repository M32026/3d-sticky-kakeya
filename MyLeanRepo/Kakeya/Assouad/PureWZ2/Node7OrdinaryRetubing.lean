import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7AffineExactShading
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.SameAxisThickening
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance

/-!
# Ordinary retubing of the Node 7 cubical affine image

The radius-six family first contains the literal affine image.  The final
radius-twelve family contains its target-grid saturation, so the Section 7
ordinary shading is cubical without changing indices or axes.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

namespace PureWZ2Node7AffineDiagonalPreparationData

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}

/-- Final ordinary radius after target-grid saturation. -/
def finalRadius
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) : ℝ :=
  12 * data.node7Scale.affineScale.targetDelta

theorem finalRadius_pos
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    0 < data.finalRadius := by
  unfold finalRadius
  positivity [data.affineScale.targetDelta_pos]

theorem finalRadius_le_six_fifths
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    data.finalRadius ≤ 6 / 5 := by
  unfold finalRadius
  linarith [data.affineScale.targetDelta_le_tenth]

/-- Source-scale upper bound for the final radius, retaining the exact
affine exponent used by all pre-runtime absorption arguments. -/
theorem finalRadius_le_source_power
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    data.finalRadius ≤ 60000 * Real.rpow delta (1 - epsilon) := by
  unfold finalRadius
  calc
    12 * data.node7Scale.affineScale.targetDelta ≤
        12 * (5000 * Real.rpow delta (1 - epsilon)) := by
      gcongr
      exact data.node7Scale.targetDelta_le_source_power
    _ = 60000 * Real.rpow delta (1 - epsilon) := by ring

theorem finalRadius_le_one_of_targetDelta_le_twelfth
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (hsmall : data.affineScale.targetDelta ≤ 1 / 12) :
    data.finalRadius ≤ 1 := by
  unfold finalRadius
  linarith

/-- A source-scale cutoff making the final radius smaller than any prescribed
positive threshold.  The cutoff is chosen before the runtime source. -/
theorem exists_source_cutoff_for_finalRadius
    (epsilon threshold : ℝ)
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon < 1)
    (hthreshold : 0 < threshold) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {sigma delta : ℝ}
        {commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta}
        (data : PureWZ2Node7AffineDiagonalPreparationData commonSource),
        0 < delta → delta ≤ delta₀ → data.finalRadius ≤ threshold := by
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := threshold / 60000) (s := 1 - epsilon)
      (by positivity) (by linarith) with
    ⟨delta₀, hdelta₀, hdelta₀One, hpower⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro logExponent sigma delta commonSource data hdelta hdeltaBound
  have hscale := data.node7Scale.targetDelta_le_source_power
  have hsmall := hpower delta hdelta hdeltaBound
  unfold finalRadius
  calc
    12 * data.node7Scale.affineScale.targetDelta ≤
        12 * (5000 * Real.rpow delta (1 - epsilon)) := by gcongr
    _ ≤ 12 * (5000 * (threshold / 60000)) := by gcongr
    _ = threshold := by ring

/-- Intermediate ordinary carrier for the literal affine image. -/
def exactOrdinaryFamily
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    Kakeya.Streamlined.TubeFamily
      (6 * data.node7Scale.affineScale.targetDelta) :=
  sameAxisTubeFamily
    (rho := 6 * data.node7Scale.affineScale.targetDelta)
    data.selected.localizedFamily

/-- The exact affine image lies in the radius-six unit-segment tube having the
same zero-based, positively oriented axis. -/
theorem exactShading_carrier_subset_exactOrdinaryFamily
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (index : Fin data.exactOrdinaryFamily.card) :
    data.exactShading.carrier index ⊆
      (data.exactOrdinaryFamily.tube index).carrier := by
  intro point hpoint
  let scale := data.node7Scale.affineScale
  let target := data.selected.localizedFamily.tube index
  have hline : WZ1PaperTubeInLineClass target :=
    data.selected.localized_line_class index
  have htargetVertical : target.direction (2 : Fin 3) ≠ 0 := by
    intro hzero
    have hvertical := hline.vertical
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  have hheightPoint := data.exactShading_active_height index point hpoint
  rcases hpoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  have hsourceThick :=
    (data.sourceExactShading.subset_body index hsourcePoint).1
  rcases exists_dist_le_of_mem_cthickening_closed
      (isClosed_tubeAxisLine
        (data.sourceRegularization.regularized.selected.family.tube index))
      (mul_nonneg (by norm_num)
        commonSource.commonBand.band.lemma31.data.cfg.extremal.delta_pos.le)
      hsourceThick with
    ⟨sourceAxisPoint, hsourceAxisPoint, hsourceDistance⟩
  let imagePoint :=
    pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope
      data.selected.center scale.slopeData.heightScale
      scale.slopeData.transverseScale 1 sourcePoint
  let imageAxisPoint :=
    pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope
      data.selected.center scale.slopeData.heightScale
      scale.slopeData.transverseScale 1 sourceAxisPoint
  have himageAxis : imageAxisPoint ∈ tubeAxisLine target := by
    dsimp only [target, imageAxisPoint]
    rw [data.selected.localized_axis index]
    exact ⟨sourceAxisPoint, hsourceAxisPoint, rfl⟩
  have himageDistance : dist imagePoint imageAxisPoint ≤
      3 * scale.targetDelta := by
    rw [dist_eq_norm]
    have hdiff : imagePoint - imageAxisPoint =
        pureWZ2AffineDiagonalLinear scale.slopeData.frameSlope
          scale.slopeData.heightScale scale.slopeData.transverseScale 1
          (sourcePoint - sourceAxisPoint) := by
      dsimp only [imagePoint, imageAxisPoint]
      exact pureWZ2AffineDiagonalMapCentered_sub _ _ _ _ _ _ _
    rw [hdiff]
    calc
      ‖pureWZ2AffineDiagonalLinear scale.slopeData.frameSlope
          scale.slopeData.heightScale scale.slopeData.transverseScale 1
          (sourcePoint - sourceAxisPoint)‖ ≤
          scale.slopeData.heightScale * ‖sourcePoint - sourceAxisPoint‖ :=
        pureWZ2AffineDiagonalLinear_norm_le_height _
          (by linarith [scale.height_lower]) scale.transverse_pos.le
          (scale.transverse_le.trans (by norm_num)) _
      _ ≤ scale.slopeData.heightScale * (6 * delta) := by
        apply mul_le_mul_of_nonneg_left
        · simpa [dist_eq_norm] using hsourceDistance
        · linarith [scale.height_lower]
      _ = 3 * scale.targetDelta := by
        rw [scale.targetDelta_eq]
        ring
  let axisPoint := wz1PaperAxisPointAtHeight target (imagePoint 2)
  have haxisDistance : dist axisPoint imagePoint ≤
      6 * scale.targetDelta := by
    exact (wz1Paper_axisPointAtHeight_dist_point_le_two_mul
      hline imagePoint imageAxisPoint himageAxis).trans (by
        linarith [himageDistance])
  have hheight : 0 ≤ imagePoint 2 ∧ imagePoint 2 ≤ 1 / 2 := by
    simpa only [imagePoint] using hheightPoint
  have hzeroBased := data.selected.localized_zeroBased index
  have hbase : target.base = wz1TubeAxisZeroPoint target := by
    have raw := congrArg Kakeya.DeltaTube.base hzeroBased
    exact raw.symm
  have hdirection : target.direction = wz1PaperDirection target := by
    have raw := congrArg Kakeya.DeltaTube.direction hzeroBased
    exact raw.symm
  let parameter := imagePoint 2 / wz1PaperDirection target 2
  have hvertical : 0 < wz1PaperDirection target 2 := by
    linarith [hline.1]
  have hparameter : parameter ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [parameter]
    constructor
    · exact div_nonneg hheight.1 hvertical.le
    · exact (div_le_one hvertical).2 (by linarith [hheight.2, hline.1])
  have haxisSegment : axisPoint ∈
      Kakeya.unitSegment target.base target.direction := by
    refine ⟨parameter, hparameter, ?_⟩
    dsimp only [axisPoint, wz1PaperAxisPointAtHeight, parameter]
    rw [hbase, hdirection]
  change imagePoint ∈ Metric.cthickening (6 * scale.targetDelta)
    (Kakeya.unitSegment target.base target.direction)
  exact Metric.mem_cthickening_of_dist_le imagePoint axisPoint
    (6 * scale.targetDelta) _ haxisSegment (by simpa [dist_comm] using haxisDistance)

/-- The literal exact-image fibers at the intermediate radius-six scale. -/
def exactOrdinaryShading
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    Kakeya.Streamlined.TubeShading data.exactOrdinaryFamily where
  carrier index := data.exactShading.carrier index
  measurable_carrier index := data.exactShading.measurable_carrier index
  subset_body index :=
    data.exactShading_carrier_subset_exactOrdinaryFamily index

/-- The final ordinary family has the same axes and radius twelve times the
affine target scale. -/
def ordinaryFamily
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    Kakeya.Streamlined.TubeFamily data.finalRadius :=
  sameAxisTubeFamily
    (rho := data.finalRadius)
    data.selected.localizedFamily

/-- The radius-twelve carrier contains the synchronized target-grid
saturation.  A saturated point is within `2Δ` of an exact image, while that
exact image already lies in the radius-`6Δ` unit-segment carrier. -/
theorem localizedShading_carrier_subset_ordinaryFamily
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (index : Fin data.ordinaryFamily.card) :
    data.selected.localizedShading.carrier index ⊆
      (data.ordinaryFamily.tube index).carrier := by
  intro point hpoint
  rcases data.selected.shading_carrier
      (data.selected.localizedToPublicIndex index) ▸ hpoint with
    ⟨exactPoint, hexactImage, hcell⟩
  have hexactCarrier : exactPoint ∈ data.exactShading.carrier index := by
    have hindex : data.selected.localizedToPublicIndex index = index := rfl
    rw [hindex] at hexactImage
    change exactPoint ∈
      pureWZ2AffineDiagonalMapCentered
          data.affineScale.slopeData.frameSlope data.selected.center
          data.affineScale.slopeData.heightScale
          data.affineScale.slopeData.transverseScale 1 ''
        data.popular.popular.restricted.carrier
          (data.sourceRegularization.regularized.selected.embedding index)
    exact hexactImage
  have hexactOrdinary :=
    data.exactShading_carrier_subset_exactOrdinaryFamily index hexactCarrier
  have hsegmentCompact : IsCompact
      (Kakeya.unitSegment
        (data.selected.localizedFamily.tube index).base
        (data.selected.localizedFamily.tube index).direction) := by
    exact isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  rcases exists_dist_le_of_mem_cthickening_closed hsegmentCompact.isClosed
      (mul_nonneg (by norm_num) data.affineScale.targetDelta_pos.le)
      hexactOrdinary with ⟨axisPoint, haxisPoint, hexactDistance⟩
  have hpointDistance : dist point exactPoint <
      2 * data.affineScale.targetDelta := by
    apply wz1_paper_grid_cube_diameter_lt_two_rho
      data.affineScale.targetDelta_pos
      (cell := wz1PaperGridIndex data.affineScale.targetDelta point)
    · exact (mem_wz1PaperGridCube _ _ _).mpr rfl
    · exact (mem_wz1PaperGridCube _ _ _).mpr hcell.symm
  change point ∈ Metric.cthickening (12 * data.affineScale.targetDelta)
    (Kakeya.unitSegment
      (data.selected.localizedFamily.tube index).base
      (data.selected.localizedFamily.tube index).direction)
  exact Metric.mem_cthickening_of_dist_le point axisPoint _ _ haxisPoint <|
    le_of_lt <| by
    calc
      dist point axisPoint ≤ dist point exactPoint + dist exactPoint axisPoint :=
        dist_triangle _ _ _
      _ < 2 * data.affineScale.targetDelta +
          6 * data.affineScale.targetDelta :=
        add_lt_add_of_lt_of_le hpointDistance hexactDistance
      _ ≤ 12 * data.affineScale.targetDelta := by
        nlinarith [data.affineScale.targetDelta_pos]

/-- The synchronized cubical saturation, now regarded as an ordinary
shading on the radius-twelve family. -/
def ordinaryShading
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    Kakeya.Streamlined.TubeShading data.ordinaryFamily where
  carrier index := data.selected.localizedShading.carrier index
  measurable_carrier index :=
    data.selected.localizedShading.measurable_carrier index
  subset_body index := data.localizedShading_carrier_subset_ordinaryFamily index

@[simp] theorem ordinaryShading_carrier
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (index : Fin data.ordinaryFamily.card) :
    data.ordinaryShading.carrier index =
      data.selected.localizedShading.carrier index :=
  rfl

theorem ordinaryFamily_nonempty
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    data.ordinaryFamily.Nonempty := by
  change 0 < data.sourceRegularization.regularized.selected.family.card
  exact data.sourceRegularization.regularized.selected_nonempty

theorem ordinaryFamily_hasBoundedBase
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    HasBoundedBase data.ordinaryFamily 4 := by
  apply sameAxisTubeFamily_hasBoundedBase
  intro index
  have hfixed := data.selected.localized_zeroBased index
  have hbase := congrArg (fun tube => tube.base) hfixed
  have hbaseEq :
      (data.selected.localizedFamily.tube index).base =
        wz1TubeAxisZeroPoint (data.selected.localizedFamily.tube index) := by
    simpa only [pureWZ2PaperZeroBasedTube] using hbase.symm
  rw [hbaseEq]
  exact (pureWZ2_zeroPoint_norm_le_one
    (data.selected.localized_line_class index)).trans (by norm_num)

theorem ordinaryFamily_isInVerticalChart
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    IsInVerticalChart data.ordinaryFamily := by
  apply sameAxisTubeFamily_isInVerticalChart
  intro index
  exact (data.selected.localized_line_class index).vertical

theorem ordinaryShading_isInSlopeWindow
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    IsInSlopeWindow data.ordinaryShading := by
  intro point hpoint
  rcases hpoint with ⟨index, hindex⟩
  have hbox := data.selected.localizedShading.subset_body index hindex |>.2
  simpa [Kakeya.Streamlined.axisBox, horizontalSlab, abs_le] using hbox.2.2

theorem ordinaryShading_mass
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    data.ordinaryShading.mass = data.selected.localizedShading.mass := by
  rfl

theorem ordinaryShading_mass_lower
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    (ENNReal.ofReal
          data.node7Scale.affineScale.slopeData.rotatedSlopeScale *
        data.sourceRegularization.regularized.selectedWeightLevel) *
        data.ordinaryFamily.enncard ≤
      data.ordinaryShading.mass := by
  change
    (ENNReal.ofReal
          data.node7Scale.affineScale.slopeData.rotatedSlopeScale *
        data.sourceRegularization.regularized.selectedWeightLevel) *
        data.selected.localizedFamily.enncard ≤
      data.selected.localizedShading.mass
  have hexactMass : data.exactShading.mass ≤
      data.selected.localizedShading.mass := by
    apply Finset.sum_le_sum
    intro index _
    exact measure_mono (data.exactShading_sub_finalShading index)
  exact data.exactShading_mass_lower.trans hexactMass

theorem ordinaryShading_union
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    data.ordinaryShading.union = data.selected.localizedShading.union := by
  rfl

end PureWZ2Node7AffineDiagonalPreparationData

end Kakeya.Assouad

end
