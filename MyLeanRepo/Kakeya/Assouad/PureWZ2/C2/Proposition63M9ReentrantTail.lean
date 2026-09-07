import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition63M9QuantitativeTail
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantSource
import MyLeanRepo.Kakeya.Assouad.PureWZ2.DenseCubicalTrace
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DenseCubicalizationRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9NestedPreGrainSource

/-!
# Re-entry-aware quantitative receipt for the Proposition 6.3 M9 tail

The construction-aware M9 tail retains the exact final slope and plane map.
This private receipt adds the critical volume floor and ordinary re-entry on
that same final shading.  No independently selected grain or re-entry witness
can be inserted after the receipt has been formed.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory

namespace Proposition63M9MildRescalingSourceData

/-- The source-side finite regularization stays inside the exact ancestor
shading whose ordinary re-entry was retained by the nested M9 construction. -/
theorem refined_sub_ancestor
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    (data : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant) :
    ∀ index, data.refined.carrier index ⊆
      source.ancestorShading.carrier (data.selected.embedding index) := by
  intro index point pointMem
  exact source.shading_sub_ancestor _
    (data.boxed_subshading _
      (data.refined_sub_boxed index pointMem))

/-- The exact ancestor ordinary trace retained inside the source-side
whole-cell regularization. -/
noncomputable def refinedOrdinaryOverlap
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    (data : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant) :
    WZ1PaperTubeShading data.selected.family where
  carrier index :=
    (source.ancestorReentry.geometry.frame ''
      source.ancestorReentry.geometry.ordinaryRefined.carrier
        (source.ancestorReentry.geometry.indexEquiv.symm
          (data.selected.embedding index))) ∩
      data.refined.carrier index
  measurable_carrier index :=
    (source.ancestorReentry.geometry.frame.toHomeomorph.measurableEmbedding
      |>.measurableSet_image'
        (source.ancestorReentry.geometry.ordinaryRefined.measurable_carrier
          (source.ancestorReentry.geometry.indexEquiv.symm
            (data.selected.embedding index)))).inter
      (data.refined.measurable_carrier index)
  subset_body index point pointMem :=
    data.refined.subset_body index pointMem.2

/-- Dense cubicalization gives a quantitative ordinary-overlap lower bound on
every source tube retained by the M9 finite regularization. -/
theorem refinedOrdinaryOverlap_per_tube
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    (data : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant)
    (index : Fin data.selected.family.card) :
    (100 : ENNReal)⁻¹ *
          source.ancestorReentry.geometry.ordinaryDensity *
          volume (data.refined.carrier index) ≤
      volume ((data.refinedOrdinaryOverlap source hsourceLoss).carrier index) := by
  let ordinaryIndex :=
    source.ancestorReentry.geometry.indexEquiv.symm
      (data.selected.embedding index)
  let ordinary :=
    source.ancestorReentry.geometry.frame ''
      source.ancestorReentry.geometry.ordinaryRefined.carrier ordinaryIndex
  let cropped := data.refined.carrier index
  let tube := source.family.tube (data.selected.embedding index)
  have hcropped : cropped ⊆ pureWZ2DenseCubicalization tube ordinary := by
    intro point pointMem
    have ancestorMem :=
      data.refined_sub_ancestor source hsourceLoss index pointMem
    have hdense :=
      source.ancestorReentry.geometry.cropped_carrier_eq_dense_cubicalization
        ordinaryIndex
    rw [source.ancestorReentry.geometry.indexEquiv.apply_symm_apply
      (data.selected.embedding index)] at hdense
    rw [hdense] at ancestorMem
    exact ancestorMem
  have hordinaryMeasurable : MeasurableSet ordinary :=
    source.ancestorReentry.geometry.frame.toHomeomorph.measurableEmbedding
      |>.measurableSet_image'
        (source.ancestorReentry.geometry.ordinaryRefined.measurable_carrier
          ordinaryIndex)
  have htrace := pureWZ2_dense_cubical_trace
    source.ancestorReentry.cropped_extremal.delta_pos tube ordinary cropped
    hordinaryMeasurable (data.refined.measurable_carrier index)
    (data.refined_cubical index) hcropped
  have hordinaryVolume :
      volume ordinary =
        volume
          (source.ancestorReentry.geometry.ordinaryRefined.carrier
            ordinaryIndex) :=
    Kakeya.Streamlined.AffineIsometryEquiv.volume_image
      source.ancestorReentry.geometry.frame _
      (source.ancestorReentry.geometry.ordinaryRefined.measurable_carrier
        ordinaryIndex)
  have hsourceTubeVolume :
      volume
          (source.ancestorReentry.geometry.selected.family.tube
            ordinaryIndex).carrier =
        volume tube.carrier := by
    have hframeVolume :=
      Kakeya.Streamlined.AffineIsometryEquiv.volume_image
        source.ancestorReentry.geometry.frame
        (source.ancestorReentry.geometry.selected.family.tube
          ordinaryIndex).carrier
        (wz2_paper_ordinary_tube_carrier_measurable
          (source.ancestorReentry.geometry.selected.family.tube ordinaryIndex)
          source.ancestorReentry.cropped_extremal.delta_pos)
    have hcarrier :=
      source.ancestorReentry.geometry.ordinary_carrier_image_eq ordinaryIndex
    rw [source.ancestorReentry.geometry.indexEquiv.apply_symm_apply
      (data.selected.embedding index)] at hcarrier
    calc
      volume
          (source.ancestorReentry.geometry.selected.family.tube
            ordinaryIndex).carrier =
          volume
            (source.ancestorReentry.geometry.frame ''
              (source.ancestorReentry.geometry.selected.family.tube
                ordinaryIndex).carrier) :=
        hframeVolume.symm
      _ = volume tube.carrier := by rw [← hcarrier]
  have hordinaryDensity :
      source.ancestorReentry.geometry.ordinaryDensity *
          volume tube.carrier ≤
        volume ordinary := by
    rw [← hsourceTubeVolume, hordinaryVolume]
    exact source.ancestorReentry.geometry.ordinary_per_tube ordinaryIndex
  have htubePositive : 0 < volume tube.carrier :=
    wz2_paper_ordinary_tube_volume_pos tube
      source.ancestorReentry.cropped_extremal.delta_pos
  have htubeTop : volume tube.carrier ≠ ⊤ :=
    wz2_paper_ordinary_tube_volume_ne_top tube
      source.ancestorReentry.cropped_extremal.delta_pos
  have hdensityRatio :
      source.ancestorReentry.geometry.ordinaryDensity ≤
        volume ordinary * (volume tube.carrier)⁻¹ := by
    calc
      source.ancestorReentry.geometry.ordinaryDensity =
          (source.ancestorReentry.geometry.ordinaryDensity *
            volume tube.carrier) * (volume tube.carrier)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel htubePositive.ne' htubeTop,
          mul_one]
      _ ≤ volume ordinary * (volume tube.carrier)⁻¹ := by
        gcongr
  calc
    (100 : ENNReal)⁻¹ *
          source.ancestorReentry.geometry.ordinaryDensity *
          volume cropped ≤
        (100 : ENNReal)⁻¹ *
          (volume ordinary * (volume tube.carrier)⁻¹) *
            volume cropped := by
      gcongr
    _ = (100 : ENNReal)⁻¹ * volume ordinary *
          (volume tube.carrier)⁻¹ * volume cropped := by ring
    _ ≤ volume (ordinary ∩ cropped) := htrace
    _ = volume ((data.refinedOrdinaryOverlap source hsourceLoss).carrier index) :=
      rfl

/-- The pointwise trace estimate controls the complete source-side
regularized shading mass. -/
theorem refinedOrdinaryOverlap_mass_lower
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    (data : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant) :
    (100 : ENNReal)⁻¹ *
          source.ancestorReentry.geometry.ordinaryDensity *
          data.refined.mass ≤
      (data.refinedOrdinaryOverlap source hsourceLoss).mass := by
  change
    ((100 : ENNReal)⁻¹ *
        source.ancestorReentry.geometry.ordinaryDensity) *
          (∑ index : Fin data.selected.family.card,
            volume (data.refined.carrier index)) ≤
      ∑ index : Fin data.selected.family.card,
        volume ((data.refinedOrdinaryOverlap source hsourceLoss).carrier index)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun index _ =>
    data.refinedOrdinaryOverlap_per_tube source hsourceLoss index

/-- Every source-side ordinary overlap retained by M9 has positive mass. -/
theorem refinedOrdinaryOverlap_volume_pos
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    (data : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant)
    (index : Fin data.selected.family.card) :
    0 < volume ((data.refinedOrdinaryOverlap source hsourceLoss).carrier index) := by
  have sourceDensityPos : 0 < data.sourceDensity := by
    rw [data.sourceDensity_eq]
    apply ENNReal.mul_pos
    · apply (ENNReal.ofReal_pos.mpr ?_).ne'
      have scalePos : 0 < scale := zero_lt_one.trans_le hscale
      positivity
    · simp only [Kakeya.realRpowENN]
      exact (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos source.delta_pos source.tailSourceLoss)).ne'
  have sourceScalePos : 0 < Kakeya.realRpowENN source.delta 2 := by
    simp only [Kakeya.realRpowENN]
    exact ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos source.delta_pos 2)
  have refinedPos : 0 < volume (data.refined.carrier index) :=
    (ENNReal.mul_pos
      (ENNReal.mul_pos (by norm_num) sourceDensityPos.ne').ne'
      sourceScalePos.ne').trans_le (data.refined_per_tube index)
  have lowerPos : 0 <
      (100 : ENNReal)⁻¹ *
        source.ancestorReentry.geometry.ordinaryDensity *
          volume (data.refined.carrier index) := by
    exact ENNReal.mul_pos
      (ENNReal.mul_pos (ENNReal.inv_pos.mpr (by norm_num)).ne'
        source.ancestorReentry.geometry.ordinaryDensity_pos.ne').ne'
      refinedPos.ne'
  exact lowerPos.trans_le
    (data.refinedOrdinaryOverlap_per_tube source hsourceLoss index)

/-- Restricting the ancestor ordinary trace by the retained whole cells
recovers the exact M9 source shading under dense cubicalization. -/
theorem denseCubicalization_refinedOrdinaryOverlap_eq
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    (data : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant)
    (index : Fin data.selected.family.card) :
    pureWZ2DenseCubicalization
        (source.family.tube (data.selected.embedding index))
        ((source.ancestorReentry.geometry.frame ''
            source.ancestorReentry.geometry.ordinaryRefined.carrier
              (source.ancestorReentry.geometry.indexEquiv.symm
                (data.selected.embedding index))) ∩
          data.refined.carrier index) =
      data.refined.carrier index := by
  apply pureWZ2DenseCubicalization_inter_whole_cells
  · exact source.ancestorReentry.cropped_extremal.delta_pos
  · intro point pointMem
    have ancestorMem :=
      data.refined_sub_ancestor source hsourceLoss index pointMem
    have hdense :=
      source.ancestorReentry.geometry.cropped_carrier_eq_dense_cubicalization
        (source.ancestorReentry.geometry.indexEquiv.symm
          (data.selected.embedding index))
    rw [source.ancestorReentry.geometry.indexEquiv.apply_symm_apply
      (data.selected.embedding index)] at hdense
    rwa [← hdense]
  · exact data.refined_cubical index
  · exact data.refinedOrdinaryOverlap_volume_pos source hsourceLoss index

/-- A point on a paper line is the canonical point of that same height. -/
private theorem axisPointAtHeight_eq_of_mem_axis
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta)
    (tubeLine : WZ1PaperTubeInLineClass tube)
    (point : Point3)
    (pointMem : point ∈ tubeAxisLine tube) :
    wz1PaperAxisPointAtHeight tube (point (2 : Fin 3)) = point := by
  rcases wz1Paper_axis_exists_parameter tubeLine pointMem with
    ⟨parameter, rfl⟩
  have zeroTwo :
      wz1TubeAxisZeroPoint tube (2 : Fin 3) = 0 :=
    wz1TubeAxisZeroPoint_coord_two tube tubeLine.vertical
  have directionTwo :
      wz1PaperDirection tube (2 : Fin 3) ≠ 0 := by
    linarith [tubeLine.1]
  unfold wz1PaperAxisPointAtHeight
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, zeroTwo]
  rw [zero_add]
  field_simp

/-- The central height window of a canonical centered paper line lies in its
ordinary unit segment. -/
private theorem centered_axisPointAtHeight_mem_segment
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta)
    (tubeLine : WZ1PaperTubeInLineClass tube)
    (tubeCentered : proposition63CenteredTube tube = tube)
    {height : ℝ}
    (heightWindow : |height| ≤ 1 / 4) :
    wz1PaperAxisPointAtHeight tube height ∈
      Kakeya.unitSegment tube.base tube.direction := by
  have verticalPos : 0 < wz1PaperDirection tube (2 : Fin 3) := by
    linarith [tubeLine.1]
  have parameterLower :
      0 ≤ 1 / 2 + height / wz1PaperDirection tube (2 : Fin 3) := by
    have heightLower : -(1 / 4 : ℝ) ≤ height :=
      (abs_le.mp heightWindow).1
    have quotientLower :
        -(1 / 2 : ℝ) ≤
          height / wz1PaperDirection tube (2 : Fin 3) := by
      rw [le_div_iff₀ verticalPos]
      nlinarith [tubeLine.1]
    linarith
  have parameterUpper :
      1 / 2 + height / wz1PaperDirection tube (2 : Fin 3) ≤ 1 := by
    have heightUpper : height ≤ (1 / 4 : ℝ) :=
      (abs_le.mp heightWindow).2
    have quotientUpper :
        height / wz1PaperDirection tube (2 : Fin 3) ≤ 1 / 2 := by
      rw [div_le_iff₀ verticalPos]
      nlinarith [tubeLine.1]
    linarith
  refine
    ⟨1 / 2 + height / wz1PaperDirection tube (2 : Fin 3),
      ⟨parameterLower, parameterUpper⟩, ?_⟩
  have centeredBase := congrArg Kakeya.DeltaTube.base tubeCentered
  have centeredDirection :=
    congrArg Kakeya.DeltaTube.direction tubeCentered
  change
    tube.base +
        (1 / 2 + height / wz1PaperDirection tube (2 : Fin 3)) •
          tube.direction =
      wz1TubeAxisZeroPoint tube +
        (height / wz1PaperDirection tube (2 : Fin 3)) •
          wz1PaperDirection tube
  change
    wz1TubeAxisZeroPoint tube -
        (1 / 2 : ℝ) • wz1PaperDirection tube =
      tube.base at centeredBase
  change wz1PaperDirection tube = tube.direction at centeredDirection
  rw [← centeredBase, ← centeredDirection]
  module

/-- A source ordinary-carrier point in the production M9 core is sent into
the canonical centered target ordinary carrier.  The proof uses the source
unit-segment carrier, not the larger cropped paper carrier. -/
theorem proposition63MildRescalingFamily_image_mem_ordinaryCarrier
    {sourceDelta scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceShading center)
    (hscale : 1 ≤ scale)
    (hsourceDelta : 0 < sourceDelta)
    (hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000)
    (hrawLine : WZ1PaperIsLineClass raw.family)
    (index : Fin (proposition63MildRescalingFamily hscale raw).card)
    (point : Point3)
    (hpoint : point ∈ (sourceFamily.tube index).carrier)
    (hpointCore : point ∈
      pureWZ2ShiftedOriginGridCore sourceDelta scale center) :
    wz1IsotropicRescalingMap center scale point ∈
      ((proposition63MildRescalingFamily hscale raw).tube index).carrier := by
  let sourceTube := sourceFamily.tube index
  let targetTube :=
    (proposition63MildRescalingFamily hscale raw).tube index
  let imagePoint := wz1IsotropicRescalingMap center scale point
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have targetLine : WZ1PaperTubeInLineClass targetTube :=
    proposition63MildRescalingFamily_lineClass hscale raw hrawLine index
  have targetCentered : proposition63CenteredTube targetTube = targetTube :=
    proposition63MildRescalingFamily_centered hscale raw hrawLine index
  rcases exists_closest_on_axis hsourceDelta.le sourceTube point hpoint with
    ⟨parameter, _parameterMem, sourceDistance⟩
  let sourceAxisPoint :=
    sourceTube.base + parameter • sourceTube.direction
  let imageAxisPoint :=
    wz1IsotropicRescalingMap center scale sourceAxisPoint
  have sourceAxisMem : sourceAxisPoint ∈ tubeAxisLine sourceTube :=
    ⟨parameter, rfl⟩
  have imageAxisMem : imageAxisPoint ∈ tubeAxisLine targetTube := by
    dsimp only [targetTube, imageAxisPoint]
    rw [proposition63MildRescalingFamily_axis_provenance hscale raw index]
    exact ⟨sourceAxisPoint, sourceAxisMem, rfl⟩
  have imageDistance :
      dist imagePoint imageAxisPoint ≤ scale * sourceDelta := by
    dsimp only [imagePoint, imageAxisPoint]
    simp only [wz1IsotropicRescalingMap, dist_eq_norm]
    have difference :
        scale • (point - center) -
            scale • (sourceAxisPoint - center) =
          scale • (point - sourceAxisPoint) := by
      module
    rw [difference, norm_smul, Real.norm_eq_abs, abs_of_pos hscalePos]
    exact mul_le_mul_of_nonneg_left
      (by simpa [sourceAxisPoint, dist_eq_norm] using sourceDistance)
      hscalePos.le
  have sourceCell :
      point ∈
        wz1PaperGridCube sourceDelta
          (wz1PaperGridIndex sourceDelta point) :=
    (mem_wz1PaperGridCube sourceDelta _ point).mpr rfl
  have imagePointHeight : |imagePoint (2 : Fin 3)| ≤ 1 / 9 := by
    have sourceBound :
        |point (2 : Fin 3) - center (2 : Fin 3)| ≤
          1 / (9 * scale) - 6 * sourceDelta :=
      hpointCore sourceCell 2
    change |scale * (point (2 : Fin 3) - center (2 : Fin 3))| ≤ 1 / 9
    rw [abs_mul, abs_of_pos hscalePos]
    calc
      scale * |point (2 : Fin 3) - center (2 : Fin 3)| ≤
          scale * (1 / (9 * scale) - 6 * sourceDelta) :=
        mul_le_mul_of_nonneg_left sourceBound hscalePos.le
      _ = 1 / 9 - 6 * scale * sourceDelta := by
        field_simp [hscalePos.ne']
        <;> ring
      _ ≤ 1 / 9 := by
        have nonnegative : 0 ≤ 6 * scale * sourceDelta :=
          mul_nonneg (mul_nonneg (by norm_num) hscalePos.le)
            hsourceDelta.le
        linarith
  have imageAxisHeight : |imageAxisPoint (2 : Fin 3)| ≤ 1 / 4 := by
    have coordinateDistance :
        |imageAxisPoint (2 : Fin 3) - imagePoint (2 : Fin 3)| ≤
          dist imageAxisPoint imagePoint :=
      abs_coord_sub_le_dist
        (x := imageAxisPoint) (y := imagePoint) (2 : Fin 3)
    calc
      |imageAxisPoint (2 : Fin 3)| ≤
          |imagePoint (2 : Fin 3)| +
            |imageAxisPoint (2 : Fin 3) - imagePoint (2 : Fin 3)| := by
        calc
          |imageAxisPoint (2 : Fin 3)| =
              |imagePoint (2 : Fin 3) +
                (imageAxisPoint (2 : Fin 3) - imagePoint (2 : Fin 3))| := by
            congr 1
            ring
          _ ≤ |imagePoint (2 : Fin 3)| +
                |imageAxisPoint (2 : Fin 3) - imagePoint (2 : Fin 3)| :=
            abs_add_le _ _
      _ ≤ 1 / 9 + dist imageAxisPoint imagePoint := by
        exact add_le_add imagePointHeight coordinateDistance
      _ ≤ 1 / 9 + scale * sourceDelta := by
        rw [dist_comm imageAxisPoint imagePoint]
        exact add_le_add (le_refl (1 / 9 : ℝ)) imageDistance
      _ ≤ 1 / 4 := by
        linarith
  have imageAxisCanonical :
      wz1PaperAxisPointAtHeight targetTube
          (imageAxisPoint (2 : Fin 3)) =
        imageAxisPoint :=
    axisPointAtHeight_eq_of_mem_axis targetTube targetLine
      imageAxisPoint imageAxisMem
  have imageAxisSegment :
      imageAxisPoint ∈
        Kakeya.unitSegment targetTube.base targetTube.direction := by
    rw [← imageAxisCanonical]
    exact centered_axisPointAtHeight_mem_segment
      targetTube targetLine targetCentered imageAxisHeight
  exact Metric.mem_cthickening_of_dist_le imagePoint imageAxisPoint
    (scale * sourceDelta) _ imageAxisSegment imageDistance

/-- The exact isotropic image of every retained source ordinary overlap lies
in its canonical centered target ordinary carrier. -/
theorem refinedOrdinaryOverlap_image_subset_target_carrier
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    (data : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant) :
    ∀ index,
      wz1IsotropicRescalingMap data.center scale ''
          (data.refinedOrdinaryOverlap source hsourceLoss).carrier index ⊆
        ((proposition63MildRescalingFamily hscale data.raw).tube index).carrier := by
  intro index imagePoint imagePointMem
  rcases imagePointMem with ⟨point, pointMem, rfl⟩
  apply proposition63MildRescalingFamily_image_mem_ordinaryCarrier
    data.raw hscale source.delta_pos hscaleDeltaSmall data.raw_line_class
    index point
  · have carrierIdentity :=
      source.ancestorReentry.geometry.ordinary_carrier_image_eq
        (source.ancestorReentry.geometry.indexEquiv.symm
          (data.selected.embedding index))
    rw [source.ancestorReentry.geometry.indexEquiv.apply_symm_apply
      (data.selected.embedding index)] at carrierIdentity
    rw [data.selected.tube_eq, carrierIdentity]
    rcases pointMem.1 with ⟨ordinaryPoint, ordinaryPointMem, rfl⟩
    exact ⟨ordinaryPoint,
      source.ancestorReentry.geometry.ordinaryRefined.subset_body _
        ordinaryPointMem,
      rfl⟩
  · have pointBoxed :=
      data.refined_sub_boxed index pointMem.2
    rw [data.boxed_carrier_eq (data.selected.embedding index)] at pointBoxed
    exact pointBoxed.2

/-- Target-side ordinary shading whose fibers are definitionally the exact
isotropic images of the retained source ordinary overlaps. -/
noncomputable def targetOrdinaryShading
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    (data : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant) :
    Kakeya.Streamlined.TubeShading
      (proposition63MildRescalingFamily hscale data.raw) where
  carrier index :=
    wz1IsotropicRescalingMap data.center scale ''
      (data.refinedOrdinaryOverlap source hsourceLoss).carrier index
  measurable_carrier index := by
    let inverse : Point3 → Point3 :=
      wz1IsotropicRescalingInverse data.center scale
    have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
    have imageAsPreimage :
        wz1IsotropicRescalingMap data.center scale ''
            (data.refinedOrdinaryOverlap source hsourceLoss).carrier index =
          inverse ⁻¹'
            (data.refinedOrdinaryOverlap source hsourceLoss).carrier index := by
      ext point
      constructor
      · rintro ⟨sourcePoint, sourcePointMem, rfl⟩
        have inverseMap :
            inverse
                (wz1IsotropicRescalingMap data.center scale sourcePoint) =
              sourcePoint := by
          ext coordinate
          simp [inverse, wz1IsotropicRescalingMap,
            wz1IsotropicRescalingInverse]
          field_simp [hscalePos.ne']
          ring
        simpa [inverseMap] using sourcePointMem
      · intro sourcePointMem
        refine ⟨inverse point, sourcePointMem, ?_⟩
        ext coordinate
        simp [inverse, wz1IsotropicRescalingMap,
          wz1IsotropicRescalingInverse]
        field_simp [hscalePos.ne']
    rw [imageAsPreimage]
    exact
      ((data.refinedOrdinaryOverlap source hsourceLoss).measurable_carrier
        index).preimage
        (continuous_const.add
          (continuous_const.smul continuous_id)).measurable
  subset_body index :=
    data.refinedOrdinaryOverlap_image_subset_target_carrier
      source hsourceLoss index

/-- The target ordinary carrier is exactly the production isotropic image,
with no independently selected witness or equality cast. -/
@[simp] theorem targetOrdinaryShading_carrier
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    (data : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant)
    (index : Fin data.selected.family.card) :
    (data.targetOrdinaryShading source hsourceLoss).carrier index =
      wz1IsotropicRescalingMap data.center scale ''
        (data.refinedOrdinaryOverlap source hsourceLoss).carrier index :=
  rfl

/-- The exact-image ordinary shading is carrierwise contained in the existing
production target paper shading. -/
theorem targetOrdinaryShading_sub_targetShading
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    (data : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant) :
    ∀ index,
      (data.targetOrdinaryShading source hsourceLoss).carrier index ⊆
        data.targetShading.carrier index := by
  intro index point pointMem
  rcases pointMem with ⟨sourcePoint, sourcePointMem, rfl⟩
  rw [data.targetShading_eq]
  refine ⟨sourcePoint, ⟨sourcePointMem.2, ?_⟩, rfl⟩
  have pointBoxed :=
    data.refined_sub_boxed index sourcePointMem.2
  rw [data.boxed_carrier_eq (data.selected.embedding index)] at pointBoxed
  exact pointBoxed.2

/-- The target ordinary fiber has the exact cubic isotropic Jacobian. -/
theorem targetOrdinaryShading_volume
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    (data : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant)
    (index : Fin data.selected.family.card) :
    volume ((data.targetOrdinaryShading source hsourceLoss).carrier index) =
      ENNReal.ofReal (scale ^ 3) *
        volume
          ((data.refinedOrdinaryOverlap source hsourceLoss).carrier index) := by
  exact volume_image_wz1IsotropicRescalingMap
    (lt_of_lt_of_le zero_lt_one hscale) data.center
    ((data.refinedOrdinaryOverlap source hsourceLoss).measurable_carrier index)

/-- Every exact-image target ordinary fiber has positive volume. -/
theorem targetOrdinaryShading_volume_pos
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    (data : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant)
    (index : Fin data.selected.family.card) :
    0 < volume
      ((data.targetOrdinaryShading source hsourceLoss).carrier index) := by
  rw [data.targetOrdinaryShading_volume source hsourceLoss index]
  exact ENNReal.mul_pos
    (ENNReal.ofReal_pos.mpr
      (pow_pos (lt_of_lt_of_le zero_lt_one hscale) 3)).ne'
    (data.refinedOrdinaryOverlap_volume_pos source hsourceLoss index).ne'

/-- The common source core places every point of the rescaled target shading
inside the fixed coordinate window required by ordinary re-entry. -/
theorem targetShading_coordinate_bound
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    (data : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant) :
    ∀ point ∈ data.targetShading.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 / 9 := by
  intro point pointMem coordinate
  rw [data.targetShading_eq, proposition63MildRescalingShading_union] at pointMem
  rcases pointMem with ⟨sourcePoint, ⟨_sourceMem, sourceCore⟩, rfl⟩
  have sourceCell :
      sourcePoint ∈
        wz1PaperGridCube sourceDelta
          (wz1PaperGridIndex sourceDelta sourcePoint) :=
    (mem_wz1PaperGridCube sourceDelta _ sourcePoint).mpr rfl
  have sourceBound :
      |sourcePoint coordinate - data.center coordinate| ≤
        1 / (9 * scale) - 6 * sourceDelta :=
    sourceCore sourceCell coordinate
  have scalePos : 0 < scale := zero_lt_one.trans_le hscale
  change
    |scale * (sourcePoint coordinate - data.center coordinate)| ≤ 1 / 9
  rw [abs_mul, abs_of_pos scalePos]
  calc
    scale * |sourcePoint coordinate - data.center coordinate| ≤
        scale * (1 / (9 * scale) - 6 * sourceDelta) :=
      mul_le_mul_of_nonneg_left sourceBound scalePos.le
    _ = 1 / 9 - 6 * scale * sourceDelta := by
      field_simp [scalePos.ne']
      <;> ring
    _ ≤ 1 / 9 := by
      have nonnegative : 0 ≤ 6 * scale * sourceDelta :=
        mul_nonneg (mul_nonneg (by norm_num) scalePos.le)
          sourceExtremal.delta_pos.le
      linarith

end Proposition63M9MildRescalingSourceData

namespace Proposition63M9MildRescalingQuotientTargetData

/-- Restrict the exact-image target ordinary shading along the quotient
selection and the joint regularization. -/
noncomputable def finalOrdinaryShading
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    Kakeya.Streamlined.TubeShading
      (data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).family where
  carrier index :=
    (sourceData.targetOrdinaryShading source hsourceLoss).carrier
      (data.finalSourceIndex index)
  measurable_carrier index :=
    (sourceData.targetOrdinaryShading source hsourceLoss).measurable_carrier
      (data.finalSourceIndex index)
  subset_body index point pointMem := by
    change point ∈
      ((data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).family.tube index).carrier
    rw [(data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).tube_eq,
      (data.quotientSchedule.selectedTarget data.selection).tube_eq]
    exact
      (sourceData.targetOrdinaryShading source hsourceLoss).subset_body
        (data.finalSourceIndex index) pointMem

/-- Each final ordinary carrier is exactly the isotropic image of the
corresponding retained source ordinary overlap. -/
@[simp] theorem finalOrdinaryShading_carrier
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule)
    (index : Fin (data.quotientSchedule.jointRegularizedTarget
      data.jointRegularized).family.card) :
    (data.finalOrdinaryShading source hsourceLoss).carrier index =
      wz1IsotropicRescalingMap sourceData.center scale ''
        (sourceData.refinedOrdinaryOverlap source hsourceLoss).carrier
          (data.finalSourceIndex index) :=
  rfl

/-- The final exact-image ordinary shading is carrierwise contained in the
final production paper shading. -/
theorem finalOrdinaryShading_sub_finalShading
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    ∀ index,
      (data.finalOrdinaryShading source hsourceLoss).carrier index ⊆
        data.finalShading.carrier index := by
  intro index point pointMem
  exact sourceData.targetOrdinaryShading_sub_targetShading
    source hsourceLoss (data.finalSourceIndex index) pointMem

/-- Every final exact-image ordinary fiber has positive volume. -/
theorem finalOrdinaryShading_volume_pos
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule)
    (index : Fin (data.quotientSchedule.jointRegularizedTarget
      data.jointRegularized).family.card) :
    0 < volume
      ((data.finalOrdinaryShading source hsourceLoss).carrier index) :=
  sourceData.targetOrdinaryShading_volume_pos source hsourceLoss
    (data.finalSourceIndex index)

/-- Every later quotient selection inherits the common target coordinate
window from the construction-aware source package. -/
theorem finalShading_coordinate_bound
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    ∀ point ∈ data.finalShading.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 / 9 := by
  rintro point ⟨index, pointMem⟩ coordinate
  exact sourceData.targetShading_coordinate_bound point
    ⟨(data.quotientSchedule.selectedTarget data.selection).embedding
        ((data.quotientSchedule.jointRegularizedTarget
          data.jointRegularized).embedding index),
      pointMem⟩ coordinate

/-- The final ordinary trace remains in the central height window needed by
the identity-frame normalization. -/
theorem finalOrdinaryShading_axial_window
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    ∀ index point,
      point ∈ (data.finalOrdinaryShading source hsourceLoss).carrier index →
        |point (2 : Fin 3)| ≤ 1 / 4 := by
  intro index point pointMem
  have finalMem : point ∈ data.finalShading.carrier index :=
    data.finalOrdinaryShading_sub_finalShading
      source hsourceLoss index pointMem
  exact (data.finalShading_coordinate_bound point
    ⟨index, finalMem⟩ 2).trans (by norm_num)

/-- The production M9 trace satisfies the stronger axial window consumed by
the reentrant kernel.  This is kept separate from the public normalization
field, whose historical interface records only the weaker `1 / 4` bound. -/
theorem finalOrdinaryShading_axial_window_eighth
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    ∀ index point,
      point ∈ (data.finalOrdinaryShading source hsourceLoss).carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8 := by
  intro index point pointMem
  have finalMem : point ∈ data.finalShading.carrier index :=
    data.finalOrdinaryShading_sub_finalShading
      source hsourceLoss index pointMem
  exact (data.finalShading_coordinate_bound point
    ⟨index, finalMem⟩ 2).trans (by norm_num)

/-- Any target grid cell meeting the final ordinary trace is wholly contained
in the corresponding final paper carrier. -/
theorem finalOrdinaryShading_ordinary_cell_containment
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    ∀ index (cell : ℤ × ℤ × ℤ),
      ((data.finalOrdinaryShading source hsourceLoss).carrier index ∩
          wz1PaperGridCube (scale * source.delta) cell).Nonempty →
        wz1PaperGridCube (scale * source.delta) cell ⊆
          wz1PaperTubeCarrier
            ((data.quotientSchedule.jointRegularizedTarget
              data.jointRegularized).family.tube index) := by
  intro index cell cellHit
  rcases cellHit with ⟨point, pointOrdinary, pointCell⟩
  have pointFinal : point ∈ data.finalShading.carrier index :=
    data.finalOrdinaryShading_sub_finalShading
      source hsourceLoss index pointOrdinary
  have cellSubset :=
    data.finalCubical index point pointFinal
  have cellIdentity :
      wz1PaperGridIndex (scale * source.delta) point = cell :=
    (mem_wz1PaperGridCube (scale * source.delta) cell point).mp pointCell
  rw [cellIdentity] at cellSubset
  intro other otherCell
  exact data.finalShading.subset_body index (cellSubset otherCell)

/-- Unit-ball support of the exact final family supplies the fixed base bound
used by the next normalization stage. -/
theorem finalFamily_hasBoundedBase_four
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    HasBoundedBase
      (data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).family 4 := by
  have boundedOne : HasBoundedBase
      (data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).family 1 :=
    hasBoundedBase_of_isInUnitBall
      (mul_nonneg (lt_of_lt_of_le zero_lt_one hscale).le
        sourceExtremal.delta_pos.le)
      data.finalFamily_isInUnitBall
  intro index
  exact (boundedOne index).trans (by norm_num)

/-- The family-independent ordinary density floor surviving source
regularization, ancestor overlap, and the cubic isotropic Jacobian. -/
def finalOrdinaryDensityFloor
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    {sourceData : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant} : ENNReal :=
  ENNReal.ofReal (scale ^ 3) *
    ((100 : ENNReal)⁻¹ *
      source.ancestorReentry.geometry.ordinaryDensity *
        ((1 / 2 : ENNReal) * sourceData.sourceDensity *
          Kakeya.realRpowENN source.delta 2))

@[simp] theorem finalOrdinaryDensityFloor_eq
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    {sourceData : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant} :
    finalOrdinaryDensityFloor (scale := scale) (sourceData := sourceData)
      source hsourceLoss =
      ENNReal.ofReal (scale ^ 3) *
        ((100 : ENNReal)⁻¹ *
          source.ancestorReentry.geometry.ordinaryDensity *
            ((1 / 2 : ENNReal) * sourceData.sourceDensity *
              Kakeya.realRpowENN source.delta 2)) :=
  rfl

/-- The final ordinary fibers retain the complete source regularization
floor, the ancestor ordinary-overlap fraction, and the cubic isotropic
Jacobian. -/
theorem finalOrdinaryShading_per_tube_lower
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule)
    (index : Fin (data.quotientSchedule.jointRegularizedTarget
      data.jointRegularized).family.card) :
    finalOrdinaryDensityFloor (scale := scale) (sourceData := sourceData)
      source hsourceLoss ≤
      volume
        ((data.finalOrdinaryShading source hsourceLoss).carrier index) := by
  let sourceIndex := data.finalSourceIndex index
  rw [finalOrdinaryDensityFloor_eq]
  change
    ENNReal.ofReal (scale ^ 3) *
          ((100 : ENNReal)⁻¹ *
            source.ancestorReentry.geometry.ordinaryDensity *
              ((1 / 2 : ENNReal) * sourceData.sourceDensity *
                Kakeya.realRpowENN source.delta 2)) ≤
      volume
        ((sourceData.targetOrdinaryShading source hsourceLoss).carrier
          sourceIndex)
  rw [sourceData.targetOrdinaryShading_volume
    source hsourceLoss sourceIndex]
  apply mul_le_mul_left'
  calc
    (100 : ENNReal)⁻¹ *
          source.ancestorReentry.geometry.ordinaryDensity *
            ((1 / 2 : ENNReal) * sourceData.sourceDensity *
              Kakeya.realRpowENN source.delta 2) ≤
        (100 : ENNReal)⁻¹ *
          source.ancestorReentry.geometry.ordinaryDensity *
            volume (sourceData.refined.carrier sourceIndex) := by
      exact mul_le_mul_left'
        (sourceData.refined_per_tube sourceIndex)
        ((100 : ENNReal)⁻¹ *
          source.ancestorReentry.geometry.ordinaryDensity)
    _ ≤ volume
        ((sourceData.refinedOrdinaryOverlap source hsourceLoss).carrier
          sourceIndex) :=
      sourceData.refinedOrdinaryOverlap_per_tube
        source hsourceLoss sourceIndex

/-- Summing the uniform explicit floor gives the corresponding total final
ordinary mass lower bound. -/
theorem finalOrdinaryShading_mass_lower
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    finalOrdinaryDensityFloor (scale := scale) (sourceData := sourceData)
      source hsourceLoss *
        (data.quotientSchedule.jointRegularizedTarget
          data.jointRegularized).family.enncard ≤
      (data.finalOrdinaryShading source hsourceLoss).mass := by
  let floor : ENNReal :=
    finalOrdinaryDensityFloor (scale := scale) (sourceData := sourceData)
      source hsourceLoss
  change floor *
      ((data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).family.card : ENNReal) ≤
    ∑ index : Fin (data.quotientSchedule.jointRegularizedTarget
      data.jointRegularized).family.card,
      volume ((data.finalOrdinaryShading source hsourceLoss).carrier index)
  calc
    floor *
          ((data.quotientSchedule.jointRegularizedTarget
            data.jointRegularized).family.card : ENNReal) =
        ∑ _index : Fin (data.quotientSchedule.jointRegularizedTarget
            data.jointRegularized).family.card, floor := by
      simp [Finset.sum_const, mul_comm]
    _ ≤ ∑ index : Fin (data.quotientSchedule.jointRegularizedTarget
          data.jointRegularized).family.card,
        volume ((data.finalOrdinaryShading source hsourceLoss).carrier index) :=
      Finset.sum_le_sum fun index _ =>
        data.finalOrdinaryShading_per_tube_lower
          source hsourceLoss index

/-- Dense target-grid cubicalization of the exact final ordinary shading. -/
noncomputable def finalDenseShading
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    WZ1PaperTubeShading
      (data.quotientSchedule.jointRegularizedTarget
        data.jointRegularized).family :=
  pureWZ2DenseCubicalShading
    (data.finalOrdinaryShading source hsourceLoss)

/-- The literal dense cubicalization is cubical by construction. -/
theorem finalDenseShading_cubical
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    WZ1PaperIsCubicalShading
      (data.finalDenseShading source hsourceLoss) :=
  pureWZ2DenseCubicalShading_cubical
    (data.finalOrdinaryShading source hsourceLoss)

/-- Dense cubicalization stays carrierwise inside the exact final production
paper shading. -/
theorem finalDenseShading_sub_finalShading
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    PaperIsSubshading
      (data.finalDenseShading source hsourceLoss) data.finalShading := by
  apply pureWZ2DenseCubicalShading_sub_cubical
    (data.finalOrdinaryShading source hsourceLoss) data.finalShading
    (mul_pos (lt_of_lt_of_le zero_lt_one hscale) source.delta_pos)
  · exact data.finalOrdinaryShading_sub_finalShading source hsourceLoss
  · exact data.finalCubical
  · exact data.finalOrdinaryShading_volume_pos source hsourceLoss

/-- The ordinary trace through the dense cubicalization retains the universal
`73/100` fraction required by identity-frame normalization. -/
theorem finalDenseShading_trace_mass_retention
    {sigma sourceLoss sourceDeltaCutoff scale : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    (73 / 100 : ENNReal) *
          (data.finalOrdinaryShading source hsourceLoss).mass ≤
      (proposition63OrdinaryTrace
        (data.finalOrdinaryShading source hsourceLoss)
        (data.finalDenseShading source hsourceLoss)).mass := by
  apply pureWZ2DenseCubicalShading_mass_retention
    (mul_pos (lt_of_lt_of_le zero_lt_one hscale) source.delta_pos)
  · have sqrtThree : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    have targetNonnegative : 0 ≤ scale * source.delta :=
      (mul_pos (lt_of_lt_of_le zero_lt_one hscale) source.delta_pos).le
    calc
      (scale * source.delta) * (1 + Real.sqrt 3) ≤
          (scale * source.delta) * 3 := by
        apply mul_le_mul_of_nonneg_left (by linarith) targetNonnegative
      _ ≤ (1 / 1000 : ℝ) * 3 := by
        exact mul_le_mul_of_nonneg_right hscaleDeltaSmall (by norm_num)
      _ ≤ 1 := by norm_num
  · exact data.finalOrdinaryShading_ordinary_cell_containment
      source hsourceLoss

end Proposition63M9MildRescalingQuotientTargetData

/-- The exact additional payload needed to use a construction-aware M9 tail
as the initial source of the Proposition 6.4 hierarchy. -/
structure Proposition63M9ReentrantTailData
    {sourceDelta scale sigma sourceLoss outputLoss : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFine)
    {Lplane Lslope : NNReal}
    (preGrains : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1)
    (targetFine : Kakeya.Streamlined.TubeFamily (scale * sourceDelta))
    (targetShading : WZ1PaperTubeShading targetFine)
    (finalGrain : Proposition63MildRescalingFiniteParentScheduleData.Proposition63MildRescalingFinalGrainData
      (outputLoss := outputLoss) sourceShading preGrains targetFine
      targetShading)
    (normalizationExponent : ℕ) where
  volume_lower :
    Kakeya.realRpowENN (scale * sourceDelta) (sigma + outputLoss) ≤
      volume targetShading.union
  source_vertical :
    ∀ point : {point : Point3 // point ∈ sourceShading.union},
      |preGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  source_slope :
    ∀ height : ℝ, height ∈ Set.Icc (-1 : ℝ) 1 →
      |preGrains.slope height| ≤ 3
  ordinaryLoss : ℝ
  reentry :
    PureWZ2PropStickyReentryData
      (sigma := sigma) targetShading normalizationExponent ordinaryLoss
        outputLoss
  ordinary_axial_window_eighth :
    ∀ index point,
      point ∈
          reentry.geometry.frame ''
            reentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8

namespace Proposition63M9ReentrantTailData

/-- Project the dependent M9 receipt to the exact hierarchy state. -/
noncomputable def toReentrantGrainSource
    {sourceDelta scale sigma sourceLoss outputLoss : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFine}
    {Lplane Lslope : NNReal}
    {preGrains : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {targetFine : Kakeya.Streamlined.TubeFamily (scale * sourceDelta)}
    {targetShading : WZ1PaperTubeShading targetFine}
    {finalGrain : Proposition63MildRescalingFiniteParentScheduleData.Proposition63MildRescalingFinalGrainData
      (outputLoss := outputLoss) sourceShading preGrains targetFine
      targetShading}
    {normalizationExponent : ℕ}
    (data : Proposition63M9ReentrantTailData sourceShading preGrains targetFine
      targetShading finalGrain normalizationExponent) :
    PureWZ2ReentrantGrainSource sigma outputLoss (scale * sourceDelta)
      normalizationExponent where
  ordinaryLoss := data.ordinaryLoss
  grain := finalGrain.toQuantitativeGrainConfiguration data.volume_lower
    data.source_vertical data.source_slope
  reentry := data.reentry
  ordinary_axial_window_eighth := data.ordinary_axial_window_eighth

end Proposition63M9ReentrantTailData

end Kakeya.Assouad.PureWZ2

end
