import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64IsotropicPlaneMap
import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingBoxPigeonhole
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance

/-!
# Isotropic paper retubing for Proposition 6.4

This is the final geometric operation in the Lemma-3.5 cleanup: restrict the
exact affine image to a mass-popular box, apply one positive isotropic
similarity, and saturate in the final paper grid.  Since paper tubes use full
supporting lines, the isotropic map preserves one source index per target
index.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- A mass-popular box inside an exact-image paper shading. -/
structure PureWZ2Proposition64PopularBoxData
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) (width : ℝ) where
  center : Point3
  center_margin : ∀ i : Fin 3, |center i| ≤ 1 - width / 2
  center_mem : center ∈ wz1MildRescalingSourceWindow
  box : Set Point3 := wz1MildRescalingSourceBox center
    (point3 (width / 2) (width / 2) (width / 2))
  box_eq : box = wz1MildRescalingSourceBox center
    (point3 (width / 2) (width / 2) (width / 2))
  box_measurable : MeasurableSet box
  restricted : WZ1PaperTubeShading family
  restricted_carrier : ∀ index, restricted.carrier index =
    shading.carrier index ∩ box
  restricted_subshading : PureWZ2PaperIsSubshading restricted shading
  restricted_union : restricted.union = shading.union ∩ box
  mass_lower : ENNReal.ofReal (width ^ 3 / 27) * shading.mass ≤
    restricted.mass

/-- Apply the closed finite box pigeonhole to a paper shading. -/
theorem pureWZ2Proposition64_selectPopularBox
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    {width : ℝ} (hwidth : 0 < width) (hwidthOne : width ≤ 1) :
    Nonempty (PureWZ2Proposition64PopularBoxData shading width) := by
  have hunionWindow : shading.union ⊆ wz1MildRescalingSourceWindow := by
    rintro point ⟨index, hpoint⟩ coordinate
    have hbox := (shading.subset_body index hpoint).2
    fin_cases coordinate
    · simpa [wz1MildRescalingSourceWindow,
        Kakeya.Streamlined.axisBox] using hbox.1
    · simpa [wz1MildRescalingSourceWindow,
        Kakeya.Streamlined.axisBox] using hbox.2.1
    · simpa [wz1MildRescalingSourceWindow,
        Kakeya.Streamlined.axisBox] using hbox.2.2
  rcases wz1_mild_rescaling_box_pigeonhole shading
      hunionWindow width hwidth hwidthOne with
    ⟨center, hcenterMargin, hcenter, hmass⟩
  let halfWidth := point3 (width / 2) (width / 2) (width / 2)
  let box := wz1MildRescalingSourceBox center halfWidth
  have hboxMeasurable : MeasurableSet box := by
    dsimp only [box, wz1MildRescalingSourceBox, wz1AxisBox,
      wz1MildRescalingSourceWindow]
    apply MeasurableSet.inter
    · have hmeas : MeasurableSet (⋂ coordinate : Fin 3,
          {point : Point3 |
            |point coordinate - center coordinate| ≤ halfWidth coordinate}) :=
        MeasurableSet.iInter fun coordinate : Fin 3 =>
          measurableSet_le
            ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) coordinate).sub
              continuous_const).abs.measurable measurable_const
      simpa only [Set.setOf_forall] using hmeas
    · have hmeas : MeasurableSet (⋂ coordinate : Fin 3,
          {point : Point3 | |point coordinate| ≤ 1}) :=
        MeasurableSet.iInter fun coordinate : Fin 3 =>
          measurableSet_le
            (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) coordinate).abs.measurable
            measurable_const
      simpa only [Set.setOf_forall] using hmeas
  let restricted : WZ1PaperTubeShading family :=
    { carrier := fun index => shading.carrier index ∩ box
      measurable_carrier := fun index =>
        (shading.measurable_carrier index).inter hboxMeasurable
      subset_body := fun index => Set.inter_subset_left.trans
        (shading.subset_body index) }
  have hunion : restricted.union = shading.union ∩ box := by
    ext point
    constructor
    · rintro ⟨index, hsource, hbox⟩
      exact ⟨⟨index, hsource⟩, hbox⟩
    · rintro ⟨⟨index, hsource⟩, hbox⟩
      exact ⟨index, hsource, hbox⟩
  exact ⟨{
    center := center
    center_margin := hcenterMargin
    center_mem := hcenter
    box := box
    box_eq := rfl
    box_measurable := hboxMeasurable
    restricted := restricted
    restricted_carrier := fun _ => rfl
    restricted_subshading := fun _ => Set.inter_subset_left
    restricted_union := hunion
    mass_lower := by
      change ENNReal.ofReal (width ^ 3 / 27) * shading.mass ≤
        ∑ index, volume (shading.carrier index ∩ box)
      simpa [box, halfWidth] using hmass }⟩

/-- The target paper tube with the isotropically dilated source axis. -/
def pureWZ2Proposition64IsotropicPaperTube
    {sourceDelta targetDelta : ℝ}
    (center : Point3) (scale : ℝ)
    (sourceTube : Kakeya.DeltaTube sourceDelta) :
    Kakeya.DeltaTube targetDelta where
  base := pureWZ2Proposition64IsotropicMap center scale sourceTube.base
  direction := sourceTube.direction
  direction_unit := sourceTube.direction_unit

theorem pureWZ2Proposition64IsotropicPaperTube_axis
    {sourceDelta targetDelta : ℝ}
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (sourceTube : Kakeya.DeltaTube sourceDelta) :
    tubeAxisLine (pureWZ2Proposition64IsotropicPaperTube
        (targetDelta := targetDelta) center scale sourceTube) =
      pureWZ2Proposition64IsotropicMap center scale ''
        tubeAxisLine sourceTube := by
  ext point
  constructor
  · rintro ⟨parameter, rfl⟩
    refine ⟨sourceTube.base + (parameter / scale) • sourceTube.direction,
      ⟨parameter / scale, rfl⟩, ?_⟩
    simp only [pureWZ2Proposition64IsotropicMap,
      pureWZ2Proposition64IsotropicPaperTube]
    rw [show sourceTube.base + (parameter / scale) • sourceTube.direction -
        center = (sourceTube.base - center) +
          (parameter / scale) • sourceTube.direction by abel,
      smul_add, smul_smul]
    field_simp [hscale.ne']
  · rintro ⟨sourcePoint, ⟨parameter, rfl⟩, rfl⟩
    refine ⟨scale * parameter, ?_⟩
    simp only [pureWZ2Proposition64IsotropicMap,
      pureWZ2Proposition64IsotropicPaperTube]
    rw [show sourceTube.base + parameter • sourceTube.direction - center =
        (sourceTube.base - center) + parameter • sourceTube.direction by abel,
      smul_add, smul_smul]

/-- Canonical unit segment centered at the height-zero point of the
isotropically dilated supporting line.  This rebase keeps the full paper
carrier unchanged and makes the ordinary representative live in the standard
target window used by pure Definition 2.12. -/
def pureWZ2Proposition64IsotropicRebasedPaperTube
    {sourceDelta targetDelta : ℝ}
    (center : Point3) (scale : ℝ)
    (sourceTube : Kakeya.DeltaTube sourceDelta) :
    Kakeya.DeltaTube targetDelta where
  base :=
    let target := pureWZ2Proposition64IsotropicPaperTube
      (targetDelta := targetDelta) center scale sourceTube
    wz1TubeAxisZeroPoint target - (1 / 2 : ℝ) • target.direction
  direction := (pureWZ2Proposition64IsotropicPaperTube
    (targetDelta := targetDelta) center scale sourceTube).direction
  direction_unit := (pureWZ2Proposition64IsotropicPaperTube
    (targetDelta := targetDelta) center scale sourceTube).direction_unit

/-- Rebasing at height zero does not change the supporting line. -/
theorem pureWZ2Proposition64IsotropicRebasedPaperTube_axis
    {sourceDelta targetDelta : ℝ}
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (sourceTube : Kakeya.DeltaTube sourceDelta) :
    tubeAxisLine (pureWZ2Proposition64IsotropicRebasedPaperTube
        (targetDelta := targetDelta) center scale sourceTube) =
      pureWZ2Proposition64IsotropicMap center scale ''
        tubeAxisLine sourceTube := by
  let unreBased := pureWZ2Proposition64IsotropicPaperTube
    (targetDelta := targetDelta) center scale sourceTube
  have hzeroAxis : wz1TubeAxisZeroPoint unreBased ∈ tubeAxisLine unreBased :=
    wz1TubeAxisZeroPoint_mem_axis unreBased
  have hsameAxis : tubeAxisLine
      (pureWZ2Proposition64IsotropicRebasedPaperTube
        (targetDelta := targetDelta) center scale sourceTube) =
        tubeAxisLine unreBased := by
    apply Set.Subset.antisymm
    · rintro point ⟨parameter, rfl⟩
      rcases hzeroAxis with ⟨offset, hoffset⟩
      refine ⟨offset - 1 / 2 + parameter, ?_⟩
      dsimp only [pureWZ2Proposition64IsotropicRebasedPaperTube]
      change (wz1TubeAxisZeroPoint unreBased -
        (1 / 2 : ℝ) • unreBased.direction) + parameter • unreBased.direction = _
      rw [hoffset]
      module
    · rintro point ⟨parameter, rfl⟩
      rcases hzeroAxis with ⟨offset, hoffset⟩
      refine ⟨parameter - offset + 1 / 2, ?_⟩
      dsimp only [pureWZ2Proposition64IsotropicRebasedPaperTube]
      change _ = (wz1TubeAxisZeroPoint unreBased -
        (1 / 2 : ℝ) • unreBased.direction) +
        (parameter - offset + 1 / 2) • unreBased.direction
      rw [hoffset]
      module
  rw [hsameAxis]
  exact pureWZ2Proposition64IsotropicPaperTube_axis center hscale sourceTube

/-- The height-zero point of the centered target segment is the isotropic
image of the source axis at the center height. -/
theorem pureWZ2Proposition64IsotropicRebasedPaperTube_axisZeroPoint
    {sourceDelta targetDelta : ℝ}
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceLine : WZ1PaperTubeInLineClass sourceTube) :
    wz1TubeAxisZeroPoint (pureWZ2Proposition64IsotropicRebasedPaperTube
        (targetDelta := targetDelta) center scale sourceTube) =
      pureWZ2Proposition64IsotropicMap center scale
        (wz1PaperAxisPointAtHeight sourceTube (center 2)) := by
  let unreBased := pureWZ2Proposition64IsotropicPaperTube
    (targetDelta := targetDelta) center scale sourceTube
  let candidate := pureWZ2Proposition64IsotropicMap center scale
    (wz1PaperAxisPointAtHeight sourceTube (center 2))
  have hcandidateAxis : candidate ∈ tubeAxisLine unreBased := by
    rw [pureWZ2Proposition64IsotropicPaperTube_axis center hscale]
    exact ⟨wz1PaperAxisPointAtHeight sourceTube (center 2),
      wz1PaperAxisPointAtHeight_mem_axis sourceTube _, rfl⟩
  have hcandidateTwo : candidate 2 = 0 := by
    simp [candidate, pureWZ2Proposition64IsotropicMap,
      wz1PaperAxisPointAtHeight_coord_two hsourceLine]
  have hunreBasedVertical :
      (1 / 2 : ℝ) ≤ |unreBased.direction (2 : Fin 3)| := by
    simpa [unreBased, pureWZ2Proposition64IsotropicPaperTube] using
      hsourceLine.vertical
  apply wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
    (by simpa [pureWZ2Proposition64IsotropicRebasedPaperTube, unreBased] using
      hunreBasedVertical)
  · rw [pureWZ2Proposition64IsotropicRebasedPaperTube_axis center hscale]
    exact ⟨wz1PaperAxisPointAtHeight sourceTube (center 2),
      wz1PaperAxisPointAtHeight_mem_axis sourceTube _, rfl⟩
  · exact hcandidateTwo

/-- The canonical rebasing centers its ordinary unit segment at the
height-zero point of the unchanged supporting line. -/
theorem pureWZ2Proposition64IsotropicRebasedPaperTube_midpoint
    {sourceDelta targetDelta : ℝ}
    (center : Point3) (scale : ℝ)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hvertical : (1 / 2 : ℝ) ≤ |sourceTube.direction (2 : Fin 3)|) :
    wz2PaperTubeMidpoint
        (pureWZ2Proposition64IsotropicRebasedPaperTube
          (targetDelta := targetDelta) center scale sourceTube) =
      wz1TubeAxisZeroPoint
        (pureWZ2Proposition64IsotropicRebasedPaperTube
          (targetDelta := targetDelta) center scale sourceTube) := by
  let target := pureWZ2Proposition64IsotropicPaperTube
    (targetDelta := targetDelta) center scale sourceTube
  have htargetVertical : (1 / 2 : ℝ) ≤ |target.direction (2 : Fin 3)| := by
    simpa [target, pureWZ2Proposition64IsotropicPaperTube] using hvertical
  have hdirectionNe : target.direction (2 : Fin 3) ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at htargetVertical
    norm_num at htargetVertical
  have hzeroTwo : wz1TubeAxisZeroPoint target (2 : Fin 3) = 0 :=
    wz1TubeAxisZeroPoint_coord_two target htargetVertical
  apply PiLp.ext
  intro coordinate
  change ((wz1TubeAxisZeroPoint target -
      (1 / 2 : ℝ) • target.direction) +
        (1 / 2 : ℝ) • target.direction) coordinate =
    ((wz1TubeAxisZeroPoint target -
      (1 / 2 : ℝ) • target.direction) -
        (((wz1TubeAxisZeroPoint target -
          (1 / 2 : ℝ) • target.direction) (2 : Fin 3)) /
            target.direction (2 : Fin 3)) • target.direction) coordinate
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hzeroTwo]
  field_simp [hdirectionNe]
  ring

/-- Distance between two points of one paper-oriented axis at prescribed
heights. -/
theorem wz1PaperAxisPointAtHeight_dist_le_two_abs_sub
    {delta firstHeight secondHeight : ℝ}
    (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube) :
    dist (wz1PaperAxisPointAtHeight tube firstHeight)
        (wz1PaperAxisPointAtHeight tube secondHeight) ≤
      2 * |firstHeight - secondHeight| := by
  let direction := wz1PaperDirection tube
  let vertical := direction 2
  have hvertical : 1 / 2 ≤ vertical := hline.1
  have hverticalPos : 0 < vertical := by linarith
  rw [dist_eq_norm]
  have hdifference :
      wz1PaperAxisPointAtHeight tube firstHeight -
          wz1PaperAxisPointAtHeight tube secondHeight =
        ((firstHeight - secondHeight) / vertical) • direction := by
    simp only [wz1PaperAxisPointAtHeight]
    module
  rw [hdifference, norm_smul, wz1PaperDirection_norm, mul_one,
    Real.norm_eq_abs, abs_div, abs_of_pos hverticalPos]
  apply (div_le_iff₀ hverticalPos).2
  nlinarith [abs_nonneg (firstHeight - secondHeight)]

/-- An occupied exact-image carrier in the narrow popular box puts the
canonically rebased isotropic target tube in the fixed paper line class. -/
theorem pureWZ2Proposition64IsotropicRebasedPaperTube_lineClass_of_occupied
    {sourceDelta targetDelta : ℝ}
    (center : Point3) {scale : ℝ} (hscale : 1 ≤ scale)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceDelta : 0 < sourceDelta)
    (hsourceLine : WZ1PaperTubeInLineClass sourceTube)
    (sourcePoint : Point3)
    (hsourcePoint : sourcePoint ∈ wz1PaperTubeCarrier sourceTube)
    (hsourceCenter : dist sourcePoint center ≤ 1 / (12 * scale))
    (htargetDeltaSmall : targetDelta ≤ 1 / 96)
    (hradius : scale * (6 * sourceDelta) +
      2 * targetDelta ≤ 6 * targetDelta) :
    WZ1PaperTubeInLineClass
      (pureWZ2Proposition64IsotropicRebasedPaperTube
        (targetDelta := targetDelta) center scale sourceTube) := by
  let targetTube := pureWZ2Proposition64IsotropicRebasedPaperTube
    (targetDelta := targetDelta) center scale sourceTube
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have hvertical : (1 / 2 : ℝ) ≤ wz1PaperDirection targetTube 2 := by
    simpa [targetTube, pureWZ2Proposition64IsotropicRebasedPaperTube,
      pureWZ2Proposition64IsotropicPaperTube, wz1PaperDirection]
      using hsourceLine.1
  have hsourceThickening := hsourcePoint.1
  rcases exists_dist_le_of_mem_cthickening_closed
      (isClosed_tubeAxisLine sourceTube)
      (mul_nonneg (by norm_num) hsourceDelta.le) hsourceThickening with
    ⟨axisPoint, haxisPoint, hpointAxis⟩
  let sameHeight := wz1PaperAxisPointAtHeight sourceTube (sourcePoint 2)
  have hsameHeightPoint : dist sameHeight sourcePoint ≤ 12 * sourceDelta := by
    exact (wz1Paper_axisPointAtHeight_dist_point_le_two_mul hsourceLine
      sourcePoint axisPoint haxisPoint).trans (by linarith)
  let centerAxis := wz1PaperAxisPointAtHeight sourceTube (center 2)
  have hheightDistance : |center 2 - sourcePoint 2| ≤
      dist sourcePoint center := by
    have h := PiLp.dist_apply_le sourcePoint center (2 : Fin 3)
    simpa [Real.dist_eq, abs_sub_comm] using h
  have hcenterAxisSame : dist centerAxis sameHeight ≤
      2 * dist sourcePoint center := by
    exact (wz1PaperAxisPointAtHeight_dist_le_two_abs_sub sourceTube
      hsourceLine).trans (by gcongr)
  have hcenterAxisPoint : dist centerAxis sourcePoint ≤
      2 * dist sourcePoint center + 12 * sourceDelta := by
    exact (dist_triangle centerAxis sameHeight sourcePoint).trans
      (add_le_add hcenterAxisSame hsameHeightPoint)
  have htargetZero := pureWZ2Proposition64IsotropicRebasedPaperTube_axisZeroPoint
    (targetDelta := targetDelta) center hscalePos sourceTube hsourceLine
  have himageDist : dist (wz1TubeAxisZeroPoint targetTube)
      (pureWZ2Proposition64IsotropicMap center scale sourcePoint) ≤
        1 / 6 + 8 * targetDelta := by
    rw [htargetZero, pureWZ2Proposition64IsotropicMap_dist center hscalePos]
    have hsourceBound : dist centerAxis sourcePoint ≤
        1 / (6 * scale) + 12 * sourceDelta := by
      calc
        dist centerAxis sourcePoint ≤
            2 * dist sourcePoint center + 12 * sourceDelta := hcenterAxisPoint
        _ ≤ 2 * (1 / (12 * scale)) + 12 * sourceDelta := by gcongr
        _ = 1 / (6 * scale) + 12 * sourceDelta := by ring
    calc
      scale * dist centerAxis sourcePoint ≤
          scale * (1 / (6 * scale) + 12 * sourceDelta) := by gcongr
      _ = 1 / 6 + 12 * scale * sourceDelta := by
        field_simp [hscalePos.ne']
      _ ≤ 1 / 6 + 8 * targetDelta := by
        have := hradius
        nlinarith
  have himageNorm :
      ‖pureWZ2Proposition64IsotropicMap center scale sourcePoint‖ ≤ 1 / 12 := by
    rw [show ‖pureWZ2Proposition64IsotropicMap center scale sourcePoint‖ =
      scale * dist sourcePoint center by
        simp [pureWZ2Proposition64IsotropicMap, dist_eq_norm, norm_smul,
          Real.norm_eq_abs, abs_of_pos hscalePos]]
    calc
      scale * dist sourcePoint center ≤ scale * (1 / (12 * scale)) := by
        gcongr
      _ = 1 / 12 := by field_simp [hscalePos.ne']
  have hzeroNorm : ‖wz1TubeAxisZeroPoint targetTube‖ ≤ 1 / 3 := by
    calc
      ‖wz1TubeAxisZeroPoint targetTube‖ ≤
          ‖pureWZ2Proposition64IsotropicMap center scale sourcePoint‖ +
            ‖wz1TubeAxisZeroPoint targetTube -
              pureWZ2Proposition64IsotropicMap center scale sourcePoint‖ :=
        norm_le_norm_add_norm_sub' _ _
      _ ≤ 1 / 12 + (1 / 6 + 8 * targetDelta) := by
        gcongr
        simpa [dist_eq_norm] using himageDist
      _ ≤ 1 / 3 := by linarith
  have hzeroCoord : ∀ coordinate : Fin 3,
      |wz1TubeAxisZeroPoint targetTube coordinate| ≤ 1 / 3 := by
    intro coordinate
    have hcoordinate :
        |wz1TubeAxisZeroPoint targetTube coordinate| ≤
          ‖wz1TubeAxisZeroPoint targetTube‖ := by
      simpa only [Real.norm_eq_abs] using
        (PiLp.norm_apply_le (wz1TubeAxisZeroPoint targetTube) coordinate)
    exact hcoordinate.trans hzeroNorm
  refine ⟨hvertical, ?_, ?_⟩
  · exact hzeroCoord 0
  · exact hzeroCoord 1

/-- The ordinary final-grid saturation of an isotropically dilated carrier
still lies in the corresponding rebased paper tube.  The tube-radius budget
pays for the source thickening and one target grid-cell diameter, while the
popular-box window keeps the whole saturated cell inside the ambient crop. -/
theorem pureWZ2Proposition64IsotropicCubicalSaturation_subset_rebasedTube
    {sourceDelta targetDelta : ℝ}
    (center : Point3) {scale : ℝ} (hscale : 1 ≤ scale)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hradius : scale * (6 * sourceDelta) +
      2 * targetDelta ≤ 6 * targetDelta)
    (sourceCarrier : Set Point3)
    (hsourceCarrier : sourceCarrier ⊆ wz1PaperTubeCarrier sourceTube)
    (hsourceWindow : sourceCarrier ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    wz1PaperCubicalSaturation targetDelta
        (pureWZ2Proposition64IsotropicMap center scale '' sourceCarrier) ⊆
      wz1PaperTubeCarrier
        (pureWZ2Proposition64IsotropicRebasedPaperTube
          (targetDelta := targetDelta) center scale sourceTube) := by
  intro point hpoint
  rcases hpoint with ⟨imagePoint, ⟨sourcePoint, hsourcePoint, rfl⟩, hcell⟩
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have hpointCell :
      point ∈ wz1PaperGridCube targetDelta
        (wz1PaperGridIndex targetDelta point) :=
    (mem_wz1PaperGridCube _ _ _).mpr rfl
  have himageCell :
      pureWZ2Proposition64IsotropicMap center scale sourcePoint ∈
        wz1PaperGridCube targetDelta
          (wz1PaperGridIndex targetDelta point) :=
    (mem_wz1PaperGridCube _ _ _).mpr hcell.symm
  have hgridDist :
      dist point
          (pureWZ2Proposition64IsotropicMap center scale sourcePoint) <
        2 * targetDelta :=
    wz1_paper_grid_cube_diameter_lt_two_rho htargetDelta
      hpointCell himageCell
  have hsourceTube := hsourceCarrier hsourcePoint
  rcases exists_dist_le_of_mem_cthickening_closed
      (isClosed_tubeAxisLine sourceTube)
      (mul_nonneg (by norm_num) hsourceDelta.le) hsourceTube.1 with
    ⟨axisPoint, haxisPoint, hsourceAxis⟩
  have himageAxis :
      pureWZ2Proposition64IsotropicMap center scale axisPoint ∈
        tubeAxisLine
          (pureWZ2Proposition64IsotropicRebasedPaperTube
            (targetDelta := targetDelta) center scale sourceTube) := by
    rw [pureWZ2Proposition64IsotropicRebasedPaperTube_axis center hscalePos]
    exact ⟨axisPoint, haxisPoint, rfl⟩
  have himageSourceAxis :
      dist (pureWZ2Proposition64IsotropicMap center scale sourcePoint)
          (pureWZ2Proposition64IsotropicMap center scale axisPoint) ≤
        scale * (6 * sourceDelta) := by
    rw [pureWZ2Proposition64IsotropicMap_dist center hscalePos]
    gcongr
  have htargetDistance :
      dist point
          (pureWZ2Proposition64IsotropicMap center scale axisPoint) ≤
        6 * targetDelta := by
    calc
      _ ≤ dist point
            (pureWZ2Proposition64IsotropicMap center scale sourcePoint) +
          dist (pureWZ2Proposition64IsotropicMap center scale sourcePoint)
            (pureWZ2Proposition64IsotropicMap center scale axisPoint) :=
        dist_triangle _ _ _
      _ ≤ 2 * targetDelta + scale * (6 * sourceDelta) := by linarith
      _ ≤ 6 * targetDelta := by linarith
  have hsourceBall := hsourceWindow hsourcePoint
  rw [Metric.mem_closedBall] at hsourceBall
  have himageNorm :
      ‖pureWZ2Proposition64IsotropicMap center scale sourcePoint‖ ≤
        1 / 2 := by
    rw [show ‖pureWZ2Proposition64IsotropicMap center scale sourcePoint‖ =
      scale * dist sourcePoint center by
        simp [pureWZ2Proposition64IsotropicMap, dist_eq_norm, norm_smul,
          Real.norm_eq_abs, abs_of_pos hscalePos]]
    calc
      scale * dist sourcePoint center ≤ scale * (1 / (2 * scale)) := by
        gcongr
      _ = 1 / 2 := by field_simp [hscalePos.ne']
  have hpointBox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
    have hcoordinate : ∀ coordinate : Fin 3, |point coordinate| ≤ 1 := by
      intro coordinate
      have hdiff :
          |point coordinate -
              pureWZ2Proposition64IsotropicMap center scale sourcePoint
                coordinate| ≤
            dist point
              (pureWZ2Proposition64IsotropicMap center scale sourcePoint) := by
        simpa [Real.dist_eq] using
          PiLp.dist_apply_le point
            (pureWZ2Proposition64IsotropicMap center scale sourcePoint)
              coordinate
      have himageCoordinate :
          |pureWZ2Proposition64IsotropicMap center scale sourcePoint
              coordinate| ≤ 1 / 2 := by
        have hnormCoordinate :
            |pureWZ2Proposition64IsotropicMap center scale sourcePoint
                coordinate| ≤
              ‖pureWZ2Proposition64IsotropicMap center scale sourcePoint‖ := by
          simpa only [Real.norm_eq_abs] using
            (PiLp.norm_apply_le
              (pureWZ2Proposition64IsotropicMap center scale sourcePoint)
                coordinate)
        exact hnormCoordinate.trans himageNorm
      calc
        |point coordinate| ≤
            |point coordinate -
                pureWZ2Proposition64IsotropicMap center scale sourcePoint
                  coordinate| +
              |pureWZ2Proposition64IsotropicMap center scale sourcePoint
                coordinate| := by
          simpa only [sub_add_cancel] using
            abs_add_le (point coordinate -
              pureWZ2Proposition64IsotropicMap center scale sourcePoint
                coordinate)
              (pureWZ2Proposition64IsotropicMap center scale sourcePoint
                coordinate)
        _ ≤ 2 * targetDelta + 1 / 2 := by linarith
        _ ≤ 1 := by linarith
    refine ⟨?_, ?_, ?_⟩ <;> norm_num
    · exact hcoordinate 0
    · exact hcoordinate 1
    · exact hcoordinate 2
  exact ⟨Metric.mem_cthickening_of_dist_le point _ (6 * targetDelta) _
    himageAxis htargetDistance, hpointBox⟩

/-- One-to-one paper family on the isotropically dilated supporting lines. -/
def pureWZ2Proposition64IsotropicPaperFamily
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (center : Point3) (scale : ℝ) :
    Kakeya.Streamlined.TubeFamily targetDelta where
  card := sourceFamily.card
  tube index := pureWZ2Proposition64IsotropicRebasedPaperTube center scale
    (sourceFamily.tube index)

/-- The full final-grid saturation of the isotropically dilated source
shading.  Unlike the older safe carrier, this construction retains every
point of the exact image.  The preceding containment theorem proves directly
that no boundary cell leaves its corresponding paper tube. -/
def pureWZ2Proposition64FullIsotropicPaperShading
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        2 * targetDelta ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    WZ1PaperTubeShading
      (pureWZ2Proposition64IsotropicPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale) where
  carrier index := wz1PaperCubicalSaturation targetDelta
    (pureWZ2Proposition64IsotropicMap center scale ''
      sourceShading.carrier index)
  measurable_carrier index := wz1PaperCubicalSaturation_measurable _ _
  subset_body index :=
    pureWZ2Proposition64IsotropicCubicalSaturation_subset_rebasedTube
      center hscale (sourceFamily.tube index) hsourceDelta htargetDelta
        htargetDeltaSmall hradius (sourceShading.carrier index)
        (sourceShading.subset_body index)
        (fun point hpoint => hsourceWindow ⟨index, hpoint⟩)

theorem pureWZ2Proposition64FullIsotropicPaperShading_cubical
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        2 * targetDelta ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    WZ1PaperIsCubicalShading
      (pureWZ2Proposition64FullIsotropicPaperShading sourceShading center scale
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
          hsourceWindow) := by
  intro index point hpoint
  exact wz1PaperCubicalSaturation_isCubical targetDelta _ point hpoint

/-- The exact isotropic image is retained carrier by carrier. -/
theorem pureWZ2Proposition64FullIsotropicPaperShading_image_subset
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        2 * targetDelta ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    ∀ index,
      pureWZ2Proposition64IsotropicMap center scale ''
          sourceShading.carrier index ⊆
        (pureWZ2Proposition64FullIsotropicPaperShading sourceShading center
          scale hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
            hsourceWindow).carrier index := by
  intro index point hpoint
  exact ⟨point, hpoint, rfl⟩

/-- Cubical saturation loses no indexed mass: the only quantitative change is
the exact cubic Jacobian of the positive isotropic similarity. -/
theorem pureWZ2Proposition64FullIsotropicPaperShading_mass_lower
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) {scale : ℝ} (hscalePos : 0 < scale)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        2 * targetDelta ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    ENNReal.ofReal (scale ^ 3) * sourceShading.mass ≤
      (pureWZ2Proposition64FullIsotropicPaperShading sourceShading center
        scale hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
          hsourceWindow).mass := by
  calc
    ENNReal.ofReal (scale ^ 3) * sourceShading.mass =
        ∑ index, ENNReal.ofReal (scale ^ 3) *
          volume (sourceShading.carrier index) := by
      change ENNReal.ofReal (scale ^ 3) *
          (∑ index, volume (sourceShading.carrier index)) = _
      rw [Finset.mul_sum]
    _ = ∑ index, volume
          (pureWZ2Proposition64IsotropicMap center scale ''
            sourceShading.carrier index) := by
      apply Finset.sum_congr rfl
      intro index _
      rw [pureWZ2Proposition64IsotropicMap_volume_image_eq center hscalePos
        (sourceShading.measurable_carrier index)]
    _ ≤ ∑ index, volume
          ((pureWZ2Proposition64FullIsotropicPaperShading sourceShading center
            scale hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
              hsourceWindow).carrier index) := by
      apply Finset.sum_le_sum
      intro index _
      exact measure_mono
        (pureWZ2Proposition64FullIsotropicPaperShading_image_subset
          sourceShading center scale hsourceDelta htargetDelta
            htargetDeltaSmall hscale hradius hsourceWindow index)
    _ = (pureWZ2Proposition64FullIsotropicPaperShading sourceShading center
          scale hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
            hsourceWindow).mass := rfl

/-- The same exact-image inclusion also retains union volume. -/
theorem pureWZ2Proposition64FullIsotropicPaperShading_union_volume_lower
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) {scale : ℝ} (hscalePos : 0 < scale)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        2 * targetDelta ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    ENNReal.ofReal (scale ^ 3) * volume sourceShading.union ≤
      volume
        (pureWZ2Proposition64FullIsotropicPaperShading sourceShading center
          scale hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
            hsourceWindow).union := by
  have himageSubset :
      pureWZ2Proposition64IsotropicMap center scale '' sourceShading.union ⊆
        (pureWZ2Proposition64FullIsotropicPaperShading sourceShading center
          scale hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
            hsourceWindow).union := by
    rintro point ⟨sourcePoint, ⟨index, hsourcePoint⟩, rfl⟩
    exact ⟨index,
      pureWZ2Proposition64FullIsotropicPaperShading_image_subset
        sourceShading center scale hsourceDelta htargetDelta
          htargetDeltaSmall hscale hradius hsourceWindow index
          ⟨sourcePoint, hsourcePoint, rfl⟩⟩
  rw [← pureWZ2Proposition64IsotropicMap_volume_image_eq center hscalePos
    sourceShading.union_measurable]
  exact measure_mono himageSubset

/-- Every point of the full saturation has an exact-image witness in the same
grid cell. -/
theorem pureWZ2Proposition64FullIsotropicPaperShading_targetWitness
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        2 * targetDelta ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    ∀ point : {point : Point3 // point ∈
      (pureWZ2Proposition64FullIsotropicPaperShading sourceShading center scale
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
          hsourceWindow).union},
      ∃ source : {point : Point3 // point ∈
        pureWZ2Proposition64IsotropicMap center scale '' sourceShading.union},
        dist (point : Point3) (source : Point3) ≤ 2 * targetDelta := by
  intro point
  rcases point.property with ⟨index, imagePoint, himagePoint, hcell⟩
  refine ⟨⟨imagePoint, ?_⟩, ?_⟩
  · rcases himagePoint with ⟨sourcePoint, hsourcePoint, rfl⟩
    exact ⟨sourcePoint, ⟨index, hsourcePoint⟩, rfl⟩
  · exact le_of_lt <|
      wz1_paper_grid_cube_diameter_lt_two_rho htargetDelta
        ((mem_wz1PaperGridCube _ _ _).mpr rfl)
        ((mem_wz1PaperGridCube _ _ _).mpr hcell.symm)

/-- Literal final-grid saturation of the isotropically dilated restricted
exact-image shading. -/
def pureWZ2Proposition64IsotropicPaperShading
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        2 * targetDelta ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    WZ1PaperTubeShading
      (pureWZ2Proposition64IsotropicPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale) where
  carrier index := pureWZ2Proposition64SafeCubicalCarrier targetDelta
    ((pureWZ2Proposition64IsotropicPaperFamily
      (targetDelta := targetDelta) sourceFamily center scale).tube index)
    (pureWZ2Proposition64IsotropicMap center scale ''
      sourceShading.carrier index)
  measurable_carrier index :=
    pureWZ2Proposition64SafeCubicalCarrier_measurable _ _ _
  subset_body index :=
    pureWZ2Proposition64SafeCubicalCarrier_subset_tube _ _ _

theorem pureWZ2Proposition64IsotropicPaperShading_cubical
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        2 * targetDelta ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    WZ1PaperIsCubicalShading
      (pureWZ2Proposition64IsotropicPaperShading sourceShading center scale
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
          hsourceWindow) := by
  intro index point hpoint
  change Fin sourceFamily.card at index
  exact pureWZ2Proposition64SafeCubicalCarrier_isCubical
    targetDelta _ _ point hpoint

theorem pureWZ2Proposition64IsotropicPaperShading_targetWitness
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        2 * targetDelta ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    ∀ point : {point : Point3 // point ∈
      (pureWZ2Proposition64IsotropicPaperShading sourceShading center scale
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
          hsourceWindow).union},
      ∃ source : {point : Point3 // point ∈
        pureWZ2Proposition64IsotropicMap center scale '' sourceShading.union},
        dist (point : Point3) (source : Point3) ≤
          2 * targetDelta := by
  intro point
  rcases point.property with ⟨index, hpoint⟩
  rcases pureWZ2Proposition64SafeCubicalCarrier_cell_meets_image
      targetDelta _ _ hpoint with ⟨imagePoint, himagePoint, hcell⟩
  refine ⟨⟨imagePoint, ?_⟩, ?_⟩
  · rcases himagePoint with ⟨original, horiginal, rfl⟩
    exact ⟨original, ⟨index, horiginal⟩, rfl⟩
  · exact le_of_lt <|
      wz1_paper_grid_cube_diameter_lt_two_rho htargetDelta
        ((mem_wz1PaperGridCube _ _ _).mpr rfl)
        ((mem_wz1PaperGridCube _ _ _).mpr hcell.symm)

/-- On every active target height, the safe final-grid saturation has an
exact isotropic-image witness in the same horizontal slice. -/
theorem pureWZ2Proposition64IsotropicPaperShading_projection_close
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        2 * targetDelta ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale)))
    (targetSlope : SlopeFunction) (hnormalized : targetSlope.IsNormalized) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      ∀ value ∈
        scalarProjection (globalGrainDirection (targetSlope z))
          (horizontalSlice
            (pureWZ2Proposition64IsotropicPaperShading sourceShading center
              scale hsourceDelta htargetDelta htargetDeltaSmall hscale
                hradius hsourceWindow).union z),
        ∃ sourceValue ∈
          scalarProjection (globalGrainDirection (targetSlope z))
            (horizontalSlice
              (pureWZ2Proposition64IsotropicMap center scale ''
                sourceShading.union) z),
          |value - sourceValue| ≤ 4 * targetDelta := by
  intro z hz value hvalue
  rcases hvalue with ⟨point, ⟨⟨index, hpoint⟩, hheight⟩, rfl⟩
  rcases pureWZ2Proposition64SafeCubicalCarrier_projection_close
      targetDelta _ htargetDelta targetSlope hnormalized
      (pureWZ2Proposition64IsotropicMap center scale ''
        sourceShading.carrier index) hz hpoint hheight with
    ⟨imagePoint, himagePoint, hclose⟩
  refine ⟨inner ℝ imagePoint (globalGrainDirection (targetSlope z)), ?_, hclose⟩
  refine ⟨imagePoint, ⟨?_, himagePoint.2⟩, rfl⟩
  rcases himagePoint.1 with ⟨sourcePoint, hsourcePoint, rfl⟩
  exact ⟨sourcePoint, ⟨index, hsourcePoint⟩, rfl⟩

/-- Every final saturated carrier remains within `6 * targetDelta` of the
isotropic image of its corresponding source carrier.  This is the composed
carrier provenance used after the final similarity in Proposition 6.4. -/
theorem pureWZ2Proposition64IsotropicPaperShading_near_source_image
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        2 * targetDelta ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    ∀ index,
      (pureWZ2Proposition64IsotropicPaperShading sourceShading center scale
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
          hsourceWindow).carrier index ⊆
        Metric.cthickening (6 * targetDelta)
          (pureWZ2Proposition64IsotropicMap center scale ''
            sourceShading.carrier index) := by
  intro index point hpoint
  rcases pureWZ2Proposition64SafeCubicalCarrier_cell_meets_image
      targetDelta _ _ hpoint with ⟨imagePoint, himagePoint, hcell⟩
  have hsameCell : dist point imagePoint ≤ 2 * targetDelta :=
    le_of_lt <| wz1_paper_grid_cube_diameter_lt_two_rho htargetDelta
      ((mem_wz1PaperGridCube _ _ _).mpr rfl)
      ((mem_wz1PaperGridCube _ _ _).mpr hcell.symm)
  exact Metric.mem_cthickening_of_dist_le point
    imagePoint
    (6 * targetDelta)
    _
    himagePoint
    (hsameCell.trans (by linarith))

end Kakeya.Assouad

end
