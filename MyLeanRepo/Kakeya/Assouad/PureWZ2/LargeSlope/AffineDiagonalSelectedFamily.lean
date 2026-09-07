import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalRawFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PopularSourceExternalRegularization

/-!
# Midpoint-rebased affine family on the public regularized source

This is the synchronized family boundary for paper Lemma 8.  Every target
tube corresponds to one genuinely selected ambient source tube.  Its public
ordinary midpoint is the affine image of the source ordinary midpoint, while
its cropped shading is the cubical saturation of the literal popular-box
shading under the same common affine map.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

attribute [local instance] Classical.propDecidable

/-- Canonical one-to-one midpoint-rebased target family. -/
def pureWZ2AffineDiagonalSelectedFamily
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband)
    (scale : PureWZ2AffineDiagonalScaleData subband)
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount) :
    Kakeya.Streamlined.TubeFamily scale.targetDelta :=
  { card := regularized.selected.family.card
    tube := fun index =>
    pureWZ2AffineDiagonalPublicTube scale.slopeData.frameSlope center
      scale.slopeData.heightScale scale.slopeData.transverseScale 1
      (regularized.selected.family.tube index)
      (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
      scale.transverse_pos.ne' one_ne_zero }
  where center :=
    (pureWZ2AffineDiagonalCommonCenter popular
      (height := scale.slopeData.anchor))

structure PureWZ2AffineDiagonalSelectedFamilyData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband)
    (scale : PureWZ2AffineDiagonalScaleData subband)
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount) where
  center : Point3
  center_eq : center =
    pureWZ2AffineDiagonalCommonCenter popular
      (height := scale.slopeData.anchor)
  shading : WZ1PaperTubeShading
    (pureWZ2AffineDiagonalSelectedFamily popular scale regularized)
  shading_carrier : ∀ index, shading.carrier index =
    wz1PaperCubicalSaturation scale.targetDelta
      (pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
        scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
          popular.popular.restricted.carrier
            (regularized.selected.embedding index))
  line_class : WZ1PaperIsLineClass
    (pureWZ2AffineDiagonalSelectedFamily popular scale regularized)
  cubical : WZ1PaperIsCubicalShading shading
  axis : ∀ index, tubeAxisLine
      ((pureWZ2AffineDiagonalSelectedFamily popular scale regularized).tube index) =
    pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
      scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
        tubeAxisLine (regularized.selected.family.tube index)
  axis_ambient : ∀ index, tubeAxisLine
      ((pureWZ2AffineDiagonalSelectedFamily popular scale regularized).tube index) =
    pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
      scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
        tubeAxisLine (band.lemma31.data.cfg.family.tube
          (regularized.selected.embedding index))
  exact_image_subset : ∀ index,
    pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
        scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
      popular.popular.restricted.carrier
        (regularized.selected.embedding index) ⊆
      shading.carrier index
  mass_lower : ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
      regularized.selectedWeight ≤ shading.mass

/-- The public midpoint-rebased family is coaxial with the already verified
localized raw family.  Consequently the existing cubical-saturation carrier
proof transfers without changing the literal shading. -/
theorem PureWZ2SubbandPopularBoxData.toAffineDiagonalSelectedFamily
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband)
    (scale : PureWZ2AffineDiagonalScaleData subband)
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount) :
    Nonempty (PureWZ2AffineDiagonalSelectedFamilyData
      popular scale regularized) := by
  let center :=
    pureWZ2AffineDiagonalCommonCenter popular
      (height := scale.slopeData.anchor)
  have hheight : scale.slopeData.heightScale ≠ 0 :=
    (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
  have htransverse : scale.slopeData.transverseScale ≠ 0 :=
    scale.transverse_pos.ne'
  let sourceFamily := regularized.selected.family
  let family :=
    pureWZ2AffineDiagonalSelectedFamily popular scale regularized
  have haxis : ∀ index, tubeAxisLine (family.tube index) =
      pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
        scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
          tubeAxisLine (sourceFamily.tube index) := by
    intro index
    exact pureWZ2AffineDiagonalPublicTube_axis
      scale.slopeData.frameSlope center (sourceFamily.tube index)
      hheight htransverse one_ne_zero
  have haxisAmbient : ∀ index, tubeAxisLine (family.tube index) =
      pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
        scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
          tubeAxisLine (band.lemma31.data.cfg.family.tube
            (regularized.selected.embedding index)) := by
    intro index
    rw [haxis index, regularized.selected.tube_eq index]
  -- Compare with the localized raw tube of the same ambient source.  Both
  -- tubes have the exact same supporting line.
  let localized : Fin sourceFamily.card → Kakeya.DeltaTube scale.targetDelta :=
    fun index => pureWZ2AffineDiagonalRawTube
      scale.slopeData.frameSlope center scale.slopeData.heightScale
      scale.slopeData.transverseScale 1 (sourceFamily.tube index)
      hheight htransverse one_ne_zero
  have hlocalizedAxis : ∀ index,
      tubeAxisLine (localized index) = tubeAxisLine (family.tube index) := by
    intro index
    rw [pureWZ2AffineDiagonalRawTube_axis, haxis index]
  have hsourceLine : WZ1PaperIsLineClass sourceFamily :=
    band.lemma31.data.cfg.line_class.subfamily regularized.selected
  -- The public tube remains in the positive vertical chart and has the same
  -- zero-point bounds as the localized coaxial representative.
  have hlocalizedLine : ∀ index, WZ1PaperTubeInLineClass (localized index) := by
    intro index
    let sourceTube := sourceFamily.tube index
    have hverticalAbs : (1 / 2 : ℝ) ≤
        |(localized index).direction 2| := by
      exact pureWZ2AffineDiagonalDirection_vertical
        scale.slopeData.frameSlope scale.height_lower
        scale.transverse_pos.le (scale.transverse_le.trans (by norm_num))
        sourceTube.direction_unit (hsourceLine index).vertical
    have htargetVertical : (localized index).direction 2 ≠ 0 := by
      intro hzero
      rw [hzero, abs_zero] at hverticalAbs
      norm_num at hverticalAbs
    have hcenterHeight : center 2 = scale.slopeData.anchor := by
      simp [center, pureWZ2AffineDiagonalCommonCenter, point3]
    have hbaseTwo : (localized index).base 2 = 0 := by
      simp only [localized, pureWZ2AffineDiagonalRawTube]
      rw [pureWZ2AffineDiagonalMapCentered_coord_two, hcenterHeight]
      rw [tubeAxisPointAtHeight_coord_two (sourceFamily.tube index)
        (fun hzero => by
          have h := (hsourceLine index).vertical
          rw [hzero, abs_zero] at h
          norm_num at h) scale.slopeData.anchor]
      simp
    have hzero : wz1TubeAxisZeroPoint (localized index) =
        (localized index).base := by
      simp [wz1TubeAxisZeroPoint, hbaseTwo, htargetVertical]
    -- A selected source has positive literal popular-box weight, hence an
    -- actual point in the same narrow source box.
    have hweightPos := regularized.selected_weight_pos index
    have hcarrierNonempty :
        (popular.popular.restricted.carrier
          (regularized.selected.embedding index)).Nonempty := by
      by_contra hempty
      have hset : popular.popular.restricted.carrier
          (regularized.selected.embedding index) = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hempty
      have hzeroWeight : pureWZ2PopularSourceWeight popular
          (regularized.selected.embedding index) = 0 := by
        simp [pureWZ2PopularSourceWeight, hset]
      rw [hzeroWeight] at hweightPos
      exact (lt_irrefl 0 hweightPos)
    rcases hcarrierNonempty with ⟨point, hpoint⟩
    have hbox := by
      rw [popular.popular.restricted_carrier, popular.popular.box_eq] at hpoint
      exact hpoint.2.1
    have hsubband : point ∈ subband.shading.carrier
        (regularized.selected.embedding index) := by
      rw [popular.popular.restricted_carrier] at hpoint
      exact hpoint.1
    rw [subband.carrier_eq] at hsubband
    let halfWidth := point3 (1 / 16) (1 / 16) (scale.rho / 5000)
    have hpointCommonBox : point ∈ wz1AxisBox center halfWidth := by
      intro coordinate
      fin_cases coordinate
      · convert hbox (0 : Fin 3) using 1 <;>
          simp [center, halfWidth, pureWZ2AffineDiagonalCommonCenter,
            point3, wz1AxisBox] <;> norm_num
      · convert hbox (1 : Fin 3) using 1 <;>
          simp [center, halfWidth, pureWZ2AffineDiagonalCommonCenter,
            point3, wz1AxisBox] <;> norm_num
      · have hhalf : |point 2 - scale.slopeData.anchor| ≤
            subband.right - subband.left := by
          rw [abs_le]
          constructor <;>
            linarith [hsubband.2.1, hsubband.2.2,
              scale.slope_anchor_mem.1, scale.slope_anchor_mem.2]
        have hlength : subband.right - subband.left =
            scale.rho / 5000 := by
          rw [subband.length_eq, band.length_eq, scale.rho_eq]
          ring
        simpa [center, halfWidth, pureWZ2AffineDiagonalCommonCenter,
          point3, wz1AxisBox, hlength] using hhalf
    have hheightBound : |center 2 - point 2| ≤ halfWidth 2 := by
      simpa [center, halfWidth, pureWZ2AffineDiagonalCommonCenter, point3,
        abs_sub_comm] using hpointCommonBox (2 : Fin 3)
    have haxisBound := pureWZ2_axis_center_coordinate_bound
      band.lemma31.data.cfg.extremal.delta_pos (hsourceLine index)
      center halfWidth point
      (by
        rw [regularized.selected.tube_eq index]
        exact (popular.popular.restricted.subset_body
          (regularized.selected.embedding index)) hpoint)
      hpointCommonBox hheightBound
    have haxisCenter : ∀ coordinate,
        |(tubeAxisPointAtHeight (sourceFamily.tube index)
          scale.slopeData.anchor -
          center) coordinate| ≤
            2 * (scale.rho / 5000) + 18 * delta + 1 / 16 := by
      intro coordinate
      have hbound := haxisBound coordinate
      fin_cases coordinate
      · rw [hcenterHeight] at hbound
        simpa [halfWidth, point3] using hbound
      · rw [hcenterHeight] at hbound
        simpa [halfWidth, point3] using hbound
      · have hrhoSmall : 3 * (scale.rho / 5000) ≤ 1 / 16 := by
          rw [scale.rho_eq]
          linarith [band.lemma31.rho_tiny]
        rw [hcenterHeight] at hbound
        calc
          |(tubeAxisPointAtHeight (sourceFamily.tube index)
              scale.slopeData.anchor -
              center) 2| ≤ 2 * (scale.rho / 5000) + 18 * delta +
                scale.rho / 5000 := by
            simpa [halfWidth, point3] using hbound
          _ = 3 * (scale.rho / 5000) + 18 * delta := by ring
          _ ≤ 2 * (scale.rho / 5000) + 18 * delta + 1 / 16 := by
            linarith
    have hsmallAxis : ∀ coordinate,
        |(tubeAxisPointAtHeight (sourceFamily.tube index)
          scale.slopeData.anchor -
          center) coordinate| ≤ 1 / 15 := by
      intro coordinate
      have h := haxisCenter coordinate
      have hrho := band.lemma31.rho_tiny
      have hdelta := band.lemma31.delta_le_rho_sq
      rw [scale.rho_eq] at h
      have hrhoNonneg : 0 ≤ band.lemma31.data.rho.1 := by
        rw [← scale.rho_eq]
        exact scale.rho_pos.le
      nlinarith [sq_nonneg band.lemma31.data.rho.1]
    have hframe : |scale.slopeData.frameSlope| ≤ 1 := by
      exact scale.slopeData.frameSlope_bound
    have hx := hsmallAxis 0
    have hy := hsmallAxis 1
    have hbaseZero : |(localized index).base 0| ≤ 1 / 3 := by
      simp only [localized, pureWZ2AffineDiagonalRawTube]
      rw [pureWZ2AffineDiagonalMapCentered_coord_zero _ _ _ _ _ one_ne_zero]
      rw [hcenterHeight]
      simp only [one_mul]
      rw [abs_div, abs_of_pos (pureWZ2HorizontalNorm_pos _)]
      have h := affineHorizontalFirstBound hframe hx hy (by norm_num)
      exact h.trans (by norm_num)
    have hbaseOne : |(localized index).base 1| ≤ 1 / 3 := by
      simp only [localized, pureWZ2AffineDiagonalRawTube]
      rw [pureWZ2AffineDiagonalMapCentered_coord_one _ _ _ _ _
        htransverse one_ne_zero]
      rw [hcenterHeight]
      simp only [one_mul]
      rw [abs_mul, abs_div, abs_of_pos scale.transverse_pos,
        abs_of_pos (pureWZ2HorizontalNorm_pos _)]
      have h := affineHorizontalSecondBound hframe scale.transverse_pos.le
        (scale.transverse_le.trans (by norm_num)) hx hy (by norm_num)
      have htwo : (2 : ℝ) * (1 / 15) ≤ 1 / 3 := by norm_num
      simpa [PiLp.sub_apply, mul_div_assoc] using h.trans htwo
    exact ⟨by
      unfold wz1PaperDirection
      split_ifs with horientation
      · exact hverticalAbs.trans_eq (abs_of_nonneg horientation)
      · exact hverticalAbs.trans_eq
          (abs_of_neg (lt_of_not_ge horientation)),
      by rw [hzero]; exact hbaseZero,
      by rw [hzero]; exact hbaseOne⟩
  have hline : WZ1PaperIsLineClass family := by
    intro index
    have hsame := hlocalizedAxis index
    -- Line-class data depends only on the positive vertical direction and
    -- the supporting-line zero point.  The two constructors use the same
    -- normalized direction definitionally.
    have hdir : (family.tube index).direction =
        (localized index).direction := rfl
    have hlocalizedVerticalAbs : (1 / 2 : ℝ) ≤
        |(localized index).direction 2| := by
      exact pureWZ2AffineDiagonalDirection_vertical
        scale.slopeData.frameSlope scale.height_lower
        scale.transverse_pos.le (scale.transverse_le.trans (by norm_num))
        (sourceFamily.tube index).direction_unit
        (hsourceLine index).vertical
    have hzero : wz1TubeAxisZeroPoint (family.tube index) =
        wz1TubeAxisZeroPoint (localized index) := by
      symm
      apply wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
        hlocalizedVerticalAbs
      · rw [hsame]
        exact wz1TubeAxisZeroPoint_mem_axis (family.tube index)
      · exact wz1TubeAxisZeroPoint_coord_two (family.tube index) (by
          simpa [hdir] using hlocalizedVerticalAbs)
    have hpaperDir : wz1PaperDirection (family.tube index) =
        wz1PaperDirection (localized index) := by
      simp [wz1PaperDirection, hdir]
    rcases hlocalizedLine index with ⟨hv, hx, hy⟩
    exact ⟨by rw [hpaperDir]; exact hv, by rw [hzero]; exact hx,
      by rw [hzero]; exact hy⟩
  let targetCarrier : Fin family.card → Set Point3 := fun index =>
    wz1PaperCubicalSaturation scale.targetDelta
      (pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
        scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
          popular.popular.restricted.carrier
            (regularized.selected.embedding index))
  have hcarrierSubset : ∀ index, targetCarrier index ⊆
      wz1PaperTubeCarrier (family.tube index) := by
    intro index point hpoint
    -- The proof is identical to the raw-family carrier proof because only
    -- the supporting line enters the cropped carrier.
    rcases hpoint with ⟨imagePoint, ⟨sourcePoint, hsourcePoint, rfl⟩, hgrid⟩
    have hsameCell : dist point
        (pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
          scale.slopeData.heightScale scale.slopeData.transverseScale 1
          sourcePoint) < 2 * scale.targetDelta := by
      apply wz1_paper_grid_cube_diameter_lt_two_rho scale.targetDelta_pos
        (cell := wz1PaperGridIndex scale.targetDelta point)
      · exact (mem_wz1PaperGridCube _ _ _).mpr rfl
      · exact (mem_wz1PaperGridCube _ _ _).mpr hgrid.symm
    have hsourceThick :=
      (popular.popular.restricted.subset_body
        (regularized.selected.embedding index) hsourcePoint).1
    rcases exists_dist_le_of_mem_cthickening_closed
        (isClosed_tubeAxisLine
          (band.lemma31.data.cfg.family.tube
            (regularized.selected.embedding index)))
        (mul_nonneg (by norm_num)
          band.lemma31.data.cfg.extremal.delta_pos.le) hsourceThick with
      ⟨axisPoint, haxisPoint, haxisDist⟩
    let targetAxisPoint := pureWZ2AffineDiagonalMapCentered
      scale.slopeData.frameSlope center scale.slopeData.heightScale
      scale.slopeData.transverseScale 1 axisPoint
    have htargetAxis : targetAxisPoint ∈ tubeAxisLine (family.tube index) := by
      rw [haxisAmbient index]
      exact ⟨axisPoint, haxisPoint, rfl⟩
    have himageDist : dist
        (pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
          scale.slopeData.heightScale scale.slopeData.transverseScale 1
          sourcePoint) targetAxisPoint ≤ 3 * scale.targetDelta := by
      rw [dist_eq_norm]
      rw [pureWZ2AffineDiagonalMapCentered_sub]
      calc
        ‖pureWZ2AffineDiagonalLinear scale.slopeData.frameSlope
            scale.slopeData.heightScale scale.slopeData.transverseScale 1
            (sourcePoint - axisPoint)‖ ≤
          scale.slopeData.heightScale * ‖sourcePoint - axisPoint‖ :=
            pureWZ2AffineDiagonalLinear_norm_le_height _
              (by linarith [scale.height_lower]) scale.transverse_pos.le
              (scale.transverse_le.trans (by norm_num)) _
        _ ≤ scale.slopeData.heightScale * (6 * delta) := by
          apply mul_le_mul_of_nonneg_left
          · simpa [dist_eq_norm] using haxisDist
          · linarith [scale.height_lower]
        _ = 3 * scale.targetDelta := by rw [scale.targetDelta_eq]; ring
    have htargetDist : dist point targetAxisPoint <
        6 * scale.targetDelta := by
      calc
        dist point targetAxisPoint ≤
            dist point (pureWZ2AffineDiagonalMapCentered
              scale.slopeData.frameSlope center scale.slopeData.heightScale
              scale.slopeData.transverseScale 1 sourcePoint) +
            dist (pureWZ2AffineDiagonalMapCentered
              scale.slopeData.frameSlope center scale.slopeData.heightScale
              scale.slopeData.transverseScale 1 sourcePoint)
              targetAxisPoint := dist_triangle _ _ _
        _ < 2 * scale.targetDelta + 3 * scale.targetDelta :=
          add_lt_add_of_lt_of_le hsameCell himageDist
        _ < 6 * scale.targetDelta := by linarith [scale.targetDelta_pos]
    refine ⟨Metric.mem_cthickening_of_dist_le point targetAxisPoint
      (6 * scale.targetDelta) _ htargetAxis htargetDist.le, ?_⟩
    have hpopular := hsourcePoint
    rw [popular.popular.restricted_carrier, popular.popular.box_eq] at hpopular
    have hbox := hpopular.2.1
    have hsubband : sourcePoint ∈ subband.shading.carrier
        (regularized.selected.embedding index) := hpopular.1
    rw [subband.carrier_eq] at hsubband
    have hframe : |scale.slopeData.frameSlope| ≤ 1 := by
      exact scale.slopeData.frameSlope_bound
    have hx : |sourcePoint 0 - center 0| ≤ 1 / 16 := by
      convert hbox (0 : Fin 3) using 1 <;>
        simp [center, pureWZ2AffineDiagonalCommonCenter, point3, wz1AxisBox] <;>
        norm_num
    have hy : |sourcePoint 1 - center 1| ≤ 1 / 16 := by
      convert hbox (1 : Fin 3) using 1 <;>
        simp [center, pureWZ2AffineDiagonalCommonCenter, point3, wz1AxisBox] <;>
        norm_num
    have hz : |sourcePoint 2 - center 2| ≤ scale.rho / 5000 := by
      have hhalf : |sourcePoint 2 - scale.slopeData.anchor| ≤
          subband.right - subband.left := by
        rw [abs_le]
        constructor <;>
          linarith [hsubband.2.1, hsubband.2.2,
            scale.slope_anchor_mem.1, scale.slope_anchor_mem.2]
      rw [subband.length_eq, band.length_eq, ← scale.rho_eq] at hhalf
      convert hhalf using 1 <;>
        simp [center, pureWZ2AffineDiagonalCommonCenter, point3] <;> ring
    let image := pureWZ2AffineDiagonalMapCentered
      scale.slopeData.frameSlope center scale.slopeData.heightScale
      scale.slopeData.transverseScale 1 sourcePoint
    have himage0 : |image 0| ≤ 1 / 8 := by
      rw [pureWZ2AffineDiagonalMapCentered_coord_zero _ _ _ _ _ one_ne_zero]
      simp only [one_mul]
      rw [abs_div, abs_of_pos (pureWZ2HorizontalNorm_pos _)]
      calc
        |sourcePoint 0 - center 0 +
              scale.slopeData.frameSlope * (sourcePoint 1 - center 1)| /
            pureWZ2HorizontalNorm scale.slopeData.frameSlope ≤
          2 * (1 / 16) :=
            affineHorizontalFirstBound hframe hx hy (by norm_num)
        _ = 1 / 8 := by norm_num
    have himage1 : |image 1| ≤ 1 / 8 := by
      rw [pureWZ2AffineDiagonalMapCentered_coord_one _ _ _ _ _
        htransverse one_ne_zero]
      simp only [one_mul]
      rw [abs_mul, abs_div, abs_of_pos scale.transverse_pos,
        abs_of_pos (pureWZ2HorizontalNorm_pos _)]
      have h := affineHorizontalSecondBound hframe scale.transverse_pos.le
        (scale.transverse_le.trans (by norm_num)) hx hy (by norm_num)
      convert h using 1 <;> ring
    have himage2 : |image 2| ≤ 3 / 5 := by
      rw [pureWZ2AffineDiagonalMapCentered_coord_two]
      simp only [one_mul, abs_mul,
        abs_of_pos (by linarith [scale.height_lower] :
          0 < scale.slopeData.heightScale)]
      calc
        scale.slopeData.heightScale * |sourcePoint 2 - center 2| ≤
            (3000 / scale.rho) * (scale.rho / 5000) := by
          exact mul_le_mul scale.height_upper hz (abs_nonneg _)
            (div_nonneg (by norm_num) scale.rho_pos.le)
        _ = 3 / 5 := by field_simp [scale.rho_pos.ne']; ring
        _ ≤ 3 / 5 := le_rfl
    have hcoordClose : ∀ coordinate,
        |point coordinate - image coordinate| < 2 * scale.targetDelta := by
      intro coordinate
      simpa [Real.dist_eq] using
        (PiLp.dist_apply_le point image coordinate).trans_lt hsameCell
    have hpoint0 : |point 0| ≤ 1 := by
      calc
        |point 0| = |(point 0 - image 0) + image 0| := by ring_nf
        _ ≤ |point 0 - image 0| + |image 0| := abs_add_le _ _
        _ ≤ 1 := by
          linarith [hcoordClose 0, himage0, scale.targetDelta_le_tenth]
    have hpoint1 : |point 1| ≤ 1 := by
      calc
        |point 1| = |(point 1 - image 1) + image 1| := by ring_nf
        _ ≤ |point 1 - image 1| + |image 1| := abs_add_le _ _
        _ ≤ 1 := by
          linarith [hcoordClose 1, himage1, scale.targetDelta_le_tenth]
    have hpoint2 : |point 2| ≤ 1 := by
      calc
        |point 2| = |(point 2 - image 2) + image 2| := by ring_nf
        _ ≤ |point 2 - image 2| + |image 2| := abs_add_le _ _
        _ ≤ 1 := by
          linarith [hcoordClose 2, himage2, scale.targetDelta_le_tenth]
    simpa [Kakeya.Streamlined.axisBox] using
      (show |point 0| ≤ 1 ∧ |point 1| ≤ 1 ∧ |point 2| ≤ 1 from
        ⟨hpoint0, hpoint1, hpoint2⟩)
  let shading : WZ1PaperTubeShading family :=
    { carrier := targetCarrier
      measurable_carrier := fun index =>
        wz1PaperCubicalSaturation_measurable scale.targetDelta _
      subset_body := hcarrierSubset }
  have hcubical : WZ1PaperIsCubicalShading shading := by
    intro index point hpoint
    exact wz1PaperCubicalSaturation_isCubical scale.targetDelta _ point hpoint
  have himageSubset : ∀ index,
      pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
          scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
        popular.popular.restricted.carrier
          (regularized.selected.embedding index) ⊆ shading.carrier index := by
    intro index point hpoint
    exact ⟨point, hpoint, rfl⟩
  have hmass : ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
      regularized.selectedWeight ≤ shading.mass := by
    rw [regularized.selectedWeight_eq]
    change ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
        (∑ index, volume (popular.popular.restricted.carrier
          (regularized.selected.embedding index))) ≤
      ∑ index, volume (shading.carrier index)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro index _
    have himageMeasure : volume
          (pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
              scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
            popular.popular.restricted.carrier
              (regularized.selected.embedding index)) ≤
        volume (shading.carrier index) :=
      measure_mono (himageSubset index)
    rw [scale.slopeData.heightScale_eq,
      scale.slopeData.transverseScale_eq] at himageMeasure
    rw [pureWZ2AffineDiagonalMapCentered_volume_image_general
      scale.slopeData.frameSlope center
      scale.slopeData.rotatedSlopeScale_pos
      scale.slopeData.normalizationConstant_pos
      (popular.popular.restricted.measurable_carrier
        (regularized.selected.embedding index))] at himageMeasure
    exact himageMeasure
  exact ⟨{
    center := center
    center_eq := rfl
    shading := shading
    shading_carrier := fun _ => rfl
    line_class := hline
    cubical := hcubical
    axis := haxis
    axis_ambient := haxisAmbient
    exact_image_subset := himageSubset
    mass_lower := hmass
  }⟩

end Kakeya.Assouad

end
