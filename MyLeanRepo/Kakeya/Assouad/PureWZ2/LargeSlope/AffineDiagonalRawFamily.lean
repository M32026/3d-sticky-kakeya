import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalGeometryBounds
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.SubbandPopularBox
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GridCubeCover

/-!
# Raw exact-axis affine diagonal family and literal shading
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

attribute [local instance] Classical.propDecidable

lemma affineHorizontalFirstBound
    {frame x y bound : ℝ}
    (hframe : |frame| ≤ 1) (hx : |x| ≤ bound) (hy : |y| ≤ bound)
    (hbound : 0 ≤ bound) :
    |x + frame * y| / pureWZ2HorizontalNorm frame ≤ 2 * bound := by
  have hn : 1 ≤ pureWZ2HorizontalNorm frame := by
    exact Real.one_le_sqrt.mpr (by nlinarith)
  have hnum : |x + frame * y| ≤ 2 * bound := by
    calc
      |x + frame * y| ≤ |x| + |frame * y| := abs_add_le _ _
      _ = |x| + |frame| * |y| := by rw [abs_mul]
      _ ≤ bound + 1 * bound := by gcongr
      _ = 2 * bound := by ring
  calc
    |x + frame * y| / pureWZ2HorizontalNorm frame ≤
        (2 * bound) / pureWZ2HorizontalNorm frame :=
      div_le_div_of_nonneg_right hnum (pureWZ2HorizontalNorm_pos _).le
    _ ≤ (2 * bound) / 1 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hn
    _ = 2 * bound := by ring

lemma affineHorizontalSecondBound
    {frame transverse x y bound : ℝ}
    (hframe : |frame| ≤ 1)
    (htransverse : 0 ≤ transverse) (htransverseOne : transverse ≤ 1)
    (hx : |x| ≤ bound) (hy : |y| ≤ bound) (hbound : 0 ≤ bound) :
    transverse * |-frame * x + y| / pureWZ2HorizontalNorm frame ≤
      2 * bound := by
  have hinner := affineHorizontalFirstBound (frame := -frame)
    (x := y) (y := x) (bound := bound) (by simpa) hy hx hbound
  have hnorm : pureWZ2HorizontalNorm (-frame) =
      pureWZ2HorizontalNorm frame := by
    simp [pureWZ2HorizontalNorm]
  rw [hnorm] at hinner
  have heq : |-frame * x + y| = |y + (-frame) * x| := by ring_nf
  rw [heq]
  have hproduct : transverse *
      (|y + -frame * x| / pureWZ2HorizontalNorm frame) ≤
        1 * (2 * bound) := by
    calc
      transverse * (|y + -frame * x| / pureWZ2HorizontalNorm frame) ≤
          transverse * (2 * bound) :=
        mul_le_mul_of_nonneg_left hinner htransverse
      _ ≤ 1 * (2 * bound) :=
        mul_le_mul_of_nonneg_right htransverseOne (by positivity)
  calc
    transverse * |y + -frame * x| / pureWZ2HorizontalNorm frame =
        transverse * (|y + -frame * x| /
          pureWZ2HorizontalNorm frame) := by ring
    _ ≤ 1 * (2 * bound) := hproduct
    _ = 2 * bound := by ring

/-- The common translation center: horizontal coordinates come from the
mass-popular box and the height comes from the mass-popular subband. -/
def pureWZ2AffineDiagonalCommonCenter
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband)
    (height : ℝ := subband.anchor) : Point3 :=
  point3 (popular.popular.center 0) (popular.popular.center 1) height

structure PureWZ2AffineDiagonalRawFamilyData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband)
    (scale : PureWZ2AffineDiagonalScaleData subband) where
  center : Point3
  center_eq : center =
    pureWZ2AffineDiagonalCommonCenter popular scale.slopeData.anchor
  center_height_bound : |center 2| ≤ 1
  frame_bound : |scale.slopeData.frameSlope| ≤ 1
  family : Kakeya.Streamlined.TubeFamily scale.targetDelta
  supportIndex : Fin family.card ≃ Fin
    (wz2PaperNonemptyCarrierSubfamily popular.popular.restricted).family.card
  sourceParent : Fin family.card →
    Fin band.lemma31.data.cfg.family.card
  sourceParent_eq : sourceParent = fun index =>
    ⇑(wz2PaperNonemptyCarrierSubfamily popular.popular.restricted).embedding
      (supportIndex index)
  sourceParent_injective : Function.Injective sourceParent
  family_tube : ∀ index, family.tube index =
    pureWZ2AffineDiagonalRawTube scale.slopeData.frameSlope center
      scale.slopeData.heightScale scale.slopeData.transverseScale 1
      ((wz2PaperNonemptyCarrierSubfamily
        popular.popular.restricted).family.tube (supportIndex index))
      (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
      scale.transverse_pos.ne' one_ne_zero
  shading : WZ1PaperTubeShading family
  shading_carrier : ∀ index, shading.carrier index =
    wz1PaperCubicalSaturation scale.targetDelta
      (pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
        scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
          popular.sourceShading.carrier (supportIndex index))
  line_class : WZ1PaperIsLineClass family
  midpoint_local : ∀ index,
    ‖wz2PaperTubeMidpoint (family.tube index)‖ ≤ 3
  cubical : WZ1PaperIsCubicalShading shading
  axis : ∀ index, tubeAxisLine (family.tube index) =
    pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
      scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
        tubeAxisLine ((wz2PaperNonemptyCarrierSubfamily
          popular.popular.restricted).family.tube (supportIndex index))
  axis_ambient : ∀ index, tubeAxisLine (family.tube index) =
    pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
      scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
        tubeAxisLine
          (band.lemma31.data.cfg.family.tube
            (sourceParent index))
  exact_image_subset : ∀ index,
    pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
        scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
      popular.sourceShading.carrier (supportIndex index) ⊆
        shading.carrier index
  union_image_subset :
    pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
        scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
      popular.sourceShading.union ⊆ shading.union
  mass_lower : ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
    popular.sourceShading.mass ≤ shading.mass

theorem PureWZ2SubbandPopularBoxData.toAffineDiagonalRawFamily
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband)
    (scale : PureWZ2AffineDiagonalScaleData subband) :
    Nonempty (PureWZ2AffineDiagonalRawFamilyData popular scale) := by
  let sourceFamily :=
    (wz2PaperNonemptyCarrierSubfamily popular.popular.restricted).family
  let sourceShading : WZ1PaperTubeShading sourceFamily := popular.sourceShading
  let sourceIndex : Fin sourceFamily.card →
      Fin band.lemma31.data.cfg.family.card :=
    (wz2PaperNonemptyCarrierSubfamily popular.popular.restricted).embedding
  let center :=
    pureWZ2AffineDiagonalCommonCenter popular scale.slopeData.anchor
  have hheight : scale.slopeData.heightScale ≠ 0 := by
    exact (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
  have htransverse : scale.slopeData.transverseScale ≠ 0 :=
    scale.transverse_pos.ne'
  let family : Kakeya.Streamlined.TubeFamily scale.targetDelta :=
    { card := sourceFamily.card
      tube := fun index =>
        pureWZ2AffineDiagonalRawTube scale.slopeData.frameSlope center
          scale.slopeData.heightScale scale.slopeData.transverseScale 1
          (sourceFamily.tube index) hheight htransverse one_ne_zero }
  let supportIndex : Fin family.card ≃ Fin sourceFamily.card := Equiv.refl _
  have hsourceLine : WZ1PaperIsLineClass sourceFamily := by
    intro index
    change WZ1PaperTubeInLineClass
      (band.lemma31.data.cfg.family.tube
        (sourceIndex index))
    exact band.lemma31.data.cfg.line_class
      (sourceIndex index)
  have hframe : |scale.slopeData.frameSlope| ≤ 1 := by
    exact scale.slopeData.frameSlope_bound
  have hcenterCoords : center 0 = popular.popular.center 0 ∧
      center 1 = popular.popular.center 1 ∧
        center 2 = scale.slopeData.anchor := by
    simp [center, pureWZ2AffineDiagonalCommonCenter, point3]
  have hcenterHeightBound : |center 2| ≤ 1 := by
    rw [hcenterCoords.2.2, abs_le]
    exact ⟨band.lemma31.data.scaleData.slabLeft_mem.trans
        (band.left_mem.trans <| subband.left_mem.trans
          scale.slope_anchor_mem.1),
      scale.slope_anchor_mem.2.trans <| subband.right_mem.trans <|
        band.right_mem.trans
          band.lemma31.data.scaleData.slabRight_mem⟩
  have hsourceWitness : ∀ index, ∃ point,
      point ∈ sourceShading.carrier index ∧
      point ∈ wz1AxisBox popular.popular.center
        (point3 (1 / 16) (1 / 16) (1 / 16)) ∧
      point 2 ∈ Set.Icc subband.left subband.right := by
    intro index
    rcases popular.source_carrier_nonempty index with ⟨point, hpoint⟩
    refine ⟨point, hpoint, ?_, ?_⟩
    · have hpopular : point ∈ popular.popular.restricted.carrier
          (sourceIndex index) := by
        rw [← popular.source_carrier_eq index]
        exact hpoint
      rw [popular.popular.restricted_carrier] at hpopular
      rw [popular.popular.box_eq] at hpopular
      have hbox := hpopular.2.1
      intro coordinate
      have hc := hbox coordinate
      norm_num at hc ⊢
      exact hc
    · have hpopular : point ∈ popular.popular.restricted.carrier
          (sourceIndex index) := by
        rw [← popular.source_carrier_eq index]
        exact hpoint
      rw [popular.popular.restricted_carrier] at hpopular
      have hsubband : point ∈ subband.shading.carrier
          (sourceIndex index) := hpopular.1
      rw [subband.carrier_eq] at hsubband
      exact hsubband.2
  have haxisCenter : ∀ index coordinate,
      |(tubeAxisPointAtHeight (sourceFamily.tube index) scale.slopeData.anchor -
          center) coordinate| ≤
        2 * (scale.rho / 5000) + 18 * delta + 1 / 16 := by
    intro index coordinate
    rcases hsourceWitness index with ⟨point, hpoint, hbox, hsubband⟩
    let halfWidth := point3 (1 / 16) (1 / 16) (scale.rho / 5000)
    have hpointCommonBox : point ∈ wz1AxisBox center halfWidth := by
      intro i
      fin_cases i
      · simpa [center, halfWidth, pureWZ2AffineDiagonalCommonCenter,
          point3, wz1AxisBox] using hbox (0 : Fin 3)
      · simpa [center, halfWidth, pureWZ2AffineDiagonalCommonCenter,
          point3, wz1AxisBox] using hbox (1 : Fin 3)
      · have hhalf : |point 2 - scale.slopeData.anchor| ≤
            subband.right - subband.left := by
          rw [abs_le]
          constructor <;> linarith [hsubband.1, hsubband.2,
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
    have hbound := pureWZ2_axis_center_coordinate_bound
      band.lemma31.data.cfg.extremal.delta_pos (hsourceLine index)
      center halfWidth point
      ((sourceShading.subset_body index) hpoint) hpointCommonBox
      hheightBound coordinate
    have hcenterHeight : center 2 = scale.slopeData.anchor := hcenterCoords.2.2
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
        |(tubeAxisPointAtHeight (sourceFamily.tube index) scale.slopeData.anchor -
            center) 2| ≤ 2 * (scale.rho / 5000) + 18 * delta +
              scale.rho / 5000 := by
          simpa [halfWidth, point3] using hbound
        _ = 3 * (scale.rho / 5000) + 18 * delta := by ring
        _ ≤ 2 * (scale.rho / 5000) + 18 * delta + 1 / 16 := by
          linarith
  have hsmallAxis : ∀ index coordinate,
      |(tubeAxisPointAtHeight (sourceFamily.tube index)
        scale.slopeData.anchor -
          center) coordinate| ≤ 1 / 15 := by
    intro index coordinate
    have h := haxisCenter index coordinate
    have hrho := band.lemma31.rho_tiny
    have hdelta := band.lemma31.delta_le_rho_sq
    rw [scale.rho_eq] at h
    have hrhoNonneg : 0 ≤ band.lemma31.data.rho.1 := by
      rw [← scale.rho_eq]
      exact scale.rho_pos.le
    nlinarith [sq_nonneg band.lemma31.data.rho.1]
  have hline : WZ1PaperIsLineClass family := by
    intro index
    let sourceTube := sourceFamily.tube index
    let targetTube := family.tube index
    have hverticalAbs : (1 / 2 : ℝ) ≤ |targetTube.direction 2| := by
      exact pureWZ2AffineDiagonalDirection_vertical
        scale.slopeData.frameSlope scale.height_lower
        scale.transverse_pos.le (scale.transverse_le.trans (by norm_num))
        sourceTube.direction_unit (hsourceLine index).vertical
    have htargetVertical : targetTube.direction 2 ≠ 0 := by
      intro hzero
      rw [hzero, abs_zero] at hverticalAbs
      norm_num at hverticalAbs
    have hbaseTwo : targetTube.base 2 = 0 := by
      dsimp only [targetTube, family, sourceTube]
      simp only [pureWZ2AffineDiagonalRawTube]
      rw [pureWZ2AffineDiagonalMapCentered_coord_two]
      rw [hcenterCoords.2.2]
      rw [tubeAxisPointAtHeight_coord_two sourceTube
        (fun hzero => by
          have h := (hsourceLine index).vertical
          rw [hzero, abs_zero] at h
          norm_num at h) scale.slopeData.anchor]
      simp
    have hzero : wz1TubeAxisZeroPoint targetTube = targetTube.base := by
      simp [wz1TubeAxisZeroPoint, hbaseTwo, htargetVertical]
    have hbaseZero : |targetTube.base 0| ≤ 1 / 3 := by
      dsimp only [targetTube, family, sourceTube]
      simp only [pureWZ2AffineDiagonalRawTube]
      rw [pureWZ2AffineDiagonalMapCentered_coord_zero _ _ _ _ _ one_ne_zero]
      rw [hcenterCoords.2.2]
      have hx := hsmallAxis index 0
      have hy := hsmallAxis index 1
      simp only [one_mul]
      rw [abs_div, abs_of_pos (pureWZ2HorizontalNorm_pos _)]
      have h := affineHorizontalFirstBound hframe hx hy (by norm_num)
      exact h.trans (by norm_num)
    have hbaseOne : |targetTube.base 1| ≤ 1 / 3 := by
      dsimp only [targetTube, family, sourceTube]
      simp only [pureWZ2AffineDiagonalRawTube]
      rw [pureWZ2AffineDiagonalMapCentered_coord_one _ _ _ _ _
        htransverse one_ne_zero]
      rw [hcenterCoords.2.2]
      have hx := hsmallAxis index 0
      have hy := hsmallAxis index 1
      simp only [one_mul]
      rw [abs_mul, abs_div, abs_of_pos scale.transverse_pos,
        abs_of_pos (pureWZ2HorizontalNorm_pos _)]
      have h := affineHorizontalSecondBound hframe scale.transverse_pos.le
        (scale.transverse_le.trans (by norm_num)) hx hy (by norm_num)
      have htwo : (2 : ℝ) * (1 / 15) ≤ 1 / 3 := by norm_num
      simpa [PiLp.sub_apply, mul_div_assoc] using h.trans htwo
    unfold WZ1PaperTubeInLineClass
    change WZ1PaperTubeInLineClass targetTube
    refine ⟨?_, ?_, ?_⟩
    · unfold wz1PaperDirection
      split_ifs with horientation
      · exact hverticalAbs.trans_eq (abs_of_nonneg horientation)
      · have hnegative : targetTube.direction 2 < 0 := lt_of_not_ge horientation
        exact hverticalAbs.trans_eq (abs_of_neg hnegative)
    · rw [hzero]
      exact hbaseZero
    · rw [hzero]
      exact hbaseOne
  have haxis : ∀ index, tubeAxisLine (family.tube index) =
      pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
        scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
          tubeAxisLine (sourceFamily.tube index) := by
    intro index
    exact pureWZ2AffineDiagonalRawTube_axis
      scale.slopeData.frameSlope center (sourceFamily.tube index)
      hheight htransverse one_ne_zero
  have haxisAmbient : ∀ index, tubeAxisLine (family.tube index) =
      pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
        scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
          tubeAxisLine
            (band.lemma31.data.cfg.family.tube
              (sourceIndex (supportIndex index))) := by
    intro index
    rw [haxis index]
    congr 1
  have hmidpointLocal : ∀ index,
      ‖wz2PaperTubeMidpoint (family.tube index)‖ ≤ 3 := by
    intro index
    let targetTube := family.tube index
    have hbaseTwo : targetTube.base 2 = 0 := by
      dsimp only [targetTube, family]
      simp only [pureWZ2AffineDiagonalRawTube]
      rw [pureWZ2AffineDiagonalMapCentered_coord_two]
      rw [hcenterCoords.2.2]
      rw [tubeAxisPointAtHeight_coord_two (sourceFamily.tube index)
        (fun hzero => by
          have h := (hsourceLine index).vertical
          rw [hzero, abs_zero] at h
          norm_num at h) scale.slopeData.anchor]
      simp
    have htargetVertical : targetTube.direction 2 ≠ 0 := by
      intro hzero
      have h := (hline index).vertical
      rw [hzero, abs_zero] at h
      norm_num at h
    have hzero : wz1TubeAxisZeroPoint targetTube = targetTube.base := by
      simp [wz1TubeAxisZeroPoint, hbaseTwo, htargetVertical]
    have hx : |targetTube.base 0| ≤ 1 / 3 := by
      rw [← hzero]
      exact (hline index).2.1
    have hy : |targetTube.base 1| ≤ 1 / 3 := by
      rw [← hzero]
      exact (hline index).2.2
    have hxSq : (targetTube.base 0) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
      nlinarith [sq_abs (targetTube.base 0), abs_nonneg (targetTube.base 0)]
    have hySq : (targetTube.base 1) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
      nlinarith [sq_abs (targetTube.base 1), abs_nonneg (targetTube.base 1)]
    have hbaseNorm : ‖targetTube.base‖ ≤ 1 := by
      have hnorm := point3_coord_norm_sq targetTube.base
      have hnormSq : ‖targetTube.base‖ ^ 2 ≤ 1 := by
        rw [hnorm, hbaseTwo]
        nlinarith
      nlinarith [norm_nonneg targetTube.base]
    calc
      ‖wz2PaperTubeMidpoint targetTube‖ =
          ‖targetTube.base + (1 / 2 : ℝ) • targetTube.direction‖ := rfl
      _ ≤ ‖targetTube.base‖ +
          ‖(1 / 2 : ℝ) • targetTube.direction‖ := norm_add_le _ _
      _ = ‖targetTube.base‖ + 1 / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num),
          targetTube.direction_unit]
        ring
      _ ≤ 3 := by linarith
  let targetCarrier : Fin family.card → Set Point3 := fun index =>
    wz1PaperCubicalSaturation scale.targetDelta
      (pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
        scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
          sourceShading.carrier (supportIndex index))
  have hcarrierSubset : ∀ index, targetCarrier index ⊆
      wz1PaperTubeCarrier (family.tube index) := by
    intro index point hpoint
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
      (sourceShading.subset_body (supportIndex index) hsourcePoint).1
    rcases exists_dist_le_of_mem_cthickening_closed
        (isClosed_tubeAxisLine (sourceFamily.tube (supportIndex index)))
        (mul_nonneg (by norm_num) band.lemma31.data.cfg.extremal.delta_pos.le)
        hsourceThick with
      ⟨axisPoint, haxisPoint, haxisDist⟩
    let targetAxisPoint :=
      pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
        scale.slopeData.heightScale scale.slopeData.transverseScale 1 axisPoint
    have htargetAxis : targetAxisPoint ∈ tubeAxisLine (family.tube index) := by
      rw [haxis index]
      exact ⟨axisPoint, haxisPoint, rfl⟩
    have himageDist : dist
        (pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
          scale.slopeData.heightScale scale.slopeData.transverseScale 1
          sourcePoint) targetAxisPoint ≤ 3 * scale.targetDelta := by
      rw [dist_eq_norm]
      have hdiff :
          pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
              scale.slopeData.heightScale scale.slopeData.transverseScale 1
              sourcePoint - targetAxisPoint =
            pureWZ2AffineDiagonalLinear scale.slopeData.frameSlope
              scale.slopeData.heightScale scale.slopeData.transverseScale 1
              (sourcePoint - axisPoint) := by
        dsimp only [targetAxisPoint]
        exact pureWZ2AffineDiagonalMapCentered_sub _ _ _ _ _ _ _
      rw [hdiff]
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
    have htargetDist : dist point targetAxisPoint < 6 * scale.targetDelta := by
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
    constructor
    · exact Metric.mem_cthickening_of_dist_le point targetAxisPoint
        (6 * scale.targetDelta) _ htargetAxis htargetDist.le
    · have hpopular : sourcePoint ∈ popular.popular.restricted.carrier
          (sourceIndex (supportIndex index)) := by
        rw [← popular.source_carrier_eq (supportIndex index)]
        exact hsourcePoint
      rw [popular.popular.restricted_carrier] at hpopular
      rw [popular.popular.box_eq] at hpopular
      have hbox := hpopular.2.1
      have hsubband : sourcePoint ∈ subband.shading.carrier
          (sourceIndex (supportIndex index)) := hpopular.1
      rw [subband.carrier_eq] at hsubband
      have hz : |sourcePoint 2 - scale.slopeData.anchor| ≤
          scale.rho / 5000 := by
        have hhalf : |sourcePoint 2 - scale.slopeData.anchor| ≤
            subband.right - subband.left := by
          rw [abs_le]
          constructor <;> linarith [hsubband.2.1, hsubband.2.2,
            scale.slope_anchor_mem.1, scale.slope_anchor_mem.2]
        rw [subband.length_eq, band.length_eq, ← scale.rho_eq] at hhalf
        convert hhalf using 1 <;> ring
      have hx : |sourcePoint 0 - center 0| ≤ 1 / 16 := by
        convert hbox (0 : Fin 3) using 1 <;>
          simp [center, pureWZ2AffineDiagonalCommonCenter, point3, wz1AxisBox] <;>
          norm_num
      have hy : |sourcePoint 1 - center 1| ≤ 1 / 16 := by
        convert hbox (1 : Fin 3) using 1 <;>
          simp [center, pureWZ2AffineDiagonalCommonCenter, point3, wz1AxisBox] <;>
          norm_num
      let image := pureWZ2AffineDiagonalMapCentered
        scale.slopeData.frameSlope center scale.slopeData.heightScale
        scale.slopeData.transverseScale 1 sourcePoint
      have himage0 : |image 0| ≤ 1 / 8 := by
        rw [pureWZ2AffineDiagonalMapCentered_coord_zero _ _ _ _ _ one_ne_zero]
        simp only [one_mul]
        rw [abs_div, abs_of_pos (pureWZ2HorizontalNorm_pos _)]
        have h := affineHorizontalFirstBound hframe hx hy (by norm_num)
        convert h using 1 <;> norm_num
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
        simp only [one_mul]
        rw [abs_mul, abs_of_pos (by linarith [scale.height_lower] :
          0 < scale.slopeData.heightScale)]
        have hheightNonneg : 0 ≤ scale.slopeData.heightScale := by
          linarith [scale.height_lower]
        have hupperNonneg : 0 ≤ 3000 / scale.rho :=
          div_nonneg (by norm_num) scale.rho_pos.le
        have hzCenter : |sourcePoint 2 - center 2| ≤ scale.rho / 5000 := by
          simpa [center, pureWZ2AffineDiagonalCommonCenter, point3] using hz
        calc
          scale.slopeData.heightScale * |sourcePoint 2 - center 2| ≤
              (3000 / scale.rho) * (scale.rho / 5000) := by
                exact mul_le_mul scale.height_upper hzCenter
                  (abs_nonneg _) hupperNonneg
          _ = 3 / 5 := by field_simp [scale.rho_pos.ne']; ring
      have hcoordClose : ∀ coordinate, |point coordinate - image coordinate| <
          2 * scale.targetDelta := by
        intro coordinate
        calc
          |point coordinate - image coordinate| ≤ dist point image := by
            simpa [Real.dist_eq] using PiLp.dist_apply_le point image coordinate
          _ < 2 * scale.targetDelta := hsameCell
      have hboxTarget :
          |point 0| ≤ 1 ∧ |point 1| ≤ 1 ∧ |point 2| ≤ 1 := by
        constructor
        · have hsum : |point 0| ≤ |point 0 - image 0| + |image 0| := by
            simpa [sub_add_cancel] using abs_add_le (point 0 - image 0) (image 0)
          have hlt : |point 0| < 1 :=
            lt_of_le_of_lt hsum <|
              (add_lt_add_of_lt_of_le (hcoordClose 0) himage0).trans <| by
                linarith [scale.targetDelta_le_tenth]
          exact hlt.le
        constructor
        · have hsum : |point 1| ≤ |point 1 - image 1| + |image 1| := by
            simpa [sub_add_cancel] using abs_add_le (point 1 - image 1) (image 1)
          have hlt : |point 1| < 1 :=
            lt_of_le_of_lt hsum <|
              (add_lt_add_of_lt_of_le (hcoordClose 1) himage1).trans <| by
                linarith [scale.targetDelta_le_tenth]
          exact hlt.le
        · have hsum : |point 2| ≤ |point 2 - image 2| + |image 2| := by
            simpa [sub_add_cancel] using abs_add_le (point 2 - image 2) (image 2)
          have hlt : |point 2| < 1 :=
            lt_of_le_of_lt hsum <|
              (add_lt_add_of_lt_of_le (hcoordClose 2) himage2).trans <| by
                linarith [scale.targetDelta_le_tenth]
          exact hlt.le
      simpa [Kakeya.Streamlined.axisBox] using hboxTarget
  let shading : WZ1PaperTubeShading family :=
    { carrier := targetCarrier
      measurable_carrier := fun index =>
        wz1PaperCubicalSaturation_measurable scale.targetDelta _
      subset_body := hcarrierSubset }
  have hcubical : WZ1PaperIsCubicalShading shading := by
    intro index point hpoint
    exact wz1PaperCubicalSaturation_isCubical
      scale.targetDelta _ point hpoint
  have himageSubset : ∀ index,
      pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
          scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
        sourceShading.carrier (supportIndex index) ⊆
          shading.carrier index := by
    intro index point hpoint
    exact ⟨point, hpoint, rfl⟩
  have hunionSubset :
      pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
          scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
        sourceShading.union ⊆ shading.union := by
    rintro target ⟨source, ⟨index, hsource⟩, rfl⟩
    let targetIndex := supportIndex.symm index
    exact ⟨targetIndex, himageSubset targetIndex <| by
      simpa [targetIndex] using (show _ from ⟨source, hsource, rfl⟩)⟩
  have hmass : ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
      sourceShading.mass ≤ shading.mass := by
    change ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
        (∑ index, volume (sourceShading.carrier index)) ≤
      ∑ index, volume (shading.carrier index)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro index _
    have himageMeasure : volume
          (pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope center
              scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
            sourceShading.carrier (supportIndex index)) ≤
        volume (shading.carrier index) :=
      measure_mono (himageSubset index)
    rw [scale.slopeData.heightScale_eq,
      scale.slopeData.transverseScale_eq] at himageMeasure
    rw [pureWZ2AffineDiagonalMapCentered_volume_image_general
      scale.slopeData.frameSlope center
      scale.slopeData.rotatedSlopeScale_pos
      scale.slopeData.normalizationConstant_pos
      (sourceShading.measurable_carrier (supportIndex index))] at himageMeasure
    simpa only [supportIndex, Equiv.refl_apply] using himageMeasure
  exact ⟨{
    center := center
    center_eq := rfl
    center_height_bound := hcenterHeightBound
    frame_bound := hframe
    family := family
    supportIndex := supportIndex
    sourceParent := fun index => sourceIndex (supportIndex index)
    sourceParent_eq := rfl
    sourceParent_injective :=
      (wz2PaperNonemptyCarrierSubfamily
        popular.popular.restricted).embedding.injective.comp
          supportIndex.injective
    family_tube := fun _ => rfl
    shading := shading
    shading_carrier := fun _ => rfl
    line_class := hline
    midpoint_local := hmidpointLocal
    cubical := hcubical
    axis := haxis
    axis_ambient := haxisAmbient
    exact_image_subset := himageSubset
    union_image_subset := hunionSubset
    mass_lower := hmass
  }⟩

end Kakeya.Assouad

end
