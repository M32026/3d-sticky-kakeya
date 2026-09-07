import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalIncidence
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHorizontalNormalizationGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6Absorption

/-!
# Actual geometry for the direct half-offset terminal

This file discharges the radius, line-class, carrier, and crop premises of
the literal `(x,z)` terminal.  The reciprocal-grid target radius is reused
from the direct scalar geometry, but the family and shading are the new
fixed-projective half-offset output.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

attribute [local instance] Classical.propDecidable

theorem pureWZ2DirectHalfOffsetTerminalLambda_le_horizontalScale :
    pureWZ2DirectHalfOffsetTerminalLambda ≤ pureWZ2DirectHorizontalScale := by
  change (60600 : ℝ) ≤ max 1
    (max (16 * (lipschitzExtensionConstant Point3 : ℝ) * 145440000)
      1818000000)
  exact (by norm_num : (60600 : ℝ) ≤ 1818000000) |>.trans
    ((le_max_right _ _).trans (le_max_right _ _))

theorem pureWZ2DirectHalfOffsetTerminalLambda_mul_halfWidth :
    pureWZ2DirectHalfOffsetTerminalLambda *
        (pureWZ2DirectHalfOffsetTerminalWidth / 2) = 1 / 200 := by
  norm_num [pureWZ2DirectHalfOffsetTerminalLambda,
    pureWZ2DirectHalfOffsetTerminalWidth, pureWZ2FixedProjectiveNormalLambda]

theorem pureWZ2DirectHalfOffsetTerminalWidth_le_hundredth :
    pureWZ2DirectHalfOffsetTerminalWidth ≤ 1 / 100 := by
  norm_num [pureWZ2DirectHalfOffsetTerminalLambda,
    pureWZ2DirectHalfOffsetTerminalWidth, pureWZ2FixedProjectiveNormalLambda]

theorem pureWZ2DirectHorizontalScale_three_le :
    (3 : ℝ) ≤ pureWZ2DirectHorizontalScale := by
  unfold pureWZ2DirectHorizontalScale pureWZ2DirectFinalGeometryConstant
  exact (by norm_num : (3 : ℝ) ≤ 1818000000) |>.trans
    ((le_max_right _ _).trans (le_max_right _ _))

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

/-- The actual terminal radius is the already aligned reciprocal-grid radius
for the first exact triangular output. -/
abbrev halfOffsetLineClassTargetDelta : ℝ :=
  commonSource.halfOffsetAssembly.directHorizontalTargetScale

theorem halfOffsetLineClassSourceDelta_pos :
    0 < anisotropicPaperAlignedScale delta
      commonSource.halfOffsetAssembly.horizontalSource.c
      commonSource.halfOffsetAssembly.horizontalSource.d := by
  exact commonSource.halfOffsetAssembly.directPreHorizontalScale_pos

theorem halfOffsetLineClassTargetDelta_pos :
    0 < commonSource.halfOffsetLineClassTargetDelta := by
  exact commonSource.halfOffsetAssembly.directHorizontalTargetScale_pos

theorem halfOffsetLineClassTargetDelta_aligned :
    commonSource.halfOffsetLineClassTargetDelta *
        (pureWZ2DirectHorizontalTargetCount
          commonSource.halfOffsetAssembly.directPreHorizontalScale : ℝ) = 1 := by
  exact commonSource.halfOffsetAssembly.directHorizontalTargetScale_aligned

theorem halfOffsetLineClassTargetDelta_small :
    commonSource.halfOffsetLineClassTargetDelta < 1 / 125 := by
  exact commonSource.halfOffsetAssembly.directHorizontalTargetScale_small

/-- Quantitative source-to-target scale provenance for the actual fixed
terminal.  This is the literal combination of the reciprocal-grid rounding,
the first anisotropic radius, and the derivative-subband identity
`rho = delta ^ epsilon / 50`. -/
theorem halfOffsetLineClassTargetDelta_lt_source_power :
    commonSource.halfOffsetLineClassTargetDelta <
      (1280000 * pureWZ2DirectHorizontalScale) *
        Real.rpow delta (1 - epsilon) := by
  have hfirst : commonSource.halfOffsetLineClassTargetDelta <
      8 * pureWZ2DirectHorizontalScale *
        commonSource.halfOffsetAssembly.directPreHorizontalScale := by
    calc
      commonSource.halfOffsetLineClassTargetDelta <
          2 * pureWZ2DirectHorizontalRawTargetScale
            commonSource.halfOffsetAssembly.directPreHorizontalScale :=
        pureWZ2DirectHorizontalTargetScale_lt_two_mul_raw
          commonSource.halfOffsetAssembly.directHorizontalRawTargetScale_pos
          commonSource.halfOffsetAssembly.directHorizontalRawTargetScale_half
      _ = 8 * pureWZ2DirectHorizontalScale *
          commonSource.halfOffsetAssembly.directPreHorizontalScale := by
        unfold pureWZ2DirectHorizontalRawTargetScale
        ring
  have hsecond :
      8 * pureWZ2DirectHorizontalScale *
          commonSource.halfOffsetAssembly.directPreHorizontalScale <
        8 * pureWZ2DirectHorizontalScale *
          (3200 * delta / commonSource.halfOffsetAssembly.rho.1) := by
    exact mul_lt_mul_of_pos_left
      commonSource.halfOffsetAssembly.directPreHorizontalScale_upper
      (mul_pos (by norm_num) pureWZ2DirectHorizontalScale_pos)
  calc
    commonSource.halfOffsetLineClassTargetDelta <
        8 * pureWZ2DirectHorizontalScale *
          commonSource.halfOffsetAssembly.directPreHorizontalScale := hfirst
    _ < 8 * pureWZ2DirectHorizontalScale *
        (3200 * delta / commonSource.halfOffsetAssembly.rho.1) := hsecond
    _ = (1280000 * pureWZ2DirectHorizontalScale) *
        Real.rpow delta (1 - epsilon) := by
      rw [commonSource.halfOffsetAssembly_rho_eq_power_div]
      have hdelta := commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
      have hpow : delta / Real.rpow delta epsilon =
          Real.rpow delta (1 - epsilon) := by
        simpa using (Real.rpow_sub hdelta 1 epsilon).symm
      rw [show 3200 * delta / (Real.rpow delta epsilon / 50) =
          160000 * (delta / Real.rpow delta epsilon) by
        field_simp [Real.rpow_pos_of_pos hdelta epsilon |>.ne']
        ring, hpow]
      ring

/-- A pre-runtime smallness threshold absorbs the fixed terminal dilation
constant and turns the raw estimate above into a clean source-power bound. -/
theorem exists_delta_for_halfOffsetLineClassTargetDelta_power_upper
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ}
        {sigma delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        0 < delta → delta ≤ delta₀ →
        commonSource.halfOffsetLineClassTargetDelta ≤
          Real.rpow delta (1 - 2 * epsilon) := by
  have hgap : 1 - 2 * epsilon < 1 - epsilon := by linarith
  rcases exists_delta_constant_mul_power_le_power
      (ENNReal.ofReal (1280000 * pureWZ2DirectHorizontalScale))
      ENNReal.ofReal_ne_top (1 - 2 * epsilon) (1 - epsilon) hgap with
    ⟨delta₀, hdelta₀Pos, hdelta₀One, habsorb⟩
  refine ⟨delta₀, hdelta₀Pos, hdelta₀One, ?_⟩
  intro logExponent sigma delta commonSource hdelta hdeltaBound
  have hENN := habsorb hdelta hdeltaBound
  have hconstantNonneg :
      0 ≤ 1280000 * pureWZ2DirectHorizontalScale := by
    positivity [pureWZ2DirectHorizontalScale_pos]
  have hreal :
      (1280000 * pureWZ2DirectHorizontalScale) *
          Real.rpow delta (1 - epsilon) ≤
        Real.rpow delta (1 - 2 * epsilon) := by
    rw [Kakeya.realRpowENN, Kakeya.realRpowENN,
      ← ENNReal.ofReal_mul hconstantNonneg] at hENN
    exact (ENNReal.ofReal_le_ofReal_iff
      (Real.rpow_nonneg hdelta.le _)).mp hENN
  exact commonSource.halfOffsetLineClassTargetDelta_lt_source_power.le.trans
    hreal

theorem halfOffsetLineClass_lambda_mul_sourceDelta_le :
    pureWZ2DirectHalfOffsetTerminalLambda *
        commonSource.halfOffsetAssembly.directPreHorizontalScale ≤
      1 / 1000 := by
  calc
    pureWZ2DirectHalfOffsetTerminalLambda *
        commonSource.halfOffsetAssembly.directPreHorizontalScale ≤
      pureWZ2DirectHorizontalScale *
        commonSource.halfOffsetAssembly.directPreHorizontalScale := by
          exact mul_le_mul_of_nonneg_right
            pureWZ2DirectHalfOffsetTerminalLambda_le_horizontalScale
            commonSource.halfOffsetAssembly.directPreHorizontalScale_pos.le
    _ ≤ 1 / 1000 :=
      commonSource.halfOffsetAssembly.directHorizontalScale_mul_pre_le

theorem halfOffsetLineClass_radius_budget :
    pureWZ2DirectHalfOffsetTerminalLambda *
          (6 * commonSource.halfOffsetAssembly.directPreHorizontalScale) +
        2 * commonSource.halfOffsetLineClassTargetDelta ≤
      6 * commonSource.halfOffsetLineClassTargetDelta := by
  have hraw :=
    commonSource.halfOffsetAssembly.directHorizontalRawTargetScale_le_target
  have hsourceNonneg :=
    commonSource.halfOffsetAssembly.directPreHorizontalScale_pos.le
  have htargetNonneg := commonSource.halfOffsetLineClassTargetDelta_pos.le
  have hlambda := pureWZ2DirectHalfOffsetTerminalLambda_le_horizontalScale
  unfold pureWZ2DirectHorizontalRawTargetScale at hraw
  nlinarith

theorem halfOffsetLineClass_incidence_budget :
    delta + (51 / 100 : ℝ) *
        (commonSource.halfOffsetLineClassTargetDelta * Real.sqrt 3) ≤
      commonSource.halfOffsetLineClassTargetDelta := by
  have hdeltaPre :=
    commonSource.halfOffsetAssembly.delta_le_directPreHorizontalScale
  have hraw :=
    commonSource.halfOffsetAssembly.directHorizontalRawTargetScale_le_target
  have hpreNonneg :=
    commonSource.halfOffsetAssembly.directPreHorizontalScale_pos.le
  have hdeltaNonneg := commonSource.halfOffsetAssembly.cfg.extremal.delta_pos.le
  have htargetNonneg := commonSource.halfOffsetLineClassTargetDelta_pos.le
  have hscale := pureWZ2DirectHorizontalScale_three_le
  have hten : 10 * delta ≤ commonSource.halfOffsetLineClassTargetDelta := by
    unfold pureWZ2DirectHorizontalRawTargetScale at hraw
    calc
      10 * delta ≤ 10 *
          commonSource.halfOffsetAssembly.directPreHorizontalScale := by
            gcongr
      _ ≤ 4 * pureWZ2DirectHorizontalScale *
          commonSource.halfOffsetAssembly.directPreHorizontalScale := by
            nlinarith
      _ ≤ commonSource.halfOffsetLineClassTargetDelta := hraw
  have hsqrt : Real.sqrt 3 ≤ 26 / 15 := by
    have hsqrtNonneg := Real.sqrt_nonneg 3
    have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith
  have herror : (51 / 100 : ℝ) *
      (commonSource.halfOffsetLineClassTargetDelta * Real.sqrt 3) ≤
        (221 / 250 : ℝ) * commonSource.halfOffsetLineClassTargetDelta := by
    have hcoefficient : 0 ≤
        (51 / 100 : ℝ) * commonSource.halfOffsetLineClassTargetDelta :=
      mul_nonneg (by norm_num) htargetNonneg
    have hscaled := mul_le_mul_of_nonneg_left hsqrt hcoefficient
    nlinarith
  nlinarith

/-- The first exact triangular map strongly contracts the unselected `y`
coordinate.  Thus the terminal `(x,z)` pigeonhole does not need a third
spatial localization. -/
theorem halfOffsetLineClassTerminalSource_coord_one
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth)
    {point : Point3}
    (hpoint : point ∈
      (commonSource.halfOffsetLineClassTerminalSourceShading retubing box).union) :
    |point 1| ≤ 1 / 50 := by
  have hbox : point ∈ box.restricted.union := by
    rw [← commonSource.halfOffsetLineClassTerminalSourceShading_union
      retubing box]
    exact hpoint
  rcases hbox with ⟨index, hrestricted⟩
  have hraw : point ∈ retubing.raw.exactShading.carrier index :=
    box.restricted_subshading index hrestricted
  rw [retubing.raw.exactShading_carrier] at hraw
  rcases hraw with ⟨sourcePoint, hsourcePoint, rfl⟩
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let ambientIndex : Fin commonSource.halfOffsetAssembly.cfg.family.card :=
    (wz2PaperNonemptyCarrierSubfamily
      retubing.popular.popular.restricted).embedding index
  have hsourceAmbient :
      sourcePoint ∈ source.sourceShading.carrier ambientIndex :=
    retubing.popular.source_subshading index hsourcePoint.1
  have hsourceBody := source.sourceShading.subset_body ambientIndex hsourceAmbient
  have hsourceY : |sourcePoint 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hsourceBody.2.2.1
  have hlengthPos : 0 < source.d - source.c := sub_pos.mpr source.ordered
  have hlengthUpper : source.d - source.c ≤ 1 / 25 := by
    rw [source.length_eq, commonSource.halfOffsetAssembly.horizontalSource_scale]
    linarith [commonSource.halfOffsetAssembly.rho_tiny]
  have hbPos : 0 < source.m * (source.d - source.c) / 2 :=
    div_pos (mul_pos source.slopeScale_pos hlengthPos) (by norm_num)
  have hbUpper : source.m * (source.d - source.c) / 2 ≤ 1 / 50 := by
    have hproduct := mul_le_mul_of_nonneg_right source.slopeScale_le_one
      hlengthPos.le
    nlinarith
  simp only [anisotropicCenteredRescalingMap, anisotropicRescalingMap,
    point3_coord1, PiLp.sub_apply]
  rw [sub_zero, abs_mul, abs_of_pos hbPos]
  calc
    source.m * (source.d - source.c) / 2 * |sourcePoint 1| ≤
        (1 / 50 : ℝ) * 1 := by gcongr
    _ = 1 / 50 := by norm_num

/-- The occupied `(x,z)` source subfamily remains in the line class produced
by the exact triangular retubing. -/
theorem halfOffsetLineClassTerminalSource_line_class
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :
    WZ1PaperIsLineClass
      (wz2PaperNonemptyCarrierSubfamily box.restricted).family :=
  retubing.raw.line_class.subfamily
    (wz2PaperNonemptyCarrierSubfamily box.restricted)

/-- Every tube of the actual fixed-projective terminal family lies in the
paper line class. -/
theorem halfOffsetLineClassTerminalFamily_line_class
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :
    WZ1PaperIsLineClass
      (commonSource.halfOffsetLineClassTerminalFamily retubing box
        commonSource.halfOffsetLineClassTargetDelta) := by
  let sourceDelta := commonSource.halfOffsetAssembly.directPreHorizontalScale
  let lambda := pureWZ2DirectHalfOffsetTerminalLambda
  have hsourceDelta : 0 < sourceDelta :=
    commonSource.halfOffsetLineClassSourceDelta_pos
  have hlambda : 0 < lambda := pureWZ2DirectHalfOffsetTerminalLambda_pos
  have hlambdaOne : 1 ≤ lambda :=
    pureWZ2DirectHalfOffsetTerminalLambda_one_le
  have hscaledSource : lambda * sourceDelta ≤ 1 / 1000 :=
    commonSource.halfOffsetLineClass_lambda_mul_sourceDelta_le
  have hsourceSmall : sourceDelta ≤ 1 / 1000 := by
    calc
      sourceDelta ≤ lambda * sourceDelta := by
        nlinarith [hsourceDelta, hlambdaOne]
      _ ≤ 1 / 1000 := hscaledSource
  intro index
  let source := (wz2PaperNonemptyCarrierSubfamily
    box.restricted).family.tube index
  have hline : WZ1PaperTubeInLineClass source :=
    commonSource.halfOffsetLineClassTerminalSource_line_class retubing box index
  rcases commonSource.halfOffsetLineClassTerminalSourceShading_carrier_nonempty
      retubing box index with ⟨point, hpoint⟩
  have hpointCarrier : point ∈ wz1PaperTubeCarrier source :=
    (commonSource.halfOffsetLineClassTerminalSourceShading retubing box
      |>.subset_body index) hpoint
  have hpointAmbient : point ∈ box.restricted.union := by
    rw [← commonSource.halfOffsetLineClassTerminalSourceShading_union
      retubing box]
    exact ⟨index, hpoint⟩
  rcases hpointAmbient with ⟨ambientIndex, hpointRestricted⟩
  have hpointBox := hpointRestricted
  rw [box.restricted_carrier] at hpointBox
  have hpointBox' := hpointBox.2
  simp only [pureWZ2LineClassSourceBox, Set.mem_inter_iff, wz1AxisBox,
    Set.mem_setOf_eq] at hpointBox'
  have hheight : |box.center 2 - point 2| ≤
      pureWZ2DirectHalfOffsetTerminalWidth / 2 := by
    simpa [point3, abs_sub_comm] using hpointBox'.1 (2 : Fin 3)
  have hpointX : |point 0 - box.center 0| ≤
      pureWZ2DirectHalfOffsetTerminalWidth / 2 := by
    simpa [point3] using hpointBox'.1 (0 : Fin 3)
  have hpointYAbs : |point 1| ≤ 1 / 50 :=
    commonSource.halfOffsetLineClassTerminalSource_coord_one retubing box
      ⟨index, hpoint⟩
  have hpointY : |point 1 - box.center 1| ≤ 1 / 50 := by
    rw [box.center_y, sub_zero]
    exact hpointYAbs
  have haxisX := pureWZ2_paperAxis_center_coordinate_bound_of_point
    hsourceDelta hline box.center point
      (pureWZ2DirectHalfOffsetTerminalWidth / 2)
      (pureWZ2DirectHalfOffsetTerminalWidth / 2) hpointCarrier hheight
      (0 : Fin 3) hpointX
  have haxisY := pureWZ2_paperAxis_center_coordinate_bound_of_point
    hsourceDelta hline box.center point
      (pureWZ2DirectHalfOffsetTerminalWidth / 2) (1 / 50)
      hpointCarrier hheight (1 : Fin 3) hpointY
  apply lineClassNormalizationTube_in_lineClass box.center hlambdaOne source
    hline.vertical
  · simp only [pureWZ2LineClassNormalizationMap, point3_coord0, abs_mul,
      abs_of_pos hlambda]
    calc
      lambda *
          |(tubeAxisPointAtHeight source (box.center 2) - box.center) 0| ≤
        lambda * (2 * (pureWZ2DirectHalfOffsetTerminalWidth / 2) +
          18 * sourceDelta + pureWZ2DirectHalfOffsetTerminalWidth / 2) := by
            exact mul_le_mul_of_nonneg_left haxisX hlambda.le
      _ ≤ 1 / 3 := by
        rw [show lambda *
            (2 * (pureWZ2DirectHalfOffsetTerminalWidth / 2) +
              18 * sourceDelta + pureWZ2DirectHalfOffsetTerminalWidth / 2) =
          3 * (lambda * (pureWZ2DirectHalfOffsetTerminalWidth / 2)) +
            18 * (lambda * sourceDelta) by ring]
        rw [pureWZ2DirectHalfOffsetTerminalLambda_mul_halfWidth]
        nlinarith
  · simpa only [pureWZ2LineClassNormalizationMap, point3_coord1,
      PiLp.sub_apply] using
      (show |(tubeAxisPointAtHeight source (box.center 2) - box.center) 1| ≤
          1 / 3 from haxisY.trans (by
            have hwidth :=
              pureWZ2DirectHalfOffsetTerminalWidth_le_hundredth
            nlinarith))

/-- Every exact point of the actual terminal source has a strict coordinate
margin after the fixed terminal normalization. -/
theorem halfOffsetLineClass_image_coordinate_bound
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth)
    {point : Point3}
    (hpoint : point ∈
      (commonSource.halfOffsetLineClassTerminalSourceShading retubing box).union)
    (coordinate : Fin 3) :
    |pureWZ2LineClassNormalizationMap box.center
        pureWZ2DirectHalfOffsetTerminalLambda point coordinate| ≤ 1 / 50 := by
  have hpointAmbient : point ∈ box.restricted.union := by
    rw [← commonSource.halfOffsetLineClassTerminalSourceShading_union
      retubing box]
    exact hpoint
  rcases hpointAmbient with ⟨ambientIndex, hpointRestricted⟩
  rw [box.restricted_carrier] at hpointRestricted
  have hpointBox := hpointRestricted.2
  simp only [pureWZ2LineClassSourceBox, Set.mem_inter_iff, wz1AxisBox,
    Set.mem_setOf_eq] at hpointBox
  fin_cases coordinate
  · have hx := mul_le_mul_of_nonneg_left
      (by simpa [point3] using hpointBox.1 (0 : Fin 3))
      pureWZ2DirectHalfOffsetTerminalLambda_pos.le
    rw [pureWZ2DirectHalfOffsetTerminalLambda_mul_halfWidth] at hx
    simpa [pureWZ2LineClassNormalizationMap, point3, abs_mul,
      abs_of_pos pureWZ2DirectHalfOffsetTerminalLambda_pos] using
      hx.trans (by norm_num : (1 / 200 : ℝ) ≤ 1 / 50)
  · have hy :=
      commonSource.halfOffsetLineClassTerminalSource_coord_one retubing box
        hpoint
    simpa [pureWZ2LineClassNormalizationMap, point3, box.center_y] using hy
  · have hz := mul_le_mul_of_nonneg_left
      (by simpa [point3] using hpointBox.1 (2 : Fin 3))
      pureWZ2DirectHalfOffsetTerminalLambda_pos.le
    rw [pureWZ2DirectHalfOffsetTerminalLambda_mul_halfWidth] at hz
    simpa [pureWZ2LineClassNormalizationMap, point3, abs_mul,
      abs_of_pos pureWZ2DirectHalfOffsetTerminalLambda_pos] using
      hz.trans (by norm_num : (1 / 200 : ℝ) ≤ 1 / 50)

theorem halfOffsetLineClass_exact_radius_budget :
    pureWZ2DirectHalfOffsetTerminalLambda *
        (6 * commonSource.halfOffsetAssembly.directPreHorizontalScale) ≤
      6 * commonSource.halfOffsetLineClassTargetDelta := by
  have h := commonSource.halfOffsetLineClass_radius_budget
  have htarget := commonSource.halfOffsetLineClassTargetDelta_pos.le
  nlinarith

/-- The literal exact image lies in the full paper carrier of the actual
terminal family. -/
theorem halfOffsetLineClass_exact_carrier
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :
    ∀ index,
      pureWZ2LineClassNormalizationMap box.center
          pureWZ2DirectHalfOffsetTerminalLambda ''
          (commonSource.halfOffsetLineClassTerminalSourceShading retubing box).carrier
            index ⊆
        wz1PaperTubeCarrier
          ((commonSource.halfOffsetLineClassTerminalFamily retubing box
            commonSource.halfOffsetLineClassTargetDelta).tube index) := by
  intro index targetPoint htargetPoint
  constructor
  · apply pureWZ2LineClassNormalizationExactCarrier_subset_cthickening
      box.center pureWZ2DirectHalfOffsetTerminalLambda_one_le
      commonSource.halfOffsetLineClassSourceDelta_pos
      ((wz2PaperNonemptyCarrierSubfamily box.restricted).family.tube index)
      commonSource.halfOffsetLineClass_exact_radius_budget
    rcases htargetPoint with ⟨sourcePoint, hsourcePoint, rfl⟩
    exact ⟨sourcePoint,
      (commonSource.halfOffsetLineClassTerminalSourceShading retubing box
        |>.subset_body index) hsourcePoint, rfl⟩
  · rcases htargetPoint with ⟨sourcePoint, hsourcePoint, rfl⟩
    have himage := commonSource.halfOffsetLineClass_image_coordinate_bound
      retubing box (show sourcePoint ∈
        (commonSource.halfOffsetLineClassTerminalSourceShading retubing box).union
        from ⟨index, hsourcePoint⟩)
    simpa [Kakeya.Streamlined.axisBox] using
      (show
        |pureWZ2LineClassNormalizationMap box.center
            pureWZ2DirectHalfOffsetTerminalLambda sourcePoint 0| ≤ 1 ∧
          |pureWZ2LineClassNormalizationMap box.center
            pureWZ2DirectHalfOffsetTerminalLambda sourcePoint 1| ≤ 1 ∧
          |pureWZ2LineClassNormalizationMap box.center
            pureWZ2DirectHalfOffsetTerminalLambda sourcePoint 2| ≤ 1 from
        ⟨(himage 0).trans (by norm_num),
          (himage 1).trans (by norm_num),
          (himage 2).trans (by norm_num)⟩)

/-- Reciprocal-grid saturation of the actual terminal exact image remains in
the paper crop. -/
theorem halfOffsetLineClass_cubical_crop
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :
    ∀ index,
      wz1PaperCubicalSaturation commonSource.halfOffsetLineClassTargetDelta
          (pureWZ2LineClassNormalizationMap box.center
            pureWZ2DirectHalfOffsetTerminalLambda ''
            (commonSource.halfOffsetLineClassTerminalSourceShading retubing box).carrier
              index) ⊆
        Kakeya.Streamlined.axisBox 2 2 2 := by
  have hcountPos : 0 < pureWZ2DirectHorizontalTargetCount
      commonSource.halfOffsetAssembly.directPreHorizontalScale :=
    pureWZ2DirectHorizontalTargetCount_pos
      commonSource.halfOffsetAssembly.directHorizontalRawTargetScale_pos
      commonSource.halfOffsetAssembly.directHorizontalRawTargetScale_half
  intro index
  apply anisotropicPaperCubicalSaturation_subset_axisBox
    commonSource.halfOffsetLineClassTargetDelta_pos hcountPos
    commonSource.halfOffsetLineClassTargetDelta_aligned
  intro imagePoint himagePoint coordinate
  rcases himagePoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  have hbound := commonSource.halfOffsetLineClass_image_coordinate_bound
    retubing box (show sourcePoint ∈
      (commonSource.halfOffsetLineClassTerminalSourceShading retubing box).union
      from ⟨index, hsourcePoint⟩) coordinate
  rcases abs_le.mp hbound with ⟨hlower, hupper⟩
  constructor <;> nlinarith

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
