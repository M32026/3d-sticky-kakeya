import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryLineConflictPacking
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryRescaledLocality

/-!
# Locality of ordinary rescaling from bounded source bases

The frozen normalization records bounded ordinary basepoints rather than the
stronger full-carrier unit-ball condition.  Strict source-to-anchor line
cover controls the transverse axis-zero displacement, while the bounded base
controls the source midpoint's longitudinal parameter.  The literal
anisotropic map therefore sends the source midpoint into the fixed radius
three window.
-/

noncomputable section

namespace Kakeya.Assouad

private theorem boundedBase_midpoint_axial_decomposition
    {delta : ℝ}
    (source : Kakeya.DeltaTube delta)
    (sourceLine : WZ1PaperTubeInLineClass source)
    (sourceBase : ‖source.base‖ ≤ 4) :
    ∃ axial : ℝ,
      |axial| ≤ 6 ∧
        wz2PaperTubeMidpoint source =
          wz1TubeAxisZeroPoint source +
            axial • wz1PaperDirection source := by
  let axial := pureWZ2OrdinaryAxialParameter source sourceLine
  exact
    ⟨axial,
      pureWZ2OrdinaryAxialParameter_abs_le_six
        sourceLine sourceBase,
      pureWZ2OrdinaryAxialParameter_spec source sourceLine⟩

private theorem covered_axisZero_image_norm_le
    {delta rho : ℝ}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (covered : WZ1PaperTubeCovers source anchor) :
    ‖wz2PaperLiteralUnitRescalingLinear anchor
        (wz1TubeAxisZeroPoint source -
          wz1TubeAxisZeroPoint anchor)‖ ≤
      1 / 200 := by
  have zeroDistance :
      ‖wz1TubeAxisZeroPoint source -
          wz1TubeAxisZeroPoint anchor‖ ≤
        rho / 2 := by
    simpa [dist_eq_norm] using covered.components.1
  calc
    ‖wz2PaperLiteralUnitRescalingLinear anchor
        (wz1TubeAxisZeroPoint source -
          wz1TubeAxisZeroPoint anchor)‖ ≤
        ‖wz1TubeAxisZeroPoint source -
            wz1TubeAxisZeroPoint anchor‖ / (100 * rho) :=
      wz2PaperLiteralUnitRescalingLinear_norm_le
        anchor hrho hrhoOne _
    _ ≤ (rho / 2) / (100 * rho) := by
      gcongr
    _ = 1 / 200 := by
      field_simp [hrho.ne']
      ring

private theorem literalOrdinaryRescaled_midpoint_eq_map
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    wz2PaperTubeMidpoint
        (wz2PaperLiteralOrdinaryRescaledTube source anchor hrho) =
      wz2PaperLiteralUnitRescalingMap anchor hrho
        (wz2PaperTubeMidpoint source) := by
  dsimp only [wz2PaperTubeMidpoint,
    wz2PaperLiteralOrdinaryRescaledTube]
  module

private theorem literalMap_midpoint_decomposition
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (axial : ℝ)
    (sourceMidpoint :
      wz2PaperTubeMidpoint source =
        wz1TubeAxisZeroPoint source +
          axial • wz1PaperDirection source) :
    wz2PaperLiteralUnitRescalingMap anchor hrho
        (wz2PaperTubeMidpoint source) =
      wz2PaperLiteralUnitRescalingLinear anchor
          (wz1TubeAxisZeroPoint source -
            wz1TubeAxisZeroPoint anchor) +
        axial •
          wz2PaperLiteralUnitRescalingLinear anchor
            (wz1PaperDirection source) := by
  have anchorZeroMap :
      wz2PaperLiteralUnitRescalingMap anchor hrho
          (wz1TubeAxisZeroPoint anchor) =
        0 := by
    simp [wz2PaperLiteralUnitRescalingMap, unitRescalingMap]
  have mapMidpoint :
      wz2PaperLiteralUnitRescalingMap anchor hrho
          (wz2PaperTubeMidpoint source) =
        wz2PaperLiteralUnitRescalingLinear anchor
          (wz2PaperTubeMidpoint source -
            wz1TubeAxisZeroPoint anchor) := by
    have difference :=
      wz2PaperLiteralUnitRescalingMap_sub
        anchor hrho (wz2PaperTubeMidpoint source)
          (wz1TubeAxisZeroPoint anchor)
    rw [anchorZeroMap, sub_zero] at difference
    exact difference
  have decomposition :
      wz2PaperTubeMidpoint source -
          wz1TubeAxisZeroPoint anchor =
        (wz1TubeAxisZeroPoint source -
          wz1TubeAxisZeroPoint anchor) +
          axial • wz1PaperDirection source := by
    rw [sourceMidpoint]
    abel
  rw [mapMidpoint, decomposition, map_add, map_smul]

private theorem norm_add_smul_le_three
    (first second : Point3)
    (coefficient : ℝ)
    (firstBound : ‖first‖ ≤ 1 / 200)
    (coefficientBound : |coefficient| ≤ 6)
    (secondBound : ‖second‖ ≤ 3 / 200) :
    ‖first + coefficient • second‖ ≤ 3 := by
  calc
    ‖first + coefficient • second‖ ≤
        ‖first‖ + ‖coefficient • second‖ :=
      norm_add_le _ _
    _ = ‖first‖ + |coefficient| * ‖second‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 / 200 + 6 * (3 / 200) := by
      gcongr
    _ ≤ 3 := by norm_num

private theorem norm_le_three_of_eq_add_smul
    (point first second : Point3)
    (coefficient : ℝ)
    (pointEq : point = first + coefficient • second)
    (firstBound : ‖first‖ ≤ 1 / 200)
    (coefficientBound : |coefficient| ≤ 6)
    (secondBound : ‖second‖ ≤ 3 / 200) :
    ‖point‖ ≤ 3 := by
  rw [pointEq]
  exact
    norm_add_smul_le_three
      first second coefficient
      firstBound coefficientBound secondBound

private theorem literalPaperDirection_norm_le
    {delta rho : ℝ}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (covered : WZ1PaperTubeCovers source anchor) :
    ‖wz2PaperLiteralUnitRescalingLinear anchor
        (wz1PaperDirection source)‖ ≤
      3 / 200 := by
  have stored :
      ‖wz2PaperLiteralUnitRescalingLinear anchor source.direction‖ ≤
        3 / 200 :=
    wz2PaperLiteralUnitRescalingLinear_sourceDirection_norm_le
      hrho hrhoOne covered
  unfold wz1PaperDirection
  split_ifs
  · exact stored
  · simpa using stored

private theorem literalLinear_axial_norm_le_three
    {delta rho : ℝ}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (axial : ℝ)
    (axialBound : |axial| ≤ 6)
    (covered : WZ1PaperTubeCovers source anchor) :
    ‖wz2PaperLiteralUnitRescalingLinear anchor
          (wz1TubeAxisZeroPoint source -
            wz1TubeAxisZeroPoint anchor) +
        axial •
          wz2PaperLiteralUnitRescalingLinear anchor
            (wz1PaperDirection source)‖ ≤
      3 := by
  apply
    norm_add_smul_le_three
      (wz2PaperLiteralUnitRescalingLinear anchor
        (wz1TubeAxisZeroPoint source -
          wz1TubeAxisZeroPoint anchor))
      (wz2PaperLiteralUnitRescalingLinear anchor
        (wz1PaperDirection source))
      axial
  · exact
      covered_axisZero_image_norm_le
        (hrho := hrho) (hrhoOne := hrhoOne)
        (source := source) (anchor := anchor) covered
  · exact axialBound
  · exact
      literalPaperDirection_norm_le
        hrho hrhoOne source anchor covered

private theorem literalMap_sourceMidpoint_norm_le_three_of_axial
    {delta rho : ℝ}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (axial : ℝ)
    (axialBound : |axial| ≤ 6)
    (sourceMidpoint :
      wz2PaperTubeMidpoint source =
        wz1TubeAxisZeroPoint source +
          axial • wz1PaperDirection source)
    (covered : WZ1PaperTubeCovers source anchor) :
    ‖wz2PaperLiteralUnitRescalingMap anchor hrho
        (wz2PaperTubeMidpoint source)‖ ≤
      3 := by
  rw [literalMap_midpoint_decomposition
    (source := source) (anchor := anchor)
    (hrho := hrho) axial sourceMidpoint]
  exact
    literalLinear_axial_norm_le_three
      hrho hrhoOne source anchor axial axialBound covered

theorem wz2PaperLiteralOrdinaryRescaledTube_midpoint_norm_le_three_of_boundedBase
    {delta rho : ℝ}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (sourceLine : WZ1PaperTubeInLineClass source)
    (sourceBase : ‖source.base‖ ≤ 4)
    (covered : WZ1PaperTubeCovers source anchor) :
    ‖wz2PaperTubeMidpoint
        (wz2PaperLiteralOrdinaryRescaledTube source anchor hrho)‖ ≤
      3 := by
  let axial := pureWZ2OrdinaryAxialParameter source sourceLine
  rw [literalOrdinaryRescaled_midpoint_eq_map source anchor hrho]
  exact
    literalMap_sourceMidpoint_norm_le_three_of_axial
      (hrho := hrho) (hrhoOne := hrhoOne)
      (source := source) (anchor := anchor) axial
      (pureWZ2OrdinaryAxialParameter_abs_le_six
        sourceLine sourceBase)
      (pureWZ2OrdinaryAxialParameter_spec source sourceLine)
      covered

end Kakeya.Assouad

end
