import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.TubeParameters
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralCommonRescalingLineCoverHelpers

/-!
# WZ line distance from vertical-chart tube parameters

The four parameters `(a,b,c,d)` describe the supporting line as
`(a + c z, b + d z, z)`.  On the fixed WZ line class, coordinatewise
closeness of these parameters quantitatively controls the paper line metric.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Coordinatewise width `w` in the four vertical-chart parameters gives paper
line distance at most `6w`.
-/
theorem wz1PaperLineDistance_le_of_tubeParams_close
    {firstScale secondScale width : ℝ}
    {first : Kakeya.DeltaTube firstScale}
    {second : Kakeya.DeltaTube secondScale}
    (firstLine : WZ1PaperTubeInLineClass first)
    (secondLine : WZ1PaperTubeInLineClass second)
    (widthNonnegative : 0 ≤ width)
    (ha :
      |(tubeParamsOfTube first).a -
          (tubeParamsOfTube second).a| ≤ width)
    (hb :
      |(tubeParamsOfTube first).b -
          (tubeParamsOfTube second).b| ≤ width)
    (hc :
      |(tubeParamsOfTube first).c -
          (tubeParamsOfTube second).c| ≤ width)
    (hd :
      |(tubeParamsOfTube first).d -
          (tubeParamsOfTube second).d| ≤ width) :
    wz1PaperLineDistance first second ≤ 6 * width := by
  let firstDirection := wz1PaperDirection first
  let secondDirection := wz1PaperDirection second
  let firstVertical := firstDirection (2 : Fin 3)
  let secondVertical := secondDirection (2 : Fin 3)
  let firstSlope := firstVertical⁻¹ • firstDirection
  let secondSlope := secondVertical⁻¹ • secondDirection
  let firstZero := wz1TubeAxisZeroPoint first
  let secondZero := wz1TubeAxisZeroPoint second
  have firstVerticalPositive : 0 < firstVertical := by
    dsimp only [firstVertical, firstDirection]
    linarith [firstLine.1]
  have secondVerticalPositive : 0 < secondVertical := by
    dsimp only [secondVertical, secondDirection]
    linarith [secondLine.1]
  have firstRawVertical : first.direction (2 : Fin 3) ≠ 0 := by
    intro hzero
    have hvertical := firstLine.vertical
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  have secondRawVertical : second.direction (2 : Fin 3) ≠ 0 := by
    intro hzero
    have hvertical := secondLine.vertical
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  have firstSlopeZero :
      firstSlope (0 : Fin 3) = (tubeParamsOfTube first).c := by
    dsimp only [firstSlope, firstVertical, firstDirection]
    unfold wz1PaperDirection tubeParamsOfTube
    split_ifs with horientation
    · simp only [PiLp.smul_apply, smul_eq_mul]
      field_simp [firstRawVertical]
    · simp only [PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      field_simp [firstRawVertical]
  have firstSlopeOne :
      firstSlope (1 : Fin 3) = (tubeParamsOfTube first).d := by
    dsimp only [firstSlope, firstVertical, firstDirection]
    unfold wz1PaperDirection tubeParamsOfTube
    split_ifs with horientation
    · simp only [PiLp.smul_apply, smul_eq_mul]
      field_simp [firstRawVertical]
    · simp only [PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      field_simp [firstRawVertical]
  have firstSlopeTwo : firstSlope (2 : Fin 3) = 1 := by
    change firstVertical⁻¹ * firstVertical = 1
    exact inv_mul_cancel₀ firstVerticalPositive.ne'
  have secondSlopeZero :
      secondSlope (0 : Fin 3) = (tubeParamsOfTube second).c := by
    dsimp only [secondSlope, secondVertical, secondDirection]
    unfold wz1PaperDirection tubeParamsOfTube
    split_ifs with horientation
    · simp only [PiLp.smul_apply, smul_eq_mul]
      field_simp [secondRawVertical]
    · simp only [PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      field_simp [secondRawVertical]
  have secondSlopeOne :
      secondSlope (1 : Fin 3) = (tubeParamsOfTube second).d := by
    dsimp only [secondSlope, secondVertical, secondDirection]
    unfold wz1PaperDirection tubeParamsOfTube
    split_ifs with horientation
    · simp only [PiLp.smul_apply, smul_eq_mul]
      field_simp [secondRawVertical]
    · simp only [PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      field_simp [secondRawVertical]
  have secondSlopeTwo : secondSlope (2 : Fin 3) = 1 := by
    change secondVertical⁻¹ * secondVertical = 1
    exact inv_mul_cancel₀ secondVerticalPositive.ne'
  have slopeNormBound :
      ‖firstSlope - secondSlope‖ ≤ 2 * width := by
    have hnorm :=
      point3_coord_norm_sq (firstSlope - secondSlope)
    simp only [PiLp.sub_apply] at hnorm
    rw [firstSlopeZero, secondSlopeZero,
      firstSlopeOne, secondSlopeOne,
      firstSlopeTwo, secondSlopeTwo] at hnorm
    have hcBounds :=
      (abs_le.mp hc)
    have hdBounds :=
      (abs_le.mp hd)
    have hnormNonnegative :
        0 ≤ ‖firstSlope - secondSlope‖ :=
      norm_nonneg _
    nlinarith [
      sq_nonneg
        ((tubeParamsOfTube first).c -
          (tubeParamsOfTube second).c),
      sq_nonneg
        ((tubeParamsOfTube first).d -
          (tubeParamsOfTube second).d)]
  have firstSlopeNorm : 1 ≤ ‖firstSlope‖ := by
    have hcoordinate :=
      PiLp.norm_apply_le firstSlope (2 : Fin 3)
    rw [firstSlopeTwo] at hcoordinate
    simpa using hcoordinate
  have secondSlopeNorm : 1 ≤ ‖secondSlope‖ := by
    have hcoordinate :=
      PiLp.norm_apply_le secondSlope (2 : Fin 3)
    rw [secondSlopeTwo] at hcoordinate
    simpa using hcoordinate
  have firstNormalize :
      NormedSpace.normalize firstSlope = firstDirection := by
    dsimp only [firstSlope]
    rw [NormedSpace.normalize_smul_of_pos
      (inv_pos.mpr firstVerticalPositive)]
    exact
      NormedSpace.normalize_eq_self_of_norm_eq_one
        (wz1PaperDirection_norm first)
  have secondNormalize :
      NormedSpace.normalize secondSlope = secondDirection := by
    dsimp only [secondSlope]
    rw [NormedSpace.normalize_smul_of_pos
      (inv_pos.mpr secondVerticalPositive)]
    exact
      NormedSpace.normalize_eq_self_of_norm_eq_one
        (wz1PaperDirection_norm second)
  have directionNormBound :
      ‖firstDirection - secondDirection‖ ≤ 2 * width := by
    rw [← firstNormalize, ← secondNormalize]
    exact
      (norm_normalize_sub_normalize_le_norm_sub
        firstSlopeNorm secondSlopeNorm).trans slopeNormBound
  have angleBound :
      InnerProductGeometry.angle
          firstDirection secondDirection ≤
        4 * width := by
    calc
      InnerProductGeometry.angle firstDirection secondDirection ≤
          (Real.pi / 2) *
            ‖firstDirection - secondDirection‖ :=
        angle_le_pi_div_two_mul_norm_sub
          (wz1PaperDirection_norm first)
          (wz1PaperDirection_norm second)
      _ ≤ 2 * (2 * width) := by
        gcongr
        linarith [Real.pi_lt_four]
      _ = 4 * width := by ring
  have firstZeroZero :
      firstZero (0 : Fin 3) = (tubeParamsOfTube first).a := by
    have h :=
      tubeAxisLine_coord_zero first firstRawVertical
        (wz1TubeAxisZeroPoint_mem_axis first)
    rw [wz1TubeAxisZeroPoint_coord_two first firstLine.vertical,
      mul_zero, add_zero] at h
    exact h
  have firstZeroOne :
      firstZero (1 : Fin 3) = (tubeParamsOfTube first).b := by
    have h :=
      tubeAxisLine_coord_one first firstRawVertical
        (wz1TubeAxisZeroPoint_mem_axis first)
    rw [wz1TubeAxisZeroPoint_coord_two first firstLine.vertical,
      mul_zero, add_zero] at h
    exact h
  have firstZeroTwo : firstZero (2 : Fin 3) = 0 :=
    wz1TubeAxisZeroPoint_coord_two first firstLine.vertical
  have secondZeroZero :
      secondZero (0 : Fin 3) = (tubeParamsOfTube second).a := by
    have h :=
      tubeAxisLine_coord_zero second secondRawVertical
        (wz1TubeAxisZeroPoint_mem_axis second)
    rw [wz1TubeAxisZeroPoint_coord_two second secondLine.vertical,
      mul_zero, add_zero] at h
    exact h
  have secondZeroOne :
      secondZero (1 : Fin 3) = (tubeParamsOfTube second).b := by
    have h :=
      tubeAxisLine_coord_one second secondRawVertical
        (wz1TubeAxisZeroPoint_mem_axis second)
    rw [wz1TubeAxisZeroPoint_coord_two second secondLine.vertical,
      mul_zero, add_zero] at h
    exact h
  have secondZeroTwo : secondZero (2 : Fin 3) = 0 :=
    wz1TubeAxisZeroPoint_coord_two second secondLine.vertical
  have zeroDistanceBound :
      dist firstZero secondZero ≤ 2 * width := by
    rw [dist_eq_norm]
    have hnorm :=
      point3_coord_norm_sq (firstZero - secondZero)
    simp only [PiLp.sub_apply] at hnorm
    rw [firstZeroZero, secondZeroZero,
      firstZeroOne, secondZeroOne,
      firstZeroTwo, secondZeroTwo] at hnorm
    have haBounds := abs_le.mp ha
    have hbBounds := abs_le.mp hb
    have hnormNonnegative :
        0 ≤ ‖firstZero - secondZero‖ :=
      norm_nonneg _
    nlinarith [
      sq_nonneg
        ((tubeParamsOfTube first).a -
          (tubeParamsOfTube second).a),
      sq_nonneg
        ((tubeParamsOfTube first).b -
          (tubeParamsOfTube second).b)]
  change
    dist firstZero secondZero +
        InnerProductGeometry.angle firstDirection secondDirection ≤
      6 * width
  linarith

end Kakeya.Assouad

end
