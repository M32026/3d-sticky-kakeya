import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62InsertedCWACore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.TubeParameterLineDistance
import Mathlib.Data.ZMod.Basic

/-!
# Proposition 6.2 metric parents: four-dimensional line mesh

The mesh is the literal `(a,b,c,d)` chart of affine lines in the fixed
vertical class.  Equal cells have paper line distance at most six cell widths.
Equal residue colors and distinct cells force one parameter difference to be
large, hence force line separation.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

def pureWZ2Prop62TubeParameterCoordinate
    (params : TubeParams) (coordinate : Fin 4) : ℝ :=
  match coordinate with
  | ⟨0, _⟩ => params.a
  | ⟨1, _⟩ => params.b
  | ⟨2, _⟩ => params.c
  | ⟨3, _⟩ => params.d

def pureWZ2Prop62LineCell
    {scale : ℝ}
    (width : ℝ)
    (tube : Kakeya.DeltaTube scale) :
    Fin 4 → ℤ :=
  fun coordinate =>
    ⌊pureWZ2Prop62TubeParameterCoordinate
        (tubeParamsOfTube tube) coordinate / width⌋

def pureWZ2Prop62LineColor
    {scale : ℝ}
    (width : ℝ)
    (stride : ℕ)
    (tube : Kakeya.DeltaTube scale) :
    Fin 4 → ZMod stride :=
  fun coordinate =>
    (pureWZ2Prop62LineCell width tube coordinate :
      ZMod stride)

private theorem pureWZ2Prop62_sameFloor_abs_sub_lt
    {first second width : ℝ}
    (widthPos : 0 < width)
    (sameFloor : ⌊first / width⌋ = ⌊second / width⌋) :
    |first - second| < width := by
  have firstLower :
      (⌊first / width⌋ : ℝ) ≤ first / width :=
    Int.floor_le _
  have firstUpper :
      first / width < (⌊first / width⌋ : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have secondLower :
      (⌊first / width⌋ : ℝ) ≤ second / width := by
    rw [sameFloor]
    exact Int.floor_le _
  have secondUpper :
      second / width < (⌊first / width⌋ : ℝ) + 1 := by
    rw [sameFloor]
    exact Int.lt_floor_add_one _
  have quotientBound :
      |(first - second) / width| < 1 := by
    rw [abs_lt]
    constructor <;>
      rw [sub_div] <;>
      linarith
  rw [abs_div, abs_of_pos widthPos] at quotientBound
  have := (div_lt_iff₀ widthPos).mp quotientBound
  simpa using this

theorem pureWZ2_prop62_sameLineCell_lineDistance_le
    {firstScale secondScale width : ℝ}
    (widthPos : 0 < width)
    (first : Kakeya.DeltaTube firstScale)
    (second : Kakeya.DeltaTube secondScale)
    (firstLine : WZ1PaperTubeInLineClass first)
    (secondLine : WZ1PaperTubeInLineClass second)
    (sameCell :
      pureWZ2Prop62LineCell width first =
        pureWZ2Prop62LineCell width second) :
    wz1PaperLineDistance first second ≤ 6 * width := by
  have coordinateClose :
      ∀ coordinate : Fin 4,
        |pureWZ2Prop62TubeParameterCoordinate
            (tubeParamsOfTube first) coordinate -
          pureWZ2Prop62TubeParameterCoordinate
            (tubeParamsOfTube second) coordinate| ≤ width := by
    intro coordinate
    exact le_of_lt <|
      pureWZ2Prop62_sameFloor_abs_sub_lt
        widthPos (congrFun sameCell coordinate)
  exact
    wz1PaperLineDistance_le_of_tubeParams_close
      firstLine secondLine widthPos.le
      (coordinateClose ⟨0, by omega⟩)
      (coordinateClose ⟨1, by omega⟩)
      (coordinateClose ⟨2, by omega⟩)
      (coordinateClose ⟨3, by omega⟩)

private theorem tubeParams_a_eq_axisZero
    {scale : ℝ}
    (tube : Kakeya.DeltaTube scale)
    (line : WZ1PaperTubeInLineClass tube) :
    (tubeParamsOfTube tube).a =
      wz1TubeAxisZeroPoint tube 0 := by
  have vertical : tube.direction (2 : Fin 3) ≠ 0 := by
    intro hzero
    have := line.vertical
    rw [hzero, abs_zero] at this
    norm_num at this
  unfold tubeParamsOfTube wz1TubeAxisZeroPoint
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp [vertical]

private theorem tubeParams_b_eq_axisZero
    {scale : ℝ}
    (tube : Kakeya.DeltaTube scale)
    (line : WZ1PaperTubeInLineClass tube) :
    (tubeParamsOfTube tube).b =
      wz1TubeAxisZeroPoint tube 1 := by
  have vertical : tube.direction (2 : Fin 3) ≠ 0 := by
    intro hzero
    have := line.vertical
    rw [hzero, abs_zero] at this
    norm_num at this
  unfold tubeParamsOfTube wz1TubeAxisZeroPoint
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp [vertical]

private theorem tubeParams_c_eq_paperSlope
    {scale : ℝ}
    (tube : Kakeya.DeltaTube scale) :
    (tubeParamsOfTube tube).c =
      wz1PaperDirection tube 0 /
        wz1PaperDirection tube 2 := by
  unfold tubeParamsOfTube wz1PaperDirection
  split_ifs <;> simp

private theorem tubeParams_d_eq_paperSlope
    {scale : ℝ}
    (tube : Kakeya.DeltaTube scale) :
    (tubeParamsOfTube tube).d =
      wz1PaperDirection tube 1 /
        wz1PaperDirection tube 2 := by
  unfold tubeParamsOfTube wz1PaperDirection
  split_ifs <;> simp

private theorem slope_difference_le_six
    {first second : Point3}
    (firstNorm : ‖first‖ = 1)
    (secondNorm : ‖second‖ = 1)
    (firstVertical : 1 / 2 ≤ first 2)
    (secondVertical : 1 / 2 ≤ second 2)
    (coordinate : Fin 3) :
    |first coordinate / first 2 -
        second coordinate / second 2| ≤
      6 * ‖first - second‖ := by
  have firstVerticalPos : 0 < first 2 := by linarith
  have secondVerticalPos : 0 < second 2 := by linarith
  have firstVerticalLe : first 2 ≤ 1 := by
    have h := PiLp.norm_apply_le first 2
    simpa [firstNorm, Real.norm_eq_abs,
      abs_of_pos firstVerticalPos] using h
  have secondVerticalLe : second 2 ≤ 1 := by
    have h := PiLp.norm_apply_le second 2
    simpa [secondNorm, Real.norm_eq_abs,
      abs_of_pos secondVerticalPos] using h
  have firstCoordinate :
      |first coordinate| ≤ 1 := by
    have h := PiLp.norm_apply_le first coordinate
    simpa [firstNorm, Real.norm_eq_abs] using h
  have secondCoordinate :
      |second coordinate| ≤ 1 := by
    have h := PiLp.norm_apply_le second coordinate
    simpa [secondNorm, Real.norm_eq_abs] using h
  have coordinateDifference :
      |first coordinate - second coordinate| ≤
        ‖first - second‖ := by
    simpa [Real.norm_eq_abs] using
      PiLp.norm_apply_le (first - second) coordinate
  have verticalDifference :
      |first 2 - second 2| ≤ ‖first - second‖ := by
    simpa [Real.norm_eq_abs] using
      PiLp.norm_apply_le (first - second) 2
  have algebra :
      first coordinate / first 2 -
          second coordinate / second 2 =
        (first coordinate - second coordinate) / first 2 +
          second coordinate *
            (second 2 - first 2) /
              (first 2 * second 2) := by
    field_simp [firstVerticalPos.ne', secondVerticalPos.ne']
    ring
  have normNonnegative : 0 ≤ ‖first - second‖ :=
    norm_nonneg _
  have firstTerm :
      |first coordinate - second coordinate| / first 2 ≤
        2 * ‖first - second‖ := by
    calc
      |first coordinate - second coordinate| / first 2 ≤
          ‖first - second‖ / first 2 :=
        div_le_div_of_nonneg_right
          coordinateDifference firstVerticalPos.le
      _ ≤ 2 * ‖first - second‖ := by
        apply (div_le_iff₀ firstVerticalPos).2
        nlinarith
  have numeratorBound :
      |second coordinate| * |second 2 - first 2| ≤
        ‖first - second‖ := by
    calc
      |second coordinate| * |second 2 - first 2| ≤
          1 * ‖first - second‖ := by
        gcongr
        simpa [abs_sub_comm] using verticalDifference
      _ = ‖first - second‖ := one_mul _
  have denominatorLower :
      (1 / 4 : ℝ) ≤ first 2 * second 2 := by
    nlinarith [
      mul_nonneg
        (sub_nonneg.mpr firstVertical)
        (sub_nonneg.mpr secondVertical)]
  have secondTerm :
      |second coordinate| * |second 2 - first 2| /
          (first 2 * second 2) ≤
        4 * ‖first - second‖ := by
    have denominatorPos :
        0 < first 2 * second 2 :=
      mul_pos firstVerticalPos secondVerticalPos
    calc
      |second coordinate| * |second 2 - first 2| /
            (first 2 * second 2) ≤
          ‖first - second‖ / (first 2 * second 2) :=
        div_le_div_of_nonneg_right
          numeratorBound denominatorPos.le
      _ ≤ 4 * ‖first - second‖ := by
        apply (div_le_iff₀ denominatorPos).2
        nlinarith
  rw [algebra]
  calc
    |(first coordinate - second coordinate) / first 2 +
        second coordinate * (second 2 - first 2) /
          (first 2 * second 2)| ≤
      |(first coordinate - second coordinate) / first 2| +
        |second coordinate * (second 2 - first 2) /
          (first 2 * second 2)| := abs_add_le _ _
    _ =
      |first coordinate - second coordinate| / first 2 +
        |second coordinate| *
          |second 2 - first 2| /
            (first 2 * second 2) := by
      rw [abs_div, abs_div, abs_mul, abs_mul]
      rw [abs_of_pos firstVerticalPos,
        abs_of_pos secondVerticalPos]
    _ ≤
      2 * ‖first - second‖ +
        4 * ‖first - second‖ :=
      add_le_add firstTerm secondTerm
    _ = 6 * ‖first - second‖ := by ring

theorem pureWZ2_prop62_tubeParameterCoordinate_le_lineDistance
    {firstScale secondScale : ℝ}
    (first : Kakeya.DeltaTube firstScale)
    (second : Kakeya.DeltaTube secondScale)
    (firstLine : WZ1PaperTubeInLineClass first)
    (secondLine : WZ1PaperTubeInLineClass second)
    (coordinate : Fin 4) :
    |pureWZ2Prop62TubeParameterCoordinate
        (tubeParamsOfTube first) coordinate -
      pureWZ2Prop62TubeParameterCoordinate
        (tubeParamsOfTube second) coordinate| ≤
      6 * wz1PaperLineDistance first second := by
  fin_cases coordinate
  · dsimp only [pureWZ2Prop62TubeParameterCoordinate]
    rw [tubeParams_a_eq_axisZero first firstLine,
      tubeParams_a_eq_axisZero second secondLine]
    have h :=
      PiLp.dist_apply_le
        (wz1TubeAxisZeroPoint first)
        (wz1TubeAxisZeroPoint second) 0
    rw [Real.dist_eq] at h
    calc
      |(wz1TubeAxisZeroPoint first).ofLp 0 -
          (wz1TubeAxisZeroPoint second).ofLp 0| ≤
          dist (wz1TubeAxisZeroPoint first)
            (wz1TubeAxisZeroPoint second) := h
      _ ≤
          wz1PaperLineDistance first second := by
        unfold wz1PaperLineDistance
        exact le_add_of_nonneg_right
          (InnerProductGeometry.angle_nonneg _ _)
      _ ≤ 6 * wz1PaperLineDistance first second := by
        have hnonnegative :
            0 ≤ wz1PaperLineDistance first second := by
          unfold wz1PaperLineDistance
          exact add_nonneg dist_nonneg
            (InnerProductGeometry.angle_nonneg _ _)
        nlinarith
  · dsimp only [pureWZ2Prop62TubeParameterCoordinate]
    rw [tubeParams_b_eq_axisZero first firstLine,
      tubeParams_b_eq_axisZero second secondLine]
    have h :=
      PiLp.dist_apply_le
        (wz1TubeAxisZeroPoint first)
        (wz1TubeAxisZeroPoint second) 1
    rw [Real.dist_eq] at h
    calc
      |(wz1TubeAxisZeroPoint first).ofLp 1 -
          (wz1TubeAxisZeroPoint second).ofLp 1| ≤
          dist (wz1TubeAxisZeroPoint first)
            (wz1TubeAxisZeroPoint second) := h
      _ ≤
          wz1PaperLineDistance first second := by
        unfold wz1PaperLineDistance
        exact le_add_of_nonneg_right
          (InnerProductGeometry.angle_nonneg _ _)
      _ ≤ 6 * wz1PaperLineDistance first second := by
        have hnonnegative :
            0 ≤ wz1PaperLineDistance first second := by
          unfold wz1PaperLineDistance
          exact add_nonneg dist_nonneg
            (InnerProductGeometry.angle_nonneg _ _)
        nlinarith
  · dsimp only [pureWZ2Prop62TubeParameterCoordinate]
    rw [tubeParams_c_eq_paperSlope first,
      tubeParams_c_eq_paperSlope second]
    have h :=
      slope_difference_le_six
        (wz1PaperDirection_norm first)
        (wz1PaperDirection_norm second)
        firstLine.1 secondLine.1 (0 : Fin 3)
    have chord :=
      unit_norm_sub_le_angle
        (wz1PaperDirection_norm first)
        (wz1PaperDirection_norm second)
    calc
      |wz1PaperDirection first 0 /
            wz1PaperDirection first 2 -
          wz1PaperDirection second 0 /
            wz1PaperDirection second 2| ≤
          6 *
            ‖wz1PaperDirection first -
              wz1PaperDirection second‖ := h
      _ ≤
          6 *
            InnerProductGeometry.angle
              (wz1PaperDirection first)
              (wz1PaperDirection second) := by
        gcongr
      _ ≤ 6 * wz1PaperLineDistance first second := by
        unfold wz1PaperLineDistance
        gcongr
        exact le_add_of_nonneg_left dist_nonneg
  · dsimp only [pureWZ2Prop62TubeParameterCoordinate]
    rw [tubeParams_d_eq_paperSlope first,
      tubeParams_d_eq_paperSlope second]
    have h :=
      slope_difference_le_six
        (wz1PaperDirection_norm first)
        (wz1PaperDirection_norm second)
        firstLine.1 secondLine.1 (1 : Fin 3)
    have chord :=
      unit_norm_sub_le_angle
        (wz1PaperDirection_norm first)
        (wz1PaperDirection_norm second)
    calc
      |wz1PaperDirection first 1 /
            wz1PaperDirection first 2 -
          wz1PaperDirection second 1 /
            wz1PaperDirection second 2| ≤
          6 *
            ‖wz1PaperDirection first -
              wz1PaperDirection second‖ := h
      _ ≤
          6 *
            InnerProductGeometry.angle
              (wz1PaperDirection first)
              (wz1PaperDirection second) := by
        gcongr
      _ ≤ 6 * wz1PaperLineDistance first second := by
        unfold wz1PaperLineDistance
        gcongr
        exact le_add_of_nonneg_left dist_nonneg

private theorem pureWZ2Prop62_floor_sameResidue_separated
    {first second width : ℝ}
    {stride : ℕ}
    (widthPos : 0 < width)
    (sameResidue :
      (⌊first / width⌋ : ZMod stride) =
        (⌊second / width⌋ : ZMod stride))
    (differentFloor :
      ⌊first / width⌋ ≠ ⌊second / width⌋) :
    ((stride : ℝ) - 1) * width < |first - second| := by
  let firstFloor : ℤ := ⌊first / width⌋
  let secondFloor : ℤ := ⌊second / width⌋
  have divisible :
      (stride : ℤ) ∣ secondFloor - firstFloor :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub
      firstFloor secondFloor stride).mp sameResidue
  have differenceNonzero :
      secondFloor - firstFloor ≠ 0 :=
    sub_ne_zero.mpr fun equality =>
      differentFloor equality.symm
  have floorDifference :
      stride ≤ (secondFloor - firstFloor).natAbs :=
    Int.natAbs_le_of_dvd_ne_zero divisible differenceNonzero
  have firstLower :
      (firstFloor : ℝ) ≤ first / width :=
    Int.floor_le _
  have firstUpper :
      first / width < (firstFloor : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have secondLower :
      (secondFloor : ℝ) ≤ second / width :=
    Int.floor_le _
  have secondUpper :
      second / width < (secondFloor : ℝ) + 1 :=
    Int.lt_floor_add_one _
  by_cases horder : firstFloor ≤ secondFloor
  · have differenceNonnegative :
        0 ≤ secondFloor - firstFloor := sub_nonneg.mpr horder
    have castDifference :
        (stride : ℝ) ≤
          (secondFloor : ℝ) - (firstFloor : ℝ) := by
      have hint :
          (stride : ℤ) ≤ secondFloor - firstFloor := by
        rw [← Int.natAbs_of_nonneg differenceNonnegative]
        exact_mod_cast floorDifference
      exact_mod_cast hint
    have quotient :
        (stride : ℝ) - 1 <
          (second - first) / width := by
      rw [sub_div]
      linarith
    have realDifference :
        ((stride : ℝ) - 1) * width <
          second - first :=
      (lt_div_iff₀ widthPos).mp <| by
        simpa [sub_div] using quotient
    calc
      ((stride : ℝ) - 1) * width <
          second - first := realDifference
      _ ≤ |second - first| := le_abs_self _
      _ = |first - second| := abs_sub_comm _ _
  · have horder' : secondFloor ≤ firstFloor := by
      omega
    have differenceNonpositive :
        secondFloor - firstFloor ≤ 0 := sub_nonpos.mpr horder'
    have castDifference :
        (stride : ℝ) ≤
          (firstFloor : ℝ) - (secondFloor : ℝ) := by
      have divisible' :
          (stride : ℤ) ∣ firstFloor - secondFloor := by
        have := dvd_neg.mpr divisible
        simpa only [neg_sub] using this
      have differenceNonzero' :
          firstFloor - secondFloor ≠ 0 := by
        exact sub_ne_zero.mpr differentFloor
      have hnat :
          stride ≤ Int.natAbs (firstFloor - secondFloor) :=
        Int.natAbs_le_of_dvd_ne_zero
          divisible' differenceNonzero'
      have differenceNonnegative' :
          0 ≤ firstFloor - secondFloor :=
        sub_nonneg.mpr horder'
      have hint :
          (stride : ℤ) ≤ firstFloor - secondFloor := by
        rw [← Int.natAbs_of_nonneg differenceNonnegative']
        exact_mod_cast hnat
      exact_mod_cast hint
    have quotient :
        (stride : ℝ) - 1 <
          (first - second) / width := by
      rw [sub_div]
      linarith
    have realDifference :
        ((stride : ℝ) - 1) * width <
          first - second :=
      (lt_div_iff₀ widthPos).mp <| by
        simpa [sub_div] using quotient
    exact realDifference.trans_le (le_abs_self _)

theorem pureWZ2_prop62_sameLineColor_distinctCell_separated
    {firstScale secondScale width : ℝ}
    {stride : ℕ}
    (widthPos : 0 < width)
    (first : Kakeya.DeltaTube firstScale)
    (second : Kakeya.DeltaTube secondScale)
    (firstLine : WZ1PaperTubeInLineClass first)
    (secondLine : WZ1PaperTubeInLineClass second)
    (sameColor :
      pureWZ2Prop62LineColor width stride first =
        pureWZ2Prop62LineColor width stride second)
    (differentCell :
      pureWZ2Prop62LineCell width first ≠
        pureWZ2Prop62LineCell width second) :
    ((stride : ℝ) - 1) * width <
      6 * wz1PaperLineDistance first second := by
  have existsCoordinate :
      ∃ coordinate : Fin 4,
        pureWZ2Prop62LineCell width first coordinate ≠
          pureWZ2Prop62LineCell width second coordinate := by
    by_contra hnone
    push Not at hnone
    exact differentCell (funext hnone)
  rcases existsCoordinate with
    ⟨coordinate, hcoordinate⟩
  let firstValue :=
    pureWZ2Prop62TubeParameterCoordinate
      (tubeParamsOfTube first) coordinate
  let secondValue :=
    pureWZ2Prop62TubeParameterCoordinate
      (tubeParamsOfTube second) coordinate
  have parameterSeparated :
      ((stride : ℝ) - 1) * width <
        |firstValue - secondValue| := by
    apply pureWZ2Prop62_floor_sameResidue_separated
      widthPos
    · exact congrFun sameColor coordinate
    · exact hcoordinate
  exact parameterSeparated.trans_le <|
    pureWZ2_prop62_tubeParameterCoordinate_le_lineDistance
      first second firstLine secondLine coordinate

end Kakeya.Assouad

end
