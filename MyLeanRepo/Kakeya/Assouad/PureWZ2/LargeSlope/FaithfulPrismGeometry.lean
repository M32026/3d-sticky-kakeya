import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.RotatedWeightedCommonYRefinement
import MyLeanRepo.Kakeya.Assouad.LargeSlope.XZGridThreeIncidence
import MyLeanRepo.Kakeya.Assouad.WZ1.HorizontalChartNormalization.Basic

/-!
# Fixed-frame x'z prisms
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

attribute [local instance] Classical.propDecidable

/-- The inverse image of a paper xz-grid prism under one fixed horizontal
rotation. -/
def pureWZ2RotatedXZGridPrism
    (frameSlope x0 a b : ℝ) (index : ℤ) : Set Point3 :=
  {point | pureWZ2HorizontalRotation frameSlope point ∈
    xzGridPrism x0 a b index}

theorem measurableSet_pureWZ2RotatedXZGridPrism
    (frameSlope x0 a b : ℝ) (index : ℤ) :
    MeasurableSet (pureWZ2RotatedXZGridPrism
      frameSlope x0 a b index) := by
  have hcoordinate0 : Measurable
      (fun point : Point3 =>
        pureWZ2HorizontalRotation frameSlope point 0) := by fun_prop
  have hcoordinate2 : Measurable
      (fun point : Point3 =>
        pureWZ2HorizontalRotation frameSlope point 2) := by fun_prop
  change MeasurableSet
    ({point : Point3 |
      pureWZ2HorizontalRotation frameSlope point 0 ∈
        Set.Ico (x0 + (index : ℝ) * (b - a))
          (x0 + ((index : ℝ) + 1) * (b - a))} ∩
      {point : Point3 |
        pureWZ2HorizontalRotation frameSlope point 2 ∈ Set.Icc a b})
  exact (measurableSet_Ico.preimage hcoordinate0).inter
    (measurableSet_Icc.preimage hcoordinate2)

theorem pureWZ2RotatedXZGridPrism_mem
    {frameSlope x0 a b : ℝ} {index : ℤ} {point : Point3} :
    point ∈ pureWZ2RotatedXZGridPrism frameSlope x0 a b index ↔
      pureWZ2HorizontalRotation frameSlope point 0 ∈
          Set.Ico (x0 + (index : ℝ) * (b - a))
            (x0 + ((index : ℝ) + 1) * (b - a)) ∧
        point 2 ∈ Set.Icc a b := by
  simp [pureWZ2RotatedXZGridPrism, xzGridPrism]

theorem pureWZ2_mem_floor_rotatedXZGridPrism
    {frameSlope x0 a b : ℝ} (hwidth : 0 < b - a)
    {point : Point3} (hpointZ : point 2 ∈ Set.Icc a b) :
    point ∈ pureWZ2RotatedXZGridPrism frameSlope x0 a b
      (Int.floor ((pureWZ2HorizontalRotation frameSlope point 0 - x0) /
        (b - a))) := by
  rw [pureWZ2RotatedXZGridPrism_mem]
  refine ⟨?_, hpointZ⟩
  let value := (pureWZ2HorizontalRotation frameSlope point 0 - x0) /
    (b - a)
  have hlower : (Int.floor value : ℝ) ≤ value := Int.floor_le _
  have hupper : value < (Int.floor value : ℝ) + 1 :=
    Int.lt_floor_add_one _
  constructor
  · have hmul := mul_le_mul_of_nonneg_right hlower hwidth.le
    have hcancel : value * (b - a) =
        pureWZ2HorizontalRotation frameSlope point 0 - x0 := by
      dsimp only [value]
      field_simp [hwidth.ne']
    rw [hcancel] at hmul
    linarith
  · have hmul := mul_lt_mul_of_pos_right hupper hwidth
    have hcancel : value * (b - a) =
        pureWZ2HorizontalRotation frameSlope point 0 - x0 := by
      dsimp only [value]
      field_simp [hwidth.ne']
    rw [hcancel] at hmul
    linarith

/-- The fixed rotation preserves the vertical-chart bound of a tube. -/
lemma pureWZ2_rotated_direction_zero_bound
    {delta : ℝ} (frameSlope : ℝ)
    (tube : Kakeya.DeltaTube delta)
    (hvertical : (1 / 2 : ℝ) ≤ |tube.direction 2|) :
    |pureWZ2HorizontalRotation frameSlope tube.direction 0| ≤
      Real.sqrt 3 / 2 := by
  let rotatedTube := transportTube
    (pureWZ2HorizontalRotation frameSlope) tube
  have hvertical' : (1 / 2 : ℝ) ≤ |rotatedTube.direction 2| := by
    simpa [rotatedTube, transportTube] using hvertical
  simpa [rotatedTube, transportTube] using
    (direction_x_bound (T := rotatedTube) hvertical')

/-- Rotated-x diameter of a paper carrier inside one horizontal slab. -/
theorem pureWZ2_rotated_paper_tube_slab_x_diam
    {delta a b : ℝ} (hdelta : 0 < delta) (hab : a < b)
    (frameSlope : ℝ) {tube : Kakeya.DeltaTube delta}
    (hvertical : (1 / 2 : ℝ) ≤ |tube.direction 2|) :
    ∀ first second : Point3,
      first ∈ wz1PaperTubeCarrier tube ∩ horizontalSlab a b →
      second ∈ wz1PaperTubeCarrier tube ∩ horizontalSlab a b →
      |pureWZ2HorizontalRotation frameSlope first 0 -
          pureWZ2HorizontalRotation frameSlope second 0| ≤
        Real.sqrt 3 * (b - a) +
          (12 * Real.sqrt 3 + 12) * delta := by
  let rotation := pureWZ2HorizontalRotation frameSlope
  let W := b - a
  have hW : 0 < W := by dsimp only [W]; linarith
  let d0 := rotation tube.direction 0
  let d2 := tube.direction 2
  have hd0 : |d0| ≤ Real.sqrt 3 / 2 :=
    pureWZ2_rotated_direction_zero_bound frameSlope tube hvertical
  have hd2 : d2 ≠ 0 := by
    intro hzero
    have hzero' : tube.direction 2 = 0 := by simpa [d2] using hzero
    rw [hzero', abs_zero] at hvertical
    norm_num at hvertical
  have hlineClosed : IsClosed (tubeAxisLine tube) :=
    isClosed_tubeAxisLine tube
  intro first second hfirst hsecond
  rcases exists_dist_le_of_mem_cthickening_closed hlineClosed
      (by positivity) hfirst.1.1 with ⟨firstAxis, hfirstAxis, hfirstDist⟩
  rcases exists_dist_le_of_mem_cthickening_closed hlineClosed
      (by positivity) hsecond.1.1 with ⟨secondAxis, hsecondAxis, hsecondDist⟩
  rcases hfirstAxis with ⟨firstParameter, rfl⟩
  rcases hsecondAxis with ⟨secondParameter, rfl⟩
  let firstOnAxis := tube.base + firstParameter • tube.direction
  let secondOnAxis := tube.base + secondParameter • tube.direction
  have hfirstNorm : ‖first - firstOnAxis‖ ≤ 6 * delta := by
    simpa [dist_eq_norm] using hfirstDist
  have hsecondNorm : ‖second - secondOnAxis‖ ≤ 6 * delta := by
    simpa [dist_eq_norm] using hsecondDist
  have hfirstZ : |first 2 - firstOnAxis 2| ≤ 6 * delta :=
    (PiLp.norm_apply_le (first - firstOnAxis) 2).trans hfirstNorm
  have hsecondZ : |second 2 - secondOnAxis 2| ≤ 6 * delta :=
    (PiLp.norm_apply_le (second - secondOnAxis) 2).trans hsecondNorm
  have hfirstAxisZ : firstOnAxis 2 = tube.base 2 + firstParameter * d2 := by
    simp [firstOnAxis, d2] <;> abel
  have hsecondAxisZ : secondOnAxis 2 = tube.base 2 + secondParameter * d2 := by
    simp [secondOnAxis, d2] <;> abel
  have haxisZDiff :
      |(firstParameter - secondParameter) * d2| ≤ W + 12 * delta := by
    have hfirstRange : firstOnAxis 2 ∈
        Set.Icc (a - 6 * delta) (b + 6 * delta) := by
      constructor <;> linarith [hfirst.2.1, hfirst.2.2, abs_le.mp hfirstZ]
    have hsecondRange : secondOnAxis 2 ∈
        Set.Icc (a - 6 * delta) (b + 6 * delta) := by
      constructor <;> linarith [hsecond.2.1, hsecond.2.2, abs_le.mp hsecondZ]
    have hdiff : |firstOnAxis 2 - secondOnAxis 2| ≤ W + 12 * delta := by
      rw [abs_le]
      constructor <;> linarith [hfirstRange.1, hfirstRange.2,
        hsecondRange.1, hsecondRange.2]
    rw [hfirstAxisZ, hsecondAxisZ] at hdiff
    convert hdiff using 1 <;> ring
  have hparameter : |firstParameter - secondParameter| ≤
      2 * (W + 12 * delta) := by
    rw [abs_mul] at haxisZDiff
    have hd2Pos : 0 < |d2| := abs_pos.mpr hd2
    have hdivide : |firstParameter - secondParameter| ≤
        (W + 12 * delta) / |d2| := by
      exact (le_div_iff₀ hd2Pos).2 haxisZDiff
    have hinv : 1 / |d2| ≤ 2 := by
      calc
        1 / |d2| ≤ 1 / (1 / 2 : ℝ) := by gcongr
        _ = 2 := by norm_num
    calc
      |firstParameter - secondParameter| ≤
          (W + 12 * delta) / |d2| := hdivide
      _ = (W + 12 * delta) * (1 / |d2|) := by ring
      _ ≤ (W + 12 * delta) * 2 := by gcongr <;> positivity
      _ = 2 * (W + 12 * delta) := by ring
  have hfirstRot :
      |rotation first 0 - rotation firstOnAxis 0| ≤ 6 * delta := by
    have hcoord := PiLp.norm_apply_le (rotation (first - firstOnAxis)) 0
    rw [rotation.norm_map] at hcoord
    have hmap : rotation (first - firstOnAxis) =
        rotation first - rotation firstOnAxis := rotation.map_sub _ _
    rw [hmap] at hcoord
    exact hcoord.trans hfirstNorm
  have hsecondRot :
      |rotation second 0 - rotation secondOnAxis 0| ≤ 6 * delta := by
    have hcoord := PiLp.norm_apply_le (rotation (second - secondOnAxis)) 0
    rw [rotation.norm_map] at hcoord
    have hmap : rotation (second - secondOnAxis) =
        rotation second - rotation secondOnAxis := rotation.map_sub _ _
    rw [hmap] at hcoord
    exact hcoord.trans hsecondNorm
  have haxisRot : |rotation firstOnAxis 0 - rotation secondOnAxis 0| ≤
      |firstParameter - secondParameter| * (Real.sqrt 3 / 2) := by
    have heq : rotation firstOnAxis - rotation secondOnAxis =
        (firstParameter - secondParameter) • rotation tube.direction := by
      simp [firstOnAxis, secondOnAxis]
      module
    have hcoord := congr_arg (fun point : Point3 => point 0) heq
    simp at hcoord
    rw [hcoord, abs_mul]
    exact mul_le_mul_of_nonneg_left hd0 (abs_nonneg _)
  calc
    |rotation first 0 - rotation second 0| ≤
        |rotation first 0 - rotation firstOnAxis 0| +
        |rotation firstOnAxis 0 - rotation secondOnAxis 0| +
        |rotation secondOnAxis 0 - rotation second 0| := by
      have hdecomp : rotation first 0 - rotation second 0 =
          (rotation first 0 - rotation firstOnAxis 0) +
          (rotation firstOnAxis 0 - rotation secondOnAxis 0) +
          (rotation secondOnAxis 0 - rotation second 0) := by ring
      rw [hdecomp]
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ 6 * delta +
        |firstParameter - secondParameter| * (Real.sqrt 3 / 2) +
          6 * delta := by
      gcongr
      simpa [abs_sub_comm] using hsecondRot
    _ ≤ 6 * delta + 2 * (W + 12 * delta) *
        (Real.sqrt 3 / 2) + 6 * delta := by gcongr
    _ = Real.sqrt 3 * (b - a) +
        (12 * Real.sqrt 3 + 12) * delta := by
      dsimp only [W]
      ring

lemma pureWZ2_paper_diam_lt_two_width
    {width delta : ℝ} (hwidth : 0 < width)
    (hsmall : 256 * delta ≤ width) :
    Real.sqrt 3 * width + (12 * Real.sqrt 3 + 12) * delta <
      2 * width := by
  have hsqrt : Real.sqrt 3 < 7 / 4 := by
    exact (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  have hdelta : delta ≤ width / 256 := by linarith
  calc
    Real.sqrt 3 * width + (12 * Real.sqrt 3 + 12) * delta ≤
        Real.sqrt 3 * width +
          (12 * Real.sqrt 3 + 12) * (width / 256) := by
      gcongr <;> nlinarith [Real.sqrt_nonneg 3]
    _ < 2 * width := by
      nlinarith [Real.sqrt_nonneg 3]

/-- A paper tube meets at most three fixed-frame x'z prisms. -/
theorem pureWZ2_rotated_paper_tube_three_prisms
    {delta a b x0 : ℝ} (hdelta : 0 < delta) (hab : a < b)
    (frameSlope : ℝ) {tube : Kakeya.DeltaTube delta}
    (hvertical : (1 / 2 : ℝ) ≤ |tube.direction 2|)
    (hsmall : 256 * delta ≤ b - a) (indices : Finset ℤ) :
    (indices.filter fun (index : ℤ) =>
      (wz1PaperTubeCarrier tube ∩
        pureWZ2RotatedXZGridPrism frameSlope x0 a b index).Nonempty).card ≤
      3 := by
  let rotation := pureWZ2HorizontalRotation frameSlope
  let width := b - a
  let values : Set ℝ :=
    (fun point : Point3 => rotation point 0) ''
      (wz1PaperTubeCarrier tube ∩ horizontalSlab a b)
  have hdiam : ∀ first second, first ∈ values → second ∈ values →
      |first - second| < 2 * width := by
    intro first second hfirst hsecond
    rcases hfirst with ⟨firstPoint, hfirstPoint, rfl⟩
    rcases hsecond with ⟨secondPoint, hsecondPoint, rfl⟩
    exact (pureWZ2_rotated_paper_tube_slab_x_diam hdelta hab
      frameSlope hvertical firstPoint secondPoint hfirstPoint hsecondPoint).trans_lt
        (pureWZ2_paper_diam_lt_two_width (by change 0 < b - a; linarith)
          (by simpa only [width] using hsmall))
  have hsubset :
      indices.filter (fun index =>
        (wz1PaperTubeCarrier tube ∩
          pureWZ2RotatedXZGridPrism frameSlope x0 a b index).Nonempty) ⊆
      indices.filter (fun index =>
        (values ∩ Set.Ico
          (x0 + (index : ℝ) * width)
          (x0 + ((index : ℝ) + 1) * width)).Nonempty) := by
    intro index hindex
    rcases Finset.mem_filter.mp hindex with ⟨hindexMem, point,
      hpointPaper, hpointPrism⟩
    rw [pureWZ2RotatedXZGridPrism_mem] at hpointPrism
    exact Finset.mem_filter.mpr ⟨hindexMem, rotation point 0,
      ⟨point, ⟨hpointPaper, hpointPrism.2⟩, rfl⟩, hpointPrism.1⟩
  exact (Finset.card_le_card hsubset).trans
    (grid_meets_at_most_three (by dsimp only [width]; linarith) hdiam indices)

/-- A radius-width ball in the rotated coordinates meets at most three x'z
grid columns. -/
theorem pureWZ2_rotated_ball_three_prisms
    {width x0 a b : ℝ} (hwidth : 0 < width)
    (hwidthEq : width = b - a) (center : Point3)
    (indices : Finset ℤ)
    (hindices : ∀ index ∈ indices,
      (Metric.closedBall center width ∩ xzGridPrism x0 a b index).Nonempty) :
    indices.card ≤ 3 := by
  let coordinateSet : Set ℝ :=
    (fun point : Point3 => point 0) '' Metric.closedBall center width
  have hdiam : ∀ first second, first ∈ coordinateSet →
      second ∈ coordinateSet → |first - second| ≤ 2 * width := by
    intro first second hfirst hsecond
    rcases hfirst with ⟨firstPoint, hfirstBall, rfl⟩
    rcases hsecond with ⟨secondPoint, hsecondBall, rfl⟩
    have hfirstCoord : |firstPoint 0 - center 0| ≤ width := by
      exact (PiLp.norm_apply_le (firstPoint - center) 0).trans hfirstBall
    have hsecondCoord : |secondPoint 0 - center 0| ≤ width := by
      exact (PiLp.norm_apply_le (secondPoint - center) 0).trans hsecondBall
    rw [abs_le]
    constructor <;> linarith [abs_le.mp hfirstCoord, abs_le.mp hsecondCoord]
  let middle : ℤ := Int.floor ((center 0 - x0) / width)
  have hsubset : indices ⊆ ({middle - 1, middle, middle + 1} : Finset ℤ) := by
    intro index hindex
    rcases hindices index hindex with ⟨point, hpointBall, hpointPrism⟩
    have hpointX : point 0 ∈
        Set.Ico (x0 + (index : ℝ) * width)
          (x0 + ((index : ℝ) + 1) * width) := by
      simpa [xzGridPrism, hwidthEq] using hpointPrism.1
    have hcoord : |point 0 - center 0| ≤ width :=
      (PiLp.norm_apply_le (point - center) 0).trans hpointBall
    have hfloorLower : (middle : ℝ) ≤ (center 0 - x0) / width :=
      Int.floor_le _
    have hfloorUpper : (center 0 - x0) / width < (middle : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have hindexLower : middle - 1 ≤ index := by
      by_contra hnot
      have hindexUpper : index ≤ middle - 2 := by omega
      have hcast : (index : ℝ) ≤ (middle : ℝ) - 2 := by exact_mod_cast hindexUpper
      have hmul : (index : ℝ) * width ≤ ((middle : ℝ) - 2) * width :=
        mul_le_mul_of_nonneg_right hcast hwidth.le
      have hpointUpper := hpointX.2
      have hcenterLower : x0 + (middle : ℝ) * width ≤ center 0 := by
        have := mul_le_mul_of_nonneg_right hfloorLower hwidth.le
        field_simp [hwidth.ne'] at this
        linarith
      have hpointCenter : center 0 - width ≤ point 0 := by
        linarith [abs_le.mp hcoord]
      have hgridUpper : x0 + ((index : ℝ) + 1) * width ≤
          x0 + (middle : ℝ) * width - width := by
        nlinarith
      linarith
    have hindexUpper : index ≤ middle + 1 := by
      by_contra hnot
      have hindexLower' : middle + 2 ≤ index := by omega
      have hcast : (middle : ℝ) + 2 ≤ (index : ℝ) := by exact_mod_cast hindexLower'
      have hmul : ((middle : ℝ) + 2) * width ≤ (index : ℝ) * width :=
        mul_le_mul_of_nonneg_right hcast hwidth.le
      have hpointLower := hpointX.1
      have hcenterUpper : center 0 < x0 + ((middle : ℝ) + 1) * width := by
        have := mul_lt_mul_of_pos_right hfloorUpper hwidth
        field_simp [hwidth.ne'] at this
        linarith
      have hpointCenter : point 0 ≤ center 0 + width := by
        linarith [abs_le.mp hcoord]
      have hgridLower : x0 + ((middle : ℝ) + 2) * width ≤
          x0 + (index : ℝ) * width := by linarith
      linarith
    have : index = middle - 1 ∨ index = middle ∨ index = middle + 1 := by omega
    rcases this with (rfl | rfl | rfl) <;> simp
  calc
    indices.card ≤ ({middle - 1, middle, middle + 1} : Finset ℤ).card :=
      Finset.card_le_card hsubset
    _ = 3 := by
      have hleft : middle - 1 ≠ middle := by omega
      have hright : middle ≠ middle + 1 := by omega
      have hfar : middle - 1 ≠ middle + 1 := by omega
      simp [hleft, hright, hfar]

/-- A set of real numbers with diameter strictly below three grid widths
meets at most four half-open grid intervals. -/
theorem pureWZ2_set_meets_at_most_four_intervals
    {width : ℝ} (hwidth : 0 < width) {origin : ℝ}
    {values : Set ℝ}
    (hdiam : ∀ first second, first ∈ values → second ∈ values →
      |first - second| < 3 * width)
    (indices : Finset ℤ) :
    (indices.filter fun (index : ℤ) =>
      (values ∩ Set.Ico
        (origin + (index : ℝ) * width)
        (origin + ((index : ℝ) + 1) * width)).Nonempty).card ≤ 4 := by
  let selected : Finset ℤ := indices.filter fun (index : ℤ) =>
    (values ∩ Set.Ico
      (origin + (index : ℝ) * width)
      (origin + ((index : ℝ) + 1) * width)).Nonempty
  by_contra hnot
  change ¬ selected.card ≤ 4 at hnot
  have hfive : 5 ≤ selected.card := by omega
  have hnonempty : selected.Nonempty := Finset.card_pos.mp (by omega)
  let lower := selected.min' hnonempty
  let upper := selected.max' hnonempty
  have hlower := Finset.min'_mem selected hnonempty
  have hupper := Finset.max'_mem selected hnonempty
  have hgap : 4 ≤ upper - lower := by
    by_contra hgapNot
    have hgapLe : upper - lower ≤ 3 := by omega
    have hsubset : selected ⊆ Finset.Icc lower (lower + 3) := by
      intro index hindex
      exact Finset.mem_Icc.mpr
        ⟨Finset.min'_le selected index hindex, by
          have := Finset.le_max' selected index hindex
          omega⟩
    have hcard := Finset.card_le_card hsubset
    have hIccSet : Finset.Icc lower (lower + 3) =
        {lower, lower + 1, lower + 2, lower + 3} := by
      ext value
      simp [Finset.mem_Icc]
      omega
    have hIcc : (Finset.Icc lower (lower + 3)).card = 4 := by
      rw [hIccSet]
      simp
    rw [hIcc] at hcard
    omega
  rcases Finset.mem_filter.mp hlower |>.2 with
    ⟨lowerPoint, hlowerValue, hlowerGrid⟩
  rcases Finset.mem_filter.mp hupper |>.2 with
    ⟨upperPoint, hupperValue, hupperGrid⟩
  have hgap' : lower + 4 ≤ upper := by omega
  have hcast : (lower : ℝ) + 4 ≤ (upper : ℝ) := by exact_mod_cast hgap'
  have hseparation : 3 * width < upperPoint - lowerPoint := by
    have hlowerUpper := hlowerGrid.2
    have hupperLower := hupperGrid.1
    have hmul : ((lower : ℝ) + 4) * width ≤ (upper : ℝ) * width :=
      mul_le_mul_of_nonneg_right hcast hwidth.le
    linarith
  have habs : |upperPoint - lowerPoint| = upperPoint - lowerPoint :=
    abs_of_pos (by linarith)
  have hcontradiction := hdiam upperPoint lowerPoint hupperValue hlowerValue
  rw [habs] at hcontradiction
  linarith


end Kakeya.Assouad

end
