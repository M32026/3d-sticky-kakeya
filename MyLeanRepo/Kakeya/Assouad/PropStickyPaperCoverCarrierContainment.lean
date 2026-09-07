import MyLeanRepo.Kakeya.Assouad.PropStickyPaperUnitRescalingBasics

/-!
# Literal paper-carrier containment from a dilated line cover

The cropped paper tube of radius `r` is the `6r`-neighborhood of the full
supporting line inside `[-1,1]^3`.  On the positive vertical chart, a
factor-two line-distance cover at scale `rho` therefore contains every
`delta`-paper carrier once `delta ≤ rho`.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric

/-- The point on a paper-oriented axis with prescribed third coordinate. -/
def wz1PaperAxisPointAtHeight
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (height : ℝ) : Point3 :=
  wz1TubeAxisZeroPoint tube +
    (height / (wz1PaperDirection tube (2 : Fin 3))) •
      wz1PaperDirection tube

lemma wz1TubeAxisZeroPoint_add_smul_paperDirection_mem_axis
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (scale : ℝ) :
    wz1TubeAxisZeroPoint tube +
        scale • wz1PaperDirection tube ∈
      tubeAxisLine tube := by
  rcases wz1TubeAxisZeroPoint_mem_axis tube with
    ⟨parameter, hparameter⟩
  unfold wz1PaperDirection
  split_ifs
  · refine ⟨parameter + scale, ?_⟩
    rw [hparameter]
    module
  · refine ⟨parameter - scale, ?_⟩
    rw [hparameter]
    module

lemma wz1PaperAxisPointAtHeight_mem_axis
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (height : ℝ) :
    wz1PaperAxisPointAtHeight tube height ∈ tubeAxisLine tube := by
  exact
    wz1TubeAxisZeroPoint_add_smul_paperDirection_mem_axis
      tube
      (height / (wz1PaperDirection tube (2 : Fin 3)))

lemma wz1PaperAxisPointAtHeight_coord_two
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (hline : WZ1PaperTubeInLineClass tube)
    (height : ℝ) :
    wz1PaperAxisPointAtHeight tube height (2 : Fin 3) =
      height := by
  have hvertical :
      wz1PaperDirection tube (2 : Fin 3) ≠ 0 := by
    linarith [hline.1]
  simp [wz1PaperAxisPointAtHeight,
    wz1TubeAxisZeroPoint_coord_two tube hline.vertical,
    hvertical]

/--
At a common height in the cropped box, line-distance controls the distance
between the two paper-oriented axes.
-/
lemma wz1PaperAxisPointAtHeight_dist_le
    {delta rho : ℝ}
    {fine : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    (hfine : WZ1PaperTubeInLineClass fine)
    (hcoarse : WZ1PaperTubeInLineClass coarse)
    {height : ℝ} (hheight : |height| ≤ 1) :
    dist
        (wz1PaperAxisPointAtHeight fine height)
        (wz1PaperAxisPointAtHeight coarse height) ≤
      6 * wz1PaperLineDistance fine coarse := by
  let fineZero := wz1TubeAxisZeroPoint fine
  let coarseZero := wz1TubeAxisZeroPoint coarse
  let fineDirection := wz1PaperDirection fine
  let coarseDirection := wz1PaperDirection coarse
  let fineVertical := fineDirection (2 : Fin 3)
  let coarseVertical := coarseDirection (2 : Fin 3)
  have hfine_vertical : 1 / 2 ≤ fineVertical := hfine.1
  have hcoarse_vertical : 1 / 2 ≤ coarseVertical := hcoarse.1
  have hfine_vertical_pos : 0 < fineVertical := by linarith
  have hcoarse_vertical_pos : 0 < coarseVertical := by linarith
  have hfine_vertical_le_one : fineVertical ≤ 1 := by
    have hcoord :=
      abs_coord_two_le_norm fineDirection
    rw [abs_of_pos hfine_vertical_pos,
      wz1PaperDirection_norm fine] at hcoord
    exact hcoord
  have hcoarse_vertical_le_one : coarseVertical ≤ 1 := by
    have hcoord :=
      abs_coord_two_le_norm coarseDirection
    rw [abs_of_pos hcoarse_vertical_pos,
      wz1PaperDirection_norm coarse] at hcoord
    exact hcoord
  have hinv_fine : fineVertical⁻¹ ≤ 2 := by
    rw [← one_div]
    exact (div_le_iff₀ hfine_vertical_pos).mpr (by linarith)
  have hinv_coarse : coarseVertical⁻¹ ≤ 2 := by
    rw [← one_div]
    exact (div_le_iff₀ hcoarse_vertical_pos).mpr (by linarith)
  have hvertical_difference :
      |fineVertical - coarseVertical| ≤
        ‖fineDirection - coarseDirection‖ :=
    abs_coord_two_le_norm (fineDirection - coarseDirection)
      |>.trans_eq (by rfl)
  have hparameter_difference :
      |height / fineVertical - height / coarseVertical| ≤
        4 * ‖fineDirection - coarseDirection‖ := by
    have hinv_difference :
        |fineVertical⁻¹ - coarseVertical⁻¹| ≤
          4 * |fineVertical - coarseVertical| := by
      have halgebra :
          fineVertical⁻¹ - coarseVertical⁻¹ =
            (coarseVertical - fineVertical) /
              (fineVertical * coarseVertical) := by
        field_simp [hfine_vertical_pos.ne',
          hcoarse_vertical_pos.ne']
      rw [halgebra, abs_div, abs_mul,
        abs_of_pos hfine_vertical_pos,
        abs_of_pos hcoarse_vertical_pos]
      have hdenominator :
          1 / 4 ≤ fineVertical * coarseVertical := by
        nlinarith
      have hdenominator_pos :
          0 < fineVertical * coarseVertical := by positivity
      rw [abs_sub_comm]
      exact (div_le_iff₀ hdenominator_pos).mpr
        (by nlinarith [abs_nonneg (fineVertical - coarseVertical)])
    rw [div_eq_mul_inv, div_eq_mul_inv,
      ← mul_sub, abs_mul]
    calc
      |height| * |fineVertical⁻¹ - coarseVertical⁻¹|
          ≤ 1 * (4 * |fineVertical - coarseVertical|) := by
        gcongr
      _ ≤ 4 * ‖fineDirection - coarseDirection‖ := by
        rw [one_mul]
        gcongr
  have hpoint_difference :
      wz1PaperAxisPointAtHeight fine height -
          wz1PaperAxisPointAtHeight coarse height =
        (fineZero - coarseZero) +
          (height / fineVertical) •
            (fineDirection - coarseDirection) +
          (height / fineVertical -
            height / coarseVertical) • coarseDirection := by
    dsimp only [wz1PaperAxisPointAtHeight,
      fineZero, coarseZero, fineDirection,
      coarseDirection, fineVertical, coarseVertical]
    module
  rw [dist_eq_norm, hpoint_difference]
  calc
    ‖(fineZero - coarseZero) +
        (height / fineVertical) •
          (fineDirection - coarseDirection) +
        (height / fineVertical -
          height / coarseVertical) • coarseDirection‖
        ≤ ‖fineZero - coarseZero‖ +
            ‖(height / fineVertical) •
              (fineDirection - coarseDirection)‖ +
            ‖(height / fineVertical -
              height / coarseVertical) • coarseDirection‖ := by
      exact (norm_add_le _ _).trans <| by
        gcongr
        exact norm_add_le _ _
    _ = dist fineZero coarseZero +
          |height / fineVertical| *
            ‖fineDirection - coarseDirection‖ +
          |height / fineVertical -
            height / coarseVertical| := by
      rw [norm_smul, norm_smul,
        wz1PaperDirection_norm coarse, mul_one,
        dist_eq_norm]
      simp only [Real.norm_eq_abs]
    _ ≤ dist fineZero coarseZero +
          2 * ‖fineDirection - coarseDirection‖ +
          4 * ‖fineDirection - coarseDirection‖ := by
      gcongr
      rw [abs_div, abs_of_pos hfine_vertical_pos]
      exact (div_le_iff₀ hfine_vertical_pos).mpr
        (by nlinarith [abs_nonneg height])
    _ ≤ dist fineZero coarseZero +
          6 * InnerProductGeometry.angle
            fineDirection coarseDirection := by
      have hchord :=
        unit_norm_sub_le_angle
          (wz1PaperDirection_norm fine)
          (wz1PaperDirection_norm coarse)
      nlinarith
    _ ≤ 6 * wz1PaperLineDistance fine coarse := by
      dsimp only [wz1PaperLineDistance,
        fineZero, coarseZero, fineDirection, coarseDirection]
      have hdist_nonneg : 0 ≤ dist
          (wz1TubeAxisZeroPoint fine)
          (wz1TubeAxisZeroPoint coarse) := dist_nonneg
      have hangle_nonneg : 0 ≤ InnerProductGeometry.angle
          (wz1PaperDirection fine)
          (wz1PaperDirection coarse) :=
        InnerProductGeometry.angle_nonneg _ _
      nlinarith

end Kakeya.Assouad

end
