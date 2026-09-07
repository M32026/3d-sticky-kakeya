import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoverCarrierContainment
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralCommonRescalingLineCoverHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryHelpers

/-!
# Paper line distance forced by literal carrier containment

Literal containment of one cropped full-line paper tube in another forces
their oriented supporting lines to be close in the paper line metric.  A
coarse absolute constant is sufficient for the parent-fiber repair: selected
recursive parent families use the named literal source-separation factor.
-/

noncomputable section

namespace Kakeya.Assouad

lemma wz1Paper_axis_exists_parameter
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (hline : WZ1PaperTubeInLineClass tube)
    {point : Point3}
    (hpoint : point ∈ tubeAxisLine tube) :
    ∃ parameter : ℝ,
      point =
        wz1TubeAxisZeroPoint tube +
          parameter • wz1PaperDirection tube := by
  rcases hpoint with ⟨parameter, rfl⟩
  have hdirection :
      tube.direction (2 : Fin 3) ≠ 0 := by
    intro hzero
    have hvertical := hline.vertical
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  unfold wz1PaperDirection
  split_ifs with horientation
  · refine
      ⟨parameter +
          tube.base (2 : Fin 3) /
            tube.direction (2 : Fin 3), ?_⟩
    ext coordinate
    simp only [wz1TubeAxisZeroPoint, PiLp.add_apply,
      PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [hdirection]
    ring
  · refine
      ⟨-(parameter +
          tube.base (2 : Fin 3) /
            tube.direction (2 : Fin 3)), ?_⟩
    ext coordinate
    simp only [wz1TubeAxisZeroPoint, PiLp.add_apply,
      PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      PiLp.neg_apply]
    field_simp [hdirection]
    ring

lemma wz1Paper_axisPointAtHeight_dist_le_of_axis_point
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (hline : WZ1PaperTubeInLineClass tube)
    (height radius : ℝ)
    {point : Point3}
    (hpoint : point ∈ tubeAxisLine tube)
    (hheight : |height - point (2 : Fin 3)| ≤ radius) :
    dist (wz1PaperAxisPointAtHeight tube height) point ≤
      2 * radius := by
  rcases wz1Paper_axis_exists_parameter hline hpoint with
    ⟨parameter, rfl⟩
  let direction := wz1PaperDirection tube
  let vertical := direction (2 : Fin 3)
  have hvertical : 1 / 2 ≤ vertical := hline.1
  have hverticalPos : 0 < vertical := by linarith
  have hzeroTwo :
      wz1TubeAxisZeroPoint tube (2 : Fin 3) = 0 :=
    wz1TubeAxisZeroPoint_coord_two tube hline.vertical
  have hpointTwo :
      (wz1TubeAxisZeroPoint tube +
          parameter • direction) (2 : Fin 3) =
        parameter * vertical := by
    simp [direction, vertical, hzeroTwo]
  rw [hpointTwo] at hheight
  have hvector :
      wz1PaperAxisPointAtHeight tube height -
          (wz1TubeAxisZeroPoint tube +
            parameter • direction) =
        (height / vertical - parameter) • direction := by
    dsimp only [wz1PaperAxisPointAtHeight, direction, vertical]
    module
  rw [dist_eq_norm, hvector, norm_smul,
    wz1PaperDirection_norm, mul_one]
  simp only [Real.norm_eq_abs]
  have halgebra :
      height / vertical - parameter =
        (height - parameter * vertical) / vertical := by
    field_simp [hverticalPos.ne']
  rw [halgebra, abs_div, abs_of_pos hverticalPos]
  exact
    (div_le_iff₀ hverticalPos).mpr
      (by
        calc
          |height - parameter * vertical| ≤ radius := hheight
          _ ≤ 2 * radius * vertical := by
            nlinarith [abs_nonneg
              (height - parameter * vertical)])

/--
Projection to the point of the paper axis at the same third coordinate has
operator norm at most two on the positive vertical chart.
-/
lemma wz1Paper_axisPointAtHeight_dist_point_le_two_mul
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (hline : WZ1PaperTubeInLineClass tube)
    (point axisPoint : Point3)
    (haxisPoint : axisPoint ∈ tubeAxisLine tube) :
    dist
        (wz1PaperAxisPointAtHeight tube (point (2 : Fin 3)))
        point ≤
      2 * dist point axisPoint := by
  rcases wz1Paper_axis_exists_parameter hline haxisPoint with
    ⟨parameter, haxisPointEq⟩
  let direction := wz1PaperDirection tube
  let vertical := direction (2 : Fin 3)
  let error :=
    point -
      (wz1TubeAxisZeroPoint tube + parameter • direction)
  let horizontalError :=
    error - (error (2 : Fin 3) / vertical) • direction
  have hvertical : 1 / 2 ≤ vertical := hline.1
  have hverticalPos : 0 < vertical := by linarith
  have hzeroTwo :
      wz1TubeAxisZeroPoint tube (2 : Fin 3) = 0 :=
    wz1TubeAxisZeroPoint_coord_two tube hline.vertical
  have haxisTwo :
      (wz1TubeAxisZeroPoint tube + parameter • direction)
          (2 : Fin 3) =
        parameter * vertical := by
    simp [direction, vertical, hzeroTwo]
  have herrorTwo :
      error (2 : Fin 3) =
        point (2 : Fin 3) - parameter * vertical := by
    simp [error, haxisTwo]
  have hvector :
      wz1PaperAxisPointAtHeight tube (point (2 : Fin 3)) -
          point =
        -horizontalError := by
    have hdirectionVertical :
        wz1PaperDirection tube (2 : Fin 3) ≠ 0 := by
      dsimp only [vertical, direction] at hverticalPos
      exact hverticalPos.ne'
    apply PiLp.ext
    intro coordinate
    simp only [wz1PaperAxisPointAtHeight, horizontalError, error,
      PiLp.sub_apply, PiLp.neg_apply, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]
    dsimp only [direction, vertical]
    rw [hzeroTwo]
    field_simp [hdirectionVertical]
    ring
  have hdirectionSq :
      direction (0 : Fin 3) ^ 2 +
          direction (1 : Fin 3) ^ 2 +
          vertical ^ 2 =
        1 := by
    have hnorm := point3_coord_norm_sq direction
    rw [wz1PaperDirection_norm tube] at hnorm
    dsimp only [vertical]
    nlinarith
  have hhorizontalTwo :
      horizontalError (2 : Fin 3) = 0 := by
    simp [horizontalError, vertical, hverticalPos.ne']
  have hscaledHorizontal :
      vertical ^ 2 * ‖horizontalError‖ ^ 2 =
        (vertical * error 0 - error 2 * direction 0) ^ 2 +
          (vertical * error 1 - error 2 * direction 1) ^ 2 := by
    rw [point3_coord_norm_sq horizontalError, hhorizontalTwo]
    simp only [horizontalError, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]
    field_simp [hverticalPos.ne']
    ring
  have hloss :
      (vertical * error 0 - error 2 * direction 0) ^ 2 +
          (vertical * error 1 - error 2 * direction 1) ^ 2 ≤
        ‖error‖ ^ 2 := by
    have herrorNorm := point3_coord_norm_sq error
    have hcross :=
      sq_nonneg
        (direction 0 * error 1 - direction 1 * error 0)
    have hparallel :=
      sq_nonneg
        (vertical * error 2 +
          direction 0 * error 0 +
          direction 1 * error 1)
    rw [herrorNorm]
    nlinarith [hdirectionSq]
  have hscaled :
      vertical ^ 2 * ‖horizontalError‖ ^ 2 ≤
        ‖error‖ ^ 2 := by
    rw [hscaledHorizontal]
    exact hloss
  have hverticalSq : 1 / 4 ≤ vertical ^ 2 := by
    nlinarith
  have hnorm :
      ‖horizontalError‖ ≤ 2 * ‖error‖ := by
    have hnonneg := norm_nonneg horizontalError
    have herrorNonneg := norm_nonneg error
    nlinarith [sq_nonneg ‖horizontalError‖, sq_nonneg ‖error‖]
  rw [dist_eq_norm, hvector, norm_neg, dist_eq_norm, haxisPointEq]
  exact hnorm

private lemma paper_axisPointAtHeight_mem_box
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (hline : WZ1PaperTubeInLineClass tube)
    {height : ℝ}
    (hheight : |height| ≤ 1 / 4) :
    wz1PaperAxisPointAtHeight tube height ∈
      Kakeya.Streamlined.axisBox 2 2 2 := by
  let point := wz1PaperAxisPointAtHeight tube height
  let zero := wz1TubeAxisZeroPoint tube
  have hzeroAxis : zero ∈ tubeAxisLine tube :=
    wz1TubeAxisZeroPoint_mem_axis tube
  have hzeroTwo : zero (2 : Fin 3) = 0 :=
    wz1TubeAxisZeroPoint_coord_two tube hline.vertical
  have hdist :
      dist point zero ≤ 2 * |height| := by
    exact
      wz1Paper_axisPointAtHeight_dist_le_of_axis_point
        hline height |height| hzeroAxis (by simp [hzeroTwo])
  have hdistHalf : dist point zero ≤ 1 / 2 := by
    linarith
  have hcoord :
      ∀ coordinate : Fin 3,
        |point coordinate - zero coordinate| ≤ 1 / 2 := by
    intro coordinate
    have h :=
      PiLp.dist_apply_le point zero coordinate
    simpa [Real.dist_eq] using h.trans hdistHalf
  have hzero0 : |zero (0 : Fin 3)| ≤ 1 / 3 := hline.2.1
  have hzero1 : |zero (1 : Fin 3)| ≤ 1 / 3 := hline.2.2
  have hpoint0 : |point (0 : Fin 3)| ≤ 1 := by
    calc
      |point (0 : Fin 3)| =
          |(point 0 - zero 0) + zero 0| := by ring_nf
      _ ≤ |point 0 - zero 0| + |zero 0| := abs_add_le _ _
      _ ≤ 1 / 2 + 1 / 3 :=
        add_le_add (hcoord (0 : Fin 3)) hzero0
      _ ≤ 1 := by norm_num
  have hpoint1 : |point (1 : Fin 3)| ≤ 1 := by
    calc
      |point (1 : Fin 3)| =
          |(point 1 - zero 1) + zero 1| := by ring_nf
      _ ≤ |point 1 - zero 1| + |zero 1| := abs_add_le _ _
      _ ≤ 1 / 2 + 1 / 3 :=
        add_le_add (hcoord (1 : Fin 3)) hzero1
      _ ≤ 1 := by norm_num
  have hpoint2 :
      point (2 : Fin 3) = height :=
    wz1PaperAxisPointAtHeight_coord_two hline height
  simp only [Kakeya.Streamlined.axisBox]
  simpa [point] using
    (show
      |point (0 : Fin 3)| ≤ 2 / 2 ∧
        |point (1 : Fin 3)| ≤ 2 / 2 ∧
          |point (2 : Fin 3)| ≤ 2 / 2 from
      ⟨by norm_num at hpoint0 ⊢; exact hpoint0,
        by norm_num at hpoint1 ⊢; exact hpoint1,
        by rw [hpoint2]; linarith⟩)

private lemma paper_axisPoint_contained_dist
    {delta rho : ℝ}
    {fine : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hfine : WZ1PaperTubeInLineClass fine)
    (hcoarse : WZ1PaperTubeInLineClass coarse)
    (hcontained : WZ2PaperTubeCarrierCovers fine coarse)
    {height : ℝ}
    (hheight : |height| ≤ 1 / 4) :
    dist
        (wz1PaperAxisPointAtHeight fine height)
        (wz1PaperAxisPointAtHeight coarse height) ≤
      18 * rho := by
  let point := wz1PaperAxisPointAtHeight fine height
  have hpointAxis : point ∈ tubeAxisLine fine :=
    wz1PaperAxisPointAtHeight_mem_axis fine height
  have hpointFine : point ∈ wz1PaperTubeCarrier fine := by
    refine ⟨?_, paper_axisPointAtHeight_mem_box hfine hheight⟩
    exact
      Metric.mem_cthickening_of_dist_le
        point point (6 * delta) (tubeAxisLine fine)
        hpointAxis (by simp; positivity)
  have hpointCoarse := hcontained hpointFine
  rcases
      exists_dist_le_of_mem_cthickening_closed
        (isClosed_tubeAxisLine coarse)
        (by positivity : 0 ≤ 6 * rho)
        hpointCoarse.1
    with ⟨axisPoint, haxisPoint, hpointAxisPoint⟩
  have hpointTwo :
      point (2 : Fin 3) = height :=
    wz1PaperAxisPointAtHeight_coord_two hfine height
  have hheightAxis :
      |height - axisPoint (2 : Fin 3)| ≤ 6 * rho := by
    have hcoord :=
      PiLp.dist_apply_le point axisPoint (2 : Fin 3)
    rw [hpointTwo] at hcoord
    simpa [Real.dist_eq] using hcoord.trans hpointAxisPoint
  have hsameHeight :
      dist
          (wz1PaperAxisPointAtHeight coarse height)
          axisPoint ≤
        12 * rho := by
    convert
      wz1Paper_axisPointAtHeight_dist_le_of_axis_point
        hcoarse height (6 * rho) haxisPoint hheightAxis using 1 <;>
      ring
  calc
    dist point (wz1PaperAxisPointAtHeight coarse height) ≤
        dist point axisPoint +
          dist axisPoint
            (wz1PaperAxisPointAtHeight coarse height) :=
      dist_triangle _ _ _
    _ ≤ 6 * rho + 12 * rho := by
      gcongr
      simpa [dist_comm] using hsameHeight
    _ = 18 * rho := by ring

/--
Literal containment in a radius-`rho` paper tube forces paper line distance
at most `400 * rho`.
-/
theorem wz2_paper_carrier_containment_lineDistance_le
    {delta rho : ℝ}
    {fine : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hfine : WZ1PaperTubeInLineClass fine)
    (hcoarse : WZ1PaperTubeInLineClass coarse)
    (hcontained : WZ2PaperTubeCarrierCovers fine coarse) :
    wz1PaperLineDistance fine coarse ≤ 400 * rho := by
  let fineZero := wz1TubeAxisZeroPoint fine
  let coarseZero := wz1TubeAxisZeroPoint coarse
  let fineDirection := wz1PaperDirection fine
  let coarseDirection := wz1PaperDirection coarse
  let fineVertical := fineDirection (2 : Fin 3)
  let coarseVertical := coarseDirection (2 : Fin 3)
  have hfineVertical : 1 / 2 ≤ fineVertical := hfine.1
  have hcoarseVertical : 1 / 2 ≤ coarseVertical := hcoarse.1
  have hfineVerticalPos : 0 < fineVertical := by linarith
  have hcoarseVerticalPos : 0 < coarseVertical := by linarith
  have hfineVerticalLe : fineVertical ≤ 1 := by
    have h :=
      abs_coord_two_le_norm fineDirection
    rw [abs_of_pos hfineVerticalPos,
      wz1PaperDirection_norm fine] at h
    exact h
  have hcoarseVerticalLe : coarseVertical ≤ 1 := by
    have h :=
      abs_coord_two_le_norm coarseDirection
    rw [abs_of_pos hcoarseVerticalPos,
      wz1PaperDirection_norm coarse] at h
    exact h
  let fineSlope := fineVertical⁻¹ • fineDirection
  let coarseSlope := coarseVertical⁻¹ • coarseDirection
  have hfineSlopeNorm : 1 ≤ ‖fineSlope‖ := by
    change 1 ≤ ‖fineVertical⁻¹ • fineDirection‖
    rw [norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hfineVerticalPos]
    have hnorm : ‖fineDirection‖ = 1 := by
      exact wz1PaperDirection_norm fine
    rw [hnorm, mul_one]
    exact (one_le_inv₀ hfineVerticalPos).mpr hfineVerticalLe
  have hcoarseSlopeNorm : 1 ≤ ‖coarseSlope‖ := by
    change 1 ≤ ‖coarseVertical⁻¹ • coarseDirection‖
    rw [norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hcoarseVerticalPos]
    have hnorm : ‖coarseDirection‖ = 1 := by
      exact wz1PaperDirection_norm coarse
    rw [hnorm, mul_one]
    exact (one_le_inv₀ hcoarseVerticalPos).mpr hcoarseVerticalLe
  have hfineNormalize :
      NormedSpace.normalize fineSlope = fineDirection := by
    dsimp only [fineSlope]
    rw [NormedSpace.normalize_smul_of_pos (inv_pos.mpr hfineVerticalPos)]
    exact
      NormedSpace.normalize_eq_self_of_norm_eq_one
        (wz1PaperDirection_norm fine)
  have hcoarseNormalize :
      NormedSpace.normalize coarseSlope = coarseDirection := by
    dsimp only [coarseSlope]
    rw [NormedSpace.normalize_smul_of_pos
      (inv_pos.mpr hcoarseVerticalPos)]
    exact
      NormedSpace.normalize_eq_self_of_norm_eq_one
        (wz1PaperDirection_norm coarse)
  let fineQuarter := wz1PaperAxisPointAtHeight fine (1 / 4)
  let coarseQuarter := wz1PaperAxisPointAtHeight coarse (1 / 4)
  have hzeroDist : dist fineZero coarseZero ≤ 18 * rho := by
    simpa [fineZero, coarseZero,
      wz1PaperAxisPointAtHeight, div_zero, zero_smul,
      add_zero] using
      (paper_axisPoint_contained_dist
        hdelta hrho hfine hcoarse hcontained
        (height := 0) (by norm_num))
  have hquarterDist :
      dist fineQuarter coarseQuarter ≤ 18 * rho := by
    exact
      paper_axisPoint_contained_dist
        hdelta hrho hfine hcoarse hcontained
        (height := 1 / 4) (by norm_num)
  have hfineQuarter :
      fineQuarter = fineZero + (1 / 4 : ℝ) • fineSlope := by
    dsimp only [fineQuarter, fineZero, fineSlope,
      wz1PaperAxisPointAtHeight, fineVertical, fineDirection]
    congr 1
    rw [div_eq_mul_inv, smul_smul]
  have hcoarseQuarter :
      coarseQuarter =
        coarseZero + (1 / 4 : ℝ) • coarseSlope := by
    dsimp only [coarseQuarter, coarseZero, coarseSlope,
      wz1PaperAxisPointAtHeight, coarseVertical, coarseDirection]
    congr 1
    rw [div_eq_mul_inv, smul_smul]
  have hslopeVector :
      fineSlope - coarseSlope =
        (4 : ℝ) • ((fineQuarter - coarseQuarter) -
          (fineZero - coarseZero)) := by
    rw [hfineQuarter, hcoarseQuarter]
    module
  have hslopeDist :
      ‖fineSlope - coarseSlope‖ ≤ 144 * rho := by
    rw [hslopeVector, norm_smul,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    calc
      4 * ‖(fineQuarter - coarseQuarter) -
            (fineZero - coarseZero)‖ ≤
          4 * (‖fineQuarter - coarseQuarter‖ +
            ‖fineZero - coarseZero‖) := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ 4 * (18 * rho + 18 * rho) := by
        gcongr
        · simpa [dist_eq_norm] using hquarterDist
        · simpa [dist_eq_norm] using hzeroDist
      _ = 144 * rho := by ring
  have hdirectionDist :
      ‖fineDirection - coarseDirection‖ ≤ 144 * rho := by
    rw [← hfineNormalize, ← hcoarseNormalize]
    exact
      (norm_normalize_sub_normalize_le_norm_sub
        hfineSlopeNorm hcoarseSlopeNorm).trans hslopeDist
  have hangle :
      InnerProductGeometry.angle fineDirection coarseDirection ≤
        288 * rho := by
    calc
      InnerProductGeometry.angle fineDirection coarseDirection ≤
          (Real.pi / 2) *
            ‖fineDirection - coarseDirection‖ :=
        angle_le_pi_div_two_mul_norm_sub
          (wz1PaperDirection_norm fine)
          (wz1PaperDirection_norm coarse)
      _ ≤ 2 * (144 * rho) := by
        gcongr
        linarith [Real.pi_lt_four]
      _ = 288 * rho := by ring
  dsimp only [wz1PaperLineDistance]
  change dist fineZero coarseZero +
      InnerProductGeometry.angle fineDirection coarseDirection ≤
    400 * rho
  linarith

end Kakeya.Assouad

end
