import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalRawTube
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalScaleData
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance

/-!
# Quantitative geometry bounds for fixed affine diagonal retubing
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- The fixed affine diagonal linear map has operator norm at most its height
factor when the transverse factor is at most one. -/
theorem pureWZ2AffineDiagonalLinear_norm_le_height
    (frameSlope : ℝ)
    {heightScale transverseScale : ℝ}
    (hheight : 1 ≤ heightScale)
    (htransverse : 0 ≤ transverseScale)
    (htransverseOne : transverseScale ≤ 1)
    (vector : Point3) :
    ‖pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale 1
        vector‖ ≤ heightScale * ‖vector‖ := by
  let rotated := pureWZ2HorizontalRotation frameSlope vector
  have hrotated : ‖rotated‖ = ‖vector‖ :=
    (pureWZ2HorizontalRotation frameSlope).norm_map vector
  have hsquare :
      ‖pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale 1
          vector‖ ^ 2 =
        (rotated 0) ^ 2 + (transverseScale * rotated 1) ^ 2 +
          (heightScale * rotated 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [pureWZ2AffineDiagonalLinear, rotated, Fin.sum_univ_succ, point3]
    ring
  have hrotatedSquare :
      ‖rotated‖ ^ 2 =
        (rotated 0) ^ 2 + (rotated 1) ^ 2 + (rotated 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
    ring
  have htransverseSquare : transverseScale ^ 2 ≤ heightScale ^ 2 := by
    nlinarith
  have honeSquare : (1 : ℝ) ≤ heightScale ^ 2 := by
    nlinarith
  have hboundSquare :
      ‖pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale 1
          vector‖ ^ 2 ≤ heightScale ^ 2 * ‖vector‖ ^ 2 := by
    rw [hsquare, ← hrotated, hrotatedSquare]
    nlinarith [sq_nonneg (rotated 0), sq_nonneg (rotated 1),
      sq_nonneg (rotated 2)]
  have hright : 0 ≤ heightScale * ‖vector‖ := mul_nonneg (by linarith) (norm_nonneg _)
  nlinarith [norm_nonneg
    (pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale 1
      vector)]

private theorem pureWZ2_reciprocalDiagonal_norm_le_inv_transverse
    {heightScale transverseScale : ℝ}
    (hheight : 1 ≤ heightScale)
    (htransverse : 0 < transverseScale)
    (htransverseOne : transverseScale ≤ 1)
    (vector : Point3) :
    ‖point3 (vector 0) (vector 1 / transverseScale)
        (vector 2 / heightScale)‖ ≤
      (1 / transverseScale) * ‖vector‖ := by
  have hheightPos : 0 < heightScale := lt_of_lt_of_le (by norm_num) hheight
  have hinvOne : 1 ≤ 1 / transverseScale := by
    exact (le_div_iff₀ htransverse).2 (by simpa using htransverseOne)
  have hinvHeight : 1 / heightScale ≤ 1 / transverseScale := by
    exact one_div_le_one_div_of_le htransverse (htransverseOne.trans hheight)
  have hinvHeightNonneg : 0 ≤ 1 / heightScale := by positivity
  have hinvTransverseNonneg : 0 ≤ 1 / transverseScale := by positivity
  have hsource := point3_coord_norm_sq vector
  have htarget := point3_coord_norm_sq
    (point3 (vector 0) (vector 1 / transverseScale)
      (vector 2 / heightScale))
  have hsquares :
      ‖point3 (vector 0) (vector 1 / transverseScale)
          (vector 2 / heightScale)‖ ^ 2 ≤
        ((1 / transverseScale) * ‖vector‖) ^ 2 := by
    rw [htarget, mul_pow, hsource]
    simp only [point3_coord0, point3_coord1, point3_coord2]
    rw [show vector 1 / transverseScale =
        (1 / transverseScale) * vector 1 by ring,
      show vector 2 / heightScale =
        (1 / heightScale) * vector 2 by ring]
    nlinarith [sq_nonneg (vector 0), sq_nonneg (vector 1),
      sq_nonneg (vector 2),
      mul_le_mul_of_nonneg_right
        (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) hinvTransverseNonneg |>.2
          hinvOne)
        (sq_nonneg (vector 0)),
      mul_le_mul_of_nonneg_right
        (sq_le_sq₀ hinvHeightNonneg hinvTransverseNonneg |>.2 hinvHeight)
        (sq_nonneg (vector 2))]
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hinvTransverseNonneg (norm_nonneg _))).mp hsquares

/-- The inverse transpose of the affine-diagonal map costs at most the
reciprocal transverse scale. -/
theorem pureWZ2AffineDiagonalInvTranspose_norm_le_inv_transverse
    (frameSlope : ℝ)
    {heightScale transverseScale : ℝ}
    (hheight : 1 ≤ heightScale)
    (htransverse : 0 < transverseScale)
    (htransverseOne : transverseScale ≤ 1)
    (normal : Point3) :
    ‖pureWZ2AffineDiagonalInvTranspose frameSlope heightScale
        transverseScale 1 normal‖ ≤
      (1 / transverseScale) * ‖normal‖ := by
  let rotated := pureWZ2HorizontalRotation frameSlope normal
  have hbound := pureWZ2_reciprocalDiagonal_norm_le_inv_transverse
    hheight htransverse htransverseOne rotated
  simpa [pureWZ2AffineDiagonalInvTranspose, rotated] using hbound

/-- Operator-norm form of
`pureWZ2AffineDiagonalInvTranspose_norm_le_inv_transverse`. -/
theorem pureWZ2AffineDiagonalInvTransposeLinear_opNorm_le_inv_transverse
    (frameSlope : ℝ)
    {heightScale transverseScale : ℝ}
    (hheight : 1 ≤ heightScale)
    (htransverse : 0 < transverseScale)
    (htransverseOne : transverseScale ≤ 1) :
    ‖(pureWZ2AffineDiagonalInvTransposeLinear frameSlope heightScale
        transverseScale 1).toContinuousLinearMap‖ ≤
      1 / transverseScale := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro normal
  exact pureWZ2AffineDiagonalInvTranspose_norm_le_inv_transverse frameSlope
    hheight htransverse htransverseOne normal

/-- The inverse linear equivalence has the same reciprocal-transverse
operator-norm bound. -/
theorem pureWZ2AffineDiagonalLinearEquiv_symm_opNorm_le_inv_transverse
    (frameSlope : ℝ)
    {heightScale transverseScale : ℝ}
    (hheight : 1 ≤ heightScale)
    (htransverse : 0 < transverseScale)
    (htransverseOne : transverseScale ≤ 1) :
    ‖(pureWZ2AffineDiagonalLinearEquiv frameSlope heightScale transverseScale 1
        (ne_of_gt (lt_of_lt_of_le (by norm_num) hheight)) htransverse.ne'
        one_ne_zero).symm.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤
      1 / transverseScale := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro vector
  let equivalence := pureWZ2AffineDiagonalLinearEquiv frameSlope heightScale
    transverseScale 1
    (ne_of_gt (lt_of_lt_of_le (by norm_num) hheight)) htransverse.ne'
    one_ne_zero
  have happly : equivalence.symm vector =
      pureWZ2AffineDiagonalLinearInverse frameSlope heightScale
        transverseScale 1 vector := by
    apply equivalence.injective
    rw [equivalence.apply_symm_apply]
    exact (pureWZ2AffineDiagonalLinear_inverse frameSlope
      (ne_of_gt (lt_of_lt_of_le (by norm_num) hheight)) htransverse.ne'
      one_ne_zero vector).symm
  change ‖equivalence.symm vector‖ ≤ (1 / transverseScale) * ‖vector‖
  rw [happly]
  unfold pureWZ2AffineDiagonalLinearInverse
  simp only [one_mul, div_one]
  change ‖(pureWZ2HorizontalRotation frameSlope).symm
        (point3 (vector 0) (vector 1 / transverseScale)
          (vector 2 / heightScale))‖ ≤
      (1 / transverseScale) * ‖vector‖
  rw [(pureWZ2HorizontalRotation frameSlope).symm.norm_map]
  exact pureWZ2_reciprocalDiagonal_norm_le_inv_transverse
    hheight htransverse htransverseOne vector

/-- The normalized affine image direction remains in the positive paper
vertical chart. -/
theorem pureWZ2AffineDiagonalDirection_vertical
    (frameSlope : ℝ)
    {heightScale transverseScale : ℝ}
    (hheight : 100 ≤ heightScale)
    (htransverse : 0 ≤ transverseScale)
    (htransverseOne : transverseScale ≤ 1)
    {direction : Point3}
    (hunit : ‖direction‖ = 1)
    (hvertical : (1 / 2 : ℝ) ≤ |direction 2|) :
    (1 / 2 : ℝ) ≤
      |(pureWZ2AffineDiagonalDirection frameSlope heightScale
          transverseScale 1 direction) 2| := by
  let rotated := pureWZ2HorizontalRotation frameSlope direction
  have hrotatedNorm : ‖rotated‖ = 1 := by
    rw [(pureWZ2HorizontalRotation frameSlope).norm_map, hunit]
  have hrotatedTwo : rotated 2 = direction 2 := by
    simp [rotated, pureWZ2HorizontalRotation_coord_two]
  let image := pureWZ2AffineDiagonalLinear frameSlope heightScale
    transverseScale 1 direction
  have himageTwo : image 2 = heightScale * direction 2 := by
    simp [image, pureWZ2AffineDiagonalLinear, rotated, point3,
      pureWZ2HorizontalRotation_coord_two]
  have himageNorm : ‖image‖ ≤ heightScale := by
    simpa [hunit] using pureWZ2AffineDiagonalLinear_norm_le_height
      frameSlope (by linarith : 1 ≤ heightScale) htransverse
      htransverseOne direction
  have himageNonzero : image ≠ 0 := by
    intro hzero
    rw [hzero] at himageTwo
    have hheightPos : 0 < heightScale := by linarith
    have hdirectionTwo : direction 2 = 0 := by
      simpa using (mul_eq_zero.mp (by simpa using himageTwo)).resolve_left
        hheightPos.ne'
    rw [hdirectionTwo, abs_zero] at hvertical
    norm_num at hvertical
  have himageNormPos : 0 < ‖image‖ := norm_pos_iff.mpr himageNonzero
  change (1 / 2 : ℝ) ≤
      |(‖image‖⁻¹ : ℝ) * image 2|
  rw [abs_mul, abs_inv, abs_of_nonneg (norm_nonneg image),
    himageTwo, abs_mul, abs_of_pos (by linarith : 0 < heightScale)]
  have hratio : (1 / 2 : ℝ) ≤
      ‖image‖⁻¹ * (heightScale * |direction 2|) := by
    rw [show ‖image‖⁻¹ * (heightScale * |direction 2|) =
        heightScale * |direction 2| / ‖image‖ by ring]
    apply (le_div_iff₀ himageNormPos).2
    calc
      (1 / 2 : ℝ) * ‖image‖ ≤ (1 / 2) * heightScale := by gcongr
      _ ≤ heightScale * |direction 2| := by
        have := mul_le_mul_of_nonneg_left hvertical
          (by linarith : 0 ≤ heightScale)
        simpa [mul_comm] using this
  simpa [mul_assoc] using hratio

/-- A source carrier point in a narrow common box forces the source axis at
the center height to remain close to the common center. -/
theorem pureWZ2_axis_center_coordinate_bound
    {delta : ℝ}
    {tube : Kakeya.DeltaTube delta}
    (hdelta : 0 < delta)
    (hline : WZ1PaperTubeInLineClass tube)
    (center halfWidth point : Point3)
    (hpointCarrier : point ∈ wz1PaperTubeCarrier tube)
    (hpointBox : point ∈ wz1AxisBox center halfWidth)
    (hheight : |center 2 - point 2| ≤ halfWidth 2)
    (coordinate : Fin 3) :
    |(tubeAxisPointAtHeight tube (center 2) - center) coordinate| ≤
      2 * halfWidth 2 + 18 * delta + halfWidth coordinate := by
  let sameHeight := wz1PaperAxisPointAtHeight tube (point 2)
  have hsameDist : dist point sameHeight ≤ 18 * delta :=
    wz2_paper_carrier_same_height_dist_18delta hdelta tube hline hpointCarrier
  have hcenterAxis : dist
      (wz1PaperAxisPointAtHeight tube (center 2)) sameHeight ≤
        2 * halfWidth 2 :=
    wz1Paper_axisPointAtHeight_dist_le_of_axis_point hline
      (center 2) (halfWidth 2)
      (wz1PaperAxisPointAtHeight_mem_axis tube (point 2)) <| by
        rw [wz1PaperAxisPointAtHeight_coord_two hline]
        exact hheight
  have haxisEq : wz1PaperAxisPointAtHeight tube (center 2) =
      tubeAxisPointAtHeight tube (center 2) := by
    apply PiLp.ext
    intro i
    have hvertical : tube.direction 2 ≠ 0 := by
      intro hzero
      have hverticalBound := hline.vertical
      rw [hzero, abs_zero] at hverticalBound
      norm_num at hverticalBound
    unfold wz1PaperAxisPointAtHeight wz1PaperDirection
    split_ifs with horientation <;>
      simp [wz1TubeAxisZeroPoint, tubeAxisPointAtHeight, hvertical,
        smul_eq_mul] <;> field_simp [hvertical] <;> ring
  have hcoordinateBox : |point coordinate - center coordinate| ≤
      halfWidth coordinate := by
    simpa [wz1AxisBox] using hpointBox coordinate
  -- The coordinate statement only needs the direct coordinate triangle; use
  -- the two axis moves and the box coordinate instead of the coarse norm sum.
  rw [← haxisEq]
  calc
    |(wz1PaperAxisPointAtHeight tube (center 2) - center) coordinate| ≤
        |(wz1PaperAxisPointAtHeight tube (center 2) - sameHeight) coordinate| +
          |(sameHeight - point) coordinate| + |(point - center) coordinate| := by
            rw [show wz1PaperAxisPointAtHeight tube (center 2) - center =
              (wz1PaperAxisPointAtHeight tube (center 2) - sameHeight) +
                (sameHeight - point) + (point - center) by abel]
            simp only [PiLp.add_apply]
            calc
              |((wz1PaperAxisPointAtHeight tube (center 2) - sameHeight)
                    coordinate + (sameHeight - point) coordinate) +
                  (point - center) coordinate| ≤
                |(wz1PaperAxisPointAtHeight tube (center 2) - sameHeight)
                    coordinate + (sameHeight - point) coordinate| +
                  |(point - center) coordinate| := abs_add_le _ _
              _ ≤ (|(wz1PaperAxisPointAtHeight tube (center 2) - sameHeight)
                    coordinate| + |(sameHeight - point) coordinate|) +
                  |(point - center) coordinate| := by
                    gcongr
                    exact abs_add_le _ _
    _ ≤ 2 * halfWidth 2 + 18 * delta + halfWidth coordinate := by
      gcongr
      · simpa [dist_eq_norm] using (PiLp.norm_apply_le
          (wz1PaperAxisPointAtHeight tube (center 2) - sameHeight) coordinate
          |>.trans <| by simpa [dist_eq_norm] using hcenterAxis)
      · calc
          |(sameHeight - point) coordinate| ≤ ‖sameHeight - point‖ := by
            simpa [Real.norm_eq_abs] using
              (PiLp.norm_apply_le (sameHeight - point) coordinate)
          _ = dist sameHeight point := by rw [dist_eq_norm]
          _ = dist point sameHeight := dist_comm _ _
          _ ≤ 18 * delta := hsameDist
      · simpa using hcoordinateBox

end Kakeya.Assouad

end
