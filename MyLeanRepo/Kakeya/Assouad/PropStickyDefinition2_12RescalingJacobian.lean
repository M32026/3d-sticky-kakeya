import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingBridge
import MyLeanRepo.Kakeya.Assouad.PropStickyOrdinaryToCroppedShading
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume
import MyLeanRepo.Kakeya.Streamlined.VolumeHelpers

/-!
# Dimension-only Jacobian bound between Assouad and WZ coordinates

The outer John ellipsoid of a `rho`-tube has determinant at least
`rho^2 / 4`: it contains the tube, the tube has volume at least `2 rho^2`,
and the three-dimensional unit ball has volume at most `8`.

The literal WZ map has determinant
`(1 / 100)^3 * (1 / rho)^2`.  Hence the common coordinate change from
outer-John coordinates to literal WZ coordinates has determinant at least
`1 / 4_000_000`, uniformly in the tube and the scale.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- The three-dimensional closed unit ball has volume at most eight. -/
theorem wz2Paper_unitBall_volume_le_eight :
    volume (Metric.closedBall (0 : Point3) 1) ≤ 8 := by
  calc
    volume (Metric.closedBall (0 : Point3) 1) ≤
        volume (Kakeya.Streamlined.axisBox 2 2 2) :=
      measure_mono wz2_paper_unitBall_subset_axisBox
    _ = 8 := by
      rw [Kakeya.Streamlined.volume_axisBox 2 2 2]
      · norm_num
      · norm_num
      · norm_num
      · norm_num

/-- Every ordinary `rho`-tube has volume at least `2 rho^2`. -/
theorem wz2Paper_ordinary_tube_volume_lower
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    ENNReal.ofReal (2 * rho ^ 2) ≤ volume anchor.carrier := by
  let canonical : Kakeya.DeltaTube rho :=
    {
      base := 0
      direction := EuclideanSpace.single (0 : Fin 3) 1
      direction_unit := by simp
    }
  have hcanonical :
      canonical.volume = Kakeya.deltaTubeVolume rho := rfl
  have hvolume :
      anchor.volume = canonical.volume :=
    Kakeya.Streamlined.tube_volume_eq anchor canonical
  change
    ENNReal.ofReal (2 * rho ^ 2) ≤ anchor.volume
  rw [hvolume, hcanonical]
  exact
    Kakeya.Streamlined.tube_volume_ge_two_delta_sq rho hrho

/-- The outer-John linear map of a `rho`-tube has determinant at least
`rho^2 / 4`. -/
theorem wz2Paper_outerJohn_abs_det_lower
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    rho ^ 2 / 4 ≤
      |LinearMap.det
        ((wz2_paper_ordinary_tube_isConvexBody anchor hrho
          ).outerJohnEllipsoidMap : Point3 →ₗ[ℝ] Point3)| := by
  let convexBody :=
    wz2_paper_ordinary_tube_isConvexBody anchor hrho
  let center := convexBody.outerJohnEllipsoidCenter
  let linear := convexBody.outerJohnEllipsoidMap
  have hcarrier :
      anchor.carrier ⊆ JohnEllipsoid.ellipsoid center linear :=
    convexBody.outerJohnEllipsoid_spec.1
  have hvolumeLower :
      ENNReal.ofReal (2 * rho ^ 2) ≤
        volume (JohnEllipsoid.ellipsoid center linear) :=
    (wz2Paper_ordinary_tube_volume_lower anchor hrho).trans
      (measure_mono hcarrier)
  have hvolumeUpper :
      volume (JohnEllipsoid.ellipsoid center linear) ≤
        ENNReal.ofReal
            |LinearMap.det (linear : Point3 →ₗ[ℝ] Point3)| * 8 := by
    rw [JohnEllipsoid.volume_ellipsoid_eq]
    gcongr
    exact wz2Paper_unitBall_volume_le_eight
  have hENN :
      ENNReal.ofReal (2 * rho ^ 2) ≤
        ENNReal.ofReal
          (|LinearMap.det (linear : Point3 →ₗ[ℝ] Point3)| * 8) := by
    calc
      ENNReal.ofReal (2 * rho ^ 2) ≤
          volume (JohnEllipsoid.ellipsoid center linear) :=
        hvolumeLower
      _ ≤
          ENNReal.ofReal
              |LinearMap.det (linear : Point3 →ₗ[ℝ] Point3)| * 8 :=
        hvolumeUpper
      _ =
          ENNReal.ofReal
            (|LinearMap.det (linear : Point3 →ₗ[ℝ] Point3)| * 8) := by
        rw [ENNReal.ofReal_mul (abs_nonneg _)]
        norm_num
  have hreal :
      2 * rho ^ 2 ≤
        |LinearMap.det (linear : Point3 →ₗ[ℝ] Point3)| * 8 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hENN
  change
    rho ^ 2 / 4 ≤
      |LinearMap.det (linear : Point3 →ₗ[ℝ] Point3)|
  linarith

/-- Exact determinant of the literal WZ affine rescaling. -/
theorem wz2PaperLiteralUnitRescalingAffineEquiv_abs_det
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    |LinearMap.det
        ((wz2PaperLiteralUnitRescalingAffineEquiv anchor hrho).linear :
          Point3 →ₗ[ℝ] Point3)| =
      (1 / 100 : ℝ) ^ 3 * (1 / rho) ^ 2 := by
  change
    |LinearMap.det
      ((1 / 100 : ℝ) •
        ((transverseScaleLin rho).comp
          (householderToE3
            (wz1PaperDirection anchor)
            (wz1PaperDirection_norm anchor)).toLinearMap))| =
      _
  rw [LinearMap.det_smul]
  have hfinrank : Module.finrank ℝ Point3 = 3 := by
    simp [Point3]
  rw [hfinrank, LinearMap.det_comp,
    transverseScaleLin_det rho hrho,
    abs_mul, abs_mul,
    householderToE3_abs_det,
    abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  ring

/-- Exact determinant factorization of the John-to-literal coordinate
change. -/
theorem wz2PaperJohnToLiteralCoordinateChange_abs_det
    {rho : ℝ} {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (normalization : WZ2PaperAssouadUnitRescalingData anchor) :
    |LinearMap.det
        ((wz2PaperJohnToLiteralCoordinateChange hrho normalization).linear :
          Point3 →ₗ[ℝ] Point3)| =
      ((1 / 100 : ℝ) ^ 3 * (1 / rho) ^ 2) *
        |LinearMap.det
          (normalization.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| := by
  let literal :=
    wz2PaperLiteralUnitRescalingAffineEquiv anchor hrho
  have hlinear :
      (wz2PaperJohnToLiteralCoordinateChange hrho normalization).linear =
        normalization.map.symm.linear.trans literal.linear := rfl
  rw [hlinear]
  have hcomposition :
      ((normalization.map.symm.linear.trans literal.linear :
        Point3 ≃ₗ[ℝ] Point3) : Point3 →ₗ[ℝ] Point3) =
        (literal.linear : Point3 →ₗ[ℝ] Point3).comp
          (normalization.map.symm.linear :
            Point3 →ₗ[ℝ] Point3) := by
    ext point
    rfl
  rw [hcomposition, LinearMap.det_comp, abs_mul]
  have hJohn :
      (normalization.map.symm.linear : Point3 →ₗ[ℝ] Point3) =
        normalization.parent_convex_body.outerJohnEllipsoidMap := rfl
  rw [hJohn,
    wz2PaperLiteralUnitRescalingAffineEquiv_abs_det anchor hrho]

/-- Uniform lower determinant bound for the common coordinate change. -/
theorem wz2PaperJohnToLiteralCoordinateChange_abs_det_lower
    {rho : ℝ} {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (normalization : WZ2PaperAssouadUnitRescalingData anchor) :
    (1 / 4000000 : ℝ) ≤
      |LinearMap.det
        ((wz2PaperJohnToLiteralCoordinateChange hrho normalization).linear :
          Point3 →ₗ[ℝ] Point3)| := by
  rw [wz2PaperJohnToLiteralCoordinateChange_abs_det
    hrho normalization]
  have hJohn :=
    wz2Paper_outerJohn_abs_det_lower anchor hrho
  have hrhoSq : 0 < rho ^ 2 := sq_pos_of_pos hrho
  calc
    (1 / 4000000 : ℝ) =
        ((1 / 100 : ℝ) ^ 3 * (1 / rho) ^ 2) *
          (rho ^ 2 / 4) := by
      field_simp [hrho.ne']
      ring
    _ ≤
        ((1 / 100 : ℝ) ^ 3 * (1 / rho) ^ 2) *
          |LinearMap.det
            (normalization.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)| := by
      gcongr

/-- The inverse coordinate change loses at most the fixed factor
`4_000_000` in volume. -/
theorem wz2PaperJohnToLiteralCoordinateChange_inverse_volume
    {rho : ℝ} {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (normalization : WZ2PaperAssouadUnitRescalingData anchor)
    (targetSet : Set Point3) :
    volume
        ((wz2PaperJohnToLiteralCoordinateChange hrho normalization).symm ''
          targetSet) ≤
      (4000000 : ENNReal) * volume targetSet := by
  let coordinateChange :=
    wz2PaperJohnToLiteralCoordinateChange hrho normalization
  rw [wz2PaperAffineEquiv_volume_image_eq]
  have hdetLower :=
    wz2PaperJohnToLiteralCoordinateChange_abs_det_lower
      hrho normalization
  have hdetPos :
      0 <
        |LinearMap.det
          (coordinateChange.linear : Point3 →ₗ[ℝ] Point3)| := by
    linarith
  have hinverse :
      |LinearMap.det
          (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
        4000000 := by
    have hsymm :
        coordinateChange.symm.linear =
          coordinateChange.linear.symm := rfl
    rw [hsymm, LinearEquiv.det_coe_symm, abs_inv]
    apply (inv_le_iff_one_le_mul₀ hdetPos).2
    nlinarith
  have hENN :
      ENNReal.ofReal
          |LinearMap.det
            (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
        (4000000 : ENNReal) := by
    calc
      ENNReal.ofReal
          |LinearMap.det
            (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
          ENNReal.ofReal (4000000 : ℝ) :=
        ENNReal.ofReal_mono hinverse
      _ = (4000000 : ENNReal) := by norm_num
  gcongr

end Kakeya.Assouad

end
