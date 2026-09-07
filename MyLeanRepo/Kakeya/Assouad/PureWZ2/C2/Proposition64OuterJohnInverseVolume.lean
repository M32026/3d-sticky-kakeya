import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12NestedJohnCWATransport
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingBridge
import MyLeanRepo.Kakeya.Assouad.EssentiallyDistinctCardBound

/-!
# Scale-explicit inverse volume for the canonical outer-John chart

The inverse canonical normalization has Jacobian equal to the determinant of
the parent outer-John ellipsoid.  For an ordinary `rho`-tube with `rho ≤ 1`,
John's theorem and the capsule volume bound give a uniform `324 * rho^2`
upper bound.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- The determinant of the parent outer-John ellipsoid is at most
`324 * rho^2`. -/
theorem pureWZ2Proposition64_outerJohn_detENN_le
    {rho : ℝ}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (parent : Kakeya.DeltaTube rho)
    (normalization : WZ2PaperAssouadUnitRescalingData parent) :
    ENNReal.ofReal
        |LinearMap.det
          (normalization.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| ≤
      (324 : ENNReal) * Kakeya.realRpowENN rho 2 := by
  let unitBallVolume : ENNReal :=
    volume (Metric.closedBall (0 : Point3) 1)
  have hunitBallOne : (1 : ENNReal) ≤ unitBallVolume := by
    dsimp only [unitBallVolume]
    rw [EuclideanSpace.volume_closedBall_fin_three]
    have hreal : (1 : ℝ) ≤ Real.pi * 4 / 3 := by
      linarith [Real.pi_gt_three]
    simpa using ENNReal.ofReal_mono hreal
  have hellipsoidVolume :
      volume normalization.parent_convex_body.outerJohnEllipsoid =
        ENNReal.ofReal
            |LinearMap.det
              (normalization.parent_convex_body.outerJohnEllipsoidMap :
                Point3 →ₗ[ℝ] Point3)| *
          unitBallVolume := by
    exact JohnEllipsoid.volume_ellipsoid_eq
      normalization.parent_convex_body.outerJohnEllipsoidCenter
      normalization.parent_convex_body.outerJohnEllipsoidMap
  have hdetVolume :
      ENNReal.ofReal
          |LinearMap.det
            (normalization.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)| ≤
        volume normalization.parent_convex_body.outerJohnEllipsoid := by
    rw [hellipsoidVolume]
    calc
      ENNReal.ofReal
          |LinearMap.det
            (normalization.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)| =
          ENNReal.ofReal
              |LinearMap.det
                (normalization.parent_convex_body.outerJohnEllipsoidMap :
                  Point3 →ₗ[ℝ] Point3)| * 1 := by simp
      _ ≤
          ENNReal.ofReal
              |LinearMap.det
                (normalization.parent_convex_body.outerJohnEllipsoidMap :
                  Point3 →ₗ[ℝ] Point3)| * unitBallVolume := by
        gcongr
  have hparentVolume :
      volume parent.carrier ≤
        (12 : ENNReal) * Kakeya.realRpowENN rho 2 := by
    have hraw := tube_volume_upper_pi hrho parent
    have hreal :
        Real.pi * rho ^ 2 * (1 + 2 * rho) ≤ 12 * rho ^ 2 := by
      have hpi : Real.pi ≤ 4 := Real.pi_le_four
      have hfactor : Real.pi * (1 + 2 * rho) ≤ 12 := by
        calc
          Real.pi * (1 + 2 * rho) ≤
              4 * (1 + 2 * rho) := by
            gcongr
          _ ≤ 12 := by nlinarith
      calc
        Real.pi * rho ^ 2 * (1 + 2 * rho) =
            rho ^ 2 * (Real.pi * (1 + 2 * rho)) := by ring
        _ ≤ rho ^ 2 * 12 :=
          mul_le_mul_of_nonneg_left hfactor (sq_nonneg rho)
        _ = 12 * rho ^ 2 := by ring
    calc
      volume parent.carrier ≤
          ENNReal.ofReal (Real.pi * rho ^ 2 * (1 + 2 * rho)) :=
        hraw
      _ ≤ ENNReal.ofReal (12 * rho ^ 2) :=
        ENNReal.ofReal_mono hreal
      _ = (12 : ENNReal) * Kakeya.realRpowENN rho 2 := by
        simp [Kakeya.realRpowENN, Real.rpow_two,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12)]
  calc
    ENNReal.ofReal
        |LinearMap.det
          (normalization.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| ≤
        volume normalization.parent_convex_body.outerJohnEllipsoid :=
      hdetVolume
    _ ≤ (27 : ENNReal) * volume parent.carrier :=
      normalization.outerJohn_volume_le_twentySeven
    _ ≤ (27 : ENNReal) *
          ((12 : ENNReal) * Kakeya.realRpowENN rho 2) := by
      gcongr
    _ = (324 : ENNReal) * Kakeya.realRpowENN rho 2 := by ring

/-- Scale-unrestricted determinant bound for the parent outer-John
ellipsoid.  This is the form needed by nearby-scale witnesses whose actual
covering radius is allowed to exceed one by a fixed finite factor. -/
theorem pureWZ2Proposition64_outerJohn_detENN_le_general
    {rho : ℝ}
    (hrho : 0 < rho)
    (parent : Kakeya.DeltaTube rho)
    (normalization : WZ2PaperAssouadUnitRescalingData parent) :
    ENNReal.ofReal
        |LinearMap.det
          (normalization.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| ≤
      (108 : ENNReal) * Kakeya.realRpowENN rho 2 *
        ENNReal.ofReal (1 + 2 * rho) := by
  let unitBallVolume : ENNReal :=
    volume (Metric.closedBall (0 : Point3) 1)
  have hunitBallOne : (1 : ENNReal) ≤ unitBallVolume := by
    dsimp only [unitBallVolume]
    rw [EuclideanSpace.volume_closedBall_fin_three]
    have hreal : (1 : ℝ) ≤ Real.pi * 4 / 3 := by
      linarith [Real.pi_gt_three]
    simpa using ENNReal.ofReal_mono hreal
  have hellipsoidVolume :
      volume normalization.parent_convex_body.outerJohnEllipsoid =
        ENNReal.ofReal
            |LinearMap.det
              (normalization.parent_convex_body.outerJohnEllipsoidMap :
                Point3 →ₗ[ℝ] Point3)| *
          unitBallVolume := by
    exact JohnEllipsoid.volume_ellipsoid_eq
      normalization.parent_convex_body.outerJohnEllipsoidCenter
      normalization.parent_convex_body.outerJohnEllipsoidMap
  have hdetVolume :
      ENNReal.ofReal
          |LinearMap.det
            (normalization.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)| ≤
        volume normalization.parent_convex_body.outerJohnEllipsoid := by
    rw [hellipsoidVolume]
    calc
      ENNReal.ofReal
          |LinearMap.det
            (normalization.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)| =
          ENNReal.ofReal
              |LinearMap.det
                (normalization.parent_convex_body.outerJohnEllipsoidMap :
                  Point3 →ₗ[ℝ] Point3)| * 1 := by simp
      _ ≤
          ENNReal.ofReal
              |LinearMap.det
                (normalization.parent_convex_body.outerJohnEllipsoidMap :
                  Point3 →ₗ[ℝ] Point3)| * unitBallVolume := by
        gcongr
  have hparentVolume :
      volume parent.carrier ≤
        (4 : ENNReal) * Kakeya.realRpowENN rho 2 *
          ENNReal.ofReal (1 + 2 * rho) := by
    have hraw := tube_volume_upper_pi hrho parent
    have hreal :
        Real.pi * rho ^ 2 * (1 + 2 * rho) ≤
          4 * rho ^ 2 * (1 + 2 * rho) := by
      have hfactor : 0 ≤ rho ^ 2 * (1 + 2 * rho) := by positivity
      nlinarith [Real.pi_le_four]
    calc
      volume parent.carrier ≤
          ENNReal.ofReal (Real.pi * rho ^ 2 * (1 + 2 * rho)) :=
        hraw
      _ ≤ ENNReal.ofReal (4 * rho ^ 2 * (1 + 2 * rho)) :=
        ENNReal.ofReal_mono hreal
      _ = (4 : ENNReal) * Kakeya.realRpowENN rho 2 *
          ENNReal.ofReal (1 + 2 * rho) := by
        simp [Kakeya.realRpowENN, Real.rpow_two,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
          ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * rho ^ 2)]
  calc
    ENNReal.ofReal
        |LinearMap.det
          (normalization.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| ≤
        volume normalization.parent_convex_body.outerJohnEllipsoid :=
      hdetVolume
    _ ≤ (27 : ENNReal) * volume parent.carrier :=
      normalization.outerJohn_volume_le_twentySeven
    _ ≤ (27 : ENNReal) *
          ((4 : ENNReal) * Kakeya.realRpowENN rho 2 *
            ENNReal.ofReal (1 + 2 * rho)) := by
      gcongr
    _ = (108 : ENNReal) * Kakeya.realRpowENN rho 2 *
        ENNReal.ofReal (1 + 2 * rho) := by ring

/-- Scale-unrestricted inverse-volume form of the preceding determinant
estimate. -/
theorem pureWZ2Proposition64_outerJohn_inverse_volume_le_general
    {rho : ℝ}
    (hrho : 0 < rho)
    (parent : Kakeya.DeltaTube rho)
    (normalization : WZ2PaperAssouadUnitRescalingData parent)
    (targetSet : Set Point3) :
    volume (normalization.map.symm '' targetSet) ≤
      ((108 : ENNReal) * Kakeya.realRpowENN rho 2 *
        ENNReal.ofReal (1 + 2 * rho)) * volume targetSet := by
  rw [wz2PaperAffineEquiv_volume_image_eq]
  have hlinear :
      (normalization.map.symm.linear : Point3 →ₗ[ℝ] Point3) =
        normalization.parent_convex_body.outerJohnEllipsoidMap := rfl
  rw [hlinear]
  gcongr
  exact pureWZ2Proposition64_outerJohn_detENN_le_general
    hrho parent normalization

/-- The inverse canonical outer-John chart loses at most
`324 * rho^2` in volume. -/
theorem pureWZ2Proposition64_outerJohn_inverse_volume_le
    {rho : ℝ}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (parent : Kakeya.DeltaTube rho)
    (normalization : WZ2PaperAssouadUnitRescalingData parent)
    (targetSet : Set Point3) :
    volume (normalization.map.symm '' targetSet) ≤
      (324 : ENNReal) * Kakeya.realRpowENN rho 2 *
        volume targetSet := by
  rw [wz2PaperAffineEquiv_volume_image_eq]
  have hlinear :
      (normalization.map.symm.linear : Point3 →ₗ[ℝ] Point3) =
        normalization.parent_convex_body.outerJohnEllipsoidMap := rfl
  rw [hlinear]
  gcongr
  exact pureWZ2Proposition64_outerJohn_detENN_le
    hrho hrhoOne parent normalization

/-- The determinant estimate with the larger fixed-scale range used by the
localized high-scale root.  The capsule factor is now bounded by
`pi * (1 + 2 * rho) <= 36` for `rho <= 4`. -/
theorem pureWZ2Proposition64_outerJohn_detENN_le_of_le_four
    {rho : ℝ}
    (hrho : 0 < rho)
    (hrhoFour : rho ≤ 4)
    (parent : Kakeya.DeltaTube rho)
    (normalization : WZ2PaperAssouadUnitRescalingData parent) :
    ENNReal.ofReal
        |LinearMap.det
          (normalization.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| ≤
      (972 : ENNReal) * Kakeya.realRpowENN rho 2 := by
  let unitBallVolume : ENNReal :=
    volume (Metric.closedBall (0 : Point3) 1)
  have hunitBallOne : (1 : ENNReal) ≤ unitBallVolume := by
    dsimp only [unitBallVolume]
    rw [EuclideanSpace.volume_closedBall_fin_three]
    have hreal : (1 : ℝ) ≤ Real.pi * 4 / 3 := by
      linarith [Real.pi_gt_three]
    simpa using ENNReal.ofReal_mono hreal
  have hellipsoidVolume :
      volume normalization.parent_convex_body.outerJohnEllipsoid =
        ENNReal.ofReal
            |LinearMap.det
              (normalization.parent_convex_body.outerJohnEllipsoidMap :
                Point3 →ₗ[ℝ] Point3)| *
          unitBallVolume := by
    exact JohnEllipsoid.volume_ellipsoid_eq
      normalization.parent_convex_body.outerJohnEllipsoidCenter
      normalization.parent_convex_body.outerJohnEllipsoidMap
  have hdetVolume :
      ENNReal.ofReal
          |LinearMap.det
            (normalization.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)| ≤
        volume normalization.parent_convex_body.outerJohnEllipsoid := by
    rw [hellipsoidVolume]
    calc
      ENNReal.ofReal
          |LinearMap.det
            (normalization.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)| =
          ENNReal.ofReal
              |LinearMap.det
                (normalization.parent_convex_body.outerJohnEllipsoidMap :
                  Point3 →ₗ[ℝ] Point3)| * 1 := by simp
      _ ≤
          ENNReal.ofReal
              |LinearMap.det
                (normalization.parent_convex_body.outerJohnEllipsoidMap :
                  Point3 →ₗ[ℝ] Point3)| * unitBallVolume := by
        gcongr
  have hparentVolume :
      volume parent.carrier ≤
        (36 : ENNReal) * Kakeya.realRpowENN rho 2 := by
    have hraw := tube_volume_upper_pi hrho parent
    have hreal :
        Real.pi * rho ^ 2 * (1 + 2 * rho) ≤ 36 * rho ^ 2 := by
      have hpi : Real.pi ≤ 4 := Real.pi_le_four
      have hfactor : Real.pi * (1 + 2 * rho) ≤ 36 := by
        calc
          Real.pi * (1 + 2 * rho) ≤
              4 * (1 + 2 * rho) := by
            gcongr
          _ ≤ 36 := by nlinarith
      calc
        Real.pi * rho ^ 2 * (1 + 2 * rho) =
            rho ^ 2 * (Real.pi * (1 + 2 * rho)) := by ring
        _ ≤ rho ^ 2 * 36 :=
          mul_le_mul_of_nonneg_left hfactor (sq_nonneg rho)
        _ = 36 * rho ^ 2 := by ring
    calc
      volume parent.carrier ≤
          ENNReal.ofReal (Real.pi * rho ^ 2 * (1 + 2 * rho)) :=
        hraw
      _ ≤ ENNReal.ofReal (36 * rho ^ 2) :=
        ENNReal.ofReal_mono hreal
      _ = (36 : ENNReal) * Kakeya.realRpowENN rho 2 := by
        simp [Kakeya.realRpowENN, Real.rpow_two,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 36)]
  calc
    ENNReal.ofReal
        |LinearMap.det
          (normalization.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| ≤
        volume normalization.parent_convex_body.outerJohnEllipsoid :=
      hdetVolume
    _ ≤ (27 : ENNReal) * volume parent.carrier :=
      normalization.outerJohn_volume_le_twentySeven
    _ ≤ (27 : ENNReal) *
          ((36 : ENNReal) * Kakeya.realRpowENN rho 2) := by
      gcongr
    _ = (972 : ENNReal) * Kakeya.realRpowENN rho 2 := by ring

/-- The inverse canonical outer-John chart on a radius-at-most-four parent
loses at most `972 * rho^2` in volume. -/
theorem pureWZ2Proposition64_outerJohn_inverse_volume_le_of_le_four
    {rho : ℝ}
    (hrho : 0 < rho)
    (hrhoFour : rho ≤ 4)
    (parent : Kakeya.DeltaTube rho)
    (normalization : WZ2PaperAssouadUnitRescalingData parent)
    (targetSet : Set Point3) :
    volume (normalization.map.symm '' targetSet) ≤
      (972 : ENNReal) * Kakeya.realRpowENN rho 2 *
        volume targetSet := by
  rw [wz2PaperAffineEquiv_volume_image_eq]
  have hlinear :
      (normalization.map.symm.linear : Point3 →ₗ[ℝ] Point3) =
        normalization.parent_convex_body.outerJohnEllipsoidMap := rfl
  rw [hlinear]
  gcongr
  exact pureWZ2Proposition64_outerJohn_detENN_le_of_le_four
    hrho hrhoFour parent normalization

end Kakeya.Assouad

end
