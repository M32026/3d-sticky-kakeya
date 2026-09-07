import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryEnvelopeJohnTransport

/-!
# Actual-John transport to an arbitrary factor-nineteen parent

The target parent need not be the same-axis envelope of the source parent.
Only its radius is fixed to `19 * sigma`.  Equal-radius ordinary tubes have
equal volume, so the outer-John determinant comparison used for the canonical
envelope remains valid for an arbitrary target axis.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- Coordinate change from one actual parent John chart to an arbitrary
factor-`19` parent John chart. -/
noncomputable def wz2PaperFactorNineteenJohnCoordinateChange
    {sigma : ℝ}
    {sourceParent : Kakeya.DeltaTube sigma}
    {targetParent : Kakeya.DeltaTube (19 * sigma)}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  sourceJohn.map.symm.trans targetJohn.map

@[simp]
theorem wz2PaperFactorNineteenJohnCoordinateChange_apply_map
    {sigma : ℝ}
    {sourceParent : Kakeya.DeltaTube sigma}
    {targetParent : Kakeya.DeltaTube (19 * sigma)}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (point : Point3) :
    wz2PaperFactorNineteenJohnCoordinateChange sourceJohn targetJohn
        (sourceJohn.map point) =
      targetJohn.map point := by
  simp [wz2PaperFactorNineteenJohnCoordinateChange,
    AffineEquiv.trans_apply]

theorem wz2PaperFactorNineteenJohnCoordinateChange_image
    {sigma : ℝ}
    {sourceParent : Kakeya.DeltaTube sigma}
    {targetParent : Kakeya.DeltaTube (19 * sigma)}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (source : Set Point3) :
    wz2PaperFactorNineteenJohnCoordinateChange sourceJohn targetJohn ''
        (sourceJohn.map '' source) =
      targetJohn.map '' source := by
  ext point
  constructor
  · rintro ⟨johnPoint, ⟨sourcePoint, sourceMem, rfl⟩, rfl⟩
    exact
      ⟨sourcePoint, sourceMem,
        (wz2PaperFactorNineteenJohnCoordinateChange_apply_map
          sourceJohn targetJohn sourcePoint).symm⟩
  · rintro ⟨sourcePoint, sourceMem, rfl⟩
    exact
      ⟨sourceJohn.map sourcePoint,
        ⟨sourcePoint, sourceMem, rfl⟩,
        wz2PaperFactorNineteenJohnCoordinateChange_apply_map
          sourceJohn targetJohn sourcePoint⟩

/-- The target outer-John ellipsoid has the same scale-free volume comparison
as the canonical same-axis factor-`19` envelope. -/
theorem wz2PaperFactorNineteen_outerJohn_volume_le
    {sigma : ℝ}
    (hsigma : 0 < sigma)
    (sourceParent : Kakeya.DeltaTube sigma)
    (targetParent : Kakeya.DeltaTube (19 * sigma))
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent) :
    volume targetJohn.parent_convex_body.outerJohnEllipsoid ≤
      (185193 : ENNReal) *
        volume sourceJohn.parent_convex_body.outerJohnEllipsoid := by
  have sourceCarrier :
      sourceParent.carrier ⊆
        sourceJohn.parent_convex_body.outerJohnEllipsoid :=
    sourceJohn.parent_convex_body.outerJohnEllipsoid_spec.1
  have targetVolume :
      volume targetParent.carrier =
        volume (wz2PaperOrdinaryEnvelope sourceParent).carrier := by
    change targetParent.volume =
      (wz2PaperOrdinaryEnvelope sourceParent).volume
    exact Kakeya.Streamlined.tube_volume_eq _ _
  calc
    volume targetJohn.parent_convex_body.outerJohnEllipsoid ≤
        (27 : ENNReal) * volume targetParent.carrier :=
      targetJohn.outerJohn_volume_le_twentySeven
    _ =
        (27 : ENNReal) *
          volume (wz2PaperOrdinaryEnvelope sourceParent).carrier := by
      rw [targetVolume]
    _ ≤
        (27 : ENNReal) *
          volume (wz2PaperCenteredDilatedCarrier 19 sourceParent) := by
      gcongr
      exact
        wz2PaperOrdinaryEnvelope_carrier_subset_centeredDilatedNineteen
          hsigma sourceParent
    _ =
        (185193 : ENNReal) * volume sourceParent.carrier := by
      rw [wz2_paper_centeredDilatedCarrier_volume]
      norm_num
      ring
    _ ≤
        (185193 : ENNReal) *
          volume sourceJohn.parent_convex_body.outerJohnEllipsoid := by
      gcongr

/-- Determinant form of the factor-`19` outer-John comparison. -/
theorem wz2PaperFactorNineteen_outerJohn_abs_det_le
    {sigma : ℝ}
    (hsigma : 0 < sigma)
    (sourceParent : Kakeya.DeltaTube sigma)
    (targetParent : Kakeya.DeltaTube (19 * sigma))
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent) :
    |LinearMap.det
        (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)| ≤
      185193 *
        |LinearMap.det
          (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| := by
  let unitBallVolume : ENNReal :=
    volume (Metric.closedBall (0 : Point3) 1)
  have unitBallPos : 0 < unitBallVolume :=
    Metric.measure_closedBall_pos volume (0 : Point3) (by norm_num)
  have unitBallTop : unitBallVolume ≠ ⊤ :=
    (ProperSpace.isCompact_closedBall (0 : Point3) 1).measure_ne_top
  have ellipsoidVolume :=
    wz2PaperFactorNineteen_outerJohn_volume_le
      hsigma sourceParent targetParent sourceJohn targetJohn
  have targetVolume :
      volume targetJohn.parent_convex_body.outerJohnEllipsoid =
        ENNReal.ofReal
            |LinearMap.det
              (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
                Point3 →ₗ[ℝ] Point3)| *
          unitBallVolume :=
    JohnEllipsoid.volume_ellipsoid_eq
      targetJohn.parent_convex_body.outerJohnEllipsoidCenter
      targetJohn.parent_convex_body.outerJohnEllipsoidMap
  have sourceVolume :
      volume sourceJohn.parent_convex_body.outerJohnEllipsoid =
        ENNReal.ofReal
            |LinearMap.det
              (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
                Point3 →ₗ[ℝ] Point3)| *
          unitBallVolume :=
    JohnEllipsoid.volume_ellipsoid_eq
      sourceJohn.parent_convex_body.outerJohnEllipsoidCenter
      sourceJohn.parent_convex_body.outerJohnEllipsoidMap
  rw [targetVolume, sourceVolume] at ellipsoidVolume
  have rearranged :
      (185193 : ENNReal) *
            (ENNReal.ofReal
                |LinearMap.det
                  (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
                    Point3 →ₗ[ℝ] Point3)| *
              unitBallVolume) =
        ((185193 : ENNReal) *
            ENNReal.ofReal
              |LinearMap.det
                (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
                  Point3 →ₗ[ℝ] Point3)|) *
          unitBallVolume := by
    ring
  rw [rearranged] at ellipsoidVolume
  have determinantENN :
      ENNReal.ofReal
          |LinearMap.det
            (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)| ≤
        (185193 : ENNReal) *
          ENNReal.ofReal
            |LinearMap.det
              (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
                Point3 →ₗ[ℝ] Point3)| :=
    (ENNReal.mul_le_mul_iff_left
      unitBallPos.ne' unitBallTop).1 ellipsoidVolume
  rw [← ENNReal.ofReal_ofNat (n := 185193),
    ← ENNReal.ofReal_mul (by norm_num)] at determinantENN
  exact
    (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (by norm_num) (abs_nonneg _))).1 determinantENN

theorem wz2PaperFactorNineteenJohnCoordinateChange_abs_det
    {sigma : ℝ}
    {sourceParent : Kakeya.DeltaTube sigma}
    {targetParent : Kakeya.DeltaTube (19 * sigma)}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent) :
    |LinearMap.det
        ((wz2PaperFactorNineteenJohnCoordinateChange
          sourceJohn targetJohn).linear :
          Point3 →ₗ[ℝ] Point3)| =
      |LinearMap.det
          (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| *
        |LinearMap.det
          (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)|⁻¹ := by
  have linear :
      (wz2PaperFactorNineteenJohnCoordinateChange
        sourceJohn targetJohn).linear =
        sourceJohn.map.symm.linear.trans targetJohn.map.linear := rfl
  rw [linear]
  have composition :
      (((sourceJohn.map.symm.linear.trans targetJohn.map.linear :
        Point3 ≃ₗ[ℝ] Point3) : Point3 →ₗ[ℝ] Point3)) =
        (targetJohn.map.linear : Point3 →ₗ[ℝ] Point3).comp
          (sourceJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3) := by
    ext point
    rfl
  rw [composition, LinearMap.det_comp, abs_mul]
  have sourceLinear :
      (sourceJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3) =
        sourceJohn.parent_convex_body.outerJohnEllipsoidMap := rfl
  have targetLinear :
      (targetJohn.map.linear : Point3 →ₗ[ℝ] Point3) =
        targetJohn.parent_convex_body.outerJohnEllipsoidMap.symm := rfl
  rw [sourceLinear, targetLinear, LinearEquiv.det_coe_symm, abs_inv]
  ring

/-- The inverse John coordinate change loses only the factor-`19` dimensional
constant, independently of the target axis. -/
theorem wz2PaperFactorNineteenJohnCoordinateChange_inverse_volume
    {sigma : ℝ}
    (hsigma : 0 < sigma)
    (sourceParent : Kakeya.DeltaTube sigma)
    (targetParent : Kakeya.DeltaTube (19 * sigma))
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (targetSet : Set Point3) :
    volume
        ((wz2PaperFactorNineteenJohnCoordinateChange
          sourceJohn targetJohn).symm '' targetSet) ≤
      (185193 : ENNReal) * volume targetSet := by
  let coordinateChange :=
    wz2PaperFactorNineteenJohnCoordinateChange sourceJohn targetJohn
  rw [wz2PaperAffineEquiv_volume_image_eq]
  have targetDet :=
    wz2PaperFactorNineteen_outerJohn_abs_det_le
      hsigma sourceParent targetParent sourceJohn targetJohn
  have sourceDetPos :
      0 <
        |LinearMap.det
          (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr
      (LinearEquiv.isUnit_det'
        sourceJohn.parent_convex_body.outerJohnEllipsoidMap).ne_zero
  have targetDetPos :
      0 <
        |LinearMap.det
          (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr
      (LinearEquiv.isUnit_det'
        targetJohn.parent_convex_body.outerJohnEllipsoidMap).ne_zero
  have coordinateDet :
      (1 / 185193 : ℝ) ≤
        |LinearMap.det
          (coordinateChange.linear : Point3 →ₗ[ℝ] Point3)| := by
    rw [wz2PaperFactorNineteenJohnCoordinateChange_abs_det
      sourceJohn targetJohn]
    apply (le_div_iff₀ targetDetPos).2
    calc
      (1 / 185193 : ℝ) *
            |LinearMap.det
              (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
                Point3 →ₗ[ℝ] Point3)| ≤
          (1 / 185193 : ℝ) *
            (185193 *
              |LinearMap.det
                (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
                  Point3 →ₗ[ℝ] Point3)|) := by
        gcongr
      _ =
          |LinearMap.det
            (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)| := by
        ring
  have coordinateDetPos :
      0 <
        |LinearMap.det
          (coordinateChange.linear : Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr
      (LinearEquiv.isUnit_det' coordinateChange.linear).ne_zero
  have inverse :
      |LinearMap.det
          (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
        185193 := by
    have symmLinear :
        coordinateChange.symm.linear =
          coordinateChange.linear.symm := rfl
    rw [symmLinear, LinearEquiv.det_coe_symm, abs_inv]
    apply (inv_le_iff_one_le_mul₀ coordinateDetPos).2
    nlinarith
  gcongr
  calc
    ENNReal.ofReal
        |LinearMap.det
          (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
        ENNReal.ofReal (185193 : ℝ) :=
      ENNReal.ofReal_mono inverse
    _ = (185193 : ENNReal) := by norm_num

/-- Generic normalized body CWA transport to an arbitrary factor-`19` parent. -/
theorem wz2PaperBodyConvexWolffBound_of_factorNineteenJohnTransport
    {sigma : ℝ}
    (hsigma : 0 < sigma)
    (sourceParent : Kakeya.DeltaTube sigma)
    (targetParent : Kakeya.DeltaTube (19 * sigma))
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    {source target : Kakeya.Streamlined.BodyFamily}
    {C : ENNReal}
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (carrier_containment :
      ∀ targetIndex,
        wz2PaperFactorNineteenJohnCoordinateChange
              sourceJohn targetJohn ''
            (source.body (indexEquiv targetIndex)).carrier ⊆
          (target.body targetIndex).carrier)
    (sourceCWA : WZ2PaperBodyConvexWolffBound source C) :
    WZ2PaperBodyConvexWolffBound
      target ((185193 : ENNReal) * C) := by
  apply
    wz2PaperBodyConvexWolffBound_of_affineTransport
      (wz2PaperFactorNineteenJohnCoordinateChange
        sourceJohn targetJohn)
      indexEquiv carrier_containment
  · intro targetSet
    exact
      wz2PaperFactorNineteenJohnCoordinateChange_inverse_volume
        hsigma sourceParent targetParent sourceJohn targetJohn targetSet
  · exact sourceCWA

end Kakeya.Assouad

end
