import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12BodyReindex
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingBridge
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingJacobian
import MyLeanRepo.Kakeya.Assouad.TubeVolumeRatio

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

noncomputable def wz2PaperNestedJohnCoordinateChange
    {rho sigma : ℝ}
    {sourceParent : Kakeya.DeltaTube rho}
    {anchor : Kakeya.DeltaTube sigma}
    {targetParent : Kakeya.DeltaTube (rho / sigma)}
    (hsigma : 0 < sigma)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  sourceJohn.map.symm.trans
    ((wz2PaperLiteralUnitRescalingAffineEquiv anchor hsigma).trans
      targetJohn.map)

@[simp] theorem wz2PaperNestedJohnCoordinateChange_apply_map
    {rho sigma : ℝ}
    {sourceParent : Kakeya.DeltaTube rho}
    {anchor : Kakeya.DeltaTube sigma}
    {targetParent : Kakeya.DeltaTube (rho / sigma)}
    (hsigma : 0 < sigma)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (point : Point3) :
    wz2PaperNestedJohnCoordinateChange
        (anchor := anchor) hsigma sourceJohn targetJohn
        (sourceJohn.map point) =
      targetJohn.map
        (wz2PaperLiteralUnitRescalingMap anchor hsigma point) := by
  simp [wz2PaperNestedJohnCoordinateChange, AffineEquiv.trans_apply]

theorem wz2PaperNestedJohnCoordinateChange_image
    {rho sigma : ℝ}
    {sourceParent : Kakeya.DeltaTube rho}
    {anchor : Kakeya.DeltaTube sigma}
    {targetParent : Kakeya.DeltaTube (rho / sigma)}
    (hsigma : 0 < sigma)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (source : Set Point3) :
    wz2PaperNestedJohnCoordinateChange
          (anchor := anchor) hsigma sourceJohn targetJohn ''
        (sourceJohn.map '' source) =
      targetJohn.map ''
        (wz2PaperLiteralUnitRescalingMap anchor hsigma '' source) := by
  ext point
  constructor
  · rintro ⟨sourceJohnPoint, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
    exact
      ⟨wz2PaperLiteralUnitRescalingMap anchor hsigma sourcePoint,
        ⟨sourcePoint, hsourcePoint, rfl⟩,
        wz2PaperNestedJohnCoordinateChange_apply_map
          (anchor := anchor) hsigma sourceJohn targetJohn sourcePoint |>.symm⟩
  · rintro ⟨literalPoint, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
    exact
      ⟨sourceJohn.map sourcePoint,
        ⟨sourcePoint, hsourcePoint, rfl⟩,
        wz2PaperNestedJohnCoordinateChange_apply_map
          (anchor := anchor) hsigma sourceJohn targetJohn sourcePoint⟩

theorem wz2PaperBodyConvexWolffBound_of_affineTransport
    {source target : Kakeya.Streamlined.BodyFamily}
    {C inverseVolumeConstant : ENNReal}
    (coordinateChange : Point3 ≃ᵃ[ℝ] Point3)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (carrier_containment :
      ∀ targetIndex,
        coordinateChange ''
            (source.body (indexEquiv targetIndex)).carrier ⊆
          (target.body targetIndex).carrier)
    (inverse_volume :
      ∀ targetSet : Set Point3,
        volume (coordinateChange.symm '' targetSet) ≤
          inverseVolumeConstant * volume targetSet)
    (hsource : WZ2PaperBodyConvexWolffBound source C) :
    WZ2PaperBodyConvexWolffBound
      target (inverseVolumeConstant * C) := by
  apply
    wz2PaperBodyConvexWolffBound_of_indexed_envelope
      indexEquiv
  · intro targetConvexSet htargetConvex
    refine
      ⟨coordinateChange.symm '' targetConvexSet,
        Convex.affine_image coordinateChange.symm.toAffineMap htargetConvex,
        inverse_volume targetConvexSet,
        ?_⟩
    intro targetIndex htargetCarrier point hpoint
    have hcoordinatePoint :
        coordinateChange point ∈ targetConvexSet :=
      htargetCarrier
        (carrier_containment targetIndex ⟨point, hpoint, rfl⟩)
    exact
      ⟨coordinateChange point, hcoordinatePoint,
        coordinateChange.symm_apply_apply point⟩
  · exact hsource

theorem wz2PaperBodyConvexWolffBound_of_nestedCanonicalJohnTransport
    {rho sigma : ℝ}
    {sourceParent : Kakeya.DeltaTube rho}
    {anchor : Kakeya.DeltaTube sigma}
    {targetParent : Kakeya.DeltaTube (rho / sigma)}
    (hsigma : 0 < sigma)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    {source target : Kakeya.Streamlined.BodyFamily}
    {C : ENNReal}
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (carrier_containment :
      ∀ targetIndex,
        wz2PaperNestedJohnCoordinateChange
              (anchor := anchor) hsigma sourceJohn targetJohn ''
            (source.body (indexEquiv targetIndex)).carrier ⊆
          (target.body targetIndex).carrier)
    (inverse_volume :
      ∀ targetSet : Set Point3,
        volume
            ((wz2PaperNestedJohnCoordinateChange
              (anchor := anchor)
              hsigma sourceJohn targetJohn).symm '' targetSet) ≤
          (81000000 : ENNReal) * volume targetSet)
    (hsource : WZ2PaperBodyConvexWolffBound source C) :
    WZ2PaperBodyConvexWolffBound
      target ((81000000 : ENNReal) * C) :=
  wz2PaperBodyConvexWolffBound_of_affineTransport
    (wz2PaperNestedJohnCoordinateChange
      (anchor := anchor) hsigma sourceJohn targetJohn)
    indexEquiv carrier_containment inverse_volume hsource

theorem wz2Paper_outerJohn_volume_le_twentySeven
    {convexBody : Set Point3}
    (hbody : JohnEllipsoid.IsConvexBody convexBody) :
    volume hbody.outerJohnEllipsoid ≤
      (27 : ENNReal) * volume convexBody := by
  let center : Point3 := hbody.outerJohnEllipsoidCenter
  let ellipsoid : Set Point3 := hbody.outerJohnEllipsoid
  have hinner :
      AffineMap.homothety center ((3 : ℝ)⁻¹) '' ellipsoid ⊆
        convexBody :=
    hbody.homothety_subset_outerJohnEllipsoid
  have hinnerVolume :
      ENNReal.ofReal (1 / 27 : ℝ) * volume ellipsoid ≤
        volume convexBody := by
    calc
      ENNReal.ofReal (1 / 27 : ℝ) * volume ellipsoid =
          volume
            (AffineMap.homothety
              center ((3 : ℝ)⁻¹) '' ellipsoid) := by
        rw [JohnEllipsoid.volume_homothety]
        norm_num
      _ ≤ volume convexBody := measure_mono hinner
  have hcancel :
      (27 : ENNReal) * ENNReal.ofReal (1 / 27 : ℝ) = 1 := by
    rw [← ENNReal.ofReal_ofNat (n := 27),
      ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  calc
    volume hbody.outerJohnEllipsoid =
        (27 : ENNReal) *
          (ENNReal.ofReal (1 / 27 : ℝ) * volume ellipsoid) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ (27 : ENNReal) * volume convexBody := by
      gcongr

theorem WZ2PaperAssouadUnitRescalingData.outerJohn_volume_le_twentySeven
    {rho : ℝ}
    {parent : Kakeya.DeltaTube rho}
    (normalization : WZ2PaperAssouadUnitRescalingData parent) :
    volume normalization.parent_convex_body.outerJohnEllipsoid ≤
      (27 : ENNReal) * volume parent.carrier :=
  wz2Paper_outerJohn_volume_le_twentySeven
    normalization.parent_convex_body

/--
Across a nested scale `rho ≤ sigma`, the target outer-John determinant is at
most `81 / sigma²` times the source determinant.

The factor is exactly the product of:

* `27` from the outer-John volume comparison;
* `3 / sigma²` from the ordinary tube-volume ratio.
-/
theorem wz2Paper_nested_outerJohn_abs_det_le
    {rho sigma : ℝ}
    (hrho : 0 < rho)
    (hsigma : 0 < sigma)
    (hrhoSigma : rho ≤ sigma)
    (hsigmaOne : sigma ≤ 1)
    (sourceParent : Kakeya.DeltaTube rho)
    (targetParent : Kakeya.DeltaTube (rho / sigma))
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent) :
    |LinearMap.det
        (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)| ≤
      (81 / sigma ^ 2) *
        |LinearMap.det
          (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| := by
  let unitBallVolume : ENNReal :=
    volume (Metric.closedBall (0 : Point3) 1)
  have hunitBallPos : 0 < unitBallVolume :=
    Metric.measure_closedBall_pos volume (0 : Point3) (by norm_num)
  have hunitBallTop : unitBallVolume ≠ ⊤ :=
    (ProperSpace.isCompact_closedBall (0 : Point3) 1).measure_ne_top
  have htargetScalePos : 0 < rho / sigma :=
    div_pos hrho hsigma
  have hrhoTarget : rho ≤ rho / sigma := by
    apply (le_div_iff₀ hsigma).2
    nlinarith
  have htargetScaleOne : rho / sigma ≤ 1 :=
    (div_le_one hsigma).2 hrhoSigma
  have htargetTubeRatio :
      volume targetParent.carrier ≤
        3 * Kakeya.realRpowENN (rho / sigma) 2 *
            (Kakeya.realRpowENN rho 2)⁻¹ *
          volume sourceParent.carrier := by
    change
      targetParent.volume ≤
        3 * Kakeya.realRpowENN (rho / sigma) 2 *
            (Kakeya.realRpowENN rho 2)⁻¹ *
          sourceParent.volume
    rw [
      Kakeya.Streamlined.tube_volume_eq targetParent
        {
          base := 0
          direction := EuclideanSpace.single (0 : Fin 3) 1
          direction_unit := by simp
        },
      Kakeya.Streamlined.tube_volume_eq sourceParent
        {
          base := 0
          direction := EuclideanSpace.single (0 : Fin 3) 1
          direction_unit := by simp
        }
    ]
    exact
      deltaTubeVolume_ratio_bound_cylinder
        hrho hrhoTarget htargetScaleOne
  have hsourceCarrier :
      sourceParent.carrier ⊆
        sourceJohn.parent_convex_body.outerJohnEllipsoid :=
    sourceJohn.parent_convex_body.outerJohnEllipsoid_spec.1
  have hellipsoidVolume :
      volume targetJohn.parent_convex_body.outerJohnEllipsoid ≤
        (81 : ENNReal) *
          (Kakeya.realRpowENN (rho / sigma) 2 *
            (Kakeya.realRpowENN rho 2)⁻¹) *
          volume sourceJohn.parent_convex_body.outerJohnEllipsoid := by
    calc
      volume targetJohn.parent_convex_body.outerJohnEllipsoid ≤
          (27 : ENNReal) * volume targetParent.carrier :=
        targetJohn.outerJohn_volume_le_twentySeven
      _ ≤
          (27 : ENNReal) *
            (3 * Kakeya.realRpowENN (rho / sigma) 2 *
                (Kakeya.realRpowENN rho 2)⁻¹ *
              volume sourceParent.carrier) := by
        gcongr
      _ ≤
          (27 : ENNReal) *
            (3 * Kakeya.realRpowENN (rho / sigma) 2 *
                (Kakeya.realRpowENN rho 2)⁻¹ *
              volume sourceJohn.parent_convex_body.outerJohnEllipsoid) := by
        gcongr
      _ =
          (81 : ENNReal) *
            (Kakeya.realRpowENN (rho / sigma) 2 *
              (Kakeya.realRpowENN rho 2)⁻¹) *
            volume sourceJohn.parent_convex_body.outerJohnEllipsoid := by
        ring
  have hscaleRatio :
      Kakeya.realRpowENN (rho / sigma) 2 *
          (Kakeya.realRpowENN rho 2)⁻¹ =
        ENNReal.ofReal (1 / sigma ^ 2) := by
    have hquotient :
        (rho / sigma) ^ 2 / rho ^ 2 = 1 / sigma ^ 2 := by
      field_simp [hrho.ne', hsigma.ne']
    rw [show
      Kakeya.realRpowENN (rho / sigma) 2 =
        ENNReal.ofReal ((rho / sigma) ^ 2) by
          simp [Kakeya.realRpowENN, Real.rpow_two]]
    rw [show
      Kakeya.realRpowENN rho 2 =
        ENNReal.ofReal (rho ^ 2) by
          simp [Kakeya.realRpowENN, Real.rpow_two]]
    rw [← ENNReal.ofReal_inv_of_pos (sq_pos_of_pos hrho)]
    rw [← ENNReal.ofReal_mul (sq_nonneg (rho / sigma))]
    rw [show (rho / sigma) ^ 2 * (rho ^ 2)⁻¹ =
      (rho / sigma) ^ 2 / rho ^ 2 by ring]
    rw [hquotient]
  have hdetENN :
      ENNReal.ofReal
          |LinearMap.det
            (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)| ≤
        ENNReal.ofReal (81 / sigma ^ 2) *
          ENNReal.ofReal
            |LinearMap.det
              (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
                Point3 →ₗ[ℝ] Point3)| := by
    have htargetVolume :
        volume targetJohn.parent_convex_body.outerJohnEllipsoid =
          ENNReal.ofReal
              |LinearMap.det
                (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
                  Point3 →ₗ[ℝ] Point3)| *
            unitBallVolume := by
      exact
        JohnEllipsoid.volume_ellipsoid_eq
          targetJohn.parent_convex_body.outerJohnEllipsoidCenter
          targetJohn.parent_convex_body.outerJohnEllipsoidMap
    have hsourceVolume :
        volume sourceJohn.parent_convex_body.outerJohnEllipsoid =
          ENNReal.ofReal
              |LinearMap.det
                (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
                  Point3 →ₗ[ℝ] Point3)| *
            unitBallVolume := by
      exact
        JohnEllipsoid.volume_ellipsoid_eq
          sourceJohn.parent_convex_body.outerJohnEllipsoidCenter
          sourceJohn.parent_convex_body.outerJohnEllipsoidMap
    rw [htargetVolume, hsourceVolume, hscaleRatio] at hellipsoidVolume
    have hcoefficient :
        (81 : ENNReal) * ENNReal.ofReal (1 / sigma ^ 2) =
          ENNReal.ofReal (81 / sigma ^ 2) := by
      rw [← ENNReal.ofReal_ofNat (n := 81),
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    rw [hcoefficient] at hellipsoidVolume
    have hrearranged :
        ENNReal.ofReal (81 / sigma ^ 2) *
              (ENNReal.ofReal
                  |LinearMap.det
                    (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
                      Point3 →ₗ[ℝ] Point3)| *
                unitBallVolume) =
          (ENNReal.ofReal (81 / sigma ^ 2) *
              ENNReal.ofReal
                |LinearMap.det
                  (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
                    Point3 →ₗ[ℝ] Point3)|) *
            unitBallVolume := by ring
    rw [hrearranged] at hellipsoidVolume
    exact
      (ENNReal.mul_le_mul_iff_left
        hunitBallPos.ne' hunitBallTop).1 hellipsoidVolume
  rw [← ENNReal.ofReal_mul (by positivity)] at hdetENN
  exact
    (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (by positivity) (abs_nonneg _))).1 hdetENN

/-- Exact determinant of the canonical nested John-to-John coordinate
change. -/
theorem wz2PaperNestedJohnCoordinateChange_abs_det
    {rho sigma : ℝ}
    {sourceParent : Kakeya.DeltaTube rho}
    {anchor : Kakeya.DeltaTube sigma}
    {targetParent : Kakeya.DeltaTube (rho / sigma)}
    (hsigma : 0 < sigma)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent) :
    |LinearMap.det
        ((wz2PaperNestedJohnCoordinateChange
          (anchor := anchor) hsigma sourceJohn targetJohn).linear :
          Point3 →ₗ[ℝ] Point3)| =
      |LinearMap.det
          (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| *
        ((1 / 100 : ℝ) ^ 3 * (1 / sigma) ^ 2) *
        |LinearMap.det
          (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)|⁻¹ := by
  let literal :=
    wz2PaperLiteralUnitRescalingAffineEquiv anchor hsigma
  have hlinear :
      (wz2PaperNestedJohnCoordinateChange
        (anchor := anchor) hsigma sourceJohn targetJohn).linear =
        (sourceJohn.map.symm.linear.trans literal.linear).trans
          targetJohn.map.linear := rfl
  rw [hlinear]
  have hcomposition :
      ((((sourceJohn.map.symm.linear.trans literal.linear).trans
        targetJohn.map.linear : Point3 ≃ₗ[ℝ] Point3) :
          Point3 →ₗ[ℝ] Point3)) =
        (targetJohn.map.linear : Point3 →ₗ[ℝ] Point3).comp
          ((literal.linear : Point3 →ₗ[ℝ] Point3).comp
            (sourceJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3)) := by
    ext point
    rfl
  rw [hcomposition, LinearMap.det_comp, LinearMap.det_comp,
    abs_mul, abs_mul]
  have hsource :
      (sourceJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3) =
        sourceJohn.parent_convex_body.outerJohnEllipsoidMap := rfl
  have htarget :
      (targetJohn.map.linear : Point3 →ₗ[ℝ] Point3) =
        targetJohn.parent_convex_body.outerJohnEllipsoidMap.symm := rfl
  rw [hsource, htarget, LinearEquiv.det_coe_symm, abs_inv,
    wz2PaperLiteralUnitRescalingAffineEquiv_abs_det anchor hsigma]
  ring

/-- The inverse nested canonical John coordinate change loses at most the
dimension-only factor `81_000_000` in volume. -/
theorem wz2PaperNestedJohnCoordinateChange_inverse_volume
    {rho sigma : ℝ}
    {sourceParent : Kakeya.DeltaTube rho}
    {anchor : Kakeya.DeltaTube sigma}
    {targetParent : Kakeya.DeltaTube (rho / sigma)}
    (hrho : 0 < rho)
    (hsigma : 0 < sigma)
    (hrhoSigma : rho ≤ sigma)
    (hsigmaOne : sigma ≤ 1)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (targetSet : Set Point3) :
    volume
        ((wz2PaperNestedJohnCoordinateChange
          (anchor := anchor) hsigma sourceJohn targetJohn).symm ''
          targetSet) ≤
      (81000000 : ENNReal) * volume targetSet := by
  let coordinateChange :=
    wz2PaperNestedJohnCoordinateChange
      (anchor := anchor) hsigma sourceJohn targetJohn
  rw [wz2PaperAffineEquiv_volume_image_eq]
  have htargetDet :=
    wz2Paper_nested_outerJohn_abs_det_le
      hrho hsigma hrhoSigma hsigmaOne
      sourceParent targetParent sourceJohn targetJohn
  have hsourceDetPos :
      0 <
        |LinearMap.det
          (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr
      (LinearEquiv.isUnit_det'
        sourceJohn.parent_convex_body.outerJohnEllipsoidMap).ne_zero
  have htargetDetPos :
      0 <
        |LinearMap.det
          (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr
      (LinearEquiv.isUnit_det'
        targetJohn.parent_convex_body.outerJohnEllipsoidMap).ne_zero
  have hcoordinateDet :
      (1 / 81000000 : ℝ) ≤
        |LinearMap.det
          (coordinateChange.linear : Point3 →ₗ[ℝ] Point3)| := by
    rw [wz2PaperNestedJohnCoordinateChange_abs_det
      (anchor := anchor) hsigma sourceJohn targetJohn]
    apply (le_div_iff₀ htargetDetPos).2
    calc
      (1 / 81000000 : ℝ) *
            |LinearMap.det
              (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
                Point3 →ₗ[ℝ] Point3)| ≤
          (1 / 81000000 : ℝ) *
            ((81 / sigma ^ 2) *
              |LinearMap.det
                (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
                  Point3 →ₗ[ℝ] Point3)|) := by
        gcongr
      _ =
          |LinearMap.det
              (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
                Point3 →ₗ[ℝ] Point3)| *
            ((1 / 100 : ℝ) ^ 3 * (1 / sigma) ^ 2) := by
        field_simp [hsigma.ne']
        ring
  have hcoordinateDetPos :
      0 <
        |LinearMap.det
          (coordinateChange.linear : Point3 →ₗ[ℝ] Point3)| := by
    exact
      abs_pos.mpr
        (LinearEquiv.isUnit_det' coordinateChange.linear).ne_zero
  have hinverse :
      |LinearMap.det
          (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
        81000000 := by
    have hsymm :
        coordinateChange.symm.linear =
          coordinateChange.linear.symm := rfl
    rw [hsymm, LinearEquiv.det_coe_symm, abs_inv]
    apply (inv_le_iff_one_le_mul₀ hcoordinateDetPos).2
    nlinarith
  have hENN :
      ENNReal.ofReal
          |LinearMap.det
            (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
        (81000000 : ENNReal) := by
    calc
      ENNReal.ofReal
          |LinearMap.det
            (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
          ENNReal.ofReal (81000000 : ℝ) :=
        ENNReal.ofReal_mono hinverse
      _ = (81000000 : ENNReal) := by norm_num
  gcongr

end Kakeya.Assouad

end
