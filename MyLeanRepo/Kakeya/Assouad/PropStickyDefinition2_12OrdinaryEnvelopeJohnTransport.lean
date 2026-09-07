import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryEnvelopeContainment
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12NestedJohnCWATransport

/-!
# Direct outer-John transport to an ordinary radius-19 envelope

The ordinary envelope keeps the source tube's unit axis segment and replaces
its radius `sigma` by `19 * sigma`.  This module compares the canonical
outer-John normalizations of the source tube and that envelope directly.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- The direct coordinate change between the canonical outer-John charts of
an ordinary tube and its radius-`19` envelope. -/
noncomputable def wz2PaperOrdinaryEnvelopeJohnCoordinateChange
    {sigma : ℝ}
    {sourceParent : Kakeya.DeltaTube sigma}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn :
      WZ2PaperAssouadUnitRescalingData
        (wz2PaperOrdinaryEnvelope sourceParent)) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  sourceJohn.map.symm.trans targetJohn.map

@[simp] theorem wz2PaperOrdinaryEnvelopeJohnCoordinateChange_apply_map
    {sigma : ℝ}
    {sourceParent : Kakeya.DeltaTube sigma}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn :
      WZ2PaperAssouadUnitRescalingData
        (wz2PaperOrdinaryEnvelope sourceParent))
    (point : Point3) :
    wz2PaperOrdinaryEnvelopeJohnCoordinateChange sourceJohn targetJohn
        (sourceJohn.map point) =
      targetJohn.map point := by
  simp [wz2PaperOrdinaryEnvelopeJohnCoordinateChange,
    AffineEquiv.trans_apply]

/-- The direct John coordinate change carries the source John image of every
physical set exactly to its target John image. -/
theorem wz2PaperOrdinaryEnvelopeJohnCoordinateChange_image
    {sigma : ℝ}
    {sourceParent : Kakeya.DeltaTube sigma}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn :
      WZ2PaperAssouadUnitRescalingData
        (wz2PaperOrdinaryEnvelope sourceParent))
    (physicalSet : Set Point3) :
    wz2PaperOrdinaryEnvelopeJohnCoordinateChange sourceJohn targetJohn ''
        (sourceJohn.map '' physicalSet) =
      targetJohn.map '' physicalSet := by
  ext point
  constructor
  · rintro ⟨sourceJohnPoint, ⟨physicalPoint, hphysicalPoint, rfl⟩, rfl⟩
    exact
      ⟨physicalPoint, hphysicalPoint,
        wz2PaperOrdinaryEnvelopeJohnCoordinateChange_apply_map
          sourceJohn targetJohn physicalPoint |>.symm⟩
  · rintro ⟨physicalPoint, hphysicalPoint, rfl⟩
    exact
      ⟨sourceJohn.map physicalPoint,
        ⟨physicalPoint, hphysicalPoint, rfl⟩,
        wz2PaperOrdinaryEnvelopeJohnCoordinateChange_apply_map
          sourceJohn targetJohn physicalPoint⟩

/-- The radius-`19 * sigma` envelope is contained in the factor-`19`
homothety of the radius-`sigma` source carrier about their common midpoint. -/
theorem wz2PaperOrdinaryEnvelope_carrier_subset_centeredDilatedNineteen
    {sigma : ℝ}
    (hsigma : 0 < sigma)
    (sourceParent : Kakeya.DeltaTube sigma) :
    (wz2PaperOrdinaryEnvelope sourceParent).carrier ⊆
      wz2PaperCenteredDilatedCarrier 19 sourceParent := by
  let center := wz2PaperTubeMidpoint sourceParent
  have hsegmentCompact :
      IsCompact
        (Kakeya.unitSegment sourceParent.base sourceParent.direction) :=
    isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  intro point hpoint
  change point ∈
    Metric.cthickening (19 * sigma)
      (Kakeya.unitSegment sourceParent.base sourceParent.direction) at hpoint
  rw [hsegmentCompact.cthickening_eq_biUnion_closedBall
    (by positivity)] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint with
    ⟨axisPoint, haxisPoint, hpointAxis⟩
  rcases haxisPoint with ⟨parameter, hparameter, haxisPoint⟩
  let contractedParameter : ℝ :=
    1 / 2 + (parameter - 1 / 2) / 19
  let contractedAxisPoint : Point3 :=
    sourceParent.base +
      contractedParameter • sourceParent.direction
  let contractedPoint : Point3 :=
    center + (1 / 19 : ℝ) • (point - center)
  have hcontractedParameter :
      contractedParameter ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;>
      dsimp only [contractedParameter] <;>
      linarith [hparameter.1, hparameter.2]
  have hcontractedAxisPoint :
      contractedAxisPoint ∈
        Kakeya.unitSegment sourceParent.base sourceParent.direction :=
    ⟨contractedParameter, hcontractedParameter, rfl⟩
  have hcontractedAxisPoint_eq :
      contractedAxisPoint =
        center + (1 / 19 : ℝ) • (axisPoint - center) := by
    rw [← haxisPoint]
    dsimp only [contractedAxisPoint, contractedParameter, center]
    simp only [wz2PaperTubeMidpoint]
    module
  have hpointAxisDistance :
      dist point axisPoint ≤ 19 * sigma := by
    simpa [Metric.mem_closedBall] using hpointAxis
  have hcontractedDistance :
      dist contractedPoint contractedAxisPoint ≤ sigma := by
    rw [hcontractedAxisPoint_eq]
    calc
      dist contractedPoint
          (center + (1 / 19 : ℝ) • (axisPoint - center)) =
          (1 / 19 : ℝ) * dist point axisPoint := by
        rw [dist_eq_norm, dist_eq_norm]
        have hdifference :
            contractedPoint -
                (center + (1 / 19 : ℝ) • (axisPoint - center)) =
              (1 / 19 : ℝ) • (point - axisPoint) := by
          dsimp only [contractedPoint]
          module
        rw [hdifference, norm_smul, Real.norm_eq_abs]
        norm_num
      _ ≤ (1 / 19 : ℝ) * (19 * sigma) :=
        mul_le_mul_of_nonneg_left hpointAxisDistance (by norm_num)
      _ = sigma := by ring
  have hcontractedCarrier :
      contractedPoint ∈ sourceParent.carrier :=
    Metric.mem_cthickening_of_dist_le
      contractedPoint contractedAxisPoint sigma
      (Kakeya.unitSegment sourceParent.base sourceParent.direction)
      hcontractedAxisPoint hcontractedDistance
  refine ⟨contractedPoint, hcontractedCarrier, ?_⟩
  simp only [AffineMap.homothety_apply]
  ext coordinate
  simp [contractedPoint, center, wz2PaperTubeMidpoint]

/-- The envelope outer-John ellipsoid has at most
`27 * 19^3 = 185193` times the volume of the source outer-John ellipsoid. -/
theorem wz2PaperOrdinaryEnvelope_outerJohn_volume_le
    {sigma : ℝ}
    (hsigma : 0 < sigma)
    (sourceParent : Kakeya.DeltaTube sigma)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn :
      WZ2PaperAssouadUnitRescalingData
        (wz2PaperOrdinaryEnvelope sourceParent)) :
    volume targetJohn.parent_convex_body.outerJohnEllipsoid ≤
      (185193 : ENNReal) *
        volume sourceJohn.parent_convex_body.outerJohnEllipsoid := by
  have hsourceCarrier :
      sourceParent.carrier ⊆
        sourceJohn.parent_convex_body.outerJohnEllipsoid :=
    sourceJohn.parent_convex_body.outerJohnEllipsoid_spec.1
  calc
    volume targetJohn.parent_convex_body.outerJohnEllipsoid ≤
        (27 : ENNReal) *
          volume (wz2PaperOrdinaryEnvelope sourceParent).carrier :=
      targetJohn.outerJohn_volume_le_twentySeven
    _ ≤
        (27 : ENNReal) *
          volume (wz2PaperCenteredDilatedCarrier 19 sourceParent) := by
      apply mul_le_mul_left'
      exact
        MeasureTheory.measure_mono
          (wz2PaperOrdinaryEnvelope_carrier_subset_centeredDilatedNineteen
            hsigma sourceParent)
    _ =
        (185193 : ENNReal) * volume sourceParent.carrier := by
      rw [wz2_paper_centeredDilatedCarrier_volume]
      norm_num
      ring
    _ ≤
        (185193 : ENNReal) *
          volume sourceJohn.parent_convex_body.outerJohnEllipsoid := by
      apply mul_le_mul_left'
      exact MeasureTheory.measure_mono hsourceCarrier

/-- The target outer-John determinant is at most
`185193` times the source outer-John determinant. -/
theorem wz2PaperOrdinaryEnvelope_outerJohn_abs_det_le
    {sigma : ℝ}
    (hsigma : 0 < sigma)
    (sourceParent : Kakeya.DeltaTube sigma)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn :
      WZ2PaperAssouadUnitRescalingData
        (wz2PaperOrdinaryEnvelope sourceParent)) :
    |LinearMap.det
        (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)| ≤
      185193 *
        |LinearMap.det
          (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| := by
  let unitBallVolume : ENNReal :=
    volume (Metric.closedBall (0 : Point3) 1)
  have hunitBallPos : 0 < unitBallVolume :=
    Metric.measure_closedBall_pos volume (0 : Point3) (by norm_num)
  have hunitBallTop : unitBallVolume ≠ ⊤ :=
    (ProperSpace.isCompact_closedBall (0 : Point3) 1).measure_ne_top
  have hellipsoidVolume :=
    wz2PaperOrdinaryEnvelope_outerJohn_volume_le
      hsigma sourceParent sourceJohn targetJohn
  have htargetVolume :
      volume targetJohn.parent_convex_body.outerJohnEllipsoid =
        ENNReal.ofReal
            |LinearMap.det
              (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
                Point3 →ₗ[ℝ] Point3)| *
          unitBallVolume :=
    JohnEllipsoid.volume_ellipsoid_eq
      targetJohn.parent_convex_body.outerJohnEllipsoidCenter
      targetJohn.parent_convex_body.outerJohnEllipsoidMap
  have hsourceVolume :
      volume sourceJohn.parent_convex_body.outerJohnEllipsoid =
        ENNReal.ofReal
            |LinearMap.det
              (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
                Point3 →ₗ[ℝ] Point3)| *
          unitBallVolume :=
    JohnEllipsoid.volume_ellipsoid_eq
      sourceJohn.parent_convex_body.outerJohnEllipsoidCenter
      sourceJohn.parent_convex_body.outerJohnEllipsoidMap
  rw [htargetVolume, hsourceVolume] at hellipsoidVolume
  have hrearranged :
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
  rw [hrearranged] at hellipsoidVolume
  have hdetENN :
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
      hunitBallPos.ne' hunitBallTop).1 hellipsoidVolume
  rw [← ENNReal.ofReal_ofNat (n := 185193),
    ← ENNReal.ofReal_mul (by norm_num)] at hdetENN
  exact
    (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (by norm_num) (abs_nonneg _))).1 hdetENN

/-- Exact determinant of the direct source-John to envelope-John coordinate
change. -/
theorem wz2PaperOrdinaryEnvelopeJohnCoordinateChange_abs_det
    {sigma : ℝ}
    {sourceParent : Kakeya.DeltaTube sigma}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn :
      WZ2PaperAssouadUnitRescalingData
        (wz2PaperOrdinaryEnvelope sourceParent)) :
    |LinearMap.det
        ((wz2PaperOrdinaryEnvelopeJohnCoordinateChange
          sourceJohn targetJohn).linear :
          Point3 →ₗ[ℝ] Point3)| =
      |LinearMap.det
          (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| *
        |LinearMap.det
          (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)|⁻¹ := by
  have hlinear :
      (wz2PaperOrdinaryEnvelopeJohnCoordinateChange
        sourceJohn targetJohn).linear =
        sourceJohn.map.symm.linear.trans targetJohn.map.linear := rfl
  rw [hlinear]
  have hcomposition :
      (((sourceJohn.map.symm.linear.trans targetJohn.map.linear :
        Point3 ≃ₗ[ℝ] Point3) : Point3 →ₗ[ℝ] Point3)) =
        (targetJohn.map.linear : Point3 →ₗ[ℝ] Point3).comp
          (sourceJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3) := by
    ext point
    rfl
  rw [hcomposition, LinearMap.det_comp, abs_mul]
  have hsource :
      (sourceJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3) =
        sourceJohn.parent_convex_body.outerJohnEllipsoidMap := rfl
  have htarget :
      (targetJohn.map.linear : Point3 →ₗ[ℝ] Point3) =
        targetJohn.parent_convex_body.outerJohnEllipsoidMap.symm := rfl
  rw [hsource, htarget, LinearEquiv.det_coe_symm, abs_inv]
  ring

/-- The inverse direct John coordinate change loses at most the scale-free
factor `185193` in volume. -/
theorem wz2PaperOrdinaryEnvelopeJohnCoordinateChange_inverse_volume
    {sigma : ℝ}
    (hsigma : 0 < sigma)
    (sourceParent : Kakeya.DeltaTube sigma)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn :
      WZ2PaperAssouadUnitRescalingData
        (wz2PaperOrdinaryEnvelope sourceParent))
    (targetSet : Set Point3) :
    volume
        ((wz2PaperOrdinaryEnvelopeJohnCoordinateChange
          sourceJohn targetJohn).symm '' targetSet) ≤
      (185193 : ENNReal) * volume targetSet := by
  let coordinateChange :=
    wz2PaperOrdinaryEnvelopeJohnCoordinateChange sourceJohn targetJohn
  rw [wz2PaperAffineEquiv_volume_image_eq]
  have htargetDet :=
    wz2PaperOrdinaryEnvelope_outerJohn_abs_det_le
      hsigma sourceParent sourceJohn targetJohn
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
      (1 / 185193 : ℝ) ≤
        |LinearMap.det
          (coordinateChange.linear : Point3 →ₗ[ℝ] Point3)| := by
    rw [wz2PaperOrdinaryEnvelopeJohnCoordinateChange_abs_det
      sourceJohn targetJohn]
    apply (le_div_iff₀ htargetDetPos).2
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
  have hcoordinateDetPos :
      0 <
        |LinearMap.det
          (coordinateChange.linear : Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr
      (LinearEquiv.isUnit_det' coordinateChange.linear).ne_zero
  have hinverse :
      |LinearMap.det
          (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
        185193 := by
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
        (185193 : ENNReal) := by
    calc
      ENNReal.ofReal
          |LinearMap.det
            (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
          ENNReal.ofReal (185193 : ℝ) :=
        ENNReal.ofReal_mono hinverse
      _ = (185193 : ENNReal) := by norm_num
  gcongr

/-- Generic normalized BodyFamily Convex-Wolff transport through the direct
source-John to ordinary-envelope-John coordinate change. -/
theorem wz2PaperBodyConvexWolffBound_of_ordinaryEnvelopeJohnTransport
    {sigma : ℝ}
    (hsigma : 0 < sigma)
    (sourceParent : Kakeya.DeltaTube sigma)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn :
      WZ2PaperAssouadUnitRescalingData
        (wz2PaperOrdinaryEnvelope sourceParent))
    {source target : Kakeya.Streamlined.BodyFamily}
    {C : ENNReal}
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (carrier_containment :
      ∀ targetIndex,
        wz2PaperOrdinaryEnvelopeJohnCoordinateChange
              sourceJohn targetJohn ''
            (source.body (indexEquiv targetIndex)).carrier ⊆
          (target.body targetIndex).carrier)
    (hsource : WZ2PaperBodyConvexWolffBound source C) :
    WZ2PaperBodyConvexWolffBound
      target ((185193 : ENNReal) * C) := by
  apply
    wz2PaperBodyConvexWolffBound_of_affineTransport
      (wz2PaperOrdinaryEnvelopeJohnCoordinateChange
        sourceJohn targetJohn)
      indexEquiv carrier_containment
  · intro targetSet
    exact
      wz2PaperOrdinaryEnvelopeJohnCoordinateChange_inverse_volume
        hsigma sourceParent sourceJohn targetJohn targetSet
  · exact hsource

end Kakeya.Assouad

end
