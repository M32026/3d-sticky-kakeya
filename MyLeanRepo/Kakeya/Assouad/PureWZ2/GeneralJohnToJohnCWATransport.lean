import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12NestedJohnCWATransport
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryEnvelopeContainment

/-!
# General outer-John to outer-John CWA transport

This module transports a body-family Convex Wolff bound between the canonical
outer-John charts of two arbitrary positive-scale parent tubes.  The loss is
the supplied outer-John ellipsoid volume ratio; no relation between the two
parent scales is required.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

noncomputable def wz2PaperGeneralJohnToJohnCoordinateChange
    {sourceScale targetScale : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceScale}
    {targetParent : Kakeya.DeltaTube targetScale}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  sourceJohn.map.symm.trans targetJohn.map

@[simp]
theorem wz2PaperGeneralJohnToJohnCoordinateChange_apply_map
    {sourceScale targetScale : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceScale}
    {targetParent : Kakeya.DeltaTube targetScale}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (point : Point3) :
    wz2PaperGeneralJohnToJohnCoordinateChange sourceJohn targetJohn
        (sourceJohn.map point) =
      targetJohn.map point := by
  simp [wz2PaperGeneralJohnToJohnCoordinateChange,
    AffineEquiv.trans_apply]

theorem wz2PaperGeneralJohnToJohnCoordinateChange_image
    {sourceScale targetScale : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceScale}
    {targetParent : Kakeya.DeltaTube targetScale}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (source : Set Point3) :
    wz2PaperGeneralJohnToJohnCoordinateChange sourceJohn targetJohn ''
        (sourceJohn.map '' source) =
      targetJohn.map '' source := by
  ext point
  constructor
  · rintro ⟨sourceJohnPoint, ⟨sourcePoint, sourceMem, rfl⟩, rfl⟩
    exact
      ⟨sourcePoint, sourceMem,
        (wz2PaperGeneralJohnToJohnCoordinateChange_apply_map
          sourceJohn targetJohn sourcePoint).symm⟩
  · rintro ⟨sourcePoint, sourceMem, rfl⟩
    exact
      ⟨sourceJohn.map sourcePoint,
        ⟨sourcePoint, sourceMem, rfl⟩,
        wz2PaperGeneralJohnToJohnCoordinateChange_apply_map
          sourceJohn targetJohn sourcePoint⟩

theorem wz2PaperGeneralJohnToJohnCoordinateChange_symm_abs_det
    {sourceScale targetScale : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceScale}
    {targetParent : Kakeya.DeltaTube targetScale}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent) :
    |LinearMap.det
        ((wz2PaperGeneralJohnToJohnCoordinateChange
          sourceJohn targetJohn).symm.linear :
          Point3 →ₗ[ℝ] Point3)| =
      |LinearMap.det
          (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| *
        |LinearMap.det
          (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)|⁻¹ := by
  let coordinateChange :=
    wz2PaperGeneralJohnToJohnCoordinateChange sourceJohn targetJohn
  have symmLinear :
      coordinateChange.symm.linear =
        targetJohn.map.symm.linear.trans sourceJohn.map.linear := rfl
  rw [symmLinear]
  have composition :
      (((targetJohn.map.symm.linear.trans sourceJohn.map.linear :
        Point3 ≃ₗ[ℝ] Point3) : Point3 →ₗ[ℝ] Point3)) =
        (sourceJohn.map.linear : Point3 →ₗ[ℝ] Point3).comp
          (targetJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3) := by
    ext point
    rfl
  rw [composition, LinearMap.det_comp, abs_mul]
  have targetLinear :
      (targetJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3) =
        targetJohn.parent_convex_body.outerJohnEllipsoidMap := rfl
  have sourceLinear :
      (sourceJohn.map.linear : Point3 →ₗ[ℝ] Point3) =
        sourceJohn.parent_convex_body.outerJohnEllipsoidMap.symm := rfl
  rw [targetLinear, sourceLinear, LinearEquiv.det_coe_symm, abs_inv]
  ring

theorem wz2PaperGeneralJohnToJohnCoordinateChange_inverse_volume
    {sourceScale targetScale : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceScale}
    {targetParent : Kakeya.DeltaTube targetScale}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (K : ENNReal)
    (_K_ne_top : K ≠ ⊤)
    (outerJohnVolume_le :
      volume targetJohn.parent_convex_body.outerJohnEllipsoid ≤
        K * volume sourceJohn.parent_convex_body.outerJohnEllipsoid)
    (targetSet : Set Point3) :
    volume
        ((wz2PaperGeneralJohnToJohnCoordinateChange
          sourceJohn targetJohn).symm '' targetSet) ≤
      K * volume targetSet := by
  let unitBallVolume : ENNReal :=
    volume (Metric.closedBall (0 : Point3) 1)
  let sourceDet : ENNReal :=
    ENNReal.ofReal
      |LinearMap.det
        (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)|
  let targetDet : ENNReal :=
    ENNReal.ofReal
      |LinearMap.det
        (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)|
  have unitBallPos : 0 < unitBallVolume :=
    Metric.measure_closedBall_pos volume (0 : Point3) (by norm_num)
  have unitBallTop : unitBallVolume ≠ ⊤ :=
    (ProperSpace.isCompact_closedBall (0 : Point3) 1).measure_ne_top
  have sourceDetRealPos :
      0 <
        |LinearMap.det
          (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr
      (LinearEquiv.isUnit_det'
        sourceJohn.parent_convex_body.outerJohnEllipsoidMap).ne_zero
  have sourceDetPos : 0 < sourceDet :=
    ENNReal.ofReal_pos.mpr sourceDetRealPos
  have sourceDetTop : sourceDet ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have targetVolume :
      volume targetJohn.parent_convex_body.outerJohnEllipsoid =
        targetDet * unitBallVolume :=
    JohnEllipsoid.volume_ellipsoid_eq
      targetJohn.parent_convex_body.outerJohnEllipsoidCenter
      targetJohn.parent_convex_body.outerJohnEllipsoidMap
  have sourceVolume :
      volume sourceJohn.parent_convex_body.outerJohnEllipsoid =
        sourceDet * unitBallVolume :=
    JohnEllipsoid.volume_ellipsoid_eq
      sourceJohn.parent_convex_body.outerJohnEllipsoidCenter
      sourceJohn.parent_convex_body.outerJohnEllipsoidMap
  have determinantBound :
      targetDet ≤ K * sourceDet := by
    rw [targetVolume, sourceVolume] at outerJohnVolume_le
    apply
      (ENNReal.mul_le_mul_iff_left
        unitBallPos.ne' unitBallTop).mp
    simpa [mul_assoc] using outerJohnVolume_le
  have inverseDetBound :
      targetDet * sourceDet⁻¹ ≤ K := by
    calc
      targetDet * sourceDet⁻¹ ≤
          (K * sourceDet) * sourceDet⁻¹ := by
        gcongr
      _ = K := by
        rw [mul_assoc,
          ENNReal.mul_inv_cancel sourceDetPos.ne' sourceDetTop,
          mul_one]
  rw [wz2PaperAffineEquiv_volume_image_eq]
  have determinantIdentity :
      ENNReal.ofReal
          |LinearMap.det
            ((wz2PaperGeneralJohnToJohnCoordinateChange
              sourceJohn targetJohn).symm.linear :
              Point3 →ₗ[ℝ] Point3)| =
        targetDet * sourceDet⁻¹ := by
    rw [
      wz2PaperGeneralJohnToJohnCoordinateChange_symm_abs_det
        sourceJohn targetJohn,
      ENNReal.ofReal_mul (abs_nonneg _),
      ENNReal.ofReal_inv_of_pos sourceDetRealPos
    ]
  rw [determinantIdentity]
  gcongr

theorem wz2PaperBodyConvexWolffBound_of_generalJohnToJohnTransport
    {sourceScale targetScale : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceScale}
    {targetParent : Kakeya.DeltaTube targetScale}
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    {source target : Kakeya.Streamlined.BodyFamily}
    {C K : ENNReal}
    (K_ne_top : K ≠ ⊤)
    (outerJohnVolume_le :
      volume targetJohn.parent_convex_body.outerJohnEllipsoid ≤
        K * volume sourceJohn.parent_convex_body.outerJohnEllipsoid)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (carrier_containment :
      ∀ targetIndex,
        wz2PaperGeneralJohnToJohnCoordinateChange
              sourceJohn targetJohn ''
            (source.body (indexEquiv targetIndex)).carrier ⊆
          (target.body targetIndex).carrier)
    (sourceCWA : WZ2PaperBodyConvexWolffBound source C) :
    WZ2PaperBodyConvexWolffBound target (K * C) := by
  apply
    wz2PaperBodyConvexWolffBound_of_affineTransport
      (wz2PaperGeneralJohnToJohnCoordinateChange
        sourceJohn targetJohn)
      indexEquiv carrier_containment
  · exact
      wz2PaperGeneralJohnToJohnCoordinateChange_inverse_volume
        sourceJohn targetJohn K K_ne_top outerJohnVolume_le
  · exact sourceCWA

theorem wz2PaperOrdinaryRadiusRelabel_carrier_subset_centeredDilated
    {sourceScale factor : ℝ}
    (sourceScalePos : 0 < sourceScale)
    (factorOne : 1 ≤ factor)
    (sourceParent : Kakeya.DeltaTube sourceScale) :
    (wz2PaperOrdinaryRadiusRelabel
        (factor * sourceScale) sourceParent).carrier ⊆
      wz2PaperCenteredDilatedCarrier factor sourceParent := by
  have factorPos : 0 < factor := zero_lt_one.trans_le factorOne
  let center := wz2PaperTubeMidpoint sourceParent
  have segmentCompact :
      IsCompact
        (Kakeya.unitSegment sourceParent.base sourceParent.direction) := by
    apply IsCompact.image isCompact_Icc
    fun_prop
  intro point pointMem
  change
    point ∈
      Metric.cthickening (factor * sourceScale)
        (Kakeya.unitSegment
          sourceParent.base sourceParent.direction) at pointMem
  rw [segmentCompact.cthickening_eq_biUnion_closedBall
    (mul_nonneg factorPos.le sourceScalePos.le)] at pointMem
  rcases Set.mem_iUnion₂.mp pointMem with
    ⟨axisPoint, axisPointMem, pointAxis⟩
  rcases axisPointMem with
    ⟨parameter, parameterMem, rfl⟩
  let contractedParameter : ℝ :=
    1 / 2 + (parameter - 1 / 2) / factor
  let contractedAxisPoint : Point3 :=
    sourceParent.base +
      contractedParameter • sourceParent.direction
  let contractedPoint : Point3 :=
    center + (1 / factor) • (point - center)
  have contractedParameterMem :
      contractedParameter ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [contractedParameter]
    have lower :
        -(1 / 2 : ℝ) ≤ (parameter - 1 / 2) / factor := by
      apply (le_div_iff₀ factorPos).2
      nlinarith [parameterMem.1]
    have upper :
        (parameter - 1 / 2) / factor ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ factorPos).2
      nlinarith [parameterMem.2]
    constructor
    · linarith
    · linarith
  have contractedAxisPointMem :
      contractedAxisPoint ∈
        Kakeya.unitSegment
          sourceParent.base sourceParent.direction :=
    ⟨contractedParameter, contractedParameterMem, rfl⟩
  have contractedAxisPointEq :
      contractedAxisPoint =
        center + (1 / factor) •
          ((sourceParent.base +
            parameter • sourceParent.direction) - center) := by
    dsimp only [contractedAxisPoint, contractedParameter, center]
    simp only [wz2PaperTubeMidpoint]
    ext coordinate
    simp only [
      PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul
    ]
    field_simp [factorPos.ne']
    ring
  have pointAxisDistance :
      dist point
          (sourceParent.base +
            parameter • sourceParent.direction) ≤
        factor * sourceScale := by
    simpa [Metric.mem_closedBall] using pointAxis
  have contractedDistance :
      dist contractedPoint contractedAxisPoint ≤ sourceScale := by
    rw [contractedAxisPointEq, dist_eq_norm]
    have difference :
        contractedPoint -
            (center + (1 / factor) •
              ((sourceParent.base +
                parameter • sourceParent.direction) - center)) =
          (1 / factor) •
            (point -
              (sourceParent.base +
                parameter • sourceParent.direction)) := by
      dsimp only [contractedPoint]
      module
    rw [difference, norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr factorPos)]
    calc
      (1 / factor) *
            ‖point -
              (sourceParent.base +
                parameter • sourceParent.direction)‖ ≤
          (1 / factor) * (factor * sourceScale) := by
        gcongr
        simpa [dist_eq_norm] using pointAxisDistance
      _ = sourceScale := by
        field_simp [factorPos.ne']
  have contractedPointMem :
      contractedPoint ∈ sourceParent.carrier :=
    Metric.mem_cthickening_of_dist_le
      contractedPoint contractedAxisPoint sourceScale
      (Kakeya.unitSegment
        sourceParent.base sourceParent.direction)
      contractedAxisPointMem contractedDistance
  refine ⟨contractedPoint, contractedPointMem, ?_⟩
  simp only [AffineMap.homothety_apply]
  dsimp only [contractedPoint, center]
  ext coordinate
  simp [wz2PaperTubeMidpoint]
  field_simp [factorPos.ne']
  ring

theorem wz2PaperFactor_outerJohn_volume_le
    {sourceScale factor : ℝ}
    (sourceScalePos : 0 < sourceScale)
    (factorOne : 1 ≤ factor)
    (sourceParent : Kakeya.DeltaTube sourceScale)
    (targetParent : Kakeya.DeltaTube (factor * sourceScale))
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent) :
    volume targetJohn.parent_convex_body.outerJohnEllipsoid ≤
      ((27 : ENNReal) * ENNReal.ofReal (factor ^ 3)) *
        volume sourceJohn.parent_convex_body.outerJohnEllipsoid := by
  have sourceCarrier :
      sourceParent.carrier ⊆
        sourceJohn.parent_convex_body.outerJohnEllipsoid :=
    sourceJohn.parent_convex_body.outerJohnEllipsoid_spec.1
  have targetVolume :
      volume targetParent.carrier =
        volume
          (wz2PaperOrdinaryRadiusRelabel
            (factor * sourceScale) sourceParent).carrier := by
    change targetParent.volume =
      (wz2PaperOrdinaryRadiusRelabel
        (factor * sourceScale) sourceParent).volume
    exact Kakeya.Streamlined.tube_volume_eq _ _
  have factorNonnegative : 0 ≤ factor := zero_le_one.trans factorOne
  have relabelSubset :
      (wz2PaperOrdinaryRadiusRelabel
          (factor * sourceScale) sourceParent).carrier ⊆
        wz2PaperCenteredDilatedCarrier factor sourceParent :=
    wz2PaperOrdinaryRadiusRelabel_carrier_subset_centeredDilated
      sourceScalePos factorOne sourceParent
  have relabelVolumeLe :
      volume
          (wz2PaperOrdinaryRadiusRelabel
            (factor * sourceScale) sourceParent).carrier ≤
        volume (wz2PaperCenteredDilatedCarrier factor sourceParent) :=
    MeasureTheory.measure_mono (μ := volume) relabelSubset
  calc
    volume targetJohn.parent_convex_body.outerJohnEllipsoid ≤
        (27 : ENNReal) * volume targetParent.carrier :=
      targetJohn.outerJohn_volume_le_twentySeven
    _ =
        (27 : ENNReal) *
          volume
            (wz2PaperOrdinaryRadiusRelabel
              (factor * sourceScale) sourceParent).carrier := by
      rw [targetVolume]
    _ ≤
        (27 : ENNReal) *
          volume (wz2PaperCenteredDilatedCarrier factor sourceParent) := by
      exact mul_le_mul_right relabelVolumeLe (27 : ENNReal)
    _ =
        ((27 : ENNReal) * ENNReal.ofReal (factor ^ 3)) *
          volume sourceParent.carrier := by
      rw [wz2_paper_centeredDilatedCarrier_volume,
        abs_of_nonneg factorNonnegative]
      ring
    _ ≤
        ((27 : ENNReal) * ENNReal.ofReal (factor ^ 3)) *
          volume sourceJohn.parent_convex_body.outerJohnEllipsoid := by
      gcongr

theorem wz2PaperBodyConvexWolffBound_of_factorJohnTransport
    {sourceScale factor : ℝ}
    (sourceScalePos : 0 < sourceScale)
    (factorOne : 1 ≤ factor)
    (sourceParent : Kakeya.DeltaTube sourceScale)
    (targetParent : Kakeya.DeltaTube (factor * sourceScale))
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    {source target : Kakeya.Streamlined.BodyFamily}
    {C : ENNReal}
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (carrier_containment :
      ∀ targetIndex,
        wz2PaperGeneralJohnToJohnCoordinateChange
              sourceJohn targetJohn ''
            (source.body (indexEquiv targetIndex)).carrier ⊆
          (target.body targetIndex).carrier)
    (sourceCWA : WZ2PaperBodyConvexWolffBound source C) :
    WZ2PaperBodyConvexWolffBound target
      (((27 : ENNReal) * ENNReal.ofReal (factor ^ 3)) * C) := by
  exact
    wz2PaperBodyConvexWolffBound_of_generalJohnToJohnTransport
      (source := source) (target := target)
      (K := (27 : ENNReal) * ENNReal.ofReal (factor ^ 3))
      (C := C)
      sourceJohn targetJohn
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      (wz2PaperFactor_outerJohn_volume_le
        sourceScalePos factorOne sourceParent targetParent
          sourceJohn targetJohn)
      indexEquiv carrier_containment sourceCWA

end Kakeya.Assouad

end
