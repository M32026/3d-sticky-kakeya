import MyLeanRepo.Kakeya.Assouad.PureWZ2.BoundedOrdinaryRescaledLocality
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CanonicalJohnBodyVolumeFloor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.ActiveParentGeometry
import MyLeanRepo.Kakeya.Assouad.EssentiallyDistinctCardBound

/-!
# Proposition 6.2 rescaled top singleton

The Section 6 metric parent controls supporting lines, not the longitudinal
placement of finite ordinary unit segments.  Therefore the paper's singleton
range must not be implemented as an ordinary physical singleton at radius
`rho`.

After literal unit rescaling, however, every public tube midpoint lies in the
fixed radius-three window.  A single radius-four ordinary tube then contains
the whole public family.  Physical body CWA transports to this singleton
parent's canonical outer-John chart with an absolute Jacobian loss.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

def pureWZ2Prop62RescaledTopParent : Kakeya.DeltaTube 4 where
  base := 0
  direction := EuclideanSpace.single (0 : Fin 3) 1
  direction_unit := by simp

theorem pureWZ2_prop62_rescaled_tube_subset_topParent
    {scale : ℝ}
    (scalePos : 0 < scale)
    (scaleLe : scale ≤ 1 / 100)
    (tube : Kakeya.DeltaTube scale)
    (midpointLocal : ‖wz2PaperTubeMidpoint tube‖ ≤ 3) :
    tube.carrier ⊆ pureWZ2Prop62RescaledTopParent.carrier := by
  intro point pointMem
  have pointMidpoint :
      dist point (wz2PaperTubeMidpoint tube) ≤ scale + 1 / 2 := by
    simpa [Metric.mem_closedBall] using
      pureWZ2_tube_carrier_subset_midpoint_ball scalePos.le tube pointMem
  have midpointZero :
      dist (wz2PaperTubeMidpoint tube) 0 ≤ 3 := by
    simpa [dist_zero_right] using midpointLocal
  have pointZero : dist point 0 ≤ 4 := by
    calc
      dist point 0 ≤
          dist point (wz2PaperTubeMidpoint tube) +
            dist (wz2PaperTubeMidpoint tube) 0 :=
        dist_triangle _ _ _
      _ ≤ (scale + 1 / 2) + 3 := by gcongr
      _ ≤ 4 := by linarith
  apply Metric.mem_cthickening_of_dist_le
    point 0 4
    (Kakeya.unitSegment
      pureWZ2Prop62RescaledTopParent.base
      pureWZ2Prop62RescaledTopParent.direction)
  · exact ⟨0, by norm_num, by simp [pureWZ2Prop62RescaledTopParent]⟩
  · simpa using pointZero

private theorem pureWZ2_prop62_topParent_outerJohn_det_le :
    ENNReal.ofReal
        |LinearMap.det
          ((WZ2PaperAssouadUnitRescalingData.ofTube
            pureWZ2Prop62RescaledTopParent (by norm_num)
            ).parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| ≤
      (1000000 : ENNReal) := by
  let normalization :=
    WZ2PaperAssouadUnitRescalingData.ofTube
      pureWZ2Prop62RescaledTopParent (by norm_num)
  let determinant : ENNReal :=
    ENNReal.ofReal
      |LinearMap.det
        (normalization.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)|
  have ellipsoidVolume :
      volume normalization.parent_convex_body.outerJohnEllipsoid =
        determinant * volume (Metric.closedBall (0 : Point3) 1) :=
    JohnEllipsoid.volume_ellipsoid_eq
      normalization.parent_convex_body.outerJohnEllipsoidCenter
      normalization.parent_convex_body.outerJohnEllipsoidMap
  have ballOne :
      (1 : ENNReal) ≤ volume (Metric.closedBall (0 : Point3) 1) :=
    wz2_unitBall_volume_ge_one
  have determinantLeEllipsoid :
      determinant ≤
        volume normalization.parent_convex_body.outerJohnEllipsoid := by
    calc
      determinant = determinant * 1 := by simp
      _ ≤ determinant * volume (Metric.closedBall (0 : Point3) 1) := by
        gcongr
      _ = volume normalization.parent_convex_body.outerJohnEllipsoid :=
        ellipsoidVolume.symm
  have parentVolume :
      volume pureWZ2Prop62RescaledTopParent.carrier ≤
        ENNReal.ofReal (Real.pi * 4 ^ 2 * (1 + 2 * 4)) :=
    tube_volume_upper_pi (by norm_num)
      pureWZ2Prop62RescaledTopParent
  have numeric :
      ENNReal.ofReal (Real.pi * 4 ^ 2 * (1 + 2 * 4)) ≤
        (1000 : ENNReal) := by
    have piBound : Real.pi ≤ 4 := Real.pi_lt_four.le
    calc
      ENNReal.ofReal (Real.pi * 4 ^ 2 * (1 + 2 * 4)) ≤
          ENNReal.ofReal (4 * 4 ^ 2 * (1 + 2 * 4)) := by
        apply ENNReal.ofReal_mono
        nlinarith
      _ ≤ (1000 : ENNReal) := by norm_num
  change determinant ≤ (1000000 : ENNReal)
  calc
    determinant ≤
        volume normalization.parent_convex_body.outerJohnEllipsoid :=
      determinantLeEllipsoid
    _ ≤ 27 * volume pureWZ2Prop62RescaledTopParent.carrier :=
      normalization.outerJohn_volume_le_twentySeven
    _ ≤ 27 * 1000 := by
      gcongr
      exact parentVolume.trans numeric
    _ ≤ 1000000 := by norm_num

private theorem pureWZ2_prop62_topParent_inverse_volume
    (targetSet : Set Point3) :
    volume
        ((WZ2PaperAssouadUnitRescalingData.ofTube
          pureWZ2Prop62RescaledTopParent (by norm_num)).map.symm ''
          targetSet) ≤
      (1000000 : ENNReal) * volume targetSet := by
  rw [wz2PaperAffineEquiv_volume_image_eq]
  gcongr
  exact pureWZ2_prop62_topParent_outerJohn_det_le

theorem pureWZ2_prop62_rescaled_topScale
    {scale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily scale}
    {C : ENNReal}
    (scalePos : 0 < scale)
    (scaleLe : scale ≤ 1 / 100)
    (familyNonempty : family.Nonempty)
    (midpointLocal :
      ∀ index, ‖wz2PaperTubeMidpoint (family.tube index)‖ ≤ 3)
    (physicalCWA :
      WZ2PaperBodyConvexWolffBound family.toBodyFamily C)
    (COne : 1 ≤ C) :
    Nonempty
      (WZ2PaperPureScaleCoverData family 4
        ((81000000 : ENNReal) * C)) := by
  let coarse : Kakeya.Streamlined.TubeFamily 4 :=
    {
      card := 1
      tube := fun _ => pureWZ2Prop62RescaledTopParent
    }
  have tubeSubset :
      ∀ index, (family.tube index).carrier ⊆ (coarse.tube 0).carrier := by
    intro index
    exact pureWZ2_prop62_rescaled_tube_subset_topParent
      scalePos scaleLe (family.tube index) (midpointLocal index)
  let cover : WZ2PaperPurePartitioningCover family coarse :=
    {
      covers := fun index =>
        ⟨0, (mem_wz2PaperOrdinaryFullFiberIndices_iff 0 index).mpr
          (tubeSubset index)⟩
      doubled_fibers_disjoint := by
        intro first second indexNe
        exact (indexNe ((Fin.eq_zero first).trans
          (Fin.eq_zero second).symm)).elim
    }
  have fullFiber :
      wz2PaperOrdinaryFullFiberIndices family coarse 0 = Finset.univ := by
    apply Finset.eq_univ_of_forall
    exact fun index => cover.parent_mem_fullFiber index
  have uniform :
      WZ2PaperPureFullFibersAreCUniform family coarse
        ((81000000 : ENNReal) * C) := by
    intro first second
    have firstEq : first = 0 := Fin.eq_zero first
    have secondEq : second = 0 := Fin.eq_zero second
    rw [firstEq, secondEq]
    rw [wz2PaperOrdinaryFullFiberCount, fullFiber]
    have constantOne :
        (1 : ENNReal) ≤ (81000000 : ENNReal) * C := by
      calc
        (1 : ENNReal) ≤ 81000000 := by norm_num
        _ = 81000000 * 1 := by simp
        _ ≤ 81000000 * C := by gcongr
    simpa using mul_le_mul_right'
      constantOne (family.card : ENNReal)
  let normalization :=
    WZ2PaperAssouadUnitRescalingData.ofTube
      (coarse.tube 0) (by norm_num)
  let target :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := family) (coarse := coarse) 0 normalization
  let source := family.toBodyFamily
  let fullFiberEquiv :=
    wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := family) (coarse := coarse) 0
  let allSource :
      {index : Fin family.card //
        index ∈ wz2PaperOrdinaryFullFiberIndices family coarse 0} ≃
        Fin family.card :=
    {
      toFun := fun index => index.1
      invFun := fun index =>
        ⟨index, by rw [fullFiber]; exact Finset.mem_univ index⟩
      left_inv := fun _ => by ext; rfl
      right_inv := fun _ => rfl
    }
  let indexEquiv : Fin target.card ≃ Fin source.card :=
    fullFiberEquiv.trans allSource
  have carrierEq :
      ∀ targetIndex,
        normalization.map ''
            (source.body (indexEquiv targetIndex)).carrier =
          (target.body targetIndex).carrier := by
    intro targetIndex
    change
      normalization.map ''
          (family.tube (indexEquiv targetIndex)).carrier =
        normalization.map ''
          (family.tube
            ((wz2PaperOrdinaryFullFiberIndexEquiv 0) targetIndex).1).carrier
    congr 3
  have targetRaw :
      WZ2PaperBodyConvexWolffBound target
        ((1000000 : ENNReal) * C) := by
    apply wz2PaperBodyConvexWolffBound_of_affineTransport
      normalization.map indexEquiv
    · intro targetIndex
      exact (carrierEq targetIndex).le
    · exact pureWZ2_prop62_topParent_inverse_volume
    · exact physicalCWA
  have targetCWA :
      WZ2PaperBodyConvexWolffBound target
        ((81000000 : ENNReal) * C) := by
    intro convexSet convex
    exact (targetRaw convexSet convex).trans <| by
      gcongr
      norm_num
  exact
    ⟨{
      delta_pos := scalePos
      rho_pos := by norm_num
      coarse := coarse
      cover := cover
      full_fiber_uniform := uniform
      rescaledFiber := fun parent => by
        have parentEq : parent = 0 := Fin.eq_zero parent
        subst parent
        exact ⟨{
          normalization := normalization
          convex_wolff := targetCWA
        }⟩
    }⟩

end Kakeya.Assouad

end
