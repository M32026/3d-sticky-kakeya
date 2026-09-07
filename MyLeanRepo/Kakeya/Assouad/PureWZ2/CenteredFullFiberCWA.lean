import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12BodyReindex
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OneScaleRescaling
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingJacobian
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CenteredRescaling

/-!
# Centered public CWA for one complete strict full fiber

Definition 2.12 supplies Convex-Wolff counting for the actual outer-John
images of a complete strict full fiber.  This module transports that counting
to the centered ordinary target tubes used by the Assertion-D localization.

The target has exactly the strict full-fiber index type.  No assigned parent
map or assigned-fiber API occurs.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The centered literal rescaling as an affine equivalence. -/
noncomputable def wz2PaperCenteredLiteralRescalingAffineEquiv
    {rho : ℝ}
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  AffineEquiv.ofLinearEquiv
    (wz2PaperLiteralUnitRescalingLinearEquiv anchor hrho)
    (wz2PaperTubeMidpoint anchor) 0

@[simp] theorem wz2PaperCenteredLiteralRescalingAffineEquiv_apply
    {rho : ℝ}
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (point : Point3) :
    wz2PaperCenteredLiteralRescalingAffineEquiv anchor hrho point =
      wz2PaperCenteredLiteralRescalingMap anchor hrho point := by
  rw [wz2PaperCenteredLiteralRescalingAffineEquiv,
    AffineEquiv.ofLinearEquiv_apply]
  rw [vadd_eq_add, add_zero]
  rfl

/-- Common coordinate change from actual John coordinates to centered WZ
coordinates. -/
noncomputable def wz2PaperJohnToCenteredCoordinateChange
    {rho : ℝ}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (normalization : WZ2PaperAssouadUnitRescalingData anchor) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  normalization.map.symm.trans
    (wz2PaperCenteredLiteralRescalingAffineEquiv anchor hrho)

@[simp] theorem wz2PaperJohnToCenteredCoordinateChange_apply_map
    {rho : ℝ}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (normalization : WZ2PaperAssouadUnitRescalingData anchor)
    (point : Point3) :
    wz2PaperJohnToCenteredCoordinateChange hrho normalization
        (normalization.map point) =
      wz2PaperCenteredLiteralRescalingMap anchor hrho point := by
  simp [wz2PaperJohnToCenteredCoordinateChange,
    AffineEquiv.trans_apply]

theorem wz2PaperJohnToCenteredCoordinateChange_image
    {rho : ℝ}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (normalization : WZ2PaperAssouadUnitRescalingData anchor)
    (source : Set Point3) :
    wz2PaperJohnToCenteredCoordinateChange hrho normalization ''
        (normalization.map '' source) =
      wz2PaperCenteredLiteralRescalingMap anchor hrho '' source := by
  ext point
  constructor
  · rintro ⟨johnPoint, ⟨sourcePoint, hsource, rfl⟩, rfl⟩
    exact
      ⟨sourcePoint, hsource,
        (wz2PaperJohnToCenteredCoordinateChange_apply_map
          hrho normalization sourcePoint).symm⟩
  · rintro ⟨sourcePoint, hsource, rfl⟩
    exact
      ⟨normalization.map sourcePoint,
        ⟨sourcePoint, hsource, rfl⟩,
        wz2PaperJohnToCenteredCoordinateChange_apply_map
          hrho normalization sourcePoint⟩

/-- The centered and standard John-to-WZ changes have the same linear part. -/
theorem wz2PaperJohnToCenteredCoordinateChange_linear
    {rho : ℝ}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (normalization : WZ2PaperAssouadUnitRescalingData anchor) :
    (wz2PaperJohnToCenteredCoordinateChange hrho normalization).linear =
      (wz2PaperJohnToLiteralCoordinateChange hrho normalization).linear := by
  rfl

/-- The centered inverse coordinate change has the same fixed Jacobian loss
as the standard literal coordinate change. -/
theorem wz2PaperJohnToCenteredCoordinateChange_inverse_volume
    {rho : ℝ}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (normalization : WZ2PaperAssouadUnitRescalingData anchor)
    (targetSet : Set Point3) :
    MeasureTheory.volume
        ((wz2PaperJohnToCenteredCoordinateChange hrho normalization).symm ''
          targetSet) ≤
      (4000000 : ENNReal) * MeasureTheory.volume targetSet := by
  rw [wz2PaperAffineEquiv_volume_image_eq]
  have hold :=
    wz2PaperJohnToLiteralCoordinateChange_inverse_volume
      hrho normalization targetSet
  rw [wz2PaperAffineEquiv_volume_image_eq] at hold
  have hlinear :
      (wz2PaperJohnToCenteredCoordinateChange hrho normalization).symm.linear =
        (wz2PaperJohnToLiteralCoordinateChange hrho normalization).symm.linear := by
    rfl
  rw [hlinear]
  exact hold

/-- The centered ordinary family indexed by one complete strict full fiber. -/
def wz2PaperCenteredPublicFullFiberFamily
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card)
    (hrho : 0 < rho) :
    Kakeya.Streamlined.TubeFamily (delta / rho) where
  card :=
    (wz2PaperPureFullFiberSubfamily fine coarse parent).family.card
  tube index :=
    wz2PaperCenteredLiteralOrdinaryRescaledTube
      ((wz2PaperPureFullFiberSubfamily fine coarse parent).family.tube index)
      (coarse.tube parent) hrho

@[simp] theorem wz2PaperCenteredPublicFullFiberFamily_card
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card)
    (hrho : 0 < rho) :
    (wz2PaperCenteredPublicFullFiberFamily
      fine coarse parent hrho).card =
      (wz2PaperOrdinaryFullFiberIndices fine coarse parent).card := by
  rfl

/-- The actual John-image family and the centered ordinary family have the
same strict-full-fiber indexing. -/
noncomputable def wz2PaperCenteredFullFiberIndexEquiv
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card)
    (hrho : 0 < rho)
    (normalization :
      WZ2PaperAssouadUnitRescalingData (coarse.tube parent)) :
    Fin (wz2PaperCenteredPublicFullFiberFamily
      fine coarse parent hrho).card ≃
      Fin (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := fine) (coarse := coarse) parent normalization).card :=
  Equiv.refl _

/-- Transport the complete strict-full-fiber CWA to centered ordinary tubes. -/
theorem wz2PaperCenteredPublicFullFiber_convexWolff
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hrhoSmall : rho ≤ 1 / 4)
    (hdeltaRho : delta ≤ rho)
    {C : ENNReal}
    (data :
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := fine) (coarse := coarse) parent C) :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperCenteredPublicFullFiberFamily
        fine coarse parent hrho).toBodyFamily
      ((4000000 : ENNReal) * C) := by
  let source :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := fine) (coarse := coarse) parent data.normalization
  let target :=
    (wz2PaperCenteredPublicFullFiberFamily
      fine coarse parent hrho).toBodyFamily
  let indexEquiv :=
    wz2PaperCenteredFullFiberIndexEquiv
      fine coarse parent hrho data.normalization
  let coordinateChange :=
    wz2PaperJohnToCenteredCoordinateChange
      hrho data.normalization
  apply
    wz2PaperBodyConvexWolffBound_of_indexed_envelope
      (source := source) (target := target)
      indexEquiv
  · intro targetConvexSet htargetConvex
    refine
      ⟨coordinateChange.symm '' targetConvexSet,
        htargetConvex.affine_image coordinateChange.symm.toAffineMap,
        ?_, ?_⟩
    · exact
        wz2PaperJohnToCenteredCoordinateChange_inverse_volume
          hrho data.normalization targetConvexSet
    · intro targetIndex htargetCarrier
      intro point hpoint
      let sourceTube :=
        (wz2PaperPureFullFiberSubfamily fine coarse parent).family.tube
          targetIndex
      have hcoordinateImage :
          coordinateChange point ∈
            coordinateChange ''
              (data.normalization.map '' sourceTube.carrier) :=
        ⟨point, hpoint, rfl⟩
      have hcenteredImage :
          coordinateChange point ∈
            wz2PaperCenteredLiteralRescalingMap
              (coarse.tube parent) hrho '' sourceTube.carrier := by
        rw [← wz2PaperJohnToCenteredCoordinateChange_image
          hrho data.normalization sourceTube.carrier]
        exact hcoordinateImage
      have hsourceContainment :
          sourceTube.carrier ⊆ (coarse.tube parent).carrier := by
        have hfull :
            (wz2PaperPureFullFiberSubfamily
              fine coarse parent).embedding targetIndex ∈
              wz2PaperOrdinaryFullFiberIndices fine coarse parent :=
          Finset.orderEmbOfFin_mem
            (wz2PaperOrdinaryFullFiberIndices fine coarse parent)
            rfl targetIndex
        have hambient :
            (fine.tube
              ((wz2PaperPureFullFiberSubfamily
                fine coarse parent).embedding targetIndex)).carrier ⊆
              (coarse.tube parent).carrier :=
          (mem_wz2PaperOrdinaryFullFiberIndices_iff
            parent
            ((wz2PaperPureFullFiberSubfamily
              fine coarse parent).embedding targetIndex)).mp hfull
        simpa [sourceTube,
          (wz2PaperPureFullFiberSubfamily
            fine coarse parent).tube_eq targetIndex] using hambient
      have htargetTube :
          coordinateChange point ∈
            ((wz2PaperCenteredPublicFullFiberFamily
              fine coarse parent hrho).tube targetIndex).carrier := by
        exact
          centered_image_carrier_subset
            hdelta sourceTube (coarse.tube parent)
            hrho hrhoOne hrhoSmall hdeltaRho
            hsourceContainment
            hcenteredImage
      have htarget : coordinateChange point ∈ targetConvexSet :=
        htargetCarrier htargetTube
      exact
        ⟨coordinateChange point, htarget,
          coordinateChange.symm_apply_apply point⟩
  · exact data.convex_wolff

end Kakeya.Assouad

end
