import MyLeanRepo.Kakeya.Assouad.PureWZ2.BodyCWAFromVolumeFloor
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12NestedJohnCWATransport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.FrostmanConvexWolff

/-!
# Uniform volume floor for canonical John-image tube bodies

The canonical outer-John ellipsoid contains its parent tube and has volume at
most `27` times the parent volume.  Mapping the parent tube by the inverse
outer-John linear map therefore produces a body of volume at least `1 / 27`.

Every strict full-fiber body is the image of a tube of the same radius as the
parent, hence has the same physical volume.  Consequently every nonempty
canonical full-fiber body family satisfies normalized CWA with constant `27`,
independently of its multiplicity.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

theorem WZ2PaperAssouadUnitRescalingData.tube_image_volume_floor
    {rho : ℝ}
    {parent : Kakeya.DeltaTube rho}
    (normalization :
      WZ2PaperAssouadUnitRescalingData parent)
    (hrho : 0 < rho)
    (tube : Kakeya.DeltaTube rho) :
    (27 : ENNReal)⁻¹ ≤
      volume (normalization.map '' tube.carrier) := by
  let detENN : ENNReal :=
    ENNReal.ofReal
      |LinearMap.det
        (normalization.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)|
  have hellipsoidVolume :
      volume
          normalization.parent_convex_body.outerJohnEllipsoid =
        detENN *
          volume (Metric.closedBall (0 : Point3) 1) :=
    JohnEllipsoid.volume_ellipsoid_eq
      normalization.parent_convex_body.outerJohnEllipsoidCenter
      normalization.parent_convex_body.outerJohnEllipsoidMap
  have hdetUpper :
      detENN ≤ (27 : ENNReal) * volume parent.carrier := by
    have hellipsoidUpper :
        volume
            normalization.parent_convex_body.outerJohnEllipsoid ≤
          (27 : ENNReal) * volume parent.carrier :=
      normalization.outerJohn_volume_le_twentySeven
    rw [hellipsoidVolume] at hellipsoidUpper
    have hball :
        (1 : ENNReal) ≤
          volume (Metric.closedBall (0 : Point3) 1) :=
      wz2_unitBall_volume_ge_one
    exact
      (show detENN ≤
          detENN *
            volume (Metric.closedBall (0 : Point3) 1) by
        calc
          detENN = detENN * 1 := by simp
          _ ≤ detENN *
              volume (Metric.closedBall (0 : Point3) 1) := by
            gcongr).trans
        hellipsoidUpper
  have hparentVolume :
      volume tube.carrier = volume parent.carrier := by
    change tube.volume = parent.volume
    exact Kakeya.Streamlined.tube_volume_eq tube parent
  have hdetPos :
      0 < detENN := by
    change
      0 <
        ENNReal.ofReal
          |LinearMap.det
            (normalization.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)|
    rw [ENNReal.ofReal_pos]
    exact
      abs_pos.mpr
        (LinearEquiv.isUnit_det'
          normalization.parent_convex_body.outerJohnEllipsoidMap).ne_zero
  have hdetTop : detENN ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hmapDet :
      ENNReal.ofReal
          |LinearMap.det
            (normalization.map.linear :
              Point3 →ₗ[ℝ] Point3)| =
        detENN⁻¹ := by
    have hlinear :
        normalization.map.linear =
          normalization.parent_convex_body.outerJohnEllipsoidMap.symm := rfl
    rw [hlinear, LinearEquiv.det_coe_symm, abs_inv,
      ENNReal.ofReal_inv_of_pos]
    exact
      abs_pos.mpr
        (LinearEquiv.isUnit_det'
          normalization.parent_convex_body.outerJohnEllipsoidMap).ne_zero
  rw [wz2PaperAffineEquiv_volume_image_eq, hmapDet,
    hparentVolume]
  have hparentPos :
      0 < volume parent.carrier :=
    wz2_paper_ordinary_tube_volume_pos parent hrho
  have hparentTop :
      volume parent.carrier ≠ ⊤ :=
    wz2_paper_ordinary_tube_volume_ne_top parent hrho
  have hscaled :
      detENN⁻¹ * volume parent.carrier ≥
        ((27 : ENNReal) * volume parent.carrier)⁻¹ *
          volume parent.carrier :=
    mul_le_mul_right'
      (ENNReal.inv_le_inv' hdetUpper)
      (volume parent.carrier)
  calc
    (27 : ENNReal)⁻¹ =
        ((27 : ENNReal) * volume parent.carrier)⁻¹ *
          volume parent.carrier := by
      rw [ENNReal.mul_inv
          (Or.inl (by norm_num))
          (Or.inl (by norm_num)),
        mul_assoc,
        ENNReal.inv_mul_cancel hparentPos.ne' hparentTop,
        mul_one]
    _ ≤ detENN⁻¹ * volume parent.carrier :=
      hscaled

theorem wz2PaperPureUnitRescaledFullFiberBodyFamily_volume_floor
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hdeltaRho : delta = rho)
    (normalization :
      WZ2PaperAssouadUnitRescalingData
        (coarse.tube parent)) :
    ∀ index,
      (27 : ENNReal)⁻¹ ≤
        ((wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := fine) (coarse := coarse)
          parent normalization).body index).volume := by
  subst rho
  intro index
  exact
    normalization.tube_image_volume_floor
      hdelta (fine.tube
        ((wz2PaperOrdinaryFullFiberIndexEquiv parent) index).1)

/--
Every canonical full-fiber body family satisfies CWA with the explicit
physical-volume ratio

`27 * |parent| * |T_delta|⁻¹`.

Unlike the same-radius corollary above, this form allows the fine and parent
radii to differ and records exactly the quadratic scale loss.
-/
theorem wz2PaperPureUnitRescaledFullFiberBodyFamily_convexWolff_volumeRatio
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (normalization :
      WZ2PaperAssouadUnitRescalingData
        (coarse.tube parent)) :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := fine) (coarse := coarse)
        parent normalization)
      ((27 : ENNReal) *
        volume (coarse.tube parent).carrier *
        (Kakeya.deltaTubeVolume delta)⁻¹) := by
  let family :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := fine) (coarse := coarse)
      parent normalization
  apply
    wz2PaperBodyConvexWolffBound_of_volume_ratio
      family
      ((27 : ENNReal) *
        volume (coarse.tube parent).carrier *
        (Kakeya.deltaTubeVolume delta)⁻¹)
  intro index
  let source :=
    (wz2PaperOrdinaryFullFiberIndexEquiv parent index).1
  let sourceTube := fine.tube source
  let detENN : ENNReal :=
    ENNReal.ofReal
      |LinearMap.det
        (normalization.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)|
  have hellipsoidVolume :
      volume
          normalization.parent_convex_body.outerJohnEllipsoid =
        detENN *
          volume (Metric.closedBall (0 : Point3) 1) :=
    JohnEllipsoid.volume_ellipsoid_eq
      normalization.parent_convex_body.outerJohnEllipsoidCenter
      normalization.parent_convex_body.outerJohnEllipsoidMap
  have hdetUpper :
      detENN ≤
        (27 : ENNReal) *
          volume (coarse.tube parent).carrier := by
    have hellipsoidUpper :
        volume
            normalization.parent_convex_body.outerJohnEllipsoid ≤
          (27 : ENNReal) *
            volume (coarse.tube parent).carrier :=
      normalization.outerJohn_volume_le_twentySeven
    rw [hellipsoidVolume] at hellipsoidUpper
    have hball :
        (1 : ENNReal) ≤
          volume (Metric.closedBall (0 : Point3) 1) :=
      wz2_unitBall_volume_ge_one
    exact
      (show detENN ≤
          detENN *
            volume (Metric.closedBall (0 : Point3) 1) by
        calc
          detENN = detENN * 1 := by simp
          _ ≤ detENN *
              volume (Metric.closedBall (0 : Point3) 1) := by
            gcongr).trans
        hellipsoidUpper
  have hdetPos : 0 < detENN := by
    change
      0 <
        ENNReal.ofReal
          |LinearMap.det
            (normalization.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)|
    rw [ENNReal.ofReal_pos]
    exact
      abs_pos.mpr
        (LinearEquiv.isUnit_det'
          normalization.parent_convex_body.outerJohnEllipsoidMap).ne_zero
  have hdetTop : detENN ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hmapDet :
      ENNReal.ofReal
          |LinearMap.det
            (normalization.map.linear :
              Point3 →ₗ[ℝ] Point3)| =
        detENN⁻¹ := by
    have hlinear :
        normalization.map.linear =
          normalization.parent_convex_body.outerJohnEllipsoidMap.symm := rfl
    rw [hlinear, LinearEquiv.det_coe_symm, abs_inv,
      ENNReal.ofReal_inv_of_pos]
    exact
      abs_pos.mpr
        (LinearEquiv.isUnit_det'
          normalization.parent_convex_body.outerJohnEllipsoidMap).ne_zero
  have hsourceVolume :
      volume sourceTube.carrier =
        Kakeya.deltaTubeVolume delta := by
    let canonical : Kakeya.DeltaTube delta :=
      {
        base := 0
        direction := EuclideanSpace.single (0 : Fin 3) 1
        direction_unit := by simp
      }
    have hvolume :=
      Kakeya.Streamlined.tube_volume_eq sourceTube canonical
    calc
      volume sourceTube.carrier = sourceTube.volume := rfl
      _ = canonical.volume := hvolume
      _ = Kakeya.deltaTubeVolume delta := rfl
  have hsourcePos :
      0 < Kakeya.deltaTubeVolume delta := by
    exact
      (wz2_paper_ordinary_tube_volume_pos sourceTube hdelta)
        |>.trans_eq hsourceVolume
  have hsourceTop :
      Kakeya.deltaTubeVolume delta ≠ ⊤ := by
    rw [← hsourceVolume]
    exact wz2_paper_ordinary_tube_volume_ne_top sourceTube hdelta
  have honeDet :
      (1 : ENNReal) ≤
        ((27 : ENNReal) *
          volume (coarse.tube parent).carrier) *
          detENN⁻¹ := by
    calc
      (1 : ENNReal) =
          detENN * detENN⁻¹ := by
        rw [ENNReal.mul_inv_cancel hdetPos.ne' hdetTop]
      _ ≤
          ((27 : ENNReal) *
            volume (coarse.tube parent).carrier) *
            detENN⁻¹ := by
        gcongr
  change
    (1 : ENNReal) ≤
      ((27 : ENNReal) *
          volume (coarse.tube parent).carrier *
          (Kakeya.deltaTubeVolume delta)⁻¹) *
        volume (normalization.map '' sourceTube.carrier)
  rw [wz2PaperAffineEquiv_volume_image_eq,
    hmapDet, hsourceVolume]
  calc
    (1 : ENNReal) ≤
        ((27 : ENNReal) *
          volume (coarse.tube parent).carrier) *
          detENN⁻¹ :=
      honeDet
    _ =
        ((27 : ENNReal) *
            volume (coarse.tube parent).carrier *
            (Kakeya.deltaTubeVolume delta)⁻¹) *
          (detENN⁻¹ *
            Kakeya.deltaTubeVolume delta) := by
      have hcancel :
          (Kakeya.deltaTubeVolume delta)⁻¹ *
              Kakeya.deltaTubeVolume delta = 1 :=
        ENNReal.inv_mul_cancel hsourcePos.ne' hsourceTop
      calc
        (27 : ENNReal) *
              volume (coarse.tube parent).carrier *
              detENN⁻¹ =
            ((27 : ENNReal) *
                volume (coarse.tube parent).carrier) *
              detENN⁻¹ *
              ((Kakeya.deltaTubeVolume delta)⁻¹ *
                Kakeya.deltaTubeVolume delta) := by
          rw [hcancel, mul_one]
        _ =
            ((27 : ENNReal) *
                volume (coarse.tube parent).carrier *
                (Kakeya.deltaTubeVolume delta)⁻¹) *
              (detENN⁻¹ *
                Kakeya.deltaTubeVolume delta) := by
          ring

end Kakeya.Assouad

end
