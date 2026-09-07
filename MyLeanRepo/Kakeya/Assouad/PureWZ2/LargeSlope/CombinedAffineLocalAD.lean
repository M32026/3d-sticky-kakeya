import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicExactPlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ScaledPlaneMapNormalization

/-!
# Local AD through the combined affine and isotropic normalization

The paper applies the anisotropic map and the final isotropic dilation as one
bounded-condition-number rescaling.  This file isolates the two exact facts
needed by that argument: scalar projections differ by a positive affine map,
and a source AD estimate may then be weakened to the final target scale.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- The source distance recovered from the combined triangular map and a
positive isotropic dilation. -/
theorem pureWZ2_combined_affine_source_dist_le
    (g : SlopeFunction) {c d m scale : ℝ}
    (hcd : c < d) (hm : 0 < m) (hscale : 0 < scale)
    (anisotropicCenter isotropicCenter first second : Point3) :
    dist first second ≤
      ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
        (dist
          (pureWZ2IsotropicMap isotropicCenter scale
            (anisotropicCenteredRescalingMap g c d m anisotropicCenter first))
          (pureWZ2IsotropicMap isotropicCenter scale
            (anisotropicCenteredRescalingMap g c d m anisotropicCenter second)) /
          scale) := by
  let linear := anisotropicRescalingLinearEquiv g c d m hcd hm
  let inverseLinear := linear.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hrecover : first - second =
      inverseLinear (dPhiLin g c d m (first - second)) := by
    have hinverse : linear.symm (linear (first - second)) = first - second :=
      linear.symm_apply_apply (first - second)
    rw [show linear (first - second) =
        dPhiLin g c d m (first - second) by
          exact anisotropicRescalingLinearMap_apply_eq_dPhiLin
            g c d m (first - second)] at hinverse
    exact hinverse.symm
  have hinverseBound := inverseLinear.le_opNorm
    (dPhiLin g c d m (first - second))
  rw [← hrecover] at hinverseBound
  have htargetDistance :
      dist
          (pureWZ2IsotropicMap isotropicCenter scale
            (anisotropicCenteredRescalingMap g c d m anisotropicCenter first))
          (pureWZ2IsotropicMap isotropicCenter scale
            (anisotropicCenteredRescalingMap g c d m anisotropicCenter second)) =
        scale * ‖dPhiLin g c d m (first - second)‖ := by
    simp only [pureWZ2IsotropicMap, dist_eq_norm]
    have hdiff :
        scale •
              (anisotropicCenteredRescalingMap g c d m anisotropicCenter first -
                isotropicCenter) -
            scale •
              (anisotropicCenteredRescalingMap g c d m anisotropicCenter second -
                isotropicCenter) =
          scale • dPhiLin g c d m (first - second) := by
      rw [← smul_sub]
      congr 1
      calc
        (anisotropicCenteredRescalingMap g c d m anisotropicCenter first -
              isotropicCenter) -
            (anisotropicCenteredRescalingMap g c d m anisotropicCenter second -
              isotropicCenter) =
          anisotropicCenteredRescalingMap g c d m anisotropicCenter first -
            anisotropicCenteredRescalingMap g c d m anisotropicCenter second := by
              module
        _ = dPhiLin g c d m (first - second) :=
          anisotropicCenteredRescalingMap_sub g c d m anisotropicCenter
            first second
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hscale]
  rw [dist_eq_norm, htargetDistance]
  have hcancel : scale * ‖dPhiLin g c d m (first - second)‖ / scale =
      ‖dPhiLin g c d m (first - second)‖ := by
    field_simp [hscale.ne']
  rw [hcancel]
  simpa only [inverseLinear] using hinverseBound

/-- A subset of a positive affine image of an AD set inherits its AD bound at
any larger base scale. -/
theorem PureWZ2PaperADSet1.affine_image_subset_weaken_scale
    {source target : Set ℝ}
    {sourceDelta targetDelta alpha a b : ℝ} {C : ENNReal}
    (hsource : PureWZ2PaperADSet1 source sourceDelta alpha C)
    (ha : 0 < a) (htargetDelta : 0 < targetDelta)
    (hbase : a * sourceDelta ≤ targetDelta)
    (hsubset : target ⊆ (fun value : ℝ => a * value + b) '' source) :
    PureWZ2PaperADSet1 target targetDelta alpha C := by
  exact (hsource.affine_transfer ha).weaken_scale htargetDelta hbase
    |>.weaken_subset hsubset

/-- Exact covariance of local scalar-projection differences under the
centered triangular map followed by a positive isotropic dilation. -/
theorem pureWZ2_combined_local_projection_difference
    (g : SlopeFunction) {c d m scale : ℝ}
    (hcd : c < d) (hm : 0 < m)
    (anisotropicCenter isotropicCenter first second normal : Point3) :
    let transported := dPhiInvT g c d m normal
    let normalized := (‖transported‖⁻¹ : ℝ) • transported
    inner ℝ
          (pureWZ2IsotropicMap isotropicCenter scale
            (anisotropicCenteredRescalingMap g c d m anisotropicCenter first))
          normalized -
        inner ℝ
          (pureWZ2IsotropicMap isotropicCenter scale
            (anisotropicCenteredRescalingMap g c d m anisotropicCenter second))
          normalized =
      (scale / ‖transported‖) *
        (inner ℝ first normal - inner ℝ second normal) := by
  dsimp only
  let transported := dPhiInvT g c d m normal
  have hmapDifference :
      pureWZ2IsotropicMap isotropicCenter scale
          (anisotropicCenteredRescalingMap g c d m anisotropicCenter first) -
        pureWZ2IsotropicMap isotropicCenter scale
          (anisotropicCenteredRescalingMap g c d m anisotropicCenter second) =
      scale • dPhiLin g c d m (first - second) := by
    simp only [pureWZ2IsotropicMap]
    rw [← smul_sub]
    congr 1
    calc
      (anisotropicCenteredRescalingMap g c d m anisotropicCenter first -
          isotropicCenter) -
        (anisotropicCenteredRescalingMap g c d m anisotropicCenter second -
          isotropicCenter) =
        anisotropicCenteredRescalingMap g c d m anisotropicCenter first -
          anisotropicCenteredRescalingMap g c d m anisotropicCenter second := by
            module
      _ = dPhiLin g c d m (first - second) :=
        anisotropicCenteredRescalingMap_sub g c d m anisotropicCenter first second
  rw [← inner_sub_left, hmapDifference, inner_smul_left, inner_smul_right,
    dPhi_inner_identity g c d m hcd hm, inner_sub_left]
  simp only [starRingEnd_apply, star_trivial]
  ring

/-- The abstract covering-number step of the combined Lemma-8 local-grain
transport.  Geometry enters only through the actual source anchor, the source
ball containment, and the exact scalar-projection affine relation. -/
theorem pureWZ2_combined_affine_isotropic_local_ad
    {sourceDelta sourceRho targetRho sigma a b : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (sourcePoint : {point : Point3 // point ∈ sourceShading.union})
    (targetNormal : Point3) (targetSet : Set Point3)
    (hsourceRho : sourceDelta ≤ sourceRho)
    (hsourceRhoOne : sourceRho ≤ 1)
    (ha : 0 < a) (htargetRho : 0 < targetRho)
    (hbase : a * sourceRho ≤ targetRho)
    (hprojection :
      scalarProjection targetNormal targetSet ⊆
        (fun value : ℝ => a * value + b) ''
          scalarProjection (sourceLocal.planeMap sourcePoint)
            (sourceShading.union ∩
              Metric.closedBall (sourcePoint : Point3)
                (Real.sqrt sourceRho))) :
    PureWZ2PaperADSet1
      (scalarProjection targetNormal targetSet) targetRho
        (1 - sigma) C := by
  exact (sourceLocal.local_ad sourceRho hsourceRho hsourceRhoOne sourcePoint)
    |>.affine_image_subset_weaken_scale ha htargetRho hbase hprojection

/-- Local AD for a genuine subset of the combined triangular and isotropic
image.  All distortion is visible in the two scalar hypotheses `hball` and
`hbase`; no intermediate same-scale local-AD assertion is used. -/
theorem pureWZ2_combined_affine_isotropic_local_ad_of_image
    {sourceDelta sourceRho targetRho sigma c d m scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (g : SlopeFunction) (hcd : c < d) (hm : 0 < m)
    (anisotropicCenter isotropicCenter : Point3)
    (hscale : 0 < scale)
    (sourcePoint : {point : Point3 // point ∈ sourceShading.union})
    (targetPoint : Point3)
    (htargetPoint : targetPoint =
      pureWZ2IsotropicMap isotropicCenter scale
        (anisotropicCenteredRescalingMap g c d m anisotropicCenter
          sourcePoint))
    (targetSet : Set Point3)
    (htarget : targetSet ⊆
      (fun source => pureWZ2IsotropicMap isotropicCenter scale
        (anisotropicCenteredRescalingMap g c d m anisotropicCenter source)) ''
          sourceShading.union)
    (hsourceRho : sourceDelta ≤ sourceRho)
    (hsourceRhoOne : sourceRho ≤ 1)
    (hball :
      ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          (Real.sqrt targetRho / scale) ≤ Real.sqrt sourceRho)
    (hbase :
      (scale /
          ‖dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)‖) *
        sourceRho ≤ targetRho)
    (htargetRho : 0 < targetRho) :
    let transported := dPhiInvT g c d m
      (sourceLocal.planeMap sourcePoint)
    let targetNormal := (‖transported‖⁻¹ : ℝ) • transported
    PureWZ2PaperADSet1
      (scalarProjection targetNormal
        (targetSet ∩ Metric.closedBall targetPoint (Real.sqrt targetRho)))
      targetRho (1 - sigma) C := by
  dsimp only
  let transported := dPhiInvT g c d m
    (sourceLocal.planeMap sourcePoint)
  have hsourceNonzero : sourceLocal.planeMap sourcePoint ≠ 0 := by
    intro hzero
    have hunit := sourceLocal.planeMap_unit sourcePoint
    rw [hzero, norm_zero] at hunit
    norm_num at hunit
  have htransported : transported ≠ 0 := by
    intro hzero
    apply hsourceNonzero
    apply dPhiInvT_injective g c d m hcd hm
    rw [show dPhiInvT g c d m (sourceLocal.planeMap sourcePoint) =
        transported by rfl, hzero]
    simp [dPhiInvT, point3]
  have htransportedNorm : 0 < ‖transported‖ :=
    norm_pos_iff.mpr htransported
  let targetNormal := (‖transported‖⁻¹ : ℝ) • transported
  let targetLocalSet :=
    targetSet ∩ Metric.closedBall targetPoint (Real.sqrt targetRho)
  let a := scale / ‖transported‖
  let b := inner ℝ targetPoint targetNormal -
    a * inner ℝ (sourcePoint : Point3) (sourceLocal.planeMap sourcePoint)
  have ha : 0 < a := div_pos hscale htransportedNorm
  have hprojection : scalarProjection targetNormal targetLocalSet ⊆
      (fun value : ℝ => a * value + b) ''
        scalarProjection (sourceLocal.planeMap sourcePoint)
          (sourceShading.union ∩
            Metric.closedBall (sourcePoint : Point3)
              (Real.sqrt sourceRho)) := by
    rintro value ⟨target, htargetLocal, rfl⟩
    rcases htarget htargetLocal.1 with ⟨source, hsource, hsourceTargetEq⟩
    have hsourceDistance : dist source (sourcePoint : Point3) ≤
        ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
            |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          (dist target targetPoint / scale) := by
      have h := pureWZ2_combined_affine_source_dist_le g hcd hm hscale
        anisotropicCenter isotropicCenter source sourcePoint
      calc
        dist source (sourcePoint : Point3) ≤
            ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
                |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
              (dist
                (pureWZ2IsotropicMap isotropicCenter scale
                  (anisotropicCenteredRescalingMap g c d m
                    anisotropicCenter source))
                (pureWZ2IsotropicMap isotropicCenter scale
                  (anisotropicCenteredRescalingMap g c d m
                    anisotropicCenter sourcePoint)) / scale) := h
        _ = ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
                |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
              (dist target targetPoint / scale) := by
          congr 2
          exact congrArg₂ dist hsourceTargetEq htargetPoint.symm
    have hsourceBall : source ∈
        Metric.closedBall (sourcePoint : Point3) (Real.sqrt sourceRho) := by
      rw [Metric.mem_closedBall]
      calc
        dist source (sourcePoint : Point3) ≤
            ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
                |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
              (dist target targetPoint / scale) := hsourceDistance
        _ ≤ ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
                |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
              (Real.sqrt targetRho / scale) := by
            gcongr
            exact htargetLocal.2
        _ ≤ Real.sqrt sourceRho := hball
    refine ⟨inner ℝ source (sourceLocal.planeMap sourcePoint),
      ⟨source, ⟨hsource, hsourceBall⟩, rfl⟩, ?_⟩
    have hdifference := pureWZ2_combined_local_projection_difference
      (scale := scale) g hcd hm anisotropicCenter isotropicCenter source
        sourcePoint (sourceLocal.planeMap sourcePoint)
    dsimp only [transported, targetNormal, a, b] at hdifference ⊢
    have htargetPointEq :
        targetPoint = pureWZ2IsotropicMap isotropicCenter scale
          (anisotropicCenteredRescalingMap g c d m anisotropicCenter
            (sourcePoint : Point3)) := htargetPoint
    calc
      scale / ‖dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)‖ *
            inner ℝ source (sourceLocal.planeMap sourcePoint) +
          (inner ℝ targetPoint
              ((‖dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)‖⁻¹ : ℝ) •
                dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)) -
            scale / ‖dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)‖ *
              inner ℝ (sourcePoint : Point3)
                (sourceLocal.planeMap sourcePoint)) =
          inner ℝ
            (pureWZ2IsotropicMap isotropicCenter scale
              (anisotropicCenteredRescalingMap g c d m
                anisotropicCenter source))
            ((‖dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)‖⁻¹ : ℝ) •
              dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)) := by
                rw [htargetPointEq]
                linarith [hdifference]
      _ = inner ℝ target
            ((‖dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)‖⁻¹ : ℝ) •
              dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)) := by
                exact congrArg (fun point => inner ℝ point
                  ((‖dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)‖⁻¹ : ℝ) •
                    dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)))
                  hsourceTargetEq
  exact pureWZ2_combined_affine_isotropic_local_ad sourceLocal sourcePoint
    targetNormal targetLocalSet hsourceRho hsourceRhoOne ha htargetRho hbase
    hprojection

/-- Local AD on an arbitrary bounded subset of the combined affine/isotropic
image.  This is the radius-explicit form needed after cubical saturation:
the exact-image set is enlarged from `sqrt targetRho` to
`sqrt targetRho + 2 * witnessRadius`, and the caller pays for that enlarged
radius in `hball`. -/
theorem pureWZ2_combined_affine_isotropic_local_ad_of_image_in_ball
    {sourceDelta sourceRho targetRho targetRadius sigma c d m scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (g : SlopeFunction) (hcd : c < d) (hm : 0 < m)
    (anisotropicCenter isotropicCenter : Point3)
    (hscale : 0 < scale)
    (sourcePoint : {point : Point3 // point ∈ sourceShading.union})
    (targetPoint : Point3)
    (htargetPoint : targetPoint =
      pureWZ2IsotropicMap isotropicCenter scale
        (anisotropicCenteredRescalingMap g c d m anisotropicCenter
          sourcePoint))
    (targetSet : Set Point3)
    (htargetImage : targetSet ⊆
      (fun source => pureWZ2IsotropicMap isotropicCenter scale
        (anisotropicCenteredRescalingMap g c d m anisotropicCenter source)) ''
          sourceShading.union)
    (htargetBall : targetSet ⊆
      Metric.closedBall targetPoint targetRadius)
    (hsourceRho : sourceDelta ≤ sourceRho)
    (hsourceRhoOne : sourceRho ≤ 1)
    (hball :
      ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          (targetRadius / scale) ≤ Real.sqrt sourceRho)
    (hbase :
      (scale /
          ‖dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)‖) *
        sourceRho ≤ targetRho)
    (htargetRho : 0 < targetRho) :
    let transported := dPhiInvT g c d m
      (sourceLocal.planeMap sourcePoint)
    let targetNormal := (‖transported‖⁻¹ : ℝ) • transported
    PureWZ2PaperADSet1
      (scalarProjection targetNormal targetSet)
      targetRho (1 - sigma) C := by
  dsimp only
  let transported := dPhiInvT g c d m
    (sourceLocal.planeMap sourcePoint)
  have hsourceNonzero : sourceLocal.planeMap sourcePoint ≠ 0 := by
    intro hzero
    have hunit := sourceLocal.planeMap_unit sourcePoint
    rw [hzero, norm_zero] at hunit
    norm_num at hunit
  have htransported : transported ≠ 0 := by
    intro hzero
    apply hsourceNonzero
    apply dPhiInvT_injective g c d m hcd hm
    rw [show dPhiInvT g c d m (sourceLocal.planeMap sourcePoint) =
        transported by rfl, hzero]
    simp [dPhiInvT, point3]
  have htransportedNorm : 0 < ‖transported‖ :=
    norm_pos_iff.mpr htransported
  let targetNormal := (‖transported‖⁻¹ : ℝ) • transported
  let a := scale / ‖transported‖
  let b := inner ℝ targetPoint targetNormal -
    a * inner ℝ (sourcePoint : Point3) (sourceLocal.planeMap sourcePoint)
  have ha : 0 < a := div_pos hscale htransportedNorm
  have hprojection : scalarProjection targetNormal targetSet ⊆
      (fun value : ℝ => a * value + b) ''
        scalarProjection (sourceLocal.planeMap sourcePoint)
          (sourceShading.union ∩
            Metric.closedBall (sourcePoint : Point3)
              (Real.sqrt sourceRho)) := by
    rintro value ⟨target, htargetSet, rfl⟩
    rcases htargetImage htargetSet with ⟨source, hsource, hsourceTargetEq⟩
    have hsourceDistance : dist source (sourcePoint : Point3) ≤
        ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
            |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          (dist target targetPoint / scale) := by
      have h := pureWZ2_combined_affine_source_dist_le g hcd hm hscale
        anisotropicCenter isotropicCenter source sourcePoint
      calc
        dist source (sourcePoint : Point3) ≤
            ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
                |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
              (dist
                (pureWZ2IsotropicMap isotropicCenter scale
                  (anisotropicCenteredRescalingMap g c d m
                    anisotropicCenter source))
                (pureWZ2IsotropicMap isotropicCenter scale
                  (anisotropicCenteredRescalingMap g c d m
                    anisotropicCenter sourcePoint)) / scale) := h
        _ = ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
                |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
              (dist target targetPoint / scale) := by
          congr 2
          exact congrArg₂ dist hsourceTargetEq htargetPoint.symm
    have hsourceBall : source ∈
        Metric.closedBall (sourcePoint : Point3) (Real.sqrt sourceRho) := by
      rw [Metric.mem_closedBall]
      calc
        dist source (sourcePoint : Point3) ≤
            ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
                |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
              (dist target targetPoint / scale) := hsourceDistance
        _ ≤ ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
                |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
              (targetRadius / scale) := by
            gcongr
            exact htargetBall htargetSet
        _ ≤ Real.sqrt sourceRho := hball
    refine ⟨inner ℝ source (sourceLocal.planeMap sourcePoint),
      ⟨source, ⟨hsource, hsourceBall⟩, rfl⟩, ?_⟩
    have hdifference := pureWZ2_combined_local_projection_difference
      (scale := scale) g hcd hm anisotropicCenter isotropicCenter source
        sourcePoint (sourceLocal.planeMap sourcePoint)
    dsimp only [transported, targetNormal, a, b] at hdifference ⊢
    calc
      scale / ‖dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)‖ *
            inner ℝ source (sourceLocal.planeMap sourcePoint) +
          (inner ℝ targetPoint
              ((‖dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)‖⁻¹ : ℝ) •
                dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)) -
            scale / ‖dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)‖ *
              inner ℝ (sourcePoint : Point3)
                (sourceLocal.planeMap sourcePoint)) =
          inner ℝ
            (pureWZ2IsotropicMap isotropicCenter scale
              (anisotropicCenteredRescalingMap g c d m
                anisotropicCenter source))
            ((‖dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)‖⁻¹ : ℝ) •
              dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)) := by
                rw [htargetPoint]
                linarith [hdifference]
      _ = inner ℝ target
            ((‖dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)‖⁻¹ : ℝ) •
              dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)) := by
                exact congrArg (fun point => inner ℝ point
                  ((‖dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)‖⁻¹ : ℝ) •
                    dPhiInvT g c d m (sourceLocal.planeMap sourcePoint)))
                  hsourceTargetEq
  exact pureWZ2_combined_affine_isotropic_local_ad sourceLocal sourcePoint
    targetNormal targetSet hsourceRho hsourceRhoOne ha htargetRho hbase
    hprojection

end Kakeya.Assouad

end
