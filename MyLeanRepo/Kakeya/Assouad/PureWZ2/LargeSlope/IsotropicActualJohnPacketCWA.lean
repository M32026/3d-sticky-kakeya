import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ActualJohnPacketCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicRepresentativeParent
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.OuterJohnInverseVolume

/-!
# Actual-John packet CWA under a positive similarity

This module is the body-level transport used after the final isotropic
normalization.  It is independent of how target quotient parents are chosen.
The only geometric input is that each complete image of a source ordinary
tube is contained in a controlled homothety of the corresponding canonical
target tube.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- The final positive similarity as an affine equivalence. -/
noncomputable def pureWZ2IsotropicAffineEquiv
    (center : Point3) (scale : ℝ) (hscale : 0 < scale) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  AffineEquiv.ofLinearEquiv
    (LinearEquiv.smulOfNeZero ℝ Point3 scale hscale.ne') center 0

@[simp] theorem pureWZ2IsotropicAffineEquiv_apply
    (center : Point3) (scale : ℝ) (hscale : 0 < scale)
    (point : Point3) :
    pureWZ2IsotropicAffineEquiv center scale hscale point =
      pureWZ2IsotropicMap center scale point := by
  rw [pureWZ2IsotropicAffineEquiv, AffineEquiv.ofLinearEquiv_apply]
  simp [pureWZ2IsotropicMap, LinearEquiv.smulOfNeZero_apply]

/-- Coordinate change from a source actual-John normalization to a target
actual-John normalization through the positive similarity. -/
noncomputable def pureWZ2IsotropicJohnCoordinateChange
    {sourceRho targetRho : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (center : Point3) (scale : ℝ) (hscale : 0 < scale)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  sourceJohn.map.symm.trans
    ((pureWZ2IsotropicAffineEquiv center scale hscale).trans targetJohn.map)

@[simp] theorem pureWZ2IsotropicJohnCoordinateChange_apply_sourceMap
    {sourceRho targetRho : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (center : Point3) (scale : ℝ) (hscale : 0 < scale)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (point : Point3) :
    pureWZ2IsotropicJohnCoordinateChange center scale hscale
        sourceJohn targetJohn (sourceJohn.map point) =
      targetJohn.map (pureWZ2IsotropicMap center scale point) := by
  simp [pureWZ2IsotropicJohnCoordinateChange, AffineEquiv.trans_apply]

/-- The same midpoint envelope transported through both actual-John maps. -/
theorem pureWZ2IsotropicJohnCoordinateChange_carrier
    {sourceRho targetRho : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (center : Point3) (scale : ℝ) (hscale : 0 < scale)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (factor : ℝ) (targetCenter : Point3)
    (sourceSet targetSet : Set Point3)
    (hcarrier : pureWZ2IsotropicMap center scale '' sourceSet ⊆
      AffineMap.homothety targetCenter factor '' targetSet) :
    pureWZ2IsotropicJohnCoordinateChange center scale hscale
          sourceJohn targetJohn '' (sourceJohn.map '' sourceSet) ⊆
      AffineMap.homothety (targetJohn.map targetCenter) factor ''
        (targetJohn.map '' targetSet) := by
  rintro targetPoint ⟨sourceJohnPoint,
    ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
  rcases hcarrier ⟨sourcePoint, hsourcePoint, rfl⟩ with
    ⟨targetCarrierPoint, htargetCarrierPoint, hhomothety⟩
  refine ⟨targetJohn.map targetCarrierPoint,
    ⟨targetCarrierPoint, htargetCarrierPoint, rfl⟩, ?_⟩
  rw [pureWZ2IsotropicJohnCoordinateChange_apply_sourceMap]
  rw [← hhomothety]
  change (AffineMap.lineMap
      (targetJohn.map targetCenter)
      (targetJohn.map targetCarrierPoint)) factor =
    targetJohn.map ((AffineMap.lineMap targetCenter targetCarrierPoint) factor)
  exact (targetJohn.map.apply_lineMap
    targetCenter targetCarrierPoint factor).symm

theorem pureWZ2IsotropicMap_add_smul
    (center : Point3) (scale scalar : ℝ)
    (base direction : Point3) :
    pureWZ2IsotropicMap center scale (base + scalar • direction) =
      pureWZ2IsotropicMap center scale base +
        scalar • (scale • direction) := by
  unfold pureWZ2IsotropicMap
  module

/-- A positive isotropic image of an ordinary unit-segment tube is contained
in the `scale`-homothety of the canonical midpoint-centered target tube. -/
theorem pureWZ2IsotropicMap_ordinaryCarrier_image_subset_homothety
    {sourceDelta targetDelta : ℝ}
    (center : Point3) {scale : ℝ} (hscale : 1 ≤ scale)
    (source : Kakeya.DeltaTube sourceDelta)
    (hsourceDelta : 0 < sourceDelta)
    (hsource : WZ1PaperTubeInLineClass source)
    (hsourceBase : ‖source.base‖ ≤ 5)
    (hcenter : |center 2| ≤ 1)
    (htargetDelta : scale * sourceDelta ≤ targetDelta) :
    let target := pureWZ2PaperCenteredTube
      (pureWZ2IsotropicPaperTube (targetDelta := targetDelta)
        center scale source)
    pureWZ2IsotropicMap center scale '' source.carrier ⊆
      AffineMap.homothety (wz2PaperTubeMidpoint target) (32 * scale) ''
        target.carrier := by
  dsimp only
  let target := pureWZ2PaperCenteredTube
    (pureWZ2IsotropicPaperTube (targetDelta := targetDelta)
      center scale source)
  let sourceCenter := wz1PaperAxisPointAtHeight source (center 2)
  let targetMidpoint := pureWZ2IsotropicMap center scale sourceCenter
  let imageDirection := scale • wz1PaperDirection source
  let imageLength := scale
  let targetDirection := wz1PaperDirection source
  let factor := 32 * scale
  have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
  have htargetMidpoint : wz2PaperTubeMidpoint target = targetMidpoint := by
    dsimp only [target, targetMidpoint, sourceCenter]
    rw [pureWZ2PaperCenteredTube_midpoint]
    exact pureWZ2IsotropicPaperTube_zeroPoint center hscalePos source hsource
  have htargetDirection : target.direction = targetDirection := by
    rfl
  have hfactorPos : 0 < factor := by
    dsimp only [factor]
    positivity
  rintro imagePoint ⟨sourcePoint, hsourcePoint, rfl⟩
  rcases exists_closest_on_axis hsourceDelta.le source sourcePoint
      hsourcePoint with ⟨parameter, hparameter, hsourceDistance⟩
  let sourceAxisPoint := source.base + parameter • source.direction
  have hsourceAxis : sourceAxisPoint ∈ tubeAxisLine source := ⟨parameter, rfl⟩
  have hsourceAxisNorm : ‖sourceAxisPoint‖ ≤ 6 := by
    calc
      ‖sourceAxisPoint‖ ≤ ‖source.base‖ + ‖parameter • source.direction‖ :=
        norm_add_le _ _
      _ = ‖source.base‖ + |parameter| := by
        rw [norm_smul, Real.norm_eq_abs, source.direction_unit, mul_one]
      _ ≤ 5 + 1 := by
        gcongr
        exact abs_le.mpr ⟨by linarith [hparameter.1], hparameter.2⟩
      _ = 6 := by norm_num
  have haxisHeight : |sourceAxisPoint 2| ≤ 6 :=
    (PiLp.norm_apply_le sourceAxisPoint 2).trans hsourceAxisNorm
  have hheightDifference : |center 2 - sourceAxisPoint 2| ≤ 7 := by
    calc
      |center 2 - sourceAxisPoint 2| ≤ |center 2| + |sourceAxisPoint 2| :=
        abs_sub _ _
      _ ≤ 1 + 6 := add_le_add hcenter haxisHeight
      _ = 7 := by norm_num
  have hsourceAxisDistance : dist sourceCenter sourceAxisPoint ≤ 14 := by
    change dist (wz1PaperAxisPointAtHeight source (center 2))
      sourceAxisPoint ≤ 14
    convert wz1Paper_axisPointAtHeight_dist_le_of_axis_point
      hsource (center 2) 7 hsourceAxis hheightDifference using 1 <;> norm_num
  rcases wz1Paper_axis_exists_parameter hsource hsourceAxis with
    ⟨axisParameter, haxisParameter⟩
  have hsourceCenterAxis : sourceCenter ∈ tubeAxisLine source :=
    wz1PaperAxisPointAtHeight_mem_axis source _
  rcases wz1Paper_axis_exists_parameter hsource hsourceCenterAxis with
    ⟨centerParameter, hcenterParameter⟩
  let relativeParameter := axisParameter - centerParameter
  have hsourceRelative : sourceAxisPoint = sourceCenter +
      relativeParameter • wz1PaperDirection source := by
    rw [haxisParameter, hcenterParameter]
    dsimp only [relativeParameter]
    module
  have hrelativeBound : |relativeParameter| ≤ 14 := by
    have hdistanceEq : dist sourceCenter sourceAxisPoint =
        |relativeParameter| := by
      rw [hsourceRelative, dist_eq_norm]
      have hsub : sourceCenter -
          (sourceCenter + relativeParameter • wz1PaperDirection source) =
        (-relativeParameter) • wz1PaperDirection source := by module
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_neg,
        wz1PaperDirection_norm source, mul_one]
    rw [← hdistanceEq]
    exact hsourceAxisDistance
  let imageAxisPoint := pureWZ2IsotropicMap center scale sourceAxisPoint
  have himageAxis : imageAxisPoint = targetMidpoint +
      relativeParameter • imageDirection := by
    dsimp only [imageAxisPoint]
    rw [hsourceRelative, pureWZ2IsotropicMap_add_smul]
  let contractedPoint := targetMidpoint + factor⁻¹ •
    (pureWZ2IsotropicMap center scale sourcePoint - targetMidpoint)
  let contractedAxisPoint := targetMidpoint + factor⁻¹ •
    (imageAxisPoint - targetMidpoint)
  have hcoefficient :
      |relativeParameter * imageLength / factor| ≤ 1 / 2 := by
    have habsProduct : |relativeParameter * imageLength / factor| =
        |relativeParameter| * scale / factor := by
      dsimp only [imageLength]
      rw [abs_div, abs_mul, abs_of_pos hscalePos, abs_of_pos hfactorPos]
    rw [habsProduct]
    apply (div_le_iff₀ hfactorPos).2
    dsimp only [factor]
    nlinarith
  have hcontractedAxis : contractedAxisPoint ∈
      Kakeya.unitSegment target.base target.direction := by
    let targetParameter : ℝ :=
      1 / 2 + relativeParameter * imageLength / factor
    have htargetParameter : targetParameter ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp only [targetParameter]
      rw [abs_le] at hcoefficient
      constructor <;> linarith
    refine ⟨targetParameter, htargetParameter, ?_⟩
    rw [htargetDirection]
    have himageDirectionEq : imageDirection =
        imageLength • targetDirection := by
      rfl
    have htargetBase : target.base = targetMidpoint -
        (1 / 2 : ℝ) • targetDirection := by
      change (pureWZ2PaperCenteredTube
        (pureWZ2IsotropicPaperTube center scale source)).base = _
      rw [show targetMidpoint = wz1TubeAxisZeroPoint
          (pureWZ2IsotropicPaperTube center scale source) by
        rw [← htargetMidpoint]
        exact pureWZ2PaperCenteredTube_midpoint _]
      rfl
    have hcontractedAxisEq : contractedAxisPoint = targetMidpoint +
        (relativeParameter * imageLength / factor) • targetDirection := by
      dsimp only [contractedAxisPoint]
      rw [himageAxis, show targetMidpoint +
          relativeParameter • imageDirection - targetMidpoint =
        relativeParameter • imageDirection by abel,
        himageDirectionEq, smul_smul, smul_smul]
      congr 2
      field_simp [hfactorPos.ne']
    rw [htargetBase, hcontractedAxisEq]
    dsimp only [targetParameter]
    module
  have hcontractedDistance :
      dist contractedPoint contractedAxisPoint ≤ targetDelta := by
    rw [dist_eq_norm]
    have hdifference : contractedPoint - contractedAxisPoint =
        factor⁻¹ •
          (pureWZ2IsotropicMap center scale sourcePoint -
            pureWZ2IsotropicMap center scale sourceAxisPoint) := by
      dsimp only [contractedPoint, contractedAxisPoint, imageAxisPoint]
      module
    rw [hdifference, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hfactorPos)]
    have himageDifference :
        pureWZ2IsotropicMap center scale sourcePoint -
            pureWZ2IsotropicMap center scale sourceAxisPoint =
          scale • (sourcePoint - sourceAxisPoint) := by
      unfold pureWZ2IsotropicMap
      module
    rw [himageDifference, norm_smul, Real.norm_eq_abs, abs_of_pos hscalePos]
    calc
      factor⁻¹ * (scale * ‖sourcePoint - sourceAxisPoint‖) =
          ‖sourcePoint - sourceAxisPoint‖ / 32 := by
        dsimp only [factor]
        field_simp [hscalePos.ne']
      _ ≤ sourceDelta / 32 := by
        gcongr
        simpa [sourceAxisPoint, dist_eq_norm] using hsourceDistance
      _ ≤ targetDelta := by
        have hsourceTarget : sourceDelta ≤ targetDelta := by
          exact (show sourceDelta ≤ scale * sourceDelta by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hscale hsourceDelta.le).trans
            htargetDelta
        nlinarith [hsourceTarget, hsourceDelta]
  have hcontractedCarrier : contractedPoint ∈ target.carrier :=
    Metric.mem_cthickening_of_dist_le contractedPoint contractedAxisPoint
      targetDelta _ hcontractedAxis hcontractedDistance
  refine ⟨contractedPoint, hcontractedCarrier, ?_⟩
  change (AffineMap.homothety (wz2PaperTubeMidpoint target) factor)
      contractedPoint = pureWZ2IsotropicMap center scale sourcePoint
  rw [htargetMidpoint]
  rw [AffineMap.homothety_apply]
  change factor • (contractedPoint - targetMidpoint) + targetMidpoint =
    pureWZ2IsotropicMap center scale sourcePoint
  have hcontracted : contractedPoint - targetMidpoint =
      factor⁻¹ •
        (pureWZ2IsotropicMap center scale sourcePoint - targetMidpoint) := by
    dsimp only [contractedPoint]
    abel
  rw [hcontracted, smul_smul]
  have hcancel : factor * factor⁻¹ = 1 :=
    mul_inv_cancel₀ hfactorPos.ne'
  rw [hcancel, one_smul]
  abel

/-- The inverse determinant of the source-John to target-John coordinate
change has the expected `scale⁻³` Jacobian and parent-radius ratio. -/
theorem pureWZ2IsotropicJohnCoordinateChange_inverse_det_le
    {sourceRho targetRho : ℝ}
    (hsourceRho : 0 < sourceRho) (htargetRho : 0 < targetRho)
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (sourceParent : Kakeya.DeltaTube sourceRho)
    (targetParent : Kakeya.DeltaTube targetRho)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent) :
    ENNReal.ofReal |LinearMap.det
        ((pureWZ2IsotropicJohnCoordinateChange center scale hscale
          sourceJohn targetJohn).symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
      (432 : ENNReal) * Kakeya.realRpowENN targetRho 2 *
        ENNReal.ofReal (1 + 2 * targetRho) *
        ENNReal.ofReal (1 / (scale ^ 3 * sourceRho ^ 2)) := by
  let coordinateChange := pureWZ2IsotropicJohnCoordinateChange center scale
    hscale sourceJohn targetJohn
  have hsourceDetLower :=
    wz2Paper_outerJohn_abs_det_lower sourceParent hsourceRho
  have htargetDetUpper :=
    pureWZ2_outerJohn_detENN_le_general htargetRho targetParent targetJohn
  have hisotropicDet :
      |LinearMap.det
        ((pureWZ2IsotropicAffineEquiv center scale hscale).linear :
          Point3 →ₗ[ℝ] Point3)| = scale ^ 3 := by
    change |LinearMap.det (scale • (LinearMap.id : Point3 →ₗ[ℝ] Point3))| = _
    rw [LinearMap.det_smul]
    have hfinrank : Module.finrank ℝ Point3 = 3 := by simp [Point3]
    rw [hfinrank, LinearMap.det_id, mul_one, abs_pow, abs_of_pos hscale]
  have hlinear : coordinateChange.linear =
      sourceJohn.map.symm.linear.trans
        ((pureWZ2IsotropicAffineEquiv center scale hscale).linear.trans
          targetJohn.map.linear) := rfl
  have hsourceLinear : (sourceJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3) =
      sourceJohn.parent_convex_body.outerJohnEllipsoidMap := rfl
  have htargetLinear : (targetJohn.map.linear : Point3 →ₗ[ℝ] Point3) =
      targetJohn.parent_convex_body.outerJohnEllipsoidMap.symm := rfl
  have hcoordinateDet : |LinearMap.det
      (coordinateChange.linear : Point3 →ₗ[ℝ] Point3)| =
      |LinearMap.det (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)| * scale ^ 3 *
      |LinearMap.det (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)|⁻¹ := by
    rw [hlinear]
    have hcomposition :
        ((sourceJohn.map.symm.linear.trans
          ((pureWZ2IsotropicAffineEquiv center scale hscale).linear.trans
            targetJohn.map.linear) : Point3 ≃ₗ[ℝ] Point3) :
              Point3 →ₗ[ℝ] Point3) =
          (targetJohn.map.linear : Point3 →ₗ[ℝ] Point3).comp
            (((pureWZ2IsotropicAffineEquiv center scale hscale).linear :
              Point3 →ₗ[ℝ] Point3).comp
              (sourceJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3)) := by
      ext point
      rfl
    rw [hcomposition, LinearMap.det_comp, LinearMap.det_comp, abs_mul,
      abs_mul, hsourceLinear, htargetLinear, LinearEquiv.det_coe_symm,
      abs_inv, hisotropicDet]
    ring
  have hsourceDetPos : 0 < |LinearMap.det
      (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr (LinearEquiv.isUnit_det'
      sourceJohn.parent_convex_body.outerJohnEllipsoidMap).ne_zero
  have htargetDetPos : 0 < |LinearMap.det
      (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr (LinearEquiv.isUnit_det'
      targetJohn.parent_convex_body.outerJohnEllipsoidMap).ne_zero
  have htargetDetReal : |LinearMap.det
      (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)| ≤
      108 * targetRho ^ 2 * (1 + 2 * targetRho) := by
    have hnonneg : 0 ≤ 108 * targetRho ^ 2 * (1 + 2 * targetRho) := by
      positivity
    rw [show Kakeya.realRpowENN targetRho 2 =
      ENNReal.ofReal (targetRho ^ 2) by
        simp [Kakeya.realRpowENN, Real.rpow_two],
      ← ENNReal.ofReal_ofNat (n := 108),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 108),
      ← ENNReal.ofReal_mul
        (by positivity : 0 ≤ 108 * targetRho ^ 2)] at htargetDetUpper
    exact (ENNReal.ofReal_le_ofReal_iff hnonneg).mp htargetDetUpper
  have hinverseReal : |LinearMap.det
      (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
      432 * targetRho ^ 2 * (1 + 2 * targetRho) /
        (scale ^ 3 * sourceRho ^ 2) := by
    have hsymm : coordinateChange.symm.linear =
        coordinateChange.linear.symm := rfl
    rw [hsymm, LinearEquiv.det_coe_symm, abs_inv, hcoordinateDet]
    let sourceDet := |LinearMap.det
      (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)|
    let targetDet := |LinearMap.det
      (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)|
    have hdenominatorPos : 0 < sourceDet * scale ^ 3 * targetDet⁻¹ := by
      positivity
    apply (inv_le_iff_one_le_mul₀ hdenominatorPos).2
    have hsourceProduct : scale ^ 3 * sourceRho ^ 2 ≤
        4 * (sourceDet * scale ^ 3) := by
      dsimp only [sourceDet]
      have hmul := mul_le_mul_of_nonneg_left hsourceDetLower
        (pow_nonneg hscale.le 3)
      nlinarith
    dsimp only [sourceDet, targetDet]
    field_simp [hscale.ne', hsourceRho.ne', hsourceDetPos.ne',
      htargetDetPos.ne']
    nlinarith [htargetDetReal]
  calc
    ENNReal.ofReal |LinearMap.det
        (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
      ENNReal.ofReal (432 * targetRho ^ 2 * (1 + 2 * targetRho) /
        (scale ^ 3 * sourceRho ^ 2)) := ENNReal.ofReal_mono hinverseReal
    _ = (432 : ENNReal) * Kakeya.realRpowENN targetRho 2 *
        ENNReal.ofReal (1 + 2 * targetRho) *
        ENNReal.ofReal (1 / (scale ^ 3 * sourceRho ^ 2)) := by
      rw [show Kakeya.realRpowENN targetRho 2 =
        ENNReal.ofReal (targetRho ^ 2) by
          simp [Kakeya.realRpowENN, Real.rpow_two],
        ← ENNReal.ofReal_ofNat (n := 432),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 432),
        ← ENNReal.ofReal_mul
          (by positivity : 0 ≤ 432 * targetRho ^ 2),
        ← ENNReal.ofReal_mul
          (by positivity : 0 ≤ 432 * targetRho ^ 2 * (1 + 2 * targetRho))]
      congr 1
      ring

/-- Packetwise actual-John CWA after the final positive similarity.  The
source packet may be any injectively indexed subfamily of one complete source
fiber; the target body is the genuine target actual-John body. -/
theorem pureWZ2_isotropicCenteredTargetPacket_cwa
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    (sourceParent : Fin sourceCoarse.card)
    {sourceConstant : ENNReal}
    (sourceFiber : WZ2PaperPureUnitRescaledFullFiberData
      (fine := sourceFine) (coarse := sourceCoarse)
      sourceParent sourceConstant)
    (center : Point3) {scale : ℝ} (hscale : 1 ≤ scale)
    (hcenter : |center 2| ≤ 1)
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : scale * sourceDelta ≤ targetDelta)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (targetBodies : Kakeya.Streamlined.BodyFamily)
    (targetIndex : Fin targetBodies.card → Fin sourceFine.card)
    (targetIndex_injective : Function.Injective targetIndex)
    (target_mem : ∀ index, targetIndex index ∈
      wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent)
    (targetParent : Kakeya.DeltaTube targetRho)
    (targetNormalization : WZ2PaperAssouadUnitRescalingData targetParent)
    (target_mem_parent : ∀ index,
      (pureWZ2PaperCenteredTube
        (pureWZ2IsotropicPaperTube (targetDelta := targetDelta) center scale
          (sourceFine.tube (targetIndex index)))).carrier ⊆
        targetParent.carrier)
    (target_body : ∀ index,
      (targetBodies.body index).carrier = targetNormalization.map ''
        (pureWZ2PaperCenteredTube
          (pureWZ2IsotropicPaperTube (targetDelta := targetDelta) center scale
            (sourceFine.tube (targetIndex index)))).carrier)
    (weight K : ENNReal)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hcardinality :
      weight * ((wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent).card : ENNReal) ≤
      K * targetBodies.enncard) :
    WZ2PaperBodyConvexWolffBound targetBodies
      (ENNReal.ofReal (27 * (2 * (32 * scale) - 1) ^ 3) *
        ENNReal.ofReal |LinearMap.det
          ((pureWZ2IsotropicJohnCoordinateChange center scale
            (lt_of_lt_of_le (by norm_num) hscale) sourceFiber.normalization
              targetNormalization).symm.linear : Point3 →ₗ[ℝ] Point3)| *
        ((weight⁻¹ * K) * sourceConstant)) := by
  let sourcePacket := pureWZ2ActualJohnSourcePacketBodyFamily
    sourceParent sourceFiber.normalization targetBodies targetIndex target_mem
  let coordinateChange := pureWZ2IsotropicJohnCoordinateChange
    center scale (lt_of_lt_of_le (by norm_num) hscale)
      sourceFiber.normalization targetNormalization
  let factor := 32 * scale
  have hfactor : 1 ≤ factor := by
    dsimp only [factor]
    nlinarith
  let targetCenter : Fin targetBodies.card → Point3 := fun index =>
    targetNormalization.map
      (wz2PaperTubeMidpoint
        (pureWZ2PaperCenteredTube
          (pureWZ2IsotropicPaperTube (targetDelta := targetDelta) center scale
            (sourceFine.tube (targetIndex index)))))
  have htargetDeltaPos : 0 < targetDelta :=
    (mul_pos (lt_of_lt_of_le (by norm_num) hscale) hsourceDelta).trans_le
      htargetDelta
  have htargetBody : ∀ index,
      JohnEllipsoid.IsConvexBody (targetBodies.body index).carrier := by
    intro index
    rw [target_body]
    let tube := pureWZ2PaperCenteredTube
      (pureWZ2IsotropicPaperTube (targetDelta := targetDelta) center scale
        (sourceFine.tube (targetIndex index)))
    let sourceBody := wz2_paper_ordinary_tube_isConvexBody tube htargetDeltaPos
    let homeomorph := targetNormalization.map.toHomeomorphOfFiniteDimensional
    refine ⟨sourceBody.1.affine_image targetNormalization.map.toAffineMap, ?_, ?_⟩
    · change IsCompact (homeomorph '' tube.carrier)
      exact (homeomorph.isCompact_image).2 sourceBody.2.1
    · change (interior (homeomorph '' tube.carrier)).Nonempty
      rw [← homeomorph.image_interior]
      exact sourceBody.2.2.image homeomorph
  have htargetBound : ∀ index, (targetBodies.body index).carrier ⊆
      Metric.closedBall (0 : Point3) 1 := by
    intro index point hpoint
    rw [target_body] at hpoint
    rcases hpoint with ⟨targetPoint, htargetPoint, rfl⟩
    have hellipsoid :=
      targetNormalization.parent_convex_body.outerJohnEllipsoid_spec.1
        (target_mem_parent index htargetPoint)
    have himage : targetNormalization.map targetPoint ∈
        targetNormalization.map ''
          targetNormalization.parent_convex_body.outerJohnEllipsoid :=
      ⟨targetPoint, hellipsoid, rfl⟩
    rw [targetNormalization.outerJohn_image] at himage
    exact himage
  have htargetCenter : ∀ index,
      targetCenter index ∈ (targetBodies.body index).carrier := by
    intro index
    rw [target_body]
    exact ⟨wz2PaperTubeMidpoint
        (pureWZ2PaperCenteredTube
          (pureWZ2IsotropicPaperTube (targetDelta := targetDelta) center scale
            (sourceFine.tube (targetIndex index)))),
      wz2_paper_tubeMidpoint_mem_carrier _ htargetDeltaPos.le, rfl⟩
  have hcarrier : ∀ index, coordinateChange ''
        ((pureWZ2ActualJohnSourcePacketBodyFamily
          sourceParent sourceFiber.normalization targetBodies
            targetIndex target_mem).body index).carrier ⊆
      AffineMap.homothety (targetCenter index) factor ''
        (targetBodies.body index).carrier := by
    intro index
    rw [target_body]
    have hordinary :=
      pureWZ2IsotropicMap_ordinaryCarrier_image_subset_homothety
        center hscale (sourceFine.tube (targetIndex index)) hsourceDelta
        (hsourceLine _) (hsourceBase _) hcenter htargetDelta
    have hraw := pureWZ2IsotropicJohnCoordinateChange_carrier
      center scale (lt_of_lt_of_le (by norm_num) hscale)
      sourceFiber.normalization targetNormalization factor
      (wz2PaperTubeMidpoint
        (pureWZ2PaperCenteredTube
          (pureWZ2IsotropicPaperTube (targetDelta := targetDelta) center scale
            (sourceFine.tube (targetIndex index)))))
      (sourceFine.tube (targetIndex index)).carrier
      (pureWZ2PaperCenteredTube
        (pureWZ2IsotropicPaperTube (targetDelta := targetDelta) center scale
          (sourceFine.tube (targetIndex index)))).carrier hordinary
    have hsourceIndex :
        ((wz2PaperOrdinaryFullFiberIndexEquiv sourceParent)
          (pureWZ2ActualJohnPacketSourceBodyIndex
            sourceParent targetIndex target_mem index)).1 =
          targetIndex index := by
      simp [pureWZ2ActualJohnPacketSourceBodyIndex]
    simpa only [coordinateChange, factor, targetCenter,
      pureWZ2ActualJohnSourcePacketBodyFamily,
      wz2PaperPureUnitRescaledFullFiberBodyFamily, hsourceIndex] using hraw
  have hresult := pureWZ2_actualJohnPacket_cwa_of_affine_homothetic_envelope
    sourceParent sourceFiber targetBodies targetIndex targetIndex_injective
    target_mem weight K hweightZero hweightTop hcardinality
    coordinateChange factor 1 hfactor (by norm_num) htargetBody htargetBound
    targetCenter htargetCenter hcarrier
  simpa [coordinateChange, factor] using hresult

end Kakeya.Assouad

end
