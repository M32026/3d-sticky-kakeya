import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalRepresentativeSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalOrdinaryCarrierEnvelope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ActualJohnPacketCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicQuotientScheduleCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.OuterJohnInverseVolume

/-!
# Actual-John packet geometry for the affine-diagonal family

The source and target actual-John charts are joined through the same fixed
horizontal rotation and diagonal affine map used to construct the target
family.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- Exact Jacobian of the fixed-rotation affine-diagonal equivalence. -/
theorem pureWZ2AffineDiagonalAffineEquivCentered_abs_det
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale isotropicScale : ℝ)
    (hheight : 0 < heightScale)
    (htransverse : 0 < transverseScale)
    (hisotropic : 0 < isotropicScale) :
    |LinearMap.det
      ((pureWZ2AffineDiagonalAffineEquivCentered frameSlope center
        heightScale transverseScale isotropicScale hheight.ne'
          htransverse.ne' hisotropic.ne').linear : Point3 →ₗ[ℝ] Point3)| =
      heightScale * transverseScale * isotropicScale ^ 3 := by
  let linear : Point3 →ₗ[ℝ] Point3 :=
    (pureWZ2AffineDiagonalAffineEquivCentered frameSlope center
      heightScale transverseScale isotropicScale hheight.ne'
        htransverse.ne' hisotropic.ne').linear
  let basis : Module.Basis (Fin 3) ℝ Point3 := PiLp.basisFun 2 ℝ (Fin 3)
  have hmatrix : LinearMap.toMatrix basis basis linear =
      !![isotropicScale / pureWZ2HorizontalNorm frameSlope,
          isotropicScale * frameSlope / pureWZ2HorizontalNorm frameSlope, 0;
        -(isotropicScale * transverseScale * frameSlope) /
          pureWZ2HorizontalNorm frameSlope,
          isotropicScale * transverseScale /
            pureWZ2HorizontalNorm frameSlope, 0;
        0, 0, isotropicScale * heightScale] := by
    ext i j
    have hentry : (LinearMap.toMatrix basis basis linear) i j =
        (linear (basis j)) i := by
      rw [LinearMap.toMatrix_apply]
      exact PiLp.basisFun_repr 2 ℝ (Fin 3) (linear (basis j)) i
    rw [hentry]
    fin_cases i <;> fin_cases j <;>
      simp [linear, basis, pureWZ2AffineDiagonalAffineEquivCentered,
        pureWZ2AffineDiagonalLinearEquiv, pureWZ2AffineDiagonalLinear,
        pureWZ2HorizontalRotation, pureWZ2HorizontalRotationEquiv,
        pureWZ2HorizontalRotationLinear, PiLp.basisFun_apply, point3] <;> ring
  have hnorm := pureWZ2HorizontalNorm_sq frameSlope
  have hnormPos := pureWZ2HorizontalNorm_pos frameSlope
  change |LinearMap.det linear| = _
  rw [← LinearMap.det_toMatrix basis linear, hmatrix]
  simp [Matrix.det_fin_three]
  field_simp [hnormPos.ne']
  rw [hnorm]
  have hdenominator : 1 + frameSlope ^ 2 ≠ 0 := by positivity
  rw [show 1 - -frameSlope ^ 2 = 1 + frameSlope ^ 2 by ring]
  have hcancel :
      isotropicScale ^ 3 * transverseScale * heightScale *
          (1 + frameSlope ^ 2) / (1 + frameSlope ^ 2) =
        isotropicScale ^ 3 * transverseScale * heightScale := by
    field_simp [hdenominator]
  rw [hcancel]
  have hproductPos :
      0 < isotropicScale ^ 3 * transverseScale * heightScale := by
    positivity
  rw [abs_of_pos hproductPos]

/-- Source-John to target-John coordinates through the affine-diagonal map. -/
noncomputable def pureWZ2AffineDiagonalJohnCoordinateChange
    {sourceRho targetRho : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hheight : 0 < heightScale) (htransverse : 0 < transverseScale)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  sourceJohn.map.symm.trans
    ((pureWZ2AffineDiagonalAffineEquivCentered frameSlope center heightScale
      transverseScale 1 hheight.ne' htransverse.ne' one_ne_zero).trans
        targetJohn.map)

@[simp] theorem pureWZ2AffineDiagonalJohnCoordinateChange_apply_sourceMap
    {sourceRho targetRho : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hheight : 0 < heightScale) (htransverse : 0 < transverseScale)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (point : Point3) :
    pureWZ2AffineDiagonalJohnCoordinateChange frameSlope center heightScale
        transverseScale hheight htransverse sourceJohn targetJohn
          (sourceJohn.map point) =
      targetJohn.map
        (pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale 1 point) := by
  simp [pureWZ2AffineDiagonalJohnCoordinateChange, AffineEquiv.trans_apply]

/-- A carrier envelope for the affine-diagonal map transports through both
actual-John charts. -/
theorem pureWZ2AffineDiagonalJohnCoordinateChange_carrier
    {sourceRho targetRho : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hheight : 0 < heightScale) (htransverse : 0 < transverseScale)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (factor : ℝ) (targetCenter : Point3)
    (sourceSet targetSet : Set Point3)
    (hcarrier : pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale 1 '' sourceSet ⊆
      AffineMap.homothety targetCenter factor '' targetSet) :
    pureWZ2AffineDiagonalJohnCoordinateChange frameSlope center heightScale
        transverseScale hheight htransverse sourceJohn targetJohn ''
          (sourceJohn.map '' sourceSet) ⊆
      AffineMap.homothety (targetJohn.map targetCenter) factor ''
        (targetJohn.map '' targetSet) := by
  rintro targetPoint ⟨sourceJohnPoint,
    ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
  rcases hcarrier ⟨sourcePoint, hsourcePoint, rfl⟩ with
    ⟨targetCarrierPoint, htargetCarrierPoint, hhomothety⟩
  refine ⟨targetJohn.map targetCarrierPoint,
    ⟨targetCarrierPoint, htargetCarrierPoint, rfl⟩, ?_⟩
  rw [pureWZ2AffineDiagonalJohnCoordinateChange_apply_sourceMap]
  rw [← hhomothety]
  change (AffineMap.lineMap
      (targetJohn.map targetCenter)
      (targetJohn.map targetCarrierPoint)) factor =
    targetJohn.map ((AffineMap.lineMap targetCenter targetCarrierPoint) factor)
  exact (targetJohn.map.apply_lineMap
    targetCenter targetCarrierPoint factor).symm

/-- The inverse determinant of the affine-diagonal source-John to
target-John coordinate change. -/
theorem pureWZ2AffineDiagonalJohnCoordinateChange_inverse_det_le
    {sourceRho targetRho : ℝ}
    (hsourceRho : 0 < sourceRho) (htargetRho : 0 < targetRho)
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hheight : 0 < heightScale) (htransverse : 0 < transverseScale)
    (sourceParent : Kakeya.DeltaTube sourceRho)
    (targetParent : Kakeya.DeltaTube targetRho)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent) :
    ENNReal.ofReal |LinearMap.det
        ((pureWZ2AffineDiagonalJohnCoordinateChange frameSlope center
          heightScale transverseScale hheight htransverse sourceJohn
            targetJohn).symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
      (432 : ENNReal) * Kakeya.realRpowENN targetRho 2 *
        ENNReal.ofReal (1 + 2 * targetRho) *
        ENNReal.ofReal
          (1 / (heightScale * transverseScale * sourceRho ^ 2)) := by
  let coordinateChange := pureWZ2AffineDiagonalJohnCoordinateChange
    frameSlope center heightScale transverseScale hheight htransverse
      sourceJohn targetJohn
  have hsourceDetLower :=
    wz2Paper_outerJohn_abs_det_lower sourceParent hsourceRho
  have htargetDetUpper :=
    pureWZ2_outerJohn_detENN_le_general htargetRho targetParent targetJohn
  have hmapDet := pureWZ2AffineDiagonalAffineEquivCentered_abs_det
    frameSlope center heightScale transverseScale 1 hheight htransverse
      (by norm_num)
  have hlinear : coordinateChange.linear =
      sourceJohn.map.symm.linear.trans
        ((pureWZ2AffineDiagonalAffineEquivCentered frameSlope center
          heightScale transverseScale 1 hheight.ne' htransverse.ne'
            one_ne_zero).linear.trans targetJohn.map.linear) := rfl
  have hsourceLinear :
      (sourceJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3) =
        sourceJohn.parent_convex_body.outerJohnEllipsoidMap := rfl
  have htargetLinear :
      (targetJohn.map.linear : Point3 →ₗ[ℝ] Point3) =
        targetJohn.parent_convex_body.outerJohnEllipsoidMap.symm := rfl
  have hcoordinateDet : |LinearMap.det
      (coordinateChange.linear : Point3 →ₗ[ℝ] Point3)| =
      |LinearMap.det
        (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)| * (heightScale * transverseScale) *
      |LinearMap.det
        (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)|⁻¹ := by
    rw [hlinear]
    have hcomposition :
        ((sourceJohn.map.symm.linear.trans
          ((pureWZ2AffineDiagonalAffineEquivCentered frameSlope center
            heightScale transverseScale 1 hheight.ne' htransverse.ne'
              one_ne_zero).linear.trans targetJohn.map.linear) :
                Point3 ≃ₗ[ℝ] Point3) : Point3 →ₗ[ℝ] Point3) =
          (targetJohn.map.linear : Point3 →ₗ[ℝ] Point3).comp
            (((pureWZ2AffineDiagonalAffineEquivCentered frameSlope center
              heightScale transverseScale 1 hheight.ne' htransverse.ne'
                one_ne_zero).linear : Point3 →ₗ[ℝ] Point3).comp
              (sourceJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3)) := by
      ext point
      rfl
    rw [hcomposition, LinearMap.det_comp, LinearMap.det_comp, abs_mul,
      abs_mul, hsourceLinear, htargetLinear, LinearEquiv.det_coe_symm,
      abs_inv, hmapDet]
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
        (heightScale * transverseScale * sourceRho ^ 2) := by
    have hsymm : coordinateChange.symm.linear =
        coordinateChange.linear.symm := rfl
    rw [hsymm, LinearEquiv.det_coe_symm, abs_inv, hcoordinateDet]
    let sourceDet := |LinearMap.det
      (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)|
    let targetDet := |LinearMap.det
      (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)|
    have hdenominatorPos :
        0 < sourceDet * (heightScale * transverseScale) * targetDet⁻¹ := by
      positivity
    apply (inv_le_iff_one_le_mul₀ hdenominatorPos).2
    have hsourceProduct :
        heightScale * transverseScale * sourceRho ^ 2 ≤
          4 * (sourceDet * (heightScale * transverseScale)) := by
      dsimp only [sourceDet]
      have hmul := mul_le_mul_of_nonneg_left hsourceDetLower
        (mul_nonneg hheight.le htransverse.le)
      nlinarith
    dsimp only [sourceDet, targetDet]
    field_simp [hheight.ne', htransverse.ne', hsourceRho.ne',
      hsourceDetPos.ne', htargetDetPos.ne']
    nlinarith [htargetDetReal]
  calc
    ENNReal.ofReal |LinearMap.det
        (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
      ENNReal.ofReal (432 * targetRho ^ 2 * (1 + 2 * targetRho) /
        (heightScale * transverseScale * sourceRho ^ 2)) :=
          ENNReal.ofReal_mono hinverseReal
    _ = (432 : ENNReal) * Kakeya.realRpowENN targetRho 2 *
        ENNReal.ofReal (1 + 2 * targetRho) *
        ENNReal.ofReal
          (1 / (heightScale * transverseScale * sourceRho ^ 2)) := by
      rw [show Kakeya.realRpowENN targetRho 2 =
        ENNReal.ofReal (targetRho ^ 2) by
          simp [Kakeya.realRpowENN, Real.rpow_two],
        ← ENNReal.ofReal_ofNat (n := 432),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 432),
        ← ENNReal.ofReal_mul
          (by positivity : 0 ≤ 432 * targetRho ^ 2),
        ← ENNReal.ofReal_mul
          (by positivity : 0 ≤ 432 * targetRho ^ 2 *
            (1 + 2 * targetRho))]
      congr 1
      ring

/-- A bounded source ordinary carrier maps into a controlled homothety of
any positive-oriented ordinary target on the exact affine image line. -/
theorem pureWZ2AffineDiagonalMap_ordinaryCarrier_image_subset_homothety_of_axis
    {sourceDelta targetDelta : ℝ}
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hheight : 1 ≤ heightScale)
    (htransverse : 0 < transverseScale)
    (htransverseOne : transverseScale ≤ 1)
    (hcenter : ‖center‖ ≤ 2)
    (source : Kakeya.DeltaTube sourceDelta)
    (target : Kakeya.DeltaTube targetDelta)
    (hsourceDelta : 0 < sourceDelta)
    (hsourceTarget : sourceDelta ≤ targetDelta)
    (hsourceBase : ‖source.base‖ ≤ 5)
    (htarget : WZ1PaperTubeInLineClass target)
    (htargetDirection : target.direction = wz1PaperDirection target)
    (htargetMidpoint : ‖wz2PaperTubeMidpoint target‖ ≤ 3)
    (haxis : tubeAxisLine target =
      pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale 1 '' tubeAxisLine source) :
    pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale 1 '' source.carrier ⊆
      AffineMap.homothety (wz2PaperTubeMidpoint target)
        (32 * heightScale) '' target.carrier := by
  let factor := 32 * heightScale
  let targetMidpoint := wz2PaperTubeMidpoint target
  have hheightPos : 0 < heightScale := lt_of_lt_of_le (by norm_num) hheight
  have hfactorPos : 0 < factor := by dsimp only [factor]; positivity
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
  let imageAxisPoint :=
    pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
      transverseScale 1 sourceAxisPoint
  have himageAxis : imageAxisPoint ∈ tubeAxisLine target := by
    rw [haxis]
    exact ⟨sourceAxisPoint, hsourceAxis, rfl⟩
  have htargetMidpointAxis : targetMidpoint ∈ tubeAxisLine target := by
    exact wz2_paper_unitSegment_subset_axisLine target
      ⟨1 / 2, by constructor <;> norm_num, rfl⟩
  rcases wz1Paper_axis_exists_parameter htarget himageAxis with
    ⟨imageParameter, himageParameter⟩
  rcases wz1Paper_axis_exists_parameter htarget htargetMidpointAxis with
    ⟨midpointParameter, hmidpointParameter⟩
  let relativeParameter := imageParameter - midpointParameter
  have himageRelative : imageAxisPoint = targetMidpoint +
      relativeParameter • wz1PaperDirection target := by
    rw [himageParameter, hmidpointParameter]
    dsimp only [relativeParameter]
    module
  have himageAxisNorm : ‖imageAxisPoint‖ ≤ 8 * heightScale := by
    dsimp only [imageAxisPoint]
    rw [pureWZ2AffineDiagonalMapCentered_eq_linear_sub_center]
    calc
      ‖pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale 1
          (sourceAxisPoint - center)‖ ≤
        heightScale * ‖sourceAxisPoint - center‖ :=
          pureWZ2AffineDiagonalLinear_norm_le_height frameSlope hheight
            htransverse.le htransverseOne _
      _ ≤ heightScale * 8 := by
        gcongr
        exact (norm_sub_le _ _).trans (by linarith)
      _ = 8 * heightScale := by ring
  have himageAxisDistance : dist targetMidpoint imageAxisPoint ≤
      11 * heightScale := by
    rw [dist_eq_norm]
    calc
      ‖targetMidpoint - imageAxisPoint‖ ≤
          ‖targetMidpoint‖ + ‖imageAxisPoint‖ := norm_sub_le _ _
      _ ≤ 3 + 8 * heightScale := by gcongr
      _ ≤ 11 * heightScale := by nlinarith
  have hrelativeBound : |relativeParameter| ≤ 11 * heightScale := by
    have hdistanceEq : dist targetMidpoint imageAxisPoint =
        |relativeParameter| := by
      rw [himageRelative, dist_eq_norm]
      have hsubtraction : targetMidpoint -
          (targetMidpoint + relativeParameter • wz1PaperDirection target) =
        (-relativeParameter) • wz1PaperDirection target := by module
      rw [hsubtraction, norm_smul, Real.norm_eq_abs, abs_neg,
        wz1PaperDirection_norm target, mul_one]
    rw [← hdistanceEq]
    exact himageAxisDistance
  let contractedPoint := targetMidpoint + factor⁻¹ •
    (pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
      transverseScale 1 sourcePoint - targetMidpoint)
  let contractedAxisPoint := targetMidpoint + factor⁻¹ •
    (imageAxisPoint - targetMidpoint)
  have hcoefficient : |relativeParameter / factor| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hfactorPos]
    apply (div_le_iff₀ hfactorPos).2
    dsimp only [factor]
    nlinarith
  have hcontractedAxis : contractedAxisPoint ∈
      Kakeya.unitSegment target.base target.direction := by
    let targetParameter := 1 / 2 + relativeParameter / factor
    have htargetParameter : targetParameter ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp only [targetParameter]
      rw [abs_le] at hcoefficient
      constructor <;> linarith
    refine ⟨targetParameter, htargetParameter, ?_⟩
    have htargetBase : target.base = targetMidpoint -
        (1 / 2 : ℝ) • target.direction := by
      dsimp only [targetMidpoint, wz2PaperTubeMidpoint]
      module
    have hcontractedAxisEq : contractedAxisPoint = targetMidpoint +
        (relativeParameter / factor) • target.direction := by
      dsimp only [contractedAxisPoint]
      rw [himageRelative, htargetDirection]
      rw [show targetMidpoint +
          relativeParameter • wz1PaperDirection target - targetMidpoint =
        relativeParameter • wz1PaperDirection target by abel, smul_smul]
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
          pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale 1
            (sourcePoint - sourceAxisPoint) := by
      dsimp only [contractedPoint, contractedAxisPoint, imageAxisPoint]
      rw [show
        (targetMidpoint + factor⁻¹ •
            (pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
              transverseScale 1 sourcePoint - targetMidpoint)) -
          (targetMidpoint + factor⁻¹ •
            (pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
              transverseScale 1 sourceAxisPoint - targetMidpoint)) =
        factor⁻¹ •
          (pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
              transverseScale 1 sourcePoint -
            pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
              transverseScale 1 sourceAxisPoint) by module]
      rw [pureWZ2AffineDiagonalMapCentered_sub]
    rw [hdifference, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hfactorPos)]
    calc
      factor⁻¹ *
          ‖pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale 1
            (sourcePoint - sourceAxisPoint)‖ ≤
        factor⁻¹ * (heightScale * ‖sourcePoint - sourceAxisPoint‖) := by
          gcongr
          exact pureWZ2AffineDiagonalLinear_norm_le_height frameSlope
            hheight htransverse.le htransverseOne _
      _ ≤ factor⁻¹ * (heightScale * sourceDelta) := by
          gcongr
          simpa [sourceAxisPoint, dist_eq_norm] using hsourceDistance
      _ ≤ sourceDelta := by
        have hsourceNonneg : 0 ≤ sourceDelta := hsourceDelta.le
        dsimp only [factor]
        rw [show (32 * heightScale)⁻¹ * (heightScale * sourceDelta) =
            sourceDelta / 32 by field_simp [hheightPos.ne'] <;> ring]
        nlinarith
      _ ≤ targetDelta := hsourceTarget
  have hcontractedCarrier : contractedPoint ∈ target.carrier :=
    Metric.mem_cthickening_of_dist_le contractedPoint contractedAxisPoint
      targetDelta _ hcontractedAxis hcontractedDistance
  refine ⟨contractedPoint, hcontractedCarrier, ?_⟩
  rw [AffineMap.homothety_apply]
  change factor • (contractedPoint - targetMidpoint) + targetMidpoint =
    pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
      transverseScale 1 sourcePoint
  have hcontracted : contractedPoint - targetMidpoint = factor⁻¹ •
      (pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale 1 sourcePoint - targetMidpoint) := by
    dsimp only [contractedPoint]
    abel
  rw [hcontracted, smul_smul,
    mul_inv_cancel₀ hfactorPos.ne', one_smul]
  abel

/-- Packetwise actual-John CWA for an ordinary target family carried by the
exact affine-diagonal image lines. -/
theorem pureWZ2_affineDiagonalTargetPacket_cwa
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    (sourceParent : Fin sourceCoarse.card)
    {sourceConstant : ENNReal}
    (sourceFiber : WZ2PaperPureUnitRescaledFullFiberData
      (fine := sourceFine) (coarse := sourceCoarse)
      sourceParent sourceConstant)
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hheight : 1 ≤ heightScale)
    (htransverse : 0 < transverseScale)
    (htransverseOne : transverseScale ≤ 1)
    (hcenter : ‖center‖ ≤ 2)
    (hsourceDelta : 0 < sourceDelta)
    (hsourceTarget : sourceDelta ≤ targetDelta)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (targetBodies : Kakeya.Streamlined.BodyFamily)
    (targetIndex : Fin targetBodies.card → Fin sourceFine.card)
    (targetIndex_injective : Function.Injective targetIndex)
    (target_mem : ∀ index, targetIndex index ∈
      wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent)
    (targetTube : Fin targetBodies.card → Kakeya.DeltaTube targetDelta)
    (htargetLine : ∀ index, WZ1PaperTubeInLineClass (targetTube index))
    (htargetDirection : ∀ index,
      (targetTube index).direction = wz1PaperDirection (targetTube index))
    (htargetMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (targetTube index)‖ ≤ 3)
    (htargetAxis : ∀ index, tubeAxisLine (targetTube index) =
      pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale 1 ''
          tubeAxisLine (sourceFine.tube (targetIndex index)))
    (targetParent : Kakeya.DeltaTube targetRho)
    (targetNormalization : WZ2PaperAssouadUnitRescalingData targetParent)
    (target_mem_parent : ∀ index,
      (targetTube index).carrier ⊆ targetParent.carrier)
    (target_body : ∀ index,
      (targetBodies.body index).carrier = targetNormalization.map ''
        (targetTube index).carrier)
    (weight K : ENNReal)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hcardinality :
      weight * ((wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent).card : ENNReal) ≤
      K * targetBodies.enncard) :
    WZ2PaperBodyConvexWolffBound targetBodies
      (ENNReal.ofReal (27 * (2 * (32 * heightScale) - 1) ^ 3) *
        ENNReal.ofReal |LinearMap.det
          ((pureWZ2AffineDiagonalJohnCoordinateChange frameSlope center
            heightScale transverseScale (lt_of_lt_of_le (by norm_num) hheight)
              htransverse sourceFiber.normalization
                targetNormalization).symm.linear : Point3 →ₗ[ℝ] Point3)| *
        ((weight⁻¹ * K) * sourceConstant)) := by
  let coordinateChange := pureWZ2AffineDiagonalJohnCoordinateChange
    frameSlope center heightScale transverseScale
      (lt_of_lt_of_le (by norm_num) hheight) htransverse
      sourceFiber.normalization targetNormalization
  let factor := 32 * heightScale
  have hfactor : 1 ≤ factor := by
    dsimp only [factor]
    nlinarith
  let targetCenter : Fin targetBodies.card → Point3 := fun index =>
    targetNormalization.map (wz2PaperTubeMidpoint (targetTube index))
  have htargetDeltaPos : 0 < targetDelta :=
    hsourceDelta.trans_le hsourceTarget
  have htargetBody : ∀ index,
      JohnEllipsoid.IsConvexBody (targetBodies.body index).carrier := by
    intro index
    rw [target_body]
    let sourceBody := wz2_paper_ordinary_tube_isConvexBody
      (targetTube index) htargetDeltaPos
    let homeomorph := targetNormalization.map.toHomeomorphOfFiniteDimensional
    refine ⟨sourceBody.1.affine_image targetNormalization.map.toAffineMap,
      ?_, ?_⟩
    · change IsCompact (homeomorph '' (targetTube index).carrier)
      exact (homeomorph.isCompact_image).2 sourceBody.2.1
    · change (interior (homeomorph '' (targetTube index).carrier)).Nonempty
      rw [← homeomorph.image_interior]
      exact sourceBody.2.2.image homeomorph
  have htargetBound : ∀ index,
      (targetBodies.body index).carrier ⊆
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
    exact ⟨wz2PaperTubeMidpoint (targetTube index),
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
      pureWZ2AffineDiagonalMap_ordinaryCarrier_image_subset_homothety_of_axis
        frameSlope center heightScale transverseScale hheight htransverse
          htransverseOne hcenter (sourceFine.tube (targetIndex index))
          (targetTube index) hsourceDelta hsourceTarget (hsourceBase _)
          (htargetLine index) (htargetDirection index)
          (htargetMidpoint index) (htargetAxis index)
    have hraw := pureWZ2AffineDiagonalJohnCoordinateChange_carrier
      frameSlope center heightScale transverseScale
        (lt_of_lt_of_le (by norm_num) hheight) htransverse
        sourceFiber.normalization targetNormalization factor
        (wz2PaperTubeMidpoint (targetTube index))
        (sourceFine.tube (targetIndex index)).carrier
        (targetTube index).carrier hordinary
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

attribute [local instance] Classical.propDecidable

namespace PureWZ2FiniteAnisotropicParentQuotientScheduleData
namespace PureWZ2AnisotropicJointRegularizationData

/-- One source-parent packet in an affine-diagonal quotient fiber has the
actual-John CWA bound. -/
theorem affineDiagonalQuotientTargetBodyPacket_cwa
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule : PureWZ2FiniteRepresentativeParentScheduleData
      targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData schedule weight selection)
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hheight : 1 ≤ heightScale)
    (htransverse : 0 < transverseScale)
    (htransverseOne : transverseScale ≤ 1)
    (hcenter : ‖center‖ ≤ 2)
    (hsourceDelta : 0 < sourceDelta)
    (hsourceTarget : sourceDelta ≤ targetDelta)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (htargetLine : WZ1PaperIsLineClass targetFine)
    (htargetDirection : ∀ target,
      (targetFine.tube target).direction =
        wz1PaperDirection (targetFine.tube target))
    (htargetMidpoint : ∀ target,
      ‖wz2PaperTubeMidpoint (targetFine.tube target)‖ ≤ 3)
    (htargetAxis : ∀ target, tubeAxisLine (targetFine.tube target) =
      pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale 1 ''
          tubeAxisLine (sourceFine.tube (sourceEquiv target)))
    (normalizationWeight retentionConstant : ENNReal)
    (hweightZero : normalizationWeight ≠ 0)
    (hweightTop : normalizationWeight ≠ ⊤)
    (hglobal : normalizationWeight * sourceFine.enncard ≤
      retentionConstant *
        (schedule.jointlyRegularizedFine
          weight selection data.selected).family.enncard)
    (coordinate : Fin scaleCount)
    (targetParent : Fin (data.finalCoarse coordinate).card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.finalCoarse coordinate).tube targetParent))
    (sourceParent : Fin
      (representativeSchedule.sourceScale coordinate).coarse.card) :
    WZ2PaperBodyConvexWolffBound
      (data.quotientTargetBodyPacket coordinate targetParent normalization
        sourceParent)
      (ENNReal.ofReal (27 * (2 * (32 * heightScale) - 1) ^ 3) *
        ENNReal.ofReal |LinearMap.det
          ((pureWZ2AffineDiagonalJohnCoordinateChange frameSlope center
            heightScale transverseScale (lt_of_lt_of_le (by norm_num) hheight)
              htransverse
              (Classical.choice
                ((representativeSchedule.sourceScale coordinate).rescaledFiber
                  sourceParent)).normalization normalization).symm.linear :
                Point3 →ₗ[ℝ] Point3)| *
        ((normalizationWeight⁻¹ *
          (sourceConstant * retentionConstant *
            (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
              (Nat.log 2
                (2 * (schedule.separatedFine weight selection).family.card) +
                  1 : ENNReal) ^ (scaleCount + scaleCount)))) *
          sourceConstant)) := by
  let packet := data.quotientTargetBodyPacket coordinate targetParent
    normalization sourceParent
  by_cases hpacket : 0 < packet.card
  · let sourceFiber := Classical.choice
      ((representativeSchedule.sourceScale coordinate).rescaledFiber
        sourceParent)
    let sourceIndex := data.quotientTargetBodyPacketSourceIndex
      coordinate targetParent normalization sourceParent
    have hpacketCard :=
      data.jointlyRegularizedSourcePacket_card_le_quotientTargetBodyPacket
        coordinate targetParent normalization sourceParent hpacket
    have hpacketCardReverse :=
      data.quotientTargetBodyPacket_card_le_jointlyRegularizedSourcePacket
        coordinate targetParent normalization sourceParent
    have hglobalPacket : 0 < (schedule.jointlyRegularizedSourcePacket
        weight selection data.selected coordinate sourceParent).card :=
      lt_of_lt_of_le hpacket hpacketCardReverse
    have hsourceRatio :=
      data.source_fullFiber_weighted_card_le_packet coordinate
        normalizationWeight retentionConstant hglobal sourceParent
        hglobalPacket
    have hcardinality : normalizationWeight *
        ((wz2PaperOrdinaryFullFiberIndices sourceFine
          (representativeSchedule.sourceScale coordinate).coarse
          sourceParent).card : ENNReal) ≤
        (sourceConstant * retentionConstant *
          (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
            (Nat.log 2
              (2 * (schedule.separatedFine weight selection).family.card) + 1 :
                ENNReal) ^ (scaleCount + scaleCount))) * packet.enncard := by
      have hpacketCardENN :
          ((schedule.jointlyRegularizedSourcePacket weight selection
            data.selected coordinate sourceParent).card : ENNReal) ≤
          packet.enncard := by
        change _ ≤ (packet.card : ENNReal)
        exact_mod_cast hpacketCard
      exact hsourceRatio.trans (mul_le_mul_left' hpacketCardENN _)
    let targetTube : Fin packet.card → Kakeya.DeltaTube targetDelta :=
      fun index => targetFine.tube (sourceEquiv.symm (sourceIndex index))
    have htargetMemParent : ∀ index : Fin packet.card,
        (targetTube index).carrier ⊆
          ((data.finalCoarse coordinate).tube targetParent).carrier := by
      intro index
      have htargetFiber := ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
        (data.quotientTargetBodyPacketEmbedding coordinate targetParent
          normalization sourceParent index)).2
      have hcontain := (mem_wz2PaperOrdinaryFullFiberIndices_iff
        targetParent ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
          (data.quotientTargetBodyPacketEmbedding coordinate targetParent
            normalization sourceParent index)).1).mp htargetFiber
      have hfinalTube : (schedule.jointlyRegularizedFine weight selection
          data.selected).family.tube
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
            (data.quotientTargetBodyPacketEmbedding coordinate targetParent
              normalization sourceParent index)).1 =
        targetFine.tube (data.finalTargetIndex
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
            (data.quotientTargetBodyPacketEmbedding coordinate targetParent
              normalization sourceParent index)).1) := rfl
      rw [hfinalTube] at hcontain
      have htargetIndex : sourceEquiv.symm (sourceIndex index) =
          data.finalTargetIndex
            ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
              (data.quotientTargetBodyPacketEmbedding coordinate targetParent
                normalization sourceParent index)).1 := by
        apply sourceEquiv.symm_apply_eq.mpr
        rfl
      simpa only [targetTube, htargetIndex] using hcontain
    have htargetBody : ∀ index : Fin packet.card,
        (packet.body index).carrier = normalization.map ''
          (targetTube index).carrier := by
      intro index
      change normalization.map ''
        ((schedule.jointlyRegularizedFine weight selection data.selected).family.tube
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
            (data.quotientTargetBodyPacketEmbedding coordinate targetParent
              normalization sourceParent index)).1).carrier = _
      rw [show (schedule.jointlyRegularizedFine weight selection
          data.selected).family.tube
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
            (data.quotientTargetBodyPacketEmbedding coordinate targetParent
              normalization sourceParent index)).1 =
        targetFine.tube (data.finalTargetIndex
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
            (data.quotientTargetBodyPacketEmbedding coordinate targetParent
              normalization sourceParent index)).1) by rfl]
      have htargetIndex : sourceEquiv.symm (sourceIndex index) =
          data.finalTargetIndex
            ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
              (data.quotientTargetBodyPacketEmbedding coordinate targetParent
                normalization sourceParent index)).1 := by
        apply sourceEquiv.symm_apply_eq.mpr
        rfl
      rw [← htargetIndex]
    have hraw := pureWZ2_affineDiagonalTargetPacket_cwa
      sourceParent sourceFiber frameSlope center heightScale transverseScale
      hheight htransverse htransverseOne hcenter hsourceDelta hsourceTarget
      hsourceBase packet sourceIndex
      (data.quotientTargetBodyPacketSourceIndex_injective
        coordinate targetParent normalization sourceParent)
      (data.quotientTargetBodyPacketSourceIndex_mem
        coordinate targetParent normalization sourceParent)
      targetTube (fun index => htargetLine _)
      (fun index => htargetDirection _) (fun index => htargetMidpoint _)
      (fun index => by
        simpa [targetTube] using htargetAxis (sourceEquiv.symm (sourceIndex index)))
      ((data.finalCoarse coordinate).tube targetParent) normalization
      htargetMemParent htargetBody normalizationWeight
      (sourceConstant * retentionConstant *
        (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
          (Nat.log 2
            (2 * (schedule.separatedFine weight selection).family.card) + 1 :
              ENNReal) ^ (scaleCount + scaleCount)))
      hweightZero hweightTop hcardinality
    simpa [sourceFiber, packet] using hraw
  · have hcardZero : packet.card = 0 := by omega
    intro convexSet hconvex
    have hcontainedZero : packet.containedCount convexSet = 0 := by
      unfold Kakeya.Streamlined.BodyFamily.containedCount
      have hle : (packet.containedIndices convexSet).card ≤ packet.card := by
        simpa using Finset.card_le_univ (packet.containedIndices convexSet)
      have hnat : (packet.containedIndices convexSet).card = 0 := by omega
      exact_mod_cast hnat
    have henncardZero : packet.enncard = 0 := by
      change (packet.card : ENNReal) = 0
      rw [hcardZero]
      norm_num
    rw [hcontainedZero, henncardZero]
    simp

/-- Uniform determinant version of the affine-diagonal packet estimate. -/
theorem affineDiagonalQuotientTargetBodyPacket_cwa_uniform
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule : PureWZ2FiniteRepresentativeParentScheduleData
      targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData schedule weight selection)
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hheight : 1 ≤ heightScale)
    (htransverse : 0 < transverseScale)
    (htransverseOne : transverseScale ≤ 1)
    (hcenter : ‖center‖ ≤ 2)
    (hsourceDelta : 0 < sourceDelta)
    (hsourceTarget : sourceDelta ≤ targetDelta)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (htargetLine : WZ1PaperIsLineClass targetFine)
    (htargetDirection : ∀ target,
      (targetFine.tube target).direction =
        wz1PaperDirection (targetFine.tube target))
    (htargetMidpoint : ∀ target,
      ‖wz2PaperTubeMidpoint (targetFine.tube target)‖ ≤ 3)
    (htargetAxis : ∀ target, tubeAxisLine (targetFine.tube target) =
      pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale 1 ''
          tubeAxisLine (sourceFine.tube (sourceEquiv target)))
    (normalizationWeight retentionConstant : ENNReal)
    (hweightZero : normalizationWeight ≠ 0)
    (hweightTop : normalizationWeight ≠ ⊤)
    (hglobal : normalizationWeight * sourceFine.enncard ≤
      retentionConstant *
        (schedule.jointlyRegularizedFine
          weight selection data.selected).family.enncard)
    (coordinate : Fin scaleCount)
    (targetParent : Fin (data.finalCoarse coordinate).card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.finalCoarse coordinate).tube targetParent))
    (sourceParent : Fin
      (representativeSchedule.sourceScale coordinate).coarse.card) :
    WZ2PaperBodyConvexWolffBound
      (data.quotientTargetBodyPacket coordinate targetParent normalization
        sourceParent)
      (ENNReal.ofReal (27 * (2 * (32 * heightScale) - 1) ^ 3) *
        ((432 : ENNReal) *
          Kakeya.realRpowENN (schedule.callerRho coordinate) 2 *
          ENNReal.ofReal (1 + 2 * schedule.callerRho coordinate) *
          ENNReal.ofReal (1 / (heightScale * transverseScale *
            representativeSchedule.sourceRho coordinate ^ 2))) *
        ((normalizationWeight⁻¹ *
          (sourceConstant * retentionConstant *
            (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
              (Nat.log 2
                (2 * (schedule.separatedFine weight selection).family.card) +
                  1 : ENNReal) ^ (scaleCount + scaleCount)))) *
          sourceConstant)) := by
  let sourceFiber := Classical.choice
    ((representativeSchedule.sourceScale coordinate).rescaledFiber
      sourceParent)
  have hraw := data.affineDiagonalQuotientTargetBodyPacket_cwa
    frameSlope center heightScale transverseScale hheight htransverse
    htransverseOne hcenter hsourceDelta hsourceTarget hsourceBase htargetLine
    htargetDirection htargetMidpoint htargetAxis normalizationWeight
    retentionConstant hweightZero hweightTop hglobal coordinate targetParent
    normalization sourceParent
  intro convexSet hconvex
  exact (hraw convexSet hconvex).trans <| by
    gcongr
    exact pureWZ2AffineDiagonalJohnCoordinateChange_inverse_det_le
      (representativeSchedule.sourceScale coordinate).rho_pos
      (schedule.quotient coordinate).caller_rho_pos frameSlope center
      heightScale transverseScale (lt_of_lt_of_le (by norm_num) hheight)
      htransverse
      ((representativeSchedule.sourceScale coordinate).coarse.tube sourceParent)
      ((data.finalCoarse coordinate).tube targetParent)
      sourceFiber.normalization normalization

/-- One complete affine-diagonal quotient fiber inherits the uniform packet
CWA bound, without a multiplicative source-packet count. -/
theorem affineDiagonalQuotientTargetFullFiber_cwa
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule : PureWZ2FiniteRepresentativeParentScheduleData
      targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData schedule weight selection)
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hheight : 1 ≤ heightScale)
    (htransverse : 0 < transverseScale)
    (htransverseOne : transverseScale ≤ 1)
    (hcenter : ‖center‖ ≤ 2)
    (hsourceDelta : 0 < sourceDelta)
    (hsourceTarget : sourceDelta ≤ targetDelta)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (htargetLine : WZ1PaperIsLineClass targetFine)
    (htargetDirection : ∀ target,
      (targetFine.tube target).direction =
        wz1PaperDirection (targetFine.tube target))
    (htargetMidpoint : ∀ target,
      ‖wz2PaperTubeMidpoint (targetFine.tube target)‖ ≤ 3)
    (htargetAxis : ∀ target, tubeAxisLine (targetFine.tube target) =
      pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale 1 ''
          tubeAxisLine (sourceFine.tube (sourceEquiv target)))
    (normalizationWeight retentionConstant : ENNReal)
    (hweightZero : normalizationWeight ≠ 0)
    (hweightTop : normalizationWeight ≠ ⊤)
    (hglobal : normalizationWeight * sourceFine.enncard ≤
      retentionConstant *
        (schedule.jointlyRegularizedFine
          weight selection data.selected).family.enncard)
    (coordinate : Fin scaleCount)
    (targetParent : Fin (data.finalCoarse coordinate).card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.finalCoarse coordinate).tube targetParent)) :
    WZ2PaperBodyConvexWolffBound
      (data.quotientTargetBodies coordinate targetParent normalization)
      (ENNReal.ofReal (27 * (2 * (32 * heightScale) - 1) ^ 3) *
        ((432 : ENNReal) *
          Kakeya.realRpowENN (schedule.callerRho coordinate) 2 *
          ENNReal.ofReal (1 + 2 * schedule.callerRho coordinate) *
          ENNReal.ofReal (1 / (heightScale * transverseScale *
            representativeSchedule.sourceRho coordinate ^ 2))) *
        ((normalizationWeight⁻¹ *
          (sourceConstant * retentionConstant *
            (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
              (Nat.log 2
                (2 * (schedule.separatedFine weight selection).family.card) +
                  1 : ENNReal) ^ (scaleCount + scaleCount)))) *
          sourceConstant)) := by
  apply pureWZ2_bodyCWA_of_parent_fibers
  · let source : Fin sourceFine.card :=
      ⟨0, (representativeSchedule.parentData coordinate).source_nonempty⟩
    rcases (representativeSchedule.sourceScale coordinate).cover.covers source
      with ⟨sourceParent, _⟩
    exact lt_of_le_of_lt (Nat.zero_le sourceParent.val) sourceParent.isLt
  · intro sourceParent
    exact data.affineDiagonalQuotientTargetBodyPacket_cwa_uniform
      frameSlope center heightScale transverseScale hheight htransverse
      htransverseOne hcenter hsourceDelta hsourceTarget hsourceBase htargetLine
      htargetDirection htargetMidpoint htargetAxis normalizationWeight
      retentionConstant hweightZero hweightTop hglobal coordinate targetParent
      normalization sourceParent

end PureWZ2AnisotropicJointRegularizationData
end PureWZ2FiniteAnisotropicParentQuotientScheduleData

end Kakeya.Assouad

end
