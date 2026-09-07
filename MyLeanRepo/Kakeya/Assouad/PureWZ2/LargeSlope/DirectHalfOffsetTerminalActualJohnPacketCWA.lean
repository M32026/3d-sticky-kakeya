import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalRequestedCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalConflictDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ActualJohnPacketCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.OuterJohnInverseVolume

/-!
# Actual-John coordinates for the direct half-offset terminal

The direct terminal is obtained by the literal exact triangular map and then
the line-class dilation `diag(lambda, 1, lambda)`.  This file packages that
composite as one affine equivalence and records the corresponding source-John
to target-John coordinate change.  In particular, its Jacobian is
`m * lambda^2`; no rotation-diagonal surrogate is used.

The final theorem isolates the exact remaining geometric input for a packet
CWA proof: an ordinary-carrier envelope for this particular composite map.
It then feeds that envelope directly to the common actual-John transfer
theorem.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2DirectCommonYSourceAssembly
namespace TerminalGeometry

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

/-- The literal affine equivalence underlying the direct half-offset terminal:
first the exact triangular map, then `diag(lambda, 1, lambda)` about the
terminal box center. -/
noncomputable def totalAffineEquiv
    (terminal : commonSource.TerminalGeometry) : Point3 ≃ᵃ[ℝ] Point3 :=
  let source := commonSource.halfOffsetAssembly.horizontalSource
  (anisotropicCenteredRescalingAffineEquiv
    (pureWZ2DirectGeometrySlope source) source.c source.d source.m
    (pureWZ2DirectAnisotropicCenter terminal.retubing.popular)
    source.ordered source.slopeScale_pos).trans
      (pureWZ2LineClassNormalizationAffineEquiv terminal.box.center
        pureWZ2DirectHalfOffsetTerminalLambda
        pureWZ2DirectHalfOffsetTerminalLambda_pos)

@[simp] theorem totalAffineEquiv_apply
    (terminal : commonSource.TerminalGeometry) (point : Point3) :
    totalAffineEquiv commonSource terminal point =
      totalAffineMap commonSource terminal point := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  rw [totalAffineEquiv, AffineEquiv.trans_apply,
    anisotropicCenteredRescalingAffineEquiv_apply,
    pureWZ2LineClassNormalizationAffineEquiv_apply]
  rfl

/-- The exact Jacobian of the literal total terminal map. -/
theorem totalAffineEquiv_abs_det
    (terminal : commonSource.TerminalGeometry) :
    let source := commonSource.halfOffsetAssembly.horizontalSource
    |LinearMap.det
      ((totalAffineEquiv commonSource terminal).linear :
        Point3 →ₗ[ℝ] Point3)| =
      source.m * pureWZ2DirectHalfOffsetTerminalLambda ^ 2 := by
  dsimp only
  let source := commonSource.halfOffsetAssembly.horizontalSource
  have hanisotropic :
      |LinearMap.det
        ((anisotropicCenteredRescalingAffineEquiv
          (pureWZ2DirectGeometrySlope source) source.c source.d source.m
          (pureWZ2DirectAnisotropicCenter terminal.retubing.popular)
          source.ordered source.slopeScale_pos).linear :
            Point3 →ₗ[ℝ] Point3)| = source.m := by
    rw [anisotropicCenteredRescalingAffineEquiv_linear]
    change |LinearMap.det
      (anisotropicRescalingLinearMap
        (pureWZ2DirectGeometrySlope source) source.c source.d source.m)| =
      source.m
    rw [anisotropicRescalingLinear_det _ source.ordered source.slopeScale_pos,
      abs_of_pos source.slopeScale_pos]
  have hterminal :
      |LinearMap.det
        ((pureWZ2LineClassNormalizationAffineEquiv terminal.box.center
          pureWZ2DirectHalfOffsetTerminalLambda
          pureWZ2DirectHalfOffsetTerminalLambda_pos).linear :
            Point3 →ₗ[ℝ] Point3)| =
      pureWZ2DirectHalfOffsetTerminalLambda ^ 2 :=
    pureWZ2LineClassNormalizationLinearEquiv_abs_det
      pureWZ2DirectHalfOffsetTerminalLambda
      pureWZ2DirectHalfOffsetTerminalLambda_pos
  change |LinearMap.det
      (((pureWZ2LineClassNormalizationAffineEquiv terminal.box.center
        pureWZ2DirectHalfOffsetTerminalLambda
        pureWZ2DirectHalfOffsetTerminalLambda_pos).linear :
          Point3 →ₗ[ℝ] Point3).comp
        ((anisotropicCenteredRescalingAffineEquiv
          (pureWZ2DirectGeometrySlope source) source.c source.d source.m
          (pureWZ2DirectAnisotropicCenter terminal.retubing.popular)
          source.ordered source.slopeScale_pos).linear :
            Point3 →ₗ[ℝ] Point3))| = _
  rw [LinearMap.det_comp, abs_mul, hanisotropic, hterminal]
  ring

/-- Source-John to target-John coordinates through the literal total terminal
affine map. -/
noncomputable def totalJohnCoordinateChange
    {sourceRho targetRho : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (terminal : commonSource.TerminalGeometry)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  sourceJohn.map.symm.trans
    ((totalAffineEquiv commonSource terminal).trans targetJohn.map)

@[simp] theorem totalJohnCoordinateChange_apply_sourceMap
    {sourceRho targetRho : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (terminal : commonSource.TerminalGeometry)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (point : Point3) :
    totalJohnCoordinateChange commonSource terminal sourceJohn targetJohn
        (sourceJohn.map point) =
      targetJohn.map (totalAffineMap commonSource terminal point) := by
  simp [totalJohnCoordinateChange, AffineEquiv.trans_apply]

/-- A carrier envelope for the literal total terminal map transports through
the source and target actual-John charts. -/
theorem totalJohnCoordinateChange_carrier
    {sourceRho targetRho : ℝ}
    {sourceParent : Kakeya.DeltaTube sourceRho}
    {targetParent : Kakeya.DeltaTube targetRho}
    (terminal : commonSource.TerminalGeometry)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (factor : ℝ) (targetCenter : Point3)
    (sourceSet targetSet : Set Point3)
    (hcarrier : totalAffineMap commonSource terminal '' sourceSet ⊆
      AffineMap.homothety targetCenter factor '' targetSet) :
    totalJohnCoordinateChange commonSource terminal sourceJohn targetJohn ''
        (sourceJohn.map '' sourceSet) ⊆
      AffineMap.homothety (targetJohn.map targetCenter) factor ''
        (targetJohn.map '' targetSet) := by
  rintro targetPoint ⟨sourceJohnPoint,
    ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
  rcases hcarrier ⟨sourcePoint, hsourcePoint, rfl⟩ with
    ⟨targetCarrierPoint, htargetCarrierPoint, hhomothety⟩
  refine ⟨targetJohn.map targetCarrierPoint,
    ⟨targetCarrierPoint, htargetCarrierPoint, rfl⟩, ?_⟩
  rw [totalJohnCoordinateChange_apply_sourceMap]
  rw [← hhomothety]
  change (AffineMap.lineMap
      (targetJohn.map targetCenter)
      (targetJohn.map targetCarrierPoint)) factor =
    targetJohn.map ((AffineMap.lineMap targetCenter targetCarrierPoint) factor)
  exact (targetJohn.map.apply_lineMap
    targetCenter targetCarrierPoint factor).symm

/-- Uniform inverse-Jacobian bound for the literal total terminal John
coordinate change. -/
theorem totalJohnCoordinateChange_inverse_det_le
    {sourceRho targetRho : ℝ}
    (hsourceRho : 0 < sourceRho) (htargetRho : 0 < targetRho)
    (terminal : commonSource.TerminalGeometry)
    (sourceParent : Kakeya.DeltaTube sourceRho)
    (targetParent : Kakeya.DeltaTube targetRho)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent) :
    let source := commonSource.halfOffsetAssembly.horizontalSource
    ENNReal.ofReal |LinearMap.det
        ((totalJohnCoordinateChange commonSource terminal sourceJohn
          targetJohn).symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
      (432 : ENNReal) * Kakeya.realRpowENN targetRho 2 *
        ENNReal.ofReal (1 + 2 * targetRho) *
        ENNReal.ofReal (1 /
          (source.m * pureWZ2DirectHalfOffsetTerminalLambda ^ 2 *
            sourceRho ^ 2)) := by
  dsimp only
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let coordinateChange :=
    totalJohnCoordinateChange commonSource terminal sourceJohn targetJohn
  have hsourceDetLower :=
    wz2Paper_outerJohn_abs_det_lower sourceParent hsourceRho
  have htargetDetUpper :=
    pureWZ2_outerJohn_detENN_le_general htargetRho targetParent targetJohn
  have hmapDet := totalAffineEquiv_abs_det commonSource terminal
  have hlinear : coordinateChange.linear =
      sourceJohn.map.symm.linear.trans
        ((totalAffineEquiv commonSource terminal).linear.trans
          targetJohn.map.linear) := rfl
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
          Point3 →ₗ[ℝ] Point3)| *
        (source.m * pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
      |LinearMap.det
        (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)|⁻¹ := by
    rw [hlinear]
    have hcomposition :
        ((sourceJohn.map.symm.linear.trans
          ((totalAffineEquiv commonSource terminal).linear.trans
            targetJohn.map.linear) : Point3 ≃ₗ[ℝ] Point3) :
              Point3 →ₗ[ℝ] Point3) =
          (targetJohn.map.linear : Point3 →ₗ[ℝ] Point3).comp
            (((totalAffineEquiv commonSource terminal).linear :
              Point3 →ₗ[ℝ] Point3).comp
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
        simp [Kakeya.realRpowENN],
      ← ENNReal.ofReal_ofNat (n := 108),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 108),
      ← ENNReal.ofReal_mul
        (by positivity : 0 ≤ 108 * targetRho ^ 2)] at htargetDetUpper
    exact (ENNReal.ofReal_le_ofReal_iff hnonneg).mp htargetDetUpper
  have hinverseReal : |LinearMap.det
      (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
      432 * targetRho ^ 2 * (1 + 2 * targetRho) /
        (source.m * pureWZ2DirectHalfOffsetTerminalLambda ^ 2 *
          sourceRho ^ 2) := by
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
        0 < sourceDet *
          (source.m * pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
            targetDet⁻¹ := by
      positivity [source.slopeScale_pos,
        pureWZ2DirectHalfOffsetTerminalLambda_pos]
    apply (inv_le_iff_one_le_mul₀ hdenominatorPos).2
    have hsourceProduct :
        (source.m * pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
            sourceRho ^ 2 ≤
          4 * (sourceDet *
            (source.m * pureWZ2DirectHalfOffsetTerminalLambda ^ 2)) := by
      dsimp only [sourceDet]
      have hmul := mul_le_mul_of_nonneg_left hsourceDetLower
        (mul_nonneg source.slopeScale_pos.le
          (sq_nonneg pureWZ2DirectHalfOffsetTerminalLambda))
      nlinarith
    dsimp only [sourceDet, targetDet]
    field_simp [source.slopeScale_pos.ne',
      pureWZ2DirectHalfOffsetTerminalLambda_pos.ne', hsourceRho.ne',
      hsourceDetPos.ne', htargetDetPos.ne']
    nlinarith [htargetDetReal]
  calc
    ENNReal.ofReal |LinearMap.det
        (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
      ENNReal.ofReal (432 * targetRho ^ 2 * (1 + 2 * targetRho) /
        (source.m * pureWZ2DirectHalfOffsetTerminalLambda ^ 2 *
          sourceRho ^ 2)) := ENNReal.ofReal_mono hinverseReal
    _ = (432 : ENNReal) * Kakeya.realRpowENN targetRho 2 *
        ENNReal.ofReal (1 + 2 * targetRho) *
        ENNReal.ofReal (1 /
          (source.m * pureWZ2DirectHalfOffsetTerminalLambda ^ 2 *
            sourceRho ^ 2)) := by
      rw [show Kakeya.realRpowENN targetRho 2 =
        ENNReal.ofReal (targetRho ^ 2) by
          simp [Kakeya.realRpowENN],
        ← ENNReal.ofReal_ofNat (n := 432),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 432),
        ← ENNReal.ofReal_mul
          (by positivity : 0 ≤ 432 * targetRho ^ 2),
        ← ENNReal.ofReal_mul
          (by positivity : 0 ≤ 432 * targetRho ^ 2 *
            (1 + 2 * targetRho))]
      congr 1
      ring

/-- A complete ordinary source tube maps into a controlled homothety of any
positive-oriented target tube on its literal total-map image line.  The
factor is uniform in the tube: it uses only the operator norm and translation
of the actual composite affine map. -/
theorem totalAffineMap_ordinaryCarrier_image_subset_homothety_of_axis
    {sourceDelta targetDelta : ℝ}
    (terminal : commonSource.TerminalGeometry)
    (source : Kakeya.DeltaTube sourceDelta)
    (target : Kakeya.DeltaTube targetDelta)
    (hsourceDelta : 0 < sourceDelta)
    (hsourceTarget : sourceDelta ≤ targetDelta)
    (hsourceBase : ‖source.base‖ ≤ 5)
    (htarget : WZ1PaperTubeInLineClass target)
    (htargetDirection : target.direction = wz1PaperDirection target)
    (htargetMidpoint : ‖wz2PaperTubeMidpoint target‖ ≤ 3)
    (haxis : tubeAxisLine target =
      totalAffineMap commonSource terminal '' tubeAxisLine source) :
    let equivalence := totalAffineEquiv commonSource terminal
    let mapNorm :=
      ‖equivalence.linear.toContinuousLinearEquiv.toContinuousLinearMap‖
    let factor := 32 * (1 + mapNorm + ‖equivalence 0‖)
    totalAffineMap commonSource terminal '' source.carrier ⊆
      AffineMap.homothety (wz2PaperTubeMidpoint target) factor ''
        target.carrier := by
  dsimp only
  let equivalence := totalAffineEquiv commonSource terminal
  let mapNorm :=
    ‖equivalence.linear.toContinuousLinearEquiv.toContinuousLinearMap‖
  let targetMidpoint := wz2PaperTubeMidpoint target
  let factor := 32 * (1 + mapNorm + ‖equivalence 0‖)
  have hmapNorm : 0 ≤ mapNorm := norm_nonneg _
  have hmapZero : 0 ≤ ‖equivalence 0‖ := norm_nonneg _
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
      ‖sourceAxisPoint‖ ≤
          ‖source.base‖ + ‖parameter • source.direction‖ := norm_add_le _ _
      _ = ‖source.base‖ + |parameter| := by
        rw [norm_smul, Real.norm_eq_abs, source.direction_unit, mul_one]
      _ ≤ 5 + 1 := by
        gcongr
        exact abs_le.mpr ⟨by linarith [hparameter.1], hparameter.2⟩
      _ = 6 := by norm_num
  let imageAxisPoint := totalAffineMap commonSource terminal sourceAxisPoint
  have himageAxis : imageAxisPoint ∈ tubeAxisLine target := by
    rw [haxis]
    exact ⟨sourceAxisPoint, hsourceAxis, rfl⟩
  have htargetMidpointAxis : targetMidpoint ∈ tubeAxisLine target :=
    wz2_paper_unitSegment_subset_axisLine target
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
  have himageAxisNorm : ‖imageAxisPoint‖ ≤
      ‖equivalence 0‖ + mapNorm * 6 := by
    have hdifference : equivalence sourceAxisPoint =
        equivalence 0 + equivalence.linear sourceAxisPoint := by
      simpa [vadd_eq_add, add_comm] using
        equivalence.map_vadd (0 : Point3) sourceAxisPoint
    rw [show imageAxisPoint = equivalence sourceAxisPoint by
      exact totalAffineEquiv_apply commonSource terminal sourceAxisPoint |>.symm,
      hdifference]
    calc
      ‖equivalence 0 + equivalence.linear sourceAxisPoint‖ ≤
          ‖equivalence 0‖ + ‖equivalence.linear sourceAxisPoint‖ :=
        norm_add_le _ _
      _ ≤ ‖equivalence 0‖ + mapNorm * ‖sourceAxisPoint‖ := by
        gcongr
        exact equivalence.linear.toContinuousLinearEquiv.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖equivalence 0‖ + mapNorm * 6 := by gcongr
  have himageAxisDistance : dist targetMidpoint imageAxisPoint ≤
      3 + ‖equivalence 0‖ + mapNorm * 6 := by
    rw [dist_eq_norm]
    calc
      ‖targetMidpoint - imageAxisPoint‖ ≤
          ‖targetMidpoint‖ + ‖imageAxisPoint‖ := norm_sub_le _ _
      _ ≤ 3 + (‖equivalence 0‖ + mapNorm * 6) := by gcongr
      _ = 3 + ‖equivalence 0‖ + mapNorm * 6 := by ring
  have hrelativeBound : |relativeParameter| ≤
      3 + ‖equivalence 0‖ + mapNorm * 6 := by
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
    (totalAffineMap commonSource terminal sourcePoint - targetMidpoint)
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
        factor⁻¹ • equivalence.linear (sourcePoint - sourceAxisPoint) := by
      dsimp only [contractedPoint, contractedAxisPoint, imageAxisPoint]
      rw [show
        (targetMidpoint + factor⁻¹ •
            (totalAffineMap commonSource terminal sourcePoint - targetMidpoint)) -
          (targetMidpoint + factor⁻¹ •
            (totalAffineMap commonSource terminal sourceAxisPoint -
              targetMidpoint)) =
        factor⁻¹ •
          (totalAffineMap commonSource terminal sourcePoint -
            totalAffineMap commonSource terminal sourceAxisPoint) by module]
      rw [← totalAffineEquiv_apply commonSource terminal sourcePoint,
        ← totalAffineEquiv_apply commonSource terminal sourceAxisPoint]
      congr 1
      exact (equivalence.toAffineMap.linearMap_vsub
        sourcePoint sourceAxisPoint).symm
    rw [hdifference, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hfactorPos)]
    calc
      factor⁻¹ * ‖equivalence.linear (sourcePoint - sourceAxisPoint)‖ ≤
        factor⁻¹ * (mapNorm * ‖sourcePoint - sourceAxisPoint‖) := by
          gcongr
          exact equivalence.linear.toContinuousLinearEquiv.toContinuousLinearMap.le_opNorm _
      _ ≤ factor⁻¹ * (mapNorm * sourceDelta) := by
          gcongr
          simpa [sourceAxisPoint, dist_eq_norm] using hsourceDistance
      _ ≤ sourceDelta := by
        have hfactorOne : 1 ≤ factor := by
          dsimp only [factor]
          nlinarith
        have hmapFactor : mapNorm ≤ factor := by
          dsimp only [factor]
          nlinarith
        have hinvNonneg : 0 ≤ factor⁻¹ := by positivity
        have := mul_le_mul_of_nonneg_left hmapFactor hinvNonneg
        rw [inv_mul_cancel₀ hfactorPos.ne'] at this
        nlinarith [hsourceDelta]
      _ ≤ targetDelta := hsourceTarget
  have hcontractedCarrier : contractedPoint ∈ target.carrier :=
    Metric.mem_cthickening_of_dist_le contractedPoint contractedAxisPoint
      targetDelta _ hcontractedAxis hcontractedDistance
  refine ⟨contractedPoint, hcontractedCarrier, ?_⟩
  rw [AffineMap.homothety_apply]
  change factor • (contractedPoint - targetMidpoint) + targetMidpoint =
    totalAffineMap commonSource terminal sourcePoint
  have hcontracted : contractedPoint - targetMidpoint = factor⁻¹ •
      (totalAffineMap commonSource terminal sourcePoint - targetMidpoint) := by
    dsimp only [contractedPoint]
    abel
  rw [hcontracted, smul_smul, mul_inv_cancel₀ hfactorPos.ne', one_smul]
  abel

namespace PureWZ2ExternalWeightRegularizationData

/-- The cleanup-selected terminal target has the literal total-map carrier
envelope over its synchronized selected ambient source tube. -/
theorem halfOffsetTerminalCleanupTarget_carrier_envelope
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount)
    (index : Fin (DirectHalfOffsetTerminalRequestedCWAPreTarget
      (commonSource := commonSource) regularization).card) :
    let equivalence := totalAffineEquiv commonSource terminal
    let mapNorm :=
      ‖equivalence.linear.toContinuousLinearEquiv.toContinuousLinearMap‖
    totalAffineMap commonSource terminal ''
        (regularization.selected.family.tube index).carrier ⊆
      AffineMap.homothety
          (wz2PaperTubeMidpoint
            ((DirectHalfOffsetTerminalRequestedCWAPreTarget
              (commonSource := commonSource) regularization).tube index))
          (32 * (1 + mapNorm + ‖equivalence 0‖)) ''
        ((DirectHalfOffsetTerminalRequestedCWAPreTarget
          (commonSource := commonSource) regularization).tube index).carrier := by
  dsimp only
  let targetFamily := DirectHalfOffsetTerminalRequestedCWAPreTarget
    (commonSource := commonSource) regularization
  let targetIndex := halfOffsetTerminalCleanupTargetPreimage
    (commonSource := commonSource) regularization index
  let terminalIndex : Fin terminal.centeredFamily.card :=
    cleanup.originalIndex commonSource targetIndex
  have htargetTube : targetFamily.tube index =
      terminal.centeredFamily.tube terminalIndex := rfl
  have hsourceTarget : delta ≤ terminal.targetDelta := by
    have hbudget := commonSource.halfOffsetLineClass_incidence_budget
    have herrorNonneg : 0 ≤ (51 / 100 : ℝ) *
        (terminal.targetDelta * Real.sqrt 3) := by
      positivity [commonSource.halfOffsetLineClassTargetDelta_pos]
    linarith
  have hsourceBase : ‖(regularization.selected.family.tube index).base‖ ≤ 5 := by
    rw [regularization.selected.tube_eq]
    exact commonSource.halfOffsetAssembly.cfg.bounded_base _ |>.trans
      (by norm_num)
  have htargetLine : WZ1PaperTubeInLineClass (targetFamily.tube index) :=
    ((TerminalGeometry.line_class_subfamily commonSource terminal
      cleanup.family).subfamily
        (halfOffsetTerminalCleanupTargetSubfamily
          (commonSource := commonSource) regularization)) index
  have htargetDirection :
      (targetFamily.tube index).direction =
        wz1PaperDirection (targetFamily.tube index) := by
    rw [htargetTube, centeredFamily_tube,
      pureWZ2PaperCenteredTube_direction]
    have hidempotent := pureWZ2PaperCenteredTube_idempotent
      (terminal.family.tube terminalIndex)
      (TerminalGeometry.line_class commonSource terminal terminalIndex)
    have hdirection := congrArg
      (fun tube : Kakeya.DeltaTube terminal.targetDelta => tube.direction)
      hidempotent
    exact hdirection.symm
  have htargetMidpoint :
      ‖wz2PaperTubeMidpoint (targetFamily.tube index)‖ ≤ 3 :=
    by
      rw [htargetTube, centeredFamily_tube]
      exact pureWZ2PaperCenteredTube_midpoint_norm_le_three _
        (TerminalGeometry.line_class commonSource terminal terminalIndex)
  have haxis : tubeAxisLine (targetFamily.tube index) =
      totalAffineMap commonSource terminal ''
        tubeAxisLine (regularization.selected.family.tube index) := by
    have hraw := centeredFamily_axis_totalAffineMap commonSource terminal terminalIndex
    have hsource := halfOffsetTerminalCleanupTargetPreimage_source
      (commonSource := commonSource) regularization index
    change cleanup.sourceIndex targetIndex =
      regularization.selected.embedding index at hsource
    change tubeAxisLine (terminal.centeredFamily.tube terminalIndex) =
      totalAffineMap commonSource terminal ''
        tubeAxisLine (commonSource.halfOffsetAssembly.cfg.family.tube
          (cleanup.sourceIndex targetIndex)) at hraw
    have hsourceTube : regularization.selected.family.tube index =
        commonSource.halfOffsetAssembly.cfg.family.tube
          (cleanup.sourceIndex targetIndex) := by
      rw [regularization.selected.tube_eq, ← hsource]
    rw [htargetTube, hsourceTube]
    exact hraw
  exact totalAffineMap_ordinaryCarrier_image_subset_homothety_of_axis
    commonSource terminal (regularization.selected.family.tube index)
      (targetFamily.tube index)
      commonSource.halfOffsetAssembly.cfg.extremal.delta_pos hsourceTarget
      hsourceBase htargetLine htargetDirection htargetMidpoint haxis

end PureWZ2ExternalWeightRegularizationData

/-- Map-specific packet transfer for the direct half-offset terminal.  The
sole geometric premise is the literal ordinary-carrier envelope for the
actual total map; all John-chart and convex-body bookkeeping is discharged
here. -/
theorem actualTerminalTargetPacket_cwa_of_carrier_envelope
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    (sourceParent : Fin sourceCoarse.card)
    {sourceConstant : ENNReal}
    (sourceFiber : WZ2PaperPureUnitRescaledFullFiberData
      (fine := sourceFine) (coarse := sourceCoarse)
      sourceParent sourceConstant)
    (terminal : commonSource.TerminalGeometry)
    (targetBodies : Kakeya.Streamlined.BodyFamily)
    (sourceIndex : Fin targetBodies.card → Fin sourceFine.card)
    (sourceIndex_injective : Function.Injective sourceIndex)
    (source_mem : ∀ index, sourceIndex index ∈
      wz2PaperOrdinaryFullFiberIndices sourceFine sourceCoarse sourceParent)
    (targetTube : Fin targetBodies.card → Kakeya.DeltaTube targetDelta)
    (targetParent : Kakeya.DeltaTube targetRho)
    (targetNormalization : WZ2PaperAssouadUnitRescalingData targetParent)
    (target_mem_parent : ∀ index,
      (targetTube index).carrier ⊆ targetParent.carrier)
    (target_body : ∀ index,
      (targetBodies.body index).carrier =
        targetNormalization.map '' (targetTube index).carrier)
    (factor : ℝ) (hfactor : 1 ≤ factor)
    (carrier_envelope : ∀ index,
      totalAffineMap commonSource terminal ''
          (sourceFine.tube (sourceIndex index)).carrier ⊆
        AffineMap.homothety (wz2PaperTubeMidpoint (targetTube index))
          factor '' (targetTube index).carrier)
    (weight K : ENNReal)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hcardinality :
      weight * ((wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceCoarse sourceParent).card : ENNReal) ≤
      K * targetBodies.enncard)
    (htargetDelta : 0 < targetDelta) :
    WZ2PaperBodyConvexWolffBound targetBodies
      (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
        ENNReal.ofReal |LinearMap.det
          ((totalJohnCoordinateChange commonSource terminal
            sourceFiber.normalization targetNormalization).symm.linear :
              Point3 →ₗ[ℝ] Point3)| *
        ((weight⁻¹ * K) * sourceConstant)) := by
  let coordinateChange := totalJohnCoordinateChange commonSource terminal
    sourceFiber.normalization targetNormalization
  let targetCenter : Fin targetBodies.card → Point3 := fun index =>
    targetNormalization.map (wz2PaperTubeMidpoint (targetTube index))
  have htargetBody : ∀ index,
      JohnEllipsoid.IsConvexBody (targetBodies.body index).carrier := by
    intro index
    rw [target_body]
    let sourceBody :=
      wz2_paper_ordinary_tube_isConvexBody (targetTube index) htargetDelta
    let homeomorph :=
      targetNormalization.map.toContinuousAffineEquiv.toHomeomorph
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
      wz2_paper_tubeMidpoint_mem_carrier _ htargetDelta.le, rfl⟩
  have hcarrier : ∀ index, coordinateChange ''
        ((pureWZ2ActualJohnSourcePacketBodyFamily
          sourceParent sourceFiber.normalization targetBodies
            sourceIndex source_mem).body index).carrier ⊆
      AffineMap.homothety (targetCenter index) factor ''
        (targetBodies.body index).carrier := by
    intro index
    rw [target_body]
    have hraw := totalJohnCoordinateChange_carrier commonSource terminal
      sourceFiber.normalization targetNormalization factor
      (wz2PaperTubeMidpoint (targetTube index))
      (sourceFine.tube (sourceIndex index)).carrier
      (targetTube index).carrier (carrier_envelope index)
    have hsourceIndex :
        ((wz2PaperOrdinaryFullFiberIndexEquiv sourceParent)
          (pureWZ2ActualJohnPacketSourceBodyIndex
            sourceParent sourceIndex source_mem index)).1 =
          sourceIndex index := by
      simp [pureWZ2ActualJohnPacketSourceBodyIndex]
    simpa only [coordinateChange, targetCenter,
      pureWZ2ActualJohnSourcePacketBodyFamily,
      wz2PaperPureUnitRescaledFullFiberBodyFamily, hsourceIndex] using hraw
  have hresult := pureWZ2_actualJohnPacket_cwa_of_affine_homothetic_envelope
    sourceParent sourceFiber targetBodies sourceIndex sourceIndex_injective
      source_mem weight K hweightZero hweightTop hcardinality
      coordinateChange factor 1 hfactor (by norm_num) htargetBody htargetBound
      targetCenter htargetCenter hcarrier
  simpa [coordinateChange] using hresult

namespace PureWZ2ExternalWeightRegularizationData
namespace PureWZ2FiniteAnisotropicParentQuotientScheduleData
namespace PureWZ2AnisotropicJointRegularizationData

/-- Actual-terminal packet CWA in the exact shape required by the finite
requested-scale assembly.  The source packet and target body packet are the
canonical ones supplied by the quotient schedule; the actual total-map
carrier envelope is discharged above. -/
theorem directHalfOffsetQuotientTargetBodyPacket_cwa
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight sourceFiberConstant : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount)
    {scaleCount : ℕ}
    {representativeSchedule :
      @PureWZ2FiniteRepresentativeParentScheduleData
        delta terminal.targetDelta regularization.selected.family
        (DirectHalfOffsetTerminalRequestedCWAPreTarget
          (commonSource := commonSource) regularization)
        (Equiv.refl _) sourceFiberConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin (DirectHalfOffsetTerminalRequestedCWAPreTarget
      (commonSource := commonSource) regularization).card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : Kakeya.Assouad.PureWZ2FiniteAnisotropicParentQuotientScheduleData.PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (packetWeight retentionConstant : ENNReal)
    (hweightZero : packetWeight ≠ 0)
    (hweightTop : packetWeight ≠ ⊤)
    (hglobal : packetWeight * regularization.selected.family.enncard ≤
      retentionConstant *
        (schedule.jointlyRegularizedFine
          weight selection data.selected).family.enncard)
    (coordinate : Fin scaleCount)
    (targetParent : Fin (data.finalCoarse coordinate).card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.finalCoarse coordinate).tube targetParent))
    (sourceParent : Fin
      (representativeSchedule.sourceScale coordinate).coarse.card) :
    let equivalence := totalAffineEquiv commonSource terminal
    let mapNorm :=
      ‖equivalence.linear.toContinuousLinearEquiv.toContinuousLinearMap‖
    let factor := 32 * (1 + mapNorm + ‖equivalence 0‖)
    WZ2PaperBodyConvexWolffBound
      (data.quotientTargetBodyPacket coordinate targetParent normalization
        sourceParent)
      (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
        ENNReal.ofReal |LinearMap.det
          ((totalJohnCoordinateChange commonSource terminal
            (Classical.choice
              ((representativeSchedule.sourceScale coordinate).rescaledFiber
                sourceParent)).normalization normalization).symm.linear :
              Point3 →ₗ[ℝ] Point3)| *
        ((packetWeight⁻¹ *
          (sourceFiberConstant * retentionConstant *
            (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
              (Nat.log 2
                (2 * (schedule.separatedFine weight selection).family.card) + 1 :
                  ENNReal) ^ (scaleCount + scaleCount)))) *
          sourceFiberConstant)) := by
  dsimp only
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
        packetWeight retentionConstant hglobal sourceParent hglobalPacket
    have hcardinality :
        packetWeight *
            ((wz2PaperOrdinaryFullFiberIndices regularization.selected.family
              (representativeSchedule.sourceScale coordinate).coarse
              sourceParent).card : ENNReal) ≤
          (sourceFiberConstant * retentionConstant *
            (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
              (Nat.log 2
                (2 * (schedule.separatedFine weight selection).family.card) + 1 :
                  ENNReal) ^ (scaleCount + scaleCount))) *
            packet.enncard := by
      have hpacketCardENN :
          ((schedule.jointlyRegularizedSourcePacket
            weight selection data.selected coordinate sourceParent).card :
              ENNReal) ≤ packet.enncard := by
        change _ ≤ (packet.card : ENNReal)
        exact_mod_cast hpacketCard
      exact hsourceRatio.trans (mul_le_mul_right hpacketCardENN _)
    let targetTube : Fin packet.card → Kakeya.DeltaTube terminal.targetDelta :=
      fun index =>
        (DirectHalfOffsetTerminalRequestedCWAPreTarget
          (commonSource := commonSource) regularization).tube (sourceIndex index)
    have htargetMemParent : ∀ index : Fin packet.card,
        (targetTube index).carrier ⊆
          ((data.finalCoarse coordinate).tube targetParent).carrier := by
      intro index
      have htargetFiber :=
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
          (data.quotientTargetBodyPacketEmbedding coordinate targetParent
            normalization sourceParent index)).2
      have hcontain :=
        (mem_wz2PaperOrdinaryFullFiberIndices_iff
          targetParent
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
            (data.quotientTargetBodyPacketEmbedding coordinate targetParent
              normalization sourceParent index)).1).mp htargetFiber
      have hfinalTube :
          (schedule.jointlyRegularizedFine
            weight selection data.selected).family.tube
              ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
                (data.quotientTargetBodyPacketEmbedding coordinate targetParent
                  normalization sourceParent index)).1 =
            (DirectHalfOffsetTerminalRequestedCWAPreTarget
              (commonSource := commonSource) regularization).tube
              (data.finalTargetIndex
                ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
                  (data.quotientTargetBodyPacketEmbedding coordinate targetParent
                    normalization sourceParent index)).1) := rfl
      rw [hfinalTube] at hcontain
      have htargetIndex : sourceIndex index =
          data.finalTargetIndex
            ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
              (data.quotientTargetBodyPacketEmbedding coordinate targetParent
                normalization sourceParent index)).1 := rfl
      simpa only [targetTube, htargetIndex] using hcontain
    have htargetBody : ∀ index : Fin packet.card,
        (packet.body index).carrier = normalization.map ''
          (targetTube index).carrier := by
      intro index
      change normalization.map ''
          ((schedule.jointlyRegularizedFine
            weight selection data.selected).family.tube
              ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
                (data.quotientTargetBodyPacketEmbedding coordinate targetParent
                  normalization sourceParent index)).1).carrier = _
      rw [show (schedule.jointlyRegularizedFine
          weight selection data.selected).family.tube
            ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
              (data.quotientTargetBodyPacketEmbedding coordinate targetParent
                normalization sourceParent index)).1 =
          (DirectHalfOffsetTerminalRequestedCWAPreTarget
            (commonSource := commonSource) regularization).tube
            (data.finalTargetIndex
              ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
                (data.quotientTargetBodyPacketEmbedding coordinate targetParent
                  normalization sourceParent index)).1) by rfl]
      have htargetIndex : sourceIndex index =
          data.finalTargetIndex
            ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
              (data.quotientTargetBodyPacketEmbedding coordinate targetParent
                normalization sourceParent index)).1 := rfl
      rw [← htargetIndex]
    have hcarrier : ∀ index : Fin packet.card,
        totalAffineMap commonSource terminal ''
            (regularization.selected.family.tube (sourceIndex index)).carrier ⊆
          AffineMap.homothety (wz2PaperTubeMidpoint (targetTube index))
              (32 * (1 +
                ‖(totalAffineEquiv commonSource terminal).linear
                  |>.toContinuousLinearEquiv.toContinuousLinearMap‖ +
                ‖totalAffineEquiv commonSource terminal 0‖)) ''
            (targetTube index).carrier := by
      intro index
      exact halfOffsetTerminalCleanupTarget_carrier_envelope
        (commonSource := commonSource) regularization (sourceIndex index)
    have hfactor : 1 ≤ 32 * (1 +
        ‖(totalAffineEquiv commonSource terminal).linear
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ +
        ‖totalAffineEquiv commonSource terminal 0‖) := by
      have hlinear : 0 ≤
          ‖(totalAffineEquiv commonSource terminal).linear
            |>.toContinuousLinearEquiv.toContinuousLinearMap‖ := norm_nonneg _
      have hzero : 0 ≤ ‖totalAffineEquiv commonSource terminal 0‖ :=
        norm_nonneg _
      nlinarith
    have hraw := actualTerminalTargetPacket_cwa_of_carrier_envelope
      (sourceFine := regularization.selected.family)
      commonSource sourceParent sourceFiber terminal packet sourceIndex
      (data.quotientTargetBodyPacketSourceIndex_injective
        (sourceFine := regularization.selected.family)
        (targetFine := DirectHalfOffsetTerminalRequestedCWAPreTarget
          (commonSource := commonSource) regularization)
        coordinate targetParent normalization sourceParent)
      (data.quotientTargetBodyPacketSourceIndex_mem
        (sourceFine := regularization.selected.family)
        (targetFine := DirectHalfOffsetTerminalRequestedCWAPreTarget
          (commonSource := commonSource) regularization)
        coordinate targetParent normalization sourceParent)
      (targetTube := targetTube)
      (targetParent := (data.finalCoarse coordinate).tube targetParent)
      (targetNormalization := normalization)
      (target_mem_parent := htargetMemParent)
      (target_body := htargetBody)
      (factor := 32 * (1 +
        ‖(totalAffineEquiv commonSource terminal).linear
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ +
        ‖totalAffineEquiv commonSource terminal 0‖))
      (hfactor := hfactor) (carrier_envelope := hcarrier)
      (weight := packetWeight)
      (K := sourceFiberConstant * retentionConstant *
        (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
          (Nat.log 2
            (2 * (schedule.separatedFine weight selection).family.card) + 1 :
              ENNReal) ^ (scaleCount + scaleCount)))
      (hweightZero := hweightZero) (hweightTop := hweightTop)
      (hcardinality := hcardinality)
      (htargetDelta := commonSource.halfOffsetLineClassTargetDelta_pos)
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

end PureWZ2AnisotropicJointRegularizationData
end PureWZ2FiniteAnisotropicParentQuotientScheduleData
end PureWZ2ExternalWeightRegularizationData

end TerminalGeometry
end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
