import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ActualJohnPacketCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.OuterJohnInverseVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingJacobian

/-!
# Determinant bound for exact-triangular John coordinates

The source John inverse, exact triangular map, and target John normalization
have inverse determinant bounded by an explicit ratio of the target and source
parent radii.
-/

noncomputable section

namespace Kakeya.Assouad

theorem pureWZ2AnisotropicJohnCoordinateChange_inverse_det_le
    {sourceRho targetRho c d m : ℝ}
    (hsourceRho : 0 < sourceRho)
    (htargetRho : 0 < targetRho)
    (htargetRhoOne : targetRho ≤ 1)
    (g : SlopeFunction) (center : Point3)
    (hcd : c < d) (hm : 0 < m)
    (sourceParent : Kakeya.DeltaTube sourceRho)
    (targetParent : Kakeya.DeltaTube targetRho)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent) :
    ENNReal.ofReal
        |LinearMap.det
          ((pureWZ2AnisotropicJohnCoordinateChange g center hcd hm
            sourceJohn targetJohn).symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
      (1296 : ENNReal) * Kakeya.realRpowENN targetRho 2 *
        ENNReal.ofReal (1 / (m * sourceRho ^ 2)) := by
  let coordinateChange := pureWZ2AnisotropicJohnCoordinateChange
    g center hcd hm sourceJohn targetJohn
  have hsourceDetLower :=
    wz2Paper_outerJohn_abs_det_lower sourceParent hsourceRho
  have htargetDetUpper :=
    pureWZ2_outerJohn_detENN_le htargetRho htargetRhoOne
      targetParent targetJohn
  have hlinear :
      coordinateChange.linear =
        sourceJohn.map.symm.linear.trans
          ((anisotropicCenteredRescalingAffineEquiv
            g c d m center hcd hm).linear.trans targetJohn.map.linear) := rfl
  have hsourceLinear :
      (sourceJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3) =
        sourceJohn.parent_convex_body.outerJohnEllipsoidMap := rfl
  have htargetLinear :
      (targetJohn.map.linear : Point3 →ₗ[ℝ] Point3) =
        targetJohn.parent_convex_body.outerJohnEllipsoidMap.symm := rfl
  have hphiDet :
      |LinearMap.det
        ((anisotropicCenteredRescalingAffineEquiv
          g c d m center hcd hm).linear : Point3 →ₗ[ℝ] Point3)| = m := by
    rw [anisotropicCenteredRescalingAffineEquiv_linear]
    change |LinearMap.det (anisotropicRescalingLinearMap g c d m)| = m
    rw [anisotropicRescalingLinear_det g hcd hm, abs_of_pos hm]
  have hcoordinateDet :
      |LinearMap.det (coordinateChange.linear : Point3 →ₗ[ℝ] Point3)| =
        |LinearMap.det
          (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| * m *
          |LinearMap.det
            (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)|⁻¹ := by
    rw [hlinear]
    have hcomposition :
        ((sourceJohn.map.symm.linear.trans
          ((anisotropicCenteredRescalingAffineEquiv
            g c d m center hcd hm).linear.trans targetJohn.map.linear) :
              Point3 ≃ₗ[ℝ] Point3) : Point3 →ₗ[ℝ] Point3) =
          (targetJohn.map.linear : Point3 →ₗ[ℝ] Point3).comp
            (((anisotropicCenteredRescalingAffineEquiv
              g c d m center hcd hm).linear : Point3 →ₗ[ℝ] Point3).comp
              (sourceJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3)) := by
      ext point
      rfl
    rw [hcomposition, LinearMap.det_comp, LinearMap.det_comp, abs_mul,
      abs_mul, hsourceLinear, htargetLinear, LinearEquiv.det_coe_symm,
      abs_inv, hphiDet]
    ring
  have hsourceDetPos : 0 <
      |LinearMap.det
        (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr
      (LinearEquiv.isUnit_det'
        sourceJohn.parent_convex_body.outerJohnEllipsoidMap).ne_zero
  have htargetDetPos : 0 <
      |LinearMap.det
        (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr
      (LinearEquiv.isUnit_det'
        targetJohn.parent_convex_body.outerJohnEllipsoidMap).ne_zero
  have hcoordinateDetPos : 0 <
      |LinearMap.det (coordinateChange.linear : Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr (LinearEquiv.isUnit_det' coordinateChange.linear).ne_zero
  have htargetDetReal :
      |LinearMap.det
        (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)| ≤
        324 * targetRho ^ 2 := by
    have hnonneg : 0 ≤ 324 * targetRho ^ 2 := by positivity
    rw [show Kakeya.realRpowENN targetRho 2 =
      ENNReal.ofReal (targetRho ^ 2) by
        simp [Kakeya.realRpowENN, Real.rpow_two]] at htargetDetUpper
    rw [← ENNReal.ofReal_ofNat (n := 324),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 324)] at htargetDetUpper
    exact (ENNReal.ofReal_le_ofReal_iff hnonneg).mp htargetDetUpper
  have hinverseReal :
      |LinearMap.det
        (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
        1296 * targetRho ^ 2 / (m * sourceRho ^ 2) := by
    have hsymm : coordinateChange.symm.linear =
        coordinateChange.linear.symm := rfl
    rw [hsymm, LinearEquiv.det_coe_symm, abs_inv]
    rw [hcoordinateDet]
    let sourceDet :=
      |LinearMap.det
        (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)|
    let targetDet :=
      |LinearMap.det
        (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)|
    have hdenominatorPos : 0 < sourceDet * m * targetDet⁻¹ := by
      positivity
    apply (inv_le_iff_one_le_mul₀ hdenominatorPos).2
    have htargetBound :
        |LinearMap.det
            (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)| ≤
          324 * targetRho ^ 2 := htargetDetReal
    have hsourceProduct :
        m * sourceRho ^ 2 ≤ 4 * (sourceDet * m) := by
      dsimp only [sourceDet]
      have hmul := mul_le_mul_of_nonneg_left hsourceDetLower hm.le
      nlinarith
    have htargetProduct :
        targetDet ≤ 324 * targetRho ^ 2 := by
      exact htargetDetReal
    dsimp only [sourceDet, targetDet]
    field_simp [hm.ne', hsourceRho.ne', hsourceDetPos.ne',
      htargetDetPos.ne']
    nlinarith
  calc
    ENNReal.ofReal
        |LinearMap.det (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
        ENNReal.ofReal
          (1296 * targetRho ^ 2 / (m * sourceRho ^ 2)) :=
      ENNReal.ofReal_mono hinverseReal
    _ = (1296 : ENNReal) * Kakeya.realRpowENN targetRho 2 *
        ENNReal.ofReal (1 / (m * sourceRho ^ 2)) := by
      have htargetSq : Real.rpow targetRho 2 = targetRho ^ 2 :=
        Real.rpow_two targetRho
      rw [Kakeya.realRpowENN, htargetSq]
      rw [← ENNReal.ofReal_ofNat (n := 1296),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1296)]
      rw [← ENNReal.ofReal_mul
        (by positivity : 0 ≤ 1296 * targetRho ^ 2)]
      congr 1
      ring

/-- The scale-unrestricted version of the exact-triangular John-coordinate
determinant estimate.  The extra `1 + 2 * targetRho` is the literal capsule
length factor and is later absorbed by the finite nearby-scale budget. -/
theorem pureWZ2AnisotropicJohnCoordinateChange_inverse_det_le_general
    {sourceRho targetRho c d m : ℝ}
    (hsourceRho : 0 < sourceRho)
    (htargetRho : 0 < targetRho)
    (g : SlopeFunction) (center : Point3)
    (hcd : c < d) (hm : 0 < m)
    (sourceParent : Kakeya.DeltaTube sourceRho)
    (targetParent : Kakeya.DeltaTube targetRho)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent) :
    ENNReal.ofReal
        |LinearMap.det
          ((pureWZ2AnisotropicJohnCoordinateChange g center hcd hm
            sourceJohn targetJohn).symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
      (432 : ENNReal) * Kakeya.realRpowENN targetRho 2 *
        ENNReal.ofReal (1 + 2 * targetRho) *
        ENNReal.ofReal (1 / (m * sourceRho ^ 2)) := by
  let coordinateChange := pureWZ2AnisotropicJohnCoordinateChange
    g center hcd hm sourceJohn targetJohn
  have hsourceDetLower :=
    wz2Paper_outerJohn_abs_det_lower sourceParent hsourceRho
  have htargetDetUpper :=
    pureWZ2_outerJohn_detENN_le_general htargetRho targetParent targetJohn
  have hlinear :
      coordinateChange.linear =
        sourceJohn.map.symm.linear.trans
          ((anisotropicCenteredRescalingAffineEquiv
            g c d m center hcd hm).linear.trans targetJohn.map.linear) := rfl
  have hsourceLinear :
      (sourceJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3) =
        sourceJohn.parent_convex_body.outerJohnEllipsoidMap := rfl
  have htargetLinear :
      (targetJohn.map.linear : Point3 →ₗ[ℝ] Point3) =
        targetJohn.parent_convex_body.outerJohnEllipsoidMap.symm := rfl
  have hphiDet :
      |LinearMap.det
        ((anisotropicCenteredRescalingAffineEquiv
          g c d m center hcd hm).linear : Point3 →ₗ[ℝ] Point3)| = m := by
    rw [anisotropicCenteredRescalingAffineEquiv_linear]
    change |LinearMap.det (anisotropicRescalingLinearMap g c d m)| = m
    rw [anisotropicRescalingLinear_det g hcd hm, abs_of_pos hm]
  have hcoordinateDet :
      |LinearMap.det (coordinateChange.linear : Point3 →ₗ[ℝ] Point3)| =
        |LinearMap.det
          (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| * m *
          |LinearMap.det
            (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)|⁻¹ := by
    rw [hlinear]
    have hcomposition :
        ((sourceJohn.map.symm.linear.trans
          ((anisotropicCenteredRescalingAffineEquiv
            g c d m center hcd hm).linear.trans targetJohn.map.linear) :
              Point3 ≃ₗ[ℝ] Point3) : Point3 →ₗ[ℝ] Point3) =
          (targetJohn.map.linear : Point3 →ₗ[ℝ] Point3).comp
            (((anisotropicCenteredRescalingAffineEquiv
              g c d m center hcd hm).linear : Point3 →ₗ[ℝ] Point3).comp
              (sourceJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3)) := by
      ext point
      rfl
    rw [hcomposition, LinearMap.det_comp, LinearMap.det_comp, abs_mul,
      abs_mul, hsourceLinear, htargetLinear, LinearEquiv.det_coe_symm,
      abs_inv, hphiDet]
    ring
  have hsourceDetPos : 0 <
      |LinearMap.det
        (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr
      (LinearEquiv.isUnit_det'
        sourceJohn.parent_convex_body.outerJohnEllipsoidMap).ne_zero
  have htargetDetPos : 0 <
      |LinearMap.det
        (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr
      (LinearEquiv.isUnit_det'
        targetJohn.parent_convex_body.outerJohnEllipsoidMap).ne_zero
  have hcoordinateDetPos : 0 <
      |LinearMap.det (coordinateChange.linear : Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr (LinearEquiv.isUnit_det' coordinateChange.linear).ne_zero
  have htargetDetReal :
      |LinearMap.det
        (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)| ≤
        108 * targetRho ^ 2 * (1 + 2 * targetRho) := by
    have hnonneg :
        0 ≤ 108 * targetRho ^ 2 * (1 + 2 * targetRho) := by positivity
    rw [show Kakeya.realRpowENN targetRho 2 =
      ENNReal.ofReal (targetRho ^ 2) by
        simp [Kakeya.realRpowENN, Real.rpow_two]] at htargetDetUpper
    rw [← ENNReal.ofReal_ofNat (n := 108),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 108),
      ← ENNReal.ofReal_mul
        (by positivity : 0 ≤ 108 * targetRho ^ 2)] at htargetDetUpper
    exact (ENNReal.ofReal_le_ofReal_iff hnonneg).mp htargetDetUpper
  have hinverseReal :
      |LinearMap.det
        (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
        432 * targetRho ^ 2 * (1 + 2 * targetRho) /
          (m * sourceRho ^ 2) := by
    have hsymm : coordinateChange.symm.linear =
        coordinateChange.linear.symm := rfl
    rw [hsymm, LinearEquiv.det_coe_symm, abs_inv]
    rw [hcoordinateDet]
    let sourceDet :=
      |LinearMap.det
        (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)|
    let targetDet :=
      |LinearMap.det
        (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)|
    have hdenominatorPos : 0 < sourceDet * m * targetDet⁻¹ := by
      positivity
    apply (inv_le_iff_one_le_mul₀ hdenominatorPos).2
    have hsourceProduct :
        m * sourceRho ^ 2 ≤ 4 * (sourceDet * m) := by
      dsimp only [sourceDet]
      have hmul := mul_le_mul_of_nonneg_left hsourceDetLower hm.le
      nlinarith
    have htargetProduct :
        targetDet ≤ 108 * targetRho ^ 2 * (1 + 2 * targetRho) := by
      exact htargetDetReal
    dsimp only [sourceDet, targetDet]
    field_simp [hm.ne', hsourceRho.ne', hsourceDetPos.ne',
      htargetDetPos.ne']
    nlinarith
  calc
    ENNReal.ofReal
        |LinearMap.det
          (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
        ENNReal.ofReal
          (432 * targetRho ^ 2 * (1 + 2 * targetRho) /
            (m * sourceRho ^ 2)) :=
      ENNReal.ofReal_mono hinverseReal
    _ = (432 : ENNReal) * Kakeya.realRpowENN targetRho 2 *
        ENNReal.ofReal (1 + 2 * targetRho) *
        ENNReal.ofReal (1 / (m * sourceRho ^ 2)) := by
      have htargetSq : Real.rpow targetRho 2 = targetRho ^ 2 :=
        Real.rpow_two targetRho
      rw [Kakeya.realRpowENN, htargetSq]
      rw [← ENNReal.ofReal_ofNat (n := 432),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 432),
        ← ENNReal.ofReal_mul
          (by positivity : 0 ≤ 432 * targetRho ^ 2),
        ← ENNReal.ofReal_mul
          (by positivity :
            0 ≤ 432 * targetRho ^ 2 * (1 + 2 * targetRho))]
      congr 1
      ring

end Kakeya.Assouad

end
