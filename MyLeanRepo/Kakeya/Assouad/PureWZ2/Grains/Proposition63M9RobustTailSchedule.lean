import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RobustTailAssembly
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingJacobian
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SingleTubeCWANearby
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12NestedJohnCWATransport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.FrostmanConvexWolff
import MyLeanRepo.Kakeya.Assouad.TubeVolumeRatio

/-!
# Proposition 6.3 M9: pre-runtime robust-tail scalar schedule

The mild-rescaling factor, dyadic depth, and root cutoff are selected before
the runtime family.  Once a finite family is supplied, the output CWA
constant is the explicit maximum of the two source-side obligations; this
does not feed back into the root cutoff.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory

/-- Exact inverse Jacobian factorization for the actual John-to-John map used
by the mild rescaling.  The middle factor is the inverse isotropic dilation. -/
theorem proposition63MildRescalingJohnCoordinateChange_symm_abs_det
    {sourceRho scale targetRho : ℝ}
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    (sourceParent : Fin sourceCoarse.card)
    (sourceNormalization : WZ2PaperAssouadUnitRescalingData
      (sourceCoarse.tube sourceParent))
    {targetCoarse : Kakeya.Streamlined.TubeFamily targetRho}
    (targetParent : Fin targetCoarse.card)
    (targetNormalization : WZ2PaperAssouadUnitRescalingData
      (targetCoarse.tube targetParent))
    (center : Point3) (hscale : 0 < scale) :
    |LinearMap.det
        ((proposition63MildRescalingJohnCoordinateChange sourceParent
          sourceNormalization targetParent targetNormalization center hscale
          ).symm.linear : Point3 →ₗ[ℝ] Point3)| =
      |LinearMap.det
          (targetNormalization.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| * scale⁻¹ ^ 3 *
        |LinearMap.det
          (sourceNormalization.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)|⁻¹ := by
  let coordinateChange := proposition63MildRescalingJohnCoordinateChange
    sourceParent sourceNormalization targetParent targetNormalization center hscale
  have hlinear :
      coordinateChange.symm.linear =
        (targetNormalization.map.symm.linear.trans
          (proposition63IsotropicAffineEquiv center scale hscale).symm.linear).trans
            sourceNormalization.map.linear := rfl
  rw [hlinear]
  have hcomposition :
      (((targetNormalization.map.symm.linear.trans
          (proposition63IsotropicAffineEquiv center scale hscale).symm.linear).trans
            sourceNormalization.map.linear : Point3 ≃ₗ[ℝ] Point3) :
          Point3 →ₗ[ℝ] Point3) =
        (sourceNormalization.map.linear : Point3 →ₗ[ℝ] Point3).comp
          (((proposition63IsotropicAffineEquiv center scale hscale).symm.linear :
            Point3 →ₗ[ℝ] Point3).comp
            (targetNormalization.map.symm.linear : Point3 →ₗ[ℝ] Point3)) := by
    ext point
    rfl
  rw [hcomposition, LinearMap.det_comp, LinearMap.det_comp, abs_mul, abs_mul]
  have hsource :
      (sourceNormalization.map.linear : Point3 →ₗ[ℝ] Point3) =
        sourceNormalization.parent_convex_body.outerJohnEllipsoidMap.symm := rfl
  have htarget :
      (targetNormalization.map.symm.linear : Point3 →ₗ[ℝ] Point3) =
        targetNormalization.parent_convex_body.outerJohnEllipsoidMap := rfl
  rw [hsource, htarget, LinearEquiv.det_coe_symm, abs_inv]
  have hisotropic :
      |LinearMap.det
        ((proposition63IsotropicAffineEquiv center scale hscale).symm.linear :
          Point3 →ₗ[ℝ] Point3)| = scale⁻¹ ^ 3 := by
    change
      |LinearMap.det
        ((LinearEquiv.smulOfNeZero ℝ Point3 scale⁻¹
          (inv_ne_zero hscale.ne')).toLinearMap)| = scale⁻¹ ^ 3
    have hsmul :
        ((LinearEquiv.smulOfNeZero ℝ Point3 scale⁻¹
          (inv_ne_zero hscale.ne')).toLinearMap : Point3 →ₗ[ℝ] Point3) =
          scale⁻¹ • LinearMap.id := by
      ext point
      rfl
    rw [hsmul]
    rw [LinearMap.det_smul, LinearMap.det_id]
    have hfinrank : Module.finrank ℝ Point3 = 3 := by simp [Point3]
    rw [hfinrank, abs_of_nonneg (by positivity)]
    simp
  rw [hisotropic]
  ring

/-- A scale-unrestricted polynomial upper bound for the outer-John
determinant of an ordinary tube. -/
theorem tube_outerJohn_abs_det_upper_polynomial
    {rho : ℝ} (tube : Kakeya.DeltaTube rho) (hrho : 0 < rho) :
    ENNReal.ofReal
        |LinearMap.det
          ((wz2_paper_ordinary_tube_isConvexBody tube hrho
            ).outerJohnEllipsoidMap : Point3 →ₗ[ℝ] Point3)| ≤
      27 * ENNReal.ofReal (Real.pi * rho ^ 2 * (1 + 2 * rho)) := by
  let normalization := WZ2PaperAssouadUnitRescalingData.ofTube tube hrho
  let determinant := ENNReal.ofReal
    |LinearMap.det
      (normalization.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)|
  have hellipsoid :
      volume normalization.parent_convex_body.outerJohnEllipsoid =
        determinant * volume (Metric.closedBall (0 : Point3) 1) :=
    JohnEllipsoid.volume_ellipsoid_eq
      normalization.parent_convex_body.outerJohnEllipsoidCenter
      normalization.parent_convex_body.outerJohnEllipsoidMap
  have hdetVolume : determinant ≤
      volume normalization.parent_convex_body.outerJohnEllipsoid := by
    rw [hellipsoid]
    calc
      determinant = determinant * 1 := by simp
      _ ≤ determinant * volume (Metric.closedBall (0 : Point3) 1) := by
        gcongr
        exact wz2_unitBall_volume_ge_one
  calc
    ENNReal.ofReal
          |LinearMap.det
            ((wz2_paper_ordinary_tube_isConvexBody tube hrho
              ).outerJohnEllipsoidMap : Point3 →ₗ[ℝ] Point3)| =
        determinant := rfl
    _ ≤ volume normalization.parent_convex_body.outerJohnEllipsoid :=
      hdetVolume
    _ ≤ 27 * volume tube.carrier :=
      normalization.outerJohn_volume_le_twentySeven
    _ = 27 * Kakeya.deltaTubeVolume rho := by
      congr 1
      exact Kakeya.Streamlined.tube_volume_eq tube
        { base := 0
          direction := EuclideanSpace.single (0 : Fin 3) 1
          direction_unit := by simp }
    _ ≤ 27 * ENNReal.ofReal (Real.pi * rho ^ 2 * (1 + 2 * rho)) := by
      gcongr
      exact deltaTubeVolume_upper_pi hrho

/-- The actual John-to-John inverse Jacobian has a family-free quadratic
envelope.  In particular, the cutoff needed to absorb it can be selected
before either finite family is known. -/
theorem proposition63MildRescalingJohnCoordinateChange_symm_det_le
    {sourceDelta sourceRho scale targetRho : ℝ}
    (hdelta : 0 < sourceDelta) (hdeltaRho : sourceDelta ≤ sourceRho)
    (hsourceRho : 0 < sourceRho) (htargetRho : 0 < targetRho)
    (htargetRhoOne : targetRho ≤ 1) (hscale : 1 ≤ scale)
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    (sourceParent : Fin sourceCoarse.card)
    (sourceNormalization : WZ2PaperAssouadUnitRescalingData
      (sourceCoarse.tube sourceParent))
    {targetCoarse : Kakeya.Streamlined.TubeFamily targetRho}
    (targetParent : Fin targetCoarse.card)
    (targetNormalization : WZ2PaperAssouadUnitRescalingData
      (targetCoarse.tube targetParent))
    (center : Point3) :
    ENNReal.ofReal
        |LinearMap.det
          ((proposition63MildRescalingJohnCoordinateChange sourceParent
            sourceNormalization targetParent targetNormalization center
            (zero_lt_one.trans_le hscale)).symm.linear :
              Point3 →ₗ[ℝ] Point3)| ≤
      9 * Kakeya.realRpowENN sourceDelta (-2) := by
  let sourceDet :=
    |LinearMap.det
      (sourceNormalization.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)|
  let targetDet :=
    |LinearMap.det
      (targetNormalization.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)|
  have hsourceLower : sourceRho ^ 2 / 4 ≤ sourceDet :=
    wz2Paper_outerJohn_abs_det_lower
      (sourceCoarse.tube sourceParent) hsourceRho
  have hsourcePositive : 0 < sourceDet :=
    (div_pos (sq_pos_of_pos hsourceRho) (by norm_num)).trans_le hsourceLower
  have htargetUpper : targetDet ≤ 9 / 4 :=
    tube_outerJohn_abs_det_upper (targetCoarse.tube targetParent)
      htargetRho htargetRhoOne
  have hscaleInv : scale⁻¹ ^ 3 ≤ 1 := by
    have hinvNonneg : 0 ≤ scale⁻¹ := inv_nonneg.mpr (zero_le_one.trans hscale)
    have hinvOne : scale⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hscale
    nlinarith [sq_nonneg scale⁻¹]
  have hdeltaSq : sourceDelta ^ 2 ≤ sourceRho ^ 2 := by
    nlinarith
  have hinverse : sourceDet⁻¹ ≤ 4 / sourceDelta ^ 2 := by
    have hdeltaQuarter : 0 < sourceDelta ^ 2 / 4 := by positivity
    calc
      sourceDet⁻¹ ≤ (sourceDelta ^ 2 / 4)⁻¹ :=
        (inv_le_inv₀ hsourcePositive hdeltaQuarter).2
          ((div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).2
            hdeltaSq |>.trans hsourceLower)
      _ = 4 / sourceDelta ^ 2 := by field_simp
  have hreal : targetDet * scale⁻¹ ^ 3 * sourceDet⁻¹ ≤
      9 * sourceDelta ^ (-2 : ℤ) := by
    rw [zpow_neg, zpow_ofNat]
    calc
      targetDet * scale⁻¹ ^ 3 * sourceDet⁻¹ ≤
          (9 / 4) * 1 * (4 / sourceDelta ^ 2) := by gcongr
      _ = 9 * (sourceDelta ^ 2)⁻¹ := by ring
  rw [proposition63MildRescalingJohnCoordinateChange_symm_abs_det]
  change ENNReal.ofReal (targetDet * scale⁻¹ ^ 3 * sourceDet⁻¹) ≤ _
  rw [show Kakeya.realRpowENN sourceDelta (-2) =
      ENNReal.ofReal (sourceDelta ^ (-2 : ℤ)) by
    simp [Kakeya.realRpowENN, Real.rpow_neg (le_of_lt hdelta)] <;> rfl]
  calc
    ENNReal.ofReal (targetDet * scale⁻¹ ^ 3 * sourceDet⁻¹) ≤
        ENNReal.ofReal (9 * sourceDelta ^ (-2 : ℤ)) :=
      ENNReal.ofReal_mono hreal
    _ = 9 * ENNReal.ofReal (sourceDelta ^ (-2 : ℤ)) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num

/-- Scale-unrestricted version of the preceding estimate.  The dependence
on the target radius is an explicit cubic polynomial. -/
theorem proposition63MildRescalingJohnCoordinateChange_symm_det_le_polynomial
    {sourceDelta sourceRho scale targetRho : ℝ}
    (hdelta : 0 < sourceDelta) (hdeltaRho : sourceDelta ≤ sourceRho)
    (hsourceRho : 0 < sourceRho) (htargetRho : 0 < targetRho)
    (hscale : 1 ≤ scale)
    {sourceCoarse : Kakeya.Streamlined.TubeFamily sourceRho}
    (sourceParent : Fin sourceCoarse.card)
    (sourceNormalization : WZ2PaperAssouadUnitRescalingData
      (sourceCoarse.tube sourceParent))
    {targetCoarse : Kakeya.Streamlined.TubeFamily targetRho}
    (targetParent : Fin targetCoarse.card)
    (targetNormalization : WZ2PaperAssouadUnitRescalingData
      (targetCoarse.tube targetParent))
    (center : Point3) :
    ENNReal.ofReal
        |LinearMap.det
          ((proposition63MildRescalingJohnCoordinateChange sourceParent
            sourceNormalization targetParent targetNormalization center
            (zero_lt_one.trans_le hscale)).symm.linear :
              Point3 →ₗ[ℝ] Point3)| ≤
      ENNReal.ofReal
        (108 * Real.pi * targetRho ^ 2 * (1 + 2 * targetRho) *
          sourceDelta ^ (-2 : ℤ)) := by
  let sourceDet :=
    |LinearMap.det
      (sourceNormalization.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)|
  let targetDet :=
    |LinearMap.det
      (targetNormalization.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)|
  have hsourceLower : sourceRho ^ 2 / 4 ≤ sourceDet :=
    wz2Paper_outerJohn_abs_det_lower
      (sourceCoarse.tube sourceParent) hsourceRho
  have hsourcePositive : 0 < sourceDet :=
    (div_pos (sq_pos_of_pos hsourceRho) (by norm_num)).trans_le hsourceLower
  have htargetNonneg :
      0 ≤ 27 * Real.pi * targetRho ^ 2 * (1 + 2 * targetRho) := by
    positivity
  have htargetUpper : targetDet ≤
      27 * Real.pi * targetRho ^ 2 * (1 + 2 * targetRho) := by
    apply (ENNReal.ofReal_le_ofReal_iff htargetNonneg).1
    simpa [targetDet, mul_assoc] using
      tube_outerJohn_abs_det_upper_polynomial
        (targetCoarse.tube targetParent) htargetRho
  have hscaleInv : scale⁻¹ ^ 3 ≤ 1 := by
    have hinvNonneg : 0 ≤ scale⁻¹ := inv_nonneg.mpr (zero_le_one.trans hscale)
    have hinvOne : scale⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hscale
    nlinarith [sq_nonneg scale⁻¹]
  have hdeltaSq : sourceDelta ^ 2 ≤ sourceRho ^ 2 := by nlinarith
  have hinverse : sourceDet⁻¹ ≤ 4 / sourceDelta ^ 2 := by
    have hdeltaQuarter : 0 < sourceDelta ^ 2 / 4 := by positivity
    calc
      sourceDet⁻¹ ≤ (sourceDelta ^ 2 / 4)⁻¹ :=
        (inv_le_inv₀ hsourcePositive hdeltaQuarter).2
          ((div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).2
            hdeltaSq |>.trans hsourceLower)
      _ = 4 / sourceDelta ^ 2 := by field_simp
  rw [proposition63MildRescalingJohnCoordinateChange_symm_abs_det]
  change ENNReal.ofReal (targetDet * scale⁻¹ ^ 3 * sourceDet⁻¹) ≤ _
  apply ENNReal.ofReal_mono
  rw [zpow_neg, zpow_ofNat]
  calc
    targetDet * scale⁻¹ ^ 3 * sourceDet⁻¹ ≤
        (27 * Real.pi * targetRho ^ 2 * (1 + 2 * targetRho)) *
          1 * (4 / sourceDelta ^ 2) := by gcongr
    _ = 108 * Real.pi * targetRho ^ 2 * (1 + 2 * targetRho) *
        (sourceDelta ^ 2)⁻¹ := by ring

/-- The preceding polynomial bound specialized to the exact source and
quotient-parent normalizations occurring in a canonical packet. -/
theorem Proposition63MildRescalingQuotientScheduleData.canonicalPacket_det_le
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    (data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule)
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.quotient coordinate).parentFamily.card)
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card) :
    ENNReal.ofReal
        |LinearMap.det
          ((proposition63MildRescalingJohnCoordinateChange sourceParent
            (Classical.choice
              ((sourceSchedule.witness coordinate).scaleData.rescaledFiber
                sourceParent)).normalization targetParent
            (WZ2PaperAssouadUnitRescalingData.ofTube
              ((data.quotient coordinate).parentFamily.tube targetParent)
              (data.quotient coordinate).caller_rho_pos) center
            (zero_lt_one.trans_le hscale)).symm.linear :
              Point3 →ₗ[ℝ] Point3)| ≤
      ENNReal.ofReal
        (108 * Real.pi *
          (proposition63MildRescalingQuotientRho sourceDelta
            (sourceSchedule.witness coordinate).rho scale) ^ 2 *
          (1 + 2 * proposition63MildRescalingQuotientRho sourceDelta
            (sourceSchedule.witness coordinate).rho scale) *
          sourceDelta ^ (-2 : ℤ)) := by
  apply proposition63MildRescalingJohnCoordinateChange_symm_det_le_polynomial
  · exact (sourceSchedule.witness coordinate).scaleData.delta_pos
  · exact (sourceSchedule.requested coordinate).2.1.trans
      (sourceSchedule.witness coordinate).requested_le
  · exact (sourceSchedule.witness coordinate).scaleData.rho_pos
  · exact (data.quotient coordinate).caller_rho_pos
  · exact hscale

/-- The exact quotient radius cancels the quadratic source-John loss.  This
is the determinant estimate needed by the pre-runtime tail: unlike the
coarser root-scale estimate above, it carries no negative source power. -/
theorem Proposition63MildRescalingQuotientScheduleData.canonicalPacket_det_le_no_power
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    (data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule)
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.quotient coordinate).parentFamily.card)
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card) :
    ENNReal.ofReal
        |LinearMap.det
          ((proposition63MildRescalingJohnCoordinateChange sourceParent
            (Classical.choice
              ((sourceSchedule.witness coordinate).scaleData.rescaledFiber
                sourceParent)).normalization targetParent
            (WZ2PaperAssouadUnitRescalingData.ofTube
              ((data.quotient coordinate).parentFamily.tube targetParent)
              (data.quotient coordinate).caller_rho_pos) center
            (zero_lt_one.trans_le hscale)).symm.linear :
              Point3 →ₗ[ℝ] Point3)| ≤
      ENNReal.ofReal
        (108 * Real.pi * 5200004 ^ 2 *
          (1 + 2 * proposition63MildRescalingQuotientRho sourceDelta
            (sourceSchedule.witness coordinate).rho scale)) := by
  let sourceRho := (sourceSchedule.witness coordinate).rho
  let targetRho := proposition63MildRescalingQuotientRho
    sourceDelta sourceRho scale
  let sourceNormalization :=
    (Classical.choice
      ((sourceSchedule.witness coordinate).scaleData.rescaledFiber
        sourceParent)).normalization
  let targetNormalization := WZ2PaperAssouadUnitRescalingData.ofTube
    ((data.quotient coordinate).parentFamily.tube targetParent)
    (data.quotient coordinate).caller_rho_pos
  let sourceDet :=
    |LinearMap.det
      (sourceNormalization.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)|
  let targetDet :=
    |LinearMap.det
      (targetNormalization.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)|
  have hsourceRho : 0 < sourceRho :=
    (sourceSchedule.witness coordinate).scaleData.rho_pos
  have htargetRho : 0 < targetRho :=
    (data.quotient coordinate).caller_rho_pos
  have hsourceLower : sourceRho ^ 2 / 4 ≤ sourceDet :=
    wz2Paper_outerJohn_abs_det_lower
      ((sourceSchedule.witness coordinate).scaleData.coarse.tube sourceParent)
      hsourceRho
  have hsourcePositive : 0 < sourceDet :=
    (div_pos (sq_pos_of_pos hsourceRho) (by norm_num)).trans_le hsourceLower
  have htargetUpper : targetDet ≤
      27 * Real.pi * targetRho ^ 2 * (1 + 2 * targetRho) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).1
    simpa [targetDet, targetNormalization, targetRho, mul_assoc] using
      tube_outerJohn_abs_det_upper_polynomial
        ((data.quotient coordinate).parentFamily.tube targetParent) htargetRho
  have hinverse : sourceDet⁻¹ ≤ 4 / sourceRho ^ 2 := by
    have hrhoQuarter : 0 < sourceRho ^ 2 / 4 := by positivity
    calc
      sourceDet⁻¹ ≤ (sourceRho ^ 2 / 4)⁻¹ :=
        (inv_le_inv₀ hsourcePositive hrhoQuarter).2 hsourceLower
      _ = 4 / sourceRho ^ 2 := by field_simp
  have hdeltaRho : sourceDelta ≤ sourceRho :=
    (sourceSchedule.requested coordinate).2.1.trans
      (sourceSchedule.witness coordinate).requested_le
  have htargetRatio : targetRho ≤ 5200004 * scale * sourceRho := by
    dsimp only [targetRho, sourceRho]
    unfold proposition63MildRescalingQuotientRho
    nlinarith [mul_nonneg (zero_lt_one.trans_le hscale).le
      (sub_nonneg.mpr hdeltaRho)]
  rw [proposition63MildRescalingJohnCoordinateChange_symm_abs_det]
  change ENNReal.ofReal (targetDet * scale⁻¹ ^ 3 * sourceDet⁻¹) ≤ _
  apply ENNReal.ofReal_mono
  calc
    targetDet * scale⁻¹ ^ 3 * sourceDet⁻¹ ≤
        (27 * Real.pi * targetRho ^ 2 * (1 + 2 * targetRho)) *
          scale⁻¹ ^ 3 * (4 / sourceRho ^ 2) := by gcongr
    _ ≤ 108 * Real.pi * 5200004 ^ 2 * (1 + 2 * targetRho) := by
      have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
      have hratioSq : targetRho ^ 2 ≤
          (5200004 * scale * sourceRho) ^ 2 := by gcongr
      calc
        (27 * Real.pi * targetRho ^ 2 * (1 + 2 * targetRho)) *
              scale⁻¹ ^ 3 * (4 / sourceRho ^ 2) ≤
            (27 * Real.pi * (5200004 * scale * sourceRho) ^ 2 *
              (1 + 2 * targetRho)) * scale⁻¹ ^ 3 *
                (4 / sourceRho ^ 2) := by gcongr
        _ = 108 * Real.pi * 5200004 ^ 2 * (1 + 2 * targetRho) *
              scale⁻¹ := by
          field_simp [hscalePos.ne', hsourceRho.ne'] <;> ring
        _ ≤ 108 * Real.pi * 5200004 ^ 2 * (1 + 2 * targetRho) := by
          exact mul_le_of_le_one_right (by positivity)
            (inv_le_one_of_one_le₀ hscale)

/-- Every actual quotient-parent radius is bounded by the fixed source
schedule window; no runtime-family cardinality enters this estimate. -/
theorem Proposition63MildRescalingQuotientScheduleData.quotientRho_le_window
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    (data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule)
    (hconstantWindow : sourceConstant ≤ sourceWindowConstant)
    (coordinate : Fin sourceSchedule.scaleCount) :
    ENNReal.ofReal
        (proposition63MildRescalingQuotientRho sourceDelta
          (sourceSchedule.witness coordinate).rho scale) ≤
      ENNReal.ofReal scale *
        Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
          sourceWindowConstant := by
  have hscaleNonneg : 0 ≤ scale := zero_le_one.trans hscale
  have hdeltaOne : sourceDelta ≤ 1 :=
    (sourceSchedule.requested coordinate).2.1.trans
      (sourceSchedule.requested coordinate).2.2
  have hrhoWindow :
      ENNReal.ofReal (sourceSchedule.witness coordinate).rho ≤
        sourceWindowConstant := by
    have hlt : ENNReal.ofReal (sourceSchedule.witness coordinate).rho <
        sourceWindowConstant := by
      calc
        ENNReal.ofReal (sourceSchedule.witness coordinate).rho <
            sourceWindowConstant *
              ENNReal.ofReal (sourceSchedule.requested coordinate).1 :=
          (sourceSchedule.witness coordinate).within_factor.trans_le <| by
            gcongr
        _ ≤ sourceWindowConstant * 1 := by
          gcongr
          simpa using ENNReal.ofReal_mono
            (sourceSchedule.requested coordinate).2.2
        _ = sourceWindowConstant := by simp
    exact hlt.le
  have hdeltaENN : ENNReal.ofReal sourceDelta ≤ 1 := by
    simpa using ENNReal.ofReal_mono hdeltaOne
  unfold proposition63MildRescalingQuotientRho
  rw [show 5200000 * scale * (sourceSchedule.witness coordinate).rho +
        4 * scale * sourceDelta =
      scale * (5200000 * (sourceSchedule.witness coordinate).rho +
        4 * sourceDelta) by ring]
  rw [ENNReal.ofReal_mul hscaleNonneg]
  apply mul_le_mul_left'
  rw [ENNReal.ofReal_add (mul_nonneg (by norm_num)
      (sourceSchedule.witness coordinate).scaleData.rho_pos.le)
    (mul_nonneg (by norm_num)
      (sourceSchedule.witness coordinate).scaleData.delta_pos.le),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5200000),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  unfold Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
  norm_num only [ENNReal.ofReal_ofNat]
  simpa using add_le_add (mul_le_mul_left' hrhoWindow 5200000)
    (mul_le_mul_left' hdeltaENN 4)

/-- Family-free determinant envelope for the exact canonical normalization
used by a jointly regularized quotient packet. -/
theorem Proposition63MildRescalingQuotientScheduleData.canonicalJointPacket_det_le_window
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (hconstantWindow : sourceConstant ≤ sourceWindowConstant)
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.jointRegularizedParents regularized coordinate).family.card)
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card) :
    ENNReal.ofReal
        |LinearMap.det
          ((proposition63MildRescalingJohnCoordinateChange sourceParent
            (Classical.choice
              ((sourceSchedule.witness coordinate).scaleData.rescaledFiber
                sourceParent)).normalization targetParent
            (WZ2PaperAssouadUnitRescalingData.ofTube
              ((data.jointRegularizedParents regularized coordinate).family.tube
                targetParent)
              (data.quotient coordinate).caller_rho_pos) center
            (zero_lt_one.trans_le hscale)).symm.linear :
              Point3 →ₗ[ℝ] Point3)| ≤
      108 * ENNReal.ofReal Real.pi *
        (ENNReal.ofReal scale *
          Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
            sourceWindowConstant) ^ 2 *
        (1 + 2 * (ENNReal.ofReal scale *
          Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
            sourceWindowConstant)) *
        Kakeya.realRpowENN sourceDelta (-2) := by
  let rho := proposition63MildRescalingQuotientRho sourceDelta
    (sourceSchedule.witness coordinate).rho scale
  have hrhoPos : 0 < rho := (data.quotient coordinate).caller_rho_pos
  have hdet :=
    proposition63MildRescalingJohnCoordinateChange_symm_det_le_polynomial
      (sourceSchedule.witness coordinate).scaleData.delta_pos
      ((sourceSchedule.requested coordinate).2.1.trans
        (sourceSchedule.witness coordinate).requested_le)
      (sourceSchedule.witness coordinate).scaleData.rho_pos hrhoPos hscale
      sourceParent
      (Classical.choice
        ((sourceSchedule.witness coordinate).scaleData.rescaledFiber sourceParent)
        ).normalization targetParent
      (WZ2PaperAssouadUnitRescalingData.ofTube
        ((data.jointRegularizedParents regularized coordinate).family.tube
          targetParent) hrhoPos) center
  have hrho := data.quotientRho_le_window hconstantWindow coordinate
  have hrhoENN : ENNReal.ofReal rho ≤ ENNReal.ofReal scale *
      Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
        sourceWindowConstant := by
    exact hrho
  calc
    ENNReal.ofReal
          |LinearMap.det
            ((proposition63MildRescalingJohnCoordinateChange sourceParent
              (Classical.choice
                ((sourceSchedule.witness coordinate).scaleData.rescaledFiber
                  sourceParent)).normalization targetParent
              (WZ2PaperAssouadUnitRescalingData.ofTube
                ((data.jointRegularizedParents regularized coordinate).family.tube
                  targetParent) hrhoPos) center
              (zero_lt_one.trans_le hscale)).symm.linear :
                Point3 →ₗ[ℝ] Point3)| ≤
        ENNReal.ofReal
          (108 * Real.pi * rho ^ 2 * (1 + 2 * rho) *
            sourceDelta ^ (-2 : ℤ)) := hdet
    _ = 108 * ENNReal.ofReal Real.pi * (ENNReal.ofReal rho) ^ 2 *
          (1 + 2 * ENNReal.ofReal rho) *
          Kakeya.realRpowENN sourceDelta (-2) := by
      have hpi : 0 ≤ Real.pi := Real.pi_pos.le
      have hrho : 0 ≤ rho := hrhoPos.le
      have hlinear : 0 ≤ 1 + 2 * rho := by positivity
      have hpower : 0 ≤ sourceDelta ^ (-2 : ℤ) := by positivity
      have hzpow : sourceDelta ^ (-2 : ℤ) = (sourceDelta ^ 2)⁻¹ := by
        rw [zpow_neg, zpow_ofNat]
      have hrpowZpow : Real.rpow sourceDelta (-2 : ℝ) =
          sourceDelta ^ (-2 : ℤ) := by
        rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num]
        exact Real.rpow_intCast sourceDelta (-2)
      rw [hzpow]
      rw [show 108 * Real.pi * rho ^ 2 * (1 + 2 * rho) *
            (sourceDelta ^ 2)⁻¹ =
          (((108 * Real.pi) * rho ^ 2) * (1 + 2 * rho)) *
            (sourceDelta ^ 2)⁻¹ by ring]
      rw [ENNReal.ofReal_mul
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hpi)
            (sq_nonneg rho)) hlinear),
        ENNReal.ofReal_mul
          (mul_nonneg (mul_nonneg (by norm_num) hpi) (sq_nonneg rho)),
        ENNReal.ofReal_mul (mul_nonneg (by norm_num) hpi),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 108),
        ENNReal.ofReal_pow hrho, ENNReal.ofReal_add (by norm_num)
          (mul_nonneg (by norm_num) hrho),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_ofNat]
      norm_num
      rw [show Kakeya.realRpowENN sourceDelta (-2) =
          ENNReal.ofReal ((sourceDelta ^ 2)⁻¹) by
        simp only [Kakeya.realRpowENN]
        congr 1]
    _ ≤ 108 * ENNReal.ofReal Real.pi *
          (ENNReal.ofReal scale *
            Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
              sourceWindowConstant) ^ 2 *
          (1 + 2 * (ENNReal.ofReal scale *
            Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
              sourceWindowConstant)) *
          Kakeya.realRpowENN sourceDelta (-2) := by gcongr

/-- Joint-parent form of the cancellation estimate.  Restricting quotient
parents does not alter their common radius, so the same source-radius
cancellation survives regularization. -/
theorem Proposition63MildRescalingQuotientScheduleData.canonicalJointPacket_det_le_window_no_power
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (hconstantWindow : sourceConstant ≤ sourceWindowConstant)
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.jointRegularizedParents regularized coordinate).family.card)
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card) :
    ENNReal.ofReal
        |LinearMap.det
          ((proposition63MildRescalingJohnCoordinateChange sourceParent
            (Classical.choice
              ((sourceSchedule.witness coordinate).scaleData.rescaledFiber
                sourceParent)).normalization targetParent
            (WZ2PaperAssouadUnitRescalingData.ofTube
              ((data.jointRegularizedParents regularized coordinate).family.tube
                targetParent)
              (data.quotient coordinate).caller_rho_pos) center
            (zero_lt_one.trans_le hscale)).symm.linear :
              Point3 →ₗ[ℝ] Point3)| ≤
      108 * ENNReal.ofReal Real.pi * 5200004 ^ 2 *
        (1 + 2 * (ENNReal.ofReal scale *
          Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
            sourceWindowConstant)) := by
  let sourceRho := (sourceSchedule.witness coordinate).rho
  let targetRho := proposition63MildRescalingQuotientRho
    sourceDelta sourceRho scale
  let sourceNormalization :=
    (Classical.choice
      ((sourceSchedule.witness coordinate).scaleData.rescaledFiber
        sourceParent)).normalization
  let targetNormalization := WZ2PaperAssouadUnitRescalingData.ofTube
    ((data.jointRegularizedParents regularized coordinate).family.tube
      targetParent) (data.quotient coordinate).caller_rho_pos
  let sourceDet :=
    |LinearMap.det
      (sourceNormalization.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)|
  let targetDet :=
    |LinearMap.det
      (targetNormalization.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)|
  have hsourceRho : 0 < sourceRho :=
    (sourceSchedule.witness coordinate).scaleData.rho_pos
  have htargetRho : 0 < targetRho :=
    (data.quotient coordinate).caller_rho_pos
  have hsourceLower : sourceRho ^ 2 / 4 ≤ sourceDet :=
    wz2Paper_outerJohn_abs_det_lower
      ((sourceSchedule.witness coordinate).scaleData.coarse.tube sourceParent)
      hsourceRho
  have hsourcePositive : 0 < sourceDet :=
    (div_pos (sq_pos_of_pos hsourceRho) (by norm_num)).trans_le hsourceLower
  have htargetUpper : targetDet ≤
      27 * Real.pi * targetRho ^ 2 * (1 + 2 * targetRho) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).1
    simpa [targetDet, targetNormalization, targetRho, mul_assoc] using
      tube_outerJohn_abs_det_upper_polynomial
        ((data.jointRegularizedParents regularized coordinate).family.tube
          targetParent) htargetRho
  have hinverse : sourceDet⁻¹ ≤ 4 / sourceRho ^ 2 := by
    have hrhoQuarter : 0 < sourceRho ^ 2 / 4 := by positivity
    calc
      sourceDet⁻¹ ≤ (sourceRho ^ 2 / 4)⁻¹ :=
        (inv_le_inv₀ hsourcePositive hrhoQuarter).2 hsourceLower
      _ = 4 / sourceRho ^ 2 := by field_simp
  have hdeltaRho : sourceDelta ≤ sourceRho :=
    (sourceSchedule.requested coordinate).2.1.trans
      (sourceSchedule.witness coordinate).requested_le
  have htargetRatio : targetRho ≤ 5200004 * scale * sourceRho := by
    dsimp only [targetRho, sourceRho]
    unfold proposition63MildRescalingQuotientRho
    nlinarith [mul_nonneg (zero_lt_one.trans_le hscale).le
      (sub_nonneg.mpr hdeltaRho)]
  have hreal : targetDet * scale⁻¹ ^ 3 * sourceDet⁻¹ ≤
      108 * Real.pi * 5200004 ^ 2 * (1 + 2 * targetRho) := by
    have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
    calc
      targetDet * scale⁻¹ ^ 3 * sourceDet⁻¹ ≤
          (27 * Real.pi * targetRho ^ 2 * (1 + 2 * targetRho)) *
            scale⁻¹ ^ 3 * (4 / sourceRho ^ 2) := by gcongr
      _ ≤ (27 * Real.pi * (5200004 * scale * sourceRho) ^ 2 *
            (1 + 2 * targetRho)) * scale⁻¹ ^ 3 *
              (4 / sourceRho ^ 2) := by gcongr
      _ = 108 * Real.pi * 5200004 ^ 2 * (1 + 2 * targetRho) *
            scale⁻¹ := by
        field_simp [hscalePos.ne', hsourceRho.ne'] <;> ring
      _ ≤ 108 * Real.pi * 5200004 ^ 2 * (1 + 2 * targetRho) := by
        exact mul_le_of_le_one_right (by positivity)
          (inv_le_one_of_one_le₀ hscale)
  rw [proposition63MildRescalingJohnCoordinateChange_symm_abs_det]
  change ENNReal.ofReal (targetDet * scale⁻¹ ^ 3 * sourceDet⁻¹) ≤ _
  calc
    ENNReal.ofReal (targetDet * scale⁻¹ ^ 3 * sourceDet⁻¹) ≤
        ENNReal.ofReal
          (108 * Real.pi * 5200004 ^ 2 * (1 + 2 * targetRho)) :=
      ENNReal.ofReal_mono hreal
    _ = 108 * ENNReal.ofReal Real.pi * 5200004 ^ 2 *
          (1 + 2 * ENNReal.ofReal targetRho) := by
      rw [ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by norm_num)
          (mul_nonneg (by norm_num) htargetRho.le),
        ENNReal.ofReal_mul (by norm_num)]
      norm_num
    _ ≤ 108 * ENNReal.ofReal Real.pi * 5200004 ^ 2 *
          (1 + 2 * (ENNReal.ofReal scale *
            Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
              sourceWindowConstant)) := by
      gcongr
      exact data.quotientRho_le_window hconstantWindow coordinate

/-- A uniform pointwise bound on the actual canonical packets bounds their
threefold finite supremum without introducing any new family dependence. -/
theorem Proposition63MildRescalingQuotientScheduleData.quotientScheduleBodyConstant_le_of_packet
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (normalizationWeight retentionConstant envelope : ENNReal)
    (packetBound : ∀ coordinate targetParent sourceParent,
      data.quotientCanonicalPacketConstant regularized normalizationWeight
        retentionConstant coordinate targetParent sourceParent ≤ envelope) :
    data.quotientScheduleBodyConstant regularized normalizationWeight
      retentionConstant ≤ envelope := by
  unfold Proposition63MildRescalingQuotientScheduleData.quotientScheduleBodyConstant
  apply Finset.sup_le
  intro coordinate _
  apply Finset.sup_le
  intro targetParent _
  apply Finset.sup_le
  intro sourceParent _
  exact packetBound coordinate targetParent sourceParent

/-- A fixed determinant and joint-regularization envelope controls every
canonical packet by one explicit scalar expression. -/
theorem Proposition63MildRescalingQuotientScheduleData.quotientCanonicalPacketConstant_le_envelope
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (normalizationWeight retentionConstant determinantEnvelope
      jointEnvelope : ENNReal)
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.jointRegularizedParents regularized coordinate).family.card)
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card)
    (determinantBound :
      ENNReal.ofReal
          |LinearMap.det
            ((proposition63MildRescalingJohnCoordinateChange sourceParent
              (Classical.choice
                ((sourceSchedule.witness coordinate).scaleData.rescaledFiber
                  sourceParent)).normalization targetParent
              (WZ2PaperAssouadUnitRescalingData.ofTube
                ((data.jointRegularizedParents regularized coordinate).family.tube
                  targetParent)
                (data.quotient coordinate).caller_rho_pos) center
              (zero_lt_one.trans_le hscale)).symm.linear :
                Point3 →ₗ[ℝ] Point3)| ≤ determinantEnvelope)
    (jointBound :
      data.quotientFiberRegularizationConstant selection ≤ jointEnvelope) :
    data.quotientCanonicalPacketConstant regularized normalizationWeight
        retentionConstant coordinate targetParent sourceParent ≤
      ENNReal.ofReal (27 * (2 * (22 * scale + 3) - 1) ^ 3) *
        determinantEnvelope *
        ((normalizationWeight⁻¹ *
          (sourceConstant * retentionConstant * jointEnvelope)) *
          sourceConstant) := by
  unfold Proposition63MildRescalingQuotientScheduleData.quotientCanonicalPacketConstant
  unfold Proposition63MildRescalingQuotientScheduleData.quotientPacketConstant
  have jointBound' :
      16 * ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
          ENNReal) *
        (Nat.log 2 (2 * (data.selectedTarget selection).family.card) + 1 :
          ENNReal) ^ (sourceSchedule.scaleCount + sourceSchedule.scaleCount) ≤
        jointEnvelope := by
    simpa [Proposition63MildRescalingQuotientScheduleData.quotientFiberRegularizationConstant]
      using jointBound
  gcongr

/-- The corresponding fixed envelope for the full threefold packet supremum. -/
theorem Proposition63MildRescalingQuotientScheduleData.quotientScheduleBodyConstant_le_envelope
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (normalizationWeight retentionConstant determinantEnvelope
      jointEnvelope : ENNReal)
    (determinantBound : ∀ coordinate targetParent sourceParent,
      ENNReal.ofReal
          |LinearMap.det
            ((proposition63MildRescalingJohnCoordinateChange sourceParent
              (Classical.choice
                ((sourceSchedule.witness coordinate).scaleData.rescaledFiber
                  sourceParent)).normalization targetParent
              (WZ2PaperAssouadUnitRescalingData.ofTube
                ((data.jointRegularizedParents regularized coordinate).family.tube
                  targetParent)
                (data.quotient coordinate).caller_rho_pos) center
              (zero_lt_one.trans_le hscale)).symm.linear :
                Point3 →ₗ[ℝ] Point3)| ≤ determinantEnvelope)
    (jointBound :
      data.quotientFiberRegularizationConstant selection ≤ jointEnvelope) :
    data.quotientScheduleBodyConstant regularized normalizationWeight
        retentionConstant ≤
      ENNReal.ofReal (27 * (2 * (22 * scale + 3) - 1) ^ 3) *
        determinantEnvelope *
        ((normalizationWeight⁻¹ *
          (sourceConstant * retentionConstant * jointEnvelope)) *
          sourceConstant) := by
  apply data.quotientScheduleBodyConstant_le_of_packet
  intro coordinate targetParent sourceParent
  exact data.quotientCanonicalPacketConstant_le_envelope regularized
    normalizationWeight retentionConstant determinantEnvelope jointEnvelope
    coordinate targetParent sourceParent
    (determinantBound coordinate targetParent sourceParent) jointBound

/-- The actual jointly regularized quotient body constant is controlled by
the source window, the fixed scale, and one uniform joint-log envelope.  In
particular, the John determinant is no longer a runtime receipt. -/
theorem Proposition63MildRescalingQuotientScheduleData.quotientScheduleBodyConstant_le_window
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (normalizationWeight retentionConstant jointEnvelope : ENNReal)
    (hconstantWindow : sourceConstant ≤ sourceWindowConstant)
    (jointBound :
      data.quotientFiberRegularizationConstant selection ≤ jointEnvelope) :
    data.quotientScheduleBodyConstant regularized normalizationWeight
        retentionConstant ≤
      ENNReal.ofReal (27 * (2 * (22 * scale + 3) - 1) ^ 3) *
        (108 * ENNReal.ofReal Real.pi *
          (ENNReal.ofReal scale *
            Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
              sourceWindowConstant) ^ 2 *
          (1 + 2 * (ENNReal.ofReal scale *
            Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
              sourceWindowConstant)) *
          Kakeya.realRpowENN sourceDelta (-2)) *
        ((normalizationWeight⁻¹ *
          (sourceConstant * retentionConstant * jointEnvelope)) *
          sourceConstant) := by
  apply data.quotientScheduleBodyConstant_le_envelope regularized
    normalizationWeight retentionConstant
      (108 * ENNReal.ofReal Real.pi *
        (ENNReal.ofReal scale *
          Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
            sourceWindowConstant) ^ 2 *
        (1 + 2 * (ENNReal.ofReal scale *
          Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
            sourceWindowConstant)) *
        Kakeya.realRpowENN sourceDelta (-2)) jointEnvelope
  · intro coordinate targetParent sourceParent
    exact data.canonicalJointPacket_det_le_window regularized
      hconstantWindow coordinate targetParent sourceParent
  · exact jointBound

/-- Cancellation-preserving version of the quotient body envelope. -/
theorem Proposition63MildRescalingQuotientScheduleData.quotientScheduleBodyConstant_le_window_no_power
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (normalizationWeight retentionConstant jointEnvelope : ENNReal)
    (hconstantWindow : sourceConstant ≤ sourceWindowConstant)
    (jointBound :
      data.quotientFiberRegularizationConstant selection ≤ jointEnvelope) :
    data.quotientScheduleBodyConstant regularized normalizationWeight
        retentionConstant ≤
      ENNReal.ofReal (27 * (2 * (22 * scale + 3) - 1) ^ 3) *
        (108 * ENNReal.ofReal Real.pi * 5200004 ^ 2 *
          (1 + 2 * (ENNReal.ofReal scale *
            Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
              sourceWindowConstant))) *
        ((normalizationWeight⁻¹ *
          (sourceConstant * retentionConstant * jointEnvelope)) *
          sourceConstant) := by
  apply data.quotientScheduleBodyConstant_le_envelope regularized
    normalizationWeight retentionConstant
      (108 * ENNReal.ofReal Real.pi * 5200004 ^ 2 *
        (1 + 2 * (ENNReal.ofReal scale *
          Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
            sourceWindowConstant))) jointEnvelope
  · intro coordinate targetParent sourceParent
    exact data.canonicalJointPacket_det_le_window_no_power regularized
      hconstantWindow coordinate targetParent sourceParent
  · exact jointBound

/-- A pre-runtime cutoff absorbs any fixed coefficient multiplying a fixed
negative power.  The cutoff is chosen before the runtime family and before
the eventual target CWA constant. -/
theorem exists_proposition63_m9_fixed_power_envelope_cutoff
    (coefficient : ENNReal) (baseLoss gap : ℝ)
    (coefficientFinite : coefficient ≠ ⊤) (gapPos : 0 < gap) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        coefficient * Kakeya.realRpowENN delta (-baseLoss) ≤
          Kakeya.realRpowENN delta (-(baseLoss + gap)) := by
  rcases exists_delta_realRpowENN_bound coefficient coefficientFinite gapPos with
    ⟨delta₀, delta₀Pos, delta₀One, coefficientBound⟩
  refine ⟨delta₀, delta₀Pos, delta₀One, ?_⟩
  intro delta deltaPos deltaLe
  calc
    coefficient * Kakeya.realRpowENN delta (-baseLoss) ≤
        Kakeya.realRpowENN delta (-gap) *
          Kakeya.realRpowENN delta (-baseLoss) := by
      gcongr
      exact coefficientBound delta deltaPos deltaLe
    _ = Kakeya.realRpowENN delta (-(baseLoss + gap)) := by
      calc
        Kakeya.realRpowENN delta (-gap) *
              Kakeya.realRpowENN delta (-baseLoss) =
            Kakeya.realRpowENN delta ((-gap) + (-baseLoss)) :=
          (Kakeya.Assouad.realRpowENN_add deltaPos (-gap) (-baseLoss)).symm
        _ = Kakeya.realRpowENN delta (-(baseLoss + gap)) := by
          rw [show (-gap) + (-baseLoss) = -(baseLoss + gap) by ring]

/-- The selected target's logarithmic cardinality factor has a family-free
envelope at the target scale. -/
theorem Proposition63M9MildRescalingQuotientTargetData.selectedTarget_cardLog_le_logEnvelope
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    (Nat.log 2
        (2 * (data.quotientSchedule.selectedTarget data.selection).family.card) + 1 :
      ENNReal) ≤
      proposition63OneScaleLogEnvelope (scale * sourceDelta) := by
  let selected := data.quotientSchedule.selectedTarget data.selection
  have targetDeltaPos : 0 < scale * sourceDelta :=
    mul_pos (zero_lt_one.trans_le hscale) sourceExtremal.delta_pos
  have targetDeltaOne : scale * sourceDelta ≤ 1 :=
    hscaleDeltaSmall.trans (by norm_num)
  have selectedDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct
      selected.family :=
    data.quotientSchedule.selectedTarget_ordinaryDistinct_of_cleanup
      data.cleanup data.selection data.selection_subset_cleanup
  have selectedLine : WZ1PaperIsLineClass selected.family :=
    (proposition63MildRescalingFamily_lineClass hscale sourceData.raw
      sourceData.raw_line_class).subfamily selected.toTubeSubfamily
  have selectedCardBound : selected.family.card ≤
      (2 * Nat.ceil (320 / (scale * sourceDelta)) + 1) ^ 6 := by
    have packed := wz2PaperOrdinary_local_six_grid_card_bound
      targetDeltaPos (show (0 : ℝ) ≤ 3 by norm_num) selectedDistinct
      Finset.univ (0 : Point3) (by
        intro index _
        rw [selected.tube_eq]
        simpa [dist_zero_right] using
          proposition63MildRescalingFamily_midpoint_local
            hscale sourceData.raw
            sourceData.raw_line_class (selected.embedding index))
    have hfirst :
        3 / ((scale * sourceDelta) / 64) =
          192 / (scale * sourceDelta) := by
      field_simp [targetDeltaPos.ne']
      ring
    have hsecond :
        1 / ((scale * sourceDelta) / 64) ≤
          320 / (scale * sourceDelta) := by
      have hid : 1 / ((scale * sourceDelta) / 64) =
          64 / (scale * sourceDelta) := by
        field_simp [targetDeltaPos.ne']
      rw [hid]
      exact div_le_div_of_nonneg_right (by norm_num) targetDeltaPos.le
    have hfirstCeil :
        Nat.ceil (3 / ((scale * sourceDelta) / 64)) ≤
          Nat.ceil (320 / (scale * sourceDelta)) := by
      rw [hfirst]
      apply Nat.ceil_mono
      exact div_le_div_of_nonneg_right (by norm_num) targetDeltaPos.le
    have hsecondCeil :
        Nat.ceil (1 / ((scale * sourceDelta) / 64)) ≤
          Nat.ceil (320 / (scale * sourceDelta)) :=
      Nat.ceil_mono hsecond
    let lowerBase := 2 * Nat.ceil (320 / (scale * sourceDelta)) + 1
    let upperBase := 2 * Nat.ceil (320 / (scale * sourceDelta)) + 1
    simpa only [Finset.card_univ, Fintype.card_fin] using
      packed.trans (by
        calc
          (2 * Nat.ceil (3 / ((scale * sourceDelta) / 64)) + 1) ^ 3 *
                (2 * Nat.ceil (1 / ((scale * sourceDelta) / 64)) + 1) ^ 3 ≤
              lowerBase ^ 3 * upperBase ^ 3 := by
            apply Nat.mul_le_mul
            · apply Nat.pow_le_pow_left
              dsimp only [lowerBase]
              omega
            · apply Nat.pow_le_pow_left
              dsimp only [upperBase]
              omega
          _ = upperBase ^ 6 := by
            dsimp only [lowerBase]
            ring)
  have selectedLog :
      (Nat.log 2 (2 * selected.family.card) + 1 : ENNReal) ≤
        proposition63OneScaleLogEnvelope (scale * sourceDelta) := by
    by_cases hcard : 0 < selected.family.card
    · have realBound := pureWZ2Prop62_ordinary_card_log_bound
        targetDeltaPos targetDeltaOne hcard selectedCardBound
      unfold proposition63OneScaleLogEnvelope
      calc
        (Nat.log 2 (2 * selected.family.card) + 1 : ENNReal) =
            ENNReal.ofReal
              (Nat.log 2 (2 * selected.family.card) + 1 : ℝ) := by
          simpa using (ENNReal.ofReal_natCast
            (Nat.log 2 (2 * selected.family.card) + 1)).symm
        _ ≤ ENNReal.ofReal
            (pureWZ2Prop62OrdinaryCardLogConstant *
              (1 + Real.log (scale * sourceDelta)⁻¹)) :=
          ENNReal.ofReal_mono realBound
        _ ≤ ENNReal.ofReal
            (proposition63OneScaleLogCoefficient *
              (1 + Real.log (scale * sourceDelta)⁻¹)) := by
          apply ENNReal.ofReal_mono
          apply mul_le_mul_of_nonneg_right (le_max_right _ _)
          have : (1 : ℝ) ≤ (scale * sourceDelta)⁻¹ :=
            (one_le_inv₀ targetDeltaPos).mpr targetDeltaOne
          linarith [Real.log_nonneg this]
    · have hzero : selected.family.card = 0 := Nat.eq_zero_of_not_pos hcard
      rw [hzero]
      norm_num
      unfold proposition63OneScaleLogEnvelope
      rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num]
      apply ENNReal.ofReal_mono
      have hlog : 0 ≤ Real.log (scale * sourceDelta)⁻¹ :=
        Real.log_nonneg ((one_le_inv₀ targetDeltaPos).mpr targetDeltaOne)
      have hcoefficient : 1 ≤ proposition63OneScaleLogCoefficient :=
        (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
      nlinarith [proposition63OneScaleLogCoefficient_nonneg]
  exact selectedLog

/-- The joint regularization constant of the actual dependent target data has
a family-free logarithmic envelope at the target scale. -/
theorem Proposition63M9MildRescalingQuotientTargetData.quotientFiberRegularizationConstant_le_logEnvelope
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    data.quotientSchedule.quotientFiberRegularizationConstant data.selection ≤
      16 * ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
          ENNReal) *
        proposition63OneScaleLogEnvelope (scale * sourceDelta) ^
          (sourceSchedule.scaleCount + sourceSchedule.scaleCount) := by
  unfold Proposition63MildRescalingQuotientScheduleData.quotientFiberRegularizationConstant
  exact mul_le_mul_left'
    (pow_le_pow_left' data.selectedTarget_cardLog_le_logEnvelope
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)) _

/-- The complete quotient-selection loss has no residual family dependence:
its only nonconstant factor is a fixed power of the target-scale log envelope. -/
theorem Proposition63M9MildRescalingQuotientTargetData.selectionLoss_le_logEnvelope
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    data.selectionLoss ≤
      (((((2 * Nat.ceil (11200 * scale) + 1) ^ 5 + 1 : ℕ) : ENNReal) *
          (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
            sourceSchedule.scaleCount) * 8) *
        proposition63OneScaleLogEnvelope (scale * sourceDelta) ^
          (sourceSchedule.scaleCount + sourceSchedule.scaleCount + 1) := by
  have hdegree : proposition63MildRescalingConflictDegree sourceDelta scale =
      (2 * Nat.ceil (11200 * scale) + 1) ^ 5 := by
    unfold proposition63MildRescalingConflictDegree
    congr 3
    apply congrArg Nat.ceil
    field_simp [sourceExtremal.delta_pos.ne']
    ring
  rw [Proposition63M9MildRescalingQuotientTargetData.selectionLoss, hdegree]
  have selectedLog :
      (Nat.log 2
        (2 * (data.quotientSchedule.selectedTarget data.selection).family.card) + 1 :
          ENNReal) ≤
        proposition63OneScaleLogEnvelope (scale * sourceDelta) :=
    data.selectedTarget_cardLog_le_logEnvelope
  calc
    (((((2 * Nat.ceil (11200 * scale) + 1) ^ 5 + 1 : ℕ) : ENNReal) *
          (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
            sourceSchedule.scaleCount) *
        (8 * (Nat.log 2
          (2 * (data.quotientSchedule.selectedTarget data.selection).family.card) + 1 :
            ENNReal) ^
          (sourceSchedule.scaleCount + sourceSchedule.scaleCount + 1))) ≤
      (((((2 * Nat.ceil (11200 * scale) + 1) ^ 5 + 1 : ℕ) : ENNReal) *
          (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
            sourceSchedule.scaleCount) *
        (8 * proposition63OneScaleLogEnvelope (scale * sourceDelta) ^
          (sourceSchedule.scaleCount + sourceSchedule.scaleCount + 1))) := by
      gcongr
    _ = (((((2 * Nat.ceil (11200 * scale) + 1) ^ 5 + 1 : ℕ) : ENNReal) *
          (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
            sourceSchedule.scaleCount) * 8) *
        proposition63OneScaleLogEnvelope (scale * sourceDelta) ^
          (sourceSchedule.scaleCount + sourceSchedule.scaleCount + 1) := by ring

/-- The actual body constant on one dependent `targetData` is bounded by the
same family-free target-scale log envelope and the source schedule window. -/
theorem Proposition63M9MildRescalingQuotientTargetData.quotientScheduleBodyConstant_le_logWindowEnvelope
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule)
    (normalizationWeight retentionConstant : ENNReal)
    (hconstantWindow : scheduleConstant ≤ scheduleWindowConstant) :
    data.quotientSchedule.quotientScheduleBodyConstant data.jointRegularized
        normalizationWeight retentionConstant ≤
      ENNReal.ofReal (27 * (2 * (22 * scale + 3) - 1) ^ 3) *
        (108 * ENNReal.ofReal Real.pi * 5200004 ^ 2 *
          (1 + 2 * (ENNReal.ofReal scale *
            Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
              scheduleWindowConstant))) *
        ((normalizationWeight⁻¹ *
          (scheduleConstant * retentionConstant *
            (16 *
              ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
                ENNReal) *
              proposition63OneScaleLogEnvelope (scale * sourceDelta) ^
                (sourceSchedule.scaleCount + sourceSchedule.scaleCount)))) *
          scheduleConstant) := by
  apply data.quotientSchedule.quotientScheduleBodyConstant_le_window_no_power
    data.jointRegularized normalizationWeight retentionConstant
      (16 *
        ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
          ENNReal) *
        proposition63OneScaleLogEnvelope (scale * sourceDelta) ^
          (sourceSchedule.scaleCount + sourceSchedule.scaleCount))
    hconstantWindow
  exact data.quotientFiberRegularizationConstant_le_logEnvelope

/-- The inverse of the actual normalization weight separates into a frozen
scale coefficient and the sole runtime power of the source radius. -/
theorem realRpowENN_inv_eq_neg {delta loss : ℝ} (hdelta : 0 < delta) :
    (Kakeya.realRpowENN delta loss)⁻¹ =
      Kakeya.realRpowENN delta (-loss) := by
  calc
    (Kakeya.realRpowENN delta loss)⁻¹ =
        ENNReal.ofReal ((Real.rpow delta loss)⁻¹) :=
      (ENNReal.ofReal_inv_of_pos
        (Real.rpow_pos_of_pos hdelta loss)).symm
    _ = ENNReal.ofReal (Real.rpow delta (-loss)) := by
      congr 1
      exact (Real.rpow_neg hdelta.le loss).symm
    _ = Kakeya.realRpowENN delta (-loss) := rfl

theorem proposition63M9_actualNormalizationWeight_inv_eq
    {sourceDelta sourceLoss scale : ℝ} (hdelta : 0 < sourceDelta) :
    ((((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
          ENNReal.ofReal scale) *
        ((1 / 2 : ENNReal) *
          (ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3) *
            Kakeya.realRpowENN sourceDelta sourceLoss)))⁻¹) =
      ((((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
            ENNReal.ofReal scale) *
          ((1 / 2 : ENNReal) *
            ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3)))⁻¹) *
        Kakeya.realRpowENN sourceDelta (-sourceLoss) := by
  let fixed : ENNReal :=
    ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
      ENNReal.ofReal scale) *
      ((1 / 2 : ENNReal) *
        ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3))
  have hrpowZero : Kakeya.realRpowENN sourceDelta sourceLoss ≠ 0 := by
    simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hdelta]
  have hrpowTop : Kakeya.realRpowENN sourceDelta sourceLoss ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have hinv :
      (fixed * Kakeya.realRpowENN sourceDelta sourceLoss)⁻¹ =
        fixed⁻¹ * (Kakeya.realRpowENN sourceDelta sourceLoss)⁻¹ :=
    ENNReal.mul_inv (Or.inr hrpowTop) (Or.inr hrpowZero)
  have hrpowInv := realRpowENN_inv_eq_neg
    (loss := sourceLoss) hdelta
  change (_ * (_ * (_ * Kakeya.realRpowENN sourceDelta sourceLoss)))⁻¹ =
    fixed⁻¹ * Kakeya.realRpowENN sourceDelta (-sourceLoss)
  rw [show
    ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
        ENNReal.ofReal scale) *
          ((1 / 2 : ENNReal) *
            (ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3) *
              Kakeya.realRpowENN sourceDelta sourceLoss)) =
      fixed * Kakeya.realRpowENN sourceDelta sourceLoss by
        dsimp only [fixed]
        ac_rfl]
  rw [hinv, hrpowInv]

/-- Fully family-free specialization of the preceding bound to the actual
normalization weight and retention loss used by the quotient tail. -/
theorem Proposition63M9MildRescalingQuotientTargetData.quotientScheduleBodyConstant_le_actualFamilyFreeEnvelope
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule)
    (hconstantWindow : scheduleConstant ≤ scheduleWindowConstant) :
    data.quotientSchedule.quotientScheduleBodyConstant data.jointRegularized
        (((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
          ENNReal.ofReal scale) *
          ((1 / 2 : ENNReal) * sourceData.sourceDensity))
        (data.selectionLoss * (55296 * Kakeya.deltaTubeVolume 1)) ≤
      ENNReal.ofReal (27 * (2 * (22 * scale + 3) - 1) ^ 3) *
        (108 * ENNReal.ofReal Real.pi * 5200004 ^ 2 *
          (1 + 2 * (ENNReal.ofReal scale *
            Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
              scheduleWindowConstant))) *
        ((((((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
                ENNReal.ofReal scale) *
              ((1 / 2 : ENNReal) *
                ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3)))⁻¹ *
            Kakeya.realRpowENN sourceDelta (-sourceLoss)) *
          (scheduleConstant *
            ((((((2 * Nat.ceil (11200 * scale) + 1) ^ 5 + 1 : ℕ) : ENNReal) *
                (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
                  sourceSchedule.scaleCount) * 8) *
              proposition63OneScaleLogEnvelope (scale * sourceDelta) ^
                (sourceSchedule.scaleCount + sourceSchedule.scaleCount + 1)) *
              (55296 * Kakeya.deltaTubeVolume 1) *
              (16 *
                ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
                  ENNReal) *
                proposition63OneScaleLogEnvelope (scale * sourceDelta) ^
                  (sourceSchedule.scaleCount + sourceSchedule.scaleCount)))) *
          scheduleConstant) := by
  have retentionBound :
      data.selectionLoss * (55296 * Kakeya.deltaTubeVolume 1) ≤
        ((((((2 * Nat.ceil (11200 * scale) + 1) ^ 5 + 1 : ℕ) : ENNReal) *
              (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
                sourceSchedule.scaleCount) * 8) *
            proposition63OneScaleLogEnvelope (scale * sourceDelta) ^
              (sourceSchedule.scaleCount + sourceSchedule.scaleCount + 1)) *
          (55296 * Kakeya.deltaTubeVolume 1) := by
    simpa [mul_comm] using mul_le_mul_right
      data.selectionLoss_le_logEnvelope
      (55296 * Kakeya.deltaTubeVolume 1)
  have bodyBound := data.quotientScheduleBodyConstant_le_logWindowEnvelope
    ((((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
      ENNReal.ofReal scale) *
      ((1 / 2 : ENNReal) * sourceData.sourceDensity)))
    (data.selectionLoss * (55296 * Kakeya.deltaTubeVolume 1)) hconstantWindow
  rw [sourceData.sourceDensity_eq] at bodyBound ⊢
  apply bodyBound.trans
  have innerBound := mul_le_mul_right'
    (mul_le_mul_left'
      (mul_le_mul_right'
        (mul_le_mul_left' retentionBound scheduleConstant)
        (16 *
          ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
            ENNReal) *
          proposition63OneScaleLogEnvelope (scale * sourceDelta) ^
            (sourceSchedule.scaleCount + sourceSchedule.scaleCount)))
      (((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
          ENNReal.ofReal scale) *
        ((1 / 2 : ENNReal) *
          (ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3) *
            Kakeya.realRpowENN sourceDelta sourceLoss)))⁻¹)
    scheduleConstant
  have outerBound := mul_le_mul_left' innerBound
    (ENNReal.ofReal (27 * (2 * (22 * scale + 3) - 1) ^ 3) *
      (108 * ENNReal.ofReal Real.pi * 5200004 ^ 2 *
        (1 + 2 * (ENNReal.ofReal scale *
          Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
            scheduleWindowConstant))))
  apply outerBound.trans_eq
  rw [proposition63M9_actualNormalizationWeight_inv_eq
    sourceExtremal.delta_pos]
  ac_rfl

/-- Family-independent scalar choices for the final mild rescaling. -/
structure Proposition63M9RobustTailScheduleData
    (sourceLoss : ℝ) (Lplane Lslope : NNReal) where
  scale : ℝ
  scale_eq : scale = max 1 (max (Lplane : ℝ) (Lslope : ℝ))
  scale_one : 1 ≤ scale
  plane_scale : (Lplane : ℝ) ≤ scale
  slope_scale : (Lslope : ℝ) ≤ scale
  levelCount : ℕ
  levelCount_pos : 0 < levelCount
  levelCount_loss : 1 ≤ (levelCount : ℝ) * sourceLoss
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  scale_delta_small : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    scale * delta ≤ 1 / 1000
  ambient_two : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    (2 : ENNReal) < Kakeya.realRpowENN delta (-sourceLoss)

namespace Proposition63M9RobustTailScheduleData

variable {sourceLoss : ℝ} {Lplane Lslope : NNReal}
    (schedule : Proposition63M9RobustTailScheduleData
      sourceLoss Lplane Lslope)

/-- The source family itself has the same family-free logarithmic envelope. -/
theorem source_cardLog_le_logEnvelope
    {sourceDelta sigma : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading)
    (sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3) :
    (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ≤
      proposition63OneScaleLogEnvelope sourceDelta := by
  have cardBound : sourceFamily.card ≤
      (2 * Nat.ceil (320 / sourceDelta) + 1) ^ 6 := by
    have packed := wz2PaperOrdinary_local_six_grid_card_bound
      sourceExtremal.delta_pos (show (0 : ℝ) ≤ 3 by norm_num)
      sourceExtremal.cwa_nearby_scales.2.2.1 Finset.univ (0 : Point3) (by
        intro index _
        simpa [dist_zero_right] using sourceMidpoint index)
    have hfirst : 3 / (sourceDelta / 64) = 192 / sourceDelta := by
      field_simp [sourceExtremal.delta_pos.ne']
      ring
    have hfirstCeil : Nat.ceil (3 / (sourceDelta / 64)) ≤
        Nat.ceil (320 / sourceDelta) := by
      rw [hfirst]
      exact Nat.ceil_mono <|
        div_le_div_of_nonneg_right (by norm_num) sourceExtremal.delta_pos.le
    have hsecondCeil : Nat.ceil (1 / (sourceDelta / 64)) ≤
        Nat.ceil (320 / sourceDelta) := by
      apply Nat.ceil_mono
      have hid : 1 / (sourceDelta / 64) = 64 / sourceDelta := by
        field_simp [sourceExtremal.delta_pos.ne']
      rw [hid]
      exact div_le_div_of_nonneg_right (by norm_num)
        sourceExtremal.delta_pos.le
    simpa only [Finset.card_univ, Fintype.card_fin] using packed.trans (by
      calc
        (2 * Nat.ceil (3 / (sourceDelta / 64)) + 1) ^ 3 *
              (2 * Nat.ceil (1 / (sourceDelta / 64)) + 1) ^ 3 ≤
            (2 * Nat.ceil (320 / sourceDelta) + 1) ^ 3 *
              (2 * Nat.ceil (320 / sourceDelta) + 1) ^ 3 := by gcongr
        _ = (2 * Nat.ceil (320 / sourceDelta) + 1) ^ 6 := by ring)
  have realBound := pureWZ2Prop62_ordinary_card_log_bound
    sourceExtremal.delta_pos sourceExtremal.delta_le_one
    sourceExtremal.nonempty cardBound
  unfold proposition63OneScaleLogEnvelope
  calc
    (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) =
        ENNReal.ofReal
          (Nat.log 2 (2 * sourceFamily.card) + 1 : ℝ) := by
      simpa using (ENNReal.ofReal_natCast
        (Nat.log 2 (2 * sourceFamily.card) + 1)).symm
    _ ≤ ENNReal.ofReal
        (pureWZ2Prop62OrdinaryCardLogConstant *
          (1 + Real.log sourceDelta⁻¹)) := ENNReal.ofReal_mono realBound
    _ ≤ ENNReal.ofReal
        (proposition63OneScaleLogCoefficient *
          (1 + Real.log sourceDelta⁻¹)) := by
      apply ENNReal.ofReal_mono
      apply mul_le_mul_of_nonneg_right (le_max_right _ _)
      have hlog : 0 ≤ Real.log sourceDelta⁻¹ :=
        Real.log_nonneg ((one_le_inv₀ sourceExtremal.delta_pos).mpr
          sourceExtremal.delta_le_one)
      linarith

/-- The complete runtime-family expression which must be dominated by the
source nearby-CWA constant. -/
def sourceRegularizationExpression
    {sourceDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta) : ENNReal :=
  let density :=
    ENNReal.ofReal ((1 / 2000000 : ℝ) / schedule.scale ^ 3) *
      Kakeya.realRpowENN sourceDelta sourceLoss
  let degreeConstant :=
    16 * ((schedule.levelCount + 1 : ℕ) : ENNReal) *
      (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
        (schedule.levelCount + 1)
  let regularizationLoss :=
    (8 : ENNReal) *
      (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
        (schedule.levelCount + 2)
  let weight := (1 / 2 : ENNReal) * density
  let cardinalityLoss :=
    (2 * regularizationLoss) * (55296 * Kakeya.deltaTubeVolume 1)
  max degreeConstant
      ((weight⁻¹ *
          (Kakeya.realRpowENN sourceDelta (-sourceLoss) *
            cardinalityLoss * degreeConstant)) *
        Kakeya.realRpowENN sourceDelta (-sourceLoss))

/-- The least explicit constant simultaneously satisfying the source window
and the complete finite-family regularization receipt. -/
def sourceOutputConstant
    {sourceDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta) : ENNReal :=
  max
    (Kakeya.realRpowENN sourceDelta (-sourceLoss) *
      Kakeya.realRpowENN sourceDelta (-sourceLoss))
    (schedule.sourceRegularizationExpression sourceFamily)

/-- Fixed part of the source regularization bound. -/
def sourceEnvelopeCoefficient : ENNReal :=
  let degree : ENNReal := 16 * (schedule.levelCount + 1 : ℕ)
  let density : ENNReal := (1 / 2) *
    ENNReal.ofReal ((1 / 2000000 : ℝ) / schedule.scale ^ 3)
  max 1 <| max degree <|
    density⁻¹ * ((2 * 8) * (55296 * Kakeya.deltaTubeVolume 1) * degree)

theorem sourceEnvelopeCoefficient_ne_top :
    schedule.sourceEnvelopeCoefficient ≠ ⊤ := by
  unfold sourceEnvelopeCoefficient
  apply max_ne_top
  · norm_num
  · apply max_ne_top
    · finiteness
    · apply ENNReal.mul_ne_top
      · apply ENNReal.inv_ne_top.mpr
        apply mul_ne_zero
        · norm_num
        · exact (ENNReal.ofReal_pos.mpr (by
            have hscalePos : 0 < schedule.scale :=
              zero_lt_one.trans_le schedule.scale_one
            positivity)).ne'
      · apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · apply ENNReal.mul_ne_top <;> norm_num
          · exact ENNReal.mul_ne_top (by norm_num)
              deltaTubeVolume_one_ne_top
        · exact ENNReal.mul_ne_top (by norm_num)
            (ENNReal.natCast_ne_top _)

/-- The runtime source-family constant has a uniform fixed-log-power bound. -/
theorem sourceOutputConstant_le_familyFreeEnvelope
    {sourceDelta sigma : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading)
    (sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3)
    (sourceLossPos : 0 < sourceLoss) :
    schedule.sourceOutputConstant sourceFamily ≤
      schedule.sourceEnvelopeCoefficient *
        proposition63OneScaleLogEnvelope sourceDelta ^
          (schedule.levelCount + schedule.levelCount + 3) *
        Kakeya.realRpowENN sourceDelta (-(3 * sourceLoss)) := by
  let logEnvelope := proposition63OneScaleLogEnvelope sourceDelta
  let ambient := Kakeya.realRpowENN sourceDelta (-sourceLoss)
  let degree : ENNReal := 16 * (schedule.levelCount + 1 : ℕ)
  let density : ENNReal := (1 / 2) *
    ENNReal.ofReal ((1 / 2000000 : ℝ) / schedule.scale ^ 3)
  have logOne : (1 : ENNReal) ≤ logEnvelope := by
    dsimp only [logEnvelope, proposition63OneScaleLogEnvelope]
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num]
    apply ENNReal.ofReal_mono
    have hlog : 0 ≤ Real.log sourceDelta⁻¹ :=
      Real.log_nonneg ((one_le_inv₀ sourceExtremal.delta_pos).mpr
        sourceExtremal.delta_le_one)
    have hcoefficient : 1 ≤ proposition63OneScaleLogCoefficient :=
      (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
    nlinarith [proposition63OneScaleLogCoefficient_nonneg]
  have ambientOne : (1 : ENNReal) ≤ ambient := by
    have hreal : Real.rpow sourceDelta 0 ≤
        Real.rpow sourceDelta (-sourceLoss) :=
      Real.rpow_le_rpow_of_exponent_ge sourceExtremal.delta_pos
        sourceExtremal.delta_le_one (by
          linarith)
    simpa [ambient, Kakeya.realRpowENN] using ENNReal.ofReal_mono hreal
  have cardLog := source_cardLog_le_logEnvelope
    sourceExtremal sourceMidpoint
  have ambientCube : ambient * ambient * ambient =
      Kakeya.realRpowENN sourceDelta (-(3 * sourceLoss)) := by
    rw [← Kakeya.Assouad.realRpowENN_add sourceExtremal.delta_pos,
      ← Kakeya.Assouad.realRpowENN_add sourceExtremal.delta_pos]
    congr 1
    ring
  have densityInv :
      (density * Kakeya.realRpowENN sourceDelta sourceLoss)⁻¹ =
        density⁻¹ * ambient := by
    rw [ENNReal.mul_inv
      (Or.inr (by simp [Kakeya.realRpowENN]))
      (Or.inr (by simp [Kakeya.realRpowENN,
        Real.rpow_pos_of_pos sourceExtremal.delta_pos]))]
    rw [realRpowENN_inv_eq_neg sourceExtremal.delta_pos]
  unfold sourceOutputConstant sourceRegularizationExpression
  dsimp only
  apply max_le
  · calc
      ambient * ambient ≤ 1 * logEnvelope ^
          (schedule.levelCount + schedule.levelCount + 3) *
          (ambient * ambient * ambient) := by
        have hlogs : (1 : ENNReal) ≤
            logEnvelope ^ (schedule.levelCount + schedule.levelCount + 3) :=
          one_le_pow₀ logOne
        calc
          ambient * ambient = 1 * (ambient * ambient) := by simp
          _ ≤ logEnvelope ^ (schedule.levelCount + schedule.levelCount + 3) *
              (ambient * ambient) := by gcongr
          _ ≤ logEnvelope ^ (schedule.levelCount + schedule.levelCount + 3) *
              (ambient * ambient * ambient) := by
            apply mul_le_mul_left'
            calc
              ambient * ambient = ambient * ambient * 1 := by simp
              _ ≤ ambient * ambient * ambient := by gcongr
          _ = 1 * logEnvelope ^
              (schedule.levelCount + schedule.levelCount + 3) *
              (ambient * ambient * ambient) := by simp
      _ ≤ schedule.sourceEnvelopeCoefficient *
          logEnvelope ^ (schedule.levelCount + schedule.levelCount + 3) *
            (ambient * ambient * ambient) := by
        gcongr
        exact le_max_left _ _
      _ = _ := by rw [ambientCube]
  · apply max_le
    · calc
        degree * (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
              (schedule.levelCount + 1) ≤
            degree * logEnvelope ^ (schedule.levelCount + 1) := by gcongr
        _ ≤ degree * logEnvelope ^
              (schedule.levelCount + schedule.levelCount + 3) *
              (ambient * ambient * ambient) := by
          have hp : logEnvelope ^ (schedule.levelCount + 1) ≤
              logEnvelope ^ (schedule.levelCount + schedule.levelCount + 3) :=
            pow_le_pow_right₀ logOne (by omega)
          calc
            degree * logEnvelope ^ (schedule.levelCount + 1) ≤
                degree * logEnvelope ^
                  (schedule.levelCount + schedule.levelCount + 3) := by gcongr
            _ ≤ degree * logEnvelope ^
                  (schedule.levelCount + schedule.levelCount + 3) *
                (ambient * ambient * ambient) := by
              apply le_mul_of_one_le_right'
              exact one_le_mul_of_one_le_of_one_le
                (one_le_mul_of_one_le_of_one_le ambientOne ambientOne)
                ambientOne
        _ ≤ schedule.sourceEnvelopeCoefficient *
              logEnvelope ^ (schedule.levelCount + schedule.levelCount + 3) *
                (ambient * ambient * ambient) := by
          gcongr
          exact (le_max_left degree _).trans (le_max_right _ _)
        _ = _ := by rw [ambientCube]
    · rw [show
          (1 / 2 : ENNReal) *
              (ENNReal.ofReal ((1 / 2000000 : ℝ) / schedule.scale ^ 3) *
                Kakeya.realRpowENN sourceDelta sourceLoss) =
            density * Kakeya.realRpowENN sourceDelta sourceLoss by
          dsimp only [density]
          ac_rfl,
        densityInv]
      have hcardLoss :
          (2 * ((8 : ENNReal) *
              (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
                (schedule.levelCount + 2))) *
              (55296 * Kakeya.deltaTubeVolume 1) ≤
            ((2 * 8) * (55296 * Kakeya.deltaTubeVolume 1)) *
              logEnvelope ^ (schedule.levelCount + 2) := by
        calc
          (2 * ((8 : ENNReal) *
                (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
                  (schedule.levelCount + 2))) *
                (55296 * Kakeya.deltaTubeVolume 1) ≤
              (2 * (8 * logEnvelope ^ (schedule.levelCount + 2))) *
                (55296 * Kakeya.deltaTubeVolume 1) := by gcongr
          _ = ((2 * 8) * (55296 * Kakeya.deltaTubeVolume 1)) *
                logEnvelope ^ (schedule.levelCount + 2) := by ac_rfl
      have hdegree : degree *
          (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
            (schedule.levelCount + 1) ≤
          degree * logEnvelope ^ (schedule.levelCount + 1) := by gcongr
      have hcombined :
          ((2 * ((8 : ENNReal) *
              (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
                (schedule.levelCount + 2))) *
              (55296 * Kakeya.deltaTubeVolume 1)) *
            (degree *
              (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
                (schedule.levelCount + 1)) ≤
          (((2 * 8) * (55296 * Kakeya.deltaTubeVolume 1)) * degree) *
            logEnvelope ^
              (schedule.levelCount + schedule.levelCount + 3) := by
        calc
          _ ≤ (((2 * 8) * (55296 * Kakeya.deltaTubeVolume 1)) *
                logEnvelope ^ (schedule.levelCount + 2)) *
              (degree * logEnvelope ^ (schedule.levelCount + 1)) := by gcongr
          _ = _ := by
            have hpow : logEnvelope ^ (schedule.levelCount + 2) *
                logEnvelope ^ (schedule.levelCount + 1) =
              logEnvelope ^ (schedule.levelCount + schedule.levelCount + 3) := by
              rw [← pow_add]
              congr 1
              omega
            calc
              _ = ((2 * 8) * (55296 * Kakeya.deltaTubeVolume 1) * degree) *
                    (logEnvelope ^ (schedule.levelCount + 2) *
                      logEnvelope ^ (schedule.levelCount + 1)) := by ac_rfl
              _ = _ := by rw [hpow]
      have hcombinedWithAmbient :
          density⁻¹ * ambient *
                (ambient *
                  ((2 * ((8 : ENNReal) *
                      (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
                        (schedule.levelCount + 2))) *
                      (55296 * Kakeya.deltaTubeVolume 1)) *
                    (degree *
                      (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
                        (schedule.levelCount + 1))) * ambient ≤
            density⁻¹ * ambient *
                (ambient *
                  ((((2 * 8) * (55296 * Kakeya.deltaTubeVolume 1)) * degree) *
                    logEnvelope ^
                      (schedule.levelCount + schedule.levelCount + 3))) *
              ambient := by
        have lifted := mul_le_mul_left'
          (mul_le_mul_right'
            (mul_le_mul_left' hcombined ambient) ambient)
          (density⁻¹ * ambient)
        convert lifted using 1 <;> ac_rfl
      calc
        density⁻¹ * ambient *
              (ambient *
                ((2 * ((8 : ENNReal) *
                    (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
                      (schedule.levelCount + 2))) *
                    (55296 * Kakeya.deltaTubeVolume 1)) *
                  (degree *
                    (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
                      (schedule.levelCount + 1))) * ambient ≤
            density⁻¹ * ambient *
              (ambient *
                ((((2 * 8) * (55296 * Kakeya.deltaTubeVolume 1)) * degree) *
                    logEnvelope ^
                      (schedule.levelCount + schedule.levelCount + 3))) *
              ambient := hcombinedWithAmbient
        _ = (density⁻¹ *
              ((2 * 8) * (55296 * Kakeya.deltaTubeVolume 1) * degree)) *
              logEnvelope ^ (schedule.levelCount + schedule.levelCount + 3) *
                (ambient * ambient * ambient) := by ac_rfl
        _ ≤ schedule.sourceEnvelopeCoefficient *
              logEnvelope ^ (schedule.levelCount + schedule.levelCount + 3) *
                (ambient * ambient * ambient) := by
          gcongr
          exact (le_max_right degree _).trans (le_max_right _ _)
        _ = _ := by rw [ambientCube]

/-- A family-free cutoff turns the explicit source constant into a pure
negative power.  The cutoff is selected before the runtime scale and family. -/
theorem exists_sourceOutputConstant_power_cutoff
    (sourceLossPos : 0 < sourceLoss) (gap : ℝ) (gapPos : 0 < gap) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sourceDelta sigma : ℝ}, 0 < sourceDelta → sourceDelta ≤ delta₀ →
        ∀ {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
          {sourceShading : WZ1PaperTubeShading sourceFamily},
          WZ2PaperCroppedIsExtremal
              sigma sourceLoss sourceFamily sourceShading →
          (∀ index,
            ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3) →
          schedule.sourceOutputConstant sourceFamily ≤
            Kakeya.realRpowENN sourceDelta (-(3 * sourceLoss + gap)) := by
  have exponentPos : 0 < schedule.levelCount + schedule.levelCount + 3 := by
    omega
  rcases Kakeya.Assouad.exists_delta_C_pow_log_absorbed_ennreal
      schedule.sourceEnvelopeCoefficient
      schedule.sourceEnvelopeCoefficient_ne_top
      proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg gapPos exponentPos with
    ⟨delta₀, delta₀Pos, delta₀One, absorb⟩
  refine ⟨delta₀, delta₀Pos, delta₀One, ?_⟩
  intro sourceDelta sigma deltaPos deltaLe sourceFamily sourceShading
    sourceExtremal sourceMidpoint
  have envelope := schedule.sourceOutputConstant_le_familyFreeEnvelope
    sourceExtremal sourceMidpoint sourceLossPos
  calc
    schedule.sourceOutputConstant sourceFamily ≤
        schedule.sourceEnvelopeCoefficient *
          proposition63OneScaleLogEnvelope sourceDelta ^
            (schedule.levelCount + schedule.levelCount + 3) *
          Kakeya.realRpowENN sourceDelta (-(3 * sourceLoss)) := envelope
    _ ≤ Kakeya.realRpowENN sourceDelta (-gap) *
          Kakeya.realRpowENN sourceDelta (-(3 * sourceLoss)) := by
      apply mul_le_mul_right'
      simpa [proposition63OneScaleLogEnvelope] using
        absorb sourceDelta deltaPos deltaLe
    _ = Kakeya.realRpowENN sourceDelta (-(3 * sourceLoss + gap)) := by
      rw [← Kakeya.Assouad.realRpowENN_add deltaPos]
      congr 1
      ring

theorem sourceOutputConstant_ne_top
    {sourceDelta : ℝ} (hdelta : 0 < sourceDelta)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta) :
    schedule.sourceOutputConstant sourceFamily ≠ ⊤ := by
  apply (max_lt_iff.mpr ⟨?_, ?_⟩).ne
  · apply ENNReal.mul_lt_top
    · simp [Kakeya.realRpowENN]
    · simp [Kakeya.realRpowENN]
  · unfold sourceRegularizationExpression
    dsimp only
    apply max_lt
    · finiteness
    · have hscalePos : 0 < schedule.scale :=
        zero_lt_one.trans_le schedule.scale_one
      have hdensity :
          ENNReal.ofReal ((1 / 2000000 : ℝ) / schedule.scale ^ 3) *
              Kakeya.realRpowENN sourceDelta sourceLoss ≠ 0 := by
        apply mul_ne_zero
        · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
        · simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hdelta]
      have hweight :
          (1 / 2 : ENNReal) *
              (ENNReal.ofReal ((1 / 2000000 : ℝ) / schedule.scale ^ 3) *
                Kakeya.realRpowENN sourceDelta sourceLoss) ≠ 0 :=
        mul_ne_zero (by norm_num) hdensity
      apply ENNReal.mul_lt_top
      · apply ENNReal.mul_lt_top
        · exact (ENNReal.inv_ne_top.mpr hweight).lt_top
        · have hambient :
              Kakeya.realRpowENN sourceDelta (-sourceLoss) < ⊤ := by
            simp [Kakeya.realRpowENN]
          have hlog :
              (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) < ⊤ := by
            exact ENNReal.add_lt_top.mpr
              ⟨ENNReal.natCast_lt_top _, by norm_num⟩
          have hregularization :
              (8 : ENNReal) *
                  (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
                    (schedule.levelCount + 2) < ⊤ :=
            ENNReal.mul_lt_top (by norm_num) (ENNReal.pow_lt_top hlog)
          have hcardinalityLoss :
              (2 * ((8 : ENNReal) *
                    (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
                      (schedule.levelCount + 2))) *
                (55296 * Kakeya.deltaTubeVolume 1) < ⊤ := by
            apply ENNReal.mul_lt_top
            · exact ENNReal.mul_lt_top (by norm_num) hregularization
            · exact ENNReal.mul_lt_top (by norm_num)
                deltaTubeVolume_one_ne_top.lt_top
          have hdegree :
              (16 : ENNReal) * ((schedule.levelCount + 1 : ℕ) : ENNReal) *
                  (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
                    (schedule.levelCount + 1) < ⊤ := by
            exact ENNReal.mul_lt_top
              (ENNReal.mul_lt_top (by norm_num) (ENNReal.natCast_lt_top _))
              (ENNReal.pow_lt_top hlog)
          exact ENNReal.mul_lt_top
            (ENNReal.mul_lt_top hambient hcardinalityLoss) hdegree
      · simp [Kakeya.realRpowENN]

theorem source_levels
    {sourceDelta : ℝ} (hdelta : 0 < sourceDelta)
    (hdeltaOne : sourceDelta ≤ 1) :
    ENNReal.ofReal (1 / sourceDelta) ≤
      Kakeya.realRpowENN sourceDelta (-sourceLoss) ^
        schedule.levelCount := by
  have hexponent : -1 ≥ -(schedule.levelCount : ℝ) * sourceLoss := by
    linarith [schedule.levelCount_loss]
  have hrpow : Real.rpow sourceDelta (-1) ≤
      Real.rpow sourceDelta (-(schedule.levelCount : ℝ) * sourceLoss) :=
    Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne hexponent
  have hleft : Real.rpow sourceDelta (-1) = 1 / sourceDelta := by
    calc
      Real.rpow sourceDelta (-1) = sourceDelta⁻¹ :=
        Real.rpow_neg_one sourceDelta
      _ = 1 / sourceDelta := inv_eq_one_div _
  have hright :
      Kakeya.realRpowENN sourceDelta (-sourceLoss) ^ schedule.levelCount =
        ENNReal.ofReal
          (Real.rpow sourceDelta
            (-(schedule.levelCount : ℝ) * sourceLoss)) := by
    have hbase :
        Kakeya.realRpowENN sourceDelta (-sourceLoss) =
          ENNReal.ofReal (Real.rpow sourceDelta (-sourceLoss)) := by
      rfl
    rw [hbase]
    have hpow :
        (ENNReal.ofReal (Real.rpow sourceDelta (-sourceLoss))) ^
            schedule.levelCount =
          ENNReal.ofReal
            ((Real.rpow sourceDelta (-sourceLoss)) ^
              schedule.levelCount) := by
      exact (ENNReal.ofReal_pow
        (Real.rpow_nonneg hdelta.le _) schedule.levelCount).symm
    rw [hpow]
    congr 1
    rw [rpow_nat_pow hdelta (-sourceLoss) schedule.levelCount]
    ring
  rw [hright, ← hleft]
  exact ENNReal.ofReal_mono hrpow

/-- Specialize the frozen schedule to an actual finite source family. -/
theorem sourceCertificates
    {sourceDelta : ℝ} (hdelta : 0 < sourceDelta)
    (hdeltaCutoff : sourceDelta ≤ schedule.delta₀)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta) :
    Proposition63M9RobustTailSourceCertificates
      (sourceLoss := sourceLoss) (sourceFamily := sourceFamily)
      schedule.scale_one schedule.levelCount
      (schedule.sourceOutputConstant sourceFamily) := by
  refine {
    scale_delta_small := schedule.scale_delta_small hdelta hdeltaCutoff
    ambient_two := schedule.ambient_two hdelta hdeltaCutoff
    levels := schedule.source_levels hdelta
      (hdeltaCutoff.trans schedule.delta₀_le_one)
    output_ne_top := schedule.sourceOutputConstant_ne_top hdelta sourceFamily
    output_window := ?_
    regularization_absorb := ?_ }
  · exact le_max_left _ _
  · exact le_max_right _ _

end Proposition63M9RobustTailScheduleData

/-- Freeze the mild-rescaling scalar schedule before the source family and
all dependent target data are known. -/
theorem proposition63_m9_robust_tail_schedule
    (sourceLoss : ℝ) (hsourceLoss : 0 < sourceLoss)
    (Lplane Lslope : NNReal) :
    Nonempty (Proposition63M9RobustTailScheduleData
      sourceLoss Lplane Lslope) := by
  let scale : ℝ := max 1 (max (Lplane : ℝ) (Lslope : ℝ))
  have hscale : 1 ≤ scale := le_max_left _ _
  have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
  let levelCount : ℕ := Nat.ceil (1 / sourceLoss) + 1
  have hlevelCountPos : 0 < levelCount := by positivity
  have hlevelCountLoss : 1 ≤ (levelCount : ℝ) * sourceLoss := by
    have hceil : (1 / sourceLoss : ℝ) ≤ Nat.ceil (1 / sourceLoss) :=
      Nat.le_ceil _
    have hcast : (Nat.ceil (1 / sourceLoss) : ℝ) ≤ levelCount := by
      dsimp only [levelCount]
      norm_num
    have hone : 1 ≤ (Nat.ceil (1 / sourceLoss) : ℝ) * sourceLoss := by
      calc
        1 = (1 / sourceLoss) * sourceLoss := by
          field_simp [hsourceLoss.ne']
        _ ≤ (Nat.ceil (1 / sourceLoss) : ℝ) * sourceLoss := by gcongr
    exact hone.trans (mul_le_mul_of_nonneg_right hcast hsourceLoss.le)
  rcases exists_delta_realRpowENN_bound
      (3 : ENNReal) (by norm_num) hsourceLoss with
    ⟨ambientCutoff, ambientCutoffPos, ambientCutoffOne, ambientBound⟩
  let scaleCutoff : ℝ := 1 / (1000 * scale)
  have scaleCutoffPos : 0 < scaleCutoff := by positivity
  let delta₀ := min ambientCutoff scaleCutoff
  refine ⟨{
    scale := scale
    scale_eq := rfl
    scale_one := hscale
    plane_scale := le_max_of_le_right (le_max_left _ _)
    slope_scale := le_max_of_le_right (le_max_right _ _)
    levelCount := levelCount
    levelCount_pos := hlevelCountPos
    levelCount_loss := hlevelCountLoss
    delta₀ := delta₀
    delta₀_pos := lt_min ambientCutoffPos scaleCutoffPos
    delta₀_le_one := (min_le_left _ _).trans ambientCutoffOne
    scale_delta_small := ?_
    ambient_two := ?_ }⟩
  · intro delta hdelta hdeltaCutoff
    have hle : delta ≤ 1 / (1000 * scale) :=
      hdeltaCutoff.trans (min_le_right _ _)
    calc
      scale * delta ≤ scale * (1 / (1000 * scale)) := by gcongr
      _ = 1 / 1000 := by field_simp [hscalePos.ne']
  · intro delta hdelta hdeltaCutoff
    have hthree : (3 : ENNReal) ≤
        Kakeya.realRpowENN delta (-sourceLoss) :=
      ambientBound delta hdelta
        (hdeltaCutoff.trans (min_le_left _ _))
    exact (by norm_num : (2 : ENNReal) < 3).trans_le hthree

/-- Build the canonical finite nearby-scale schedule from the CWA carried by
the exact mild-rescaling source output.  Unlike the former arbitrary-schedule
interface, its output window is the explicit power
`sourceDelta ^ (-windowLoss)`.  Thus all later quotient constants see a
window whose size was fixed by an exponent, rather than an unconstrained
runtime parameter. -/
theorem Proposition63M9MildRescalingSourceData.canonicalNearbySchedule
    {sourceDelta sigma sourceLoss scale windowLoss : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    (sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant)
    (hambientTwo : (2 : ENNReal) < sourceOutputConstant)
    (hlevels : ENNReal.ofReal (1 / sourceDelta) ≤
      sourceOutputConstant ^ levelCount)
    (hwindow : sourceOutputConstant * sourceOutputConstant ≤
      Kakeya.realRpowENN sourceDelta (-windowLoss)) :
    Nonempty (WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) sourceOutputConstant
      (Kakeya.realRpowENN sourceDelta (-windowLoss)) levelCount) := by
  exact paper_pure_finite_nearby_schedule levelCount
    sourceExtremal.delta_pos sourceExtremal.delta_le_one
    hambientTwo sourceData.pure_cwa_nearby.2.1.2
    hlevels hwindow sourceData.pure_cwa_nearby

/-- Canonical specialization for the explicit source constant chosen by this
file.  All geometric inputs and the finite family are kept definitionally
fixed; the only remaining scalar receipt is the family-free power majorant
for the square of the explicit source constant. -/
theorem Proposition63M9RobustTailScheduleData.canonicalSourceNearbySchedule
    {sourceDelta sigma sourceLoss windowLoss : ℝ}
    {Lplane Lslope : NNReal}
    (schedule : Proposition63M9RobustTailScheduleData
      sourceLoss Lplane Lslope)
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    (hdelta : 0 < sourceDelta)
    (hdeltaCutoff : sourceDelta ≤ schedule.delta₀)
    (sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain
      schedule.scale_one
      (schedule.scale_delta_small hdelta hdeltaCutoff) schedule.levelCount
      (schedule.sourceOutputConstant sourceFamily))
    (hwindow : schedule.sourceOutputConstant sourceFamily *
        schedule.sourceOutputConstant sourceFamily ≤
      Kakeya.realRpowENN sourceDelta (-windowLoss)) :
    Nonempty (WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family)
      (schedule.sourceOutputConstant sourceFamily)
      (Kakeya.realRpowENN sourceDelta (-windowLoss))
      schedule.levelCount) := by
  have certificates := schedule.sourceCertificates hdelta hdeltaCutoff
    sourceFamily
  have ambientOne : (1 : ENNReal) ≤
      Kakeya.realRpowENN sourceDelta (-sourceLoss) :=
    (by norm_num : (1 : ENNReal) < 2).le.trans certificates.ambient_two.le
  have ambientLeOutput :
      Kakeya.realRpowENN sourceDelta (-sourceLoss) ≤
        schedule.sourceOutputConstant sourceFamily := by
    calc
      Kakeya.realRpowENN sourceDelta (-sourceLoss) ≤
          Kakeya.realRpowENN sourceDelta (-sourceLoss) *
            Kakeya.realRpowENN sourceDelta (-sourceLoss) :=
        le_mul_of_one_le_right' ambientOne
      _ ≤ schedule.sourceOutputConstant sourceFamily :=
        certificates.output_window
  exact sourceData.canonicalNearbySchedule
    (certificates.ambient_two.trans_le ambientLeOutput)
    (certificates.levels.trans <| pow_le_pow_left' ambientLeOutput _) hwindow

/-- A power majorant for the explicit source constant canonically fixes the
nearby output window at twice the exponent. -/
theorem Proposition63M9RobustTailScheduleData.canonicalSourceNearbyScheduleOfPowerBound
    {sourceDelta sigma sourceLoss outputExponent : ℝ}
    {Lplane Lslope : NNReal}
    (schedule : Proposition63M9RobustTailScheduleData
      sourceLoss Lplane Lslope)
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    (hdelta : 0 < sourceDelta)
    (hdeltaCutoff : sourceDelta ≤ schedule.delta₀)
    (sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain
      schedule.scale_one
      (schedule.scale_delta_small hdelta hdeltaCutoff) schedule.levelCount
      (schedule.sourceOutputConstant sourceFamily))
    (houtput : schedule.sourceOutputConstant sourceFamily ≤
      Kakeya.realRpowENN sourceDelta (-outputExponent)) :
    Nonempty (WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family)
      (schedule.sourceOutputConstant sourceFamily)
      (Kakeya.realRpowENN sourceDelta (-(2 * outputExponent)))
      schedule.levelCount) := by
  apply schedule.canonicalSourceNearbySchedule hdelta hdeltaCutoff sourceData
  calc
    schedule.sourceOutputConstant sourceFamily *
          schedule.sourceOutputConstant sourceFamily ≤
        Kakeya.realRpowENN sourceDelta (-outputExponent) *
          Kakeya.realRpowENN sourceDelta (-outputExponent) := by gcongr
    _ = Kakeya.realRpowENN sourceDelta (-(2 * outputExponent)) := by
      calc
        Kakeya.realRpowENN sourceDelta (-outputExponent) *
              Kakeya.realRpowENN sourceDelta (-outputExponent) =
            Kakeya.realRpowENN sourceDelta
              ((-outputExponent) + (-outputExponent)) :=
          (Kakeya.Assouad.realRpowENN_add hdelta
            (-outputExponent) (-outputExponent)).symm
        _ = Kakeya.realRpowENN sourceDelta (-(2 * outputExponent)) := by
          congr 1
          ring

/-- Once the canonical source window is a fixed negative power, the affine
quotient enlargement costs only one further arbitrarily small exponent. -/
theorem exists_proposition63_m9_quotient_window_cutoff
    (windowLoss gap : ℝ) (hwindowLoss : 0 < windowLoss)
    (hgap : 0 < gap) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
            (Kakeya.realRpowENN delta (-windowLoss)) ≤
          Kakeya.realRpowENN delta (-(windowLoss + gap)) := by
  rcases exists_delta_realRpowENN_bound (5200004 : ENNReal) (by norm_num)
      hgap with ⟨delta₀, delta₀Pos, delta₀One, fixedBound⟩
  refine ⟨delta₀, delta₀Pos, delta₀One, ?_⟩
  intro delta deltaPos deltaLe
  have deltaOne : delta ≤ 1 := deltaLe.trans delta₀One
  have windowOne : (1 : ENNReal) ≤
      Kakeya.realRpowENN delta (-windowLoss) := by
    have realBound : Real.rpow delta 0 ≤
        Real.rpow delta (-windowLoss) :=
      Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne (by linarith)
    simpa [Kakeya.realRpowENN] using ENNReal.ofReal_mono realBound
  have affineBound :
      Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
          (Kakeya.realRpowENN delta (-windowLoss)) ≤
        (5200004 : ENNReal) *
          Kakeya.realRpowENN delta (-windowLoss) := by
    unfold Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
    calc
      (5200000 : ENNReal) * Kakeya.realRpowENN delta (-windowLoss) + 4 ≤
          5200000 * Kakeya.realRpowENN delta (-windowLoss) +
            4 * Kakeya.realRpowENN delta (-windowLoss) := by
        apply add_le_add_right
        calc
          (4 : ENNReal) = 4 * 1 := by rw [mul_one]
          _ ≤ 4 * Kakeya.realRpowENN delta (-windowLoss) :=
            mul_le_mul_right windowOne 4
      _ = (5200004 : ENNReal) *
          Kakeya.realRpowENN delta (-windowLoss) := by
        rw [show (5200004 : ENNReal) = 5200000 + 4 by norm_num, add_mul]
  calc
    Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
          (Kakeya.realRpowENN delta (-windowLoss)) ≤
        (5200004 : ENNReal) *
          Kakeya.realRpowENN delta (-windowLoss) := affineBound
    _ ≤ Kakeya.realRpowENN delta (-gap) *
          Kakeya.realRpowENN delta (-windowLoss) := by
      gcongr
      exact fixedBound delta deltaPos deltaLe
    _ = Kakeya.realRpowENN delta (-(windowLoss + gap)) := by
      calc
        Kakeya.realRpowENN delta (-gap) *
              Kakeya.realRpowENN delta (-windowLoss) =
            Kakeya.realRpowENN delta ((-gap) + (-windowLoss)) :=
          (Kakeya.Assouad.realRpowENN_add deltaPos (-gap) (-windowLoss)).symm
        _ = Kakeya.realRpowENN delta (-(windowLoss + gap)) := by
          congr 1
          ring

/-- Passing from the root scale to the larger mild-rescaled scale can only
decrease the canonical logarithmic envelope. -/
theorem proposition63OneScaleLogEnvelope_scale_mul_le
    {delta scale : ℝ} (hdelta : 0 < delta) (hscale : 1 ≤ scale)
    (hscaleDelta : scale * delta ≤ 1) :
    proposition63OneScaleLogEnvelope (scale * delta) ≤
      proposition63OneScaleLogEnvelope delta := by
  unfold proposition63OneScaleLogEnvelope
  apply ENNReal.ofReal_mono
  apply mul_le_mul_of_nonneg_left _
    proposition63OneScaleLogCoefficient_nonneg
  have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
  have htargetPos : 0 < scale * delta := mul_pos hscalePos hdelta
  have hinv : (scale * delta)⁻¹ ≤ delta⁻¹ := by
    exact inv_anti₀ hdelta (le_mul_of_one_le_left hdelta.le hscale)
  have hlog : Real.log (scale * delta)⁻¹ ≤ Real.log delta⁻¹ := by
    exact Real.log_le_log (inv_pos.mpr htargetPos) hinv
  linarith

/-- The affine-distortion receipt has a cutoff depending only on the frozen
scale and the strict loss gap. -/
theorem exists_proposition63_m9_ad_cutoff
    (scale sourceLoss outputLoss : ℝ) (hscale : 1 ≤ scale)
    (hloss : sourceLoss < outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        Real.rpow delta (outputLoss - sourceLoss) ≤
          Real.rpow scale (-outputLoss) := by
  have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
  have hcoefficient : 0 ≤ Real.rpow scale outputLoss :=
    Real.rpow_nonneg hscalePos.le _
  rcases Kakeya.Assouad.exists_delta_mul_rpow_le_rpow
      (Real.rpow scale outputLoss) hcoefficient
      (alpha := outputLoss - sourceLoss) (beta := 0) (by linarith) with
    ⟨delta₀, delta₀Pos, delta₀One, absorb⟩
  refine ⟨delta₀, delta₀Pos, delta₀One, ?_⟩
  intro delta deltaPos deltaLe
  have hbound := absorb delta deltaPos deltaLe
  have hboundOne : Real.rpow scale outputLoss *
      Real.rpow delta (outputLoss - sourceLoss) ≤ 1 := by
    simpa using hbound
  have hneg : Real.rpow scale (-outputLoss) =
      (Real.rpow scale outputLoss)⁻¹ :=
    Real.rpow_neg hscalePos.le outputLoss
  rw [hneg]
  calc
    Real.rpow delta (outputLoss - sourceLoss) =
        (Real.rpow scale outputLoss)⁻¹ *
          (Real.rpow scale outputLoss *
            Real.rpow delta (outputLoss - sourceLoss)) := by
      field_simp [(Real.rpow_pos_of_pos hscalePos outputLoss).ne']
    _ ≤ (Real.rpow scale outputLoss)⁻¹ * 1 := by gcongr
    _ = (Real.rpow scale outputLoss)⁻¹ := mul_one _

/-- The volume-Jacobian receipt likewise has a cutoff independent of every
runtime family and target witness. -/
theorem exists_proposition63_m9_volume_cutoff
    (scale sigma sourceLoss outputLoss : ℝ) (hscale : 1 ≤ scale)
    (hloss : sourceLoss < outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ENNReal.ofReal (scale ^ 3) *
            Kakeya.realRpowENN delta (sigma - sourceLoss) ≤
          Kakeya.realRpowENN (scale * delta) (sigma - outputLoss) := by
  have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
  let coefficient : ℝ := scale ^ 3 * Real.rpow scale (outputLoss - sigma)
  have coefficientNonneg : 0 ≤ coefficient := by
    dsimp only [coefficient]
    exact mul_nonneg (pow_nonneg hscalePos.le _)
      (Real.rpow_nonneg hscalePos.le _)
  rcases Kakeya.Assouad.exists_delta_mul_rpow_le_rpow coefficient
      coefficientNonneg (alpha := sigma - sourceLoss)
      (beta := sigma - outputLoss) (by linarith) with
    ⟨delta₀, delta₀Pos, delta₀One, absorb⟩
  refine ⟨delta₀, delta₀Pos, delta₀One, ?_⟩
  intro delta deltaPos deltaLe
  have hbound := absorb delta deltaPos deltaLe
  have hscaleFactorPos : 0 < Real.rpow scale (sigma - outputLoss) :=
    Real.rpow_pos_of_pos hscalePos _
  have hscaleCancel : Real.rpow scale (sigma - outputLoss) *
      Real.rpow scale (outputLoss - sigma) = 1 := by
    calc
      Real.rpow scale (sigma - outputLoss) *
            Real.rpow scale (outputLoss - sigma) =
          Real.rpow scale
            ((sigma - outputLoss) + (outputLoss - sigma)) :=
        (Real.rpow_add hscalePos _ _).symm
      _ = Real.rpow scale 0 := by congr 1 <;> ring
      _ = 1 := Real.rpow_zero scale
  have hreal : scale ^ 3 * Real.rpow delta (sigma - sourceLoss) ≤
      Real.rpow (scale * delta) (sigma - outputLoss) := by
    calc
      scale ^ 3 * Real.rpow delta (sigma - sourceLoss) =
          Real.rpow scale (sigma - outputLoss) *
            (coefficient * Real.rpow delta (sigma - sourceLoss)) := by
        dsimp only [coefficient]
        calc
          scale ^ 3 * Real.rpow delta (sigma - sourceLoss) =
              1 * (scale ^ 3 * Real.rpow delta (sigma - sourceLoss)) := by ring
          _ = _ := by rw [← hscaleCancel]; ring
      _ ≤ Real.rpow scale (sigma - outputLoss) *
          Real.rpow delta (sigma - outputLoss) := by gcongr
      _ = Real.rpow (scale * delta) (sigma - outputLoss) :=
        (Real.mul_rpow hscalePos.le deltaPos.le).symm
  change ENNReal.ofReal (scale ^ 3) *
      ENNReal.ofReal (Real.rpow delta (sigma - sourceLoss)) ≤
    ENNReal.ofReal (Real.rpow (scale * delta) (sigma - outputLoss))
  rw [← ENNReal.ofReal_mul (pow_nonneg hscalePos.le 3)]
  exact ENNReal.ofReal_mono hreal

/-- Fixed coefficient in the family-free selection-loss envelope. -/
def proposition63M9SelectionCoefficient (scale : ℝ) (levelCount : ℕ) : ENNReal :=
  ((((2 * Nat.ceil (11200 * scale) + 1) ^ 5 + 1 : ℕ) : ENNReal) *
      (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
        (levelCount + 1)) * 8

theorem proposition63M9SelectionCoefficient_ne_top
    (scale : ℝ) (levelCount : ℕ) :
    proposition63M9SelectionCoefficient scale levelCount ≠ ⊤ := by
  unfold proposition63M9SelectionCoefficient
  finiteness

/-- Replace the runtime schedule length in the actual selection loss by its
frozen pre-runtime upper bound. -/
theorem Proposition63M9MildRescalingQuotientTargetData.selectionLoss_le_rootEnvelope
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    (sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant)
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant levelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    data.selectionLoss ≤
      proposition63M9SelectionCoefficient scale levelCount *
        proposition63OneScaleLogEnvelope sourceDelta ^ (2 * levelCount + 3) := by
  have targetDeltaPos : 0 < scale * sourceDelta :=
    mul_pos (zero_lt_one.trans_le hscale) sourceExtremal.delta_pos
  have targetDeltaOne : scale * sourceDelta ≤ 1 :=
    hscaleDeltaSmall.trans (by norm_num)
  have logOne : (1 : ENNReal) ≤
      proposition63OneScaleLogEnvelope sourceDelta := by
    unfold proposition63OneScaleLogEnvelope
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num]
    apply ENNReal.ofReal_mono
    have hlog : 0 ≤ Real.log sourceDelta⁻¹ :=
      Real.log_nonneg ((one_le_inv₀ sourceExtremal.delta_pos).mpr
        sourceExtremal.delta_le_one)
    have hcoefficient : 1 ≤ proposition63OneScaleLogCoefficient :=
      (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
    nlinarith [proposition63OneScaleLogCoefficient_nonneg]
  have targetLogLe := proposition63OneScaleLogEnvelope_scale_mul_le
    sourceExtremal.delta_pos hscale targetDeltaOne
  have degreeOne : (1 : ENNReal) ≤
      proposition63MildRescalingQuotientConflictDegree := by
    unfold proposition63MildRescalingQuotientConflictDegree
    norm_num
  have raw := data.selectionLoss_le_logEnvelope
  have hdegreePow :
      (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
          sourceSchedule.scaleCount ≤
        (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
          (levelCount + 1) :=
    pow_le_pow_right' degreeOne sourceSchedule.scaleCount_le
  have hlogPow :
      proposition63OneScaleLogEnvelope (scale * sourceDelta) ^
          (sourceSchedule.scaleCount + sourceSchedule.scaleCount + 1) ≤
        proposition63OneScaleLogEnvelope sourceDelta ^
          (2 * levelCount + 3) := by
    have hcount : sourceSchedule.scaleCount ≤ levelCount + 1 :=
      sourceSchedule.scaleCount_le
    exact pow_le_pow targetLogLe logOne (by omega)
  calc
    data.selectionLoss ≤ _ := raw
    _ ≤ proposition63M9SelectionCoefficient scale levelCount *
        proposition63OneScaleLogEnvelope sourceDelta ^ (2 * levelCount + 3) := by
      unfold proposition63M9SelectionCoefficient
      gcongr

/-- The actual selection loss is absorbed into the actual source-density
normalization by a cutoff chosen before the family and dependent target. -/
theorem exists_proposition63_m9_density_cutoff
    (scale sourceLoss outputLoss : ℝ) (levelCount : ℕ)
    (hscale : 1 ≤ scale) (hloss : sourceLoss < outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sourceDelta sigma : ℝ}, 0 < sourceDelta → sourceDelta ≤ delta₀ →
        ∀ {Lplane Lslope : NNReal}
          {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
          {sourceShading : WZ1PaperTubeShading sourceFamily}
          {sourceExtremal : WZ2PaperCroppedIsExtremal
            sigma sourceLoss sourceFamily sourceShading}
          {sourceLine : WZ1PaperIsLineClass sourceFamily}
          {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
          {sourceMidpoint : ∀ index,
            ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
          {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
            Lplane Lslope 1}
          {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
          {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
          (sourceData : Proposition63M9MildRescalingSourceData sourceShading
            sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain
            hscale hscaleDeltaSmall levelCount sourceOutputConstant)
          {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
            (fine := sourceData.selected.family) scheduleConstant
            scheduleWindowConstant levelCount}
          (targetData : Proposition63M9MildRescalingQuotientTargetData
            sourceData sourceSchedule),
          targetData.selectionLoss *
              Kakeya.realRpowENN (scale * sourceDelta) outputLoss ≤
            ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
              ENNReal.ofReal scale) *
              ((1 / 2 : ENNReal) * sourceData.sourceDensity) := by
  let densityCoefficient : ENNReal :=
    ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
      ENNReal.ofReal scale) *
      ((1 / 2 : ENNReal) *
        ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3))
  have densityCoefficientZero : densityCoefficient ≠ 0 := by
    dsimp only [densityCoefficient]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact ENNReal.inv_ne_zero.mpr <|
          ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top
      · exact (ENNReal.ofReal_pos.mpr (zero_lt_one.trans_le hscale)).ne'
    · apply mul_ne_zero (by norm_num)
      exact (ENNReal.ofReal_pos.mpr (by
        have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
        positivity)).ne'
  have densityCoefficientTop : densityCoefficient ≠ ⊤ := by
    dsimp only [densityCoefficient]
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top
        (ENNReal.inv_ne_top.mpr (by
          exact mul_ne_zero (by norm_num)
            (zero_lt_one.trans_le one_le_deltaTubeVolume_one).ne'))
        ENNReal.ofReal_ne_top
    · exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  let coefficient := densityCoefficient⁻¹ *
    (proposition63M9SelectionCoefficient scale levelCount *
      ENNReal.ofReal (Real.rpow scale outputLoss))
  have coefficientTop : coefficient ≠ ⊤ := by
    dsimp only [coefficient]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr densityCoefficientZero)
      (ENNReal.mul_ne_top
        (proposition63M9SelectionCoefficient_ne_top scale levelCount)
        ENNReal.ofReal_ne_top)
  have gapPos : 0 < outputLoss - sourceLoss := sub_pos.mpr hloss
  have exponentPos : 0 < 2 * levelCount + 3 := by omega
  rcases Kakeya.Assouad.exists_delta_C_pow_log_absorbed_ennreal
      coefficient coefficientTop proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg gapPos exponentPos with
    ⟨delta₀, delta₀Pos, delta₀One, absorb⟩
  refine ⟨delta₀, delta₀Pos, delta₀One, ?_⟩
  intro sourceDelta sigma deltaPos deltaLe Lplane Lslope sourceFamily
    sourceShading sourceExtremal sourceLine sourceDistinct sourceMidpoint
    preGrain hscaleDeltaSmall sourceOutputConstant scheduleConstant
    scheduleWindowConstant sourceData sourceSchedule targetData
  have selectionBound := targetData.selectionLoss_le_rootEnvelope sourceData
  have logAbsorb := absorb sourceDelta deltaPos deltaLe
  have scalePower : Kakeya.realRpowENN (scale * sourceDelta) outputLoss =
      ENNReal.ofReal (Real.rpow scale outputLoss) *
        Kakeya.realRpowENN sourceDelta outputLoss := by
    unfold Kakeya.realRpowENN
    calc
      ENNReal.ofReal (Real.rpow (scale * sourceDelta) outputLoss) =
          ENNReal.ofReal (Real.rpow scale outputLoss *
            Real.rpow sourceDelta outputLoss) := by
        congr 1
        exact Real.mul_rpow (zero_lt_one.trans_le hscale).le deltaPos.le
      _ = _ := ENNReal.ofReal_mul (Real.rpow_nonneg
        (zero_lt_one.trans_le hscale).le outputLoss)
  have coefficientIdentity :
      densityCoefficient *
          (coefficient * proposition63OneScaleLogEnvelope sourceDelta ^
            (2 * levelCount + 3)) =
        proposition63M9SelectionCoefficient scale levelCount *
          proposition63OneScaleLogEnvelope sourceDelta ^
            (2 * levelCount + 3) *
          ENNReal.ofReal (Real.rpow scale outputLoss) := by
    dsimp only [coefficient]
    calc
      _ = (densityCoefficient * densityCoefficient⁻¹) *
          ((proposition63M9SelectionCoefficient scale levelCount *
            ENNReal.ofReal (Real.rpow scale outputLoss)) *
            proposition63OneScaleLogEnvelope sourceDelta ^
              (2 * levelCount + 3)) := by ac_rfl
      _ = _ := by
        rw [ENNReal.mul_inv_cancel densityCoefficientZero
          densityCoefficientTop, one_mul]
        ac_rfl
  have coefficientBound :
      proposition63M9SelectionCoefficient scale levelCount *
          proposition63OneScaleLogEnvelope sourceDelta ^ (2 * levelCount + 3) *
          ENNReal.ofReal (Real.rpow scale outputLoss) ≤
        densityCoefficient *
          Kakeya.realRpowENN sourceDelta (-(outputLoss - sourceLoss)) := by
    calc
      _ = densityCoefficient * (coefficient *
          proposition63OneScaleLogEnvelope sourceDelta ^
            (2 * levelCount + 3)) := by
        exact coefficientIdentity.symm
      _ ≤ densityCoefficient *
          Kakeya.realRpowENN sourceDelta (-(outputLoss - sourceLoss)) := by
        exact mul_le_mul_left' logAbsorb densityCoefficient
  rw [sourceData.sourceDensity_eq, scalePower]
  have firstBound := mul_le_mul_right' selectionBound
    (ENNReal.ofReal (Real.rpow scale outputLoss) *
      Kakeya.realRpowENN sourceDelta outputLoss)
  calc
    targetData.selectionLoss *
          (ENNReal.ofReal (Real.rpow scale outputLoss) *
            Kakeya.realRpowENN sourceDelta outputLoss) ≤
        (proposition63M9SelectionCoefficient scale levelCount *
          proposition63OneScaleLogEnvelope sourceDelta ^ (2 * levelCount + 3) *
          ENNReal.ofReal (Real.rpow scale outputLoss)) *
            Kakeya.realRpowENN sourceDelta outputLoss := by
      convert firstBound using 1 <;> ac_rfl
    _ ≤ (densityCoefficient *
          Kakeya.realRpowENN sourceDelta (-(outputLoss - sourceLoss))) *
            Kakeya.realRpowENN sourceDelta outputLoss := by gcongr
    _ = densityCoefficient *
          Kakeya.realRpowENN sourceDelta sourceLoss := by
      rw [show densityCoefficient *
          Kakeya.realRpowENN sourceDelta (-(outputLoss - sourceLoss)) *
            Kakeya.realRpowENN sourceDelta outputLoss =
          densityCoefficient *
            (Kakeya.realRpowENN sourceDelta (-(outputLoss - sourceLoss)) *
              Kakeya.realRpowENN sourceDelta outputLoss) by ac_rfl]
      rw [← Kakeya.Assouad.realRpowENN_add deltaPos]
      congr 1
      ring
    _ = _ := by
      dsimp only [densityCoefficient]
      ring

/-- Any completed quotient-tail certificate necessarily absorbs the source
schedule's window constant at the final target scale.  This is the exact
quantifier-order obstruction to a cutoff chosen before an otherwise
unrestricted `sourceSchedule`: its finite window constant may be arbitrarily
large. -/
theorem Proposition63M9RobustQuotientTailCertificates.windowNecessary
    {sourceDelta sigma sourceLoss outputLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    {targetData : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule}
    (certificates : Proposition63M9RobustQuotientTailCertificates
      (outputLoss := outputLoss) targetData) :
    (4 : ENNReal) *
        Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
          scheduleWindowConstant ≤
      Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss) := by
  calc
    (4 : ENNReal) *
          Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
            scheduleWindowConstant ≤
        4 * certificates.targetConstant := by
      exact mul_le_mul_right certificates.scale_budget 4
    _ ≤ Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss) :=
      certificates.final_cwa_absorb

/-- Every completed quotient certificate also absorbs each actual packet's
John-coordinate-change constant.  This exposes the second family-dependent
quantity which a genuine pre-runtime producer must uniformly majorize. -/
theorem Proposition63M9RobustQuotientTailCertificates.packetNecessary
    {sourceDelta sigma sourceLoss outputLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    {targetData : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule}
    (certificates : Proposition63M9RobustQuotientTailCertificates
      (outputLoss := outputLoss) targetData)
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (targetData.quotientSchedule.jointRegularizedParents
        targetData.jointRegularized coordinate).family.card)
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card) :
    (4 : ENNReal) *
        targetData.quotientSchedule.quotientCanonicalPacketConstant
          targetData.jointRegularized
          (((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
            ENNReal.ofReal scale) *
            ((1 / 2 : ENNReal) * sourceData.sourceDensity))
          (targetData.selectionLoss *
            (55296 * Kakeya.deltaTubeVolume 1))
          coordinate targetParent sourceParent ≤
      Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss) := by
  have packetLeBody :=
    targetData.quotientSchedule.quotientCanonicalPacketConstant_le_schedule
      targetData.jointRegularized
      (((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
        ENNReal.ofReal scale) *
        ((1 / 2 : ENNReal) * sourceData.sourceDensity))
      (targetData.selectionLoss *
        (55296 * Kakeya.deltaTubeVolume 1))
      coordinate targetParent sourceParent
  have bodyLeTarget :
      targetData.quotientSchedule.quotientScheduleBodyConstant
          targetData.jointRegularized
          (((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
            ENNReal.ofReal scale) *
            ((1 / 2 : ENNReal) * sourceData.sourceDensity))
          (targetData.selectionLoss *
            (55296 * Kakeya.deltaTubeVolume 1)) ≤
        certificates.targetConstant :=
    (le_max_right _ _).trans (certificates.constant_budget coordinate)
  calc
    (4 : ENNReal) *
          targetData.quotientSchedule.quotientCanonicalPacketConstant
            targetData.jointRegularized
            (((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
              ENNReal.ofReal scale) *
              ((1 / 2 : ENNReal) * sourceData.sourceDensity))
            (targetData.selectionLoss *
              (55296 * Kakeya.deltaTubeVolume 1))
            coordinate targetParent sourceParent ≤
        4 * certificates.targetConstant := by
      gcongr
      exact packetLeBody.trans bodyLeTarget
    _ ≤ Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss) :=
      certificates.final_cwa_absorb

/-- Runtime target constant attached to one actual dependent target. -/
def Proposition63M9MildRescalingQuotientTargetData.robustTargetConstant
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) : ENNReal :=
  max
    (Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
      scheduleWindowConstant)
    (max
      (data.quotientSchedule.quotientFiberRegularizationConstant data.selection)
      (data.quotientSchedule.quotientScheduleBodyConstant data.jointRegularized
        (((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
          ENNReal.ofReal scale) *
          ((1 / 2 : ENNReal) * sourceData.sourceDensity))
        (data.selectionLoss * (55296 * Kakeya.deltaTubeVolume 1))))

/-- Fixed coefficient dominating every non-logarithmic factor in the actual
quotient target constant. -/
def proposition63M9TargetEnvelopeCoefficient
    (scale : ℝ) (levelCount : ℕ) : ENNReal :=
  let joint : ENNReal := 16 * (2 * (levelCount + 1) : ℕ)
  let body : ENNReal :=
    ENNReal.ofReal (27 * (2 * (22 * scale + 3) - 1) ^ 3) *
      (108 * ENNReal.ofReal Real.pi * 5200004 ^ 2 *
        (1 + 2 * ENNReal.ofReal scale)) *
      (((((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
          ENNReal.ofReal scale) *
        ((1 / 2 : ENNReal) *
          ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3)))⁻¹) *
        (proposition63M9SelectionCoefficient scale levelCount *
          (55296 * Kakeya.deltaTubeVolume 1) * joint))
  max 1 (max joint body)

theorem proposition63M9TargetEnvelopeCoefficient_ne_top
    (scale : ℝ) (levelCount : ℕ) (hscale : 1 ≤ scale) :
    proposition63M9TargetEnvelopeCoefficient scale levelCount ≠ ⊤ := by
  have fixedZero :
      ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
        ENNReal.ofReal scale) *
          ((1 / 2 : ENNReal) *
            ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3)) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact ENNReal.inv_ne_zero.mpr <|
          ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top
      · exact (ENNReal.ofReal_pos.mpr (zero_lt_one.trans_le hscale)).ne'
    · apply mul_ne_zero (by norm_num)
      exact (ENNReal.ofReal_pos.mpr (by
        have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
        positivity)).ne'
  unfold proposition63M9TargetEnvelopeCoefficient
  apply max_ne_top (by norm_num)
  apply max_ne_top
  · finiteness
  · have houter :
        ENNReal.ofReal (27 * (2 * (22 * scale + 3) - 1) ^ 3) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have hpi : ENNReal.ofReal Real.pi ≠ ⊤ := ENNReal.ofReal_ne_top
    have hscaleTop : ENNReal.ofReal scale ≠ ⊤ := ENNReal.ofReal_ne_top
    have hwindow :
        108 * ENNReal.ofReal Real.pi * 5200004 ^ 2 *
          (1 + 2 * ENNReal.ofReal scale) ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.mul_ne_top (by norm_num) hpi
        · exact ENNReal.pow_ne_top (by norm_num)
      · exact ENNReal.add_ne_top.mpr
          ⟨by norm_num, ENNReal.mul_ne_top (by norm_num) hscaleTop⟩
    have hjoint : (16 * (2 * (levelCount + 1) : ℕ) : ENNReal) ≠ ⊤ := by
      finiteness
    apply ENNReal.mul_ne_top (ENNReal.mul_ne_top houter hwindow)
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr fixedZero) <|
      ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (proposition63M9SelectionCoefficient_ne_top scale levelCount) <|
            ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top) hjoint

/-- Uniform target envelope after the source constant and quotient window
have been replaced by their pre-runtime negative-power bounds. -/
def proposition63M9TargetEnvelope
    (scale sourceLoss : ℝ) (levelCount : ℕ) (delta : ℝ) : ENNReal :=
  let logEnvelope := proposition63OneScaleLogEnvelope delta
  let joint : ENNReal := 16 * (2 * (levelCount + 1) : ℕ)
  max (Kakeya.realRpowENN delta (-(9 * sourceLoss)))
    (max
      (joint * logEnvelope ^ (2 * levelCount + 2))
      (proposition63M9TargetEnvelopeCoefficient scale levelCount *
        logEnvelope ^ (4 * levelCount + 5) *
        Kakeya.realRpowENN delta (-(18 * sourceLoss))))

theorem proposition63M9TargetEnvelope_le_body
    {scale sourceLoss delta : ℝ} {levelCount : ℕ}
    (sourceLossPos : 0 < sourceLoss) (deltaPos : 0 < delta)
    (deltaOne : delta ≤ 1) :
    proposition63M9TargetEnvelope scale sourceLoss levelCount delta ≤
      proposition63M9TargetEnvelopeCoefficient scale levelCount *
        proposition63OneScaleLogEnvelope delta ^ (4 * levelCount + 5) *
        Kakeya.realRpowENN delta (-(18 * sourceLoss)) := by
  let coefficient := proposition63M9TargetEnvelopeCoefficient scale levelCount
  let logEnvelope := proposition63OneScaleLogEnvelope delta
  let joint : ENNReal := 16 * (2 * (levelCount + 1) : ℕ)
  have coefficientOne : (1 : ENNReal) ≤ coefficient := by
    dsimp only [coefficient, proposition63M9TargetEnvelopeCoefficient]
    exact le_max_left _ _
  have jointLe : joint ≤ coefficient := by
    dsimp only [joint, coefficient, proposition63M9TargetEnvelopeCoefficient]
    exact le_max_of_le_right (le_max_left _ _)
  have logOne : (1 : ENNReal) ≤ logEnvelope := by
    dsimp only [logEnvelope, proposition63OneScaleLogEnvelope]
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num]
    apply ENNReal.ofReal_mono
    have hlog : 0 ≤ Real.log delta⁻¹ :=
      Real.log_nonneg ((one_le_inv₀ deltaPos).mpr deltaOne)
    have hcoefficient : 1 ≤ proposition63OneScaleLogCoefficient :=
      (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
    nlinarith [proposition63OneScaleLogCoefficient_nonneg]
  have powerOne : (1 : ENNReal) ≤
      Kakeya.realRpowENN delta (-(18 * sourceLoss)) := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num]
    apply ENNReal.ofReal_mono
    have hone : Real.rpow delta 0 ≤
        Real.rpow delta (-(18 * sourceLoss)) :=
      Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne (by linarith)
    simpa using hone
  have powerNineLe :
      Kakeya.realRpowENN delta (-(9 * sourceLoss)) ≤
        Kakeya.realRpowENN delta (-(18 * sourceLoss)) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne (by linarith)
  have logPowLe : logEnvelope ^ (2 * levelCount + 2) ≤
      logEnvelope ^ (4 * levelCount + 5) :=
    pow_le_pow_right₀ logOne (by omega)
  unfold proposition63M9TargetEnvelope
  dsimp only
  apply max_le
  · calc
      Kakeya.realRpowENN delta (-(9 * sourceLoss)) ≤
          Kakeya.realRpowENN delta (-(18 * sourceLoss)) := powerNineLe
      _ ≤ coefficient * logEnvelope ^ (4 * levelCount + 5) *
          Kakeya.realRpowENN delta (-(18 * sourceLoss)) := by
        apply le_mul_of_one_le_left'
        exact one_le_mul_of_one_le_of_one_le coefficientOne
          (one_le_pow₀ logOne)
  apply max_le
  · calc
      joint * logEnvelope ^ (2 * levelCount + 2) ≤
          coefficient * logEnvelope ^ (4 * levelCount + 5) := by gcongr
      _ ≤ coefficient * logEnvelope ^ (4 * levelCount + 5) *
          Kakeya.realRpowENN delta (-(18 * sourceLoss)) :=
        le_mul_of_one_le_right' powerOne
  · exact le_rfl

theorem proposition63M9TargetEnvelope_ne_top
    (scale sourceLoss delta : ℝ) (levelCount : ℕ) (hscale : 1 ≤ scale) :
    proposition63M9TargetEnvelope scale sourceLoss levelCount delta ≠ ⊤ := by
  unfold proposition63M9TargetEnvelope
  have logTop : proposition63OneScaleLogEnvelope delta ≠ ⊤ := by
    unfold proposition63OneScaleLogEnvelope
    exact ENNReal.ofReal_ne_top
  apply max_ne_top
  · simp [Kakeya.realRpowENN]
  apply max_ne_top
  · exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _))
      (ENNReal.pow_ne_top logTop)
  · exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (proposition63M9TargetEnvelopeCoefficient_ne_top
          scale levelCount hscale) (ENNReal.pow_ne_top logTop))
      (by simp [Kakeya.realRpowENN])

theorem Proposition63M9MildRescalingQuotientTargetData.robustTargetConstant_le_envelope
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    (sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant)
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) sourceOutputConstant
      (Kakeya.realRpowENN sourceDelta (-(8 * sourceLoss))) levelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule)
    (sourceLossPos : 0 < sourceLoss)
    (houtput : sourceOutputConstant ≤
      Kakeya.realRpowENN sourceDelta (-(4 * sourceLoss)))
    (hwindow :
      Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
          (Kakeya.realRpowENN sourceDelta (-(8 * sourceLoss))) ≤
        Kakeya.realRpowENN sourceDelta (-(9 * sourceLoss))) :
    data.robustTargetConstant ≤
      proposition63M9TargetEnvelope scale sourceLoss levelCount sourceDelta := by
  unfold Proposition63M9MildRescalingQuotientTargetData.robustTargetConstant
  unfold proposition63M9TargetEnvelope
  apply max_le
  · exact hwindow.trans (le_max_left _ _)
  apply (max_le_iff.mpr ⟨?_, ?_⟩)
  · apply le_max_of_le_right
    apply le_max_of_le_left
    have raw := data.quotientFiberRegularizationConstant_le_logEnvelope
    have hcount : sourceSchedule.scaleCount ≤ levelCount + 1 :=
      sourceSchedule.scaleCount_le
    have logOne : (1 : ENNReal) ≤
        proposition63OneScaleLogEnvelope (scale * sourceDelta) := by
      unfold proposition63OneScaleLogEnvelope
      rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num]
      apply ENNReal.ofReal_mono
      have hlog : 0 ≤ Real.log (scale * sourceDelta)⁻¹ :=
        Real.log_nonneg ((one_le_inv₀ (mul_pos
          (zero_lt_one.trans_le hscale) sourceExtremal.delta_pos)).mpr
            (hscaleDeltaSmall.trans (by norm_num)))
      have hcoefficient : 1 ≤ proposition63OneScaleLogCoefficient :=
        (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
      nlinarith [proposition63OneScaleLogCoefficient_nonneg]
    calc
      _ ≤ _ := raw
      _ ≤ (16 * (2 * (levelCount + 1) : ℕ) : ENNReal) *
          proposition63OneScaleLogEnvelope sourceDelta ^
            (2 * levelCount + 2) := by
        have logLe := proposition63OneScaleLogEnvelope_scale_mul_le
          sourceExtremal.delta_pos hscale
            (hscaleDeltaSmall.trans (by norm_num))
        have hnat : sourceSchedule.scaleCount + sourceSchedule.scaleCount ≤
            2 * levelCount + 2 := by omega
        have hlogPow := pow_le_pow logLe (logOne.trans logLe) hnat
        have hcountENN :
            ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
                ENNReal) ≤ (2 * (levelCount + 1) : ℕ) := by
          exact_mod_cast hnat
        exact mul_le_mul
          (mul_le_mul_left' hcountENN 16) hlogPow (by positivity) (by positivity)
  · apply le_max_of_le_right
    apply le_max_of_le_right
    have sourceDeltaOne : sourceDelta ≤ 1 := by
      exact (le_mul_of_one_le_left sourceExtremal.delta_pos.le hscale).trans
        (hscaleDeltaSmall.trans (by norm_num))
    have hconstantWindow : sourceOutputConstant ≤
        Kakeya.realRpowENN sourceDelta (-(8 * sourceLoss)) := by
      apply houtput.trans
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge sourceExtremal.delta_pos
        sourceDeltaOne (by linarith)
    have hbody := data.quotientScheduleBodyConstant_le_actualFamilyFreeEnvelope
      hconstantWindow
    have powerOne : (1 : ENNReal) ≤
        Kakeya.realRpowENN sourceDelta (-sourceLoss) := by
      rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num]
      apply ENNReal.ofReal_mono
      have hone : Real.rpow sourceDelta 0 ≤
          Real.rpow sourceDelta (-sourceLoss) :=
        Real.rpow_le_rpow_of_exponent_ge sourceExtremal.delta_pos
          sourceDeltaOne (by linarith)
      simpa using hone
    have logLe := proposition63OneScaleLogEnvelope_scale_mul_le
      sourceExtremal.delta_pos hscale
        (hscaleDeltaSmall.trans (by norm_num))
    have rootLogOne : (1 : ENNReal) ≤
        proposition63OneScaleLogEnvelope sourceDelta := by
      unfold proposition63OneScaleLogEnvelope
      rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num]
      apply ENNReal.ofReal_mono
      have hlog : 0 ≤ Real.log sourceDelta⁻¹ :=
        Real.log_nonneg ((one_le_inv₀ sourceExtremal.delta_pos).mpr
          sourceDeltaOne)
      have hcoefficient : 1 ≤ proposition63OneScaleLogCoefficient :=
        (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
      nlinarith [proposition63OneScaleLogCoefficient_nonneg]
    have hcount : sourceSchedule.scaleCount ≤ levelCount + 1 :=
      sourceSchedule.scaleCount_le
    have targetPowerOne : (1 : ENNReal) ≤
        Kakeya.realRpowENN sourceDelta (-(9 * sourceLoss)) := by
      rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num]
      apply ENNReal.ofReal_mono
      have hone : Real.rpow sourceDelta 0 ≤
          Real.rpow sourceDelta (-(9 * sourceLoss)) :=
        Real.rpow_le_rpow_of_exponent_ge sourceExtremal.delta_pos
          sourceDeltaOne (by linarith)
      simpa using hone
    have scaleOne : (1 : ENNReal) ≤ ENNReal.ofReal scale := by
      rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num]
      exact ENNReal.ofReal_mono hscale
    have windowFactor :
        1 + 2 * (ENNReal.ofReal scale *
              Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
                (Kakeya.realRpowENN sourceDelta (-(8 * sourceLoss)))) ≤
          (1 + 2 * ENNReal.ofReal scale) *
            Kakeya.realRpowENN sourceDelta (-(9 * sourceLoss)) := by
      calc
        _ ≤ 1 + 2 * (ENNReal.ofReal scale *
              Kakeya.realRpowENN sourceDelta (-(9 * sourceLoss))) := by
          simpa [add_comm] using add_le_add_left
            (mul_le_mul_left' (mul_le_mul_left' hwindow
              (ENNReal.ofReal scale)) 2) 1
        _ ≤ Kakeya.realRpowENN sourceDelta (-(9 * sourceLoss)) +
              2 * ENNReal.ofReal scale *
                Kakeya.realRpowENN sourceDelta (-(9 * sourceLoss)) := by
          simpa [mul_assoc] using add_le_add targetPowerOne
            (le_refl (2 * ENNReal.ofReal scale *
              Kakeya.realRpowENN sourceDelta (-(9 * sourceLoss))))
        _ = _ := by ring
    have selectionEnvelope := data.selectionLoss_le_rootEnvelope sourceData
    have jointEnvelope :
        16 * ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
            ENNReal) *
          proposition63OneScaleLogEnvelope (scale * sourceDelta) ^
            (sourceSchedule.scaleCount + sourceSchedule.scaleCount) ≤
        (16 * (2 * (levelCount + 1) : ℕ) : ENNReal) *
          proposition63OneScaleLogEnvelope sourceDelta ^
            (2 * levelCount + 2) := by
      have hnat : sourceSchedule.scaleCount + sourceSchedule.scaleCount ≤
          2 * levelCount + 2 := by omega
      have hcountENN :
          ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
              ENNReal) ≤ (2 * (levelCount + 1) : ℕ) := by exact_mod_cast hnat
      exact mul_le_mul (mul_le_mul_left' hcountENN 16)
        (pow_le_pow logLe rootLogOne hnat) (by positivity) (by positivity)
    have sourceSelectionEnvelope :
        sourceOutputConstant * data.selectionLoss ≤
          Kakeya.realRpowENN sourceDelta (-(4 * sourceLoss)) *
            (proposition63M9SelectionCoefficient scale levelCount *
              proposition63OneScaleLogEnvelope sourceDelta ^
                (2 * levelCount + 3)) :=
      mul_le_mul houtput selectionEnvelope (by positivity) (by positivity)
    let rawSelection : ENNReal :=
      (((((2 * Nat.ceil (11200 * scale) + 1) ^ 5 + 1 : ℕ) : ENNReal) *
          (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
            sourceSchedule.scaleCount) * 8) *
        proposition63OneScaleLogEnvelope (scale * sourceDelta) ^
          (sourceSchedule.scaleCount + sourceSchedule.scaleCount + 1)
    have rawSelectionEnvelope : rawSelection ≤
        proposition63M9SelectionCoefficient scale levelCount *
          proposition63OneScaleLogEnvelope sourceDelta ^
            (2 * levelCount + 3) := by
      have degreeOne : (1 : ENNReal) ≤
          proposition63MildRescalingQuotientConflictDegree := by
        unfold proposition63MildRescalingQuotientConflictDegree
        norm_num
      have hdegreePow :
          (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
              sourceSchedule.scaleCount ≤
            (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
              (levelCount + 1) :=
        pow_le_pow_right' degreeOne sourceSchedule.scaleCount_le
      have hlogPow :
          proposition63OneScaleLogEnvelope (scale * sourceDelta) ^
              (sourceSchedule.scaleCount + sourceSchedule.scaleCount + 1) ≤
            proposition63OneScaleLogEnvelope sourceDelta ^
              (2 * levelCount + 3) := by
        exact pow_le_pow logLe rootLogOne (by omega)
      dsimp only [rawSelection, proposition63M9SelectionCoefficient]
      gcongr
    have sourceRawSelectionEnvelope :
        sourceOutputConstant * rawSelection ≤
          Kakeya.realRpowENN sourceDelta (-(4 * sourceLoss)) *
            (proposition63M9SelectionCoefficient scale levelCount *
              proposition63OneScaleLogEnvelope sourceDelta ^
                (2 * levelCount + 3)) :=
      mul_le_mul houtput rawSelectionEnvelope (by positivity) (by positivity)
    have middleEnvelope :
        sourceOutputConstant * rawSelection *
            (55296 * Kakeya.deltaTubeVolume 1) *
            (16 *
              ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
                ENNReal) *
              proposition63OneScaleLogEnvelope (scale * sourceDelta) ^
                (sourceSchedule.scaleCount + sourceSchedule.scaleCount)) ≤
          Kakeya.realRpowENN sourceDelta (-(4 * sourceLoss)) *
              (proposition63M9SelectionCoefficient scale levelCount *
                proposition63OneScaleLogEnvelope sourceDelta ^
                  (2 * levelCount + 3)) *
              (55296 * Kakeya.deltaTubeVolume 1) *
            ((16 : ENNReal) * (2 * (levelCount + 1) : ℕ) *
              proposition63OneScaleLogEnvelope sourceDelta ^
                (2 * levelCount + 2)) := by
      exact mul_le_mul
        (mul_le_mul sourceRawSelectionEnvelope (le_refl _)
          (by positivity) (by positivity))
        jointEnvelope (by positivity) (by positivity)
    let normalizationFixed : ENNReal :=
      ((((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
          ENNReal.ofReal scale) *
        ((1 / 2 : ENNReal) *
          ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3)))⁻¹)
    have payloadEnvelope :
        (normalizationFixed *
              Kakeya.realRpowENN sourceDelta (-sourceLoss) *
            (sourceOutputConstant * rawSelection *
              (55296 * Kakeya.deltaTubeVolume 1) *
              (16 *
                ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
                  ENNReal) *
                proposition63OneScaleLogEnvelope (scale * sourceDelta) ^
                  (sourceSchedule.scaleCount + sourceSchedule.scaleCount))) *
          sourceOutputConstant) ≤
        (normalizationFixed *
              Kakeya.realRpowENN sourceDelta (-sourceLoss) *
            (Kakeya.realRpowENN sourceDelta (-(4 * sourceLoss)) *
                (proposition63M9SelectionCoefficient scale levelCount *
                  proposition63OneScaleLogEnvelope sourceDelta ^
                    (2 * levelCount + 3)) *
                (55296 * Kakeya.deltaTubeVolume 1) *
              ((16 : ENNReal) * (2 * (levelCount + 1) : ℕ) *
                proposition63OneScaleLogEnvelope sourceDelta ^
                  (2 * levelCount + 2))) *
          Kakeya.realRpowENN sourceDelta (-(4 * sourceLoss))) := by
      apply mul_le_mul
      · exact mul_le_mul_left' middleEnvelope
          (normalizationFixed *
            Kakeya.realRpowENN sourceDelta (-sourceLoss))
      · exact houtput
      · positivity
      · positivity
    let bodyCoefficient : ENNReal :=
      ENNReal.ofReal (27 * (2 * (22 * scale + 3) - 1) ^ 3) *
        (108 * ENNReal.ofReal Real.pi * 5200004 ^ 2 *
          (1 + 2 * ENNReal.ofReal scale)) *
        (normalizationFixed *
          (proposition63M9SelectionCoefficient scale levelCount *
            (55296 * Kakeya.deltaTubeVolume 1) *
            (16 * (2 * (levelCount + 1) : ℕ))))
    have bodyCoefficientLe : bodyCoefficient ≤
        proposition63M9TargetEnvelopeCoefficient scale levelCount := by
      dsimp only [bodyCoefficient, normalizationFixed,
        proposition63M9TargetEnvelopeCoefficient]
      exact le_max_of_le_right (le_max_right _ _)
    have logProduct :
        proposition63OneScaleLogEnvelope sourceDelta ^ (2 * levelCount + 3) *
            proposition63OneScaleLogEnvelope sourceDelta ^
              (2 * levelCount + 2) =
          proposition63OneScaleLogEnvelope sourceDelta ^
            (4 * levelCount + 5) := by
      rw [← pow_add]
      congr 1 <;> omega
    have powerProduct :
        Kakeya.realRpowENN sourceDelta (-(9 * sourceLoss)) *
              Kakeya.realRpowENN sourceDelta (-sourceLoss) *
              Kakeya.realRpowENN sourceDelta (-(4 * sourceLoss)) *
              Kakeya.realRpowENN sourceDelta (-(4 * sourceLoss)) =
          Kakeya.realRpowENN sourceDelta (-(18 * sourceLoss)) := by
      rw [← Kakeya.Assouad.realRpowENN_add sourceExtremal.delta_pos,
        ← Kakeya.Assouad.realRpowENN_add sourceExtremal.delta_pos,
        ← Kakeya.Assouad.realRpowENN_add sourceExtremal.delta_pos]
      congr 1 <;> ring
    dsimp only [proposition63M9TargetEnvelopeCoefficient]
    apply hbody.trans
    calc
      _ ≤ ENNReal.ofReal (27 * (2 * (22 * scale + 3) - 1) ^ 3) *
          (108 * ENNReal.ofReal Real.pi * 5200004 ^ 2 *
            ((1 + 2 * ENNReal.ofReal scale) *
              Kakeya.realRpowENN sourceDelta (-(9 * sourceLoss)))) *
          (((((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
                ENNReal.ofReal scale) *
              ((1 / 2 : ENNReal) *
                ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3)))⁻¹ *
            Kakeya.realRpowENN sourceDelta (-sourceLoss)) *
            ((Kakeya.realRpowENN sourceDelta (-(4 * sourceLoss)) *
                (proposition63M9SelectionCoefficient scale levelCount *
                  proposition63OneScaleLogEnvelope sourceDelta ^
                    (2 * levelCount + 3)) *
                (55296 * Kakeya.deltaTubeVolume 1) *
                ((16 : ENNReal) * (2 * (levelCount + 1) : ℕ) *
                  proposition63OneScaleLogEnvelope sourceDelta ^
                    (2 * levelCount + 2))) *
              Kakeya.realRpowENN sourceDelta (-(4 * sourceLoss)))) := by
        exact mul_le_mul
          (mul_le_mul (le_refl _)
            (mul_le_mul_left' windowFactor
              (108 * ENNReal.ofReal Real.pi * 5200004 ^ 2))
            (by positivity) (by positivity))
          (by
            dsimp only [rawSelection, normalizationFixed] at payloadEnvelope
            simpa only [mul_assoc] using payloadEnvelope)
          (by positivity) (by positivity)
      _ = bodyCoefficient *
          proposition63OneScaleLogEnvelope sourceDelta ^
            (4 * levelCount + 5) *
          Kakeya.realRpowENN sourceDelta (-(18 * sourceLoss)) := by
        rw [← logProduct, ← powerProduct]
        dsimp only [bodyCoefficient, normalizationFixed]
        ac_rfl
      _ ≤ proposition63M9TargetEnvelopeCoefficient scale levelCount *
          proposition63OneScaleLogEnvelope sourceDelta ^
            (4 * levelCount + 5) *
          Kakeya.realRpowENN sourceDelta (-(18 * sourceLoss)) := by
        exact mul_le_mul
          (mul_le_mul bodyCoefficientLe (le_refl _)
            (by positivity) (by positivity))
          (le_refl _) (by positivity) (by positivity)

theorem Proposition63M9MildRescalingQuotientTargetData.robustTargetConstant_scaleBudget
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
        scheduleWindowConstant ≤ data.robustTargetConstant :=
  le_max_left _ _

theorem Proposition63M9MildRescalingQuotientTargetData.robustTargetConstant_constantBudget
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    max (data.quotientSchedule.quotientFiberRegularizationConstant data.selection)
      (data.quotientSchedule.quotientScheduleBodyConstant data.jointRegularized
        (((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
          ENNReal.ofReal scale) *
          ((1 / 2 : ENNReal) * sourceData.sourceDensity))
        (data.selectionLoss * (55296 * Kakeya.deltaTubeVolume 1))) ≤
      data.robustTargetConstant :=
  le_max_right _ _

/-- The final target-CWA absorption cutoff is fixed before the runtime source
family, source schedule, dependent quotient target, and target constant. -/
theorem exists_proposition63_m9_target_envelope_cutoff
    (scale sourceLoss outputLoss : ℝ) (levelCount : ℕ)
    (hscale : 1 ≤ scale) (sourceLossPos : 0 < sourceLoss)
    (hloss : 18 * sourceLoss < outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        (4 : ENNReal) *
            proposition63M9TargetEnvelope scale sourceLoss levelCount delta ≤
          Kakeya.realRpowENN (scale * delta) (-outputLoss) := by
  let coefficient : ENNReal :=
    4 * proposition63M9TargetEnvelopeCoefficient scale levelCount *
      ENNReal.ofReal (Real.rpow scale outputLoss)
  have coefficientTop : coefficient ≠ ⊤ := by
    dsimp only [coefficient]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num)
        (proposition63M9TargetEnvelopeCoefficient_ne_top
          scale levelCount hscale))
      ENNReal.ofReal_ne_top
  have gapPos : 0 < outputLoss - 18 * sourceLoss := sub_pos.mpr hloss
  have exponentPos : 0 < 4 * levelCount + 5 := by omega
  rcases Kakeya.Assouad.exists_delta_C_pow_log_absorbed_ennreal
      coefficient coefficientTop proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg gapPos exponentPos with
    ⟨delta₀, delta₀Pos, delta₀One, absorb⟩
  refine ⟨delta₀, delta₀Pos, delta₀One, ?_⟩
  intro delta deltaPos deltaLe
  have envelopeBody := proposition63M9TargetEnvelope_le_body
    (scale := scale) (levelCount := levelCount) sourceLossPos deltaPos
      (deltaLe.trans delta₀One)
  have absorbBound := absorb delta deltaPos deltaLe
  have scalePower :
      Kakeya.realRpowENN (scale * delta) (-outputLoss) =
        ENNReal.ofReal (Real.rpow scale (-outputLoss)) *
          Kakeya.realRpowENN delta (-outputLoss) := by
    exact Kakeya.Assouad.realRpowENN_mul
      (zero_lt_one.trans_le hscale) deltaPos (-outputLoss)
  have scaleCancel :
      ENNReal.ofReal (Real.rpow scale outputLoss) *
          ENNReal.ofReal (Real.rpow scale (-outputLoss)) = 1 := by
    have hreal : Real.rpow scale outputLoss *
        Real.rpow scale (-outputLoss) = 1 := by
      calc
        _ = Real.rpow scale (outputLoss + (-outputLoss)) :=
          (Real.rpow_add (zero_lt_one.trans_le hscale) _ _).symm
        _ = 1 := by simp
    calc
      _ = ENNReal.ofReal (Real.rpow scale outputLoss *
          Real.rpow scale (-outputLoss)) :=
        (ENNReal.ofReal_mul (Real.rpow_nonneg
          (zero_lt_one.trans_le hscale).le outputLoss)).symm
      _ = 1 := by rw [hreal]; norm_num
  have weightedAbsorb :
      (4 * proposition63M9TargetEnvelopeCoefficient scale levelCount) *
          proposition63OneScaleLogEnvelope delta ^ (4 * levelCount + 5) ≤
        ENNReal.ofReal (Real.rpow scale (-outputLoss)) *
          Kakeya.realRpowENN delta (-(outputLoss - 18 * sourceLoss)) := by
    calc
      _ = ENNReal.ofReal (Real.rpow scale (-outputLoss)) *
          (coefficient * proposition63OneScaleLogEnvelope delta ^
            (4 * levelCount + 5)) := by
        dsimp only [coefficient]
        have scaleCancel' : ENNReal.ofReal (Real.rpow scale (-outputLoss)) *
            ENNReal.ofReal (Real.rpow scale outputLoss) = 1 := by
          simpa [mul_comm] using scaleCancel
        calc
          _ = 1 * ((4 * proposition63M9TargetEnvelopeCoefficient
              scale levelCount) *
                proposition63OneScaleLogEnvelope delta ^
                  (4 * levelCount + 5)) := by simp
          _ = _ := by rw [← scaleCancel']; ac_rfl
      _ ≤ _ := mul_le_mul_left' (by
        simpa only [proposition63OneScaleLogEnvelope] using absorbBound) _
  calc
    (4 : ENNReal) *
          proposition63M9TargetEnvelope scale sourceLoss levelCount delta ≤
        (4 * proposition63M9TargetEnvelopeCoefficient scale levelCount) *
          proposition63OneScaleLogEnvelope delta ^ (4 * levelCount + 5) *
          Kakeya.realRpowENN delta (-(18 * sourceLoss)) := by
      simpa only [mul_assoc] using mul_le_mul_left' envelopeBody 4
    _ ≤ ENNReal.ofReal (Real.rpow scale (-outputLoss)) *
          Kakeya.realRpowENN delta (-(outputLoss - 18 * sourceLoss)) *
          Kakeya.realRpowENN delta (-(18 * sourceLoss)) :=
      mul_le_mul_right' weightedAbsorb _
    _ = ENNReal.ofReal (Real.rpow scale (-outputLoss)) *
          Kakeya.realRpowENN delta (-outputLoss) := by
      rw [show ENNReal.ofReal (Real.rpow scale (-outputLoss)) *
            Kakeya.realRpowENN delta (-(outputLoss - 18 * sourceLoss)) *
            Kakeya.realRpowENN delta (-(18 * sourceLoss)) =
          ENNReal.ofReal (Real.rpow scale (-outputLoss)) *
            (Kakeya.realRpowENN delta (-(outputLoss - 18 * sourceLoss)) *
              Kakeya.realRpowENN delta (-(18 * sourceLoss))) by ac_rfl]
      rw [← Kakeya.Assouad.realRpowENN_add deltaPos]
      congr 1
      ring
    _ = Kakeya.realRpowENN (scale * delta) (-outputLoss) := scalePower.symm

/-- Assemble the dependent certificate on the very same `targetData` once
the five target-side scalar receipts are supplied.  The first receipt is a
finite envelope simultaneously dominating the scale window and both actual
target constants; the other four are precisely the power absorptions which
must come from a correctly ordered pre-runtime bound. -/
def proposition63_m9_robust_quotient_certificates_of_receipts
    {sourceDelta sigma sourceLoss outputLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (targetData : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule)
    (targetConstant : ENNReal)
    (targetFinite : WZ2PaperFiniteErrorConstant targetConstant)
    (scaleBudget :
      Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
        scheduleWindowConstant ≤ targetConstant)
    (constantBudget : ∀ _coordinate : Fin sourceSchedule.scaleCount,
      max (targetData.quotientSchedule.quotientFiberRegularizationConstant
          targetData.selection)
        (targetData.quotientSchedule.quotientScheduleBodyConstant
          targetData.jointRegularized
          (((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
            ENNReal.ofReal scale) *
            ((1 / 2 : ENNReal) * sourceData.sourceDensity))
          (targetData.selectionLoss *
            (55296 * Kakeya.deltaTubeVolume 1))) ≤ targetConstant)
    (finalCWAAbsorb : (4 : ENNReal) * targetConstant ≤
      Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss))
    (densityAbsorb : targetData.selectionLoss *
        Kakeya.realRpowENN (scale * sourceDelta) outputLoss ≤
      ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
        ENNReal.ofReal scale) *
        ((1 / 2 : ENNReal) * sourceData.sourceDensity))
    (volumeAbsorb : ENNReal.ofReal (scale ^ 3) *
        Kakeya.realRpowENN sourceDelta (sigma - sourceLoss) ≤
      Kakeya.realRpowENN (scale * sourceDelta) (sigma - outputLoss))
    (sourceLossPos : 0 < sourceLoss)
    (sourceLossLt : sourceLoss < outputLoss)
    (adAbsorb : Real.rpow sourceDelta (outputLoss - sourceLoss) ≤
      Real.rpow scale (-outputLoss))
    (planeScale : (Lplane : ℝ) ≤ scale)
    (slopeScale : (Lslope : ℝ) ≤ scale)
    (sigmaPos : 0 < sigma) (sigmaOne : sigma < 1) :
    Proposition63M9RobustQuotientTailCertificates
      (outputLoss := outputLoss) targetData := by
  exact {
    targetConstant := targetConstant
    target_finite := targetFinite
    scale_budget := scaleBudget
    constant_budget := constantBudget
    final_cwa_absorb := finalCWAAbsorb
    density_absorb := densityAbsorb
    volume_absorb := volumeAbsorb
    source_loss_pos := sourceLossPos
    source_loss_lt := sourceLossLt
    ad_absorb := adAbsorb
    plane_scale := planeScale
    slope_scale := slopeScale
    sigma_pos := sigmaPos
    sigma_lt_one := sigmaOne }

/-- Specialize the receipt constructor to the actual constant of the same
dependent quotient target.  The envelope is used only to prove finiteness and
the final absorption; it does not replace the runtime target constant. -/
def Proposition63M9MildRescalingQuotientTargetData.robustCertificates
    {sourceDelta sigma sourceLoss outputLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant : ENNReal}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) sourceOutputConstant
      (Kakeya.realRpowENN sourceDelta (-(8 * sourceLoss))) levelCount}
    (targetData : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule)
    (sourceLossPos : 0 < sourceLoss)
    (sourceLossLt : sourceLoss < outputLoss)
    (houtput : sourceOutputConstant ≤
      Kakeya.realRpowENN sourceDelta (-(4 * sourceLoss)))
    (hwindow :
      Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
          (Kakeya.realRpowENN sourceDelta (-(8 * sourceLoss))) ≤
        Kakeya.realRpowENN sourceDelta (-(9 * sourceLoss)))
    (targetEnvelopeAbsorb : (4 : ENNReal) *
        proposition63M9TargetEnvelope scale sourceLoss levelCount sourceDelta ≤
      Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss))
    (densityAbsorb : targetData.selectionLoss *
        Kakeya.realRpowENN (scale * sourceDelta) outputLoss ≤
      ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
        ENNReal.ofReal scale) *
        ((1 / 2 : ENNReal) * sourceData.sourceDensity))
    (volumeAbsorb : ENNReal.ofReal (scale ^ 3) *
        Kakeya.realRpowENN sourceDelta (sigma - sourceLoss) ≤
      Kakeya.realRpowENN (scale * sourceDelta) (sigma - outputLoss))
    (adAbsorb : Real.rpow sourceDelta (outputLoss - sourceLoss) ≤
      Real.rpow scale (-outputLoss))
    (planeScale : (Lplane : ℝ) ≤ scale)
    (slopeScale : (Lslope : ℝ) ≤ scale)
    (sigmaPos : 0 < sigma) (sigmaOne : sigma < 1) :
    Proposition63M9RobustQuotientTailCertificates
      (outputLoss := outputLoss) targetData := by
  let targetConstant := targetData.robustTargetConstant
  have targetLe := targetData.robustTargetConstant_le_envelope sourceData
    sourceLossPos houtput hwindow
  have targetTop : targetConstant ≠ ⊤ := by
    apply (targetLe.trans_lt <|
      (proposition63M9TargetEnvelope_ne_top scale sourceLoss sourceDelta
        levelCount hscale).lt_top).ne
  have targetOne : (1 : ENNReal) ≤ targetConstant := by
    apply (show (1 : ENNReal) ≤
      Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
        (Kakeya.realRpowENN sourceDelta (-(8 * sourceLoss))) by
      unfold Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
      exact (by norm_num : (1 : ENNReal) ≤ 4).trans (le_add_left le_rfl)).trans
    exact targetData.robustTargetConstant_scaleBudget
  apply proposition63_m9_robust_quotient_certificates_of_receipts targetData
    targetConstant ⟨targetOne, targetTop⟩
  · exact targetData.robustTargetConstant_scaleBudget
  · intro _
    exact targetData.robustTargetConstant_constantBudget
  · exact (mul_le_mul_left' targetLe 4).trans targetEnvelopeAbsorb
  · exact densityAbsorb
  · exact volumeAbsorb
  · exact sourceLossPos
  · exact sourceLossLt
  · exact adAbsorb
  · exact planeScale
  · exact slopeScale
  · exact sigmaPos
  · exact sigmaOne

/-- A single family-free cutoff which produces all quotient-tail
certificates for the actual dependent target chosen after runtime begins. -/
theorem Proposition63M9RobustTailScheduleData.exists_robustQuotientTailCutoff
    {sourceLoss : ℝ} {Lplane Lslope : NNReal}
    (schedule : Proposition63M9RobustTailScheduleData
      sourceLoss Lplane Lslope)
    (sigma outputLoss : ℝ) (sourceLossPos : 0 < sourceLoss)
    (hloss : 18 * sourceLoss < outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ schedule.delta₀ ∧
      ∀ {sourceDelta : ℝ}, 0 < sourceDelta → sourceDelta ≤ delta₀ →
        ∀ {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
          {sourceShading : WZ1PaperTubeShading sourceFamily}
          {sourceExtremal : WZ2PaperCroppedIsExtremal
            sigma sourceLoss sourceFamily sourceShading}
          {sourceLine : WZ1PaperIsLineClass sourceFamily}
          {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
          {sourceMidpoint : ∀ index,
            ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
          {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
            Lplane Lslope 1}
          {hscaleDeltaSmall : schedule.scale * sourceDelta ≤ 1 / 1000}
          (sourceData : Proposition63M9MildRescalingSourceData sourceShading
            sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain
            schedule.scale_one hscaleDeltaSmall
            schedule.levelCount (schedule.sourceOutputConstant sourceFamily))
          (sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
            (fine := sourceData.selected.family)
            (schedule.sourceOutputConstant sourceFamily)
            (Kakeya.realRpowENN sourceDelta (-(8 * sourceLoss)))
            schedule.levelCount)
          (targetData : Proposition63M9MildRescalingQuotientTargetData
            sourceData sourceSchedule),
          0 < sigma → sigma < 1 →
          Nonempty (Proposition63M9RobustQuotientTailCertificates
            (outputLoss := outputLoss) targetData) := by
  have sourceLossLt : sourceLoss < outputLoss := by linarith
  rcases schedule.exists_sourceOutputConstant_power_cutoff
      sourceLossPos sourceLoss sourceLossPos with
    ⟨sourceCutoff, sourceCutoffPos, sourceCutoffOne, sourceBound⟩
  rcases exists_proposition63_m9_quotient_window_cutoff
      (8 * sourceLoss) sourceLoss (by positivity) sourceLossPos with
    ⟨windowCutoff, windowCutoffPos, windowCutoffOne, windowBound⟩
  rcases exists_proposition63_m9_target_envelope_cutoff schedule.scale
      sourceLoss outputLoss schedule.levelCount schedule.scale_one
      sourceLossPos hloss with
    ⟨targetCutoff, targetCutoffPos, targetCutoffOne, targetBound⟩
  rcases exists_proposition63_m9_density_cutoff schedule.scale sourceLoss
      outputLoss schedule.levelCount schedule.scale_one sourceLossLt with
    ⟨densityCutoff, densityCutoffPos, densityCutoffOne, densityBound⟩
  rcases exists_proposition63_m9_volume_cutoff schedule.scale sigma sourceLoss
      outputLoss schedule.scale_one sourceLossLt with
    ⟨volumeCutoff, volumeCutoffPos, volumeCutoffOne, volumeBound⟩
  rcases exists_proposition63_m9_ad_cutoff schedule.scale sourceLoss
      outputLoss schedule.scale_one sourceLossLt with
    ⟨adCutoff, adCutoffPos, adCutoffOne, adBound⟩
  let delta₀ := min schedule.delta₀ <| min sourceCutoff <|
    min windowCutoff <| min targetCutoff <| min densityCutoff <|
      min volumeCutoff adCutoff
  have delta₀Pos : 0 < delta₀ := by
    dsimp only [delta₀]
    exact lt_min schedule.delta₀_pos <| lt_min sourceCutoffPos <|
      lt_min windowCutoffPos <| lt_min targetCutoffPos <|
        lt_min densityCutoffPos <| lt_min volumeCutoffPos adCutoffPos
  have delta₀Schedule : delta₀ ≤ schedule.delta₀ := by
    exact min_le_left _ _
  refine ⟨delta₀, delta₀Pos, delta₀Schedule, ?_⟩
  intro sourceDelta deltaPos deltaLe sourceFamily sourceShading
    sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain
    hscaleDeltaSmall sourceData sourceSchedule targetData sigmaPos sigmaOne
  have sourceLe : sourceDelta ≤ sourceCutoff :=
    deltaLe.trans <| (min_le_right _ _).trans <| min_le_left _ _
  have windowLe : sourceDelta ≤ windowCutoff :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| min_le_left _ _
  have targetLe : sourceDelta ≤ targetCutoff :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <| min_le_left _ _
  have densityLe : sourceDelta ≤ densityCutoff :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| min_le_left _ _
  have volumeLe : sourceDelta ≤ volumeCutoff :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <| min_le_left _ _
  have adLe : sourceDelta ≤ adCutoff :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <| min_le_right _ _
  have houtput := sourceBound deltaPos sourceLe sourceExtremal sourceMidpoint
  have hwindow := windowBound sourceDelta deltaPos windowLe
  have htarget := targetBound sourceDelta deltaPos targetLe
  have hdensity := densityBound deltaPos densityLe sourceData targetData
  have had := adBound sourceDelta deltaPos adLe
  have hvolume := volumeBound sourceDelta deltaPos volumeLe
  have houtput' : schedule.sourceOutputConstant sourceFamily ≤
      Kakeya.realRpowENN sourceDelta (-(4 * sourceLoss)) := by
    convert houtput using 1 <;> ring
  have hwindow' :
      Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
          (Kakeya.realRpowENN sourceDelta (-(8 * sourceLoss))) ≤
        Kakeya.realRpowENN sourceDelta (-(9 * sourceLoss)) := by
    convert hwindow using 1 <;> ring
  exact ⟨targetData.robustCertificates sourceLossPos sourceLossLt
    houtput' hwindow' htarget hdensity
    hvolume had schedule.plane_scale
    schedule.slope_scale sigmaPos sigmaOne⟩

/-! ## Runtime power-scale specialization -/

/-- The mild-rescaling scale used by the production M9 caller. -/
def proposition63M9PowerScale (delta scaleLoss : ℝ) : ℝ :=
  Real.rpow delta (-scaleLoss)

theorem proposition63M9PowerScale_pos
    {delta scaleLoss : ℝ} (deltaPos : 0 < delta) :
    0 < proposition63M9PowerScale delta scaleLoss :=
  Real.rpow_pos_of_pos deltaPos _

theorem proposition63M9PowerScale_one_le
    {delta scaleLoss : ℝ} (deltaPos : 0 < delta) (deltaOne : delta ≤ 1)
    (scaleLossNonneg : 0 ≤ scaleLoss) :
    1 ≤ proposition63M9PowerScale delta scaleLoss := by
  unfold proposition63M9PowerScale
  have h := Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne
    (show (0 : ℝ) ≥ -scaleLoss by linarith)
  simpa using h

theorem proposition63M9PowerScale_mul_delta
    {delta scaleLoss : ℝ} (deltaPos : 0 < delta) :
    proposition63M9PowerScale delta scaleLoss * delta =
      Real.rpow delta (1 - scaleLoss) := by
  unfold proposition63M9PowerScale
  have hdelta : Real.rpow delta 1 = delta := Real.rpow_one delta
  calc
    Real.rpow delta (-scaleLoss) * delta =
        Real.rpow delta (-scaleLoss) * Real.rpow delta 1 := by
      rw [hdelta]
    _ = Real.rpow delta (-scaleLoss + 1) := by
      exact (Real.rpow_add deltaPos _ _).symm
    _ = Real.rpow delta (1 - scaleLoss) := by ring_nf

/-- The discrete conflict-selection coefficient costs exactly five powers of
the runtime mild-rescaling scale. -/
def proposition63M9PowerSelectionCoefficient (levelCount : ℕ) : ENNReal :=
  (((22403 : ENNReal) ^ 5 + 1) *
      (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
        (levelCount + 1)) * 8

theorem proposition63M9SelectionCoefficient_le_power
    {scale : ℝ} (levelCount : ℕ) (hscale : 1 ≤ scale) :
    proposition63M9SelectionCoefficient scale levelCount ≤
      proposition63M9PowerSelectionCoefficient levelCount *
        ENNReal.ofReal (scale ^ 5) := by
  have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
  have hceilReal : (Nat.ceil (11200 * scale) : ℝ) ≤ 11201 * scale := by
    have hlt : (Nat.ceil (11200 * scale) : ℝ) < 11200 * scale + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    linarith
  have hbaseReal :
      ((2 * Nat.ceil (11200 * scale) + 1 : ℕ) : ℝ) ≤ 22403 * scale := by
    norm_cast at hceilReal ⊢
    push_cast
    linarith
  have hbaseENN :
      ((2 * Nat.ceil (11200 * scale) + 1 : ℕ) : ENNReal) ≤
        ENNReal.ofReal (22403 * scale) := by
    rw [show ((2 * Nat.ceil (11200 * scale) + 1 : ℕ) : ENNReal) =
      ENNReal.ofReal
        (((2 * Nat.ceil (11200 * scale) + 1 : ℕ) : ℝ)) by
          simpa using (ENNReal.ofReal_natCast
            (2 * Nat.ceil (11200 * scale) + 1)).symm]
    exact ENNReal.ofReal_mono hbaseReal
  have hpow :
      (((2 * Nat.ceil (11200 * scale) + 1 : ℕ) : ENNReal) ^ 5) ≤
        (22403 : ENNReal) ^ 5 * ENNReal.ofReal (scale ^ 5) := by
    calc
      _ ≤ ENNReal.ofReal (22403 * scale) ^ 5 := by gcongr
      _ = (22403 : ENNReal) ^ 5 * ENNReal.ofReal (scale ^ 5) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 22403)]
        rw [mul_pow, ENNReal.ofReal_pow (by positivity)]
        norm_num
  have scalePowOne : (1 : ENNReal) ≤ ENNReal.ofReal (scale ^ 5) := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num]
    apply ENNReal.ofReal_mono
    exact one_le_pow₀ hscale
  have hplus :
      (((2 * Nat.ceil (11200 * scale) + 1) ^ 5 + 1 : ℕ) : ENNReal) ≤
        (22403 : ENNReal) ^ 5 * ENNReal.ofReal (scale ^ 5) +
          ENNReal.ofReal (scale ^ 5) := by
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    exact add_le_add hpow scalePowOne
  unfold proposition63M9SelectionCoefficient
  unfold proposition63M9PowerSelectionCoefficient
  calc
    _ ≤ ((((22403 : ENNReal) ^ 5 * ENNReal.ofReal (scale ^ 5)) +
          ENNReal.ofReal (scale ^ 5)) *
          (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
          (levelCount + 1)) * 8 := by gcongr
    _ = (((22403 : ENNReal) ^ 5 + 1) *
          (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
            (levelCount + 1) * 8) * ENNReal.ofReal (scale ^ 5) := by ring

/-- The inverse density normalization contributes exactly two powers of the
runtime scale. -/
theorem proposition63M9NormalizationFixed_eq_power
    {scale : ℝ} (hscale : 1 ≤ scale) :
    (((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
        ENNReal.ofReal scale) *
      ((1 / 2 : ENNReal) *
        ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3)))⁻¹ =
      (((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
        ((1 / 2 : ENNReal) * ENNReal.ofReal (1 / 2000000 : ℝ)))⁻¹) *
        ENNReal.ofReal (scale ^ 2) := by
  have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
  have hscaleENNZero : ENNReal.ofReal scale ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hscalePos).ne'
  have hscaleENNTop : ENNReal.ofReal scale ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.ofReal_div_of_pos (pow_pos hscalePos 3)]
  rw [ENNReal.ofReal_pow hscalePos.le, ENNReal.ofReal_pow hscalePos.le]
  let s : ENNReal := ENNReal.ofReal scale
  let fixed : ENNReal :=
    (55296 * Kakeya.deltaTubeVolume 1)⁻¹ *
      (2⁻¹ * ENNReal.ofReal (2000000⁻¹ : ℝ))
  simp only [div_eq_mul_inv, one_mul]
  have hrepack :
      (55296 * Kakeya.deltaTubeVolume 1)⁻¹ * s *
          (2⁻¹ * (ENNReal.ofReal (2000000⁻¹ : ℝ) * (s ^ 3)⁻¹)) =
        fixed * s * (s ^ 3)⁻¹ := by
    dsimp only [fixed]
    ring
  rw [hrepack]
  change (fixed * s * (s ^ 3)⁻¹)⁻¹ = fixed⁻¹ * s ^ 2
  have hreduce : s * (s ^ 3)⁻¹ = (s ^ 2)⁻¹ := by
    rw [show s ^ 3 = s * s ^ 2 by ring]
    rw [ENNReal.mul_inv (Or.inl hscaleENNZero) (Or.inl hscaleENNTop)]
    rw [← mul_assoc, ENNReal.mul_inv_cancel hscaleENNZero hscaleENNTop]
    simp
  calc
    (fixed * s * (s ^ 3)⁻¹)⁻¹ = (fixed * (s ^ 2)⁻¹)⁻¹ := by
      rw [show fixed * s * (s ^ 3)⁻¹ = fixed * (s * (s ^ 3)⁻¹) by ring]
      rw [hreduce]
    _ = fixed⁻¹ * s ^ 2 := by
      rw [ENNReal.mul_inv
        (Or.inr <| ENNReal.inv_ne_top.mpr <| pow_ne_zero 2 hscaleENNZero)
        (Or.inr <| ENNReal.inv_ne_zero.mpr <|
          ENNReal.pow_ne_top hscaleENNTop)]
      simp
      rfl

theorem proposition63M9OuterCoefficient_le_power
    {scale : ℝ} (hscale : 1 ≤ scale) :
    ENNReal.ofReal (27 * (2 * (22 * scale + 3) - 1) ^ 3) ≤
      (27 * 49 ^ 3 : ENNReal) * ENNReal.ofReal (scale ^ 3) := by
  have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
  have hbase : 2 * (22 * scale + 3) - 1 ≤ 49 * scale := by linarith
  have hbaseNonneg : 0 ≤ 2 * (22 * scale + 3) - 1 := by linarith
  calc
    _ ≤ ENNReal.ofReal (27 * (49 * scale) ^ 3) := by
      apply ENNReal.ofReal_mono
      gcongr
    _ = (27 * 49 ^ 3 : ENNReal) * ENNReal.ofReal (scale ^ 3) := by
      rw [show (27 : ENNReal) = ENNReal.ofReal 27 by norm_num]
      rw [show (49 : ENNReal) = ENNReal.ofReal 49 by norm_num]
      rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 49)]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 27)]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (27 : ℝ) * 49 ^ 3)]
      congr 1
      ring

theorem proposition63M9WindowCoefficient_le_power
    {scale : ℝ} (hscale : 1 ≤ scale) :
    1 + 2 * ENNReal.ofReal scale ≤ 3 * ENNReal.ofReal scale := by
  have hone : (1 : ENNReal) ≤ ENNReal.ofReal scale := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num]
    exact ENNReal.ofReal_mono hscale
  calc
    1 + 2 * ENNReal.ofReal scale ≤
        ENNReal.ofReal scale + 2 * ENNReal.ofReal scale :=
      add_le_add_right hone (2 * ENNReal.ofReal scale)
        |> fun h => by simpa [add_comm] using h
    _ = 3 * ENNReal.ofReal scale := by ring

/-- Frozen coefficient left after extracting all eleven runtime-scale powers
from the actual target envelope. -/
def proposition63M9PowerTargetEnvelopeCoefficient
    (levelCount : ℕ) : ENNReal :=
  let joint : ENNReal := 16 * (2 * (levelCount + 1) : ℕ)
  let normalization : ENNReal :=
    ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
      ((1 / 2 : ENNReal) * ENNReal.ofReal (1 / 2000000 : ℝ)))⁻¹
  let body : ENNReal :=
    (27 * 49 ^ 3) *
      (108 * ENNReal.ofReal Real.pi * 5200004 ^ 2 * 3) *
      (normalization *
        (proposition63M9PowerSelectionCoefficient levelCount *
          (55296 * Kakeya.deltaTubeVolume 1) * joint))
  max 1 (max joint body)

theorem proposition63M9PowerTargetEnvelopeCoefficient_ne_top
    (levelCount : ℕ) :
    proposition63M9PowerTargetEnvelopeCoefficient levelCount ≠ ⊤ := by
  have hnormalizationZero :
      (55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
          ((1 / 2 : ENNReal) * ENNReal.ofReal (1 / 2000000 : ℝ)) ≠ 0 := by
    apply mul_ne_zero
    · exact ENNReal.inv_ne_zero.mpr <|
        ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top
    · apply mul_ne_zero (by norm_num)
      exact (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  dsimp only [proposition63M9PowerTargetEnvelopeCoefficient]
  apply max_ne_top (by norm_num)
  apply max_ne_top
  · finiteness
  · apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top (by norm_num) <|
        ENNReal.mul_ne_top
          (by
            exact ENNReal.mul_ne_top
              (ENNReal.mul_ne_top (by norm_num : (108 : ENNReal) ≠ ⊤)
                ENNReal.ofReal_ne_top)
              (by norm_num))
          (by norm_num)
    · apply ENNReal.mul_ne_top
      · exact ENNReal.inv_ne_top.mpr hnormalizationZero
      · exact ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by
            dsimp only [proposition63M9PowerSelectionCoefficient]
            finiteness) <|
            ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top)
          (by finiteness)

theorem proposition63M9TargetEnvelopeCoefficient_le_power
    {scale : ℝ} (levelCount : ℕ) (hscale : 1 ≤ scale) :
    proposition63M9TargetEnvelopeCoefficient scale levelCount ≤
      proposition63M9PowerTargetEnvelopeCoefficient levelCount *
        ENNReal.ofReal (scale ^ 11) := by
  let joint : ENNReal := 16 * (2 * (levelCount + 1) : ℕ)
  let normalization : ENNReal :=
    ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
      ((1 / 2 : ENNReal) * ENNReal.ofReal (1 / 2000000 : ℝ)))⁻¹
  let body : ENNReal :=
    (27 * 49 ^ 3) *
      (108 * ENNReal.ofReal Real.pi * 5200004 ^ 2 * 3) *
      (normalization *
        (proposition63M9PowerSelectionCoefficient levelCount *
          (55296 * Kakeya.deltaTubeVolume 1) * joint))
  have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
  have hsOne : (1 : ENNReal) ≤ ENNReal.ofReal (scale ^ 11) := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num]
    exact ENNReal.ofReal_mono (one_le_pow₀ hscale)
  have houter := proposition63M9OuterCoefficient_le_power hscale
  have hwindow := proposition63M9WindowCoefficient_le_power hscale
  have hnormalization := proposition63M9NormalizationFixed_eq_power hscale
  have hselection := proposition63M9SelectionCoefficient_le_power
    levelCount hscale
  have hwindowFull :
      108 * ENNReal.ofReal Real.pi * 5200004 ^ 2 *
          (1 + 2 * ENNReal.ofReal scale) ≤
        (108 * ENNReal.ofReal Real.pi * 5200004 ^ 2 * 3) *
          ENNReal.ofReal scale := by
    calc
      _ ≤ (108 * ENNReal.ofReal Real.pi * 5200004 ^ 2) *
          (3 * ENNReal.ofReal scale) :=
        mul_le_mul_left' hwindow _
      _ = _ := by ring
  have hpower :
      ENNReal.ofReal (scale ^ 3) * ENNReal.ofReal scale *
          ENNReal.ofReal (scale ^ 2) * ENNReal.ofReal (scale ^ 5) =
        ENNReal.ofReal (scale ^ 11) := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hscalePos.le 3)]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ scale ^ 3 * scale)]
    rw [← ENNReal.ofReal_mul
      (by positivity : 0 ≤ scale ^ 3 * scale * scale ^ 2)]
    congr 1
    ring
  have hbody :
      ENNReal.ofReal (27 * (2 * (22 * scale + 3) - 1) ^ 3) *
          (108 * ENNReal.ofReal Real.pi * 5200004 ^ 2 *
            (1 + 2 * ENNReal.ofReal scale)) *
          (((((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
                ENNReal.ofReal scale) *
              ((1 / 2 : ENNReal) *
                ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3)))⁻¹) *
            (proposition63M9SelectionCoefficient scale levelCount *
              (55296 * Kakeya.deltaTubeVolume 1) * joint)) ≤
        body * ENNReal.ofReal (scale ^ 11) := by
    rw [hnormalization]
    calc
      _ ≤ ((27 * 49 ^ 3 : ENNReal) * ENNReal.ofReal (scale ^ 3)) *
          ((108 * ENNReal.ofReal Real.pi * 5200004 ^ 2 * 3) *
            ENNReal.ofReal scale) *
          ((normalization * ENNReal.ofReal (scale ^ 2)) *
            ((proposition63M9PowerSelectionCoefficient levelCount *
                ENNReal.ofReal (scale ^ 5)) *
              (55296 * Kakeya.deltaTubeVolume 1) * joint)) := by
        dsimp only [normalization]
        apply mul_le_mul
        · exact mul_le_mul houter hwindowFull (by positivity) (by positivity)
        · apply mul_le_mul
          · exact le_rfl
          · exact mul_le_mul
              (mul_le_mul hselection le_rfl (by positivity) (by positivity))
              le_rfl (by positivity) (by positivity)
          · positivity
          · positivity
        · positivity
        · positivity
      _ = body * ENNReal.ofReal (scale ^ 11) := by
        dsimp only [body]
        rw [← hpower]
        ac_rfl
  dsimp only [proposition63M9TargetEnvelopeCoefficient,
    proposition63M9PowerTargetEnvelopeCoefficient]
  apply max_le
  · exact (le_max_left _ _).trans <|
      (le_mul_of_one_le_right (by positivity) hsOne)
  · apply max_le
    · exact (le_max_of_le_right <| le_max_left _ _).trans <|
        (le_mul_of_one_le_right (by positivity) hsOne)
    · exact hbody.trans <| mul_le_mul_right' (le_max_of_le_right <|
        le_max_right _ _) _

theorem proposition63M9PowerScale_ennreal_pow
    {delta scaleLoss : ℝ} (deltaPos : 0 < delta) (power : ℕ) :
    ENNReal.ofReal (proposition63M9PowerScale delta scaleLoss ^ power) =
      Kakeya.realRpowENN delta (-(power : ℝ) * scaleLoss) := by
  unfold proposition63M9PowerScale Kakeya.realRpowENN
  congr 1
  calc
    Real.rpow delta (-scaleLoss) ^ power =
        Real.rpow (Real.rpow delta (-scaleLoss)) power := by
      exact (Real.rpow_natCast _ power).symm
    _ = Real.rpow delta ((-scaleLoss) * power) := by
      exact (Real.rpow_mul deltaPos.le _ _).symm
    _ = Real.rpow delta (-(power : ℝ) * scaleLoss) := by
      congr 1
      push_cast
      ring

/-- Fixed coefficient in the runtime power-scale source regularization
envelope.  The omitted scale dependence is exactly the third power coming
from the inverse source density. -/
def proposition63M9PowerSourceEnvelopeCoefficient
    (levelCount : ℕ) : ENNReal :=
  let degree : ENNReal := 16 * (levelCount + 1 : ℕ)
  let density : ENNReal := (1 / 2) * ENNReal.ofReal (1 / 2000000 : ℝ)
  max 1 <| max degree <|
    density⁻¹ * ((2 * 8) * (55296 * Kakeya.deltaTubeVolume 1) * degree)

theorem proposition63M9PowerSourceEnvelopeCoefficient_ne_top
    (levelCount : ℕ) :
    proposition63M9PowerSourceEnvelopeCoefficient levelCount ≠ ⊤ := by
  unfold proposition63M9PowerSourceEnvelopeCoefficient
  apply max_ne_top
  · norm_num
  apply max_ne_top
  · finiteness
  apply ENNReal.mul_ne_top
  · apply ENNReal.inv_ne_top.mpr
    apply mul_ne_zero
    · norm_num
    · exact (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  · exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) (by norm_num))
        (ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top))
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _))

/-- The exact source-side regularization expression appearing in the robust
source certificates. -/
def proposition63M9PowerSourceRegularizationExpression
    {sourceDelta : ℝ} (scale sourceLoss : ℝ) (levelCount : ℕ)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta) : ENNReal :=
  let density := ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3) *
    Kakeya.realRpowENN sourceDelta sourceLoss
  let degreeConstant := 16 * ((levelCount + 1 : ℕ) : ENNReal) *
    (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^ (levelCount + 1)
  let regularizationLoss := (8 : ENNReal) *
    (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^ (levelCount + 2)
  let weight := (1 / 2 : ENNReal) * density
  let cardinalityLoss :=
    (2 * regularizationLoss) * (55296 * Kakeya.deltaTubeVolume 1)
  max degreeConstant
    ((weight⁻¹ *
      (Kakeya.realRpowENN sourceDelta (-sourceLoss) * cardinalityLoss *
        degreeConstant)) *
      Kakeya.realRpowENN sourceDelta (-sourceLoss))

/-- Family-free envelope for the actual source regularization formula at a
runtime scale. -/
theorem proposition63M9PowerSourceRegularizationExpression_le_envelope
    {sourceDelta sigma sourceLoss scale : ℝ} {levelCount : ℕ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading)
    (sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3)
    (sourceLossPos : 0 < sourceLoss) (hscale : 1 ≤ scale) :
    proposition63M9PowerSourceRegularizationExpression scale sourceLoss
        levelCount sourceFamily ≤
      proposition63M9PowerSourceEnvelopeCoefficient levelCount *
        proposition63OneScaleLogEnvelope sourceDelta ^
          (levelCount + levelCount + 3) *
        ENNReal.ofReal (scale ^ 3) *
        Kakeya.realRpowENN sourceDelta (-(3 * sourceLoss)) := by
  let logEnvelope := proposition63OneScaleLogEnvelope sourceDelta
  let ambient := Kakeya.realRpowENN sourceDelta (-sourceLoss)
  let degree : ENNReal := 16 * (levelCount + 1 : ℕ)
  let fixedDensity : ENNReal :=
    (1 / 2) * ENNReal.ofReal (1 / 2000000 : ℝ)
  have scalePos : 0 < scale := zero_lt_one.trans_le hscale
  have logOne : (1 : ENNReal) ≤ logEnvelope := by
    dsimp only [logEnvelope, proposition63OneScaleLogEnvelope]
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num]
    apply ENNReal.ofReal_mono
    have hlog : 0 ≤ Real.log sourceDelta⁻¹ :=
      Real.log_nonneg ((one_le_inv₀ sourceExtremal.delta_pos).mpr
        sourceExtremal.delta_le_one)
    have hcoefficient : 1 ≤ proposition63OneScaleLogCoefficient :=
      (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
    nlinarith [proposition63OneScaleLogCoefficient_nonneg]
  have ambientOne : (1 : ENNReal) ≤ ambient := by
    have hreal := Real.rpow_le_rpow_of_exponent_ge sourceExtremal.delta_pos
      sourceExtremal.delta_le_one
      (show (0 : ℝ) ≥ -sourceLoss by linarith)
    simpa [ambient, Kakeya.realRpowENN] using ENNReal.ofReal_mono hreal
  have scaleCubeOne : (1 : ENNReal) ≤ ENNReal.ofReal (scale ^ 3) := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num]
    exact ENNReal.ofReal_mono (one_le_pow₀ hscale)
  have cardLog :=
    Proposition63M9RobustTailScheduleData.source_cardLog_le_logEnvelope
      sourceExtremal sourceMidpoint
  have ambientCube : ambient * ambient * ambient =
      Kakeya.realRpowENN sourceDelta (-(3 * sourceLoss)) := by
    rw [← Kakeya.Assouad.realRpowENN_add sourceExtremal.delta_pos,
      ← Kakeya.Assouad.realRpowENN_add sourceExtremal.delta_pos]
    congr 1
    ring
  have densityFixed :
      (1 / 2 : ENNReal) *
          ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3) =
        fixedDensity * (ENNReal.ofReal (scale ^ 3))⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (pow_pos scalePos 3)]
    dsimp only [fixedDensity]
    rw [ENNReal.ofReal_pow scalePos.le]
    simp only [div_eq_mul_inv]
    ring
  have densityInv :
      ((1 / 2 : ENNReal) *
          (ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3) *
            Kakeya.realRpowENN sourceDelta sourceLoss))⁻¹ =
        fixedDensity⁻¹ * ENNReal.ofReal (scale ^ 3) * ambient := by
    rw [show (1 / 2 : ENNReal) *
        (ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3) *
          Kakeya.realRpowENN sourceDelta sourceLoss) =
        ((1 / 2 : ENNReal) *
          ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3)) *
          Kakeya.realRpowENN sourceDelta sourceLoss by ac_rfl, densityFixed]
    rw [ENNReal.mul_inv
      (Or.inr (by simp [Kakeya.realRpowENN]))
      (Or.inr (by simp [Kakeya.realRpowENN,
        Real.rpow_pos_of_pos sourceExtremal.delta_pos]))]
    rw [ENNReal.mul_inv
      (Or.inr (by
        exact ENNReal.inv_ne_top.mpr <|
          (ENNReal.ofReal_pos.mpr (pow_pos scalePos 3)).ne'))
      (Or.inr (by simp [fixedDensity]))]
    rw [inv_inv, realRpowENN_inv_eq_neg sourceExtremal.delta_pos]
  unfold proposition63M9PowerSourceRegularizationExpression
  dsimp only
  apply max_le
  · calc
      degree * (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
            (levelCount + 1) ≤
          degree * logEnvelope ^ (levelCount + 1) := by gcongr
      _ ≤ degree * logEnvelope ^ (levelCount + levelCount + 3) *
            ENNReal.ofReal (scale ^ 3) * (ambient * ambient * ambient) := by
        have hp := pow_le_pow_right₀ logOne
          (show levelCount + 1 ≤ levelCount + levelCount + 3 by omega)
        calc
          _ ≤ degree * logEnvelope ^ (levelCount + levelCount + 3) := by
            gcongr
          _ ≤ degree * logEnvelope ^ (levelCount + levelCount + 3) *
              ENNReal.ofReal (scale ^ 3) := le_mul_of_one_le_right' scaleCubeOne
          _ ≤ _ := le_mul_of_one_le_right' <|
            one_le_mul_of_one_le_of_one_le
              (one_le_mul_of_one_le_of_one_le ambientOne ambientOne) ambientOne
      _ ≤ proposition63M9PowerSourceEnvelopeCoefficient levelCount *
            logEnvelope ^ (levelCount + levelCount + 3) *
            ENNReal.ofReal (scale ^ 3) * (ambient * ambient * ambient) := by
        gcongr
        exact (le_max_left degree _).trans (le_max_right _ _)
      _ = _ := by rw [ambientCube]
  · rw [densityInv]
    have hcardLoss :
        (2 * ((8 : ENNReal) *
          (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
            (levelCount + 2))) * (55296 * Kakeya.deltaTubeVolume 1) ≤
          ((2 * 8) * (55296 * Kakeya.deltaTubeVolume 1)) *
            logEnvelope ^ (levelCount + 2) := by
      calc
        _ ≤ (2 * (8 * logEnvelope ^ (levelCount + 2))) *
            (55296 * Kakeya.deltaTubeVolume 1) := by gcongr
        _ = _ := by ac_rfl
    have hdegree : degree *
        (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
          (levelCount + 1) ≤ degree * logEnvelope ^ (levelCount + 1) := by
      gcongr
    have hcombined :
        ((2 * ((8 : ENNReal) *
          (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
            (levelCount + 2))) * (55296 * Kakeya.deltaTubeVolume 1)) *
          (degree * (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
            (levelCount + 1)) ≤
        (((2 * 8) * (55296 * Kakeya.deltaTubeVolume 1)) * degree) *
          logEnvelope ^ (levelCount + levelCount + 3) := by
      calc
        _ ≤ (((2 * 8) * (55296 * Kakeya.deltaTubeVolume 1)) *
              logEnvelope ^ (levelCount + 2)) *
            (degree * logEnvelope ^ (levelCount + 1)) := by gcongr
        _ = _ := by
          have hpow : logEnvelope ^ (levelCount + 2) *
              logEnvelope ^ (levelCount + 1) =
            logEnvelope ^ (levelCount + levelCount + 3) := by
            rw [← pow_add]
            congr 1
            omega
          rw [← hpow]
          ac_rfl
    have lifted := mul_le_mul_left'
      (mul_le_mul_right'
        (mul_le_mul_left' hcombined ambient) ambient)
      (fixedDensity⁻¹ * ENNReal.ofReal (scale ^ 3) * ambient)
    calc
      fixedDensity⁻¹ * ENNReal.ofReal (scale ^ 3) * ambient *
            (ambient *
              ((2 * ((8 : ENNReal) *
                (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
                  (levelCount + 2))) *
                (55296 * Kakeya.deltaTubeVolume 1)) *
              (degree *
                (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
                  (levelCount + 1))) * ambient ≤
          fixedDensity⁻¹ * ENNReal.ofReal (scale ^ 3) * ambient *
            (ambient *
              ((((2 * 8) * (55296 * Kakeya.deltaTubeVolume 1)) * degree) *
                logEnvelope ^ (levelCount + levelCount + 3))) * ambient := by
        convert lifted using 1 <;> ac_rfl
      _ = (fixedDensity⁻¹ *
            ((2 * 8) * (55296 * Kakeya.deltaTubeVolume 1) * degree)) *
          logEnvelope ^ (levelCount + levelCount + 3) *
          ENNReal.ofReal (scale ^ 3) * (ambient * ambient * ambient) := by
        ac_rfl
      _ ≤ proposition63M9PowerSourceEnvelopeCoefficient levelCount *
          logEnvelope ^ (levelCount + levelCount + 3) *
          ENNReal.ofReal (scale ^ 3) * (ambient * ambient * ambient) := by
        gcongr
        exact (le_max_right degree _).trans (le_max_right _ _)
      _ = _ := by rw [ambientCube]

/-- Power-scale version of the final target-envelope cutoff.  Its cutoff is
frozen before `sourceDelta` and hence before every source family and dependent
target witness.  The strengthened gap uses twelve scale-loss powers: eleven
from the target coefficient and one uniformly covering the final
`scale ^ (-outputLoss)` when `outputLoss ≤ 1`. -/
theorem exists_proposition63_m9_power_target_envelope_cutoff
    (sourceLoss outputLoss scaleLoss : ℝ) (levelCount : ℕ)
    (sourceLossPos : 0 < sourceLoss) (scaleLossNonneg : 0 ≤ scaleLoss)
    (outputLossOne : outputLoss ≤ 1)
    (hloss : 18 * sourceLoss + 12 * scaleLoss < outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        (4 : ENNReal) * proposition63M9TargetEnvelope
            (proposition63M9PowerScale delta scaleLoss) sourceLoss
            levelCount delta ≤
          Kakeya.realRpowENN
            (proposition63M9PowerScale delta scaleLoss * delta)
            (-outputLoss) := by
  let coefficient : ENNReal :=
    4 * proposition63M9PowerTargetEnvelopeCoefficient levelCount
  have coefficientTop : coefficient ≠ ⊤ := by
    dsimp only [coefficient]
    exact ENNReal.mul_ne_top (by norm_num) <|
      proposition63M9PowerTargetEnvelopeCoefficient_ne_top levelCount
  have gapPos :
      0 < outputLoss - 18 * sourceLoss - 12 * scaleLoss := by linarith
  have exponentPos : 0 < 4 * levelCount + 5 := by omega
  rcases Kakeya.Assouad.exists_delta_C_pow_log_absorbed_ennreal
      coefficient coefficientTop proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg gapPos exponentPos with
    ⟨delta₀, delta₀Pos, delta₀One, absorb⟩
  refine ⟨delta₀, delta₀Pos, delta₀One, ?_⟩
  intro delta deltaPos deltaLe
  have deltaOne : delta ≤ 1 := deltaLe.trans delta₀One
  let scale := proposition63M9PowerScale delta scaleLoss
  have scaleOne : 1 ≤ scale :=
    proposition63M9PowerScale_one_le deltaPos deltaOne scaleLossNonneg
  have envelopeBody := proposition63M9TargetEnvelope_le_body
    (scale := scale) (levelCount := levelCount) sourceLossPos deltaPos deltaOne
  have coefficientPower := proposition63M9TargetEnvelopeCoefficient_le_power
    levelCount scaleOne
  have scalePow : ENNReal.ofReal (scale ^ 11) =
      Kakeya.realRpowENN delta (-(11 : ℝ) * scaleLoss) := by
    exact proposition63M9PowerScale_ennreal_pow deltaPos 11
  have absorbBound := absorb delta deltaPos deltaLe
  have outputScaleLe : outputLoss * scaleLoss ≤ scaleLoss := by
    nlinarith
  have targetPowerLe :
      Kakeya.realRpowENN delta
          (-outputLoss + scaleLoss) ≤
        Kakeya.realRpowENN delta
          (-outputLoss + outputLoss * scaleLoss) := by
    unfold Kakeya.realRpowENN
    exact ENNReal.ofReal_mono <|
      Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne (by linarith)
  calc
    (4 : ENNReal) * proposition63M9TargetEnvelope scale sourceLoss
          levelCount delta ≤
        (4 * proposition63M9TargetEnvelopeCoefficient scale levelCount) *
          proposition63OneScaleLogEnvelope delta ^ (4 * levelCount + 5) *
          Kakeya.realRpowENN delta (-(18 * sourceLoss)) := by
      simpa only [mul_assoc] using mul_le_mul_left' envelopeBody 4
    _ ≤ (coefficient * ENNReal.ofReal (scale ^ 11)) *
          proposition63OneScaleLogEnvelope delta ^ (4 * levelCount + 5) *
          Kakeya.realRpowENN delta (-(18 * sourceLoss)) := by
      exact mul_le_mul_right' (mul_le_mul_right'
        (show 4 * proposition63M9TargetEnvelopeCoefficient scale levelCount ≤
            coefficient * ENNReal.ofReal (scale ^ 11) by
          dsimp only [coefficient]
          simpa only [mul_assoc] using mul_le_mul_left' coefficientPower 4) _) _
    _ = (coefficient * proposition63OneScaleLogEnvelope delta ^
            (4 * levelCount + 5)) *
          (Kakeya.realRpowENN delta (-(11 * scaleLoss)) *
            Kakeya.realRpowENN delta (-(18 * sourceLoss))) := by
      rw [scalePow]
      norm_num
      ac_rfl
    _ ≤ Kakeya.realRpowENN delta
          (-(outputLoss - 18 * sourceLoss - 12 * scaleLoss)) *
          (Kakeya.realRpowENN delta (-(11 * scaleLoss)) *
            Kakeya.realRpowENN delta (-(18 * sourceLoss))) := by
      gcongr
      simpa only [proposition63OneScaleLogEnvelope] using absorbBound
    _ = Kakeya.realRpowENN delta (-outputLoss + scaleLoss) := by
      rw [← Kakeya.Assouad.realRpowENN_add deltaPos,
        ← Kakeya.Assouad.realRpowENN_add deltaPos]
      congr 1
      ring
    _ ≤ Kakeya.realRpowENN delta
          (-outputLoss + outputLoss * scaleLoss) := targetPowerLe
    _ = Kakeya.realRpowENN (scale * delta) (-outputLoss) := by
      rw [proposition63M9PowerScale_mul_delta deltaPos]
      unfold Kakeya.realRpowENN
      have hrpow : Real.rpow delta (-outputLoss + outputLoss * scaleLoss) =
          Real.rpow (Real.rpow delta (1 - scaleLoss)) (-outputLoss) := by
        calc
          Real.rpow delta (-outputLoss + outputLoss * scaleLoss) =
              Real.rpow delta ((1 - scaleLoss) * (-outputLoss)) := by
            congr 1
            ring
          _ = Real.rpow (Real.rpow delta (1 - scaleLoss)) (-outputLoss) :=
            Real.rpow_mul deltaPos.le _ _
      exact congrArg ENNReal.ofReal hrpow

theorem proposition63M9PowerScale_ad_absorb
    {delta sourceLoss outputLoss scaleLoss : ℝ}
    (deltaPos : 0 < delta) (deltaOne : delta ≤ 1)
    (sourceLossPos : 0 < sourceLoss) (scaleLossNonneg : 0 ≤ scaleLoss)
    (outputLossOne : outputLoss ≤ 1)
    (hloss : 18 * sourceLoss + 12 * scaleLoss < outputLoss) :
    Real.rpow delta (outputLoss - sourceLoss) ≤
      Real.rpow (proposition63M9PowerScale delta scaleLoss) (-outputLoss) := by
  unfold proposition63M9PowerScale
  have htarget : Real.rpow (Real.rpow delta (-scaleLoss)) (-outputLoss) =
      Real.rpow delta ((-scaleLoss) * (-outputLoss)) :=
    (Real.rpow_mul deltaPos.le _ _).symm
  rw [htarget]
  apply Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne
  nlinarith

theorem proposition63M9PowerScale_volume_absorb
    {delta sigma sourceLoss outputLoss scaleLoss : ℝ}
    (deltaPos : 0 < delta) (deltaOne : delta ≤ 1)
    (sigmaPos : 0 < sigma) (sigmaOne : sigma < 1)
    (sourceLossPos : 0 < sourceLoss) (scaleLossNonneg : 0 ≤ scaleLoss)
    (outputLossOne : outputLoss ≤ 1)
    (hloss : 18 * sourceLoss + 12 * scaleLoss < outputLoss) :
    ENNReal.ofReal (proposition63M9PowerScale delta scaleLoss ^ 3) *
        Kakeya.realRpowENN delta (sigma - sourceLoss) ≤
      Kakeya.realRpowENN
        (proposition63M9PowerScale delta scaleLoss * delta)
        (sigma - outputLoss) := by
  rw [proposition63M9PowerScale_ennreal_pow deltaPos 3]
  rw [← Kakeya.Assouad.realRpowENN_add deltaPos]
  rw [proposition63M9PowerScale_mul_delta deltaPos]
  unfold Kakeya.realRpowENN
  apply ENNReal.ofReal_mono
  have htarget :
      Real.rpow (Real.rpow delta (1 - scaleLoss)) (sigma - outputLoss) =
        Real.rpow delta ((1 - scaleLoss) * (sigma - outputLoss)) :=
    (Real.rpow_mul deltaPos.le _ _).symm
  rw [htarget]
  apply Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne
  have hfactor : 3 - sigma + outputLoss ≤ 4 := by linarith
  have hscaled : (3 - sigma + outputLoss) * scaleLoss ≤
      4 * scaleLoss := by gcongr
  have hgap : 4 * scaleLoss < outputLoss - sourceLoss := by nlinarith
  have hexponent :
      (1 - scaleLoss) * (sigma - outputLoss) ≤
        -(3 : ℝ) * scaleLoss + (sigma - sourceLoss) := by
    nlinarith
  have hexponent' :
      3 * scaleLoss + (1 - scaleLoss) * (sigma - outputLoss) ≤
        sigma - sourceLoss := by nlinarith
  norm_num
  linarith

/-- Family-free source-output absorption when the source envelope carries
three powers of the runtime mild-rescaling scale. -/
theorem exists_proposition63_m9_power_source_output_cutoff
    (coefficient : ENNReal) (logPower : ℕ)
    (sourceLoss scaleLoss outputExponent : ℝ)
    (coefficientTop : coefficient ≠ ⊤)
    (hloss : 3 * sourceLoss + 3 * scaleLoss < outputExponent) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        coefficient * proposition63OneScaleLogEnvelope delta ^ logPower *
            ENNReal.ofReal (proposition63M9PowerScale delta scaleLoss ^ 3) *
            Kakeya.realRpowENN delta (-(3 * sourceLoss)) ≤
          Kakeya.realRpowENN delta (-outputExponent) := by
  have gapPos :
      0 < outputExponent - 3 * sourceLoss - 3 * scaleLoss := by linarith
  rcases Kakeya.Assouad.exists_delta_C_pow_log_absorbed_ennreal
      coefficient coefficientTop proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg gapPos
      (show 0 < logPower + 1 by omega) with
    ⟨delta₀, delta₀Pos, delta₀One, absorb⟩
  refine ⟨delta₀, delta₀Pos, delta₀One, ?_⟩
  intro delta deltaPos deltaLe
  have logOne : (1 : ENNReal) ≤ proposition63OneScaleLogEnvelope delta := by
    unfold proposition63OneScaleLogEnvelope
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num]
    apply ENNReal.ofReal_mono
    have hlog : 0 ≤ Real.log delta⁻¹ :=
      Real.log_nonneg ((one_le_inv₀ deltaPos).mpr (deltaLe.trans delta₀One))
    have hcoefficient : 1 ≤ proposition63OneScaleLogCoefficient :=
      (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
    nlinarith
  have absorb' : coefficient *
      proposition63OneScaleLogEnvelope delta ^ logPower ≤
        Kakeya.realRpowENN delta
          (-(outputExponent - 3 * sourceLoss - 3 * scaleLoss)) := by
    calc
      _ ≤ coefficient * proposition63OneScaleLogEnvelope delta ^ logPower *
          proposition63OneScaleLogEnvelope delta :=
        le_mul_of_one_le_right' logOne
      _ = coefficient * proposition63OneScaleLogEnvelope delta ^
          (logPower + 1) := by
        rw [pow_succ']
        ac_rfl
      _ ≤ _ := by
        simpa only [proposition63OneScaleLogEnvelope] using
          absorb delta deltaPos deltaLe
  rw [proposition63M9PowerScale_ennreal_pow deltaPos 3]
  calc
    _ ≤ Kakeya.realRpowENN delta
          (-(outputExponent - 3 * sourceLoss - 3 * scaleLoss)) *
          Kakeya.realRpowENN delta (-((3 : ℕ) : ℝ) * scaleLoss) *
          Kakeya.realRpowENN delta (-(3 * sourceLoss)) := by
      exact mul_le_mul_right'
          (mul_le_mul_right' absorb'
            (Kakeya.realRpowENN delta (-((3 : ℕ) : ℝ) * scaleLoss)))
          (Kakeya.realRpowENN delta (-(3 * sourceLoss)))
    _ = Kakeya.realRpowENN delta (-outputExponent) := by
      rw [← Kakeya.Assouad.realRpowENN_add deltaPos,
        ← Kakeya.Assouad.realRpowENN_add deltaPos]
      congr 1
      ring

/-- Pre-runtime construction of every scalar receipt needed by the actual
source producer at the runtime power scale.  The output constant is the pure
power `delta ^ (-outputExponent)` and is therefore independent of the family. -/
theorem exists_proposition63_m9_power_source_certificates_cutoff
    (sourceLoss scaleLoss outputExponent : ℝ) (levelCount : ℕ)
    (sourceLossPos : 0 < sourceLoss) (scaleLossNonneg : 0 ≤ scaleLoss)
    (scaleLossOne : scaleLoss < 1)
    (levelCountLoss : 1 ≤ (levelCount : ℝ) * sourceLoss)
    (windowLoss : 2 * sourceLoss ≤ outputExponent)
    (sourceGap : 3 * sourceLoss + 3 * scaleLoss < outputExponent) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sourceDelta sigma : ℝ}, 0 < sourceDelta → sourceDelta ≤ delta₀ →
        ∀ {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
          {sourceShading : WZ1PaperTubeShading sourceFamily},
          WZ2PaperCroppedIsExtremal
              sigma sourceLoss sourceFamily sourceShading →
          (∀ index,
            ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3) →
          ∃ hscale : 1 ≤ proposition63M9PowerScale sourceDelta scaleLoss,
            Proposition63M9RobustTailSourceCertificates
              (sourceLoss := sourceLoss) (sourceFamily := sourceFamily)
              hscale levelCount
              (Kakeya.realRpowENN sourceDelta (-outputExponent)) := by
  let coefficient := proposition63M9PowerSourceEnvelopeCoefficient levelCount
  have coefficientTop : coefficient ≠ ⊤ :=
    proposition63M9PowerSourceEnvelopeCoefficient_ne_top levelCount
  rcases exists_proposition63_m9_power_source_output_cutoff coefficient
      (levelCount + levelCount + 3) sourceLoss scaleLoss outputExponent
      coefficientTop sourceGap with
    ⟨outputCutoff, outputCutoffPos, outputCutoffOne, outputBound⟩
  rcases pure_wz2_exists_delta₀_rpow_le (threshold := 1 / 1000)
      (s := 1 - scaleLoss) (by norm_num) (by linarith) with
    ⟨scaleCutoff, scaleCutoffPos, scaleCutoffOne, scaleBound⟩
  rcases exists_delta_realRpowENN_bound (3 : ENNReal) (by norm_num)
      sourceLossPos with
    ⟨ambientCutoff, ambientCutoffPos, ambientCutoffOne, ambientBound⟩
  let delta₀ := min outputCutoff (min scaleCutoff ambientCutoff)
  have delta₀Pos : 0 < delta₀ :=
    lt_min outputCutoffPos (lt_min scaleCutoffPos ambientCutoffPos)
  have delta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans outputCutoffOne
  refine ⟨delta₀, delta₀Pos, delta₀One, ?_⟩
  intro sourceDelta sigma deltaPos deltaLe sourceFamily sourceShading
    sourceExtremal sourceMidpoint
  have deltaOne : sourceDelta ≤ 1 := deltaLe.trans delta₀One
  have outputLe : sourceDelta ≤ outputCutoff :=
    deltaLe.trans (min_le_left _ _)
  have scaleLe : sourceDelta ≤ scaleCutoff :=
    deltaLe.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ambientLe : sourceDelta ≤ ambientCutoff :=
    deltaLe.trans ((min_le_right _ _).trans (min_le_right _ _))
  let scale := proposition63M9PowerScale sourceDelta scaleLoss
  have scaleOne : 1 ≤ scale :=
    proposition63M9PowerScale_one_le deltaPos deltaOne scaleLossNonneg
  have scaleSmall : scale * sourceDelta ≤ 1 / 1000 := by
    rw [proposition63M9PowerScale_mul_delta deltaPos]
    exact scaleBound sourceDelta deltaPos scaleLe
  have ambientTwo : (2 : ENNReal) <
      Kakeya.realRpowENN sourceDelta (-sourceLoss) :=
    (by norm_num : (2 : ENNReal) < 3).trans_le
      (ambientBound sourceDelta deltaPos ambientLe)
  have levels : ENNReal.ofReal (1 / sourceDelta) ≤
      Kakeya.realRpowENN sourceDelta (-sourceLoss) ^ levelCount := by
    have hexponent : -1 ≥ -(levelCount : ℝ) * sourceLoss := by linarith
    have hrpow := Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne hexponent
    have hleft : Real.rpow sourceDelta (-1) = 1 / sourceDelta := by
      calc
        Real.rpow sourceDelta (-1) = sourceDelta⁻¹ :=
          Real.rpow_neg_one sourceDelta
        _ = 1 / sourceDelta := inv_eq_one_div _
    have hright :
        Kakeya.realRpowENN sourceDelta (-sourceLoss) ^ levelCount =
          ENNReal.ofReal
            (Real.rpow sourceDelta (-(levelCount : ℝ) * sourceLoss)) := by
      have hbase :
          Kakeya.realRpowENN sourceDelta (-sourceLoss) =
            ENNReal.ofReal (Real.rpow sourceDelta (-sourceLoss)) := by rfl
      rw [hbase]
      have hpow :
          (ENNReal.ofReal (Real.rpow sourceDelta (-sourceLoss))) ^ levelCount =
            ENNReal.ofReal
              ((Real.rpow sourceDelta (-sourceLoss)) ^ levelCount) := by
        exact (ENNReal.ofReal_pow
          (Real.rpow_nonneg deltaPos.le _) levelCount).symm
      rw [hpow]
      congr 1
      rw [rpow_nat_pow deltaPos (-sourceLoss) levelCount]
      ring
    rw [hright, ← hleft]
    exact ENNReal.ofReal_mono hrpow
  have outputWindow :
      Kakeya.realRpowENN sourceDelta (-sourceLoss) *
          Kakeya.realRpowENN sourceDelta (-sourceLoss) ≤
        Kakeya.realRpowENN sourceDelta (-outputExponent) := by
    rw [← Kakeya.Assouad.realRpowENN_add deltaPos]
    unfold Kakeya.realRpowENN
    exact ENNReal.ofReal_mono <|
      Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne (by linarith)
  have envelope :=
    proposition63M9PowerSourceRegularizationExpression_le_envelope
      (levelCount := levelCount)
      sourceExtremal sourceMidpoint sourceLossPos scaleOne
  have absorbed := outputBound sourceDelta deltaPos outputLe
  refine ⟨scaleOne, {
    scale_delta_small := scaleSmall
    ambient_two := ambientTwo
    levels := levels
    output_ne_top := by simp [Kakeya.realRpowENN]
    output_window := outputWindow
    regularization_absorb := ?_ }⟩
  change proposition63M9PowerSourceRegularizationExpression scale sourceLoss
      levelCount sourceFamily ≤
    Kakeya.realRpowENN sourceDelta (-outputExponent)
  exact envelope.trans absorbed

/-- Density absorption at the runtime power scale.  The scale cost is at most
eight powers: five from selection, two from inverse normalization, and one
covering the target `outputLoss` power. -/
theorem exists_proposition63_m9_power_density_cutoff
    (sourceLoss outputLoss scaleLoss : ℝ) (levelCount : ℕ)
    (sourceLossPos : 0 < sourceLoss) (scaleLossNonneg : 0 ≤ scaleLoss)
    (outputLossOne : outputLoss ≤ 1)
    (hloss : sourceLoss + 8 * scaleLoss < outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sourceDelta sigma : ℝ}, 0 < sourceDelta → sourceDelta ≤ delta₀ →
        ∀ {Lplane Lslope : NNReal}
          {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
          {sourceShading : WZ1PaperTubeShading sourceFamily}
          {sourceExtremal : WZ2PaperCroppedIsExtremal
            sigma sourceLoss sourceFamily sourceShading}
          {sourceLine : WZ1PaperIsLineClass sourceFamily}
          {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
          {sourceMidpoint : ∀ index,
            ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
          {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
            Lplane Lslope 1}
          {hscale : 1 ≤ proposition63M9PowerScale sourceDelta scaleLoss}
          {hscaleDeltaSmall : proposition63M9PowerScale sourceDelta scaleLoss *
            sourceDelta ≤ 1 / 1000}
          {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
          (sourceData : Proposition63M9MildRescalingSourceData sourceShading
            sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain
            hscale
            hscaleDeltaSmall levelCount sourceOutputConstant)
          {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
            (fine := sourceData.selected.family) scheduleConstant
            scheduleWindowConstant levelCount}
          (targetData : Proposition63M9MildRescalingQuotientTargetData
            sourceData sourceSchedule),
          targetData.selectionLoss *
              Kakeya.realRpowENN
                (proposition63M9PowerScale sourceDelta scaleLoss * sourceDelta)
                outputLoss ≤
            ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
              ENNReal.ofReal (proposition63M9PowerScale sourceDelta scaleLoss)) *
              ((1 / 2 : ENNReal) * sourceData.sourceDensity) := by
  let normalization : ENNReal :=
    ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
      ((1 / 2 : ENNReal) * ENNReal.ofReal (1 / 2000000 : ℝ)))⁻¹
  let coefficient := normalization *
    proposition63M9PowerSelectionCoefficient levelCount
  have coefficientTop : coefficient ≠ ⊤ := by
    dsimp only [coefficient, normalization]
    apply ENNReal.mul_ne_top
    · apply ENNReal.inv_ne_top.mpr
      apply mul_ne_zero
      · exact ENNReal.inv_ne_zero.mpr <|
          ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top
      · apply mul_ne_zero (by norm_num)
        exact (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
    · dsimp only [proposition63M9PowerSelectionCoefficient]
      finiteness
  have gapPos : 0 < outputLoss - sourceLoss - 8 * scaleLoss := by linarith
  have exponentPos : 0 < 2 * levelCount + 3 := by omega
  rcases Kakeya.Assouad.exists_delta_C_pow_log_absorbed_ennreal
      coefficient coefficientTop proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg gapPos exponentPos with
    ⟨delta₀, delta₀Pos, delta₀One, absorb⟩
  refine ⟨delta₀, delta₀Pos, delta₀One, ?_⟩
  intro sourceDelta sigma deltaPos deltaLe Lplane Lslope sourceFamily
    sourceShading sourceExtremal sourceLine sourceDistinct sourceMidpoint
    preGrain hscale hscaleDeltaSmall sourceOutputConstant scheduleConstant
    scheduleWindowConstant sourceData sourceSchedule targetData
  let scale := proposition63M9PowerScale sourceDelta scaleLoss
  have scaleOne : 1 ≤ scale := proposition63M9PowerScale_one_le deltaPos
    (deltaLe.trans delta₀One) scaleLossNonneg
  have selectionBound := targetData.selectionLoss_le_rootEnvelope sourceData
  have selectionPower := proposition63M9SelectionCoefficient_le_power
    levelCount scaleOne
  have normalizationEq := proposition63M9NormalizationFixed_eq_power scaleOne
  have scaleOutputLe :
      ENNReal.ofReal (Real.rpow scale outputLoss) ≤ ENNReal.ofReal scale := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_self_of_one_le scaleOne (by linarith)
  have scaleEight :
      ENNReal.ofReal (scale ^ 2) * ENNReal.ofReal (scale ^ 5) *
          ENNReal.ofReal scale ≤ ENNReal.ofReal (scale ^ 8) := by
    rw [← ENNReal.ofReal_mul (pow_nonneg (zero_le_one.trans scaleOne) 2),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ scale ^ 2 * scale ^ 5)]
    apply ENNReal.ofReal_mono
    ring_nf
    exact le_rfl
  have scalePow : ENNReal.ofReal (scale ^ 8) =
      Kakeya.realRpowENN sourceDelta (-(8 : ℝ) * scaleLoss) :=
    proposition63M9PowerScale_ennreal_pow deltaPos 8
  have logAbsorb := absorb sourceDelta deltaPos deltaLe
  have targetScalePower :
      Kakeya.realRpowENN (scale * sourceDelta) outputLoss =
        ENNReal.ofReal (Real.rpow scale outputLoss) *
          Kakeya.realRpowENN sourceDelta outputLoss :=
    Kakeya.Assouad.realRpowENN_mul (zero_lt_one.trans_le scaleOne)
      deltaPos outputLoss
  change targetData.selectionLoss *
      Kakeya.realRpowENN (scale * sourceDelta) outputLoss ≤
    ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
      ENNReal.ofReal scale) * ((1 / 2 : ENNReal) * sourceData.sourceDensity)
  rw [sourceData.sourceDensity_eq, targetScalePower]
  let densityCoefficient : ENNReal :=
    ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
      ENNReal.ofReal scale) *
      ((1 / 2 : ENNReal) *
        ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3))
  have densityZero : densityCoefficient ≠ 0 := by
    dsimp only [densityCoefficient]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact ENNReal.inv_ne_zero.mpr <|
          ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top
      · exact (ENNReal.ofReal_pos.mpr <| zero_lt_one.trans_le scaleOne).ne'
    · apply mul_ne_zero (by norm_num)
      exact (ENNReal.ofReal_pos.mpr (by
        have : 0 < (1 / 2000000 : ℝ) / scale ^ 3 := by positivity
        exact this)).ne'
  have densityTop : densityCoefficient ≠ ⊤ := by
    dsimp only [densityCoefficient]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.inv_ne_top.mpr <| mul_ne_zero (by norm_num)
          (zero_lt_one.trans_le one_le_deltaTubeVolume_one).ne')
        ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
  rw [show
      (55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ * ENNReal.ofReal scale *
          (1 / 2 * (ENNReal.ofReal
            ((1 / 2000000 : ℝ) / proposition63M9PowerScale
              sourceDelta scaleLoss ^ 3) *
            Kakeya.realRpowENN sourceDelta sourceLoss)) =
        densityCoefficient * Kakeya.realRpowENN sourceDelta sourceLoss by
      dsimp only [densityCoefficient, scale]
      ring]
  apply (ENNReal.inv_mul_le_iff densityZero densityTop).mp
  have densityInv : densityCoefficient⁻¹ =
      normalization * ENNReal.ofReal (scale ^ 2) := by
    dsimp only [densityCoefficient, normalization]
    exact normalizationEq
  rw [densityInv]
  calc
    (normalization * ENNReal.ofReal (scale ^ 2)) *
          (targetData.selectionLoss *
            (ENNReal.ofReal (Real.rpow scale outputLoss) *
              Kakeya.realRpowENN sourceDelta outputLoss)) ≤
        (normalization * ENNReal.ofReal (scale ^ 2)) *
          ((proposition63M9SelectionCoefficient scale levelCount *
              proposition63OneScaleLogEnvelope sourceDelta ^
                (2 * levelCount + 3)) *
            (ENNReal.ofReal (Real.rpow scale outputLoss) *
              Kakeya.realRpowENN sourceDelta outputLoss)) := by
      gcongr
    _ ≤ (normalization * ENNReal.ofReal (scale ^ 2)) *
          ((proposition63M9PowerSelectionCoefficient levelCount *
              ENNReal.ofReal (scale ^ 5) *
              proposition63OneScaleLogEnvelope sourceDelta ^
                (2 * levelCount + 3)) *
            (ENNReal.ofReal scale *
              Kakeya.realRpowENN sourceDelta outputLoss)) := by
      gcongr
    _ ≤ (coefficient * ENNReal.ofReal (scale ^ 8)) *
          proposition63OneScaleLogEnvelope sourceDelta ^
            (2 * levelCount + 3) *
          Kakeya.realRpowENN sourceDelta outputLoss := by
      dsimp only [coefficient]
      calc
        _ = (normalization *
              proposition63M9PowerSelectionCoefficient levelCount) *
            (ENNReal.ofReal (scale ^ 2) * ENNReal.ofReal (scale ^ 5) *
              ENNReal.ofReal scale) *
            proposition63OneScaleLogEnvelope sourceDelta ^
              (2 * levelCount + 3) *
            Kakeya.realRpowENN sourceDelta outputLoss := by ac_rfl
        _ ≤ _ := by gcongr
    _ = (coefficient * proposition63OneScaleLogEnvelope sourceDelta ^
            (2 * levelCount + 3)) *
          (Kakeya.realRpowENN sourceDelta (-(8 * scaleLoss)) *
            Kakeya.realRpowENN sourceDelta outputLoss) := by
      rw [scalePow]
      norm_num
      ac_rfl
    _ ≤ Kakeya.realRpowENN sourceDelta
          (-(outputLoss - sourceLoss - 8 * scaleLoss)) *
          (Kakeya.realRpowENN sourceDelta (-(8 * scaleLoss)) *
            Kakeya.realRpowENN sourceDelta outputLoss) := by
      gcongr
      simpa only [proposition63OneScaleLogEnvelope] using logAbsorb
    _ = Kakeya.realRpowENN sourceDelta sourceLoss := by
      rw [← Kakeya.Assouad.realRpowENN_add deltaPos,
        ← Kakeya.Assouad.realRpowENN_add deltaPos]
      congr 1
      ring

/-- Runtime power-scale tail assembly from explicit source-output and
nearby-window receipts.  This is the same-target core used by the fully
pre-runtime cutoff below. -/
theorem exists_proposition63_m9_power_robust_quotient_tail_cutoff_of_source_receipts
    (sourceLoss outputLoss scaleLoss : ℝ) (levelCount : ℕ)
    (sourceLossPos : 0 < sourceLoss) (scaleLossNonneg : 0 ≤ scaleLoss)
    (outputLossOne : outputLoss ≤ 1)
    (hloss : 18 * sourceLoss + 12 * scaleLoss < outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sourceDelta sigma : ℝ}, 0 < sourceDelta → sourceDelta ≤ delta₀ →
        ∀ {Lplane Lslope : NNReal}
          {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
          {sourceShading : WZ1PaperTubeShading sourceFamily}
          {sourceExtremal : WZ2PaperCroppedIsExtremal
            sigma sourceLoss sourceFamily sourceShading}
          {sourceLine : WZ1PaperIsLineClass sourceFamily}
          {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
          {sourceMidpoint : ∀ index,
            ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
          {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
            Lplane Lslope 1}
          {hscale : 1 ≤ proposition63M9PowerScale sourceDelta scaleLoss}
          {hscaleDeltaSmall : proposition63M9PowerScale sourceDelta scaleLoss *
            sourceDelta ≤ 1 / 1000}
          {sourceOutputConstant : ENNReal}
          (sourceData : Proposition63M9MildRescalingSourceData sourceShading
            sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain
            hscale hscaleDeltaSmall levelCount sourceOutputConstant)
          (sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
            (fine := sourceData.selected.family) sourceOutputConstant
            (Kakeya.realRpowENN sourceDelta (-(8 * sourceLoss))) levelCount)
          (targetData : Proposition63M9MildRescalingQuotientTargetData
            sourceData sourceSchedule),
          sourceOutputConstant ≤
            Kakeya.realRpowENN sourceDelta (-(4 * sourceLoss)) →
          Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
              (Kakeya.realRpowENN sourceDelta (-(8 * sourceLoss))) ≤
            Kakeya.realRpowENN sourceDelta (-(9 * sourceLoss)) →
          (Lplane : ℝ) ≤ proposition63M9PowerScale sourceDelta scaleLoss →
          (Lslope : ℝ) ≤ proposition63M9PowerScale sourceDelta scaleLoss →
          0 < sigma → sigma < 1 →
          Nonempty (Proposition63M9RobustQuotientTailCertificates
            (outputLoss := outputLoss) targetData) := by
  have densityGap : sourceLoss + 8 * scaleLoss < outputLoss := by
    nlinarith
  rcases exists_proposition63_m9_power_target_envelope_cutoff sourceLoss
      outputLoss scaleLoss levelCount sourceLossPos scaleLossNonneg
      outputLossOne hloss with
    ⟨targetCutoff, targetCutoffPos, targetCutoffOne, targetBound⟩
  rcases exists_proposition63_m9_power_density_cutoff sourceLoss outputLoss
      scaleLoss levelCount sourceLossPos scaleLossNonneg outputLossOne
      densityGap with
    ⟨densityCutoff, densityCutoffPos, densityCutoffOne, densityBound⟩
  let delta₀ := min targetCutoff densityCutoff
  refine ⟨delta₀, lt_min targetCutoffPos densityCutoffPos,
    (min_le_left _ _).trans targetCutoffOne, ?_⟩
  intro sourceDelta sigma deltaPos deltaLe Lplane Lslope sourceFamily
    sourceShading sourceExtremal sourceLine sourceDistinct sourceMidpoint
    preGrain hscale hscaleDeltaSmall sourceOutputConstant sourceData
    sourceSchedule targetData houtput hwindow planeScale slopeScale
    sigmaPos sigmaOne
  have deltaOne : sourceDelta ≤ 1 :=
    deltaLe.trans ((min_le_left _ _).trans targetCutoffOne)
  have targetLe : sourceDelta ≤ targetCutoff := deltaLe.trans (min_le_left _ _)
  have densityLe : sourceDelta ≤ densityCutoff :=
    deltaLe.trans (min_le_right _ _)
  have targetAbsorb := targetBound sourceDelta deltaPos targetLe
  have densityAbsorb := densityBound deltaPos densityLe sourceData targetData
  have sourceLossLt : sourceLoss < outputLoss := by nlinarith
  exact ⟨targetData.robustCertificates sourceLossPos sourceLossLt houtput
    hwindow targetAbsorb densityAbsorb
    (proposition63M9PowerScale_volume_absorb deltaPos deltaOne sigmaPos
      sigmaOne sourceLossPos scaleLossNonneg outputLossOne hloss)
    (proposition63M9PowerScale_ad_absorb deltaPos deltaOne sourceLossPos
      scaleLossNonneg outputLossOne hloss)
    planeScale slopeScale sigmaPos sigmaOne⟩

/-- Fully pre-runtime production cutoff for the power-scale M9 tail.  The
relations exposing the historical four/eight/nine losses are assumptions,
rather than hidden arithmetic in the theorem.  At runtime the caller supplies
only the actual family-free source envelope; both scalar receipts and all
target receipts are then produced for the same dependent `targetData`. -/
theorem exists_proposition63_m9_power_robust_quotient_tail_cutoff
    (coefficient : ENNReal) (logPower levelCount : ℕ)
    (sourceLoss scaleLoss outputLoss outputExponent windowLoss windowGap : ℝ)
    (coefficientTop : coefficient ≠ ⊤)
    (sourceLossPos : 0 < sourceLoss) (scaleLossNonneg : 0 ≤ scaleLoss)
    (outputLossOne : outputLoss ≤ 1)
    (outputExponentEq : outputExponent = 4 * sourceLoss)
    (windowLossEq : windowLoss = 8 * sourceLoss)
    (windowGapEq : windowGap = sourceLoss)
    (sourceGap : 3 * sourceLoss + 3 * scaleLoss < outputExponent)
    (hloss : 18 * sourceLoss + 12 * scaleLoss < outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sourceDelta sigma : ℝ}, 0 < sourceDelta → sourceDelta ≤ delta₀ →
        ∀ {Lplane Lslope : NNReal}
          {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
          {sourceShading : WZ1PaperTubeShading sourceFamily}
          {sourceExtremal : WZ2PaperCroppedIsExtremal
            sigma sourceLoss sourceFamily sourceShading}
          {sourceLine : WZ1PaperIsLineClass sourceFamily}
          {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
          {sourceMidpoint : ∀ index,
            ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
          {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
            Lplane Lslope 1}
          {hscale : 1 ≤ proposition63M9PowerScale sourceDelta scaleLoss}
          {hscaleDeltaSmall : proposition63M9PowerScale sourceDelta scaleLoss *
            sourceDelta ≤ 1 / 1000}
          {sourceOutputConstant : ENNReal}
          (sourceData : Proposition63M9MildRescalingSourceData sourceShading
            sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain
            hscale hscaleDeltaSmall levelCount sourceOutputConstant)
          (sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
            (fine := sourceData.selected.family) sourceOutputConstant
            (Kakeya.realRpowENN sourceDelta (-(8 * sourceLoss))) levelCount)
          (targetData : Proposition63M9MildRescalingQuotientTargetData
            sourceData sourceSchedule),
          sourceOutputConstant ≤
              coefficient * proposition63OneScaleLogEnvelope sourceDelta ^
                logPower *
                ENNReal.ofReal
                  (proposition63M9PowerScale sourceDelta scaleLoss ^ 3) *
                Kakeya.realRpowENN sourceDelta (-(3 * sourceLoss)) →
          (Lplane : ℝ) ≤ proposition63M9PowerScale sourceDelta scaleLoss →
          (Lslope : ℝ) ≤ proposition63M9PowerScale sourceDelta scaleLoss →
          0 < sigma → sigma < 1 →
          Nonempty (Proposition63M9RobustQuotientTailCertificates
            (outputLoss := outputLoss) targetData) := by
  have windowLossPos : 0 < windowLoss := by
    rw [windowLossEq]
    positivity
  have windowGapPos : 0 < windowGap := by
    rw [windowGapEq]
    exact sourceLossPos
  rcases exists_proposition63_m9_power_source_output_cutoff coefficient
      logPower sourceLoss scaleLoss outputExponent coefficientTop sourceGap with
    ⟨sourceCutoff, sourceCutoffPos, sourceCutoffOne, sourceBound⟩
  rcases exists_proposition63_m9_quotient_window_cutoff windowLoss windowGap
      windowLossPos windowGapPos with
    ⟨windowCutoff, windowCutoffPos, windowCutoffOne, windowBound⟩
  rcases exists_proposition63_m9_power_robust_quotient_tail_cutoff_of_source_receipts
      sourceLoss outputLoss scaleLoss levelCount sourceLossPos scaleLossNonneg
      outputLossOne hloss with
    ⟨tailCutoff, tailCutoffPos, tailCutoffOne, tailBound⟩
  let delta₀ := min sourceCutoff (min windowCutoff tailCutoff)
  refine ⟨delta₀, lt_min sourceCutoffPos (lt_min windowCutoffPos tailCutoffPos),
    (min_le_left _ _).trans sourceCutoffOne, ?_⟩
  intro sourceDelta sigma deltaPos deltaLe Lplane Lslope sourceFamily
    sourceShading sourceExtremal sourceLine sourceDistinct sourceMidpoint
    preGrain hscale hscaleDeltaSmall sourceOutputConstant sourceData
    sourceSchedule targetData sourceEnvelope planeScale slopeScale sigmaPos
    sigmaOne
  have sourceLe : sourceDelta ≤ sourceCutoff :=
    deltaLe.trans (min_le_left _ _)
  have windowLe : sourceDelta ≤ windowCutoff :=
    deltaLe.trans ((min_le_right _ _).trans (min_le_left _ _))
  have tailLe : sourceDelta ≤ tailCutoff :=
    deltaLe.trans ((min_le_right _ _).trans (min_le_right _ _))
  have houtputRaw := sourceEnvelope.trans
    (sourceBound sourceDelta deltaPos sourceLe)
  have houtput : sourceOutputConstant ≤
      Kakeya.realRpowENN sourceDelta (-(4 * sourceLoss)) := by
    simpa only [outputExponentEq] using houtputRaw
  have hwindowRaw := windowBound sourceDelta deltaPos windowLe
  have hwindow :
      Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
          (Kakeya.realRpowENN sourceDelta (-(8 * sourceLoss))) ≤
        Kakeya.realRpowENN sourceDelta (-(9 * sourceLoss)) := by
    have hwindowLoss : -(8 * sourceLoss) = -windowLoss := by
      rw [windowLossEq]
    have hwindowOutput : -(9 * sourceLoss) =
        -(windowLoss + windowGap) := by
      rw [windowLossEq, windowGapEq]
      ring
    simpa only [hwindowLoss, hwindowOutput] using hwindowRaw
  exact tailBound deltaPos tailLe sourceData sourceSchedule targetData houtput
    hwindow planeScale slopeScale sigmaPos sigmaOne

/-- Arithmetic receipt for the production choice
`sourceLoss = 4p`, `scaleLoss = p`, `outputExponent = 16p`, and
`windowLoss = 32p`.  The source envelope costs fifteen powers, while the
target-side power envelope costs eighty-four powers. -/
theorem proposition63_m9_production_power_tail_losses
    {p outputLoss : ℝ} (pPos : 0 < p)
    (targetGap : 84 * p < outputLoss) :
    3 * (4 * p) + 3 * p < 16 * p ∧
      18 * (4 * p) + 12 * p < outputLoss ∧
      32 * p = 8 * (4 * p) := by
  constructor
  · nlinarith
  constructor
  · nlinarith
  · ring

/-- End-to-end power-scale source producer and same-witness quotient-tail
certificate theorem.  Every cutoff is frozen before the runtime family.  The
source output constant, source data, and canonical nearby schedule are then
constructed once, and the conclusion is uniform over targets dependent on
those exact witnesses. -/
theorem exists_proposition63_m9_power_source_and_robust_tail_cutoff
    (sourceLoss scaleLoss outputLoss outputExponent : ℝ) (levelCount : ℕ)
    (sourceLossPos : 0 < sourceLoss) (scaleLossNonneg : 0 ≤ scaleLoss)
    (scaleLossOne : scaleLoss < 1)
    (levelCountLoss : 1 ≤ (levelCount : ℝ) * sourceLoss)
    (outputExponentEq : outputExponent = 4 * sourceLoss)
    (sourceGap : 3 * sourceLoss + 3 * scaleLoss < outputExponent)
    (outputLossOne : outputLoss ≤ 1)
    (tailGap : 18 * sourceLoss + 12 * scaleLoss < outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sourceDelta sigma : ℝ}, 0 < sourceDelta → sourceDelta ≤ delta₀ →
        ∀ {Lplane Lslope : NNReal}
          {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
          (sourceShading : WZ1PaperTubeShading sourceFamily)
          (sourceExtremal : WZ2PaperCroppedIsExtremal
            sigma sourceLoss sourceFamily sourceShading)
          (sourceLine : WZ1PaperIsLineClass sourceFamily)
          (sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily)
          (sourceMidpoint : ∀ index,
            ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3)
          (preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
            Lplane Lslope 1),
          (Lplane : ℝ) ≤ proposition63M9PowerScale sourceDelta scaleLoss →
          (Lslope : ℝ) ≤ proposition63M9PowerScale sourceDelta scaleLoss →
          0 < sigma → sigma < 1 →
          ∃ hscale : 1 ≤ proposition63M9PowerScale sourceDelta scaleLoss,
          ∃ hscaleDeltaSmall :
              proposition63M9PowerScale sourceDelta scaleLoss * sourceDelta ≤
                1 / 1000,
          ∃ sourceData : Proposition63M9MildRescalingSourceData sourceShading
              sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain
              hscale hscaleDeltaSmall levelCount
              (Kakeya.realRpowENN sourceDelta (-outputExponent)),
          ∃ sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
              (fine := sourceData.selected.family)
              (Kakeya.realRpowENN sourceDelta (-outputExponent))
              (Kakeya.realRpowENN sourceDelta (-(8 * sourceLoss))) levelCount,
            ∀ targetData : Proposition63M9MildRescalingQuotientTargetData
                sourceData sourceSchedule,
              Nonempty (Proposition63M9RobustQuotientTailCertificates
                (outputLoss := outputLoss) targetData) := by
  have sourceWindow : 2 * sourceLoss ≤ outputExponent := by
    rw [outputExponentEq]
    linarith
  rcases exists_proposition63_m9_power_source_certificates_cutoff sourceLoss
      scaleLoss outputExponent levelCount sourceLossPos scaleLossNonneg
      scaleLossOne levelCountLoss sourceWindow sourceGap with
    ⟨sourceCutoff, sourceCutoffPos, sourceCutoffOne, sourceCertificates⟩
  rcases exists_proposition63_m9_quotient_window_cutoff
      (8 * sourceLoss) sourceLoss (by positivity) sourceLossPos with
    ⟨windowCutoff, windowCutoffPos, windowCutoffOne, windowBound⟩
  rcases exists_proposition63_m9_power_robust_quotient_tail_cutoff_of_source_receipts
      sourceLoss outputLoss scaleLoss levelCount sourceLossPos scaleLossNonneg
      outputLossOne tailGap with
    ⟨tailCutoff, tailCutoffPos, tailCutoffOne, tailBound⟩
  let delta₀ := min sourceCutoff (min windowCutoff tailCutoff)
  have delta₀Pos : 0 < delta₀ :=
    lt_min sourceCutoffPos (lt_min windowCutoffPos tailCutoffPos)
  have delta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans sourceCutoffOne
  refine ⟨delta₀, delta₀Pos, delta₀One, ?_⟩
  intro sourceDelta sigma deltaPos deltaLe Lplane Lslope sourceFamily
    sourceShading sourceExtremal sourceLine sourceDistinct sourceMidpoint
    preGrain planeScale slopeScale sigmaPos sigmaOne
  have sourceLe : sourceDelta ≤ sourceCutoff :=
    deltaLe.trans (min_le_left _ _)
  have windowLe : sourceDelta ≤ windowCutoff :=
    deltaLe.trans ((min_le_right _ _).trans (min_le_left _ _))
  have tailLe : sourceDelta ≤ tailCutoff :=
    deltaLe.trans ((min_le_right _ _).trans (min_le_right _ _))
  rcases sourceCertificates deltaPos sourceLe sourceExtremal sourceMidpoint with
    ⟨hscale, certificates⟩
  rcases proposition63_m9_robust_tail_source sourceShading sourceExtremal
      sourceLine sourceDistinct sourceMidpoint preGrain hscale levelCount
      (Kakeya.realRpowENN sourceDelta (-outputExponent)) certificates with
    ⟨sourceData⟩
  have outputSquare :
      Kakeya.realRpowENN sourceDelta (-outputExponent) *
          Kakeya.realRpowENN sourceDelta (-outputExponent) ≤
        Kakeya.realRpowENN sourceDelta (-(8 * sourceLoss)) := by
    rw [← Kakeya.Assouad.realRpowENN_add deltaPos]
    rw [outputExponentEq]
    ring_nf
    exact le_rfl
  have ambientOne : (1 : ENNReal) ≤
      Kakeya.realRpowENN sourceDelta (-sourceLoss) :=
    (by norm_num : (1 : ENNReal) < 2).le.trans certificates.ambient_two.le
  have ambientLeOutput :
      Kakeya.realRpowENN sourceDelta (-sourceLoss) ≤
        Kakeya.realRpowENN sourceDelta (-outputExponent) := by
    calc
      _ ≤ Kakeya.realRpowENN sourceDelta (-sourceLoss) *
          Kakeya.realRpowENN sourceDelta (-sourceLoss) :=
        le_mul_of_one_le_right' ambientOne
      _ ≤ _ := certificates.output_window
  have outputTwo : (2 : ENNReal) <
      Kakeya.realRpowENN sourceDelta (-outputExponent) :=
    certificates.ambient_two.trans_le ambientLeOutput
  have outputLevels : ENNReal.ofReal (1 / sourceDelta) ≤
      Kakeya.realRpowENN sourceDelta (-outputExponent) ^ levelCount :=
    certificates.levels.trans (pow_le_pow_left' ambientLeOutput _)
  rcases sourceData.canonicalNearbySchedule outputTwo outputLevels
      outputSquare with ⟨sourceSchedule⟩
  refine ⟨hscale, certificates.scale_delta_small, sourceData, sourceSchedule, ?_⟩
  intro targetData
  have houtput : Kakeya.realRpowENN sourceDelta (-outputExponent) ≤
      Kakeya.realRpowENN sourceDelta (-(4 * sourceLoss)) := by
    rw [outputExponentEq]
  have hwindowRaw := windowBound sourceDelta deltaPos windowLe
  have hwindow :
      Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
          (Kakeya.realRpowENN sourceDelta (-(8 * sourceLoss))) ≤
        Kakeya.realRpowENN sourceDelta (-(9 * sourceLoss)) := by
    simpa only [show -(8 * sourceLoss + sourceLoss) =
      -(9 * sourceLoss) by ring] using hwindowRaw
  exact tailBound deltaPos tailLe sourceData sourceSchedule targetData houtput
    hwindow planeScale slopeScale sigmaPos sigmaOne

end Kakeya.Assouad.PureWZ2

end
