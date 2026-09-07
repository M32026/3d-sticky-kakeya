import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalGeometryBounds

/-!
# Ordinary carrier envelope under the fixed affine diagonal map

The image of the source unit segment is generally longer than one.  The
midpoint-rebased public target retains its middle unit segment.  Contracting
the full affine image about the common midpoint by the height factor puts it
inside the public target carrier.  Equivalently, the complete source carrier
image lies in one controlled homothety of the target ordinary carrier.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

theorem pureWZ2_affineDiagonal_ordinaryCarrier_image_subset_homothety
    {sourceDelta targetDelta : ℝ}
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hheight : 1 ≤ heightScale)
    (htransverse : 0 < transverseScale)
    (htransverseOne : transverseScale ≤ 1)
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : sourceDelta ≤ targetDelta)
    (source : Kakeya.DeltaTube sourceDelta) :
    let target : Kakeya.DeltaTube targetDelta :=
      pureWZ2AffineDiagonalPublicTube frameSlope center heightScale
        transverseScale 1 source (by linarith) htransverse.ne' one_ne_zero
    pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale 1 '' source.carrier ⊆
      AffineMap.homothety (wz2PaperTubeMidpoint target) heightScale ''
        target.carrier := by
  dsimp only
  let target : Kakeya.DeltaTube targetDelta :=
    pureWZ2AffineDiagonalPublicTube frameSlope center heightScale
      transverseScale 1 source (by linarith) htransverse.ne' one_ne_zero
  let sourceMidpoint := wz2PaperTubeMidpoint source
  let targetMidpoint := wz2PaperTubeMidpoint target
  let imageDirection := pureWZ2AffineDiagonalLinear frameSlope heightScale
    transverseScale 1 source.direction
  let imageLength := ‖imageDirection‖
  let targetDirection := imageLength⁻¹ • imageDirection
  have hheightPos : 0 < heightScale := by linarith
  have himageDirection : imageDirection ≠ 0 := by
    intro hzero
    have hinverse := pureWZ2AffineDiagonalLinearInverse_linear frameSlope
      (by linarith : heightScale ≠ 0) htransverse.ne' one_ne_zero
      source.direction
    rw [show pureWZ2AffineDiagonalLinear frameSlope heightScale
      transverseScale 1 source.direction = imageDirection by rfl, hzero] at hinverse
    have hinverseZero :
        pureWZ2AffineDiagonalLinearInverse frameSlope heightScale
          transverseScale 1 0 = 0 := by
      simp [pureWZ2AffineDiagonalLinearInverse, point3]
    rw [hinverseZero] at hinverse
    have hsourceDirection : source.direction ≠ 0 := by
      intro hsourceZero
      have := congrArg norm hsourceZero
      rw [source.direction_unit, norm_zero] at this
      norm_num at this
    exact hsourceDirection hinverse.symm
  have himageLengthPos : 0 < imageLength :=
    norm_pos_iff.mpr himageDirection
  have himageLengthLe : imageLength ≤ heightScale := by
    dsimp only [imageLength, imageDirection]
    simpa [source.direction_unit] using
      pureWZ2AffineDiagonalLinear_norm_le_height frameSlope hheight
        htransverse.le htransverseOne source.direction
  have htargetDirection : target.direction = targetDirection := rfl
  have htargetMidpoint :
      targetMidpoint =
        pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale 1 sourceMidpoint := by
    exact pureWZ2AffineDiagonalPublicTube_midpoint frameSlope center source
      (by linarith) htransverse.ne' one_ne_zero
  rintro imagePoint ⟨sourcePoint, hsourcePoint, rfl⟩
  rcases exists_closest_on_axis hsourceDelta.le source sourcePoint
      hsourcePoint with ⟨parameter, hparameter, hsourceDistance⟩
  let sourceAxisPoint := source.base + parameter • source.direction
  let imageAxisPoint :=
    pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
      transverseScale 1 sourceAxisPoint
  let contractedPoint := targetMidpoint + heightScale⁻¹ •
    (pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
      transverseScale 1 sourcePoint - targetMidpoint)
  let contractedAxisPoint := targetMidpoint + heightScale⁻¹ •
    (imageAxisPoint - targetMidpoint)
  have himageAxis :
      imageAxisPoint = targetMidpoint +
        (parameter - 1 / 2) • imageDirection := by
    dsimp only [imageAxisPoint, sourceAxisPoint]
    rw [htargetMidpoint]
    have hsourceAxis :
        source.base + parameter • source.direction =
          sourceMidpoint + (parameter - 1 / 2) • source.direction := by
      dsimp only [sourceMidpoint, wz2PaperTubeMidpoint]
      module
    rw [hsourceAxis,
      pureWZ2AffineDiagonalMapCentered_add_smul]
  have hcontractedAxis : contractedAxisPoint ∈
      Kakeya.unitSegment target.base target.direction := by
    let targetParameter : ℝ :=
      1 / 2 + (parameter - 1 / 2) * imageLength / heightScale
    have hratio : 0 ≤ imageLength / heightScale ∧
        imageLength / heightScale ≤ 1 := by
      constructor
      · positivity
      · exact (div_le_one hheightPos).2 himageLengthLe
    have htargetParameter : targetParameter ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp only [targetParameter]
      by_cases hparameterMid : 1 / 2 ≤ parameter
      · have hproductNonneg :
            0 ≤ (parameter - 1 / 2) * (imageLength / heightScale) :=
          mul_nonneg (by linarith) hratio.1
        have hproductLe :
            (parameter - 1 / 2) * (imageLength / heightScale) ≤
              parameter - 1 / 2 := by
          simpa using mul_le_mul_of_nonneg_left hratio.2
            (by linarith : 0 ≤ parameter - 1 / 2)
        constructor
        · exact add_nonneg (by norm_num)
            (by simpa [div_eq_mul_inv, mul_assoc] using hproductNonneg)
        · calc
            1 / 2 + (parameter - 1 / 2) * imageLength / heightScale =
                1 / 2 +
                  (parameter - 1 / 2) * (imageLength / heightScale) := by ring
            _ ≤ 1 / 2 + (parameter - 1 / 2) := by gcongr
            _ = parameter := by ring
            _ ≤ 1 := hparameter.2
      · have hparameterMid' : parameter - 1 / 2 ≤ 0 := by linarith
        have hproductNonpos :
            (parameter - 1 / 2) * (imageLength / heightScale) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hparameterMid' hratio.1
        have hproductGe :
            parameter - 1 / 2 ≤
              (parameter - 1 / 2) * (imageLength / heightScale) := by
          have := mul_le_mul_of_nonpos_left hratio.2 hparameterMid'
          simpa using this
        constructor
        · calc
            0 ≤ parameter := hparameter.1
            _ = 1 / 2 + (parameter - 1 / 2) := by ring
            _ ≤ 1 / 2 +
                (parameter - 1 / 2) * (imageLength / heightScale) := by
                  gcongr
            _ = 1 / 2 +
                (parameter - 1 / 2) * imageLength / heightScale := by ring
        · calc
            1 / 2 + (parameter - 1 / 2) * imageLength / heightScale =
                1 / 2 +
                  (parameter - 1 / 2) * (imageLength / heightScale) := by ring
            _ ≤ 1 / 2 := by linarith
            _ ≤ 1 := by norm_num
    refine ⟨targetParameter, htargetParameter, ?_⟩
    rw [htargetDirection]
    have himageDirectionEq :
        imageDirection = imageLength • targetDirection := by
      dsimp only [targetDirection]
      rw [smul_smul]
      have hcancel : imageLength * imageLength⁻¹ = 1 :=
        mul_inv_cancel₀ himageLengthPos.ne'
      rw [hcancel, one_smul]
    have htargetBase :
        target.base = targetMidpoint - (1 / 2 : ℝ) • targetDirection := by
      rw [htargetMidpoint]
      dsimp only [target, targetDirection, imageLength, imageDirection,
        pureWZ2AffineDiagonalPublicTube,
        pureWZ2AffineDiagonalDirection]
    have hcontractedAxisEq :
        contractedAxisPoint = targetMidpoint +
          ((parameter - 1 / 2) * imageLength / heightScale) •
            targetDirection := by
      dsimp only [contractedAxisPoint]
      rw [himageAxis]
      rw [show
        targetMidpoint + (parameter - 1 / 2) • imageDirection -
            targetMidpoint =
          (parameter - 1 / 2) • imageDirection by abel,
        himageDirectionEq, smul_smul, smul_smul]
      congr 2
      field_simp [hheightPos.ne']
    rw [htargetBase]
    rw [hcontractedAxisEq]
    dsimp only [targetParameter]
    module
  have hcontractedDistance :
      dist contractedPoint contractedAxisPoint ≤ targetDelta := by
    rw [dist_eq_norm]
    have hdifference : contractedPoint - contractedAxisPoint =
        heightScale⁻¹ •
          pureWZ2AffineDiagonalLinear frameSlope heightScale
            transverseScale 1 (sourcePoint - sourceAxisPoint) := by
      dsimp only [contractedPoint, contractedAxisPoint, imageAxisPoint]
      rw [show
        (targetMidpoint + heightScale⁻¹ •
            (pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
              transverseScale 1 sourcePoint - targetMidpoint)) -
          (targetMidpoint + heightScale⁻¹ •
            (pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
              transverseScale 1 sourceAxisPoint - targetMidpoint)) =
        heightScale⁻¹ •
          (pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
              transverseScale 1 sourcePoint -
            pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
              transverseScale 1 sourceAxisPoint) by module]
      rw [pureWZ2AffineDiagonalMapCentered_sub]
    rw [hdifference, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hheightPos)]
    calc
      heightScale⁻¹ *
          ‖pureWZ2AffineDiagonalLinear frameSlope heightScale
            transverseScale 1 (sourcePoint - sourceAxisPoint)‖
          ≤ heightScale⁻¹ *
              (heightScale * ‖sourcePoint - sourceAxisPoint‖) := by
            gcongr
            exact pureWZ2AffineDiagonalLinear_norm_le_height frameSlope
              hheight htransverse.le htransverseOne _
      _ = ‖sourcePoint - sourceAxisPoint‖ := by
            field_simp [hheightPos.ne']
      _ ≤ sourceDelta := by
            simpa [sourceAxisPoint, dist_eq_norm] using hsourceDistance
      _ ≤ targetDelta := htargetDelta
  have hcontractedCarrier : contractedPoint ∈ target.carrier :=
    Metric.mem_cthickening_of_dist_le contractedPoint contractedAxisPoint
      targetDelta _ hcontractedAxis hcontractedDistance
  refine ⟨contractedPoint, hcontractedCarrier, ?_⟩
  change heightScale • (contractedPoint - targetMidpoint) +
      targetMidpoint =
    pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
      transverseScale 1 sourcePoint
  have hcontracted : contractedPoint - targetMidpoint =
      heightScale⁻¹ •
        (pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale 1 sourcePoint - targetMidpoint) := by
    dsimp only [contractedPoint]
    abel
  rw [hcontracted, smul_smul]
  have hcancel : heightScale * heightScale⁻¹ = 1 :=
    mul_inv_cancel₀ hheightPos.ne'
  rw [hcancel, one_smul]
  abel

end Kakeya.Assouad

end
