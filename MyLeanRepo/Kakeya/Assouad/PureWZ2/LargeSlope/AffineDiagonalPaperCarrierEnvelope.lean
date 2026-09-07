import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalGeometryBounds
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.VariableJohnHomotheticEnvelope
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoverCarrierContainment

/-!
# Full cropped-carrier envelope under the fixed paper diagonal

The target tube is localized on the exact affine image line.  The complete
source cropped carrier is not claimed to lie in the target cropped carrier.
Instead its affine image lies in a controlled homothety of that carrier.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

theorem pureWZ2_point_norm_le_two_of_mem_axisBox
    {point : Point3}
    (hpoint : point ∈ Kakeya.Streamlined.axisBox 2 2 2) :
    ‖point‖ ≤ 2 := by
  have h0 : |point 0| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpoint.1
  have h1 : |point 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpoint.2.1
  have h2 : |point 2| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpoint.2.2
  have hsq := point3_coord_norm_sq point
  have h0sq : point 0 ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (point 0)]
  have h1sq : point 1 ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (point 1)]
  have h2sq : point 2 ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (point 2)]
  nlinarith [norm_nonneg point]

theorem pureWZ2_zeroPoint_norm_le_one
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (hline : WZ1PaperTubeInLineClass tube) :
    ‖wz1TubeAxisZeroPoint tube‖ ≤ 1 := by
  let zero := wz1TubeAxisZeroPoint tube
  have hz : zero 2 = 0 :=
    wz1TubeAxisZeroPoint_coord_two tube hline.vertical
  have hxSq : zero 0 ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    nlinarith [sq_abs (zero 0), abs_nonneg (zero 0), hline.2.1]
  have hySq : zero 1 ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    nlinarith [sq_abs (zero 1), abs_nonneg (zero 1), hline.2.2]
  have hnorm := point3_coord_norm_sq zero
  nlinarith [norm_nonneg zero]

/-- The full source cropped carrier maps into a controlled target homothety.
The homothety center is the target axis point at height zero, not an arbitrary
unit-segment midpoint. -/
theorem pureWZ2_affineDiagonal_paperCarrier_image_subset_homothety
    {sourceDelta targetDelta : ℝ}
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hheight : 100 ≤ heightScale)
    (htransverse : 0 < transverseScale)
    (htransverseOne : transverseScale ≤ 1)
    (hcenter : ‖center‖ ≤ 2)
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : targetDelta = 2 * heightScale * sourceDelta)
    (source : Kakeya.DeltaTube sourceDelta)
    (target : Kakeya.DeltaTube targetDelta)
    (htargetLine : WZ1PaperTubeInLineClass target)
    (haxis : tubeAxisLine target =
      pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale 1 '' tubeAxisLine source) :
    pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale 1 '' wz1PaperTubeCarrier source ⊆
      AffineMap.homothety (wz1TubeAxisZeroPoint target)
        (8 * heightScale) '' wz1PaperTubeCarrier target := by
  rintro imagePoint ⟨sourcePoint, hsourcePoint, rfl⟩
  let affinePoint := pureWZ2AffineDiagonalMapCentered frameSlope center
    heightScale transverseScale 1 sourcePoint
  let targetZero := wz1TubeAxisZeroPoint target
  let factor := 8 * heightScale
  let contractedPoint :=
    targetZero + factor⁻¹ • (affinePoint - targetZero)
  have hheightPos : 0 < heightScale := by linarith
  have hfactorPos : 0 < factor := by dsimp only [factor]; positivity
  have hfactorOne : 1 ≤ factor := by
    dsimp only [factor]
    linarith
  have hsourceNorm : ‖sourcePoint‖ ≤ 2 :=
    pureWZ2_point_norm_le_two_of_mem_axisBox hsourcePoint.2
  have hsourceCenter : ‖sourcePoint - center‖ ≤ 4 := by
    calc
      ‖sourcePoint - center‖ ≤ ‖sourcePoint‖ + ‖center‖ := norm_sub_le _ _
      _ ≤ 4 := by linarith
  have haffineNorm : ‖affinePoint‖ ≤ 4 * heightScale := by
    rw [show affinePoint =
        pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale 1
          (sourcePoint - center) by
      exact pureWZ2AffineDiagonalMapCentered_eq_linear_sub_center
        frameSlope center heightScale transverseScale 1 sourcePoint]
    calc
      ‖pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale 1
          (sourcePoint - center)‖ ≤
          heightScale * ‖sourcePoint - center‖ :=
        pureWZ2AffineDiagonalLinear_norm_le_height frameSlope
          (by linarith) htransverse.le htransverseOne _
      _ ≤ heightScale * 4 := by gcongr
      _ = 4 * heightScale := by ring
  have hzeroNorm : ‖targetZero‖ ≤ 1 :=
    pureWZ2_zeroPoint_norm_le_one htargetLine
  have hcontractedDifference :
      ‖contractedPoint - targetZero‖ ≤ 2 / 3 := by
    have hdiff : contractedPoint - targetZero =
        factor⁻¹ • (affinePoint - targetZero) := by
      dsimp only [contractedPoint]
      abel
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hfactorPos)]
    have hraw : ‖affinePoint - targetZero‖ ≤ 4 * heightScale + 1 := by
      exact (norm_sub_le _ _).trans (by linarith)
    rw [show factor⁻¹ * ‖affinePoint - targetZero‖ =
        ‖affinePoint - targetZero‖ / factor by ring]
    apply (div_le_iff₀ hfactorPos).2
    dsimp only [factor]
    nlinarith
  have hcontractedBox :
      contractedPoint ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
    have hcoord : ∀ coordinate : Fin 3,
        |contractedPoint coordinate - targetZero coordinate| ≤ 2 / 3 := by
      intro coordinate
      exact (PiLp.norm_apply_le (contractedPoint - targetZero) coordinate).trans
        hcontractedDifference
    have hzeroTwo : targetZero 2 = 0 :=
      wz1TubeAxisZeroPoint_coord_two target htargetLine.vertical
    simp only [Kakeya.Streamlined.axisBox]
    norm_num
    constructor
    · calc
        |contractedPoint 0| =
            |(contractedPoint 0 - targetZero 0) + targetZero 0| := by ring_nf
        _ ≤ |contractedPoint 0 - targetZero 0| + |targetZero 0| :=
          abs_add_le _ _
        _ ≤ 2 / 3 + 1 / 3 := add_le_add (hcoord 0) htargetLine.2.1
        _ = 1 := by ring
    constructor
    · calc
        |contractedPoint 1| =
            |(contractedPoint 1 - targetZero 1) + targetZero 1| := by ring_nf
        _ ≤ |contractedPoint 1 - targetZero 1| + |targetZero 1| :=
          abs_add_le _ _
        _ ≤ 2 / 3 + 1 / 3 := add_le_add (hcoord 1) htargetLine.2.2
        _ = 1 := by ring
    · rw [show contractedPoint 2 =
          contractedPoint 2 - targetZero 2 by rw [hzeroTwo, sub_zero]]
      exact (hcoord 2).trans (by norm_num)
  have hsourceAxisClosed := isClosed_tubeAxisLine source
  rcases exists_dist_le_of_mem_cthickening_closed hsourceAxisClosed
      (by positivity : 0 ≤ 6 * sourceDelta) hsourcePoint.1 with
    ⟨sourceAxisPoint, hsourceAxisPoint, hsourceDistance⟩
  let targetAxisPoint := pureWZ2AffineDiagonalMapCentered frameSlope center
    heightScale transverseScale 1 sourceAxisPoint
  have htargetAxisPoint : targetAxisPoint ∈ tubeAxisLine target := by
    rw [haxis]
    exact ⟨sourceAxisPoint, hsourceAxisPoint, rfl⟩
  let contractedAxisPoint :=
    targetZero + factor⁻¹ • (targetAxisPoint - targetZero)
  have hcontractedAxis : contractedAxisPoint ∈ tubeAxisLine target := by
    have hzeroAxis : targetZero ∈ tubeAxisLine target :=
      wz1TubeAxisZeroPoint_mem_axis target
    have hcoeff : factor⁻¹ ≤ 1 := by
      exact (inv_le_one₀ hfactorPos).2 hfactorOne
    have hconvex := convex_tubeAxisLine target
    have hsum : 1 - factor⁻¹ + factor⁻¹ = 1 := by ring
    have hcombination := hconvex hzeroAxis htargetAxisPoint
      (sub_nonneg.mpr hcoeff) (inv_nonneg.mpr hfactorPos.le)
      hsum
    convert hcombination using 1 <;> dsimp only [contractedAxisPoint] <;> module
  have hcontractedDistance :
      dist contractedPoint contractedAxisPoint ≤ 6 * targetDelta := by
    rw [dist_eq_norm]
    have hvector : contractedPoint - contractedAxisPoint =
        factor⁻¹ • (affinePoint - targetAxisPoint) := by
      dsimp only [contractedPoint, contractedAxisPoint]
      module
    rw [hvector, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hfactorPos)]
    have himageDistance : ‖affinePoint - targetAxisPoint‖ ≤
        heightScale * (6 * sourceDelta) := by
      have hvectorImage : affinePoint - targetAxisPoint =
          pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale 1
            (sourcePoint - sourceAxisPoint) := by
        dsimp only [affinePoint, targetAxisPoint]
        exact pureWZ2AffineDiagonalMapCentered_sub _ _ _ _ _ _ _
      rw [hvectorImage]
      exact (pureWZ2AffineDiagonalLinear_norm_le_height frameSlope
        (by linarith) htransverse.le htransverseOne _).trans (by
          gcongr
          simpa [dist_eq_norm] using hsourceDistance)
    rw [show factor⁻¹ * ‖affinePoint - targetAxisPoint‖ =
        ‖affinePoint - targetAxisPoint‖ / factor by ring]
    calc
      ‖affinePoint - targetAxisPoint‖ / factor ≤
          (heightScale * (6 * sourceDelta)) / factor := by gcongr
      _ = (3 / 4 : ℝ) * sourceDelta := by
        dsimp only [factor]
        field_simp [hheightPos.ne']
        ring
      _ ≤ 6 * targetDelta := by
        rw [htargetDelta]
        nlinarith [mul_pos hheightPos hsourceDelta]
  have hcontractedCarrier : contractedPoint ∈ wz1PaperTubeCarrier target :=
    ⟨Metric.mem_cthickening_of_dist_le contractedPoint contractedAxisPoint
      (6 * targetDelta) _ hcontractedAxis hcontractedDistance, hcontractedBox⟩
  refine ⟨contractedPoint, hcontractedCarrier, ?_⟩
  change factor • (contractedPoint - targetZero) + targetZero = affinePoint
  have hdiff : contractedPoint - targetZero =
      factor⁻¹ • (affinePoint - targetZero) := by
    dsimp only [contractedPoint]
    abel
  have hcancel : factor * factor⁻¹ = 1 :=
    mul_inv_cancel₀ hfactorPos.ne'
  rw [hdiff, smul_smul, hcancel, one_smul]
  abel

end Kakeya.Assouad

end
