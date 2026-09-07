import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicPaperTargetTube
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicPaperRetubingGeometry
import MyLeanRepo.Kakeya.Assouad.TubeAlignmentGeometry

/-!
# Ordinary carrier envelope under the exact triangular map

The target segment is centered at the image of the selected slab midpoint,
not at the image of the source tube midpoint.  The localized source-base
bound controls this longitudinal offset.  After contraction by `32 * S`,
where `S = 2 / (d-c)` is the vertical Lipschitz factor, the complete affine
image of the ordinary source tube lies in the canonical target tube.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

theorem anisotropicCenteredRescalingMap_ordinaryCarrier_image_subset_homothety
    {sourceDelta targetDelta : ℝ}
    (g : SlopeFunction) {c d m S : ℝ}
    (hg : g.IsNormalized)
    (hcd : c < d)
    (hdc : d - c ≤ 1 / 25)
    (hm : 0 < m)
    (hmOne : m ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hS : S = 2 / (d - c))
    (center : Point3)
    (source : Kakeya.DeltaTube sourceDelta)
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : S * sourceDelta ≤ targetDelta)
    (hsource : WZ1PaperTubeInLineClass source)
    (hsourceBase : ‖source.base‖ ≤ 5) :
    let target := anisotropicPaperTargetTube
      g c d m center targetDelta hcd hm source
    anisotropicCenteredRescalingMap g c d m center '' source.carrier ⊆
      AffineMap.homothety (wz2PaperTubeMidpoint target) (32 * S) ''
        target.carrier := by
  dsimp only
  let target := anisotropicPaperTargetTube
    g c d m center targetDelta hcd hm source
  let sourceCenter :=
    wz1PaperAxisPointAtHeight source (c + (d - c) / 2)
  let targetMidpoint := wz2PaperTubeMidpoint target
  let imageDirection := dPhiLin g c d m (wz1PaperDirection source)
  let imageLength := ‖imageDirection‖
  let targetDirection := imageLength⁻¹ • imageDirection
  let factor := 32 * S
  have hlength : 0 < d - c := sub_pos.mpr hcd
  have hSPos : 0 < S := by rw [hS]; positivity
  have hfactorPos : 0 < factor := by dsimp only [factor]; positivity
  have himageDirection : imageDirection ≠ 0 := by
    intro hzero
    have hsourceDirection : wz1PaperDirection source ≠ 0 := by
      intro hsourceZero
      have hnorm := congrArg norm hsourceZero
      rw [wz1PaperDirection_norm source, norm_zero] at hnorm
      norm_num at hnorm
    apply hsourceDirection
    apply dPhiLin_injective g c d m hcd hm
    rw [show dPhiLin g c d m (wz1PaperDirection source) =
        imageDirection by rfl, hzero]
    simp [dPhiLin, point3]
  have himageLengthPos : 0 < imageLength :=
    norm_pos_iff.mpr himageDirection
  have hgmid : |g (c + (d - c) / 2)| ≤ 1 :=
    (hg _ (hsub ⟨by linarith, by linarith⟩)).1
  have hKabs : |m * (d - c) / 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have hSTwo : 2 ≤ S := by
    rw [hS]
    apply (le_div_iff₀ hlength).2
    linarith
  have himageRaw :
      ‖dPhiLin g c d m (wz1PaperDirection source)‖ ≤
        S * ‖wz1PaperDirection source‖ := by
    have hdphi : dPhiLin g c d m (wz1PaperDirection source) =
        point3
          ((wz1PaperDirection source) 0 +
            g (c + (d - c) / 2) * (wz1PaperDirection source) 1)
          ((m * (d - c) / 2) * (wz1PaperDirection source) 1)
          (S * (wz1PaperDirection source) 2) := by
      rw [dPhiLin, hS]
    rw [hdphi]
    exact anisotropicMap_opNorm_bound
      hgmid hKabs hSTwo (wz1PaperDirection source)
  have himageLengthLe : imageLength ≤ S := by
    rw [wz1PaperDirection_norm source, mul_one] at himageRaw
    exact himageRaw
  have htargetDirection : target.direction = targetDirection := rfl
  have htargetMidpoint : targetMidpoint =
      anisotropicCenteredRescalingMap g c d m center sourceCenter := by
    dsimp only [targetMidpoint, target, sourceCenter]
    rw [anisotropicPaperTargetTube_midpoint]
    rfl
  have hcenterHeight : |c + (d - c) / 2| ≤ 1 :=
    abs_le.mpr (hsub ⟨by linarith, by linarith⟩)
  rintro imagePoint ⟨sourcePoint, hsourcePoint, rfl⟩
  rcases exists_closest_on_axis hsourceDelta.le source sourcePoint
      hsourcePoint with ⟨parameter, hparameter, hsourceDistance⟩
  let sourceAxisPoint := source.base + parameter • source.direction
  have hsourceAxis : sourceAxisPoint ∈ tubeAxisLine source :=
    ⟨parameter, rfl⟩
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
  have haxisHeight : |sourceAxisPoint 2| ≤ 6 := by
    exact (PiLp.norm_apply_le sourceAxisPoint 2).trans hsourceAxisNorm
  have hheightDifference :
      |(c + (d - c) / 2) - sourceAxisPoint 2| ≤ 7 := by
    calc
      |(c + (d - c) / 2) - sourceAxisPoint 2| ≤
          |c + (d - c) / 2| + |sourceAxisPoint 2| := abs_sub _ _
      _ ≤ 1 + 6 := add_le_add hcenterHeight haxisHeight
      _ = 7 := by norm_num
  have hsourceAxisDistance : dist sourceCenter sourceAxisPoint ≤ 14 := by
    change dist (wz1PaperAxisPointAtHeight source
      (c + (d - c) / 2)) sourceAxisPoint ≤ 14
    convert wz1Paper_axisPointAtHeight_dist_le_of_axis_point
      hsource (c + (d - c) / 2) 7 hsourceAxis hheightDifference
      using 1 <;> norm_num
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
  let imageAxisPoint := anisotropicCenteredRescalingMap
    g c d m center sourceAxisPoint
  have himageAxis : imageAxisPoint = targetMidpoint +
      relativeParameter • imageDirection := by
    dsimp only [imageAxisPoint]
    rw [hsourceRelative, anisotropicCenteredRescalingMap_add_smul,
      ← htargetMidpoint]
  let contractedPoint := targetMidpoint + factor⁻¹ •
    (anisotropicCenteredRescalingMap g c d m center sourcePoint -
      targetMidpoint)
  let contractedAxisPoint := targetMidpoint + factor⁻¹ •
    (imageAxisPoint - targetMidpoint)
  have hcoefficient :
      |relativeParameter * imageLength / factor| ≤ 1 / 2 := by
    have habsProduct :
        |relativeParameter * imageLength / factor| =
          |relativeParameter| * imageLength / factor := by
      rw [abs_div, abs_mul, abs_of_pos himageLengthPos,
        abs_of_pos hfactorPos]
    rw [habsProduct]
    apply (div_le_iff₀ hfactorPos).2
    dsimp only [factor]
    calc
      |relativeParameter| * imageLength ≤ 14 * S := by gcongr
      _ ≤ (1 / 2 : ℝ) * (32 * S) := by nlinarith
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
    have himageDirectionEq :
        imageDirection = imageLength • targetDirection := by
      dsimp only [targetDirection]
      rw [smul_smul]
      rw [mul_inv_cancel₀ himageLengthPos.ne', one_smul]
    have htargetBase :
        target.base = targetMidpoint - (1 / 2 : ℝ) • targetDirection := by
      change target.base =
        target.base + (1 / 2 : ℝ) • target.direction -
          (1 / 2 : ℝ) • targetDirection
      rw [htargetDirection]
      module
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
          (anisotropicCenteredRescalingMap g c d m center sourcePoint -
            anisotropicCenteredRescalingMap g c d m center
              sourceAxisPoint) := by
      dsimp only [contractedPoint, contractedAxisPoint, imageAxisPoint]
      module
    rw [hdifference, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hfactorPos)]
    have himageDistance := anisotropicCenteredRescalingMap_dist_le_height
      g hg hcd hdc hm hmOne hsub hS center sourcePoint sourceAxisPoint
    calc
      factor⁻¹ *
          ‖anisotropicCenteredRescalingMap g c d m center sourcePoint -
            anisotropicCenteredRescalingMap g c d m center
              sourceAxisPoint‖ ≤
        factor⁻¹ * (S * ‖sourcePoint - sourceAxisPoint‖) := by
          gcongr
          simpa [dist_eq_norm] using himageDistance
      _ = ‖sourcePoint - sourceAxisPoint‖ / 32 := by
        dsimp only [factor]
        field_simp [hSPos.ne']
      _ ≤ sourceDelta / 32 := by
        gcongr
        simpa [sourceAxisPoint, dist_eq_norm] using hsourceDistance
      _ ≤ targetDelta := by
        have hsourceTarget : sourceDelta ≤ targetDelta := by
          exact (show sourceDelta ≤ S * sourceDelta by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right (show 1 ≤ S from hSTwo.trans'
                (by norm_num : (1 : ℝ) ≤ 2)) hsourceDelta.le).trans
            htargetDelta
        nlinarith [hsourceTarget, hsourceDelta]
  have hcontractedCarrier : contractedPoint ∈ target.carrier :=
    Metric.mem_cthickening_of_dist_le contractedPoint contractedAxisPoint
      targetDelta _ hcontractedAxis hcontractedDistance
  refine ⟨contractedPoint, hcontractedCarrier, ?_⟩
  rw [AffineMap.homothety_apply]
  change factor • (contractedPoint - targetMidpoint) + targetMidpoint =
    anisotropicCenteredRescalingMap g c d m center sourcePoint
  have hcontracted : contractedPoint - targetMidpoint =
      factor⁻¹ •
        (anisotropicCenteredRescalingMap g c d m center sourcePoint -
          targetMidpoint) := by
    dsimp only [contractedPoint]
    abel
  rw [hcontracted, smul_smul,
    mul_inv_cancel₀ hfactorPos.ne', one_smul]
  abel

end Kakeya.Assouad

end
