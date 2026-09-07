import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalTubeParameters

/-!
# One exact-axis tube under the fixed affine diagonal map

The tube radius is kept external.  This module records only the exact
supporting-line geometry: the base is the affine image of the source axis at
the center height, and the direction is the normalized image under the common
linear part.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- The normalized image of a source direction under the common linear part. -/
def pureWZ2AffineDiagonalDirection
    (frameSlope heightScale transverseScale isotropicScale : ℝ)
    (direction : Point3) : Point3 :=
  let image := pureWZ2AffineDiagonalLinear frameSlope heightScale
    transverseScale isotropicScale direction
  (‖image‖⁻¹ : ℝ) • image

theorem pureWZ2AffineDiagonalDirection_unit
    (frameSlope : ℝ)
    {heightScale transverseScale isotropicScale : ℝ}
    (hheight : heightScale ≠ 0)
    (htransverse : transverseScale ≠ 0)
    (hisotropic : isotropicScale ≠ 0)
    {direction : Point3} (hdirection : direction ≠ 0) :
    ‖pureWZ2AffineDiagonalDirection frameSlope heightScale transverseScale
        isotropicScale direction‖ = 1 := by
  let image := pureWZ2AffineDiagonalLinear frameSlope heightScale
    transverseScale isotropicScale direction
  have himage : image ≠ 0 := by
    intro hzero
    have := pureWZ2AffineDiagonalLinearInverse_linear frameSlope
      hheight htransverse hisotropic direction
    rw [show pureWZ2AffineDiagonalLinear frameSlope heightScale
      transverseScale isotropicScale direction = image by rfl, hzero] at this
    have hinverseZero :
        pureWZ2AffineDiagonalLinearInverse frameSlope heightScale
          transverseScale isotropicScale 0 = 0 := by
      simp [pureWZ2AffineDiagonalLinearInverse, map_zero, point3]
    rw [hinverseZero] at this
    exact hdirection this.symm
  have himageNorm : 0 < ‖image‖ := norm_pos_iff.mpr himage
  rw [pureWZ2AffineDiagonalDirection]
  change ‖(‖image‖⁻¹ : ℝ) • image‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp [himageNorm.ne']

/-- The normalized affine direction is odd. -/
theorem pureWZ2AffineDiagonalDirection_neg
    (frameSlope heightScale transverseScale isotropicScale : ℝ)
    (direction : Point3) :
    pureWZ2AffineDiagonalDirection frameSlope heightScale transverseScale
        isotropicScale (-direction) =
      -pureWZ2AffineDiagonalDirection frameSlope heightScale transverseScale
        isotropicScale direction := by
  unfold pureWZ2AffineDiagonalDirection
  have hlinearNeg : pureWZ2AffineDiagonalLinear frameSlope heightScale
      transverseScale isotropicScale (-direction) =
    -(pureWZ2AffineDiagonalLinear frameSlope heightScale transverseScale
      isotropicScale direction) := by
    simpa using pureWZ2AffineDiagonalLinear_smul frameSlope heightScale
      transverseScale isotropicScale (-1) direction
  simp only [hlinearNeg]
  rw [norm_neg]
  module

/-- The vertical sign of the normalized affine direction agrees with the
source sign when the vertical and isotropic scales are positive. -/
theorem pureWZ2AffineDiagonalDirection_coord_two_nonneg_iff
    (frameSlope : ℝ)
    {heightScale transverseScale isotropicScale : ℝ}
    (hheight : 0 < heightScale)
    (htransverse : transverseScale ≠ 0)
    (hisotropic : 0 < isotropicScale)
    {direction : Point3} (hdirection : direction ≠ 0) :
    0 ≤ (pureWZ2AffineDiagonalDirection frameSlope heightScale
        transverseScale isotropicScale direction) 2 ↔
      0 ≤ direction 2 := by
  have himageNonzero : pureWZ2AffineDiagonalLinear frameSlope heightScale
      transverseScale isotropicScale direction ≠ 0 := by
    intro hzero
    have hinverse := pureWZ2AffineDiagonalLinearInverse_linear frameSlope
      hheight.ne' htransverse hisotropic.ne' direction
    rw [hzero] at hinverse
    simp [pureWZ2AffineDiagonalLinearInverse, point3] at hinverse
    exact hdirection hinverse.symm
  have hcoefficient : 0 <
      ‖pureWZ2AffineDiagonalLinear frameSlope heightScale
          transverseScale isotropicScale direction‖⁻¹ *
        (isotropicScale * heightScale) := by
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr himageNonzero))
      (mul_pos hisotropic hheight)
  rw [show (pureWZ2AffineDiagonalDirection frameSlope heightScale
        transverseScale isotropicScale direction) 2 =
      (‖pureWZ2AffineDiagonalLinear frameSlope heightScale
          transverseScale isotropicScale direction‖⁻¹ *
        (isotropicScale * heightScale)) * direction 2 by
    simp [pureWZ2AffineDiagonalDirection, pureWZ2AffineDiagonalLinear,
      point3, pureWZ2HorizontalRotation_coord_two]
    ring]
  exact (mul_nonneg_iff_of_pos_left hcoefficient)

/-- One raw target tube whose supporting line is the exact affine image of
the source supporting line. -/
def pureWZ2AffineDiagonalRawTube
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale isotropicScale : ℝ)
    {sourceDelta targetDelta : ℝ}
    (source : Kakeya.DeltaTube sourceDelta)
    (hheight : heightScale ≠ 0)
    (htransverse : transverseScale ≠ 0)
    (hisotropic : isotropicScale ≠ 0) :
    Kakeya.DeltaTube targetDelta where
  base := pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
    transverseScale isotropicScale
    (tubeAxisPointAtHeight source (center 2))
  direction := pureWZ2AffineDiagonalDirection frameSlope heightScale
    transverseScale isotropicScale source.direction
  direction_unit := pureWZ2AffineDiagonalDirection_unit frameSlope
    hheight htransverse hisotropic
    (by
      intro hzero
      have := congrArg norm hzero
      rw [source.direction_unit, norm_zero] at this
      norm_num at this)

/-- Positive paper orientation commutes with the affine-diagonal direction
transport. -/
theorem wz1PaperDirection_affineDiagonalRawTube
    (frameSlope : ℝ) (center : Point3)
    {heightScale transverseScale isotropicScale : ℝ}
    {sourceDelta targetDelta : ℝ}
    (source : Kakeya.DeltaTube sourceDelta)
    (hheight : 0 < heightScale)
    (htransverse : transverseScale ≠ 0)
    (hisotropic : 0 < isotropicScale) :
    wz1PaperDirection
        (pureWZ2AffineDiagonalRawTube frameSlope center heightScale
          transverseScale isotropicScale source hheight.ne' htransverse
            hisotropic.ne' : Kakeya.DeltaTube targetDelta) =
      pureWZ2AffineDiagonalDirection frameSlope heightScale transverseScale
        isotropicScale (wz1PaperDirection source) := by
  have hsourceNonzero : source.direction ≠ 0 := by
    intro hzero
    have := congrArg norm hzero
    rw [source.direction_unit, norm_zero] at this
    norm_num at this
  have hsign := pureWZ2AffineDiagonalDirection_coord_two_nonneg_iff
    frameSlope hheight htransverse hisotropic hsourceNonzero
  unfold wz1PaperDirection
  change (if 0 ≤ (pureWZ2AffineDiagonalDirection frameSlope heightScale
        transverseScale isotropicScale source.direction) 2 then
      pureWZ2AffineDiagonalDirection frameSlope heightScale transverseScale
        isotropicScale source.direction
    else -pureWZ2AffineDiagonalDirection frameSlope heightScale
      transverseScale isotropicScale source.direction) =
    pureWZ2AffineDiagonalDirection frameSlope heightScale transverseScale
      isotropicScale (if 0 ≤ source.direction 2 then source.direction
        else -source.direction)
  by_cases hsourceSign : 0 ≤ source.direction 2
  · rw [if_pos hsourceSign, if_pos (hsign.mpr hsourceSign)]
  · rw [if_neg hsourceSign, if_neg (fun h => hsourceSign (hsign.mp h)),
      pureWZ2AffineDiagonalDirection_neg]

/-- The raw tube has the exact affine-image supporting line. -/
theorem pureWZ2AffineDiagonalRawTube_axis
    (frameSlope : ℝ) (center : Point3)
    {heightScale transverseScale isotropicScale : ℝ}
    {sourceDelta targetDelta : ℝ}
    (source : Kakeya.DeltaTube sourceDelta)
    (hheight : heightScale ≠ 0)
    (htransverse : transverseScale ≠ 0)
    (hisotropic : isotropicScale ≠ 0) :
    tubeAxisLine (pureWZ2AffineDiagonalRawTube frameSlope center
        heightScale transverseScale isotropicScale source
        hheight htransverse hisotropic : Kakeya.DeltaTube targetDelta) =
      pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale isotropicScale '' tubeAxisLine source := by
  let linear := pureWZ2AffineDiagonalLinear frameSlope heightScale
    transverseScale isotropicScale
  let imageDirection := linear source.direction
  have himageDirection : imageDirection ≠ 0 := by
    intro hzero
    have := pureWZ2AffineDiagonalLinearInverse_linear frameSlope
      hheight htransverse hisotropic source.direction
    rw [show pureWZ2AffineDiagonalLinear frameSlope heightScale
      transverseScale isotropicScale source.direction = imageDirection by rfl,
      hzero] at this
    have hinverseZero :
        pureWZ2AffineDiagonalLinearInverse frameSlope heightScale
          transverseScale isotropicScale 0 = 0 := by
      simp [pureWZ2AffineDiagonalLinearInverse, map_zero, point3]
    rw [hinverseZero] at this
    have hsource : source.direction ≠ 0 :=
      fun hzero => by
        have := congrArg norm hzero
        rw [source.direction_unit, norm_zero] at this
        norm_num at this
    exact hsource this.symm
  have himageNorm : 0 < ‖imageDirection‖ := norm_pos_iff.mpr himageDirection
  let sourceBase := tubeAxisPointAtHeight source (center 2)
  have hsourceBase : sourceBase ∈ tubeAxisLine source :=
    tubeAxisPointAtHeight_mem source (center 2)
  have hsourceLine : tubeAxisLine source =
      {point | ∃ parameter : ℝ, point = sourceBase + parameter • source.direction} := by
    ext point
    constructor
    · rintro ⟨parameter, rfl⟩
      rcases hsourceBase with ⟨baseParameter, hbase⟩
      refine ⟨parameter - baseParameter, ?_⟩
      rw [hbase]
      module
    · rintro ⟨parameter, rfl⟩
      rcases hsourceBase with ⟨baseParameter, hbase⟩
      refine ⟨baseParameter + parameter, ?_⟩
      rw [hbase]
      module
  ext target
  constructor
  · rintro ⟨parameter, rfl⟩
    rw [hsourceLine]
    refine ⟨sourceBase + (parameter / ‖imageDirection‖) • source.direction,
      ⟨parameter / ‖imageDirection‖, rfl⟩, ?_⟩
    change pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale isotropicScale
          (sourceBase + (parameter / ‖imageDirection‖) • source.direction) =
      pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale isotropicScale sourceBase +
        parameter •
          ((‖imageDirection‖⁻¹ : ℝ) • imageDirection)
    rw [pureWZ2AffineDiagonalMapCentered_add_smul, smul_smul]
    congr 2
  · rintro ⟨sourcePoint, hsourcePoint, rfl⟩
    rw [hsourceLine] at hsourcePoint
    rcases hsourcePoint with ⟨parameter, rfl⟩
    refine ⟨parameter * ‖imageDirection‖, ?_⟩
    change pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale isotropicScale
          (sourceBase + parameter • source.direction) =
      pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale isotropicScale sourceBase +
        (parameter * ‖imageDirection‖) •
          ((‖imageDirection‖⁻¹ : ℝ) • imageDirection)
    rw [pureWZ2AffineDiagonalMapCentered_add_smul, smul_smul]
    congr 2
    field_simp [himageNorm.ne']

/-- The public ordinary target is centered at the affine image of the source
unit segment midpoint.  Unlike `pureWZ2AffineDiagonalRawTube`, whose base is
chosen at the active slab height for cropped localization, this tube keeps the
ordinary unit-segment provenance needed by Assouad Definition 2.12. -/
def pureWZ2AffineDiagonalPublicTube
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale isotropicScale : ℝ)
    {sourceDelta targetDelta : ℝ}
    (source : Kakeya.DeltaTube sourceDelta)
    (hheight : heightScale ≠ 0)
    (htransverse : transverseScale ≠ 0)
    (hisotropic : isotropicScale ≠ 0) :
    Kakeya.DeltaTube targetDelta where
  base :=
    pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale isotropicScale (wz2PaperTubeMidpoint source) -
      (1 / 2 : ℝ) •
        pureWZ2AffineDiagonalDirection frameSlope heightScale
          transverseScale isotropicScale source.direction
  direction := pureWZ2AffineDiagonalDirection frameSlope heightScale
    transverseScale isotropicScale source.direction
  direction_unit := pureWZ2AffineDiagonalDirection_unit frameSlope
    hheight htransverse hisotropic
    (by
      intro hzero
      have := congrArg norm hzero
      rw [source.direction_unit, norm_zero] at this
      norm_num at this)

/-- The ordinary target midpoint is exactly the affine image of the source
ordinary midpoint. -/
theorem pureWZ2AffineDiagonalPublicTube_midpoint
    (frameSlope : ℝ) (center : Point3)
    {heightScale transverseScale isotropicScale : ℝ}
    {sourceDelta targetDelta : ℝ}
    (source : Kakeya.DeltaTube sourceDelta)
    (hheight : heightScale ≠ 0)
    (htransverse : transverseScale ≠ 0)
    (hisotropic : isotropicScale ≠ 0) :
    wz2PaperTubeMidpoint
        (pureWZ2AffineDiagonalPublicTube frameSlope center
          heightScale transverseScale isotropicScale source
          hheight htransverse hisotropic : Kakeya.DeltaTube targetDelta) =
      pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale isotropicScale (wz2PaperTubeMidpoint source) := by
  simp only [wz2PaperTubeMidpoint, pureWZ2AffineDiagonalPublicTube]
  module

/-- Midpoint recentering changes the ordinary unit segment but preserves the
exact affine-image supporting line. -/
theorem pureWZ2AffineDiagonalPublicTube_axis
    (frameSlope : ℝ) (center : Point3)
    {heightScale transverseScale isotropicScale : ℝ}
    {sourceDelta targetDelta : ℝ}
    (source : Kakeya.DeltaTube sourceDelta)
    (hheight : heightScale ≠ 0)
    (htransverse : transverseScale ≠ 0)
    (hisotropic : isotropicScale ≠ 0) :
    tubeAxisLine (pureWZ2AffineDiagonalPublicTube frameSlope center
        heightScale transverseScale isotropicScale source
        hheight htransverse hisotropic : Kakeya.DeltaTube targetDelta) =
      pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale isotropicScale '' tubeAxisLine source := by
  let linear := pureWZ2AffineDiagonalLinear frameSlope heightScale
    transverseScale isotropicScale
  let imageDirection := linear source.direction
  have himageDirection : imageDirection ≠ 0 := by
    intro hzero
    have hinverse := pureWZ2AffineDiagonalLinearInverse_linear frameSlope
      hheight htransverse hisotropic source.direction
    rw [show pureWZ2AffineDiagonalLinear frameSlope heightScale
      transverseScale isotropicScale source.direction = imageDirection by rfl,
      hzero] at hinverse
    have hinverseZero :
        pureWZ2AffineDiagonalLinearInverse frameSlope heightScale
          transverseScale isotropicScale 0 = 0 := by
      simp [pureWZ2AffineDiagonalLinearInverse, map_zero, point3]
    rw [hinverseZero] at hinverse
    have hsource : source.direction ≠ 0 := by
      intro hzero
      have := congrArg norm hzero
      rw [source.direction_unit, norm_zero] at this
      norm_num at this
    exact hsource hinverse.symm
  have himageNorm : 0 < ‖imageDirection‖ := norm_pos_iff.mpr himageDirection
  let sourceMidpoint := wz2PaperTubeMidpoint source
  have hsourceMidpoint : sourceMidpoint ∈ tubeAxisLine source := by
    exact ⟨1 / 2, rfl⟩
  have hsourceLine : tubeAxisLine source =
      {point | ∃ parameter : ℝ,
        point = sourceMidpoint + parameter • source.direction} := by
    ext point
    constructor
    · rintro ⟨parameter, rfl⟩
      refine ⟨parameter - 1 / 2, ?_⟩
      dsimp only [sourceMidpoint, wz2PaperTubeMidpoint]
      module
    · rintro ⟨parameter, rfl⟩
      refine ⟨1 / 2 + parameter, ?_⟩
      dsimp only [sourceMidpoint, wz2PaperTubeMidpoint]
      module
  ext target
  constructor
  · rintro ⟨parameter, rfl⟩
    rw [hsourceLine]
    refine
      ⟨sourceMidpoint +
          ((parameter - 1 / 2) / ‖imageDirection‖) • source.direction,
        ⟨(parameter - 1 / 2) / ‖imageDirection‖, rfl⟩, ?_⟩
    change
      pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale isotropicScale
          (sourceMidpoint +
            ((parameter - 1 / 2) / ‖imageDirection‖) • source.direction) =
        (pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
            transverseScale isotropicScale sourceMidpoint -
          (1 / 2 : ℝ) •
            ((‖imageDirection‖⁻¹ : ℝ) • imageDirection)) +
          parameter • ((‖imageDirection‖⁻¹ : ℝ) • imageDirection)
    rw [pureWZ2AffineDiagonalMapCentered_add_smul]
    have hcancel :
        ((parameter - 1 / 2) / ‖imageDirection‖) • imageDirection =
          (parameter - 1 / 2) •
            ((‖imageDirection‖⁻¹ : ℝ) • imageDirection) := by
      rw [smul_smul]
      congr 1
    rw [hcancel]
    module
  · rintro ⟨sourcePoint, hsourcePoint, rfl⟩
    rw [hsourceLine] at hsourcePoint
    rcases hsourcePoint with ⟨parameter, rfl⟩
    refine ⟨1 / 2 + parameter * ‖imageDirection‖, ?_⟩
    change
      pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
          transverseScale isotropicScale
          (sourceMidpoint + parameter • source.direction) =
        (pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
            transverseScale isotropicScale sourceMidpoint -
          (1 / 2 : ℝ) •
            ((‖imageDirection‖⁻¹ : ℝ) • imageDirection)) +
          (1 / 2 + parameter * ‖imageDirection‖) •
            ((‖imageDirection‖⁻¹ : ℝ) • imageDirection)
    rw [pureWZ2AffineDiagonalMapCentered_add_smul]
    have hcancel : ‖imageDirection‖ * ‖imageDirection‖⁻¹ = 1 :=
      mul_inv_cancel₀ himageNorm.ne'
    have hcoefficient :
        (1 / 2 + parameter * ‖imageDirection‖) *
            ‖imageDirection‖⁻¹ =
          (1 / 2) * ‖imageDirection‖⁻¹ + parameter := by
      rw [add_mul, mul_assoc, hcancel, mul_one]
    simp only [smul_smul]
    rw [hcoefficient]
    module

end Kakeya.Assouad

end
