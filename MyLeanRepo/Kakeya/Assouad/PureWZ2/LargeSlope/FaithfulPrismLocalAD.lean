import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.RotatedProjectedNormal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicADTransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ADTransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsADSet1AffineTransfer
import MyLeanRepo.Kakeya.Assouad.WZ1.TransportNormalizeAD
import MyLeanRepo.Kakeya.Assouad.WZ1.GeneralizedThickening

/-!
# Local AD in a faithful fixed-frame prism

The local plane-map AD bound is first restricted to a genuine common rotated-y
slice.  On that slice, deleting the rotated y-component is a translation of
the scalar projection.  The projected normal is then normalized and the base
scale is coarsened to the Step-4 scale.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

private lemma pureWZ2_axisBox_norm_le_sqrtThree
    {point : Point3}
    (hpoint : point ∈ Kakeya.Streamlined.axisBox 2 2 2) :
    ‖point‖ ≤ Real.sqrt 3 := by
  have hnorm := point3_coord_norm_sq point
  have hx : |point 0| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpoint.1
  have hy : |point 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpoint.2.1
  have hz : |point 2| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpoint.2.2
  have hsq : ‖point‖ ^ 2 ≤ 3 := by
    rw [hnorm]
    have hxSq : (point 0) ^ 2 ≤ 1 := by
      nlinarith [sq_abs (point 0), abs_nonneg (point 0)]
    have hySq : (point 1) ^ 2 ≤ 1 := by
      nlinarith [sq_abs (point 1), abs_nonneg (point 1)]
    have hzSq : (point 2) ^ 2 ≤ 1 := by
      nlinarith [sq_abs (point 2), abs_nonneg (point 2)]
    linarith
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
    Real.sqrt_nonneg 3, norm_nonneg point]

private lemma pureWZ2_scalarProjection_frameProjected_eq_translation
    (frameSlope y0 : ℝ) (normal : Point3)
    (E : Set Point3)
    (hEslice : ∀ point ∈ E,
      pureWZ2HorizontalRotation frameSlope point 1 = y0) :
    scalarProjection (pureWZ2FrameProjectedNormal frameSlope normal) E =
      (fun value : ℝ => value -
        y0 * (pureWZ2HorizontalRotation frameSlope normal) 1) ''
        scalarProjection normal E := by
  let rotation := pureWZ2HorizontalRotation frameSlope
  have hinner : ∀ point ∈ E,
      inner ℝ point (pureWZ2FrameProjectedNormal frameSlope normal) =
        inner ℝ point normal - y0 * (rotation normal) 1 := by
    intro point hpoint
    rw [pureWZ2FrameProjectedNormal,
      ← rotation.inner_map_map point
        (rotation.symm (xzProjectedNormal (rotation normal)))]
    simp only [rotation.apply_symm_apply]
    have hfull : inner ℝ (rotation point) (rotation normal) =
        inner ℝ point normal := rotation.inner_map_map point normal
    have hprojected :
        inner ℝ (rotation point) (xzProjectedNormal (rotation normal)) =
          inner ℝ (rotation point) (rotation normal) -
            (rotation point) 1 * (rotation normal) 1 := by
      have hleft :
          inner ℝ (rotation point) (xzProjectedNormal (rotation normal)) =
            (rotation point) 0 * (rotation normal) 0 +
              (rotation point) 2 * (rotation normal) 2 := by
        simp [xzProjectedNormal, PiLp.inner_apply, Fin.sum_univ_succ,
          RCLike.inner_apply, mul_comm]
      have hright :
          inner ℝ (rotation point) (rotation normal) =
            (rotation point) 0 * (rotation normal) 0 +
              (rotation point) 1 * (rotation normal) 1 +
                (rotation point) 2 * (rotation normal) 2 := by
        simp [inner, Fin.sum_univ_succ]
        ring
      rw [hleft, hright]
      ring
    rw [hprojected, hfull, hEslice point hpoint]
  ext value
  constructor
  · rintro ⟨point, hpoint, rfl⟩
    refine ⟨inner ℝ point normal, ⟨point, hpoint, rfl⟩, ?_⟩
    exact (hinner point hpoint).symm
  · rintro ⟨sourceValue, ⟨point, hpoint, rfl⟩, rfl⟩
    exact ⟨point, hpoint, hinner point hpoint⟩

private lemma pureWZ2_scalarProjection_normalizedFrame_eq_dilation
    (frameSlope : ℝ) (normal : Point3) (E : Set Point3) :
    scalarProjection
        (pureWZ2NormalizedFrameProjectedNormal frameSlope normal) E =
      (fun value : ℝ =>
        ‖pureWZ2FrameProjectedNormal frameSlope normal‖⁻¹ * value) ''
        scalarProjection
          (pureWZ2FrameProjectedNormal frameSlope normal) E := by
  let scale := ‖pureWZ2FrameProjectedNormal frameSlope normal‖⁻¹
  have hnormal :
      pureWZ2NormalizedFrameProjectedNormal frameSlope normal =
        scale • pureWZ2FrameProjectedNormal frameSlope normal := by
    simp [pureWZ2NormalizedFrameProjectedNormal,
      pureWZ2FrameProjectedNormal, normalizedXZNormal, scale]
  ext value
  constructor
  · rintro ⟨point, hpoint, rfl⟩
    refine ⟨inner ℝ point
      (pureWZ2FrameProjectedNormal frameSlope normal),
      ⟨point, hpoint, rfl⟩, ?_⟩
    rw [hnormal]
    simp [inner_smul_right, scale]
  · rintro ⟨sourceValue, ⟨point, hpoint, rfl⟩, rfl⟩
    refine ⟨point, hpoint, ?_⟩
    rw [hnormal]
    simp [inner_smul_right, scale]

/-- Paper-AD version of the common rotated-slice argument.  Unlike the
bounded `IsADSet1` wrapper below, positive affine covariance preserves the
constant exactly.  The normalization factor is at most sixteen, so starting
at scale `rho / 16` is enough to return to the requested scale `rho`. -/
theorem pureWZ2_common_rotated_slice_paper_local_ad_of_frame_lower
    {sourceDelta sigma rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    {frameSlope y0 : ℝ}
    (source : {point : Point3 // point ∈ sourceShading.union})
    (hframeLower : (1 / 16 : ℝ) ≤
      ‖pureWZ2FrameProjectedNormal frameSlope
        (sourceLocal.planeMap source)‖)
    (hrhoPos : 0 < rho) (hrhoOne : rho ≤ 1)
    (hsourceBase : sourceDelta ≤ rho / 16)
    (E : Set Point3)
    (hEsource : E ⊆ sourceShading.union)
    (hEball : E ⊆ Metric.closedBall (source : Point3)
      (Real.sqrt (rho / 16)))
    (hEslice : ∀ point ∈ E,
      pureWZ2HorizontalRotation frameSlope point 1 = y0) :
    PureWZ2PaperADSet1
      (scalarProjection
        (pureWZ2NormalizedFrameProjectedNormal frameSlope
          (sourceLocal.planeMap source)) E)
      rho (1 - sigma) C := by
  let normal := sourceLocal.planeMap source
  let baseScale := rho / 16
  let frameNormal := pureWZ2FrameProjectedNormal frameSlope normal
  let normalizedNormal :=
    pureWZ2NormalizedFrameProjectedNormal frameSlope normal
  let dilation := ‖frameNormal‖⁻¹
  have hbasePos : 0 < baseScale := by
    dsimp only [baseScale]
    positivity
  have hbaseOne : baseScale ≤ 1 := by
    dsimp only [baseScale]
    linarith
  have hpaperFull := sourceLocal.local_ad baseScale hsourceBase hbaseOne source
  have hsetSubset : E ⊆ sourceShading.union ∩
      Metric.closedBall (source : Point3) (Real.sqrt baseScale) :=
    fun point hpoint => ⟨hEsource hpoint, hEball hpoint⟩
  have hpaper : PureWZ2PaperADSet1
      (scalarProjection normal E) baseScale (1 - sigma) C :=
    hpaperFull.weaken_subset (Set.image_mono hsetSubset)
  have hframeEq : scalarProjection frameNormal E =
      (fun value : ℝ => 1 * value +
        (-(y0 * (pureWZ2HorizontalRotation frameSlope normal) 1))) ''
        scalarProjection normal E := by
    rw [show scalarProjection frameNormal E =
        scalarProjection (pureWZ2FrameProjectedNormal frameSlope normal) E by
      rfl]
    rw [pureWZ2_scalarProjection_frameProjected_eq_translation
      frameSlope y0 normal E hEslice]
    congr 1
    funext value
    ring
  have hframeAD : PureWZ2PaperADSet1
      (scalarProjection frameNormal E) baseScale (1 - sigma) C := by
    rw [hframeEq]
    simpa only [one_mul] using PureWZ2PaperADSet1.affine_transfer
      (a := (1 : ℝ))
      (b := -(y0 * (pureWZ2HorizontalRotation frameSlope normal) 1))
      hpaper (by norm_num)
  have hframeLower' : (1 / 16 : ℝ) ≤ ‖frameNormal‖ := by
    simpa [frameNormal, normal] using hframeLower
  have hframePos : 0 < ‖frameNormal‖ :=
    lt_of_lt_of_le (by norm_num) hframeLower'
  have hnormalUnit : ‖normal‖ = 1 := sourceLocal.planeMap_unit source
  have hframeUpper : ‖frameNormal‖ ≤ 1 := by
    rw [show ‖frameNormal‖ =
        ‖xzProjectedNormal
          (pureWZ2HorizontalRotation frameSlope normal)‖ by
      exact pureWZ2FrameProjectedNormal_norm frameSlope normal]
    exact (norm_xzProjected_le_norm
      (pureWZ2HorizontalRotation frameSlope normal)).trans_eq
        (by rw [(pureWZ2HorizontalRotation frameSlope).norm_map, hnormalUnit])
  have hdilationPos : 0 < dilation := by
    dsimp only [dilation]
    positivity
  have hdilationUpper : dilation ≤ 16 := by
    dsimp only [dilation]
    exact (inv_le_comm₀ hframePos (by norm_num : (0 : ℝ) < 16)).2 (by
      norm_num at hframeLower' ⊢
      exact hframeLower')
  have hnormalizedEq : scalarProjection normalizedNormal E =
      (fun value : ℝ => dilation * value + 0) ''
        scalarProjection frameNormal E := by
    rw [show scalarProjection normalizedNormal E =
        (fun value : ℝ => dilation * value) ''
          scalarProjection frameNormal E by
      exact pureWZ2_scalarProjection_normalizedFrame_eq_dilation
        frameSlope normal E]
    congr 1
    funext value
    ring
  have hnormalizedAD : PureWZ2PaperADSet1
      (scalarProjection normalizedNormal E) (dilation * baseScale)
        (1 - sigma) C := by
    rw [hnormalizedEq]
    exact PureWZ2PaperADSet1.affine_transfer
      (a := dilation) (b := 0) hframeAD hdilationPos
  have hnewScaleRho : dilation * baseScale ≤ rho := by
    dsimp only [baseScale]
    calc
      dilation * (rho / 16) ≤ 16 * (rho / 16) := by gcongr
      _ = rho := by ring
  exact hnormalizedAD.weaken_scale hrhoPos hnewScaleRho

/-- Local AD for a set contained in the common rotated-y slice and in the
`sqrt (rho / 16)` ball about an occupied source point. -/
theorem pureWZ2_common_rotated_slice_local_ad_of_frame_lower
    {sigma loss delta rho : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
    {frameSlope y0 : ℝ}
    (source : Point3) (hsource : source ∈ cfg.shading.union)
    (hframeLower : (1 / 16 : ℝ) ≤
      ‖pureWZ2FrameProjectedNormal frameSlope
        (cfg.localGrains.planeMap ⟨source, hsource⟩)‖)
    (hrhoPos : 0 < rho) (hrhoOne : rho ≤ 1)
    (hdeltaBase : delta ≤ rho / 16)
    (E : Set Point3)
    (hEcfg : E ⊆ cfg.shading.union)
    (hEball : E ⊆ Metric.closedBall source (Real.sqrt (rho / 16)))
    (hEslice : ∀ point ∈ E,
      pureWZ2HorizontalRotation frameSlope point 1 = y0) :
    IsADSet1
      (scalarProjection
        (pureWZ2NormalizedFrameProjectedNormal frameSlope
          (cfg.localGrains.planeMap ⟨source, hsource⟩)) E)
      rho (1 - sigma)
      (20 * Kakeya.realRpowENN delta (-loss)) := by
  let sourceSubtype : {point : Point3 // point ∈ cfg.shading.union} :=
    ⟨source, hsource⟩
  let normal := cfg.localGrains.planeMap sourceSubtype
  let baseScale := rho / 16
  let frameNormal := pureWZ2FrameProjectedNormal frameSlope normal
  let normalizedNormal :=
    pureWZ2NormalizedFrameProjectedNormal frameSlope normal
  let dilation := ‖frameNormal‖⁻¹
  have hbasePos : 0 < baseScale := by
    dsimp only [baseScale]
    positivity
  have hbaseOne : baseScale ≤ 1 := by
    dsimp only [baseScale]
    linarith
  have hnormalUnit : ‖normal‖ = 1 :=
    cfg.localGrains.planeMap_unit sourceSubtype
  have hpaperFull := cfg.localGrains.local_ad baseScale hdeltaBase hbaseOne
    sourceSubtype
  have hsetSubset : E ⊆ cfg.shading.union ∩
      Metric.closedBall source (Real.sqrt baseScale) :=
    fun point hpoint => ⟨hEcfg hpoint, hEball hpoint⟩
  have hpaper : PureWZ2PaperADSet1
      (scalarProjection normal E) baseScale (1 - sigma)
        (Kakeya.realRpowENN delta (-loss)) :=
    hpaperFull.weaken_subset (Set.image_mono hsetSubset)
  have hfullBounded : scalarProjection normal E ⊆ Set.Icc (-4 : ℝ) 4 := by
    intro value hvalue
    rcases hvalue with ⟨point, hpoint, rfl⟩
    rcases hEcfg hpoint with ⟨index, hcarrier⟩
    have hpointNorm : ‖point‖ ≤ Real.sqrt 3 :=
      pureWZ2_axisBox_norm_le_sqrtThree
        (cfg.shading.subset_body index hcarrier).2
    have hinner := abs_real_inner_le_norm point normal
    rw [hnormalUnit, mul_one] at hinner
    have hsqrtThree : Real.sqrt 3 ≤ 4 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    exact abs_le.mp (hinner.trans (hpointNorm.trans hsqrtThree))
  have hfullAD : IsADSet1 (scalarProjection normal E) baseScale
      (1 - sigma) (2 * Kakeya.realRpowENN delta (-loss)) :=
    hpaper.toIsADSet1 hfullBounded
  have hframeEq : scalarProjection frameNormal E =
      (fun value : ℝ => 1 * value +
        (-(y0 * (pureWZ2HorizontalRotation frameSlope normal) 1))) ''
        scalarProjection normal E := by
    rw [show scalarProjection frameNormal E =
        scalarProjection (pureWZ2FrameProjectedNormal frameSlope normal) E by
      rfl]
    rw [pureWZ2_scalarProjection_frameProjected_eq_translation
      frameSlope y0 normal E hEslice]
    congr 1
    funext value
    ring
  have hframeBounded : scalarProjection frameNormal E ⊆
      Set.Icc (-4 : ℝ) 4 := by
    intro value hvalue
    rcases hvalue with ⟨point, hpoint, rfl⟩
    rcases hEcfg hpoint with ⟨index, hcarrier⟩
    have hpointNorm : ‖point‖ ≤ Real.sqrt 3 :=
      pureWZ2_axisBox_norm_le_sqrtThree
        (cfg.shading.subset_body index hcarrier).2
    have hframeNormUpper : ‖frameNormal‖ ≤ 1 := by
      rw [show ‖frameNormal‖ =
          ‖xzProjectedNormal
            (pureWZ2HorizontalRotation frameSlope normal)‖ by
        exact pureWZ2FrameProjectedNormal_norm frameSlope normal]
      exact (norm_xzProjected_le_norm
        (pureWZ2HorizontalRotation frameSlope normal)).trans_eq
          (by rw [(pureWZ2HorizontalRotation frameSlope).norm_map, hnormalUnit])
    have hinner := abs_real_inner_le_norm point frameNormal
    have hbound : |inner ℝ point frameNormal| ≤ Real.sqrt 3 := by
      calc
        |inner ℝ point frameNormal| ≤ ‖point‖ * ‖frameNormal‖ := hinner
        _ ≤ Real.sqrt 3 * 1 := by gcongr
        _ = Real.sqrt 3 := by ring
    have hsqrtThree : Real.sqrt 3 ≤ 4 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    exact abs_le.mp (hbound.trans hsqrtThree)
  have hframeAD : IsADSet1 (scalarProjection frameNormal E) baseScale
      (1 - sigma) (20 * Kakeya.realRpowENN delta (-loss)) := by
    have htransfer := hfullAD.affine_transfer
      (a := (1 : ℝ)) (b := -(y0 *
        (pureWZ2HorizontalRotation frameSlope normal) 1))
      (by norm_num) (by norm_num) (scalarProjection frameNormal E)
      hframeEq hframeBounded
    simpa only [show (10 : ENNReal) *
        (2 * Kakeya.realRpowENN delta (-loss)) =
          20 * Kakeya.realRpowENN delta (-loss) by ring] using htransfer
  have hframeLower : (1 / 16 : ℝ) ≤ ‖frameNormal‖ := by
    simpa [frameNormal, normal, sourceSubtype] using hframeLower
  have hframePos : 0 < ‖frameNormal‖ := lt_of_lt_of_le (by norm_num) hframeLower
  have hdilationOne : 1 ≤ dilation := by
    have hframeUpper : ‖frameNormal‖ ≤ 1 := by
      rw [show ‖frameNormal‖ =
          ‖xzProjectedNormal
            (pureWZ2HorizontalRotation frameSlope normal)‖ by
        exact pureWZ2FrameProjectedNormal_norm frameSlope normal]
      exact (norm_xzProjected_le_norm
        (pureWZ2HorizontalRotation frameSlope normal)).trans_eq
          (by rw [(pureWZ2HorizontalRotation frameSlope).norm_map, hnormalUnit])
    dsimp only [dilation]
    exact (one_le_inv₀ hframePos).2 hframeUpper
  have hdilationUpper : dilation ≤ 16 := by
    dsimp only [dilation]
    exact (inv_le_comm₀ hframePos (by norm_num : (0 : ℝ) < 16)).2 (by
      norm_num at hframeLower ⊢
      exact hframeLower)
  have hnormalizedEq : scalarProjection normalizedNormal E =
      (fun value : ℝ => dilation * value) ''
        scalarProjection frameNormal E := by
    exact pureWZ2_scalarProjection_normalizedFrame_eq_dilation
      frameSlope normal E
  have hnormalizedBounded : scalarProjection normalizedNormal E ⊆
      Set.Icc (-4 : ℝ) 4 := by
    intro value hvalue
    rcases hvalue with ⟨point, hpoint, rfl⟩
    rcases hEcfg hpoint with ⟨index, hcarrier⟩
    have hpointNorm : ‖point‖ ≤ Real.sqrt 3 :=
      pureWZ2_axisBox_norm_le_sqrtThree
        (cfg.shading.subset_body index hcarrier).2
    have hnormalizedUnit : ‖normalizedNormal‖ = 1 := by
      exact pureWZ2NormalizedFrameProjectedNormal_unit hframePos
    have hinner := abs_real_inner_le_norm point normalizedNormal
    rw [hnormalizedUnit, mul_one] at hinner
    have hsqrtThree : Real.sqrt 3 ≤ 4 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    exact abs_le.mp (hinner.trans (hpointNorm.trans hsqrtThree))
  have hnewScalePos : 0 < dilation * baseScale := by positivity
  have hnewScaleRho : dilation * baseScale ≤ rho := by
    dsimp only [baseScale]
    calc
      dilation * (rho / 16) ≤ 16 * (rho / 16) := by
        gcongr
      _ = rho := by ring
  have hnormalizedAD : IsADSet1
      (scalarProjection normalizedNormal E) (dilation * baseScale)
      (1 - sigma) (20 * Kakeya.realRpowENN delta (-loss)) := by
    rw [hnormalizedEq]
    exact hframeAD.dilation_ge_one hdilationOne
      (by simpa only [← hnormalizedEq] using hnormalizedBounded)
      (hnewScaleRho.trans hrhoOne) hframeAD.1 hframeAD.2.1
      hframeAD.2.2.1 hframeAD.2.2.2.1
  have hcoarsened := hnormalizedAD.coarsen_scale
    hrhoPos hnewScaleRho hrhoOne
  simpa [normal, frameNormal, normalizedNormal, sourceSubtype] using hcoarsened

/-- Compatibility wrapper for callers that retain the former pointwise
local/global certificate. -/
theorem pureWZ2_common_rotated_slice_local_ad
    {sigma loss delta rho : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
    (compatibility : PureWZ2LocalGlobalCompatibility cfg)
    {frameSlope y0 : ℝ}
    (source : Point3) (hsource : source ∈ cfg.shading.union)
    (hsourceFrame :
      |cfg.globalGrains.slope (source 2) - frameSlope| ≤ 1 / 25)
    (_hdeltaSmall : delta ≤ 1 / 100)
    (hrhoPos : 0 < rho) (hrhoOne : rho ≤ 1)
    (hdeltaBase : delta ≤ rho / 16)
    (E : Set Point3)
    (hEcfg : E ⊆ cfg.shading.union)
    (hEball : E ⊆ Metric.closedBall source (Real.sqrt (rho / 16)))
    (hEslice : ∀ point ∈ E,
      pureWZ2HorizontalRotation frameSlope point 1 = y0) :
    IsADSet1
      (scalarProjection
        (pureWZ2NormalizedFrameProjectedNormal frameSlope
          (cfg.localGrains.planeMap ⟨source, hsource⟩)) E)
      rho (1 - sigma)
      (20 * Kakeya.realRpowENN delta (-loss)) := by
  apply pureWZ2_common_rotated_slice_local_ad_of_frame_lower cfg source hsource
  · exact pureWZ2_frameProjectedNormal_norm_lower cfg compatibility
      ⟨source, hsource⟩ hsourceFrame
  · exact hrhoPos
  · exact hrhoOne
  · exact hdeltaBase
  · exact hEcfg
  · exact hEball
  · exact hEslice

end Kakeya.Assouad

end
