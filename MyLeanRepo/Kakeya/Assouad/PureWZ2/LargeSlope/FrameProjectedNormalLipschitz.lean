import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FrameNormalCompatibilityCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalGrainTransfer

/-!
# Lipschitz control for the projected Section-6 normal

This is the quantitative normal-field estimate needed before the final
Lemma-8 isotropic normalization.  It deliberately keeps the power-sized
Lipschitz constant explicit instead of pretending that the anisotropic step
preserves the public unit Lipschitz bound.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Orthogonal projection to the fixed-frame `xz` plane is nonexpanding. -/
lemma pureWZ2FrameProjectedNormal_sub_norm_le
    (frameSlope : ℝ) (first second : Point3) :
    ‖pureWZ2FrameProjectedNormal frameSlope first -
        pureWZ2FrameProjectedNormal frameSlope second‖ ≤
      ‖first - second‖ := by
  let rotation := pureWZ2HorizontalRotation frameSlope
  change ‖rotation.symm (xzProjectedNormal (rotation first)) -
      rotation.symm (xzProjectedNormal (rotation second))‖ ≤ _
  rw [← map_sub, rotation.symm.norm_map]
  have hproject :
      xzProjectedNormal (rotation first) -
          xzProjectedNormal (rotation second) =
        xzProjectedNormal (rotation first - rotation second) := by
    ext coordinate
    fin_cases coordinate <;> simp [xzProjectedNormal]
  rw [hproject]
  exact (norm_xzProjected_le_norm (rotation first - rotation second)).trans_eq <| by
    rw [← rotation.map_sub, rotation.norm_map]

lemma pureWZ2NormalizedFrameProjectedNormal_eq_normalize
    (frameSlope : ℝ) (normal : Point3) :
    pureWZ2NormalizedFrameProjectedNormal frameSlope normal =
      (‖pureWZ2FrameProjectedNormal frameSlope normal‖⁻¹ : ℝ) •
        pureWZ2FrameProjectedNormal frameSlope normal := by
  let rotation := pureWZ2HorizontalRotation frameSlope
  change rotation.symm
      ((‖xzProjectedNormal (rotation normal)‖⁻¹ : ℝ) •
        xzProjectedNormal (rotation normal)) =
    (‖rotation.symm (xzProjectedNormal (rotation normal))‖⁻¹ : ℝ) •
      rotation.symm (xzProjectedNormal (rotation normal))
  rw [map_smul, rotation.symm.norm_map]

/-- Normalizing the projected source normal costs at most the reciprocal of
the uniform `1/16` lower bound. -/
theorem pureWZ2_normalizedFrameProjectedNormal_lipschitz
    {sigma loss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
    (compatibility : PureWZ2FrameNormalCompatibility cfg)
    (frameSlope : ℝ)
    (hframe : ∀ point : {point : Point3 // point ∈ cfg.shading.union},
      |cfg.globalGrains.slope (point.1 2) - frameSlope| ≤ 1 / 50) :
    LipschitzWith 32
      (fun point : {point : Point3 // point ∈ cfg.shading.union} =>
        pureWZ2NormalizedFrameProjectedNormal frameSlope
          (cfg.localGrains.planeMap point)) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  have hfirst : (1 / 16 : ℝ) ≤
      ‖pureWZ2FrameProjectedNormal frameSlope
        (cfg.localGrains.planeMap first)‖ :=
    compatibility frameSlope first (hframe first)
  have hsecond : (1 / 16 : ℝ) ≤
      ‖pureWZ2FrameProjectedNormal frameSlope
        (cfg.localGrains.planeMap second)‖ :=
    compatibility frameSlope second (hframe second)
  have hnormal := normalization_lipschitz
    (x := pureWZ2FrameProjectedNormal frameSlope
      (cfg.localGrains.planeMap first))
    (y := pureWZ2FrameProjectedNormal frameSlope
      (cfg.localGrains.planeMap second))
    (m := (1 / 16 : ℝ)) (by norm_num) hfirst hsecond
  have hproject := pureWZ2FrameProjectedNormal_sub_norm_le frameSlope
    (cfg.localGrains.planeMap first)
    (cfg.localGrains.planeMap second)
  have hsource := cfg.localGrains.planeMap_lipschitz.dist_le_mul
    first second
  rw [dist_eq_norm] at hsource
  have hsource' :
      ‖cfg.localGrains.planeMap first -
        cfg.localGrains.planeMap second‖ ≤ dist first second := by
    simpa only [NNReal.coe_one, one_mul] using hsource
  have hreal :
      dist
          (pureWZ2NormalizedFrameProjectedNormal frameSlope
            (cfg.localGrains.planeMap first))
          (pureWZ2NormalizedFrameProjectedNormal frameSlope
            (cfg.localGrains.planeMap second)) ≤
        32 * dist first second := by
    rw [dist_eq_norm]
    calc
      ‖pureWZ2NormalizedFrameProjectedNormal frameSlope
            (cfg.localGrains.planeMap first) -
          pureWZ2NormalizedFrameProjectedNormal frameSlope
            (cfg.localGrains.planeMap second)‖
          ≤ 32 *
              ‖pureWZ2FrameProjectedNormal frameSlope
                    (cfg.localGrains.planeMap first) -
                pureWZ2FrameProjectedNormal frameSlope
                    (cfg.localGrains.planeMap second)‖ := by
            rw [pureWZ2NormalizedFrameProjectedNormal_eq_normalize,
              pureWZ2NormalizedFrameProjectedNormal_eq_normalize]
            norm_num at hnormal ⊢
            exact hnormal
      _ ≤ 32 *
          ‖cfg.localGrains.planeMap first -
            cfg.localGrains.planeMap second‖ := by gcongr
      _ ≤ 32 * dist first second := by gcongr
  simpa only [NNReal.coe_ofNat] using hreal

/-- Restrict the previous estimate to any subshading while keeping the
ambient source normal as the genuine provenance of each selected point. -/
theorem pureWZ2_normalizedFrameProjectedNormal_lipschitz_on_subshading
    {sigma loss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
    (compatibility : PureWZ2FrameNormalCompatibility cfg)
    (frameSlope : ℝ)
    {shading : WZ1PaperTubeShading cfg.family}
    (hsub : ∀ index, shading.carrier index ⊆ cfg.shading.carrier index)
    (hframe : ∀ point : {point : Point3 // point ∈ shading.union},
      |cfg.globalGrains.slope (point.1 2) - frameSlope| ≤ 1 / 50) :
    let inclusion :
        {point : Point3 // point ∈ shading.union} →
          {point : Point3 // point ∈ cfg.shading.union} :=
      fun point => ⟨point, paperSubshading_union_subset hsub point.property⟩
    LipschitzWith 32
      (fun point => pureWZ2NormalizedFrameProjectedNormal frameSlope
        (cfg.localGrains.planeMap (inclusion point))) := by
  dsimp only
  let inclusion :
      {point : Point3 // point ∈ shading.union} →
        {point : Point3 // point ∈ cfg.shading.union} :=
    fun point => ⟨point, paperSubshading_union_subset hsub point.property⟩
  apply LipschitzWith.of_dist_le_mul
  intro first second
  have hfirst : (1 / 16 : ℝ) ≤
      ‖pureWZ2FrameProjectedNormal frameSlope
        (cfg.localGrains.planeMap (inclusion first))‖ :=
    compatibility frameSlope (inclusion first) (hframe first)
  have hsecond : (1 / 16 : ℝ) ≤
      ‖pureWZ2FrameProjectedNormal frameSlope
        (cfg.localGrains.planeMap (inclusion second))‖ :=
    compatibility frameSlope (inclusion second) (hframe second)
  have hnormal := normalization_lipschitz
    (x := pureWZ2FrameProjectedNormal frameSlope
      (cfg.localGrains.planeMap (inclusion first)))
    (y := pureWZ2FrameProjectedNormal frameSlope
      (cfg.localGrains.planeMap (inclusion second)))
    (m := (1 / 16 : ℝ)) (by norm_num) hfirst hsecond
  have hproject := pureWZ2FrameProjectedNormal_sub_norm_le frameSlope
    (cfg.localGrains.planeMap (inclusion first))
    (cfg.localGrains.planeMap (inclusion second))
  have hsource := cfg.localGrains.planeMap_lipschitz.dist_le_mul
    (inclusion first) (inclusion second)
  rw [dist_eq_norm] at hsource
  have hsource' :
      ‖cfg.localGrains.planeMap (inclusion first) -
        cfg.localGrains.planeMap (inclusion second)‖ ≤ dist first second := by
    simpa only [NNReal.coe_one, one_mul, inclusion, Subtype.dist_eq] using hsource
  have hreal :
      dist
          (pureWZ2NormalizedFrameProjectedNormal frameSlope
            (cfg.localGrains.planeMap (inclusion first)))
          (pureWZ2NormalizedFrameProjectedNormal frameSlope
            (cfg.localGrains.planeMap (inclusion second))) ≤
        32 * dist first second := by
    rw [dist_eq_norm]
    calc
      ‖pureWZ2NormalizedFrameProjectedNormal frameSlope
            (cfg.localGrains.planeMap (inclusion first)) -
          pureWZ2NormalizedFrameProjectedNormal frameSlope
            (cfg.localGrains.planeMap (inclusion second))‖
          ≤ 32 *
              ‖pureWZ2FrameProjectedNormal frameSlope
                    (cfg.localGrains.planeMap (inclusion first)) -
                pureWZ2FrameProjectedNormal frameSlope
                    (cfg.localGrains.planeMap (inclusion second))‖ := by
            rw [pureWZ2NormalizedFrameProjectedNormal_eq_normalize,
              pureWZ2NormalizedFrameProjectedNormal_eq_normalize]
            norm_num at hnormal ⊢
            exact hnormal
      _ ≤ 32 *
          ‖cfg.localGrains.planeMap (inclusion first) -
            cfg.localGrains.planeMap (inclusion second)‖ := by gcongr
      _ ≤ 32 * dist first second := by gcongr
  simpa only [NNReal.coe_ofNat] using hreal

end Kakeya.Assouad

end
