import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingNormalizedGrainsStatements

/-!
# Normalized global grain package after mild rescaling

Assemble the complete target global-grain structure from the exact clamped
rescaled slope and the closed isotropic global-slab AD transport.
-/

namespace Kakeya.Assouad

lemma wz1ClampHeight_mem_Icc (z : ℝ) :
    wz1ClampHeight z ∈ Set.Icc (-1 : ℝ) 1 := by
  simp only [wz1ClampHeight, Set.mem_Icc]
  constructor
  · exact le_max_left (-1) (min 1 z)
  · apply max_le
    · linarith
    · exact min_le_left (1 : ℝ) z

lemma wz1ClampHeight_id {z : ℝ}
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    wz1ClampHeight z = z := by
  simp only [wz1ClampHeight]
  rw [min_eq_right hz.2, max_eq_right hz.1]

lemma wz1ClampHeight_dist_le (x y : ℝ) :
    |wz1ClampHeight x - wz1ClampHeight y| ≤ |x - y| := by
  simp only [wz1ClampHeight]
  rw [max_comm (-1 : ℝ), max_comm (-1 : ℝ)]
  exact
    (abs_max_sub_max_le_abs
      (min 1 x) (min 1 y) (-1 : ℝ)).trans
      (by
        have h :=
          abs_min_sub_min_le_max (1 : ℝ) x (1 : ℝ) y
        simpa using h)

theorem wz1_mild_rescaling_normalized_global_grain :
    WZ1MildRescalingNormalizedGlobalGrainStatement := by
  intro hAD
  intro sourceDelta sigma scale hsourceDelta hscale hscale_delta
  intro sourceFamily sourceShading C sourceGlobal hL_le_scale
    hsource_window hslope_bound
  intro center K hcenterK hmax_le_one
  intro targetFamily targetShading htarget_image hprojection_window
  set targetSlope : ℝ → ℝ :=
    wz1MildRescaledSlope center
      (point3 scale scale scale) sourceGlobal.slope
  have hscale_pos : 0 < scale := by linarith
  have hp0 : (point3 scale scale scale) 0 = scale := by
    simp [point3]
  have hp1 : (point3 scale scale scale) 1 = scale := by
    simp [point3]
  have hp2 : (point3 scale scale scale) 2 = scale := by
    simp [point3]
  have hratio :
      (point3 scale scale scale) 0 /
          (point3 scale scale scale) 1 = 1 := by
    rw [hp0, hp1]
    field_simp [hscale_pos.ne']
  have h_targetSlope_simp :
      ∀ z : ℝ,
        targetSlope z =
          sourceGlobal.slope
            (wz1ClampHeight (center 2 + z / scale)) := by
    intro z
    change
      (point3 scale scale scale) 0 /
            (point3 scale scale scale) 1 *
          sourceGlobal.slope
            (wz1ClampHeight
              (center 2 + z /
                (point3 scale scale scale) 2)) =
        _
    rw [hratio, hp2]
    ring
  have h_lipschitz :
      LipschitzOnWith (1 : NNReal) targetSlope
        (Set.Icc (-1 : ℝ) 1) := by
    intro z₁ hz₁ z₂ hz₂
    let c₁ :=
      wz1ClampHeight (center 2 + z₁ / scale)
    let c₂ :=
      wz1ClampHeight (center 2 + z₂ / scale)
    rw [h_targetSlope_simp z₁, h_targetSlope_simp z₂]
    have hc₁ : c₁ ∈ Set.Icc (-1 : ℝ) 1 :=
      wz1ClampHeight_mem_Icc _
    have hc₂ : c₂ ∈ Set.Icc (-1 : ℝ) 1 :=
      wz1ClampHeight_mem_Icc _
    have hsource :=
      sourceGlobal.lipschitz hc₁ hc₂
    have hclamp :
        |c₁ - c₂| ≤
          (1 / scale) * |z₁ - z₂| := by
      calc
        |c₁ - c₂| ≤
            |(center 2 + z₁ / scale) -
              (center 2 + z₂ / scale)| :=
          wz1ClampHeight_dist_le _ _
        _ = (1 / scale) * |z₁ - z₂| := by
          have h :
              (center 2 + z₁ / scale) -
                  (center 2 + z₂ / scale) =
                (z₁ - z₂) / scale := by
            ring
          rw [h, abs_div, abs_of_pos hscale_pos]
          ring
    have hdist :
        edist c₁ c₂ ≤
          ENNReal.ofReal ((1 / scale) * |z₁ - z₂|) := by
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal hclamp
    calc
      edist (sourceGlobal.slope c₁)
          (sourceGlobal.slope c₂) ≤
          (sourceGlobal.lipschitzConstant : ENNReal) *
            edist c₁ c₂ := hsource
      _ ≤ (sourceGlobal.lipschitzConstant : ENNReal) *
            ENNReal.ofReal
              ((1 / scale) * |z₁ - z₂|) := by
        gcongr
      _ = ((sourceGlobal.lipschitzConstant : ENNReal) *
              ENNReal.ofReal (1 / scale)) *
            ENNReal.ofReal |z₁ - z₂| := by
        rw [ENNReal.ofReal_mul (by positivity)]
        ring
      _ ≤ (1 : ENNReal) *
            ENNReal.ofReal |z₁ - z₂| := by
        have hreal :
            (sourceGlobal.lipschitzConstant : ℝ) *
                (1 / scale) ≤ 1 := by
          calc
            (sourceGlobal.lipschitzConstant : ℝ) *
                (1 / scale) =
                (sourceGlobal.lipschitzConstant : ℝ) /
                  scale := by ring
            _ ≤ 1 := (div_le_one hscale_pos).mpr hL_le_scale
        have hcoeff :
            (sourceGlobal.lipschitzConstant : ENNReal) *
                ENNReal.ofReal (1 / scale) ≤ 1 := by
          rw [ENNReal.coe_nnreal_eq,
            ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_one.mpr hreal
        gcongr
      _ = (1 : ENNReal) * edist z₁ z₂ := by
        rw [edist_dist, Real.dist_eq]
  have h_slope_on_image :
      ∀ p ∈ sourceShading.union,
        targetSlope
            ((wz1IsotropicRescalingMap center scale p) 2) =
          sourceGlobal.slope (p 2) := by
    intro p hp
    have hp_window :=
      hsource_window hp
    have hp_height :
        p 2 ∈ Set.Icc (-1 : ℝ) 1 := by
      have h := hp_window 2
      simpa [wz1MildRescalingSourceWindow, abs_le] using h
    rw [h_targetSlope_simp]
    have hcoord :
        (wz1IsotropicRescalingMap center scale p) 2 =
          scale * (p 2 - center 2) := by
      simp [wz1IsotropicRescalingMap]
    rw [hcoord]
    have harg :
        center 2 +
            scale * (p 2 - center 2) / scale =
          p 2 := by
      field_simp [hscale_pos.ne']
      ring
    rw [harg, wz1ClampHeight_id hp_height]
  have h_slope_bound :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        |targetSlope z| ≤ 3 := by
    intro z hz
    rw [h_targetSlope_simp]
    exact
      hslope_bound _ (wz1ClampHeight_mem_Icc _)
  have h_global_ad :
      HasGlobalSlabAD targetShading targetSlope sigma
        (60 *
          max (1 : ENNReal)
            ((K : ENNReal) *
              (sourceGlobal.lipschitzConstant : ENNReal)) *
          C) := by
    exact
      hAD hsourceDelta hscale hscale_delta
        sourceGlobal.slope sourceGlobal.global_slab_ad
        sourceGlobal.lipschitzConstant K
        sourceGlobal.lipschitz hsource_window
        center hcenterK hmax_le_one targetSlope
        h_slope_on_image targetShading htarget_image
        hprojection_window
  let globalGrains :
      WZ1LipschitzGlobalGrainData targetShading sigma
        (60 *
          max (1 : ENNReal)
            ((K : ENNReal) *
              (sourceGlobal.lipschitzConstant : ENNReal)) *
          C) :=
    { slope := targetSlope
      lipschitzConstant := 1
      lipschitz := h_lipschitz
      global_slab_ad := h_global_ad }
  exact
    ⟨globalGrains, rfl, rfl,
      h_slope_on_image, h_slope_bound⟩

end Kakeya.Assouad
