import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PureLocalGrainWZ1Bridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.RotatedProjectedNormal
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23FullGrainNormalBound

/-!
# A genuine local source certifies one fixed-frame prism normal

This is the local replacement for the historical global
`PureWZ2LocalGlobalCompatibility` assumption.  It starts from an actual
positive-volume source in one `sqrt rho` ball, uses the frozen Node-5 local AD
field to select a full local grain, and compares that grain with the exact
height-wise global AD field.

The proof deliberately splits on the vertical component of the local normal.
If it is large, the fixed-frame `xz` projection is already nondegenerate.  If
it is small, the closed WZ1 full-grain argument supplies the needed tilt.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

/-- One actual heavy local source, with a height window on which the global
slope stays close to the fixed Section-6 frame. -/
structure PureWZ2HeavyLocalSource
    {sigma loss delta rho eta frameSlope : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta) where
  anchor : {point : Point3 // point ∈ cfg.shading.union}
  source : Set Point3
  source_measurable : MeasurableSet source
  source_nonempty : source.Nonempty
  source_subset : source ⊆
    cfg.shading.union ∩ Metric.closedBall (anchor : Point3) (Real.sqrt rho)
  source_volume :
    Kakeya.realRpowENN rho (3 / 2 + sigma / 2 + eta) ≤ volume source
  heightLeft : ℝ
  source_height : ∀ point ∈ source,
    point 2 ∈ Set.Ico heightLeft (heightLeft + Real.sqrt rho)
  height_window : Set.Ico heightLeft (heightLeft + Real.sqrt rho) ⊆
    Set.Icc (-1 : ℝ) 1
  frame_close : ∀ z ∈ Set.Ico heightLeft (heightLeft + Real.sqrt rho),
    |cfg.globalGrains.slope z - frameSlope| ≤ 1 / 25

private lemma pureWZ2_global_projection_bounded
    {sigma loss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
    {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    scalarProjection
        (globalGrainDirection (cfg.globalGrains.slope z))
        (horizontalSlice cfg.shading.union z) ⊆
      Set.Icc (-4 : ℝ) 4 := by
  rintro value ⟨point, hpoint, rfl⟩
  rcases hpoint.1 with ⟨index, hcarrier⟩
  have hbox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
    (cfg.shading.subset_body index hcarrier).2
  have hcoords : |point 0| ≤ 1 ∧ |point 1| ≤ 1 := by
    constructor
    · simpa [Kakeya.Streamlined.axisBox] using hbox.1
    · simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
  have hslope : |cfg.globalGrains.slope z| ≤ 1 :=
    (cfg.globalGrains.slope_normalized z hz).1
  have hinner : inner ℝ point
      (globalGrainDirection (cfg.globalGrains.slope z)) =
        point 0 + cfg.globalGrains.slope z * point 1 := by
    rw [PiLp.inner_apply]
    simp [globalGrainDirection, Fin.sum_univ_succ]
  change inner ℝ point (globalGrainDirection (cfg.globalGrains.slope z)) ∈
    Set.Icc (-4 : ℝ) 4
  rw [hinner]
  have habs :
      |point 0 + cfg.globalGrains.slope z * point 1| ≤ 2 := by
    calc
      |point 0 + cfg.globalGrains.slope z * point 1| ≤
          |point 0| + |cfg.globalGrains.slope z| * |point 1| := by
            simpa [abs_mul] using abs_add_le
              (point 0) (cfg.globalGrains.slope z * point 1)
      _ ≤ 1 + 1 * 1 := by
        exact add_le_add hcoords.1
          (mul_le_mul hslope hcoords.2 (abs_nonneg _) (by norm_num))
      _ = 2 := by norm_num
  exact ⟨by linarith [abs_le.mp habs], by linarith [abs_le.mp habs]⟩

private lemma PureWZ2HeavyLocalSource.globalAD_coarsened
    {sigma loss delta rho eta frameSlope : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma loss delta}
    (data : PureWZ2HeavyLocalSource
      (rho := rho) (eta := eta) (frameSlope := frameSlope) cfg)
    (hrho : 0 < rho) (hdeltaRho : delta ≤ rho) (hrhoOne : rho ≤ 1)
    (z : ℝ) (hz : z ∈ Set.Ico data.heightLeft
      (data.heightLeft + Real.sqrt rho)) :
    IsADSet1
      (scalarProjection
        (globalGrainDirection (cfg.globalGrains.slope z))
        (horizontalSlice cfg.shading.union z))
      rho (1 - sigma) (2 * Kakeya.realRpowENN delta (-loss)) := by
  have hheight : z ∈ Set.Icc (-1 : ℝ) 1 := data.height_window hz
  have hpaper := cfg.globalGrains.global_ad_slope z hheight
  have hbounded := pureWZ2_global_projection_bounded cfg hheight
  have hclassical : IsADSet1
      (scalarProjection
        (globalGrainDirection (cfg.globalGrains.slope z))
        (horizontalSlice cfg.shading.union z))
      delta (1 - sigma) (2 * Kakeya.realRpowENN delta (-loss)) := by
    exact hpaper.toIsADSet1 hbounded
  exact hclassical.coarsen_scale hrho hdeltaRho hrhoOne

/-- Algebraic fixed-frame nondegeneracy from one genuine normal-tilt
certificate. -/
private lemma pureWZ2_frameProjectedNormal_norm_lower_of_tilt
    {normal : Point3} {sourceSlope frameSlope : ℝ}
    (hnormal : ‖normal‖ = 1)
    (hsource : |sourceSlope| ≤ 1)
    (hfirst : (1 / 4 : ℝ) ≤ |normal 0|)
    (htilt : |normal 1 - sourceSlope * normal 0| ≤ 1 / 14)
    (hframe : |sourceSlope - frameSlope| ≤ 1 / 25) :
    (1 / 16 : ℝ) ≤
      ‖pureWZ2FrameProjectedNormal frameSlope normal‖ := by
  let denominator := pureWZ2HorizontalNorm frameSlope
  have hdenPos : 0 < denominator := pureWZ2HorizontalNorm_pos frameSlope
  have hdenSq : denominator ^ 2 = 1 + frameSlope ^ 2 :=
    pureWZ2HorizontalNorm_sq frameSlope
  have hframeBound : |frameSlope| ≤ 26 / 25 := by
    calc
      |frameSlope| ≤ |sourceSlope| + |sourceSlope - frameSlope| := by
        have htriangle := abs_add_le sourceSlope (frameSlope - sourceSlope)
        rw [show sourceSlope + (frameSlope - sourceSlope) = frameSlope by ring,
          abs_sub_comm] at htriangle
        exact htriangle
      _ ≤ 1 + 1 / 25 := by gcongr
      _ = 26 / 25 := by norm_num
  have hdenUpper : denominator ≤ 3 / 2 := by
    have hframeSq : frameSlope ^ 2 ≤ (26 / 25 : ℝ) ^ 2 := by
      nlinarith [sq_abs frameSlope, abs_nonneg frameSlope]
    have hsq : denominator ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := by
      rw [hdenSq]
      nlinarith
    nlinarith [norm_nonneg denominator]
  have hnormalFirstUpper : |normal 0| ≤ 1 := by
    have hcoord := PiLp.norm_apply_le normal (0 : Fin 3)
    simpa [Real.norm_eq_abs, hnormal] using hcoord
  let error := normal 1 - sourceSlope * normal 0
  have hdecomp : normal 0 + frameSlope * normal 1 =
      (1 + frameSlope ^ 2) * normal 0 + frameSlope * error +
        frameSlope * (sourceSlope - frameSlope) * normal 0 := by
    dsimp only [error]
    ring
  have hmain :
      (1 + frameSlope ^ 2) * |normal 0| -
          |frameSlope| * |error| -
          |frameSlope| * |sourceSlope - frameSlope| * |normal 0| ≤
        |normal 0 + frameSlope * normal 1| := by
    rw [hdecomp]
    let leading := (1 + frameSlope ^ 2) * normal 0
    let perturbation := frameSlope * error +
      frameSlope * (sourceSlope - frameSlope) * normal 0
    have hperturbation : |perturbation| ≤
        |frameSlope| * |error| +
          |frameSlope| * |sourceSlope - frameSlope| * |normal 0| := by
      dsimp only [perturbation]
      calc
        |frameSlope * error +
            frameSlope * (sourceSlope - frameSlope) * normal 0| ≤
          |frameSlope * error| +
            |frameSlope * (sourceSlope - frameSlope) * normal 0| :=
              abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_mul]
    have hleading : |leading| = (1 + frameSlope ^ 2) * |normal 0| := by
      simp [leading, abs_mul, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ 1 + frameSlope ^ 2)]
    have hreverse : |leading| - |perturbation| ≤ |leading + perturbation| := by
      have htriangle := abs_add_le (leading + perturbation) (-perturbation)
      have heq : leading + perturbation + -perturbation = leading := by ring
      rw [heq, abs_neg] at htriangle
      linarith
    have hsum : leading + perturbation =
        (1 + frameSlope ^ 2) * normal 0 + frameSlope * error +
          frameSlope * (sourceSlope - frameSlope) * normal 0 := by
      dsimp only [leading, perturbation]
      ring
    rw [hleading, hsum] at hreverse
    have hbound := (sub_le_sub_left hperturbation
      ((1 + frameSlope ^ 2) * |normal 0|)).trans hreverse
    simpa only [sub_sub] using hbound
  have herror : |error| ≤ 1 / 14 := by simpa [error] using htilt
  have hnumerator : (1 / 10 : ℝ) ≤
      |normal 0 + frameSlope * normal 1| := by
    have hleading : (1 / 4 : ℝ) ≤
        (1 + frameSlope ^ 2) * |normal 0| := by
      calc
        (1 / 4 : ℝ) ≤ 1 * |normal 0| := by simpa using hfirst
        _ ≤ (1 + frameSlope ^ 2) * |normal 0| := by
          gcongr
          nlinarith [sq_nonneg frameSlope]
    have herrorTerm : |frameSlope| * |error| ≤ 13 / 175 := by
      nlinarith [abs_nonneg frameSlope, abs_nonneg error]
    have hframeTerm :
        |frameSlope| * |sourceSlope - frameSlope| * |normal 0| ≤
          26 / 625 := by
      have hproduct : |sourceSlope - frameSlope| * |normal 0| ≤ 1 / 25 := by
        nlinarith [abs_nonneg (sourceSlope - frameSlope),
          abs_nonneg (normal 0)]
      nlinarith [abs_nonneg frameSlope]
    exact (by linarith : (1 / 10 : ℝ) ≤
      (1 + frameSlope ^ 2) * |normal 0| -
        |frameSlope| * |error| -
        |frameSlope| * |sourceSlope - frameSlope| * |normal 0|) |>.trans hmain
  have hrotatedZero :
      (pureWZ2HorizontalRotation frameSlope normal) 0 =
        (normal 0 + frameSlope * normal 1) / denominator :=
    pureWZ2HorizontalRotation_coord_zero frameSlope normal
  have hcoordLower : (1 / 16 : ℝ) ≤
      |(pureWZ2HorizontalRotation frameSlope normal) 0| := by
    rw [hrotatedZero, abs_div, abs_of_pos hdenPos]
    have hquot : (1 / 10 : ℝ) / denominator ≤
        |normal 0 + frameSlope * normal 1| / denominator := by gcongr
    have hconst : (1 / 16 : ℝ) ≤ (1 / 10) / denominator := by
      rw [le_div_iff₀ hdenPos]
      nlinarith
    exact hconst.trans hquot
  rw [pureWZ2FrameProjectedNormal_norm]
  exact hcoordLower.trans (by
    have hcoord := PiLp.norm_apply_le
      (xzProjectedNormal (pureWZ2HorizontalRotation frameSlope normal))
      (0 : Fin 3)
    have hdenNonneg : 0 ≤ denominator := hdenPos.le
    simpa [xzProjectedNormal, Real.norm_eq_abs, abs_div,
      abs_of_nonneg hdenNonneg] using hcoord)

/-- An actual heavy local source produces a nonzero normalized normal for the
whole fixed-frame prism.  No global compatibility field is assumed. -/
theorem PureWZ2HeavyLocalSource.frameProjectedNormal_norm_lower
    {sigma loss delta rho eta frameSlope : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma loss delta}
    (data : PureWZ2HeavyLocalSource
      (rho := rho) (eta := eta) (frameSlope := frameSlope) cfg)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hTwoCOne : 1 ≤ 2 * Kakeya.realRpowENN delta (-loss))
    (hTwoCPower :
      2 * Kakeya.realRpowENN delta (-loss) ≤
        Kakeya.realRpowENN rho (-eta))
    (hPlanarSmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt rho ≤ 1)
    (habsorb : Real.rpow rho (1 - 4 * eta / sigma) ≤
      Real.sqrt rho / 14) :
    (1 / 16 : ℝ) ≤
      ‖pureWZ2FrameProjectedNormal frameSlope
        (cfg.localGrains.planeMap data.anchor)‖ := by
  let C : ENNReal := Kakeya.realRpowENN delta (-loss)
  let normal := cfg.localGrains.planeMap data.anchor
  have hnormal : ‖normal‖ = 1 := cfg.localGrains.planeMap_unit data.anchor
  by_cases hvertical : |normal 2| ≤ 1 / 2
  · let fiber : PureWZ2LocalProjectionHeavyFiberInSource
        (rho := rho) cfg.shading C cfg.localGrains data.anchor data.source :=
      Classical.choice (pureWZ2_local_projection_heavy_fiber_in_source
        cfg.shading C cfg.localGrains data.anchor data.source
        data.source_measurable data.source_nonempty data.source_subset
        hrho hdeltaRho hrhoOne (by simp [C, Kakeya.realRpowENN]))
    let input : WZ1Lemma23FullLocalGrainInputGeneralized
        rho sigma eta (2 * C) cfg.globalGrains.slope :=
      { grain := fiber.grain
        grain_measurable := fiber.grain_measurable
        grain_finite := fiber.grain_finite
        heightLeft := data.heightLeft
        grain_height := fun point hpoint =>
          data.source_height point (fiber.grain_in_source hpoint)
        grain_volume := fiber.grain_volume_of_source_lower hrho
          (by simpa [C] using hTwoCOne)
          (by simpa [C] using hTwoCPower) data.source_volume
        center := data.anchor
        normal := normal
        localProjectionCenter := fiber.center
        normal_unit := hnormal
        normal_vertical := hvertical
        grain_square := fiber.grain_square
        grain_local_strip := fiber.grain_local_strip
        slope_small := by
          intro z hz
          exact (cfg.globalGrains.slope_normalized z
            (data.height_window hz)).1.trans
            (by norm_num)
        projected := fun z => scalarProjection
          (globalGrainDirection (cfg.globalGrains.slope z))
          (horizontalSlice cfg.shading.union z)
        globalAD := by
          intro z hz
          exact data.globalAD_coarsened hrho hdeltaRho hrhoOne z hz
        global_projection_sub := by
          intro z _hz
          rintro value ⟨point, hpoint, rfl⟩
          have hlift : point3 (point 0) (point 1) z ∈ fiber.grain :=
            wz1Lemma23_mem_planarSlice_iff.mp hpoint
          have hshading : point3 (point 0) (point 1) z ∈ cfg.shading.union :=
            fiber.grain_in_shading hlift
          refine ⟨point3 (point 0) (point 1) z,
            ⟨hshading, by simp [point3]⟩, ?_⟩
          change inner ℝ (point3 (point 0) (point 1) z)
              (globalGrainDirection (cfg.globalGrains.slope z)) =
            point 0 + cfg.globalGrains.slope z * point 1
          rw [PiLp.inner_apply]
          simp [globalGrainDirection, point3, Fin.sum_univ_succ] }
    rcases wz1_lemma23_full_grain_normal_tilt_exists_generalized
        rho sigma eta (2 * C) cfg.globalGrains.slope
        hrho hrhoOne hsigma hsigmaOne heta hetaSigma
        (ENNReal.mul_ne_top (by norm_num) (by
          simp [C, Kakeya.realRpowENN]))
        (by simpa [C] using hTwoCPower) hPlanarSmall hrootSmall20 habsorb input with
      ⟨z, hz, htilt⟩
    have hsourceSlope : |cfg.globalGrains.slope z| ≤ 1 :=
      (cfg.globalGrains.slope_normalized z (data.height_window hz)).1
    have hfirst : (1 / 4 : ℝ) ≤ |normal 0| :=
      wz1_lemma23_normal_first_component_generalized normal
        (cfg.globalGrains.slope z) hnormal hvertical
        (hsourceSlope.trans (by norm_num)) htilt
    exact pureWZ2_frameProjectedNormal_norm_lower_of_tilt hnormal
      hsourceSlope hfirst htilt (data.frame_close z hz)
  · have hverticalLower : (1 / 2 : ℝ) < |normal 2| := lt_of_not_ge hvertical
    rw [pureWZ2FrameProjectedNormal_norm]
    have hcoord := PiLp.norm_apply_le
      (xzProjectedNormal (pureWZ2HorizontalRotation frameSlope normal))
      (2 : Fin 3)
    have hcoordEq :
        (xzProjectedNormal (pureWZ2HorizontalRotation frameSlope normal)) 2 =
          normal 2 := by
      simp [xzProjectedNormal, pureWZ2HorizontalRotation_coord_two]
    rw [hcoordEq] at hcoord
    exact (by linarith : (1 / 16 : ℝ) ≤ |normal 2|) |>.trans (by
      simpa [Real.norm_eq_abs] using hcoord)

end Kakeya.Assouad

end
