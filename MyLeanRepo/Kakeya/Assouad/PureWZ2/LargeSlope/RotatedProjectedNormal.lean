import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.RotatedWeightedCommonYRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.BlockALemmas
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GrainSubfamilyRestriction

/-!
# Projected local normals in the fixed Section-6 frame
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- Delete the rotated y-component of a normal, expressed back in the source frame. -/
def pureWZ2FrameProjectedNormal (frameSlope : ℝ) (normal : Point3) : Point3 :=
  (pureWZ2HorizontalRotation frameSlope).symm
    (xzProjectedNormal (pureWZ2HorizontalRotation frameSlope normal))

/-- Normalize the fixed-frame projected normal. -/
def pureWZ2NormalizedFrameProjectedNormal
    (frameSlope : ℝ) (normal : Point3) : Point3 :=
  (pureWZ2HorizontalRotation frameSlope).symm
    (normalizedXZNormal (pureWZ2HorizontalRotation frameSlope normal))

lemma pureWZ2FrameProjectedNormal_norm
    (frameSlope : ℝ) (normal : Point3) :
    ‖pureWZ2FrameProjectedNormal frameSlope normal‖ =
      ‖xzProjectedNormal (pureWZ2HorizontalRotation frameSlope normal)‖ := by
  exact (pureWZ2HorizontalRotation frameSlope).symm.norm_map _

lemma pureWZ2NormalizedFrameProjectedNormal_unit
    {frameSlope : ℝ} {normal : Point3}
    (hprojection : 0 < ‖pureWZ2FrameProjectedNormal frameSlope normal‖) :
    ‖pureWZ2NormalizedFrameProjectedNormal frameSlope normal‖ = 1 := by
  rw [pureWZ2NormalizedFrameProjectedNormal,
    (pureWZ2HorizontalRotation frameSlope).symm.norm_map]
  apply normalizedXZNormal_unit
  simpa [pureWZ2FrameProjectedNormal_norm] using hprojection

lemma pureWZ2FrameProjectedNormal_rotated_y_zero
    (frameSlope : ℝ) (normal : Point3) :
    pureWZ2HorizontalRotation frameSlope
        (pureWZ2NormalizedFrameProjectedNormal frameSlope normal) 1 = 0 := by
  simp [pureWZ2NormalizedFrameProjectedNormal, normalizedXZNormal_y_zero]

/-- Inner products with the source-frame normal equal inner products in the rotated frame. -/
lemma inner_pureWZ2NormalizedFrameProjectedNormal
    (frameSlope : ℝ) (point normal : Point3) :
    inner ℝ point (pureWZ2NormalizedFrameProjectedNormal frameSlope normal) =
      inner ℝ (pureWZ2HorizontalRotation frameSlope point)
        (normalizedXZNormal (pureWZ2HorizontalRotation frameSlope normal)) := by
  rw [pureWZ2NormalizedFrameProjectedNormal,
    ← (pureWZ2HorizontalRotation frameSlope).inner_map_map]
  simp

/-- WZ1 local/global compatibility makes the projected normal nondegenerate
in every nearby fixed horizontal frame. -/
theorem pureWZ2_frameProjectedNormal_norm_lower
    {sigma loss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
    (compatibility : PureWZ2LocalGlobalCompatibility cfg)
    (point : {point : Point3 // point ∈ cfg.shading.union})
    {frameSlope : ℝ}
    (hframe : |cfg.globalGrains.slope (point.1 2) - frameSlope| ≤
      1 / 25) :
    (1 / 16 : ℝ) ≤
      ‖pureWZ2FrameProjectedNormal frameSlope
        (cfg.localGrains.planeMap point)‖ := by
  let normal := cfg.localGrains.planeMap point
  let sourceSlope := cfg.globalGrains.slope (point.1 2)
  let denominator := pureWZ2HorizontalNorm frameSlope
  have hdenPos : 0 < denominator := pureWZ2HorizontalNorm_pos frameSlope
  have hdenSq : denominator ^ 2 = 1 + frameSlope ^ 2 :=
    pureWZ2HorizontalNorm_sq frameSlope
  have hframeBound : |frameSlope| ≤ 26 / 25 := by
    have hsourceBound := (cfg.globalGrains.slope_normalized (point.1 2) (by
      rcases point.property with ⟨index, hpoint⟩
      have hbox := (cfg.shading.subset_body index hpoint).2
      simpa [Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2)).1
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
  have hfirst : 1 / 4 ≤ |normal 0| :=
    compatibility.normal_first point
  have htilt : |normal 1 - sourceSlope * normal 0| ≤ 1 / 10 :=
    compatibility.normal_tilt point
  have hframeSource : |frameSlope - sourceSlope| ≤ 1 / 25 := by
    simpa [abs_sub_comm] using hframe
  have hnormalFirstUpper : |normal 0| ≤ 1 := by
    have hcoord := PiLp.norm_apply_le normal (0 : Fin 3)
    simpa [normal, Real.norm_eq_abs, cfg.localGrains.planeMap_unit point]
      using hcoord
  have hnumerator :
      1 / 10 ≤ |normal 0 + frameSlope * normal 1| := by
    let error := normal 1 - sourceSlope * normal 0
    have hdecomp : normal 0 + frameSlope * normal 1 =
        (1 + frameSlope ^ 2) * normal 0 +
          frameSlope * error +
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
      have htriangle := abs_add_le (frameSlope * error)
        (frameSlope * (sourceSlope - frameSlope) * normal 0)
      have htriangle' : |perturbation| ≤
          |frameSlope| * |error| +
            |frameSlope| * |sourceSlope - frameSlope| * |normal 0| := by
        dsimp only [perturbation]
        calc
          |frameSlope * error +
              frameSlope * (sourceSlope - frameSlope) * normal 0|
            ≤ |frameSlope * error| +
                |frameSlope * (sourceSlope - frameSlope) * normal 0| :=
              abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_mul]
      have hcoeff : |1 + frameSlope ^ 2| = 1 + frameSlope ^ 2 :=
        abs_of_nonneg (by positivity)
      have hleading : |leading| = (1 + frameSlope ^ 2) * |normal 0| := by
        simp [leading, abs_mul, hcoeff]
      have hreverse' : |leading| - |perturbation| ≤
          |leading + perturbation| := by
        have htriangleReverse := abs_add_le (leading + perturbation) (-perturbation)
        have heq : leading + perturbation + -perturbation = leading := by ring
        rw [heq, abs_neg] at htriangleReverse
        linarith
      have hsumEq : leading + perturbation =
          (1 + frameSlope ^ 2) * normal 0 +
            frameSlope * error +
            frameSlope * (sourceSlope - frameSlope) * normal 0 := by
        dsimp only [leading, perturbation]
        ring
      rw [hleading] at hreverse'
      rw [hsumEq] at hreverse'
      have hbound := (sub_le_sub_left htriangle'
        ((1 + frameSlope ^ 2) * |normal 0|)).trans hreverse'
      have harith :
          (1 + frameSlope ^ 2) * |normal 0| -
              (|frameSlope| * |error| +
                |frameSlope| * |sourceSlope - frameSlope| * |normal 0|) =
            (1 + frameSlope ^ 2) * |normal 0| -
              |frameSlope| * |error| -
              |frameSlope| * |sourceSlope - frameSlope| * |normal 0| := by ring
      rw [← harith]
      exact hbound
    have herror : |error| ≤ 1 / 10 := by simpa [error] using htilt
    have hsourceFrame : |sourceSlope - frameSlope| ≤ 1 / 25 := hframe
    have hpositive :
        1 / 10 ≤ (1 + frameSlope ^ 2) * |normal 0| -
          |frameSlope| * |error| -
          |frameSlope| * |sourceSlope - frameSlope| * |normal 0| := by
      have hfirstNonneg : 0 ≤ |normal 0| := abs_nonneg _
      have hleadingLower :
          1 / 4 ≤ (1 + frameSlope ^ 2) * |normal 0| := by
        calc
          (1 / 4 : ℝ) ≤ 1 * |normal 0| := by simpa using hfirst
          _ ≤ (1 + frameSlope ^ 2) * |normal 0| := by
            apply mul_le_mul_of_nonneg_right
            · nlinarith [sq_nonneg frameSlope]
            · exact hfirstNonneg
      have herrorTerm : |frameSlope| * |error| ≤ 13 / 125 := by
        nlinarith [abs_nonneg frameSlope, abs_nonneg error]
      have hframeTerm :
          |frameSlope| * |sourceSlope - frameSlope| * |normal 0| ≤
            26 / 625 := by
        have hsourceSmall : |sourceSlope - frameSlope| ≤ 1 / 25 := hframe
        have hproduct : |sourceSlope - frameSlope| * |normal 0| ≤ 1 / 25 := by
          nlinarith [abs_nonneg (sourceSlope - frameSlope),
            abs_nonneg (normal 0)]
        nlinarith [abs_nonneg frameSlope]
      linarith
    exact hpositive.trans hmain
  have hrotatedZero :
      (pureWZ2HorizontalRotation frameSlope normal) 0 =
        (normal 0 + frameSlope * normal 1) / denominator :=
    pureWZ2HorizontalRotation_coord_zero frameSlope normal
  have hcoordLower : 1 / 16 ≤
      |(pureWZ2HorizontalRotation frameSlope normal) 0| := by
    rw [hrotatedZero, abs_div, abs_of_pos hdenPos]
    have hquot : (1 / 10 : ℝ) / denominator ≤
        |normal 0 + frameSlope * normal 1| / denominator := by gcongr
    have hconst : (1 / 16 : ℝ) ≤ (1 / 10) / denominator := by
      rw [le_div_iff₀ hdenPos]
      nlinarith
    exact hconst.trans hquot
  have hcoordNorm :
      |(pureWZ2HorizontalRotation frameSlope normal) 0| ≤
        ‖xzProjectedNormal
          (pureWZ2HorizontalRotation frameSlope normal)‖ := by
    have hcoord := PiLp.norm_apply_le
      (xzProjectedNormal (pureWZ2HorizontalRotation frameSlope normal))
      (0 : Fin 3)
    have hcoord' :
        |(pureWZ2HorizontalRotation frameSlope normal) 0| ≤
          ‖xzProjectedNormal
            (pureWZ2HorizontalRotation frameSlope normal)‖ := by
      have hxzCoord :
          (xzProjectedNormal
            (pureWZ2HorizontalRotation frameSlope normal)) 0 =
            (pureWZ2HorizontalRotation frameSlope normal) 0 := by
        simp [xzProjectedNormal]
      rw [← hxzCoord]
      exact hcoord
    exact hcoord'
  rw [pureWZ2FrameProjectedNormal_norm]
  exact hcoordLower.trans hcoordNorm

/-- Coordinate diameter of one complete weighted label in the fixed frame. -/
theorem pureWZ2_weightedLabel_rotated_xz_diameter
    {sigma grainLoss slabLoss delta gap : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale}
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    {label : ℤ × ℤ} (hlabel : label ∈ popular.keptLabels)
    {frameSlope : ℝ}
    (hgap : 0 ≤ gap)
    (hclose : |cfg.globalGrains.slope
        ((pureWZ2PaperCellCenter delta
          (popular.label_anchor label hlabel)) 2) - frameSlope| ≤
      gap)
    {first second : Point3}
    (hfirst : first ∈ pureWZ2WeightedCroppedLabelRegion popular label)
    (hsecond : second ∈ pureWZ2WeightedCroppedLabelRegion popular label) :
    |pureWZ2HorizontalRotation frameSlope first 0 -
        pureWZ2HorizontalRotation frameSlope second 0| ≤
          8 * delta + 2 * gap ∧
      |pureWZ2HorizontalRotation frameSlope first 2 -
        pureWZ2HorizontalRotation frameSlope second 2| ≤ 8 * delta := by
  let anchor := pureWZ2PaperCellCenter delta
    (popular.label_anchor label hlabel)
  have hanchorBox : anchor ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
    have hanchorActive := (mem_pureWZ2GlobalGrainFiber
      cfg.globalGrains.slope delta popular.activeCells label
      (popular.label_anchor label hlabel)).mp
        (popular.label_anchor_mem label hlabel) |>.1
    have hanchorCell : popular.label_anchor label hlabel ∈
        wz1PaperActiveCells scaleData.slabShading cfg.extremal.delta_pos := by
      simpa [popular.activeCells_eq] using hanchorActive
    rcases pureWZ2_activeCellCenter_mem_union
        cfg.extremal.delta_pos scaleData.slab_cubical hanchorCell with
      ⟨index, hcarrier⟩
    exact (scaleData.slabShading.subset_body index hcarrier).2
  let rotation := pureWZ2HorizontalRotation frameSlope
  have hpair := pureWZ2_fixedFrame_globalGrain_pair_diameter
    cfg.globalGrains.slope cfg.extremal.delta_pos.le hgap anchor hclose
    ⟨popular.label_grain_containment label hlabel hfirst.1, hfirst.2⟩
    ⟨popular.label_grain_containment label hlabel hsecond.1, hsecond.2⟩
  exact ⟨hpair.1, by simpa [rotation] using hpair.2⟩

/-- An occupied point of a selected label is still close to the fixed frame
slope.  Same-label cells have the same vertical grid index, so the source
height differs from the label anchor height by at most `delta / 2`. -/
theorem PureWZ2RotatedWeightedCommonYCore.selected_source_frame_close_of_gap
    {sigma grainLoss slabLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale}
    {popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData}
    {frameSlope : ℝ}
    (data : PureWZ2RotatedWeightedCommonYCore
      cfg scale scaleData popular frameSlope)
    {gap : ℝ}
    (hlabelClose : ∀ label (hlabel : label ∈ data.selectedLabels),
      |cfg.globalGrains.slope
          ((pureWZ2PaperCellCenter delta
            (popular.label_anchor label
              (data.selectedLabels_subset hlabel))) 2) - frameSlope| ≤ gap)
    {label : ℤ × ℤ} (hlabel : label ∈ data.selectedLabels)
    {source : Point3}
    (hsource : source ∈ pureWZ2WeightedCroppedLabelRegion popular label) :
    |cfg.globalGrains.slope (source 2) - frameSlope| ≤
      delta / 2 + gap := by
  have hkept := data.selectedLabels_subset hlabel
  have hsourceBox : source ∈ Kakeya.Streamlined.axisBox 2 2 2 := hsource.2
  let anchorCell := popular.label_anchor label hkept
  let anchor := pureWZ2PaperCellCenter delta anchorCell
  rw [pureWZ2WeightedCroppedLabelRegion_eq] at hsource
  rcases Set.mem_iUnion₂.mp hsource with ⟨sourceCell, hsourceFiber, hsourceCell⟩
  have hanchorFiber := popular.label_anchor_mem label hkept
  have hsourceLabel := (mem_pureWZ2GlobalGrainFiber
    cfg.globalGrains.slope delta popular.activeCells label sourceCell).mp
      hsourceFiber |>.2
  have hanchorLabel := (mem_pureWZ2GlobalGrainFiber
    cfg.globalGrains.slope delta popular.activeCells label anchorCell).mp
      hanchorFiber |>.2
  have hcenters := pureWZ2_cellCenters_same_label cfg.extremal.delta_pos
    cfg.globalGrains.slope (hsourceLabel.trans hanchorLabel.symm)
  have hcenterZ : (pureWZ2PaperCellCenter delta sourceCell) 2 = anchor 2 := by
    exact sub_eq_zero.mp (abs_eq_zero.mp hcenters.1)
  have hsourceCenter := pureWZ2_point_close_to_cellCenter
    cfg.extremal.delta_pos hsourceCell (2 : Fin 3)
  have hheight : |source 2 - anchor 2| ≤ delta / 2 := by
    simpa [hcenterZ] using hsourceCenter
  have hsourceHeight : source 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    simpa [Kakeya.Streamlined.axisBox, abs_le] using hsourceBox.2.2
  have hanchorActive := (mem_pureWZ2GlobalGrainFiber
    cfg.globalGrains.slope delta popular.activeCells label anchorCell).mp
      hanchorFiber |>.1
  have hanchorCellActive : anchorCell ∈ wz1PaperActiveCells
      scaleData.slabShading cfg.extremal.delta_pos := by
    simpa [popular.activeCells_eq] using hanchorActive
  rcases pureWZ2_activeCellCenter_mem_union cfg.extremal.delta_pos
      scaleData.slab_cubical hanchorCellActive with ⟨index, hanchorCarrier⟩
  have hanchorHeight : anchor 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    have hbox :=
      (scaleData.slabShading.subset_body index hanchorCarrier).2
    have habs : |anchor 2| ≤ 1 := by
      have hraw := hbox.2.2
      change |anchor 2| ≤ 2 / 2 at hraw
      norm_num at hraw ⊢
      exact hraw
    exact abs_le.mp habs
  have hslope : |cfg.globalGrains.slope (source 2) -
      cfg.globalGrains.slope (anchor 2)| ≤ |source 2 - anchor 2| := by
    simpa [Real.dist_eq] using
      cfg.globalGrains.slope_lipschitzOn.dist_le_mul
        (source 2) hsourceHeight (anchor 2) hanchorHeight
  have hanchorFrame := hlabelClose label hlabel
  calc
    |cfg.globalGrains.slope (source 2) - frameSlope| ≤
        |cfg.globalGrains.slope (source 2) -
          cfg.globalGrains.slope (anchor 2)| +
        |cfg.globalGrains.slope (anchor 2) - frameSlope| := by
      simpa only [show cfg.globalGrains.slope (source 2) - frameSlope =
          (cfg.globalGrains.slope (source 2) -
            cfg.globalGrains.slope (anchor 2)) +
          (cfg.globalGrains.slope (anchor 2) - frameSlope) by ring] using
        abs_add_le
          (cfg.globalGrains.slope (source 2) -
            cfg.globalGrains.slope (anchor 2))
          (cfg.globalGrains.slope (anchor 2) - frameSlope)
    _ ≤ delta / 2 + gap :=
      add_le_add (hslope.trans hheight) hanchorFrame

/-- Quadratic-frame specialization retained for existing Lemma-31 callers. -/
theorem PureWZ2RotatedWeightedCommonYData.selected_source_frame_close
    {sigma grainLoss slabLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale}
    {popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData}
    {frameSlope : ℝ}
    (data : PureWZ2RotatedWeightedCommonYData
      cfg scale scaleData popular frameSlope)
    {label : ℤ × ℤ} (hlabel : label ∈ data.selectedLabels)
    {source : Point3}
    (hsource : source ∈ pureWZ2WeightedCroppedLabelRegion popular label) :
    |cfg.globalGrains.slope (source 2) - frameSlope| ≤
      delta / 2 + 2 * scale.1 ^ 2 := by
  exact data.toPureWZ2RotatedWeightedCommonYCore
    |>.selected_source_frame_close_of_gap data.selected_label_frame_close
      hlabel hsource

/-- A whole weighted label has projection diameter `O(delta)` along any
unit normal whose rotated y-component vanishes. -/
theorem pureWZ2_weightedLabel_projection_diameter
    {sigma grainLoss slabLoss delta gap : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale}
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    {label : ℤ × ℤ} (hlabel : label ∈ popular.keptLabels)
    {frameSlope : ℝ} {normal : Point3}
    (hgap : 0 ≤ gap)
    (hclose : |cfg.globalGrains.slope
        ((pureWZ2PaperCellCenter delta
          (popular.label_anchor label hlabel)) 2) - frameSlope| ≤
      gap)
    (hnormal : ‖normal‖ = 1)
    (hrotatedY : pureWZ2HorizontalRotation frameSlope normal 1 = 0)
    {first second : Point3}
    (hfirst : first ∈ pureWZ2WeightedCroppedLabelRegion popular label)
    (hsecond : second ∈ pureWZ2WeightedCroppedLabelRegion popular label) :
    |inner ℝ first normal - inner ℝ second normal| ≤
      16 * delta + 2 * gap := by
  let anchor := pureWZ2PaperCellCenter delta
    (popular.label_anchor label hlabel)
  have hfirstGrain := popular.label_grain_containment label hlabel hfirst.1
  have hsecondGrain := popular.label_grain_containment label hlabel hsecond.1
  have hanchorBox : anchor ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
    have hanchorActive := (mem_pureWZ2GlobalGrainFiber
      cfg.globalGrains.slope delta popular.activeCells label
      (popular.label_anchor label hlabel)).mp
        (popular.label_anchor_mem label hlabel) |>.1
    have hanchorCell : popular.label_anchor label hlabel ∈
        wz1PaperActiveCells scaleData.slabShading cfg.extremal.delta_pos := by
      simpa [popular.activeCells_eq] using hanchorActive
    have hanchorUnion := pureWZ2_activeCellCenter_mem_union
      cfg.extremal.delta_pos scaleData.slab_cubical hanchorCell
    rcases hanchorUnion with ⟨index, hcarrier⟩
    exact (scaleData.slabShading.subset_body index hcarrier).2
  let rotation := pureWZ2HorizontalRotation frameSlope
  have hrotatedY' : (rotation normal) 1 = 0 := by
    simpa [rotation] using hrotatedY
  have hnormalRotUnit : ‖rotation normal‖ = 1 := by
    rw [rotation.norm_map, hnormal]
  have hnormalRot0 : |(rotation normal) 0| ≤ 1 := by
    have h := PiLp.norm_apply_le (rotation normal) (0 : Fin 3)
    simpa [Real.norm_eq_abs, hnormalRotUnit] using h
  have hnormalRot2 : |(rotation normal) 2| ≤ 1 := by
    have h := PiLp.norm_apply_le (rotation normal) (2 : Fin 3)
    simpa [Real.norm_eq_abs, hnormalRotUnit] using h
  have hpair := pureWZ2_weightedLabel_rotated_xz_diameter popular hlabel
    hgap hclose hfirst hsecond
  have hx := hpair.1
  have hz := hpair.2
  have hinner : inner ℝ first normal - inner ℝ second normal =
      ((rotation first) 0 - (rotation second) 0) * (rotation normal) 0 +
        ((rotation first) 2 - (rotation second) 2) * (rotation normal) 2 := by
    rw [← rotation.inner_map_map first normal,
      ← rotation.inner_map_map second normal]
    rw [PiLp.inner_apply, PiLp.inner_apply]
    simp [Fin.sum_univ_succ, RCLike.inner_apply, hrotatedY', mul_comm]
    ring
  rw [hinner]
  calc
    |((rotation first) 0 - (rotation second) 0) * (rotation normal) 0 +
        ((rotation first) 2 - (rotation second) 2) * (rotation normal) 2|
      ≤ |(rotation first) 0 - (rotation second) 0| * |(rotation normal) 0| +
        |(rotation first) 2 - (rotation second) 2| * |(rotation normal) 2| := by
          calc
            _ ≤ |((rotation first) 0 - (rotation second) 0) *
                  (rotation normal) 0| +
                |((rotation first) 2 - (rotation second) 2) *
                  (rotation normal) 2| := abs_add_le _ _
            _ = _ := by rw [abs_mul, abs_mul]
    _ ≤ (8 * delta + 2 * gap) * 1 + 8 * delta * 1 := by
      have h16delta : 0 ≤ 8 * delta + 2 * gap := by
        exact add_nonneg (mul_nonneg (by norm_num) cfg.extremal.delta_pos.le)
          (mul_nonneg (by norm_num) hgap)
      have h8delta : 0 ≤ 8 * delta := by
        exact mul_nonneg (by norm_num) cfg.extremal.delta_pos.le
      exact add_le_add
        (mul_le_mul hx hnormalRot0 (abs_nonneg _) h16delta)
        (mul_le_mul hz hnormalRot2 (abs_nonneg _) h8delta)
    _ = 16 * delta + 2 * gap := by ring

/-- If a set of common-slice representatives meets every selected label, then
the projection of the complete selected whole-cell shading lies in its
`32 * delta`-thickening.  This is the paper's passage from the common slice
back to the complete global grains. -/
theorem PureWZ2RotatedWeightedCommonYData.scalarProjection_F2_subset_cthickening
    {sigma grainLoss slabLoss delta gap : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale}
    {popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData}
    {frameSlope : ℝ}
    (data : PureWZ2RotatedWeightedCommonYData
      cfg scale scaleData popular frameSlope)
    {normal : Point3}
    (hgap : 0 ≤ gap)
    (hlabelClose : ∀ label (hlabel : label ∈ data.selectedLabels),
      |cfg.globalGrains.slope
          ((pureWZ2PaperCellCenter delta
            (popular.label_anchor label
              (data.selectedLabels_subset hlabel))) 2) - frameSlope| ≤
        gap)
    (hnormal : ‖normal‖ = 1)
    (hrotatedY : pureWZ2HorizontalRotation frameSlope normal 1 = 0) :
    scalarProjection normal data.F2.union ⊆
      Metric.cthickening (16 * delta + 2 * gap)
        (scalarProjection normal
          {point : Point3 |
            point ∈ data.F2.union ∧
            pureWZ2HorizontalRotation frameSlope point 1 = data.y0}) := by
  intro projected hprojected
  rcases hprojected with ⟨point, hpoint, rfl⟩
  rcases data.exists_common_slice_companion hpoint with
    ⟨label, hlabel, hpointLabel, companion, hcompanionLabel,
      hcompanionSlice⟩
  have hcompanionF2 : companion ∈ data.F2.union := by
    rw [data.F2_union_eq, data.selectedCells_eq]
    rw [pureWZ2WeightedCroppedLabelRegion_eq] at hcompanionLabel
    rcases Set.mem_iUnion₂.mp hcompanionLabel with
      ⟨cell, hfiber, hcell⟩
    exact Set.mem_iUnion₂.mpr ⟨cell,
      Finset.mem_biUnion.mpr ⟨label, hlabel, hfiber⟩, hcell⟩
  have hprojection :
      |inner ℝ point normal - inner ℝ companion normal| ≤
        16 * delta + 2 * gap :=
    pureWZ2_weightedLabel_projection_diameter popular
      (data.selectedLabels_subset hlabel)
      hgap (hlabelClose label hlabel) hnormal hrotatedY
      hpointLabel hcompanionLabel
  have hcompanionProjection : inner ℝ companion normal ∈
      scalarProjection normal
        {point : Point3 |
          point ∈ data.F2.union ∧
          pureWZ2HorizontalRotation frameSlope point 1 = data.y0} :=
    ⟨companion, ⟨hcompanionF2, hcompanionSlice⟩, rfl⟩
  have hdist : dist (inner ℝ point normal) (inner ℝ companion normal) ≤
      16 * delta + 2 * gap := by
    simpa [Real.dist_eq] using hprojection
  exact Metric.mem_cthickening_of_dist_le _ _ _ _
    hcompanionProjection hdist

end Kakeya.Assouad

end
