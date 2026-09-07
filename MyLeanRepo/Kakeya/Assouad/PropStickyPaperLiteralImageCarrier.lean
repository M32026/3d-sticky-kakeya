import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralRescalingBounds
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescalingStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment

/-!
# Target: transformed cubical shading lies in its literal paper tube

Proof of `wz2_paper_literal_image_carrier`: every `delta / rho`-grid cube meeting
the literal affine image of a source set contained in one covered source paper tube
lies in the cropped target paper tube with the exact image axis.

## Proof outline

Given `p` in the cubical saturation at scale `eps = delta / rho`:
1. Pick `imagePoint` in the same grid cube, arising from `sourcePoint` in the source carrier.
2. **Axis neighborhood**: Find `q` on the source axis within `6 * delta` of `sourcePoint`.
   Its image `imageQ` lies on the target axis. The linear map norm bound gives
   `dist imagePoint imageQ ≤ 6 * delta / (100 * rho) = 0.06 * eps`. Combined with
   grid diameter `< 2 * eps`, we get `dist p imageQ < 6 * eps`.
3. **Crop bound**: Decompose `v = sourcePoint - z_anchor = w + t • d_source + u` where
   `‖w‖ ≤ 6*delta`, `|t| ≤ 5/2`, `‖u‖ ≤ rho/2`. Bound the perpendicular part and use
   the WZ2 literal coordinate bounds to show all image coordinates are small.
   Adding the grid offset `< 1/12` keeps `p` in `[-1,1]^3`.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- Difference of two WZ2 literal map values is the linear map applied to the difference. -/
lemma wz2LiteralMap_sub
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (p q : Point3) :
    wz2PaperLiteralUnitRescalingMap anchor hrho p -
        wz2PaperLiteralUnitRescalingMap anchor hrho q =
      wz2LiteralLinear (wz1PaperDirection anchor)
        (wz1PaperDirection_norm anchor) rho (p - q) := by
  let z := wz1TubeAxisZeroPoint anchor
  let d := wz1PaperDirection anchor
  let hd := wz1PaperDirection_norm anchor
  let R := householderToE3 d hd
  let S := transverseScaleLin rho
  have h1 : wz2PaperLiteralUnitRescalingMap anchor hrho p =
      (1 / 100 : ℝ) • S (R (p - z)) := by rfl
  have h2 : wz2PaperLiteralUnitRescalingMap anchor hrho q =
      (1 / 100 : ℝ) • S (R (q - z)) := by rfl
  rw [h1, h2]
  have h3 : (1 / 100 : ℝ) • S (R (p - z)) - (1 / 100 : ℝ) • S (R (q - z)) =
      (1 / 100 : ℝ) • (S (R (p - z)) - S (R (q - z))) := by
    rw [← smul_sub]
  rw [h3]
  have h4 : S (R (p - z)) - S (R (q - z)) = S (R (p - q)) := by
    have h5 : S (R (p - z)) - S (R (q - z)) = S (R (p - z) - R (q - z)) := by
      rw [← map_sub S]
    rw [h5]
    have h6 : R (p - z) - R (q - z) = R ((p - z) - (q - z)) := by
      rw [← map_sub R]
    rw [h6]
    have h7 : (p - z) - (q - z) = p - q := by abel
    rw [h7]
  rw [h4]
  rfl

/-- `perpPart d` is additive. -/
lemma perpPart_add (d v w : Point3) :
    perpPart d (v + w) = perpPart d v + perpPart d w := by
  ext i
  simp [perpPart, inner_add_left, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  <;> ring

/-- `perpPart d` is homogeneous. -/
lemma perpPart_smul (d : Point3) (c : ℝ) (v : Point3) :
    perpPart d (c • v) = c • perpPart d v := by
  ext i
  simp [perpPart, inner_smul_left, PiLp.smul_apply, smul_eq_mul]
  <;> ring

/-- Norm of `perpPart d v` is at most norm of `v`. -/
lemma perpPart_norm_le (d : Point3) (hd : ‖d‖ = 1) (v : Point3) :
    ‖perpPart d v‖ ≤ ‖v‖ := by
  have h1 : ‖perpPart d v‖ ^ 2 = ‖v‖ ^ 2 - (inner ℝ v d) ^ 2 := perpPart_norm_sq hd v
  have h2 : (inner ℝ v d) ^ 2 ≥ 0 := by positivity
  have h3 : ‖perpPart d v‖ ^ 2 ≤ ‖v‖ ^ 2 := by linarith
  nlinarith [norm_nonneg (perpPart d v), norm_nonneg v]

/--
The transverse part of the Householder image of a unit vector has norm
`sin(angle)`, which is at most the angular distance.
-/
lemma wz2Literal_transverse_part_angle_bound
    {rho : ℝ}
    {d_source d_anchor : Point3}
    (hds : ‖d_source‖ = 1) (hda : ‖d_anchor‖ = 1)
    (hangle : InnerProductGeometry.angle d_source d_anchor ≤ rho / 2)
    (_hrho : 0 < rho) :
    ‖transversePart (householderToE3 d_anchor hda d_source)‖ ≤ rho / 2 := by
  let R := householderToE3 d_anchor hda
  let angle := InnerProductGeometry.angle d_source d_anchor
  have hinner : inner ℝ d_source d_anchor = Real.cos angle := by
    rw [InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hds hda]
  have hcoord2 : (R d_source) 2 = inner ℝ d_source d_anchor := by
    rw [coord2_eq_inner_e3, householderToE3_symmetric d_anchor hda d_source e3,
      householderToE3_sends_e3_to_d d_anchor hda]
  have hR_norm : ‖R d_source‖ = 1 := by
    rw [householderToE3_norm d_anchor hda d_source, hds]
  have hnorm_sq : ‖transversePart (R d_source)‖ ^ 2 =
      ‖R d_source‖ ^ 2 - (R d_source) 2 ^ 2 := transversePart_norm_sq (R d_source)
  have hsin_sq : ‖transversePart (R d_source)‖ ^ 2 = Real.sin angle ^ 2 := by
    rw [hnorm_sq, hR_norm, hcoord2, hinner]
    have h2 : Real.cos angle ^ 2 + Real.sin angle ^ 2 = 1 := Real.cos_sq_add_sin_sq angle
    have h : (1 : ℝ) ^ 2 - Real.cos angle ^ 2 = Real.sin angle ^ 2 := by linarith
    exact h
  have hsin_nonneg : 0 ≤ Real.sin angle :=
    Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [InnerProductGeometry.angle_nonneg d_source d_anchor],
        by linarith [InnerProductGeometry.angle_le_pi d_source d_anchor]⟩
  have hnorm_eq : ‖transversePart (R d_source)‖ = Real.sin angle := by
    nlinarith [norm_nonneg (transversePart (R d_source))]
  rw [hnorm_eq]
  have hangle_nonneg : 0 ≤ angle := InnerProductGeometry.angle_nonneg d_source d_anchor
  have hsin_le : Real.sin angle ≤ angle := Real.sin_le hangle_nonneg
  linarith

theorem wz2_paper_literal_image_carrier :
    WZ2PaperLiteralImageCarrierStatement := by
  intro delta rho hdelta hrho hrho_one heps_le source anchor
  let eps : ℝ := delta / rho
  have heps_def : eps = delta / rho := by rfl
  intro target hsource hanchor htarget hcover haxis sourceSet hsourceSet p hp
  have heps_pos : 0 < eps := by positivity
  have heps_le24 : eps ≤ 1 / 24 := by
    simpa [eps, heps_def] using heps_le
  have hdelta_le : delta ≤ 1 / 24 := by
    have hde : delta = eps * rho := by
      rw [heps_def] <;> field_simp [hrho.ne'] <;> ring
    rw [hde]
    have h : eps * rho ≤ (1 / 24 : ℝ) * 1 := by gcongr <;> linarith
    simpa using h

  -- Extract imagePoint from cubical saturation
  rcases hp with ⟨imagePoint, himage_in_set, hgrid⟩
  rcases himage_in_set with ⟨sourcePoint, hsourcePoint_in_set, h_eq⟩
  have himage_eq : imagePoint = wz2PaperLiteralUnitRescalingMap anchor hrho sourcePoint := h_eq.symm
  have hsourcePoint_carrier : sourcePoint ∈ wz1PaperTubeCarrier source :=
    hsourceSet hsourcePoint_in_set
  have hsourcePoint_z2 : |sourcePoint 2| ≤ 1 := by
    have hbox : sourcePoint ∈ Kakeya.Streamlined.axisBox 2 2 2 := hsourcePoint_carrier.2
    have h : |sourcePoint 0| ≤ 1 ∧ |sourcePoint 1| ≤ 1 ∧ |sourcePoint 2| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox
    exact h.2.2

  -- Same grid cube => distance < 2*eps
  have hgrid_dist : dist p imagePoint < 2 * eps :=
    have hcell_p : p ∈ wz1PaperGridCube eps (wz1PaperGridIndex eps p) := by simp
    have hcell_img : imagePoint ∈ wz1PaperGridCube eps (wz1PaperGridIndex eps p) := by
      have h : wz1PaperGridIndex eps imagePoint = wz1PaperGridIndex eps p := hgrid.symm
      simpa [mem_wz1PaperGridCube] using h
    wz1_paper_grid_cube_diameter_lt_two_rho heps_pos hcell_p hcell_img

  -- Part 1: Axis neighborhood
  have hthick_source : sourcePoint ∈ Metric.cthickening (6 * delta) (tubeAxisLine source) :=
    hsourcePoint_carrier.1
  have hclosed_source : IsClosed (tubeAxisLine source) := isClosed_tubeAxisLine source
  rcases exists_dist_le_of_mem_cthickening_closed hclosed_source (by positivity) hthick_source with
    ⟨q, hq_line, hq_dist⟩
  set imageQ : Point3 := wz2PaperLiteralUnitRescalingMap anchor hrho q with himageQ_def
  have himageQ_line : imageQ ∈ tubeAxisLine target := by
    have h1 : imageQ ∈ wz2PaperLiteralUnitRescalingMap anchor hrho '' tubeAxisLine source :=
      ⟨q, hq_line, by simp [himageQ_def]⟩
    have h2 : imageQ ∈ tubeAxisLine target := by
      rw [haxis]
      exact h1
    exact h2
  have hlinear_dist : dist imagePoint imageQ ≤ 6 * delta / (100 * rho) := by
    have h1 : imagePoint - imageQ = wz2LiteralLinear (wz1PaperDirection anchor)
        (wz1PaperDirection_norm anchor) rho (sourcePoint - q) := by
      rw [himage_eq]
      exact wz2LiteralMap_sub anchor hrho sourcePoint q
    rw [dist_eq_norm, h1]
    have h2 : ‖sourcePoint - q‖ ≤ 6 * delta := by
      simpa [dist_eq_norm] using hq_dist
    have h3 := wz2LiteralLinear_norm_le (d := wz1PaperDirection anchor)
      (hd := wz1PaperDirection_norm anchor) (hrho := hrho) hrho_one (sourcePoint - q)
    calc
      ‖wz2LiteralLinear (wz1PaperDirection anchor) (wz1PaperDirection_norm anchor) rho (sourcePoint - q)‖
        ≤ ‖sourcePoint - q‖ / (100 * rho) := h3
      _ ≤ (6 * delta) / (100 * rho) := by gcongr
  have h_axis_dist : dist p imageQ < 6 * eps := by
    have h4 : dist p imageQ ≤ dist p imagePoint + dist imagePoint imageQ := dist_triangle p imagePoint imageQ
    have h5 : 6 * delta / (100 * rho) = (6 / 100 : ℝ) * eps := by
      rw [heps_def] <;> field_simp [hrho.ne'] <;> ring
    linarith [h4, hgrid_dist, hlinear_dist, h5]
  have hthick_target : p ∈ Metric.cthickening (6 * eps) (tubeAxisLine target) :=
    Metric.mem_cthickening_of_dist_le p imageQ (6 * eps) (tubeAxisLine target) himageQ_line (by linarith)

  -- Part 2: Crop
  set z_anchor : Point3 := wz1TubeAxisZeroPoint anchor with hz_anchor_def
  set d_anchor : Point3 := wz1PaperDirection anchor with hd_anchor_def
  set z_source : Point3 := wz1TubeAxisZeroPoint source with hz_source_def
  set d_source : Point3 := wz1PaperDirection source with hd_source_def

  -- q = z_source + t • d_source
  have hline_eq : tubeAxisLine source =
      {p | ∃ t : ℝ, p = z_source + t • d_source} :=
    tubeAxisLine_eq_affineSpan source hsource.vertical
  have hq_set : q ∈ {p | ∃ t : ℝ, p = z_source + t • d_source} := by
    rw [← hline_eq] <;> exact hq_line
  rcases hq_set with ⟨t, ht_eq⟩

  set w : Point3 := sourcePoint - q with hw_def
  have hw_norm : ‖w‖ ≤ 6 * delta := by simpa [dist_eq_norm, hw_def] using hq_dist
  set u : Point3 := z_source - z_anchor with hu_def
  have hu_norm : ‖u‖ ≤ rho / 2 := hcover.components.1
  have hangle : InnerProductGeometry.angle d_source d_anchor ≤ rho / 2 := hcover.components.2

  -- Parameter bound |t| ≤ 5/2
  have hz_source2 : z_source 2 = 0 := wz1TubeAxisZeroPoint_coord_two source hsource.vertical
  have hd_source2 : (1 / 2 : ℝ) ≤ d_source 2 := hsource.1
  have hd_source2_pos : 0 < d_source 2 := by linarith
  have hsourcePoint2_eq : sourcePoint 2 = t * d_source 2 + w 2 := by
    have h : sourcePoint = q + w := by simp [hw_def] <;> abel
    rw [h, ht_eq]
    simp [hz_source2, smul_eq_mul] <;> ring
  have h_t_bound : |t| ≤ 5 / 2 := by
    have h1 : |t * d_source 2| ≤ |sourcePoint 2| + |w 2| := by
      have h2 : t * d_source 2 = sourcePoint 2 - w 2 := by linarith
      rw [h2]
      exact abs_sub _ _
    have h3 : |w 2| ≤ ‖w‖ := abs_coord_le_norm w 2
    have h4 : |t| * d_source 2 ≤ 1 + 6 * delta := by
      have h5 : |t * d_source 2| = |t| * d_source 2 := by
        rw [abs_mul, abs_of_pos hd_source2_pos]
      rw [h5] at h1
      linarith [hsourcePoint_z2, h3, hw_norm]
    have h6 : |t| * (1 / 2 : ℝ) ≤ |t| * d_source 2 := by gcongr
    have h7 : |t| ≤ 2 * (1 + 6 * delta) := by linarith
    have h8 : 2 * (1 + 6 * delta) ≤ 5 / 2 := by
      have h9 : delta ≤ 1 / 24 := hdelta_le
      linarith
    linarith

  -- v = sourcePoint - z_anchor = w + t • d_source + u
  set v : Point3 := sourcePoint - z_anchor with hv_def
  have hv_decomp : v = w + t • d_source + u := by
    have h : sourcePoint = q + w := by simp [hw_def] <;> abel
    rw [hv_def, h, ht_eq, hu_def] <;> abel

  -- Bound ‖perpPart d_anchor v‖
  have hperp_decomp : perpPart d_anchor v =
      perpPart d_anchor w + t • perpPart d_anchor d_source + perpPart d_anchor u := by
    rw [hv_decomp]
    rw [perpPart_add d_anchor (w + t • d_source) u, perpPart_add d_anchor w (t • d_source), perpPart_smul d_anchor t d_source]
    <;> abel
  have hperp_norm : ‖perpPart d_anchor v‖ ≤ 6 * delta + 7 * rho / 4 := by
    rw [hperp_decomp]
    have h1 : ‖perpPart d_anchor w + t • perpPart d_anchor d_source + perpPart d_anchor u‖ ≤
        ‖perpPart d_anchor w‖ + ‖t • perpPart d_anchor d_source‖ + ‖perpPart d_anchor u‖ := by
      calc
        ‖perpPart d_anchor w + t • perpPart d_anchor d_source + perpPart d_anchor u‖
          ≤ ‖perpPart d_anchor w + t • perpPart d_anchor d_source‖ + ‖perpPart d_anchor u‖ := norm_add_le _ _
        _ ≤ ‖perpPart d_anchor w‖ + ‖t • perpPart d_anchor d_source‖ + ‖perpPart d_anchor u‖ := by
          have h2 := norm_add_le (perpPart d_anchor w) (t • perpPart d_anchor d_source)
          linarith
    have h2 : ‖t • perpPart d_anchor d_source‖ = |t| * ‖perpPart d_anchor d_source‖ := by
      rw [norm_smul] <;> simp [Real.norm_eq_abs]
    rw [h2] at h1
    have h3 : ‖perpPart d_anchor w‖ ≤ ‖w‖ := perpPart_norm_le d_anchor (wz1PaperDirection_norm anchor) w
    have h4 : ‖perpPart d_anchor u‖ ≤ ‖u‖ := perpPart_norm_le d_anchor (wz1PaperDirection_norm anchor) u
    have h5 : ‖perpPart d_anchor d_source‖ ≤ rho / 2 := by
      have h6 : ‖perpPart d_anchor d_source‖ = ‖transversePart (householderToE3 d_anchor (wz1PaperDirection_norm anchor) d_source)‖ :=
        (householder_transversePart_norm_eq_perpPart (wz1PaperDirection_norm anchor) d_source).symm
      rw [h6]
      exact wz2Literal_transverse_part_angle_bound
        (wz1PaperDirection_norm source) (wz1PaperDirection_norm anchor) hangle hrho
    have h6 : ‖perpPart d_anchor w‖ ≤ 6 * delta := by linarith [h3, hw_norm]
    have h7 : ‖t • perpPart d_anchor d_source‖ ≤ (5 / 2 : ℝ) * (rho / 2) := by
      calc
        ‖t • perpPart d_anchor d_source‖ = |t| * ‖perpPart d_anchor d_source‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ (5 / 2 : ℝ) * (rho / 2) := by gcongr <;> linarith [h_t_bound, h5]
    have h8 : ‖perpPart d_anchor u‖ ≤ rho / 2 := by linarith [h4, hu_norm]
    linarith

  -- imagePoint = L v (since map z_anchor = 0)
  have h_map_zero : wz2PaperLiteralUnitRescalingMap anchor hrho z_anchor = 0 := by
    have h1 : wz2PaperLiteralUnitRescalingMap anchor hrho z_anchor =
        (1 / 100 : ℝ) • transverseScaleLin rho (householderToE3 d_anchor (wz1PaperDirection_norm anchor) (z_anchor - z_anchor)) := by rfl
    rw [h1]
    have h2 : z_anchor - z_anchor = 0 := by abel
    rw [h2]
    simp
  have hL : imagePoint - wz2PaperLiteralUnitRescalingMap anchor hrho z_anchor =
      wz2LiteralLinear d_anchor (wz1PaperDirection_norm anchor) rho v := by
    rw [himage_eq]
    exact wz2LiteralMap_sub anchor hrho sourcePoint z_anchor
  have h_imageQ0 : imagePoint 0 = (wz2LiteralLinear d_anchor (wz1PaperDirection_norm anchor) rho v) 0 := by
    rw [h_map_zero] at hL
    simpa using congr_arg (fun x : Point3 => x 0) hL
  have h_imageQ1 : imagePoint 1 = (wz2LiteralLinear d_anchor (wz1PaperDirection_norm anchor) rho v) 1 := by
    rw [h_map_zero] at hL
    simpa using congr_arg (fun x : Point3 => x 1) hL
  have h_imageQ2 : imagePoint 2 = (wz2LiteralLinear d_anchor (wz1PaperDirection_norm anchor) rho v) 2 := by
    rw [h_map_zero] at hL
    simpa using congr_arg (fun x : Point3 => x 2) hL

  -- Coordinate bounds for imagePoint
  have himage0_bound : |imagePoint 0| ≤ 2 / 100 := by
    rw [h_imageQ0]
    have h1 : |(wz2LiteralLinear d_anchor (wz1PaperDirection_norm anchor) rho v) 0| ≤
        ‖perpPart d_anchor v‖ / (100 * rho) :=
      wz2LiteralLinear_coord0_abs_le (d := d_anchor) (hd := wz1PaperDirection_norm anchor) (hrho := hrho) v
    have h2 : ‖perpPart d_anchor v‖ / (100 * rho) ≤ (6 * delta + 7 * rho / 4) / (100 * rho) := by gcongr
    have h3 : (6 * delta + 7 * rho / 4) / (100 * rho) = (6 * eps + 7 / 4) / 100 := by
      rw [heps_def] <;> field_simp [hrho.ne'] <;> ring
    have h4 : |(wz2LiteralLinear d_anchor (wz1PaperDirection_norm anchor) rho v) 0| ≤ (6 * eps + 7 / 4) / 100 := by
      calc
        _ ≤ ‖perpPart d_anchor v‖ / (100 * rho) := h1
        _ ≤ (6 * delta + 7 * rho / 4) / (100 * rho) := h2
        _ = (6 * eps + 7 / 4) / 100 := h3
    have h5 : 6 * eps ≤ 1 / 4 := by linarith
    linarith

  have himage1_bound : |imagePoint 1| ≤ 2 / 100 := by
    rw [h_imageQ1]
    have h1 : |(wz2LiteralLinear d_anchor (wz1PaperDirection_norm anchor) rho v) 1| ≤
        ‖perpPart d_anchor v‖ / (100 * rho) :=
      wz2LiteralLinear_coord1_abs_le (d := d_anchor) (hd := wz1PaperDirection_norm anchor) (hrho := hrho) v
    have h2 : ‖perpPart d_anchor v‖ / (100 * rho) ≤ (6 * delta + 7 * rho / 4) / (100 * rho) := by gcongr
    have h3 : (6 * delta + 7 * rho / 4) / (100 * rho) = (6 * eps + 7 / 4) / 100 := by
      rw [heps_def] <;> field_simp [hrho.ne'] <;> ring
    have h4 : |(wz2LiteralLinear d_anchor (wz1PaperDirection_norm anchor) rho v) 1| ≤ (6 * eps + 7 / 4) / 100 := by
      calc
        _ ≤ ‖perpPart d_anchor v‖ / (100 * rho) := h1
        _ ≤ (6 * delta + 7 * rho / 4) / (100 * rho) := h2
        _ = (6 * eps + 7 / 4) / 100 := h3
    have h5 : 6 * eps ≤ 1 / 4 := by linarith
    linarith

  have himage2_bound : |imagePoint 2| ≤ 13 / 400 := by
    rw [h_imageQ2]
    have h1 : (wz2LiteralLinear d_anchor (wz1PaperDirection_norm anchor) rho v) 2 =
        (1 / 100 : ℝ) * inner ℝ v d_anchor :=
      wz2LiteralLinear_coord2 (d := d_anchor) (hd := wz1PaperDirection_norm anchor) v
    rw [h1]
    have h2 : |inner ℝ v d_anchor| ≤ 6 * delta + 5 / 2 + rho / 2 := by
      rw [hv_decomp]
      have h3 : inner ℝ (w + t • d_source + u) d_anchor =
          inner ℝ w d_anchor + t * inner ℝ d_source d_anchor + inner ℝ u d_anchor := by
        simp [inner_add_left, inner_smul_left] <;> ring
      rw [h3]
      have h4 : |inner ℝ w d_anchor| ≤ ‖w‖ := by
        calc |inner ℝ w d_anchor| ≤ ‖w‖ * ‖d_anchor‖ := abs_real_inner_le_norm _ _
             _ = ‖w‖ := by rw [wz1PaperDirection_norm anchor] <;> ring
      have h5 : |inner ℝ d_source d_anchor| ≤ 1 := by
        calc |inner ℝ d_source d_anchor| ≤ ‖d_source‖ * ‖d_anchor‖ := abs_real_inner_le_norm _ _
             _ = 1 := by rw [wz1PaperDirection_norm source, wz1PaperDirection_norm anchor] <;> ring
      have h6 : |inner ℝ u d_anchor| ≤ ‖u‖ := by
        calc |inner ℝ u d_anchor| ≤ ‖u‖ * ‖d_anchor‖ := abs_real_inner_le_norm _ _
             _ = ‖u‖ := by rw [wz1PaperDirection_norm anchor] <;> ring
      have h7 : |inner ℝ w d_anchor + t * inner ℝ d_source d_anchor + inner ℝ u d_anchor| ≤
          |inner ℝ w d_anchor| + |t * inner ℝ d_source d_anchor| + |inner ℝ u d_anchor| := by
        have h_abs3 : ∀ (x y z : ℝ), |x + y + z| ≤ |x| + |y| + |z| := by
          intro x y z
          have h1 : |x + y + z| ≤ |x + y| + |z| :=
            abs_add_le (x + y) z
          have h2 : |x + y| ≤ |x| + |y| :=
            abs_add_le x y
          linarith
        exact h_abs3 _ _ _
      have h9 : |t * inner ℝ d_source d_anchor| = |t| * |inner ℝ d_source d_anchor| := by rw [abs_mul]
      have h10 : |t * inner ℝ d_source d_anchor| ≤ 5 / 2 := by
        rw [h9]
        have h11 : |t| * |inner ℝ d_source d_anchor| ≤ (5 / 2 : ℝ) * 1 := by gcongr <;> linarith [h_t_bound, h5]
        linarith
      have h12 : |inner ℝ w d_anchor| ≤ 6 * delta := by linarith [h4, hw_norm]
      have h13 : |inner ℝ u d_anchor| ≤ rho / 2 := by linarith [h6, hu_norm]
      linarith [h7, h9, h10, h12, h13]
    have hpos : (0 : ℝ) < 1 / 100 := by norm_num
    have h10 : |(1 / 100 : ℝ) * inner ℝ v d_anchor| = (1 / 100 : ℝ) * |inner ℝ v d_anchor| := by
      rw [abs_mul, abs_of_pos hpos]
    rw [h10]
    have h11 : (1 / 100 : ℝ) * |inner ℝ v d_anchor| ≤ (1 / 100 : ℝ) * (6 * delta + 5 / 2 + rho / 2) := by gcongr
    have h12 : 6 * delta ≤ 1 / 4 := by linarith
    have h13 : rho / 2 ≤ 1 / 2 := by linarith
    linarith

  -- Grid offset
  have hgrid_off0 : |p 0 - imagePoint 0| ≤ dist p imagePoint := abs_coord_sub_le_dist 0
  have hgrid_off1 : |p 1 - imagePoint 1| ≤ dist p imagePoint := abs_coord_sub_le_dist 1
  have hgrid_off2 : |p 2 - imagePoint 2| ≤ dist p imagePoint := abs_coord_sub_le_dist 2
  have hgrid_lt2 : dist p imagePoint < 1 / 12 := by
    have h : 2 * eps ≤ 1 / 12 := by linarith
    linarith [hgrid_dist]

  -- Final bounds
  have h_abs_add : ∀ (a b : ℝ), |a + b| ≤ |a| + |b| := by
    intro a b
    exact abs_add_le a b
  have hp0 : |p 0| ≤ 1 := by
    have h : |p 0| ≤ |imagePoint 0| + |p 0 - imagePoint 0| := by
      calc |p 0| = |imagePoint 0 + (p 0 - imagePoint 0)| := by ring_nf
        _ ≤ |imagePoint 0| + |p 0 - imagePoint 0| := h_abs_add _ _
    linarith
  have hp1 : |p 1| ≤ 1 := by
    have h : |p 1| ≤ |imagePoint 1| + |p 1 - imagePoint 1| := by
      calc |p 1| = |imagePoint 1 + (p 1 - imagePoint 1)| := by ring_nf
        _ ≤ |imagePoint 1| + |p 1 - imagePoint 1| := h_abs_add _ _
    linarith
  have hp2 : |p 2| ≤ 1 := by
    have h : |p 2| ≤ |imagePoint 2| + |p 2 - imagePoint 2| := by
      calc |p 2| = |imagePoint 2 + (p 2 - imagePoint 2)| := by ring_nf
        _ ≤ |imagePoint 2| + |p 2 - imagePoint 2| := h_abs_add _ _
    linarith

  have hp0' : |p 0| ≤ 2 / 2 := by linarith [hp0]
  have hp1' : |p 1| ≤ 2 / 2 := by linarith [hp1]
  have hp2' : |p 2| ≤ 2 / 2 := by linarith [hp2]
  have hbox : p ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq]
    <;> exact ⟨hp0', hp1', hp2'⟩

  exact ⟨hthick_target, hbox⟩

end Kakeya.Assouad

end
