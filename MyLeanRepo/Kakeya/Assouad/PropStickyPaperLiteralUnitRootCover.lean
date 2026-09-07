import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRootCoverStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralCommonRescalingLineCoverHelpers
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Unit-scale vertical root cover for literal target tubes

The factor-two line cover follows from the target zero-point bound
`3 / 200` and direction angle bound `π / 6`.  Carrier containment follows
because the fixed vertical root carrier contains the whole crop box.
-/

noncomputable section

namespace Kakeya.Assouad

open InnerProductGeometry Kakeya.Streamlined

lemma public_direction_close_e3
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hcover : WZ1PaperTubeCovers source anchor) :
    ‖unitRescalingLinear
        (wz1PaperDirection anchor)
        (wz1PaperDirection_norm anchor)
        rho
        (wz1PaperDirection source) - e3‖ ≤ 1 / 2 := by
  let rotation := householderToE3
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor)
  let scale := rho
  have hrotation_coarse :
      rotation (wz1PaperDirection anchor) = e3 :=
    householderToE3_sends_d_to_e3 _ _
  have hscale_e3 : transverseScaleLin scale e3 = e3 := by
    ext i
    fin_cases i <;>
      simp [transverseScaleLin_coord0, transverseScaleLin_coord1,
        transverseScaleLin_coord2, e3]
  have hsource_chord :
      ‖wz1PaperDirection source - wz1PaperDirection anchor‖ ≤
        rho / 2 :=
    (unit_norm_sub_le_angle
      (wz1PaperDirection_norm source)
      (wz1PaperDirection_norm anchor)).trans
        hcover.components.2
  have hrotation_chord :
      ‖rotation
          (wz1PaperDirection source -
            wz1PaperDirection anchor)‖ ≤
        rho / 2 := by
    rw [rotation.norm_map]
    exact hsource_chord
  have hrewrite :
      unitRescalingLinear
          (wz1PaperDirection anchor)
          (wz1PaperDirection_norm anchor)
          rho (wz1PaperDirection source) - e3 =
        transverseScaleLin scale
          (rotation
            (wz1PaperDirection source -
              wz1PaperDirection anchor)) := by
    calc
      _ =
          transverseScaleLin scale
              (rotation (wz1PaperDirection source)) -
            transverseScaleLin scale
              (rotation (wz1PaperDirection anchor)) := by
        rw [hrotation_coarse, hscale_e3]
        rfl
      _ =
          transverseScaleLin scale
            (rotation (wz1PaperDirection source) -
              rotation (wz1PaperDirection anchor)) := by
        exact (map_sub (transverseScaleLin scale) _ _).symm
      _ =
          transverseScaleLin scale
            (rotation
              (wz1PaperDirection source -
                wz1PaperDirection anchor)) := by
        exact congrArg (transverseScaleLin scale)
          (map_sub rotation _ _).symm
  rw [hrewrite]
  calc
    _ ≤
        (1 / scale) *
          ‖rotation
            (wz1PaperDirection source -
              wz1PaperDirection anchor)‖ :=
      transverseScaleLin_norm_bound scale hrho hrhoOne _
    _ ≤ (1 / scale) * (rho / 2) := by gcongr
    _ = 1 / 2 := by
      dsimp only [scale]
      field_simp [hrho.ne'] <;> ring

lemma angle_normalize_le_pi_six
    (u : Point3) (h : ‖u - e3‖ ≤ 1 / 2) :
    InnerProductGeometry.angle
        (NormedSpace.normalize u) e3 ≤
      Real.pi / 6 := by
  have hu_pos : 0 < ‖u‖ := by
    have hrev : ‖e3‖ - ‖u‖ ≤ ‖e3 - u‖ :=
      norm_sub_norm_le e3 u
    rw [e3_norm] at hrev
    have h' : ‖e3 - u‖ = ‖u - e3‖ := by
      rw [norm_sub_rev]
    rw [h'] at hrev
    linarith
  set v : Point3 := NormedSpace.normalize u with hv_def
  have hv_norm : ‖v‖ = 1 :=
    NormedSpace.norm_normalize
      (norm_ne_zero_iff.mp hu_pos.ne')
  set r : ℝ := ‖u‖ with hr_def
  have hpos : 0 < r := hu_pos
  have hu_eq : u = r • v := by
    have h1 : v = (1 / r) • u := by
      simpa [hv_def, NormedSpace.normalize, hr_def] using rfl
    have h2 : r • v = u := by
      rw [h1, smul_smul]
      have h3 : r * (1 / r) = 1 := by
        field_simp [hpos.ne'] <;> ring
      rw [h3]
      simp
    exact h2.symm
  have hnorm2 : ‖u - e3‖ ^ 2 ≤ 1 / 4 := by
    nlinarith [norm_nonneg (u - e3)]
  have hcalc :
      ‖u - e3‖ ^ 2 =
        r ^ 2 - 2 * r * inner ℝ v e3 + 1 := by
    have h5 : u - e3 = r • v - e3 := by rw [hu_eq]
    rw [h5]
    have h6 :
        ‖r • v - e3‖ ^ 2 =
          ‖r • v‖ ^ 2 -
            2 * inner ℝ (r • v) e3 + ‖e3‖ ^ 2 :=
      norm_sub_sq_real (r • v) e3
    rw [h6]
    have h7 : ‖r • v‖ ^ 2 = r ^ 2 := by
      have h71 : ‖r • v‖ = |r| * ‖v‖ := norm_smul r v
      rw [h71, hv_norm, abs_of_pos hpos]
      ring
    have h8 :
        inner ℝ (r • v) e3 = r * inner ℝ v e3 := by
      rw [inner_smul_left]
      simp
    rw [h7, h8, e3_norm]
    ring
  rw [hcalc] at hnorm2
  have h15' :
      r ^ 2 + 3 / 4 ≤
        (2 * r) * inner ℝ v e3 := by
    nlinarith
  have h16 :
      inner ℝ v e3 ≥
        (r ^ 2 + 3 / 4) / (2 * r) := by
    have h17 :
        (r ^ 2 + 3 / 4) / (2 * r) ≤
          ((2 * r) * inner ℝ v e3) / (2 * r) := by
      gcongr
    have h18 :
        ((2 * r) * inner ℝ v e3) / (2 * r) =
          inner ℝ v e3 := by
      field_simp [hpos.ne'] <;> ring
    rw [h18] at h17
    exact h17
  have h17 :
      (r ^ 2 + 3 / 4) / (2 * r) =
        r / 2 + 3 / (8 * r) := by
    field_simp [hpos.ne']
    ring
  rw [h17] at h16
  have hsqrt3_sq : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have h9 :
      4 * r ^ 2 - 4 * Real.sqrt 3 * r + 3 ≥ 0 := by
    have h10 : (2 * r - Real.sqrt 3) ^ 2 ≥ 0 := by
      positivity
    have h11 :
        (2 * r - Real.sqrt 3) ^ 2 =
          4 * r ^ 2 - 4 * Real.sqrt 3 * r +
            (Real.sqrt 3) ^ 2 := by
      ring
    rw [h11, hsqrt3_sq] at h10
    exact h10
  have h13 :
      r / 2 + 3 / (8 * r) - Real.sqrt 3 / 2 =
        (4 * r ^ 2 - 4 * Real.sqrt 3 * r + 3) /
          (8 * r) := by
    field_simp [hpos.ne']
    ring
  have h19 :
      (4 * r ^ 2 - 4 * Real.sqrt 3 * r + 3) /
          (8 * r) ≥
        0 :=
    div_nonneg h9 (mul_nonneg (by norm_num) hpos.le)
  have h20 :
      r / 2 + 3 / (8 * r) ≥ Real.sqrt 3 / 2 := by
    have h21 :
        r / 2 + 3 / (8 * r) - Real.sqrt 3 / 2 ≥ 0 := by
      rw [h13]
      exact h19
    linarith
  have hinner : inner ℝ v e3 ≥ Real.sqrt 3 / 2 := by
    calc
      inner ℝ v e3 ≥ r / 2 + 3 / (8 * r) := h16
      _ ≥ Real.sqrt 3 / 2 := h20
  have hangle :
      InnerProductGeometry.angle v e3 =
        Real.arccos (inner ℝ v e3) := by
    simp [InnerProductGeometry.angle, hv_norm, e3_norm]
  rw [hangle]
  have hcos_pi6 :
      Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
    rw [Real.cos_pi_div_six] <;> ring
  have hle :
      Real.cos (Real.pi / 6) ≤ inner ℝ v e3 := by
    rw [hcos_pi6]
    exact hinner
  have h_arccos_cos :
      Real.arccos (Real.cos (Real.pi / 6)) =
        Real.pi / 6 := by
    rw [Real.arccos_cos] <;> linarith [Real.pi_pos]
  have hfinal :
      Real.arccos (inner ℝ v e3) ≤
        Real.arccos (Real.cos (Real.pi / 6)) :=
    Real.arccos_le_arccos hle
  rw [h_arccos_cos] at hfinal
  exact hfinal

/-- Exact image-axis provenance upgrades the fixed line-class lower bound to
the stronger vertical-direction bound used by the M9 Lemma 4.3 normal. -/
lemma literal_target_paperDirection_vertical_ge_sqrt_three_half
    {delta rho targetDelta : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    {target : Kakeya.DeltaTube targetDelta}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hsource : WZ1PaperTubeInLineClass source)
    (hcover : WZ1PaperTubeCovers source anchor)
    (htarget : WZ1PaperTubeInLineClass target)
    (haxis : tubeAxisLine target =
        wz2PaperLiteralUnitRescalingMap anchor hrho '' tubeAxisLine source) :
    Real.sqrt 3 / 2 ≤ wz1PaperDirection target (2 : Fin 3) := by
  let u := unitRescalingLinear
    (wz1PaperDirection anchor)
    (wz1PaperDirection_norm anchor) rho
    (wz1PaperDirection source)
  have hdirection :
      wz1PaperDirection target = NormedSpace.normalize u := by
    have h := literal_target_direction_eq_normalize
      hrho hrhoOne hsource hcover htarget haxis
    have hnormalize :
        NormedSpace.normalize
            (wz2PaperLiteralUnitRescalingLinear anchor
              (wz1PaperDirection source)) =
          NormedSpace.normalize u := by
      have hlinear :
          wz2PaperLiteralUnitRescalingLinear anchor
              (wz1PaperDirection source) =
            (1 / 100 : ℝ) • u := by
        rfl
      rw [hlinear, NormedSpace.normalize_smul_of_pos
        (by norm_num : (0 : ℝ) < 1 / 100)]
    rw [h, hnormalize]
  have hclose : ‖u - e3‖ ≤ 1 / 2 :=
    literal_unitRescalingLinear_direction_close_e3 hrho hrhoOne hcover
  have hangle :
      InnerProductGeometry.angle (wz1PaperDirection target) e3 ≤
        Real.pi / 6 := by
    rw [hdirection]
    exact angle_normalize_le_pi_six u hclose
  have hcos :
      Real.cos (Real.pi / 6) ≤
        Real.cos (InnerProductGeometry.angle
          (wz1PaperDirection target) e3) := by
    exact Real.cos_le_cos_of_nonneg_of_le_pi
      (InnerProductGeometry.angle_nonneg _ _)
      (by linarith [Real.pi_pos]) hangle
  have hinner :
      inner ℝ (wz1PaperDirection target) e3 =
        Real.cos (InnerProductGeometry.angle
          (wz1PaperDirection target) e3) :=
    InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one
      (wz1PaperDirection_norm target) e3_norm
  have hcoordinate :
      inner ℝ (wz1PaperDirection target) e3 =
        wz1PaperDirection target (2 : Fin 3) := by
    simpa [e3] using
      EuclideanSpace.inner_single_right (2 : Fin 3) (1 : ℝ)
        (wz1PaperDirection target)
  rw [Real.cos_pi_div_six] at hcos
  rw [← hinner, hcoordinate] at hcos
  simpa only [div_eq_mul_inv] using hcos

lemma root_carrier_contains_crop_box :
    axisBox 2 2 2 ⊆
      Metric.cthickening 6
        (tubeAxisLine wz2PaperLiteralUnitRootTube) := by
  intro x hx
  have h0 : |x (0 : Fin 3)| ≤ 1 := by
    simpa [axisBox] using hx.1
  have h1 : |x (1 : Fin 3)| ≤ 1 := by
    simpa [axisBox] using hx.2.1
  let y : Point3 := (x (2 : Fin 3)) • e3
  have hy_axis :
      y ∈ tubeAxisLine wz2PaperLiteralUnitRootTube := by
    refine ⟨x (2 : Fin 3), ?_⟩
    simp [wz2PaperLiteralUnitRootTube, y, e3]
    <;> ext i
    <;> fin_cases i
    <;> simp [e3]
    <;> ring
  have hnorm_sq :
      ‖x - y‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
    have h2 :
        inner ℝ (x - y) (x - y) =
          (x 0) ^ 2 + (x 1) ^ 2 := by
      rw [PiLp.inner_apply]
      simp [Fin.sum_univ_succ, y, e3] <;> ring
    have h3 :
        inner ℝ (x - y) (x - y) = ‖x - y‖ ^ 2 := by
      simpa using real_inner_self_eq_norm_sq (x - y)
    linarith
  have hdist : dist x y ≤ 6 := by
    rw [dist_eq_norm]
    have h0' : (x 0) ^ 2 ≤ 1 := by
      have := abs_le.mp h0
      nlinarith
    have h1' : (x 1) ^ 2 ≤ 1 := by
      have := abs_le.mp h1
      nlinarith
    have hnorm : ‖x - y‖ ≤ Real.sqrt 2 := by
      rw [← sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)]
      rw [hnorm_sq, Real.sq_sqrt (by norm_num)]
      nlinarith
    have hsqrt2_lt_six : Real.sqrt 2 < 6 := by
      nlinarith [Real.sqrt_nonneg 2,
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith
  exact Metric.mem_cthickening_of_dist_le
    x y 6 (tubeAxisLine wz2PaperLiteralUnitRootTube)
    hy_axis hdist

theorem wz2_paper_literal_unit_root_cover :
    WZ2PaperLiteralUnitRootCoverStatement := by
  intro delta sigma hsigma hsigmaOne source anchor
    hsource hanchor hcover target htarget htarget_axis
  set sourceDir := wz1PaperDirection source
  set anchorDir := wz1PaperDirection anchor
  set sourcePoint := wz1PaperOrthogonalSectionPoint source anchor
  set sourceZero := wz1TubeAxisZeroPoint source
  set anchorZero := wz1TubeAxisZeroPoint anchor
  let u :=
    unitRescalingLinear anchorDir
      (wz1PaperDirection_norm anchor) sigma sourceDir
  have hdir_eq :
      wz1PaperDirection target = NormedSpace.normalize u := by
    have h :=
      literal_target_direction_eq_normalize
        hsigma hsigmaOne hsource hcover htarget htarget_axis
    have hnormalize_same :
        NormedSpace.normalize
            (wz2PaperLiteralUnitRescalingLinear
              anchor sourceDir) =
          NormedSpace.normalize u := by
      have hdef :
          wz2PaperLiteralUnitRescalingLinear anchor sourceDir =
            (1 / 100 : ℝ) • u := by
        rfl
      rw [hdef,
        NormedSpace.normalize_smul_of_pos
          (by norm_num : (0 : ℝ) < 1 / 100)]
    rw [h, hnormalize_same]
  have hclose : ‖u - e3‖ ≤ 1 / 2 :=
    public_direction_close_e3 hsigma hsigmaOne hcover
  have hangle_le :
      InnerProductGeometry.angle
          (wz1PaperDirection target) e3 ≤
        Real.pi / 6 := by
    rw [hdir_eq]
    exact angle_normalize_le_pi_six u hclose
  have hsourcePoint_mem :
      sourcePoint ∈ tubeAxisLine source :=
    wz1PaperOrthogonalSectionPoint_mem_axis source anchor
  have hinner_ne : inner ℝ sourceDir anchorDir ≠ 0 := by
    have h :=
      wz1PaperTubeCovers.inner_direction_ge_seven_eighths
        hsigmaOne hcover
    linarith
  have hperp :
      inner ℝ (sourcePoint - anchorZero) anchorDir = 0 :=
    wz1PaperOrthogonalSectionPoint_perp hinner_ne
  have hzero_eq :
      wz1TubeAxisZeroPoint target =
        wz2PaperLiteralUnitRescalingMap
          anchor hsigma sourcePoint :=
    wz2PaperLiteralAxisZeroPoint_eq_of_mem_axis_of_inner_eq_zero
      hsigma htarget htarget_axis hsourcePoint_mem hperp
  have hmap_linear :
      wz2PaperLiteralUnitRescalingMap anchor hsigma sourcePoint =
        wz2PaperLiteralUnitRescalingLinear
          anchor (sourcePoint - anchorZero) := by
    have hzeroMap :
        wz2PaperLiteralUnitRescalingMap
            anchor hsigma anchorZero =
          0 := by
      dsimp only [anchorZero]
      simp [wz2PaperLiteralUnitRescalingMap, unitRescalingMap]
    have hsub :=
      wz2PaperLiteralUnitRescalingMap_sub
        anchor hsigma sourcePoint anchorZero
    rw [hzeroMap, sub_zero] at hsub
    exact hsub
  have hsourcePoint_eq :
      sourcePoint =
        sourceZero +
          wz1PaperOrthogonalSectionParameter source anchor •
            sourceDir := rfl
  have hzero_dist :
      dist sourceZero anchorZero ≤ sigma / 2 :=
    hcover.components.1
  have hparam_abs :
      |wz1PaperOrthogonalSectionParameter source anchor| ≤ sigma :=
    abs_wz1PaperOrthogonalSectionParameter_le
      hsigma hsigmaOne hcover
  have hdist :
      ‖sourcePoint - anchorZero‖ ≤ 3 * sigma / 2 := by
    rw [hsourcePoint_eq]
    have hrewrite :
        sourceZero +
              wz1PaperOrthogonalSectionParameter source anchor •
                sourceDir -
            anchorZero =
          (sourceZero - anchorZero) +
            wz1PaperOrthogonalSectionParameter source anchor •
              sourceDir := by
      ext i
      simp
      ring
    rw [hrewrite]
    calc
      _ ≤
          ‖sourceZero - anchorZero‖ +
            ‖wz1PaperOrthogonalSectionParameter source anchor •
              sourceDir‖ :=
        norm_add_le _ _
      _ =
          dist sourceZero anchorZero +
            |wz1PaperOrthogonalSectionParameter source anchor| := by
        rw [dist_eq_norm, norm_smul,
          wz1PaperDirection_norm source, mul_one]
        simp [Real.norm_eq_abs]
      _ ≤ 3 * sigma / 2 := by linarith
  have hnorm_val :
      ‖wz2PaperLiteralUnitRescalingLinear
        anchor (sourcePoint - anchorZero)‖ =
        ‖sourcePoint - anchorZero‖ / (100 * sigma) :=
    wz2PaperLiteralUnitRescalingLinear_perp_norm
      anchor hsigma _ hperp
  have hzero_norm :
      ‖wz1TubeAxisZeroPoint target‖ ≤ 3 / 200 := by
    rw [hzero_eq, hmap_linear, hnorm_val]
    calc
      ‖sourcePoint - anchorZero‖ / (100 * sigma) ≤
          (3 * sigma / 2) / (100 * sigma) := by gcongr
      _ = 3 / 200 := by
        field_simp [hsigma.ne']
        ring
  have hroot_zero :
      wz1TubeAxisZeroPoint wz2PaperLiteralUnitRootTube = 0 := by
    simp [wz1TubeAxisZeroPoint,
      wz2PaperLiteralUnitRootTube, e3]
    <;> ext i
    <;> fin_cases i
    <;> simp [e3]
    <;> ring
  have hroot_dir :
      wz1PaperDirection wz2PaperLiteralUnitRootTube = e3 := by
    simp [wz1PaperDirection, wz2PaperLiteralUnitRootTube, e3]
    <;> norm_num
  have hline_dist :
      wz1PaperLineDistance
          target wz2PaperLiteralUnitRootTube ≤
        1 := by
    dsimp only [wz1PaperLineDistance]
    rw [hroot_zero, hroot_dir]
    simp only [dist_zero_right]
    calc
      ‖wz1TubeAxisZeroPoint target‖ +
            InnerProductGeometry.angle
              (wz1PaperDirection target) e3 ≤
          (3 / 200 : ℝ) + Real.pi / 6 := by gcongr
      _ ≤ 1 := by
        linarith [Real.pi_lt_four]
  have h1 :
      WZ2PaperDilatedTubeCovers 2
        target wz2PaperLiteralUnitRootTube := by
    simpa [WZ2PaperDilatedTubeCovers] using hline_dist
  have h2 :
      WZ2PaperTubeCarrierCovers
        target wz2PaperLiteralUnitRootTube := by
    intro p hp
    have hthick :
        p ∈ Metric.cthickening
            (6 * (1 : ℝ))
            (tubeAxisLine wz2PaperLiteralUnitRootTube) := by
      have h6 : (6 * (1 : ℝ)) = (6 : ℝ) := by
        norm_num
      rw [h6]
      exact root_carrier_contains_crop_box hp.2
    exact ⟨hthick, hp.2⟩
  exact ⟨h1, h2⟩

end Kakeya.Assouad

end
