import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralCanonicalRescaledTube
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperUnitRescalingBasics
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCanonicalDilatedDirection
import MyLeanRepo.Kakeya.Assouad.WZ1.TargetDirectionParallelToImage
import MyLeanRepo.Kakeya.Assouad.PropStickyCommonRescalingGeometryHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.AnchoredRescalingGeometry


/-!
# Helper lemmas for the common-rescaling line-cover transfer

This module provides:
1. Target zero-point identification and distance formula under literal WZ2 rescaling
2. Bound on the difference of orthogonal section points
3. Direction identification from equal affine line images
4. Angle-from-chord bound and transverse scaling norm bounds
-/

noncomputable section

namespace Kakeya.Assouad

open Metric InnerProductGeometry

/-!
### Zero-point identification and distance
-/

/--
Literal version: if a source point lies on the source axis and is in the
anchor-perpendicular plane, then its image under the literal WZ2 map is the
zero point of the target tube.
-/
lemma wz2PaperLiteralAxisZeroPoint_eq_of_mem_axis_of_inner_eq_zero
    {delta rho targetDelta : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    {target : Kakeya.DeltaTube targetDelta}
    (hrho : 0 < rho)
    (htarget : WZ1PaperTubeInLineClass target)
    (haxis :
      tubeAxisLine target =
        wz2PaperLiteralUnitRescalingMap anchor hrho ''
          tubeAxisLine source)
    {sourcePoint : Point3}
    (hsourcePoint : sourcePoint ∈ tubeAxisLine source)
    (hsourcePoint_perp :
      inner ℝ
          (sourcePoint - wz1TubeAxisZeroPoint anchor)
          (wz1PaperDirection anchor) =
        0) :
    wz1TubeAxisZeroPoint target =
      wz2PaperLiteralUnitRescalingMap anchor hrho sourcePoint := by
  apply wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
    htarget.vertical
  · rw [haxis]
    exact ⟨sourcePoint, hsourcePoint, rfl⟩
  · rw [wz2PaperLiteralUnitRescalingMap_coord2, hsourcePoint_perp]
    ring

/--
Literal version: distance between two target zero points equals the distance
between the corresponding source orthogonal section points divided by `100 * rho`.
-/
lemma wz2PaperLiteralRescaledAxisZeroPoint_dist_eq
    {delta rho targetDelta : ℝ}
    {source₁ source₂ : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    {target₁ target₂ : Kakeya.DeltaTube targetDelta}
    (hrho : 0 < rho)
    (htarget₁ : WZ1PaperTubeInLineClass target₁)
    (htarget₂ : WZ1PaperTubeInLineClass target₂)
    (haxis₁ :
      tubeAxisLine target₁ =
        wz2PaperLiteralUnitRescalingMap anchor hrho ''
          tubeAxisLine source₁)
    (haxis₂ :
      tubeAxisLine target₂ =
        wz2PaperLiteralUnitRescalingMap anchor hrho ''
          tubeAxisLine source₂)
    {sourcePoint₁ sourcePoint₂ : Point3}
    (hsourcePoint₁ : sourcePoint₁ ∈ tubeAxisLine source₁)
    (hsourcePoint₂ : sourcePoint₂ ∈ tubeAxisLine source₂)
    (hsourcePoint₁_perp :
      inner ℝ
          (sourcePoint₁ - wz1TubeAxisZeroPoint anchor)
          (wz1PaperDirection anchor) =
        0)
    (hsourcePoint₂_perp :
      inner ℝ
          (sourcePoint₂ - wz1TubeAxisZeroPoint anchor)
          (wz1PaperDirection anchor) =
        0) :
    dist (wz1TubeAxisZeroPoint target₁)
        (wz1TubeAxisZeroPoint target₂) =
      dist sourcePoint₁ sourcePoint₂ / (100 * rho) := by
  rw [
    wz2PaperLiteralAxisZeroPoint_eq_of_mem_axis_of_inner_eq_zero
      hrho htarget₁ haxis₁ hsourcePoint₁ hsourcePoint₁_perp,
    wz2PaperLiteralAxisZeroPoint_eq_of_mem_axis_of_inner_eq_zero
      hrho htarget₂ haxis₂ hsourcePoint₂ hsourcePoint₂_perp,
    dist_eq_norm,
    wz2PaperLiteralUnitRescalingMap_sub]
  have hperp :
      inner ℝ (sourcePoint₁ - sourcePoint₂)
          (wz1PaperDirection anchor) =
        0 := by
    rw [
      show sourcePoint₁ - sourcePoint₂ =
          (sourcePoint₁ - wz1TubeAxisZeroPoint anchor) -
            (sourcePoint₂ - wz1TubeAxisZeroPoint anchor) by
        abel,
      inner_sub_left, hsourcePoint₁_perp,
      hsourcePoint₂_perp, sub_self]
  rw [wz2PaperLiteralUnitRescalingLinear_perp_norm
    anchor hrho _ hperp]
  rfl

/-!
### Bound on orthogonal section point distance
-/

/--
Bound on the distance between two orthogonal section points relative to a
common anchor, given strict fine→middle cover, strict fine→anchor cover,
and factor-two middle→anchor dilated cover.

The bound is `45/14 * rho`.
-/
lemma orthogonal_section_distance_bound
    {delta rho sigma : ℝ}
    {fine : Kakeya.DeltaTube delta}
    {middle : Kakeya.DeltaTube rho}
    {anchor : Kakeya.DeltaTube sigma}
    (hsigma : 0 < sigma)
    (hsigmaOne : sigma ≤ 1)
    (hrho_nonneg : 0 ≤ rho)
    (hcoverFM : WZ1PaperTubeCovers fine middle)
    (hcoverFA : WZ1PaperTubeCovers fine anchor)
    (hcoverMA : WZ2PaperDilatedTubeCovers 2 middle anchor) :
    ‖wz1PaperOrthogonalSectionPoint fine anchor -
        wz1PaperOrthogonalSectionPoint middle anchor‖ ≤
      45 / 14 * rho := by
  set zeroFine := wz1TubeAxisZeroPoint fine
  set zeroMiddle := wz1TubeAxisZeroPoint middle
  set zeroAnchor := wz1TubeAxisZeroPoint anchor
  set dirFine := wz1PaperDirection fine
  set dirMiddle := wz1PaperDirection middle
  set dirAnchor := wz1PaperDirection anchor
  set tFine := wz1PaperOrthogonalSectionParameter fine anchor
  set tMiddle := wz1PaperOrthogonalSectionParameter middle anchor
  set pFine := wz1PaperOrthogonalSectionPoint fine anchor
  set pMiddle := wz1PaperOrthogonalSectionPoint middle anchor
  set aFine := inner ℝ dirFine dirAnchor
  set aMiddle := inner ℝ dirMiddle dirAnchor
  set nFine := inner ℝ (zeroFine - zeroAnchor) dirAnchor
  set nMiddle := inner ℝ (zeroMiddle - zeroAnchor) dirAnchor

  have hnormFine : ‖dirFine‖ = 1 := wz1PaperDirection_norm fine
  have hnormMiddle : ‖dirMiddle‖ = 1 := wz1PaperDirection_norm middle
  have hnormAnchor : ‖dirAnchor‖ = 1 := wz1PaperDirection_norm anchor

  have hFM_zero : dist zeroFine zeroMiddle ≤ rho / 2 :=
    hcoverFM.components.1
  have hFM_angle :
      InnerProductGeometry.angle dirFine dirMiddle ≤ rho / 2 :=
    hcoverFM.components.2
  have hFA_zero : dist zeroFine zeroAnchor ≤ sigma / 2 :=
    hcoverFA.components.1
  have hMA_zero : dist zeroMiddle zeroAnchor ≤ sigma :=
    hcoverMA.components.1

  have haFine : 7 / 8 ≤ aFine :=
    wz1PaperTubeCovers.inner_direction_ge_seven_eighths
      hsigmaOne hcoverFA
  have haMiddle : 1 / 2 ≤ aMiddle :=
    hcoverMA.inner_direction_ge_half hsigmaOne
  have haFine_pos : 0 < aFine := by linarith
  have haMiddle_pos : 0 < aMiddle := by linarith
  have haFine_le_one : aFine ≤ 1 := by
    have h : |aFine| ≤ ‖dirFine‖ * ‖dirAnchor‖ :=
      abs_real_inner_le_norm _ _
    rw [hnormFine, hnormAnchor, mul_one] at h
    have h2 : 0 ≤ aFine := by linarith
    rw [abs_of_nonneg h2] at h
    exact h

  have hchordFM : ‖dirFine - dirMiddle‖ ≤ rho / 2 :=
    (unit_norm_sub_le_angle hnormFine hnormMiddle).trans hFM_angle

  have hpFine_eq : pFine = zeroFine + tFine • dirFine := rfl
  have hpMiddle_eq : pMiddle = zeroMiddle + tMiddle • dirMiddle := rfl

  have hinnerFine_ne : aFine ≠ 0 := by linarith
  have hinnerMiddle_ne : aMiddle ≠ 0 := by linarith

  have htFine_abs : |tFine| ≤ sigma :=
    abs_wz1PaperOrthogonalSectionParameter_le
      hsigma hsigmaOne hcoverFA
  have htMiddle_abs : |tMiddle| ≤ 2 * sigma := by
    have hinnerPos : 0 < aMiddle := by linarith
    have hzero : dist zeroMiddle zeroAnchor ≤ sigma := hcoverMA.components.1
    have hnumerator : |nMiddle| ≤ sigma := by
      calc
        |nMiddle| ≤ ‖zeroMiddle - zeroAnchor‖ * ‖dirAnchor‖ :=
          abs_real_inner_le_norm _ _
        _ = dist zeroMiddle zeroAnchor := by
          rw [hnormAnchor, mul_one, dist_eq_norm]
        _ ≤ sigma := hzero
    have h_eq : tMiddle = -nMiddle / aMiddle := by
      simp [tMiddle, wz1PaperOrthogonalSectionParameter]; rfl
    rw [h_eq]
    rw [abs_div, abs_neg, abs_of_pos hinnerPos]
    exact (div_le_iff₀ hinnerPos).mpr (by nlinarith)

  have hnFine_abs : |nFine| ≤ sigma / 2 := by
    calc
      |nFine| ≤ ‖zeroFine - zeroAnchor‖ * ‖dirAnchor‖ :=
        abs_real_inner_le_norm _ _
      _ = dist zeroFine zeroAnchor := by
        rw [hnormAnchor, mul_one, dist_eq_norm]
      _ ≤ sigma / 2 := hFA_zero

  have hnMiddle_abs : |nMiddle| ≤ sigma := by
    calc
      |nMiddle| ≤ ‖zeroMiddle - zeroAnchor‖ * ‖dirAnchor‖ :=
        abs_real_inner_le_norm _ _
      _ = dist zeroMiddle zeroAnchor := by
        rw [hnormAnchor, mul_one, dist_eq_norm]
      _ ≤ sigma := hMA_zero

  have hndiff_abs : |nMiddle - nFine| ≤ rho / 2 := by
    have h : nMiddle - nFine =
        inner ℝ (zeroMiddle - zeroFine) dirAnchor := by
      simp [nFine, nMiddle, inner_sub_left]
    rw [h]
    calc
      |inner ℝ (zeroMiddle - zeroFine) dirAnchor|
          ≤ ‖zeroMiddle - zeroFine‖ * ‖dirAnchor‖ :=
        abs_real_inner_le_norm _ _
      _ = dist zeroMiddle zeroFine := by
        rw [hnormAnchor, mul_one, dist_eq_norm]
      _ = dist zeroFine zeroMiddle := by rw [dist_comm]
      _ ≤ rho / 2 := hFM_zero

  have hadiff_abs : |aMiddle - aFine| ≤ rho / 2 := by
    have h : aMiddle - aFine =
        inner ℝ (dirMiddle - dirFine) dirAnchor := by
      simp [aFine, aMiddle, inner_sub_left]
    rw [h]
    calc
      |inner ℝ (dirMiddle - dirFine) dirAnchor|
          ≤ ‖dirMiddle - dirFine‖ * ‖dirAnchor‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖dirMiddle - dirFine‖ := by
        rw [hnormAnchor, mul_one]
      _ = ‖dirFine - dirMiddle‖ := by rw [norm_sub_rev]
      _ ≤ rho / 2 := hchordFM

  have htFine_formula : tFine = -nFine / aFine := by
    simp [tFine, wz1PaperOrthogonalSectionParameter]; rfl
  have htMiddle_formula : tMiddle = -nMiddle / aMiddle := by
    simp [tMiddle, wz1PaperOrthogonalSectionParameter]; rfl

  have hparam_diff :
      |tFine - tMiddle| ≤ 12 / 7 * rho := by
    rw [htFine_formula, htMiddle_formula]
    have hnum :
        (-nFine / aFine) - (-nMiddle / aMiddle) =
          (nMiddle * aFine - nFine * aMiddle) / (aFine * aMiddle) := by
      field_simp [haFine_pos.ne', haMiddle_pos.ne']; ring
    rw [hnum]
    have hnum2 :
        nMiddle * aFine - nFine * aMiddle =
          aFine * (nMiddle - nFine) - nFine * (aMiddle - aFine) := by
      ring
    rw [hnum2]
    have hbound :
        |aFine * (nMiddle - nFine) - nFine * (aMiddle - aFine)| ≤
          aFine * |nMiddle - nFine| + |nFine| * |aMiddle - aFine| := by
      calc
        _ ≤ |aFine * (nMiddle - nFine)| + |nFine * (aMiddle - aFine)| :=
          by apply abs_sub
        _ = aFine * |nMiddle - nFine| + |nFine| * |aMiddle - aFine| := by
          rw [abs_mul, abs_mul, abs_of_nonneg haFine_pos.le]
    have hdenom_pos : 0 < aFine * aMiddle := mul_pos haFine_pos haMiddle_pos
    have habs_denom : |aFine * aMiddle| = aFine * aMiddle :=
      abs_of_pos hdenom_pos
    rw [abs_div, habs_denom]
    rw [div_le_iff₀ hdenom_pos]
    have h_lhs :
        |aFine * (nMiddle - nFine) - nFine * (aMiddle - aFine)| ≤
          aFine * (rho / 2) + (sigma / 2) * (rho / 2) := by
      calc
        _ ≤ aFine * |nMiddle - nFine| + |nFine| * |aMiddle - aFine| := hbound
        _ ≤ aFine * (rho / 2) + (sigma / 2) * (rho / 2) := by gcongr
    have h1 : aFine * (rho / 2) + (sigma / 2) * (rho / 2) ≤ 3 / 4 * rho := by
      have h2 : aFine ≤ 1 := haFine_le_one
      have h3 : sigma ≤ 1 := hsigmaOne
      have h4 : 0 ≤ rho := hrho_nonneg
      nlinarith
    have h4 : 3 / 4 * rho ≤ aFine * aMiddle * (12 / 7 * rho) := by
      have h5 : aFine * aMiddle ≥ 7 / 16 := by
        have h6 : aFine ≥ 7 / 8 := haFine
        have h7 : aMiddle ≥ 1 / 2 := haMiddle
        nlinarith
      have h8 : 0 ≤ rho := hrho_nonneg
      nlinarith
    have h_rhs :
        aFine * (rho / 2) + (sigma / 2) * (rho / 2) ≤
          aFine * aMiddle * (12 / 7 * rho) := by
      calc
        _ ≤ 3 / 4 * rho := h1
        _ ≤ aFine * aMiddle * (12 / 7 * rho) := h4
    linarith

  have hdecomp :
      pFine - pMiddle =
        (zeroFine - zeroMiddle) +
          (tFine - tMiddle) • dirFine +
          tMiddle • (dirFine - dirMiddle) := by
    rw [hpFine_eq, hpMiddle_eq]
    simp [smul_sub, sub_smul]; abel

  rw [hdecomp]
  calc
    ‖(zeroFine - zeroMiddle) +
        (tFine - tMiddle) • dirFine +
        tMiddle • (dirFine - dirMiddle)‖
        ≤ ‖zeroFine - zeroMiddle‖ +
            ‖(tFine - tMiddle) • dirFine‖ +
            ‖tMiddle • (dirFine - dirMiddle)‖ := by
          calc
            _ ≤ ‖(zeroFine - zeroMiddle) + (tFine - tMiddle) • dirFine‖ +
                  ‖tMiddle • (dirFine - dirMiddle)‖ :=
              norm_add_le _ _
            _ ≤ ‖zeroFine - zeroMiddle‖ + ‖(tFine - tMiddle) • dirFine‖ +
                  ‖tMiddle • (dirFine - dirMiddle)‖ := by
              have h := norm_add_le (zeroFine - zeroMiddle)
                ((tFine - tMiddle) • dirFine)
              linarith
    _ = dist zeroFine zeroMiddle + |tFine - tMiddle| +
          |tMiddle| * ‖dirFine - dirMiddle‖ := by
        have h1 : ‖zeroFine - zeroMiddle‖ = dist zeroFine zeroMiddle := by
          rw [dist_eq_norm]
        have h2 : ‖(tFine - tMiddle) • dirFine‖ = |tFine - tMiddle| := by
          rw [norm_smul, hnormFine, mul_one, Real.norm_eq_abs]
        have h3 : ‖tMiddle • (dirFine - dirMiddle)‖ =
            |tMiddle| * ‖dirFine - dirMiddle‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        rw [h1, h2, h3]
    _ ≤ rho / 2 + 12 / 7 * rho + 2 * sigma * (rho / 2) := by
        gcongr
    _ = rho / 2 + 12 / 7 * rho + sigma * rho := by ring
    _ ≤ rho / 2 + 12 / 7 * rho + rho := by
      have h : sigma * rho ≤ rho := by
        have h5 : sigma ≤ 1 := hsigmaOne
        have h6 : 0 ≤ rho := hrho_nonneg
        nlinarith
      linarith
    _ = 45 / 14 * rho := by ring

/-!
### Direction identification
-/

/--
If the target tube axis is the literal rescaling image of the source axis,
then the paper direction of the target is the normalized linear image of
the source paper direction.
-/
lemma literal_target_direction_eq_normalize
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
    wz1PaperDirection target =
      NormedSpace.normalize
        (wz2PaperLiteralUnitRescalingLinear anchor
          (wz1PaperDirection source)) := by
  set sourceDir := wz1PaperDirection source
  set anchorDir := wz1PaperDirection anchor
  set linearMap := wz2PaperLiteralUnitRescalingLinear anchor
  set imageDir := linearMap sourceDir
  set sourceZero := wz1TubeAxisZeroPoint source
  set rescaling := wz2PaperLiteralUnitRescalingMap anchor hrho

  have hsourceDirUnit : ‖sourceDir‖ = 1 := wz1PaperDirection_norm source

  have hsourceRange : tubeAxisLine source =
      Set.range (fun t : ℝ => sourceZero + t • sourceDir) :=
    wz2PaperTubeAxisLine_eq_range source

  have himageRange : (rescaling '' tubeAxisLine source) =
      Set.range (fun t : ℝ => rescaling sourceZero + t • imageDir) := by
    rw [hsourceRange]
    exact wz2PaperLiteralUnitRescalingMap_image_range anchor hrho sourceZero sourceDir

  have hbase_mem : rescaling sourceZero ∈ tubeAxisLine target := by
    rw [haxis, himageRange]
    exact ⟨0, by simp⟩
  have hbase1_mem : rescaling sourceZero + imageDir ∈ tubeAxisLine target := by
    rw [haxis, himageRange]
    exact ⟨1, by simp⟩

  rcases hbase_mem with ⟨s1, hs1⟩
  rcases hbase1_mem with ⟨s2, hs2⟩

  have hdir_eq : imageDir = (s2 - s1) • target.direction := by
    calc
      imageDir = (rescaling sourceZero + imageDir) - rescaling sourceZero := by abel
      _ = (target.base + s2 • target.direction) - (target.base + s1 • target.direction) := by rw [hs2, hs1]
      _ = (s2 - s1) • target.direction := by module

  have hscalar_ne : (s2 - s1) ≠ 0 := by
    intro h
    rw [h, zero_smul] at hdir_eq
    exact literal_direction_ne_zero (source := source) (anchor := anchor) hrho hdir_eq

  set c : ℝ := (s2 - s1)⁻¹ with hc
  have hc_ne : c ≠ 0 := inv_ne_zero hscalar_ne
  have htarget_dir_eq : target.direction = c • imageDir := by
    have h : (s2 - s1) • target.direction = imageDir := hdir_eq.symm
    have h2 : c • ((s2 - s1) • target.direction) = c • imageDir := by rw [h]
    have h3 : c • ((s2 - s1) • target.direction) = target.direction := by
      rw [smul_smul, hc] <;> field_simp [hscalar_ne] <;> exact one_smul ℝ target.direction
    rw [h3] at h2
    exact h2

  have hinner_pos : 0 < inner ℝ sourceDir anchorDir := by
    have h : 7 / 8 ≤ inner ℝ sourceDir anchorDir :=
      wz1PaperTubeCovers.inner_direction_ge_seven_eighths hrhoOne hcover
    linarith

  have himageDir2_pos : 0 < imageDir 2 := by
    have hcoord : imageDir 2 = (1 / 100 : ℝ) * inner ℝ sourceDir anchorDir := by
      simp [imageDir, linearMap, wz2PaperLiteralUnitRescalingLinear, unitRescalingLinear_coord2] <;> ring
    rw [hcoord]
    positivity

  have htargetPaper2_pos : 0 < wz1PaperDirection target 2 := by
    have h : 1 / 2 ≤ wz1PaperDirection target 2 := htarget.1
    linarith

  have hmain : ∀ (k : ℝ), 0 < k → wz1PaperDirection target = k • imageDir →
      wz1PaperDirection target = NormedSpace.normalize imageDir := by
    intro k hk hk_eq
    have hnorm1 : NormedSpace.normalize (wz1PaperDirection target) = wz1PaperDirection target := by
      rw [NormedSpace.normalize_eq_self_of_norm_eq_one (wz1PaperDirection_norm target)]
    have hnorm2 : NormedSpace.normalize (k • imageDir) = NormedSpace.normalize imageDir :=
      NormedSpace.normalize_smul_of_pos hk imageDir
    have h_eq1 : NormedSpace.normalize (wz1PaperDirection target) = NormedSpace.normalize (k • imageDir) := by rw [hk_eq]
    rw [hnorm1, hnorm2] at h_eq1
    exact h_eq1

  have hcases : wz1PaperDirection target = target.direction ∨ wz1PaperDirection target = -target.direction := by
    unfold wz1PaperDirection
    split_ifs <;> tauto

  rcases hcases with (hcase | hcase)
  · have hpos : 0 < c := by
      have h : (wz1PaperDirection target) 2 = c * imageDir 2 := by
        rw [hcase, htarget_dir_eq] <;> simp
      rw [h] at htargetPaper2_pos
      exact (mul_pos_iff_of_pos_right himageDir2_pos).mp htargetPaper2_pos
    exact hmain c hpos (by rw [hcase, htarget_dir_eq])
  · have hpos : 0 < -c := by
      have h : (wz1PaperDirection target) 2 = (-c) * imageDir 2 := by
        rw [hcase, htarget_dir_eq] <;> simp
      rw [h] at htargetPaper2_pos
      exact (mul_pos_iff_of_pos_right himageDir2_pos).mp htargetPaper2_pos
    have h_eq : wz1PaperDirection target = (-c) • imageDir := by
      rw [hcase, htarget_dir_eq] <;> simp
    exact hmain (-c) hpos h_eq

/--
Generalized direction identification using only positive inner product.
-/
lemma literal_target_direction_eq_normalize_of_inner_pos
    {delta rho targetDelta : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    {target : Kakeya.DeltaTube targetDelta}
    (hrho : 0 < rho)
    (hsource : WZ1PaperTubeInLineClass source)
    (htarget : WZ1PaperTubeInLineClass target)
    (haxis : tubeAxisLine target =
        wz2PaperLiteralUnitRescalingMap anchor hrho '' tubeAxisLine source)
    (hinner_pos : 0 < inner ℝ (wz1PaperDirection source) (wz1PaperDirection anchor)) :
    wz1PaperDirection target =
      NormedSpace.normalize
        (wz2PaperLiteralUnitRescalingLinear anchor
          (wz1PaperDirection source)) := by
  set sourceDir := wz1PaperDirection source
  set anchorDir := wz1PaperDirection anchor
  set linearMap := wz2PaperLiteralUnitRescalingLinear anchor
  set imageDir := linearMap sourceDir
  set sourceZero := wz1TubeAxisZeroPoint source
  set rescaling := wz2PaperLiteralUnitRescalingMap anchor hrho

  have hsourceDirUnit : ‖sourceDir‖ = 1 := wz1PaperDirection_norm source

  have hsourceRange : tubeAxisLine source =
      Set.range (fun t : ℝ => sourceZero + t • sourceDir) :=
    wz2PaperTubeAxisLine_eq_range source

  have himageRange : (rescaling '' tubeAxisLine source) =
      Set.range (fun t : ℝ => rescaling sourceZero + t • imageDir) := by
    rw [hsourceRange]
    exact wz2PaperLiteralUnitRescalingMap_image_range anchor hrho sourceZero sourceDir

  have hbase_mem : rescaling sourceZero ∈ tubeAxisLine target := by
    rw [haxis, himageRange]
    exact ⟨0, by simp⟩
  have hbase1_mem : rescaling sourceZero + imageDir ∈ tubeAxisLine target := by
    rw [haxis, himageRange]
    exact ⟨1, by simp⟩

  rcases hbase_mem with ⟨s1, hs1⟩
  rcases hbase1_mem with ⟨s2, hs2⟩

  have hdir_eq : imageDir = (s2 - s1) • target.direction := by
    calc
      imageDir = (rescaling sourceZero + imageDir) - rescaling sourceZero := by abel
      _ = (target.base + s2 • target.direction) - (target.base + s1 • target.direction) := by rw [hs2, hs1]
      _ = (s2 - s1) • target.direction := by module

  have hscalar_ne : (s2 - s1) ≠ 0 := by
    intro h
    rw [h, zero_smul] at hdir_eq
    exact literal_direction_ne_zero (source := source) (anchor := anchor) hrho hdir_eq

  set c : ℝ := (s2 - s1)⁻¹ with hc
  have hc_ne : c ≠ 0 := inv_ne_zero hscalar_ne
  have htarget_dir_eq : target.direction = c • imageDir := by
    have h : (s2 - s1) • target.direction = imageDir := hdir_eq.symm
    have h2 : c • ((s2 - s1) • target.direction) = c • imageDir := by rw [h]
    have h3 : c • ((s2 - s1) • target.direction) = target.direction := by
      rw [smul_smul, hc] <;> field_simp [hscalar_ne] <;> exact one_smul ℝ target.direction
    rw [h3] at h2
    exact h2

  have himageDir2_pos : 0 < imageDir 2 := by
    have hcoord : imageDir 2 = (1 / 100 : ℝ) * inner ℝ sourceDir anchorDir := by
      simp [imageDir, linearMap, wz2PaperLiteralUnitRescalingLinear, unitRescalingLinear_coord2] <;> ring
    rw [hcoord]
    positivity

  have htargetPaper2_pos : 0 < wz1PaperDirection target 2 := by
    have h : 1 / 2 ≤ wz1PaperDirection target 2 := htarget.1
    linarith

  have hmain : ∀ (k : ℝ), 0 < k → wz1PaperDirection target = k • imageDir →
      wz1PaperDirection target = NormedSpace.normalize imageDir := by
    intro k hk hk_eq
    have hnorm1 : NormedSpace.normalize (wz1PaperDirection target) = wz1PaperDirection target := by
      rw [NormedSpace.normalize_eq_self_of_norm_eq_one (wz1PaperDirection_norm target)]
    have hnorm2 : NormedSpace.normalize (k • imageDir) = NormedSpace.normalize imageDir :=
      NormedSpace.normalize_smul_of_pos hk imageDir
    have h_eq1 : NormedSpace.normalize (wz1PaperDirection target) = NormedSpace.normalize (k • imageDir) := by rw [hk_eq]
    rw [hnorm1, hnorm2] at h_eq1
    exact h_eq1

  have hcases : wz1PaperDirection target = target.direction ∨ wz1PaperDirection target = -target.direction := by
    unfold wz1PaperDirection
    split_ifs <;> tauto

  rcases hcases with (hcase | hcase)
  · have hpos : 0 < c := by
      have h : (wz1PaperDirection target) 2 = c * imageDir 2 := by
        rw [hcase, htarget_dir_eq] <;> simp
      rw [h] at htargetPaper2_pos
      exact (mul_pos_iff_of_pos_right himageDir2_pos).mp htargetPaper2_pos
    exact hmain c hpos (by rw [hcase, htarget_dir_eq])
  · have hpos : 0 < -c := by
      have h : (wz1PaperDirection target) 2 = (-c) * imageDir 2 := by
        rw [hcase, htarget_dir_eq] <;> simp
      rw [h] at htargetPaper2_pos
      exact (mul_pos_iff_of_pos_right himageDir2_pos).mp htargetPaper2_pos
    have h_eq : wz1PaperDirection target = (-c) • imageDir := by
      rw [hcase, htarget_dir_eq] <;> simp
    exact hmain (-c) hpos h_eq

/-!
### Angle bounds and transverse scaling norm bounds
-/

/--
For unit vectors, the angle is at most `π/2` times the chordal distance.
-/
lemma angle_le_pi_div_two_mul_norm_sub
    {u v : Point3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    InnerProductGeometry.angle u v ≤ (Real.pi / 2 : ℝ) * ‖u - v‖ := by
  set θ := InnerProductGeometry.angle u v
  have hθ_nonneg : 0 ≤ θ := InnerProductGeometry.angle_nonneg u v
  have hθ_le_pi : θ ≤ Real.pi := InnerProductGeometry.angle_le_pi u v

  have hcos : inner ℝ u v = Real.cos θ := by
    have h3 := InnerProductGeometry.cos_angle_mul_norm_mul_norm u v
    rw [hu, hv] at h3
    linarith

  have h1 : ‖u - v‖ ^ 2 = 2 - 2 * Real.cos θ := by
    have h4 : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * inner ℝ u v + ‖v‖ ^ 2 := norm_sub_sq_real u v
    rw [h4, hu, hv, hcos] <;> ring

  have hsin_nonneg : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_nonneg]) (by linarith [Real.pi_nonneg])

  have h_chord : ‖u - v‖ = 2 * Real.sin (θ / 2) := by
    have h5 : ‖u - v‖ ^ 2 = (2 * Real.sin (θ / 2)) ^ 2 := by
      rw [h1]
      have h61 : Real.cos θ = Real.cos (2 * (θ / 2)) := by ring_nf
      rw [h61]
      have h62 : Real.cos (2 * (θ / 2)) = 2 * Real.cos (θ / 2) ^ 2 - 1 := Real.cos_two_mul (θ / 2)
      rw [h62]
      have h63 : Real.sin (θ / 2) ^ 2 + Real.cos (θ / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (θ / 2)
      have h64 : 2 * Real.cos (θ / 2) ^ 2 - 1 = 1 - 2 * Real.sin (θ / 2) ^ 2 := by linarith
      rw [h64] <;> ring
    have h7 : 0 ≤ ‖u - v‖ := by positivity
    have h8 : 0 ≤ 2 * Real.sin (θ / 2) := by positivity
    nlinarith

  have h_sin_bound : ∀ (x : ℝ), 0 ≤ x → x ≤ Real.pi / 2 → Real.sin x ≥ 2 * x / Real.pi := by
    intro x hx0 hx1
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    set y := -x with hy_def
    have hy1 : -(Real.pi / 2) ≤ y := by
      rw [hy_def] <;> linarith [hpi_pos]
    have hy2 : y ≤ 0 := by
      rw [hy_def] <;> linarith
    have h : Real.sin y ≤ (2 / Real.pi) * y := Real.sin_le_mul hy1 hy2
    have hsin_y : Real.sin y = -Real.sin x := by
      rw [hy_def, Real.sin_neg] <;> ring
    rw [hsin_y, hy_def] at h
    have h' : (2 / Real.pi) * x ≤ Real.sin x := by simpa using h
    have h'' : 2 * x / Real.pi = (2 / Real.pi) * x := by ring
    rw [h'']
    exact h'

  have h13 : Real.sin (θ / 2) ≥ 2 * (θ / 2) / Real.pi :=
    h_sin_bound (θ / 2) (by linarith [Real.pi_nonneg]) (by linarith [Real.pi_nonneg])

  rw [h_chord]
  have h14 : θ ≤ Real.pi * Real.sin (θ / 2) := by
    have h15 : 0 < Real.pi := Real.pi_pos
    calc
      θ = Real.pi * (θ / Real.pi) := by field_simp [h15.ne'] <;> ring
      _ = Real.pi * (2 * (θ / 2) / Real.pi) := by ring
      _ ≤ Real.pi * Real.sin (θ / 2) := by gcongr
  have h16 : Real.pi * Real.sin (θ / 2) = (Real.pi / 2 : ℝ) * (2 * Real.sin (θ / 2)) := by ring
  rw [h16] at h14
  exact h14

/--
Transverse scaling of a unit vector has norm at least one when `sigma ≤ 1`.
-/
lemma transverseScaleLin_norm_ge_one
    {u : Point3} (hu : ‖u‖ = 1) {sigma : ℝ} (hsigma : 0 < sigma)
    (hsigmaOne : sigma ≤ 1) :
    1 ≤ ‖transverseScaleLin sigma u‖ := by
  have h1 : ‖transverseScaleLin sigma u‖ ^ 2 =
      (1 / sigma ^ 2) * ((u 0) ^ 2 + (u 1) ^ 2) + (u 2) ^ 2 :=
    transverseScaleLin_norm_sq sigma hsigma u
  set a := (u 0) ^ 2 + (u 1) ^ 2 with ha_def
  set b := (u 2) ^ 2 with hb_def
  have h2 : a + b = 1 := by
    have h21 : inner ℝ u u = (u 0) ^ 2 + (u 1) ^ 2 + (u 2) ^ 2 := by
      simp [inner, Fin.sum_univ_succ] <;> ring
    have h22 : inner ℝ u u = ‖u‖ ^ 2 := inner_self_eq_norm_sq_to_K u
    have h23 : ‖u‖ ^ 2 = 1 := by rw [hu] <;> norm_num
    simp only [ha_def, hb_def] at * <;> linarith
  have h4 : 0 < sigma ^ 2 := by positivity
  have h5 : 1 / sigma ^ 2 ≥ 1 := by
    have h6 : sigma ^ 2 ≤ 1 := by nlinarith
    exact (one_le_div h4).mpr h6
  have h7 : (1 / sigma ^ 2) * a + b ≥ 1 := by
    have h8 : (1 / sigma ^ 2) * a + b = 1 + a * (1 / sigma ^ 2 - 1) := by
      have h9 : a + b = 1 := h2
      linarith
    rw [h8]
    have h10 : 0 ≤ a * (1 / sigma ^ 2 - 1) := by
      apply mul_nonneg
      · positivity
      · linarith
    linarith
  have h11 : ‖transverseScaleLin sigma u‖ ^ 2 ≥ 1 := by
    rw [h1]
    simpa [ha_def, hb_def] using h7
  have h12 : 0 ≤ ‖transverseScaleLin sigma u‖ := by positivity
  have h13 : 1 ≤ ‖transverseScaleLin sigma u‖ := by nlinarith
  exact h13

end Kakeya.Assouad

end
