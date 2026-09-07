import MyLeanRepo.Kakeya.Assouad.PropStickyStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRescalingDistinctnessStatements
import MyLeanRepo.Kakeya.Assouad.TubeAlignmentGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.AnchoredRescalingGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.UnitRescaling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Basic geometry of the paper unit rescaling

This module records the affine and linear identities used in the lower
distortion estimate preceding WZ Lemma 3.3, equation (3.2).
-/

noncomputable section

namespace Kakeya.Assouad

/-- Linear part of the paper unit-rescaling map. -/
def wz1PaperUnitRescalingLinear
    {rho : ℝ} (coarse : Kakeya.DeltaTube rho) :
    Point3 →ₗ[ℝ] Point3 :=
  unitRescalingLinear
    (wz1PaperDirection coarse)
    (wz1PaperDirection_norm coarse)
    (100 * rho)

lemma wz1PaperUnitRescalingMap_sub
    {rho : ℝ} (coarse : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) (point₁ point₂ : Point3) :
    wz1PaperUnitRescalingMap coarse hrho point₁ -
        wz1PaperUnitRescalingMap coarse hrho point₂ =
      wz1PaperUnitRescalingLinear coarse (point₁ - point₂) := by
  simp [wz1PaperUnitRescalingMap, wz1PaperUnitRescalingLinear,
    unitRescalingMap, unitRescalingLinear]

lemma wz1PaperUnitRescalingMap_add
    {rho : ℝ} (coarse : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) (point vector : Point3) :
    wz1PaperUnitRescalingMap coarse hrho (point + vector) =
      wz1PaperUnitRescalingMap coarse hrho point +
        wz1PaperUnitRescalingLinear coarse vector := by
  have hsub :=
    wz1PaperUnitRescalingMap_sub
      coarse hrho (point + vector) point
  have hdiff : point + vector - point = vector := by abel
  rw [hdiff] at hsub
  calc
    wz1PaperUnitRescalingMap coarse hrho (point + vector) =
        wz1PaperUnitRescalingMap coarse hrho point +
          (wz1PaperUnitRescalingMap coarse hrho (point + vector) -
            wz1PaperUnitRescalingMap coarse hrho point) := by
      abel
    _ = wz1PaperUnitRescalingMap coarse hrho point +
        wz1PaperUnitRescalingLinear coarse vector := by
      rw [hsub]

lemma wz1PaperUnitRescalingLinear_coord2
    {rho : ℝ} (coarse : Kakeya.DeltaTube rho)
    (vector : Point3) :
    (wz1PaperUnitRescalingLinear coarse vector) 2 =
      inner ℝ vector (wz1PaperDirection coarse) :=
  unitRescalingLinear_coord2
    (wz1PaperDirection coarse)
    (wz1PaperDirection_norm coarse)
    (100 * rho) vector

lemma wz1PaperUnitRescalingMap_coord2
    {rho : ℝ} (coarse : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) (point : Point3) :
    (wz1PaperUnitRescalingMap coarse hrho point) 2 =
      inner ℝ
        (point - wz1TubeAxisZeroPoint coarse)
        (wz1PaperDirection coarse) :=
  unitRescalingMap_coord2
    (wz1TubeAxisZeroPoint coarse)
    (wz1PaperDirection coarse)
    (wz1PaperDirection_norm coarse)
    (100 * rho) (by positivity) point

lemma wz1PaperUnitRescalingLinear_perp_norm
    {rho : ℝ} (coarse : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) (vector : Point3)
    (hperp :
      inner ℝ vector (wz1PaperDirection coarse) = 0) :
    ‖wz1PaperUnitRescalingLinear coarse vector‖ =
      ‖vector‖ / (100 * rho) :=
  unitRescalingLinear_perp_norm
    (wz1PaperDirection coarse)
    (wz1PaperDirection_norm coarse)
    (100 * rho) (by positivity) vector hperp

lemma wz1PaperUnitRescalingLinear_injective
    {rho : ℝ} (coarse : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    Function.Injective (wz1PaperUnitRescalingLinear coarse) := by
  let rotation :=
    householderToE3
      (wz1PaperDirection coarse)
      (wz1PaperDirection_norm coarse)
  let scaling := transverseScaleLin (100 * rho)
  have hrotation : Function.Injective rotation :=
    rotation.injective
  have hscaling : Function.Injective scaling := by
    intro first second heq
    have h0 := congrArg (fun point : Point3 => point 0) heq
    have h1 := congrArg (fun point : Point3 => point 1) heq
    have h2 := congrArg (fun point : Point3 => point 2) heq
    have hscale : 0 < 100 * rho := by positivity
    rw [transverseScaleLin_coord0, transverseScaleLin_coord0] at h0
    rw [transverseScaleLin_coord1, transverseScaleLin_coord1] at h1
    rw [transverseScaleLin_coord2, transverseScaleLin_coord2] at h2
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate
    · field_simp [hscale.ne'] at h0
      exact h0
    · field_simp [hscale.ne'] at h1
      exact h1
    · exact h2
  exact hscaling.comp hrotation

lemma wz1PaperUnitRescalingMap_injective
    {rho : ℝ} (coarse : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    Function.Injective (wz1PaperUnitRescalingMap coarse hrho) := by
  intro first second heq
  have hsub :=
    wz1PaperUnitRescalingMap_sub coarse hrho first second
  rw [heq, sub_self] at hsub
  have hzero :
      wz1PaperUnitRescalingLinear coarse (first - second) =
        wz1PaperUnitRescalingLinear coarse 0 := by
    simpa using hsub.symm
  have hdiff :
      first - second = 0 :=
    wz1PaperUnitRescalingLinear_injective coarse hrho hzero
  exact sub_eq_zero.mp hdiff

lemma WZ1PaperTubeCovers.components
    {delta rho : ℝ}
    {fine : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    (hcover : WZ1PaperTubeCovers fine coarse) :
    dist
        (wz1TubeAxisZeroPoint fine)
        (wz1TubeAxisZeroPoint coarse) ≤ rho / 2 ∧
      InnerProductGeometry.angle
          (wz1PaperDirection fine)
          (wz1PaperDirection coarse) ≤ rho / 2 := by
  have hsum :
      dist
          (wz1TubeAxisZeroPoint fine)
          (wz1TubeAxisZeroPoint coarse) +
        InnerProductGeometry.angle
          (wz1PaperDirection fine)
          (wz1PaperDirection coarse) ≤ rho / 2 :=
    hcover
  have hdistance :
      0 ≤ dist
        (wz1TubeAxisZeroPoint fine)
        (wz1TubeAxisZeroPoint coarse) :=
    dist_nonneg
  have hangle :
      0 ≤ InnerProductGeometry.angle
        (wz1PaperDirection fine)
        (wz1PaperDirection coarse) :=
    InnerProductGeometry.angle_nonneg _ _
  exact ⟨by linarith, by linarith⟩

/--
The axis point of a vertical-chart tube at height zero is its canonical
`wz1TubeAxisZeroPoint`.
-/
lemma wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (hvertical :
      (1 / 2 : ℝ) ≤ |tube.direction (2 : Fin 3)|)
    {point : Point3}
    (hpoint : point ∈ tubeAxisLine tube)
    (hpoint_two : point (2 : Fin 3) = 0) :
    wz1TubeAxisZeroPoint tube = point := by
  rcases hpoint with ⟨parameter, rfl⟩
  have hdirection_ne :
      tube.direction (2 : Fin 3) ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hvertical
    norm_num at hvertical
  have hparameter :
      parameter =
        -(tube.base (2 : Fin 3) /
          tube.direction (2 : Fin 3)) := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hpoint_two
    apply (mul_right_cancel₀ hdirection_ne)
    field_simp [hdirection_ne] at hpoint_two ⊢
    linarith
  rw [hparameter]
  ext coordinate
  simp only [wz1TubeAxisZeroPoint, PiLp.sub_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/--
The image of a source-axis point in the coarse-orthogonal plane is the
canonical height-zero point of any target tube with the exact image axis.
-/
lemma wz1TubeAxisZeroPoint_eq_unitRescalingMap_of_mem_axis_of_inner_eq_zero
    {delta rho targetDelta : ℝ}
    {source : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    {target : Kakeya.DeltaTube targetDelta}
    (hrho : 0 < rho)
    (htarget : WZ1PaperTubeInLineClass target)
    (haxis :
      tubeAxisLine target =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine source)
    {sourcePoint : Point3}
    (hsourcePoint : sourcePoint ∈ tubeAxisLine source)
    (hsourcePoint_perp :
      inner ℝ
          (sourcePoint - wz1TubeAxisZeroPoint coarse)
          (wz1PaperDirection coarse) =
        0) :
    wz1TubeAxisZeroPoint target =
      wz1PaperUnitRescalingMap coarse hrho sourcePoint := by
  apply
    wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
      htarget.vertical
  · rw [haxis]
    exact ⟨sourcePoint, hsourcePoint, rfl⟩
  · rw [wz1PaperUnitRescalingMap_coord2]
    exact hsourcePoint_perp

/--
Exact positional expansion for two source-axis intersections with the
coarse-orthogonal plane.
-/
lemma wz1PaperUnitRescaledAxisZeroPoint_dist_eq
    {delta rho targetDelta : ℝ}
    {source₁ source₂ : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    {target₁ target₂ : Kakeya.DeltaTube targetDelta}
    (hrho : 0 < rho)
    (htarget₁ : WZ1PaperTubeInLineClass target₁)
    (htarget₂ : WZ1PaperTubeInLineClass target₂)
    (haxis₁ :
      tubeAxisLine target₁ =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine source₁)
    (haxis₂ :
      tubeAxisLine target₂ =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine source₂)
    {sourcePoint₁ sourcePoint₂ : Point3}
    (hsourcePoint₁ : sourcePoint₁ ∈ tubeAxisLine source₁)
    (hsourcePoint₂ : sourcePoint₂ ∈ tubeAxisLine source₂)
    (hsourcePoint₁_perp :
      inner ℝ
          (sourcePoint₁ - wz1TubeAxisZeroPoint coarse)
          (wz1PaperDirection coarse) =
        0)
    (hsourcePoint₂_perp :
      inner ℝ
          (sourcePoint₂ - wz1TubeAxisZeroPoint coarse)
          (wz1PaperDirection coarse) =
        0) :
    dist (wz1TubeAxisZeroPoint target₁)
        (wz1TubeAxisZeroPoint target₂) =
      dist sourcePoint₁ sourcePoint₂ / (100 * rho) := by
  rw [
    wz1TubeAxisZeroPoint_eq_unitRescalingMap_of_mem_axis_of_inner_eq_zero
      hrho htarget₁ haxis₁ hsourcePoint₁
        hsourcePoint₁_perp,
    wz1TubeAxisZeroPoint_eq_unitRescalingMap_of_mem_axis_of_inner_eq_zero
      hrho htarget₂ haxis₂ hsourcePoint₂
        hsourcePoint₂_perp,
    dist_eq_norm,
    wz1PaperUnitRescalingMap_sub]
  have hperp :
      inner ℝ (sourcePoint₁ - sourcePoint₂)
          (wz1PaperDirection coarse) =
        0 := by
    rw [
      show sourcePoint₁ - sourcePoint₂ =
          (sourcePoint₁ - wz1TubeAxisZeroPoint coarse) -
            (sourcePoint₂ - wz1TubeAxisZeroPoint coarse) by
        abel,
      inner_sub_left, hsourcePoint₁_perp,
      hsourcePoint₂_perp, sub_self]
  rw [
    wz1PaperUnitRescalingLinear_perp_norm
      coarse hrho _ hperp]
  rfl

/--
For unit vectors, chordal distance is bounded above by angular distance.
-/
lemma unit_norm_sub_le_angle
    {first second : Point3}
    (hfirst : ‖first‖ = 1)
    (hsecond : ‖second‖ = 1) :
    ‖first - second‖ ≤
      InnerProductGeometry.angle first second := by
  let angle :=
    InnerProductGeometry.angle first second
  have hangle_nonneg : 0 ≤ angle :=
    InnerProductGeometry.angle_nonneg first second
  have hinner :
      inner ℝ first second = Real.cos angle := by
    have h :=
      InnerProductGeometry.cos_angle_mul_norm_mul_norm
        first second
    rw [hfirst, hsecond] at h
    linarith
  have hfirst_inner :
      inner ℝ first first = ‖first‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  have hsecond_inner :
      inner ℝ second second = ‖second‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  have hcomm :
      inner ℝ second first = inner ℝ first second :=
    (real_inner_comm second first).symm
  have hnorm_sq :
      ‖first - second‖ ^ 2 =
        2 - 2 * Real.cos angle := by
    have h1 :
        ‖first - second‖ ^ 2 =
          inner ℝ (first - second) (first - second) := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    have h2 :
        inner ℝ (first - second) (first - second) =
          inner ℝ first first -
            inner ℝ first second -
            inner ℝ second first +
            inner ℝ second second := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right]
      ring
    rw [
      h1, h2, hfirst_inner, hsecond_inner, hcomm,
      hfirst, hsecond, hinner]
    norm_num
    ring
  have hcos :
      Real.cos angle =
        1 - 2 * Real.sin (angle / 2) ^ 2 := by
    have htwo :
        Real.cos (2 * (angle / 2)) =
          2 * Real.cos (angle / 2) ^ 2 - 1 :=
      Real.cos_two_mul (angle / 2)
    have harg :
        Real.cos (2 * (angle / 2)) =
          Real.cos angle := by
      ring_nf
    have htrig :
        Real.cos (angle / 2) ^ 2 +
            Real.sin (angle / 2) ^ 2 =
          1 :=
      Real.cos_sq_add_sin_sq (angle / 2)
    linarith
  have hsin_nonneg :
      0 ≤ Real.sin (angle / 2) :=
    Real.sin_nonneg_of_mem_Icc
      ⟨by linarith,
        by
          linarith [
            InnerProductGeometry.angle_le_pi first second]⟩
  have hnorm :
      ‖first - second‖ =
        2 * Real.sin (angle / 2) := by
    have hsquare :
        ‖first - second‖ ^ 2 =
          (2 * Real.sin (angle / 2)) ^ 2 := by
      rw [hnorm_sq, hcos]
      ring
    nlinarith [norm_nonneg (first - second)]
  have habs :
      |Real.sin (angle / 2)| ≤ |angle / 2| :=
    Real.abs_sin_le_abs (x := angle / 2)
  have hsin_le :
      Real.sin (angle / 2) ≤ angle / 2 := by
    rw [
      abs_of_nonneg hsin_nonneg,
      abs_of_nonneg (by linarith : 0 ≤ angle / 2)] at habs
    exact habs
  rw [hnorm]
  linarith

/--
For unit vectors, angular distance is at most `pi/2` times chordal distance.
-/
lemma angle_le_pi_div_two_mul_unit_norm_sub
    {first second : Point3}
    (hfirst : ‖first‖ = 1)
    (hsecond : ‖second‖ = 1) :
    InnerProductGeometry.angle first second ≤
      (Real.pi / 2) * ‖first - second‖ := by
  let angle :=
    InnerProductGeometry.angle first second
  have hangle_nonneg : 0 ≤ angle :=
    InnerProductGeometry.angle_nonneg first second
  have hangle_le_pi : angle ≤ Real.pi :=
    InnerProductGeometry.angle_le_pi first second
  have hinner :
      inner ℝ first second = Real.cos angle := by
    have h :=
      InnerProductGeometry.cos_angle_mul_norm_mul_norm
        first second
    rw [hfirst, hsecond] at h
    simpa [angle] using h.symm
  have hnorm_sq :
      ‖first - second‖ ^ 2 =
        (2 * Real.sin (angle / 2)) ^ 2 := by
    have hnorm :
        ‖first - second‖ ^ 2 =
          ‖first‖ ^ 2 -
            2 * inner ℝ first second +
            ‖second‖ ^ 2 :=
      norm_sub_sq_real first second
    have hcos :
        Real.cos angle =
          1 - 2 * Real.sin (angle / 2) ^ 2 := by
      have htwo := Real.cos_two_mul (angle / 2)
      have htrig :=
        Real.sin_sq_add_cos_sq (angle / 2)
      have harg : 2 * (angle / 2) = angle := by ring
      rw [harg] at htwo
      nlinarith
    rw [hnorm, hfirst, hsecond, hinner, hcos]
    ring
  have hsin_nonneg :
      0 ≤ Real.sin (angle / 2) :=
    Real.sin_nonneg_of_mem_Icc
      ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hnorm :
      ‖first - second‖ =
        2 * Real.sin (angle / 2) := by
    nlinarith [norm_nonneg (first - second)]
  have hhalf_le :
      angle / 2 ≤ Real.pi / 2 := by
    linarith
  have hsin_lower :
      angle / 2 ≤
        (Real.pi / 2) * Real.sin (angle / 2) :=
    le_pi2_mul_sin
      (angle / 2) (by linarith) hhalf_le
  rw [hnorm]
  nlinarith [Real.pi_pos]

/--
Normalization is `2`-Lipschitz between vectors whose norms are at least one.
-/
lemma norm_normalize_sub_normalize_le_two_mul_norm_sub
    {first second : Point3}
    (hfirst : 1 ≤ ‖first‖)
    (hsecond : 1 ≤ ‖second‖) :
    ‖NormedSpace.normalize first -
        NormedSpace.normalize second‖ ≤
      2 * ‖first - second‖ := by
  have hfirst_pos : 0 < ‖first‖ := lt_of_lt_of_le zero_lt_one hfirst
  have hsecond_pos : 0 < ‖second‖ := lt_of_lt_of_le zero_lt_one hsecond
  have hfirst_ne : ‖first‖ ≠ 0 := hfirst_pos.ne'
  have hsecond_ne : ‖second‖ ≠ 0 := hsecond_pos.ne'
  have hinv_first_nonneg : 0 ≤ ‖first‖⁻¹ := inv_nonneg.mpr hfirst_pos.le
  have hinv_first_le_one : ‖first‖⁻¹ ≤ 1 :=
    (inv_le_one₀ hfirst_pos).mpr hfirst
  have hnorm_diff :
      |‖second‖ - ‖first‖| ≤ ‖first - second‖ := by
    have hreverse :
        second - first = -(first - second) := by
      abel
    rw [← norm_neg (first - second), ← hreverse]
    exact abs_norm_sub_norm_le second first
  have hinv_diff :
      |‖first‖⁻¹ - ‖second‖⁻¹| * ‖second‖ =
        |‖second‖ - ‖first‖| / ‖first‖ := by
    have halgebra :
        ‖first‖⁻¹ - ‖second‖⁻¹ =
          (‖second‖ - ‖first‖) /
            (‖first‖ * ‖second‖) := by
      field_simp [hfirst_ne, hsecond_ne]
    rw [halgebra, abs_div, abs_mul, abs_norm, abs_norm]
    field_simp [hfirst_ne, hsecond_ne]
  have hdecompose :
      NormedSpace.normalize first -
          NormedSpace.normalize second =
        ‖first‖⁻¹ • (first - second) +
          (‖first‖⁻¹ - ‖second‖⁻¹) • second := by
    simp only [NormedSpace.normalize]
    module
  rw [hdecompose]
  calc
    ‖‖first‖⁻¹ • (first - second) +
        (‖first‖⁻¹ - ‖second‖⁻¹) • second‖
        ≤ ‖‖first‖⁻¹ • (first - second)‖ +
            ‖(‖first‖⁻¹ - ‖second‖⁻¹) • second‖ :=
      norm_add_le _ _
    _ = ‖first‖⁻¹ * ‖first - second‖ +
        |‖first‖⁻¹ - ‖second‖⁻¹| * ‖second‖ := by
      rw [norm_smul, norm_smul]
      simp only [Real.norm_eq_abs, abs_inv, abs_norm]
    _ = ‖first‖⁻¹ * ‖first - second‖ +
        |‖second‖ - ‖first‖| / ‖first‖ := by
      rw [hinv_diff]
    _ ≤ ‖first - second‖ + ‖first - second‖ := by
      gcongr
      · exact mul_le_of_le_one_left (norm_nonneg _) hinv_first_le_one
      · exact (div_le_iff₀ hfirst_pos).mpr
          (by
            calc
              |‖second‖ - ‖first‖|
                  ≤ ‖first - second‖ := hnorm_diff
              _ ≤ ‖first - second‖ * ‖first‖ := by
                nlinarith [norm_nonneg (first - second)])
    _ = 2 * ‖first - second‖ := by ring

/--
Normalization is nonexpanding between vectors whose norms are at least one.
-/
lemma norm_normalize_sub_normalize_le_norm_sub
    {first second : Point3}
    (hfirst : 1 ≤ ‖first‖)
    (hsecond : 1 ≤ ‖second‖) :
    ‖NormedSpace.normalize first -
        NormedSpace.normalize second‖ ≤
      ‖first - second‖ := by
  have hfirst_pos : 0 < ‖first‖ := zero_lt_one.trans_le hfirst
  have hsecond_pos : 0 < ‖second‖ := zero_lt_one.trans_le hsecond
  have hfirst_ne : first ≠ 0 := norm_pos_iff.mp hfirst_pos
  have hsecond_ne : second ≠ 0 := norm_pos_iff.mp hsecond_pos
  let normalizedFirst := NormedSpace.normalize first
  let normalizedSecond := NormedSpace.normalize second
  have hnormalized_first : ‖normalizedFirst‖ = 1 :=
    NormedSpace.norm_normalize hfirst_ne
  have hnormalized_second : ‖normalizedSecond‖ = 1 :=
    NormedSpace.norm_normalize hsecond_ne
  have hinner_normalized :
      inner ℝ normalizedFirst normalizedSecond =
        (‖first‖ * ‖second‖)⁻¹ *
          inner ℝ first second := by
    simp only [normalizedFirst, normalizedSecond,
      NormedSpace.normalize, inner_smul_left,
      inner_smul_right, RCLike.star_def, RCLike.conj_to_real]
    field_simp [hfirst_pos.ne', hsecond_pos.ne']
  have hnormalized_sq :
      ‖normalizedFirst - normalizedSecond‖ ^ 2 =
        2 -
          2 * (‖first‖ * ‖second‖)⁻¹ *
            inner ℝ first second := by
    rw [norm_sub_sq_real, hnormalized_first,
      hnormalized_second, hinner_normalized]
    ring
  have hsource_sq :
      ‖first - second‖ ^ 2 =
        ‖first‖ ^ 2 -
          2 * inner ℝ first second +
            ‖second‖ ^ 2 :=
    norm_sub_sq_real first second
  have hidentity :
      ‖first - second‖ ^ 2 =
        (‖first‖ - ‖second‖) ^ 2 +
          (‖first‖ * ‖second‖) *
            ‖normalizedFirst - normalizedSecond‖ ^ 2 := by
    rw [hsource_sq, hnormalized_sq]
    field_simp [hfirst_pos.ne', hsecond_pos.ne']
    ring
  have hproduct : 1 ≤ ‖first‖ * ‖second‖ := by
    nlinarith
  have hnormalized_nonneg :
      0 ≤ ‖normalizedFirst - normalizedSecond‖ ^ 2 := sq_nonneg _
  have hsq :
      ‖normalizedFirst - normalizedSecond‖ ^ 2 ≤
        ‖first - second‖ ^ 2 := by
    rw [hidentity]
    nlinarith [sq_nonneg (‖first‖ - ‖second‖)]
  dsimp only [normalizedFirst, normalizedSecond] at hsq ⊢
  nlinarith [
    norm_nonneg
      (NormedSpace.normalize first -
        NormedSpace.normalize second),
    norm_nonneg (first - second)]

/--
Transverse scaling is a contraction once its denominator is at least one.
-/
lemma transverseScaleLin_norm_le_of_one_le
    (scale : ℝ) (hscale : 1 ≤ scale) (vector : Point3) :
    ‖transverseScaleLin scale vector‖ ≤ ‖vector‖ := by
  have hscale_pos : 0 < scale := zero_lt_one.trans_le hscale
  have hinv_sq_le : 1 / scale ^ 2 ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hscale_pos)]
    nlinarith
  have hnorm_sq :=
    transverseScaleLin_norm_sq scale hscale_pos vector
  have hsq :
      ‖transverseScaleLin scale vector‖ ^ 2 ≤
        ‖vector‖ ^ 2 := by
    rw [hnorm_sq, point3_coord_norm_sq vector]
    nlinarith [sq_nonneg (vector 0), sq_nonneg (vector 1),
      sq_nonneg (vector 2)]
  nlinarith [norm_nonneg (transverseScaleLin scale vector),
    norm_nonneg vector]

/--
A direction covered by `coarse` has a paper-rescaled linear image within
distance `1/2` of the vertical unit vector.
-/
lemma wz1PaperUnitRescalingLinear_direction_close_e3
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hcover : WZ1PaperTubeCovers source coarse) :
    ‖wz1PaperUnitRescalingLinear coarse
          (wz1PaperDirection source) -
        e3‖ ≤ 1 / 2 := by
  let rotation :=
    householderToE3
      (wz1PaperDirection coarse)
      (wz1PaperDirection_norm coarse)
  let scale := 100 * rho
  have hrotation_coarse :
      rotation (wz1PaperDirection coarse) = e3 :=
    householderToE3_sends_d_to_e3
      (wz1PaperDirection coarse)
      (wz1PaperDirection_norm coarse)
  have hscale_e3 :
      transverseScaleLin scale e3 = e3 := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;>
      simp [transverseScaleLin_coord0, transverseScaleLin_coord1,
        transverseScaleLin_coord2, e3]
  have hsource_chord :
      ‖wz1PaperDirection source -
          wz1PaperDirection coarse‖ ≤ rho / 2 :=
    (unit_norm_sub_le_angle
      (wz1PaperDirection_norm source)
      (wz1PaperDirection_norm coarse)).trans
      hcover.components.2
  have hrotation_chord :
      ‖rotation
          (wz1PaperDirection source -
            wz1PaperDirection coarse)‖ ≤ rho / 2 := by
    rw [rotation.norm_map]
    exact hsource_chord
  have hrewrite :
      wz1PaperUnitRescalingLinear coarse
            (wz1PaperDirection source) -
          e3 =
        transverseScaleLin scale
          (rotation
            (wz1PaperDirection source -
              wz1PaperDirection coarse)) := by
    calc
      wz1PaperUnitRescalingLinear coarse
            (wz1PaperDirection source) - e3 =
          transverseScaleLin scale
                (rotation (wz1PaperDirection source)) -
            transverseScaleLin scale
                (rotation (wz1PaperDirection coarse)) := by
        rw [hrotation_coarse, hscale_e3]
        rfl
      _ = transverseScaleLin scale
          (rotation (wz1PaperDirection source) -
            rotation (wz1PaperDirection coarse)) := by
        exact
          (map_sub (transverseScaleLin scale)
            (rotation (wz1PaperDirection source))
            (rotation (wz1PaperDirection coarse))).symm
      _ = transverseScaleLin scale
          (rotation
            (wz1PaperDirection source -
              wz1PaperDirection coarse)) := by
        exact congrArg (transverseScaleLin scale)
          (map_sub rotation
            (wz1PaperDirection source)
            (wz1PaperDirection coarse)).symm
  rw [hrewrite]
  by_cases hsmall : scale ≤ 1
  · calc
      ‖transverseScaleLin scale
          (rotation
            (wz1PaperDirection source -
              wz1PaperDirection coarse))‖
          ≤ (1 / scale) *
              ‖rotation
                (wz1PaperDirection source -
                  wz1PaperDirection coarse)‖ :=
        transverseScaleLin_norm_bound scale (by positivity) hsmall _
      _ ≤ (1 / scale) * (rho / 2) := by
        gcongr
      _ = 1 / 200 := by
        dsimp only [scale]
        field_simp [hrho.ne']
        ring
      _ ≤ 1 / 2 := by norm_num
  · have hlarge : 1 ≤ scale := le_of_not_ge hsmall
    calc
      ‖transverseScaleLin scale
          (rotation
            (wz1PaperDirection source -
              wz1PaperDirection coarse))‖
          ≤ ‖rotation
              (wz1PaperDirection source -
                wz1PaperDirection coarse)‖ :=
        transverseScaleLin_norm_le_of_one_le scale hlarge _
      _ ≤ rho / 2 := hrotation_chord
      _ ≤ 1 / 2 := by linarith

/--
The norm of a covered source direction after paper rescaling stays between
`1/2` and `3/2`.
-/
lemma wz1PaperUnitRescalingLinear_direction_norm_bounds
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hcover : WZ1PaperTubeCovers source coarse) :
    1 / 2 ≤
        ‖wz1PaperUnitRescalingLinear coarse
          (wz1PaperDirection source)‖ ∧
      ‖wz1PaperUnitRescalingLinear coarse
          (wz1PaperDirection source)‖ ≤ 3 / 2 := by
  have hclose :=
    wz1PaperUnitRescalingLinear_direction_close_e3
      hrho hrho_one hcover
  constructor
  · have hreverse :
        ‖e3‖ -
            ‖wz1PaperUnitRescalingLinear coarse
              (wz1PaperDirection source)‖ ≤
          ‖e3 -
            wz1PaperUnitRescalingLinear coarse
              (wz1PaperDirection source)‖ :=
      norm_sub_norm_le e3
        (wz1PaperUnitRescalingLinear coarse
          (wz1PaperDirection source))
    rw [e3_norm, norm_sub_rev] at hreverse
    linarith
  · calc
      ‖wz1PaperUnitRescalingLinear coarse
          (wz1PaperDirection source)‖
          ≤ ‖wz1PaperUnitRescalingLinear coarse
                (wz1PaperDirection source) - e3‖ +
              ‖e3‖ := by
            have :=
              norm_add_le
                (wz1PaperUnitRescalingLinear coarse
                  (wz1PaperDirection source) - e3) e3
            simpa only [sub_add_cancel] using this
      _ ≤ 3 / 2 := by rw [e3_norm]; linarith

/-- Height-one representative of a positively vertical projective direction. -/
def wz1PaperProjectiveDirection (direction : Point3) : Point3 :=
  (direction (2 : Fin 3))⁻¹ • direction

lemma wz1PaperProjectiveDirection_coord_two
    {direction : Point3}
    (hvertical : direction (2 : Fin 3) ≠ 0) :
    wz1PaperProjectiveDirection direction (2 : Fin 3) = 1 := by
  simp [wz1PaperProjectiveDirection, hvertical]

lemma normalize_wz1PaperProjectiveDirection
    {direction : Point3}
    (hunit : ‖direction‖ = 1)
    (hvertical : 0 < direction (2 : Fin 3)) :
    NormedSpace.normalize
        (wz1PaperProjectiveDirection direction) =
      direction := by
  rw [wz1PaperProjectiveDirection,
    NormedSpace.normalize_smul_of_pos (inv_pos.mpr hvertical)]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one hunit

lemma wz1PaperProjectiveDirection_smul_of_pos
    (scale : ℝ) (hscale : 0 < scale)
    (direction : Point3) :
    wz1PaperProjectiveDirection (scale • direction) =
      wz1PaperProjectiveDirection direction := by
  apply PiLp.ext
  intro coordinate
  simp only [wz1PaperProjectiveDirection,
    PiLp.smul_apply, smul_eq_mul]
  field_simp [hscale.ne']

lemma wz1PaperProjectiveDirection_normalize
    {direction : Point3}
    (hdirection : direction ≠ 0) :
    wz1PaperProjectiveDirection
        (NormedSpace.normalize direction) =
      wz1PaperProjectiveDirection direction := by
  rw [NormedSpace.normalize]
  exact wz1PaperProjectiveDirection_smul_of_pos
    ‖direction‖⁻¹ (inv_pos.mpr (norm_pos_iff.mpr hdirection)) direction

lemma transversePart_norm_le
    (vector : Point3) :
    ‖transversePart vector‖ ≤ ‖vector‖ := by
  have hsq := transversePart_norm_sq vector
  nlinarith [norm_nonneg (transversePart vector),
    norm_nonneg vector, sq_nonneg (vector 2)]

lemma abs_coord_two_le_norm
    (vector : Point3) :
    |vector (2 : Fin 3)| ≤ ‖vector‖ := by
  have hsq := point3_coord_norm_sq vector
  have hcoord_sq :
      (vector (2 : Fin 3)) ^ 2 ≤ ‖vector‖ ^ 2 := by
    nlinarith [sq_nonneg (vector 0), sq_nonneg (vector 1)]
  nlinarith [abs_nonneg (vector 2), norm_nonneg vector,
    sq_abs (vector 2)]

/--
Changing from the horizontal zero section to another section of two vertical
lines costs at most three times the new positional separation plus a
directional error proportional to the section parameter.
-/
lemma zero_section_reintersection_dist_le
    {rho parameter₁ parameter₂ : ℝ}
    {zero₁ zero₂ direction₁ direction₂
      section₁ section₂ : Point3}
    (hrho : 0 ≤ rho)
    (hdirection₁_norm : ‖direction₁‖ = 1)
    (hdirection₁_vertical :
      1 / 2 ≤ direction₁ (2 : Fin 3))
    (hzero₁_two : zero₁ (2 : Fin 3) = 0)
    (hzero₂_two : zero₂ (2 : Fin 3) = 0)
    (hsection₁ :
      section₁ = zero₁ + parameter₁ • direction₁)
    (hsection₂ :
      section₂ = zero₂ + parameter₂ • direction₂)
    (hparameter₂ : |parameter₂| ≤ rho) :
    ‖zero₁ - zero₂‖ ≤
      3 * ‖section₁ - section₂‖ +
        3 * rho * ‖direction₁ - direction₂‖ := by
  have hdirection₁_vertical_pos :
      0 < direction₁ (2 : Fin 3) := by
    linarith
  have hcoordinate :
      (section₁ - section₂) (2 : Fin 3) =
        (parameter₁ - parameter₂) *
            direction₁ (2 : Fin 3) +
          parameter₂ *
            ((direction₁ - direction₂) (2 : Fin 3)) := by
    rw [hsection₁, hsection₂]
    simp only [PiLp.sub_apply, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, hzero₁_two,
      hzero₂_two]
    ring
  have hparameter_difference :
      |parameter₁ - parameter₂| ≤
        2 * ‖section₁ - section₂‖ +
          2 * rho * ‖direction₁ - direction₂‖ := by
    have hsection_coordinate :
        |(section₁ - section₂) (2 : Fin 3)| ≤
          ‖section₁ - section₂‖ :=
      abs_coord_two_le_norm (section₁ - section₂)
    have hdirection_coordinate :
        |(direction₁ - direction₂) (2 : Fin 3)| ≤
          ‖direction₁ - direction₂‖ :=
      abs_coord_two_le_norm (direction₁ - direction₂)
    have hproduct :
        |(parameter₁ - parameter₂) *
            direction₁ (2 : Fin 3)| ≤
          ‖section₁ - section₂‖ +
            rho * ‖direction₁ - direction₂‖ := by
      have hproduct_eq :
          (parameter₁ - parameter₂) *
              direction₁ (2 : Fin 3) =
            (section₁ - section₂) (2 : Fin 3) -
              parameter₂ *
                (direction₁ - direction₂) (2 : Fin 3) := by
        linarith [hcoordinate]
      rw [hproduct_eq]
      calc
        |(section₁ - section₂) (2 : Fin 3) -
            parameter₂ *
              (direction₁ - direction₂) (2 : Fin 3)|
            ≤ |(section₁ - section₂) (2 : Fin 3)| +
                |parameter₂ *
                  (direction₁ - direction₂) (2 : Fin 3)| :=
          abs_sub _ _
        _ = |(section₁ - section₂) (2 : Fin 3)| +
              |parameter₂| *
                |(direction₁ - direction₂) (2 : Fin 3)| := by
          rw [abs_mul]
        _ ≤ ‖section₁ - section₂‖ +
              rho * ‖direction₁ - direction₂‖ := by
          gcongr
    have hhalf :
        (1 / 2 : ℝ) * |parameter₁ - parameter₂| ≤
          |(parameter₁ - parameter₂) *
            direction₁ (2 : Fin 3)| := by
      rw [abs_mul,
        abs_of_pos hdirection₁_vertical_pos]
      nlinarith [abs_nonneg (parameter₁ - parameter₂)]
    nlinarith
  have hvector :
      zero₁ - zero₂ =
        (section₁ - section₂) -
          (parameter₁ - parameter₂) • direction₁ -
            parameter₂ • (direction₁ - direction₂) := by
    rw [hsection₁, hsection₂]
    module
  rw [hvector]
  calc
    ‖(section₁ - section₂) -
        (parameter₁ - parameter₂) • direction₁ -
          parameter₂ • (direction₁ - direction₂)‖
        ≤ ‖(section₁ - section₂) -
              (parameter₁ - parameter₂) • direction₁‖ +
            ‖parameter₂ • (direction₁ - direction₂)‖ :=
      norm_sub_le _ _
    _ ≤
        (‖section₁ - section₂‖ +
          ‖(parameter₁ - parameter₂) • direction₁‖) +
            ‖parameter₂ • (direction₁ - direction₂)‖ := by
      gcongr
      exact norm_sub_le _ _
    _ =
        ‖section₁ - section₂‖ +
          |parameter₁ - parameter₂| +
            |parameter₂| * ‖direction₁ - direction₂‖ := by
      rw [norm_smul, norm_smul, hdirection₁_norm]
      simp only [Real.norm_eq_abs]
      ring
    _ ≤
        ‖section₁ - section₂‖ +
          (2 * ‖section₁ - section₂‖ +
            2 * rho * ‖direction₁ - direction₂‖) +
          rho * ‖direction₁ - direction₂‖ := by
      gcongr
    _ =
        3 * ‖section₁ - section₂‖ +
          3 * rho * ‖direction₁ - direction₂‖ := by
      ring

lemma one_le_norm_wz1PaperProjectiveDirection
    {direction : Point3}
    (hvertical : direction (2 : Fin 3) ≠ 0) :
    1 ≤ ‖wz1PaperProjectiveDirection direction‖ := by
  have hcoord :=
    abs_coord_two_le_norm
      (wz1PaperProjectiveDirection direction)
  rw [wz1PaperProjectiveDirection_coord_two hvertical,
    abs_one] at hcoord
  exact hcoord

lemma transversePart_norm_le_seven_eighths
    {direction : Point3}
    (hunit : ‖direction‖ = 1)
    (hvertical : 1 / 2 ≤ direction (2 : Fin 3)) :
    ‖transversePart direction‖ ≤ 7 / 8 := by
  have hsq := transversePart_norm_sq direction
  rw [hunit] at hsq
  nlinarith [norm_nonneg (transversePart direction)]

/--
The height-one projective chart is `21/4`-Lipschitz on the positive vertical
unit cap `direction₂ ≥ 1/2`.
-/
lemma wz1PaperProjectiveDirection_sub_norm_le
    {first second : Point3}
    (hfirst_unit : ‖first‖ = 1)
    (hsecond_unit : ‖second‖ = 1)
    (hfirst_vertical : 1 / 2 ≤ first (2 : Fin 3))
    (hsecond_vertical : 1 / 2 ≤ second (2 : Fin 3)) :
    ‖wz1PaperProjectiveDirection first -
        wz1PaperProjectiveDirection second‖ ≤
      (21 / 4 : ℝ) * ‖first - second‖ := by
  have hfirst_pos : 0 < first (2 : Fin 3) := by linarith
  have hsecond_pos : 0 < second (2 : Fin 3) := by linarith
  have hfirst_ne : first (2 : Fin 3) ≠ 0 := hfirst_pos.ne'
  have hsecond_ne : second (2 : Fin 3) ≠ 0 := hsecond_pos.ne'
  have hinv_first_nonneg :
      0 ≤ (first (2 : Fin 3))⁻¹ :=
    inv_nonneg.mpr hfirst_pos.le
  have hinv_first_le_two :
      (first (2 : Fin 3))⁻¹ ≤ 2 := by
    rw [← one_div]
    exact (div_le_iff₀ hfirst_pos).mpr (by nlinarith)
  have hsecond_transverse :
      ‖transversePart second‖ ≤ 7 / 8 :=
    transversePart_norm_le_seven_eighths
      hsecond_unit hsecond_vertical
  let difference := first - second
  let transverseDifference := transversePart difference
  let verticalDifference := |difference (2 : Fin 3)|
  have htransverse_nonneg : 0 ≤ ‖transverseDifference‖ :=
    norm_nonneg _
  have hvertical_nonneg : 0 ≤ verticalDifference :=
    abs_nonneg _
  have hdifference_nonneg : 0 ≤ ‖difference‖ :=
    norm_nonneg _
  have hpythagorean :
      ‖transverseDifference‖ ^ 2 +
          verticalDifference ^ 2 =
        ‖difference‖ ^ 2 := by
    have hsq := transversePart_norm_sq difference
    rw [sq_abs] at *
    linarith
  have hsum :
      ‖transverseDifference‖ + verticalDifference ≤
        (3 / 2 : ℝ) * ‖difference‖ := by
    have hcross :
        2 * ‖transverseDifference‖ * verticalDifference ≤
          ‖transverseDifference‖ ^ 2 +
            verticalDifference ^ 2 := by
      nlinarith [sq_nonneg
        (‖transverseDifference‖ - verticalDifference)]
    have hsq :
        (‖transverseDifference‖ + verticalDifference) ^ 2 ≤
          ((3 / 2 : ℝ) * ‖difference‖) ^ 2 := by
      nlinarith
    nlinarith
  have hinv_diff :
      |(first (2 : Fin 3))⁻¹ -
          (second (2 : Fin 3))⁻¹| ≤
        4 * verticalDifference := by
    have halgebra :
        (first (2 : Fin 3))⁻¹ -
            (second (2 : Fin 3))⁻¹ =
          (second (2 : Fin 3) - first (2 : Fin 3)) /
            (first (2 : Fin 3) * second (2 : Fin 3)) := by
      field_simp [hfirst_ne, hsecond_ne]
    rw [halgebra, abs_div, abs_mul]
    have hdenominator :
        1 / 4 ≤
          first (2 : Fin 3) * second (2 : Fin 3) := by
      nlinarith
    have hdenominator_pos :
        0 <
          first (2 : Fin 3) * second (2 : Fin 3) := by
      positivity
    have hnum :
        |second (2 : Fin 3) - first (2 : Fin 3)| =
          verticalDifference := by
      dsimp only [verticalDifference, difference]
      simp only [PiLp.sub_apply, abs_sub_comm]
    rw [hnum, abs_of_pos hfirst_pos, abs_of_pos hsecond_pos]
    exact (div_le_iff₀ hdenominator_pos).mpr
      (by nlinarith)
  have hfirst_projective :
      wz1PaperProjectiveDirection first =
        (first (2 : Fin 3))⁻¹ • transversePart first + e3 := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;>
      simp [wz1PaperProjectiveDirection,
        transversePart_coord0, transversePart_coord1,
        transversePart_coord2, e3, hfirst_ne,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hsecond_projective :
      wz1PaperProjectiveDirection second =
        (second (2 : Fin 3))⁻¹ • transversePart second + e3 := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;>
      simp [wz1PaperProjectiveDirection,
        transversePart_coord0, transversePart_coord1,
        transversePart_coord2, e3, hsecond_ne,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hdecompose :
      wz1PaperProjectiveDirection first -
          wz1PaperProjectiveDirection second =
        (first (2 : Fin 3))⁻¹ • transverseDifference +
          ((first (2 : Fin 3))⁻¹ -
            (second (2 : Fin 3))⁻¹) •
              transversePart second := by
    rw [hfirst_projective, hsecond_projective]
    have hdifference_transverse :
        transverseDifference =
          transversePart first - transversePart second := by
      apply PiLp.ext
      intro coordinate
      fin_cases coordinate <;>
        simp [transverseDifference, difference,
          transversePart_coord0, transversePart_coord1,
          transversePart_coord2]
    rw [hdifference_transverse]
    module
  rw [hdecompose]
  calc
    ‖(first (2 : Fin 3))⁻¹ • transverseDifference +
        ((first (2 : Fin 3))⁻¹ -
          (second (2 : Fin 3))⁻¹) •
            transversePart second‖
        ≤ ‖(first (2 : Fin 3))⁻¹ • transverseDifference‖ +
            ‖((first (2 : Fin 3))⁻¹ -
              (second (2 : Fin 3))⁻¹) •
                transversePart second‖ :=
      norm_add_le _ _
    _ = (first (2 : Fin 3))⁻¹ *
          ‖transverseDifference‖ +
        |(first (2 : Fin 3))⁻¹ -
          (second (2 : Fin 3))⁻¹| *
            ‖transversePart second‖ := by
      rw [norm_smul, norm_smul]
      simp [Real.norm_eq_abs, abs_of_pos hfirst_pos]
    _ ≤ 2 * ‖transverseDifference‖ +
        (4 * verticalDifference) * (7 / 8 : ℝ) := by
      gcongr
    _ ≤ (7 / 2 : ℝ) *
        (‖transverseDifference‖ + verticalDifference) := by
      nlinarith
    _ ≤ (7 / 2 : ℝ) * ((3 / 2 : ℝ) * ‖difference‖) := by
      gcongr
    _ = (21 / 4 : ℝ) * ‖first - second‖ := by
      dsimp only [difference]
      ring

/--
A source direction covered by `coarse` has positive inner product at least
`7/8` with the coarse paper direction.
-/
lemma wz1PaperTubeCovers.inner_direction_ge_seven_eighths
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    (hrho_one : rho ≤ 1)
    (hcover : WZ1PaperTubeCovers source coarse) :
    7 / 8 ≤
      inner ℝ
        (wz1PaperDirection source)
        (wz1PaperDirection coarse) := by
  let angle :=
    InnerProductGeometry.angle
      (wz1PaperDirection source)
      (wz1PaperDirection coarse)
  have hangle_nonneg : 0 ≤ angle :=
    InnerProductGeometry.angle_nonneg _ _
  have hangle : angle ≤ 1 / 2 := by
    exact hcover.components.2.trans (by linarith)
  have hcos :
      1 - angle ^ 2 / 2 ≤ Real.cos angle :=
    Real.one_sub_sq_div_two_le_cos
  have hinner :
      inner ℝ
          (wz1PaperDirection source)
          (wz1PaperDirection coarse) =
        Real.cos angle := by
    rw [
      InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one
        (wz1PaperDirection_norm source)
        (wz1PaperDirection_norm coarse)]
  rw [hinner]
  nlinarith

/--
The height-one projective representative before transverse scaling is the
vertical unit vector plus the scaled transverse part of the representative
after scaling.
-/
lemma wz1PaperProjectiveDirection_transverseScaleLin
    {scale : ℝ} (hscale : 0 < scale)
    {direction : Point3}
    (hvertical : 0 < direction (2 : Fin 3)) :
    wz1PaperProjectiveDirection direction =
      e3 + scale •
        transversePart
          (wz1PaperProjectiveDirection
            (transverseScaleLin scale direction)) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [wz1PaperProjectiveDirection,
      transversePart_coord0, transversePart_coord1,
      transversePart_coord2, transverseScaleLin_coord0,
      transverseScaleLin_coord1, transverseScaleLin_coord2,
      e3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
    field_simp [hscale.ne', hvertical.ne'] <;>
    ring

/--
Projective directions before and after the paper transverse scaling differ by
the exact factor `100 * rho`.
-/
lemma wz1PaperUnitRescaling_projective_direction_sub_norm_eq
    {delta rho : ℝ}
    {source₁ source₂ : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hcover₁ : WZ1PaperTubeCovers source₁ coarse)
    (hcover₂ : WZ1PaperTubeCovers source₂ coarse) :
    ‖wz1PaperProjectiveDirection
          (householderToE3
            (wz1PaperDirection coarse)
            (wz1PaperDirection_norm coarse)
            (wz1PaperDirection source₁)) -
        wz1PaperProjectiveDirection
          (householderToE3
            (wz1PaperDirection coarse)
            (wz1PaperDirection_norm coarse)
            (wz1PaperDirection source₂))‖ =
      (100 * rho) *
        ‖wz1PaperProjectiveDirection
              (wz1PaperUnitRescalingLinear coarse
                (wz1PaperDirection source₁)) -
            wz1PaperProjectiveDirection
              (wz1PaperUnitRescalingLinear coarse
                (wz1PaperDirection source₂))‖ := by
  let rotation :=
    householderToE3
      (wz1PaperDirection coarse)
      (wz1PaperDirection_norm coarse)
  let sourceDirection₁ := wz1PaperDirection source₁
  let sourceDirection₂ := wz1PaperDirection source₂
  let imageDirection₁ :=
    wz1PaperUnitRescalingLinear coarse sourceDirection₁
  let imageDirection₂ :=
    wz1PaperUnitRescalingLinear coarse sourceDirection₂
  have hrotation_coord_two :
      ∀ sourceDirection : Point3,
        (rotation sourceDirection) (2 : Fin 3) =
          inner ℝ sourceDirection
            (wz1PaperDirection coarse) := by
    intro sourceDirection
    calc
      (rotation sourceDirection) (2 : Fin 3) =
          inner ℝ (rotation sourceDirection) e3 :=
        coord2_eq_inner_e3 _
      _ = inner ℝ sourceDirection (rotation e3) := by
        exact householderToE3_symmetric
          (wz1PaperDirection coarse)
          (wz1PaperDirection_norm coarse)
          sourceDirection e3
      _ = inner ℝ sourceDirection
          (wz1PaperDirection coarse) := by
        rw [householderToE3_sends_e3_to_d]
  have hsource_inner₁ :
      0 <
        inner ℝ sourceDirection₁
          (wz1PaperDirection coarse) := by
    have h :=
      wz1PaperTubeCovers.inner_direction_ge_seven_eighths
        hrho_one hcover₁
    dsimp only [sourceDirection₁]
    linarith
  have hsource_inner₂ :
      0 <
        inner ℝ sourceDirection₂
          (wz1PaperDirection coarse) := by
    have h :=
      wz1PaperTubeCovers.inner_direction_ge_seven_eighths
        hrho_one hcover₂
    dsimp only [sourceDirection₂]
    linarith
  have hrotation_vertical₁ :
      0 < (rotation sourceDirection₁) (2 : Fin 3) := by
    rw [hrotation_coord_two]
    exact hsource_inner₁
  have hrotation_vertical₂ :
      0 < (rotation sourceDirection₂) (2 : Fin 3) := by
    rw [hrotation_coord_two]
    exact hsource_inner₂
  have hprojective₁ :
      wz1PaperProjectiveDirection
          (rotation sourceDirection₁) =
        e3 + (100 * rho) •
          transversePart
            (wz1PaperProjectiveDirection imageDirection₁) := by
    have h :=
      wz1PaperProjectiveDirection_transverseScaleLin
        (scale := 100 * rho) (by positivity)
        hrotation_vertical₁
    simpa [imageDirection₁, sourceDirection₁, rotation,
      wz1PaperUnitRescalingLinear, unitRescalingLinear] using h
  have hprojective₂ :
      wz1PaperProjectiveDirection
          (rotation sourceDirection₂) =
        e3 + (100 * rho) •
          transversePart
            (wz1PaperProjectiveDirection imageDirection₂) := by
    have h :=
      wz1PaperProjectiveDirection_transverseScaleLin
        (scale := 100 * rho) (by positivity)
        hrotation_vertical₂
    simpa [imageDirection₂, sourceDirection₂, rotation,
      wz1PaperUnitRescalingLinear, unitRescalingLinear] using h
  rw [hprojective₁, hprojective₂]
  have hcoord₂₁ :
      wz1PaperProjectiveDirection imageDirection₁ (2 : Fin 3) = 1 := by
    apply wz1PaperProjectiveDirection_coord_two
    rw [wz1PaperUnitRescalingLinear_coord2]
    exact hsource_inner₁.ne'
  have hcoord₂₂ :
      wz1PaperProjectiveDirection imageDirection₂ (2 : Fin 3) = 1 := by
    apply wz1PaperProjectiveDirection_coord_two
    rw [wz1PaperUnitRescalingLinear_coord2]
    exact hsource_inner₂.ne'
  have hdiff :
      (e3 + (100 * rho) •
            transversePart
              (wz1PaperProjectiveDirection imageDirection₁)) -
          (e3 + (100 * rho) •
            transversePart
              (wz1PaperProjectiveDirection imageDirection₂)) =
        (100 * rho) •
          (wz1PaperProjectiveDirection imageDirection₁ -
            wz1PaperProjectiveDirection imageDirection₂) := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;>
      simp [transversePart_coord0, transversePart_coord1,
        transversePart_coord2, hcoord₂₁, hcoord₂₂,
        PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul] <;>
      ring
  rw [hdiff, norm_smul]
  rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 100 * rho)]

/--
Angular separation of two source directions in one coarse fiber is bounded
by `1050 * rho` times the angular separation of their unnormalized rescaling
images.
-/
lemma wz1PaperUnitRescaling_source_angle_le
    {delta rho : ℝ}
    {source₁ source₂ : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hcover₁ : WZ1PaperTubeCovers source₁ coarse)
    (hcover₂ : WZ1PaperTubeCovers source₂ coarse) :
    InnerProductGeometry.angle
        (wz1PaperDirection source₁)
        (wz1PaperDirection source₂) ≤
      1050 * rho *
        InnerProductGeometry.angle
          (wz1PaperUnitRescalingLinear coarse
            (wz1PaperDirection source₁))
          (wz1PaperUnitRescalingLinear coarse
            (wz1PaperDirection source₂)) := by
  let rotation :=
    householderToE3
      (wz1PaperDirection coarse)
      (wz1PaperDirection_norm coarse)
  let sourceDirection₁ := wz1PaperDirection source₁
  let sourceDirection₂ := wz1PaperDirection source₂
  let imageDirection₁ :=
    wz1PaperUnitRescalingLinear coarse sourceDirection₁
  let imageDirection₂ :=
    wz1PaperUnitRescalingLinear coarse sourceDirection₂
  have hrotation_unit₁ : ‖rotation sourceDirection₁‖ = 1 := by
    rw [rotation.norm_map]
    exact wz1PaperDirection_norm source₁
  have hrotation_unit₂ : ‖rotation sourceDirection₂‖ = 1 := by
    rw [rotation.norm_map]
    exact wz1PaperDirection_norm source₂
  have hrotation_vertical₁ :
      1 / 2 ≤ (rotation sourceDirection₁) (2 : Fin 3) := by
    calc
      (1 / 2 : ℝ) ≤
          inner ℝ sourceDirection₁
            (wz1PaperDirection coarse) := by
        have h :=
          wz1PaperTubeCovers.inner_direction_ge_seven_eighths
            hrho_one hcover₁
        linarith
      _ = (rotation sourceDirection₁) (2 : Fin 3) := by
        calc
          inner ℝ sourceDirection₁
              (wz1PaperDirection coarse) =
              inner ℝ sourceDirection₁ (rotation e3) := by
            rw [householderToE3_sends_e3_to_d]
          _ = inner ℝ (rotation sourceDirection₁) e3 := by
            symm
            exact householderToE3_symmetric
              (wz1PaperDirection coarse)
              (wz1PaperDirection_norm coarse)
              sourceDirection₁ e3
          _ = (rotation sourceDirection₁) (2 : Fin 3) := by
            rw [coord2_eq_inner_e3]
  have hrotation_vertical₂ :
      1 / 2 ≤ (rotation sourceDirection₂) (2 : Fin 3) := by
    calc
      (1 / 2 : ℝ) ≤
          inner ℝ sourceDirection₂
            (wz1PaperDirection coarse) := by
        have h :=
          wz1PaperTubeCovers.inner_direction_ge_seven_eighths
            hrho_one hcover₂
        linarith
      _ = (rotation sourceDirection₂) (2 : Fin 3) := by
        calc
          inner ℝ sourceDirection₂
              (wz1PaperDirection coarse) =
              inner ℝ sourceDirection₂ (rotation e3) := by
            rw [householderToE3_sends_e3_to_d]
          _ = inner ℝ (rotation sourceDirection₂) e3 := by
            symm
            exact householderToE3_symmetric
              (wz1PaperDirection coarse)
              (wz1PaperDirection_norm coarse)
              sourceDirection₂ e3
          _ = (rotation sourceDirection₂) (2 : Fin 3) := by
            rw [coord2_eq_inner_e3]
  have himage_ne₁ : imageDirection₁ ≠ 0 := by
    intro hzero
    have hnorm :=
      wz1PaperUnitRescalingLinear_direction_norm_bounds
        hrho hrho_one hcover₁
    change 1 / 2 ≤ ‖imageDirection₁‖ ∧
      ‖imageDirection₁‖ ≤ 3 / 2 at hnorm
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have himage_ne₂ : imageDirection₂ ≠ 0 := by
    intro hzero
    have hnorm :=
      wz1PaperUnitRescalingLinear_direction_norm_bounds
        hrho hrho_one hcover₂
    change 1 / 2 ≤ ‖imageDirection₂‖ ∧
      ‖imageDirection₂‖ ≤ 3 / 2 at hnorm
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have hprojective :=
    wz1PaperUnitRescaling_projective_direction_sub_norm_eq
      hrho hrho_one hcover₁ hcover₂
  have himage_projective :
      ‖wz1PaperProjectiveDirection imageDirection₁ -
          wz1PaperProjectiveDirection imageDirection₂‖ ≤
        (21 / 4 : ℝ) *
          ‖NormedSpace.normalize imageDirection₁ -
            NormedSpace.normalize imageDirection₂‖ := by
    have hnormalized₁ :
        1 / 2 ≤
          (NormedSpace.normalize imageDirection₁) (2 : Fin 3) := by
      have hnorm :=
        wz1PaperUnitRescalingLinear_direction_norm_bounds
          hrho hrho_one hcover₁
      change 1 / 2 ≤ ‖imageDirection₁‖ ∧
        ‖imageDirection₁‖ ≤ 3 / 2 at hnorm
      have hinner :=
        wz1PaperTubeCovers.inner_direction_ge_seven_eighths
          hrho_one hcover₁
      have hnorm_pos : 0 < ‖imageDirection₁‖ :=
        norm_pos_iff.mpr himage_ne₁
      simp only [NormedSpace.normalize, PiLp.smul_apply,
        smul_eq_mul]
      rw [wz1PaperUnitRescalingLinear_coord2, inv_mul_eq_div]
      exact (le_div_iff₀ hnorm_pos).mpr (by nlinarith [hnorm.2])
    have hnormalized₂ :
        1 / 2 ≤
          (NormedSpace.normalize imageDirection₂) (2 : Fin 3) := by
      have hnorm :=
        wz1PaperUnitRescalingLinear_direction_norm_bounds
          hrho hrho_one hcover₂
      change 1 / 2 ≤ ‖imageDirection₂‖ ∧
        ‖imageDirection₂‖ ≤ 3 / 2 at hnorm
      have hinner :=
        wz1PaperTubeCovers.inner_direction_ge_seven_eighths
          hrho_one hcover₂
      have hnorm_pos : 0 < ‖imageDirection₂‖ :=
        norm_pos_iff.mpr himage_ne₂
      simp only [NormedSpace.normalize, PiLp.smul_apply,
        smul_eq_mul]
      rw [wz1PaperUnitRescalingLinear_coord2, inv_mul_eq_div]
      exact (le_div_iff₀ hnorm_pos).mpr (by nlinarith [hnorm.2])
    have h :=
      wz1PaperProjectiveDirection_sub_norm_le
        (NormedSpace.norm_normalize himage_ne₁)
        (NormedSpace.norm_normalize himage_ne₂)
        hnormalized₁ hnormalized₂
    simpa only [
      wz1PaperProjectiveDirection_normalize himage_ne₁,
      wz1PaperProjectiveDirection_normalize himage_ne₂] using h
  have hrotation_chord :
      ‖rotation sourceDirection₁ -
          rotation sourceDirection₂‖ =
        ‖sourceDirection₁ - sourceDirection₂‖ := by
    rw [← map_sub]
    exact rotation.norm_map _
  have hsource_chord :
      ‖sourceDirection₁ - sourceDirection₂‖ ≤
        525 * rho *
          ‖NormedSpace.normalize imageDirection₁ -
            NormedSpace.normalize imageDirection₂‖ := by
    rw [← hrotation_chord]
    have hsource_from_projective :
        ‖rotation sourceDirection₁ -
            rotation sourceDirection₂‖ ≤
          ‖wz1PaperProjectiveDirection
                (rotation sourceDirection₁) -
            wz1PaperProjectiveDirection
                (rotation sourceDirection₂)‖ := by
      have hnormalize₁ :=
        normalize_wz1PaperProjectiveDirection
          hrotation_unit₁ (by linarith :
            0 < (rotation sourceDirection₁) (2 : Fin 3))
      have hnormalize₂ :=
        normalize_wz1PaperProjectiveDirection
          hrotation_unit₂ (by linarith :
            0 < (rotation sourceDirection₂) (2 : Fin 3))
      have h :=
        norm_normalize_sub_normalize_le_norm_sub
          (first :=
            wz1PaperProjectiveDirection
              (rotation sourceDirection₁))
          (second :=
            wz1PaperProjectiveDirection
              (rotation sourceDirection₂))
          (one_le_norm_wz1PaperProjectiveDirection
            (by linarith :
              (rotation sourceDirection₁) (2 : Fin 3) ≠ 0))
          (one_le_norm_wz1PaperProjectiveDirection
            (by linarith :
              (rotation sourceDirection₂) (2 : Fin 3) ≠ 0))
      rw [hnormalize₁, hnormalize₂] at h
      exact h
    calc
      ‖rotation sourceDirection₁ -
          rotation sourceDirection₂‖
          ≤ ‖wz1PaperProjectiveDirection
                (rotation sourceDirection₁) -
              wz1PaperProjectiveDirection
                (rotation sourceDirection₂)‖ :=
        hsource_from_projective
      _ = 100 * rho *
          ‖wz1PaperProjectiveDirection imageDirection₁ -
            wz1PaperProjectiveDirection imageDirection₂‖ := by
        rw [hprojective]
      _ ≤ 100 * rho * ((21 / 4 : ℝ) *
          ‖NormedSpace.normalize imageDirection₁ -
            NormedSpace.normalize imageDirection₂‖) := by
        gcongr
      _ = 525 * rho *
          ‖NormedSpace.normalize imageDirection₁ -
            NormedSpace.normalize imageDirection₂‖ := by ring
  have hsource_angle :=
    angle_le_pi_div_two_mul_unit_norm_sub
      (wz1PaperDirection_norm source₁)
      (wz1PaperDirection_norm source₂)
  have himage_chord_angle :=
    unit_norm_sub_le_angle
      (NormedSpace.norm_normalize himage_ne₁)
      (NormedSpace.norm_normalize himage_ne₂)
  have hpi : Real.pi / 2 < 2 := by
    linarith [Real.pi_lt_four]
  have himage_angle :
      InnerProductGeometry.angle imageDirection₁ imageDirection₂ =
        InnerProductGeometry.angle
          (NormedSpace.normalize imageDirection₁)
          (NormedSpace.normalize imageDirection₂) := by
    simp
  change
    InnerProductGeometry.angle sourceDirection₁ sourceDirection₂ ≤
      1050 * rho *
        InnerProductGeometry.angle imageDirection₁ imageDirection₂
  rw [himage_angle]
  calc
    InnerProductGeometry.angle sourceDirection₁ sourceDirection₂
        ≤ (Real.pi / 2) *
          ‖sourceDirection₁ - sourceDirection₂‖ := hsource_angle
    _ ≤ 2 * (525 * rho *
          ‖NormedSpace.normalize imageDirection₁ -
            NormedSpace.normalize imageDirection₂‖) := by
      have hfactor_nonneg :
          0 ≤ 525 * rho *
            ‖NormedSpace.normalize imageDirection₁ -
              NormedSpace.normalize imageDirection₂‖ := by
        positivity
      calc
        (Real.pi / 2) *
            ‖sourceDirection₁ - sourceDirection₂‖
            ≤ (Real.pi / 2) * (525 * rho *
                ‖NormedSpace.normalize imageDirection₁ -
                  NormedSpace.normalize imageDirection₂‖) := by
              gcongr
        _ ≤ 2 * (525 * rho *
          ‖NormedSpace.normalize imageDirection₁ -
            NormedSpace.normalize imageDirection₂‖) := by
              gcongr
    _ = 1050 * rho *
        ‖NormedSpace.normalize imageDirection₁ -
          NormedSpace.normalize imageDirection₂‖ := by ring
    _ ≤ 1050 * rho *
        InnerProductGeometry.angle
          (NormedSpace.normalize imageDirection₁)
          (NormedSpace.normalize imageDirection₂) := by
      gcongr

/-- The canonical height-zero point lies on the supporting axis. -/
lemma wz1TubeAxisZeroPoint_mem_axis
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    wz1TubeAxisZeroPoint tube ∈ tubeAxisLine tube := by
  refine
    ⟨-(tube.base (2 : Fin 3) /
        tube.direction (2 : Fin 3)), ?_⟩
  ext coordinate
  simp only [wz1TubeAxisZeroPoint, PiLp.sub_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/--
Parameter at which the source paper axis meets the plane through the coarse
zero point orthogonal to the coarse paper direction.
-/
def wz1PaperOrthogonalSectionParameter
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (coarse : Kakeya.DeltaTube rho) : ℝ :=
  -inner ℝ
      (wz1TubeAxisZeroPoint source -
        wz1TubeAxisZeroPoint coarse)
      (wz1PaperDirection coarse) /
    inner ℝ
      (wz1PaperDirection source)
      (wz1PaperDirection coarse)

/-- The corresponding point on the source paper axis. -/
def wz1PaperOrthogonalSectionPoint
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (coarse : Kakeya.DeltaTube rho) : Point3 :=
  wz1TubeAxisZeroPoint source +
    wz1PaperOrthogonalSectionParameter source coarse •
      wz1PaperDirection source

lemma wz1PaperOrthogonalSectionPoint_mem_axis
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (coarse : Kakeya.DeltaTube rho) :
    wz1PaperOrthogonalSectionPoint source coarse ∈
      tubeAxisLine source := by
  rcases wz1TubeAxisZeroPoint_mem_axis source with
    ⟨parameter, hparameter⟩
  unfold wz1PaperOrthogonalSectionPoint wz1PaperDirection
  split_ifs with hsign
  · refine
      ⟨parameter +
          wz1PaperOrthogonalSectionParameter source coarse, ?_⟩
    rw [hparameter]
    module
  · refine
      ⟨parameter -
          wz1PaperOrthogonalSectionParameter source coarse, ?_⟩
    rw [hparameter]
    module

lemma wz1PaperOrthogonalSectionPoint_perp
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    (hinner :
      inner ℝ
          (wz1PaperDirection source)
          (wz1PaperDirection coarse) ≠
        0) :
    inner ℝ
        (wz1PaperOrthogonalSectionPoint source coarse -
          wz1TubeAxisZeroPoint coarse)
        (wz1PaperDirection coarse) =
      0 := by
  simp only [wz1PaperOrthogonalSectionPoint,
    wz1PaperOrthogonalSectionParameter]
  rw [show
      wz1TubeAxisZeroPoint source +
            (-inner ℝ
                (wz1TubeAxisZeroPoint source -
                  wz1TubeAxisZeroPoint coarse)
                (wz1PaperDirection coarse) /
              inner ℝ
                (wz1PaperDirection source)
                (wz1PaperDirection coarse)) •
              wz1PaperDirection source -
          wz1TubeAxisZeroPoint coarse =
        (wz1TubeAxisZeroPoint source -
          wz1TubeAxisZeroPoint coarse) +
          (-inner ℝ
              (wz1TubeAxisZeroPoint source -
                wz1TubeAxisZeroPoint coarse)
              (wz1PaperDirection coarse) /
            inner ℝ
              (wz1PaperDirection source)
              (wz1PaperDirection coarse)) •
            wz1PaperDirection source by
    module]
  rw [inner_add_left, inner_smul_left]
  simp only [RCLike.star_def, RCLike.conj_to_real]
  field_simp [hinner]
  ring

lemma abs_wz1PaperOrthogonalSectionParameter_le
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hcover : WZ1PaperTubeCovers source coarse) :
    |wz1PaperOrthogonalSectionParameter source coarse| ≤
      rho := by
  have hinner :=
    wz1PaperTubeCovers.inner_direction_ge_seven_eighths
      hrho_one hcover
  have hinner_pos :
      0 <
        inner ℝ
          (wz1PaperDirection source)
          (wz1PaperDirection coarse) := by
    linarith
  have hzero :
      dist
          (wz1TubeAxisZeroPoint source)
          (wz1TubeAxisZeroPoint coarse) ≤
        rho / 2 :=
    hcover.components.1
  have hnumerator :
      |inner ℝ
          (wz1TubeAxisZeroPoint source -
            wz1TubeAxisZeroPoint coarse)
          (wz1PaperDirection coarse)| ≤
        rho / 2 := by
    calc
      |inner ℝ
          (wz1TubeAxisZeroPoint source -
            wz1TubeAxisZeroPoint coarse)
          (wz1PaperDirection coarse)|
          ≤ ‖wz1TubeAxisZeroPoint source -
                wz1TubeAxisZeroPoint coarse‖ *
              ‖wz1PaperDirection coarse‖ :=
        abs_real_inner_le_norm _ _
      _ = dist
            (wz1TubeAxisZeroPoint source)
            (wz1TubeAxisZeroPoint coarse) := by
        rw [wz1PaperDirection_norm, mul_one, dist_eq_norm]
      _ ≤ rho / 2 := hzero
  unfold wz1PaperOrthogonalSectionParameter
  rw [abs_div, abs_neg, abs_of_pos hinner_pos]
  exact (div_le_iff₀ hinner_pos).mpr
    (by nlinarith)

/-- Advancing one paper-oriented unit along an axis stays on that axis. -/
lemma wz1TubeAxisZeroPoint_add_paperDirection_mem_axis
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    wz1TubeAxisZeroPoint tube + wz1PaperDirection tube ∈
      tubeAxisLine tube := by
  unfold wz1PaperDirection
  split_ifs with hsign
  · refine
      ⟨1 -
          tube.base (2 : Fin 3) /
            tube.direction (2 : Fin 3), ?_⟩
    ext coordinate
    simp only [wz1TubeAxisZeroPoint, PiLp.sub_apply,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  · refine
      ⟨-1 -
          tube.base (2 : Fin 3) /
            tube.direction (2 : Fin 3), ?_⟩
    ext coordinate
    simp only [wz1TubeAxisZeroPoint, PiLp.sub_apply,
      PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply,
      smul_eq_mul]
    ring

/--
Under exact image-axis provenance, the image of the source paper direction is
a positive multiple of the target paper direction.
-/
lemma wz1PaperUnitRescalingLinear_paperDirection_eq_pos_smul
    {delta rho targetDelta : ℝ}
    {source : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    {target : Kakeya.DeltaTube targetDelta}
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hcover : WZ1PaperTubeCovers source coarse)
    (htarget : WZ1PaperTubeInLineClass target)
    (haxis :
      tubeAxisLine target =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine source) :
    ∃ scale : ℝ, 0 < scale ∧
      wz1PaperUnitRescalingLinear coarse
          (wz1PaperDirection source) =
        scale • wz1PaperDirection target := by
  let sourceZero := wz1TubeAxisZeroPoint source
  let sourceDirection := wz1PaperDirection source
  have hsourceZero : sourceZero ∈ tubeAxisLine source :=
    wz1TubeAxisZeroPoint_mem_axis source
  have hsourceOne :
      sourceZero + sourceDirection ∈ tubeAxisLine source :=
    wz1TubeAxisZeroPoint_add_paperDirection_mem_axis source
  have htargetZero :
      wz1PaperUnitRescalingMap coarse hrho sourceZero ∈
        tubeAxisLine target := by
    rw [haxis]
    exact ⟨sourceZero, hsourceZero, rfl⟩
  have htargetOne :
      wz1PaperUnitRescalingMap coarse hrho
          (sourceZero + sourceDirection) ∈
        tubeAxisLine target := by
    rw [haxis]
    exact
      ⟨sourceZero + sourceDirection, hsourceOne, rfl⟩
  rcases htargetZero with
    ⟨parameterZero, hparameterZero⟩
  rcases htargetOne with
    ⟨parameterOne, hparameterOne⟩
  let rawScale := parameterOne - parameterZero
  have hraw :
      wz1PaperUnitRescalingLinear coarse sourceDirection =
        rawScale • target.direction := by
    have hadd :=
      wz1PaperUnitRescalingMap_add
        coarse hrho sourceZero sourceDirection
    have hdifference :
        wz1PaperUnitRescalingLinear coarse sourceDirection =
          wz1PaperUnitRescalingMap coarse hrho
              (sourceZero + sourceDirection) -
            wz1PaperUnitRescalingMap coarse hrho sourceZero := by
      rw [hadd]
      abel
    rw [hdifference, hparameterOne, hparameterZero]
    simp only [rawScale]
    module
  have hangle := hcover.components.2
  have hangle_lt :
      InnerProductGeometry.angle
          (wz1PaperDirection source)
          (wz1PaperDirection coarse) <
        Real.pi / 2 := by
    have hpi : (1 : ℝ) < Real.pi := by
      linarith [Real.pi_gt_three]
    linarith
  have hcos_pos :
      0 <
        Real.cos
          (InnerProductGeometry.angle
            (wz1PaperDirection source)
            (wz1PaperDirection coarse)) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [
        InnerProductGeometry.angle_nonneg
          (wz1PaperDirection source)
          (wz1PaperDirection coarse),
        Real.pi_pos]
    · exact hangle_lt
  have hinner_pos :
      0 <
        inner ℝ
          (wz1PaperDirection source)
          (wz1PaperDirection coarse) := by
    rw [
      InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one
        (wz1PaperDirection_norm source)
        (wz1PaperDirection_norm coarse)]
    exact hcos_pos
  have hlinear_coord_pos :
      0 <
        (wz1PaperUnitRescalingLinear coarse sourceDirection)
          (2 : Fin 3) := by
    rw [wz1PaperUnitRescalingLinear_coord2]
    exact hinner_pos
  by_cases htargetSign :
      0 ≤ target.direction (2 : Fin 3)
  · refine ⟨rawScale, ?_, ?_⟩
    · have hcoord :=
        congrArg
          (fun point : Point3 => point (2 : Fin 3)) hraw
      simp only [PiLp.smul_apply, smul_eq_mul] at hcoord
      have htargetCoord :
          (1 / 2 : ℝ) ≤ target.direction (2 : Fin 3) := by
        simpa [wz1PaperDirection, htargetSign] using htarget.1
      nlinarith
    · simpa [sourceDirection, wz1PaperDirection, htargetSign]
        using hraw
  · have htargetNeg :
        target.direction (2 : Fin 3) < 0 :=
      lt_of_not_ge htargetSign
    refine ⟨-rawScale, ?_, ?_⟩
    · have hcoord :=
        congrArg
          (fun point : Point3 => point (2 : Fin 3)) hraw
      simp only [PiLp.smul_apply, smul_eq_mul] at hcoord
      nlinarith
    · rw [hraw]
      simp [sourceDirection, wz1PaperDirection, htargetSign]

/--
The target paper direction is the normalized linear image of the source paper
direction.
-/
lemma wz1PaperUnitRescaledTargetDirection_eq_normalize
    {delta rho targetDelta : ℝ}
    {source : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    {target : Kakeya.DeltaTube targetDelta}
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hcover : WZ1PaperTubeCovers source coarse)
    (htarget : WZ1PaperTubeInLineClass target)
    (haxis :
      tubeAxisLine target =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine source) :
    wz1PaperDirection target =
      NormedSpace.normalize
        (wz1PaperUnitRescalingLinear coarse
          (wz1PaperDirection source)) := by
  rcases
      wz1PaperUnitRescalingLinear_paperDirection_eq_pos_smul
        hrho hrho_one hcover htarget haxis with
    ⟨scale, hscale, hrelation⟩
  rw [hrelation, NormedSpace.normalize_smul_of_pos hscale]
  rw [
    NormedSpace.normalize_eq_self_of_norm_eq_one
      (wz1PaperDirection_norm target)]

/--
Angular lower distortion for two exact image-axis target tubes.
-/
lemma wz1PaperUnitRescaling_source_angle_le_target_angle
    {delta rho targetDelta : ℝ}
    {source₁ source₂ : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    {target₁ target₂ : Kakeya.DeltaTube targetDelta}
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hcover₁ : WZ1PaperTubeCovers source₁ coarse)
    (hcover₂ : WZ1PaperTubeCovers source₂ coarse)
    (htarget₁ : WZ1PaperTubeInLineClass target₁)
    (htarget₂ : WZ1PaperTubeInLineClass target₂)
    (haxis₁ :
      tubeAxisLine target₁ =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine source₁)
    (haxis₂ :
      tubeAxisLine target₂ =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine source₂) :
    InnerProductGeometry.angle
        (wz1PaperDirection source₁)
        (wz1PaperDirection source₂) ≤
      1050 * rho *
        InnerProductGeometry.angle
          (wz1PaperDirection target₁)
          (wz1PaperDirection target₂) := by
  have hsource :=
    wz1PaperUnitRescaling_source_angle_le
      hrho hrho_one hcover₁ hcover₂
  rw [
    wz1PaperUnitRescaledTargetDirection_eq_normalize
      hrho hrho_one hcover₁ htarget₁ haxis₁,
    wz1PaperUnitRescaledTargetDirection_eq_normalize
      hrho hrho_one hcover₂ htarget₂ haxis₂]
  simpa using hsource

/--
Positional lower distortion for two exact image-axis target tubes.
-/
lemma wz1PaperUnitRescaling_source_zero_dist_le_target
    {delta rho targetDelta : ℝ}
    {source₁ source₂ : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    {target₁ target₂ : Kakeya.DeltaTube targetDelta}
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hcover₁ : WZ1PaperTubeCovers source₁ coarse)
    (hcover₂ : WZ1PaperTubeCovers source₂ coarse)
    (hsource₁ : WZ1PaperTubeInLineClass source₁)
    (hsource₂ : WZ1PaperTubeInLineClass source₂)
    (htarget₁ : WZ1PaperTubeInLineClass target₁)
    (htarget₂ : WZ1PaperTubeInLineClass target₂)
    (haxis₁ :
      tubeAxisLine target₁ =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine source₁)
    (haxis₂ :
      tubeAxisLine target₂ =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine source₂) :
    dist
        (wz1TubeAxisZeroPoint source₁)
        (wz1TubeAxisZeroPoint source₂) ≤
      300 * rho *
          dist
            (wz1TubeAxisZeroPoint target₁)
            (wz1TubeAxisZeroPoint target₂) +
        6 * rho *
          InnerProductGeometry.angle
            (wz1PaperDirection source₁)
            (wz1PaperDirection source₂) := by
  let sourcePoint₁ :=
    wz1PaperOrthogonalSectionPoint source₁ coarse
  let sourcePoint₂ :=
    wz1PaperOrthogonalSectionPoint source₂ coarse
  let parameter₁ :=
    wz1PaperOrthogonalSectionParameter source₁ coarse
  let parameter₂ :=
    wz1PaperOrthogonalSectionParameter source₂ coarse
  have hinner₁ :=
    wz1PaperTubeCovers.inner_direction_ge_seven_eighths
      hrho_one hcover₁
  have hinner₂ :=
    wz1PaperTubeCovers.inner_direction_ge_seven_eighths
      hrho_one hcover₂
  have hinner₁_ne :
      inner ℝ
          (wz1PaperDirection source₁)
          (wz1PaperDirection coarse) ≠ 0 := by
    linarith
  have hinner₂_ne :
      inner ℝ
          (wz1PaperDirection source₂)
          (wz1PaperDirection coarse) ≠ 0 := by
    linarith
  have hsourcePoint₁ :
      sourcePoint₁ ∈ tubeAxisLine source₁ :=
    wz1PaperOrthogonalSectionPoint_mem_axis source₁ coarse
  have hsourcePoint₂ :
      sourcePoint₂ ∈ tubeAxisLine source₂ :=
    wz1PaperOrthogonalSectionPoint_mem_axis source₂ coarse
  have hsourcePoint₁_perp :
      inner ℝ
          (sourcePoint₁ - wz1TubeAxisZeroPoint coarse)
          (wz1PaperDirection coarse) =
        0 :=
    wz1PaperOrthogonalSectionPoint_perp hinner₁_ne
  have hsourcePoint₂_perp :
      inner ℝ
          (sourcePoint₂ - wz1TubeAxisZeroPoint coarse)
          (wz1PaperDirection coarse) =
        0 :=
    wz1PaperOrthogonalSectionPoint_perp hinner₂_ne
  have htarget_dist :
      dist
          (wz1TubeAxisZeroPoint target₁)
          (wz1TubeAxisZeroPoint target₂) =
        dist sourcePoint₁ sourcePoint₂ / (100 * rho) :=
    wz1PaperUnitRescaledAxisZeroPoint_dist_eq
      hrho htarget₁ htarget₂ haxis₁ haxis₂
      hsourcePoint₁ hsourcePoint₂
      hsourcePoint₁_perp hsourcePoint₂_perp
  have hparameter₂ :
      |parameter₂| ≤ rho :=
    abs_wz1PaperOrthogonalSectionParameter_le
      hrho hrho_one hcover₂
  have hzero_reintersection :
      ‖wz1TubeAxisZeroPoint source₁ -
          wz1TubeAxisZeroPoint source₂‖ ≤
        3 * ‖sourcePoint₁ - sourcePoint₂‖ +
          3 * rho *
            ‖wz1PaperDirection source₁ -
              wz1PaperDirection source₂‖ := by
    exact zero_section_reintersection_dist_le
      (rho := rho)
      (parameter₁ := parameter₁)
      (parameter₂ := parameter₂)
      (zero₁ := wz1TubeAxisZeroPoint source₁)
      (zero₂ := wz1TubeAxisZeroPoint source₂)
      (direction₁ := wz1PaperDirection source₁)
      (direction₂ := wz1PaperDirection source₂)
      (section₁ := sourcePoint₁)
      (section₂ := sourcePoint₂)
      hrho.le
      (wz1PaperDirection_norm source₁)
      hsource₁.1
      (wz1TubeAxisZeroPoint_coord_two source₁ hsource₁.vertical)
      (wz1TubeAxisZeroPoint_coord_two source₂ hsource₂.vertical)
      rfl rfl hparameter₂
  have hsource_chord :
      ‖wz1PaperDirection source₁ -
          wz1PaperDirection source₂‖ ≤
        InnerProductGeometry.angle
          (wz1PaperDirection source₁)
          (wz1PaperDirection source₂) :=
    unit_norm_sub_le_angle
      (wz1PaperDirection_norm source₁)
      (wz1PaperDirection_norm source₂)
  have hsection_distance :
      ‖sourcePoint₁ - sourcePoint₂‖ =
        100 * rho *
          dist
            (wz1TubeAxisZeroPoint target₁)
            (wz1TubeAxisZeroPoint target₂) := by
    rw [htarget_dist]
    rw [dist_eq_norm]
    field_simp [hrho.ne']
  rw [dist_eq_norm]
  calc
    ‖wz1TubeAxisZeroPoint source₁ -
        wz1TubeAxisZeroPoint source₂‖
        ≤ 3 * ‖sourcePoint₁ - sourcePoint₂‖ +
            3 * rho *
              ‖wz1PaperDirection source₁ -
                wz1PaperDirection source₂‖ :=
      hzero_reintersection
    _ ≤
        3 * (100 * rho *
          dist
            (wz1TubeAxisZeroPoint target₁)
            (wz1TubeAxisZeroPoint target₂)) +
          3 * rho *
            InnerProductGeometry.angle
              (wz1PaperDirection source₁)
              (wz1PaperDirection source₂) := by
      rw [← hsection_distance]
      gcongr
    _ ≤
        300 * rho *
            dist
              (wz1TubeAxisZeroPoint target₁)
              (wz1TubeAxisZeroPoint target₂) +
          6 * rho *
            InnerProductGeometry.angle
              (wz1PaperDirection source₁)
              (wz1PaperDirection source₂) := by
      have hangle_nonneg :
          0 ≤ InnerProductGeometry.angle
            (wz1PaperDirection source₁)
            (wz1PaperDirection source₂) :=
        InnerProductGeometry.angle_nonneg _ _
      nlinarith

/--
Full lower distortion of the paper line metric under exact image-axis unit
rescaling.
-/
lemma wz1PaperUnitRescaling_source_lineDistance_le_target
    {delta rho targetDelta : ℝ}
    {source₁ source₂ : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    {target₁ target₂ : Kakeya.DeltaTube targetDelta}
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hcover₁ : WZ1PaperTubeCovers source₁ coarse)
    (hcover₂ : WZ1PaperTubeCovers source₂ coarse)
    (hsource₁ : WZ1PaperTubeInLineClass source₁)
    (hsource₂ : WZ1PaperTubeInLineClass source₂)
    (htarget₁ : WZ1PaperTubeInLineClass target₁)
    (htarget₂ : WZ1PaperTubeInLineClass target₂)
    (haxis₁ :
      tubeAxisLine target₁ =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine source₁)
    (haxis₂ :
      tubeAxisLine target₂ =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine source₂) :
    wz1PaperLineDistance source₁ source₂ ≤
      7350 * rho *
        wz1PaperLineDistance target₁ target₂ := by
  have hposition :=
    wz1PaperUnitRescaling_source_zero_dist_le_target
      hrho hrho_one hcover₁ hcover₂
      hsource₁ hsource₂ htarget₁ htarget₂
      haxis₁ haxis₂
  have hangle :=
    wz1PaperUnitRescaling_source_angle_le_target_angle
      hrho hrho_one hcover₁ hcover₂
      htarget₁ htarget₂ haxis₁ haxis₂
  have hsource_angle_nonneg :
      0 ≤ InnerProductGeometry.angle
        (wz1PaperDirection source₁)
        (wz1PaperDirection source₂) :=
    InnerProductGeometry.angle_nonneg _ _
  have htarget_angle_nonneg :
      0 ≤ InnerProductGeometry.angle
        (wz1PaperDirection target₁)
        (wz1PaperDirection target₂) :=
    InnerProductGeometry.angle_nonneg _ _
  have htarget_dist_nonneg :
      0 ≤ dist
        (wz1TubeAxisZeroPoint target₁)
        (wz1TubeAxisZeroPoint target₂) :=
    dist_nonneg
  dsimp only [wz1PaperLineDistance] at *
  nlinarith

/--
Close the strong source-separation transfer from the quantitative lower
distortion theorem.
-/
theorem wz2_paper_strong_source_separation_transfer_from_lower_distortion :
    WZ2PaperStrongSourceSeparationTransferStatement := by
  intro delta rho hdelta _hdelta_rho
    fine coarse cover parent hrho hrho_one hcoarse
    C data selected hselected hstrong
  intro first second hne
  change Fin selected.family.card at first second
  let source₁ := selected.family.tube first
  let source₂ := selected.family.tube second
  let target₁ :=
    (data.targetSubfamilyForSource selected).family.tube first
  let target₂ :=
    (data.targetSubfamilyForSource selected).family.tube second
  have hsource₁ :
      WZ1PaperTubeInLineClass source₁ :=
    hselected first
  have hsource₂ :
      WZ1PaperTubeInLineClass source₂ :=
    hselected second
  have htarget_family :
      WZ1PaperIsLineClass
        (data.targetSubfamilyForSource selected).family :=
    data.target_line_class.subfamily
      (data.targetSubfamilyForSource selected)
  have htarget₁ :
      WZ1PaperTubeInLineClass target₁ :=
    htarget_family first
  have htarget₂ :
      WZ1PaperTubeInLineClass target₂ :=
    htarget_family second
  have hcover₁ :
      WZ1PaperTubeCovers source₁ (coarse.tube parent) := by
    dsimp only [source₁]
    simpa only [selected.tube_eq] using
      cover.fullFiberSubfamily_covered parent
        (selected.embedding first)
  have hcover₂ :
      WZ1PaperTubeCovers source₂ (coarse.tube parent) := by
    dsimp only [source₂]
    simpa only [selected.tube_eq] using
      cover.fullFiberSubfamily_covered parent
        (selected.embedding second)
  have haxis₁ :
      tubeAxisLine target₁ =
        wz1PaperUnitRescalingMap
            (coarse.tube parent) hrho ''
          tubeAxisLine source₁ := by
    simpa only [source₁, selected.tube_eq] using
      data.targetSubfamilyForSource_axis selected first
  have haxis₂ :
      tubeAxisLine target₂ =
        wz1PaperUnitRescalingMap
            (coarse.tube parent) hrho ''
          tubeAxisLine source₂ := by
    simpa only [source₂, selected.tube_eq] using
      data.targetSubfamilyForSource_axis selected second
  have hlower :
      wz1PaperLineDistance source₁ source₂ ≤
        7350 * rho *
          wz1PaperLineDistance target₁ target₂ :=
    wz1PaperUnitRescaling_source_lineDistance_le_target
      hrho hrho_one hcover₁ hcover₂
      hsource₁ hsource₂ htarget₁ htarget₂
      haxis₁ haxis₂
  have hstrong_pair :
      10000 * delta <
        wz1PaperLineDistance source₁ source₂ :=
    hstrong first second hne
  have htarget_nonneg :
      0 ≤ wz1PaperLineDistance target₁ target₂ := by
    exact add_nonneg dist_nonneg
      (InnerProductGeometry.angle_nonneg _ _)
  have hdelta_target :
      delta < rho *
        wz1PaperLineDistance target₁ target₂ := by
    nlinarith
  change delta / rho <
    wz1PaperLineDistance target₁ target₂
  exact (div_lt_iff₀ hrho).mpr (by simpa [mul_comm] using hdelta_target)

lemma wz1PaperUnitRescalingMap_volume
    {rho : ℝ} (coarse : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (source : Set Point3) (hsource : MeasurableSet source) :
    MeasureTheory.volume
        (wz1PaperUnitRescalingMap coarse hrho '' source) =
      ENNReal.ofReal ((1 / (100 * rho)) ^ 2) *
        MeasureTheory.volume source :=
  unitRescalingMap_volume
    (wz1TubeAxisZeroPoint coarse)
    (wz1PaperDirection coarse)
    (wz1PaperDirection_norm coarse)
    (100 * rho) (by positivity) source hsource

end Kakeya.Assouad
