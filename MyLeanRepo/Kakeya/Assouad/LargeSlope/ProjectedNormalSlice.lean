import MyLeanRepo.Kakeya.Assouad.LargeSlope.ExternalCoveringNumberIsometry
import MyLeanRepo.Kakeya.Assouad.LargeSlope.ProjectedNormalSliceStatement

/-!
# Projecting a local plane normal onto the xz-plane

On a fixed y-slice, projection along the full normal and projection along its
xz-component differ by a translation.  The local one-dimensional AD estimate
therefore transfers unchanged.
-/

namespace Kakeya.Assouad

open Metric

private lemma coordinate_abs_le_norm
    {n : ℕ} (p : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |p i| ≤ ‖p‖ := by
  have hinner :
      inner ℝ p (EuclideanSpace.single i (1 : ℝ)) = p i := by
    rw [EuclideanSpace.inner_single_right]
    simp
  have hbound :
      |inner ℝ p (EuclideanSpace.single i (1 : ℝ))| ≤
        ‖p‖ * ‖(EuclideanSpace.single i (1 : ℝ))‖ :=
    abs_real_inner_le_norm p (EuclideanSpace.single i (1 : ℝ))
  have hsingle :
      ‖(EuclideanSpace.single i (1 : ℝ))‖ = 1 := by
    rw [PiLp.norm_single]
    norm_num
  rw [hinner, hsingle] at hbound
  simpa using hbound

private lemma translate_inter_closedBall
    (c : ℝ) (S : Set ℝ) (x r : ℝ) :
    ((fun t : ℝ => t - c) '' S) ∩ Metric.closedBall x r =
      (fun t : ℝ => t - c) ''
        (S ∩ Metric.closedBall (x + c) r) := by
  ext t'
  simp only [Set.mem_inter_iff, Set.mem_image, Metric.mem_closedBall]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hdist⟩
    refine ⟨t, ⟨ht, ?_⟩, rfl⟩
    simpa [Real.dist_eq] using hdist
  · rintro ⟨t, ⟨ht, hdist⟩, rfl⟩
    refine ⟨⟨t, ht, rfl⟩, ?_⟩
    simpa [Real.dist_eq] using hdist

theorem large_slope_projected_normal_slice :
    LargeSlopeProjectedNormalSliceStatement := by
  intro E v y₀ rho alpha C hv hEball hslice
  set c : ℝ := y₀ * v (1 : Fin 3) with hc_def
  set S : Set ℝ := scalarProjection v E with hS_def
  set S' : Set ℝ := scalarProjection (xzProjectedNormal v) E
    with hS'_def
  set f : ℝ → ℝ := fun t => t - c with hf_def
  have hinner :
      ∀ p ∈ E,
        inner ℝ p (xzProjectedNormal v) = inner ℝ p v - c := by
    intro p hp
    have hslice' : p (1 : Fin 3) = y₀ := hslice p hp
    have hprojected :
        inner ℝ p (xzProjectedNormal v) =
          p 0 * v 0 + p 2 * v 2 := by
      have h :
          inner ℝ p (xzProjectedNormal v) =
            inner ℝ p (EuclideanSpace.single 0 (v 0)) +
              inner ℝ p (EuclideanSpace.single 2 (v 2)) := by
        rw [xzProjectedNormal, inner_add_right]
      rw [h]
      have h0 :
          inner ℝ p (EuclideanSpace.single 0 (v 0)) =
            v 0 * p 0 := by
        rw [EuclideanSpace.inner_single_right]
        simp
      have h2 :
          inner ℝ p (EuclideanSpace.single 2 (v 2)) =
            v 2 * p 2 := by
        rw [EuclideanSpace.inner_single_right]
        simp
      rw [h0, h2]
      ring
    have hfull :
        inner ℝ p v =
          p 0 * v 0 + p 1 * v 1 + p 2 * v 2 := by
      rw [PiLp.inner_apply]
      simp [Fin.sum_univ_succ, mul_comm]
      ring
    rw [hprojected, hfull, hslice', hc_def]
    ring
  have htranslate : S' = f '' S := by
    ext t'
    simp only [hS'_def, hS_def, scalarProjection,
      Set.mem_image, hf_def]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact
        ⟨inner ℝ p v, ⟨p, hp, rfl⟩,
          by rw [hinner p hp]⟩
    · rintro ⟨t, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, hinner p hp⟩
  have hS_bounded : S ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro t ht
    rcases ht with ⟨p, hp, rfl⟩
    have hpnorm : ‖p‖ ≤ 1 := by
      have hunit : p ∈ Kakeya.DeltaTube.unitBall := hEball hp
      simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall,
        dist_zero_right] using hunit
    have hinner_bound :
        |inner ℝ p v| ≤ ‖p‖ * ‖v‖ :=
      abs_real_inner_le_norm p v
    rw [hv, mul_one] at hinner_bound
    exact
      ⟨by linarith [abs_le.mp (hinner_bound.trans hpnorm)],
        by linarith [abs_le.mp (hinner_bound.trans hpnorm)]⟩
  have hS'_bounded : S' ⊆ Set.Icc (-4 : ℝ) 4 := by
    by_cases hE : E = ∅
    · rw [hS'_def, scalarProjection, hE, Set.image_empty]
      simp
    · rcases Set.nonempty_iff_ne_empty.mpr hE with ⟨p₀, hp₀⟩
      have hp₀norm : ‖p₀‖ ≤ 1 := by
        have hunit : p₀ ∈ Kakeya.DeltaTube.unitBall := hEball hp₀
        simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall,
          dist_zero_right] using hunit
      have hy₀ : |y₀| ≤ 1 := by
        rw [← hslice p₀ hp₀]
        exact (coordinate_abs_le_norm p₀ 1).trans hp₀norm
      have hv₁ : |v (1 : Fin 3)| ≤ 1 := by
        simpa [hv] using coordinate_abs_le_norm v (1 : Fin 3)
      have hc : |c| ≤ 1 := by
        rw [hc_def, abs_mul]
        nlinarith [abs_nonneg y₀, abs_nonneg (v (1 : Fin 3))]
      intro t' ht'
      rw [htranslate] at ht'
      rcases ht' with ⟨t, ht, rfl⟩
      have ht_interval : t ∈ Set.Icc (-1 : ℝ) 1 :=
        hS_bounded ht
      have ht_abs : |t| ≤ 1 := abs_le.mpr ht_interval
      have hsub : |t - c| ≤ 2 := by
        calc
          |t - c| ≤ |t| + |c| := abs_sub t c
          _ ≤ 1 + 1 := add_le_add ht_abs hc
          _ = 2 := by norm_num
      change f t ∈ Set.Icc (-4 : ℝ) 4
      simp only [f]
      exact
        ⟨by linarith [abs_le.mp hsub],
          by linarith [abs_le.mp hsub]⟩
  refine ⟨htranslate, ?_⟩
  intro hAD
  rcases hAD with
    ⟨hrho_pos, halpha_pos, halpha_one, hC_one, _, hcover⟩
  refine
    ⟨hrho_pos, halpha_pos, halpha_one, hC_one,
      hS'_bounded, ?_⟩
  intro rho' hrho' hdelta_rho hrho_one x r hrho_r hr_one
  have hlocal :
      S' ∩ Metric.closedBall x r =
        f '' (S ∩ Metric.closedBall (x + c) r) := by
    rw [htranslate]
    exact translate_inter_closedBall c S x r
  rw [hlocal]
  rw [translation_externalCoveringNumber c
    (S ∩ Metric.closedBall (x + c) r) ⟨rho', hrho'⟩]
  exact hcover rho' hrho' hdelta_rho hrho_one
    (x + c) r hrho_r hr_one

/--
If a unit normal has y-component at most `sqrt rho` and `rho ≤ 1 / 4`,
then its xz-projection is quantitatively nondegenerate.
-/
lemma xzProjectedNormal_norm_lower
    {v : Point3} {rho : ℝ}
    (hv_unit : ‖v‖ = 1)
    (hvy : |v 1| ≤ Real.sqrt rho)
    (hrho_pos : 0 < rho)
    (hrho_le_quarter : rho ≤ 1 / 4) :
    (1 / 2 : ℝ) ≤ ‖xzProjectedNormal v‖ := by
  have hv_y_sq : (v 1) ^ 2 ≤ rho := by
    have hsq : (v 1) ^ 2 ≤ (Real.sqrt rho) ^ 2 := by
      exact sq_le_sq.mpr (by
        rw [abs_of_nonneg (Real.sqrt_nonneg rho)]
        exact hvy)
    simpa [Real.sq_sqrt hrho_pos.le] using hsq
  have hv_sum_sq :
      (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 = 1 := by
    have hnorm :
        ‖v‖ = Real.sqrt ((v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    have hsum_nonneg :
        0 ≤ (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 := by
      positivity
    rw [hnorm] at hv_unit
    nlinarith [Real.sq_sqrt hsum_nonneg]
  have hprojected_sq :
      ‖xzProjectedNormal v‖ ^ 2 = (v 0) ^ 2 + (v 2) ^ 2 := by
    have hnonneg : 0 ≤ (v 0) ^ 2 + (v 2) ^ 2 := by
      positivity
    simp [xzProjectedNormal, EuclideanSpace.norm_eq,
      Fin.sum_univ_three, Real.sq_sqrt hnonneg]
  have hsq_lower : 3 / 4 ≤ ‖xzProjectedNormal v‖ ^ 2 := by
    rw [hprojected_sq]
    linarith
  nlinarith [norm_nonneg (xzProjectedNormal v)]

/-- The sharper lower bound used in the final Step 4 prism constants. -/
lemma xzProjectedNormal_norm_lower_strong
    {v : Point3} {rho : ℝ}
    (hv_unit : ‖v‖ = 1)
    (hvy : |v 1| ≤ Real.sqrt rho)
    (hrho_pos : 0 < rho)
    (hrho_le_quarter : rho ≤ 1 / 4) :
    Real.sqrt 3 / 2 ≤ ‖xzProjectedNormal v‖ := by
  have hv_y_sq : (v 1) ^ 2 ≤ rho := by
    have hsq : (v 1) ^ 2 ≤ (Real.sqrt rho) ^ 2 := by
      exact sq_le_sq.mpr (by
        rw [abs_of_nonneg (Real.sqrt_nonneg rho)]
        exact hvy)
    simpa [Real.sq_sqrt hrho_pos.le] using hsq
  have hv_sum_sq :
      (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 = 1 := by
    have hnorm :
        ‖v‖ = Real.sqrt ((v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    have hsum_nonneg :
        0 ≤ (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 := by
      positivity
    rw [hnorm] at hv_unit
    nlinarith [Real.sq_sqrt hsum_nonneg]
  have hprojected_sq :
      ‖xzProjectedNormal v‖ ^ 2 = (v 0) ^ 2 + (v 2) ^ 2 := by
    have hnonneg : 0 ≤ (v 0) ^ 2 + (v 2) ^ 2 := by
      positivity
    simp [xzProjectedNormal, EuclideanSpace.norm_eq,
      Fin.sum_univ_three, Real.sq_sqrt hnonneg]
  have hsq_lower : 3 / 4 ≤ ‖xzProjectedNormal v‖ ^ 2 := by
    rw [hprojected_sq]
    linarith
  nlinarith [norm_nonneg (xzProjectedNormal v),
    Real.sqrt_nonneg 3,
    Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

/--
Plane-map incidence transfers to the normalized xz-projection on the Step 4
good set.
-/
lemma normalizedXZNormal_incidence
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho_pos : 0 < rho)
    {direction normal : Point3}
    (hdirection_unit : ‖direction‖ = 1)
    (hnormal_unit : ‖normal‖ = 1)
    (hnormal_y : |normal 1| ≤ Real.sqrt rho)
    (hincidence : |inner ℝ direction normal| ≤ 6 * delta)
    (hprojected_lower :
      (1 / 2 : ℝ) ≤ ‖xzProjectedNormal normal‖)
    (hdelta_scale : 12 * delta ≤ Real.sqrt rho) :
    |inner ℝ direction (normalizedXZNormal normal)| ≤
      3 * Real.sqrt rho := by
  let projected := xzProjectedNormal normal
  have hprojected_inner :
      inner ℝ direction projected =
        inner ℝ direction normal - direction 1 * normal 1 := by
    have hsum :
        ∀ x y : Point3,
          inner ℝ x y =
            x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
      intro x y
      rw [PiLp.inner_apply]
      simp [Fin.sum_univ_three]
      ring
    rw [hsum direction projected, hsum direction normal]
    simp [projected, xzProjectedNormal]
    ring
  have hdirection_y : |direction 1| ≤ 1 := by
    simpa [hdirection_unit] using
      coordinate_abs_le_norm direction (1 : Fin 3)
  have hinner_bound :
      |inner ℝ direction projected| ≤
        6 * delta + Real.sqrt rho := by
    rw [hprojected_inner]
    calc
      |inner ℝ direction normal - direction 1 * normal 1|
          ≤ |inner ℝ direction normal| +
              |direction 1 * normal 1| := abs_sub _ _
      _ ≤ 6 * delta + Real.sqrt rho := by
        rw [abs_mul]
        nlinarith [abs_nonneg (direction 1),
          abs_nonneg (normal 1), Real.sqrt_nonneg rho]
  have hprojected_pos : 0 < ‖projected‖ := by
    linarith
  have hinverse_bound : ‖projected‖⁻¹ ≤ 2 := by
    calc
      ‖projected‖⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := by
        gcongr
      _ = 2 := by norm_num
  have hnormalized :
      inner ℝ direction (normalizedXZNormal normal) =
        ‖projected‖⁻¹ * inner ℝ direction projected := by
    simp [normalizedXZNormal, projected, inner_smul_right]
  rw [hnormalized, abs_mul]
  calc
    |‖projected‖⁻¹| * |inner ℝ direction projected|
        = ‖projected‖⁻¹ * |inner ℝ direction projected| := by
          rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg projected))]
    _ ≤ 2 * (6 * delta + Real.sqrt rho) := by
      gcongr
    _ = 12 * delta + 2 * Real.sqrt rho := by ring
    _ ≤ 3 * Real.sqrt rho := by linarith

/--
The sharper projected-normal bound gives the `16 * width` incidence used by
the Step 4 xz-grid when `sqrt rho = 8 * width`.
-/
lemma normalizedXZNormal_incidence_strong
    {delta rho width : ℝ}
    (hdelta : 0 < delta)
    (hrho_pos : 0 < rho)
    {direction normal : Point3}
    (hdirection_unit : ‖direction‖ = 1)
    (hnormal_y : |normal 1| ≤ Real.sqrt rho)
    (hincidence : |inner ℝ direction normal| ≤ 6 * delta)
    (hprojected_lower :
      Real.sqrt 3 / 2 ≤ ‖xzProjectedNormal normal‖)
    (hdelta_scale : 12 * delta ≤ Real.sqrt rho)
    (hsqrt_rho : Real.sqrt rho = 8 * width)
    (hwidth_pos : 0 < width) :
    |inner ℝ direction (normalizedXZNormal normal)| ≤ 16 * width := by
  let projected := xzProjectedNormal normal
  have hprojected_inner :
      inner ℝ direction projected =
        inner ℝ direction normal - direction 1 * normal 1 := by
    have hsum :
        ∀ x y : Point3,
          inner ℝ x y =
            x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
      intro x y
      rw [PiLp.inner_apply]
      simp [Fin.sum_univ_three]
      ring
    rw [hsum direction projected, hsum direction normal]
    simp [projected, xzProjectedNormal]
    ring
  have hdirection_y : |direction 1| ≤ 1 := by
    simpa [hdirection_unit] using
      coordinate_abs_le_norm direction (1 : Fin 3)
  have hinner_bound :
      |inner ℝ direction projected| ≤
        6 * delta + Real.sqrt rho := by
    rw [hprojected_inner]
    calc
      |inner ℝ direction normal - direction 1 * normal 1|
          ≤ |inner ℝ direction normal| +
              |direction 1 * normal 1| := abs_sub _ _
      _ ≤ 6 * delta + Real.sqrt rho := by
        rw [abs_mul]
        nlinarith [abs_nonneg (direction 1),
          abs_nonneg (normal 1), Real.sqrt_nonneg rho]
  have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hprojected_pos : 0 < ‖projected‖ := by
    have h : 0 < Real.sqrt 3 / 2 := by positivity
    linarith
  have hinverse_bound :
      ‖projected‖⁻¹ ≤ 2 / Real.sqrt 3 := by
    calc
      ‖projected‖⁻¹ ≤ (Real.sqrt 3 / 2)⁻¹ := by
        gcongr
      _ = 2 / Real.sqrt 3 := by
        field_simp [hsqrt3_pos.ne']
  have hnormalized :
      inner ℝ direction (normalizedXZNormal normal) =
        ‖projected‖⁻¹ * inner ℝ direction projected := by
    simp [normalizedXZNormal, projected, inner_smul_right]
  rw [hnormalized, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg projected))]
  calc
    ‖projected‖⁻¹ * |inner ℝ direction projected|
        ≤ (2 / Real.sqrt 3) *
            (6 * delta + Real.sqrt rho) := by
          gcongr
    _ ≤ (3 * Real.sqrt rho) / Real.sqrt 3 := by
      have hnonneg : 0 ≤ 2 / Real.sqrt 3 := by positivity
      have hinside :
          6 * delta + Real.sqrt rho ≤
            (3 * Real.sqrt rho) / 2 := by
        linarith
      calc
        (2 / Real.sqrt 3) * (6 * delta + Real.sqrt rho)
            ≤ (2 / Real.sqrt 3) * ((3 * Real.sqrt rho) / 2) :=
              mul_le_mul_of_nonneg_left hinside hnonneg
        _ = (3 * Real.sqrt rho) / Real.sqrt 3 := by ring
    _ = Real.sqrt 3 * Real.sqrt rho := by
      field_simp [hsqrt3_pos.ne']
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    _ ≤ 16 * width := by
      rw [hsqrt_rho]
      have hsqrt3_le_two : Real.sqrt 3 ≤ 2 := by
        nlinarith [Real.sqrt_nonneg 3,
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      nlinarith

end Kakeya.Assouad
