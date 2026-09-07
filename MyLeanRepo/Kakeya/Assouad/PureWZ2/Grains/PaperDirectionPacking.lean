import MyLeanRepo.Kakeya.Assouad.WZ1.PaperPackingRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.CoarseDirectionPacking.GeometricOverlap
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance
import Mathlib.Tactic

/-!
# Direction packing for paper tube shadings

Adapts the WZ1 coarse direction packing bound to `WZ1PaperTubeShading`
using the paper line-distance metric and `tube_packing_bound_general`.

## Key lemma

`paper_line_distance_shared_point`: if two paper tubes both contain a point `p`
and their directions have cross-product norm `< 10*L`, then their paper
line-distance is `≤ 500*L`.

This reduces direction non-concentration to `tube_packing_bound_general`,
giving the universal bound `8001^5` (which fits within the stated constant
`2 * 4 * 601^3 * 12001^3`).
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set InnerProductGeometry

attribute [local instance] Classical.propDecidable

/-- Norm squared of a Point3 equals sum of coordinate squares. -/
lemma point3_norm_sq (x : Point3) : ‖x‖^2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := by
  have h1 : ‖x‖^2 = ∑ i : Fin 3, (x i)^2 := EuclideanSpace.real_norm_sq_eq x
  rw [h1]
  have h2 : ∑ i : Fin 3, (x i)^2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    <;> simp
    <;> ring
  exact h2

/-- Angle bound for unit vectors: `angle u v ≤ (π/2) * ‖u - v‖`. -/
lemma angle_le_pi2_mul_norm_sub {u v : Point3}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    InnerProductGeometry.angle u v ≤ (Real.pi / 2) * ‖u - v‖ := by
  set theta : ℝ := InnerProductGeometry.angle u v
  have htheta_nonneg : 0 ≤ theta := InnerProductGeometry.angle_nonneg u v
  have htheta_le_pi : theta ≤ Real.pi := InnerProductGeometry.angle_le_pi u v
  have hinner : inner ℝ u v = Real.cos theta := by
    have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm u v
    rw [hu, hv] at h
    simpa [theta] using h.symm
  have hnorm_sq : ‖u - v‖ ^ 2 = (2 * Real.sin (theta / 2)) ^ 2 := by
    have hnorm : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * inner ℝ u v + ‖v‖ ^ 2 :=
      norm_sub_sq_real u v
    have hcos : Real.cos theta = 1 - 2 * Real.sin (theta / 2) ^ 2 := by
      have htwo := Real.cos_two_mul (theta / 2)
      have htrig := Real.sin_sq_add_cos_sq (theta / 2)
      have harg : 2 * (theta / 2) = theta := by ring
      rw [harg] at htwo
      nlinarith
    rw [hnorm, hu, hv, hinner, hcos] <;> ring
  have hsin_nonneg : 0 ≤ Real.sin (theta / 2) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hnorm : ‖u - v‖ = 2 * Real.sin (theta / 2) := by
    nlinarith [norm_nonneg (u - v)]
  have hhalf_le : theta / 2 ≤ Real.pi / 2 := by linarith
  have hsin_lower : theta / 2 ≤ (Real.pi / 2) * Real.sin (theta / 2) :=
    le_pi2_mul_sin (theta / 2) (by linarith) hhalf_le
  rw [hnorm]
  nlinarith [Real.pi_pos]

/-- From `p ∈ Metric.cthickening (6*L) s`, get `q ∈ s` with `dist p q < 7*L`. -/
lemma point_on_line_within {L : ℝ} (hL_pos : 0 < L)
    {T : Kakeya.DeltaTube L} {p : Point3}
    (h : p ∈ Metric.cthickening (6 * L) (tubeAxisLine T)) :
    ∃ (q : Point3), q ∈ tubeAxisLine T ∧ dist p q < 7 * L := by
  have h_inf : Metric.infEDist p (tubeAxisLine T) ≤ ENNReal.ofReal (6 * L) := by
    simpa [Metric.mem_cthickening_iff] using h
  have h7pos : 0 < (7 * L : ℝ) := by positivity
  have h_lt : Metric.infEDist p (tubeAxisLine T) < ENNReal.ofReal (7 * L) := by
    calc
      Metric.infEDist p (tubeAxisLine T) ≤ ENNReal.ofReal (6 * L) := h_inf
      _ < ENNReal.ofReal (7 * L) := by
        rw [ENNReal.ofReal_lt_ofReal_iff h7pos] <;> linarith
  rw [Metric.infEDist_lt_iff] at h_lt
  rcases h_lt with ⟨q, hq, h_edist⟩
  have h_dist : edist p q = ENNReal.ofReal (dist p q) := by rw [edist_dist]
  rw [h_dist] at h_edist
  have h_final : dist p q < 7 * L :=
    (ENNReal.ofReal_lt_ofReal_iff h7pos).mp h_edist
  exact ⟨q, hq, h_final⟩

/-- If unit vectors have z-components ≥ 1/2, their inner product is ≥ -1/2. -/
lemma paper_inner_lower_bound {u v : Point3}
    (hu_norm : ‖u‖ = 1) (hv_norm : ‖v‖ = 1)
    (hu_z : (1 / 2 : ℝ) ≤ u 2) (hv_z : (1 / 2 : ℝ) ≤ v 2) :
    -(1 / 2 : ℝ) ≤ inner ℝ u v := by
  have h_i_coord : (u 0)^2 + (u 1)^2 + (u 2)^2 = 1 := by
    have h1 : ‖u‖^2 = (u 0)^2 + (u 1)^2 + (u 2)^2 := point3_norm_sq u
    rw [← h1, hu_norm] <;> norm_num
  have h_j_coord : (v 0)^2 + (v 1)^2 + (v 2)^2 = 1 := by
    have h1 : ‖v‖^2 = (v 0)^2 + (v 1)^2 + (v 2)^2 := point3_norm_sq v
    rw [← h1, hv_norm] <;> norm_num
  have h_expand : inner ℝ u v = (u 0) * (v 0) + (u 1) * (v 1) + (u 2) * (v 2) := by
    have h1 : 2 * inner ℝ u v = ‖u + v‖^2 - ‖u‖^2 - ‖v‖^2 := by
      rw [norm_add_sq_real] <;> ring
    have h2 : ‖u + v‖^2 = (u 0 + v 0)^2 + (u 1 + v 1)^2 + (u 2 + v 2)^2 := by
      rw [point3_norm_sq]
      have h3 : (u + v) 0 = u 0 + v 0 := by simp
      have h4 : (u + v) 1 = u 1 + v 1 := by simp
      have h5 : (u + v) 2 = u 2 + v 2 := by simp
      rw [h3, h4, h5] <;> ring
    rw [h2, point3_norm_sq u, point3_norm_sq v] at h1
    linarith
  set xy := (u 0) * (v 0) + (u 1) * (v 1) with hxy_def
  have h_xy2 : xy^2 ≤ ((u 0)^2 + (u 1)^2) * ((v 0)^2 + (v 1)^2) := by
    nlinarith [sq_nonneg ((u 0) * (v 1) - (u 1) * (v 0))]
  have h_i_xy : (u 0)^2 + (u 1)^2 ≤ 3 / 4 := by nlinarith [hu_z, h_i_coord]
  have h_j_xy : (v 0)^2 + (v 1)^2 ≤ 3 / 4 := by nlinarith [hv_z, h_j_coord]
  have h_xy_bound : |xy| ≤ 3 / 4 := by
    have h4 : xy^2 ≤ (3 / 4 : ℝ)^2 := by
      calc xy^2 ≤ ((u 0)^2 + (u 1)^2) * ((v 0)^2 + (v 1)^2) := h_xy2
           _ ≤ (3 / 4 : ℝ) * (3 / 4 : ℝ) := by gcongr <;> linarith
           _ = (3 / 4 : ℝ)^2 := by ring
    have h6 : 0 ≤ |xy| := by positivity
    have h7 : |xy|^2 ≤ (3 / 4 : ℝ)^2 := by
      have h8 : |xy|^2 = xy^2 := by simp [sq_abs]
      rw [h8]; exact h4
    nlinarith
  have h_ge : xy ≥ -(3 / 4 : ℝ) := (abs_le.mp h_xy_bound).1
  have h_zprod : (u 2) * (v 2) ≥ 1 / 4 := by nlinarith
  rw [h_expand]
  have h_xy_eq : xy = (u 0) * (v 0) + (u 1) * (v 1) := by dsimp only [xy] <;> ring
  linarith [h_ge, h_zprod, h_xy_eq]

/-- Given `inner^2 > 1 - 100*L^2` and `inner ≥ -1/2`, prove `inner > 1 - 100*L^2`. -/
lemma paper_inner_strict_lower {L : ℝ} (hL_pos : 0 < L) (hL_small : L ≤ 1 / 10000)
    {x : ℝ} (h_sq : x^2 > 1 - 100 * L^2) (h_lower : -(1 / 2 : ℝ) ≤ x) :
    x > 1 - 100 * L^2 := by
  have h9 : (1 - 100 * L^2) > 1 / 4 := by
    have hL2 : L^2 ≤ (1 / 10000 : ℝ)^2 := by gcongr
    nlinarith
  have h10 : x^2 > 1 / 4 := by linarith
  have h_pos : 0 < x := by
    by_cases h : 0 < x
    · exact h
    · have h_nonpos : x ≤ 0 := by linarith
      have h3 : 0 ≤ -x := by linarith
      have h4 : -x ≤ 1 / 2 := by linarith
      have h5 : (-x)^2 ≤ (1 / 2 : ℝ)^2 := by gcongr
      have h6 : x^2 = (-x)^2 := by ring
      have h7 : x^2 ≤ (1 / 2 : ℝ)^2 := by rw [h6]; exact h5
      have h_eq : (1 / 2 : ℝ)^2 = 1 / 4 := by norm_num
      rw [h_eq] at h7
      exact False.elim (not_le.mpr h10 h7)
  have h9' : 0 < 1 - 100 * L^2 := by
    have hL2 : L^2 ≤ (1 / 10000 : ℝ)^2 := by gcongr
    nlinarith
  have h10' : (1 - 100 * L^2)^2 < 1 - 100 * L^2 := by
    have h_pos2 : 0 < 1 - 100 * L^2 := h9'
    have h2 : 0 < L^2 := by positivity
    have h3 : (1 - 100 * L^2) * (100 * L^2) > 0 := by positivity
    have h4 : (1 - 100 * L^2) - (1 - 100 * L^2)^2 = (1 - 100 * L^2) * (100 * L^2) := by ring
    have h5 : (1 - 100 * L^2) - (1 - 100 * L^2)^2 > 0 := by rw [h4]; exact h3
    linarith
  have h11 : x^2 > (1 - 100 * L^2)^2 := by
    calc x^2 > 1 - 100 * L^2 := h_sq
         _ > (1 - 100 * L^2)^2 := h10'
  have h12 : 0 ≤ x := by linarith [h_pos]
  have h13 : 0 ≤ 1 - 100 * L^2 := by linarith [h9']
  by_contra h14
  have h15 : x ≤ 1 - 100 * L^2 := by linarith
  have h17 : 0 ≤ (1 - 100 * L^2) - x := by linarith
  have h18 : 0 ≤ (1 - 100 * L^2) + x := by linarith
  have h19 : 0 ≤ ((1 - 100 * L^2) - x) * ((1 - 100 * L^2) + x) := by positivity
  have h20 : (1 - 100 * L^2)^2 - x^2 =
      ((1 - 100 * L^2) - x) * ((1 - 100 * L^2) + x) := by ring
  have h21 : (1 - 100 * L^2)^2 - x^2 ≥ 0 := by linarith [h19, h20]
  linarith [h11]

/-- Given `inner > 1 - 100*L^2` for unit vectors, prove `‖u - v‖ < 15*L`. -/
lemma paper_dir_diff_bound {L : ℝ} (hL_pos : 0 < L)
    {u v : Point3} (hu_norm : ‖u‖ = 1) (hv_norm : ‖v‖ = 1)
    (h_inner_gt : inner ℝ u v > 1 - 100 * L^2) :
    ‖u - v‖ < 15 * L := by
  have h4 : ‖u - v‖^2 = 2 - 2 * inner ℝ u v := by
    rw [norm_sub_sq_real, hu_norm, hv_norm] <;> ring
  have h6 : ‖u - v‖^2 < 200 * L^2 := by
    rw [h4]; linarith [h_inner_gt]
  have h7 : 0 ≤ ‖u - v‖ := by positivity
  have h8 : 200 * L^2 < (15 * L)^2 := by nlinarith [hL_pos]
  have h10 : ‖u - v‖^2 < (15 * L)^2 := lt_trans h6 h8
  have h11 : 0 ≤ 15 * L := by positivity
  have h12 : ‖u - v‖ + 15 * L > 0 := by linarith [h7, h11, hL_pos]
  have h13 : (15 * L)^2 - ‖u - v‖^2 > 0 := by linarith
  have h14 : (15 * L - ‖u - v‖) * (15 * L + ‖u - v‖) > 0 := by
    have h15 : (15 * L)^2 - ‖u - v‖^2 =
        (15 * L - ‖u - v‖) * (15 * L + ‖u - v‖) := by ring
    rw [h15] at h13; exact h13
  have h16 : 15 * L - ‖u - v‖ > 0 := by
    by_contra h17
    have h18 : 15 * L - ‖u - v‖ ≤ 0 := by linarith
    have h19 : (15 * L - ‖u - v‖) * (15 * L + ‖u - v‖) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg h18 (by linarith)
    linarith [h14]
  linarith

/--
Bound the parameter difference `|t_i - t_j|` given nearby axis points
and close directions.
-/
lemma paper_parameter_diff_bound {L : ℝ} (hL_pos : 0 < L) (hL_small : L ≤ 1 / 10000)
    (u_i u_j : Point3) (t_i t_j : ℝ)
    (q_i q_j : Point3)
    (hui_z : (1 / 2 : ℝ) ≤ u_i 2)
    (huj_z : (1 / 2 : ℝ) ≤ u_j 2)
    (hui_norm : ‖u_i‖ = 1)
    (huj_norm : ‖u_j‖ = 1)
    (hti_z : q_i 2 = t_i * (u_i 2))
    (htj_z : q_j 2 = t_j * (u_j 2))
    (h_q_diff : ‖q_i - q_j‖ ≤ 14 * L)
    (hqi_z_bound : |q_i 2| ≤ 1 + 7 * L)
    (hqj_z_bound : |q_j 2| ≤ 1 + 7 * L)
    (h_dir_diff : ‖u_i - u_j‖ < 15 * L) :
    |t_i - t_j| ≤ 120 * L := by
  have hui_z_pos : 0 < u_i 2 := by linarith
  have huj_z_pos : 0 < u_j 2 := by linarith
  have h_coord_bound : ∀ (x : Point3), |x 2| ≤ ‖x‖ := by
    intro x
    have h1 : (x 2)^2 ≤ ‖x‖^2 := by
      rw [point3_norm_sq x] <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have h2 : 0 ≤ |x 2| := by positivity
    have h3 : 0 ≤ ‖x‖ := by positivity
    by_contra h4
    have h5 : |x 2| > ‖x‖ := by linarith
    have h6 : |x 2|^2 > ‖x‖^2 := by nlinarith
    have h7 : |x 2|^2 = (x 2)^2 := by simp [sq_abs]
    rw [h7] at h6; linarith
  have h_dir_diff2 : ‖u_j - u_i‖ ≤ 15 * L := by
    have h : ‖u_j - u_i‖ = ‖u_i - u_j‖ := by rw [norm_sub_rev]
    rw [h]; linarith [h_dir_diff]
  have hti : t_i = q_i 2 / (u_i 2) := by
    rw [hti_z] <;> field_simp [hui_z_pos.ne'] <;> ring
  have htj : t_j = q_j 2 / (u_j 2) := by
    rw [htj_z] <;> field_simp [huj_z_pos.ne'] <;> ring
  have h_abs : |q_i 2 * (u_j 2) - q_j 2 * (u_i 2)| ≤
      |q_i 2 - q_j 2| * |u_j 2| + |q_j 2| * |u_j 2 - u_i 2| := by
    have h : q_i 2 * (u_j 2) - q_j 2 * (u_i 2) =
        (q_i 2 - q_j 2) * (u_j 2) + q_j 2 * ((u_j 2) - (u_i 2)) := by ring
    rw [h]
    have h2 : |(q_i 2 - q_j 2) * (u_j 2) + q_j 2 * ((u_j 2) - (u_i 2))| ≤
        |(q_i 2 - q_j 2) * (u_j 2)| + |q_j 2 * ((u_j 2) - (u_i 2))| := by
      exact abs_add_le _ _
    have h3 : |(q_i 2 - q_j 2) * (u_j 2)| = |q_i 2 - q_j 2| * |u_j 2| := by rw [abs_mul]
    have h4 : |q_j 2 * ((u_j 2) - (u_i 2))| = |q_j 2| * |u_j 2 - u_i 2| := by rw [abs_mul]
    rw [h3, h4] at h2; exact h2
  have h1 : |q_i 2 - q_j 2| ≤ ‖q_i - q_j‖ := h_coord_bound (q_i - q_j)
  have h2 : |u_j 2| ≤ 1 := by
    have h3 : |u_j 2| ≤ ‖u_j‖ := h_coord_bound u_j
    rw [huj_norm] at h3; exact h3
  have h3 : |q_j 2| ≤ 1 + 7 * L := hqj_z_bound
  have h4 : |u_j 2 - u_i 2| ≤ ‖u_j - u_i‖ := h_coord_bound (u_j - u_i)
  have h5 : |q_i 2 * (u_j 2) - q_j 2 * (u_i 2)| ≤
      14 * L + (1 + 7 * L) * (15 * L) := by
    calc
      |q_i 2 * (u_j 2) - q_j 2 * (u_i 2)|
        ≤ |q_i 2 - q_j 2| * |u_j 2| + |q_j 2| * |u_j 2 - u_i 2| := h_abs
      _ ≤ ‖q_i - q_j‖ * 1 + (1 + 7 * L) * ‖u_j - u_i‖ := by gcongr <;> linarith
      _ ≤ 14 * L + (1 + 7 * L) * (15 * L) := by
        have h6 : ‖q_i - q_j‖ ≤ 14 * L := h_q_diff
        have h7 : ‖u_j - u_i‖ ≤ 15 * L := h_dir_diff2
        have h8 : (1 + 7 * L) * ‖u_j - u_i‖ ≤ (1 + 7 * L) * (15 * L) := by gcongr
        linarith
  have h_pos1 : 0 < (u_i 2) * (u_j 2) := by positivity
  have h_abs_den : |(u_i 2) * (u_j 2)| = (u_i 2) * (u_j 2) := by
    rw [abs_of_pos h_pos1]
  have h_div : |q_i 2 / (u_i 2) - q_j 2 / (u_j 2)| =
      |q_i 2 * (u_j 2) - q_j 2 * (u_i 2)| / ((u_i 2) * (u_j 2)) := by
    have h_eq : q_i 2 / (u_i 2) - q_j 2 / (u_j 2) =
        (q_i 2 * (u_j 2) - q_j 2 * (u_i 2)) / ((u_i 2) * (u_j 2)) := by
      field_simp [hui_z_pos.ne', huj_z_pos.ne'] <;> ring
    rw [h_eq, abs_div, h_abs_den] <;> rfl
  have h6 : |t_i - t_j| ≤
      (14 * L + (1 + 7 * L) * (15 * L)) / ((u_i 2) * (u_j 2)) := by
    rw [hti, htj, h_div]
    gcongr
  have h7 : 1 / ((u_i 2) * (u_j 2)) ≤ 4 := by
    have h8 : (u_i 2) * (u_j 2) ≥ 1 / 4 := by
      have h_i : u_i 2 ≥ 1 / 2 := hui_z
      have h_j : u_j 2 ≥ 1 / 2 := huj_z
      have h_pos : 0 ≤ u_i 2 := by linarith
      calc (u_i 2) * (u_j 2)
          ≥ (1 / 2 : ℝ) * (u_j 2) := by gcongr
        _ ≥ (1 / 2 : ℝ) * (1 / 2 : ℝ) := by gcongr
        _ = 1 / 4 := by norm_num
    have h9 : 0 < (u_i 2) * (u_j 2) := by positivity
    calc 1 / ((u_i 2) * (u_j 2)) ≤ 1 / (1 / 4 : ℝ) := by gcongr
      _ = 4 := by norm_num
  have h10 : 420 * L^2 ≤ 4 * L := by
    have h11 : L^2 ≤ (1 / 10000 : ℝ) * L := by
      have h12 : 0 ≤ L := by linarith
      have h13 : L ≤ 1 / 10000 := hL_small
      calc L^2 = L * L := by ring
        _ ≤ L * (1 / 10000 : ℝ) := by gcongr
        _ = (1 / 10000 : ℝ) * L := by ring
    calc 420 * L^2 ≤ 420 * ((1 / 10000 : ℝ) * L) := by gcongr
      _ = (420 / 10000 : ℝ) * L := by ring
      _ ≤ 4 * L := by
        have h14 : (420 / 10000 : ℝ) ≤ 4 := by norm_num
        have h15 : 0 ≤ L := by linarith
        exact mul_le_mul_of_nonneg_right h14 h15
  calc |t_i - t_j|
    ≤ (14 * L + (1 + 7 * L) * (15 * L)) / ((u_i 2) * (u_j 2)) := h6
  _ = (14 * L + (1 + 7 * L) * (15 * L)) * (1 / ((u_i 2) * (u_j 2))) := by ring
  _ ≤ (14 * L + (1 + 7 * L) * (15 * L)) * 4 := by gcongr
  _ = 4 * (14 * L + 15 * L + 105 * L^2) := by ring
  _ = 116 * L + 420 * L^2 := by ring
  _ ≤ 116 * L + 4 * L := by gcongr
  _ = 120 * L := by ring

/--
Bound the distance between axis zero-points given nearby axis points
and close directions.
-/
lemma paper_zero_point_distance_bound {L : ℝ} (hL_pos : 0 < L)
    (u_i u_j : Point3) (t_i t_j : ℝ)
    (zp_i zp_j q_i q_j : Point3)
    (hqi_eq : q_i = zp_i + t_i • u_i)
    (hqj_eq : q_j = zp_j + t_j • u_j)
    (huj_norm : ‖u_j‖ = 1)
    (h_q_diff : ‖q_i - q_j‖ ≤ 14 * L)
    (hti_bound : |t_i| ≤ 3)
    (h_dir_diff : ‖u_i - u_j‖ < 15 * L)
    (h_t_diff : |t_i - t_j| ≤ 120 * L) :
    ‖zp_i - zp_j‖ ≤ 180 * L := by
  have hqi' : q_i - t_i • u_i = zp_i := by
    rw [hqi_eq] <;> simp
  have hqj' : q_j - t_j • u_j = zp_j := by
    rw [hqj_eq] <;> simp
  have h_eq : zp_i - zp_j =
      (q_i - q_j) - t_i • (u_i - u_j) - (t_i - t_j) • u_j := by
    have h3 : zp_i - zp_j = (q_i - t_i • u_i) - (q_j - t_j • u_j) := by
      rw [hqi', hqj']
    rw [h3]
    have h5 : t_i • (u_i - u_j) = t_i • u_i - t_i • u_j := smul_sub t_i u_i u_j
    have h6 : (t_i - t_j) • u_j = t_i • u_j - t_j • u_j := sub_smul t_i t_j u_j
    have h7 : (q_i - t_i • u_i) - (q_j - t_j • u_j) =
        (q_i - q_j) - (t_i • u_i - t_i • u_j) - (t_i • u_j - t_j • u_j) := by
      simp [sub_eq_add_neg] <;> abel
    rw [h7, h5, h6]
  rw [h_eq]
  have h1 : ‖(q_i - q_j) - t_i • (u_i - u_j) - (t_i - t_j) • u_j‖ ≤
      ‖q_i - q_j‖ + ‖t_i • (u_i - u_j)‖ + ‖(t_i - t_j) • u_j‖ := by
    have h_a : ‖((q_i - q_j) - t_i • (u_i - u_j)) - (t_i - t_j) • u_j‖ ≤
        ‖(q_i - q_j) - t_i • (u_i - u_j)‖ + ‖(t_i - t_j) • u_j‖ := norm_sub_le _ _
    have h_b : ‖(q_i - q_j) - t_i • (u_i - u_j)‖ ≤ ‖q_i - q_j‖ + ‖t_i • (u_i - u_j)‖ :=
      norm_sub_le _ _
    linarith
  have h2 : ‖t_i • (u_i - u_j)‖ = ‖t_i‖ * ‖u_i - u_j‖ := by rw [norm_smul]
  have h3 : ‖(t_i - t_j) • u_j‖ = ‖t_i - t_j‖ * ‖u_j‖ := by rw [norm_smul]
  have h_abs_ti : ‖t_i‖ = |t_i| := by exact Real.norm_eq_abs t_i
  have h_abs_tij : ‖t_i - t_j‖ = |t_i - t_j| := by
    exact Real.norm_eq_abs (t_i - t_j)
  rw [h2, h3, h_abs_ti, h_abs_tij] at h1
  have h4 : ‖u_j‖ = 1 := huj_norm
  rw [h4] at h1
  have h6 : |t_i| * ‖u_i - u_j‖ ≤ 45 * L := by
    have h61 : |t_i| ≤ 3 := hti_bound
    have h62 : ‖u_i - u_j‖ < 15 * L := h_dir_diff
    have h63 : |t_i| * ‖u_i - u_j‖ ≤ 3 * ‖u_i - u_j‖ := by
      exact mul_le_mul_of_nonneg_right h61 (by positivity)
    have h64 : 3 * ‖u_i - u_j‖ < 45 * L := by
      have h65 : ‖u_i - u_j‖ < 15 * L := h62
      linarith
    linarith
  have h7 : |t_i - t_j| * (1 : ℝ) ≤ 120 * L := by
    simpa using h_t_diff
  have h5 : ‖q_i - q_j‖ + |t_i| * ‖u_i - u_j‖ + |t_i - t_j| * (1 : ℝ) ≤ 180 * L := by
    calc
      ‖q_i - q_j‖ + |t_i| * ‖u_i - u_j‖ + |t_i - t_j| * (1 : ℝ)
        ≤ 14 * L + 45 * L + 120 * L := by gcongr <;> linarith
      _ = 179 * L := by ring
      _ ≤ 180 * L := by
        have hL_nonneg : 0 ≤ L := by linarith [hL_pos]
        nlinarith
  exact h1.trans h5

/--
If two paper tubes both contain `p` and their directions have cross-product
norm `< 10*L`, then their paper line-distance is `≤ 500*L`.
-/
lemma paper_line_distance_shared_point
    {L : ℝ} (hL_pos : 0 < L) (hL_small : L ≤ 1 / 10000)
    {T_i T_j : Kakeya.DeltaTube L}
    (h_i_line : WZ1PaperTubeInLineClass T_i)
    (h_j_line : WZ1PaperTubeInLineClass T_j)
    (p : Point3)
    (hp_i : p ∈ wz1PaperTubeCarrier T_i)
    (hp_j : p ∈ wz1PaperTubeCarrier T_j)
    (h_cross : ‖wz1Cross T_i.direction T_j.direction‖ < 10 * L) :
    wz1PaperLineDistance T_j T_i ≤ 500 * L := by
  let u_i := wz1PaperDirection T_i
  let u_j := wz1PaperDirection T_j
  have hui_norm : ‖u_i‖ = 1 := wz1PaperDirection_norm T_i
  have huj_norm : ‖u_j‖ = 1 := wz1PaperDirection_norm T_j
  have hui_z : (1 / 2 : ℝ) ≤ u_i 2 := h_i_line.1
  have huj_z : (1 / 2 : ℝ) ≤ u_j 2 := h_j_line.1

  -- u_i = ±T_i.direction, u_j = ±T_j.direction
  have h1_i : u_i = T_i.direction ∨ u_i = -T_i.direction := by
    by_cases hsign : 0 ≤ T_i.direction (2 : Fin 3)
    · exact Or.inl (by simp [u_i, wz1PaperDirection, hsign])
    · exact Or.inr (by simp [u_i, wz1PaperDirection, hsign])
  have h1_j : u_j = T_j.direction ∨ u_j = -T_j.direction := by
    by_cases hsign : 0 ≤ T_j.direction (2 : Fin 3)
    · exact Or.inl (by simp [u_j, wz1PaperDirection, hsign])
    · exact Or.inr (by simp [u_j, wz1PaperDirection, hsign])

  -- Cross-product norm preserved under sign flips (via inner^2 invariance)
  have h_inner_same_sign : (inner ℝ u_i u_j)^2 = (inner ℝ T_i.direction T_j.direction)^2 := by
    rcases h1_i with (h1_i | h1_i) <;> rcases h1_j with (h1_j | h1_j) <;>
      rw [h1_i, h1_j] <;> simp [inner_neg_left, inner_neg_right] <;> ring
  have h_cross' : ‖wz1Cross u_i u_j‖ < 10 * L := by
    have h1 : ‖wz1Cross u_i u_j‖^2 = 1 - (inner ℝ u_i u_j)^2 :=
      cross_norm_sq u_i u_j hui_norm huj_norm
    have h2 : ‖wz1Cross T_i.direction T_j.direction‖^2 = 1 - (inner ℝ T_i.direction T_j.direction)^2 :=
      cross_norm_sq T_i.direction T_j.direction T_i.direction_unit T_j.direction_unit
    have h3 : ‖wz1Cross u_i u_j‖^2 = ‖wz1Cross T_i.direction T_j.direction‖^2 := by
      rw [h1, h2, h_inner_same_sign]
    have h4 : 0 ≤ ‖wz1Cross u_i u_j‖ := by positivity
    have h5 : 0 ≤ ‖wz1Cross T_i.direction T_j.direction‖ := by positivity
    have h6 : ‖wz1Cross u_i u_j‖ = ‖wz1Cross T_i.direction T_j.direction‖ := by nlinarith
    rw [h6]; exact h_cross

  -- inner^2 > 1 - 100*L^2
  have h_inner_sq : (inner ℝ u_i u_j)^2 > 1 - 100 * L^2 := by
    have h1 : ‖wz1Cross u_i u_j‖^2 = 1 - (inner ℝ u_i u_j)^2 :=
      cross_norm_sq u_i u_j hui_norm huj_norm
    have h2 : ‖wz1Cross u_i u_j‖^2 < (10 * L)^2 := by gcongr
    nlinarith

  -- inner ≥ -1/2 (via helper)
  have h_inner_lower : -(1 / 2 : ℝ) ≤ inner ℝ u_i u_j :=
    paper_inner_lower_bound hui_norm huj_norm hui_z huj_z

  -- inner > 1 - 100*L^2 (via helper)
  have h_inner_gt : inner ℝ u_i u_j > 1 - 100 * L^2 :=
    paper_inner_strict_lower hL_pos hL_small h_inner_sq h_inner_lower

  -- ‖u_i - u_j‖ < 15*L (via helper)
  have h_dir_diff : ‖u_i - u_j‖ < 15 * L :=
    paper_dir_diff_bound hL_pos hui_norm huj_norm h_inner_gt

  -- angle < 30*L (using π ≤ 4)
  have h_angle : InnerProductGeometry.angle u_i u_j < 30 * L := by
    have h1 : InnerProductGeometry.angle u_i u_j ≤ (Real.pi / 2) * ‖u_i - u_j‖ :=
      angle_le_pi2_mul_norm_sub hui_norm huj_norm
    have h2 : (Real.pi / 2) * ‖u_i - u_j‖ < (Real.pi / 2) * (15 * L) := by
      gcongr <;> linarith
    have h3 : Real.pi ≤ 4 := Real.pi_le_four
    have h4 : (Real.pi / 2) * (15 * L) ≤ 30 * L := by
      calc (Real.pi / 2) * (15 * L) ≤ (4 / 2 : ℝ) * (15 * L) := by gcongr <;> linarith
        _ = 30 * L := by ring
    linarith

  -- p ∈ axisBox gives |p 2| ≤ 1
  have hp_z : |p 2| ≤ 1 := by
    have h : |p 2| ≤ (2 / 2 : ℝ) := hp_i.2.2.2
    have h' : (2 / 2 : ℝ) = 1 := by norm_num
    rw [h'] at h; exact h

  -- Get q_i, q_j on axis lines within 7*L of p
  rcases point_on_line_within hL_pos hp_i.1 with ⟨q_i, hq_i_line, hq_i_lt⟩
  have hq_i_le : dist p q_i ≤ 7 * L := by linarith
  rcases point_on_line_within hL_pos hp_j.1 with ⟨q_j, hq_j_line, hq_j_lt⟩
  have hq_j_le : dist p q_j ≤ 7 * L := by linarith

  -- ‖q_i - q_j‖ ≤ 14*L
  have h_q_diff : ‖q_i - q_j‖ ≤ 14 * L := by
    have h_decomp : q_i - q_j = (q_i - p) + (p - q_j) := by abel
    rw [h_decomp]
    have h1 : ‖(q_i - p) + (p - q_j)‖ ≤ ‖q_i - p‖ + ‖p - q_j‖ := norm_add_le _ _
    have h2 : ‖q_i - p‖ = ‖p - q_i‖ := by rw [norm_sub_rev]
    have h3 : ‖p - q_i‖ = dist p q_i := by rw [dist_eq_norm]
    have h4 : ‖p - q_j‖ = dist p q_j := by rw [dist_eq_norm]
    have h_final : ‖(q_i - p) + (p - q_j)‖ ≤ 14 * L := by
      calc ‖(q_i - p) + (p - q_j)‖ ≤ ‖q_i - p‖ + ‖p - q_j‖ := norm_add_le _ _
        _ = ‖p - q_i‖ + ‖p - q_j‖ := by rw [norm_sub_rev]
        _ = dist p q_i + dist p q_j := by rw [dist_eq_norm, dist_eq_norm]
        _ ≤ 7 * L + 7 * L := by
          have h5 : dist p q_i ≤ 7 * L := hq_i_le
          have h6 : dist p q_j ≤ 7 * L := hq_j_le
          linarith
        _ = 14 * L := by ring
    exact h_final


  -- Use existing lemma to represent points on axis lines
  let zp_i := wz1TubeAxisZeroPoint T_i
  let zp_j := wz1TubeAxisZeroPoint T_j
  have hzp_i_z : zp_i 2 = 0 := wz1TubeAxisZeroPoint_coord_two T_i h_i_line.vertical
  have hzp_j_z : zp_j 2 = 0 := wz1TubeAxisZeroPoint_coord_two T_j h_j_line.vertical

  rcases wz1Paper_axis_exists_parameter h_i_line hq_i_line with ⟨t_i, hq_i_eq2⟩
  rcases wz1Paper_axis_exists_parameter h_j_line hq_j_line with ⟨t_j, hq_j_eq2⟩

  have hui_z_pos : 0 < u_i 2 := by linarith
  have huj_z_pos : 0 < u_j 2 := by linarith

  have hti_z : q_i 2 = t_i * (u_i 2) := by
    rw [hq_i_eq2]
    have h : (zp_i + t_i • u_i) 2 = zp_i 2 + t_i * (u_i 2) := by
      simp [Pi.add_apply, Pi.smul_apply] <;> ring
    rw [h, hzp_i_z] <;> ring
  have htj_z : q_j 2 = t_j * (u_j 2) := by
    rw [hq_j_eq2]
    have h : (zp_j + t_j • u_j) 2 = zp_j 2 + t_j * (u_j 2) := by
      simp [Pi.add_apply, Pi.smul_apply] <;> ring
    rw [h, hzp_j_z] <;> ring

  -- Coordinate bound helper
  have h_coord_bound : ∀ (x : Point3), |x 2| ≤ ‖x‖ := by
    intro x
    have h1 : (x 2)^2 ≤ ‖x‖^2 := by
      rw [point3_norm_sq x] <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have h2 : 0 ≤ |x 2| := by positivity
    have h3 : 0 ≤ ‖x‖ := by positivity
    by_contra h4
    have h5 : |x 2| > ‖x‖ := by linarith
    have h6 : |x 2|^2 > ‖x‖^2 := by nlinarith
    have h7 : |x 2|^2 = (x 2)^2 := by simp [sq_abs]
    rw [h7] at h6; linarith

  have hqi_z_bound : |q_i 2| ≤ 1 + 7 * L := by
    have h_coord : |q_i 2 - p 2| ≤ ‖q_i - p‖ := h_coord_bound (q_i - p)
    have h_abs : |q_i 2| ≤ |p 2| + |q_i 2 - p 2| := by
      calc |q_i 2| = |p 2 + (q_i 2 - p 2)| := by ring_nf
        _ ≤ |p 2| + |q_i 2 - p 2| := by
          exact abs_add_le _ _
    have h_norm : ‖q_i - p‖ = dist p q_i := by rw [norm_sub_rev, dist_eq_norm]
    calc |q_i 2| ≤ |p 2| + |q_i 2 - p 2| := h_abs
      _ ≤ 1 + ‖q_i - p‖ := by linarith [hp_z]
      _ = 1 + dist p q_i := by rw [h_norm]
      _ ≤ 1 + 7 * L := by
        have h5 : dist p q_i ≤ 7 * L := hq_i_le
        linarith

  have hqj_z_bound : |q_j 2| ≤ 1 + 7 * L := by
    have h_coord : |q_j 2 - p 2| ≤ ‖q_j - p‖ := h_coord_bound (q_j - p)
    have h_abs : |q_j 2| ≤ |p 2| + |q_j 2 - p 2| := by
      calc |q_j 2| = |p 2 + (q_j 2 - p 2)| := by ring_nf
        _ ≤ |p 2| + |q_j 2 - p 2| := by
          exact abs_add_le _ _
    have h_norm : ‖q_j - p‖ = dist p q_j := by rw [norm_sub_rev, dist_eq_norm]
    calc |q_j 2| ≤ |p 2| + |q_j 2 - p 2| := h_abs
      _ ≤ 1 + ‖q_j - p‖ := by linarith [hp_z]
      _ = 1 + dist p q_j := by rw [h_norm]
      _ ≤ 1 + 7 * L := by
        have h5 : dist p q_j ≤ 7 * L := hq_j_le
        linarith

  have hti_bound : |t_i| ≤ 3 := by
    have h_abs : |t_i| * (u_i 2) = |q_i 2| := by
      have h2 : |t_i| * (u_i 2) = |t_i * (u_i 2)| := by
        have h3 : |t_i * (u_i 2)| = |t_i| * |u_i 2| := by rw [abs_mul]
        have h4 : |u_i 2| = u_i 2 := by rw [abs_of_pos hui_z_pos]
        rw [h3, h4] <;> ring
      rw [h2, hti_z]
    have h : |t_i| * (u_i 2) ≤ 1 + 7 * L := by
      rw [h_abs]; exact hqi_z_bound
    have h2 : 0 < u_i 2 := hui_z_pos
    have h3 : |t_i| ≤ (1 + 7 * L) / (u_i 2) := by
      calc |t_i| = |t_i| * (u_i 2) / (u_i 2) := by field_simp [h2.ne'] <;> ring
        _ ≤ (1 + 7 * L) / (u_i 2) := by gcongr
    have h4 : (1 + 7 * L) / (u_i 2) ≤ 2 * (1 + 7 * L) := by
      have h5 : 1 / (u_i 2) ≤ 2 := by
        have h6 : u_i 2 ≥ 1 / 2 := hui_z
        calc 1 / (u_i 2) ≤ 1 / (1 / 2 : ℝ) := by gcongr
          _ = 2 := by norm_num
      calc (1 + 7 * L) / (u_i 2) = (1 + 7 * L) * (1 / (u_i 2)) := by ring
        _ ≤ (1 + 7 * L) * 2 := by gcongr
        _ = 2 * (1 + 7 * L) := by ring
    linarith [hL_small]

  have htj_bound : |t_j| ≤ 3 := by
    have h_abs : |t_j| * (u_j 2) = |q_j 2| := by
      have h2 : |t_j| * (u_j 2) = |t_j * (u_j 2)| := by
        have h3 : |t_j * (u_j 2)| = |t_j| * |u_j 2| := by rw [abs_mul]
        have h4 : |u_j 2| = u_j 2 := by rw [abs_of_pos huj_z_pos]
        rw [h3, h4] <;> ring
      rw [h2, htj_z]
    have h : |t_j| * (u_j 2) ≤ 1 + 7 * L := by
      rw [h_abs]; exact hqj_z_bound
    have h2 : 0 < u_j 2 := huj_z_pos
    have h3 : |t_j| ≤ (1 + 7 * L) / (u_j 2) := by
      calc |t_j| = |t_j| * (u_j 2) / (u_j 2) := by field_simp [h2.ne'] <;> ring
        _ ≤ (1 + 7 * L) / (u_j 2) := by gcongr
    have h4 : (1 + 7 * L) / (u_j 2) ≤ 2 * (1 + 7 * L) := by
      have h5 : 1 / (u_j 2) ≤ 2 := by
        have h6 : u_j 2 ≥ 1 / 2 := huj_z
        calc 1 / (u_j 2) ≤ 1 / (1 / 2 : ℝ) := by gcongr
          _ = 2 := by norm_num
      calc (1 + 7 * L) / (u_j 2) = (1 + 7 * L) * (1 / (u_j 2)) := by ring
        _ ≤ (1 + 7 * L) * 2 := by gcongr
        _ = 2 * (1 + 7 * L) := by ring
    linarith [hL_small]

  -- Bound |t_i - t_j|
  have h_t_diff : |t_i - t_j| ≤ 120 * L :=
    paper_parameter_diff_bound hL_pos hL_small u_i u_j t_i t_j q_i q_j
      hui_z huj_z hui_norm huj_norm hti_z htj_z h_q_diff hqi_z_bound hqj_z_bound h_dir_diff

  -- Bound ‖zp_i - zp_j‖
  have h_zp_diff : ‖zp_i - zp_j‖ ≤ 180 * L :=
    paper_zero_point_distance_bound hL_pos u_i u_j t_i t_j zp_i zp_j q_i q_j
      hq_i_eq2 hq_j_eq2 huj_norm h_q_diff hti_bound h_dir_diff h_t_diff

  -- Total line distance ≤ 180*L + 30*L = 210*L ≤ 500*L
  have h_main : wz1PaperLineDistance T_j T_i ≤ 210 * L := by
    dsimp only [wz1PaperLineDistance]
    have h_dist : dist zp_j zp_i ≤ 180 * L := by
      have h : dist zp_j zp_i = ‖zp_j - zp_i‖ := by rw [dist_eq_norm]
      rw [h]
      have h2 : ‖zp_j - zp_i‖ = ‖zp_i - zp_j‖ := by rw [norm_sub_rev]
      rw [h2]
      exact h_zp_diff
    have h_ang : InnerProductGeometry.angle u_j u_i < 30 * L := by
      rw [InnerProductGeometry.angle_comm]; exact h_angle
    have h_ang_le : InnerProductGeometry.angle u_j u_i ≤ 30 * L := by linarith
    have h_sum : dist zp_j zp_i + InnerProductGeometry.angle u_j u_i ≤ 180 * L + 30 * L :=
      add_le_add h_dist h_ang_le
    have h_eq : 180 * L + 30 * L = 210 * L := by ring
    rw [h_eq] at h_sum
    exact h_sum
  have h_final : 210 * L ≤ 500 * L := by
    have h : 0 ≤ L := by linarith
    linarith
  exact h_main.trans h_final

end Kakeya.Assouad

end
