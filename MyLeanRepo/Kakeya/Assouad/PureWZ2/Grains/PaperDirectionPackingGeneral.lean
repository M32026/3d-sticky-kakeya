import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperDirectionPacking
import Mathlib.Tactic

/-!
# Generalized direction packing for paper tube shadings

Generalizes `paper_line_distance_shared_point` from threshold `10*L`
to arbitrary `K*L`, with line-distance bound `100*K*L`.

## Key lemma

`paper_line_distance_shared_point_general`: if two paper tubes both
contain `p` and their directions have cross-product norm `< K*L`, then
their paper line-distance is `≤ 100*K*L`.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set InnerProductGeometry

attribute [local instance] Classical.propDecidable

/--
Generalized strict inner-product lower bound.

Given `x^2 > 1 - y^2`, `x ≥ -1/2`, `0 < y ≤ 1/2`, prove `x > 1 - y^2`.
-/
lemma paper_inner_strict_lower_general {y x : ℝ}
    (hy_pos : 0 < y) (hy_small : y ≤ 1 / 2)
    (h_sq : x^2 > 1 - y^2) (h_lower : -(1 / 2 : ℝ) ≤ x) :
    x > 1 - y^2 := by
  have h9 : 1 - y^2 > 1 / 4 := by
    have h10 : y^2 ≤ (1 / 2 : ℝ)^2 := by gcongr
    nlinarith
  have h10 : x^2 > 1 / 4 := by linarith
  have h_pos : 0 < x := by
    by_cases h : 0 < x
    · exact h
    · have h_nonpos : x ≤ 0 := by linarith
      have h3' : 0 ≤ -x := by linarith
      have h3 : -x ≤ 1 / 2 := by linarith
      have h4 : (-x)^2 ≤ (1 / 2 : ℝ)^2 := by gcongr
      have h4' : (-x)^2 ≤ 1 / 4 := by
        have h_eq : (1 / 2 : ℝ)^2 = 1 / 4 := by norm_num
        rw [h_eq] at h4; exact h4
      have h5 : x^2 = (-x)^2 := by ring
      have h6 : x^2 ≤ 1 / 4 := by rw [h5]; exact h4'
      linarith
  have h9' : 0 < 1 - y^2 := by linarith
  have h10' : (1 - y^2)^2 < 1 - y^2 := by
    have h11 : 0 < y^2 := by positivity
    have h12 : (1 - y^2) - (1 - y^2)^2 = (1 - y^2) * y^2 := by ring
    have h13 : (1 - y^2) * y^2 > 0 := by positivity
    linarith
  have h11 : x^2 > (1 - y^2)^2 := by
    calc x^2 > 1 - y^2 := h_sq
         _ > (1 - y^2)^2 := h10'
  have h12 : 0 ≤ x := by linarith
  have h13 : 0 ≤ 1 - y^2 := by linarith
  by_contra h14
  have h15 : x ≤ 1 - y^2 := by linarith
  have h17 : 0 ≤ (1 - y^2) - x := by linarith
  have h18 : 0 ≤ (1 - y^2) + x := by linarith
  have h19 : 0 ≤ ((1 - y^2) - x) * ((1 - y^2) + x) := by positivity
  have h20 : (1 - y^2)^2 - x^2 = ((1 - y^2) - x) * ((1 - y^2) + x) := by ring
  have h21 : (1 - y^2)^2 - x^2 ≥ 0 := by linarith [h19, h20]
  linarith [h11]

/--
Generalized direction difference bound.

Given `inner > 1 - y^2` for unit vectors, prove `‖u - v‖ < 2*y`.
-/
lemma paper_dir_diff_bound_general {y : ℝ} (hy_pos : 0 < y)
    {u v : Point3} (hu_norm : ‖u‖ = 1) (hv_norm : ‖v‖ = 1)
    (h_inner_gt : inner ℝ u v > 1 - y^2) :
    ‖u - v‖ < 2 * y := by
  have h4 : ‖u - v‖^2 = 2 - 2 * inner ℝ u v := by
    rw [norm_sub_sq_real, hu_norm, hv_norm] <;> ring
  have h6 : ‖u - v‖^2 < 2 * y^2 := by
    rw [h4]; linarith [h_inner_gt]
  have h7 : 0 ≤ ‖u - v‖ := by positivity
  have h8 : 2 * y^2 < (2 * y)^2 := by
    have h9 : 0 < y := hy_pos
    nlinarith
  have h10 : ‖u - v‖^2 < (2 * y)^2 := lt_trans h6 h8
  have h11 : 0 ≤ 2 * y := by positivity
  have h13 : (2 * y)^2 - ‖u - v‖^2 > 0 := by linarith
  have h14 : (2 * y - ‖u - v‖) * (2 * y + ‖u - v‖) > 0 := by
    have h15 : (2 * y)^2 - ‖u - v‖^2 =
        (2 * y - ‖u - v‖) * (2 * y + ‖u - v‖) := by ring
    rw [← h15]; exact h13
  have h16 : 0 < 2 * y + ‖u - v‖ := by positivity
  have h17 : 0 < 2 * y - ‖u - v‖ := by
    exact (mul_pos_iff_of_pos_right h16).mp h14
  linarith

/--
Generalized parameter difference bound.

Given axis points q_i, q_j with `‖q_i - q_j‖ ≤ 14*L`, directions with
`‖u_i - u_j‖ < 2*y`, and `L ≤ y`, `L ≤ 1/10000`,
prove `|t_i - t_j| ≤ 72*y`.
-/
lemma paper_parameter_diff_bound_general {L y : ℝ}
    (hL_pos : 0 < L) (hL_small : L ≤ 1 / 10000)
    (hL_le_y : L ≤ y) (hy_pos : 0 < y)
    (u_i u_j : Point3) (t_i t_j : ℝ) (q_i q_j : Point3)
    (hui_z : (1 / 2 : ℝ) ≤ u_i 2)
    (huj_z : (1 / 2 : ℝ) ≤ u_j 2)
    (hui_norm : ‖u_i‖ = 1)
    (huj_norm : ‖u_j‖ = 1)
    (hti_z : q_i 2 = t_i * (u_i 2))
    (htj_z : q_j 2 = t_j * (u_j 2))
    (h_q_diff : ‖q_i - q_j‖ ≤ 14 * L)
    (hqi_z_bound : |q_i 2| ≤ 1 + 7 * L)
    (hqj_z_bound : |q_j 2| ≤ 1 + 7 * L)
    (h_dir_diff : ‖u_i - u_j‖ < 2 * y) :
    |t_i - t_j| ≤ 72 * y := by
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
  have h_dir_diff2 : ‖u_j - u_i‖ ≤ 2 * y := by
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
      14 * L + (1 + 7 * L) * (2 * y) := by
    calc
      |q_i 2 * (u_j 2) - q_j 2 * (u_i 2)|
        ≤ |q_i 2 - q_j 2| * |u_j 2| + |q_j 2| * |u_j 2 - u_i 2| := h_abs
      _ ≤ ‖q_i - q_j‖ * 1 + (1 + 7 * L) * ‖u_j - u_i‖ := by gcongr <;> linarith
      _ ≤ 14 * L + (1 + 7 * L) * (2 * y) := by
        have h6 : ‖q_i - q_j‖ ≤ 14 * L := h_q_diff
        have h7 : ‖u_j - u_i‖ ≤ 2 * y := h_dir_diff2
        have h8 : (1 + 7 * L) * ‖u_j - u_i‖ ≤ (1 + 7 * L) * (2 * y) := by gcongr
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
      (14 * L + (1 + 7 * L) * (2 * y)) / ((u_i 2) * (u_j 2)) := by
    rw [hti, htj, h_div]; gcongr
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
  have hLy_le_y : 56 * L * y ≤ y := by
    have h19 : 56 * L ≤ 1 := by
      have h20 : 56 * L ≤ 56 * (1 / 10000 : ℝ) := mul_le_mul_of_nonneg_left hL_small (by norm_num)
      have h21 : 56 * (1 / 10000 : ℝ) ≤ 1 := by norm_num
      exact h20.trans h21
    have h22 : 0 ≤ y := by linarith
    calc 56 * L * y ≤ 1 * y := by gcongr
      _ = y := by ring
  have h_step1 : |t_i - t_j| ≤ 56 * L + 8 * y + 56 * L * y := by
    calc |t_i - t_j|
      ≤ (14 * L + (1 + 7 * L) * (2 * y)) / ((u_i 2) * (u_j 2)) := h6
    _ = (14 * L + (1 + 7 * L) * (2 * y)) * (1 / ((u_i 2) * (u_j 2))) := by ring
    _ ≤ (14 * L + (1 + 7 * L) * (2 * y)) * 4 := by gcongr
    _ = 4 * (14 * L + 2 * y + 14 * L * y) := by ring
    _ = 56 * L + 8 * y + 56 * L * y := by ring
  have h_step2 : 56 * L ≤ 56 * y := by
    exact mul_le_mul_of_nonneg_left hL_le_y (by norm_num)
  have h_step3 : 56 * L * y ≤ y := hLy_le_y
  have h_step4 : 56 * L + 8 * y + 56 * L * y ≤ 65 * y := by
    linarith
  have h_step5 : 65 * y ≤ 72 * y := by
    have h24 : 0 ≤ y := by linarith
    linarith
  exact h_step1.trans (h_step4.trans h_step5)

/--
Generalized zero-point distance bound.
-/
lemma paper_zero_point_distance_bound_general {L y : ℝ}
    (hL_pos : 0 < L) (hL_le_y : L ≤ y)
    (u_i u_j : Point3) (t_i t_j : ℝ)
    (zp_i zp_j q_i q_j : Point3)
    (hqi_eq : q_i = zp_i + t_i • u_i)
    (hqj_eq : q_j = zp_j + t_j • u_j)
    (huj_norm : ‖u_j‖ = 1)
    (h_q_diff : ‖q_i - q_j‖ ≤ 14 * L)
    (hti_bound : |t_i| ≤ 3)
    (h_dir_diff : ‖u_i - u_j‖ < 2 * y)
    (h_t_diff : |t_i - t_j| ≤ 72 * y) :
    ‖zp_i - zp_j‖ ≤ 92 * y := by
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
  have h2 : ‖t_i • (u_i - u_j)‖ = |t_i| * ‖u_i - u_j‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have h3 : ‖(t_i - t_j) • u_j‖ = |t_i - t_j| * ‖u_j‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  rw [h2, h3] at h1
  have h4 : ‖u_j‖ = 1 := huj_norm
  rw [h4] at h1
  have h6 : |t_i| * ‖u_i - u_j‖ ≤ 6 * y := by
    have h61 : |t_i| ≤ 3 := hti_bound
    have h62 : ‖u_i - u_j‖ < 2 * y := h_dir_diff
    have h63 : |t_i| * ‖u_i - u_j‖ ≤ 3 * ‖u_i - u_j‖ := by
      exact mul_le_mul_of_nonneg_right h61 (by positivity)
    have h64 : 3 * ‖u_i - u_j‖ < 6 * y := by linarith
    linarith
  have h7 : |t_i - t_j| * (1 : ℝ) ≤ 72 * y := by
    simpa using h_t_diff
  have h5 : ‖q_i - q_j‖ + |t_i| * ‖u_i - u_j‖ + |t_i - t_j| * (1 : ℝ) ≤ 92 * y := by
    calc
      ‖q_i - q_j‖ + |t_i| * ‖u_i - u_j‖ + |t_i - t_j| * (1 : ℝ)
        ≤ 14 * L + 6 * y + 72 * y := by gcongr <;> linarith
      _ = 14 * L + 78 * y := by ring
      _ ≤ 14 * y + 78 * y := by gcongr
      _ = 92 * y := by ring
  exact h1.trans h5

/--
Generalized paper line distance bound.

If two paper tubes both contain `p` and their directions have cross-product
norm `< K*L`, then their paper line-distance is `≤ 100*K*L`.
-/
lemma paper_line_distance_shared_point_general
    {L K : ℝ} (hL_pos : 0 < L) (hL_small : L ≤ 1 / 10000)
    (hK_one : 1 ≤ K) (hKL_small : K * L ≤ 1 / 2)
    {T_i T_j : Kakeya.DeltaTube L}
    (h_i_line : WZ1PaperTubeInLineClass T_i)
    (h_j_line : WZ1PaperTubeInLineClass T_j)
    (p : Point3)
    (hp_i : p ∈ wz1PaperTubeCarrier T_i)
    (hp_j : p ∈ wz1PaperTubeCarrier T_j)
    (h_cross : ‖wz1Cross T_i.direction T_j.direction‖ < K * L) :
    wz1PaperLineDistance T_j T_i ≤ 100 * K * L := by
  let y := K * L
  have hy_pos : 0 < y := by
    have hK_pos : 0 < K := by linarith
    positivity
  have hy_small : y ≤ 1 / 2 := hKL_small
  have hL_le_y : L ≤ y := by
    have h18 : 0 ≤ L := by linarith
    nlinarith [hK_one]
  let u_i := wz1PaperDirection T_i
  let u_j := wz1PaperDirection T_j
  have hui_norm : ‖u_i‖ = 1 := wz1PaperDirection_norm T_i
  have huj_norm : ‖u_j‖ = 1 := wz1PaperDirection_norm T_j
  have hui_z : (1 / 2 : ℝ) ≤ u_i 2 := h_i_line.1
  have huj_z : (1 / 2 : ℝ) ≤ u_j 2 := h_j_line.1

  have h1_i : u_i = T_i.direction ∨ u_i = -T_i.direction := by
    by_cases h : 0 ≤ T_i.direction (2 : Fin 3)
    · have h' : u_i = T_i.direction := by
        simp [u_i, wz1PaperDirection, h]
      exact Or.inl h'
    · have h' : u_i = -T_i.direction := by
        simp [u_i, wz1PaperDirection, h]
      exact Or.inr h'
  have h1_j : u_j = T_j.direction ∨ u_j = -T_j.direction := by
    by_cases h : 0 ≤ T_j.direction (2 : Fin 3)
    · have h' : u_j = T_j.direction := by
        simp [u_j, wz1PaperDirection, h]
      exact Or.inl h'
    · have h' : u_j = -T_j.direction := by
        simp [u_j, wz1PaperDirection, h]
      exact Or.inr h'

  have h_inner_sq : (inner ℝ u_i u_j)^2 > 1 - y^2 := by
    have h_inner_same : (inner ℝ u_i u_j)^2 = (inner ℝ T_i.direction T_j.direction)^2 := by
      rcases h1_i with (h1_i | h1_i) <;> rcases h1_j with (h1_j | h1_j) <;>
        rw [h1_i, h1_j] <;> simp [inner_neg_left, inner_neg_right] <;> ring
    have h1 : ‖wz1Cross T_i.direction T_j.direction‖^2 =
        1 - (inner ℝ T_i.direction T_j.direction)^2 :=
      cross_norm_sq T_i.direction T_j.direction
        T_i.direction_unit T_j.direction_unit
    have h2 : ‖wz1Cross T_i.direction T_j.direction‖^2 < y^2 := by gcongr
    have h4 : 1 - (inner ℝ T_i.direction T_j.direction)^2 < y^2 := by
      rw [h1] at *; exact h2
    have h5 : (inner ℝ T_i.direction T_j.direction)^2 > 1 - y^2 := by linarith
    rw [h_inner_same]; exact h5

  have h_inner_lower : -(1 / 2 : ℝ) ≤ inner ℝ u_i u_j :=
    paper_inner_lower_bound hui_norm huj_norm hui_z huj_z

  have h_inner_gt : inner ℝ u_i u_j > 1 - y^2 :=
    paper_inner_strict_lower_general hy_pos hy_small h_inner_sq h_inner_lower

  have h_dir_diff : ‖u_i - u_j‖ < 2 * y :=
    paper_dir_diff_bound_general hy_pos hui_norm huj_norm h_inner_gt

  have h_angle : InnerProductGeometry.angle u_i u_j < 4 * y := by
    have h1 : InnerProductGeometry.angle u_i u_j ≤ (Real.pi / 2) * ‖u_i - u_j‖ :=
      angle_le_pi2_mul_norm_sub hui_norm huj_norm
    have h2 : (Real.pi / 2) * ‖u_i - u_j‖ < (Real.pi / 2) * (2 * y) := by
      gcongr <;> linarith
    have h3 : Real.pi ≤ 4 := Real.pi_le_four
    have h4 : (Real.pi / 2) * (2 * y) ≤ 4 * y := by
      calc (Real.pi / 2) * (2 * y) ≤ (4 / 2 : ℝ) * (2 * y) := by gcongr <;> linarith
        _ = 4 * y := by ring
    linarith

  have hp_z : |p 2| ≤ 1 := by
    have h : |p 2| ≤ (2 / 2 : ℝ) := hp_i.2.2.2
    have h' : (2 / 2 : ℝ) = 1 := by norm_num
    rw [h'] at h; exact h

  rcases point_on_line_within hL_pos hp_i.1 with ⟨q_i, hq_i_line, hq_i_lt⟩
  have hq_i_le : dist p q_i ≤ 7 * L := by linarith
  rcases point_on_line_within hL_pos hp_j.1 with ⟨q_j, hq_j_line, hq_j_lt⟩
  have hq_j_le : dist p q_j ≤ 7 * L := by linarith

  have h_q_diff : ‖q_i - q_j‖ ≤ 14 * L := by
    have h_decomp : q_i - q_j = (q_i - p) + (p - q_j) := by abel
    rw [h_decomp]
    have h_final : ‖(q_i - p) + (p - q_j)‖ ≤ 14 * L := by
      calc ‖(q_i - p) + (p - q_j)‖
        ≤ ‖q_i - p‖ + ‖p - q_j‖ := norm_add_le _ _
      _ = ‖p - q_i‖ + ‖p - q_j‖ := by rw [norm_sub_rev]
      _ = dist p q_i + dist p q_j := by rw [dist_eq_norm, dist_eq_norm]
      _ ≤ 7 * L + 7 * L := by
        have h5 : dist p q_i ≤ 7 * L := hq_i_le
        have h6 : dist p q_j ≤ 7 * L := hq_j_le
        linarith
      _ = 14 * L := by ring
    exact h_final

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
        _ ≤ |p 2| + |q_i 2 - p 2| := abs_add_le _ _
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
        _ ≤ |p 2| + |q_j 2 - p 2| := abs_add_le _ _
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

  have h_t_diff : |t_i - t_j| ≤ 72 * y :=
    paper_parameter_diff_bound_general hL_pos hL_small hL_le_y hy_pos
      u_i u_j t_i t_j q_i q_j
      hui_z huj_z hui_norm huj_norm hti_z htj_z
      h_q_diff hqi_z_bound hqj_z_bound h_dir_diff

  have h_zp_diff : ‖zp_i - zp_j‖ ≤ 92 * y :=
    paper_zero_point_distance_bound_general hL_pos hL_le_y
      u_i u_j t_i t_j zp_i zp_j q_i q_j
      hq_i_eq2 hq_j_eq2 huj_norm h_q_diff hti_bound h_dir_diff h_t_diff

  have h_main : wz1PaperLineDistance T_j T_i ≤ 96 * y := by
    dsimp only [wz1PaperLineDistance]
    have h_dist : dist zp_j zp_i ≤ 92 * y := by
      have h : dist zp_j zp_i = ‖zp_j - zp_i‖ := by rw [dist_eq_norm]
      rw [h]
      have h2 : ‖zp_j - zp_i‖ = ‖zp_i - zp_j‖ := by rw [norm_sub_rev]
      rw [h2]; exact h_zp_diff
    have h_ang : InnerProductGeometry.angle u_j u_i < 4 * y := by
      rw [InnerProductGeometry.angle_comm]; exact h_angle
    have h_ang_le : InnerProductGeometry.angle u_j u_i ≤ 4 * y := by linarith
    have h_sum : dist zp_j zp_i + InnerProductGeometry.angle u_j u_i ≤ 92 * y + 4 * y :=
      add_le_add h_dist h_ang_le
    have h_eq : 92 * y + 4 * y = 96 * y := by ring
    rw [h_eq] at h_sum; exact h_sum
  have h_final : 96 * y ≤ 100 * K * L := by
    have h : 0 ≤ y := by linarith
    have h' : (100 * y : ℝ) = 100 * K * L := by
      simp [y] <;> ring
    linarith
  exact h_main.trans h_final

end Kakeya.Assouad

end
