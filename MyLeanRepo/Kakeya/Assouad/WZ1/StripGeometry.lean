import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.NonConcentrationToThinTubes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

/-!
# Strip intersection geometry

Two planar strips of width `r` whose unit normals are separated by `θ`
intersect inside a ball of radius `6r / θ`.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- The scalar two-dimensional cross product. -/
def cross2 (v w : Point2) : ℝ :=
  v 0 * w 1 - v 1 * w 0

/-- Coordinate expansion of the planar inner product. -/
lemma inner2_eq (v w : Point2) :
    inner ℝ v w = v 0 * w 0 + v 1 * w 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two] <;> ring

/-- Coordinate expansion of the squared planar norm. -/
lemma norm2_sq (v : Point2) :
    ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
  have h : inner ℝ v v = ‖v‖ ^ 2 :=
    real_inner_self_eq_norm_sq v
  have h2 : inner ℝ v v = v 0 * v 0 + v 1 * v 1 :=
    inner2_eq v v
  linarith

/-- Pythagorean decomposition into a unit normal and its planar cross term. -/
lemma norm_cross_identity (v n : Point2) (hn : ‖n‖ = 1) :
    ‖v‖ ^ 2 =
      (inner ℝ v n) ^ 2 + (cross2 v n) ^ 2 := by
  have h_nsq : (n 0) ^ 2 + (n 1) ^ 2 = 1 := by
    have h := norm2_sq n
    rw [hn] at h
    have h' : ‖n‖ ^ 2 = 1 := by
      rw [hn]
      norm_num
    linarith
  have h_vsq :
      ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 :=
    norm2_sq v
  have h_inner :
      inner ℝ v n = v 0 * n 0 + v 1 * n 1 :=
    inner2_eq v n
  have h_cross :
      cross2 v n = v 0 * n 1 - v 1 * n 0 := by
    rfl
  rw [h_vsq, h_inner, h_cross]
  nlinarith [h_nsq]

/-- Rotation formula relative to one planar unit normal. -/
lemma inner_rotation
    (v n1 n2 : Point2) (hn1 : ‖n1‖ = 1) :
    inner ℝ v n2 =
      (inner ℝ v n1) * (inner ℝ n1 n2) -
        (cross2 v n1) * (cross2 n1 n2) := by
  have h_nsq : (n1 0) ^ 2 + (n1 1) ^ 2 = 1 := by
    have h := norm2_sq n1
    rw [hn1] at h
    have h' : ‖n1‖ ^ 2 = 1 := by
      rw [hn1]
      norm_num
    linarith
  have h_main :
      (v 0 * n1 0 + v 1 * n1 1) *
          (n1 0 * n2 0 + n1 1 * n2 1) -
        (v 0 * n1 1 - v 1 * n1 0) *
          (n1 0 * n2 1 - n1 1 * n2 0) =
      (v 0 * n2 0 + v 1 * n2 1) *
        ((n1 0) ^ 2 + (n1 1) ^ 2) := by
    ring
  have h_final :
      (v 0 * n2 0 + v 1 * n2 1) *
          ((n1 0) ^ 2 + (n1 1) ^ 2) =
        v 0 * n2 0 + v 1 * n2 1 := by
    rw [h_nsq]
    ring
  have h_goal :
      v 0 * n2 0 + v 1 * n2 1 =
        (v 0 * n1 0 + v 1 * n1 1) *
            (n1 0 * n2 0 + n1 1 * n2 1) -
          (v 0 * n1 1 - v 1 * n1 0) *
            (n1 0 * n2 1 - n1 1 * n2 0) :=
    (h_main.trans h_final).symm
  simpa [inner2_eq, cross2] using h_goal

/-- Squared distance between planar unit normals. -/
lemma unit_diff_sq
    (n1 n2 : Point2) (hn1 : ‖n1‖ = 1)
    (hn2 : ‖n2‖ = 1) :
    ‖n1 - n2‖ ^ 2 =
      2 - 2 * inner ℝ n1 n2 := by
  have h1 :
      ‖n1 - n2‖ ^ 2 =
        inner ℝ (n1 - n2) (n1 - n2) :=
    Eq.symm (real_inner_self_eq_norm_sq (n1 - n2))
  have h2 :
      inner ℝ (n1 - n2) (n1 - n2) =
        inner ℝ n1 n1 - 2 * inner ℝ n1 n2 +
          inner ℝ n2 n2 := by
    have h21 :
        inner ℝ (n1 - n2) (n1 - n2) =
          inner ℝ n1 (n1 - n2) -
            inner ℝ n2 (n1 - n2) := by
      rw [inner_sub_left]
    rw [h21]
    have h22 :
        inner ℝ n1 (n1 - n2) =
          inner ℝ n1 n1 - inner ℝ n1 n2 := by
      rw [inner_sub_right]
    have h23 :
        inner ℝ n2 (n1 - n2) =
          inner ℝ n2 n1 - inner ℝ n2 n2 := by
      rw [inner_sub_right]
    rw [h22, h23, real_inner_comm n2 n1]
    ring
  have h3 : inner ℝ n1 n1 = ‖n1‖ ^ 2 :=
    real_inner_self_eq_norm_sq n1
  have h4 : inner ℝ n2 n2 = ‖n2‖ ^ 2 :=
    real_inner_self_eq_norm_sq n2
  rw [h1, h2, h3, h4, hn1, hn2]
  ring_nf

/-- Real arithmetic used in the two-strip vector estimate. -/
lemma real_norm_bound
    {r θ x y : ℝ}
    (hr : 0 < r) (hθ : 0 < θ) (hθ_le_one : θ ≤ 1)
    (hx : |x| ≤ 2 * r)
    (hy : |y| ≤ 4 * r / (θ / Real.sqrt 2)) :
    x ^ 2 + y ^ 2 ≤ (6 * r / θ) ^ 2 := by
  have hθsq_pos : 0 < θ ^ 2 := by positivity
  have hθsq_le_one : θ ^ 2 ≤ 1 := by nlinarith
  have h_sqrt2_sq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have h_x2 : x ^ 2 ≤ 4 * r ^ 2 := by
    have hsq : |x| ^ 2 ≤ (2 * r) ^ 2 := by
      gcongr
    have h_abs_sq : |x| ^ 2 = x ^ 2 := by
      simp [sq_abs]
    rw [h_abs_sq] at hsq
    have h' : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
    rwa [h'] at hsq
  have h_y2 : y ^ 2 ≤ 32 * r ^ 2 / θ ^ 2 := by
    have hsq :
        |y| ^ 2 ≤
          (4 * r / (θ / Real.sqrt 2)) ^ 2 := by
      gcongr
    have h_abs_sq : |y| ^ 2 = y ^ 2 := by
      simp [sq_abs]
    rw [h_abs_sq] at hsq
    have hC_sq :
        (4 * r / (θ / Real.sqrt 2)) ^ 2 =
          32 * r ^ 2 / θ ^ 2 := by
      have hdiv :
          4 * r / (θ / Real.sqrt 2) =
            (4 * r) * Real.sqrt 2 / θ := by
        field_simp [hθ.ne']
      rw [hdiv]
      have h :
          ((4 * r) * Real.sqrt 2 / θ) ^ 2 =
            (4 * r) ^ 2 * (Real.sqrt 2) ^ 2 /
              θ ^ 2 := by
        field_simp [hθ.ne']
      rw [h, h_sqrt2_sq]
      ring
    rwa [hC_sq] at hsq
  have h2 : 4 * r ^ 2 ≤ 4 * r ^ 2 / θ ^ 2 := by
    calc
      4 * r ^ 2 =
          (4 * r ^ 2) * θ ^ 2 / θ ^ 2 := by
        field_simp [hθsq_pos.ne']
      _ ≤ (4 * r ^ 2) * 1 / θ ^ 2 := by
        gcongr
      _ = 4 * r ^ 2 / θ ^ 2 := by ring
  have h5 :
      (6 * r / θ) ^ 2 =
        36 * r ^ 2 / θ ^ 2 := by
    field_simp [hθsq_pos.ne']
    ring
  rw [h5]
  have h6 :
      x ^ 2 + y ^ 2 ≤
        4 * r ^ 2 + 32 * r ^ 2 / θ ^ 2 := by
    linarith
  have h7 :
      4 * r ^ 2 + 32 * r ^ 2 / θ ^ 2 ≤
        36 * r ^ 2 / θ ^ 2 := by
    have h9 :
        4 * r ^ 2 / θ ^ 2 +
            32 * r ^ 2 / θ ^ 2 =
          36 * r ^ 2 / θ ^ 2 := by
      field_simp [hθsq_pos.ne']
      ring
    linarith
  linarith

/-- Two transverse width-`r` strip constraints bound the displacement. -/
lemma two_strip_vector_bound
    {r θ : ℝ}
    (hr : 0 < r) (hθ : 0 < θ) (hθ_le_one : θ ≤ 1)
    (n1 n2 : Point2) (hn1 : ‖n1‖ = 1)
    (hn2 : ‖n2‖ = 1)
    (h_angle_lower : θ ≤ ‖n1 - n2‖)
    (h_angle_upper : ‖n1 - n2‖ ≤ Real.sqrt 2)
    (v : Point2)
    (hv1 : |inner ℝ v n1| ≤ 2 * r)
    (hv2 : |inner ℝ v n2| ≤ 2 * r) :
    ‖v‖ ≤ 6 * r / θ := by
  set x := inner ℝ v n1
  set y := cross2 v n1
  set a := inner ℝ n1 n2
  set b := cross2 n1 n2
  have h_rot :
      inner ℝ v n2 = x * a - y * b :=
    inner_rotation v n1 n2 hn1
  have h_ab1 : a ^ 2 + b ^ 2 = 1 := by
    have h :
        ‖n2‖ ^ 2 =
          (inner ℝ n2 n1) ^ 2 +
            (cross2 n2 n1) ^ 2 :=
      norm_cross_identity n2 n1 hn1
    have h_sym2 :
        cross2 n2 n1 = -cross2 n1 n2 := by
      simp [cross2]
      ring
    have h_sym1 :
        inner ℝ n2 n1 = inner ℝ n1 n2 :=
      (real_inner_comm n2 n1).symm
    rw [h_sym1, h_sym2] at h
    have h5 : ‖n2‖ ^ 2 = 1 := by
      rw [hn2]
      norm_num
    rw [h5] at h
    simp only [a, b] at *
    nlinarith
  have h_inner_def :
      a = 1 - ‖n1 - n2‖ ^ 2 / 2 := by
    have h := unit_diff_sq n1 n2 hn1 hn2
    simp only [a] at *
    linarith
  have h_nonneg : 0 ≤ a := by
    have h5 : ‖n1 - n2‖ ^ 2 ≤ 2 := by
      have h7 : 0 ≤ Real.sqrt 2 := by positivity
      nlinarith
        [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith
  have h_b_sq : b ^ 2 ≥ θ ^ 2 / 2 := by
    have h9 : a ≤ 1 - θ ^ 2 / 2 := by
      have h11 : θ ^ 2 ≤ ‖n1 - n2‖ ^ 2 := by
        nlinarith
      linarith
    have h13 : b ^ 2 = 1 - a ^ 2 := by
      linarith
    rw [h13]
    nlinarith
  have h_b_abs : |b| ≥ θ / Real.sqrt 2 := by
    have h14 : 0 < θ / Real.sqrt 2 := by positivity
    by_cases hb : 0 ≤ b
    · have h17 :
          (θ / Real.sqrt 2) ^ 2 = θ ^ 2 / 2 := by
        field_simp
        nlinarith
          [Real.sq_sqrt
            (show (0 : ℝ) ≤ 2 by norm_num)]
      have h16 : b ≥ θ / Real.sqrt 2 := by
        nlinarith
      rwa [abs_of_nonneg hb]
    · have hb' : b < 0 := by linarith
      have h17 :
          (θ / Real.sqrt 2) ^ 2 = θ ^ 2 / 2 := by
        field_simp
        nlinarith
          [Real.sq_sqrt
            (show (0 : ℝ) ≤ 2 by norm_num)]
      have h16 : b ≤ -(θ / Real.sqrt 2) := by
        nlinarith
      rw [abs_of_neg hb']
      linarith
  have h_a_abs : |a| ≤ 1 := by
    have h1 : a ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg b]
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have h_y_bound : |y * b| ≤ 4 * r := by
    have h1 : |x * a| ≤ 2 * r := by
      calc
        |x * a| = |x| * |a| := by rw [abs_mul]
        _ ≤ (2 * r) * 1 := by gcongr
        _ = 2 * r := by ring
    have h2 :
        |y * b| =
          |x * a - inner ℝ v n2| := by
      have h3 :
          y * b = x * a - inner ℝ v n2 := by
        rw [h_rot]
        ring
      rw [h3]
    rw [h2]
    have h4 :
        |x * a - inner ℝ v n2| ≤
          |x * a| + |inner ℝ v n2| :=
      abs_sub _ _
    linarith
  have h_bpos : 0 < |b| := by
    have hθsqrt : 0 < θ / Real.sqrt 2 := by
      positivity
    linarith
  have h_y_abs :
      |y| ≤ 4 * r / (θ / Real.sqrt 2) := by
    have h4 : |y| * |b| ≤ 4 * r := by
      rwa [abs_mul] at h_y_bound
    calc
      |y| = (|y| * |b|) / |b| := by
        field_simp [h_bpos.ne']
      _ ≤ (4 * r) / |b| := by gcongr
      _ ≤ (4 * r) / (θ / Real.sqrt 2) := by
        gcongr
  have h_norm :
      ‖v‖ ^ 2 = x ^ 2 + y ^ 2 :=
    norm_cross_identity v n1 hn1
  have h_main :
      x ^ 2 + y ^ 2 ≤ (6 * r / θ) ^ 2 :=
    real_norm_bound hr hθ hθ_le_one hv1 h_y_abs
  have h20 :
      ‖v‖ ^ 2 ≤ (6 * r / θ) ^ 2 := by
    rwa [h_norm]
  have h22 : 0 ≤ 6 * r / θ := by positivity
  nlinarith [norm_nonneg v]

/--
The intersection of two transverse strips is contained in a controlled ball
around any point satisfying both strip inequalities.
-/
lemma strip_intersection_subset_ball
    {r θ : ℝ}
    (hr : 0 < r) (hθ : 0 < θ) (hθ_le_one : θ ≤ 1)
    (n1 n2 : Point2) (hn1 : ‖n1‖ = 1)
    (hn2 : ‖n2‖ = 1)
    (h_angle_lower : θ ≤ ‖n1 - n2‖)
    (h_angle_upper : ‖n1 - n2‖ ≤ Real.sqrt 2)
    (b1 b2 c : Point2)
    (hc1 : |inner ℝ (c - b1) n1| ≤ r)
    (hc2 : |inner ℝ (c - b2) n2| ≤ r) :
    {p : Point2 |
        |inner ℝ (p - b1) n1| ≤ r ∧
          |inner ℝ (p - b2) n2| ≤ r} ⊆
      Metric.closedBall c (6 * r / θ) := by
  intro p hp
  set v := p - c
  have hv1 : |inner ℝ v n1| ≤ 2 * r := by
    have h_eq :
        inner ℝ v n1 =
          inner ℝ (p - b1) n1 -
            inner ℝ (c - b1) n1 := by
      simp [v, inner_sub_left]
    rw [h_eq]
    have h_abs :
        |inner ℝ (p - b1) n1 -
            inner ℝ (c - b1) n1| ≤
          |inner ℝ (p - b1) n1| +
            |inner ℝ (c - b1) n1| :=
      abs_sub _ _
    exact h_abs.trans (by linarith [hp.1, hc1])
  have hv2 : |inner ℝ v n2| ≤ 2 * r := by
    have h_eq :
        inner ℝ v n2 =
          inner ℝ (p - b2) n2 -
            inner ℝ (c - b2) n2 := by
      simp [v, inner_sub_left]
    rw [h_eq]
    have h_abs :
        |inner ℝ (p - b2) n2 -
            inner ℝ (c - b2) n2| ≤
          |inner ℝ (p - b2) n2| +
            |inner ℝ (c - b2) n2| :=
      abs_sub _ _
    exact h_abs.trans (by linarith [hp.2, hc2])
  have h_main : ‖v‖ ≤ 6 * r / θ :=
    two_strip_vector_bound hr hθ hθ_le_one
      n1 n2 hn1 hn2 h_angle_lower h_angle_upper
      v hv1 hv2
  simpa [Metric.mem_closedBall, v, dist_eq_norm] using h_main

end Kakeya.Assouad
