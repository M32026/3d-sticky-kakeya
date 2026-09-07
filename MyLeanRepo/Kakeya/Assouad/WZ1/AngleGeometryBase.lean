import MyLeanRepo.Kakeya.Assouad.WZ1.StripGeometry

/-!
# Planar angle geometry for WZ1 Lemma 44

This module contains only the projection and orthonormal-decomposition
identities consumed by the three-case bad-pair estimate.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

lemma cross2_add_left (a b w : Point2) :
    cross2 (a + b) w = cross2 a w + cross2 b w := by
  simp [cross2]
  ring

lemma cross2_smul_left (c : ℝ) (a w : Point2) :
    cross2 (c • a) w = c * cross2 a w := by
  simp [cross2]
  ring

lemma cross2_sq_eq (v w : Point2) :
    cross2 v w ^ 2 =
      ‖v‖ ^ 2 * ‖w‖ ^ 2 - (inner ℝ v w) ^ 2 := by
  rw [norm2_sq, norm2_sq, inner2_eq]
  simp [cross2]
  ring

lemma abs_cross2_of_orthogonal
    {v w : Point2} (h : inner ℝ v w = 0) :
    |cross2 v w| = ‖v‖ * ‖w‖ := by
  have h1 :
      cross2 v w ^ 2 = ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
    rw [cross2_sq_eq, h]
    ring
  have h3 :
      |cross2 v w| ^ 2 = (‖v‖ * ‖w‖) ^ 2 := by
    rw [sq_abs, h1]
    ring
  nlinarith [abs_nonneg (cross2 v w),
    mul_nonneg (norm_nonneg v) (norm_nonneg w)]

/-- Orthogonal projection of `y` onto the line through `x` in direction `w`. -/
def projPoint (x y w : Point2) : Point2 :=
  x + (inner ℝ (y - x) w / ‖w‖ ^ 2) • w

lemma projPoint_orthogonal
    {x y w : Point2} (hw_ne_zero : w ≠ 0) :
    inner ℝ (y - projPoint x y w) w = 0 := by
  have hwnorm_ne_zero : ‖w‖ ≠ 0 := by
    simpa [norm_eq_zero] using hw_ne_zero
  set c : ℝ := inner ℝ (y - x) w / ‖w‖ ^ 2
  have h1 :
      y - projPoint x y w = (y - x) - c • w := by
    dsimp only [projPoint]
    abel
  have h_smul :
      inner ℝ (c • w) w = c * inner ℝ w w :=
    real_inner_smul_left w w c
  have h3 : inner ℝ w w = ‖w‖ ^ 2 :=
    real_inner_self_eq_norm_sq w
  rw [h1, inner_sub_left, h_smul, h3]
  dsimp only [c]
  field_simp [hwnorm_ne_zero]
  ring

lemma projPoint_norm
    {x y w : Point2} (hw_ne_zero : w ≠ 0) :
    ‖y - projPoint x y w‖ =
      |cross2 (y - x) w| / ‖w‖ := by
  set a := y - projPoint x y w
  set b := projPoint x y w - x
  have h_orth : inner ℝ a w = 0 :=
    projPoint_orthogonal hw_ne_zero
  have h_sum : y - x = a + b := by
    dsimp only [a, b, projPoint]
    abel
  have h3 :
      b = (inner ℝ (y - x) w / ‖w‖ ^ 2) • w := by
    dsimp only [b, projPoint]
    abel
  have h_cross_eq :
      cross2 (y - x) w = cross2 a w := by
    rw [h_sum, cross2_add_left, h3, cross2_smul_left]
    have h4 : cross2 w w = 0 := by
      simp [cross2]
      ring
    rw [h4]
    ring
  have h_abs :
      |cross2 a w| = ‖a‖ * ‖w‖ :=
    abs_cross2_of_orthogonal h_orth
  have h5 :
      |cross2 (y - x) w| = ‖a‖ * ‖w‖ := by
    rw [h_cross_eq, h_abs]
  have hwnorm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  have h7 :
      ‖a‖ = |cross2 (y - x) w| / ‖w‖ := by
    field_simp [hwnorm_pos.ne'] at h5 ⊢
    linarith
  rwa [show a = y - projPoint x y w by rfl] at h7

/-- The affine line through two planar points. -/
def lineThrough (p q : Point2) : AffineSubspace ℝ Point2 :=
  AffineSubspace.mk' p (ℝ ∙ (q - p))

lemma lineThrough_contains_first {p q : Point2} :
    p ∈ (lineThrough p q : Set Point2) := by
  simpa [lineThrough, AffineSubspace.mem_mk'] using
    (show p - p ∈ (ℝ ∙ (q - p) : Submodule ℝ Point2) by simp)

lemma wz1Perp2_coords (n : Point2) :
    wz1Perp2 n 0 = -n 1 ∧
      wz1Perp2 n 1 = n 0 := by
  simp [wz1Perp2, EuclideanSpace.single]

lemma orthonormal_decomp
    (v n : Point2) (hn : ‖n‖ = 1) :
    v =
      (inner ℝ v n) • n +
        (inner ℝ v (wz1Perp2 n)) • wz1Perp2 n := by
  have h_nsq : (n 0) ^ 2 + (n 1) ^ 2 = 1 := by
    have h := norm2_sq n
    rw [hn] at h
    nlinarith
  have hpc := wz1Perp2_coords n
  let w :=
    (inner ℝ v n) • n +
      (inner ℝ v (wz1Perp2 n)) • wz1Perp2 n
  have h_inner :
      inner ℝ v n = v 0 * n 0 + v 1 * n 1 :=
    inner2_eq v n
  have h_perp :
      inner ℝ v (wz1Perp2 n) =
        -v 0 * n 1 + v 1 * n 0 := by
    rw [inner2_eq, hpc.1, hpc.2]
    ring
  have hx : w 0 = v 0 := by
    have h2 :
        w 0 =
          (inner ℝ v n) * n 0 +
            (inner ℝ v (wz1Perp2 n)) *
              (wz1Perp2 n 0) := by
      simp [w]
    rw [h2, h_inner, h_perp, hpc.1]
    have h3 :
        (v 0 * n 0 + v 1 * n 1) * n 0 +
            (-v 0 * n 1 + v 1 * n 0) * (-n 1) =
          v 0 * ((n 0) ^ 2 + (n 1) ^ 2) := by
      ring
    rw [h3, h_nsq]
    ring
  have hy : w 1 = v 1 := by
    have h2 :
        w 1 =
          (inner ℝ v n) * n 1 +
            (inner ℝ v (wz1Perp2 n)) *
              (wz1Perp2 n 1) := by
      simp [w]
    rw [h2, h_inner, h_perp, hpc.2]
    have h3 :
        (v 0 * n 0 + v 1 * n 1) * n 1 +
            (-v 0 * n 1 + v 1 * n 0) * n 0 =
          v 1 * ((n 0) ^ 2 + (n 1) ^ 2) := by
      ring
    rw [h3, h_nsq]
    ring
  have h_ext : w = v := by
    ext i
    fin_cases i <;> assumption
  exact h_ext.symm

lemma cross2_perp_perp (n1 n2 : Point2) :
    cross2 (wz1Perp2 n1) (wz1Perp2 n2) =
      cross2 n1 n2 := by
  have h1 := wz1Perp2_coords n1
  have h2 := wz1Perp2_coords n2
  simp [cross2, h1.1, h1.2, h2.1, h2.2]
  ring

lemma abs_cross2_normals_le_dist
    (n1 n2 : Point2)
    (hn1 : ‖n1‖ = 1) (hn2 : ‖n2‖ = 1) :
    |cross2 n1 n2| ≤ ‖n1 - n2‖ := by
  set c := inner ℝ n1 n2
  have h1 : cross2 n1 n2 ^ 2 = 1 - c ^ 2 := by
    have h2 := cross2_sq_eq n1 n2
    rw [h2, hn1, hn2]
    ring
  have h5 :
      ‖n1 - n2‖ ^ 2 = 2 - 2 * c :=
    unit_diff_sq n1 n2 hn1 hn2
  by_cases hc : 0 ≤ c
  · have h7 :
        cross2 n1 n2 ^ 2 ≤ ‖n1 - n2‖ ^ 2 := by
      rw [h1, h5]
      nlinarith
    have h9 :
        |cross2 n1 n2| ^ 2 ≤ ‖n1 - n2‖ ^ 2 := by
      rwa [sq_abs]
    nlinarith [abs_nonneg (cross2 n1 n2),
      norm_nonneg (n1 - n2)]
  · have h_gt1 : 1 < ‖n1 - n2‖ := by
      have h_gt2 : 2 < ‖n1 - n2‖ ^ 2 := by
        rw [h5]
        linarith
      nlinarith [norm_nonneg (n1 - n2)]
    have h_le1 : cross2 n1 n2 ^ 2 ≤ 1 := by
      rw [h1]
      nlinarith [sq_nonneg c]
    have h_abs_le1 : |cross2 n1 n2| ≤ 1 := by
      nlinarith [sq_abs (cross2 n1 n2),
        abs_nonneg (cross2 n1 n2)]
    linarith

end Kakeya.Assouad
