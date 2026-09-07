import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.TightDistinctness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.DirectionConstraint
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.AnisotropicPacking
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CloseAxialTubes
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleBounds
import Mathlib.Tactic

/-!
# Large-scale conflict degree bound

For ρ ≥ 1/(100·A), the child tube conflict degree is bounded by O(A²).

Uses 5D anisotropic cell packing (3 midpoint + 2 direction transverse).
Two tubes in the same cell satisfy `close_axial_tubes_not_distinct`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

open Kakeya.Streamlined Metric Set InnerProductSpace
open Kakeya.Streamlined.GeometricLemmas

/-- Coordinate absolute value bounded by Euclidean norm in Point3. -/
private lemma point3_coord_le_norm (x : Point3) (k : Fin 3) : |x k| ≤ ‖x‖ := by
  have h_sum_nonneg : 0 ≤ (x 0)^2 + (x 1)^2 + (x 2)^2 := by positivity
  have h_simp : ‖x‖ = Real.sqrt ((x 0)^2 + ((x 1)^2 + (x 2)^2)) := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ]
  have h_assoc : (x 0)^2 + ((x 1)^2 + (x 2)^2) = (x 0)^2 + (x 1)^2 + (x 2)^2 := by ring
  have h1 : ‖x‖ = Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2) := by
    rw [h_simp, h_assoc]
  have h_norm_sq : ‖x‖ ^ 2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := by
    rw [h1]
    rw [Real.sq_sqrt h_sum_nonneg]
  have h2 : (x k)^2 ≤ ‖x‖ ^ 2 := by
    rw [h_norm_sq]
    fin_cases k <;> simp [Fin.sum_univ_succ] <;> ring_nf <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have h4 : 0 ≤ ‖x‖ := by positivity
  calc |x k|
    = Real.sqrt ((x k)^2) := by rw [Real.sqrt_sq_eq_abs]
  _ ≤ Real.sqrt (‖x‖ ^ 2) := Real.sqrt_le_sqrt h2
  _ = ‖x‖ := by rw [Real.sqrt_sq_eq_abs] <;> rw [abs_of_nonneg h4]

/-- Affine isometry applied to base + smul direction. -/
private lemma affine_midpoint (e : Point3 ≃ᵃⁱ[ℝ] Point3) (base dir : Point3) :
    e (base + (1 / 2 : ℝ) • dir) =
    e base + (1 / 2 : ℝ) • e.linearIsometryEquiv dir := by
  have h_vadd : e (((1 / 2 : ℝ) • dir) +ᵥ base) =
      e.linearIsometryEquiv ((1 / 2 : ℝ) • dir) +ᵥ e base :=
    e.map_vadd base ((1 / 2 : ℝ) • dir)
  have h_comm : ((1 / 2 : ℝ) • dir) +ᵥ base = base + (1 / 2 : ℝ) • dir := by
    simp [vadd_eq_add] <;> abel
  rw [h_comm] at h_vadd
  have h_smul : e.linearIsometryEquiv ((1 / 2 : ℝ) • dir) =
      (1 / 2 : ℝ) • e.linearIsometryEquiv dir :=
    e.linearIsometryEquiv.map_smul (1 / 2 : ℝ) dir
  rw [h_smul] at h_vadd
  simpa [vadd_eq_add, add_comm] using h_vadd

/-- Given two ρ-tubes with close midpoint/direction parameters in a common frame,
they are not essentially distinct. -/
private lemma close_params_not_distinct'
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {C_dir : ℝ} (hC_dir : 0 ≤ C_dir)
    {T1 T2 : Kakeya.DeltaTube ρ}
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (m1 m2 u1 u2 : Point3)
    (hm1 : m1 = frame.symm (T1.base + (1 / 2 : ℝ) • T1.direction))
    (hm2 : m2 = frame.symm (T2.base + (1 / 2 : ℝ) • T2.direction))
    (hu1 : u1 = frame.symm.linearIsometryEquiv T1.direction)
    (hu2 : u2 = frame.symm.linearIsometryEquiv T2.direction)
    (h_m0 : |(m1 - m2) 0| < ρ / 200)
    (h_m1 : |(m1 - m2) 1| < ρ / 200)
    (h_m2 : |(m1 - m2) 2| < 1 / (400 * max C_dir 16))
    (h_u0 : |(u1 - u2) 0| < ρ / 200)
    (h_u1 : |(u1 - u2) 1| < ρ / 200)
    (h_u2_0 : |u2 0| ≤ C_dir * ρ)
    (h_u2_1 : |u2 1| ≤ C_dir * ρ)
    (h_u1_long : u1 2 ≥ 1 / 2)
    (h_u2_long : u2 2 ≥ 1 / 2)
    (h_capsule_lower : CapsuleLowerBound)
    (h_capsule_upper : CapsuleUpperBound) :
    ¬ T1.EssentiallyDistinct T2 := by
  let p1 := frame.symm T1.base
  let p2 := frame.symm T2.base
  let t1 : ℝ := 1 / 2
  let t2 : ℝ := (m1 2 - p2 2) / u2 2
  let q1 := p1 + t1 • u1
  let q2 := p2 + t2 • u2

  have h_m1' : m1 = p1 + (1 / 2 : ℝ) • u1 := by
    rw [hm1, affine_midpoint frame.symm T1.base T1.direction, hu1] <;> rfl
  have h_m2' : m2 = p2 + (1 / 2 : ℝ) • u2 := by
    rw [hm2, affine_midpoint frame.symm T2.base T2.direction, hu2] <;> rfl

  have h_q1_eq : q1 = m1 := by
    dsimp only [q1, t1]
    rw [h_m1'] <;> abel
  have h_p22 : p2 2 = m2 2 - (1 / 2 : ℝ) * u2 2 := by
    have h' : m2 2 = p2 2 + (1 / 2 : ℝ) * u2 2 := by
      have h_eq : m2 = p2 + (1 / 2 : ℝ) • u2 := h_m2'
      have h : (m2 2) = (p2 + (1 / 2 : ℝ) • u2) 2 := by rw [h_eq]
      simpa [Pi.add_apply, Pi.smul_apply] using h
    linarith
  have h_q2_2 : q2 2 = m1 2 := by
    dsimp only [q2, t2]
    simp [Pi.add_apply, Pi.smul_apply, h_p22] <;> field_simp [h_u2_long] <;> ring
  have h_t2_diff : |t2 - 1 / 2| < 1 / (200 * max C_dir 16) := by
    have h_eq : t2 - 1 / 2 = (m1 2 - m2 2) / u2 2 := by
      dsimp only [t2]
      rw [h_p22] <;> field_simp [h_u2_long] <;> ring
    rw [h_eq]
    have h_pos : 0 < u2 2 := by linarith
    have h_m2' : |m1 2 - m2 2| < 1 / (400 * max C_dir 16) := by
      have h_sub : m1 2 - m2 2 = (m1 - m2) 2 := by simp [Pi.sub_apply]
      rw [h_sub]; exact h_m2
    have h_abs : |(m1 2 - m2 2) / u2 2| = |m1 2 - m2 2| / u2 2 := by
      rw [abs_div, abs_of_pos h_pos]
    rw [h_abs]
    have h1 : |m1 2 - m2 2| / u2 2 < (1 / (400 * max C_dir 16) : ℝ) / u2 2 :=
      div_lt_div_of_pos_right h_m2' h_pos
    have h2 : (1 / (400 * max C_dir 16) : ℝ) / u2 2 ≤
        (1 / (400 * max C_dir 16) : ℝ) / (1 / 2 : ℝ) := by
      apply div_le_div_of_nonneg_left
      · positivity
      · linarith
      · linarith
    have h3 : (1 / (400 * max C_dir 16) : ℝ) / (1 / 2 : ℝ) =
        1 / (200 * max C_dir 16) := by
      field_simp <;> ring
    rw [h3] at h2
    exact lt_of_lt_of_le h1 h2
  have h_t2_in : t2 ∈ Set.Icc (0 : ℝ) 1 := by
    have h4 : |t2 - 1 / 2| < 1 / (200 * max C_dir 16) := h_t2_diff
    have h5 : 1 / (200 * max C_dir 16) ≤ 1 / 3200 := by
      have h6 : (16 : ℝ) ≤ max C_dir 16 := le_max_right _ _
      gcongr
      <;> linarith
    have h7 : -(1 / 3200 : ℝ) < t2 - 1 / 2 ∧ t2 - 1 / 2 < (1 / 3200 : ℝ) := by
      have h8 : |t2 - 1 / 2| < 1 / 3200 := by linarith
      exact abs_lt.mp h8
    have h9 : 0 ≤ t2 := by linarith [h7.1]
    have h10 : t2 ≤ 1 := by linarith [h7.2]
    exact ⟨h9, h10⟩
  have h_p2_eq : p2 = m2 - (1 / 2 : ℝ) • u2 := by rw [h_m2'] <;> abel
  have h_main_eq : q1 - q2 = (m1 - m2) - (t2 - 1 / 2 : ℝ) • u2 := by
    have hq2 : q2 = p2 + t2 • u2 := by rfl
    have h_step1 : q1 - q2 = m1 - p2 - t2 • u2 := by
      rw [h_q1_eq, hq2] <;> abel
    rw [h_step1]
    rw [h_p2_eq]
    have h2 : m1 - (m2 - (1 / 2 : ℝ) • u2) - t2 • u2 =
        (m1 - m2) + (1 / 2 : ℝ) • u2 - t2 • u2 := by abel
    rw [h2]
    have h5 : (t2 - 1 / 2 : ℝ) • u2 = t2 • u2 - (1 / 2 : ℝ) • u2 := by
      rw [sub_smul]
    have h_goal : (m1 - m2) + (1 / 2 : ℝ) • u2 - t2 • u2 =
        (m1 - m2) - (t2 - 1 / 2 : ℝ) • u2 := by
      rw [h5]
      abel
    exact h_goal
  have h_corr0 : |t2 - 1 / 2| * |u2 0| ≤ ρ / 200 := by
    have h21 : |t2 - 1 / 2| < 1 / (200 * max C_dir 16) := h_t2_diff
    have h22 : |u2 0| ≤ C_dir * ρ := h_u2_0
    have h_pos : 0 < 200 * max C_dir 16 := by positivity
    have h23 : |t2 - 1 / 2| * |u2 0| ≤ (1 / (200 * max C_dir 16)) * (C_dir * ρ) := by
      have h231 : |t2 - 1 / 2| * |u2 0| ≤ (1 / (200 * max C_dir 16)) * |u2 0| :=
        mul_le_mul_of_nonneg_right (le_of_lt h21) (by positivity)
      have h232 : (1 / (200 * max C_dir 16)) * |u2 0| ≤ (1 / (200 * max C_dir 16)) * (C_dir * ρ) :=
        mul_le_mul_of_nonneg_left h22 (by positivity)
      exact le_trans h231 h232
    have h24 : (1 / (200 * max C_dir 16)) * (C_dir * ρ) ≤ ρ / 200 := by
      have h25 : C_dir ≤ max C_dir 16 := le_max_left _ _
      calc
        (1 / (200 * max C_dir 16)) * (C_dir * ρ)
          = C_dir * ρ / (200 * max C_dir 16) := by ring
        _ ≤ (max C_dir 16) * ρ / (200 * max C_dir 16) := by gcongr <;> linarith
        _ = ρ / 200 := by field_simp [h_pos.ne'] <;> ring
    exact le_trans h23 h24
  have h_corr1 : |t2 - 1 / 2| * |u2 1| ≤ ρ / 200 := by
    have h21 : |t2 - 1 / 2| < 1 / (200 * max C_dir 16) := h_t2_diff
    have h22 : |u2 1| ≤ C_dir * ρ := h_u2_1
    have h_pos : 0 < 200 * max C_dir 16 := by positivity
    have h23 : |t2 - 1 / 2| * |u2 1| ≤ (1 / (200 * max C_dir 16)) * (C_dir * ρ) := by
      have h231 : |t2 - 1 / 2| * |u2 1| ≤ (1 / (200 * max C_dir 16)) * |u2 1| :=
        mul_le_mul_of_nonneg_right (le_of_lt h21) (by positivity)
      have h232 : (1 / (200 * max C_dir 16)) * |u2 1| ≤ (1 / (200 * max C_dir 16)) * (C_dir * ρ) :=
        mul_le_mul_of_nonneg_left h22 (by positivity)
      exact le_trans h231 h232
    have h24 : (1 / (200 * max C_dir 16)) * (C_dir * ρ) ≤ ρ / 200 := by
      have h25 : C_dir ≤ max C_dir 16 := le_max_left _ _
      calc
        (1 / (200 * max C_dir 16)) * (C_dir * ρ)
          = C_dir * ρ / (200 * max C_dir 16) := by ring
        _ ≤ (max C_dir 16) * ρ / (200 * max C_dir 16) := by gcongr <;> linarith
        _ = ρ / 200 := by field_simp [h_pos.ne'] <;> ring
    exact le_trans h23 h24
  have h_q0 : |(q1 - q2) 0| ≤ ρ / 100 := by
    have h_eq : (q1 - q2) 0 = (m1 - m2) 0 - (t2 - 1 / 2) * u2 0 := by
      rw [h_main_eq]
      simp [Pi.add_apply, Pi.smul_apply, sub_smul] <;> ring
    rw [h_eq]
    have h_bound : |(m1 - m2) 0| + |t2 - 1 / 2| * |u2 0| < ρ / 100 := by
      have h1 : |(m1 - m2) 0| < ρ / 200 := h_m0
      linarith [h_corr0]
    have h_abs : |(m1 - m2) 0 - (t2 - 1 / 2) * u2 0| ≤
        |(m1 - m2) 0| + |(t2 - 1 / 2) * u2 0| := by
      exact abs_sub ((m1 - m2) 0) ((t2 - 1 / 2) * u2 0)
    have h_mul : |(t2 - 1 / 2) * u2 0| = |t2 - 1 / 2| * |u2 0| := by rw [abs_mul]
    rw [h_mul] at h_abs
    exact le_of_lt (lt_of_le_of_lt h_abs h_bound)
  have h_q1 : |(q1 - q2) 1| ≤ ρ / 100 := by
    have h_eq : (q1 - q2) 1 = (m1 - m2) 1 - (t2 - 1 / 2) * u2 1 := by
      rw [h_main_eq]
      simp [Pi.add_apply, Pi.smul_apply, sub_smul] <;> ring
    rw [h_eq]
    have h_bound : |(m1 - m2) 1| + |t2 - 1 / 2| * |u2 1| < ρ / 100 := by
      have h1 : |(m1 - m2) 1| < ρ / 200 := h_m1
      linarith [h_corr1]
    have h_abs2 : |(m1 - m2) 1 - (t2 - 1 / 2) * u2 1| ≤
        |(m1 - m2) 1| + |(t2 - 1 / 2) * u2 1| := by
      exact abs_sub ((m1 - m2) 1) ((t2 - 1 / 2) * u2 1)
    have h_mul : |(t2 - 1 / 2) * u2 1| = |t2 - 1 / 2| * |u2 1| := by rw [abs_mul]
    rw [h_mul] at h_abs2
    exact le_of_lt (lt_of_le_of_lt h_abs2 h_bound)
  have h_tdiff : |t1 - t2| ≤ 1 / 8 := by
    have h9 : |t1 - t2| = |t2 - 1 / 2| := by
      have h10 : t1 - t2 = -(t2 - 1 / 2) := by
        simp [t1] <;> ring
      rw [h10, abs_neg]
    rw [h9]
    have h10 : |t2 - 1 / 2| < 1 / (200 * max C_dir 16) := h_t2_diff
    have h11 : 1 / (200 * max C_dir 16) ≤ 1 / 3200 := by
      have h12 : (16 : ℝ) ≤ max C_dir 16 := le_max_right _ _
      gcongr <;> linarith
    linarith
  exact close_axial_tubes_not_distinct hρ hρ1 frame p1 u1 p2 u2 q1 q2 t1 t2
    rfl hu1 rfl hu2 (by norm_num) h_t2_in
    (by dsimp only [q1, t1] <;> rfl) (by dsimp only [q2, t2] <;> rfl)
    (by simp [h_q2_2, h_q1_eq])
    h_q0 h_q1 h_tdiff
    (by linarith [h_u0]) (by linarith [h_u1])
    h_u1_long h_u2_long h_capsule_lower h_capsule_upper

/--
Large-scale packing bound: essentially distinct ρ-tubes with midpoints in
a transverse ball of radius R and longitudinal bound R_long around center,
and directions in a narrow cone around v_ref.

The transverse bound R applies to coordinates perpendicular to v_ref;
the longitudinal bound R_long applies to the inner product with v_ref.
-/
lemma large_scale_packing_bound
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {R R_long : ℝ} (hR : 0 ≤ R) (hR_long : 0 ≤ R_long)
    {C_dir : ℝ} (hC_dir : 0 ≤ C_dir)
    {n : ℕ} {T : Fin n → Kakeya.DeltaTube ρ}
    (indices : Finset (Fin n))
    (center : Point3)
    (v_ref : Point3) (hv_ref : ‖v_ref‖ = 1)
    (h_mid_trans : ∀ j ∈ indices,
      ‖(((T j).base + (1 / 2 : ℝ) • (T j).direction) - center) -
          inner ℝ
              (((T j).base + (1 / 2 : ℝ) • (T j).direction) - center)
              v_ref •
            v_ref‖ ≤ R)
    (h_mid_long : ∀ j ∈ indices,
      |inner ℝ ((T j).base + (1 / 2 : ℝ) • (T j).direction - center) v_ref| ≤ R_long)
    (h_dir : ∀ j ∈ indices,
      ‖(T j).direction - inner ℝ (T j).direction v_ref • v_ref‖ ≤ C_dir * ρ)
    (h_long : ∀ j ∈ indices, inner ℝ (T j).direction v_ref ≥ 1 / 2)
    (h_distinct : ∀ i j, i ∈ indices → j ∈ indices → i ≠ j →
      (T i).EssentiallyDistinct (T j))
    (h_capsule_lower : CapsuleLowerBound)
    (h_capsule_upper : CapsuleUpperBound) :
    indices.card ≤
      (2 * Nat.ceil (200 * R / ρ) + 1)^2 *
      (2 * Nat.ceil ((400 * max C_dir 16) * R_long) + 1) *
      (2 * Nat.ceil (200 * C_dir) + 1)^2 := by
  rcases frame_of_axis v_ref hv_ref with ⟨_, _, frame, hframe2, hframe0, hframe1⟩
  let e := frame.symm
  let mid (j : Fin n) : Point3 :=
    e ((T j).base + (1 / 2 : ℝ) • (T j).direction) - e center
  let dir (j : Fin n) : Point3 := e.linearIsometryEquiv (T j).direction

  have h_ev : e.linearIsometryEquiv v_ref = (EuclideanSpace.single 2 1 : Point3) := by
    ext k
    fin_cases k
    · simpa [EuclideanSpace.single] using hframe0
    · simpa [EuclideanSpace.single] using hframe1
    · simpa [EuclideanSpace.single] using hframe2

  have h_mid_linear : ∀ j,
      mid j =
        e.linearIsometryEquiv
          ((T j).base + (1 / 2 : ℝ) • (T j).direction - center) := by
    intro j
    let point :=
      (T j).base + (1 / 2 : ℝ) • (T j).direction
    have hmap :
        e point =
          e center + e.linearIsometryEquiv (point - center) := by
      have h := e.map_vadd center (point - center)
      have hpoint : (point - center) + center = point := by abel
      simpa [vadd_eq_add, hpoint, add_comm] using h
    dsimp only [mid, point] at hmap ⊢
    rw [hmap]
    abel

  have h_mid_trans_frame : ∀ j ∈ indices,
      ‖mid j -
          inner ℝ (mid j) (e.linearIsometryEquiv v_ref) •
            e.linearIsometryEquiv v_ref‖ ≤ R := by
    intro j hj
    let displacement :=
      (T j).base + (1 / 2 : ℝ) • (T j).direction - center
    have hmap :
        e.linearIsometryEquiv
            (displacement - inner ℝ displacement v_ref • v_ref) =
          e.linearIsometryEquiv displacement -
            inner ℝ
                (e.linearIsometryEquiv displacement)
                (e.linearIsometryEquiv v_ref) •
              e.linearIsometryEquiv v_ref := by
      rw [e.linearIsometryEquiv.map_sub,
        e.linearIsometryEquiv.map_smul,
        e.linearIsometryEquiv.inner_map_map]
    have hnorm :
        ‖e.linearIsometryEquiv
            (displacement - inner ℝ displacement v_ref • v_ref)‖ ≤
          R := by
      rw [e.linearIsometryEquiv.norm_map]
      exact h_mid_trans j hj
    rw [hmap] at hnorm
    simpa [displacement, h_mid_linear j] using hnorm

  have h_mid_long_coord : ∀ j ∈ indices, (mid j) 2 =
      inner ℝ ((T j).base + (1 / 2 : ℝ) • (T j).direction - center) v_ref := by
    intro j hj
    have h1 : (mid j) 2 = inner ℝ (mid j) (e.linearIsometryEquiv v_ref) := by
      rw [h_ev]
      have h2 : inner ℝ (mid j) (EuclideanSpace.single 2 1 : Point3) = (mid j) 2 := by
        have h3 := EuclideanSpace.inner_single_right (2 : Fin 3) (1 : ℝ) (mid j)
        simpa using h3
      exact h2.symm
    rw [h1]
    rw [h_mid_linear]
    have h6 : inner ℝ (e.linearIsometryEquiv ((T j).base + (1 / 2 : ℝ) • (T j).direction - center)) (e.linearIsometryEquiv v_ref) =
        inner ℝ ((T j).base + (1 / 2 : ℝ) • (T j).direction - center) v_ref :=
      e.linearIsometryEquiv.inner_map_map _ _
    exact h6

  have h_mid_coord : ∀ j ∈ indices, ∀ k : Fin 3, |(mid j) k| ≤ (if k = 2 then R_long else R) := by
    intro j hj k
    fin_cases k <;> simp
    · let transverse :=
        mid j -
          inner ℝ (mid j) (e.linearIsometryEquiv v_ref) •
            e.linearIsometryEquiv v_ref
      have hcoordinate : transverse 0 = mid j 0 := by
        dsimp only [transverse]
        rw [h_ev]
        simp [EuclideanSpace.single, Pi.sub_apply, Pi.smul_apply]
      have h1 : |transverse 0| ≤ ‖transverse‖ :=
        point3_coord_le_norm transverse 0
      rw [hcoordinate] at h1
      exact h1.trans (h_mid_trans_frame j hj)
    · let transverse :=
        mid j -
          inner ℝ (mid j) (e.linearIsometryEquiv v_ref) •
            e.linearIsometryEquiv v_ref
      have hcoordinate : transverse 1 = mid j 1 := by
        dsimp only [transverse]
        rw [h_ev]
        simp [EuclideanSpace.single, Pi.sub_apply, Pi.smul_apply]
      have h1 : |transverse 1| ≤ ‖transverse‖ :=
        point3_coord_le_norm transverse 1
      rw [hcoordinate] at h1
      exact h1.trans (h_mid_trans_frame j hj)
    · have h3 : |(mid j) 2| ≤ R_long := by
        rw [h_mid_long_coord j hj]
        exact h_mid_long j hj
      linarith

  have h_inner_eq : ∀ j, inner ℝ (T j).direction v_ref = dir j 2 := by
    intro j
    have h5 : inner ℝ (dir j) (e.linearIsometryEquiv v_ref) =
        inner ℝ (T j).direction v_ref :=
      e.linearIsometryEquiv.inner_map_map (T j).direction v_ref
    have h6 : inner ℝ (T j).direction v_ref =
        inner ℝ (dir j) (e.linearIsometryEquiv v_ref) := h5.symm
    rw [h6, h_ev]
    have h7 : inner ℝ (dir j) (EuclideanSpace.single 2 1 : Point3) = dir j 2 := by
      have h8 : inner ℝ (dir j) (EuclideanSpace.single 2 1 : Point3) =
          (1 : ℝ) * (dir j) 2 :=
        EuclideanSpace.inner_single_right (2 : Fin 3) (1 : ℝ) (dir j)
      rw [h8] <;> ring
    exact h7

  have h_dir_frame : ∀ j ∈ indices,
      ‖(dir j) - (dir j 2) • (EuclideanSpace.single 2 1 : Point3)‖ ≤ C_dir * ρ := by
    intro j hj
    have h1 := h_dir j hj
    have h21 : e.linearIsometryEquiv ((T j).direction - inner ℝ (T j).direction v_ref • v_ref) =
        e.linearIsometryEquiv (T j).direction - e.linearIsometryEquiv (inner ℝ (T j).direction v_ref • v_ref) := by
      exact e.linearIsometryEquiv.map_sub _ _
    have h22 : e.linearIsometryEquiv (inner ℝ (T j).direction v_ref • v_ref) =
        (inner ℝ (T j).direction v_ref) • e.linearIsometryEquiv v_ref := by
      exact e.linearIsometryEquiv.map_smul _ _
    have h2 : e.linearIsometryEquiv ((T j).direction - inner ℝ (T j).direction v_ref • v_ref) =
        dir j - (inner ℝ (T j).direction v_ref) • e.linearIsometryEquiv v_ref := by
      rw [h21, h22]
      <;> rfl
    have h3 : ‖e.linearIsometryEquiv ((T j).direction - inner ℝ (T j).direction v_ref • v_ref)‖ =
        ‖(T j).direction - inner ℝ (T j).direction v_ref • v_ref‖ :=
      e.linearIsometryEquiv.norm_map _
    have h4 : ‖e.linearIsometryEquiv ((T j).direction - inner ℝ (T j).direction v_ref • v_ref)‖ ≤ C_dir * ρ := by
      rw [h3]; exact h1
    rw [h2, h_ev, h_inner_eq j] at h4
    exact h4

  have h_dir_coord : ∀ j ∈ indices, |(dir j) 0| ≤ C_dir * ρ ∧ |(dir j) 1| ≤ C_dir * ρ := by
    intro j hj
    have h1 := h_dir_frame j hj
    let w := (dir j) - (dir j 2) • (EuclideanSpace.single 2 1 : Point3)
    have hw0 : w 0 = (dir j) 0 := by
      simp [w, EuclideanSpace.single] <;> ring
    have hw1 : w 1 = (dir j) 1 := by
      simp [w, EuclideanSpace.single] <;> ring
    have h2 : |w 0| ≤ ‖w‖ := point3_coord_le_norm w 0
    have h3 : |w 1| ≤ ‖w‖ := point3_coord_le_norm w 1
    rw [hw0] at h2; rw [hw1] at h3
    exact ⟨by linarith, by linarith⟩

  have h_dir_long : ∀ j ∈ indices, (dir j) 2 ≥ 1 / 2 := by
    intro j hj
    have h1 : inner ℝ (T j).direction v_ref ≥ 1 / 2 := h_long j hj
    have h2 : inner ℝ (T j).direction v_ref = dir j 2 := h_inner_eq j
    linarith

  let f : Fin n → (Fin 5 → ℝ) := fun j =>
    ![mid j 0, mid j 1, mid j 2, dir j 0, dir j 1]
  let V : Finset (Fin 5 → ℝ) := indices.image f
  let M := max C_dir 16
  let s : Fin 5 → ℝ := ![ρ / 200, ρ / 200, 1 / (400 * M), ρ / 200, ρ / 200]
  let Rvec : Fin 5 → ℝ := ![R, R, R_long, C_dir * ρ, C_dir * ρ]

  have hs : ∀ i, 0 < s i := by
    intro i
    fin_cases i <;> simp [s, M] <;> positivity
  have hRvec : ∀ i, 0 ≤ Rvec i := by
    intro i
    fin_cases i <;> simp [Rvec] <;> positivity

  have hball : ∀ v ∈ V, ∀ i, |v i| ≤ Rvec i := by
    intro v hv i
    rcases Finset.mem_image.mp hv with ⟨j, hj, rfl⟩
    fin_cases i
    · simpa [f, Rvec] using h_mid_coord j hj 0
    · simpa [f, Rvec] using h_mid_coord j hj 1
    · simpa [f, Rvec] using h_mid_coord j hj 2
    · simpa [f, Rvec] using (h_dir_coord j hj).1
    · simpa [f, Rvec] using (h_dir_coord j hj).2

  have h_no_close : ∀ (j1 j2 : Fin n), j1 ∈ indices → j2 ∈ indices → j1 ≠ j2 →
      (∀ i, |(f j1) i - (f j2) i| < s i) → False := by
    intro j1 j2 hj1 hj2 hne h
    let m1 := mid j1 + e center
    let m2 := mid j2 + e center
    let u1 := dir j1
    let u2 := dir j2
    have h_eq0 : (m1 - m2) 0 = (f j1) 0 - (f j2) 0 := by
      simp [m1, m2, mid, f] <;> abel
    have h_eq1 : (m1 - m2) 1 = (f j1) 1 - (f j2) 1 := by
      simp [m1, m2, mid, f] <;> abel
    have h_eq2 : (m1 - m2) 2 = (f j1) 2 - (f j2) 2 := by
      simp [m1, m2, mid, f] <;> abel
    have h_eq3 : (u1 - u2) 0 = (f j1) 3 - (f j2) 3 := by
      simp [u1, u2, dir, f] <;> abel
    have h_eq4 : (u1 - u2) 1 = (f j1) 4 - (f j2) 4 := by
      simp [u1, u2, dir, f] <;> abel
    have h_m0 : |(m1 - m2) 0| < ρ / 200 := by rw [h_eq0]; exact h 0
    have h_m1 : |(m1 - m2) 1| < ρ / 200 := by rw [h_eq1]; exact h 1
    have h_m2 : |(m1 - m2) 2| < 1 / (400 * M) := by rw [h_eq2]; exact h 2
    have h_u0 : |(u1 - u2) 0| < ρ / 200 := by rw [h_eq3]; exact h 3
    have h_u1 : |(u1 - u2) 1| < ρ / 200 := by rw [h_eq4]; exact h 4
    have h_u2_0 : |u2 0| ≤ C_dir * ρ := (h_dir_coord j2 hj2).1
    have h_u2_1 : |u2 1| ≤ C_dir * ρ := (h_dir_coord j2 hj2).2
    have hm1' : m1 = e ((T j1).base + (1 / 2 : ℝ) • (T j1).direction) := by
      simp [m1, mid] <;> abel
    have hm2' : m2 = e ((T j2).base + (1 / 2 : ℝ) • (T j2).direction) := by
      simp [m2, mid] <;> abel
    have hu1' : u1 = e.linearIsometryEquiv (T j1).direction := by
      simp [u1, dir] <;> rfl
    have hu2' : u2 = e.linearIsometryEquiv (T j2).direction := by
      simp [u2, dir] <;> rfl
    have h_not_distinct : ¬ (T j1).EssentiallyDistinct (T j2) :=
      close_params_not_distinct' hρ hρ1 hC_dir frame m1 m2 u1 u2
        hm1' hm2' hu1' hu2'
        h_m0 h_m1 h_m2 h_u0 h_u1
        h_u2_0 h_u2_1
        (h_dir_long j1 hj1) (h_dir_long j2 hj2)
        h_capsule_lower h_capsule_upper
    have h_actually_distinct := h_distinct j1 j2 hj1 hj2 hne
    exact h_not_distinct h_actually_distinct

  have hsep : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → ∃ i, |v i - w i| ≥ s i := by
    intro v hv w hw hne
    rcases Finset.mem_image.mp hv with ⟨j1, hj1, rfl⟩
    rcases Finset.mem_image.mp hw with ⟨j2, hj2, rfl⟩
    by_contra h
    push Not at h
    have h_j12 : j1 ≠ j2 := by
      intro h_eq; rw [h_eq] at hne; exact hne rfl
    exact h_no_close j1 j2 hj1 hj2 h_j12 h

  have h_main : V.card ≤ ∏ i : Fin 5, (2 * Nat.ceil (Rvec i / s i) + 1) :=
    anisotropic_cell_pack hs hRvec hball hsep

  have h_inj : Set.InjOn f (indices : Set (Fin n)) := by
    intro j1 hj1 j2 hj2 h_eq
    by_contra hne
    have h_all : ∀ i, |(f j1) i - (f j2) i| < s i := by
      intro i
      have h0 : (f j1) i - (f j2) i = 0 := by
        have h1 : (f j1) i = (f j2) i := by rw [h_eq]
        linarith
      rw [h0]
      simp [abs_zero]
      <;> linarith [hs i]
    exact h_no_close j1 j2 hj1 hj2 hne h_all

  have h_card : V.card = indices.card := by
    rw [Finset.card_image_of_injOn h_inj]

  have h0 : Rvec 0 / s 0 = 200 * R / ρ := by
    simp [s, Rvec] <;> field_simp [hρ.ne'] <;> ring
  have h1 : Rvec 1 / s 1 = 200 * R / ρ := by
    simp [s, Rvec] <;> field_simp [hρ.ne'] <;> ring
  have h2 : Rvec 2 / s 2 = (400 * M) * R_long := by
    simp [s, Rvec, M] <;> field_simp [hρ.ne'] <;> ring
  have h3 : Rvec 3 / s 3 = 200 * C_dir := by
    simp [s, Rvec] <;> field_simp [hρ.ne'] <;> ring
  have h4 : Rvec 4 / s 4 = 200 * C_dir := by
    simp [s, Rvec] <;> field_simp [hρ.ne'] <;> ring

  have h_prod : (∏ i : Fin 5, (2 * Nat.ceil (Rvec i / s i) + 1)) =
      (2 * Nat.ceil (200 * R / ρ) + 1) *
      (2 * Nat.ceil (200 * R / ρ) + 1) *
      (2 * Nat.ceil ((400 * M) * R_long) + 1) *
      (2 * Nat.ceil (200 * C_dir) + 1) *
      (2 * Nat.ceil (200 * C_dir) + 1) := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
    <;> simp [h0, h1, h2, h3, h4, Fin.sum_univ_succ] <;> ring

  rw [h_card] at h_main
  rw [h_prod] at h_main
  let a := 2 * Nat.ceil (200 * R / ρ) + 1
  let b := 2 * Nat.ceil ((400 * M) * R_long) + 1
  let c := 2 * Nat.ceil (200 * C_dir) + 1
  have h_final : a * a * b * c * c = a^2 * b * c^2 := by
    simp [pow_two] <;> ring
  rw [h_final] at h_main
  exact h_main

/-- Conflict degree bound from large-scale 5D packing.

Given a fixed tube `j` and a set of conflicting tubes whose midpoints and
directions are geometrically bounded relative to `j`, apply
`large_scale_packing_bound` to bound the cardinality of the conflicting set.

The geometry bounds must be supplied as hypotheses:
- `h_mid`: transverse midpoint distance ≤ R
- `h_mid_long`: longitudinal midpoint separation ≤ R_long
- `h_dir`: direction transverse component ≤ C_dir * ρ
- `h_long`: direction inner product with v_ref ≥ 1/2

NOTE: Requires `ρ ≤ 1`. For child-tube scales ≥ 1 (far range), a different
argument or rescaling is needed.
-/
lemma large_scale_conflict_degree
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {n : ℕ} {T : Fin n → Kakeya.DeltaTube ρ}
    (j : Fin n)
    (conflicting : Finset (Fin n))
    (h_j_not_in : j ∉ conflicting)
    (R R_long C_dir : ℝ)
    (hR : 0 ≤ R) (hR_long : 0 ≤ R_long) (hC_dir : 0 ≤ C_dir)
    (h_mid : ∀ j' ∈ conflicting,
      dist ((T j').base + (1 / 2 : ℝ) • (T j').direction)
           ((T j).base + (1 / 2 : ℝ) • (T j).direction) ≤ R)
    (h_mid_long : ∀ j' ∈ conflicting,
      |inner ℝ ((T j').base + (1 / 2 : ℝ) • (T j').direction -
                 ((T j).base + (1 / 2 : ℝ) • (T j).direction))
        (T j).direction| ≤ R_long)
    (h_dir : ∀ j' ∈ conflicting,
      ‖(T j').direction - inner ℝ (T j').direction (T j).direction • (T j).direction‖
        ≤ C_dir * ρ)
    (h_long : ∀ j' ∈ conflicting,
      inner ℝ (T j').direction (T j).direction ≥ 1 / 2)
    (h_distinct : ∀ i j', i ∈ insert j conflicting → j' ∈ insert j conflicting →
      i ≠ j' → (T i).EssentiallyDistinct (T j'))
    (h_capsule_lower : CapsuleLowerBound)
    (h_capsule_upper : CapsuleUpperBound) :
    conflicting.card ≤
      (2 * Nat.ceil (200 * R / ρ) + 1)^2 *
      (2 * Nat.ceil ((400 * max C_dir 16) * R_long) + 1) *
      (2 * Nat.ceil (200 * C_dir) + 1)^2 := by
  let indices := insert j conflicting
  let center := (T j).base + (1 / 2 : ℝ) • (T j).direction
  let v_ref := (T j).direction
  have hv_ref : ‖v_ref‖ = 1 := (T j).direction_unit

  have h_mid_all : ∀ k ∈ indices,
      dist ((T k).base + (1 / 2 : ℝ) • (T k).direction) center ≤ R := by
    intro k hk
    by_cases h : k = j
    · rw [h, dist_self] <;> linarith
    · have h' : k ∈ conflicting := by
        simp only [indices, Finset.mem_insert] at hk
        tauto
      exact h_mid k h'

  have h_mid_trans_all : ∀ k ∈ indices,
      ‖(((T k).base + (1 / 2 : ℝ) • (T k).direction) - center) -
          inner ℝ
              (((T k).base + (1 / 2 : ℝ) • (T k).direction) - center)
              v_ref •
            v_ref‖ ≤ R := by
    intro k hk
    exact
      (perp_norm_le_dist_to_line_point
        hv_ref
        ((T k).base + (1 / 2 : ℝ) • (T k).direction)
        center 0 (by simp)).trans
        (h_mid_all k hk)

  have h_mid_long_all : ∀ k ∈ indices,
      |inner ℝ ((T k).base + (1 / 2 : ℝ) • (T k).direction - center) v_ref| ≤ R_long := by
    intro k hk
    by_cases h : k = j
    · rw [h]; simp [center, v_ref, abs_nonneg] <;> linarith
    · have h' : k ∈ conflicting := by
        simp only [indices, Finset.mem_insert] at hk
        tauto
      exact h_mid_long k h'

  have h_dir_all : ∀ k ∈ indices,
      ‖(T k).direction - inner ℝ (T k).direction v_ref • v_ref‖ ≤ C_dir * ρ := by
    intro k hk
    by_cases h : k = j
    · rw [h]
      have h_inner : inner ℝ (T j).direction v_ref = 1 := by
        simp [v_ref, inner_self_eq_norm_sq_to_K, hv_ref] <;> norm_num
      rw [h_inner]
      have h_zero : (T j).direction - (1 : ℝ) • v_ref = 0 := by
        simp [v_ref] <;> abel
      rw [h_zero]
      simp [norm_zero] <;> positivity
    · have h' : k ∈ conflicting := by
        simp only [indices, Finset.mem_insert] at hk
        tauto
      exact h_dir k h'

  have h_long_all : ∀ k ∈ indices, inner ℝ (T k).direction v_ref ≥ 1 / 2 := by
    intro k hk
    by_cases h : k = j
    · rw [h]
      have h_inner : inner ℝ (T j).direction v_ref = 1 := by
        simp [v_ref, inner_self_eq_norm_sq_to_K, hv_ref] <;> norm_num
      rw [h_inner] <;> norm_num
    · have h' : k ∈ conflicting := by
        simp only [indices, Finset.mem_insert] at hk
        tauto
      exact h_long k h'

  have h_main := large_scale_packing_bound hρ hρ1 hR hR_long hC_dir
    indices center v_ref hv_ref
    h_mid_trans_all h_mid_long_all h_dir_all h_long_all
    h_distinct h_capsule_lower h_capsule_upper

  have h_card : conflicting.card ≤ indices.card :=
    Finset.card_le_card (Finset.subset_insert j conflicting)

  exact le_trans h_card h_main

end Kakeya.Assouad

end
