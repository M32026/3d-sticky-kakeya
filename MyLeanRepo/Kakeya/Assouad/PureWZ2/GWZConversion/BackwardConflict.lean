import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.TileFilter
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.TightDistinctness
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleBounds
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.ForwardConflict

set_option linter.constructorNameAsVariable false

/-!
# Constant backward conflict degree bound

Uses the TightDistinctness grid approach to get a CONSTANT bound
on the number of essentially distinct δ-tubes whose 2-dilation contains
a given δ-tube.

The backward geometric bounds are looser than the forward bounds
(8δ vs 4δ for direction, 10δ vs 2δ for transverse midpoint),
requiring a larger grid but still a constant total count.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

open Kakeya.Streamlined
open Kakeya.Streamlined.GeometricLemmas

/-- Reflection function: negate z-coordinate. -/
private def zReflectFun (p : Point3) : Point3 :=
  p - (2 * (p 2)) • (EuclideanSpace.single 2 1)

@[simp] private lemma zReflectFun_0 (p : Point3) : (zReflectFun p) 0 = p 0 := by
  simp [zReflectFun, Pi.sub_apply, Pi.smul_apply, EuclideanSpace.single] <;> ring

@[simp] private lemma zReflectFun_1 (p : Point3) : (zReflectFun p) 1 = p 1 := by
  simp [zReflectFun, Pi.sub_apply, Pi.smul_apply, EuclideanSpace.single] <;> ring

@[simp] private lemma zReflectFun_2 (p : Point3) : (zReflectFun p) 2 = - (p 2) := by
  simp [zReflectFun, Pi.sub_apply, Pi.smul_apply, EuclideanSpace.single] <;> ring

/-- Reflection in the z-axis as a linear isometry. -/
private def zReflect : Point3 ≃ₗᵢ[ℝ] Point3 :=
  { toFun := zReflectFun
    invFun := zReflectFun
    left_inv := by
      intro p
      ext i
      fin_cases i <;> simp <;> ring
    right_inv := by
      intro p
      ext i
      fin_cases i <;> simp <;> ring
    map_add' := by
      intro p q
      ext i
      fin_cases i <;> simp [Pi.add_apply] <;> ring
    map_smul' := by
      intro c p
      ext i
      fin_cases i <;> simp [Pi.smul_apply] <;> ring
    norm_map' := by
      intro p
      change ‖zReflectFun p‖ = ‖p‖
      have h1 : ‖zReflectFun p‖ ^ 2 = ∑ i : Fin 3, (zReflectFun p i)^2 :=
        EuclideanSpace.real_norm_sq_eq _
      have h2 : ‖p‖ ^ 2 = ∑ i : Fin 3, (p i)^2 := EuclideanSpace.real_norm_sq_eq _
      have h3 : ∑ i : Fin 3, (zReflectFun p i)^2 = ∑ i : Fin 3, (p i)^2 := by
        apply Finset.sum_congr rfl
        intro i _
        fin_cases i <;> simp <;> ring
      have h4 : ‖zReflectFun p‖ ^ 2 = ‖p‖ ^ 2 := by rw [h1, h2, h3]
      have h5 : 0 ≤ ‖zReflectFun p‖ := by positivity
      have h6 : 0 ≤ ‖p‖ := by positivity
      have h7 : ‖zReflectFun p‖ = ‖p‖ := by nlinarith
      exact h7 }

@[simp] private lemma zReflect_apply (p : Point3) : zReflect p = zReflectFun p := by rfl

/-- Helper: component absolute value ≤ norm. -/
private lemma component_abs_le_norm (x : Point3) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have h_i2_le : (x i)^2 ≤ ‖x‖^2 := by
    have h2 : ‖x‖^2 = ∑ j : Fin 3, (x j)^2 := EuclideanSpace.real_norm_sq_eq x
    rw [h2]
    have h3 : (x i)^2 ≤ ∑ j : Fin 3, (x j)^2 := by
      apply Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i)
    exact h3
  have h_norm_nonneg : 0 ≤ ‖x‖ := by positivity
  nlinarith [sq_abs (x i), abs_nonneg (x i)]

/-- Helper: |x| ≥ 1/2 implies x ≥ 1/2 or x ≤ -1/2. -/
private lemma sign_from_abs_half' {x : ℝ} (h : |x| ≥ 1 / 2) : x ≥ 1 / 2 ∨ x ≤ -1 / 2 := by
  by_cases hpos : 0 ≤ x
  · have h' : |x| = x := abs_of_nonneg hpos
    rw [h'] at h
    exact Or.inl h
  · have hneg : x < 0 := by linarith
    have h' : |x| = -x := abs_of_neg hneg
    rw [h'] at h
    exact Or.inr (by linarith)

/-- Helper: affine map applied to p + t•v. -/
private lemma affine_apply (e : Point3 ≃ᵃⁱ[ℝ] Point3) (p : Point3) (t : ℝ) (v : Point3) :
    e (p + t • v) = e p + t • e.linearIsometryEquiv v := by
  have h_vadd := e.toAffineMap.map_vadd p (t • v)
  have h1 : (t • v) +ᵥ p = p + t • v := by simp [vadd_eq_add] <;> abel
  have h_smul : e.linearIsometryEquiv (t • v) = t • e.linearIsometryEquiv v :=
    e.linearIsometryEquiv.map_smul t v
  simpa [h1, vadd_eq_add, h_smul, add_comm] using h_vadd

/-- Helper: derive backward midpoint bounds from distance and direction bounds.
Given `a = (p_j + sm • u_j) - (p_i + 1/2 • v)` with `‖a‖ ≤ 2δ`,
and direction closeness `|u_j 0|, |u_j 1| ≤ 8δ`, derive bounds on
`m_j - p_i = a + 1/2 • v + (1/2 - sm) • u_j`. -/
private lemma backward_bounds_from_midpoint
    {δ : ℝ} (hδ : 0 < δ)
    {a u_j v : Point3} {sm : ℝ}
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) (hv2 : v 2 = 1)
    (ha_norm : ‖a‖ ≤ 2 * δ)
    (h_uj0 : |u_j 0| ≤ 8 * δ)
    (h_uj1 : |u_j 1| ≤ 8 * δ)
    (h_uj2_norm : |u_j 2| ≤ 1)
    (hsm_lower : -1 / 2 ≤ sm) (hsm_upper : sm ≤ 3 / 2) :
    (|(a + (1 / 2 : ℝ) • v + (1 / 2 - sm) • u_j) 0| ≤ 10 * δ) ∧
    (|(a + (1 / 2 : ℝ) • v + (1 / 2 - sm) • u_j) 1| ≤ 10 * δ) ∧
    (-1 / 2 - 2 * δ ≤ (a + (1 / 2 : ℝ) • v + (1 / 2 - sm) • u_j) 2) ∧
    ((a + (1 / 2 : ℝ) • v + (1 / 2 - sm) • u_j) 2 ≤ 3 / 2 + 2 * δ) := by
  have ha0 : |a 0| ≤ 2 * δ := by
    have h : |a 0| ≤ ‖a‖ := component_abs_le_norm a 0
    linarith [ha_norm, h]
  have ha1 : |a 1| ≤ 2 * δ := by
    have h : |a 1| ≤ ‖a‖ := component_abs_le_norm a 1
    linarith [ha_norm, h]
  have ha2 : |a 2| ≤ 2 * δ := by
    have h : |a 2| ≤ ‖a‖ := component_abs_le_norm a 2
    linarith [ha_norm, h]
  have h_diff_range : -1 ≤ 1 / 2 - sm ∧ 1 / 2 - sm ≤ 1 := by
    constructor <;> linarith
  let b : Point3 := a + (1 / 2 : ℝ) • v + (1 / 2 - sm) • u_j
  have h_b0 : b 0 = a 0 + (1 / 2 - sm) * u_j 0 := by
    simp [b, Pi.add_apply, Pi.smul_apply, hv0] <;> ring
  have h_b1 : b 1 = a 1 + (1 / 2 - sm) * u_j 1 := by
    simp [b, Pi.add_apply, Pi.smul_apply, hv1] <;> ring
  have h_b2 : b 2 = a 2 + 1 / 2 + (1 / 2 - sm) * u_j 2 := by
    simp [b, Pi.add_apply, Pi.smul_apply, hv2] <;> ring
  have h_mul0 : |(1 / 2 - sm) * u_j 0| ≤ 8 * δ := by
    rw [abs_mul]
    have h6 : |1 / 2 - sm| ≤ 1 := abs_le.mpr h_diff_range
    calc
      |1 / 2 - sm| * |u_j 0| ≤ 1 * |u_j 0| := by gcongr
      _ = |u_j 0| := by ring
      _ ≤ 8 * δ := h_uj0
  have h_mul1 : |(1 / 2 - sm) * u_j 1| ≤ 8 * δ := by
    rw [abs_mul]
    have h6 : |1 / 2 - sm| ≤ 1 := abs_le.mpr h_diff_range
    calc
      |1 / 2 - sm| * |u_j 1| ≤ 1 * |u_j 1| := by gcongr
      _ = |u_j 1| := by ring
      _ ≤ 8 * δ := h_uj1
  have h_mul2 : |(1 / 2 - sm) * u_j 2| ≤ 1 := by
    rw [abs_mul]
    have h6 : |1 / 2 - sm| ≤ 1 := abs_le.mpr h_diff_range
    have h9 : |u_j 2| ≤ 1 := h_uj2_norm
    calc
      |1 / 2 - sm| * |u_j 2| ≤ 1 * 1 := by gcongr
      _ = 1 := by norm_num
  have h_trans0 : |b 0| ≤ 10 * δ := by
    rw [h_b0]
    calc
      |a 0 + (1 / 2 - sm) * u_j 0| ≤ |a 0| + |(1 / 2 - sm) * u_j 0| := abs_add_le _ _
      _ ≤ 2 * δ + 8 * δ := by linarith
      _ = 10 * δ := by ring
  have h_trans1 : |b 1| ≤ 10 * δ := by
    rw [h_b1]
    calc
      |a 1 + (1 / 2 - sm) * u_j 1| ≤ |a 1| + |(1 / 2 - sm) * u_j 1| := abs_add_le _ _
      _ ≤ 2 * δ + 8 * δ := by linarith
      _ = 10 * δ := by ring
  have h_long_lower : -1 / 2 - 2 * δ ≤ b 2 := by
    rw [h_b2]
    have h4 : a 2 ≥ -2 * δ := by
      have h5 : |a 2| ≤ 2 * δ := ha2
      linarith [abs_le.mp h5]
    have h10 : (1 / 2 - sm) * u_j 2 ≥ -1 := by
      have h11 : |(1 / 2 - sm) * u_j 2| ≤ 1 := h_mul2
      exact (abs_le.mp h11).1
    linarith
  have h_long_upper : b 2 ≤ 3 / 2 + 2 * δ := by
    rw [h_b2]
    have h4 : a 2 ≤ 2 * δ := by
      have h5 : |a 2| ≤ 2 * δ := ha2
      linarith [abs_le.mp h5]
    have h10 : (1 / 2 - sm) * u_j 2 ≤ 1 := by
      have h11 : |(1 / 2 - sm) * u_j 2| ≤ 1 := h_mul2
      exact (abs_le.mp h11).2
    linarith
  exact ⟨h_trans0, h_trans1, h_long_lower, h_long_upper⟩

/-- Helper: same floor implies |x - y| ≤ c. -/
private lemma same_floor_abs_le {x y c : ℝ} (hc : 0 < c)
    (h : Int.floor (x / c) = Int.floor (y / c)) : |x - y| ≤ c := by
  set k : ℤ := Int.floor (x / c) with hk
  have h1 : (k : ℝ) ≤ x / c := by exact_mod_cast Int.floor_le (x / c)
  have h2 : x / c < (k + 1 : ℝ) := by exact_mod_cast Int.lt_floor_add_one (x / c)
  have h3 : (Int.floor (y / c) : ℝ) ≤ y / c := Int.floor_le (y / c)
  have h4 : y / c < (Int.floor (y / c) + 1 : ℝ) := Int.lt_floor_add_one (y / c)
  have h5 : (k : ℝ) ≤ y / c := by
    have h7 : (Int.floor (y / c) : ℝ) = (k : ℝ) := by exact_mod_cast h.symm
    rw [h7] at h3; exact h3
  have h7 : y / c < (k + 1 : ℝ) := by
    have h9 : (Int.floor (y / c) : ℝ) = (k : ℝ) := by exact_mod_cast h.symm
    rw [h9] at h4; exact h4
  have h12 : |x / c - y / c| < 1 := by
    rw [abs_lt] <;> constructor <;> linarith
  have h13 : |x - y| < c := by
    have h14 : x - y = c * (x / c - y / c) := by field_simp [hc.ne'] <;> ring
    rw [h14]
    have h15 : |c * (x / c - y / c)| = c * |x / c - y / c| := by
      rw [abs_mul, abs_of_pos hc]
    rw [h15]
    have h16 : c * |x / c - y / c| < c * (1 : ℝ) := mul_lt_mul_of_pos_left h12 hc
    have h17 : c * (1 : ℝ) = c := by ring
    rw [h17] at h16
    exact h16
  exact h13.le

/-- Constant backward conflict degree (larger than forward due to looser bounds). -/
def gwzBackwardConflictDegree (_δ : ℝ) : ℕ := 10^19

/-! ### Backward geometric bounds -/

/-- Backward direction bounds: from closest points on T_j's extended segment,
derive closeness of T_j's direction to T_i's axis. -/
private lemma backward_direction_bounds
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    {T_i T_j : Kakeya.DeltaTube δ}
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (v u_j : Point3)
    (hv : v = frame.symm.linearIsometryEquiv T_i.direction)
    (huj : u_j = frame.symm.linearIsometryEquiv T_j.direction)
    (hv2 : v 2 = 1) (hv0 : v 0 = 0) (hv1 : v 1 = 0)
    (s0 s1 : ℝ)
    (hz0_dist : dist T_i.base (T_j.base + s0 • T_j.direction) ≤ 2 * δ)
    (hz1_dist : dist (T_i.base + T_i.direction) (T_j.base + s1 • T_j.direction) ≤ 2 * δ) :
    (|u_j 0| ≤ 8 * δ) ∧ (|u_j 1| ≤ 8 * δ) ∧
    ((u_j 2 ≥ 1 / 2) ∨ (u_j 2 ≤ -1 / 2)) := by
  let c : ℝ := s1 - s0
  have h_dir_dist : dist T_i.direction (c • T_j.direction) ≤ 4 * δ := by
    have h_eq1 : T_i.direction = (T_i.base + T_i.direction) - T_i.base := by abel
    have h_eq2 : c • T_j.direction =
        (T_j.base + s1 • T_j.direction) - (T_j.base + s0 • T_j.direction) := by
      have h : (T_j.base + s1 • T_j.direction) - (T_j.base + s0 • T_j.direction) =
          s1 • T_j.direction - s0 • T_j.direction := by abel
      rw [h]
      have h2 : s1 • T_j.direction - s0 • T_j.direction = c • T_j.direction := by
        rw [←sub_smul] <;> rfl
      exact h2.symm
    rw [h_eq1, h_eq2]
    have h : dist ((T_i.base + T_i.direction) - T_i.base)
        (((T_j.base + s1 • T_j.direction) - (T_j.base + s0 • T_j.direction))) ≤
        dist (T_i.base + T_i.direction) (T_j.base + s1 • T_j.direction) +
        dist T_i.base (T_j.base + s0 • T_j.direction) := by
      have h_norm : ‖((T_i.base + T_i.direction) - T_i.base) -
          ((T_j.base + s1 • T_j.direction) - (T_j.base + s0 • T_j.direction))‖ ≤
          ‖(T_i.base + T_i.direction) - (T_j.base + s1 • T_j.direction)‖ +
          ‖T_i.base - (T_j.base + s0 • T_j.direction)‖ := by
        have h_eq : ((T_i.base + T_i.direction) - T_i.base) -
            ((T_j.base + s1 • T_j.direction) - (T_j.base + s0 • T_j.direction)) =
            ((T_i.base + T_i.direction) - (T_j.base + s1 • T_j.direction)) -
            (T_i.base - (T_j.base + s0 • T_j.direction)) := by abel
        rw [h_eq]
        exact norm_sub_le _ _
      simpa [dist_eq_norm] using h_norm
    have h_final : dist (T_i.base + T_i.direction) (T_j.base + s1 • T_j.direction) +
        dist T_i.base (T_j.base + s0 • T_j.direction) ≤ 4 * δ := by
      linarith [hz1_dist, hz0_dist]
    linarith
  have h_frame_dir_dist : dist v (c • u_j) ≤ 4 * δ := by
    have h1 : v = frame.symm.linearIsometryEquiv T_i.direction := hv
    have h2 : c • u_j = frame.symm.linearIsometryEquiv (c • T_j.direction) := by
      have h21 : u_j = frame.symm.linearIsometryEquiv T_j.direction := huj
      rw [h21, map_smul] <;> rfl
    rw [h1, h2]
    have h3 : dist (frame.symm.linearIsometryEquiv T_i.direction)
        (frame.symm.linearIsometryEquiv (c • T_j.direction)) =
        dist T_i.direction (c • T_j.direction) :=
      frame.symm.linearIsometryEquiv.dist_map _ _
    rw [h3]
    exact h_dir_dist
  have h_abs_c_lower : 1 - 4 * δ ≤ |c| := by
    have h9 : ‖c • T_j.direction‖ = |c| := by
      rw [norm_smul, T_j.direction_unit] <;> simp
    have h10 : ‖c • T_j.direction‖ ≥ ‖T_i.direction‖ - dist T_i.direction (c • T_j.direction) := by
      calc
        ‖c • T_j.direction‖
          = ‖T_i.direction - (T_i.direction - c • T_j.direction)‖ := by abel
        _ ≥ ‖T_i.direction‖ - ‖T_i.direction - c • T_j.direction‖ := by exact norm_sub_norm_le _ _
        _ = ‖T_i.direction‖ - dist T_i.direction (c • T_j.direction) := by rw [dist_eq_norm]
    rw [T_i.direction_unit, h9] at h10
    linarith
  have h_abs_c_upper : |c| ≤ 1 + 4 * δ := by
    have h9 : ‖c • T_j.direction‖ = |c| := by
      rw [norm_smul, T_j.direction_unit] <;> simp
    have h10 : ‖c • T_j.direction‖ ≤ ‖T_i.direction‖ + dist T_i.direction (c • T_j.direction) := by
      calc
        ‖c • T_j.direction‖
          = ‖T_i.direction + (c • T_j.direction - T_i.direction)‖ := by abel
        _ ≤ ‖T_i.direction‖ + ‖c • T_j.direction - T_i.direction‖ := norm_add_le _ _
        _ = ‖T_i.direction‖ + dist T_i.direction (c • T_j.direction) := by
          have h_eq : ‖c • T_j.direction - T_i.direction‖ = ‖T_i.direction - c • T_j.direction‖ := by
            rw [←norm_neg, neg_sub]
          rw [h_eq, dist_eq_norm] <;> rfl
    rw [T_i.direction_unit, h9] at h10
    linarith
  have h_c_pos : 0 < 1 - 4 * δ := by linarith [hδ1]
  have h_abs_c_pos : 0 < |c| := by linarith
  have h_norm_diff : ‖v - c • u_j‖ ≤ 4 * δ := by
    have h : dist v (c • u_j) = ‖v - c • u_j‖ := by rw [dist_eq_norm]
    rw [h] at h_frame_dir_dist
    exact h_frame_dir_dist
  have h_comp0 : |(v - c • u_j) 0| ≤ 4 * δ := by
    have h : |(v - c • u_j) 0| ≤ ‖v - c • u_j‖ := component_abs_le_norm (v - c • u_j) 0
    linarith
  have h_comp1 : |(v - c • u_j) 1| ≤ 4 * δ := by
    have h : |(v - c • u_j) 1| ≤ ‖v - c • u_j‖ := component_abs_le_norm (v - c • u_j) 1
    linarith
  have h_comp2 : |(v - c • u_j) 2| ≤ 4 * δ := by
    have h : |(v - c • u_j) 2| ≤ ‖v - c • u_j‖ := component_abs_le_norm (v - c • u_j) 2
    linarith
  have h_cu0 : |c * u_j 0| ≤ 4 * δ := by
    have h_eq : (v - c • u_j) 0 = -(c * u_j 0) := by
      simp [hv0, Pi.sub_apply, Pi.smul_apply] <;> ring
    rw [h_eq] at h_comp0
    rw [abs_neg] at h_comp0
    exact h_comp0
  have h_cu1 : |c * u_j 1| ≤ 4 * δ := by
    have h_eq : (v - c • u_j) 1 = -(c * u_j 1) := by
      simp [hv1, Pi.sub_apply, Pi.smul_apply] <;> ring
    rw [h_eq] at h_comp1
    rw [abs_neg] at h_comp1
    exact h_comp1
  have h_cu2 : |1 - c * u_j 2| ≤ 4 * δ := by
    have h_eq : (v - c • u_j) 2 = 1 - c * u_j 2 := by
      simp [hv2, Pi.sub_apply, Pi.smul_apply] <;> ring
    rw [h_eq] at h_comp2
    exact h_comp2
  have h_uj0 : |u_j 0| ≤ 8 * δ := by
    have h1 : |c * u_j 0| = |c| * |u_j 0| := by rw [abs_mul]
    rw [h1] at h_cu0
    have h2 : |u_j 0| ≤ (4 * δ) / |c| := by
      calc
        |u_j 0| = (|c| * |u_j 0|) / |c| := by
          field_simp [h_abs_c_pos.ne'] <;> ring
        _ ≤ (4 * δ) / |c| := by gcongr
    have h3 : (4 * δ) / |c| ≤ 8 * δ := by
      have h4 : |c| ≥ 1 - 4 * δ := h_abs_c_lower
      have h5 : 0 < 1 - 4 * δ := h_c_pos
      calc
        (4 * δ) / |c| ≤ (4 * δ) / (1 - 4 * δ) := by gcongr
        _ ≤ 8 * δ := by
          have h6 : δ ≤ 1 / 8 := by linarith [hδ1]
          have h7 : 0 ≤ δ := by linarith
          have h8 : 4 * δ ≤ 8 * δ * (1 - 4 * δ) := by nlinarith
          have h9 : 0 < 1 - 4 * δ := by linarith
          have h9' : 1 - 4 * δ ≠ 0 := by linarith
          calc
            (4 * δ) / (1 - 4 * δ) ≤ (8 * δ * (1 - 4 * δ)) / (1 - 4 * δ) := by gcongr
            _ = 8 * δ := by
              have h10 : (8 * δ * (1 - 4 * δ)) / (1 - 4 * δ) = 8 * δ := by
                have h11 : (8 * δ * (1 - 4 * δ)) = (8 * δ) * (1 - 4 * δ) := by ring
                rw [h11]
                exact mul_div_cancel_right₀ (8 * δ) h9'
              exact h10
    linarith
  have h_uj1 : |u_j 1| ≤ 8 * δ := by
    have h1 : |c * u_j 1| = |c| * |u_j 1| := by rw [abs_mul]
    rw [h1] at h_cu1
    have h2 : |u_j 1| ≤ (4 * δ) / |c| := by
      calc
        |u_j 1| = (|c| * |u_j 1|) / |c| := by
          field_simp [h_abs_c_pos.ne'] <;> ring
        _ ≤ (4 * δ) / |c| := by gcongr
    have h3 : (4 * δ) / |c| ≤ 8 * δ := by
      have h4 : |c| ≥ 1 - 4 * δ := h_abs_c_lower
      have h5 : 0 < 1 - 4 * δ := h_c_pos
      calc
        (4 * δ) / |c| ≤ (4 * δ) / (1 - 4 * δ) := by gcongr
        _ ≤ 8 * δ := by
          have h6 : δ ≤ 1 / 8 := by linarith [hδ1]
          have h7 : 0 ≤ δ := by linarith
          have h8 : 4 * δ ≤ 8 * δ * (1 - 4 * δ) := by nlinarith
          have h9 : 0 < 1 - 4 * δ := by linarith
          have h9' : 1 - 4 * δ ≠ 0 := by linarith
          calc
            (4 * δ) / (1 - 4 * δ) ≤ (8 * δ * (1 - 4 * δ)) / (1 - 4 * δ) := by gcongr
            _ = 8 * δ := by
              have h10 : (8 * δ * (1 - 4 * δ)) / (1 - 4 * δ) = 8 * δ := by
                have h11 : (8 * δ * (1 - 4 * δ)) = (8 * δ) * (1 - 4 * δ) := by ring
                rw [h11]
                exact mul_div_cancel_right₀ (8 * δ) h9'
              exact h10
    linarith
  have h_cu2_bounds : -4 * δ ≤ 1 - c * u_j 2 ∧ 1 - c * u_j 2 ≤ 4 * δ := by
    have h := abs_le.mp h_cu2
    exact ⟨by linarith, by linarith⟩
  have h_cu2_pos : 0 < c * u_j 2 := by linarith
  have h_abs_uj2_lower : |u_j 2| ≥ (1 - 4 * δ) / (1 + 4 * δ) := by
    have h1 : c * u_j 2 ≥ 1 - 4 * δ := by linarith [h_cu2_bounds]
    have h2 : |c| * |u_j 2| = c * u_j 2 := by
      have h3 : 0 ≤ c * u_j 2 := by linarith
      have h4 : |c * u_j 2| = c * u_j 2 := abs_of_nonneg h3
      rw [abs_mul] at h4
      exact h4
    have h5 : |c| * |u_j 2| ≥ 1 - 4 * δ := by linarith
    have h6 : |u_j 2| ≥ (1 - 4 * δ) / |c| := by
      calc
        |u_j 2| = (|c| * |u_j 2|) / |c| := by
          field_simp [h_abs_c_pos.ne'] <;> ring
        _ ≥ (1 - 4 * δ) / |c| := by gcongr
    have h7 : (1 - 4 * δ) / |c| ≥ (1 - 4 * δ) / (1 + 4 * δ) := by
      gcongr <;> linarith
    linarith
  have h_uj2_half : |u_j 2| ≥ 1 / 2 := by
    have h8 : (1 - 4 * δ) / (1 + 4 * δ) ≥ 1 / 2 := by
      have h9 : 0 < 1 + 4 * δ := by linarith
      have h10 : 1 - 4 * δ ≥ (1 + 4 * δ) / 2 := by linarith [hδ1]
      calc
        (1 - 4 * δ) / (1 + 4 * δ)
          ≥ ((1 + 4 * δ) / 2) / (1 + 4 * δ) := by gcongr
        _ = 1 / 2 := by field_simp [h9.ne'] <;> ring
    have h9 : |u_j 2| ≥ (1 - 4 * δ) / (1 + 4 * δ) := h_abs_uj2_lower
    linarith
  have h_sign : u_j 2 ≥ 1 / 2 ∨ u_j 2 ≤ -1 / 2 :=
    sign_from_abs_half' h_uj2_half
  exact ⟨h_uj0, h_uj1, h_sign⟩

/-- Backward geometric bounds: if T_i ⊆ 2*T_j, then in a frame aligned with T_i,
T_j's direction is nearly axial and its midpoint is close to T_i's axis. -/
lemma backward_conflict_geometric_bounds
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    {T_i T_j : Kakeya.DeltaTube δ}
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (p_i v p_j u_j m_j : Point3)
    (hpi : p_i = frame.symm T_i.base)
    (hv : v = frame.symm.linearIsometryEquiv T_i.direction)
    (hv2 : v 2 = 1) (hv0 : v 0 = 0) (hv1 : v 1 = 0)
    (hpj : p_j = frame.symm T_j.base)
    (huj : u_j = frame.symm.linearIsometryEquiv T_j.direction)
    (hmj : m_j = p_j + (1 / 2 : ℝ) • u_j)
    (h : T_i.carrier ⊆ wz2PaperCenteredDilatedCarrier (2 : ℝ) T_j) :
    (|u_j 0| ≤ 8 * δ) ∧ (|u_j 1| ≤ 8 * δ) ∧
    ((u_j 2 ≥ 1 / 2) ∨ (u_j 2 ≤ -1 / 2)) ∧
    (|(m_j - p_i) 0| ≤ 10 * δ) ∧ (|(m_j - p_i) 1| ≤ 10 * δ) ∧
    (-1 / 2 - 2 * δ ≤ (m_j - p_i) 2) ∧
    ((m_j - p_i) 2 ≤ 3 / 2 + 2 * δ) := by
  let S_ext : Set Point3 := extendedSegment T_j
  have hS_cp : IsCompact S_ext := by
    simp [S_ext, extendedSegment]
    apply IsCompact.image isCompact_Icc
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hS_nonempty : S_ext.Nonempty :=
    ⟨T_j.base, ⟨0, by norm_num, by simp⟩⟩
  have h_carrier_def : T_i.carrier = Metric.cthickening δ (unitSegment T_i.base T_i.direction) := by rfl
  have h_dist_self : ∀ (x : Point3), dist x x ≤ δ := by
    intro x
    have h : dist x x = 0 := dist_self x
    rw [h] <;> linarith
  have h_pi_in : T_i.base ∈ T_i.carrier := by
    rw [h_carrier_def]
    exact Metric.mem_cthickening_of_dist_le T_i.base T_i.base δ _
      ⟨0, by norm_num, by simp⟩ (h_dist_self T_i.base)
  have h_pui_in : T_i.base + T_i.direction ∈ T_i.carrier := by
    rw [h_carrier_def]
    exact Metric.mem_cthickening_of_dist_le (T_i.base + T_i.direction) (T_i.base + T_i.direction) δ _
      ⟨1, by norm_num, by simp⟩ (h_dist_self _)
  have h_mi_in : T_i.base + (1 / 2 : ℝ) • T_i.direction ∈ T_i.carrier := by
    rw [h_carrier_def]
    exact Metric.mem_cthickening_of_dist_le (T_i.base + (1 / 2 : ℝ) • T_i.direction)
      (T_i.base + (1 / 2 : ℝ) • T_i.direction) δ _
      ⟨1 / 2, by norm_num, by simp⟩ (h_dist_self _)
  have h1 : Metric.infDist T_i.base S_ext ≤ 2 * δ :=
    dilation_infDist_extended hδ.le T_j T_i.base (h h_pi_in)
  have h2 : Metric.infDist (T_i.base + T_i.direction) S_ext ≤ 2 * δ :=
    dilation_infDist_extended hδ.le T_j (T_i.base + T_i.direction) (h h_pui_in)
  have h3 : Metric.infDist (T_i.base + (1 / 2 : ℝ) • T_i.direction) S_ext ≤ 2 * δ :=
    dilation_infDist_extended hδ.le T_j (T_i.base + (1 / 2 : ℝ) • T_i.direction) (h h_mi_in)
  rcases hS_cp.exists_infDist_eq_dist hS_nonempty T_i.base with ⟨z0, hz0, hz0_eq⟩
  rcases hS_cp.exists_infDist_eq_dist hS_nonempty (T_i.base + T_i.direction) with ⟨z1, hz1, hz1_eq⟩
  rcases hS_cp.exists_infDist_eq_dist hS_nonempty (T_i.base + (1 / 2 : ℝ) • T_i.direction) with ⟨zm, hzm, hzm_eq⟩
  have hz0_dist : dist T_i.base z0 ≤ 2 * δ := by rw [←hz0_eq]; exact h1
  have hz1_dist : dist (T_i.base + T_i.direction) z1 ≤ 2 * δ := by rw [←hz1_eq]; exact h2
  have hzm_dist : dist (T_i.base + (1 / 2 : ℝ) • T_i.direction) zm ≤ 2 * δ := by rw [←hzm_eq]; exact h3
  rcases hz0 with ⟨s0, hs0, rfl⟩
  rcases hz1 with ⟨s1, hs1, rfl⟩
  rcases hzm with ⟨sm, hsm, rfl⟩
  have h_dir_bounds := backward_direction_bounds hδ hδ1 frame v u_j hv huj hv2 hv0 hv1 s0 s1 hz0_dist hz1_dist
  have h_uj0 : |u_j 0| ≤ 8 * δ := h_dir_bounds.1
  have h_uj1 : |u_j 1| ≤ 8 * δ := h_dir_bounds.2.1
  have h_sign : u_j 2 ≥ 1 / 2 ∨ u_j 2 ≤ -1 / 2 := h_dir_bounds.2.2
  have h_mid_dist : dist (p_i + (1 / 2 : ℝ) • v) (p_j + sm • u_j) ≤ 2 * δ := by
    have h_map_i := affine_apply frame.symm T_i.base (1 / 2 : ℝ) T_i.direction
    have h_map_j := affine_apply frame.symm T_j.base sm T_j.direction
    have h1 : frame.symm (T_i.base + (1 / 2 : ℝ) • T_i.direction) = p_i + (1 / 2 : ℝ) • v := by
      calc
        frame.symm (T_i.base + (1 / 2 : ℝ) • T_i.direction)
          = frame.symm T_i.base + (1 / 2 : ℝ) • frame.symm.linearIsometryEquiv T_i.direction := h_map_i
        _ = p_i + (1 / 2 : ℝ) • frame.symm.linearIsometryEquiv T_i.direction := by rw [hpi]
        _ = p_i + (1 / 2 : ℝ) • v := by rw [hv]
    have h2 : frame.symm (T_j.base + sm • T_j.direction) = p_j + sm • u_j := by
      calc
        frame.symm (T_j.base + sm • T_j.direction)
          = frame.symm T_j.base + sm • frame.symm.linearIsometryEquiv T_j.direction := h_map_j
        _ = p_j + sm • frame.symm.linearIsometryEquiv T_j.direction := by rw [hpj]
        _ = p_j + sm • u_j := by rw [huj]
    have h3 : dist (frame.symm (T_i.base + (1 / 2 : ℝ) • T_i.direction))
        (frame.symm (T_j.base + sm • T_j.direction)) =
        dist (T_i.base + (1 / 2 : ℝ) • T_i.direction) (T_j.base + sm • T_j.direction) :=
      frame.symm.dist_map _ _
    rw [h1, h2] at h3
    rw [h3]
    exact hzm_dist
  let x : Point3 := p_i + (1 / 2 : ℝ) • v
  let y : Point3 := p_j + sm • u_j
  let a : Point3 := y - x
  have h7 : dist x y = ‖x - y‖ := dist_eq_norm x y
  have h_norm_xy : ‖x - y‖ ≤ 2 * δ := h7 ▸ h_mid_dist
  have h9 : ‖y - x‖ = ‖x - y‖ :=
    Eq.trans (Eq.trans (dist_eq_norm y x).symm (dist_comm y x)) (dist_eq_norm x y)
  have ha_norm : ‖a‖ ≤ 2 * δ := h9.symm ▸ h_norm_xy
  have h_uj2_norm : |u_j 2| ≤ 1 := by
    have h : ‖u_j‖ = 1 := by
      rw [huj]
      have h := frame.symm.linearIsometryEquiv.norm_map T_j.direction
      rw [h, T_j.direction_unit]
    have h2 : |u_j 2| ≤ ‖u_j‖ := component_abs_le_norm u_j 2
    rw [h] at h2
    exact h2
  let b : Point3 := a + (1 / 2 : ℝ) • v + (1 / 2 - sm) • u_j
  have h_bounds := backward_bounds_from_midpoint hδ hv0 hv1 hv2 ha_norm h_uj0 h_uj1 h_uj2_norm hsm.1 hsm.2
  have h_mj_eq : m_j - p_i = b := by
    ext k
    have h_lhs : (m_j - p_i) k = m_j k - p_i k := by
      simp [Pi.sub_apply]
    have h_rhs : b k = a k + (1 / 2 : ℝ) * v k + (1 / 2 - sm) * u_j k := by
      have h_b : b = a + (1 / 2 : ℝ) • v + (1 / 2 - sm) • u_j := by rfl
      rw [h_b]
      simp [Pi.add_apply, Pi.smul_apply] <;> ring
    rw [h_lhs, h_rhs]
    have h_mj_k : m_j k = p_j k + (1 / 2 : ℝ) * u_j k := by
      rw [hmj]
      simp [Pi.add_apply, Pi.smul_apply] <;> ring
    have h_a_k : a k = (p_j + sm • u_j) k - (p_i + (1 / 2 : ℝ) • v) k := by
      have h_a1 : a = y - x := by rfl
      rw [h_a1]
      have h : (y - x) k = y k - x k := by simp [Pi.sub_apply]
      rw [h]
      <;> rfl
    rw [h_mj_k, h_a_k]
    simp [Pi.add_apply, Pi.smul_apply] <;> ring
  have h_mj0 : |(m_j - p_i) 0| ≤ 10 * δ := by
    rw [h_mj_eq]
    exact h_bounds.1
  have h_mj1 : |(m_j - p_i) 1| ≤ 10 * δ := by
    rw [h_mj_eq]
    exact h_bounds.2.1
  have h_mj2_lower : -1 / 2 - 2 * δ ≤ (m_j - p_i) 2 := by
    rw [h_mj_eq]
    exact h_bounds.2.2.1
  have h_mj2_upper : (m_j - p_i) 2 ≤ 3 / 2 + 2 * δ := by
    rw [h_mj_eq]
    exact h_bounds.2.2.2
  exact ⟨h_uj0, h_uj1, h_sign, h_mj0, h_mj1, h_mj2_lower, h_mj2_upper⟩

/-! ### Backward conflict degree bound -/

/-- Constant backward conflict degree bound using TightDistinctness grid approach. -/
lemma gwz_backward_conflict_degree_bound
    {δ : ℝ} (hδ : 0 < δ) (hδ_small : δ ≤ 1 / 100)
    {source : STubeFamily δ}
    (hdistinct : source.IsEssentiallyDistinct)
    (i : Fin source.card) :
    (Finset.univ.filter fun j =>
      (source.tube i).carrier ⊆
        wz2PaperCenteredDilatedCarrier (2 : ℝ) (source.tube j)).card
      ≤ gwzBackwardConflictDegree δ := by
  let T_i := source.tube i
  let indices : Finset (Fin source.card) :=
    Finset.univ.filter fun j =>
      (source.tube i).carrier ⊆ wz2PaperCenteredDilatedCarrier (2 : ℝ) (source.tube j)

  rcases frame_of_axis T_i.direction T_i.direction_unit with ⟨e1, e2, frame, hf2, hf0, hf1⟩

  let p_i : Point3 := frame.symm T_i.base
  let v : Point3 := frame.symm.linearIsometryEquiv T_i.direction
  let p (j : Fin source.card) : Point3 := frame.symm (source.tube j).base
  let u (j : Fin source.card) : Point3 := frame.symm.linearIsometryEquiv (source.tube j).direction
  let m (j : Fin source.card) : Point3 := p j + (1 / 2 : ℝ) • u j

  have h_capsule_lower : CapsuleLowerBound := capsule_lower_bound_instantiation
  have h_capsule_upper : CapsuleUpperBound := capsule_upper_bound_instantiation

  have h_params : ∀ j ∈ indices,
      |u j 0| ≤ 8 * δ ∧ |u j 1| ≤ 8 * δ ∧
      ((u j 2 ≥ 1 / 2) ∨ (u j 2 ≤ -1 / 2)) ∧
      |(m j - p_i) 0| ≤ 10 * δ ∧ |(m j - p_i) 1| ≤ 10 * δ ∧
      -1 / 2 - 2 * δ ≤ (m j - p_i) 2 ∧ (m j - p_i) 2 ≤ 3 / 2 + 2 * δ := by
    intro j hj
    have h_contain : (source.tube i).carrier ⊆ wz2PaperCenteredDilatedCarrier (2 : ℝ) (source.tube j) :=
      (Finset.mem_filter.mp hj).2
    exact backward_conflict_geometric_bounds hδ (by linarith) frame p_i v (p j) (u j) (m j)
      rfl rfl hf2 hf0 hf1 rfl rfl rfl h_contain

  let c_trans : ℝ := δ / 200
  let c_long : ℝ := 1 / 3200
  have hc_trans_pos : 0 < c_trans := by positivity
  have hc_long_pos : 0 < c_long := by positivity

  let cell (j : Fin source.card) : ℤ × ℤ × ℤ × ℤ × ℤ :=
    (Int.floor ((u j 0) / c_trans),
     Int.floor ((u j 1) / c_trans),
     Int.floor (((m j - p_i) 0) / c_trans),
     Int.floor (((m j - p_i) 1) / c_trans),
     Int.floor (((m j - p_i) 2) / c_long))

  let indices_pos : Finset (Fin source.card) := indices.filter fun j => u j 2 ≥ 1 / 2
  let indices_neg : Finset (Fin source.card) := indices.filter fun j => u j 2 ≤ -1 / 2

  have h_cover : indices ⊆ indices_pos ∪ indices_neg := by
    intro j hj
    have h := (h_params j hj).2.2.1
    rcases h with (h | h)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hj, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hj, h⟩)

  have h_same_cell_diff : ∀ j1 j2, cell j1 = cell j2 →
      |(u j1 - u j2) 0| ≤ δ / 200 ∧
      |(u j1 - u j2) 1| ≤ δ / 200 ∧
      |(m j1 - m j2) 0| ≤ δ / 200 ∧
      |(m j1 - m j2) 1| ≤ δ / 200 ∧
      |(m j1 - m j2) 2| ≤ 1 / 3200 := by
    intro j1 j2 hcell
    have h0 := congr_arg Prod.fst hcell
    have h1 := congr_arg (Prod.fst ∘ Prod.snd) hcell
    have h2 := congr_arg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hcell
    have h3 := congr_arg (Prod.fst ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd) hcell
    have h4 := congr_arg (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd) hcell
    have d0 : |(u j1 0) - (u j2 0)| ≤ c_trans := same_floor_abs_le hc_trans_pos h0
    have d1 : |(u j1 1) - (u j2 1)| ≤ c_trans := same_floor_abs_le hc_trans_pos h1
    have dm0 : |((m j1 - p_i) 0) - ((m j2 - p_i) 0)| ≤ c_trans := same_floor_abs_le hc_trans_pos h2
    have dm1 : |((m j1 - p_i) 1) - ((m j2 - p_i) 1)| ≤ c_trans := same_floor_abs_le hc_trans_pos h3
    have dm2 : |((m j1 - p_i) 2) - ((m j2 - p_i) 2)| ≤ c_long := same_floor_abs_le hc_long_pos h4
    have h_m0 : |(m j1 - m j2) 0| ≤ δ / 200 := by
      have h_eq : (m j1 - m j2) 0 = (m j1 - p_i) 0 - (m j2 - p_i) 0 := by
        simp [Pi.sub_apply] <;> ring
      rw [h_eq] <;> simpa [c_trans] using dm0
    have h_m1 : |(m j1 - m j2) 1| ≤ δ / 200 := by
      have h_eq : (m j1 - m j2) 1 = (m j1 - p_i) 1 - (m j2 - p_i) 1 := by
        simp [Pi.sub_apply] <;> ring
      rw [h_eq] <;> simpa [c_trans] using dm1
    have h_m2 : |(m j1 - m j2) 2| ≤ 1 / 3200 := by
      have h_eq : (m j1 - m j2) 2 = (m j1 - p_i) 2 - (m j2 - p_i) 2 := by
        simp [Pi.sub_apply] <;> ring
      rw [h_eq] <;> simpa [c_long] using dm2
    have h_u0 : |(u j1 - u j2) 0| ≤ δ / 200 := by
      have h_eq : (u j1 - u j2) 0 = (u j1 0) - (u j2 0) := by simp [Pi.sub_apply] <;> ring
      rw [h_eq] <;> simpa [c_trans] using d0
    have h_u1 : |(u j1 - u j2) 1| ≤ δ / 200 := by
      have h_eq : (u j1 - u j2) 1 = (u j1 1) - (u j2 1) := by simp [Pi.sub_apply] <;> ring
      rw [h_eq] <;> simpa [c_trans] using d1
    exact ⟨h_u0, h_u1, h_m0, h_m1, h_m2⟩

  have h_pos_inj : Set.InjOn cell indices_pos := by
    intro j1 hj1 j2 hj2 hcell
    by_contra hne
    have h_u1_pos : u j1 2 ≥ 1 / 2 := (Finset.mem_filter.mp hj1).2
    have h_u2_pos : u j2 2 ≥ 1 / 2 := (Finset.mem_filter.mp hj2).2
    have h_j1_in : j1 ∈ indices := (Finset.mem_filter.mp hj1).1
    have h_j2_in : j2 ∈ indices := (Finset.mem_filter.mp hj2).1
    have h2_params := h_params j2 h_j2_in
    have h_u2_0 : |(u j2 0)| ≤ 8 * δ := h2_params.1
    have h_u2_1 : |(u j2 1)| ≤ 8 * δ := h2_params.2.1
    have h_diffs := h_same_cell_diff j1 j2 hcell
    have hm1 : m j1 = frame.symm ((source.tube j1).base + (1 / 2 : ℝ) • (source.tube j1).direction) := by
      have h_aff := affine_apply frame.symm (source.tube j1).base (1 / 2 : ℝ) (source.tube j1).direction
      have h_def : m j1 = frame.symm (source.tube j1).base + (1 / 2 : ℝ) • frame.symm.linearIsometryEquiv (source.tube j1).direction := by rfl
      rw [h_def]
      exact h_aff.symm
    have hm2 : m j2 = frame.symm ((source.tube j2).base + (1 / 2 : ℝ) • (source.tube j2).direction) := by
      have h_aff := affine_apply frame.symm (source.tube j2).base (1 / 2 : ℝ) (source.tube j2).direction
      have h_def : m j2 = frame.symm (source.tube j2).base + (1 / 2 : ℝ) • frame.symm.linearIsometryEquiv (source.tube j2).direction := by rfl
      rw [h_def]
      exact h_aff.symm
    have h_nd : ¬ (source.tube j1).EssentiallyDistinct (source.tube j2) :=
      close_params_not_distinct hδ (by linarith) frame
        (m j1) (m j2) (u j1) (u j2)
        hm1 hm2 rfl rfl
        h_u1_pos h_u2_pos h_u2_0 h_u2_1
        h_diffs.2.2.1 h_diffs.2.2.2.1 h_diffs.2.2.2.2 h_diffs.1 h_diffs.2.1
        h_capsule_lower h_capsule_upper
    exact h_nd (hdistinct j1 j2 hne)

  -- Negative case: reflect z-coordinate
  let frame' : Point3 ≃ᵃⁱ[ℝ] Point3 := zReflect.toAffineIsometryEquiv.trans frame
  let u' (j : Fin source.card) : Point3 := frame'.symm.linearIsometryEquiv (source.tube j).direction
  let m' (j : Fin source.card) : Point3 := frame'.symm ((source.tube j).base + (1 / 2 : ℝ) • (source.tube j).direction)

  have h_frame'_symm : ∀ (x : Point3), frame'.symm x = zReflect (frame.symm x) := by
    intro x; rfl
  have h_frame'_lin : ∀ (v : Point3), frame'.symm.linearIsometryEquiv v = zReflect (frame.symm.linearIsometryEquiv v) := by
    intro v; rfl

  have h_u'_eq : ∀ j, u' j = zReflect (u j) := by
    intro j
    have h : u' j = frame'.symm.linearIsometryEquiv (source.tube j).direction := by rfl
    rw [h, h_frame'_lin] <;> rfl
  have h_m'_eq : ∀ j, m' j = zReflect (m j) := by
    intro j
    have h : m' j = frame'.symm ((source.tube j).base + (1 / 2 : ℝ) • (source.tube j).direction) := by rfl
    rw [h, h_frame'_symm]
    have h2 : frame.symm ((source.tube j).base + (1 / 2 : ℝ) • (source.tube j).direction) = m j := by
      have h_aff := affine_apply frame.symm (source.tube j).base (1 / 2 : ℝ) (source.tube j).direction
      have h_def : m j = frame.symm (source.tube j).base + (1 / 2 : ℝ) • frame.symm.linearIsometryEquiv (source.tube j).direction := by rfl
      calc frame.symm ((source.tube j).base + (1 / 2 : ℝ) • (source.tube j).direction)
        = frame.symm (source.tube j).base + (1 / 2 : ℝ) • frame.symm.linearIsometryEquiv (source.tube j).direction := h_aff
      _ = m j := h_def.symm
    rw [h2]

  have h_neg_inj : Set.InjOn cell indices_neg := by
    intro j1 hj1 j2 hj2 hcell
    by_contra hne
    have h_u1_neg : u j1 2 ≤ -1 / 2 := (Finset.mem_filter.mp hj1).2
    have h_u2_neg : u j2 2 ≤ -1 / 2 := (Finset.mem_filter.mp hj2).2
    have h_j1_in : j1 ∈ indices := (Finset.mem_filter.mp hj1).1
    have h_j2_in : j2 ∈ indices := (Finset.mem_filter.mp hj2).1
    have h2_params := h_params j2 h_j2_in
    have h_zr0 : ∀ (x : Point3), (zReflect x) 0 = x 0 := by
      intro x
      have h_eq : zReflect x = zReflectFun x := by simp [zReflect]
      rw [h_eq]
      exact zReflectFun_0 x
    have h_zr1 : ∀ (x : Point3), (zReflect x) 1 = x 1 := by
      intro x
      have h_eq : zReflect x = zReflectFun x := by simp [zReflect]
      rw [h_eq]
      exact zReflectFun_1 x
    have h_zr2 : ∀ (x : Point3), (zReflect x) 2 = - (x 2) := by
      intro x
      have h_eq : zReflect x = zReflectFun x := by simp [zReflect]
      rw [h_eq]
      exact zReflectFun_2 x
    have h_u2_0 : |(u' j2 0)| ≤ 8 * δ := by
      have h : (u' j2 0) = (u j2 0) := by rw [h_u'_eq j2, h_zr0]
      rw [h] <;> linarith [h2_params.1]
    have h_u2_1 : |(u' j2 1)| ≤ 8 * δ := by
      have h : (u' j2 1) = (u j2 1) := by rw [h_u'_eq j2, h_zr1]
      rw [h] <;> linarith [h2_params.2.1]
    have h_u1_pos' : u' j1 2 ≥ 1 / 2 := by
      have h : (u' j1 2) = - (u j1 2) := by rw [h_u'_eq j1, h_zr2]
      rw [h] <;> linarith
    have h_u2_pos' : u' j2 2 ≥ 1 / 2 := by
      have h : (u' j2 2) = - (u j2 2) := by rw [h_u'_eq j2, h_zr2]
      rw [h] <;> linarith
    have h_diffs := h_same_cell_diff j1 j2 hcell
    have h_m0' : |(m' j1 - m' j2) 0| ≤ δ / 200 := by
      have h_sub : m' j1 - m' j2 = zReflect (m j1 - m j2) := by
        rw [h_m'_eq j1, h_m'_eq j2, ←zReflect.map_sub]
      have h : (m' j1 - m' j2) 0 = (m j1 - m j2) 0 := by rw [h_sub, h_zr0]
      rw [h]; exact h_diffs.2.2.1
    have h_m1' : |(m' j1 - m' j2) 1| ≤ δ / 200 := by
      have h_sub : m' j1 - m' j2 = zReflect (m j1 - m j2) := by
        rw [h_m'_eq j1, h_m'_eq j2, ←zReflect.map_sub]
      have h : (m' j1 - m' j2) 1 = (m j1 - m j2) 1 := by rw [h_sub, h_zr1]
      rw [h]; exact h_diffs.2.2.2.1
    have h_m2' : |(m' j1 - m' j2) 2| ≤ 1 / 3200 := by
      have h_sub : m' j1 - m' j2 = zReflect (m j1 - m j2) := by
        rw [h_m'_eq j1, h_m'_eq j2, ←zReflect.map_sub]
      have h : (m' j1 - m' j2) 2 = -((m j1 - m j2) 2) := by
        rw [h_sub, h_zr2] <;> ring
      rw [h, abs_neg]; exact h_diffs.2.2.2.2
    have h_u0' : |(u' j1 - u' j2) 0| ≤ δ / 200 := by
      have h_sub : u' j1 - u' j2 = zReflect (u j1 - u j2) := by
        rw [h_u'_eq j1, h_u'_eq j2, ←zReflect.map_sub]
      have h : (u' j1 - u' j2) 0 = (u j1 - u j2) 0 := by rw [h_sub, h_zr0]
      rw [h]; exact h_diffs.1
    have h_u1' : |(u' j1 - u' j2) 1| ≤ δ / 200 := by
      have h_sub : u' j1 - u' j2 = zReflect (u j1 - u j2) := by
        rw [h_u'_eq j1, h_u'_eq j2, ←zReflect.map_sub]
      have h : (u' j1 - u' j2) 1 = (u j1 - u j2) 1 := by rw [h_sub, h_zr1]
      rw [h]; exact h_diffs.2.1
    have h_nd : ¬ (source.tube j1).EssentiallyDistinct (source.tube j2) :=
      close_params_not_distinct hδ (by linarith) frame'
        (m' j1) (m' j2) (u' j1) (u' j2)
        rfl rfl rfl rfl
        h_u1_pos' h_u2_pos' h_u2_0 h_u2_1
        h_m0' h_m1' h_m2' h_u0' h_u1'
        h_capsule_lower h_capsule_upper
    exact h_nd (hdistinct j1 j2 hne)

  have h_cell_bounds : ∀ j ∈ indices,
      Int.floor ((u j 0) / c_trans) ∈ Finset.Icc (-1600 : ℤ) 1600 ∧
      Int.floor ((u j 1) / c_trans) ∈ Finset.Icc (-1600 : ℤ) 1600 ∧
      Int.floor (((m j - p_i) 0) / c_trans) ∈ Finset.Icc (-2000 : ℤ) 2000 ∧
      Int.floor (((m j - p_i) 1) / c_trans) ∈ Finset.Icc (-2000 : ℤ) 2000 ∧
      Int.floor (((m j - p_i) 2) / c_long) ∈ Finset.Icc (-1664 : ℤ) 4864 := by
    intro j hj
    have h_p := h_params j hj
    have h_u0_l : -8 * δ ≤ u j 0 := by linarith [abs_le.mp h_p.1]
    have h_u0_u : u j 0 ≤ 8 * δ := by linarith [abs_le.mp h_p.1]
    have h_u1_l : -8 * δ ≤ u j 1 := by linarith [abs_le.mp h_p.2.1]
    have h_u1_u : u j 1 ≤ 8 * δ := by linarith [abs_le.mp h_p.2.1]
    have h_m0_l : -10 * δ ≤ (m j - p_i) 0 := by linarith [abs_le.mp h_p.2.2.2.1]
    have h_m0_u : (m j - p_i) 0 ≤ 10 * δ := by linarith [abs_le.mp h_p.2.2.2.1]
    have h_m1_l : -10 * δ ≤ (m j - p_i) 1 := by linarith [abs_le.mp h_p.2.2.2.2.1]
    have h_m1_u : (m j - p_i) 1 ≤ 10 * δ := by linarith [abs_le.mp h_p.2.2.2.2.1]
    have h_m2_l : -1 / 2 - 2 * δ ≤ (m j - p_i) 2 := h_p.2.2.2.2.2.1
    have h_m2_u : (m j - p_i) 2 ≤ 3 / 2 + 2 * δ := h_p.2.2.2.2.2.2
    have h_div_u0_l : (-1600 : ℝ) ≤ (u j 0) / c_trans := by
      have h : c_trans = δ / 200 := by rfl
      rw [h]
      calc (u j 0) / (δ / 200)
        ≥ (-8 * δ) / (δ / 200) := by gcongr
      _ = -1600 := by field_simp [hδ.ne'] <;> ring
    have h_div_u0_u : (u j 0) / c_trans ≤ (1600 : ℝ) := by
      have h : c_trans = δ / 200 := by rfl
      rw [h]
      calc (u j 0) / (δ / 200)
        ≤ (8 * δ) / (δ / 200) := by gcongr
      _ = 1600 := by field_simp [hδ.ne'] <;> ring
    have h_div_u1_l : (-1600 : ℝ) ≤ (u j 1) / c_trans := by
      have h : c_trans = δ / 200 := by rfl
      rw [h]
      calc (u j 1) / (δ / 200)
        ≥ (-8 * δ) / (δ / 200) := by gcongr
      _ = -1600 := by field_simp [hδ.ne'] <;> ring
    have h_div_u1_u : (u j 1) / c_trans ≤ (1600 : ℝ) := by
      have h : c_trans = δ / 200 := by rfl
      rw [h]
      calc (u j 1) / (δ / 200)
        ≤ (8 * δ) / (δ / 200) := by gcongr
      _ = 1600 := by field_simp [hδ.ne'] <;> ring
    have h_div_m0_l : (-2000 : ℝ) ≤ ((m j - p_i) 0) / c_trans := by
      have h : c_trans = δ / 200 := by rfl
      rw [h]
      calc ((m j - p_i) 0) / (δ / 200)
        ≥ (-10 * δ) / (δ / 200) := by gcongr
      _ = -2000 := by field_simp [hδ.ne'] <;> ring
    have h_div_m0_u : ((m j - p_i) 0) / c_trans ≤ (2000 : ℝ) := by
      have h : c_trans = δ / 200 := by rfl
      rw [h]
      calc ((m j - p_i) 0) / (δ / 200)
        ≤ (10 * δ) / (δ / 200) := by gcongr
      _ = 2000 := by field_simp [hδ.ne'] <;> ring
    have h_div_m1_l : (-2000 : ℝ) ≤ ((m j - p_i) 1) / c_trans := by
      have h : c_trans = δ / 200 := by rfl
      rw [h]
      calc ((m j - p_i) 1) / (δ / 200)
        ≥ (-10 * δ) / (δ / 200) := by gcongr
      _ = -2000 := by field_simp [hδ.ne'] <;> ring
    have h_div_m1_u : ((m j - p_i) 1) / c_trans ≤ (2000 : ℝ) := by
      have h : c_trans = δ / 200 := by rfl
      rw [h]
      calc ((m j - p_i) 1) / (δ / 200)
        ≤ (10 * δ) / (δ / 200) := by gcongr
      _ = 2000 := by field_simp [hδ.ne'] <;> ring
    have h_div_m2_l : (-1664 : ℝ) ≤ ((m j - p_i) 2) / c_long := by
      have h : c_long = 1 / 3200 := by rfl
      rw [h]
      have h' : -1 / 2 - 2 * δ ≤ (m j - p_i) 2 := h_m2_l
      have h'' : (-1664 : ℝ) ≤ (-1 / 2 - 2 * δ) / (1 / 3200 : ℝ) := by
        have hδ' : δ ≤ 1 / 100 := hδ_small
        field_simp <;> linarith
      linarith
    have h_div_m2_u : ((m j - p_i) 2) / c_long ≤ (4864 : ℝ) := by
      have h : c_long = 1 / 3200 := by rfl
      rw [h]
      have h' : (m j - p_i) 2 ≤ 3 / 2 + 2 * δ := h_m2_u
      have h'' : (3 / 2 + 2 * δ) / (1 / 3200 : ℝ) ≤ (4864 : ℝ) := by
        have hδ' : δ ≤ 1 / 100 := hδ_small
        field_simp <;> linarith
      linarith
    have h_fl1 : Int.floor ((u j 0) / c_trans) ∈ Finset.Icc (-1600 : ℤ) 1600 := by
      have h_lower : (-1600 : ℤ) ≤ Int.floor ((u j 0) / c_trans) := by
        have h : ((-1600 : ℤ) : ℝ) ≤ (u j 0) / c_trans := by exact_mod_cast h_div_u0_l
        exact (Int.le_floor).mpr h
      have h_upper : Int.floor ((u j 0) / c_trans) ≤ (1600 : ℤ) := by
        have h : (Int.floor ((u j 0) / c_trans) : ℝ) ≤ (u j 0) / c_trans := Int.floor_le _
        have h' : (Int.floor ((u j 0) / c_trans) : ℝ) ≤ (1600 : ℝ) := by linarith
        exact_mod_cast h'
      exact Finset.mem_Icc.mpr ⟨h_lower, h_upper⟩
    have h_fl2 : Int.floor ((u j 1) / c_trans) ∈ Finset.Icc (-1600 : ℤ) 1600 := by
      have h_lower : (-1600 : ℤ) ≤ Int.floor ((u j 1) / c_trans) := by
        have h : ((-1600 : ℤ) : ℝ) ≤ (u j 1) / c_trans := by exact_mod_cast h_div_u1_l
        exact (Int.le_floor).mpr h
      have h_upper : Int.floor ((u j 1) / c_trans) ≤ (1600 : ℤ) := by
        have h : (Int.floor ((u j 1) / c_trans) : ℝ) ≤ (u j 1) / c_trans := Int.floor_le _
        have h' : (Int.floor ((u j 1) / c_trans) : ℝ) ≤ (1600 : ℝ) := by linarith
        exact_mod_cast h'
      exact Finset.mem_Icc.mpr ⟨h_lower, h_upper⟩
    have h_fl3 : Int.floor (((m j - p_i) 0) / c_trans) ∈ Finset.Icc (-2000 : ℤ) 2000 := by
      have h_lower : (-2000 : ℤ) ≤ Int.floor (((m j - p_i) 0) / c_trans) := by
        have h : ((-2000 : ℤ) : ℝ) ≤ ((m j - p_i) 0) / c_trans := by exact_mod_cast h_div_m0_l
        exact (Int.le_floor).mpr h
      have h_upper : Int.floor (((m j - p_i) 0) / c_trans) ≤ (2000 : ℤ) := by
        have h : (Int.floor (((m j - p_i) 0) / c_trans) : ℝ) ≤ ((m j - p_i) 0) / c_trans := Int.floor_le _
        have h' : (Int.floor (((m j - p_i) 0) / c_trans) : ℝ) ≤ (2000 : ℝ) := by linarith
        exact_mod_cast h'
      exact Finset.mem_Icc.mpr ⟨h_lower, h_upper⟩
    have h_fl4 : Int.floor (((m j - p_i) 1) / c_trans) ∈ Finset.Icc (-2000 : ℤ) 2000 := by
      have h_lower : (-2000 : ℤ) ≤ Int.floor (((m j - p_i) 1) / c_trans) := by
        have h : ((-2000 : ℤ) : ℝ) ≤ ((m j - p_i) 1) / c_trans := by exact_mod_cast h_div_m1_l
        exact (Int.le_floor).mpr h
      have h_upper : Int.floor (((m j - p_i) 1) / c_trans) ≤ (2000 : ℤ) := by
        have h : (Int.floor (((m j - p_i) 1) / c_trans) : ℝ) ≤ ((m j - p_i) 1) / c_trans := Int.floor_le _
        have h' : (Int.floor (((m j - p_i) 1) / c_trans) : ℝ) ≤ (2000 : ℝ) := by linarith
        exact_mod_cast h'
      exact Finset.mem_Icc.mpr ⟨h_lower, h_upper⟩
    have h_fl5 : Int.floor (((m j - p_i) 2) / c_long) ∈ Finset.Icc (-1664 : ℤ) 4864 := by
      have h_lower : (-1664 : ℤ) ≤ Int.floor (((m j - p_i) 2) / c_long) := by
        have h : ((-1664 : ℤ) : ℝ) ≤ ((m j - p_i) 2) / c_long := by exact_mod_cast h_div_m2_l
        exact (Int.le_floor).mpr h
      have h_upper : Int.floor (((m j - p_i) 2) / c_long) ≤ (4864 : ℤ) := by
        have h : (Int.floor (((m j - p_i) 2) / c_long) : ℝ) ≤ ((m j - p_i) 2) / c_long := Int.floor_le _
        have h' : (Int.floor (((m j - p_i) 2) / c_long) : ℝ) ≤ (4864 : ℝ) := by linarith
        exact_mod_cast h'
      exact Finset.mem_Icc.mpr ⟨h_lower, h_upper⟩
    exact ⟨h_fl1, h_fl2, h_fl3, h_fl4, h_fl5⟩

  let cellRange : Finset (ℤ × (ℤ × (ℤ × (ℤ × ℤ)))) :=
    (Finset.Icc (-1600 : ℤ) 1600) ×ˢ
    ((Finset.Icc (-1600 : ℤ) 1600) ×ˢ
      ((Finset.Icc (-2000 : ℤ) 2000) ×ˢ
        ((Finset.Icc (-2000 : ℤ) 2000) ×ˢ
          (Finset.Icc (-1664 : ℤ) 4864))))

  have h_image_sub : ∀ (s : Finset (Fin source.card)), s ⊆ indices →
      Finset.image cell s ⊆ cellRange := by
    intro s hs
    rw [Finset.image_subset_iff]
    intro j hj
    have hj' : j ∈ indices := hs hj
    have h_bounds := h_cell_bounds j hj'
    have h1 := h_bounds.1
    have h2 := h_bounds.2.1
    have h3 := h_bounds.2.2.1
    have h4 := h_bounds.2.2.2.1
    have h5 := h_bounds.2.2.2.2
    rw [Finset.mem_product]
    exact ⟨h1, by
      rw [Finset.mem_product]
      exact ⟨h2, by
        rw [Finset.mem_product]
        exact ⟨h3, by
          rw [Finset.mem_product]
          exact ⟨h4, h5⟩⟩⟩⟩

  have h_card_range : cellRange.card = 3201 * 3201 * 4001 * 4001 * 6529 := by
    simp [cellRange, Finset.card_product, Finset.Icc_eq_empty_of_lt]
    <;> norm_num

  have h_pos_card : indices_pos.card ≤ cellRange.card := by
    have h1 : (Finset.image cell indices_pos).card = indices_pos.card :=
      Finset.card_image_of_injOn h_pos_inj
    have h2 : Finset.image cell indices_pos ⊆ cellRange := h_image_sub indices_pos (by simp [indices_pos] <;> tauto)
    rw [←h1]
    exact Finset.card_le_card h2

  have h_neg_card : indices_neg.card ≤ cellRange.card := by
    have h1 : (Finset.image cell indices_neg).card = indices_neg.card :=
      Finset.card_image_of_injOn h_neg_inj
    have h2 : Finset.image cell indices_neg ⊆ cellRange := h_image_sub indices_neg (by simp [indices_neg] <;> tauto)
    rw [←h1]
    exact Finset.card_le_card h2

  have h_main : indices.card ≤ indices_pos.card + indices_neg.card := by
    have h : indices ⊆ indices_pos ∪ indices_neg := h_cover
    have h2 : indices.card ≤ (indices_pos ∪ indices_neg).card := Finset.card_le_card h
    have h3 : (indices_pos ∪ indices_neg).card ≤ indices_pos.card + indices_neg.card :=
      Finset.card_union_le _ _
    linarith

  have h_final : indices.card ≤ 2 * cellRange.card := by linarith

  rw [h_card_range] at h_final
  have h_goal : 2 * (3201 * 3201 * 4001 * 4001 * 6529) ≤ gwzBackwardConflictDegree δ := by
    simp [gwzBackwardConflictDegree] <;> norm_num
  exact h_final.trans h_goal

end Kakeya.Assouad

end
