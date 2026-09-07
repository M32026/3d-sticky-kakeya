import MyLeanRepo.Kakeya.Hairbrush.Basic
import MyLeanRepo.Kakeya.AssertionD
import MyLeanRepo.Kakeya.Hairbrush.Helpers
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Cylinder-tube intersection volume bound

Geometric lemma: volume of intersection of a δ-tube U at angle θ from T
with the r-neighborhood of T's axis is O(δ² · (r+δ) / σ).

Uses a Householder reflection to align U.direction with the x-axis,
then applies the product-of-coordinate-diameters volume bound.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

variable {δ : ℝ}

/-- For σ ≤ 1 and θ ∈ [σ, 2σ], sin θ ≥ 2σ/π. -/
lemma sin_angle_lower_bound {σ θ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (h1 : σ ≤ θ) (h2 : θ ≤ 2 * σ) :
    Real.sin θ ≥ 2 * σ / Real.pi := by
  have hθ_nonneg : 0 ≤ θ := by linarith
  by_cases h_case : θ ≤ Real.pi / 2
  · have h4 : (2 / Real.pi) * θ ≤ Real.sin θ := Real.mul_le_sin hθ_nonneg h_case
    have h5 : 2 * θ / Real.pi ≥ 2 * σ / Real.pi := by gcongr <;> linarith
    have h6 : (2 / Real.pi) * θ = 2 * θ / Real.pi := by ring
    rw [h6] at h4
    linarith
  · have hθ_gt : θ > Real.pi / 2 := by linarith
    have h_ineq : Real.pi - 2 * σ ≤ Real.pi - θ := by linarith
    have h_a : -(Real.pi / 2) ≤ Real.pi - 2 * σ := by linarith [Real.pi_gt_three]
    have h_b : Real.pi - θ ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    have h_sin_pi : Real.sin (Real.pi - 2 * σ) ≤ Real.sin (Real.pi - θ) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two h_a h_b h_ineq
    have h1 : Real.sin (Real.pi - θ) = Real.sin θ := by rw [Real.sin_pi_sub]
    have h2 : Real.sin (Real.pi - 2 * σ) = Real.sin (2 * σ) := by rw [Real.sin_pi_sub]
    have h_sin_θ : Real.sin θ ≥ Real.sin (2 * σ) := by
      rw [←h1, ←h2]; exact h_sin_pi
    have h_c : 0 ≤ Real.pi - 2 * σ := by linarith [Real.pi_gt_three]
    have h_d : Real.pi - 2 * σ ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    have h_sin_x : (2 / Real.pi) * (Real.pi - 2 * σ) ≤ Real.sin (Real.pi - 2 * σ) :=
      Real.mul_le_sin h_c h_d
    have h_e : Real.sin (Real.pi - 2 * σ) ≥ 2 * (Real.pi - 2 * σ) / Real.pi := by
      have h_eq : (2 / Real.pi) * (Real.pi - 2 * σ) = 2 * (Real.pi - 2 * σ) / Real.pi := by ring
      rw [h_eq] at h_sin_x; exact h_sin_x
    have h_f : 2 * (Real.pi - 2 * σ) / Real.pi ≥ 2 * σ / Real.pi := by
      have h12 : 2 * (Real.pi - 2 * σ) ≥ 2 * σ := by
        have h9 : Real.pi ≥ 3 * σ := by
          have h10 : Real.pi > 3 := Real.pi_gt_three
          have h11 : 3 * σ ≤ 3 := by linarith
          linarith
        linarith
      gcongr <;> linarith
    rw [h2] at h_e
    linarith

/-- Axial diameter bound used by `tube_cylinder_intersection_volume`. -/
lemma tube_cylinder_axial_diameter
    {δ r s : ℝ} (hδ : 0 < δ) (hr : 0 ≤ r)
    (hs_pos : 0 < s) (hs_le_one : s ≤ 1)
    (Ubase Tbase v Tdirection w' : Point3)
    (hv_norm : ‖v‖ = 1)
    (hTdirection_norm : ‖Tdirection‖ = 1)
    (h_w'_perp_T : inner ℝ w' Tdirection = 0)
    (h_w'_inner_v : inner ℝ v w' = s)
    (h_w'_norm : ‖w'‖ = 1)
    (S : Set Point3)
    (h_near : ∀ x ∈ S,
      ∃ (a : Point3) (α : ℝ),
        a = Ubase + α • v ∧
        dist x a ≤ δ ∧
        ∃ (p : Point3) (t : ℝ),
          p = Tbase + t • Tdirection ∧
          dist x p ≤ r) :
    ∀ x y, x ∈ S → y ∈ S →
      |inner ℝ x v - inner ℝ y v| ≤
        4 * (r + δ) / s := by
  intro x y hx hy
  rcases h_near x hx with
    ⟨a, α, ha, hxa, p, t, hp, hxp⟩
  rcases h_near y hy with
    ⟨b, β, hb, hyb, q, u, hq, hyq⟩
  have h1 : |inner ℝ (a - b) w'| ≤ 2 * (r + δ) := by
    have h_eq : a - b = (a - p) + (p - q) + (q - b) := by
      abel
    have h4 :
        inner ℝ (a - b) w' =
          inner ℝ (a - p) w' +
            inner ℝ (p - q) w' +
              inner ℝ (q - b) w' := by
      rw [h_eq, inner_add_left, inner_add_left]
    rw [h4]
    have h7 : inner ℝ Tdirection w' = 0 := by
      have h_comm :
          inner ℝ Tdirection w' =
            inner ℝ w' Tdirection :=
        (real_inner_comm Tdirection w').symm
      rw [h_comm, h_w'_perp_T]
    have h5 : inner ℝ (p - q) w' = 0 := by
      have h6 : p - q = (t - u) • Tdirection := by
        rw [hp, hq]
        calc
          (Tbase + t • Tdirection) -
                (Tbase + u • Tdirection) =
              t • Tdirection - u • Tdirection := by
                abel
          _ = (t - u) • Tdirection := by
                rw [sub_smul]
      rw [h6, inner_smul_left, h7]
      simp [starRingEnd]
    rw [h5, add_zero]
    have h7' :
        |inner ℝ (a - p) w'| ≤ ‖a - p‖ := by
      calc
        |inner ℝ (a - p) w'| ≤ ‖a - p‖ * ‖w'‖ :=
          abs_real_inner_le_norm _ _
        _ = ‖a - p‖ := by rw [h_w'_norm]; ring
    have h8' :
        |inner ℝ (q - b) w'| ≤ ‖q - b‖ := by
      calc
        |inner ℝ (q - b) w'| ≤ ‖q - b‖ * ‖w'‖ :=
          abs_real_inner_le_norm _ _
        _ = ‖q - b‖ := by rw [h_w'_norm]; ring
    have h9 : ‖a - p‖ ≤ r + δ := by
      have h_ap : a - p = (a - x) + (x - p) := by abel
      calc
        ‖a - p‖ = ‖(a - x) + (x - p)‖ := by rw [h_ap]
        _ ≤ ‖a - x‖ + ‖x - p‖ := norm_add_le _ _
        _ = dist x a + dist x p := by
          rw [← dist_eq_norm, dist_comm, ← dist_eq_norm]
        _ ≤ δ + r := by gcongr
        _ = r + δ := by ring
    have h10 : ‖q - b‖ ≤ r + δ := by
      have h_qb : q - b = (q - y) + (y - b) := by abel
      calc
        ‖q - b‖ = ‖(q - y) + (y - b)‖ := by rw [h_qb]
        _ ≤ ‖q - y‖ + ‖y - b‖ := norm_add_le _ _
        _ = dist y q + dist y b := by
          rw [← dist_eq_norm, dist_comm, ← dist_eq_norm]
        _ ≤ r + δ := by gcongr
    calc
      |inner ℝ (a - p) w' + inner ℝ (q - b) w'| ≤
          |inner ℝ (a - p) w'| +
            |inner ℝ (q - b) w'| := abs_add_le _ _
      _ ≤ ‖a - p‖ + ‖q - b‖ := add_le_add h7' h8'
      _ ≤ (r + δ) + (r + δ) := add_le_add h9 h10
      _ = 2 * (r + δ) := by ring
  have h11 : inner ℝ (a - b) w' = (α - β) * s := by
    have h12 : a - b = (α - β) • v := by
      rw [ha, hb]
      calc
        (Ubase + α • v) - (Ubase + β • v) =
            α • v - β • v := by abel
        _ = (α - β) • v := by rw [sub_smul]
    rw [h12, inner_smul_left, h_w'_inner_v]
    simp [starRingEnd]
  rw [h11] at h1
  have h13 : |α - β| ≤ 2 * (r + δ) / s := by
    have h14 : |α - β| * s ≤ 2 * (r + δ) := by
      have habs : |(α - β) * s| = |α - β| * s := by
        rw [abs_mul, abs_of_pos hs_pos]
      rwa [habs] at h1
    calc
      |α - β| = (|α - β| * s) / s := by
        field_simp [hs_pos.ne']
      _ ≤ (2 * (r + δ)) / s := by gcongr
  have hvv : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv_norm]
    norm_num
  have h15 :
      |inner ℝ (x - y) v| ≤
        |inner ℝ (x - a) v| + |α - β| +
          |inner ℝ (b - y) v| := by
    have h16 : x - y = (x - a) + (a - b) + (b - y) := by
      abel
    have h17 :
        inner ℝ (x - y) v =
          inner ℝ (x - a) v +
            inner ℝ (a - b) v +
              inner ℝ (b - y) v := by
      rw [h16, inner_add_left, inner_add_left]
    rw [h17]
    have h18 : inner ℝ (a - b) v = α - β := by
      have h19 : a - b = (α - β) • v := by
        rw [ha, hb]
        calc
          (Ubase + α • v) - (Ubase + β • v) =
              α • v - β • v := by abel
          _ = (α - β) • v := by rw [sub_smul]
      rw [h19, inner_smul_left, hvv]
      simp [starRingEnd]
    rw [h18]
    calc
      |inner ℝ (x - a) v + (α - β) +
          inner ℝ (b - y) v| ≤
          |inner ℝ (x - a) v + (α - β)| +
            |inner ℝ (b - y) v| := abs_add_le _ _
      _ ≤
          (|inner ℝ (x - a) v| + |α - β|) +
            |inner ℝ (b - y) v| := by
        gcongr
        exact abs_add_le _ _
  have h17 : |inner ℝ (x - a) v| ≤ δ := by
    calc
      |inner ℝ (x - a) v| ≤ ‖x - a‖ * ‖v‖ :=
        abs_real_inner_le_norm _ _
      _ = dist x a := by
        rw [hv_norm, mul_one, dist_eq_norm]
      _ ≤ δ := hxa
  have h18 : |inner ℝ (b - y) v| ≤ δ := by
    calc
      |inner ℝ (b - y) v| ≤ ‖b - y‖ * ‖v‖ :=
        abs_real_inner_le_norm _ _
      _ = dist y b := by
        rw [hv_norm, mul_one, dist_comm, dist_eq_norm]
      _ ≤ δ := hyb
  have h20 : 2 * δ ≤ 2 * (r + δ) / s := by
    have h22 : 1 ≤ 1 / s := one_le_one_div hs_pos hs_le_one
    calc
      2 * δ ≤ 2 * (r + δ) := by linarith
      _ = 2 * (r + δ) * 1 := by ring
      _ ≤ 2 * (r + δ) * (1 / s) := by gcongr
      _ = 2 * (r + δ) / s := by ring
  rw [← inner_sub_left]
  calc
    |inner ℝ (x - y) v| ≤
        |inner ℝ (x - a) v| + |α - β| +
          |inner ℝ (b - y) v| := h15
    _ ≤ δ + 2 * (r + δ) / s + δ := by gcongr
    _ = 2 * δ + 2 * (r + δ) / s := by ring
    _ ≤ 2 * (r + δ) / s + 2 * (r + δ) / s := by
      exact add_le_add h20 (le_refl _)
    _ = 4 * (r + δ) / s := by ring

/-- Numerical coefficient bound for the final cylinder intersection estimate. -/
lemma tube_cylinder_volume_coefficient
    {δ r s σ : ℝ}
    (hδ : 0 < δ) (hr : 0 ≤ r)
    (hs_pos : 0 < s)
    (hs_lower : s ≥ 2 * σ / Real.pi)
    (hσ : 0 < σ) :
    (4 * (r + δ) / s) * (2 * δ) * (2 * δ) ≤
      100 * (r + δ) / σ * δ ^ 2 := by
  have h_eq :
      (4 * (r + δ) / s) * (2 * δ) * (2 * δ) =
        16 * (r + δ) * δ ^ 2 / s := by
    field_simp [hs_pos.ne']
    ring
  rw [h_eq]
  have h3 : 1 / s ≤ Real.pi / (2 * σ) := by
    have h5 : 0 < 2 * σ / Real.pi := by positivity
    have h6 :
        1 / s ≤ 1 / (2 * σ / Real.pi) :=
      one_div_le_one_div_of_le h5 hs_lower
    have h7 :
        1 / (2 * σ / Real.pi) =
          Real.pi / (2 * σ) := by
      field_simp [hσ.ne', Real.pi_ne_zero]
    rwa [h7] at h6
  have h_coeff_pos :
      0 ≤ 16 * (r + δ) * δ ^ 2 := by positivity
  have h6 :
      16 * (r + δ) * δ ^ 2 / s ≤
        16 * (r + δ) * δ ^ 2 *
          (Real.pi / (2 * σ)) := by
    have h_div :
        16 * (r + δ) * δ ^ 2 / s =
          16 * (r + δ) * δ ^ 2 * (1 / s) := by
      field_simp [hs_pos.ne']
    rw [h_div]
    exact mul_le_mul_of_nonneg_left h3 h_coeff_pos
  have h7 :
      16 * (r + δ) * δ ^ 2 *
          (Real.pi / (2 * σ)) =
        (8 * Real.pi) * (r + δ) * δ ^ 2 / σ := by
    field_simp [hσ.ne']
    ring
  rw [h7] at h6
  have h8 : 8 * Real.pi ≤ 100 := by
    nlinarith [Real.pi_lt_four]
  have h11 : 0 ≤ (r + δ) * δ ^ 2 / σ := by positivity
  calc
    16 * (r + δ) * δ ^ 2 / s ≤
        (8 * Real.pi) * (r + δ) * δ ^ 2 / σ := h6
    _ = (8 * Real.pi) * ((r + δ) * δ ^ 2 / σ) := by ring
    _ ≤ 100 * ((r + δ) * δ ^ 2 / σ) :=
      mul_le_mul_of_nonneg_right h8 h11
    _ = 100 * (r + δ) / σ * δ ^ 2 := by
      field_simp [hσ.ne']

/--
Volume bound for U.carrier ∩ thickenedTube T r.

Given δ-tubes T, U with angle in [σ, 2σ] (σ ≤ 1), and T.carrier ∩ U.carrier
nonempty, the volume of the intersection is at most 100 · (r+δ)/σ · δ².
-/
lemma tube_cylinder_intersection_volume
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (T U : Kakeya.DeltaTube δ)
    (h_angle : σ ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ)
    (h_inter : (T.carrier ∩ U.carrier).Nonempty)
    (r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.volume (U.carrier ∩ thickenedTube T r) ≤
      ENNReal.ofReal (100 * (r + δ) / σ) * ENNReal.ofReal (δ ^ 2) := by
  let θ : ℝ := angleBetween T U
  have hθ1 : σ ≤ θ := h_angle.1
  have hθ2 : θ ≤ 2 * σ := h_angle.2
  have hθ_pos : 0 < θ := by linarith
  have hθ_lt_pi : θ < Real.pi := by
    have h3 : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
    linarith
  have h_inner_bound1 : -1 ≤ inner ℝ T.direction U.direction := by
    have h : |inner ℝ T.direction U.direction| ≤ ‖T.direction‖ * ‖U.direction‖ :=
      abs_real_inner_le_norm _ _
    rw [T.direction_unit, U.direction_unit] at h
    have h' : |inner ℝ T.direction U.direction| ≤ 1 := by simpa using h
    exact (abs_le.mp h').1
  have h_inner_bound2 : inner ℝ T.direction U.direction ≤ 1 := by
    have h : |inner ℝ T.direction U.direction| ≤ ‖T.direction‖ * ‖U.direction‖ :=
      abs_real_inner_le_norm _ _
    rw [T.direction_unit, U.direction_unit] at h
    have h' : |inner ℝ T.direction U.direction| ≤ 1 := by simpa using h
    exact (abs_le.mp h').2
  have hcos : Real.cos θ = inner ℝ T.direction U.direction := by
    simpa [θ, angleBetween] using Real.cos_arccos h_inner_bound1 h_inner_bound2
  let s : ℝ := Real.sin θ
  have hs_pos : 0 < s := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
  have hs_lower : s ≥ 2 * σ / Real.pi := sin_angle_lower_bound hσ hσ1 hθ1 hθ2
  have hs_le_one : s ≤ 1 := Real.sin_le_one θ
  let c : ℝ := Real.cos θ

  -- Householder reflection A maps v = U.direction to e0_std
  let v : Point3 := U.direction
  let e0_std : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let e1_std : Point3 := EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
  let e2_std : Point3 := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  have hv_norm : ‖v‖ = 1 := U.direction_unit
  have he0_std_norm : ‖e0_std‖ = 1 := by simp [e0_std]
  let A : Point3 ≃ₗᵢ[ℝ] Point3 :=
    Submodule.reflection (ℝ ∙ (v - e0_std))ᗮ
  have hA : A v = e0_std :=
    Submodule.reflection_sub (by rw [hv_norm, he0_std_norm])
  let e2 : Point3 := A.symm e1_std
  let e3 : Point3 := A.symm e2_std
  have hA_e2 : A e2 = e1_std := by simp [e2]
  have hA_e3 : A e3 = e2_std := by simp [e3]
  have he2_norm : ‖e2‖ = 1 := by
    have h : ‖e2‖ = ‖e1_std‖ := A.symm.norm_map e1_std
    rw [h] <;> simp [e1_std]
  have he3_norm : ‖e3‖ = 1 := by
    have h : ‖e3‖ = ‖e2_std‖ := A.symm.norm_map e2_std
    rw [h] <;> simp [e2_std]

  -- Coordinate formulas: (A z) i = inner ℝ z (A.symm (stdBasis i))
  have hcoord0 : ∀ (z : Point3), (A z) 0 = inner ℝ z v := by
    intro z
    have h : (A z) 0 = inner ℝ (A z) e0_std := by
      have h2 : inner ℝ (A z) e0_std = (1 : ℝ) * (A z) 0 :=
        EuclideanSpace.inner_single_right 0 (1 : ℝ) (A z)
      rw [h2] <;> ring
    rw [h]
    have h3 : inner ℝ (A z) e0_std = inner ℝ z (A.symm e0_std) := by
      have h4 := A.inner_map_map z (A.symm e0_std)
      have h5 : A (A.symm e0_std) = e0_std := A.apply_symm_apply e0_std
      rw [h5] at h4; exact h4
    rw [h3]
    have h6 : A.symm e0_std = v := by
      have h7 : A (A.symm e0_std) = A v := by rw [A.apply_symm_apply, hA]
      exact A.injective h7
    rw [h6]
  have hcoord1 : ∀ (z : Point3), (A z) 1 = inner ℝ z e2 := by
    intro z
    have h : (A z) 1 = inner ℝ (A z) e1_std := by
      have h2 : inner ℝ (A z) e1_std = (1 : ℝ) * (A z) 1 :=
        EuclideanSpace.inner_single_right 1 (1 : ℝ) (A z)
      rw [h2] <;> ring
    rw [h]
    have h3 : inner ℝ (A z) e1_std = inner ℝ z (A.symm e1_std) := by
      have h4 := A.inner_map_map z (A.symm e1_std)
      have h5 : A (A.symm e1_std) = e1_std := A.apply_symm_apply e1_std
      rw [h5] at h4; exact h4
    rw [h3] <;> rfl
  have hcoord2 : ∀ (z : Point3), (A z) 2 = inner ℝ z e3 := by
    intro z
    have h : (A z) 2 = inner ℝ (A z) e2_std := by
      have h2 : inner ℝ (A z) e2_std = (1 : ℝ) * (A z) 2 :=
        EuclideanSpace.inner_single_right 2 (1 : ℝ) (A z)
      rw [h2] <;> ring
    rw [h]
    have h3 : inner ℝ (A z) e2_std = inner ℝ z (A.symm e2_std) := by
      have h4 := A.inner_map_map z (A.symm e2_std)
      have h5 : A (A.symm e2_std) = e2_std := A.apply_symm_apply e2_std
      rw [h5] at h4; exact h4
    rw [h3] <;> rfl

  -- e2, e3 are perpendicular to v
  have he2_orth : inner ℝ v e2 = 0 := by
    have h : inner ℝ v e2 = inner ℝ (A v) (A e2) := (A.inner_map_map v e2).symm
    rw [h, hA, hA_e2]
    have h_zero : inner ℝ e0_std e1_std = 0 := by
      have h : inner ℝ e0_std e1_std = (1 : ℝ) * e0_std 1 :=
        EuclideanSpace.inner_single_right 1 (1 : ℝ) e0_std
      rw [h]
      have h2 : e0_std 1 = 0 := by
        simp [e0_std, PiLp.single_apply] <;> decide
      rw [h2] <;> ring
    exact h_zero
  have he3_orth : inner ℝ v e3 = 0 := by
    have h : inner ℝ v e3 = inner ℝ (A v) (A e3) := (A.inner_map_map v e3).symm
    rw [h, hA, hA_e3]
    have h_zero : inner ℝ e0_std e2_std = 0 := by
      have h : inner ℝ e0_std e2_std = (1 : ℝ) * e0_std 2 :=
        EuclideanSpace.inner_single_right 2 (1 : ℝ) e0_std
      rw [h]
      have h2 : e0_std 2 = 0 := by
        simp [e0_std, PiLp.single_apply] <;> decide
      rw [h2] <;> ring
    exact h_zero

  -- w' perpendicular to T.direction, inner(v, w') = s
  let w' : Point3 := (1 / s) • (v - c • T.direction)
  have h_vT : inner ℝ v T.direction = c := by
    have h_comm : inner ℝ v T.direction = inner ℝ T.direction v := by
      exact (real_inner_comm v T.direction).symm
    rw [h_comm]
    have h_eq : inner ℝ T.direction v = inner ℝ T.direction U.direction := by rfl
    rw [h_eq]
    exact hcos.symm
  have h_TT : inner ℝ T.direction T.direction = 1 := by
    have h3 : inner ℝ T.direction T.direction = ‖T.direction‖ ^ 2 := by
      exact real_inner_self_eq_norm_sq T.direction
    rw [h3, T.direction_unit] <;> norm_num
  have h_vv : inner ℝ v v = 1 := by
    have h2 : inner ℝ v v = ‖v‖ ^ 2 := by
      exact real_inner_self_eq_norm_sq v
    rw [h2, hv_norm] <;> norm_num
  have h_Tv : inner ℝ T.direction v = c := by
    have h_comm : inner ℝ T.direction v = inner ℝ v T.direction := by
      exact (real_inner_comm T.direction v).symm
    rw [h_comm, h_vT]
  have h_w'_perp_T : inner ℝ w' T.direction = 0 := by
    have h1 : inner ℝ (v - c • T.direction) T.direction =
        inner ℝ v T.direction - inner ℝ (c • T.direction) T.direction := by
      exact inner_sub_left v (c • T.direction) T.direction
    have h2 : inner ℝ (c • T.direction) T.direction =
        c * inner ℝ T.direction T.direction := by
      exact real_inner_smul_left T.direction T.direction c
    have h_main : inner ℝ w' T.direction = (1 / s) * inner ℝ (v - c • T.direction) T.direction := by
      have h_w'def : w' = (1 / s) • (v - c • T.direction) := by rfl
      rw [h_w'def]
      simp [inner_smul_left] <;> ring
    rw [h_main, h1, h2, h_vT, h_TT] <;> ring
  have h_w'_inner_v : inner ℝ v w' = s := by
    have h1 : inner ℝ v (v - c • T.direction) =
        inner ℝ v v - c * inner ℝ v T.direction := by
      simp [inner_sub_right, inner_smul_right] <;> ring
    have h_main : inner ℝ v w' = (1 / s) * inner ℝ v (v - c • T.direction) := by
      have h_w'def : w' = (1 / s) • (v - c • T.direction) := by rfl
      rw [h_w'def]
      simp [inner_smul_right] <;> ring
    rw [h_main, h1, h_vv, h_vT]
    have h4 : 1 - c * c = s ^ 2 := by
      have h5 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
      have h6 : c = Real.cos θ := by rfl
      have h7 : s = Real.sin θ := by rfl
      rw [h6, h7] at *; linarith
    rw [h4]
    field_simp [hs_pos.ne'] <;> ring
  have h_w'_norm : ‖w'‖ = 1 := by
    have h_w'def : w' = (1 / s) • (v - c • T.direction) := by rfl
    have h1 : ‖w'‖ ^ 2 = (1 / s) ^ 2 * ‖v - c • T.direction‖ ^ 2 := by
      rw [h_w'def]
      have h_ns : ‖(1 / s) • (v - c • T.direction)‖ = |1 / s| * ‖v - c • T.direction‖ := norm_smul _ _
      rw [h_ns]
      have h_pos : 0 < 1 / s := by positivity
      rw [abs_of_pos h_pos] <;> ring
    have h2 : inner ℝ (v - c • T.direction) (v - c • T.direction) =
        inner ℝ v v - c * inner ℝ v T.direction - c * inner ℝ T.direction v + c^2 * inner ℝ T.direction T.direction := by
      have h_expand : inner ℝ (v - c • T.direction) (v - c • T.direction) =
          inner ℝ v (v - c • T.direction) - inner ℝ (c • T.direction) (v - c • T.direction) := by
        rw [inner_sub_left]
      rw [h_expand]
      have h1 : inner ℝ v (v - c • T.direction) = inner ℝ v v - c * inner ℝ v T.direction := by
        rw [inner_sub_right, inner_smul_right] <;> ring
      have h2a : inner ℝ (c • T.direction) (v - c • T.direction) =
          c * inner ℝ T.direction v - c^2 * inner ℝ T.direction T.direction := by
        have h_smul : inner ℝ (c • T.direction) (v - c • T.direction) =
            (starRingEnd ℝ c) * inner ℝ T.direction (v - c • T.direction) := by
          rw [inner_smul_left]
        rw [h_smul]
        have h_star : (starRingEnd ℝ c) = c := by simp [starRingEnd]
        rw [h_star]
        have h_inner : inner ℝ T.direction (v - c • T.direction) =
            inner ℝ T.direction v - c * inner ℝ T.direction T.direction := by
          rw [inner_sub_right, inner_smul_right] <;> ring
        rw [h_inner] <;> ring
      rw [h1, h2a] <;> ring
    have h3 : ‖v - c • T.direction‖ ^ 2 =
        inner ℝ (v - c • T.direction) (v - c • T.direction) := by
      exact (real_inner_self_eq_norm_sq (v - c • T.direction)).symm
    have h_cs : c ^ 2 + s ^ 2 = 1 := by
      have h5 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
      have h6 : c = Real.cos θ := by rfl
      have h7 : s = Real.sin θ := by rfl
      rw [h6, h7]
      linarith [h5]
    have h4 : ‖v - c • T.direction‖ ^ 2 = s ^ 2 := by
      rw [h3, h2, h_vv, h_vT, h_Tv, h_TT]
      linarith
    have h5 : ‖w'‖ ^ 2 = 1 := by
      rw [h1, h4]
      have h6 : (1 / s) ^ 2 * s ^ 2 = 1 := by field_simp [hs_pos.ne'] <;> ring
      exact h6
    have h7 : 0 ≤ ‖w'‖ := by positivity
    nlinarith

  -- Compactness of unit segments and cthickening characterization
  have h_segT_comp : IsCompact (Kakeya.unitSegment T.base T.direction) :=
    isCompact_Icc.image (show Continuous (fun t : ℝ => T.base + t • T.direction) from by fun_prop)
  have h_segU_comp : IsCompact (Kakeya.unitSegment U.base U.direction) :=
    isCompact_Icc.image (show Continuous (fun t : ℝ => U.base + t • U.direction) from by fun_prop)
  have h_eqT : thickenedTube T r = ⋃ p ∈ (Kakeya.unitSegment T.base T.direction), Metric.closedBall p r :=
    h_segT_comp.cthickening_eq_biUnion_closedBall hr
  have h_eqU : U.carrier = ⋃ a ∈ (Kakeya.unitSegment U.base U.direction), Metric.closedBall a δ := by
    have h_car : U.carrier =
        Metric.cthickening δ (Kakeya.unitSegment U.base U.direction) := by
      rfl
    rw [h_car]
    exact h_segU_comp.cthickening_eq_biUnion_closedBall hδ.le

  -- S is the intersection set
  let S : Set Point3 := U.carrier ∩ thickenedTube T r
  have hS_meas : MeasurableSet S := by
    have hT_comp : IsCompact (thickenedTube T r) := h_segT_comp.cthickening
    have hU_comp : IsCompact U.carrier := h_segU_comp.cthickening
    exact (hU_comp.inter_right hT_comp.isClosed).measurableSet

  -- Nearness property for points in S
  have h_near : ∀ x ∈ S, ∃ (a : Point3) (α : ℝ), a = U.base + α • v ∧
      dist x a ≤ δ ∧ ∃ (p : Point3) (t : ℝ), p = T.base + t • T.direction ∧ dist x p ≤ r := by
    intro x hx
    have hxU : x ∈ U.carrier := hx.1
    have hxT : x ∈ thickenedTube T r := hx.2
    have h1 : ∃ (a : Point3), a ∈ Kakeya.unitSegment U.base U.direction ∧ dist x a ≤ δ := by
      have h_mem : x ∈ (⋃ y ∈ Kakeya.unitSegment U.base U.direction, Metric.closedBall y δ) := by
        rw [h_eqU] at hxU; exact hxU
      simpa [Set.mem_iUnion, Metric.mem_closedBall] using h_mem
    have h2 : ∃ (p : Point3), p ∈ Kakeya.unitSegment T.base T.direction ∧ dist x p ≤ r := by
      have h_mem : x ∈ (⋃ y ∈ Kakeya.unitSegment T.base T.direction, Metric.closedBall y r) := by
        rw [h_eqT] at hxT; exact hxT
      simpa [Set.mem_iUnion, Metric.mem_closedBall] using h_mem
    rcases h1 with ⟨a, ha, hxa⟩
    rcases h2 with ⟨p, hp, hxp⟩
    rcases ha with ⟨α, _, rfl⟩
    rcases hp with ⟨t, _, rfl⟩
    exact ⟨U.base + α • v, α, rfl, hxa, T.base + t • T.direction, t, rfl, hxp⟩

  -- Diameter along coordinate 0 (v direction): ≤ 4(r+δ)/s
  have h0 : ∀ x y, x ∈ S → y ∈ S → |(A x) 0 - (A y) 0| ≤ 4 * (r + δ) / s := by
    intro x y hx hy
    rw [hcoord0 x, hcoord0 y]
    exact
      tube_cylinder_axial_diameter
        hδ hr hs_pos hs_le_one U.base T.base v
        T.direction w' hv_norm T.direction_unit
        h_w'_perp_T h_w'_inner_v h_w'_norm S h_near
        x y hx hy

  -- Diameter along coordinate 1 (perpendicular to v): ≤ 2δ
  have h1 : ∀ x y, x ∈ S → y ∈ S → |(A x) 1 - (A y) 1| ≤ 2 * δ := by
    intro x y hx hy
    rw [hcoord1 x, hcoord1 y]
    rcases h_near x hx with ⟨a, α, ha, hxa, _, _⟩
    rcases h_near y hy with ⟨b, β, hb, hyb, _, _⟩
    have h_ab_e2 : inner ℝ (a - b) e2 = 0 := by
      have h : a - b = (α - β) • v := by
        rw [ha, hb]
        have h' : (U.base + α • v) - (U.base + β • v) = (α - β) • v := by
          calc (U.base + α • v) - (U.base + β • v)
            = α • v - β • v := by abel
          _ = (α - β) • v := by rw [sub_smul]
        exact h'
      rw [h, inner_smul_left, he2_orth] <;> simp [starRingEnd] <;> ring
    have h3 : |inner ℝ (x - a) e2| ≤ δ := by
      have h_xa : ‖x - a‖ ≤ δ := by
        have h : ‖x - a‖ = dist x a := by rw [←dist_eq_norm]
        rw [h]; exact hxa
      calc |inner ℝ (x - a) e2| ≤ ‖x - a‖ * ‖e2‖ := abs_real_inner_le_norm _ _
        _ = ‖x - a‖ * 1 := by rw [he2_norm]
        _ = ‖x - a‖ := by ring
        _ ≤ δ := h_xa
    have h4 : |inner ℝ (b - y) e2| ≤ δ := by
      have h_yb : ‖b - y‖ ≤ δ := by
        have h : ‖b - y‖ = dist y b := by rw [←dist_eq_norm, dist_comm]
        rw [h]; exact hyb
      calc |inner ℝ (b - y) e2| ≤ ‖b - y‖ * ‖e2‖ := abs_real_inner_le_norm _ _
        _ = ‖b - y‖ * 1 := by rw [he2_norm]
        _ = ‖b - y‖ := by ring
        _ ≤ δ := h_yb
    have h5 : inner ℝ (x - y) e2 = inner ℝ (x - a) e2 + inner ℝ (a - b) e2 + inner ℝ (b - y) e2 := by
      have h6 : x - y = (x - a) + (a - b) + (b - y) := by abel
      rw [h6, inner_add_left, inner_add_left]
    have h_sub : inner ℝ x e2 - inner ℝ y e2 = inner ℝ (x - y) e2 := by
      exact (inner_sub_left x y e2).symm
    rw [h_sub, h5, h_ab_e2, add_zero]
    calc |inner ℝ (x - a) e2 + inner ℝ (b - y) e2|
        ≤ |inner ℝ (x - a) e2| + |inner ℝ (b - y) e2| := by exact abs_add_le _ _
      _ ≤ δ + δ := by gcongr
      _ = 2 * δ := by ring

  -- Diameter along coordinate 2 (perpendicular to v): ≤ 2δ
  have h2 : ∀ x y, x ∈ S → y ∈ S → |(A x) 2 - (A y) 2| ≤ 2 * δ := by
    intro x y hx hy
    rw [hcoord2 x, hcoord2 y]
    rcases h_near x hx with ⟨a, α, ha, hxa, _, _⟩
    rcases h_near y hy with ⟨b, β, hb, hyb, _, _⟩
    have h_ab_e3 : inner ℝ (a - b) e3 = 0 := by
      have h : a - b = (α - β) • v := by
        rw [ha, hb]
        have h' : (U.base + α • v) - (U.base + β • v) = (α - β) • v := by
          calc (U.base + α • v) - (U.base + β • v)
            = α • v - β • v := by abel
          _ = (α - β) • v := by rw [sub_smul]
        exact h'
      rw [h, inner_smul_left, he3_orth] <;> simp [starRingEnd] <;> ring
    have h3 : |inner ℝ (x - a) e3| ≤ δ := by
      have h_xa : ‖x - a‖ ≤ δ := by
        have h : ‖x - a‖ = dist x a := by rw [←dist_eq_norm]
        rw [h]; exact hxa
      calc |inner ℝ (x - a) e3| ≤ ‖x - a‖ * ‖e3‖ := abs_real_inner_le_norm _ _
        _ = ‖x - a‖ * 1 := by rw [he3_norm]
        _ = ‖x - a‖ := by ring
        _ ≤ δ := h_xa
    have h4 : |inner ℝ (b - y) e3| ≤ δ := by
      have h_yb : ‖b - y‖ ≤ δ := by
        have h : ‖b - y‖ = dist y b := by rw [←dist_eq_norm, dist_comm]
        rw [h]; exact hyb
      calc |inner ℝ (b - y) e3| ≤ ‖b - y‖ * ‖e3‖ := abs_real_inner_le_norm _ _
        _ = ‖b - y‖ * 1 := by rw [he3_norm]
        _ = ‖b - y‖ := by ring
        _ ≤ δ := h_yb
    have h5 : inner ℝ (x - y) e3 = inner ℝ (x - a) e3 + inner ℝ (a - b) e3 + inner ℝ (b - y) e3 := by
      have h6 : x - y = (x - a) + (a - b) + (b - y) := by abel
      rw [h6, inner_add_left, inner_add_left]
    have h_sub : inner ℝ x e3 - inner ℝ y e3 = inner ℝ (x - y) e3 := by
      exact (inner_sub_left x y e3).symm
    rw [h_sub, h5, h_ab_e3, add_zero]
    calc |inner ℝ (x - a) e3 + inner ℝ (b - y) e3|
        ≤ |inner ℝ (x - a) e3| + |inner ℝ (b - y) e3| := by exact abs_add_le _ _
      _ ≤ δ + δ := by gcongr
      _ = 2 * δ := by ring

  -- Apply product-of-diameters volume bound
  let d0 : ℝ := 4 * (r + δ) / s
  let d1 : ℝ := 2 * δ
  let d2 : ℝ := 2 * δ
  have hd0_nonneg : 0 ≤ d0 := by positivity
  have hd1_nonneg : 0 ≤ d1 := by positivity
  have hd2_nonneg : 0 ≤ d2 := by positivity

  let AS : Set Point3 := A '' S
  let F : Point3 → (Fin 3 → ℝ) := WithLp.ofLp (p := 2)
  let AS' : Set (Fin 3 → ℝ) := F '' AS
  have hpres_F : MeasurePreserving F volume volume := PiLp.volume_preserving_ofLp (ι := Fin 3)
  have hAS_meas : MeasurableSet AS := A.toMeasurableEquiv.measurableSet_image.mpr hS_meas
  have hvol : volume S = volume AS := by
    have hpres : MeasurePreserving A volume volume := A.measurePreserving
    have hmap : Measure.map A volume = volume := hpres.map_eq
    have h : volume AS = Measure.map A volume AS := by rw [hmap]
    rw [h]
    have h2 : Measure.map A volume AS = volume (A ⁻¹' AS) :=
      Measure.map_apply hpres.measurable hAS_meas
    rw [h2]
    have h3 : A ⁻¹' AS = S := by
      rw [show AS = A '' S from rfl]
      rw [Set.preimage_image_eq _ A.injective]
    rw [h3]
  have hF_cont : Continuous (WithLp.toLp (p := 2) : (Fin 3 → ℝ) → Point3) :=
    PiLp.continuous_toLp 2 (β := fun (_ : Fin 3) => ℝ)
  let F_equiv : Point3 ≃ᵐ (Fin 3 → ℝ) :=
    { toFun := F
      invFun := WithLp.toLp (p := 2)
      left_inv := WithLp.toLp_ofLp (p := 2)
      right_inv := WithLp.ofLp_toLp (p := 2)
      measurable_toFun := hpres_F.measurable
      measurable_invFun := hF_cont.measurable }
  have hAS'_meas : MeasurableSet AS' := F_equiv.measurableSet_image.mpr hAS_meas
  have hF_inj : Function.Injective F := F_equiv.injective
  have hvol' : volume AS' = volume AS := by
    have hmap : Measure.map F volume = volume := hpres_F.map_eq
    calc volume AS'
      = Measure.map F volume AS' := by rw [hmap]
    _ = volume (F ⁻¹' AS') := Measure.map_apply hpres_F.measurable hAS'_meas
    _ = volume AS := by rw [Set.preimage_image_eq _ hF_inj]

  have hAS'_eq : AS' = (fun x : Point3 => F (A x)) '' S := by
    ext z
    simp only [AS', AS, Set.mem_image]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨A x, ⟨x, hx, rfl⟩, rfl⟩
  have h_ediam0 : Metric.ediam (Function.eval 0 '' AS') ≤ ENNReal.ofReal d0 := by
    apply Metric.ediam_le_of_forall_dist_le
    intro a ha b hb
    rw [hAS'_eq] at ha hb
    rcases ha with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, hx, rfl⟩
    rcases hb with ⟨w, hw, rfl⟩
    rcases hw with ⟨y, hy, rfl⟩
    have h_goal : dist (Function.eval 0 (F (A x))) (Function.eval 0 (F (A y))) = |(A x) 0 - (A y) 0| := by
      rw [Real.dist_eq] <;> rfl
    rw [h_goal]
    exact h0 x y hx hy
  have h_ediam1 : Metric.ediam (Function.eval 1 '' AS') ≤ ENNReal.ofReal d1 := by
    apply Metric.ediam_le_of_forall_dist_le
    intro a ha b hb
    rw [hAS'_eq] at ha hb
    rcases ha with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, hx, rfl⟩
    rcases hb with ⟨w, hw, rfl⟩
    rcases hw with ⟨y, hy, rfl⟩
    have h_goal : dist (Function.eval 1 (F (A x))) (Function.eval 1 (F (A y))) = |(A x) 1 - (A y) 1| := by
      rw [Real.dist_eq] <;> rfl
    rw [h_goal]
    exact h1 x y hx hy
  have h_ediam2 : Metric.ediam (Function.eval 2 '' AS') ≤ ENNReal.ofReal d2 := by
    apply Metric.ediam_le_of_forall_dist_le
    intro a ha b hb
    rw [hAS'_eq] at ha hb
    rcases ha with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, hx, rfl⟩
    rcases hb with ⟨w, hw, rfl⟩
    rcases hw with ⟨y, hy, rfl⟩
    have h_goal : dist (Function.eval 2 (F (A x))) (Function.eval 2 (F (A y))) = |(A x) 2 - (A y) 2| := by
      rw [Real.dist_eq] <;> rfl
    rw [h_goal]
    exact h2 x y hx hy

  have hmain : volume AS' ≤ ∏ i : Fin 3, Metric.ediam (Function.eval i '' AS') :=
    Real.volume_pi_le_prod_diam AS'
  have h_prod : (∏ i : Fin 3, Metric.ediam (Function.eval i '' AS')) ≤
      ENNReal.ofReal (d0 * d1 * d2) := by
    have h_expand : (∏ i : Fin 3, Metric.ediam (Function.eval i '' AS')) =
        Metric.ediam (Function.eval 0 '' AS') * Metric.ediam (Function.eval 1 '' AS') * Metric.ediam (Function.eval 2 '' AS') := by
      simp [Fin.prod_univ_succ] <;> ring
    have h_pos0 : 0 ≤ d0 := hd0_nonneg
    have h_pos1 : 0 ≤ d1 := hd1_nonneg
    have h_pos2 : 0 ≤ d2 := hd2_nonneg
    have h_ofReal_mul : ENNReal.ofReal d0 * ENNReal.ofReal d1 * ENNReal.ofReal d2 = ENNReal.ofReal (d0 * d1 * d2) := by
      have h1 : ENNReal.ofReal d0 * ENNReal.ofReal d1 = ENNReal.ofReal (d0 * d1) :=
        Eq.symm (ENNReal.ofReal_mul hd0_nonneg)
      have h2 : ENNReal.ofReal (d0 * d1) * ENNReal.ofReal d2 = ENNReal.ofReal ((d0 * d1) * d2) :=
        Eq.symm (ENNReal.ofReal_mul (mul_nonneg hd0_nonneg hd1_nonneg))
      have h3 : (d0 * d1) * d2 = d0 * d1 * d2 := by ring
      calc ENNReal.ofReal d0 * ENNReal.ofReal d1 * ENNReal.ofReal d2
        = (ENNReal.ofReal d0 * ENNReal.ofReal d1) * ENNReal.ofReal d2 := by ring
      _ = ENNReal.ofReal (d0 * d1) * ENNReal.ofReal d2 := by rw [h1]
      _ = ENNReal.ofReal ((d0 * d1) * d2) := h2
      _ = ENNReal.ofReal (d0 * d1 * d2) := by rw [h3]
    calc (∏ i : Fin 3, Metric.ediam (Function.eval i '' AS'))
      = Metric.ediam (Function.eval 0 '' AS') * Metric.ediam (Function.eval 1 '' AS') * Metric.ediam (Function.eval 2 '' AS') := h_expand
    _ ≤ ENNReal.ofReal d0 * ENNReal.ofReal d1 * ENNReal.ofReal d2 := by gcongr <;> assumption
    _ = ENNReal.ofReal (d0 * d1 * d2) := h_ofReal_mul

  have h_bound1 : d0 * d1 * d2 ≤ 100 * (r + δ) / σ * δ^2 := by
    exact
      tube_cylinder_volume_coefficient
        hδ hr hs_pos hs_lower hσ

  have h_final : volume S ≤ ENNReal.ofReal (100 * (r + δ) / σ * δ^2) := by
    calc volume S
      = volume AS := hvol
    _ = volume AS' := hvol'.symm
    _ ≤ ∏ i : Fin 3, Metric.ediam (Function.eval i '' AS') := hmain
    _ ≤ ENNReal.ofReal (d0 * d1 * d2) := h_prod
    _ ≤ ENNReal.ofReal (100 * (r + δ) / σ * δ^2) := by gcongr <;> linarith

  have h_eq2 : ENNReal.ofReal (100 * (r + δ) / σ * δ^2) =
      ENNReal.ofReal (100 * (r + δ) / σ) * ENNReal.ofReal (δ ^ 2) := by
    have h_pos1 : 0 ≤ 100 * (r + δ) / σ := by positivity
    have h_pos2 : 0 ≤ δ ^ 2 := by positivity
    rw [←ENNReal.ofReal_mul h_pos1] <;> ring
  rw [h_eq2] at h_final
  exact h_final

end Kakeya.Assouad
