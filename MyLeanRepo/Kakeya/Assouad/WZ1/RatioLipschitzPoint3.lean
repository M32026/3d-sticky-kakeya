import MyLeanRepo.Kakeya.Assouad.WZ1.GlobalPlaninessTransportStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.SlopeConstructionHelpers

/-!
# Construct a height-dependent slope from a Lipschitz plane map

Given a Lipschitz unit plane map on a shading and a subshading where
|n_0| ≥ 1/3, define the ratio n_1/n_0, prove it's Lipschitz, extend
via McShane, and restrict to a vertical line. Clamp to [-3,3].
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/--
Lipschitz bound for the ratio `n_1 / n_0` on a subset of Point3.

If `n : Point3 → Point3` is Lipschitz with constant `L` on `s`,
`|n(p)_0| ≥ c`, `|n(p)_0| ≤ 1`, and `|n(p)_1| ≤ 1` for all p ∈ s,
then `f(p) = n(p)_1 / n(p)_0` is Lipschitz on `s` with constant `2*L/c^2`.
-/
lemma ratio_lipschitz_on_point3
    {n : Point3 → Point3} {L c : ℝ} {s : Set Point3}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ p ∈ s, ∀ q ∈ s, dist (n p) (n q) ≤ L * dist p q)
    (hc_pos : 0 < c)
    (hn0 : ∀ p ∈ s, c ≤ |n p 0|)
    (hn0_bound : ∀ p ∈ s, |n p 0| ≤ 1)
    (hn1 : ∀ p ∈ s, |n p 1| ≤ 1) :
    ∀ p ∈ s, ∀ q ∈ s,
      |n p 1 / n p 0 - n q 1 / n q 0| ≤ (2 * L / c ^ 2) * dist p q := by
  intro p hp q hq
  have h_dist_n : dist (n p) (n q) ≤ L * dist p q := hL p hp q hq
  have h0 : |n p 0 - n q 0| ≤ L * dist p q := by
    have h : |n p 0 - n q 0| ≤ ‖n p - n q‖ := PiLp.norm_apply_le (n p - n q) 0
    have h2 : ‖n p - n q‖ = dist (n p) (n q) := by rfl
    rw [h2] at h
    exact h.trans h_dist_n
  have h1 : |n p 1 - n q 1| ≤ L * dist p q := by
    have h : |n p 1 - n q 1| ≤ ‖n p - n q‖ := PiLp.norm_apply_le (n p - n q) 1
    have h2 : ‖n p - n q‖ = dist (n p) (n q) := by rfl
    rw [h2] at h
    exact h.trans h_dist_n
  have hnp0 : c ≤ |n p 0| := hn0 p hp
  have hnq0 : c ≤ |n q 0| := hn0 q hq
  have hnp1 : |n p 1| ≤ 1 := hn1 p hp
  have hnq1 : |n q 1| ≤ 1 := hn1 q hq
  have h_ne_p : n p 0 ≠ 0 := by
    have : 0 < |n p 0| := by linarith
    exact abs_ne_zero.mp this.ne'
  have h_ne_q : n q 0 ≠ 0 := by
    have : 0 < |n q 0| := by linarith
    exact abs_ne_zero.mp this.ne'
  have h_eq : n p 1 / n p 0 - n q 1 / n q 0 =
      (n p 1 * n q 0 - n q 1 * n p 0) / (n p 0 * n q 0) := by
    field_simp [h_ne_p, h_ne_q] <;> ring
  rw [h_eq]
  have h_abs_pq : 0 ≤ dist p q := dist_nonneg
  have h_num : |n p 1 * n q 0 - n q 1 * n p 0| ≤ 2 * L * dist p q := by
    have h_alg : n p 1 * n q 0 - n q 1 * n p 0 =
        n p 1 * (n q 0 - n p 0) + n p 0 * (n p 1 - n q 1) := by ring
    have h_triangle : |n p 1 * (n q 0 - n p 0) + n p 0 * (n p 1 - n q 1)| ≤
        |n p 1 * (n q 0 - n p 0)| + |n p 0 * (n p 1 - n q 1)| := by
      exact abs_add_le _ _
    have h6 : |n p 1 * (n q 0 - n p 0)| = |n p 1| * |n q 0 - n p 0| := by rw [abs_mul]
    have h7 : |n p 0 * (n p 1 - n q 1)| = |n p 0| * |n p 1 - n q 1| := by rw [abs_mul]
    have h_tri2 : |n p 1 * (n q 0 - n p 0) + n p 0 * (n p 1 - n q 1)| ≤
        |n p 1| * |n q 0 - n p 0| + |n p 0| * |n p 1 - n q 1| := by
      rw [h6, h7] at h_triangle
      exact h_triangle
    have h0' : |n q 0 - n p 0| ≤ L * dist p q := by
      have h_abs : |n q 0 - n p 0| = |n p 0 - n q 0| := by
        rw [show n q 0 - n p 0 = -(n p 0 - n q 0) by ring, abs_neg]
      rw [h_abs]; exact h0
    have h3 : |n p 1| * |n q 0 - n p 0| ≤ L * dist p q := by
      calc
        |n p 1| * |n q 0 - n p 0| ≤ 1 * |n q 0 - n p 0| := by gcongr
        _ = |n q 0 - n p 0| := by ring
        _ ≤ L * dist p q := h0'
    have hnp0_bound : |n p 0| ≤ 1 := hn0_bound p hp
    have h4 : |n p 0| * |n p 1 - n q 1| ≤ L * dist p q := by
      calc
        |n p 0| * |n p 1 - n q 1| ≤ 1 * |n p 1 - n q 1| := by
          exact mul_le_mul_of_nonneg_right hnp0_bound (abs_nonneg _)
        _ = |n p 1 - n q 1| := by ring
        _ ≤ L * dist p q := h1
    have h9 : |n p 1 * (n q 0 - n p 0) + n p 0 * (n p 1 - n q 1)| ≤ 2 * L * dist p q := by
      calc
        _ ≤ |n p 1| * |n q 0 - n p 0| + |n p 0| * |n p 1 - n q 1| := h_tri2
        _ ≤ L * dist p q + L * dist p q := add_le_add h3 h4
        _ = 2 * L * dist p q := by ring
    rw [h_alg]; exact h9
  have h_den : |n p 0 * n q 0| ≥ c ^ 2 := by
    calc
      |n p 0 * n q 0| = |n p 0| * |n q 0| := by rw [abs_mul]
      _ ≥ c * c := by gcongr
      _ = c ^ 2 := by ring
  have hc2_pos : 0 < c ^ 2 := by positivity
  have h_den_pos : 0 < |n p 0 * n q 0| := by
    have h1 : 0 < c ^ 2 := hc2_pos
    have h2 : c ^ 2 ≤ |n p 0 * n q 0| := h_den
    linarith
  have h_main2 : |n p 1 * n q 0 - n q 1 * n p 0| / |n p 0 * n q 0| ≤
      (2 * L * dist p q) / c ^ 2 := by
    have h_div1 : |n p 1 * n q 0 - n q 1 * n p 0| / |n p 0 * n q 0| ≤
        (2 * L * dist p q) / |n p 0 * n q 0| := by
      apply div_le_div_of_nonneg_right h_num
      exact le_of_lt h_den_pos
    have h_div2 : (2 * L * dist p q) / |n p 0 * n q 0| ≤ (2 * L * dist p q) / c ^ 2 := by
      have h_inv : 1 / |n p 0 * n q 0| ≤ 1 / c ^ 2 := by
        apply one_div_le_one_div_of_le
        · positivity
        · exact h_den
      calc
        (2 * L * dist p q) / |n p 0 * n q 0|
          = (2 * L * dist p q) * (1 / |n p 0 * n q 0|) := by ring
        _ ≤ (2 * L * dist p q) * (1 / c ^ 2) := by gcongr
        _ = (2 * L * dist p q) / c ^ 2 := by ring
    exact h_div1.trans h_div2
  calc
    |(n p 1 * n q 0 - n q 1 * n p 0) / (n p 0 * n q 0)|
      = |n p 1 * n q 0 - n q 1 * n p 0| / |n p 0 * n q 0| := by rw [abs_div]
    _ ≤ (2 * L * dist p q) / c ^ 2 := h_main2
    _ = (2 * L / c ^ 2) * dist p q := by ring

end Kakeya.Assouad
