import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Vertical chart preservation under anisotropic rescaling
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya Kakeya.Streamlined Metric Set

/--
The anisotropic map preserves the vertical chart property.
For d-c ≤ 1/25, if |v(2)| ≥ 1/2 and ‖v‖ = 1, then
the image direction has |L(v)(2)| / ‖L(v)‖ ≥ 1/2.

Here L(v) = (v0 + g₀*v1, K*v1, 2/(d-c)*v2) where
g₀ = g(mid), K = m*(d-c)/2.

Proof: 4*L2² - ‖L‖² = 3*L2² - L0² - L1² ≥ 0 because
L2² ≥ 625 while L0² + L1² ≤ 3/2 + 1/2500 < 2.
-/
lemma anisotropicMap_preservesVerticalChart
    (g : SlopeFunction) (hg_norm : g.IsNormalized)
    (c d m : ℝ)
    (hcd : c < d) (hm_pos : 0 < m) (hm_le_one : m ≤ 1)
    (h_len : d - c ≤ 1 / 25)
    (h_sub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (v : Point3) (hv_unit : ‖v‖ = 1)
    (hv_vert : (1 / 2 : ℝ) ≤ |v 2|) :
    let g₀ := g (c + (d - c) / 2)
    let K := m * (d - c) / 2
    let L : Point3 := point3 (v 0 + g₀ * v 1) (K * v 1) (2 / (d - c) * v 2)
    (1 / 2 : ℝ) ≤ |L 2| / ‖L‖ := by
  let g₀ := g (c + (d - c) / 2)
  let K := m * (d - c) / 2
  let L : Point3 := point3 (v 0 + g₀ * v 1) (K * v 1) (2 / (d - c) * v 2)
  have hmid_in : c + (d - c) / 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    have h1 : -1 ≤ c := (h_sub ⟨by linarith, by linarith⟩).1
    have h2 : d ≤ 1 := (h_sub ⟨by linarith, by linarith⟩).2
    constructor <;> linarith
  have hg₀_abs : |g₀| ≤ 1 := (hg_norm (c + (d - c) / 2) hmid_in).1
  have hK_nonneg : 0 ≤ K := by positivity
  have hK_le : K ≤ 1 / 50 := by
    dsimp only [K]; nlinarith
  have hvi : ∀ i : Fin 3, |v i| ≤ 1 := by
    intro i
    have hsq : (v i) ^ 2 ≤ ‖v‖ ^ 2 := by
      have h : ‖v‖ ^ 2 = ∑ j : Fin 3, (v j) ^ 2 := EuclideanSpace.real_norm_sq_eq v
      rw [h]
      have h2 : (v i) ^ 2 ≤ ∑ j : Fin 3, (v j) ^ 2 := by
        exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
      exact h2
    have h3 : |v i| ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [sq_abs] <;> exact hsq
    have h4 : |v i| ≤ ‖v‖ := by
      nlinarith [abs_nonneg (v i), norm_nonneg ‖v‖]
    rw [hv_unit] at h4; exact h4
  have hv2_sq : (v 2) ^ 2 ≥ 1 / 4 := by
    have h1 : (v 2) ^ 2 = |v 2| ^ 2 := by rw [sq_abs]
    rw [h1]; nlinarith [hv_vert]
  have h_v01_sq : (v 0) ^ 2 + (v 1) ^ 2 ≤ 3 / 4 := by
    have h_sum : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq v, Fin.sum_univ_succ, Fin.sum_univ_succ]
      <;> simp <;> ring
    rw [hv_unit] at h_sum; nlinarith
  set L0 : ℝ := v 0 + g₀ * v 1 with hL0_def
  set L1 : ℝ := K * v 1 with hL1_def
  set L2 : ℝ := (2 / (d - c)) * v 2 with hL2_def
  have hL0_comp : L 0 = L0 := by
    simp [L, point3] <;> norm_num <;> rfl
  have hL1_comp : L 1 = L1 := by
    simp [L, point3] <;> norm_num <;> rfl
  have hL2_comp : L 2 = L2 := by
    simp [L, point3] <;> norm_num <;> rfl
  have hL0_sq : L0 ^ 2 ≤ 2 * ((v 0) ^ 2 + (v 1) ^ 2) := by
    have h2 : |L0| ≤ |v 0| + |v 1| := by
      calc |L0|
        = |v 0 + g₀ * v 1| := by rfl
      _ ≤ |v 0| + |g₀ * v 1| := by
        exact abs_add_le (v 0) (g₀ * v 1)
      _ = |v 0| + |g₀| * |v 1| := by rw [abs_mul]
      _ ≤ |v 0| + |v 1| := by
        have hg : |g₀| ≤ 1 := hg₀_abs
        have h : |g₀| * |v 1| ≤ |v 1| := by
          calc |g₀| * |v 1| ≤ 1 * |v 1| := by gcongr
               _ = |v 1| := by ring
        linarith
    have h4 : L0 ^ 2 = |L0| ^ 2 := by rw [sq_abs]
    rw [h4]
    have h5 : |L0| ^ 2 ≤ (|v 0| + |v 1|) ^ 2 := by gcongr
    have h6 : (|v 0| + |v 1|) ^ 2 ≤ 2 * ((v 0) ^ 2 + (v 1) ^ 2) := by
      have h71 : |v 0| ^ 2 = (v 0) ^ 2 := by rw [sq_abs]
      have h72 : |v 1| ^ 2 = (v 1) ^ 2 := by rw [sq_abs]
      have h8 : 2 * (|v 0| * |v 1|) ≤ (v 0) ^ 2 + (v 1) ^ 2 := by
        have h9 : (|v 0| - |v 1|) ^ 2 ≥ 0 := by positivity
        have h10 : (|v 0| - |v 1|) ^ 2 = |v 0| ^ 2 + |v 1| ^ 2 - 2 * (|v 0| * |v 1|) := by ring
        rw [h10] at h9
        rw [h71, h72] at h9
        linarith
      have h11 : (|v 0| + |v 1|) ^ 2 = |v 0| ^ 2 + |v 1| ^ 2 + 2 * (|v 0| * |v 1|) := by ring
      rw [h11, h71, h72]
      linarith
    linarith
  have hL1_sq : L1 ^ 2 ≤ 1 / 2500 := by
    rw [hL1_def]
    have h : L1 ^ 2 = K ^ 2 * (v 1) ^ 2 := by ring
    rw [h]
    have hK2 : K ^ 2 ≤ (1 / 50 : ℝ) ^ 2 := by nlinarith
    have hv12 : (v 1) ^ 2 ≤ 1 := by nlinarith [hvi 1, sq_abs (v 1)]
    nlinarith
  have hL2_sq : L2 ^ 2 = (2 / (d - c)) ^ 2 * (v 2) ^ 2 := by
    rw [hL2_def] <;> ring
  have h_dc_pos : 0 < d - c := by linarith
  have hL2_lower : L2 ^ 2 ≥ 625 := by
    rw [hL2_sq]
    have h1 : 2 / (d - c) ≥ 50 := by
      calc 2 / (d - c) ≥ 2 / (1 / 25 : ℝ) := by gcongr
           _ = 50 := by norm_num
    nlinarith [hv2_sq]
  have h_norm_sq : ‖L‖ ^ 2 = L0 ^ 2 + L1 ^ 2 + L2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq L, Fin.sum_univ_succ, Fin.sum_univ_succ]
    <;> simp [hL0_comp, hL1_comp, hL2_comp] <;> ring
  have h_main : 3 * L2 ^ 2 ≥ L0 ^ 2 + L1 ^ 2 := by
    have h_upper1 : L0 ^ 2 ≤ 3 / 2 := by
      calc L0 ^ 2 ≤ 2 * ((v 0) ^ 2 + (v 1) ^ 2) := hL0_sq
           _ ≤ 2 * (3 / 4) := by gcongr
           _ = 3 / 2 := by norm_num
    have h_upper : L0 ^ 2 + L1 ^ 2 ≤ 3 / 2 + 1 / 2500 := by linarith
    have h_lower : 3 * L2 ^ 2 ≥ 1875 := by
      have h : L2 ^ 2 ≥ 625 := hL2_lower
      linarith
    have h : 3 / 2 + 1 / 2500 < 1875 := by norm_num
    linarith
  have h4L2 : 4 * L2 ^ 2 ≥ ‖L‖ ^ 2 := by
    have h : ‖L‖ ^ 2 = L0 ^ 2 + L1 ^ 2 + L2 ^ 2 := h_norm_sq
    rw [h]
    have h' : 4 * L2 ^ 2 ≥ L0 ^ 2 + L1 ^ 2 + L2 ^ 2 := by
      have h'' : 3 * L2 ^ 2 ≥ L0 ^ 2 + L1 ^ 2 := h_main
      linarith
    exact h'
  have hL2_pos : 0 < L2 ^ 2 := by rw [hL2_sq] <;> positivity
  have hpos : 0 < ‖L‖ := by
    have h : ‖L‖ ^ 2 > 0 := by rw [h_norm_sq] <;> positivity
    have h5 : ‖L‖ ≠ 0 := by
      intro h6
      rw [h6] at h
      exact False.elim (by norm_num at h)
    exact lt_of_le_of_ne (norm_nonneg L) (Ne.symm h5)
  have h_abs2_sq : |L 2| ^ 2 = (L 2) ^ 2 := by rw [sq_abs]
  have hL2_abs : |L 2| ^ 2 = L2 ^ 2 := by
    rw [h_abs2_sq, hL2_comp]
  have h_final : (1 / 2 : ℝ) * ‖L‖ ≤ |L 2| := by
    have h5 : ((1 / 2 : ℝ) * ‖L‖) ^ 2 ≤ |L 2| ^ 2 := by
      calc ((1 / 2 : ℝ) * ‖L‖) ^ 2
          = (1 / 4 : ℝ) * ‖L‖ ^ 2 := by ring
        _ ≤ (1 / 4 : ℝ) * (4 * L2 ^ 2) := by gcongr
        _ = L2 ^ 2 := by ring
        _ = |L 2| ^ 2 := by rw [hL2_abs]
    have h6 : 0 ≤ (1 / 2 : ℝ) * ‖L‖ := by positivity
    have h8 : ((1 / 2 : ℝ) * ‖L‖) ≤ |L 2| := by
      have h9 : ((1 / 2 : ℝ) * ‖L‖) ^ 2 ≤ (L 2) ^ 2 := by
        rw [←sq_abs (L 2)]; exact h5
      have h10 : |(1 / 2 : ℝ) * ‖L‖| ≤ |L 2| := by
        exact (sq_le_sq).mp h9
      have h11 : |(1 / 2 : ℝ) * ‖L‖| = (1 / 2 : ℝ) * ‖L‖ := by
        rw [abs_of_nonneg h6]
      rw [h11] at h10
      exact h10
    exact h8
  calc (1 / 2 : ℝ)
      = ((1 / 2 : ℝ) * ‖L‖) / ‖L‖ := by field_simp [hpos.ne'] <;> ring
    _ ≤ |L 2| / ‖L‖ := by gcongr

end Kakeya.Assouad
