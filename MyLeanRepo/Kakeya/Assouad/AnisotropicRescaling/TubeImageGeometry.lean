import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Geometric covering lemma for anisotropic tube images

Key result: the image of a vertical-chart δ-tube under the anisotropic
rescaling map, restricted to a horizontal slab, is covered by at most
3 ρ-tubes with ρ = 2*δ/(d-c) ≤ 200*sqrt(delta).
-/

noncomputable section

open Kakeya.Assouad Metric

namespace Kakeya.Assouad

/--
Operator norm bound for the anisotropic linear map.

For `A(x,y,z) = (x + g_mid*y, K*y, S*z)` with `|g_mid| ≤ 1`, `|K| ≤ 1`, `S ≥ 2`,
we have `‖A(v)‖ ≤ S * ‖v‖`.
-/
lemma anisotropicMap_opNorm_bound {g_mid K S : ℝ}
    (hg : |g_mid| ≤ 1) (hK : |K| ≤ 1) (hS : 2 ≤ S)
    (v : Point3) :
    ‖point3 (v 0 + g_mid * v 1) (K * v 1) (S * v 2)‖ ≤ S * ‖v‖ := by
  set v0 := v 0 with hv0
  set v1 := v 1 with hv1
  set v2 := v 2 with hv2
  have h1 : (v0 + g_mid * v1)^2 ≤ 2 * (v0^2 + v1^2) := by
    have hcauchy : (v0 + g_mid * v1)^2 ≤ (1 + g_mid^2) * (v0^2 + v1^2) := by
      nlinarith [sq_nonneg (v0 * g_mid - v1), sq_nonneg (v0 + g_mid * v1)]
    have hgm2 : g_mid^2 ≤ 1 := by nlinarith [abs_le.mp hg]
    nlinarith
  have h2 : (K * v1)^2 ≤ v1^2 := by
    have hK2 : K^2 ≤ 1 := by nlinarith [abs_le.mp hK]
    nlinarith
  have h3 : ‖point3 (v0 + g_mid * v1) (K * v1) (S * v2)‖^2 =
      (v0 + g_mid * v1)^2 + (K * v1)^2 + (S * v2)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ, point3]
    <;> ring
  have h4 : (v0 + g_mid * v1)^2 + (K * v1)^2 + (S * v2)^2 ≤
      S^2 * (v0^2 + v1^2 + v2^2) := by
    have h51 : (v0 + g_mid * v1)^2 + (K * v1)^2 ≤ 2 * (v0^2 + v1^2) + v1^2 := by
      exact add_le_add h1 h2
    have h52 : 2 * (v0^2 + v1^2) + v1^2 ≤ 3 * (v0^2 + v1^2) := by
      have h53 : 0 ≤ v0^2 := by positivity
      nlinarith
    have h5 : (v0 + g_mid * v1)^2 + (K * v1)^2 ≤ 3 * (v0^2 + v1^2) :=
      h51.trans h52
    have h6 : 3 * (v0^2 + v1^2) ≤ S^2 * (v0^2 + v1^2) := by
      have h7 : 3 ≤ S^2 := by nlinarith
      have h8 : 0 ≤ v0^2 + v1^2 := by positivity
      nlinarith
    nlinarith
  have h9 : ‖v‖^2 = v0^2 + v1^2 + v2^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ] <;> ring
  have h10 : ‖point3 (v0 + g_mid * v1) (K * v1) (S * v2)‖^2 ≤ S^2 * ‖v‖^2 := by
    rw [h3, h9]
    exact h4
  have h11 : 0 ≤ S * ‖v‖ := by positivity
  have h12 : 0 ≤ ‖point3 (v0 + g_mid * v1) (K * v1) (S * v2)‖ := by positivity
  nlinarith [sq_nonneg (‖point3 (v0 + g_mid * v1) (K * v1) (S * v2)‖ - S * ‖v‖)]

/-- The rho bound: `2*delta/(d-c) ≤ 200*sqrt(delta)` when `d-c ≥ sqrt(delta)/50`. -/
lemma rho_bound_200sqrt {delta c d : ℝ}
    (hdelta : 0 < delta) (hcd : c < d)
    (hsqrt : Real.sqrt delta / 50 ≤ d - c) :
    2 * delta / (d - c) ≤ 200 * Real.sqrt delta := by
  have hpos : 0 < d - c := by linarith [Real.sqrt_pos.mpr hdelta]
  have h : 2 * delta / (d - c) ≤ 2 * delta / (Real.sqrt delta / 50) := by
    gcongr
    <;> linarith
  have h2 : 2 * delta / (Real.sqrt delta / 50) = 100 * Real.sqrt delta := by
    have h3 : 0 < Real.sqrt delta := Real.sqrt_pos.mpr hdelta
    field_simp [h3.ne'] <;> ring_nf
    <;> nlinarith [Real.sq_sqrt (show 0 ≤ delta by linarith)]
  have h3 : 100 * Real.sqrt delta ≤ 200 * Real.sqrt delta := by
    have h4 : 0 ≤ Real.sqrt delta := Real.sqrt_nonneg delta
    nlinarith
  exact h.trans (h2 ▸ h3)

/--
The image of a tube axis subsegment (within the slab) under the anisotropic
linear map has length at most `sqrt(4 + 9*(d-c)^2)`.

For `d-c ≤ 1/25`, this is `< 2.004`, so the segment can be covered by
3 unit subsegments.
-/
lemma anisotropicAxisImage_length_bound {g_mid K S : ℝ}
    {c d : ℝ} (hcd : c < d)
    {dir : Point3} (hd_unit : ‖dir‖ = 1) (hd_z : 1 / 2 ≤ |dir 2|)
    (hg : |g_mid| ≤ 1) (hK : |K| ≤ 1)
    (hS_eq : S = 2 / (d - c)) :
    ((d - c) / |dir 2|) *
      ‖point3 (dir 0 + g_mid * dir 1) (K * dir 1) (S * dir 2)‖ ≤
    Real.sqrt (4 + 9 * (d - c)^2) := by
  set d0 := dir 0 with hd0
  set d1 := dir 1 with hd1
  set d2 := dir 2 with hd2
  set Ad := point3 (d0 + g_mid * d1) (K * d1) (S * d2) with hAd
  have hdz_pos : 0 < |d2| := by linarith
  have hunit2 : d0^2 + d1^2 + d2^2 = 1 := by
    have h : ‖dir‖^2 = d0^2 + d1^2 + d2^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_succ] <;> ring
    have h' : ‖dir‖^2 = 1 := by rw [hd_unit] <;> norm_num
    linarith
  have hAd2 : ‖Ad‖^2 = (d0 + g_mid * d1)^2 + (K * d1)^2 + (S * d2)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [hAd, Fin.sum_univ_succ, point3] <;> ring
  have h1 : (d0 + g_mid * d1)^2 ≤ 2 * (d0^2 + d1^2) := by
    have hcauchy : (d0 + g_mid * d1)^2 ≤ (1 + g_mid^2) * (d0^2 + d1^2) := by
      nlinarith [sq_nonneg (d0 * g_mid - d1)]
    have hgm2 : g_mid^2 ≤ 1 := by nlinarith [abs_le.mp hg]
    nlinarith
  have h2 : (K * d1)^2 ≤ d1^2 := by
    have hK2 : K^2 ≤ 1 := by nlinarith [abs_le.mp hK]
    nlinarith
  have h_main : (((d - c) / |d2|) * ‖Ad‖)^2 ≤ 4 + 9 * (d - c)^2 := by
    have h5 : d0^2 + d1^2 = 1 - d2^2 := by linarith
    have h6 : (d0 + g_mid * d1)^2 + (K * d1)^2 ≤ 3 * (1 - d2^2) := by
      have h71 : (d0 + g_mid * d1)^2 + (K * d1)^2 ≤ 2 * (d0^2 + d1^2) + d1^2 := by
        exact add_le_add h1 h2
      have h72 : 2 * (d0^2 + d1^2) + d1^2 ≤ 3 * (d0^2 + d1^2) := by
        have h73 : 0 ≤ d0^2 := by positivity
        nlinarith
      have h7 : (d0 + g_mid * d1)^2 + (K * d1)^2 ≤ 3 * (d0^2 + d1^2) :=
        h71.trans h72
      have h74 : 3 * (d0^2 + d1^2) = 3 * (1 - d2^2) := by rw [h5]
      rw [h74] at h7
      exact h7
    have hdz2 : d2^2 ≥ 1 / 4 := by
      have h : |d2| ≥ 1 / 2 := hd_z
      have h2 : d2^2 = |d2|^2 := by simp [sq_abs]
      rw [h2]
      nlinarith
    have h_pos2 : 0 < d2^2 := by positivity
    have h_posdc : 0 < (d - c)^2 := by positivity
    set X := (d0 + g_mid * d1)^2 + (K * d1)^2 with hX
    have hXle : X ≤ 3 * (1 - d2^2) := h6
    have h_alg : ((d - c)^2 / d2^2) * (X + S^2 * d2^2) =
        ((d - c)^2 / d2^2) * X + 4 := by
      have hS2 : S^2 = 4 / (d - c)^2 := by
        rw [hS_eq]
        field_simp [show (d - c) ≠ 0 by linarith] <;> ring
      have h : S^2 * d2^2 = 4 * d2^2 / (d - c)^2 := by
        rw [hS2] <;> field_simp <;> ring
      rw [h]
      have hne1 : d2^2 ≠ 0 := h_pos2.ne'
      have hne2 : (d - c)^2 ≠ 0 := h_posdc.ne'
      have h3 : ((d - c)^2 / d2^2) * (4 * d2^2 / (d - c)^2) = 4 := by
        have h_comm : ((d - c)^2 / d2^2) * (4 * d2^2 / (d - c)^2) =
            (((d - c)^2) * (4 * d2^2)) / (d2^2 * (d - c)^2) := by
          rw [div_mul_div_comm]
          <;> ring
        rw [h_comm]
        have h_cancel : (((d - c)^2) * (4 * d2^2)) / (d2^2 * (d - c)^2) = 4 := by
          have h_denom : d2^2 * (d - c)^2 ≠ 0 := mul_ne_zero hne1 hne2
          have h_num : ((d - c)^2) * (4 * d2^2) = 4 * (d2^2 * (d - c)^2) := by ring
          rw [h_num]
          have h_swap : 4 * (d2^2 * (d - c)^2) = (d2^2 * (d - c)^2) * 4 := by ring
          rw [h_swap]
          exact mul_div_cancel_left₀ (4) h_denom
        exact h_cancel
      calc
        ((d - c)^2 / d2^2) * (X + 4 * d2^2 / (d - c)^2)
          = ((d - c)^2 / d2^2) * X +
              ((d - c)^2 / d2^2) * (4 * d2^2 / (d - c)^2) := by ring
        _ = ((d - c)^2 / d2^2) * X + 4 := by rw [h3] <;> ring
    have h10 : ((d - c)^2 / d2^2) * X ≤ 9 * (d - c)^2 := by
      have h11 : ((d - c)^2 / d2^2) * X ≤ ((d - c)^2 / d2^2) * (3 * (1 - d2^2)) := by
        gcongr <;> positivity
      have h12 : 3 * (1 - d2^2) ≤ 9 * d2^2 := by nlinarith
      have h13 : ((d - c)^2 / d2^2) * (3 * (1 - d2^2)) ≤ ((d - c)^2 / d2^2) * (9 * d2^2) := by
        gcongr <;> positivity
      have hne1 : d2^2 ≠ 0 := h_pos2.ne'
      have h14 : ((d - c)^2 / d2^2) * (9 * d2^2) = 9 * (d - c)^2 := by
        have h : ((d - c)^2 / d2^2) * (9 * d2^2) = 9 * (((d - c)^2) * d2^2 / d2^2) := by ring
        rw [h]
        have h2 : ((d - c)^2) * d2^2 / d2^2 = (d - c)^2 := by
          have h_swap : ((d - c)^2) * d2^2 = d2^2 * (d - c)^2 := by ring
          rw [h_swap]
          exact mul_div_cancel_left₀ ((d - c)^2) hne1
        rw [h2] <;> ring
      calc
        ((d - c)^2 / d2^2) * X
          ≤ ((d - c)^2 / d2^2) * (3 * (1 - d2^2)) := h11
        _ ≤ ((d - c)^2 / d2^2) * (9 * d2^2) := h13
        _ = 9 * (d - c)^2 := h14
    have h3 : (((d - c) / |d2|) * ‖Ad‖)^2 = (d - c)^2 / d2^2 * ‖Ad‖^2 := by
      have h4 : |d2|^2 = d2^2 := by simp [sq_abs]
      have h5 : (((d - c) / |d2|) * ‖Ad‖)^2 = (d - c)^2 / |d2|^2 * ‖Ad‖^2 := by ring
      rw [h5, h4] <;> ring
    have h_final : (((d - c) / |d2|) * ‖Ad‖)^2 ≤ 4 + 9 * (d - c)^2 := by
      calc
        (((d - c) / |d2|) * ‖Ad‖)^2
          = (d - c)^2 / d2^2 * ‖Ad‖^2 := h3
        _ = (d - c)^2 / d2^2 * ((d0 + g_mid * d1)^2 + (K * d1)^2 + (S * d2)^2) := by
          rw [hAd2] <;> ring
        _ = (d - c)^2 / d2^2 * (X + S^2 * d2^2) := by
          simp only [hX] <;> ring
        _ = ((d - c)^2 / d2^2) * X + 4 := h_alg
        _ ≤ 9 * (d - c)^2 + 4 := by linarith
        _ = 4 + 9 * (d - c)^2 := by ring
    exact h_final
  have h_nonneg : 0 ≤ ((d - c) / |d2|) * ‖Ad‖ := by
    have h1 : 0 ≤ d - c := by linarith
    have h2 : 0 ≤ |d2| := by positivity
    have h3 : 0 ≤ ‖Ad‖ := by positivity
    exact mul_nonneg (div_nonneg h1 h2) h3
  have h4 : (((d - c) / |d2|) * ‖Ad‖)^2 ≤ (Real.sqrt (4 + 9 * (d - c)^2))^2 := by
    have h5 : 0 ≤ 4 + 9 * (d - c)^2 := by positivity
    rw [Real.sq_sqrt h5]
    exact h_main
  have h6 : 0 ≤ Real.sqrt (4 + 9 * (d - c)^2) := by positivity
  nlinarith [sq_nonneg (((d - c) / |d2|) * ‖Ad‖ - Real.sqrt (4 + 9 * (d - c)^2))]

end Kakeya.Assouad
