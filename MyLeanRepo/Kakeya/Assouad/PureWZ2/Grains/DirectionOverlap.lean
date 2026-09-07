import MyLeanRepo.Kakeya.Assouad.WZ1.PlaneProjectionPerturbation
import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import Mathlib.Tactic

/-!
# Direction-overlap lemma

If two unit vectors W1, W2 are both nearly perpendicular to two transverse
unit vectors u, v (with cross-product norm ≥ kappa), and they lie on the
same side of the span(u,v) plane, then W1 and W2 are close:

  ‖W1 - W2‖ ≤ 8 * eps / kappa

Proof uses the WZ1 plane-projection perturbation infrastructure: each Wi is
close to normalize(cross(u,v)), and the sign condition ensures both are on
the same side, so their mutual distance is at most twice the individual bound.
-/

noncomputable section

namespace Kakeya.Assouad

open Matrix

attribute [local instance] Classical.propDecidable

/-- Direction-overlap lemma with tight constant 6.

The actual proof gives `2 * Real.sqrt 8 * eps / kappa ≈ 5.66 * eps / kappa < 6 * eps / kappa`.
This is the key bound for the Route A Lipschitz gluing argument. -/
lemma direction_overlap_lemma
    {u v w1 w2 : Point3}
    {kappa eps : ℝ}
    (hkappa_pos : 0 < kappa)
    (heps_nonneg : 0 ≤ eps)
    (hu_norm : ‖u‖ = 1)
    (hv_norm : ‖v‖ = 1)
    (hcross : kappa ≤ ‖wz1Cross u v‖)
    (hw1_norm : ‖w1‖ = 1)
    (hw2_norm : ‖w2‖ = 1)
    (hu1 : |inner ℝ u w1| ≤ eps)
    (hv1 : |inner ℝ v w1| ≤ eps)
    (hu2 : |inner ℝ u w2| ≤ eps)
    (hv2 : |inner ℝ v w2| ≤ eps)
    (hsign1 : 0 ≤ inner ℝ (wz1Cross u v) w1)
    (hsign2 : 0 ≤ inner ℝ (wz1Cross u v) w2) :
    ‖w1 - w2‖ ≤ 6 * eps / kappa := by
  let n : Point3 := wz1Cross u v
  have hN_pos : 0 < ‖n‖ := hkappa_pos.trans_le hcross
  have hN_ne_zero : ‖n‖ ≠ 0 := hN_pos.ne'
  let n_hat : Point3 := (‖n‖)⁻¹ • n
  have h_n_hat_norm : ‖n_hat‖ = 1 := by
    rw [show n_hat = (‖n‖)⁻¹ • n from rfl, norm_smul, Real.norm_eq_abs]
    have h1 : |(‖n‖)⁻¹| = (‖n‖)⁻¹ := by
      apply abs_of_pos
      exact inv_pos.mpr hN_pos
    rw [h1]
    field_simp [hN_ne_zero] <;> ring

  let u' : Fin 3 → ℝ := (u : Fin 3 → ℝ)
  let v' : Fin 3 → ℝ := (v : Fin 3 → ℝ)
  let c' : Fin 3 → ℝ := u' ⨯₃ v'
  have hcross_def : (n : Fin 3 → ℝ) = c' := by rfl

  -- Helper: for any unit w with |inner u w| ≤ eps, |inner v w| ≤ eps,
  -- and inner n w ≥ 0, prove ‖w - n_hat‖ ≤ Real.sqrt 8 * eps / kappa
  have h_single : ∀ (w : Point3), ‖w‖ = 1 →
      |inner ℝ u w| ≤ eps → |inner ℝ v w| ≤ eps → 0 ≤ inner ℝ n w →
      ‖w - n_hat‖ ≤ Real.sqrt 8 * eps / kappa := by
    intro w hw_norm hwu hvw hsign
    let w' : Fin 3 → ℝ := (w : Fin 3 → ℝ)
    have h_dot_v : w' ⬝ᵥ v' = inner ℝ w v := by
      have h : inner ℝ w v = w' ⬝ᵥ v' := plane_proj_inner_dot w v
      exact h.symm
    have h_dot_u : u' ⬝ᵥ w' = inner ℝ w u := by
      have h : inner ℝ w u = w' ⬝ᵥ u' := plane_proj_inner_dot w u
      have hcomm : w' ⬝ᵥ u' = u' ⬝ᵥ w' := dotProduct_comm _ _
      rw [hcomm] at h
      exact h.symm
    have h_abs_dot_v : |w' ⬝ᵥ v'| ≤ eps := by
      rw [h_dot_v]
      have hcomm : inner ℝ w v = inner ℝ v w := (real_inner_comm w v).symm
      rw [hcomm] <;> exact hvw
    have h_abs_dot_u : |u' ⬝ᵥ w'| ≤ eps := by
      rw [h_dot_u]
      have hcomm : inner ℝ w u = inner ℝ u w := (real_inner_comm w u).symm
      rw [hcomm] <;> exact hwu

    have h_triple : w' ⨯₃ c' = (w' ⬝ᵥ v') • u' - (u' ⬝ᵥ w') • v' :=
      cross_cross_eq_smul_sub_smul' w' u' v'
    have h_eq_cross : WithLp.toLp 2 (w' ⨯₃ c') =
        (w' ⬝ᵥ v') • u - (u' ⬝ᵥ w') • v := by
      rw [h_triple] <;> rfl
    have h_norm_cross_bound : ‖WithLp.toLp 2 (w' ⨯₃ c')‖ ≤ 2 * eps := by
      rw [h_eq_cross]
      calc
        ‖(w' ⬝ᵥ v') • u - (u' ⬝ᵥ w') • v‖
          ≤ ‖(w' ⬝ᵥ v') • u‖ + ‖(u' ⬝ᵥ w') • v‖ := norm_sub_le _ _
        _ = |w' ⬝ᵥ v'| * ‖u‖ + |u' ⬝ᵥ w'| * ‖v‖ := by
          rw [norm_smul, norm_smul] <;> rfl
        _ = |w' ⬝ᵥ v'| + |u' ⬝ᵥ w'| := by rw [hu_norm, hv_norm] <;> ring
        _ ≤ 2 * eps := by linarith

    let d : ℝ := w' ⬝ᵥ c'
    have h1_dot : (w' ⨯₃ c') ⬝ᵥ (w' ⨯₃ c') =
        (w' ⬝ᵥ w') * (c' ⬝ᵥ c') - d ^ 2 := by
      have h := cross_dot_cross w' c' w' c'
      have h2 : c' ⬝ᵥ w' = w' ⬝ᵥ c' := dotProduct_comm c' w'
      rw [h, h2] <;> ring
    have h_w_norm2 : w' ⬝ᵥ w' = 1 := by
      have h3 := plane_proj_norm_sq w
      simpa using h3.symm.trans (by rw [hw_norm] <;> ring)
    have hN2 : ‖n‖ ^ 2 = c' ⬝ᵥ c' := by
      have h := plane_proj_norm_sq n
      rw [hcross_def] at h
      exact h
    have h_lagrange : ‖WithLp.toLp 2 (w' ⨯₃ c')‖ ^ 2 = ‖n‖ ^ 2 - d ^ 2 := by
      have h4 := plane_proj_toLp_norm_sq (w' ⨯₃ c')
      rw [h4, h1_dot, h_w_norm2, hN2] <;> ring
    have h_nonneg : 0 ≤ ‖n‖ ^ 2 - d ^ 2 := by
      rw [←h_lagrange]
      exact sq_nonneg _
    have h_main_bound : ‖n‖ ^ 2 - d ^ 2 ≤ 4 * eps ^ 2 := by
      have h5 : ‖WithLp.toLp 2 (w' ⨯₃ c')‖ ≤ 2 * eps := h_norm_cross_bound
      have h6 : 0 ≤ ‖WithLp.toLp 2 (w' ⨯₃ c')‖ := norm_nonneg _
      have h7 : ‖WithLp.toLp 2 (w' ⨯₃ c')‖ ^ 2 ≤ (2 * eps) ^ 2 := by
        nlinarith
      have h9 : (2 * eps) ^ 2 = 4 * eps ^ 2 := by ring
      rw [h_lagrange] at h7
      rw [h9] at h7
      exact h7

    let gamma : ℝ := inner ℝ w n_hat
    have h_gamma_eq : gamma = d / ‖n‖ := by
      dsimp only [gamma]
      have h1 : inner ℝ w n_hat = (‖n‖)⁻¹ * inner ℝ w n := by
        have h2 : n_hat = (‖n‖)⁻¹ • n := by rfl
        rw [h2, inner_smul_right] <;> ring
      rw [h1]
      have h3 : inner ℝ w n = w' ⬝ᵥ c' := by
        have h4 := plane_proj_inner_dot w n
        rw [h4, hcross_def] <;> rfl
      rw [h3]
      have h5 : w' ⬝ᵥ c' = d := by rfl
      rw [h5]
      field_simp [hN_ne_zero] <;> ring
    have h_gamma_nonneg : 0 ≤ gamma := by
      rw [h_gamma_eq]
      have h6 : 0 ≤ d := by
        have h7 : inner ℝ w n = w' ⬝ᵥ c' := by
          have h8 := plane_proj_inner_dot w n
          rw [h8, hcross_def] <;> rfl
        have h9 : inner ℝ n w = inner ℝ w n := (real_inner_comm n w).symm
        rw [h9] at hsign
        rw [h7] at hsign
        exact hsign
      exact div_nonneg h6 (by positivity)
    have h_1_minus : 1 - |gamma| ≤ 4 * eps ^ 2 / kappa ^ 2 := by
      rw [h_gamma_eq]
      exact factor_bound hN_pos h_nonneg h_main_bound hkappa_pos hcross
    have h_abs_gamma : |gamma| = gamma := abs_of_nonneg h_gamma_nonneg
    have h_dist_sq : ‖w - n_hat‖ ^ 2 = 2 * (1 - gamma) := by
      have h1 : ‖w - n_hat‖ ^ 2 = ‖w‖ ^ 2 + ‖n_hat‖ ^ 2 - 2 * inner ℝ w n_hat := by
        rw [norm_sub_sq_real w n_hat] <;> ring
      rw [h1, hw_norm, h_n_hat_norm]
      <;> simp [gamma] <;> ring
    have h10 : 1 - gamma ≤ 4 * eps ^ 2 / kappa ^ 2 := by
      have h11 : 1 - |gamma| ≤ 4 * eps ^ 2 / kappa ^ 2 := h_1_minus
      rw [h_abs_gamma] at h11
      exact h11
    have h12 : 2 * (1 - gamma) ≤ 8 * eps ^ 2 / kappa ^ 2 := by
      calc
        2 * (1 - gamma) ≤ 2 * (4 * eps ^ 2 / kappa ^ 2) := by gcongr
        _ = 8 * eps ^ 2 / kappa ^ 2 := by ring
    have h_final_sq : ‖w - n_hat‖ ^ 2 ≤ 8 * eps ^ 2 / kappa ^ 2 := by
      rw [h_dist_sq]
      exact h12
    have h_pos : 0 ≤ ‖w - n_hat‖ := norm_nonneg _
    have h_pos2 : 0 ≤ Real.sqrt 8 * eps / kappa := by positivity
    have h10 : ‖w - n_hat‖ ^ 2 ≤ (Real.sqrt 8 * eps / kappa) ^ 2 := by
      have h11 : (Real.sqrt 8 * eps / kappa) ^ 2 = 8 * eps ^ 2 / kappa ^ 2 := by
        have h12 : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
        have h13 : (Real.sqrt 8 * eps / kappa) ^ 2 = (Real.sqrt 8) ^ 2 * eps ^ 2 / kappa ^ 2 := by
          field_simp [hkappa_pos.ne'] <;> ring
        rw [h13, h12] <;> ring
      rw [h11]
      exact h_final_sq
    nlinarith [h_pos, h_pos2]

  have hsign1' : 0 ≤ inner ℝ n w1 := by
    have h : inner ℝ n w1 = inner ℝ (wz1Cross u v) w1 := by rfl
    rw [h]
    exact hsign1
  have hsign2' : 0 ≤ inner ℝ n w2 := by
    have h : inner ℝ n w2 = inner ℝ (wz1Cross u v) w2 := by rfl
    rw [h]
    exact hsign2

  have h1 : ‖w1 - n_hat‖ ≤ Real.sqrt 8 * eps / kappa :=
    h_single w1 hw1_norm hu1 hv1 hsign1'
  have h2 : ‖w2 - n_hat‖ ≤ Real.sqrt 8 * eps / kappa :=
    h_single w2 hw2_norm hu2 hv2 hsign2'

  have h_main : ‖w1 - w2‖ ≤ ‖w1 - n_hat‖ + ‖w2 - n_hat‖ := by
    calc
      ‖w1 - w2‖ = ‖(w1 - n_hat) - (w2 - n_hat)‖ := by abel
      _ ≤ ‖w1 - n_hat‖ + ‖w2 - n_hat‖ := norm_sub_le _ _
  have h3 : ‖w1 - n_hat‖ + ‖w2 - n_hat‖ ≤ 2 * (Real.sqrt 8 * eps / kappa) := by
    linarith
  have h4 : 2 * (Real.sqrt 8 * eps / kappa) ≤ 6 * eps / kappa := by
    have h5 : 2 * Real.sqrt 8 ≤ 6 := by
      have h6 : Real.sqrt 8 ≤ 3 := by
        rw [Real.sqrt_le_left (by norm_num)] <;> norm_num
      linarith
    have h7 : 0 ≤ eps / kappa := by positivity
    have h8 : 2 * (Real.sqrt 8 * eps / kappa) = (2 * Real.sqrt 8) * (eps / kappa) := by ring
    have h9 : 6 * eps / kappa = 6 * (eps / kappa) := by ring
    rw [h8, h9]
    exact mul_le_mul_of_nonneg_right h5 h7
  calc
    ‖w1 - w2‖ ≤ ‖w1 - n_hat‖ + ‖w2 - n_hat‖ := h_main
    _ ≤ 2 * (Real.sqrt 8 * eps / kappa) := h3
    _ ≤ 6 * eps / kappa := h4

end Kakeya.Assouad

end
