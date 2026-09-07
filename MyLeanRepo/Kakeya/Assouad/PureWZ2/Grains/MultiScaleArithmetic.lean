import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Multi-scale Córdoba arithmetic for PureWZ2

Relaxes the WZ1 `wz1_final_algebra_paper` condition from
`outputLoss ≤ σ/(2+σ)` to just `outputLoss < 1`, which is automatic
in PureWZ2 since `outputLoss ≤ σ/2 < 1/2`.

Also provides parameter selection: for any `outputLoss > 0`, there exist
`ε₁, ε₂, ε₃ > 0` and `inputLoss > 0` satisfying the core condition.
-/

noncomputable section

namespace Kakeya.Assouad

open Finset Real

/-- Relaxed paper-form final covering algebra.

Same as `wz1_final_algebra_paper` but replaces `outputLoss ≤ σ/(2+σ)`
with `outputLoss < 1`. The original condition was only used to derive
`outputLoss < 1`; the core algebra does not need it.
-/
lemma wz1_final_algebra_paper_relaxed
    (delta sigma outputLoss inputLoss epsilon1 epsilon2 epsilon3 rho tau W C K : ℝ)
    (hdelta : 0 < delta)
    (hdelta_one : delta ≤ 1)
    (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (houtputLoss_pos : 0 < outputLoss)
    (houtputLoss_lt_one : outputLoss < 1)
    (hepsilon1_pos : 0 < epsilon1)
    (hepsilon2_pos : 0 < epsilon2)
    (hepsilon3_nonneg : 0 ≤ epsilon3)
    (hinputLoss_pos : 0 < inputLoss)
    (hrho_pos : 0 < rho) (htau_pos : 0 < tau) (hC_pos : 0 < C)
    (hK : 1 ≤ K)
    (hrho_lower : delta ^ (1 - outputLoss) ≤ rho)
    (htau_lower : rho ^ (1 - outputLoss) ≤ tau)
    (hW_bound : 4 * W / rho + 2 ≤ C * delta ^ (-inputLoss))
    (h_cond : outputLoss - inputLoss >
        (1 - outputLoss) * (8 * epsilon1 + epsilon3) +
        (1 - outputLoss)^2 * epsilon2)
    (h_absorb : K * 200 * C * delta ^ (outputLoss - inputLoss -
        ((1 - outputLoss) * (8 * epsilon1 + epsilon3) +
         (1 - outputLoss)^2 * epsilon2)) ≤ 1) :
    K * ((rho ^ (sigma - epsilon1) * tau ^ (3 - sigma - epsilon2)) /
     (rho ^ (1 + 7 * epsilon1 + epsilon3) * tau ^ 2 / 200)) *
    (4 * W / rho + 2) ≤
    delta ^ (-outputLoss) * (tau / rho) ^ (1 - sigma) := by
  set a : ℝ := 8 * epsilon1 + epsilon3 with ha_def
  set p : ℝ := (1 - outputLoss) * a + (1 - outputLoss)^2 * epsilon2 with hp_def
  set m : ℝ := outputLoss - inputLoss - p with hm_def
  have ha_nonneg : 0 ≤ a := by simp only [ha_def] <;> positivity
  have hm_pos : 0 < m := by dsimp only [m, p] <;> linarith
  have h_rho_exp : delta ^ ((1 - outputLoss) * a) ≤ rho ^ a := by
    have h1 : (delta ^ (1 - outputLoss)) ^ a ≤ rho ^ a := by gcongr
    have h2 : (delta ^ (1 - outputLoss)) ^ a = delta ^ ((1 - outputLoss) * a) := by
      rw [← Real.rpow_mul hdelta.le]
    rw [h2] at h1; exact h1
  have h_tau_exp2 : delta ^ ((1 - outputLoss)^2 * epsilon2) ≤
      rho ^ ((1 - outputLoss) * epsilon2) := by
    have h_pos : 0 ≤ (1 - outputLoss) * epsilon2 := by positivity
    have h1 : (delta ^ (1 - outputLoss)) ^ ((1 - outputLoss) * epsilon2) ≤
        rho ^ ((1 - outputLoss) * epsilon2) := by gcongr
    have h2 : (delta ^ (1 - outputLoss)) ^ ((1 - outputLoss) * epsilon2) =
        delta ^ ((1 - outputLoss)^2 * epsilon2) := by
      rw [← Real.rpow_mul hdelta.le] <;> ring
    rw [h2] at h1; exact h1
  have h_tau_exp1 : rho ^ ((1 - outputLoss) * epsilon2) ≤ tau ^ epsilon2 := by
    have h1 : (rho ^ (1 - outputLoss)) ^ epsilon2 ≤ tau ^ epsilon2 := by gcongr
    have h2 : (rho ^ (1 - outputLoss)) ^ epsilon2 = rho ^ ((1 - outputLoss) * epsilon2) := by
      rw [← Real.rpow_mul hrho_pos.le]
    rw [h2] at h1; exact h1
  have h4 : delta ^ p ≤ rho ^ a * tau ^ epsilon2 := by
    have h5 : delta ^ p =
        delta ^ ((1 - outputLoss) * a) * delta ^ ((1 - outputLoss)^2 * epsilon2) := by
      rw [← Real.rpow_add hdelta, hp_def] <;> ring
    rw [h5]
    have h6 : delta ^ ((1 - outputLoss)^2 * epsilon2) ≤ tau ^ epsilon2 :=
      h_tau_exp2.trans h_tau_exp1
    exact mul_le_mul h_rho_exp h6 (by positivity) (by positivity)
  have h5 : K * 200 * C * delta ^ (outputLoss - inputLoss) ≤ rho ^ a * tau ^ epsilon2 := by
    have h6 : outputLoss - inputLoss = p + m := by dsimp only [p, m] <;> ring
    have h7 : delta ^ (outputLoss - inputLoss) = delta ^ p * delta ^ m := by
      rw [h6, Real.rpow_add hdelta p m]
    rw [h7]
    have h8 : K * 200 * C * delta ^ m ≤ 1 := h_absorb
    have h9 : K * 200 * C * (delta ^ p * delta ^ m) ≤ delta ^ p := by
      calc K * 200 * C * (delta ^ p * delta ^ m)
          = delta ^ p * (K * 200 * C * delta ^ m) := by ring
        _ ≤ delta ^ p * 1 := by gcongr
        _ = delta ^ p := by ring
    exact h9.trans h4
  have h_tau2 : (tau ^ 2 : ℝ) = tau ^ (2 : ℝ) := by simp
  have h_ratio : (rho ^ (sigma - epsilon1) * tau ^ (3 - sigma - epsilon2)) /
      (rho ^ (1 + 7 * epsilon1 + epsilon3) * tau ^ 2 / 200) =
      200 * rho ^ (sigma - 1 - a) * tau ^ (1 - sigma - epsilon2) := by
    have h1 : (rho ^ (sigma - epsilon1) * tau ^ (3 - sigma - epsilon2)) /
        (rho ^ (1 + 7 * epsilon1 + epsilon3) * tau ^ 2 / 200) =
        200 * ((rho ^ (sigma - epsilon1) / rho ^ (1 + 7 * epsilon1 + epsilon3)) *
        (tau ^ (3 - sigma - epsilon2) / tau ^ 2)) := by
      field_simp <;> ring
    rw [h1]
    have h2 : rho ^ (sigma - epsilon1) / rho ^ (1 + 7 * epsilon1 + epsilon3) =
        rho ^ (sigma - 1 - a) := by
      rw [← Real.rpow_sub hrho_pos] <;> simp only [ha_def] <;> ring
    have h3 : tau ^ (3 - sigma - epsilon2) / tau ^ 2 = tau ^ (1 - sigma - epsilon2) := by
      rw [h_tau2, ← Real.rpow_sub htau_pos] <;> ring
    rw [h2, h3] <;> ring
  have h_main1 : K * ((rho ^ (sigma - epsilon1) * tau ^ (3 - sigma - epsilon2)) /
      (rho ^ (1 + 7 * epsilon1 + epsilon3) * tau ^ 2 / 200)) * (4 * W / rho + 2) ≤
      K * 200 * C * delta ^ (-inputLoss) * rho ^ (sigma - 1 - a) *
      tau ^ (1 - sigma - epsilon2) := by
    rw [h_ratio]
    have h_pos : 0 < rho ^ (sigma - 1 - a) * tau ^ (1 - sigma - epsilon2) := by positivity
    calc K * (200 * rho ^ (sigma - 1 - a) * tau ^ (1 - sigma - epsilon2)) * (4 * W / rho + 2)
        ≤ K * (200 * rho ^ (sigma - 1 - a) * tau ^ (1 - sigma - epsilon2)) * (C * delta ^ (-inputLoss)) := by
          gcongr <;> exact hW_bound
      _ = K * 200 * C * delta ^ (-inputLoss) * rho ^ (sigma - 1 - a) * tau ^ (1 - sigma - epsilon2) := by ring
  have h_goal2 : K * 200 * C * delta ^ (-inputLoss) * rho ^ (sigma - 1 - a) *
      tau ^ (1 - sigma - epsilon2) ≤ delta ^ (-outputLoss) * (tau / rho) ^ (1 - sigma) := by
    have h_div : (tau / rho) ^ (1 - sigma) = tau ^ (1 - sigma) * rho ^ (sigma - 1) := by
      rw [Real.div_rpow htau_pos.le hrho_pos.le]
      have h_inv : (rho ^ (1 - sigma))⁻¹ = rho ^ (sigma - 1) := by
        have h_neg : sigma - 1 = -(1 - sigma) := by ring
        rw [h_neg, Real.rpow_neg hrho_pos.le]
      rw [div_eq_mul_inv, h_inv]
    rw [h_div]
    have h_d1 : delta ^ (-inputLoss) =
        delta ^ (-outputLoss) * delta ^ (outputLoss - inputLoss) := by
      have h_sum : -outputLoss + (outputLoss - inputLoss) = -inputLoss := by ring
      have h : delta ^ (-outputLoss + (outputLoss - inputLoss)) =
          delta ^ (-outputLoss) * delta ^ (outputLoss - inputLoss) :=
        Real.rpow_add hdelta (-outputLoss) (outputLoss - inputLoss)
      have h2 : delta ^ (-inputLoss) = delta ^ (-outputLoss + (outputLoss - inputLoss)) := by rw [h_sum]
      exact h2.trans h
    have h_r1 : rho ^ (sigma - 1 - a) = rho ^ (sigma - 1) * (rho ^ a)⁻¹ := by
      have h : sigma - 1 - a = (sigma - 1) - a := by ring
      rw [h]; exact Real.rpow_sub hrho_pos (sigma - 1) a
    have h_t1 : tau ^ (1 - sigma - epsilon2) = tau ^ (1 - sigma) * (tau ^ epsilon2)⁻¹ := by
      have h : 1 - sigma - epsilon2 = (1 - sigma) - epsilon2 := by ring
      rw [h]; exact Real.rpow_sub htau_pos (1 - sigma) epsilon2
    have h_factor : K * 200 * C * delta ^ (-inputLoss) * rho ^ (sigma - 1 - a) *
        tau ^ (1 - sigma - epsilon2) =
        (delta ^ (-outputLoss) * tau ^ (1 - sigma) * rho ^ (sigma - 1)) *
        (K * 200 * C * delta ^ (outputLoss - inputLoss) * (rho ^ a * tau ^ epsilon2)⁻¹) := by
      rw [h_d1, h_r1, h_t1] <;> field_simp <;> ring
    rw [h_factor]
    have h_pos_prod : 0 < rho ^ a * tau ^ epsilon2 := by positivity
    have h_frac : K * 200 * C * delta ^ (outputLoss - inputLoss) * (rho ^ a * tau ^ epsilon2)⁻¹ ≤ 1 := by
      have h : K * 200 * C * delta ^ (outputLoss - inputLoss) ≤ rho ^ a * tau ^ epsilon2 := h5
      exact (div_le_one h_pos_prod).mpr h
    have h : (delta ^ (-outputLoss) * tau ^ (1 - sigma) * rho ^ (sigma - 1)) *
        (K * 200 * C * delta ^ (outputLoss - inputLoss) * (rho ^ a * tau ^ epsilon2)⁻¹) ≤
        (delta ^ (-outputLoss) * tau ^ (1 - sigma) * rho ^ (sigma - 1)) * 1 := by gcongr
    simpa [mul_assoc] using h
  exact h_main1.trans h_goal2

/-- Parameter feasibility: for any outputLoss > 0 and σ ∈ (0,1), there exist
ε₁, ε₂, ε₃ > 0 and inputLoss > 0 with inputLoss ≤ outputLoss satisfying
the multi-scale arithmetic condition.

Construction: set C := (1-outputLoss)*9 + (1-outputLoss)^2,
ε₁=ε₂=ε₃ := outputLoss/(4*C), inputLoss := outputLoss/2.
Then RHS = C*ε = outputLoss/4 < outputLoss/2 = outputLoss - inputLoss.
-/
lemma multiscale_arithmetic_feasible
    {sigma outputLoss : ℝ}
    (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (houtputLoss_pos : 0 < outputLoss)
    (houtputLoss_le_half : outputLoss ≤ sigma / 2) :
    ∃ (epsilon1 epsilon2 epsilon3 inputLoss : ℝ),
      0 < epsilon1 ∧ 0 < epsilon2 ∧ 0 < epsilon3 ∧
      0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
      outputLoss - inputLoss >
        (1 - outputLoss) * (8 * epsilon1 + epsilon3) +
        (1 - outputLoss)^2 * epsilon2 := by
  have h1 : 0 < 1 - outputLoss := by linarith
  set C : ℝ := (1 - outputLoss) * 9 + (1 - outputLoss)^2 with hC_def
  have hC_pos : 0 < C := by positivity
  set eps : ℝ := outputLoss / (4 * C) with heps_def
  have heps_pos : 0 < eps := by positivity
  have h_ineq : (1 - outputLoss) * (8 * eps + eps) + (1 - outputLoss)^2 * eps < outputLoss / 2 := by
    have h2 : (1 - outputLoss) * (8 * eps + eps) + (1 - outputLoss)^2 * eps = C * eps := by
      simp [hC_def] <;> ring
    rw [h2]
    have h3 : C * eps = outputLoss / 4 := by
      rw [heps_def] <;> field_simp [hC_pos.ne'] <;> ring
    rw [h3] <;> linarith
  have h_inputLoss_le : outputLoss / 2 ≤ outputLoss := by linarith
  refine ⟨eps, eps, eps, outputLoss / 2, by positivity, by positivity, by positivity, by positivity, h_inputLoss_le, ?_⟩
  have h4 : outputLoss - outputLoss / 2 = outputLoss / 2 := by ring
  rw [h4]
  exact h_ineq

/-- Clean covering-number bound from WZ1 relaxed algebra.

Given the WZ1 algebra conditions, derives:
`K · 200 · ρ^(-8ε₁-ε₃) · τ^(-ε₂) · (4W/ρ + 2) ≤ δ^(-outputLoss)`

This is obtained by dividing the WZ1 algebra conclusion by
`(τ/ρ)^(1-σ) = τ^(1-σ) · ρ^(σ-1)`, simplifying the cube-factor ratio. -/
lemma covering_bound_from_wz1_algebra
    (delta sigma outputLoss inputLoss epsilon1 epsilon2 epsilon3 rho tau W K : ℝ)
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (houtputLoss_pos : 0 < outputLoss)
    (houtputLoss_lt_one : outputLoss < 1)
    (hinputLoss_pos : 0 < inputLoss)
    (hepsilon1_pos : 0 < epsilon1)
    (hepsilon2_pos : 0 < epsilon2)
    (hepsilon3_nonneg : 0 ≤ epsilon3)
    (hrho_pos : 0 < rho) (htau_pos : 0 < tau)
    (hK : 1 ≤ K)
    (hrho_lower : delta ^ (1 - outputLoss) ≤ rho)
    (htau_lower : rho ^ (1 - outputLoss) ≤ tau)
    (hW_bound : 4 * W / rho + 2 ≤ delta ^ (-inputLoss))
    (h_cond : outputLoss - inputLoss >
        (1 - outputLoss) * (8 * epsilon1 + epsilon3) +
        (1 - outputLoss)^2 * epsilon2)
    (h_absorb : K * 200 * delta ^ (outputLoss - inputLoss -
        ((1 - outputLoss) * (8 * epsilon1 + epsilon3) +
         (1 - outputLoss)^2 * epsilon2)) ≤ 1) :
    K * 200 * rho ^ (-8 * epsilon1 - epsilon3) * tau ^ (-epsilon2) *
      (4 * W / rho + 2) ≤ delta ^ (-outputLoss) := by
  set a : ℝ := 8 * epsilon1 + epsilon3 with ha_def
  set p : ℝ := (1 - outputLoss) * a + (1 - outputLoss)^2 * epsilon2 with hp_def
  have hW_bound' : 4 * W / rho + 2 ≤ (1 : ℝ) * delta ^ (-inputLoss) := by
    simpa using hW_bound
  have h_absorb' : K * 200 * (1 : ℝ) * delta ^ (outputLoss - inputLoss - p) ≤ 1 := by
    simpa using h_absorb
  have h_main := wz1_final_algebra_paper_relaxed
    delta sigma outputLoss inputLoss epsilon1 epsilon2 epsilon3 rho tau W (1 : ℝ) K
    hdelta hdelta_one hsigma_pos hsigma_lt_one houtputLoss_pos houtputLoss_lt_one
    hepsilon1_pos hepsilon2_pos hepsilon3_nonneg hinputLoss_pos
    hrho_pos htau_pos (by norm_num) hK
    hrho_lower htau_lower hW_bound' h_cond h_absorb'
  have h1 : rho ^ (sigma - epsilon1) / rho ^ (1 + 7 * epsilon1 + epsilon3) =
      rho ^ (sigma - 1 - a) := by
    rw [← Real.rpow_sub hrho_pos]
    simp only [ha_def] <;> ring
  have h_tau2 : (tau ^ 2 : ℝ) = tau ^ (2 : ℝ) := by simp
  have h2 : tau ^ (3 - sigma - epsilon2) / tau ^ 2 =
      tau ^ (1 - sigma - epsilon2) := by
    rw [h_tau2, ← Real.rpow_sub htau_pos] <;> ring
  have h_ratio : (rho ^ (sigma - epsilon1) * tau ^ (3 - sigma - epsilon2)) /
      (rho ^ (1 + 7 * epsilon1 + epsilon3) * tau ^ 2 / 200) =
      200 * rho ^ (sigma - 1 - a) * tau ^ (1 - sigma - epsilon2) := by
    have h3 : (rho ^ (sigma - epsilon1) * tau ^ (3 - sigma - epsilon2)) /
        (rho ^ (1 + 7 * epsilon1 + epsilon3) * tau ^ 2 / 200) =
        200 * (rho ^ (sigma - epsilon1) / rho ^ (1 + 7 * epsilon1 + epsilon3)) *
          (tau ^ (3 - sigma - epsilon2) / tau ^ 2) := by
      field_simp <;> ring
    rw [h3, h1, h2] <;> ring
  have h_pos1 : 0 < tau ^ (1 - sigma) := by positivity
  have h_pos2 : 0 < rho ^ (sigma - 1) := by positivity
  have h_inv : (rho ^ (1 - sigma))⁻¹ = rho ^ (sigma - 1) := by
    have h_neg1 : (rho ^ (1 - sigma))⁻¹ = rho ^ (-(1 - sigma)) := by
      rw [← Real.rpow_neg hrho_pos.le]
    have h_neg2 : -(1 - sigma) = sigma - 1 := by ring
    rw [h_neg1, h_neg2]
  have h_rhs : (tau / rho) ^ (1 - sigma) =
      tau ^ (1 - sigma) * rho ^ (sigma - 1) := by
    rw [Real.div_rpow htau_pos.le hrho_pos.le, div_eq_mul_inv, h_inv]
  have h_pos_denom : 0 < tau ^ (1 - sigma) * rho ^ (sigma - 1) := mul_pos h_pos1 h_pos2
  have h4 : K * 200 * rho ^ (sigma - 1 - a) * tau ^ (1 - sigma - epsilon2) *
      (4 * W / rho + 2) ≤
      delta ^ (-outputLoss) * (tau ^ (1 - sigma) * rho ^ (sigma - 1)) := by
    have h_main' := h_main
    rw [h_ratio, h_rhs] at h_main'
    have h_assoc : K * (200 * rho ^ (sigma - 1 - a) * tau ^ (1 - sigma - epsilon2)) *
        (4 * W / rho + 2) =
        K * 200 * rho ^ (sigma - 1 - a) * tau ^ (1 - sigma - epsilon2) *
        (4 * W / rho + 2) := by ring
    rw [h_assoc] at h_main'
    exact h_main'
  set X : ℝ := K * 200 * rho ^ (-a) * tau ^ (-epsilon2) * (4 * W / rho + 2) with hX
  set Y : ℝ := delta ^ (-outputLoss) with hY
  set C : ℝ := tau ^ (1 - sigma) * rho ^ (sigma - 1) with hC
  have hC_pos : 0 < C := h_pos_denom
  have h6 : rho ^ (-a) * rho ^ (sigma - 1) = rho ^ (sigma - 1 - a) := by
    rw [← Real.rpow_add hrho_pos] <;> ring
  have h7 : tau ^ (-epsilon2) * tau ^ (1 - sigma) = tau ^ (1 - sigma - epsilon2) := by
    rw [← Real.rpow_add htau_pos] <;> ring
  have h_mult : X * C = K * 200 * rho ^ (sigma - 1 - a) * tau ^ (1 - sigma - epsilon2) *
      (4 * W / rho + 2) := by
    simp only [hX, hC]
    calc
      K * 200 * rho ^ (-a) * tau ^ (-epsilon2) * (4 * W / rho + 2) *
          (tau ^ (1 - sigma) * rho ^ (sigma - 1))
        = K * 200 * (rho ^ (-a) * rho ^ (sigma - 1)) *
          (tau ^ (-epsilon2) * tau ^ (1 - sigma)) * (4 * W / rho + 2) := by ring
      _ = K * 200 * rho ^ (sigma - 1 - a) * tau ^ (1 - sigma - epsilon2) *
          (4 * W / rho + 2) := by rw [h6, h7] <;> ring
  have h5 : X ≤ Y := by
    by_contra h
    have h' : Y < X := by linarith
    have h'' : Y * C < X * C := mul_lt_mul_of_pos_right h' hC_pos
    rw [h_mult] at h''
    linarith
  have h_exp : -a = -8 * epsilon1 - epsilon3 := by
    simp [ha_def] <;> ring
  simpa [hX, hY, h_exp] using h5

end Kakeya.Assouad

end
