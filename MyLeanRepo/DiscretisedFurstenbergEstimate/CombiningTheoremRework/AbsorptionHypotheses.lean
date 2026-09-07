module

/-
  Absorption hypotheses for multiscaleToCombining.

  Proves the three constant-absorption bounds required by
  `MultiscaleToCombining.multiscaleToCombining`:
    h_absorb_normal, h_absorb_good_high, h_absorb_good_low.
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace DirecretisedFurstenbergEstimate.MultiscaleDecomposition

/-- For any positive constants K and C_P, there exists δ₀ > 0 such that
    for all 0 < δ < δ₀, K ≤ Real.rpow (Real.log (1 / δ)) C_P. -/
lemma const_le_polylog (K C_P : ℝ) (hK : 0 < K) (hCP : 0 < C_P) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      K ≤ Real.rpow (Real.log (1 / δ)) C_P := by
  let y : ℝ := 1 / C_P
  have hy_ne : y ≠ 0 := one_div_ne_zero hCP.ne'
  have h_y_inv : y⁻¹ = C_P := by
    dsimp only [y]
    <;> field_simp [hCP.ne']
  let L₀ : ℝ := Real.rpow K y
  have hL₀_pos : 0 < L₀ := Real.rpow_pos_of_pos hK _
  let δ₀ : ℝ := Real.exp (-L₀)
  have hδ₀_pos : 0 < δ₀ := by positivity
  have h_log₀ : Real.log (1 / δ₀) = L₀ := by
    have h1 : 1 / δ₀ = Real.exp L₀ := by
      simp [δ₀, Real.exp_neg] <;> field_simp
    rw [h1, Real.log_exp]
  have h_rpow₀ : Real.rpow (Real.log (1 / δ₀)) C_P = K := by
    rw [h_log₀]
    have h4 : Real.rpow (Real.rpow K y) y⁻¹ = K := Real.rpow_rpow_inv hK.le hy_ne
    rw [h_y_inv] at h4
    exact h4
  refine' ⟨δ₀, hδ₀_pos, _⟩
  intro δ hδ_pos hδ_lt
  have h_gt : 1 / δ > 1 / δ₀ := by gcongr
  have h_log_gt : Real.log (1 / δ) > Real.log (1 / δ₀) :=
    Real.log_lt_log (by positivity) h_gt
  have h_log₁_nonneg : 0 ≤ Real.log (1 / δ₀) := by
    have h4 : Real.log (1 / δ₀) = L₀ := h_log₀
    linarith [hL₀_pos]
  have h_log_nonneg : 0 ≤ Real.log (1 / δ) := by linarith
  have h5 : Real.rpow (Real.log (1 / δ₀)) C_P ≤ Real.rpow (Real.log (1 / δ)) C_P :=
    Real.rpow_le_rpow h_log₁_nonneg (by linarith) (by linarith [hCP])
  rw [h_rpow₀] at h5
  exact h5

/-- Absorption bound for normal scales. -/
lemma absorb_normal (K C_P ε_bad ε_N ratio δ_k : ℝ)
    (hK : 0 < K) (hCP : 0 < C_P)
    (hε_bad : 0 ≤ ε_bad) (hε_N : 0 < ε_N)
    (h_gap : ε_bad < ε_N)
    (hratio_one : 1 ≤ ratio)
    (hδ_k_pos : 0 < δ_k) (hδ_k_lt_one : δ_k < 1)
    (h_core : K ≤ Real.rpow (Real.log (1 / δ_k)) C_P) :
    K * Real.rpow ratio ε_bad ≤
      Real.rpow (Real.log (1 / δ_k)) C_P * Real.rpow ratio ε_N := by
  have hratio_nonneg : 0 ≤ ratio := by linarith
  have h1 : Real.rpow ratio ε_bad ≤ Real.rpow ratio ε_N :=
    Real.rpow_le_rpow_of_exponent_le hratio_one (by linarith)
  have hlog_pos : 0 < Real.log (1 / δ_k) := by
    have h1 : 1 < 1 / δ_k := one_lt_one_div hδ_k_pos hδ_k_lt_one
    exact Real.log_pos h1
  have hlog_nonneg : 0 ≤ Real.rpow (Real.log (1 / δ_k)) C_P :=
    Real.rpow_nonneg hlog_pos.le C_P
  have hratio_pow_nonneg : 0 ≤ Real.rpow ratio ε_bad :=
    Real.rpow_nonneg hratio_nonneg ε_bad
  have h2 : K * Real.rpow ratio ε_bad ≤
      Real.rpow (Real.log (1 / δ_k)) C_P * Real.rpow ratio ε_bad :=
    mul_le_mul_of_nonneg_right h_core hratio_pow_nonneg
  have h3 : Real.rpow (Real.log (1 / δ_k)) C_P * Real.rpow ratio ε_bad ≤
      Real.rpow (Real.log (1 / δ_k)) C_P * Real.rpow ratio ε_N :=
    mul_le_mul_of_nonneg_left h1 hlog_nonneg
  exact le_trans h2 h3

/-- Absorption bound for good-high scales (t_j ≥ t). -/
lemma absorb_good_high (K C_P ε_bad ε_G ratio δ_k : ℝ)
    (hK : 0 < K) (hCP : 0 < C_P)
    (hε_bad : 0 ≤ ε_bad) (hε_G : 0 < ε_G)
    (h_gap : ε_bad < ε_G)
    (hratio_one : 1 ≤ ratio)
    (hδ_k_pos : 0 < δ_k) (hδ_k_lt_one : δ_k < 1)
    (h_core : K ≤ Real.rpow (Real.log (1 / δ_k)) C_P) :
    K * Real.rpow ratio ε_bad ≤
      Real.rpow (Real.log (1 / δ_k)) C_P * Real.rpow ratio ε_G :=
  absorb_normal K C_P ε_bad ε_G ratio δ_k hK hCP hε_bad hε_G h_gap hratio_one
    hδ_k_pos hδ_k_lt_one h_core

/-- Absorption bound for good-low scales (t - ε_G/2 ≤ t_j < t). -/
lemma absorb_good_low (K C_P ε_bad ε_G ratio δ_k : ℝ)
    (hK : 0 < K) (hCP : 0 < C_P)
    (hε_bad : 0 ≤ ε_bad) (hε_G : 0 < ε_G)
    (h_gap : ε_bad < ε_G / 2)
    (hratio_one : 1 ≤ ratio)
    (hδ_k_pos : 0 < δ_k) (hδ_k_lt_one : δ_k < 1)
    (h_core : K ≤ Real.rpow (Real.log (1 / δ_k)) C_P) :
    K * Real.rpow ratio ε_bad * Real.rpow ratio (ε_G / 2) ≤
      Real.rpow (Real.log (1 / δ_k)) C_P * Real.rpow ratio ε_G := by
  have hratio_pos : 0 < ratio := by linarith
  have hratio_nonneg : 0 ≤ ratio := by linarith
  have h_sum : Real.rpow ratio ε_bad * Real.rpow ratio (ε_G / 2) =
      Real.rpow ratio (ε_bad + ε_G / 2) := by
    exact Eq.symm (Real.rpow_add hratio_pos ε_bad (ε_G / 2))
  have h_gap2 : ε_bad + ε_G / 2 ≤ ε_G := by linarith
  have h1 : Real.rpow ratio (ε_bad + ε_G / 2) ≤ Real.rpow ratio ε_G :=
    Real.rpow_le_rpow_of_exponent_le hratio_one h_gap2
  have hlog_pos : 0 < Real.log (1 / δ_k) := by
    have h1 : 1 < 1 / δ_k := one_lt_one_div hδ_k_pos hδ_k_lt_one
    exact Real.log_pos h1
  have hlog_nonneg : 0 ≤ Real.rpow (Real.log (1 / δ_k)) C_P :=
    Real.rpow_nonneg hlog_pos.le C_P
  have h_main : K * (Real.rpow ratio ε_bad * Real.rpow ratio (ε_G / 2)) ≤
      Real.rpow (Real.log (1 / δ_k)) C_P * Real.rpow ratio ε_G := by
    have h5 : K * (Real.rpow ratio ε_bad * Real.rpow ratio (ε_G / 2)) =
        K * Real.rpow ratio (ε_bad + ε_G / 2) := by rw [h_sum]
    rw [h5]
    have hratio_pow_nonneg : 0 ≤ Real.rpow ratio (ε_bad + ε_G / 2) :=
      Real.rpow_nonneg hratio_nonneg (ε_bad + ε_G / 2)
    have h6 : K * Real.rpow ratio (ε_bad + ε_G / 2) ≤
        Real.rpow (Real.log (1 / δ_k)) C_P * Real.rpow ratio (ε_bad + ε_G / 2) :=
      mul_le_mul_of_nonneg_right h_core hratio_pow_nonneg
    have h7 : Real.rpow (Real.log (1 / δ_k)) C_P * Real.rpow ratio (ε_bad + ε_G / 2) ≤
        Real.rpow (Real.log (1 / δ_k)) C_P * Real.rpow ratio ε_G :=
      mul_le_mul_of_nonneg_left h1 hlog_nonneg
    exact le_trans h6 h7
  have h_assoc : K * Real.rpow ratio ε_bad * Real.rpow ratio (ε_G / 2) =
      K * (Real.rpow ratio ε_bad * Real.rpow ratio (ε_G / 2)) := by ring
  rw [h_assoc]
  exact h_main

end DirecretisedFurstenbergEstimate.MultiscaleDecomposition
