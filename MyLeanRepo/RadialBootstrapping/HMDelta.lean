module

/-
  HMDelta.lean

  Proof of the hM_delta inequality needed by FinalWiring.
  Extracted into a separate file to keep each lemma small.

  Main result: hM_delta_lemma
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal


noncomputable section

namespace RadialBootstrapping

/-- log 2 > 1/2, so 1/log 2 < 2. -/
lemma log2_gt_half : (1 / 2 : ℝ) < Real.log 2 := by
  have h1 : Real.exp (1 / 2 : ℝ) < 2 := by
    have h2 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have h_pos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
    have h3 : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
      have h4 : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
        rw [← Real.exp_add] <;> norm_num
      have h5 : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) := by ring
      rw [h5]; exact h4
    nlinarith [h2, h3, h_pos]
  have h4 : Real.log (Real.exp (1 / 2 : ℝ)) = (1 / 2 : ℝ) := Real.log_exp _
  have h5 : Real.log (Real.exp (1 / 2 : ℝ)) < Real.log 2 := Real.log_lt_log (by positivity) h1
  rw [h4] at h5; exact h5

lemma one_div_log2_lt_two : 1 / Real.log 2 < 2 := by
  have h : (1 / 2 : ℝ) < Real.log 2 := log2_gt_half
  have h2 : 1 / Real.log 2 < 1 / (1 / 2 : ℝ) := by gcongr
  norm_num at h2 ⊢; exact h2

/-- Bound each of the 7 RHS terms by C_total / τ^2 components. -/
lemma hM_delta_term_bounds (τ σ ε_F κ δ₀ : ℝ) (D_X : ℕ) (ε : ℝ)
    (hτ : 0 < τ) (hτ_lt_01 : τ < 1 / 100)
    (hσ_lt_one : σ < 1)
    (hεF_pos : 0 < ε_F) (hεF_large3 : 8 * τ + 3 * κ < ε_F)
    (hδ0_pos : 0 < δ₀) (hδ0_le_one : δ₀ ≤ 1)
    (hD_X_pos : 0 < D_X)
    (hε : 0 < ε) (h_eps_lt_one : ε < 1)
    (hτ_le_epsF : τ ≤ ε_F * ε / 100)
    (hκ_le : κ ≤ 14 * τ / ε) :
    Real.log (8 / τ) / (τ * Real.log 2) < 16 / τ^2 ∧
    400 / (τ^2 * Real.log 2) < 800 / τ^2 ∧
    Real.log 390 / (τ * Real.log 2) < 10 / τ^2 ∧
    (8 : ℝ) < 10 / τ^2 ∧
    Real.log (1 / δ₀) / Real.log 2 ≤ 2 * Real.log (1 / δ₀) / τ^2 ∧
    (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * κ) < 10 / τ^2 ∧
    Real.log (100 * (D_X : ℝ)) / (ε_F * Real.log 2) ≤ 2 * Real.log (100 * (D_X : ℝ)) / τ^2 := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_1div2 : 1 / Real.log 2 < 2 := one_div_log2_lt_two
  have hτ2_lt_one : τ^2 < 1 := by nlinarith
  have hεF_gt_100τ : 100 * τ < ε_F := by
    have h1 : τ ≤ ε_F * ε / 100 := hτ_le_epsF
    have h2 : ε_F * ε / 100 < ε_F / 100 := by
      have h3 : ε_F * ε < ε_F := by nlinarith
      gcongr
    linarith
  have h_denom_gt_half : ε_F - 8 * τ - 3 * κ > ε_F / 2 := by
    have h1 : 8 * τ + 3 * κ ≤ τ * (8 + 42 / ε) := by
      calc 8 * τ + 3 * κ
        ≤ 8 * τ + 3 * (14 * τ / ε) := by gcongr
        _ = τ * (8 + 42 / ε) := by ring
    have h2 : τ * (8 + 42 / ε) ≤ (ε_F * ε / 100) * (8 + 42 / ε) := by gcongr
    have h3 : (ε_F * ε / 100) * (8 + 42 / ε) = ε_F * (8 * ε + 42) / 100 := by
      field_simp [hε.ne'] <;> ring
    rw [h3] at h2
    have h4 : ε_F * (8 * ε + 42) / 100 < ε_F / 2 := by nlinarith
    linarith
  have hlog1δ0_nonneg : 0 ≤ Real.log (1 / δ₀) := by
    have h1 : 1 ≤ 1 / δ₀ := by field_simp [hδ0_pos.ne'] <;> linarith
    exact Real.log_nonneg h1
  have hlog100DX_nonneg : 0 ≤ Real.log (100 * (D_X : ℝ)) := by
    have h21 : D_X ≥ 1 := Nat.succ_le_iff.mpr hD_X_pos
    have h2 : (D_X : ℝ) ≥ 1 := by exact_mod_cast h21
    have h3 : 1 ≤ 100 * (D_X : ℝ) := by nlinarith
    exact Real.log_nonneg h3

  -- T1
  have hT1 : Real.log (8 / τ) / (τ * Real.log 2) < 16 / τ^2 := by
    have h1 : Real.log (8 / τ) < 8 / τ := by
      have h2 : 0 < 8 / τ := by positivity
      have h3 : Real.log (8 / τ) ≤ (8 / τ) - 1 := Real.log_le_sub_one_of_pos h2
      linarith
    have h4 : Real.log (8 / τ) / (τ * Real.log 2) < (8 / τ) / (τ * Real.log 2) := by gcongr <;> positivity
    have h5 : (8 / τ) / (τ * Real.log 2) = 8 / (τ^2 * Real.log 2) := by field_simp [hτ.ne'] <;> ring
    rw [h5] at h4
    have h6 : 8 / (τ^2 * Real.log 2) < 16 / τ^2 := by
      have h7 : 8 / (τ^2 * Real.log 2) = (8 / τ^2) * (1 / Real.log 2) := by field_simp [hτ.ne'] <;> ring
      rw [h7]
      have h8 : (0 : ℝ) < 8 / τ^2 := by positivity
      have h9 : (8 / τ^2) * (1 / Real.log 2) < (8 / τ^2) * 2 := mul_lt_mul_of_pos_left h_1div2 h8
      have h10 : (8 / τ^2) * 2 = 16 / τ^2 := by ring
      rw [h10] at h9; exact h9
    exact lt_trans h4 h6

  -- T2
  have hT2 : 400 / (τ^2 * Real.log 2) < 800 / τ^2 := by
    have h7 : 400 / (τ^2 * Real.log 2) = (400 / τ^2) * (1 / Real.log 2) := by field_simp [hτ.ne'] <;> ring
    rw [h7]
    have h8 : (0 : ℝ) < 400 / τ^2 := by positivity
    have h9 : (400 / τ^2) * (1 / Real.log 2) < (400 / τ^2) * 2 := mul_lt_mul_of_pos_left h_1div2 h8
    have h10 : (400 / τ^2) * 2 = 800 / τ^2 := by ring
    rw [h10] at h9; exact h9

  -- T3
  have hT3 : Real.log 390 / (τ * Real.log 2) < 10 / τ^2 := by
    have h1 : Real.log 390 < 9 * Real.log 2 := by
      have h2 : (390 : ℝ) < (2 : ℝ)^9 := by norm_num
      have h3 : Real.log 390 < Real.log ((2 : ℝ)^9) := Real.log_lt_log (by positivity) h2
      have h4 : Real.log ((2 : ℝ)^9) = 9 * Real.log 2 := by rw [Real.log_pow] <;> ring
      rw [h4] at h3; exact h3
    have h5 : Real.log 390 / (τ * Real.log 2) < (9 * Real.log 2) / (τ * Real.log 2) := by gcongr <;> positivity
    have h6 : (9 * Real.log 2) / (τ * Real.log 2) = 9 / τ := by field_simp [hτ.ne', hlog2_pos.ne'] <;> ring
    rw [h6] at h5
    have h7 : 9 / τ < 10 / τ^2 := by
      have h8 : 0 < τ := hτ
      have h9 : 9 * τ < 10 := by linarith [hτ_lt_01]
      calc 9 / τ
        = (9 * τ) / τ^2 := by field_simp [h8.ne'] <;> ring
      _ < (10 : ℝ) / τ^2 := by gcongr
    exact lt_trans h5 h7

  -- T4
  have hT4 : (8 : ℝ) < 10 / τ^2 := by
    have h1 : (10 : ℝ) / τ^2 > 10 := by
      have h2 : 0 < τ^2 := by positivity
      have h3 : 10 / τ^2 > 10 / 1 := by gcongr
      norm_num at h3 ⊢; exact h3
    linarith

  -- T5
  have hT5 : Real.log (1 / δ₀) / Real.log 2 ≤ 2 * Real.log (1 / δ₀) / τ^2 := by
    have h1 : Real.log (1 / δ₀) / Real.log 2 ≤ 2 * Real.log (1 / δ₀) := by
      have h2 : Real.log (1 / δ₀) / Real.log 2 = Real.log (1 / δ₀) * (1 / Real.log 2) := by ring
      rw [h2]
      have h3 : Real.log (1 / δ₀) * (1 / Real.log 2) ≤ Real.log (1 / δ₀) * 2 :=
        mul_le_mul_of_nonneg_left h_1div2.le hlog1δ0_nonneg
      have h4 : Real.log (1 / δ₀) * 2 = 2 * Real.log (1 / δ₀) := by ring
      rw [h4] at h3; exact h3
    have h3 : 2 * Real.log (1 / δ₀) ≤ 2 * Real.log (1 / δ₀) / τ^2 := by
      have h4 : (1 : ℝ) ≤ 1 / τ^2 := by
        have h5 : 0 < τ^2 := by positivity
        have h6 : 1 / τ^2 ≥ 1 / 1 := by gcongr
        norm_num at h6 ⊢; exact h6
      have h7 : 0 ≤ Real.log (1 / δ₀) := hlog1δ0_nonneg
      calc 2 * Real.log (1 / δ₀)
        = 2 * Real.log (1 / δ₀) * 1 := by ring
      _ ≤ 2 * Real.log (1 / δ₀) * (1 / τ^2) := by gcongr
      _ = 2 * Real.log (1 / δ₀) / τ^2 := by ring
    exact le_trans h1 h3

  -- T6 (c4 bound)
  have hT6 : (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * κ) < 10 / τ^2 := by
    set c4 := (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * κ) with hc4_def
    have h_num_lt : 2 * σ + ε_F + Real.log 80000 / Real.log 2 < 19 + ε_F := by
      have h1 : 2 * σ < 2 := by linarith [hσ_lt_one]
      have h2 : Real.log 80000 / Real.log 2 < 17 := by
        have h3 : Real.log 80000 < 17 * Real.log 2 := by
          have h4 : (80000 : ℝ) < (2 : ℝ)^17 := by norm_num
          have h5 : Real.log 80000 < Real.log ((2 : ℝ)^17) := Real.log_lt_log (by positivity) h4
          have h6 : Real.log ((2 : ℝ)^17) = 17 * Real.log 2 := by rw [Real.log_pow] <;> ring
          rw [h6] at h5; exact h5
        calc Real.log 80000 / Real.log 2
          < (17 * Real.log 2) / Real.log 2 := by gcongr
          _ = 17 := by field_simp [hlog2_pos.ne'] <;> ring
      linarith
    have h_denom_pos : 0 < ε_F - 8 * τ - 3 * κ := by linarith [hεF_large3]
    have hc4_lt : c4 < 38 / ε_F + 2 := by
      rw [hc4_def]
      have h1 : (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * κ) <
          (19 + ε_F) / (ε_F - 8 * τ - 3 * κ) := by gcongr <;> linarith
      have h2 : (19 + ε_F) / (ε_F - 8 * τ - 3 * κ) < (19 + ε_F) / (ε_F / 2) := by
        gcongr <;> linarith
      have h3 : (19 + ε_F) / (ε_F / 2) = 38 / ε_F + 2 := by field_simp [hεF_pos.ne'] <;> ring
      rw [h3] at h2
      exact lt_trans h1 h2
    have h9 : 38 / ε_F < 1 / τ^2 := by
      have h10 : 100 * τ < ε_F := hεF_gt_100τ
      have h11 : 38 / ε_F < 38 / (100 * τ) := by
        have h_pos1 : 0 < 100 * τ := by positivity
        gcongr
      have h12 : 38 / (100 * τ) < 1 / τ^2 := by
        have h13 : 0 < τ := hτ
        have h14 : 38 * τ < 100 := by linarith [hτ_lt_01]
        calc 38 / (100 * τ)
          = (38 * τ) / (100 * τ^2) := by field_simp [h13.ne'] <;> ring
        _ < (100 : ℝ) / (100 * τ^2) := by gcongr
        _ = 1 / τ^2 := by field_simp [h13.ne'] <;> ring
      exact lt_trans h11 h12
    have h10 : (2 : ℝ) < 2 / τ^2 := by
      have h11 : (2 : ℝ) / τ^2 > 2 := by
        have h12 : 0 < τ^2 := by positivity
        have h13 : 2 / τ^2 > 2 / 1 := by gcongr
        norm_num at h13 ⊢; exact h13
      exact h11
    have h13 : c4 < 3 / τ^2 := by
      calc c4 < 38 / ε_F + 2 := hc4_lt
        _ < 1 / τ^2 + 2 / τ^2 := by gcongr
        _ = 3 / τ^2 := by ring
    have h14 : 3 / τ^2 < 10 / τ^2 := by
      have h15 : 0 < τ^2 := by positivity
      exact div_lt_div_of_pos_right (by norm_num) h15
    exact lt_trans h13 h14

  -- T7: use τ^2 < ε_F / 10000 < ε_F < 2 * ε_F * log 2
  have hτ2_lt_epsF : τ^2 < ε_F := by
    have h1 : τ < ε_F / 100 := by linarith [hεF_gt_100τ]
    have h2 : τ^2 < τ * (ε_F / 100) := by
      have h_pos : 0 < τ := hτ
      have h21 : τ * τ < τ * (ε_F / 100) := mul_lt_mul_of_pos_left h1 h_pos
      have h22 : τ^2 = τ * τ := by ring
      rw [h22]; exact h21
    have h3 : τ * (ε_F / 100) < ε_F / 10000 := by
      have h4 : τ < 1 / 100 := hτ_lt_01
      have h5 : 0 < ε_F := hεF_pos
      nlinarith
    have h6 : ε_F / 10000 < ε_F := by
      have h7 : 0 < ε_F := hεF_pos
      nlinarith
    linarith
  have h_2epsF_log2_gt : ε_F < 2 * ε_F * Real.log 2 := by
    have h1 : (1 : ℝ) < 2 * Real.log 2 := by
      have h2 : (1 / 2 : ℝ) < Real.log 2 := log2_gt_half
      linarith
    have h3 : 0 < ε_F := hεF_pos
    nlinarith
  have hτ2_lt_2epsFlog2 : τ^2 < 2 * ε_F * Real.log 2 := by
    calc τ^2 < ε_F := hτ2_lt_epsF
      _ < 2 * ε_F * Real.log 2 := h_2epsF_log2_gt
  have hT7 : Real.log (100 * (D_X : ℝ)) / (ε_F * Real.log 2) ≤
      2 * Real.log (100 * (D_X : ℝ)) / τ^2 := by
    have h_pos : 0 ≤ Real.log (100 * (D_X : ℝ)) := hlog100DX_nonneg
    have h4 : 1 / (ε_F * Real.log 2) ≤ 2 / τ^2 := by
      have h5 : 0 < ε_F * Real.log 2 := by positivity
      have h6 : 0 < τ^2 := by positivity
      have h7 : τ^2 < 2 * ε_F * Real.log 2 := hτ2_lt_2epsFlog2
      have h8 : 1 / (2 * ε_F * Real.log 2) ≤ 1 / τ^2 := one_div_le_one_div_of_le (by positivity) h7.le
      have h9 : 1 / (ε_F * Real.log 2) = 2 * (1 / (2 * ε_F * Real.log 2)) := by ring
      rw [h9]
      have h10 : 2 * (1 / (2 * ε_F * Real.log 2)) ≤ 2 * (1 / τ^2) := by gcongr
      have h11 : 2 * (1 / τ^2) = 2 / τ^2 := by ring
      rw [h11] at h10; exact h10
    calc Real.log (100 * (D_X : ℝ)) / (ε_F * Real.log 2)
      = Real.log (100 * (D_X : ℝ)) * (1 / (ε_F * Real.log 2)) := by ring
    _ ≤ Real.log (100 * (D_X : ℝ)) * (2 / τ^2) := by gcongr
    _ = 2 * Real.log (100 * (D_X : ℝ)) / τ^2 := by ring

  exact ⟨hT1, hT2, hT3, hT4, hT5, hT6, hT7⟩

/-- M * log M > C_total / τ^2 from M > 400/τ² and τ² ≤ 200·exp(-C_total/400). -/
lemma hM_log_M_bound (τ C_total M : ℝ)
    (hτ : 0 < τ) (hτ_lt_01 : τ < 1 / 100)
    (hC_total_pos : 0 < C_total)
    (hM_gt400 : M > 400 / τ^2)
    (hτ2_le : τ^2 ≤ 200 * Real.exp (-C_total / 400)) :
    M * Real.log M > C_total / τ^2 := by
  have h400_t2_gt_one : (1 : ℝ) < 400 / τ^2 := by
    have h1 : τ^2 < 1 / 10000 := by nlinarith [hτ_lt_01]
    have h2 : 400 / τ^2 > 400 / (1 / 10000 : ℝ) := by gcongr
    have h3 : (400 : ℝ) / (1 / 10000 : ℝ) = 4000000 := by norm_num
    rw [h3] at h2
    have h4 : (1 : ℝ) < 4000000 := by norm_num
    linarith
  have hM_pos : 0 < M := by linarith [hM_gt400]
  have hlogM_gt : Real.log M > Real.log (400 / τ^2) := Real.log_lt_log (by positivity) hM_gt400
  have hlog400_pos : 0 < Real.log (400 / τ^2) := Real.log_pos h400_t2_gt_one
  have hM_logM_gt1 : M * Real.log M > (400 / τ^2) * Real.log (400 / τ^2) := by
    nlinarith [hM_gt400, hlogM_gt, hlog400_pos]
  have h400_t2_ge : 400 / τ^2 ≥ 2 * Real.exp (C_total / 400) := by
    have h1 : 0 < Real.exp (-C_total / 400) := Real.exp_pos _
    have h2 : 400 / τ^2 ≥ 400 / (200 * Real.exp (-C_total / 400)) := by gcongr
    have h3 : 400 / (200 * Real.exp (-C_total / 400)) = 2 * Real.exp (C_total / 400) := by
      field_simp [h1.ne'] <;> rw [Real.exp_neg] <;> field_simp <;> ring
    rw [h3] at h2; exact h2
  have hlog400_gt : Real.log (400 / τ^2) > C_total / 400 := by
    have h1 : 400 / τ^2 ≥ 2 * Real.exp (C_total / 400) := h400_t2_ge
    have h2 : 0 < 2 * Real.exp (C_total / 400) := by positivity
    have h3 : Real.log (400 / τ^2) ≥ Real.log (2 * Real.exp (C_total / 400)) := Real.log_le_log (by positivity) h1
    have h4 : Real.log (2 * Real.exp (C_total / 400)) = Real.log 2 + C_total / 400 := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_exp] <;> ring
    rw [h4] at h3
    have h5 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  calc M * Real.log M
    > (400 / τ^2) * Real.log (400 / τ^2) := hM_logM_gt1
  _ ≥ (400 / τ^2) * (C_total / 400) := by gcongr
  _ = C_total / τ^2 := by field_simp <;> ring

/-- The full hM_delta inequality. -/
lemma hM_delta_lemma (τ σ ε_F κ δ₀ C_total M : ℝ) (D_X : ℕ) (ε : ℝ)
    (hτ : 0 < τ) (hτ_lt_01 : τ < 1 / 100)
    (hσ_pos : 0 < σ) (hσ_lt_one : σ < 1)
    (hεF_pos : 0 < ε_F) (hεF_large3 : 8 * τ + 3 * κ < ε_F)
    (hδ0_pos : 0 < δ₀) (hδ0_le_one : δ₀ ≤ 1)
    (hD_X_pos : 0 < D_X)
    (hε : 0 < ε) (h_eps_lt_one : ε < 1)
    (hτ_le_epsF : τ ≤ ε_F * ε / 100)
    (hκ_le : κ ≤ 14 * τ / ε)
    (hτ_le_eps100 : τ ≤ ε / 100)
    (hσ_le : σ ≤ 1 - ε)
    (hM_gt400 : M > 400 / τ^2)
    (hτ2_le : τ^2 ≤ 200 * Real.exp (-C_total / 400))
    (hC_total_pos : 0 < C_total)
    (hC_total_ge : C_total ≥ 2754 + 2 * Real.log (1 / δ₀) + 2 * Real.log (100 * (D_X : ℝ))) :
    M * Real.log M / ((σ + τ) * Real.log 2) >
    Real.log (8 / τ) / (τ * Real.log 2) +
    400 / (τ^2 * Real.log 2) +
    Real.log 390 / (τ * Real.log 2) + 8 +
    Real.log (1 / δ₀) / Real.log 2 +
    (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * κ) +
    Real.log (100 * (D_X : ℝ)) / (ε_F * Real.log 2) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1δ0_nonneg : 0 ≤ Real.log (1 / δ₀) := by
    have h1 : 1 ≤ 1 / δ₀ := by field_simp [hδ0_pos.ne'] <;> linarith
    exact Real.log_nonneg h1
  have hlog100DX_nonneg : 0 ≤ Real.log (100 * (D_X : ℝ)) := by
    have h21 : D_X ≥ 1 := Nat.succ_le_iff.mpr hD_X_pos
    have h2 : (D_X : ℝ) ≥ 1 := by exact_mod_cast h21
    have h3 : 1 ≤ 100 * (D_X : ℝ) := by nlinarith
    exact Real.log_nonneg h3

  have ⟨hT1, hT2, hT3, hT4, hT5, hT6, hT7⟩ :=
    hM_delta_term_bounds τ σ ε_F κ δ₀ D_X ε hτ hτ_lt_01 hσ_lt_one
      hεF_pos hεF_large3 hδ0_pos hδ0_le_one hD_X_pos hε h_eps_lt_one
      hτ_le_epsF hκ_le

  -- Sum RHS < C_total / τ^2
  have hRHS_lt_Ctotal : Real.log (8 / τ) / (τ * Real.log 2) +
      400 / (τ^2 * Real.log 2) +
      Real.log 390 / (τ * Real.log 2) + 8 +
      Real.log (1 / δ₀) / Real.log 2 +
      (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * κ) +
      Real.log (100 * (D_X : ℝ)) / (ε_F * Real.log 2) <
      C_total / τ^2 := by
    set S1 := Real.log (8 / τ) / (τ * Real.log 2) +
        400 / (τ^2 * Real.log 2) +
        Real.log 390 / (τ * Real.log 2) + 8 +
        (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * κ) with hS1_def
    have hS1_lt : Real.log (8 / τ) / (τ * Real.log 2) +
        400 / (τ^2 * Real.log 2) +
        Real.log 390 / (τ * Real.log 2) + 8 +
        (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * κ) <
        (846 : ℝ) / τ^2 := by
      have h1 : Real.log (8 / τ) / (τ * Real.log 2) < 16 / τ^2 := hT1
      have h2 : 400 / (τ^2 * Real.log 2) < 800 / τ^2 := hT2
      have h3 : Real.log 390 / (τ * Real.log 2) < 10 / τ^2 := hT3
      have h4 : (8 : ℝ) < 10 / τ^2 := hT4
      have h5 : (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * κ) < 10 / τ^2 := hT6
      have h_sum5 : Real.log (8 / τ) / (τ * Real.log 2) +
          400 / (τ^2 * Real.log 2) +
          Real.log 390 / (τ * Real.log 2) + 8 +
          (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * κ) <
          (846 : ℝ) / τ^2 := by
        have h_tmp : Real.log (8 / τ) / (τ * Real.log 2) +
            400 / (τ^2 * Real.log 2) +
            Real.log 390 / (τ * Real.log 2) + 8 +
            (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * κ) <
            16 / τ^2 + 800 / τ^2 + 10 / τ^2 + 10 / τ^2 + 10 / τ^2 :=
          add_lt_add (add_lt_add (add_lt_add (add_lt_add h1 h2) h3) h4) h5
        have h_eq : 16 / τ^2 + 800 / τ^2 + 10 / τ^2 + 10 / τ^2 + 10 / τ^2 = (846 : ℝ) / τ^2 := by
          have h_pos : 0 < τ^2 := by positivity
          field_simp [h_pos.ne'] <;> ring
        rw [h_eq] at h_tmp
        exact h_tmp
      exact h_sum5
    have h5 : Real.log (1 / δ₀) / Real.log 2 ≤ 2 * Real.log (1 / δ₀) / τ^2 := hT5
    have h7 : Real.log (100 * (D_X : ℝ)) / (ε_F * Real.log 2) ≤ 2 * Real.log (100 * (D_X : ℝ)) / τ^2 := hT7
    have h_sum : Real.log (8 / τ) / (τ * Real.log 2) +
        400 / (τ^2 * Real.log 2) +
        Real.log 390 / (τ * Real.log 2) + 8 +
        Real.log (1 / δ₀) / Real.log 2 +
        (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * κ) +
        Real.log (100 * (D_X : ℝ)) / (ε_F * Real.log 2) <
        (846 : ℝ) / τ^2 + 2 * Real.log (1 / δ₀) / τ^2 + 2 * Real.log (100 * (D_X : ℝ)) / τ^2 := by
      have h5 : Real.log (1 / δ₀) / Real.log 2 ≤ 2 * Real.log (1 / δ₀) / τ^2 := hT5
      have h7 : Real.log (100 * (D_X : ℝ)) / (ε_F * Real.log 2) ≤ 2 * Real.log (100 * (D_X : ℝ)) / τ^2 := hT7
      linarith [hS1_lt, h5, h7]
    have h11 : 0 < τ^2 := by positivity
    have h12 : (846 : ℝ) < 2754 := by norm_num
    have h13 : 0 ≤ Real.log (1 / δ₀) := hlog1δ0_nonneg
    have h14 : 0 ≤ Real.log (100 * (D_X : ℝ)) := hlog100DX_nonneg
    have h15 : (846 : ℝ) / τ^2 + 2 * Real.log (1 / δ₀) / τ^2 + 2 * Real.log (100 * (D_X : ℝ)) / τ^2 <
        (2754 + 2 * Real.log (1 / δ₀) + 2 * Real.log (100 * (D_X : ℝ))) / τ^2 := by
      have h16 : (846 : ℝ) / τ^2 < (2754 : ℝ) / τ^2 := by gcongr
      have h17 : (2754 + 2 * Real.log (1 / δ₀) + 2 * Real.log (100 * (D_X : ℝ))) / τ^2 =
          (2754 : ℝ) / τ^2 + 2 * Real.log (1 / δ₀) / τ^2 + 2 * Real.log (100 * (D_X : ℝ)) / τ^2 := by
        field_simp [h11.ne'] <;> ring
      rw [h17]
      linarith
    have h18 : (2754 + 2 * Real.log (1 / δ₀) + 2 * Real.log (100 * (D_X : ℝ))) / τ^2 ≤ C_total / τ^2 := by
      gcongr
      <;> linarith [hC_total_ge]
    exact lt_trans h_sum (lt_of_lt_of_le h15 h18)

  -- M * log M > C_total / τ^2
  have hM_logM_gt2 : M * Real.log M > C_total / τ^2 :=
    hM_log_M_bound τ C_total M hτ hτ_lt_01 hC_total_pos hM_gt400 hτ2_le

  -- (σ + τ) * log 2 < 1
  have hστ_lt_one : σ + τ < 1 := by
    have h1 : σ ≤ 1 - ε := hσ_le
    have h2 : τ ≤ ε / 100 := hτ_le_eps100
    linarith
  have h_factor_lt_one : (σ + τ) * Real.log 2 < 1 := by
    have h1 : 0 < σ + τ := by linarith [hσ_pos, hτ]
    have h2 : Real.log 2 < 1 := by
      have h3 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
      have h4 : Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by positivity) h3
      rw [Real.log_exp] at h4; exact h4
    nlinarith [hlog2_pos, hστ_lt_one]

  -- Combine
  have hM_logM_pos : 0 < M * Real.log M := by
    have h1 : 1 < M := by
      have h2 : (1 : ℝ) < 400 / τ^2 := by
        have h3 : τ^2 < 1 / 10000 := by nlinarith [hτ_lt_01]
        have h4 : 400 / τ^2 > 400 / (1 / 10000 : ℝ) := by gcongr
        have h5 : (400 : ℝ) / (1 / 10000 : ℝ) = 4000000 := by norm_num
        rw [h5] at h4
        have h6 : (1 : ℝ) < 4000000 := by norm_num
        linarith
      linarith [hM_gt400]
    have h2 : 0 < Real.log M := Real.log_pos (by linarith)
    positivity
  have h_gt : M * Real.log M / ((σ + τ) * Real.log 2) > M * Real.log M := by
    have h1 : 0 < (σ + τ) * Real.log 2 := by positivity
    have h2 : (σ + τ) * Real.log 2 < 1 := h_factor_lt_one
    have h3 : 1 / ((σ + τ) * Real.log 2) > 1 := by
      apply one_lt_one_div <;> linarith
    have h4 : M * Real.log M / ((σ + τ) * Real.log 2) =
        (M * Real.log M) * (1 / ((σ + τ) * Real.log 2)) := by ring
    rw [h4]
    nlinarith [hM_logM_pos]
  exact lt_trans hRHS_lt_Ctotal (lt_trans hM_logM_gt2 h_gt)

end RadialBootstrapping
