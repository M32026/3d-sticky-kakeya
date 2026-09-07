module

/-
  BComponentBounds.lean

  Applies general_threshold_bound to each component of B.
  Every component exceeds 8 / Q^(M/(σ+τ)).
-/

public import MyLeanRepo.RadialBootstrapping.ThresholdBounds
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Classical
open scoped ENNReal NNReal


noncomputable section

namespace RadialBootstrapping

-- Helper: Q > 1 from assumptions
lemma hQ_gt_one_of (Q τ : ℝ) (hQ_large : Q > 4000 / τ^2)
    (hτ_pos : 0 < τ) (hτ_lt_one : τ < 1) : 1 < Q := by
  have h1 : τ^2 < 1 := by nlinarith
  have h2 : 1 / τ^2 > 1 := one_lt_one_div (by positivity) h1
  have h3 : 4000 / τ^2 > 4000 := by
    have h4 : 4000 / τ^2 = 4000 * (1 / τ^2) := by ring
    rw [h4]
    have h5 : 4000 * (1 / τ^2) > 4000 * (1 : ℝ) := by
      exact mul_lt_mul_of_pos_left h2 (by norm_num)
    simpa using h5
  linarith

lemma hQ_gt_4000_of (Q τ : ℝ) (hQ_large : Q > 4000 / τ^2)
    (hτ_pos : 0 < τ) (hτ_lt_one : τ < 1) : Q > 4000 := by
  have h1 : 1 < Q := hQ_gt_one_of Q τ hQ_large hτ_pos hτ_lt_one
  have h2 : τ^2 < 1 := by nlinarith
  have h3 : 1 / τ^2 > 1 := one_lt_one_div (by positivity) h2
  have h4 : 4000 / τ^2 > 4000 := by
    have h5 : 4000 / τ^2 = 4000 * (1 / τ^2) := by ring
    rw [h5]
    have h6 : 4000 * (1 / τ^2) > 4000 * (1 : ℝ) := by
      exact mul_lt_mul_of_pos_left h3 (by norm_num)
    simpa using h6
  linarith

lemma hQ_pos_of (Q τ : ℝ) (hQ_large : Q > 4000 / τ^2) (hτ_pos : 0 < τ) : 0 < Q := by
  have hτ2_pos : 0 < τ^2 := by positivity
  have h4000_pos : 0 < (4000 : ℝ) / τ^2 := by positivity
  exact lt_trans h4000_pos hQ_large

/-- If c ≥ 1/10^7, then c ≥ Q^(-100) since Q > 4000. -/
lemma c_ge_q_neg100 (Q τ : ℝ) (hQ_large : Q > 4000 / τ^2)
    (hτ_pos : 0 < τ) (hτ_lt_one : τ < 1)
    (c : ℝ) (hc : c ≥ 1 / 10^7) : c ≥ Real.rpow Q (-100) := by
  have hQ_pos : 0 < Q := hQ_pos_of Q τ hQ_large hτ_pos
  have hQ_nonneg : 0 ≤ Q := hQ_pos.le
  have hQ_gt_one : 1 < Q := hQ_gt_one_of Q τ hQ_large hτ_pos hτ_lt_one
  have hQ2_gt_107 : Q^2 > (10^7 : ℝ) := by
    have h2 : Q > 4000 := hQ_gt_4000_of Q τ hQ_large hτ_pos hτ_lt_one
    nlinarith
  have h1 : Real.rpow Q 100 > (10^7 : ℝ) := by
    have h3 : Real.rpow Q 100 ≥ Real.rpow Q 2 :=
      Real.rpow_le_rpow_of_exponent_le hQ_gt_one.le (show (2 : ℝ) ≤ (100 : ℝ) by norm_num)
    have h4 : Real.rpow Q 2 = Q^2 := by simp
    rw [h4] at h3
    linarith [hQ2_gt_107]
  have h5 : Real.rpow Q (-100) = (Real.rpow Q 100)⁻¹ := Real.rpow_neg hQ_nonneg 100
  rw [h5]
  have h6 : (Real.rpow Q 100)⁻¹ < 1 / (10^7 : ℝ) := by
    have h7 : 0 < Real.rpow Q 100 := Real.rpow_pos_of_pos hQ_pos 100
    have h8 : (Real.rpow Q 100)⁻¹ = 1 / Real.rpow Q 100 := by
      field_simp [h7.ne'] <;> ring
    rw [h8]
    gcongr <;> linarith
  have h9 : c ≥ 1 / (10^7 : ℝ) := hc
  linarith

/-- If c ≥ 1/(const * Q^3) and const ≤ 10^7, then c ≥ Q^(-100). -/
lemma inv_Q3_ge_q_neg100 (Q τ : ℝ) (hQ_large : Q > 4000 / τ^2)
    (hτ_pos : 0 < τ) (hτ_lt_one : τ < 1)
    (c const : ℝ) (hc : c ≥ 1 / (const * Q^3))
    (hconst_pos : 0 < const) (hconst_le : const ≤ 10^7) :
    c ≥ Real.rpow Q (-100) := by
  have hQ_pos : 0 < Q := hQ_pos_of Q τ hQ_large hτ_pos
  have hQ_nonneg : 0 ≤ Q := hQ_pos.le
  have hQ_gt_one : 1 < Q := hQ_gt_one_of Q τ hQ_large hτ_pos hτ_lt_one
  have hQ_gt_4000 : Q > 4000 := hQ_gt_4000_of Q τ hQ_large hτ_pos hτ_lt_one
  have hQ2_gt_107 : Q^2 > (10^7 : ℝ) := by
    have h1 : Q > 4000 := hQ_gt_4000
    nlinarith
  have h_const_lt_Q2 : const < Q^2 := by
    have h1 : const ≤ (10^7 : ℝ) := hconst_le
    linarith
  have h4 : const * Q^3 < Q^100 := by
    have h5 : const * Q^3 < Q^2 * Q^3 := by
      gcongr
      <;> linarith
    have h6 : Q^2 * Q^3 = Q^5 := by ring
    rw [h6] at h5
    have h7 : Q^5 ≤ Q^100 := by
      have h8 : (5 : ℝ) ≤ (100 : ℝ) := by norm_num
      have h9 : Real.rpow Q 5 ≤ Real.rpow Q 100 :=
        Real.rpow_le_rpow_of_exponent_le hQ_gt_one.le h8
      have h10 : Real.rpow Q 5 = Q^5 := by simp
      have h11 : Real.rpow Q 100 = Q^100 := by simp
      rw [h10, h11] at h9
      exact h9
    linarith
  have h7 : Real.rpow Q (-100) = (Real.rpow Q 100)⁻¹ := Real.rpow_neg hQ_nonneg 100
  rw [h7]
  have h8 : 0 < Real.rpow Q 100 := Real.rpow_pos_of_pos hQ_pos 100
  have h9 : (Real.rpow Q 100)⁻¹ ≤ 1 / (const * Q^3) := by
    have h10 : (Real.rpow Q 100)⁻¹ = 1 / Real.rpow Q 100 := by
      field_simp [h8.ne'] <;> ring
    rw [h10]
    have h11 : Real.rpow Q 100 = Q^100 := by simp
    rw [h11]
    gcongr
    <;> linarith
  have h13 : 1 / (const * Q^3) ≤ c := hc
  linarith

section Bounds

variable (Q M σ τ ε_F κ C K : ℝ)
variable (D_T D_X : ℕ)
variable (hQ_large : Q > 4000 / τ^2)
variable (hM_large : M > 400 / τ^2)
variable (hτ_pos : 0 < τ) (hτ_lt_one : τ < 1) (hτ_small : τ < 1 / 14)
variable (hστ_pos : 0 < σ + τ) (hστ_lt_two : σ + τ < 2)
variable (hσ_pos : 0 < σ) (hσ_lt_one : σ < 1)
variable (hτ_very_small : τ < (1 - σ) / 14)
variable (hεF_large : ε_F > 8 * τ + 3 * κ)
variable (hκ_nonneg : 0 ≤ κ)
variable (hC : 1 ≤ C) (hK : 1 ≤ K)
variable (hK_le_Q : K ≤ Q) (hC_le_Q : C ≤ Q)
variable (hDT_pos : 0 < D_T) (hDX_pos : 0 < D_X)
variable (hDT_le_Q : (D_T : ℝ) ≤ Q) (hDX_le_Q : (D_X : ℝ) ≤ Q)
variable (hQ_huge : Q ≥ (2 : ℝ)^(ε_F + 2))

include Q M σ τ ε_F κ C K D_T D_X
include hQ_large hM_large hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
include hσ_pos hσ_lt_one hτ_very_small hεF_large hκ_nonneg
include hC hK hK_le_Q hC_le_Q hDT_pos hDX_pos hDT_le_Q hDX_le_Q hQ_huge

/-- r_CB bound -/
lemma r_CB_bound :
    Real.rpow ((2 : ℝ)^(-ε_F) / (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7))
      (1 / (ε_F - κ - 5 * τ)) >
    8 / Real.rpow Q (M / (σ + τ)) := by
  set e : ℝ := ε_F - κ - 5 * τ with he_def
  have he_pos : 0 < e := by linarith
  have he_ge : e ≥ τ / 2 := by linarith
  have h1 : e ≥ 2 * τ := by linarith
  have h_ratio : (2 + 0) / e ≤ 1 / τ := by
    have h2 : (2 : ℝ) / e ≤ 2 / (2 * τ) := by gcongr <;> linarith
    have h3 : (2 : ℝ) / (2 * τ) = 1 / τ := by
      field_simp [hτ_pos.ne'] <;> ring
    rw [h3] at h2
    simpa using h2
  set c0 : ℝ := (2 : ℝ)^(-ε_F) / (60000 * (34 : ℝ)^σ * (D_T : ℝ)^7) with hc0_def
  have hc0_pos : 0 < c0 := by dsimp only [c0]; positivity
  have h34σ_le : (34 : ℝ)^σ ≤ 34 := by
    have h1 : 0 ≤ σ := by linarith
    have h2 : σ ≤ 1 := by linarith
    have h3 : (34 : ℝ)^σ ≤ (34 : ℝ)^(1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
    have h4 : (34 : ℝ)^(1 : ℝ) = 34 := by simp
    rw [h4] at h3
    exact h3
  have h_denom_le : 60000 * (34 : ℝ)^σ * (D_T : ℝ)^7 ≤ Q^9 := by
    have h1 : 60000 * (34 : ℝ)^σ ≤ Q^2 := by
      have h2 : 60000 * (34 : ℝ)^σ ≤ 60000 * 34 := by gcongr
      have h3 : Q > 4000 := hQ_gt_4000_of Q τ hQ_large hτ_pos hτ_lt_one
      nlinarith
    have h4 : (D_T : ℝ)^7 ≤ Q^7 := by gcongr <;> linarith
    calc 60000 * (34 : ℝ)^σ * (D_T : ℝ)^7
      ≤ Q^2 * Q^7 := by gcongr
    _ = Q^9 := by ring
  have h2_neg_ge : (2 : ℝ)^(-ε_F) ≥ 4 / Q := by
    have h1 : Q ≥ (2 : ℝ)^(ε_F + 2) := hQ_huge
    have h_pos : 0 < (2 : ℝ)^(ε_F + 2) := by positivity
    have h2 : (2 : ℝ)^(-ε_F) = (2 : ℝ)^(-(ε_F + 2)) * (2 : ℝ)^(2 : ℝ) := by
      have h3 : -ε_F = (-(ε_F + 2)) + (2 : ℝ) := by ring
      rw [h3, Real.rpow_add (by norm_num)] <;> ring
    have h4 : (2 : ℝ)^(-(ε_F + 2)) = ((2 : ℝ)^(ε_F + 2))⁻¹ := by
      rw [Real.rpow_neg (by norm_num)] <;> ring
    have h5 : (2 : ℝ)^(2 : ℝ) = 4 := by norm_num
    rw [h2, h4, h5]
    have h6 : 1 / ((2 : ℝ)^(ε_F + 2)) ≥ 1 / Q := by
      apply one_div_le_one_div_of_le h_pos
      exact h1
    have h7 : ((2 : ℝ)^(ε_F + 2))⁻¹ = 1 / ((2 : ℝ)^(ε_F + 2)) := by
      simp [one_div]
    rw [h7]
    have h8 : 1 / ((2 : ℝ)^(ε_F + 2)) * 4 ≥ (1 / Q) * 4 := by
      gcongr
    have h9 : (1 / Q) * 4 = 4 / Q := by ring
    rw [h9] at h8
    exact h8
  have hQ_pos : 0 < Q := hQ_pos_of Q τ hQ_large hτ_pos
  have hQ_nonneg : 0 ≤ Q := hQ_pos.le
  have h_c_lower : c0 ≥ Real.rpow Q (-100) := by
    have h41 : c0 ≥ (4 / Q) / Q^9 := by
      rw [hc0_def]
      have h5 : (2 : ℝ)^(-ε_F) ≥ 4 / Q := h2_neg_ge
      have h6 : 60000 * (34 : ℝ)^σ * (D_T : ℝ)^7 ≤ Q^9 := h_denom_le
      gcongr <;> linarith
    have h42 : (4 / Q) / Q^9 = 4 / Q^10 := by
      field_simp [hQ_pos.ne'] <;> ring
    rw [h42] at h41
    have h43 : c0 ≥ 4 / Q^10 := h41
    have h51 : Real.rpow Q (-100) = (Real.rpow Q 100)⁻¹ := Real.rpow_neg hQ_nonneg 100
    have h5 : (4 : ℝ) / Q^10 ≥ Real.rpow Q (-100) := by
      rw [h51]
      have hQ_gt_one : 1 < Q := hQ_gt_one_of Q τ hQ_large hτ_pos hτ_lt_one
      have h7 : Real.rpow Q 100 ≥ Q^10 := by
        have h8 : (100 : ℝ) ≥ 10 := by norm_num
        have h9 : Real.rpow Q 100 ≥ Real.rpow Q 10 :=
          Real.rpow_le_rpow_of_exponent_le hQ_gt_one.le h8
        have h10 : Real.rpow Q 10 = Q^10 := by simp
        rw [h10] at h9
        exact h9
      have h11 : 0 < Real.rpow Q 100 := Real.rpow_pos_of_pos hQ_pos 100
      have h12 : (Real.rpow Q 100)⁻¹ ≤ 4 / Q^10 := by
        have h13 : (Real.rpow Q 100)⁻¹ = 1 / Real.rpow Q 100 := by
          field_simp [h11.ne'] <;> ring
        rw [h13]
        have h14 : 1 / Real.rpow Q 100 ≤ 4 / Q^10 := by
          gcongr <;> norm_num
        exact h14
      exact h12
    exact h5.trans h43
  have h_main := general_threshold_bound Q M σ τ hQ_large hM_large
    hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
    c0 2 0 e hc0_pos (by norm_num) (by norm_num) he_pos
    h_ratio he_ge h_c_lower
    K C hK hC hK_le_Q hC_le_Q
  have h_eq : (c0 / (Real.rpow K 2 * Real.rpow C 0)) =
      (2 : ℝ)^(-ε_F) / (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7) := by
    have hC0 : Real.rpow C 0 = 1 := by simp
    rw [hC0]
    <;> simp [hc0_def] <;> ring
  rw [h_eq] at h_main
  exact h_main

/-- r10 bound -/
lemma r10_bound :
    Real.rpow (66 / ((202 : ℝ) * K * (2 : ℝ)^σ)) (1 / τ) >
    8 / Real.rpow Q (M / (σ + τ)) := by
  set c0 : ℝ := (66 : ℝ) / ((202 : ℝ) * (2 : ℝ)^σ) with hc0_def
  have hc0_pos : 0 < c0 := by positivity
  have h2σ_le2 : (2 : ℝ)^σ ≤ 2 := by
    have h1 : 0 ≤ σ := by linarith
    have h2 : σ ≤ 1 := by linarith
    have h3 : (2 : ℝ)^σ ≤ (2 : ℝ)^(1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
    have h4 : (2 : ℝ)^(1 : ℝ) = 2 := by simp
    rw [h4] at h3
    exact h3
  have h_c_lower : c0 ≥ Real.rpow Q (-100) := by
    have h1 : c0 ≥ 66 / (202 * 2) := by
      rw [hc0_def]; gcongr <;> norm_num
    have h4 : (66 : ℝ) / (202 * 2) ≥ 1 / 10^7 := by norm_num
    exact c_ge_q_neg100 Q τ hQ_large hτ_pos hτ_lt_one c0 (by linarith)
  have h_ratio : (1 + 0) / τ ≤ 1 / τ := by simp
  have h_main := general_threshold_bound Q M σ τ hQ_large hM_large
    hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
    c0 1 0 τ hc0_pos (by norm_num) (by norm_num) hτ_pos
    h_ratio (by linarith) h_c_lower
    K C hK hC hK_le_Q hC_le_Q
  have h_eq : (c0 / (Real.rpow K 1 * Real.rpow C 0)) =
      (66 : ℝ) / ((202 : ℝ) * K * (2 : ℝ)^σ) := by
    have hC0 : Real.rpow C 0 = 1 := by simp
    rw [hC0] <;> simp [hc0_def] <;> ring
  rw [h_eq] at h_main
  exact h_main

/-- r6 bound -/
lemma r6_bound :
    Real.rpow (1 / ((10^7 : ℝ) * K * C * (17 / 32 : ℝ)^σ)) (1 / (2 * τ)) >
    8 / Real.rpow Q (M / (σ + τ)) := by
  set c0 : ℝ := (1 : ℝ) / ((10^7 : ℝ) * (17 / 32 : ℝ)^σ) with hc0_def
  have hc0_pos : 0 < c0 := by positivity
  have h1732_le_one : (17 / 32 : ℝ)^σ ≤ 1 := by
    have h2 : (0 : ℝ) ≤ 17 / 32 := by norm_num
    have h3 : (17 / 32 : ℝ) ≤ 1 := by norm_num
    have h4 : 0 ≤ σ := by linarith
    exact Real.rpow_le_one h2 h3 h4
  have h_c_lower : c0 ≥ Real.rpow Q (-100) := by
    have h1 : c0 ≥ 1 / (10^7 : ℝ) := by
      rw [hc0_def]
      have h2 : (17 / 32 : ℝ)^σ ≤ 1 := h1732_le_one
      have h3 : (10^7 : ℝ) * (17 / 32 : ℝ)^σ ≤ (10^7 : ℝ) := by
        have h31 : (17 / 32 : ℝ)^σ ≤ 1 := h2
        have h32 : 0 ≤ (10^7 : ℝ) := by norm_num
        nlinarith
      have h_pos : 0 < (10^7 : ℝ) * (17 / 32 : ℝ)^σ := by positivity
      gcongr
    exact c_ge_q_neg100 Q τ hQ_large hτ_pos hτ_lt_one c0 h1
  have h_e_pos : 0 < 2 * τ := mul_pos (by norm_num) hτ_pos
  have h_ratio : (1 + 1) / (2 * τ) ≤ 1 / τ := by
    have h : (1 + 1) / (2 * τ) = 1 / τ := by
      field_simp [hτ_pos.ne'] <;> ring
    rw [h]
  have h_main := general_threshold_bound Q M σ τ hQ_large hM_large
    hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
    c0 1 1 (2 * τ) hc0_pos (by norm_num) (by norm_num) h_e_pos
    h_ratio (by linarith) h_c_lower
    K C hK hC hK_le_Q hC_le_Q
  have h_eq : (c0 / (Real.rpow K 1 * Real.rpow C 1)) =
      (1 : ℝ) / ((10^7 : ℝ) * K * C * (17 / 32 : ℝ)^σ) := by
    have hK1 : Real.rpow K 1 = K := by simp
    have hC1 : Real.rpow C 1 = C := by simp
    rw [hK1, hC1] <;> simp [hc0_def] <;> ring
  rw [h_eq] at h_main
  exact h_main

/-- r2 and r9 bounds -/
lemma r2_r9_bound :
    Real.rpow (1 / (4 * C)) (1 / (1 - σ - 3 * τ)) >
    8 / Real.rpow Q (M / (σ + τ)) ∧
    Real.rpow (1 / (18 * C)) (1 / (1 - σ - 3 * τ)) >
    8 / Real.rpow Q (M / (σ + τ)) := by
  set e : ℝ := 1 - σ - 3 * τ with he_def
  have he_pos : 0 < e := by linarith
  have he_ge : e ≥ τ / 2 := by linarith
  have h_ratio : (0 + 1) / e ≤ 1 / τ := by
    have h2 : (0 + 1) / e = 1 / e := by ring
    rw [h2]
    have h3 : 1 / e ≤ 1 / τ := by gcongr <;> linarith
    exact h3
  have h_main4 := general_threshold_bound Q M σ τ hQ_large hM_large
    hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
    (1 / 4 : ℝ) 0 1 e (by norm_num) (by norm_num) (by norm_num) he_pos
    h_ratio he_ge (c_ge_q_neg100 Q τ hQ_large hτ_pos hτ_lt_one (1/4) (by norm_num))
    K C hK hC hK_le_Q hC_le_Q
  have h_main18 := general_threshold_bound Q M σ τ hQ_large hM_large
    hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
    (1 / 18 : ℝ) 0 1 e (by norm_num) (by norm_num) (by norm_num) he_pos
    h_ratio he_ge (c_ge_q_neg100 Q τ hQ_large hτ_pos hτ_lt_one (1/18) (by norm_num))
    K C hK hC hK_le_Q hC_le_Q
  have h_eq4 : ((1 / 4 : ℝ) / (Real.rpow K 0 * Real.rpow C 1)) = 1 / (4 * C) := by
    have hK0 : Real.rpow K 0 = 1 := by simp
    have hC1 : Real.rpow C 1 = C := by simp
    rw [hK0, hC1] <;> ring
  have h_eq18 : ((1 / 18 : ℝ) / (Real.rpow K 0 * Real.rpow C 1)) = 1 / (18 * C) := by
    have hK0 : Real.rpow K 0 = 1 := by simp
    have hC1 : Real.rpow C 1 = C := by simp
    rw [hK0, hC1] <;> ring
  rw [h_eq4] at h_main4
  rw [h_eq18] at h_main18
  exact ⟨h_main4, h_main18⟩

/-- r8 bound -/
lemma r8_bound :
    Real.rpow (1 / (20 * C)) (1 / τ) >
    8 / Real.rpow Q (M / (σ + τ)) := by
  have h_c_lower : (1 / 20 : ℝ) ≥ Real.rpow Q (-100) :=
    c_ge_q_neg100 Q τ hQ_large hτ_pos hτ_lt_one (1 / 20) (by norm_num)
  have h_ratio : (0 + 1) / τ ≤ 1 / τ := by simp
  have h_main := general_threshold_bound Q M σ τ hQ_large hM_large
    hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
    (1 / 20 : ℝ) 0 1 τ (by norm_num) (by norm_num) (by norm_num) hτ_pos
    h_ratio (by linarith) h_c_lower
    K C hK hC hK_le_Q hC_le_Q
  have h_eq : ((1 / 20 : ℝ) / (Real.rpow K 0 * Real.rpow C 1)) = 1 / (20 * C) := by
    have hK0 : Real.rpow K 0 = 1 := by simp
    have hC1 : Real.rpow C 1 = C := by simp
    rw [hK0, hC1] <;> ring
  rw [h_eq] at h_main
  exact h_main

/-- r1_ext bound -/
lemma r1_ext_bound :
    let A : ℝ := Real.log (4000 * C) + 1
    Real.rpow ((2 : ℝ)^(-ε_F - 1) / (200 * C * (D_X : ℝ) * A))
      (1 / (ε_F - τ)) >
    8 / Real.rpow Q (M / (σ + τ)) := by
  let A : ℝ := Real.log (4000 * C) + 1
  have hA_pos : 0 < A := by
    dsimp only [A]
    have h1 : 4000 * C > 1 := by linarith [hC]
    have h2 : Real.log (4000 * C) > 0 := Real.log_pos h1
    linarith
  have hA_le : A ≤ 4000 * Q := by
    dsimp only [A]
    have h1 : Real.log (4000 * C) ≤ 4000 * C - 1 :=
      Real.log_le_sub_one_of_pos (by linarith [hC])
    have h2 : A ≤ 4000 * C := by linarith
    have h3 : 4000 * C ≤ 4000 * Q := by gcongr
    linarith
  set e : ℝ := ε_F - τ with he_def
  have he_pos : 0 < e := by linarith
  have he_ge : e ≥ τ / 2 := by linarith
  have h_ratio : (0 + 1) / e ≤ 1 / τ := by
    have h2 : (0 + 1) / e = 1 / e := by ring
    rw [h2]
    have h3 : 1 / e ≤ 1 / (2 * τ) := by gcongr <;> linarith
    have h4 : 1 / (2 * τ) ≤ 1 / τ := by gcongr <;> linarith
    exact h3.trans h4
  have hQ_pos : 0 < Q := hQ_pos_of Q τ hQ_large hτ_pos
  have h2_pow_neg : (2 : ℝ)^(-ε_F - 1) ≥ 1 / Q := by
    have h1 : Q ≥ (2 : ℝ)^(ε_F + 2) := hQ_huge
    have h2 : (2 : ℝ)^(-ε_F - 1) = (2 : ℝ)^(-(ε_F + 2)) * 2 := by
      have h3 : -ε_F - 1 = (-(ε_F + 2)) + 1 := by ring
      rw [h3]
      rw [Real.rpow_add (by norm_num)]
      <;> simp
    rw [h2]
    have h4 : (2 : ℝ)^(-(ε_F + 2)) = ((2 : ℝ)^(ε_F + 2))⁻¹ := by
      rw [Real.rpow_neg (by norm_num)] <;> ring
    rw [h4]
    have h5 : 0 < (2 : ℝ)^(ε_F + 2) := by positivity
    have h5' : 1 / ((2 : ℝ)^(ε_F + 2)) ≥ 1 / Q :=
      one_div_le_one_div_of_le h5 (by linarith)
    have h5'' : ((2 : ℝ)^(ε_F + 2))⁻¹ ≥ Q⁻¹ := by
      simpa [one_div] using h5'
    have h6 : 0 < Q := hQ_pos
    have h7 : ((2 : ℝ)^(ε_F + 2))⁻¹ * 2 ≥ 1 / Q := by
      have h8 : ((2 : ℝ)^(ε_F + 2))⁻¹ * 2 = 2 * ((2 : ℝ)^(ε_F + 2))⁻¹ := by ring
      rw [h8]
      have h9 : 2 * ((2 : ℝ)^(ε_F + 2))⁻¹ ≥ 2 * Q⁻¹ := by gcongr
      have h10 : 2 * Q⁻¹ ≥ 1 / Q := by
        field_simp [h6.ne'] <;> linarith
      linarith
    exact h7
  set c0 : ℝ := (2 : ℝ)^(-ε_F - 1) / (200 * (D_X : ℝ) * A) with hc0_def
  have hc0_pos : 0 < c0 := by positivity
  have h_c_lower : c0 ≥ Real.rpow Q (-100) := by
    have h1 : 200 * (D_X : ℝ) * A ≤ 800000 * Q^2 := by
      calc 200 * (D_X : ℝ) * A
        ≤ 200 * Q * (4000 * Q) := by gcongr <;> linarith
      _ = 800000 * Q^2 := by ring
    have h2 : c0 ≥ (1 / Q) / (800000 * Q^2) := by
      rw [hc0_def]
      gcongr <;> linarith
    have h3 : (1 / Q) / (800000 * Q^2) = 1 / (800000 * Q^3) := by
      field_simp [hQ_pos.ne'] <;> ring
    rw [h3] at h2
    exact inv_Q3_ge_q_neg100 Q τ hQ_large hτ_pos hτ_lt_one c0 800000 h2 (by norm_num) (by norm_num)
  have h_main := general_threshold_bound Q M σ τ hQ_large hM_large
    hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
    c0 0 1 e hc0_pos (by norm_num) (by norm_num) he_pos
    h_ratio he_ge h_c_lower
    K C hK hC hK_le_Q hC_le_Q
  have h_eq : (c0 / (Real.rpow K 0 * Real.rpow C 1)) =
      (2 : ℝ)^(-ε_F - 1) / (200 * C * (D_X : ℝ) * A) := by
    have hK0 : Real.rpow K 0 = 1 := by simp
    have hC1 : Real.rpow C 1 = C := by simp
    rw [hK0, hC1] <;> simp [hc0_def] <;> ring_nf
  rw [h_eq] at h_main
  exact h_main

/-- r2_ext bound -/
lemma r2_ext_bound :
    let B : ℝ := 2 * (τ + 1) / (ε_F - τ)
    Real.rpow ((2 : ℝ)^(-ε_F - 1) / (200 * C * (D_X : ℝ) * B))
      (1 / ((ε_F - τ) / 2)) >
    8 / Real.rpow Q (M / (σ + τ)) := by
  let B : ℝ := 2 * (τ + 1) / (ε_F - τ)
  set e : ℝ := (ε_F - τ) / 2 with he_def
  have he_pos : 0 < e := by linarith
  have he_ge : e ≥ τ / 2 := by linarith
  have h_ratio : (0 + 1) / e ≤ 1 / τ := by
    have h2 : (0 + 1) / e = 2 / (ε_F - τ) := by
      dsimp only [e]
      field_simp [hτ_pos.ne'] <;> ring
    rw [h2]
    have h3 : 2 / (ε_F - τ) ≤ 2 / (3 * τ) := by gcongr <;> linarith
    have h4 : 2 / (3 * τ) ≤ 1 / τ := by
      field_simp [hτ_pos.ne'] <;> linarith
    exact h3.trans h4
  have hB_pos : 0 < B := by
    dsimp only [B]
    have h1 : 0 < 2 * (τ + 1) := by positivity
    have h2 : 0 < ε_F - τ := by linarith
    exact div_pos h1 h2
  have hB_lt_Q : B < Q := by
    dsimp only [B]
    have h1 : τ + 1 < 15 / 14 := by linarith [hτ_small]
    have h2 : ε_F - τ > 7 * τ := by linarith
    have h_pos2 : 0 < ε_F - τ := by linarith
    have h3 : 2 * (τ + 1) ≤ 2 * (15 / 14) := by gcongr <;> linarith
    have h4 : 2 * (τ + 1) / (ε_F - τ) ≤ 2 * (15 / 14) / (ε_F - τ) := by
      gcongr <;> linarith
    have h5 : 2 * (15 / 14) / (ε_F - τ) ≤ 2 * (15 / 14) / (7 * τ) := by
      gcongr <;> linarith
    have h6 : 2 * (15 / 14) / (7 * τ) = 15 / (49 * τ) := by
      field_simp [hτ_pos.ne'] <;> ring
    rw [h6] at h5
    have h7 : Q > 4000 / τ^2 := hQ_large
    have h8 : 4000 / τ^2 > 15 / (49 * τ) := by
      field_simp [hτ_pos.ne'] <;> nlinarith
    linarith
  have hQ_pos : 0 < Q := hQ_pos_of Q τ hQ_large hτ_pos
  have h2_pow_neg : (2 : ℝ)^(-ε_F - 1) ≥ 1 / Q := by
    have h1 : Q ≥ (2 : ℝ)^(ε_F + 2) := hQ_huge
    have h2 : (2 : ℝ)^(-ε_F - 1) = (2 : ℝ)^(-(ε_F + 2)) * 2 := by
      have h3 : -ε_F - 1 = (-(ε_F + 2)) + 1 := by ring
      rw [h3, Real.rpow_add (by norm_num)] <;> simp
    rw [h2]
    have h4 : (2 : ℝ)^(-(ε_F + 2)) = ((2 : ℝ)^(ε_F + 2))⁻¹ := by
      rw [Real.rpow_neg (by norm_num)] <;> ring
    rw [h4]
    have h5 : 0 < Q := hQ_pos
    have h6 : ((2 : ℝ)^(ε_F + 2))⁻¹ * 2 ≥ 1 / Q := by
      have h7 : 0 < (2 : ℝ)^(ε_F + 2) := by positivity
      have h8 : 1 / ((2 : ℝ)^(ε_F + 2)) ≥ 1 / Q :=
        one_div_le_one_div_of_le h7 (by linarith)
      have h8' : ((2 : ℝ)^(ε_F + 2))⁻¹ ≥ Q⁻¹ := by
        simpa [one_div] using h8
      have h9 : 2 * ((2 : ℝ)^(ε_F + 2))⁻¹ ≥ 2 * Q⁻¹ := by gcongr
      have h10 : 2 * Q⁻¹ ≥ 1 / Q := by
        field_simp [h5.ne'] <;> linarith
      have h11 : ((2 : ℝ)^(ε_F + 2))⁻¹ * 2 = 2 * ((2 : ℝ)^(ε_F + 2))⁻¹ := by ring
      rw [h11]
      linarith
    exact h6
  set c0 : ℝ := (2 : ℝ)^(-ε_F - 1) / (200 * (D_X : ℝ) * B) with hc0_def
  have hc0_pos : 0 < c0 := by positivity
  have h_c_lower : c0 ≥ Real.rpow Q (-100) := by
    have h1 : 200 * (D_X : ℝ) * B ≤ 200 * Q * Q := by gcongr <;> linarith
    have h2 : c0 ≥ (1 / Q) / (200 * Q * Q) := by
      rw [hc0_def]; gcongr <;> linarith
    have h3 : (1 / Q) / (200 * Q * Q) = 1 / (200 * Q^3) := by
      field_simp [hQ_pos.ne'] <;> ring
    rw [h3] at h2
    exact inv_Q3_ge_q_neg100 Q τ hQ_large hτ_pos hτ_lt_one c0 200 h2 (by norm_num) (by norm_num)
  have h_main := general_threshold_bound Q M σ τ hQ_large hM_large
    hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
    c0 0 1 e hc0_pos (by norm_num) (by norm_num) he_pos
    h_ratio he_ge h_c_lower
    K C hK hC hK_le_Q hC_le_Q
  have h_eq : (c0 / (Real.rpow K 0 * Real.rpow C 1)) =
      (2 : ℝ)^(-ε_F - 1) / (200 * C * (D_X : ℝ) * B) := by
    have hK0 : Real.rpow K 0 = 1 := by simp
    have hC1 : Real.rpow C 1 = C := by simp
    rw [hK0, hC1] <;> simp [hc0_def] <;> ring_nf
  rw [h_eq] at h_main
  exact h_main

/-- K^(-1/τ)/2 bound -/
lemma kinv_bound :
    Real.rpow K (-(1 / τ)) / 2 >
    8 / Real.rpow Q (M / (σ + τ)) := by
  have h_c_lower : (1 / 2 : ℝ) ≥ Real.rpow Q (-100) :=
    c_ge_q_neg100 Q τ hQ_large hτ_pos hτ_lt_one (1 / 2) (by norm_num)
  have hK_pos : 0 < K := by linarith
  have h_main := general_threshold_bound Q M σ τ hQ_large hM_large
    hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
    (1 / 2 : ℝ) (1 / τ) 0 1
    (by norm_num) (by positivity) (by norm_num) (by norm_num)
    (by simp) (by linarith) h_c_lower
    K C hK hC hK_le_Q hC_le_Q
  have h_eq : Real.rpow ((1 / 2 : ℝ) / (Real.rpow K (1 / τ) * Real.rpow C 0)) (1 / 1) =
      Real.rpow K (-(1 / τ)) / 2 := by
    have h1 : Real.rpow C 0 = 1 := Real.rpow_zero C
    have h2 : (1 / 2 : ℝ) / (Real.rpow K (1 / τ) * Real.rpow C 0) =
        (1 / 2 : ℝ) / Real.rpow K (1 / τ) := by
      rw [h1] <;> ring
    have h3 : Real.rpow K (-(1 / τ)) = (Real.rpow K (1 / τ))⁻¹ :=
      Real.rpow_neg hK_pos.le (1 / τ)
    have h4 : Real.rpow ((1 / 2 : ℝ) / Real.rpow K (1 / τ)) 1 =
        (1 / 2 : ℝ) / Real.rpow K (1 / τ) := by simp
    have h5 : Real.rpow ((1 / 2 : ℝ) / (Real.rpow K (1 / τ) * Real.rpow C 0)) (1 / 1) =
        Real.rpow ((1 / 2 : ℝ) / Real.rpow K (1 / τ)) 1 := by
      rw [h2] <;> norm_num
    rw [h5, h4]
    have h6 : (1 / 2 : ℝ) / Real.rpow K (1 / τ) = (Real.rpow K (1 / τ))⁻¹ / 2 := by
      field_simp [hK_pos.ne'] <;> ring
    rw [h6, h3]
  rw [h_eq] at h_main
  exact h_main

end Bounds

end RadialBootstrapping
