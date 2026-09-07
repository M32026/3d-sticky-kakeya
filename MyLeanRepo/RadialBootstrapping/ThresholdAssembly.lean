module

/-
  ThresholdAssembly.lean

  Assembles all B component bounds into hB_large:
  min r_CB (min r_conc (min r_ext (K^(-1/τ)/2))) > 8 / Q^(M/(σ+τ))

  Imports component lemmas from BComponentBounds.lean and adds
  bounds for remaining r_conc components.
-/

public import MyLeanRepo.RadialBootstrapping.ThresholdBounds
public import MyLeanRepo.RadialBootstrapping.BComponentBounds
public import MyLeanRepo.RadialBootstrapping.ConcentratedParameterSelection
public import MyLeanRepo.RadialBootstrapping.CXBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Classical
open scoped ENNReal NNReal


noncomputable section

namespace RadialBootstrapping

/-- F_conc = 202 exactly. -/
lemma hF_conc_eq : ConcentratedParam.F_conc = 202 := by
  have h_pos : 0 ≤ 16 * Real.pi * (2 : ℝ) / (1 / 2) := by positivity
  have h1 : (201 : ℝ) < 16 * Real.pi * (2 : ℝ) / (1 / 2) := by
    have hpi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
    linarith
  have h2 : 16 * Real.pi * (2 : ℝ) / (1 / 2) < (202 : ℝ) := by
    have hpi : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
    linarith
  have h3 : Nat.floor (16 * Real.pi * (2 : ℝ) / (1 / 2)) = 201 := by
    rw [Nat.floor_eq_iff h_pos]
    constructor
    · exact_mod_cast h1.le
    · exact_mod_cast h2
  have h4 : ConcentratedParam.F_conc = 202 := by
    unfold ConcentratedParam.F_conc
    rw [h3]
    <;> norm_num
  exact h4

/-- Helper: Q^2 > N / τ for N ≤ 10^7 when Q > 4000/τ^2 and τ < 1. -/
lemma q2_gt_N_div_tau (Q τ N : ℝ) (hQ_large : Q > 4000 / τ^2)
    (hτ_pos : 0 < τ) (hτ_lt_one : τ < 1) (hN : N ≤ 10^7) :
    Q^2 > N / τ := by
  have h1 : Q > 4000 / τ^2 := hQ_large
  have h2 : Q^2 > (4000 / τ^2)^2 := by gcongr
  have h3 : (4000 / τ^2)^2 ≥ N / τ := by
    have h4 : τ < 1 := hτ_lt_one
    have h5 : 0 < τ := hτ_pos
    have h6 : (4000 / τ^2)^2 = 16000000 / τ^4 := by
      field_simp [h5.ne'] <;> ring
    rw [h6]
    have h7 : 16000000 / τ^4 ≥ N / τ := by
      have h8 : τ^4 ≤ τ := by
        have h9 : 0 ≤ τ := by linarith
        have h10 : τ ≤ 1 := by linarith
        have h11 : τ^2 ≤ τ := by
          calc τ^2 = τ * τ := by ring
            _ ≤ τ * 1 := by gcongr <;> linarith
            _ = τ := by ring
        have h12 : τ^4 ≤ τ^2 := by
          calc τ^4 = τ^2 * τ^2 := by ring
            _ ≤ τ^2 * 1 := by gcongr <;> linarith
            _ = τ^2 := by ring
        linarith
      have h11 : 16000000 ≥ N := by linarith [hN]
      gcongr <;> positivity
    exact h7
  linarith

/-- Main hB_large assembly lemma. -/
lemma hB_large_assembled
    (Q M σ τ ε_F κ C K : ℝ)
    (D_T D_X : ℕ)
    (hQ_large : Q > 4000 / τ^2)
    (hM_large : M > 400 / τ^2)
    (hτ_pos : 0 < τ) (hτ_lt_one : τ < 1) (hτ_small : τ < 1 / 14)
    (hστ_pos : 0 < σ + τ) (hστ_lt_two : σ + τ < 2)
    (hσ_pos : 0 < σ) (hσ_lt_one : σ < 1)
    (hτ_very_small : τ < (1 - σ) / 14)
    (hεF_large : ε_F > 8 * τ + 3 * κ)
    (hκ_nonneg : 0 ≤ κ) (hκ_lt_one : κ < 1)
    (hC : 1 ≤ C) (hK : 1 ≤ K)
    (hK_le_Q : K ≤ Q) (hC_le_Q : C ≤ Q)
    (hDT_pos : 0 < D_T) (hDX_pos : 0 < D_X)
    (hDT_le_Q : (D_T : ℝ) ≤ Q) (hDX_le_Q : (D_X : ℝ) ≤ Q)
    (hQ_huge : Q ≥ (2 : ℝ)^(ε_F + 2)) :
    let r_CB := Real.rpow ((2 : ℝ)^(-ε_F) / (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7))
        (1 / (ε_F - κ - 5 * τ))
    let r_conc := ConcentratedParam.concentrated_r_conc σ τ C K κ
    let r_ext := c_x_r_ext τ ε_F C D_X
    let kinv := Real.rpow K (-(1 / τ)) / 2
    min r_CB (min r_conc (min r_ext kinv)) >
    8 / Real.rpow Q (M / (σ + τ)) := by
  dsimp only
  set bound : ℝ := 8 / Real.rpow Q (M / (σ + τ)) with hbound_def

  -- Reusable Q facts
  have hQ_pos : 0 < Q := hQ_pos_of Q τ hQ_large hτ_pos
  have hQ_gt_one : 1 < Q := hQ_gt_one_of Q τ hQ_large hτ_pos hτ_lt_one

  -- Generic no-K/C bound: c^(1/e) > bound when c ≥ Q^(-100), e ≥ τ/2
  let generic_noKC := fun (c e : ℝ) (hc_pos : 0 < c) (he_pos : 0 < e)
      (he_ge : e ≥ τ / 2) (hc_lower : c ≥ Real.rpow Q (-100)) => by
    have h_main := general_threshold_bound Q M σ τ hQ_large hM_large
      hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
      c 0 0 e hc_pos (by norm_num) (by norm_num) he_pos
      (by simp [hτ_pos.le]) he_ge hc_lower
      K C hK hC hK_le_Q hC_le_Q
    have h_eq : (c / (Real.rpow K 0 * Real.rpow C 0)) = c := by simp
    rw [h_eq] at h_main
    exact h_main

  -- c ≥ Q^(-100) helper for constants ≥ 1/10^7
  let c_lower_const := fun (c : ℝ) (hc : c ≥ 1 / 10^7) =>
    c_ge_q_neg100 Q τ hQ_large hτ_pos hτ_lt_one c hc

  -- c ≥ Q^(-100) helper for c ≥ τ/N with N ≤ 10^7
  let c_lower_tau := fun (c N : ℝ) (hc : c ≥ τ / N) (hN_pos : 0 < N) (hN : N ≤ 10^7) => by
    have h1 : Q^2 > N / τ := q2_gt_N_div_tau Q τ N hQ_large hτ_pos hτ_lt_one hN
    have h4 : Real.rpow Q 100 ≥ Q^2 := by
      have h5 : (100 : ℝ) ≥ 2 := by norm_num
      have h6 : Real.rpow Q 100 ≥ Real.rpow Q 2 :=
        Real.rpow_le_rpow_of_exponent_le hQ_gt_one.le h5
      have h7 : Real.rpow Q 2 = Q^2 := by simp
      rw [h7] at h6
      exact h6
    have h8 : Real.rpow Q 100 > N / τ := by linarith
    have h9 : 0 < Real.rpow Q 100 := Real.rpow_pos_of_pos hQ_pos 100
    have hNdiv_pos : 0 < N / τ := by positivity
    have h10 : (Real.rpow Q 100)⁻¹ ≤ τ / N := by
      have h11 : (Real.rpow Q 100)⁻¹ = 1 / Real.rpow Q 100 := by
        field_simp [h9.ne'] <;> ring
      rw [h11]
      have h13 : 1 / Real.rpow Q 100 ≤ 1 / (N / τ) := by
        apply one_div_le_one_div_of_le hNdiv_pos
        exact h8.le
      have h14 : 1 / (N / τ) = τ / N := by
        field_simp [hτ_pos.ne'] <;> ring
      rw [h14] at h13
      exact h13
    have h15 : Real.rpow Q (-100) = (Real.rpow Q 100)⁻¹ := Real.rpow_neg hQ_pos.le 100
    have h16 : Real.rpow Q (-100) ≤ τ / N := by
      rw [h15]
      exact h10
    exact le_trans h16 hc

  -- 1/8 > bound
  have h18 : (1 / 8 : ℝ) > bound := by
    have h := generic_noKC (1 / 8) 1 (by norm_num) (by norm_num) (by linarith)
      (c_lower_const (1 / 8) (by norm_num))
    have h_eq : Real.rpow (1 / 8 : ℝ) (1 / (1 : ℝ)) = (1 / 8 : ℝ) := by simp
    rw [h_eq] at h
    exact h

  -- 1 > bound
  have h1gt : (1 : ℝ) > bound := by
    have h := generic_noKC 1 1 (by norm_num) (by norm_num) (by linarith)
      (c_lower_const 1 (by norm_num))
    have h_eq : Real.rpow (1 : ℝ) (1 / (1 : ℝ)) = (1 : ℝ) := by simp
    rw [h_eq] at h
    exact h

  -- r5 > bound
  have hr5 : Real.rpow (1 / 6336 : ℝ) (1 / τ) > bound :=
    generic_noKC (1 / 6336) τ (by norm_num) hτ_pos (by linarith)
      (c_lower_const (1 / 6336) (by norm_num))

  -- r7 > bound
  have hr7 : Real.rpow (τ / 200) (2 / τ) > bound := by
    have h := generic_noKC (τ / 200) (τ / 2) (by positivity) (by positivity) (by linarith)
      (c_lower_tau (τ / 200) 200 (by linarith) (by norm_num) (by norm_num))
    have h_eq : 1 / (τ / 2) = 2 / τ := by
      field_simp [hτ_pos.ne'] <;> ring
    rw [h_eq] at h
    exact h

  -- target_N lower bound
  have htarget_N_lower : (1 / 8 : ℝ) / (792 * (2 / (τ * Real.log 2) + 2 + Real.log 5 / Real.log 2)) ≥ τ / 80000 := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2_lt2 : Real.log 2 < 2 := by
      have h : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
      linarith
    have hlog2_ge_half : Real.log 2 ≥ 1 / 2 := by
      have h : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      linarith
    have h1 : Real.log 5 / Real.log 2 ≤ 3 := by
      have h2 : Real.log 5 ≤ 3 * Real.log 2 := by
        have h3 : Real.log 5 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
        have h4 : Real.log 8 = 3 * Real.log 2 := by
          have h5 : (8 : ℝ) = 2^3 := by norm_num
          rw [h5, Real.log_pow] <;> ring
        linarith
      calc Real.log 5 / Real.log 2
        ≤ (3 * Real.log 2) / Real.log 2 := by gcongr
      _ = 3 := by field_simp [hlog2_pos.ne'] <;> ring
    have hτ_log2_le1 : τ * Real.log 2 ≤ 1 := by
      have hτ14 : τ < 1 / 14 := hτ_small
      nlinarith [hlog2_lt2]
    have h_term1_le : 2 / (τ * Real.log 2) ≤ 4 / τ := by
      have h_pos : 0 < τ * Real.log 2 := by positivity
      calc 2 / (τ * Real.log 2)
        ≤ 2 / (τ * (1 / 2)) := by gcongr <;> linarith [hlog2_ge_half]
      _ = 4 / τ := by field_simp [hτ_pos.ne'] <;> ring
    have h_term2_le : (2 : ℝ) ≤ 4 / τ := by
      have h : 4 / τ > 56 := by
        have h5 : 0 < τ := hτ_pos
        calc 4 / τ > 4 / (1 / 14) := by gcongr <;> linarith
          _ = 56 := by norm_num
      linarith
    have h_term3_le : Real.log 5 / Real.log 2 ≤ 4 / τ := by
      have h : 4 / τ > 56 := by
        have h5 : 0 < τ := hτ_pos
        calc 4 / τ > 4 / (1 / 14) := by gcongr <;> linarith
          _ = 56 := by norm_num
      linarith [h1]
    have h_sum_le : 2 / (τ * Real.log 2) + 2 + Real.log 5 / Real.log 2 ≤ 12 / τ := by
      calc 2 / (τ * Real.log 2) + 2 + Real.log 5 / Real.log 2
        ≤ 4 / τ + 4 / τ + 4 / τ := by gcongr <;> linarith
      _ = 12 / τ := by ring
    have h_denom_le : 792 * (2 / (τ * Real.log 2) + 2 + Real.log 5 / Real.log 2) ≤ 9504 / τ := by
      have h : 792 * (2 / (τ * Real.log 2) + 2 + Real.log 5 / Real.log 2) ≤ 792 * (12 / τ) := by gcongr
      have h2 : 792 * (12 / τ) = 9504 / τ := by
        field_simp [hτ_pos.ne'] <;> ring
      rw [h2] at h
      exact h
    have h_final : (1 / 8 : ℝ) / (792 * (2 / (τ * Real.log 2) + 2 + Real.log 5 / Real.log 2)) ≥
        (1 / 8 : ℝ) / (9504 / τ) := by gcongr <;> linarith
    have h_eq : (1 / 8 : ℝ) / (9504 / τ) = τ / 76032 := by
      field_simp [hτ_pos.ne'] <;> ring
    rw [h_eq] at h_final
    have h_last : τ / 76032 ≥ τ / 80000 := by
      gcongr <;> norm_num
    linarith

  -- r3 > bound
  have hr3 : Real.rpow ((1 / 8 : ℝ) / (792 * (2 / (τ * Real.log 2) + 2 + Real.log 5 / Real.log 2)))
      (1 / (τ / 2)) > bound :=
    generic_noKC _ (τ / 2) (by positivity) (by positivity) (by linarith)
      (c_lower_tau _ 80000 htarget_N_lower (by norm_num) (by norm_num))

  -- target_card1 lower bound
  have htarget_card1_lower : (1 / 3168 : ℝ) / (2 * (1 - κ) / (τ * Real.log 2)) ≥ τ / 20000 := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : 0 < 1 - κ := by linarith
    have h2 : Real.log 2 ≥ 1 / 2 := by
      have h3 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have h4 : (0.6931471803 : ℝ) ≥ 1 / 2 := by norm_num
      linarith
    have h3 : (1 / 3168 : ℝ) / (2 * (1 - κ) / (τ * Real.log 2)) =
        (τ * Real.log 2) / (6336 * (1 - κ)) := by
      field_simp [h1.ne', hlog2_pos.ne'] <;> ring
    rw [h3]
    have h4 : (τ * Real.log 2) / (6336 * (1 - κ)) ≥ τ / 12672 := by
      have h5 : 1 - κ ≤ 1 := by linarith
      calc (τ * Real.log 2) / (6336 * (1 - κ))
        ≥ (τ * (1 / 2)) / (6336 * 1) := by gcongr <;> linarith
      _ = τ / 12672 := by field_simp [hτ_pos.ne'] <;> ring
    have h6 : τ / 12672 ≥ τ / 20000 := by gcongr <;> norm_num
    linarith

  -- r4 > bound
  have hr4 : Real.rpow ((1 / 3168 : ℝ) / (2 * (1 - κ) / (τ * Real.log 2))) (1 / (τ / 2)) > bound :=
    generic_noKC _ (τ / 2) (by positivity) (by positivity) (by linarith)
      (c_lower_tau _ 20000 htarget_card1_lower (by norm_num) (by norm_num))

  -- F_conc = 202
  have hF_eq : ConcentratedParam.F_conc = 202 := hF_conc_eq
  have hF_pos : 0 < (ConcentratedParam.F_conc : ℝ) := by
    rw [hF_eq] <;> norm_num

  -- r10 > bound (with actual F_conc)
  have hr10 : Real.rpow (66 / ((ConcentratedParam.F_conc : ℝ) * K * (2 : ℝ)^σ)) (1 / τ) > bound := by
    have h_frac_ge : (66 : ℝ) / ((ConcentratedParam.F_conc : ℝ) * K * (2 : ℝ)^σ) ≥
        (66 : ℝ) / ((202 : ℝ) * K * (2 : ℝ)^σ) := by
      have hF_le : (ConcentratedParam.F_conc : ℝ) ≤ (202 : ℝ) := by
        rw [hF_eq] <;> norm_num
      have h_pos : 0 < K * (2 : ℝ)^σ := by positivity
      gcongr
      <;> linarith
    have h_rpow_ge : Real.rpow ((66 : ℝ) / ((ConcentratedParam.F_conc : ℝ) * K * (2 : ℝ)^σ)) (1 / τ) ≥
        Real.rpow ((66 : ℝ) / ((202 : ℝ) * K * (2 : ℝ)^σ)) (1 / τ) :=
      Real.rpow_le_rpow (by positivity) h_frac_ge (by positivity)
    have h_strict := r10_bound Q M σ τ ε_F κ C K D_T D_X
      hQ_large hM_large hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
      hσ_pos hσ_lt_one hτ_very_small hεF_large hκ_nonneg
      hC hK hK_le_Q hC_le_Q hDT_pos hDX_pos hDT_le_Q hDX_le_Q hQ_huge
    linarith

  -- r1 > bound (r1 > r10 since 396 > 66)
  have hr1 : Real.rpow (396 / ((ConcentratedParam.F_conc : ℝ) * K * (2 : ℝ)^σ)) (1 / τ) > bound := by
    have h_frac_ge : (396 : ℝ) / ((ConcentratedParam.F_conc : ℝ) * K * (2 : ℝ)^σ) ≥
        (66 : ℝ) / ((ConcentratedParam.F_conc : ℝ) * K * (2 : ℝ)^σ) := by
      have h_pos : 0 < (ConcentratedParam.F_conc : ℝ) * K * (2 : ℝ)^σ := by
        positivity <;> exact hF_pos
      gcongr <;> norm_num
    have h_rpow_ge : Real.rpow ((396 : ℝ) / ((ConcentratedParam.F_conc : ℝ) * K * (2 : ℝ)^σ)) (1 / τ) ≥
        Real.rpow ((66 : ℝ) / ((ConcentratedParam.F_conc : ℝ) * K * (2 : ℝ)^σ)) (1 / τ) :=
      Real.rpow_le_rpow (by positivity) h_frac_ge (by positivity)
    linarith [hr10]

  -- r2, r9 > bound
  have hr29 := r2_r9_bound Q M σ τ ε_F κ C K D_T D_X
    hQ_large hM_large hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
    hσ_pos hσ_lt_one hτ_very_small hεF_large hκ_nonneg
    hC hK hK_le_Q hC_le_Q hDT_pos hDX_pos hDT_le_Q hDX_le_Q hQ_huge

  -- r6 > bound
  have hr6 := r6_bound Q M σ τ ε_F κ C K D_T D_X
    hQ_large hM_large hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
    hσ_pos hσ_lt_one hτ_very_small hεF_large hκ_nonneg
    hC hK hK_le_Q hC_le_Q hDT_pos hDX_pos hDT_le_Q hDX_le_Q hQ_huge

  -- r8 > bound
  have hr8 := r8_bound Q M σ τ ε_F κ C K D_T D_X
    hQ_large hM_large hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
    hσ_pos hσ_lt_one hτ_very_small hεF_large hκ_nonneg
    hC hK hK_le_Q hC_le_Q hDT_pos hDX_pos hDT_le_Q hDX_le_Q hQ_huge

  -- r_CB > bound
  have hCB := r_CB_bound Q M σ τ ε_F κ C K D_T D_X
    hQ_large hM_large hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
    hσ_pos hσ_lt_one hτ_very_small hεF_large hκ_nonneg
    hC hK hK_le_Q hC_le_Q hDT_pos hDX_pos hDT_le_Q hDX_le_Q hQ_huge

  -- kinv > bound
  have hKinv := kinv_bound Q M σ τ ε_F κ C K D_T D_X
    hQ_large hM_large hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
    hσ_pos hσ_lt_one hτ_very_small hεF_large hκ_nonneg
    hC hK hK_le_Q hC_le_Q hDT_pos hDX_pos hDT_le_Q hDX_le_Q hQ_huge

  -- r1_ext > bound
  have h1e := r1_ext_bound Q M σ τ ε_F κ C K D_T D_X
    hQ_large hM_large hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
    hσ_pos hσ_lt_one hτ_very_small hεF_large hκ_nonneg
    hC hK hK_le_Q hC_le_Q hDT_pos hDX_pos hDT_le_Q hDX_le_Q hQ_huge

  -- r2_ext > bound
  have h2e := r2_ext_bound Q M σ τ ε_F κ C K D_T D_X
    hQ_large hM_large hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
    hσ_pos hσ_lt_one hτ_very_small hεF_large hκ_nonneg
    hC hK hK_le_Q hC_le_Q hDT_pos hDX_pos hDT_le_Q hDX_le_Q hQ_huge

  -- r_ext > bound
  have h_ext : c_x_r_ext τ ε_F C D_X > bound := by
    simp only [c_x_r_ext]
    have h_eq1 : (Real.rpow 2 (-ε_F) / 2 : ℝ) = (2 : ℝ)^(-ε_F - 1) := by
      have h : (Real.rpow 2 (-ε_F) / 2 : ℝ) = (2 : ℝ)^(-ε_F) / 2 := by simp
      rw [h]
      have h21 : (2 : ℝ)^(-ε_F - 1) = (2 : ℝ)^(-ε_F) * (2 : ℝ)^(-1 : ℝ) := by
        have h3 : -ε_F - 1 = -ε_F + (-1 : ℝ) := by ring
        rw [h3]
        rw [Real.rpow_add (by norm_num)] <;> ring
      have h22 : (2 : ℝ)^(-1 : ℝ) = 1 / 2 := by
        rw [Real.rpow_neg (by norm_num)]
        <;> norm_num
      rw [h21, h22] <;> ring
    have h_eqB : ((τ + 1) / (((ε_F - τ) / 2)) : ℝ) =
        (2 * (τ + 1) / (ε_F - τ)) := by
      field_simp [hτ_pos.ne'] <;> ring
    have h_exp : (ε_F - τ) - (ε_F - τ) / 2 = (ε_F - τ) / 2 := by ring
    rw [h_eq1]
    rw [h_eqB]
    rw [h_exp]
    exact lt_min h1e (lt_min h2e h1gt)

  -- r_conc > bound
  have h_conc : ConcentratedParam.concentrated_r_conc σ τ C K κ > bound := by
    simp only [ConcentratedParam.concentrated_r_conc]
    have h_hr7_eq : Real.rpow (τ / 200) (1 / (τ / 2)) = Real.rpow (τ / 200) (2 / τ) := by
      have h_eq : 1 / (τ / 2) = 2 / τ := by
        field_simp [hτ_pos.ne'] <;> ring
      rw [h_eq]
    rw [h_hr7_eq]
    exact lt_min h18 (lt_min hr1 (lt_min hr10 (lt_min hr29.1
      (lt_min hr3 (lt_min hr4 (lt_min hr5 (lt_min hr6 (lt_min hr7 (lt_min hr8 hr29.2)))))))))

  -- Final assembly
  have h1 : min (c_x_r_ext τ ε_F C D_X) (Real.rpow K (-(1 / τ)) / 2) > bound :=
    lt_min h_ext hKinv
  have h2 : min (ConcentratedParam.concentrated_r_conc σ τ C K κ)
      (min (c_x_r_ext τ ε_F C D_X) (Real.rpow K (-(1 / τ)) / 2)) > bound :=
    lt_min h_conc h1
  exact lt_min hCB h2

end RadialBootstrapping
