module

/-
  Combining Theorem Base Case (n=1) - Good Scale (Universal C'=1)

  Two-case strategy on M relative to threshold δ^{-s-γ}:

  Large M (M ≥ δ^{-s-γ}):
    Apply prop5_wrapper with exponent t_j. The M^{1+α} amplification yields
    δ^{-γ*α} ≥ δ^{-(η+2ε_G)} (since t_j ≥ t). Use core absorption inequality
    to get L^{-C} factor, then multiply by extra δ^{-(η+2ε_G)} and drop the
    δ^{-2ε_G} portion to reach combiningLowerBound (C'=1).

  Small M (M < δ^{-s-γ}):
    Improved incidence gives |T| ≥ δ^{-2s-ε_G}. Direct exponent comparison
    shows this dominates combiningLowerBound (C'=1) provided
    γ ≤ ε_G + lam + ε_N - η.

  Whiteprint node: combining_theorem_rework / base_case_good_universal
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.BaseCaseCommon
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FormatConversionLemmas
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M1

/-! ========================================================================
    Core absorption inequality
    ======================================================================== -/

/-- Given KCT' > 0, L > 1, 0 < δ ≤ 1/4, ε_N > 0, there exists C > 0 such that
    KCT'^{-1} · L^{-K} ≥ L^{-C} · δ^{ε_N}. -/
lemma absorb_core_ineq
    {δ L K KCT' ε_N : ℝ} (hδ_pos : 0 < δ) (hδ_le_quarter : δ ≤ 1 / 4)
    (hL_gt_one : 1 < L) (hK_pos : 0 < K) (hKCT'pos : 0 < KCT') (hεN : 0 < ε_N) :
    ∃ (C : ℝ), 0 < C ∧
      (1 / KCT') * Real.rpow L (-K) ≥ Real.rpow L (-C) * Real.rpow δ ε_N := by
  have hL_pos : 0 < L := by linarith
  have hL_one : 1 ≤ L := by linarith
  set C_bound : ℝ := max 1 KCT' with hC_bound_def
  have hC_bound_ge_one : 1 ≤ C_bound := le_max_left _ _
  have hC_bound_pos : 0 < C_bound := by linarith
  set C : ℝ := K + Real.log C_bound / Real.log L + 1 with hC_def
  have hC_pos : 0 < C := by
    have h2 : 0 ≤ Real.log C_bound / Real.log L := by
      apply div_nonneg
      · exact Real.log_nonneg hC_bound_ge_one
      · exact Real.log_nonneg hL_one
    linarith
  have h_log_L_pos : 0 < Real.log L := Real.log_pos hL_gt_one
  have h_rpow_Cbound : Real.rpow L (Real.log C_bound / Real.log L) = C_bound := by
    have h_exp : Real.rpow L (Real.log C_bound / Real.log L) =
        Real.exp (Real.log L * (Real.log C_bound / Real.log L)) :=
      Real.rpow_def_of_pos hL_pos (Real.log C_bound / Real.log L)
    rw [h_exp]
    have h9 : Real.log L * (Real.log C_bound / Real.log L) = Real.log C_bound := by
      field_simp [h_log_L_pos.ne'] <;> ring
    rw [h9]
    exact Real.exp_log hC_bound_pos
  have h_L_CK : Real.rpow L (C - K) ≥ KCT' := by
    have h1 : C - K = Real.log C_bound / Real.log L + 1 := by
      dsimp only [C] <;> ring
    rw [h1]
    have h2 : Real.rpow L (Real.log C_bound / Real.log L + 1) =
        Real.rpow L (Real.log C_bound / Real.log L) * Real.rpow L 1 := Real.rpow_add hL_pos _ _
    have h2' : Real.rpow L 1 = L := by simp
    have h3 : Real.rpow L (Real.log C_bound / Real.log L + 1) = C_bound * L := by
      rw [h2, h2', h_rpow_Cbound] <;> ring
    rw [h3]
    have h4 : C_bound * L ≥ C_bound := by nlinarith
    have h6 : C_bound ≥ KCT' := le_max_right _ _
    linarith
  have h_δ_εN_le_one : Real.rpow δ ε_N ≤ 1 := by
    have h1 : δ ≤ 1 := by linarith
    exact Real.rpow_le_one (by linarith) h1 (by linarith)
  have h1 : Real.rpow L (C - K) ≥ KCT' * Real.rpow δ ε_N := by
    have h2 : KCT' * Real.rpow δ ε_N ≤ KCT' := by nlinarith
    linarith [h_L_CK]
  have h_main_ineq : (1 / KCT') * Real.rpow L (-K) ≥
      Real.rpow L (-C) * Real.rpow δ ε_N := by
    have h4 : 0 < KCT' := hKCT'pos
    have h5 : Real.rpow L (C - K) / KCT' ≥ Real.rpow δ ε_N := by
      calc Real.rpow L (C - K) / KCT'
        ≥ (KCT' * Real.rpow δ ε_N) / KCT' := by gcongr
      _ = Real.rpow δ ε_N := by field_simp [h4.ne'] <;> ring
    have h7 : Real.rpow L (-C) * Real.rpow L (C - K) = Real.rpow L (-K) := by
      have h := Real.rpow_add hL_pos (-C) (C - K)
      have h71 : -C + (C - K) = -K := by ring
      rw [h71] at h; exact h.symm
    have h6 : (1 / KCT') * Real.rpow L (-K) =
        Real.rpow L (-C) * (Real.rpow L (C - K) / KCT') := by
      calc (1 / KCT') * Real.rpow L (-K)
        = (1 / KCT') * (Real.rpow L (-C) * Real.rpow L (C - K)) := by rw [h7]
      _ = Real.rpow L (-C) * (Real.rpow L (C - K) / KCT') := by ring
    rw [h6]
    have h8 : 0 ≤ Real.rpow L (-C) := Real.rpow_nonneg (by linarith) (-C)
    exact mul_le_mul_of_nonneg_left h5 h8
  exact ⟨C, hC_pos, h_main_ineq⟩

/-! ========================================================================
    Helper: simplify combiningLowerBound for n=1, good scale, C'=1
    ======================================================================== -/

lemma combiningLowerBound_good_cprime1
    {δ M C lam s ε_N η : ℝ} {Δ : Fin 2 → ℝ} {scaleClass : Fin 1 → ScaleClass}
    {t_j : ℝ}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (h_good : scaleClass 0 = ScaleClass.good t_j)
    (hΔ0 : Δ 0 = 1) (hΔ1 : Δ 1 = δ) (hL_eq : ∀ (x : ℝ), Real.rpow (Real.log (1 / δ)) x = Real.rpow (Real.log (1 / δ)) x) :
    combiningLowerBound δ M C 1 lam s ε_N η 1 Δ scaleClass =
    Real.rpow (Real.log (1 / δ)) (-C) * M * Real.rpow δ (lam - s + ε_N - η) := by
  dsimp only [combiningLowerBound]
  have h_good_set : (Finset.univ.filter (fun j : Fin 1 => (scaleClass j).isGood)) =
      ({0} : Finset (Fin 1)) := by
    ext j; fin_cases j; simp [h_good, ScaleClass.isGood]
  have h_bad_set : (Finset.univ.filter (fun j : Fin 1 => (scaleClass j).isBad)) =
      (∅ : Finset (Fin 1)) := by
    ext j; fin_cases j; simp [h_good, ScaleClass.isBad]
  have h_good_prod : (∏ j ∈ (Finset.univ.filter (fun j : Fin 1 => (scaleClass j).isGood)),
      Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) = Real.rpow (1 / δ) η := by
    rw [h_good_set]
    simp [hΔ0, hΔ1, Finset.prod_singleton] <;> ring
  have h_bad_prod : (∏ j ∈ (Finset.univ.filter (fun j : Fin 1 => (scaleClass j).isBad)),
      Δ (Fin.succ j) / Δ j.castSucc) = 1 := by
    rw [h_bad_set]; simp
  have h1_divdelta_rpow : Real.rpow (1 / δ) η = Real.rpow δ (-η) := by
    have h_pos2 : 0 < 1 / δ := by positivity
    have h_log : Real.log (1 / δ) = - Real.log δ := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_one] <;> ring
    have h_left : Real.rpow (1 / δ) η = Real.exp (Real.log (1 / δ) * η) :=
      Real.rpow_def_of_pos h_pos2 η
    have h_right : Real.rpow δ (-η) = Real.exp (Real.log δ * (-η)) :=
      Real.rpow_def_of_pos hδ_pos (-η)
    rw [h_left, h_right, h_log] <;> ring_nf
  rw [h_good_prod, h_bad_prod, h1_divdelta_rpow]
  have h21 : Real.rpow δ (1 * lam) * Real.rpow δ (-s + ε_N) * Real.rpow δ (-η) =
      Real.rpow δ (lam - s + ε_N - η) := by
    have h22 : Real.rpow δ (1 * lam) * Real.rpow δ (-s + ε_N) =
        Real.rpow δ (1 * lam + (-s + ε_N)) := by
      exact (Real.rpow_add hδ_pos (1 * lam) (-s + ε_N)).symm
    have h23 : Real.rpow δ (1 * lam + (-s + ε_N)) * Real.rpow δ (-η) =
        Real.rpow δ ((1 * lam + (-s + ε_N)) + (-η)) := by
      exact (Real.rpow_add hδ_pos (1 * lam + (-s + ε_N)) (-η)).symm
    rw [h22, h23] <;> ring_nf
  have h_regroup : Real.rpow (Real.log (1 / δ)) (-C) * M *
      Real.rpow δ (1 * lam) * Real.rpow δ (-s + ε_N) * Real.rpow δ (-η) * (1 : ℝ) =
      Real.rpow (Real.log (1 / δ)) (-C) * M *
        (Real.rpow δ (1 * lam) * Real.rpow δ (-s + ε_N) * Real.rpow δ (-η)) := by ring
  rw [h_regroup, h21] <;> ring

/-! ========================================================================
    Base case good universal (C'=1)
    ======================================================================== -/

lemma base_case_good_universal
    {s t τ ε_G η ε_N C_P lam : ℝ} {k M : ℕ}
    {C_between : Fin 1 → ℝ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {Δ : Fin 2 → ℝ} {scaleClass : Fin 1 → ScaleClass} {N : Fin 1 → ℕ}
    {t_j : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hlam : 0 < lam) (hεN : 0 < ε_N) (hCP : 0 < C_P)
    (hεG : 0 < ε_G) (hη : 0 < η)
    (hst : s < t)
    (hk_ge_2 : 2 ≤ k)
    (h_good : scaleClass 0 = ScaleClass.good t_j)
    (hcfg : CombiningConfig s t τ 1 ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (hP_set_tj : IsFinsetDeltaSSet (dyadicDelta k) t_j C_P
        (finsetDyadicToDSquare config.P₀))
    (h_slope : ∀ T ∈ config.T₀, |T.slope| ≤ 1)
    (htj_ge_t : t ≤ t_j)
    (htj_le_one : t_j ≤ 1)
    (h_improved_incidence :
        (config.T₀.card : ENNReal) ≥ ENNReal.ofReal (Real.rpow (dyadicDelta k) (-(2 * s + ε_G))))
    (h_exp_condition : (η + 2 * ε_G) * (1 - s) / (t - s) ≤ ε_G + lam + ε_N - η)
    :
    ∃ (C C' : ℝ), 0 < C ∧ 0 < C' ∧
      (config.T₀.card : ENNReal) ≥
        ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) C C'
          lam s ε_N η 1 Δ scaleClass) := by
  let δ : ℝ := dyadicDelta k
  have hδ_pos : 0 < δ := dyadicDelta_pos k
  have hδ_le_quarter : δ ≤ 1 / 4 := by
    have h1 : (k : ℕ) ≥ 2 := hk_ge_2
    have h2 : δ = ((2 : ℝ)^k)⁻¹ := by
      simp [δ, dyadicDelta, zpow_neg, zpow_ofNat] <;> ring
    rw [h2]
    have h3 : (2 : ℝ)^k ≥ 4 := by
      have h4 : (2 : ℝ)^k ≥ (2 : ℝ)^(2 : ℕ) := by gcongr <;> norm_num
      norm_num at h4 ⊢ <;> exact h4
    have h5 : 0 < (2 : ℝ)^k := by positivity
    have h6 : ((2 : ℝ)^k)⁻¹ ≤ (4 : ℝ)⁻¹ := by gcongr
    norm_num at h6 ⊢ <;> exact h6
  have hδ_lt_one : δ < 1 := by linarith
  have hδ_le_one : δ ≤ 1 := by linarith
  have hM_pos : 0 < M := hcfg.hM_pos
  have hP_nonempty : config.P₀.Nonempty := by
    have h_unif : IsUniformAtScales config.pointSet 1 Δ N := hcfg.h_uniform
    have h_pointSet_nonempty : config.pointSet.Nonempty := h_unif.1
    rcases h_pointSet_nonempty with ⟨x, hx⟩
    have h2 : ∃ (p : DyadicSquare k), p ∈ config.P₀ ∧ x ∈ p.toSet := by
      simpa [NiceConfiguration.pointSet, Set.mem_iUnion] using hx
    rcases h2 with ⟨p, hp, _⟩
    exact ⟨p, hp⟩
  let C₁ : ℝ := Real.rpow δ (-lam)
  have hC₁_pos : 0 < C₁ := Real.rpow_pos_of_pos hδ_pos (-lam)
  set γ : ℝ := (η + 2 * ε_G) * (1 - s) / (t - s) with hγ_def
  have hγ_pos : 0 < γ := by
    rw [hγ_def]
    have h1 : 0 < η + 2 * ε_G := by linarith
    have h2 : 0 < 1 - s := by linarith
    have h3 : 0 < t - s := by linarith
    positivity
  set α : ℝ := (t_j - s) / (1 - s) with hα_def
  have hα_nonneg : 0 ≤ α := by
    have h1 : 0 ≤ t_j - s := by linarith
    have h2 : 0 < 1 - s := by linarith
    exact div_nonneg h1 (by linarith)
  have hγ_α_ge : γ * α ≥ η + 2 * ε_G := by
    rw [hγ_def, hα_def]
    have h1 : 0 < t - s := by linarith
    have h2 : 0 < 1 - s := by linarith
    have h4 : ((η + 2 * ε_G) * (1 - s) / (t - s)) * ((t_j - s) / (1 - s)) =
        (η + 2 * ε_G) * (t_j - s) / (t - s) := by
      field_simp [h1.ne', h2.ne'] <;> ring
    rw [h4]
    have h5 : 0 < η + 2 * ε_G := by linarith
    have h6 : t_j - s ≥ t - s := by linarith
    have h7 : (η + 2 * ε_G) * (t_j - s) / (t - s) ≥ (η + 2 * ε_G) := by
      have h8 : (η + 2 * ε_G) * (t_j - s) ≥ (η + 2 * ε_G) * (t - s) := by gcongr
      have h9 : ((η + 2 * ε_G) * (t_j - s) / (t - s)) ≥
          ((η + 2 * ε_G) * (t - s) / (t - s)) := by gcongr
      have h10 : ((η + 2 * ε_G) * (t - s) / (t - s)) = (η + 2 * ε_G) := by
        field_simp [h1.ne'] <;> ring
      linarith
    exact h7
  have h_neg_γ_α_le : -γ * α ≤ -(η + 2 * ε_G) := by linarith

  let L : ℝ := Real.log (1 / δ)
  have hL_gt_one : 1 < L := by
    have h3 : 1 / δ ≥ 4 := by
      have h4 : δ ≤ 1 / 4 := hδ_le_quarter
      have h5 : 0 < δ := hδ_pos
      calc 1 / δ ≥ 1 / (1 / 4) := by gcongr
      _ = 4 := by norm_num
    have h4 : Real.log (1 / δ) ≥ Real.log 4 := Real.log_le_log (by positivity) h3
    have h5 : (1 : ℝ) < Real.log 4 := by
      have h6 : Real.exp 1 < (4 : ℝ) := by linarith [Real.exp_one_lt_d9]
      have h7 : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (by positivity) h6
      have h8 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
      rw [h8] at h7; exact h7
    linarith
  have hL_pos : 0 < L := by linarith

  have hΔ0 : Δ 0 = 1 := hcfg.hΔ_start
  have hΔ1 : Δ 1 = δ := hcfg.hΔ_end

  by_cases hM_large : (M : ℝ) ≥ Real.rpow δ (-s - γ)
  · -- LARGE M CASE
    have h_st : 0 ≤ s ∧ s ≤ t_j ∧ t_j ≤ 1 := by
      exact ⟨by linarith, by linarith, by linarith⟩
    have hs_nonneg : 0 ≤ s := by linarith
    rcases prop5_wrapper (s := s) (t := t_j) (C₁ := C₁) (C_P := C_P) config
        hk_ge_2 hM_pos hP_nonempty h_st hCP hC₁_pos hs_nonneg hP_set_tj h_slope
      with ⟨K, hK_pos, h_prop5⟩
    set KCT' : ℝ := K * C_P * 13 * Real.rpow 2 s with hKCT'def
    have h2s_pos : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
    have hKCT'pos : 0 < KCT' := by
      dsimp only [KCT']
      have h13_pos : (0 : ℝ) < 13 := by norm_num
      exact mul_pos (mul_pos (mul_pos hK_pos hCP) h13_pos) h2s_pos
    have h_inv_C1 : (1 : ℝ) / C₁ = Real.rpow δ lam := by
      rw [show C₁ = Real.rpow δ (-lam) from rfl]
      have h_pos1 : 0 < Real.rpow δ (-lam) := Real.rpow_pos_of_pos hδ_pos (-lam)
      have h_eq : Real.rpow δ (-lam) * Real.rpow δ lam = 1 := by
        have h := Real.rpow_add hδ_pos (-lam) lam
        have h5 : -lam + lam = 0 := by ring
        rw [h5] at h; simpa using h.symm
      have h_goal : (1 : ℝ) / Real.rpow δ (-lam) = Real.rpow δ lam := by
        field_simp [h_pos1.ne'] <;> linarith
      exact h_goal

    have hδs_nonneg : 0 ≤ Real.rpow δ s := Real.rpow_nonneg hδ_pos.le s
    have hMδs : (M : ℝ) * Real.rpow δ s ≥ Real.rpow δ (-γ) := by
      have h1 : (M : ℝ) ≥ Real.rpow δ (-s - γ) := hM_large
      have h2 : (M : ℝ) * Real.rpow δ s ≥ Real.rpow δ (-s - γ) * Real.rpow δ s :=
        mul_le_mul_of_nonneg_right h1 hδs_nonneg
      have h3 : Real.rpow δ (-s - γ) * Real.rpow δ s = Real.rpow δ (-γ) := by
        have h4 := Real.rpow_add hδ_pos (-s - γ) s
        have h5 : (-s - γ) + s = -γ := by ring
        rw [h5] at h4; exact h4.symm
      rw [h3] at h2; exact h2

    have h5 : (Real.rpow δ (-γ)) ^ α = Real.rpow δ (-γ * α) := by
      have h_pos : 0 ≤ δ := by linarith
      have h7 : (δ ^ (-γ)) ^ α = δ ^ (-γ * α) := (Real.rpow_mul h_pos (-γ) α).symm
      exact h7
    have h_base_nonneg : 0 ≤ Real.rpow δ (-γ) := Real.rpow_nonneg hδ_pos.le _
    have hMδs_nonneg : 0 ≤ (M : ℝ) * Real.rpow δ s := by positivity
    have h_factor : ((M : ℝ) * Real.rpow δ s) ^ α ≥ Real.rpow δ (-γ * α) := by
      have h_ineq2 : ((M : ℝ) * Real.rpow δ s) ^ α ≥ (Real.rpow δ (-γ)) ^ α := by
        exact Real.rpow_le_rpow h_base_nonneg hMδs hα_nonneg
      rw [h5] at h_ineq2; exact h_ineq2
    have h6 : Real.rpow δ (-γ * α) ≥ Real.rpow δ (-(η + 2 * ε_G)) :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h_neg_γ_α_le
    have h_factor2 : ((M : ℝ) * Real.rpow δ s) ^ α ≥ Real.rpow δ (-(η + 2 * ε_G)) :=
      le_trans h6 h_factor

    -- Simplify prop5 expression
    have h_simp_coeff : (1 / K) * (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) =
        (1 / KCT') * Real.rpow δ lam := by
      have h1 : (1 / K) * (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) =
          (1 / KCT') * (1 / C₁) := by
        simp only [hKCT'def] <;> ring
      rw [h1, h_inv_C1]

    -- Convert prop5 to standard notation
    have h_prop5_std : (config.T₀.card : ℝ) ≥
        (1 / K) * Real.rpow L (-K) *
          (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) * (M : ℝ) *
          Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α := by
      simpa [L, δ, α] using h_prop5

    have h_coeff_eq : (1 / K) * Real.rpow L (-K) * (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) =
        (1 / KCT') * Real.rpow L (-K) * Real.rpow δ lam := by
      have h1 : (1 / K) * (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) =
          (1 / KCT') * (1 / C₁) := by
        simp only [hKCT'def] <;> ring
      calc
        (1 / K) * Real.rpow L (-K) * (1 / (C_P * (13 * C₁ * Real.rpow 2 s)))
          = Real.rpow L (-K) * ((1 / K) * (1 / (C_P * (13 * C₁ * Real.rpow 2 s)))) := by ring
        _ = Real.rpow L (-K) * ((1 / KCT') * (1 / C₁)) := by rw [h1]
        _ = Real.rpow L (-K) * ((1 / KCT') * Real.rpow δ lam) := by rw [h_inv_C1]
        _ = (1 / KCT') * Real.rpow L (-K) * Real.rpow δ lam := by ring
    have h_bound_full : (config.T₀.card : ℝ) ≥
        (1 / KCT') * Real.rpow L (-K) * (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s) *
          ((M : ℝ) * Real.rpow δ s) ^ α := by
      have h : (config.T₀.card : ℝ) ≥
          (1 / K) * Real.rpow L (-K) * (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) * (M : ℝ) *
            Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α := h_prop5_std
      rw [h_coeff_eq] at h
      have h' : (config.T₀.card : ℝ) ≥
          (1 / KCT') * Real.rpow L (-K) * (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s) *
            ((M : ℝ) * Real.rpow δ s) ^ α := by
        ring_nf at h ⊢
        exact h
      exact h'

    -- Core absorption
    rcases absorb_core_ineq hδ_pos hδ_le_quarter hL_gt_one hK_pos hKCT'pos hεN
      with ⟨C, hC_pos, h_absorb⟩
    let C' : ℝ := 1
    have hC'_pos : 0 < C' := by norm_num

    have hδ_lam_pos : 0 < Real.rpow δ lam := Real.rpow_pos_of_pos hδ_pos lam
    have hδ_neg_s_pos : 0 < Real.rpow δ (-s) := Real.rpow_pos_of_pos hδ_pos (-s)
    have hL_negC_nonneg : 0 ≤ Real.rpow L (-C) := Real.rpow_nonneg hL_pos.le _
    have hM_nonneg : 0 ≤ (M : ℝ) := by positivity

    -- Multiply absorption inequality by positive factors
    have h9 : (1 / KCT') * Real.rpow L (-K) * (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s) *
          ((M : ℝ) * Real.rpow δ s) ^ α ≥
        Real.rpow L (-C) * (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s + ε_N) *
          ((M : ℝ) * Real.rpow δ s) ^ α := by
      have h10 : Real.rpow δ ε_N * Real.rpow δ (-s) = Real.rpow δ (-s + ε_N) := by
        have h11 : Real.rpow δ (ε_N + (-s)) = Real.rpow δ ε_N * Real.rpow δ (-s) :=
          Real.rpow_add hδ_pos ε_N (-s)
        have h12 : ε_N + (-s) = -s + ε_N := by ring
        rw [h12] at h11
        exact h11.symm
      have h_pos_factor : 0 ≤ (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s) *
          ((M : ℝ) * Real.rpow δ s) ^ α := by positivity
      calc
        (1 / KCT') * Real.rpow L (-K) * (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s) *
            ((M : ℝ) * Real.rpow δ s) ^ α
          = ((1 / KCT') * Real.rpow L (-K)) *
              ((M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α) := by ring
        _ ≥ (Real.rpow L (-C) * Real.rpow δ ε_N) *
              ((M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s) * ((M : ℝ) * Real.rpow δ s) ^ α) := by
          exact mul_le_mul_of_nonneg_right h_absorb h_pos_factor
        _ = Real.rpow L (-C) * (M : ℝ) * Real.rpow δ lam *
              (Real.rpow δ ε_N * Real.rpow δ (-s)) * ((M : ℝ) * Real.rpow δ s) ^ α := by ring
        _ = Real.rpow L (-C) * (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s + ε_N) *
              ((M : ℝ) * Real.rpow δ s) ^ α := by rw [h10] <;> ring

    have h12 : 0 ≤ Real.rpow L (-C) * (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s + ε_N) := by
      have h1 : 0 ≤ Real.rpow L (-C) := Real.rpow_nonneg hL_pos.le _
      have h2 : 0 ≤ (M : ℝ) := by positivity
      have h3 : 0 ≤ Real.rpow δ lam := Real.rpow_nonneg hδ_pos.le _
      have h4 : 0 ≤ Real.rpow δ (-s + ε_N) := Real.rpow_nonneg hδ_pos.le _
      exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
    have h11 : Real.rpow L (-C) * (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s + ε_N) *
          ((M : ℝ) * Real.rpow δ s) ^ α ≥
        Real.rpow L (-C) * (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s + ε_N) *
          Real.rpow δ (-(η + 2 * ε_G)) := by
      exact mul_le_mul_of_nonneg_left h_factor2 h12

    have h13 : Real.rpow δ lam * Real.rpow δ (-s + ε_N) * Real.rpow δ (-(η + 2 * ε_G)) =
        Real.rpow δ (lam - s + ε_N - η - 2 * ε_G) := by
      have h14 : Real.rpow δ lam * Real.rpow δ (-s + ε_N) =
          Real.rpow δ (lam + (-s + ε_N)) := by
        exact (Real.rpow_add hδ_pos lam (-s + ε_N)).symm
      have h15 : Real.rpow δ (lam + (-s + ε_N)) * Real.rpow δ (-(η + 2 * ε_G)) =
          Real.rpow δ ((lam + (-s + ε_N)) + (-(η + 2 * ε_G))) := by
        exact (Real.rpow_add hδ_pos (lam + (-s + ε_N)) (-(η + 2 * ε_G))).symm
      rw [h14, h15] <;> ring_nf
    have h16 : Real.rpow δ (lam - s + ε_N - η - 2 * ε_G) ≥
        Real.rpow δ (lam - s + ε_N - η) := by
      have h17 : lam - s + ε_N - η - 2 * ε_G ≤ lam - s + ε_N - η := by linarith
      exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h17

    have h_main_good : (config.T₀.card : ℝ) ≥
        Real.rpow L (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η) := by
      calc (config.T₀.card : ℝ)
        ≥ (1 / KCT') * Real.rpow L (-K) * (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s) *
            ((M : ℝ) * Real.rpow δ s) ^ α := h_bound_full
        _ ≥ Real.rpow L (-C) * (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s + ε_N) *
              ((M : ℝ) * Real.rpow δ s) ^ α := h9
        _ ≥ Real.rpow L (-C) * (M : ℝ) * Real.rpow δ lam * Real.rpow δ (-s + ε_N) *
              Real.rpow δ (-(η + 2 * ε_G)) := h11
        _ = Real.rpow L (-C) * (M : ℝ) *
              (Real.rpow δ lam * Real.rpow δ (-s + ε_N) * Real.rpow δ (-(η + 2 * ε_G))) := by ring
        _ = Real.rpow L (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η - 2 * ε_G) := by
          rw [h13]
        _ ≥ Real.rpow L (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η) := by
          have h18 : 0 ≤ Real.rpow L (-C) * (M : ℝ) := by
            exact mul_nonneg hL_negC_nonneg hM_nonneg
          exact mul_le_mul_of_nonneg_left h16 h18

    have h_bound_simp : combiningLowerBound δ (M : ℝ) C 1 lam s ε_N η 1 Δ scaleClass =
        Real.rpow L (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η) :=
      combiningLowerBound_good_cprime1 hδ_pos hδ_le_one h_good hΔ0 hΔ1 (fun _ => rfl)
    have h_nonneg : 0 ≤ Real.rpow L (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η) := by
      have h1 : 0 ≤ Real.rpow L (-C) := Real.rpow_nonneg hL_pos.le _
      have h2 : 0 ≤ (M : ℝ) := by positivity
      have h3 : 0 ≤ Real.rpow δ (lam - s + ε_N - η) := Real.rpow_nonneg hδ_pos.le _
      positivity
    have h_final : (config.T₀.card : ENNReal) ≥
        ENNReal.ofReal (combiningLowerBound δ (M : ℝ) C 1 lam s ε_N η 1 Δ scaleClass) := by
      rw [h_bound_simp]
      have h20 : ENNReal.ofReal (Real.rpow L (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η)) ≤
          ENNReal.ofReal ((config.T₀.card : ℝ)) :=
        ENNReal.ofReal_le_ofReal h_main_good
      have h21 : ENNReal.ofReal ((config.T₀.card : ℝ)) = (config.T₀.card : ENNReal) := by simp
      rw [h21] at h20
      exact h20
    exact ⟨C, 1, hC_pos, by norm_num, h_final⟩

  · -- SMALL M CASE
    have hM_small : (M : ℝ) < Real.rpow δ (-s - γ) := by
      exact lt_of_not_ge hM_large
    let C' : ℝ := 1
    have hC'_pos : 0 < C' := by norm_num
    let C : ℝ := 1
    have hC_pos : 0 < C := by norm_num

    have h_exp_ge : lam - 2 * s - γ + ε_N - η ≥ -(2 * s + ε_G) := by
      linarith [h_exp_condition]
    have hL_neg_C_le_one : Real.rpow L (-C) ≤ 1 := by
      have h1 : 1 ≤ L := by linarith
      have h2 : -C ≤ 0 := by linarith
      have h3 : Real.rpow L (-C) ≤ Real.rpow L 0 :=
        Real.rpow_le_rpow_of_exponent_le h1 h2
      have h4 : Real.rpow L 0 = 1 := by simp
      rw [h4] at h3; exact h3

    have hT_lower_real : (config.T₀.card : ℝ) ≥ Real.rpow δ (-(2 * s + ε_G)) := by
      exact_mod_cast h_improved_incidence

    have hδ_exp_nonneg : 0 ≤ Real.rpow δ (lam - s + ε_N - η) := Real.rpow_nonneg hδ_pos.le _
    have hL_negC_nonneg : 0 ≤ Real.rpow L (-C) := Real.rpow_nonneg hL_pos.le _
    have hM_nonneg : 0 ≤ (M : ℝ) := by positivity

    have h_rpow_combine : Real.rpow δ (-s - γ) * Real.rpow δ (lam - s + ε_N - η) =
        Real.rpow δ (lam - 2 * s - γ + ε_N - η) := by
      have h10 := Real.rpow_add hδ_pos (-s - γ) (lam - s + ε_N - η)
      have h11 : (-s - γ) + (lam - s + ε_N - η) = lam - 2 * s - γ + ε_N - η := by ring
      rw [h11] at h10; exact h10.symm

    have h6 : Real.rpow L (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η) <
        Real.rpow δ (-(2 * s + ε_G)) := by
      have h_posL : 0 < Real.rpow L (-C) := Real.rpow_pos_of_pos hL_pos (-C)
      have h_pos_exp : 0 < Real.rpow δ (lam - s + ε_N - η) :=
        Real.rpow_pos_of_pos hδ_pos (lam - s + ε_N - η)
      have h7 : Real.rpow L (-C) * (M : ℝ) < Real.rpow L (-C) * Real.rpow δ (-s - γ) :=
        mul_lt_mul_of_pos_left hM_small h_posL
      have h8 : Real.rpow L (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η) <
          Real.rpow L (-C) * Real.rpow δ (-s - γ) * Real.rpow δ (lam - s + ε_N - η) := by
        exact mul_lt_mul_of_pos_right h7 h_pos_exp
      have h9 : Real.rpow L (-C) * Real.rpow δ (-s - γ) * Real.rpow δ (lam - s + ε_N - η) =
          Real.rpow L (-C) * Real.rpow δ (lam - 2 * s - γ + ε_N - η) := by
        have h_assoc : Real.rpow L (-C) * Real.rpow δ (-s - γ) * Real.rpow δ (lam - s + ε_N - η) =
            Real.rpow L (-C) * (Real.rpow δ (-s - γ) * Real.rpow δ (lam - s + ε_N - η)) := by ring
        rw [h_assoc, h_rpow_combine] <;> ring
      rw [h9] at h8
      have h11 : Real.rpow L (-C) * Real.rpow δ (lam - 2 * s - γ + ε_N - η) ≤
          Real.rpow δ (lam - 2 * s - γ + ε_N - η) := by
        have h12 : 0 ≤ Real.rpow δ (lam - 2 * s - γ + ε_N - η) := Real.rpow_nonneg hδ_pos.le _
        nlinarith [hL_neg_C_le_one]
      have h14 : Real.rpow δ (lam - 2 * s - γ + ε_N - η) ≤
          Real.rpow δ (-(2 * s + ε_G)) := by
        exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h_exp_ge
      calc
        Real.rpow L (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η)
          < Real.rpow L (-C) * Real.rpow δ (lam - 2 * s - γ + ε_N - η) := h8
        _ ≤ Real.rpow δ (lam - 2 * s - γ + ε_N - η) := h11
        _ ≤ Real.rpow δ (-(2 * s + ε_G)) := h14

    have h_main_real : (config.T₀.card : ℝ) ≥
        Real.rpow L (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η) := by
      exact le_trans (le_of_lt h6) hT_lower_real

    have h_bound_simp : combiningLowerBound δ (M : ℝ) C 1 lam s ε_N η 1 Δ scaleClass =
        Real.rpow L (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η) :=
      combiningLowerBound_good_cprime1 hδ_pos hδ_le_one h_good hΔ0 hΔ1 (fun _ => rfl)
    have h_nonneg2 : 0 ≤ Real.rpow L (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η) := by
      have h1 : 0 ≤ Real.rpow L (-C) := Real.rpow_nonneg hL_pos.le _
      have h2 : 0 ≤ (M : ℝ) := by positivity
      have h3 : 0 ≤ Real.rpow δ (lam - s + ε_N - η) := Real.rpow_nonneg hδ_pos.le _
      positivity
    have h_final : (config.T₀.card : ENNReal) ≥
        ENNReal.ofReal (combiningLowerBound δ (M : ℝ) C 1 lam s ε_N η 1 Δ scaleClass) := by
      rw [h_bound_simp]
      have h20 : ENNReal.ofReal (Real.rpow L (-C) * (M : ℝ) * Real.rpow δ (lam - s + ε_N - η)) ≤
          ENNReal.ofReal ((config.T₀.card : ℝ)) :=
        ENNReal.ofReal_le_ofReal h_main_real
      have h21 : ENNReal.ofReal ((config.T₀.card : ℝ)) = (config.T₀.card : ENNReal) := by simp
      rw [h21] at h20
      exact h20
    exact ⟨C, 1, hC_pos, by norm_num, h_final⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
