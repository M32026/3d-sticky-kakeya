module

/-
  Combining Theorem Base Case (n=1) - Normal Scale (Universal C'=1)

  Uses prop5_wrapper (SL-7) with t=s to get the elementary incidence bound,
  then absorbs into combiningLowerBound with C'=1 (lam-independent).

  Key algebra:
    prop5: |T| ≥ (1/K) · L^{-K} · (1/(C_P·C_T)) · M · δ^{-s}
    C_T = 13 · δ^{-lam} · 2^s, so 1/C_T = δ^{lam}/(13·2^s)
    => |T| ≥ (1/(K·C_P·13·2^s)) · L^{-K} · M · δ^{lam-s}

    Target (C'=1): L^{-C} · M · δ^{lam-s+ε_N}
    Since δ^{ε_N} ≤ 1, it suffices L^{C-K} ≥ K·C_P·13·2^s.
    Choose C = K + log(max 1 (K·C_P·13·2^s))/log L + 1.

  Whiteprint node: combining_theorem_rework / base_case_normal_universal
  Dependencies: FormatConversionLemmas (prop5_wrapper), CombiningTheorem
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
    Absorption lemma: prop5 bound → combiningLowerBound with C'=1
    ======================================================================== -/

/-- Absorb a prop5 lower bound (with C₁ = δ^{-lam}) into the combining lower
    bound formula with C' = 1. The constant C may depend on δ (through L)
    and on all other parameters except lam; C' = 1 is independent of lam. -/
lemma absorb_normal_cprime_one
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le_quarter : δ ≤ 1 / 4)
    {K C_P C₁ M lam ε_N s T_card : ℝ}
    (hK_pos : 0 < K) (hCP : 0 < C_P) (hC₁_pos : 0 < C₁)
    (hM_pos : 0 < M) (hlam : 0 < lam) (hεN : 0 < ε_N)
    (hs : 0 < s) (hs1 : s < 1)
    (hC₁_eq : C₁ = Real.rpow δ (-lam))
    (h_bound : T_card ≥ (1 / K) * Real.rpow (Real.log (1 / δ)) (-K) *
        (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) * M * Real.rpow δ (-s)) :
    ∃ (C : ℝ), 0 < C ∧
      T_card ≥ Real.rpow (Real.log (1 / δ)) (-C) * M *
        Real.rpow δ (1 * lam) * Real.rpow δ (-s + ε_N) := by
  set L : ℝ := Real.log (1 / δ) with hL_def
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
  have hL_one : 1 ≤ L := by linarith
  have h2s_pos : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
  -- KCT' excludes C₁; the δ^lam factor comes from 1/C₁
  set KCT' : ℝ := K * C_P * 13 * Real.rpow 2 s with hKCT'def
  have hKCT'pos : 0 < KCT' := by positivity
  set C_bound : ℝ := max 1 KCT' with hC_bound_def
  have hC_bound_ge_one : 1 ≤ C_bound := le_max_left _ _
  have hC_bound_pos : 0 < C_bound := by linarith
  have hKCT'_le_Cbound : KCT' ≤ C_bound := le_max_right _ _
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
        Real.exp ((Real.log C_bound / Real.log L) * Real.log L) := by
      have h : L ^ (Real.log C_bound / Real.log L) = Real.exp (Real.log L * (Real.log C_bound / Real.log L)) :=
        Real.rpow_def_of_pos hL_pos _
      have h' : Real.rpow L (Real.log C_bound / Real.log L) = L ^ (Real.log C_bound / Real.log L) := by rfl
      rw [h']; rw [h] <;> ring_nf
    rw [h_exp]
    have h9 : (Real.log C_bound / Real.log L) * Real.log L = Real.log C_bound := by
      field_simp [h_log_L_pos.ne'] <;> ring
    rw [h9, Real.exp_log hC_bound_pos]
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
    have h4 : C_bound * L ≥ C_bound := by
      have h5 : 1 ≤ L := hL_one
      nlinarith
    have h6 : C_bound ≥ KCT' := hKCT'_le_Cbound
    linarith
  have h_δ_εN_le_one : Real.rpow δ ε_N ≤ 1 := by
    have h1 : δ ≤ 1 := by linarith
    exact Real.rpow_le_one (by linarith) h1 (by linarith)
  have h1 : Real.rpow L (C - K) ≥ KCT' * Real.rpow δ ε_N := by
    have h2 : KCT' * Real.rpow δ ε_N ≤ KCT' := by
      have h3 : Real.rpow δ ε_N ≤ 1 := h_δ_εN_le_one
      nlinarith
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
      rw [h71] at h
      exact h.symm
    have h6 : (1 / KCT') * Real.rpow L (-K) =
        Real.rpow L (-C) * (Real.rpow L (C - K) / KCT') := by
      calc (1 / KCT') * Real.rpow L (-K)
        = (1 / KCT') * (Real.rpow L (-C) * Real.rpow L (C - K)) := by rw [h7]
      _ = Real.rpow L (-C) * (Real.rpow L (C - K) / KCT') := by ring
    rw [h6]
    have h8 : 0 ≤ Real.rpow L (-C) := Real.rpow_nonneg (by linarith) (-C)
    exact mul_le_mul_of_nonneg_left h5 h8
  have h_inv_C1 : (1 : ℝ) / C₁ = Real.rpow δ lam := by
    rw [hC₁_eq]
    have h_pos1 : 0 < Real.rpow δ (-lam) := Real.rpow_pos_of_pos hδ_pos (-lam)
    have h_eq : Real.rpow δ (-lam) * Real.rpow δ lam = 1 := by
      have h := Real.rpow_add hδ_pos (-lam) lam
      have h5 : -lam + lam = 0 := by ring
      rw [h5] at h
      simpa using h.symm
    have h_goal : (1 : ℝ) / Real.rpow δ (-lam) = Real.rpow δ lam := by
      field_simp [h_pos1.ne'] <;> linarith
    exact h_goal
  have h_bound_simp : T_card ≥
      (1 / KCT') * Real.rpow L (-K) * M * Real.rpow δ lam * Real.rpow δ (-s) := by
    have h3 : (1 / K) * Real.rpow L (-K) * (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) * M * Real.rpow δ (-s) =
        (1 / KCT') * Real.rpow L (-K) * (1 / C₁) * M * Real.rpow δ (-s) := by
      simp only [hKCT'def] <;> ring
    rw [h3] at h_bound
    rw [h_inv_C1] at h_bound
    have h4 : (1 / KCT') * Real.rpow L (-K) * Real.rpow δ lam * M * Real.rpow δ (-s) =
        (1 / KCT') * Real.rpow L (-K) * M * Real.rpow δ lam * Real.rpow δ (-s) := by ring
    rw [h4] at h_bound
    exact h_bound
  have h_final : T_card ≥
      Real.rpow L (-C) * M * Real.rpow δ (1 * lam) * Real.rpow δ (-s + ε_N) := by
    have h_rpow_sum : Real.rpow δ (1 * lam) * Real.rpow δ (-s + ε_N) =
        Real.rpow δ lam * Real.rpow δ ε_N * Real.rpow δ (-s) := by
      have h1 : Real.rpow δ (1 * lam) = Real.rpow δ lam := by ring_nf
      have h2 : Real.rpow δ (-s + ε_N) = Real.rpow δ ε_N * Real.rpow δ (-s) := by
        have h : Real.rpow δ (ε_N + (-s)) = Real.rpow δ ε_N * Real.rpow δ (-s) := Real.rpow_add hδ_pos ε_N (-s)
        have h3 : -s + ε_N = ε_N + (-s) := by ring
        rw [h3]
        exact h
      rw [h1, h2] <;> ring
    calc T_card
      ≥ (1 / KCT') * Real.rpow L (-K) * M * Real.rpow δ lam * Real.rpow δ (-s) := h_bound_simp
    _ ≥ Real.rpow L (-C) * Real.rpow δ ε_N * M * Real.rpow δ lam * Real.rpow δ (-s) := by
        have h_dlam_pos : 0 < Real.rpow δ lam := Real.rpow_pos_of_pos hδ_pos lam
        have h_ds_pos : 0 < Real.rpow δ (-s) := Real.rpow_pos_of_pos hδ_pos (-s)
        have h_pos : 0 < M * Real.rpow δ lam * Real.rpow δ (-s) := by positivity
        have h : ((1 / KCT') * Real.rpow L (-K)) * (M * Real.rpow δ lam * Real.rpow δ (-s)) ≥
            (Real.rpow L (-C) * Real.rpow δ ε_N) * (M * Real.rpow δ lam * Real.rpow δ (-s)) :=
          mul_le_mul_of_nonneg_right h_main_ineq h_pos.le
        have h_left : ((1 / KCT') * Real.rpow L (-K)) * (M * Real.rpow δ lam * Real.rpow δ (-s)) =
            (1 / KCT') * Real.rpow L (-K) * M * Real.rpow δ lam * Real.rpow δ (-s) := by ring
        have h_right : (Real.rpow L (-C) * Real.rpow δ ε_N) * (M * Real.rpow δ lam * Real.rpow δ (-s)) =
            Real.rpow L (-C) * Real.rpow δ ε_N * M * Real.rpow δ lam * Real.rpow δ (-s) := by ring
        rw [h_left, h_right] at h
        exact h
    _ = Real.rpow L (-C) * M * Real.rpow δ lam * Real.rpow δ ε_N * Real.rpow δ (-s) := by ring
    _ = Real.rpow L (-C) * M * Real.rpow δ (1 * lam) * Real.rpow δ (-s + ε_N) := by
      have h10 : Real.rpow δ ε_N * Real.rpow δ (-s) = Real.rpow δ (-s + ε_N) := by
        have h11 := Real.rpow_add hδ_pos ε_N (-s)
        have h12 : ε_N + (-s) = -s + ε_N := by ring
        rw [h12] at h11
        exact h11.symm
      have h13 : Real.rpow δ (1 * lam) = Real.rpow δ lam := by ring_nf
      have h14 : Real.rpow L (-C) * M * Real.rpow δ lam * Real.rpow δ ε_N * Real.rpow δ (-s) =
          Real.rpow L (-C) * M * Real.rpow δ (1 * lam) * Real.rpow δ (-s + ε_N) := by
        calc
          Real.rpow L (-C) * M * Real.rpow δ lam * Real.rpow δ ε_N * Real.rpow δ (-s)
            = Real.rpow L (-C) * M * Real.rpow δ lam * (Real.rpow δ ε_N * Real.rpow δ (-s)) := by ring
          _ = Real.rpow L (-C) * M * Real.rpow δ lam * Real.rpow δ (-s + ε_N) := by rw [h10]
          _ = Real.rpow L (-C) * M * Real.rpow δ (1 * lam) * Real.rpow δ (-s + ε_N) := by rw [←h13]
      exact h14
  exact ⟨C, hC_pos, h_final⟩

/-! ========================================================================
    Base case normal universal (C'=1)
    ======================================================================== -/

/-- Base case: single Normal scale block, universal version with C'=1.

    Uses prop5_wrapper with t=s, then absorbs with C'=1 (lam-independent).
    The constant C may depend on δ and all parameters except lam; C'=1 does
    not depend on lam.

    Extra hypotheses:
    - hP_set: discrete S-set property on the point squares
    - h_slope: tube slope bound |slope| ≤ 1
-/
lemma base_case_normal_universal
    {s t τ ε_G η ε_N C_P lam : ℝ} {k M : ℕ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {Δ : Fin 2 → ℝ} {scaleClass : Fin 1 → ScaleClass} {N : Fin 1 → ℕ}
    {C_between : Fin 1 → ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hlam : 0 < lam) (hεN : 0 < ε_N) (hCP : 0 < C_P)
    (hk_ge_2 : 2 ≤ k)
    (h_normal : scaleClass 0 = ScaleClass.normal)
    (hcfg : CombiningConfig s t τ 1 ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (hP_set : IsFinsetDeltaSSet (dyadicDelta k) s C_P
        (finsetDyadicToDSquare config.P₀))
    (h_slope : ∀ T ∈ config.T₀, |T.slope| ≤ 1) :
    ∃ (C C' : ℝ), 0 < C ∧ 0 < C' ∧
      (config.T₀.card : ENNReal) ≥
        ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) C C'
          lam s ε_N η 1 Δ scaleClass) := by
  have hM_pos : 0 < M := hcfg.hM_pos
  have hP_nonempty : config.P₀.Nonempty := by
    have h_unif : IsUniformAtScales config.pointSet 1 Δ N := hcfg.h_uniform
    have h_pointSet_nonempty : config.pointSet.Nonempty := h_unif.1
    rcases h_pointSet_nonempty with ⟨x, hx⟩
    have h2 : ∃ (p : DyadicSquare k), p ∈ config.P₀ ∧ x ∈ p.toSet := by
      simpa [NiceConfiguration.pointSet, Set.mem_iUnion] using hx
    rcases h2 with ⟨p, hp, _⟩
    exact ⟨p, hp⟩
  let C₁ : ℝ := Real.rpow (dyadicDelta k) (-lam)
  have hC₁_pos : 0 < C₁ := Real.rpow_pos_of_pos (dyadicDelta_pos k) (-lam)
  have h_st : 0 ≤ s ∧ s ≤ s ∧ s ≤ 1 := by
    exact ⟨by linarith, by linarith, by linarith⟩
  have hs_nonneg : 0 ≤ s := by linarith
  rcases prop5_wrapper (s := s) (t := s) (C₁ := C₁) (C_P := C_P) config
      hk_ge_2 hM_pos hP_nonempty h_st hCP hC₁_pos hs_nonneg hP_set h_slope
    with ⟨K, hK_pos, h_prop5⟩
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
    have h6 : ((2 : ℝ)^k)⁻¹ ≤ 1 / 4 := by
      have h7 : (4 : ℝ) ≤ (2 : ℝ)^k := h3
      have h8 : ((2 : ℝ)^k)⁻¹ ≤ (4 : ℝ)⁻¹ := by gcongr
      norm_num at h8 ⊢ <;> exact h8
    exact h6
  have h_exp_zero : ((M : ℝ) * Real.rpow δ s) ^ ((s - s) / (1 - s)) = 1 := by
    have h1 : (s - s) / (1 - s) = 0 := by
      have h2 : s - s = 0 := by ring
      rw [h2] <;> ring
    rw [h1] <;> simp
  have h_bound_simp : (config.T₀.card : ℝ) ≥
      (1 / K) * Real.rpow (Real.log (1 / δ)) (-K) *
        (1 / (C_P * (13 * C₁ * Real.rpow 2 s))) * (M : ℝ) * Real.rpow δ (-s) := by
    simpa [h_exp_zero] using h_prop5
  rcases absorb_normal_cprime_one hδ_pos hδ_le_quarter hK_pos hCP hC₁_pos
      (by exact_mod_cast hM_pos) hlam hεN hs hs1 rfl h_bound_simp
    with ⟨C, hC_pos, h_main⟩
  let C' : ℝ := 1
  have hC'_pos : 0 < C' := by norm_num
  have hG_empty : (Finset.univ.filter (fun j : Fin 1 => (scaleClass j).isGood)) =
      (∅ : Finset (Fin 1)) := by
    ext j; fin_cases j <;> simp [h_normal, ScaleClass.isGood]
  have hB_empty : (Finset.univ.filter (fun j : Fin 1 => (scaleClass j).isBad)) =
      (∅ : Finset (Fin 1)) := by
    ext j; fin_cases j <;> simp [h_normal, ScaleClass.isBad]
  have h_goal : (config.T₀.card : ENNReal) ≥
      ENNReal.ofReal (combiningLowerBound δ (M : ℝ) C C' lam s ε_N η 1 Δ scaleClass) := by
    dsimp only [combiningLowerBound]
    rw [hG_empty, hB_empty]
    have h9 : Real.rpow δ (1 * lam) * Real.rpow δ (-s + ε_N) =
        Real.rpow δ (1 * lam + (-s + ε_N)) :=
      (Real.rpow_add hδ_pos (1 * lam) (-s + ε_N)).symm
    simpa [C', h9] using ENNReal.ofReal_le_ofReal h_main
  exact ⟨C, C', hC_pos, hC'_pos, h_goal⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
