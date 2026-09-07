module

/-
  Prop73 BaseBad — Bad scale branch lemma (n=1)

  For bad scales, C≥1, C'≥1 and the trivial bound |T| ≥ M suffices,
  since s<1 makes the bad product contribution small.

  Whiteprint node: combining_theorem_genuine / base_bad
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.BaseCaseBad
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem

/-- Bad scale branch: proves the lower bound for a single bad scale block
    with arbitrary C≥1, C'≥1.

    Uses `combining_base_bad` for the C=C'=1 case, then weakens via
    `combiningLowerBound_antitone`. Requires `hlog_ge_one` for the antitone lemma. -/
lemma base_case_bad_branch
    {s t τ ε_G η ε_N C_P lam C C' : ℝ} {k M : ℕ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {Δ : Fin 2 → ℝ} {scaleClass : Fin 1 → ScaleClass} {N : Fin 1 → ℕ}
    {C_between : Fin 1 → ℝ}
    (hs1 : s < 1) (hlam : 0 < lam) (hεN : 0 < ε_N)
    (hk_ge_2 : 2 ≤ k)
    (h_bad : scaleClass 0 = ScaleClass.bad)
    (hcfg : CombiningConfig s t τ 1 ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (hlog_ge_one : 1 ≤ Real.log (1 / dyadicDelta k))
    (hC_ge : 1 ≤ C) (hC'_ge : 1 ≤ C') :
    (config.T₀.card : ENNReal) ≥
      ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) C C'
        lam s ε_N η 1 Δ scaleClass) := by
  have hδ_pos : 0 < dyadicDelta k := dyadicDelta_pos k
  have hδ_lt_one : dyadicDelta k < 1 := by
    have h1 : (k : ℕ) ≥ 2 := hk_ge_2
    have h2 : dyadicDelta k = ((2 : ℝ)^k)⁻¹ := by
      simp [dyadicDelta, zpow_neg, zpow_ofNat] <;> ring
    rw [h2]
    have h3 : (2 : ℝ)^k > 1 := by
      have h4 : (2 : ℝ)^k ≥ (2 : ℝ)^(2 : ℕ) := by gcongr <;> norm_num
      norm_num at h4 ⊢ <;> linarith
    have h5 : 0 < (2 : ℝ)^k := by positivity
    have h6 : ((2 : ℝ)^k)⁻¹ < 1 := by
      have h7 : 1 < (2 : ℝ)^k := h3
      have h8 : 0 < (2 : ℝ)^k := by positivity
      calc ((2 : ℝ)^k)⁻¹
        = 1 / (2 : ℝ)^k := by simp
      _ < 1 := by
        apply (div_lt_one h8).mpr
        exact h7
    exact h6
  have hδ_small : dyadicDelta k ≤ Real.exp (-1) := by
    have h1 : (k : ℕ) ≥ 2 := hk_ge_2
    have h2 : dyadicDelta k = ((2 : ℝ)^k)⁻¹ := by
      simp [dyadicDelta, zpow_neg, zpow_ofNat] <;> ring
    rw [h2]
    have h3 : (2 : ℝ)^k ≥ 4 := by
      have h4 : (2 : ℝ)^k ≥ (2 : ℝ)^(2 : ℕ) := by gcongr <;> norm_num
      norm_num at h4 ⊢ <;> exact h4
    have h5 : 0 < (2 : ℝ)^k := by positivity
    have h6 : ((2 : ℝ)^k)⁻¹ ≤ 1 / 4 := by
      have h7 : (4 : ℝ) ≤ (2 : ℝ)^k := h3
      have h8 : ((2 : ℝ)^k)⁻¹ ≤ (4 : ℝ)⁻¹ := by gcongr
      norm_num at h8 ⊢ <;> exact h8
    have h9 : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
      have h10 : Real.exp (-1) = (Real.exp 1)⁻¹ := by
        rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, Real.exp_neg]
      rw [h10]
      have h11 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      have h12 : Real.exp 1 ≤ (4 : ℝ) := by
        have h13 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
        linarith
      have h14 : (1 / (Real.exp 1) : ℝ) ≥ 1 / (4 : ℝ) := one_div_le_one_div_of_le h11 h12
      simpa [one_div] using h14
    exact le_trans h6 h9
  have hΔ_pos : ∀ (i : Fin 2), 0 < Δ i := hcfg.hΔ_pos
  have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
  have h_all_bad : ∀ (j : Fin 1), scaleClass j = ScaleClass.bad := by
    intro j; fin_cases j; exact h_bad
  have h_main1 : (config.T₀.card : ENNReal) ≥
      ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) 1 1 lam s ε_N η 1 Δ scaleClass) :=
    combining_base_bad s t τ 1 ε_G η ε_N C_P lam hs1 hlam hεN k M config Δ
      scaleClass N C_between hcfg h_all_bad hδ_small
  have h_antitone : combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η 1 Δ scaleClass ≤
      combiningLowerBound (dyadicDelta k) (M : ℝ) 1 1 lam s ε_N η 1 Δ scaleClass :=
    combiningLowerBound_antitone hδ_pos hδ_lt_one hlam hM_nonneg hΔ_pos hlog_ge_one hC_ge hC'_ge
  calc (config.T₀.card : ENNReal)
    ≥ ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) 1 1 lam s ε_N η 1 Δ scaleClass) := h_main1
  _ ≥ ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η 1 Δ scaleClass) := by
    exact ENNReal.ofReal_le_ofReal h_antitone

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
