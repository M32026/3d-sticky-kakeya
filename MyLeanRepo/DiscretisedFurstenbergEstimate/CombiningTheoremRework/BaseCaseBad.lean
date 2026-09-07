module

/-
  Combining Theorem Base Case (n=1) - Bad Scale

  Trivial bound |T| ≥ M dominates combiningLowerBound.
  Delegates to combining_base_bad from CombiningTheorem.

  Whiteprint node: combining_theorem_rework / base_case_bad
  Dependencies: CombiningTheorem (combining_base_bad, combiningLowerBound)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.BaseCaseCommon
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem

/-- Base case: single Bad scale block.

    Uses trivial bound |T| ≥ M. For C=1, C'=1, the combiningLowerBound
    simplifies to L^{-1} · M · δ^{λ-s+ε_N+1} ≤ M since δ < 1 and
    λ - s + ε_N + 1 > 0.
-/
lemma base_case_bad
    {s t τ ε_G η ε_N C_P lam : ℝ} {k M : ℕ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {Δ : Fin 2 → ℝ} {scaleClass : Fin 1 → ScaleClass} {N : Fin 1 → ℕ}
    {C_between : Fin 1 → ℝ}
    (hs1 : s < 1) (hlam : 0 < lam) (hεN : 0 < ε_N)
    (hk_ge_2 : 2 ≤ k)
    (h_bad : scaleClass 0 = ScaleClass.bad)
    (hcfg : CombiningConfig s t τ 1 ε_G η lam ε_N C_P C_between k M config Δ scaleClass N) :
    ∃ (C C' : ℝ), 0 < C ∧ 0 < C' ∧
      (config.T₀.card : ENNReal) ≥
        ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) C C'
          lam s ε_N η 1 Δ scaleClass) := by
  have hδ_small : dyadicDelta k ≤ 1 / 4 := by
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
    exact h6
  have hδ_pos : 0 < dyadicDelta k := dyadicDelta_pos k
  let C : ℝ := 1
  let C' : ℝ := 1
  have hC_pos : 0 < C := by norm_num
  have hC'_pos : 0 < C' := by norm_num
  have h_all_bad : ∀ (j : Fin 1), scaleClass j = ScaleClass.bad := by
    intro j; fin_cases j; exact h_bad
  have hδ_le_exp : dyadicDelta k ≤ Real.exp (-1) := by
    have h1 : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
      have h3 : Real.exp (-1) = (Real.exp 1)⁻¹ := by
        rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, Real.exp_neg]
      rw [h3]
      have h5 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      have h6 : Real.exp 1 ≤ (4 : ℝ) := by
        have h61 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
        linarith
      have h7 : (1 / (Real.exp 1) : ℝ) ≥ 1 / (4 : ℝ) := one_div_le_one_div_of_le h5 h6
      simpa [one_div] using h7
    exact le_trans hδ_small h1
  have h_main : (config.T₀.card : ENNReal) ≥
      ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) 1 1 lam s ε_N η 1 Δ scaleClass) :=
    combining_base_bad s t τ 1 ε_G η ε_N C_P lam hs1 hlam hεN k M config Δ
      scaleClass N C_between hcfg h_all_bad hδ_le_exp
  exact ⟨1, 1, by norm_num, by norm_num, h_main⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
