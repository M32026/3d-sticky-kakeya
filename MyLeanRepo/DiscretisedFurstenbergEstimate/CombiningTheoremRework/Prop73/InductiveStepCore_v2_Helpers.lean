module

/-
  Inductive Step Core v2 Helpers — Shared helper lemmas.

  This module contains arithmetic and utility lemmas shared between
  InductiveStepCore_v2 and its body extraction.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.TailSplit
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure

open DiscretisedFurstenbergEstimate.CombiningTheorem


/-- Helper: dyadicDelta is strictly anti-monotone. -/
lemma dyadicDelta_strict_anti {a b : ℕ} (h : dyadicDelta a > dyadicDelta b) : a < b := by
  dsimp only [dyadicDelta] at h
  have h6 : (2 : ℝ)^a < (2 : ℝ)^b :=
    lt_of_one_div_lt_one_div (by positivity) h
  by_contra h10
  have h11 : b ≤ a := by omega
  have h12 : (2 : ℝ)^b ≤ (2 : ℝ)^a := pow_le_pow_right₀ (by norm_num) h11
  linarith

/-- Helper: (a/c) / (b/c) = a/b for positive b, c. -/
lemma div_div_cancel {a b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    (a / c) / (b / c) = a / b := by
  have hc' : c ≠ 0 := hc.ne'
  have hb' : b ≠ 0 := hb.ne'
  field_simp [hc', hb'] <;> ring

/-- Helper: C' final inequality. -/
lemma C_prime_final_ge_helper (C' C'_fine lam lam_tail τ : ℝ)
    (hC'_ge : C' ≥ 1 + 2 * C'_fine / τ) (hτ : 0 < τ) (hlam : 0 < lam)
    (hτ_lam_tail : τ * lam_tail = 2 * lam) :
    C' * lam ≥ 1 * lam + C'_fine * lam_tail := by
  have h6 : τ ≠ 0 := hτ.ne'
  have h7 : lam_tail = 2 * lam / τ := by
    have h9 : lam_tail * τ = 2 * lam := by
      rw [mul_comm] at hτ_lam_tail
      exact hτ_lam_tail
    have h10 : lam_tail = (2 * lam) / τ := by
      rw [←h9, mul_div_cancel_right₀ _ h6]
    exact h10
  have h5 : C'_fine * lam_tail = 2 * C'_fine * lam / τ := by
    rw [h7] <;> ring
  have h7' : C' * lam ≥ (1 + 2 * C'_fine / τ) * lam :=
    mul_le_mul_of_nonneg_right hC'_ge hlam.le
  have h8 : (1 + 2 * C'_fine / τ) * lam = 1 * lam + 2 * C'_fine * lam / τ := by ring
  rw [h8] at h7'
  rw [h5]
  exact h7'

/-- Helper: C_coarse is non-negative. -/
lemma C_coarse_nonneg_helper (m : ℕ) (K_p5 C_P : ℝ) (hK_p5_ge1 : 1 ≤ K_p5) (hCP : 1 ≤ C_P) :
    0 ≤ (if m = 1 then (0 : ℝ) else K_p5 + C_P + 8) := by
  by_cases h : m = 1
  · rw [if_pos h] <;> norm_num
  · rw [if_neg h] <;> linarith

/-- Helper: final C ≥ (1+α)*(C'_coarse+1) + C_coarse + C_fine bound. -/
lemma C_ge_final_helper (C C'_fine C_fine K_p5 C_P : ℝ) (m : ℕ)
    (hC_ge : C ≥ (1 + (7 : ℝ)) * (1 + (1 : ℝ) + C'_fine) + K_p5 + C_P + 8 + C_fine)
    (hC'_fine_pos : 0 < C'_fine) (hK_p5_ge1 : 1 ≤ K_p5) (hCP : 1 ≤ C_P) :
    C ≥ (1 + (7 : ℝ)) * (1 + (1 : ℝ)) + (if m = 1 then (0 : ℝ) else K_p5 + C_P + 8) + C_fine := by
  have h2 : (1 + (7 : ℝ)) * (1 + (1 : ℝ)) + (if m = 1 then (0 : ℝ) else K_p5 + C_P + 8) + C_fine ≤
      (1 + (7 : ℝ)) * (1 + (1 : ℝ) + C'_fine) + K_p5 + C_P + 8 + C_fine := by
    by_cases hm : m = 1
    · rw [if_pos hm]
      have h1 : 0 ≤ C'_fine := by linarith
      have h2 : 0 ≤ K_p5 := by linarith
      have h3 : 0 ≤ C_P := by linarith
      linarith
    · rw [if_neg hm]
      have h1 : 0 ≤ C'_fine := by linarith
      linarith
  exact le_trans h2 hC_ge

/-- Helper: C'_coarse ≤ C' from C' ≥ 1 + 2*C'_fine/τ. -/
lemma C_prime_coarse_le_C_prime (C' C'_fine τ : ℝ)
    (hC'_ge : C' ≥ 1 + 2 * C'_fine / τ) (hτ : 0 < τ) (hC'_fine_pos : 0 < C'_fine) :
    (1 : ℝ) ≤ C' := by
  have h_pos : 0 < 2 * C'_fine / τ := by positivity
  linarith

/-- Helper: log(1/dyadicDelta k) ≥ A from dyadicDelta k ≤ exp(-A). -/
lemma log_one_over_dyadic_ge_A (k : ℕ) (A : ℝ) (hk : dyadicDelta k ≤ Real.exp (-A)) :
    Real.log (1 / dyadicDelta k) ≥ A := by
  have h2 : 0 < dyadicDelta k := dyadicDelta_pos k
  have h3 : 1 / dyadicDelta k ≥ Real.exp A := by
    have h_pos : 0 < Real.exp A := Real.exp_pos A
    have h_neg : Real.exp (-A) = (Real.exp A)⁻¹ := by
      rw [← Real.exp_neg] <;> ring
    have h : 1 / dyadicDelta k ≥ 1 / Real.exp (-A) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact hk
    rw [h_neg] at h
    simpa [one_div] using h
  have h4 : Real.log (1 / dyadicDelta k) ≥ Real.log (Real.exp A) :=
    Real.log_le_log (by positivity) h3
  have h5 : Real.log (Real.exp A) = A := Real.log_exp A
  rw [h5] at h4
  exact h4

/-- Helper: positivity of Δ' = Δ(idx i)/Δ1. -/
lemma delta_prime_pos {n n_fine : ℕ} (Δ : Fin (n + 1) → ℝ)
    (hΔ_pos : ∀ i : Fin (n + 1), 0 < Δ i)
    (Δ' : Fin (n_fine + 1) → ℝ)
    (idx : Fin (n_fine + 1) → Fin (n + 1))
    (hΔ'_def : ∀ i, Δ' i = Δ (idx i) / Δ 1) :
    ∀ i : Fin (n_fine + 1), 0 < Δ' i := by
  intro i
  rw [hΔ'_def i]
  exact div_pos (hΔ_pos (idx i)) (hΔ_pos 1)

/-- Helper: telescoping product over Fin n equals f n / f 0. -/
lemma telescoping_prod_delta {n_fine : ℕ} (Δ' : Fin (n_fine + 1) → ℝ)
    (hΔ'_pos : ∀ i : Fin (n_fine + 1), 0 < Δ' i) :
    (∏ j : Fin n_fine, Δ' (Fin.succ j) / Δ' j.castSucc) = Δ' (Fin.last n_fine) / Δ' 0 := by
  let f : ℕ → ℝ := fun v => if h : v ≤ n_fine then Δ' ⟨v, by omega⟩ else 1
  have hf_pos : ∀ k ≤ n_fine, 0 < f k := by
    intro k hk
    simp only [f, dif_pos hk]
    exact hΔ'_pos _
  have h_eq1 : ∀ (j : Fin n_fine), Δ' (Fin.succ j) / Δ' j.castSucc = f (j.val + 1) / f j.val := by
    intro j
    simp [f, Fin.lt_iff_val_lt_val] <;> rfl
  have h : (∏ j : Fin n_fine, Δ' (Fin.succ j) / Δ' j.castSucc) = ∏ j : Fin n_fine, f (j.val + 1) / f j.val := by
    apply Finset.prod_congr rfl
    intro j _
    exact h_eq1 j
  rw [h]
  have h2 := prod_fin_telescoping f hf_pos
  rw [h2]
  have h3 : f n_fine / f 0 = Δ' (Fin.last n_fine) / Δ' 0 := by
    simp [f, Fin.last] <;> rfl
  exact h3

/-- Helper: polynomial log simplification (mixed natural/real powers). -/
lemma log_poly_simplification_mixed (k : ℕ) (hk : 2 ≤ k) {α : ℝ} (hα7 : α = (7 : ℝ)) :
    2700 * 3145728 * (8 / Real.log 2)^7 * ((k : ℝ) * Real.log 2)^α =
    2700 * 3145728 * (8 * (k : ℝ))^7 := by
  have h_cast2 : ((k : ℝ) * Real.log 2)^α = ((k : ℝ) * Real.log 2)^7 := by
    have h10 : ((k : ℝ) * Real.log 2)^α = ((k : ℝ) * Real.log 2)^(7 : ℝ) := by rw [hα7]
    have h11 : ((k : ℝ) * Real.log 2)^(7 : ℝ) = ((k : ℝ) * Real.log 2)^7 := Real.rpow_natCast _ 7
    exact Eq.trans h10 h11
  rw [h_cast2]
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (8 / Real.log 2) * ((k : ℝ) * Real.log 2) = 8 * (k : ℝ) := by
    field_simp [h_log2_pos.ne'] <;> ring
  have h2 : (8 / Real.log 2)^7 * ((k : ℝ) * Real.log 2)^7 = (8 * (k : ℝ))^7 := by
    rw [←mul_pow, h1]
  have h3 : 2700 * 3145728 * (8 / Real.log 2)^7 * ((k : ℝ) * Real.log 2)^7 =
      2700 * 3145728 * ((8 / Real.log 2)^7 * ((k : ℝ) * Real.log 2)^7) := by ring
  rw [h3, h2]

/-- Helper: polynomial bound. -/
lemma poly_bound_helper (k : ℕ) (hk : 2 ≤ k) :
    (4 * (k : ℝ) + 7)^7 ≤ (8 * (k : ℝ))^7 := by
  have h : (k : ℝ) ≥ 2 := by exact_mod_cast hk
  have h4k : 4 * (k : ℝ) + 7 ≤ 8 * (k : ℝ) := by
    have h2 : 4 * (k : ℝ) ≥ 8 := by
      have h3 : 4 * (2 : ℝ) ≤ 4 * (k : ℝ) := mul_le_mul_of_nonneg_left h (by norm_num)
      norm_num at h3; exact h3
    linarith
  have h_pos : 0 ≤ 4 * (k : ℝ) + 7 := by positivity
  gcongr




/-- Weaken the C constant of an IsDeltaSSet. -/
lemma isDeltaSSet_weaken_C {X : Type*} [PseudoMetricSpace X] {δ s C1 C2 : ℝ} {S : Set X}
    (h : IsDeltaSSet δ s C1 S) (hC : C1 ≤ C2) : IsDeltaSSet δ s C2 S := by
  rcases h with ⟨hne, hδ, hC1_pos, hs, hbound⟩
  have hC2_pos : 0 < C2 := by linarith
  refine ⟨hne, hδ, hC2_pos, hs, fun x r hr => ?_⟩
  have h4 := hbound x r hr
  have h5 : ENNReal.ofReal C1 ≤ ENNReal.ofReal C2 := ENNReal.ofReal_le_ofReal hC
  have h6 : ENNReal.ofReal C1 * (ENNReal.ofReal r) ^ s ≤
      ENNReal.ofReal C2 * (ENNReal.ofReal r) ^ s := by gcongr
  have h7 : (ENNReal.ofReal C1 * (ENNReal.ofReal r) ^ s) *
      Metric.externalCoveringNumber δ.toNNReal S ≤
      (ENNReal.ofReal C2 * (ENNReal.ofReal r) ^ s) *
      Metric.externalCoveringNumber δ.toNNReal S := by gcongr
  exact le_trans h4 h7

/-- Weaken the C constant of a NiceConfiguration. -/
def weaken_NiceConfiguration_C {n : ℕ} {s C C' : ℝ} {M : ℕ}
    (config : CTNiceConfiguration n s C M)
    (hC : C ≤ C') (hC'_pos : 0 < C') :
    CTNiceConfiguration n s C' M :=
  ⟨config.P₀, config.T₀, config.tubeFamily, config.h_subset, config.h_size,
    fun p hp => isDeltaSSet_weaken_C (config.h_delta_s_set p hp) hC,
    config.h_intersect, config.h_tube_parameters, config.h_bounded⟩

/-- Helper: if 0 < Δ ≤ 1/4, then 1 ≤ Real.log (1/Δ). -/
lemma log_one_over_ge_one {Δ : ℝ} (hΔ_pos : 0 < Δ) (hΔ_le_quarter : Δ ≤ 1 / 4) :
    1 ≤ Real.log (1 / Δ) := by
  have h3 : 4 ≤ 1 / Δ := by
    have h4 : 1 / Δ ≥ 1 / (1 / 4) := one_div_le_one_div_of_le hΔ_pos hΔ_le_quarter
    have h5 : 1 / (1 / 4 : ℝ) = 4 := by norm_num
    rw [h5] at h4; exact h4
  have h4 : Real.log 4 ≤ Real.log (1 / Δ) := Real.log_le_log (by norm_num) h3
  have h5 : (1 : ℝ) < Real.log 4 := by
    have h6 : Real.exp 1 < (4 : ℝ) := by linarith [Real.exp_one_lt_three]
    have h7 : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (by positivity) h6
    have h8 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    rw [h8] at h7; exact h7
  linarith

/-- Helper: if 2 ≤ m, then 1 ≤ Real.log (1 / dyadicDelta m). -/
lemma dyadicDelta_log_ge_one {m : ℕ} (hm : 2 ≤ m) :
    1 ≤ Real.log (1 / dyadicDelta m) := by
  have h1 : dyadicDelta m ≤ 1 / 4 := by
    dsimp only [dyadicDelta]
    have h2 : (2 : ℝ)^2 ≤ (2 : ℝ)^m := pow_le_pow_right₀ (by norm_num) hm
    have h3 : 0 < (2 : ℝ)^2 := by positivity
    have h4 : 1 / (2 : ℝ)^m ≤ 1 / (2 : ℝ)^2 := one_div_le_one_div_of_le h3 h2
    have h5 : 1 / (2 : ℝ)^2 = 1 / 4 := by norm_num
    rw [h5] at h4; exact h4
  exact log_one_over_ge_one (dyadicDelta_pos m) h1

end DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure
