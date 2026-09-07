module

/-
  Body Arithmetic — Extracted arithmetic lemmas for InductiveStepCore_v2_Body.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.InductiveStepCore_v2_Helpers
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure

open DiscretisedFurstenbergEstimate.CombiningTheorem

/-- Construct lam_fine and prove δbar^{-lam_fine} = K · δ^{-λ}. -/
lemma lam_fine_spec (K δ δbar lam : ℝ)
    (hK_ge1 : 1 ≤ K) (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hδbar_pos : 0 < δbar) (hδbar_lt_one : δbar < 1)
    (hlam : 0 < lam) :
    ∃ (lam_fine : ℝ), 0 < lam_fine ∧
      Real.rpow δbar (-lam_fine) = K * Real.rpow δ (-lam) := by
  let lam_fine : ℝ := (Real.log K + lam * Real.log (1 / δ)) / Real.log (1 / δbar)
  have hK_pos : 0 < K := by linarith
  have hL_pos : 0 < Real.log (1 / δ) := by
    apply Real.log_pos; exact one_lt_one_div hδ_pos hδ_lt_one
  have hLb_pos : 0 < Real.log (1 / δbar) := by
    apply Real.log_pos; exact one_lt_one_div hδbar_pos hδbar_lt_one
  have hlam_fine_pos : 0 < lam_fine := by
    dsimp only [lam_fine]
    have h1 : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
    have h2 : 0 < lam * Real.log (1 / δ) := mul_pos hlam hL_pos
    have h3 : 0 < Real.log K + lam * Real.log (1 / δ) := by linarith
    exact div_pos h3 hLb_pos
  have h_log1 : Real.log (1 / δbar) = -Real.log δbar := by
    rw [Real.log_div (by norm_num) hδbar_pos.ne'] <;> simp
  have h_logδbar_ne_zero : Real.log δbar ≠ 0 := by
    have h : δbar ≠ 1 := by linarith
    intro h2; have h3 : δbar = 1 := by rw [← Real.exp_log hδbar_pos, h2] <;> norm_num
    exact h h3
  have h_eq : -lam_fine * Real.log δbar = Real.log K + lam * Real.log (1 / δ) := by
    dsimp only [lam_fine]; rw [h_log1]; field_simp [h_logδbar_ne_zero] <;> ring
  have h_rpowδbar : Real.rpow δbar (-lam_fine) = Real.exp (-lam_fine * Real.log δbar) := by
    have h_def : ∀ (y : ℝ), Real.rpow δbar y = Real.exp (Real.log δbar * y) :=
      fun y => Real.rpow_def_of_pos hδbar_pos y
    have h' := h_def (-lam_fine)
    have h_comm : Real.log δbar * (-lam_fine) = -lam_fine * Real.log δbar := by ring
    rw [h_comm] at h'; exact h'
  have h_log1δ : Real.log (1 / δ) = -Real.log δ := by
    rw [Real.log_div (by norm_num) hδ_pos.ne'] <;> simp
  have h_pos1δ : 0 < 1 / δ := by positivity
  have h_rpow_inv : Real.rpow (1 / δ) lam = Real.rpow δ (-lam) := by
    have h1 : Real.rpow (1 / δ) lam = Real.exp (Real.log (1 / δ) * lam) :=
      Real.rpow_def_of_pos h_pos1δ lam
    have h2 : Real.rpow δ (-lam) = Real.exp (Real.log δ * (-lam)) :=
      Real.rpow_def_of_pos hδ_pos (-lam)
    rw [h1, h2, h_log1δ] <;> ring_nf
  have h_exp_product : Real.exp (Real.log K + lam * Real.log (1 / δ)) = K * Real.rpow δ (-lam) := by
    have h_exp_add : Real.exp (Real.log K + lam * Real.log (1 / δ)) =
        Real.exp (Real.log K) * Real.exp (lam * Real.log (1 / δ)) := by rw [Real.exp_add]
    rw [h_exp_add]
    have h_expK : Real.exp (Real.log K) = K := by rw [Real.exp_log] <;> linarith
    rw [h_expK]
    have h_exp_rpow : Real.exp (lam * Real.log (1 / δ)) = Real.rpow (1 / δ) lam := by
      have h_comm : lam * Real.log (1 / δ) = Real.log (1 / δ) * lam := by ring
      rw [h_comm]; exact (Real.rpow_def_of_pos h_pos1δ lam).symm
    rw [h_exp_rpow, h_rpow_inv] <;> ring
  have h_main : Real.rpow δbar (-lam_fine) = K * Real.rpow δ (-lam) := by
    rw [h_rpowδbar, h_eq, h_exp_product]
  exact ⟨lam_fine, hlam_fine_pos, h_main⟩

/-- K ≤ A * log(1/δ)^α polynomial bound. -/
lemma k_poly_bound_spec (k : ℕ) (K A α : ℝ)
    (hA_eq : A = 2700 * 3145728 * (8 / Real.log 2)^7)
    (hK_bound : K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7)
    (hk_exp1 : dyadicDelta k ≤ Real.exp (-1))
    (hα7 : α = (7 : ℝ)) :
    K ≤ A * (Real.log (1 / dyadicDelta k)) ^ α := by
  have h_exp_neg_lt_half : Real.exp (-1) < 1 / 2 := by
    have h1 : (2 : ℝ) < Real.exp 1 := by
      have h2 : 1 + (1 : ℝ) < Real.exp 1 := by
        apply Real.add_one_lt_exp
        norm_num
      norm_num at h2 ⊢; exact h2
    have h3 : Real.exp (-1) = (Real.exp 1)⁻¹ := by
      rw [Real.exp_neg]
    rw [h3]
    have h4 : (Real.exp 1)⁻¹ < (1 / 2 : ℝ) := by
      have h5 : (2 : ℝ) < Real.exp 1 := h1
      have h6 : (Real.exp 1)⁻¹ < (2 : ℝ)⁻¹ := by
        gcongr
      have h7 : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
      rw [h7] at h6; exact h6
    exact h4
  have h_k_ge2 : 2 ≤ k := by
    by_contra h
    have h' : k < 2 := by omega
    interval_cases k
    · norm_num [dyadicDelta] at hk_exp1
    · norm_num [dyadicDelta] at hk_exp1; linarith [h_exp_neg_lt_half]
  have h_main : (4 * (k : ℝ) + 7)^7 ≤ (8 * (k : ℝ))^7 :=
    poly_bound_helper k h_k_ge2
  have h_RHS : A * (Real.log (1 / dyadicDelta k)) ^ α = 2700 * 3145728 * (8 * (k : ℝ))^7 := by
    rw [hA_eq]
    have h_logδ : Real.log (1 / dyadicDelta k) = (k : ℝ) * Real.log 2 := by
      have h1 : 1 / dyadicDelta k = (2 : ℝ)^k := by
        dsimp only [dyadicDelta]; field_simp <;> ring
      rw [h1]
      rw [Real.log_pow] <;> norm_num
    rw [h_logδ]; exact log_poly_simplification_mixed k h_k_ge2 hα7
  rw [h_RHS]
  have h_mul : 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 ≤ 2700 * 3145728 * (8 * (k : ℝ))^7 := by
    apply mul_le_mul_of_nonneg_left h_main; positivity
  calc K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 := hK_bound
    _ ≤ 2700 * 3145728 * (8 * (k : ℝ))^7 := h_mul

/-- dyadicDelta k / dyadicDelta m = dyadicDelta (k - m) when m ≤ k. -/
lemma dyadicDelta_div (k m : ℕ) (hmk : m ≤ k) :
    dyadicDelta k / dyadicDelta m = dyadicDelta (k - m) := by
  have h4 : m + (k - m) = k := by omega
  have h6 : ∀ (a b : ℕ), dyadicDelta a * dyadicDelta b = dyadicDelta (a + b) := by
    intro a b; simp only [dyadicDelta]; field_simp; rw [← pow_add] <;> ring
  have h5 : dyadicDelta m * dyadicDelta (k - m) = dyadicDelta k := by
    have h7 := h6 m (k - m); rw [h4] at h7; exact h7
  have h8 : dyadicDelta k = dyadicDelta m * dyadicDelta (k - m) := h5.symm
  rw [h8]; have h9 : 0 < dyadicDelta m := dyadicDelta_pos m
  field_simp [h9.ne'] <;> ring

/-- log(1/dyadicDelta k) ≥ 1 bound. -/
lemma log_one_over_dyadic_ge_one_bound (k : ℕ)
    (hk_exp1 : dyadicDelta k ≤ Real.exp (-1)) :
    1 ≤ Real.log (1 / dyadicDelta k) := by
  have h3 : 0 < dyadicDelta k := dyadicDelta_pos k
  have h1 : dyadicDelta k ≤ Real.exp (-1) := hk_exp1
  have h2 : 0 < Real.exp 1 := Real.exp_pos 1
  have h3' : dyadicDelta k ≤ (Real.exp 1)⁻¹ := by
    have h4 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    rw [h4] at h1; exact h1
  have h4 : 1 / dyadicDelta k ≥ 1 / (Real.exp 1)⁻¹ :=
    one_div_le_one_div_of_le h3 h3'
  have h5 : 1 / (Real.exp 1)⁻¹ = Real.exp 1 := by simpa [one_div] using inv_inv h2
  have h6 : 1 / dyadicDelta k ≥ Real.exp 1 := by rw [h5] at h4; exact h4
  have h7 : Real.log (1 / dyadicDelta k) ≥ Real.log (Real.exp 1) :=
    Real.log_le_log (by positivity) h6
  have h8 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
  rw [h8] at h7; exact h7

/-- Proof that 1 ≤ dyadicDelta k^{-lam}. -/
lemma c1_ge1_spec (k : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    1 ≤ Real.rpow (dyadicDelta k) (-lam) := by
  have hδ_pos : 0 < dyadicDelta k := dyadicDelta_pos k
  have h9 : Real.rpow (dyadicDelta k) (-lam) = (Real.rpow (dyadicDelta k) lam)⁻¹ :=
    Real.rpow_neg (by positivity) lam
  rw [h9]
  have h10 : Real.rpow (dyadicDelta k) lam ≤ 1 := by
    apply Real.rpow_le_one
    · exact le_of_lt (dyadicDelta_pos k)
    · exact dyadicDelta_le_one k
    · linarith
  have h11 : 0 < Real.rpow (dyadicDelta k) lam := Real.rpow_pos_of_pos hδ_pos lam
  have h12 : (Real.rpow (dyadicDelta k) lam)⁻¹ ≥ 1 := by
    calc (Real.rpow (dyadicDelta k) lam)⁻¹
      ≥ (1 : ℝ)⁻¹ := by gcongr
    _ = 1 := by norm_num
  exact h12

/-- Proof that Δ 1 < 1 given CombiningConfig. -/
lemma delta_coarse_lt_one {n_fine k M : ℕ}
    {s t τ ε_G η ε_N C_P lam : ℝ}
    {C_between : Fin (n_fine + 1) → ℝ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {Δ : Fin (n_fine + 2) → ℝ}
    {scaleClass : Fin (n_fine + 1) → ScaleClass}
    {N : Fin (n_fine + 1) → ℕ}
    (hcfg : CombiningConfig s t τ (n_fine + 1) ε_G η lam ε_N C_P C_between k M config Δ scaleClass N) :
    Δ 1 < 1 := by
  have h0 : Δ 0 = 1 := hcfg.hΔ_start
  have h_j0 : 0 < n_fine + 1 := by omega
  let i0 : Fin (n_fine + 1) := ⟨0, h_j0⟩
  have h5 : Δ 1 < Δ 0 := by
    convert hcfg.hΔ_strict i0 using 2
    · apply Fin.ext; simp [i0] <;> omega
    · apply Fin.ext; simp [i0] <;> omega
  rw [h0] at h5; exact h5

/-- Proof that δbar = dyadicDelta (k - m). -/
lemma deltabar_eq_spec {n_fine k M : ℕ}
    {s t τ ε_G η ε_N C_P lam : ℝ}
    {C_between : Fin (n_fine + 1) → ℝ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {Δ : Fin (n_fine + 2) → ℝ}
    {scaleClass : Fin (n_fine + 1) → ScaleClass}
    {N : Fin (n_fine + 1) → ℕ}
    (hcfg : CombiningConfig s t τ (n_fine + 1) ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (m : ℕ) (hmk : m ≤ k)
    (hm_eq2 : Δ 1 = dyadicDelta m)
    (Δ_coarse δbar : ℝ)
    (hΔ_coarse_def : Δ_coarse = Δ 1)
    (hδbar_def : δbar = (dyadicDelta k) / Δ_coarse) :
    δbar = dyadicDelta (k - m) := by
  have hΔcoarse_eq : Δ_coarse = dyadicDelta m := by
    rw [hΔ_coarse_def, hm_eq2]
  have h1 : δbar = dyadicDelta k / dyadicDelta m := by
    rw [hδbar_def, hΔcoarse_eq]
  rw [h1]
  have h4 : m + (k - m) = k := by omega
  have h6 : ∀ (a b : ℕ), dyadicDelta a * dyadicDelta b = dyadicDelta (a + b) := by
    intro a b; simp only [dyadicDelta]; field_simp; rw [← pow_add] <;> ring
  have h5 : dyadicDelta m * dyadicDelta (k - m) = dyadicDelta k := by
    have h7 := h6 m (k - m); rw [h4] at h7; exact h7
  have h7 : dyadicDelta k / dyadicDelta m = dyadicDelta (k - m) := by
    have h8 : dyadicDelta k = dyadicDelta m * dyadicDelta (k - m) := h5.symm
    rw [h8]; have h9 : 0 < dyadicDelta m := dyadicDelta_pos m
    field_simp [h9.ne'] <;> ring
  exact h7

/-- Proof that Δ (Fin.last (n_fine + 1)) < Δ 1. -/
lemma delta_last_lt_delta_one {n_fine k M : ℕ}
    {s t τ ε_G η ε_N C_P lam : ℝ}
    {C_between : Fin (n_fine + 1) → ℝ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {Δ : Fin (n_fine + 2) → ℝ}
    {scaleClass : Fin (n_fine + 1) → ScaleClass}
    {N : Fin (n_fine + 1) → ℕ}
    (hcfg : CombiningConfig s t τ (n_fine + 1) ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (h2 : 2 ≤ n_fine + 1) :
    Δ (Fin.last (n_fine + 1)) < Δ 1 := by
  have h1 : 1 < n_fine + 1 := by omega
  have h_strict_decrease : ∀ (i j : ℕ) (hij : i < j) (hjn : j ≤ n_fine + 1),
      Δ ⟨j, Nat.lt_succ_of_le hjn⟩ < Δ ⟨i, Nat.lt_trans hij (Nat.lt_succ_of_le hjn)⟩ := by
    intro i j hij hjn
    induction' hij with j hij ih
    · have h_i_lt_n : i < n_fine + 1 := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hjn
      have h := hcfg.hΔ_strict (⟨i, h_i_lt_n⟩ : Fin (n_fine + 1))
      simpa [Fin.ext_iff] using h
    · have h_j_le_n : j ≤ n_fine + 1 := by omega
      have h_j_lt_n : j < n_fine + 1 := by omega
      have h_step := hcfg.hΔ_strict (⟨j, h_j_lt_n⟩ : Fin (n_fine + 1))
      have h_ih : Δ ⟨j, Nat.lt_succ_of_le h_j_le_n⟩ <
          Δ ⟨i, Nat.lt_trans hij (Nat.lt_succ_of_le h_j_le_n)⟩ := ih h_j_le_n
      have h_new : Δ ⟨j + 1, by omega⟩ < Δ ⟨j, by omega⟩ := by
        simpa [Fin.ext_iff] using h_step
      exact lt_trans h_new h_ih
  have h := h_strict_decrease 1 (n_fine + 1) h1 (by omega)
  have h_last : (Fin.last (n_fine + 1) : Fin (n_fine + 2)) = ⟨n_fine + 1, by omega⟩ := by
    apply Fin.ext; simp [Fin.last]
  have h_one : (1 : Fin (n_fine + 2)) = ⟨1, by omega⟩ := by
    apply Fin.ext; simp
  rw [h_last, h_one]; exact h

end DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure
