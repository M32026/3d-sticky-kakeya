module

/-
# Log Absorption Threshold Lemma

Derives `extractLogAbsorbHyp` from the standard asymptotic fact that
any power of log grows slower than any positive power of the variable.

## Key lemma

`log_pow_const_le_rpow`: for `C > 0` and `α > 0`, there exists `δ0 > 0`
such that for all `0 < δ ≤ δ0`:
  `C * (log(1/δ))^2 ≤ δ^(-α)`

## Proof

Set `x = 1/δ`. Use `general_log_pow_le_rpow 2 (α/2)` to get
`(log x)^2 ≤ x^(α/2)` for `x ≥ x0`. Then choose `x1 ≥ max(x0, C^(2/α))`
so that `C ≤ x^(α/2)`. Then:
  `C * (log x)^2 ≤ C * x^(α/2) ≤ x^(α/2) * x^(α/2) = x^α = δ^(-α)`.

## Dependency

`Vendored.NumberTheory.Analytic.Sieve.LogPowerBounds`
for `general_log_pow_le_rpow`.
-/

public import MyLeanRepo.Vendored.NumberTheory.Analytic.Sieve.LogPowerBounds
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Vendored.NumberTheory.Analytic.Sieve

/-- For `C > 0` and `α > 0`, `C * (log(1/δ))^2 ≤ δ^(-α)` for sufficiently small `δ`. -/
lemma log_pow_const_le_rpow {C α : ℝ} (hC : 0 < C) (hα : 0 < α) :
    ∃ (δ0 : ℝ), 0 < δ0 ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ δ0 →
      C * (Real.log (1 / δ)) ^ 2 ≤ δ ^ (-α) := by
  have hα2_pos : 0 < α / 2 := by linarith
  have h2α_pos : 0 < 2 / α := by positivity
  rcases general_log_pow_le_rpow 2 (α / 2) (by norm_num) hα2_pos with ⟨x0, hx0_gt_one, h_bound⟩
  let x_C : ℝ := C ^ (2 / α)
  let x1 : ℝ := max x0 x_C
  let δ0 : ℝ := 1 / x1
  have hx0_pos : 0 < x0 := by linarith
  have hxC_nonneg : 0 ≤ x_C := by positivity
  have hx1_pos : 0 < x1 := by
    dsimp only [x1]
    exact lt_max_iff.mpr (Or.inl hx0_pos)
  have hδ0_pos : 0 < δ0 := by
    dsimp only [δ0]
    positivity
  have h_main : ∀ (δ : ℝ), 0 < δ → δ ≤ δ0 → C * (Real.log (1 / δ)) ^ 2 ≤ δ ^ (-α) := by
    intro δ hδ_pos hδ_le
    set x : ℝ := 1 / δ with hx_def
    have hx_pos : 0 < x := by positivity
    have hx_ge_x1 : x ≥ x1 := by
      have h9 : 0 < x1 := hx1_pos
      have h10 : δ ≤ 1 / x1 := hδ_le
      have h11 : 1 / δ ≥ 1 / (1 / x1) := by
        apply one_div_le_one_div_of_le
        · positivity
        · exact h10
      have h12 : 1 / (1 / x1) = x1 := by
        field_simp [h9.ne'] <;> ring
      rw [h12] at h11
      exact h11
    have hx_ge_x0 : x ≥ x0 := by
      have h : x1 ≥ x0 := le_max_left _ _
      linarith
    have h1_real : (Real.log x) ^ (2 : ℝ) ≤ x ^ (α / 2) := h_bound x hx_ge_x0
    have h1 : (Real.log x) ^ 2 ≤ x ^ (α / 2) := by
      have h_eq : (Real.log x) ^ 2 = (Real.log x) ^ (2 : ℝ) := by
        simp
      rw [h_eq]
      exact h1_real
    have hx_ge_xC : x ≥ x_C := by
      have h : x1 ≥ x_C := le_max_right _ _
      linarith
    have h2 : C ≤ x ^ (α / 2) := by
      have h3 : x_C ≤ x := hx_ge_xC
      have h4 : (x_C) ^ (α / 2) ≤ x ^ (α / 2) :=
        Real.rpow_le_rpow hxC_nonneg h3 (by linarith)
      have h5 : (x_C) ^ (α / 2) = C := by
        dsimp only [x_C]
        have h6 : (C ^ (2 / α)) ^ (α / 2) = C ^ ((2 / α) * (α / 2)) := by
          have h_rpow : C ^ ((2 / α) * (α / 2)) = (C ^ (2 / α)) ^ (α / 2) :=
            Real.rpow_mul (by linarith) (2 / α) (α / 2)
          exact h_rpow.symm
        rw [h6]
        have h7 : (2 / α) * (α / 2) = 1 := by field_simp [hα.ne'] <;> ring
        rw [h7]
        simp
      rw [h5] at h4
      exact h4
    have h6 : C * (Real.log x) ^ 2 ≤ x ^ α := by
      have h7 : C * (Real.log x) ^ 2 ≤ C * (x ^ (α / 2)) := by
        exact mul_le_mul_of_nonneg_left h1 (by linarith)
      have h8 : C * (x ^ (α / 2)) ≤ (x ^ (α / 2)) * (x ^ (α / 2)) := by
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
      have h9 : (x ^ (α / 2)) * (x ^ (α / 2)) = x ^ α := by
        have h10 : (x ^ (α / 2)) * (x ^ (α / 2)) = x ^ ((α / 2) + (α / 2)) := by
          rw [← Real.rpow_add hx_pos] <;> ring
        rw [h10]
        have h11 : (α / 2) + (α / 2) = α := by ring
        rw [h11]
      calc
        C * (Real.log x) ^ 2 ≤ C * (x ^ (α / 2)) := h7
        _ ≤ (x ^ (α / 2)) * (x ^ (α / 2)) := h8
        _ = x ^ α := h9
    have h7 : x ^ α = δ ^ (-α) := by
      dsimp only [x]
      have h8 : (1 / δ) ^ α = (1 : ℝ) ^ α / δ ^ α :=
        Real.div_rpow (by norm_num) hδ_pos.le α
      rw [h8]
      have h9 : (1 : ℝ) ^ α = 1 := by simp
      rw [h9]
      have h10 : (1 : ℝ) / δ ^ α = δ ^ (-α) := by
        have h11 : δ ^ (-α) = (δ ^ α)⁻¹ := by
          rw [Real.rpow_neg hδ_pos.le] <;> ring
        rw [h11]
        <;> field_simp [hδ_pos.ne'] <;> ring
      exact h10
    rw [h7] at h6
    exact h6
  exact ⟨δ0, hδ0_pos, h_main⟩

end
