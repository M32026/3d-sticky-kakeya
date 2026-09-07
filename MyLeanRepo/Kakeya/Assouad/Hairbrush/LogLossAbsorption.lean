import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic loss absorption lemma

Shows that for any positive exponents `angleExponent` and `bandLoss`,
the number of dyadic angle bands `K = ceil(log(1/δ^angleExponent) / log 2)`
satisfies `K + 2 ≤ δ^(-bandLoss)` for sufficiently small `δ`.

This is the key estimate that lets the dyadic pigeonhole retain a
`δ^bandLoss` fraction of the original cardinality.
-/

noncomputable section

open Real

namespace Kakeya.Assouad

/--
For any `angleExponent > 0` and `bandLoss > 0`, there exists `δ₀ > 0`
such that for all `0 < δ ≤ δ₀`, the number of dyadic bands
`K = ceil(log(1/δ^angleExponent) / log 2)` satisfies `K + 2 ≤ δ^(-bandLoss)`.

Proof: set `ε = bandLoss / 2`. Using `log x ≤ x^ε / ε`, we bound
`K + 2 ≤ C * x^ε + 3` where `x = 1/δ` and `C = angleExponent / (ε * log 2)`.
Choosing `x` large enough that `x^ε ≥ max(1, C+3)` gives
`C * x^ε + 3 ≤ (x^ε)^2 = x^bandLoss = δ^(-bandLoss)`.
-/
lemma hairbrush_log_poly_bound (angleExponent bandLoss : ℝ)
    (h_ae : 0 < angleExponent) (h_bl : 0 < bandLoss) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 1000 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        let K := Nat.ceil (Real.log (1 / δ ^ angleExponent) / Real.log 2)
        (K : ℝ) + 2 ≤ δ ^ (-bandLoss) := by
  set ε : ℝ := bandLoss / 2 with hε_def
  have hε_pos : 0 < ε := by linarith
  set C : ℝ := angleExponent / (ε * Real.log 2) with hC_def
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC_nonneg : 0 ≤ C := by positivity
  set M : ℝ := max 1 (C + 3) with hM_def
  have hM_ge1 : 1 ≤ M := by simp [hM_def]
  have hM_ge_C3 : C + 3 ≤ M := by simp [hM_def]
  set x₀ : ℝ := M ^ (1 / ε) with hx₀_def
  have hM_pos : 0 < M := by linarith
  have hx₀_pos : 0 < x₀ := Real.rpow_pos_of_pos hM_pos _
  set δ₀ : ℝ := min (1 / 1000) (1 / x₀) with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_le : δ₀ ≤ 1 / 1000 := by exact min_le_left _ _
  refine ⟨δ₀, hδ₀_pos, hδ₀_le, ?_⟩
  intro δ hδ_pos hδ_le
  set x : ℝ := 1 / δ with hx_def
  have hx_pos : 0 < x := by positivity
  have hδx : δ * x = 1 := by
    rw [hx_def]
    field_simp [hδ_pos.ne']
  have hδ_le_inv : δ ≤ 1 / x₀ := by
    have h : δ ≤ min (1 / 1000) (1 / x₀) := hδ_le
    exact h.trans (min_le_right _ _)
  have hx_ge_x₀ : x ≥ x₀ := by
    have h21 : δ ≤ 1 / x₀ := hδ_le_inv
    have h22 : 1 / δ ≥ 1 / (1 / x₀) := by gcongr
    have h23 : 1 / (1 / x₀) = x₀ := by
      field_simp [hx₀_pos.ne']
    rw [h23] at h22
    exact h22
  have h1 : x ^ ε ≥ M := by
    have h3 : x ^ ε ≥ x₀ ^ ε := Real.rpow_le_rpow (by linarith) hx_ge_x₀ (by linarith)
    have h4 : x₀ ^ ε = M := by
      rw [hx₀_def]
      have h5 : (M ^ (1 / ε)) ^ ε = M := by
        rw [← Real.rpow_mul (by linarith)]
        have h6 : (1 / ε) * ε = 1 := by
          field_simp [hε_pos.ne']
        rw [h6]
        simp
      exact h5
    rw [h4] at h3
    exact h3
  have h2 : Real.log (1 / δ ^ angleExponent) = angleExponent * Real.log x := by
    have h32 : δ = 1 / x := by
      have h : 1 / x = δ := by
        rw [hx_def]
        field_simp [hδ_pos.ne']
      exact h.symm
    have h31 : δ ^ angleExponent = (1 / x) ^ angleExponent := by
      rw [h32]
    have h33 : (1 / x) ^ angleExponent = 1 / x ^ angleExponent := by
      rw [Real.div_rpow (by norm_num) (by linarith)]
      <;> simp
    have h3 : 1 / δ ^ angleExponent = x ^ angleExponent := by
      rw [h31, h33]
      field_simp [hx_pos.ne']
    rw [h3]
    have h4 : Real.log (x ^ angleExponent) = angleExponent * Real.log x :=
      Real.log_rpow hx_pos angleExponent
    exact h4
  set K : ℕ := Nat.ceil (Real.log (1 / δ ^ angleExponent) / Real.log 2) with hK_def
  have hlog_nonneg : 0 ≤ Real.log (1 / δ ^ angleExponent) / Real.log 2 := by
    apply div_nonneg
    · apply Real.log_nonneg
      have h_pos : 0 < 1 / δ ^ angleExponent := by positivity
      have h_ge_one : 1 ≤ 1 / δ ^ angleExponent := by
        have hδ_le_one : δ ≤ 1 := by linarith [hδ_le]
        have h1 : δ ^ angleExponent ≤ 1 := by
          exact Real.rpow_le_one (by linarith) hδ_le_one (by linarith)
        have h2 : 0 < δ ^ angleExponent := by positivity
        rw [one_le_div h2] <;> exact h1
      exact h_ge_one
    · linarith [hlog2_pos]
  have hK_lt : (K : ℝ) < Real.log (1 / δ ^ angleExponent) / Real.log 2 + 1 :=
    Nat.ceil_lt_add_one hlog_nonneg
  have hK_le : (K : ℝ) ≤ Real.log (1 / δ ^ angleExponent) / Real.log 2 + 1 :=
    hK_lt.le
  have hlog_le : Real.log x ≤ x ^ ε / ε :=
    Real.log_le_rpow_div (by linarith) hε_pos
  have hC_eq : C = angleExponent / (ε * Real.log 2) := hC_def
  have h6 : angleExponent * Real.log x / Real.log 2 ≤ C * x ^ ε := by
    have h7 : angleExponent * Real.log x / Real.log 2 =
        (angleExponent / (ε * Real.log 2)) * (ε * Real.log x) := by
      field_simp [hε_pos.ne', hlog2_pos.ne']
    rw [h7, hC_eq]
    have h8 : ε * Real.log x ≤ ε * (x ^ ε / ε) := by gcongr
    have h9 : ε * (x ^ ε / ε) = x ^ ε := by
      field_simp [hε_pos.ne']
    rw [h9] at h8
    exact mul_le_mul_of_nonneg_left h8 hC_nonneg
  have h5 : Real.log (1 / δ ^ angleExponent) / Real.log 2 + 3 ≤ C * x ^ ε + 3 := by
    rw [h2]
    linarith
  have h7 : (K : ℝ) + 2 ≤ C * x ^ ε + 3 := by linarith
  set y : ℝ := x ^ ε with hy_def
  have hy_ge_M : y ≥ M := h1
  have hy_ge1 : 1 ≤ y := by linarith [hM_ge1]
  have hy_ge_C3 : C + 3 ≤ y := by linarith [hM_ge_C3]
  have h8 : C * y + 3 ≤ y ^ 2 := by nlinarith
  have h9 : (x ^ ε) ^ 2 = x ^ bandLoss := by
    have h91 : (x ^ ε) ^ 2 = (x ^ ε) * (x ^ ε) := by ring
    rw [h91]
    have h92 : (x ^ ε) * (x ^ ε) = x ^ (ε + ε) := by
      rw [← Real.rpow_add (by linarith)]
    rw [h92]
    have h93 : ε + ε = bandLoss := by simp [hε_def]
    rw [h93]
  have h11 : x ^ bandLoss = δ ^ (-bandLoss) := by
    have h12 : x = 1 / δ := by simp [hx_def]
    rw [h12]
    have h13 : (1 / δ) ^ bandLoss = 1 / δ ^ bandLoss := by
      rw [Real.div_rpow (by norm_num) (by positivity)]
      simp
    have h14 : δ ^ (-bandLoss) = 1 / δ ^ bandLoss := by
      rw [Real.rpow_neg (by linarith)]
      simp
    rw [h13, h14]
  have h15 : C * x ^ ε + 3 ≤ δ ^ (-bandLoss) := by
    calc C * x ^ ε + 3
      ≤ (x ^ ε) ^ 2 := h8
    _ = x ^ bandLoss := h9
    _ = δ ^ (-bandLoss) := h11
  exact h7.trans h15

end Kakeya.Assouad
