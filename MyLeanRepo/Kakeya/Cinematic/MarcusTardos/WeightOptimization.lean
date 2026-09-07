import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Weight optimization for Marcus-Tardos proof

This module proves bounds on the weights
`w_l = 1 / (1 + k / (Real.sqrt 2)^l)` for `l ∈ {1, ..., k}`.

These weights are used in the final assembly of Theorem 1.
-/

namespace MarcusTardos.WeightOptimization

open BigOperators Finset

/-- The weight at level l. -/
noncomputable def w (k l : ℕ) : ℝ :=
  1 / (1 + (k : ℝ) / (Real.sqrt 2)^l)

-- Helper facts about sqrt 2
private lemma sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
private lemma one_lt_sqrt2 : 1 < Real.sqrt 2 := by
  have h : (1 : ℝ)^2 < (2 : ℝ) := by norm_num
  have h' : (1 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  exact h'
private lemma sqrt2_sq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)

/-- Geometric series bound: ∑_{l=1}^k (1/√2)^l ≤ 3. -/
lemma geom_sum_bound (k : ℕ) :
    ∑ l ∈ Icc 1 k, (1 / Real.sqrt 2 : ℝ)^l ≤ 3 := by
  have h₁ : 0 ≤ (1 / Real.sqrt 2 : ℝ) := by positivity
  have h₂ : (1 / Real.sqrt 2 : ℝ) < 1 := by
    have h₃ : 0 < Real.sqrt 2 := sqrt2_pos
    have h₄ : 1 < Real.sqrt 2 := one_lt_sqrt2
    exact (div_lt_one h₃).mpr h₄
  have h₃ : Icc 1 k = Ico 1 (k + 1) := by
    ext x
    simp only [mem_Icc, mem_Ico]
    <;> omega
  rw [h₃]
  have h₄ : ∑ l ∈ Ico 1 (k + 1), (1 / Real.sqrt 2 : ℝ)^l ≤
      (1 / Real.sqrt 2 : ℝ)^1 / (1 - (1 / Real.sqrt 2 : ℝ)) :=
    geom_sum_Ico_le_of_lt_one h₁ h₂
  have h₅ : (1 / Real.sqrt 2 : ℝ)^1 / (1 - (1 / Real.sqrt 2 : ℝ)) = Real.sqrt 2 + 1 := by
    have h₆ : 0 < Real.sqrt 2 - 1 := by
      have h₇ : 1 < Real.sqrt 2 := one_lt_sqrt2
      linarith
    field_simp [sqrt2_pos.ne', h₆.ne']
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [h₅] at h₄
  have h₇ : Real.sqrt 2 + 1 ≤ 3 := by
    have h₈ : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr (by norm_num)
    linarith
  exact h₄.trans h₇

/-- Weights are positive. -/
lemma w_pos (k l : ℕ) : 0 < w k l := by
  dsimp only [w]
  have h₁ : 0 < (Real.sqrt 2)^l := by positivity
  have h₂ : 0 ≤ (k : ℝ) / (Real.sqrt 2)^l := by positivity
  have h₃ : 0 < 1 + (k : ℝ) / (Real.sqrt 2)^l := by linarith
  exact div_pos zero_lt_one h₃

/-- Reciprocal of weight. -/
lemma inv_w (k l : ℕ) : 1 / w k l = 1 + (k : ℝ) / (Real.sqrt 2)^l := by
  dsimp only [w]
  have h₁ : 0 < (Real.sqrt 2)^l := by positivity
  have h₂ : 0 ≤ (k : ℝ) / (Real.sqrt 2)^l := by positivity
  have h₃ : 0 < 1 + (k : ℝ) / (Real.sqrt 2)^l := by linarith
  field_simp [h₃.ne']

/-- Each weight is at most 1. -/
lemma w_le_one (k l : ℕ) : w k l ≤ 1 := by
  dsimp only [w]
  have h₁ : 0 < (Real.sqrt 2)^l := by positivity
  have h₂ : 0 ≤ (k : ℝ) / (Real.sqrt 2)^l := by positivity
  have h₃ : 0 < 1 + (k : ℝ) / (Real.sqrt 2)^l := by linarith
  have h₄ : 1 ≤ 1 + (k : ℝ) / (Real.sqrt 2)^l := by linarith
  exact (div_le_one h₃).mpr h₄

/-- Bound on sum of weights: ∑ w_l ≤ k. -/
lemma sum_w_bound (k : ℕ) : ∑ l ∈ Icc 1 k, w k l ≤ (k : ℝ) := by
  calc
    ∑ l ∈ Icc 1 k, w k l ≤ ∑ l ∈ Icc 1 k, (1 : ℝ) := by
      gcongr with l _
      exact w_le_one k l
    _ = ((Icc 1 k).card : ℝ) := by simp
    _ = (k : ℝ) := by
      simp [Nat.card_Icc]

/-- Bound on sum of reciprocals: ∑ 1/w_l ≤ 4*k. -/
lemma sum_inv_w_bound (k : ℕ) :
    ∑ l ∈ Icc 1 k, (1 / w k l) ≤ 4 * (k : ℝ) := by
  have h₁ : ∀ l ∈ Icc 1 k, 1 / w k l = 1 + (k : ℝ) / (Real.sqrt 2)^l := by
    intro l _
    exact inv_w k l
  rw [sum_congr rfl h₁]
  have h₂ : ∑ l ∈ Icc 1 k, (1 + (k : ℝ) / (Real.sqrt 2)^l) =
      (k : ℝ) + (k : ℝ) * ∑ l ∈ Icc 1 k, (1 / Real.sqrt 2 : ℝ)^l := by
    have h₂₁ : ∑ l ∈ Icc 1 k, (1 + (k : ℝ) / (Real.sqrt 2)^l) =
        ∑ l ∈ Icc 1 k, (1 : ℝ) + ∑ l ∈ Icc 1 k, ((k : ℝ) / (Real.sqrt 2)^l) := by
      rw [sum_add_distrib]
    rw [h₂₁]
    have h₂₂ : ∑ l ∈ Icc 1 k, (1 : ℝ) = (k : ℝ) := by
      simp
    have h₂₃ : ∑ l ∈ Icc 1 k, ((k : ℝ) / (Real.sqrt 2)^l) =
        (k : ℝ) * ∑ l ∈ Icc 1 k, (1 / Real.sqrt 2 : ℝ)^l := by
      have h₂₄ : ∀ l ∈ Icc 1 k, (k : ℝ) / (Real.sqrt 2)^l =
          (k : ℝ) * (1 / Real.sqrt 2 : ℝ)^l := by
        intro l _
        have h₂₅ : (1 / Real.sqrt 2 : ℝ)^l = 1 / (Real.sqrt 2)^l := by
          rw [one_div_pow]
          <;> ring
        rw [h₂₅]
        field_simp
      rw [sum_congr rfl h₂₄, mul_sum]
    rw [h₂₂, h₂₃]
  rw [h₂]
  have h₃ : ∑ l ∈ Icc 1 k, (1 / Real.sqrt 2 : ℝ)^l ≤ 3 := geom_sum_bound k
  calc
    (k : ℝ) + (k : ℝ) * ∑ l ∈ Icc 1 k, (1 / Real.sqrt 2 : ℝ)^l
      ≤ (k : ℝ) + (k : ℝ) * 3 := by gcongr
    _ = 4 * (k : ℝ) := by ring

/-- Upper bound w_l ≤ (√2)^l / k. -/
lemma w_le_sqrt2_pow_div_k (k : ℕ) (hk : 0 < k) (l : ℕ) :
    w k l ≤ (Real.sqrt 2)^l / (k : ℝ) := by
  dsimp only [w]
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h₁ : 0 < (Real.sqrt 2)^l := by positivity
  have h₂ : 0 < (k : ℝ) / (Real.sqrt 2)^l := by positivity
  have h₃ : 1 + (k : ℝ) / (Real.sqrt 2)^l ≥ (k : ℝ) / (Real.sqrt 2)^l := by linarith
  have h₄ : 1 / (1 + (k : ℝ) / (Real.sqrt 2)^l) ≤ 1 / ((k : ℝ) / (Real.sqrt 2)^l) :=
    one_div_le_one_div_of_le (by positivity) h₃
  have h₅ : 1 / ((k : ℝ) / (Real.sqrt 2)^l) = (Real.sqrt 2)^l / (k : ℝ) := by
    field_simp [hk'.ne', h₁.ne'] <;> ring
  rw [h₅] at h₄
  exact h₄

-- Helper: (√2)^l / 2^l = 1 / (√2)^l
private lemma sqrt2_div_pow (l : ℕ) :
    (Real.sqrt 2)^l / (2 : ℝ)^l = 1 / (Real.sqrt 2)^l := by
  have h₁ : (2 : ℝ)^l = (Real.sqrt 2)^(2 * l) := by
    have h₂ : ∀ n : ℕ, (2 : ℝ)^n = (Real.sqrt 2)^(2 * n) := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
        calc
          (2 : ℝ)^(n + 1) = (2 : ℝ)^n * 2 := by ring
          _ = (Real.sqrt 2)^(2 * n) * 2 := by rw [ih]
          _ = (Real.sqrt 2)^(2 * n) * (Real.sqrt 2)^2 := by rw [sqrt2_sq]
          _ = (Real.sqrt 2)^(2 * (n + 1)) := by
            rw [show 2 * (n + 1) = 2 * n + 2 by omega]
            <;> rw [pow_add] <;> ring
    exact h₂ l
  rw [h₁]
  have h₃ : 0 < (Real.sqrt 2)^l := by positivity
  have h₄ : (Real.sqrt 2)^(2 * l) = ((Real.sqrt 2)^l)^2 := by
    rw [show 2 * l = l + l by omega]
    rw [pow_add]
    <;> ring
  rw [h₄]
  field_simp [h₃.ne'] <;> ring

/-- Bound on ∑ w_l / 2^l ≤ 3/k. -/
lemma sum_w_over_2l_bound (k : ℕ) (hk : 0 < k) :
    ∑ l ∈ Icc 1 k, (w k l) / (2 : ℝ)^l ≤ 3 / (k : ℝ) := by
  have h₁ : ∀ l ∈ Icc 1 k, (w k l) / (2 : ℝ)^l ≤ (1 : ℝ) / ((k : ℝ) * (Real.sqrt 2)^l) := by
    intro l _
    have h₂ : w k l ≤ (Real.sqrt 2)^l / (k : ℝ) := w_le_sqrt2_pow_div_k k hk l
    have h₃ : (Real.sqrt 2)^l / (k : ℝ) / (2 : ℝ)^l =
        (1 : ℝ) / ((k : ℝ) * (Real.sqrt 2)^l) := by
      have h₄ : (Real.sqrt 2)^l / (2 : ℝ)^l = 1 / (Real.sqrt 2)^l := sqrt2_div_pow l
      have h₅ : ((Real.sqrt 2)^l / (k : ℝ)) / (2 : ℝ)^l =
          ((Real.sqrt 2)^l / (2 : ℝ)^l) / (k : ℝ) := by
        field_simp <;> ring
      rw [h₅, h₄]
      field_simp
    calc
      (w k l) / (2 : ℝ)^l ≤ ((Real.sqrt 2)^l / (k : ℝ)) / (2 : ℝ)^l := by gcongr
      _ = (1 : ℝ) / ((k : ℝ) * (Real.sqrt 2)^l) := h₃
  have h_sum : ∑ l ∈ Icc 1 k, (1 : ℝ) / ((k : ℝ) * (Real.sqrt 2)^l) =
      (1 : ℝ) / (k : ℝ) * ∑ l ∈ Icc 1 k, (1 / Real.sqrt 2 : ℝ)^l := by
    have h₄ : ∀ l ∈ Icc 1 k, (1 : ℝ) / ((k : ℝ) * (Real.sqrt 2)^l) =
        (1 : ℝ) / (k : ℝ) * (1 / Real.sqrt 2 : ℝ)^l := by
      intro l _
      have h₅ : (1 : ℝ) / ((k : ℝ) * (Real.sqrt 2)^l) =
          (1 : ℝ) / (k : ℝ) * (1 / (Real.sqrt 2)^l) := by
        field_simp
      simpa using h₅
    rw [sum_congr rfl h₄, mul_sum]
  have h_main : ∑ l ∈ Icc 1 k, (w k l) / (2 : ℝ)^l ≤
      ∑ l ∈ Icc 1 k, (1 : ℝ) / ((k : ℝ) * (Real.sqrt 2)^l) :=
    Finset.sum_le_sum fun l hl => h₁ l hl
  calc
    ∑ l ∈ Icc 1 k, (w k l) / (2 : ℝ)^l
      ≤ ∑ l ∈ Icc 1 k, (1 : ℝ) / ((k : ℝ) * (Real.sqrt 2)^l) := h_main
    _ = (1 : ℝ) / (k : ℝ) * ∑ l ∈ Icc 1 k, (1 / Real.sqrt 2 : ℝ)^l := h_sum
    _ ≤ (1 : ℝ) / (k : ℝ) * 3 := by
        gcongr
        exact geom_sum_bound k
    _ = 3 / (k : ℝ) := by ring

/-- Also useful: ∑_{l=1}^k (1/2)^l ≤ 1. -/
lemma sum_half_bound (k : ℕ) : ∑ l ∈ Icc 1 k, (1 / 2 : ℝ)^l ≤ 1 := by
  have h₁ : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have h₂ : (1 / 2 : ℝ) < 1 := by norm_num
  have h₃ : Icc 1 k = Ico 1 (k + 1) := by
    ext x
    simp only [mem_Icc, mem_Ico] <;> omega
  rw [h₃]
  have h₄ : ∑ l ∈ Ico 1 (k + 1), (1 / 2 : ℝ)^l ≤ (1 / 2 : ℝ)^1 / (1 - (1 / 2 : ℝ)) :=
    geom_sum_Ico_le_of_lt_one h₁ h₂
  norm_num at h₄ ⊢
  exact h₄

end MarcusTardos.WeightOptimization
