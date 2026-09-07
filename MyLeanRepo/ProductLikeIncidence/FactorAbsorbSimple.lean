module

/-
# Simplified Factor Absorption

Proves `6 * C_raw * Real.sqrt C_Pbar * δ^e < 1` with C_raw=4, C_Pbar=4,
using only the box bound `2^20 ≤ δ^(-η_work/100)` and `e ≥ η_work/100`.

This replaces the more complex `factor_absorb_v4_strict` that needed an
extra threshold hypothesis.
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Real

namespace ProductLikeIncidence.ProductReduction

/-- **Simplified factor absorption**: With `C_raw = 4`, `C_Pbar = 4`,
`e ≥ η_work/100`, and the box bound `2^20 ≤ δ^(-η_work/100)`, we have
`6 * C_raw * sqrt(C_Pbar) * δ^e < 1`.

Proof: `6*4*sqrt(4) = 48`, `δ^e ≤ δ^(η_work/100) ≤ 1/2^20 < 1/48`,
so `48 * δ^e < 1`. -/
lemma factor_absorb_simple
    {δ η_work e : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (he_ge : e ≥ η_work / 100)
    (h_box_bound : (2 : ℝ) ^ 20 ≤ δ ^ (-(η_work / 100))) :
    6 * (4 : ℝ) * Real.sqrt 4 * δ ^ e < 1 := by
  have h1 : Real.sqrt 4 = 2 := by
    rw [Real.sqrt_eq_cases] <;> norm_num
  have h_const : 6 * (4 : ℝ) * Real.sqrt 4 = 48 := by
    rw [h1] <;> norm_num
  have h2 : δ ^ e ≤ δ ^ (η_work / 100) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos (by linarith) he_ge
  have h3 : δ ^ (η_work / 100) ≤ 1 / (2 ^ 20 : ℝ) := by
    have h4 : 0 < δ ^ (η_work / 100) := by positivity
    have h5 : δ ^ (-(η_work / 100)) = 1 / δ ^ (η_work / 100) := by
      have h51 : δ ^ (-(η_work / 100)) = (δ ^ (η_work / 100))⁻¹ :=
        Real.rpow_neg hδ_pos.le (η_work / 100)
      rw [h51]
      <;> simp [one_div]
    have h6 : (2 ^ 20 : ℝ) ≤ δ ^ (-(η_work / 100)) := h_box_bound
    rw [h5] at h6
    have h7 : (2 ^ 20 : ℝ) ≤ 1 / δ ^ (η_work / 100) := h6
    have h8 : δ ^ (η_work / 100) ≤ 1 / (2 ^ 20 : ℝ) := by
      calc δ ^ (η_work / 100)
        = 1 / (1 / δ ^ (η_work / 100)) := by field_simp [h4.ne']
      _ ≤ 1 / (2 ^ 20 : ℝ) := by gcongr
    exact h8
  have h4 : (48 : ℝ) * δ ^ e ≤ (48 : ℝ) / (2 ^ 20 : ℝ) := by
    calc (48 : ℝ) * δ ^ e
      ≤ (48 : ℝ) * δ ^ (η_work / 100) := by gcongr
    _ ≤ (48 : ℝ) * (1 / (2 ^ 20 : ℝ)) := by gcongr
    _ = (48 : ℝ) / (2 ^ 20 : ℝ) := by ring
  have h5 : (48 : ℝ) / (2 ^ 20 : ℝ) < 1 := by norm_num
  have h6 : 6 * (4 : ℝ) * Real.sqrt 4 * δ ^ e = (48 : ℝ) * δ ^ e := by
    rw [h_const]
  rw [h6]
  exact lt_of_le_of_lt h4 h5

end ProductLikeIncidence.ProductReduction
