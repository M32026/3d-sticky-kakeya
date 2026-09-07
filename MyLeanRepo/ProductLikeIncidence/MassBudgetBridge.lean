module

/-
# Mass Budget Bridge

Proves the mass budget condition `δ ^ ε_mass ≤ c_mult / 4`
(equivalently `δ ^ ε_mass ≤ c_endgame / 2` when `c_endgame = c_mult / 2`).

This is one of the H5→H6 bridge hypotheses needed by `glue_h5_to_h6`.

## Proof summary

Given:
- `c_mult = δ^(η_work/2) / (7 * C_work'^2)`
- `C_work' ≤ 35 * δ^(-η_work/2)`
- `2^20 ≤ δ^(-η_work/100)` (box bound)
- `ε_mass = 3*η_work/2 + η_work/100`

Then:
1. `C_work'^2 ≤ 35^2 * δ^(-η_work)`
2. `c_mult / 4 ≥ δ^(3*η_work/2) / (28 * 35^2)`
3. `δ^(η_work/100) ≤ 1/(28*35^2)` (since `2^20 ≥ 28*35^2`)
4. `δ^ε_mass = δ^(3*η_work/2) * δ^(η_work/100)`
5. Therefore `δ^ε_mass ≤ δ^(3*η_work/2) / (28*35^2) ≤ c_mult / 4`

## Dependencies

- `Mathlib` for real arithmetic
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set

namespace ProductLikeIncidence.ProductReduction

/-- Mass budget lemma: `δ ^ ε_mass ≤ c_mult / 4`.

This is the `h_mass_budget` hypothesis for `glue_h5_to_h6`, in the form
`δ ^ ε_mass ≤ c_mult_dir / 2` where `c_mult_dir = c_mult / 2`. -/
lemma mass_budget_bridge
    {δ η_work ε_mass C_work' c_mult : ℝ}
    (hδ_pos : 0 < δ)
    (_hδ_lt_one : δ < 1)
    (_hη_work_pos : 0 < η_work)
    (hC_work'_pos : 0 < C_work')
    (hC_work'_le : C_work' ≤ 35 * δ ^ (-η_work / 2))
    (hc_mult_def : c_mult = δ ^ (η_work / 2) / (7 * C_work' ^ 2))
    (hε_mass_def : ε_mass = 3 * η_work / 2 + η_work / 100)
    (h_box_bound : (2 ^ 20 : ℝ) ≤ δ ^ (-(η_work / 100))) :
    δ ^ ε_mass ≤ c_mult / 4 := by
  -- Step 1: C_work'^2 ≤ 35^2 * δ^(-η_work)
  have h4_pow : (δ ^ (-η_work / 2)) ^ 2 = δ ^ (-η_work) := by
    have h51 : δ ^ ((-η_work / 2) * (2 : ℝ)) = (δ ^ (-η_work / 2)) ^ (2 : ℝ) :=
      Real.rpow_mul hδ_pos.le (-η_work / 2) (2 : ℝ)
    have h5 : (δ ^ (-η_work / 2)) ^ (2 : ℝ) = δ ^ ((-η_work / 2) * (2 : ℝ)) := h51.symm
    have h6 : (δ ^ (-η_work / 2)) ^ 2 = (δ ^ (-η_work / 2)) ^ (2 : ℝ) := by norm_cast
    have h7 : (-η_work / 2 : ℝ) * (2 : ℝ) = -η_work := by ring
    rw [h6, h5, h7]
  have hC2 : C_work' ^ 2 ≤ (35 : ℝ) ^ 2 * δ ^ (-η_work) := by
    have h1 : C_work' ≤ 35 * δ ^ (-η_work / 2) := hC_work'_le
    have h2 : C_work' ^ 2 ≤ (35 * δ ^ (-η_work / 2)) ^ 2 := by gcongr
    have h3 : (35 * δ ^ (-η_work / 2)) ^ 2 = (35 : ℝ) ^ 2 * (δ ^ (-η_work / 2)) ^ 2 := by
      rw [mul_pow]
    calc
      C_work' ^ 2 ≤ (35 * δ ^ (-η_work / 2)) ^ 2 := h2
      _ = (35 : ℝ) ^ 2 * (δ ^ (-η_work / 2)) ^ 2 := h3
      _ = (35 : ℝ) ^ 2 * δ ^ (-η_work) := by rw [h4_pow]

  -- Step 2: Power division identity
  have h_pow_div : δ ^ (η_work / 2) / δ ^ (-η_work) = δ ^ (3 * η_work / 2) := by
    have h_sub : δ ^ (η_work / 2) / δ ^ (-η_work) = δ ^ (η_work / 2 - (-η_work)) := by
      rw [← Real.rpow_sub hδ_pos]
    have h_add : η_work / 2 - (-η_work) = 3 * η_work / 2 := by ring
    rw [h_sub, h_add]

  -- Step 3: c_mult / 4 ≥ δ^(3*η_work/2) / (28 * 35^2)
  have h_lower : c_mult / 4 ≥ δ ^ (3 * η_work / 2) / (28 * (35 : ℝ) ^ 2) := by
    have h4 : 0 < 7 * C_work' ^ 2 := by positivity
    have h5 : 7 * C_work' ^ 2 ≤ 7 * ((35 : ℝ) ^ 2 * δ ^ (-η_work)) := by gcongr
    have h_denom_eq : 28 * (35 : ℝ) ^ 2 * δ ^ (-η_work) =
        4 * (7 * ((35 : ℝ) ^ 2 * δ ^ (-η_work))) := by ring
    calc
      c_mult / 4
        = (δ ^ (η_work / 2) / (7 * C_work' ^ 2)) / 4 := by rw [hc_mult_def]
      _ ≥ (δ ^ (η_work / 2) / (7 * ((35 : ℝ) ^ 2 * δ ^ (-η_work)))) / 4 := by gcongr
      _ = δ ^ (η_work / 2) / (28 * (35 : ℝ) ^ 2 * δ ^ (-η_work)) := by ring
      _ = (δ ^ (η_work / 2) / δ ^ (-η_work)) / (28 * (35 : ℝ) ^ 2) := by ring
      _ = δ ^ (3 * η_work / 2) / (28 * (35 : ℝ) ^ 2) := by rw [h_pow_div]

  -- Step 4: δ^(η_work/100) ≤ 1/(28*35^2)
  have h9 : δ ^ (η_work / 100) ≤ 1 / (28 * (35 : ℝ) ^ 2) := by
    have h11 : 0 < δ ^ (η_work / 100) := by positivity
    have h12 : δ ^ (-(η_work / 100)) = (δ ^ (η_work / 100))⁻¹ := by
      rw [Real.rpow_neg hδ_pos.le]
    have h13 : (2 ^ 20 : ℝ) ≤ (δ ^ (η_work / 100))⁻¹ := by
      rw [←h12]; exact h_box_bound
    have h14 : (2 ^ 20 : ℝ) * δ ^ (η_work / 100) ≤ 1 := by
      have h15 : (2 ^ 20 : ℝ) * δ ^ (η_work / 100) ≤
          (δ ^ (η_work / 100))⁻¹ * δ ^ (η_work / 100) := by
        exact mul_le_mul_of_nonneg_right h13 (by positivity)
      have h16 : (δ ^ (η_work / 100))⁻¹ * δ ^ (η_work / 100) = 1 := by
        field_simp [h11.ne']
      rw [h16] at h15
      exact h15
    have h17 : δ ^ (η_work / 100) ≤ 1 / (2 ^ 20 : ℝ) := by
      calc
        δ ^ (η_work / 100)
          = ((2 ^ 20 : ℝ) * δ ^ (η_work / 100)) / (2 ^ 20 : ℝ) := by
            field_simp
        _ ≤ 1 / (2 ^ 20 : ℝ) := by gcongr
    have h18 : (1 : ℝ) / (2 ^ 20 : ℝ) ≤ 1 / (28 * (35 : ℝ) ^ 2) := by norm_num
    exact le_trans h17 h18

  -- Step 5: δ^ε_mass = δ^(3*η_work/2) * δ^(η_work/100)
  have h10 : δ ^ ε_mass = δ ^ (3 * η_work / 2) * δ ^ (η_work / 100) := by
    have h11 : ε_mass = 3 * η_work / 2 + η_work / 100 := hε_mass_def
    rw [h11]
    rw [← Real.rpow_add hδ_pos]

  -- Step 6: Combine
  calc
    δ ^ ε_mass
      = δ ^ (3 * η_work / 2) * δ ^ (η_work / 100) := h10
    _ ≤ δ ^ (3 * η_work / 2) * (1 / (28 * (35 : ℝ) ^ 2)) := by gcongr
    _ = δ ^ (3 * η_work / 2) / (28 * (35 : ℝ) ^ 2) := by ring
    _ ≤ c_mult / 4 := h_lower

end ProductLikeIncidence.ProductReduction
