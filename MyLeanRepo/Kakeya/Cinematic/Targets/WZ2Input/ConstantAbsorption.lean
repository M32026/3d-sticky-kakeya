import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Constant absorption lemma

For any nonnegative constant `C` and positive exponent `β`, there exists `δ₀ > 0`
such that `C ≤ δ^{-β}` for all `0 < δ ≤ δ₀`.
-/

noncomputable section

namespace Kakeya.Cinematic

/-- Constant absorption: C ≤ δ^{-β} for sufficiently small δ. -/
lemma constant_absorption (C_total β : ℝ) (hC : 0 ≤ C_total) (hβ : 0 < β) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
      C_total ≤ Real.rpow δ (-β) := by
  by_cases h0 : C_total = 0
  · refine ⟨1, by norm_num, fun δ hδ _ => ?_⟩
    rw [h0]
    exact Real.rpow_nonneg (by positivity) _
  · have hC_pos : 0 < C_total := by
      exact lt_of_le_of_ne hC (Ne.symm h0)
    let δ₀ : ℝ := Real.rpow C_total (-1 / β)
    have hδ₀_pos : 0 < δ₀ := Real.rpow_pos_of_pos hC_pos _
    refine ⟨min δ₀ 1, by positivity, fun δ hδ hδle => ?_⟩
    have h1 : δ ≤ δ₀ := le_trans hδle (min_le_left _ _)
    have h2 : 0 < δ := hδ
    have hβ_nonneg : 0 ≤ β := by linarith
    have h4 : Real.rpow δ β ≤ Real.rpow δ₀ β := by
      apply Real.rpow_le_rpow
      <;> linarith
    have h5 : 0 < Real.rpow δ β := Real.rpow_pos_of_pos h2 β
    have h6 : 0 < Real.rpow δ₀ β := Real.rpow_pos_of_pos hδ₀_pos β
    have h7 : (Real.rpow δ₀ β)⁻¹ ≤ (Real.rpow δ β)⁻¹ := by
      have h71 : (1 : ℝ) / Real.rpow δ₀ β ≤ (1 : ℝ) / Real.rpow δ β := one_div_le_one_div_of_le h5 h4
      have h72 : (1 : ℝ) / Real.rpow δ₀ β = (Real.rpow δ₀ β)⁻¹ := by simp
      have h73 : (1 : ℝ) / Real.rpow δ β = (Real.rpow δ β)⁻¹ := by simp
      rw [h72, h73] at h71
      exact h71
    have h8 : Real.rpow δ (-β) = (Real.rpow δ β)⁻¹ := by
      simpa using Real.rpow_neg (by linarith) β
    have h9 : Real.rpow δ₀ (-β) = (Real.rpow δ₀ β)⁻¹ := by
      simpa using Real.rpow_neg (by linarith) β
    have h10 : Real.rpow δ (-β) ≥ Real.rpow δ₀ (-β) := by
      rw [h8, h9]
      exact h7
    have h11 : Real.rpow δ₀ (-β) = C_total := by
      simp only [δ₀]
      have h12 : (-1 / β : ℝ) * (-β) = 1 := by
        field_simp [hβ.ne']
      have h13 : Real.rpow (Real.rpow C_total (-1 / β)) (-β) =
          Real.rpow C_total ((-1 / β : ℝ) * (-β)) := by
        exact (Real.rpow_mul (by linarith) (-1 / β) (-β)).symm
      rw [h13, h12]
      exact Real.rpow_one C_total
    rw [h11] at h10
    exact h10

end Kakeya.Cinematic
