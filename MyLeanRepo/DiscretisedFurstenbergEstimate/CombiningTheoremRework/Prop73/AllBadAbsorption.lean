module

/-
  AllBadAbsorption — Absorption inequality for the all-tail-bad branch.

  When all tail scales are bad, we only have the coarse bound and need to
  absorb the polynomial K factor into the logarithmic factor L^(-C).

  Whiteprint node: combining_theorem_rework / all_bad_absorption
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.FineConfigSublemma
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable


noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

/-- Absorption inequality: log(1/Δ)^(-C_coarse) * K^(-(C'_coarse+1)) ≥ L^(-C),
    where L = log(1/δ), δ = Δ * δbar, and K is polynomially bounded by L. -/
lemma all_bad_absorption
    {δ Δ δbar L K A C_coarse C'_coarse C α : ℝ}
    (hδ_pos : 0 < δ) (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδbar_pos : 0 < δbar) (hδbar_lt_one : δbar < 1)
    (hδ_eq : δ = Δ * δbar)
    (hL_def : L = Real.log (1 / δ))
    (hL_ge1 : 1 ≤ L) (hL_ge_A : L ≥ A)
    (hA_pos : 0 < A) (hα_pos : 0 < α)
    (hK_pos : 0 < K) (hK_ge1 : 1 ≤ K)
    (hK_poly : K ≤ A * L ^ α)
    (hC_coarse_nonneg : 0 ≤ C_coarse)
    (hC'_coarse_ge1 : 1 ≤ C'_coarse)
    (hC_pos : 0 < C)
    (hC_ge : C ≥ C_coarse + (1 + α) * (C'_coarse + 1)) :
    Real.rpow (Real.log (1 / Δ)) (-C_coarse) * Real.rpow K (-(C'_coarse + 1)) ≥
    Real.rpow L (-C) := by
  have h_logΔ_pos : 0 < Real.log (1 / Δ) :=
    Real.log_pos (by apply one_lt_one_div <;> linarith)
  have h_logΔ_le_L : Real.log (1 / Δ) ≤ L := by
    rw [hL_def]
    have h1 : δ ≤ Δ := by
      rw [hδ_eq]; exact mul_le_of_le_one_right hΔ_pos.le hδbar_lt_one.le
    exact Real.log_le_log (by positivity) (by gcongr <;> linarith)
  have h_anti : ∀ (x y p : ℝ), 0 < x → x ≤ y → p < 0 → x^p ≥ y^p := by
    intro x y p hx hxy hp
    by_cases h : x < y
    · have hy : 0 < y := lt_of_lt_of_le hx hxy
      exact (Real.strictAntiOn_rpow_Ioi_of_exponent_neg hp hx hy h).le
    · have h2 : y ≤ x := le_of_not_gt h
      have h3 : x = y := le_antisymm hxy h2
      rw [h3]
  have h1 : (Real.log (1 / Δ)) ^ (-C_coarse) ≥ L ^ (-C_coarse) := by
    by_cases hC : C_coarse = 0
    · rw [hC]; simp
    · have hC_pos' : 0 < C_coarse := lt_of_le_of_ne hC_coarse_nonneg (Ne.symm hC)
      exact h_anti (Real.log (1 / Δ)) L (-C_coarse) h_logΔ_pos h_logΔ_le_L (by linarith)
  have h3 : K ^ (-(C'_coarse + 1)) ≥ (A * L ^ α) ^ (-(C'_coarse + 1)) :=
    h_anti K (A * L ^ α) (-(C'_coarse + 1)) hK_pos hK_poly (by linarith)
  have h4 : (A * L ^ α) ^ (-(C'_coarse + 1)) =
      A ^ (-(C'_coarse + 1)) * (L ^ α) ^ (-(C'_coarse + 1)) := by
    rw [Real.mul_rpow (by linarith [hA_pos]) (by positivity)]
  have h5 : (L ^ α) ^ (-(C'_coarse + 1)) = L ^ (α * (-(C'_coarse + 1))) := by
    rw [← Real.rpow_mul (by linarith)] <;> ring
  have h6 : A ^ (-(C'_coarse + 1)) ≥ L ^ (-(C'_coarse + 1)) :=
    h_anti A L (-(C'_coarse + 1)) (by linarith [hA_pos]) hL_ge_A (by linarith)
  have h35 : K ^ (-(C'_coarse + 1)) ≥
      L ^ (-(C'_coarse + 1)) * L ^ (α * (-(C'_coarse + 1))) := by
    calc K ^ (-(C'_coarse + 1))
      ≥ (A * L ^ α) ^ (-(C'_coarse + 1)) := h3
    _ = A ^ (-(C'_coarse + 1)) * (L ^ α) ^ (-(C'_coarse + 1)) := h4
    _ = A ^ (-(C'_coarse + 1)) * L ^ (α * (-(C'_coarse + 1))) := by rw [h5]
    _ ≥ L ^ (-(C'_coarse + 1)) * L ^ (α * (-(C'_coarse + 1))) := by gcongr
  have h_exp_sum : (-C_coarse) + (-(C'_coarse + 1)) + (α * (-(C'_coarse + 1))) =
      -(C_coarse + (1 + α) * (C'_coarse + 1)) := by ring
  have h7 : L ^ (-C) ≤ L ^ (-(C_coarse + (1 + α) * (C'_coarse + 1))) :=
    Real.rpow_le_rpow_of_exponent_le hL_ge1 (by linarith)
  calc (Real.log (1 / Δ)) ^ (-C_coarse) * K ^ (-(C'_coarse + 1))
    ≥ L ^ (-C_coarse) * (L ^ (-(C'_coarse + 1)) * L ^ (α * (-(C'_coarse + 1)))) := by gcongr
  _ = L ^ ((-C_coarse) + (-(C'_coarse + 1)) + (α * (-(C'_coarse + 1)))) := by
      rw [← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith)] <;> ring_nf
  _ = L ^ (-(C_coarse + (1 + α) * (C'_coarse + 1))) := by rw [h_exp_sum]
  _ ≥ L ^ (-C) := h7

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
