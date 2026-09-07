module

/-
  AllBadBranch — Extracted all-tail-bad branch for InductiveStepCore_v2.

  When all tail scales are bad, the fine IH is unavailable. Instead:
  1. Trivial TQ_card ≥ MQ_Q from tube family subset
  2. Cancel MQ_Q from B1 card inequality
  3. Apply coarse bound directly
  4. Absorb polynomial K factor into logarithmic L^(-C)
  5. Telescoping bad product gives Pb = δbar

  Whiteprint node: combining_theorem_rework / all_bad_branch
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.AllBadAbsorption
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable


noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion

/-- Final algebra assembly for all-tail-bad branch.

    Given the coarse lower bound and absorption inequality, assemble
    the final combiningLowerBound bound. -/
lemma all_bad_final_assembly
    {L A α K M Δ_coarse δ δbar : ℝ}
    {C_coarse C'_coarse C C' lam s ε_N η PΔ : ℝ}
    {n : ℕ} {Δ : Fin (n + 1) → ℝ} {scaleClass : Fin n → ScaleClass}
    {T_card : ℝ}
    (hK_pos : 0 < K) (hM_pos : 0 < M)
    (hΔ_coarse_pos : 0 < Δ_coarse) (hΔ_lt_one : Δ_coarse < 1)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hδbar_pos : 0 < δbar) (hδbar_lt_one : δbar < 1)
    (hδ_eq : δ = Δ_coarse * δbar)
    (hL_ge1 : 1 ≤ L) (hL_ge_A : L ≥ A) (hL_def : L = Real.log (1 / δ))
    (hA_pos : 0 < A) (hα_pos : 0 < α)
    (hK_ge1 : 1 ≤ K) (hK_poly : K ≤ A * L ^ α)
    (hC_coarse_nonneg : 0 ≤ C_coarse) (hC'_coarse_ge1 : 1 ≤ C'_coarse)
    (hC_pos : 0 < C) (hC_ge : C ≥ C_coarse + (1 + α) * (C'_coarse + 1))
    (hC'_lam_ge : C'_coarse * lam ≤ C' * lam)
    (hs1 : s < 1) (hεN : 0 < ε_N)
    (hPΔ_pos : 0 < PΔ)
    (hT_lower : T_card ≥
        Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * M *
        Real.rpow K (-(C'_coarse + 1)) * Real.rpow δ (C'_coarse * lam) *
        Real.rpow Δ_coarse (-s + ε_N) * PΔ)
    (h_product : combiningLowerBound δ M C C' lam s ε_N η n Δ scaleClass =
        Real.rpow L (-C) * M * Real.rpow δ (C' * lam) *
        Real.rpow δ (-s + ε_N) * (PΔ * δbar)) :
    T_card ≥ combiningLowerBound δ M C C' lam s ε_N η n Δ scaleClass := by
  set X := Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * Real.rpow K (-(C'_coarse + 1)) with hX_def
  have h_logΔ_pos : 0 < Real.log (1 / Δ_coarse) :=
    Real.log_pos (by apply one_lt_one_div <;> linarith)
  have hX_pos : 0 < X := mul_pos
    (Real.rpow_pos_of_pos h_logΔ_pos _)
    (Real.rpow_pos_of_pos hK_pos _)
  have hΔ_pow_pos : 0 < Real.rpow Δ_coarse (-s + ε_N) :=
    Real.rpow_pos_of_pos hΔ_coarse_pos _
  have h_absorb_core : X ≥ Real.rpow L (-C) :=
    all_bad_absorption
      (hδ_pos := hδ_pos) (hΔ_pos := hΔ_coarse_pos) (hΔ_lt_one := hΔ_lt_one)
      (hδbar_pos := hδbar_pos) (hδbar_lt_one := hδbar_lt_one)
      (hδ_eq := hδ_eq) (hL_def := hL_def)
      (hL_ge1 := hL_ge1) (hL_ge_A := hL_ge_A)
      (hA_pos := hA_pos) (hα_pos := hα_pos)
      (hK_pos := hK_pos) (hK_ge1 := hK_ge1)
      (hK_poly := hK_poly)
      (hC_coarse_nonneg := hC_coarse_nonneg)
      (hC'_coarse_ge1 := hC'_coarse_ge1)
      (hC_pos := hC_pos) (hC_ge := hC_ge)
  have h1_s_epsN_pos : 0 < 1 - s + ε_N := by linarith
  have hδbar_pow_lt_one : Real.rpow δbar (1 - s + ε_N) < 1 :=
    Real.rpow_lt_one (by linarith) hδbar_lt_one h1_s_epsN_pos
  have h_pos_LC : 0 < Real.rpow L (-C) := Real.rpow_pos_of_pos (by linarith) (-C)
  have h_absorb : X ≥ Real.rpow L (-C) * Real.rpow δbar (1 - s + ε_N) := by
    have h : Real.rpow L (-C) * Real.rpow δbar (1 - s + ε_N) < Real.rpow L (-C) := by
      rw [mul_comm]
      exact mul_lt_of_lt_one_left h_pos_LC hδbar_pow_lt_one
    exact le_trans h.le h_absorb_core
  have hδ_pow_monotone : Real.rpow δ (C'_coarse * lam) ≥ Real.rpow δ (C' * lam) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le hC'_lam_ge
  have hδ_expand : Real.rpow δ (-s + ε_N) =
      Real.rpow Δ_coarse (-s + ε_N) * Real.rpow δbar (-s + ε_N) := by
    have h9 : δ = Δ_coarse * δbar := hδ_eq
    have h10 : Real.rpow δ (-s + ε_N) = Real.rpow (Δ_coarse * δbar) (-s + ε_N) := by rw [h9]
    rw [h10]
    have h11 : (Δ_coarse * δbar) ^ (-s + ε_N) = (Δ_coarse ^ (-s + ε_N)) * (δbar ^ (-s + ε_N)) :=
      Real.mul_rpow (by linarith) (by linarith)
    have h12 : Real.rpow (Δ_coarse * δbar) (-s + ε_N) =
        Real.rpow Δ_coarse (-s + ε_N) * Real.rpow δbar (-s + ε_N) := by
      exact_mod_cast h11
    exact h12
  -- Reorder hT_lower factors to match X * M * δ^... * Δ^... * PΔ
  have hT_lower' : T_card ≥ X * M * Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse (-s + ε_N) * PΔ := by
    have h_eq1 : X = Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * Real.rpow K (-(C'_coarse + 1)) := by
      simp [hX_def]
    have h_goal : Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * M *
        Real.rpow K (-(C'_coarse + 1)) * Real.rpow δ (C'_coarse * lam) *
        Real.rpow Δ_coarse (-s + ε_N) * PΔ =
        X * M * Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse (-s + ε_N) * PΔ := by
      rw [h_eq1] <;> ring
    rw [h_goal] at hT_lower
    exact hT_lower
  set R := M * Real.rpow Δ_coarse (-s + ε_N) * PΔ with hR_def
  have hR_pos : 0 < R := mul_pos (mul_pos hM_pos hΔ_pow_pos) hPΔ_pos
  have hδ'_pos : 0 < Real.rpow δ (C' * lam) := Real.rpow_pos_of_pos hδ_pos _
  have h_main2 : X * R * Real.rpow δ (C'_coarse * lam) ≥ X * R * Real.rpow δ (C' * lam) :=
    mul_le_mul_of_nonneg_left hδ_pow_monotone (mul_pos hX_pos hR_pos).le
  have h_absorb' : Real.rpow L (-C) * Real.rpow δbar (1 - s + ε_N) * R ≤ X * R :=
    mul_le_mul_of_nonneg_right h_absorb hR_pos.le
  have h_main3 : X * R * Real.rpow δ (C' * lam) ≥
      (Real.rpow L (-C) * Real.rpow δbar (1 - s + ε_N)) * R * Real.rpow δ (C' * lam) := by
    have h : (Real.rpow L (-C) * Real.rpow δbar (1 - s + ε_N)) * R ≤ X * R := h_absorb'
    have h2 : (Real.rpow L (-C) * Real.rpow δbar (1 - s + ε_N)) * R * Real.rpow δ (C' * lam) ≤
        (X * R) * Real.rpow δ (C' * lam) := by
      exact mul_le_mul_of_nonneg_right h hδ'_pos.le
    simpa [mul_assoc] using h2
  have hδbar_split : Real.rpow δbar (1 - s + ε_N) =
      Real.rpow δbar (-s + ε_N) * δbar := by
    have h_add : (1 - s + ε_N) = (-s + ε_N) + 1 := by ring
    have h : Real.rpow δbar ((-s + ε_N) + 1) = Real.rpow δbar (-s + ε_N) * Real.rpow δbar 1 :=
      Real.rpow_add hδbar_pos (-s + ε_N) 1
    have h1 : Real.rpow δbar 1 = δbar := by simp
    have h2 : Real.rpow δbar (1 - s + ε_N) = Real.rpow δbar ((-s + ε_N) + 1) := by rw [h_add]
    rw [h2, h, h1] <;> ring
  have h_main4 : (Real.rpow L (-C) * Real.rpow δbar (1 - s + ε_N)) * R * Real.rpow δ (C' * lam) =
      Real.rpow L (-C) * M * Real.rpow δ (C' * lam) * Real.rpow δ (-s + ε_N) * (PΔ * δbar) := by
    have h5 : (Real.rpow L (-C) * Real.rpow δbar (1 - s + ε_N)) * R * Real.rpow δ (C' * lam) =
        Real.rpow L (-C) * (Real.rpow δbar (1 - s + ε_N) * R) * Real.rpow δ (C' * lam) := by ring
    rw [h5]
    have h6 : Real.rpow δbar (1 - s + ε_N) * R =
        Real.rpow δbar (-s + ε_N) * (R * δbar) := by
      rw [hδbar_split, hR_def] <;> ring
    rw [h6]
    have h7 : R * δbar = M * Real.rpow Δ_coarse (-s + ε_N) * PΔ * δbar := by
      rw [hR_def] <;> ring
    rw [h7]
    have h8 : Real.rpow δbar (-s + ε_N) * (M * Real.rpow Δ_coarse (-s + ε_N) * PΔ * δbar) =
        M * (Real.rpow Δ_coarse (-s + ε_N) * Real.rpow δbar (-s + ε_N)) * (PΔ * δbar) := by ring
    rw [h8, hδ_expand] <;> ring
  have h_main : T_card ≥
      Real.rpow L (-C) * M * Real.rpow δ (C' * lam) * Real.rpow δ (-s + ε_N) * (PΔ * δbar) := by
    have hT_lower'' : T_card ≥ X * R * Real.rpow δ (C'_coarse * lam) := by
      have h_eqR : X * R * Real.rpow δ (C'_coarse * lam) =
          X * M * Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse (-s + ε_N) * PΔ := by
        simp [hR_def, mul_assoc, mul_comm, mul_left_comm] <;> ring
      rw [h_eqR]
      exact hT_lower'
    calc T_card
      ≥ X * R * Real.rpow δ (C'_coarse * lam) := hT_lower''
    _ ≥ X * R * Real.rpow δ (C' * lam) := h_main2
    _ ≥ (Real.rpow L (-C) * Real.rpow δbar (1 - s + ε_N)) * R * Real.rpow δ (C' * lam) := h_main3
    _ = Real.rpow L (-C) * M * Real.rpow δ (C' * lam) * Real.rpow δ (-s + ε_N) * (PΔ * δbar) := h_main4
  rw [h_product]
  exact h_main

end DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure
