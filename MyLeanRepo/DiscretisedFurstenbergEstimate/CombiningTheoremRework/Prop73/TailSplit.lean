module

/-
  Prop73 TailSplit — Fixed-tail bound algebra and δ₀ existence

  Contains:
  - combine_bounds_fixed_tail: algebra for fixed-tail induction
  - exists_delta0_helper: existence of sufficiently small δ₀

  Whiteprint node: combining_theorem_genuine / tail_split
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.BaseCaseBad
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.BaseCaseNormal
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.BaseCaseGood
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.GoodTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5Wrapper
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.BetweenScalesTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CompactUniformity
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M2

/-- Algebra for combining coarse and fine bounds in fixed-tail induction. -/
lemma combine_bounds_fixed_tail
    {δ Δ δbar : ℝ} (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδbar_pos : 0 < δbar) (hδbar_lt_one : δbar < 1)
    (hδ_eq : δ = Δ * δbar)
    {s ε_N : ℝ} (hs : 0 < s) (hεN : 0 < ε_N)
    {C_coarse C_fine C'_coarse C'_fine C'_final : ℝ}
    (hC_coarse_nonneg : 0 ≤ C_coarse) (hC_fine_pos : 0 < C_fine)
    (hC'_coarse_nonneg : 0 ≤ C'_coarse) (hC'_fine_pos : 0 < C'_fine)
    (hC'_final_pos : 0 < C'_final)
    {K M MΔ MQ T_card TΔ_card TQ_card : ℝ}
    (hK_ge1 : 1 ≤ K)
    {A α : ℝ} (hA_pos : 0 < A) (hα_pos : 0 < α)
    (hK_poly : K ≤ A * (Real.log (1 / δ)) ^ α)
    (hL_ge1 : 1 ≤ Real.log (1 / δ))
    (hL_ge_A : Real.log (1 / δ) ≥ A)
    (hM_pos : 0 < M) (hMΔ_pos : 0 < MΔ) (hMQ_pos : 0 < MQ)
    (h_card_ineq : K * T_card * MΔ * MQ ≥ TΔ_card * TQ_card * M)
    {PΔ Pb : ℝ} (hPΔ_pos : 0 < PΔ) (hPb_pos : 0 < Pb)
    (lam : ℝ) (hlam_pos : 0 < lam)
    (lam_tail : ℝ) (hlam_tail_pos : 0 < lam_tail)
    (hC'_final_ge : C'_final * lam ≥ C'_coarse * lam + C'_fine * lam_tail)
    (h_coarse_bound : TΔ_card ≥
        Real.rpow (Real.log (1 / Δ)) (-C_coarse) * MΔ *
        Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
        Real.rpow Δ (-s + ε_N) * PΔ)
    (h_fine_bound : TQ_card ≥
        Real.rpow (Real.log (1 / δbar)) (-C_fine) * MQ *
        Real.rpow δbar (C'_fine * lam_tail) * Real.rpow δbar (-s + ε_N) * Pb)
    (C : ℝ) (hC_pos : 0 < C)
    (hC_ge : C ≥ (1 + α) * (C'_coarse + 1) + C_coarse + C_fine) :
    T_card ≥
      Real.rpow (Real.log (1 / δ)) (-C) * M *
      Real.rpow δ (C'_final * lam) * Real.rpow δ (-s + ε_N) * (PΔ * Pb) := by
  set L : ℝ := Real.log (1 / δ) with hL_def
  have hK_pos : 0 < K := by linarith
  have hA_nonneg : 0 ≤ A := by linarith
  have hδ_lt_one : δ < 1 := by rw [hδ_eq]; nlinarith
  have h_logΔ_pos : 0 < Real.log (1 / Δ) := Real.log_pos (by apply one_lt_one_div <;> linarith)
  have h_logδbar_pos : 0 < Real.log (1 / δbar) := Real.log_pos (by apply one_lt_one_div <;> linarith)
  have h_logΔ_le_L : Real.log (1 / Δ) ≤ L := by
    have h1 : δ ≤ Δ := by rw [hδ_eq]; exact mul_le_of_le_one_right hΔ_pos.le hδbar_lt_one.le
    exact Real.log_le_log (by positivity) (by gcongr <;> linarith)
  have h_logδbar_le_L : Real.log (1 / δbar) ≤ L := by
    have h1 : δ ≤ δbar := by rw [hδ_eq]; exact mul_le_of_le_one_left hδbar_pos.le hΔ_lt_one.le
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
    · have hC_pos : 0 < C_coarse :=
        lt_of_le_of_ne hC_coarse_nonneg (Ne.symm hC)
      exact h_anti (Real.log (1 / Δ)) L (-C_coarse) h_logΔ_pos h_logΔ_le_L (by linarith)
  have h2 : (Real.log (1 / δbar)) ^ (-C_fine) ≥ L ^ (-C_fine) :=
    h_anti (Real.log (1 / δbar)) L (-C_fine) h_logδbar_pos h_logδbar_le_L (by linarith)
  have h3 : K ^ (-(C'_coarse + 1)) ≥ (A * L ^ α) ^ (-(C'_coarse + 1)) :=
    h_anti K (A * L ^ α) (-(C'_coarse + 1)) hK_pos hK_poly (by linarith)
  have h4 : (A * L ^ α) ^ (-(C'_coarse + 1)) =
      A ^ (-(C'_coarse + 1)) * (L ^ α) ^ (-(C'_coarse + 1)) := by
    rw [Real.mul_rpow hA_nonneg (by positivity)]
  have h5 : (L ^ α) ^ (-(C'_coarse + 1)) = L ^ (α * (-(C'_coarse + 1))) := by
    rw [← Real.rpow_mul (by linarith)] <;> ring
  have h6 : A ^ (-(C'_coarse + 1)) ≥ L ^ (-(C'_coarse + 1)) :=
    h_anti A L (-(C'_coarse + 1)) (by linarith) hL_ge_A (by linarith)
  have h35 : K ^ (-(C'_coarse + 1)) ≥
      L ^ (-(C'_coarse + 1)) * L ^ (α * (-(C'_coarse + 1))) := by
    calc K ^ (-(C'_coarse + 1))
      ≥ (A * L ^ α) ^ (-(C'_coarse + 1)) := h3
    _ = A ^ (-(C'_coarse + 1)) * (L ^ α) ^ (-(C'_coarse + 1)) := h4
    _ = A ^ (-(C'_coarse + 1)) * L ^ (α * (-(C'_coarse + 1))) := by rw [h5]
    _ ≥ L ^ (-(C'_coarse + 1)) * L ^ (α * (-(C'_coarse + 1))) := by gcongr
  have h_exp_sum : (-C_coarse) + (-C_fine) + (-(C'_coarse + 1)) + (α * (-(C'_coarse + 1))) =
      -((1 + α) * (C'_coarse + 1) + C_coarse + C_fine) := by ring
  have h7 : L ^ (-C) ≤ L ^ (-((1 + α) * (C'_coarse + 1) + C_coarse + C_fine)) :=
    Real.rpow_le_rpow_of_exponent_le hL_ge1 (by linarith)
  have h_log_bound : (Real.log (1 / Δ)) ^ (-C_coarse) *
      (Real.log (1 / δbar)) ^ (-C_fine) * K ^ (-(C'_coarse + 1)) ≥ L ^ (-C) := by
    calc (Real.log (1 / Δ)) ^ (-C_coarse) *
        (Real.log (1 / δbar)) ^ (-C_fine) * K ^ (-(C'_coarse + 1))
      ≥ L ^ (-C_coarse) * L ^ (-C_fine) *
          (L ^ (-(C'_coarse + 1)) * L ^ (α * (-(C'_coarse + 1)))) := by gcongr
    _ = L ^ ((-C_coarse) + (-C_fine) + (-(C'_coarse + 1)) + (α * (-(C'_coarse + 1)))) := by
        rw [← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith)] <;> ring_nf
    _ = L ^ (-((1 + α) * (C'_coarse + 1) + C_coarse + C_fine)) := by rw [h_exp_sum]
    _ ≥ L ^ (-C) := h7
  have h11 : C'_coarse * lam + C'_fine * lam_tail ≤ C'_final * lam := by linarith
  have h12 : C'_coarse * lam ≤ C'_final * lam := by
    have h_pos : 0 < C'_fine * lam_tail := mul_pos hC'_fine_pos hlam_tail_pos
    linarith
  have hδ_pow_bound : δ ^ (C'_coarse * lam) * δbar ^ (C'_fine * lam_tail) ≥ δ ^ (C'_final * lam) := by
    have hδ1 : δ ^ (C'_coarse * lam) = Δ ^ (C'_coarse * lam) * δbar ^ (C'_coarse * lam) := by
      rw [hδ_eq, Real.mul_rpow (by linarith) (by linarith)]
    have hΔ1 : Δ ^ (C'_coarse * lam) ≥ Δ ^ (C'_final * lam) :=
      Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le h12
    have hδbar_sum : δbar ^ (C'_coarse * lam) * δbar ^ (C'_fine * lam_tail) =
        δbar ^ (C'_coarse * lam + C'_fine * lam_tail) := by
      rw [← Real.rpow_add hδbar_pos] <;> ring
    have hδbar2 : δbar ^ (C'_coarse * lam + C'_fine * lam_tail) ≥ δbar ^ (C'_final * lam) :=
      Real.rpow_le_rpow_of_exponent_ge hδbar_pos hδbar_lt_one.le h11
    have hδ_final : δ ^ (C'_final * lam) = Δ ^ (C'_final * lam) * δbar ^ (C'_final * lam) := by
      rw [hδ_eq, Real.mul_rpow (by linarith) (by linarith)]
    calc δ ^ (C'_coarse * lam) * δbar ^ (C'_fine * lam_tail)
      = (Δ ^ (C'_coarse * lam) * δbar ^ (C'_coarse * lam)) * δbar ^ (C'_fine * lam_tail) := by rw [hδ1]
    _ = Δ ^ (C'_coarse * lam) * (δbar ^ (C'_coarse * lam) * δbar ^ (C'_fine * lam_tail)) := by ring
    _ = Δ ^ (C'_coarse * lam) * δbar ^ (C'_coarse * lam + C'_fine * lam_tail) := by rw [hδbar_sum]
    _ ≥ Δ ^ (C'_final * lam) * δbar ^ (C'_final * lam) := by gcongr
    _ = δ ^ (C'_final * lam) := by rw [hδ_final]
  have h_rpow_product : Δ ^ (-s + ε_N) * δbar ^ (-s + ε_N) = δ ^ (-s + ε_N) := by
    rw [hδ_eq, Real.mul_rpow (by linarith) (by linarith)]
  set A_prod : ℝ := (Real.log (1 / Δ)) ^ (-C_coarse) * MΔ * K ^ (-C'_coarse) *
        δ ^ (C'_coarse * lam) * Δ ^ (-s + ε_N) * PΔ with hA_def
  set B_prod : ℝ := (Real.log (1 / δbar)) ^ (-C_fine) * MQ *
        δbar ^ (C'_fine * lam_tail) * δbar ^ (-s + ε_N) * Pb with hB_def
  have hA_prod_nonneg : 0 ≤ A_prod := by positivity
  have hB_prod_nonneg : 0 ≤ B_prod := by positivity
  have hTΔ_nonneg : 0 ≤ TΔ_card := le_trans hA_prod_nonneg h_coarse_bound
  have hTQ_nonneg : 0 ≤ TQ_card := le_trans hB_prod_nonneg h_fine_bound
  set D : ℝ := δ ^ (C'_coarse * lam) * δbar ^ (C'_fine * lam_tail) with hD_def
  set R : ℝ := δ ^ (-s + ε_N) * M * (PΔ * Pb) with hR_def
  have hD_nonneg : 0 ≤ D := by positivity
  have hR_nonneg : 0 ≤ R := by positivity
  have h_product : TΔ_card * TQ_card ≥
      (Real.log (1 / Δ)) ^ (-C_coarse) * (Real.log (1 / δbar)) ^ (-C_fine) *
      K ^ (-C'_coarse) * D * δ ^ (-s + ε_N) * MΔ * MQ * (PΔ * Pb) := by
    have h_mul : TΔ_card * TQ_card ≥ A_prod * B_prod := by
      calc TΔ_card * TQ_card
        ≥ A_prod * TQ_card := mul_le_mul_of_nonneg_right h_coarse_bound hTQ_nonneg
      _ ≥ A_prod * B_prod := mul_le_mul_of_nonneg_left h_fine_bound hA_prod_nonneg
    have h_eq : A_prod * B_prod =
        (Real.log (1 / Δ)) ^ (-C_coarse) * (Real.log (1 / δbar)) ^ (-C_fine) *
          K ^ (-C'_coarse) * D * δ ^ (-s + ε_N) * MΔ * MQ * (PΔ * Pb) := by
      simp only [hA_def, hB_def, hD_def]
      have h9 : Δ ^ (-s + ε_N) * δbar ^ (-s + ε_N) = δ ^ (-s + ε_N) := h_rpow_product
      have h10 : (Real.log (1 / Δ)) ^ (-C_coarse) * MΔ * K ^ (-C'_coarse) *
            δ ^ (C'_coarse * lam) * Δ ^ (-s + ε_N) * PΔ *
          ((Real.log (1 / δbar)) ^ (-C_fine) * MQ *
            δbar ^ (C'_fine * lam_tail) * δbar ^ (-s + ε_N) * Pb) =
          (Real.log (1 / Δ)) ^ (-C_coarse) * (Real.log (1 / δbar)) ^ (-C_fine) *
            K ^ (-C'_coarse) * (δ ^ (C'_coarse * lam) * δbar ^ (C'_fine * lam_tail)) *
            (Δ ^ (-s + ε_N) * δbar ^ (-s + ε_N)) * MΔ * MQ * (PΔ * Pb) := by ring
      rw [h10, h9] <;> ring
    rw [h_eq] at h_mul
    exact h_mul
  have hK_div : K ^ (-C'_coarse) / K = K ^ (-(C'_coarse + 1)) := by
    have hK1 : K ^ (-C'_coarse) / K = K ^ (-C'_coarse) * K ^ (-1 : ℝ) := by
      have h : K ^ (-1 : ℝ) = K⁻¹ := by simpa using Real.rpow_neg_one K
      rw [h]; field_simp [hK_pos.ne'] <;> ring
    rw [hK1, ← Real.rpow_add hK_pos] <;> ring_nf
  have h_pos : 0 < K * MΔ * MQ := by positivity
  have h_main : T_card ≥ (TΔ_card * TQ_card * M) / (K * MΔ * MQ) := by
    have h_eq : (K * T_card * MΔ * MQ) / (K * MΔ * MQ) = T_card := by
      field_simp [h_pos.ne'] <;> ring
    have h : K * T_card * MΔ * MQ ≥ TΔ_card * TQ_card * M := h_card_ineq
    have h' : (K * T_card * MΔ * MQ) / (K * MΔ * MQ) ≥
        (TΔ_card * TQ_card * M) / (K * MΔ * MQ) := by gcongr
    rw [h_eq] at h'; exact h'
  set LogK : ℝ := (Real.log (1 / Δ)) ^ (-C_coarse) * (Real.log (1 / δbar)) ^ (-C_fine) *
      K ^ (-(C'_coarse + 1)) with hLogK_def
  have h_goal : LogK ≥ L ^ (-C) := by
    simpa [hLogK_def] using h_log_bound
  have h_goal' : L ^ (-C) ≤ LogK := h_goal
  have h_goal2 : D ≥ δ ^ (C'_final * lam) := hδ_pow_bound
  have h_goal2' : δ ^ (C'_final * lam) ≤ D := h_goal2
  have h_final : (TΔ_card * TQ_card * M) / (K * MΔ * MQ) ≥
      L ^ (-C) * M * δ ^ (C'_final * lam) * δ ^ (-s + ε_N) * (PΔ * Pb) := by
    have h_div_num : TΔ_card * TQ_card * M ≥
        ((Real.log (1 / Δ)) ^ (-C_coarse) * (Real.log (1 / δbar)) ^ (-C_fine) *
          K ^ (-C'_coarse) * D * δ ^ (-s + ε_N) * MΔ * MQ * (PΔ * Pb)) * M :=
      mul_le_mul_of_nonneg_right h_product (by positivity)
    have h1 : (TΔ_card * TQ_card * M) / (K * MΔ * MQ) ≥
        (((Real.log (1 / Δ)) ^ (-C_coarse) * (Real.log (1 / δbar)) ^ (-C_fine) *
          K ^ (-C'_coarse) * D * δ ^ (-s + ε_N) * MΔ * MQ * (PΔ * Pb)) * M) / (K * MΔ * MQ) :=
      div_le_div_of_nonneg_right h_div_num (by positivity)
    have h2 : (((Real.log (1 / Δ)) ^ (-C_coarse) * (Real.log (1 / δbar)) ^ (-C_fine) *
          K ^ (-C'_coarse) * D * δ ^ (-s + ε_N) * MΔ * MQ * (PΔ * Pb)) * M) / (K * MΔ * MQ) =
        (Real.log (1 / Δ)) ^ (-C_coarse) * (Real.log (1 / δbar)) ^ (-C_fine) *
          (K ^ (-C'_coarse) / K) * D * (δ ^ (-s + ε_N) * M * (PΔ * Pb)) := by
      field_simp [h_pos.ne'] <;> ring
    rw [h2] at h1
    rw [hK_div] at h1
    have h3 : (Real.log (1 / Δ)) ^ (-C_coarse) * (Real.log (1 / δbar)) ^ (-C_fine) *
          K ^ (-(C'_coarse + 1)) * D * (δ ^ (-s + ε_N) * M * (PΔ * Pb)) ≥
        L ^ (-C) * D * (δ ^ (-s + ε_N) * M * (PΔ * Pb)) := by
      have h_goal_D : L ^ (-C) * D ≤ LogK * D := mul_le_mul_of_nonneg_right h_goal' hD_nonneg
      have h_nonneg : 0 ≤ δ ^ (-s + ε_N) * M * (PΔ * Pb) := by positivity
      exact mul_le_mul_of_nonneg_right h_goal_D h_nonneg
    have h4 : L ^ (-C) * D * (δ ^ (-s + ε_N) * M * (PΔ * Pb)) ≥
        L ^ (-C) * δ ^ (C'_final * lam) * (δ ^ (-s + ε_N) * M * (PΔ * Pb)) := by
      have h_nonneg2 : 0 ≤ L ^ (-C) * (δ ^ (-s + ε_N) * M * (PΔ * Pb)) := by positivity
      have h : (L ^ (-C) * (δ ^ (-s + ε_N) * M * (PΔ * Pb))) * D ≥
          (L ^ (-C) * (δ ^ (-s + ε_N) * M * (PΔ * Pb))) * δ ^ (C'_final * lam) :=
        mul_le_mul_of_nonneg_left h_goal2' h_nonneg2
      have h_assoc : L ^ (-C) * D * (δ ^ (-s + ε_N) * M * (PΔ * Pb)) =
          (L ^ (-C) * (δ ^ (-s + ε_N) * M * (PΔ * Pb))) * D := by ring
      have h_assoc2 : L ^ (-C) * δ ^ (C'_final * lam) * (δ ^ (-s + ε_N) * M * (PΔ * Pb)) =
          (L ^ (-C) * (δ ^ (-s + ε_N) * M * (PΔ * Pb))) * δ ^ (C'_final * lam) := by ring
      rw [h_assoc, h_assoc2]
      exact h
    calc (TΔ_card * TQ_card * M) / (K * MΔ * MQ)
      ≥ (Real.log (1 / Δ)) ^ (-C_coarse) * (Real.log (1 / δbar)) ^ (-C_fine) *
          K ^ (-(C'_coarse + 1)) * D * (δ ^ (-s + ε_N) * M * (PΔ * Pb)) := h1
    _ ≥ L ^ (-C) * D * (δ ^ (-s + ε_N) * M * (PΔ * Pb)) := h3
    _ ≥ L ^ (-C) * δ ^ (C'_final * lam) * (δ ^ (-s + ε_N) * M * (PΔ * Pb)) := h4
    _ = L ^ (-C) * M * δ ^ (C'_final * lam) * δ ^ (-s + ε_N) * (PΔ * Pb) := by ring
  calc T_card
    ≥ (TΔ_card * TQ_card * M) / (K * MΔ * MQ) := h_main
  _ ≥ L ^ (-C) * M * δ ^ (C'_final * lam) * δ ^ (-s + ε_N) * (PΔ * Pb) := h_final

lemma exists_delta0_helper
    (A : ℝ) (hA_pos : 0 < A)
    (τ : ℝ) (hτ_pos : 0 < τ) (hτ_lt_one : τ < 1)
    (C_P : ℝ) (hCP : 1 ≤ C_P)
    (δ_tail : ℝ) (hδ_tail_pos : 0 < δ_tail)
    (lam : ℝ) (hlam_pos : 0 < lam) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ δ₀ ≤ Real.exp (-A) ∧
      Real.rpow δ₀ τ ≤ δ_tail ∧
      (∀ (k : ℕ), dyadicDelta k ≤ δ₀ →
        2700 * (3145728 : ℝ) * (4 * (k : ℝ) + 7)^7 ≤ Real.rpow (dyadicDelta k) (-lam)) ∧
      (∀ (k : ℕ), dyadicDelta k ≤ δ₀ →
        Real.log (1 / dyadicDelta k) ≥ τ ^ (-(C_P + 2))) := by
  set b : ℝ := (2 : ℝ) ^ lam with hb_def
  have hb_gt_one : 1 < b := by
    rw [hb_def]
    have h2 : 0 < lam := hlam_pos
    exact Real.one_lt_rpow (by norm_num) h2
  set C : ℝ := 2700 * (3145728 : ℝ) * (11 : ℝ)^7 with hC_def
  have hC_pos : 0 < C := by positivity
  have h_tendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ)^7 / b^n) Filter.atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 7 hb_gt_one
  have h_eventually : ∀ᶠ (n : ℕ) in Filter.atTop, (n : ℝ)^7 / b^n < 1 / C := by
    have h_ball : Metric.ball (0 : ℝ) (1 / C) ∈ nhds (0 : ℝ) :=
      Metric.ball_mem_nhds 0 (by positivity)
    have h : ∀ᶠ (n : ℕ) in Filter.atTop, (n : ℝ)^7 / b^n ∈ Metric.ball (0 : ℝ) (1 / C) :=
      h_tendsto h_ball
    filter_upwards [h] with n hn
    have h_pos : 0 ≤ (n : ℝ)^7 / b^n := by positivity
    have h_in : ‖(n : ℝ)^7 / b^n‖ < 1 / C := by simpa [Metric.mem_ball, dist_zero_right] using hn
    have h_abs : |(n : ℝ)^7 / b^n| < 1 / C := by exact_mod_cast h_in
    rwa [abs_of_nonneg h_pos] at h_abs
  rcases Filter.eventually_atTop.mp h_eventually with ⟨N0, hN0⟩
  let N : ℕ := max N0 1
  have hN_ge1 : 1 ≤ N := by simp [N] <;> omega
  have hN : ∀ n ≥ N, (n : ℝ)^7 / b^n < 1 / C := by
    intro n hn
    have h_n_ge_N0 : n ≥ N0 := by
      simp [N] at hn <;> omega
    exact hN0 n h_n_ge_N0
  have h_main_ineq : ∀ (n : ℕ), n ≥ N →
      2700 * (3145728 : ℝ) * (4 * (n : ℝ) + 7)^7 ≤ b^n := by
    intro n hn
    have h1 : n ≥ 1 := by linarith
    have h2 : (4 * (n : ℝ) + 7)^7 ≤ (11 * (n : ℝ))^7 := by
      have h3 : 4 * (n : ℝ) + 7 ≤ 11 * (n : ℝ) := by
        have h4 : (n : ℝ) ≥ 1 := by exact_mod_cast h1
        linarith
      have h4 : 0 ≤ 4 * (n : ℝ) + 7 := by positivity
      gcongr <;> linarith
    have h5 : (n : ℝ)^7 / b^n < 1 / C := hN n hn
    have h6 : (n : ℝ)^7 ≤ (1 / C) * b^n := by
      have h7 : 0 < b^n := by positivity
      have h8 : (n : ℝ)^7 / b^n < 1 / C := h5
      have h9 : (n : ℝ)^7 ≤ (1 / C) * b^n := by
        calc (n : ℝ)^7
          = ((n : ℝ)^7 / b^n) * b^n := by field_simp [h7.ne'] <;> ring
        _ ≤ (1 / C) * b^n := by gcongr
      exact h9
    calc 2700 * (3145728 : ℝ) * (4 * (n : ℝ) + 7)^7
      ≤ 2700 * (3145728 : ℝ) * (11 * (n : ℝ))^7 := by gcongr
    _ = C * (n : ℝ)^7 := by
      simp [hC_def] <;> ring
    _ ≤ C * ((1 / C) * b^n) := by gcongr
    _ = b^n := by
      field_simp [hC_pos.ne'] <;> ring
  set δ₁ : ℝ := Real.exp (-A) with hδ1_def
  have hδ1_pos : 0 < δ₁ := Real.exp_pos (-A)
  set δ₂ : ℝ := Real.rpow δ_tail (1 / τ) with hδ2_def
  have hδ2_pos : 0 < δ₂ := Real.rpow_pos_of_pos hδ_tail_pos (1 / τ)
  have hδ2_pow : Real.rpow δ₂ τ = δ_tail := by
    rw [hδ2_def]
    have h1 : Real.rpow (Real.rpow δ_tail (1 / τ)) τ = Real.rpow δ_tail ((1 / τ) * τ) := by
      exact (Real.rpow_mul hδ_tail_pos.le (1 / τ) τ).symm
    rw [h1]
    have h2 : (1 / τ) * τ = 1 := by field_simp [hτ_pos.ne'] <;> ring
    rw [h2]
    simp
  set δ₃ : ℝ := dyadicDelta N with hδ3_def
  have hδ3_pos : 0 < δ₃ := dyadicDelta_pos N
  -- δ₄ ensures log(1/δ) ≥ τ^{-(C_P+2)} for all δ ≤ δ₄
  set δ₄ : ℝ := Real.exp (-(τ ^ (-(C_P + 2)))) with hδ4_def
  have hδ4_pos : 0 < δ₄ := Real.exp_pos _
  set δ₀ : ℝ := min δ₁ (min δ₂ (min δ₃ δ₄)) with hδ0_def
  have hδ0_pos : 0 < δ₀ := by
    apply lt_min hδ1_pos
    apply lt_min hδ2_pos
    apply lt_min hδ3_pos hδ4_pos
  have hδ0_le_δ1 : δ₀ ≤ δ₁ := min_le_left _ _
  have hδ0_le_δ2 : δ₀ ≤ δ₂ := by
    have h : δ₀ ≤ min δ₂ (min δ₃ δ₄) := min_le_right _ _
    exact le_trans h (min_le_left _ _)
  have hδ0_le_δ3 : δ₀ ≤ δ₃ := by
    have h : δ₀ ≤ min δ₂ (min δ₃ δ₄) := min_le_right _ _
    have h' : min δ₃ δ₄ ≤ δ₃ := min_le_left _ _
    exact le_trans h (le_trans (min_le_right _ _) h')
  have hδ0_le_δ4 : δ₀ ≤ δ₄ := by
    have h : δ₀ ≤ min δ₂ (min δ₃ δ₄) := min_le_right _ _
    have h' : min δ₃ δ₄ ≤ δ₄ := min_le_right _ _
    exact le_trans h (le_trans (min_le_right _ _) h')
  have h_rpow_le : Real.rpow δ₀ τ ≤ δ_tail := by
    calc Real.rpow δ₀ τ
      ≤ Real.rpow δ₂ τ := Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    _ = δ_tail := hδ2_pow
  have h_final : ∀ (k : ℕ), dyadicDelta k ≤ δ₀ →
      2700 * (3145728 : ℝ) * (4 * (k : ℝ) + 7)^7 ≤ Real.rpow (dyadicDelta k) (-lam) := by
    intro k hk
    have h_k_ge_N : k ≥ N := by
      by_contra h
      have h' : k < N := by omega
      have h1 : (2 : ℕ)^k < (2 : ℕ)^N := by
        apply Nat.pow_lt_pow_right (by norm_num) h'
      have h2 : (2 : ℝ)^k < (2 : ℝ)^N := by exact_mod_cast h1
      have h3 : 1 / (2 : ℝ)^k > 1 / (2 : ℝ)^N := by
        apply one_div_lt_one_div_of_lt
        · positivity
        · exact h2
      have h4 : dyadicDelta k > dyadicDelta N := by
        simpa [dyadicDelta] using h3
      have h5 : dyadicDelta k > δ₀ := by
        calc dyadicDelta k > dyadicDelta N := h4
          _ = δ₃ := by simp [hδ3_def]
          _ ≥ δ₀ := hδ0_le_δ3
      linarith
    have h3 : b^k = Real.rpow (dyadicDelta k) (-lam) := by
      have h4 : b^k = Real.rpow 2 (lam * (k : ℝ)) := by
        have h41 : b = Real.rpow 2 lam := by simp [hb_def]
        rw [h41]
        exact (Real.rpow_mul_natCast (by norm_num) lam k).symm
      have h5 : dyadicDelta k = Real.rpow 2 (-(k : ℝ)) := by
        simp [dyadicDelta, Real.rpow_neg, Real.rpow_natCast]
        <;> field_simp <;> ring
      have h6 : Real.rpow (dyadicDelta k) (-lam) = Real.rpow 2 ((-(k : ℝ)) * (-lam)) := by
        rw [h5]
        exact (Real.rpow_mul (by norm_num) (-(k : ℝ)) (-lam)).symm
      have h7 : (-(k : ℝ)) * (-lam) = lam * (k : ℝ) := by ring
      calc b^k
        = Real.rpow 2 (lam * (k : ℝ)) := h4
      _ = Real.rpow 2 ((-(k : ℝ)) * (-lam)) := by rw [h7]
      _ = Real.rpow (dyadicDelta k) (-lam) := h6.symm
    have h6 : 2700 * (3145728 : ℝ) * (4 * (k : ℝ) + 7)^7 ≤ b^k :=
      h_main_ineq k h_k_ge_N
    rw [h3] at h6
    exact h6
  have h_polylog : ∀ (k : ℕ), dyadicDelta k ≤ δ₀ →
      Real.log (1 / dyadicDelta k) ≥ τ ^ (-(C_P + 2)) := by
    intro k hk
    have hδk_le_δ4 : dyadicDelta k ≤ δ₄ := le_trans hk hδ0_le_δ4
    have h1 : 0 < dyadicDelta k := dyadicDelta_pos k
    have h2 : Real.log (1 / dyadicDelta k) ≥ Real.log (1 / δ₄) := by
      apply Real.log_le_log
      · positivity
      · apply one_div_le_one_div_of_le h1
        exact hδk_le_δ4
    have h3 : Real.log (1 / δ₄) = τ ^ (-(C_P + 2)) := by
      rw [hδ4_def]
      have h41 : (Real.exp (-(τ ^ (-(C_P + 2)))))⁻¹ = Real.exp (τ ^ (-(C_P + 2))) := by
        rw [← Real.exp_neg] <;> ring_nf
      have h42 : 1 / Real.exp (-(τ ^ (-(C_P + 2)))) = Real.exp (τ ^ (-(C_P + 2))) := by
        simpa [one_div] using h41
      rw [h42, Real.log_exp]
    rw [h3] at h2
    exact h2
  exact ⟨δ₀, hδ0_pos, hδ0_le_δ1, h_rpow_le, h_final, h_polylog⟩

/-! ### Telescoping product and equation-(88) helper -/

/-- Telescoping product over `Finset.range n` for positive real-valued `f`. -/
lemma prod_range_div_real (n : ℕ) (f : ℕ → ℝ) (hpos : ∀ k ≤ n, 0 < f k) :
    ∏ k ∈ Finset.range n, f (k + 1) / f k = f n / f 0 := by
  induction n with
  | zero =>
    have hf0 : 0 < f 0 := hpos 0 (by omega)
    have h : f 0 / f 0 = 1 := div_self hf0.ne'
    simpa using h.symm
  | succ n ih =>
    rw [Finset.prod_range_succ]
    rw [ih (fun k hk => hpos k (by omega))]
    have hfn : 0 < f n := hpos n (by omega)
    field_simp [hfn.ne'] <;> ring

/-- Telescoping product over `Finset.Ico m n` for positive real-valued `f`. -/
lemma prod_Ico_div_real (f : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n)
    (hpos : ∀ k ≤ n, 0 < f k) :
    ∏ i ∈ Finset.Ico m n, f (i + 1) / f i = f n / f m := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    simp [hm, Finset.Ico_eq_empty]
    <;> have h : f 0 / f 0 = 1 := by
      have hf0 : 0 < f 0 := hpos 0 (by omega)
      exact div_self hf0.ne'
    exact h.symm
  | succ n ih =>
    by_cases h : m ≤ n
    · have h2 : Finset.Ico m (n + 1) = Finset.Ico m n ∪ {n} := by
        ext x
        simp [Finset.mem_Ico]
        <;> omega
      have h3 : Disjoint (Finset.Ico m n) ({n} : Finset ℕ) := by
        simp [Finset.disjoint_left]
        <;> omega
      rw [h2, Finset.prod_union h3, Finset.prod_singleton]
      rw [ih h (fun k hk => hpos k (by omega))]
      have hfm : 0 < f m := hpos m (by omega)
      have hfn : 0 < f n := hpos n (by omega)
      field_simp [hfm.ne', hfn.ne'] <;> ring
    · have hm : m = n + 1 := by omega
      simp [hm, Finset.Ico_eq_empty]
      <;> have h : f (n + 1) / f (n + 1) = 1 := by
        have hpos' : 0 < f (n + 1) := hpos (n + 1) (by omega)
        exact div_self hpos'.ne'
      exact h.symm

/-- Telescoping product over all `Fin n`. -/
lemma prod_fin_telescoping {n : ℕ} (f : ℕ → ℝ) (hpos : ∀ k ≤ n, 0 < f k) :
    ∏ j : Fin n, f (j.val + 1) / f j.val = f n / f 0 := by
  let g : ℕ → ℝ := fun i => f (i + 1) / f i
  have h_inj : Set.InjOn (fun (j : Fin n) => j.val) (Finset.univ : Finset (Fin n)) :=
    fun j _ k _ h => Fin.ext h
  have h_image : (Finset.univ : Finset (Fin n)).image (fun j => j.val) = Finset.range n := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨j, _, rfl⟩; exact j.is_lt
    · intro hi; exact ⟨⟨i, hi⟩, by simp⟩
  have h1 : (∏ j : Fin n, f (j.val + 1) / f j.val) = ∏ j ∈ (Finset.univ : Finset (Fin n)), g (j.val) := by rfl
  rw [h1]
  have h2 : ∏ j ∈ (Finset.univ : Finset (Fin n)), g (j.val) =
      ∏ i ∈ (Finset.univ : Finset (Fin n)).image (fun j => j.val), g i :=
    (Finset.prod_image h_inj).symm
  rw [h2, h_image]
  exact prod_range_div_real n f hpos

/-- Telescoping product over `Fin n \ {0}`. -/
lemma prod_fin_erase0_telescoping {n : ℕ} (hn : 1 ≤ n)
    (f : ℕ → ℝ) (hpos : ∀ k ≤ n, 0 < f k) :
    ∏ j ∈ (Finset.univ.erase (⟨0, by omega⟩ : Fin n)), f (j.val + 1) / f j.val =
    f n / f 1 := by
  let zero : Fin n := ⟨0, by omega⟩
  let g : ℕ → ℝ := fun i => f (i + 1) / f i
  have h_inj : Set.InjOn (fun (j : Fin n) => j.val) (Finset.univ.erase zero) :=
    fun j _ k _ h => Fin.ext h
  have h_image : (Finset.univ.erase zero).image (fun j => j.val) = Finset.Ico 1 n := by
    ext i
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨j, ⟨hj_ne, _⟩, rfl⟩
      have h_j_pos : 0 < j.val := by
        by_contra h; have h' : j.val = 0 := by omega
        have h'' : j = zero := by apply Fin.ext; simp [zero, h']
        exact hj_ne h''
      exact ⟨by omega, j.is_lt⟩
    · rintro ⟨hi_pos, hi_lt⟩
      refine ⟨⟨i, hi_lt⟩, ⟨?_, by simp⟩, by simp⟩
      intro h
      have h5 : (⟨i, hi_lt⟩ : Fin n).val = zero.val := by rw [h]
      simp [zero] at h5 <;> omega
  have h1 : (∏ j ∈ (Finset.univ.erase zero), f (j.val + 1) / f j.val) =
      ∏ j ∈ (Finset.univ.erase zero), g (j.val) := by rfl
  rw [h1]
  have h2 : ∏ j ∈ (Finset.univ.erase zero), g (j.val) =
      ∏ i ∈ (Finset.univ.erase zero).image (fun j => j.val), g i :=
    (Finset.prod_image h_inj).symm
  rw [h2, h_image]
  exact prod_Ico_div_real f (by omega) hpos

/-- OS equation (88): tail contains non-bad scale → `δbar ≤ δ^τ`. -/
lemma tail_nonbad_deltabar_le_deltaτ
    {n k : ℕ} (hn : 2 ≤ n) {τ : ℝ} (hτ_pos : 0 < τ)
    (Δ : Fin (n + 1) → ℝ) (scaleClass : Fin n → ScaleClass)
    (hΔ_pos : ∀ i, 0 < Δ i)
    (hΔ_strict : ∀ i : Fin n, Δ (Fin.succ i) < Δ i.castSucc)
    (h_scale_ratio : ∀ j : Fin n, ¬(scaleClass j).isBad →
        Δ (Fin.succ j) / Δ j.castSucc ≤ Real.rpow (dyadicDelta k) τ)
    (δbar : ℝ) (hδbar_eq : δbar = Δ (Fin.last n) / Δ 1)
    (h_exists : ∃ j, j ∈ (Finset.univ.erase (⟨0, by omega⟩ : Fin n)) ∧ ¬(scaleClass j).isBad) :
    δbar ≤ Real.rpow (dyadicDelta k) τ := by
  let zero : Fin n := ⟨0, by omega⟩
  rcases h_exists with ⟨j_good, hj_mem, hj_not_bad⟩
  let S := (Finset.univ.erase zero).erase j_good
  have h_disj : Disjoint {j_good} S := by
    simp [S, Finset.disjoint_left]
  have h_union : {j_good} ∪ S = (Finset.univ.erase zero) := by
    ext x
    simp only [S, Finset.mem_union, Finset.mem_singleton, Finset.mem_erase, Finset.mem_univ, true_and]
    constructor
    · rintro (h_eq | h_S)
      · have h_jg_ne_zero : j_good ≠ zero := (Finset.mem_erase.mp hj_mem).1
        have h_x_ne_zero : x ≠ zero := by rw [h_eq]; exact h_jg_ne_zero
        exact ⟨h_x_ne_zero, trivial⟩
      · exact h_S.2
    · intro h
      by_cases hx : x = j_good
      · exact Or.inl hx
      · exact Or.inr ⟨hx, h⟩
  have h_le_one : ∀ j ∈ S, Δ (Fin.succ j) / Δ j.castSucc ≤ 1 := by
    intro j _
    have h4 : Δ (Fin.succ j) < Δ j.castSucc := hΔ_strict j
    have h5 : 0 < Δ j.castSucc := hΔ_pos j.castSucc
    exact (div_le_one h5).mpr h4.le
  have h_prod_S_le_one : (∏ j ∈ S, Δ (Fin.succ j) / Δ j.castSucc) ≤ 1 := by
    apply Finset.prod_le_one
    · intro j _
      have hpos1 : 0 < Δ (Fin.succ j) := hΔ_pos (Fin.succ j)
      have hpos2 : 0 < Δ j.castSucc := hΔ_pos j.castSucc
      exact (div_pos hpos1 hpos2).le
    · intro j hj; exact h_le_one j hj
  have h_ratio_good : Δ (Fin.succ j_good) / Δ j_good.castSucc ≤ Real.rpow (dyadicDelta k) τ :=
    h_scale_ratio j_good hj_not_bad
  let f : ℕ → ℝ := fun v =>
    if h : v < n + 1 then Δ ⟨v, h⟩ else 1
  have hf_pos : ∀ k ≤ n, 0 < f k := by
    intro k hk
    have hlt : k < n + 1 := by omega
    simp only [f, dif_pos hlt]
    exact hΔ_pos _
  have h_eq1 : ∀ (j : Fin n), Δ (Fin.succ j) / Δ j.castSucc = f (j.val + 1) / f j.val := by
    intro j
    have h1 : j.val + 1 < n + 1 := by omega
    have h2 : j.val < n + 1 := by omega
    simp only [f, dif_pos h1, dif_pos h2] <;> rfl
  have h_telescoping : (∏ j ∈ (Finset.univ.erase zero), Δ (Fin.succ j) / Δ j.castSucc) =
      Δ (Fin.last n) / Δ 1 := by
    have h : (∏ j ∈ (Finset.univ.erase zero), Δ (Fin.succ j) / Δ j.castSucc) =
        ∏ j ∈ (Finset.univ.erase zero), f (j.val + 1) / f j.val := by
      apply Finset.prod_congr rfl; intro j _; exact h_eq1 j
    rw [h]
    have h2 := prod_fin_erase0_telescoping (by omega) f hf_pos
    have hfn : f n = Δ (Fin.last n) := by
      have hlt : n < n + 1 := by omega
      simp [f, hlt, Fin.last] <;> rfl
    have hf1 : f 1 = Δ 1 := by
      have h1lt : 1 < n + 1 := by omega
      unfold f
      rw [dif_pos h1lt]
      have h_eq : (1 : Fin (n + 1)) = ⟨1, h1lt⟩ := by
        apply Fin.ext
        have h : ((1 : Fin (n + 1)) : ℕ) = 1 := by
          simp [Nat.mod_eq_of_lt h1lt]
        simpa using h
      rw [h_eq]
    rw [h2, hfn, hf1]
  have hδbar_eq2 : δbar = (∏ j ∈ (Finset.univ.erase zero), Δ (Fin.succ j) / Δ j.castSucc) := by
    exact hδbar_eq.trans h_telescoping.symm
  rw [hδbar_eq2]
  have h_prod_split : (∏ j ∈ (Finset.univ.erase zero), Δ (Fin.succ j) / Δ j.castSucc) =
      (Δ (Fin.succ j_good) / Δ j_good.castSucc) * (∏ j ∈ S, Δ (Fin.succ j) / Δ j.castSucc) := by
    have h4 : (Finset.univ.erase zero) = {j_good} ∪ S := h_union.symm
    rw [h4, Finset.prod_union h_disj, Finset.prod_singleton]
    <;> rfl
  rw [h_prod_split]
  have hδk_pos : 0 < dyadicDelta k := by
    simp [dyadicDelta] <;> positivity
  have h_rpow_nonneg : 0 ≤ Real.rpow (dyadicDelta k) τ :=
    Real.rpow_nonneg hδk_pos.le τ
  have h_pos2 : 0 ≤ ∏ j ∈ S, Δ (Fin.succ j) / Δ j.castSucc := by
    apply Finset.prod_nonneg
    intro j _; exact (div_pos (hΔ_pos _) (hΔ_pos _)).le
  have h_main_ineq : (Δ (Fin.succ j_good) / Δ j_good.castSucc) * (∏ j ∈ S, Δ (Fin.succ j) / Δ j.castSucc) ≤
      (Real.rpow (dyadicDelta k) τ) * 1 :=
    mul_le_mul h_ratio_good h_prod_S_le_one h_pos2 h_rpow_nonneg
  have h_final : (Real.rpow (dyadicDelta k) τ) * 1 = Real.rpow (dyadicDelta k) τ := mul_one _
  exact h_main_ineq.trans_eq h_final

/-- Simplified combination for the all-tail-bad case. -/
lemma combine_bounds_all_bad
    {δ Δ δbar : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδbar_pos : 0 < δbar) (hδbar_lt_one : δbar < 1)
    (hδ_eq : δ = Δ * δbar)
    {s ε_N : ℝ} (hs : 0 < s) (hs1 : s < 1) (hεN : 0 < ε_N)
    {C_coarse C'_coarse C C' : ℝ}
    (hC_coarse_nonneg : 0 ≤ C_coarse)
    (hC'_coarse_nonneg : 0 ≤ C'_coarse)
    {K : ℝ} (hK_ge1 : 1 ≤ K)
    {A α : ℝ} (hA_pos : 0 < A) (hα_pos : 0 < α)
    (hK_poly : K ≤ A * (Real.log (1 / δ)) ^ α)
    (hL_ge1 : 1 ≤ Real.log (1 / δ))
    (hL_ge_A : Real.log (1 / δ) ≥ A)
    (lam : ℝ) (hlam_pos : 0 < lam)
    (hC'_coarse_le_C' : C'_coarse ≤ C')
    (C : ℝ) (hC_pos : 0 < C)
    (hC_ge : C ≥ (1 + α) * (C'_coarse + 1) + C_coarse) :
    Real.rpow (Real.log (1 / Δ)) (-C_coarse) *
    Real.rpow K (-(C'_coarse + 1)) *
    Real.rpow δ (C'_coarse * lam) ≥
    Real.rpow (Real.log (1 / δ)) (-C) *
    Real.rpow δ (C' * lam) *
    Real.rpow δbar (1 - s + ε_N) := by
  set L : ℝ := Real.log (1 / δ) with hL_def
  have hK_pos : 0 < K := by linarith
  have hA_nonneg : 0 ≤ A := by linarith
  have h_logΔ_pos : 0 < Real.log (1 / Δ) := Real.log_pos (by apply one_lt_one_div <;> linarith)
  have h_logΔ_le_L : Real.log (1 / Δ) ≤ L := by
    have h1 : δ ≤ Δ := by rw [hδ_eq]; exact mul_le_of_le_one_right hΔ_pos.le hδbar_lt_one.le
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
    · have hC_pos : 0 < C_coarse := lt_of_le_of_ne hC_coarse_nonneg (Ne.symm hC)
      exact h_anti (Real.log (1 / Δ)) L (-C_coarse) h_logΔ_pos h_logΔ_le_L (by linarith)
  have hC'_coarse_plus_one_pos : 0 < C'_coarse + 1 := by linarith
  have h3 : K ^ (-(C'_coarse + 1)) ≥ (A * L ^ α) ^ (-(C'_coarse + 1)) :=
    h_anti K (A * L ^ α) (-(C'_coarse + 1)) hK_pos hK_poly (by linarith [hC'_coarse_plus_one_pos])
  have h4 : (A * L ^ α) ^ (-(C'_coarse + 1)) =
      A ^ (-(C'_coarse + 1)) * (L ^ α) ^ (-(C'_coarse + 1)) := by
    rw [Real.mul_rpow hA_nonneg (by positivity)]
  have h5 : (L ^ α) ^ (-(C'_coarse + 1)) = L ^ (α * (-(C'_coarse + 1))) := by
    rw [← Real.rpow_mul (by linarith)] <;> ring
  have h6 : A ^ (-(C'_coarse + 1)) ≥ L ^ (-(C'_coarse + 1)) :=
    h_anti A L (-(C'_coarse + 1)) hA_pos hL_ge_A (by linarith [hC'_coarse_plus_one_pos])
  have h_log_bound : (Real.log (1 / Δ)) ^ (-C_coarse) * K ^ (-(C'_coarse + 1)) ≥ L ^ (-C) := by
    calc (Real.log (1 / Δ)) ^ (-C_coarse) * K ^ (-(C'_coarse + 1))
      ≥ L ^ (-C_coarse) * ((A * L ^ α) ^ (-(C'_coarse + 1))) := by gcongr
    _ = L ^ (-C_coarse) * (A ^ (-(C'_coarse + 1)) * L ^ (α * (-(C'_coarse + 1)))) := by rw [h4, h5]
    _ ≥ L ^ (-C_coarse) * (L ^ (-(C'_coarse + 1)) * L ^ (α * (-(C'_coarse + 1)))) := by gcongr
    _ = L ^ ((-C_coarse) + (-(C'_coarse + 1)) + (α * (-(C'_coarse + 1)))) := by
        rw [← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith)] <;> ring_nf
    _ = L ^ (-((1 + α) * (C'_coarse + 1) + C_coarse)) := by ring_nf
    _ ≥ L ^ (-C) := Real.rpow_le_rpow_of_exponent_le hL_ge1 (by linarith)
  have h_exp1 : C'_coarse * lam ≤ C' * lam := by gcongr
  have hδ_pow : δ ^ (C'_coarse * lam) ≥ δ ^ (C' * lam) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h_exp1
  have h_1s_nonneg : 0 ≤ 1 - s + ε_N := by linarith
  have hδbar_pow_le_one : δbar ^ (1 - s + ε_N) ≤ 1 := by
    have h_exp : (0 : ℝ) ≤ 1 - s + ε_N := h_1s_nonneg
    have h : δbar ^ (1 - s + ε_N) ≤ δbar ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hδbar_pos hδbar_lt_one.le h_exp
    have h0 : δbar ^ (0 : ℝ) = 1 := by simp
    rw [h0] at h
    exact h
  have h_pos_prod : 0 ≤ L ^ (-C) * δ ^ (C' * lam) := by positivity
  have h_final_step : L ^ (-C) * δ ^ (C' * lam) ≥
      L ^ (-C) * δ ^ (C' * lam) * δbar ^ (1 - s + ε_N) := by
    have h : L ^ (-C) * δ ^ (C' * lam) * δbar ^ (1 - s + ε_N) ≤
        L ^ (-C) * δ ^ (C' * lam) * 1 := by
      gcongr <;> exact hδbar_pow_le_one
    simpa using h
  calc (Real.log (1 / Δ)) ^ (-C_coarse) * K ^ (-(C'_coarse + 1)) * δ ^ (C'_coarse * lam)
    ≥ L ^ (-C) * δ ^ (C'_coarse * lam) := by gcongr
  _ ≥ L ^ (-C) * δ ^ (C' * lam) := by gcongr
  _ ≥ L ^ (-C) * δ ^ (C' * lam) * δbar ^ (1 - s + ε_N) := h_final_step

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
