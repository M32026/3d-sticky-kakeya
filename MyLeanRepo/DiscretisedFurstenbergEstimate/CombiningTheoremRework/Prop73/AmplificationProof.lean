module

/-
  AmplificationProof — Prove the outer amplification absorption.

  Given a uniform B1 polylog bound on the density loss K and sufficient
  smallness of δ, proves that the tail-consumer amplification factor A_amp
  is absorbed by the logarithmic exponent increase from C_P to C_P + 2*C_n.

  Specifically proves:
    A_amp * log(1/δ_coarse)^C_P ≤ log(1/δ)^(C_P + 2*C_n)

  where A_amp = 9 * 2 * K * (24 * log(1/δ) / n_fine)^n_fine * 4^n_fine.

  Whiteprint node: combining_theorem_rework / outer_amplification
  Status: Complete. 0 errors, 0 sorrys.
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

/-- Prove the outer amplification absorption from a uniform B1 bound.

    Given:
    - K ≤ log(1/δ)^C_K (uniform B1 polylog density bound)
    - δ ≤ δ_coarse^τ (scale separation)
    - 2*C_n > C_K + n_fine (C_n chosen large enough)
    - smallness condition on log(1/δ)

    Concludes:
    A_amp * log(1/δ_coarse)^C_P ≤ log(1/δ)^(C_P + 2*C_n)
-/
lemma outer_amplification
    {n_fine : ℕ} (hn_fine_pos : 0 < n_fine)
    (δ δ_coarse : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hδ_coarse_pos : 0 < δ_coarse) (hδ_coarse_lt_one : δ_coarse < 1)
    (τ : ℝ) (hτ_pos : 0 < τ) (hτ_lt_one : τ < 1)
    (h_scale_sep : δ ≤ δ_coarse ^ τ)
    (K C_K C_P C_n : ℝ)
    (hK_pos : 0 < K)
    (hCK_nonneg : 0 ≤ C_K)
    (hCP : 1 ≤ C_P)
    (hCn_large : C_K + (n_fine : ℝ) < 2 * C_n)
    (hK_bound : K ≤ Real.log (1 / δ) ^ C_K)
    (hL_ge_one : 1 ≤ Real.log (1 / δ))
    (h_small :
      (18 * (24 / (n_fine : ℝ)) ^ n_fine * (4 : ℝ) ^ n_fine * τ ^ (-C_P))
      ≤ Real.log (1 / δ) ^ (2 * C_n - C_K - (n_fine : ℝ))) :
    (9 * 2 * (K * (24 * Real.log (1 / δ) / (n_fine : ℝ)) ^ n_fine) * (4 : ℝ)^n_fine) *
    (Real.log (1 / δ_coarse)) ^ C_P ≤
    (Real.log (1 / δ)) ^ (C_P + 2 * C_n) := by
  let L : ℝ := Real.log (1 / δ)
  let L_coarse : ℝ := Real.log (1 / δ_coarse)
  let C_unif : ℝ := 18 * (24 / (n_fine : ℝ)) ^ n_fine * (4 : ℝ) ^ n_fine

  have hL_pos : 0 < L := Real.log_pos (by
    have h : 1 < 1 / δ := by apply one_lt_one_div <;> linarith
    exact h)
  have hL_coarse_pos : 0 < L_coarse := Real.log_pos (by
    have h : 1 < 1 / δ_coarse := by apply one_lt_one_div <;> linarith
    exact h)
  have hC_unif_pos : 0 < C_unif := by positivity

  -- Step 1: Scale separation gives L_coarse ≤ L / τ
  have h1 : L_coarse ≤ L / τ := by
    have h2 : 1 / δ ≥ (1 / δ_coarse) ^ τ := by
      have h3 : 1 / δ ≥ 1 / (δ_coarse ^ τ) := by gcongr
      have h4 : 1 / (δ_coarse ^ τ) = (1 / δ_coarse) ^ τ := by
        have h41 : (δ_coarse ^ τ)⁻¹ = (δ_coarse⁻¹) ^ τ := (Real.inv_rpow hδ_coarse_pos.le τ).symm
        simpa [one_div] using h41
      rw [h4] at h3
      exact h3
    have h5 : L ≥ Real.log ((1 / δ_coarse) ^ τ) := Real.log_le_log (by positivity) h2
    have h6 : Real.log ((1 / δ_coarse) ^ τ) = τ * L_coarse := by
      rw [Real.log_rpow (by positivity)] <;> ring
    rw [h6] at h5
    have h7 : L ≥ τ * L_coarse := h5
    calc L_coarse
      = (τ * L_coarse) / τ := by field_simp [hτ_pos.ne'] <;> ring
    _ ≤ L / τ := by gcongr

  -- Step 2: A_amp ≤ C_unif * L^(C_K + n_fine)
  have h_factor1 : (24 * L / (n_fine : ℝ)) ^ n_fine =
      (24 / (n_fine : ℝ)) ^ n_fine * L ^ n_fine := by
    have h : (24 * L / (n_fine : ℝ)) = (24 / (n_fine : ℝ)) * L := by ring
    rw [h, mul_pow]
  have hA_amp_eq : (9 * 2 * (K * (24 * L / (n_fine : ℝ)) ^ n_fine) * (4 : ℝ)^n_fine) =
      C_unif * K * L ^ n_fine := by
    simp only [C_unif]
    rw [h_factor1] <;> ring
  have hA_amp_bound : (9 * 2 * (K * (24 * L / (n_fine : ℝ)) ^ n_fine) * (4 : ℝ)^n_fine) ≤
      C_unif * L ^ (C_K + (n_fine : ℝ)) := by
    rw [hA_amp_eq]
    have h12 : K * L ^ n_fine ≤ (L ^ C_K) * L ^ n_fine := by
      gcongr <;> exact hK_bound
    have h13 : (L ^ C_K) * L ^ n_fine = L ^ (C_K + (n_fine : ℝ)) := by
      have h14 : (L ^ n_fine : ℝ) = L ^ (n_fine : ℝ) := (Real.rpow_natCast L n_fine).symm
      rw [h14, ← Real.rpow_add hL_pos] <;> ring
    rw [h13] at h12
    have h15 : C_unif * K * L ^ n_fine = C_unif * (K * L ^ n_fine) := by ring
    rw [h15]
    exact mul_le_mul_of_nonneg_left h12 hC_unif_pos.le

  -- Step 3: L_coarse^C_P ≤ (L/τ)^C_P = τ^(-C_P) * L^C_P
  have h14 : L_coarse ^ C_P ≤ (L / τ) ^ C_P := by gcongr <;> linarith
  have h15 : (L / τ) ^ C_P = τ ^ (-C_P) * L ^ C_P := by
    have h16 : (L / τ) ^ C_P = L ^ C_P / τ ^ C_P := by
      rw [Real.div_rpow (by linarith) (by linarith)] <;> ring
    rw [h16]
    have h17 : L ^ C_P / τ ^ C_P = (τ ^ C_P)⁻¹ * L ^ C_P := by ring
    rw [h17]
    have h18 : (τ ^ C_P)⁻¹ = τ ^ (-C_P) := by
      rw [← Real.rpow_neg (by linarith)] <;> ring
    rw [h18] <;> ring

  -- Step 4: Combine
  have h16 : C_unif * L ^ (C_K + (n_fine : ℝ)) * L_coarse ^ C_P ≤
      C_unif * τ ^ (-C_P) * L ^ (C_K + (n_fine : ℝ) + C_P) := by
    calc C_unif * L ^ (C_K + (n_fine : ℝ)) * L_coarse ^ C_P
      ≤ C_unif * L ^ (C_K + (n_fine : ℝ)) * ((L / τ) ^ C_P) := by gcongr
    _ = C_unif * L ^ (C_K + (n_fine : ℝ)) * (τ ^ (-C_P) * L ^ C_P) := by rw [h15]
    _ = C_unif * τ ^ (-C_P) * L ^ (C_K + (n_fine : ℝ) + C_P) := by
      have h19 : L ^ (C_K + (n_fine : ℝ)) * L ^ C_P = L ^ (C_K + (n_fine : ℝ) + C_P) := by
        rw [← Real.rpow_add hL_pos] <;> ring
      have h20 : C_unif * L ^ (C_K + (n_fine : ℝ)) * (τ ^ (-C_P) * L ^ C_P) =
          C_unif * τ ^ (-C_P) * (L ^ (C_K + (n_fine : ℝ)) * L ^ C_P) := by ring
      rw [h20, h19] <;> ring

  have h_main : (9 * 2 * (K * (24 * L / (n_fine : ℝ)) ^ n_fine) * (4 : ℝ)^n_fine) * L_coarse ^ C_P ≤
      C_unif * τ ^ (-C_P) * L ^ (C_K + (n_fine : ℝ) + C_P) := by
    calc (9 * 2 * (K * (24 * L / (n_fine : ℝ)) ^ n_fine) * (4 : ℝ)^n_fine) * L_coarse ^ C_P
      ≤ C_unif * L ^ (C_K + (n_fine : ℝ)) * L_coarse ^ C_P := by gcongr
    _ ≤ C_unif * τ ^ (-C_P) * L ^ (C_K + (n_fine : ℝ) + C_P) := h16

  -- Step 5: Absorb C_unif * τ^(-C_P) using smallness
  have h19 : 0 < 2 * C_n - C_K - (n_fine : ℝ) := by linarith
  have h20 : C_unif * τ ^ (-C_P) ≤ L ^ (2 * C_n - C_K - (n_fine : ℝ)) := by
    have h_eq : C_unif = 18 * (24 / (n_fine : ℝ)) ^ n_fine * (4 : ℝ) ^ n_fine := by
      rfl
    rw [h_eq]
    exact h_small
  have h21 : C_unif * τ ^ (-C_P) * L ^ (C_K + (n_fine : ℝ) + C_P) ≤
      L ^ (C_P + 2 * C_n) := by
    have h22 : C_unif * τ ^ (-C_P) * L ^ (C_K + (n_fine : ℝ) + C_P) ≤
        L ^ (2 * C_n - C_K - (n_fine : ℝ)) * L ^ (C_K + (n_fine : ℝ) + C_P) := by
      gcongr <;> exact h20
    have h23 : L ^ (2 * C_n - C_K - (n_fine : ℝ)) * L ^ (C_K + (n_fine : ℝ) + C_P) =
        L ^ (C_P + 2 * C_n) := by
      rw [← Real.rpow_add hL_pos] <;> ring_nf
    rw [h23] at h22
    exact h22

  exact le_trans h_main h21

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
