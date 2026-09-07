module

/-
  Coarse Branch Exponent Algebra (Revised)

  Takes ratio data from coarse_two_case_ratio and fine_cor25_producer,
  combines with B1 product inequality and multiplicity bound,
  and proves N₀ ≥ δ^{-(2s+netGain)}.

  Does NOT assume MΔ=1. Both normalized ratios contribute s/2 each.

  Whiteprint node: CombiningTheoremRework/coarse_branch_algebra
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section6.Types
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.B1Integration
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.SourceFacingTheorem61

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.Bridge
open DirecretisedFurstenbergEstimate.Section6
open DirecretisedFurstenbergEstimate.RegularIncidence

/-- Corrected coarse branch algebra using BOTH normalized ratios.

    Product inequality: K * N₀ * MΔ * MQ ≥ NΔ * NQ * M
    ⟹ N₀ ≥ (NΔ/MΔ) * (NQ/MQ) * M / K

    Ratio bounds:
    - coarseData.hcoarse: NΔ/MΔ ≥ δ^{-(s/2 + coarseGain)}
    - fineData.hfine:    NQ/MQ ≥ δ^{-(s/2 - localLoss)}
    - hM_lower:          M ≥ δ^{-s + lambda + ρ_M}
    - hK_polylog:        1/K ≥ δ^{loss_K}

    Product exponent:
      -(s/2+coarseGain) + -(s/2-localLoss) + (-s+lambda+ρ_M) + loss_K
      = -2s - coarseGain + localLoss + lambda + ρ_M + loss_K

    Budget condition:
      netGain ≤ coarseGain - localLoss - lambda - ρ_M - loss_K
-/
lemma coarse_branch_algebra
    {δ s netGain lambda ρ_M loss_K : ℝ}
    {K N₀ M : ℕ}
    (coarseData : CoarseRatioData δ s)
    (fineData : FineCor25Data δ s)
    (hK_ge1 : 1 ≤ (K : ℝ))
    (hM_pos : 0 < (M : ℝ))
    (hM_lower : (M : ℝ) ≥ δ ^ (-s + lambda + ρ_M))
    (hK_polylog : (K : ℝ) ≤ δ ^ (-loss_K))
    (h_bridge : (K : ℝ) * (N₀ : ℝ) * coarseData.coarseMultiplicity * fineData.localMultiplicity ≥
        coarseData.coarseCount * fineData.localCount * (M : ℝ))
    (h_budget : netGain ≤ coarseData.coarseGain - fineData.localLoss - lambda - ρ_M - loss_K)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) :
    (N₀ : ENNReal) ≥ ENNReal.ofReal (δ ^ (-(2 * s + netGain))) := by
  set NΔ : ℝ := coarseData.coarseCount with hNΔ_def
  set MΔ : ℝ := coarseData.coarseMultiplicity with hMΔ_def
  set NQ : ℝ := fineData.localCount with hNQ_def
  set MQ : ℝ := fineData.localMultiplicity with hMQ_def
  set coarseGain : ℝ := coarseData.coarseGain with hcoarseGain_def
  set localLoss : ℝ := fineData.localLoss with hlocalLoss_def

  have hMΔ_pos : 0 < MΔ := coarseData.hMΔ_pos
  have hMQ_pos : 0 < MQ := fineData.hMQ_pos
  have hK_pos : 0 < (K : ℝ) := by linarith
  have hcoarseGain_pos : 0 < coarseGain := coarseData.hgainΔ
  have hlocalLoss_nonneg : 0 ≤ localLoss := fineData.hlossQ

  have hNΔ_nonneg : 0 ≤ NΔ := by
    have h : δ ^ (-(s / 2 + coarseGain)) ≤ NΔ / MΔ := coarseData.hcoarse
    have hpos : 0 < δ ^ (-(s / 2 + coarseGain)) := Real.rpow_pos_of_pos hδ_pos _
    have h' : 0 ≤ NΔ / MΔ := by linarith
    have h'' : 0 ≤ NΔ := by
      by_contra h3
      have h4 : NΔ < 0 := by linarith
      have h5 : NΔ / MΔ < 0 := by exact div_neg_of_neg_of_pos h4 hMΔ_pos
      linarith
    exact h''

  have hNQ_nonneg : 0 ≤ NQ := by
    have h : δ ^ (-(s / 2 - localLoss)) ≤ NQ / MQ := fineData.hfine
    have hpos : 0 < δ ^ (-(s / 2 - localLoss)) := Real.rpow_pos_of_pos hδ_pos _
    have h' : 0 ≤ NQ / MQ := by linarith
    have h'' : 0 ≤ NQ := by
      by_contra h3
      have h4 : NQ < 0 := by linarith
      have h5 : NQ / MQ < 0 := by exact div_neg_of_neg_of_pos h4 hMQ_pos
      linarith
    exact h''

  have hloss_K_nonneg : 0 ≤ loss_K := by
    have h1 : (1 : ℝ) ≤ (K : ℝ) := hK_ge1
    have h2 : (K : ℝ) ≤ δ ^ (-loss_K) := hK_polylog
    have h3 : (1 : ℝ) ≤ δ ^ (-loss_K) := by linarith
    by_contra h4
    have h5 : -loss_K > 0 := by linarith
    have h6 : δ ^ (-loss_K) < 1 := by
      apply Real.rpow_lt_one (by linarith) (by linarith) h5
    linarith

  -- Step 1: N₀ ≥ (NΔ/MΔ) * (NQ/MQ) * M / K
  have h1 : (N₀ : ℝ) ≥ (NΔ / MΔ) * (NQ / MQ) * (M : ℝ) / (K : ℝ) := by
    have h_product : NΔ * NQ * (M : ℝ) =
        (NΔ / MΔ) * (NQ / MQ) * (M : ℝ) * (MΔ * MQ) := by
      field_simp [hMΔ_pos.ne', hMQ_pos.ne'] <;> ring
    rw [h_product] at h_bridge
    have h_div : (K : ℝ) * (N₀ : ℝ) ≥ (NΔ / MΔ) * (NQ / MQ) * (M : ℝ) := by
      have h : (K : ℝ) * (N₀ : ℝ) * (MΔ * MQ) ≥
          ((NΔ / MΔ) * (NQ / MQ) * (M : ℝ)) * (MΔ * MQ) := by
        simpa [mul_assoc] using h_bridge
      have h_pos : 0 < MΔ * MQ := mul_pos hMΔ_pos hMQ_pos
      exact le_of_mul_le_mul_right h h_pos
    have h_final : (N₀ : ℝ) ≥ ((NΔ / MΔ) * (NQ / MQ) * (M : ℝ)) / (K : ℝ) := by
      calc (N₀ : ℝ)
        = ((K : ℝ) * (N₀ : ℝ)) / (K : ℝ) := by field_simp [hK_pos.ne'] <;> ring
      _ ≥ ((NΔ / MΔ) * (NQ / MQ) * (M : ℝ)) / (K : ℝ) := by gcongr
    exact h_final

  -- Step 2: 1/K ≥ δ^{loss_K}
  have h2 : 1 / (K : ℝ) ≥ δ ^ loss_K := by
    have hK2 : (K : ℝ) ≤ δ ^ (-loss_K) := hK_polylog
    have h_pos1 : 0 < (K : ℝ) := hK_pos
    have h_pos2 : 0 < δ ^ (-loss_K) := Real.rpow_pos_of_pos hδ_pos _
    have h3 : 1 / (K : ℝ) ≥ 1 / δ ^ (-loss_K) := by
      gcongr
    have h4 : 1 / δ ^ (-loss_K) = δ ^ loss_K := by
      have h5 : δ ^ loss_K * δ ^ (-loss_K) = 1 := by
        have h6 : δ ^ loss_K * δ ^ (-loss_K) = δ ^ (loss_K + (-loss_K)) := by
          rw [←Real.rpow_add hδ_pos] <;> ring
        rw [h6]
        have h7 : loss_K + (-loss_K) = 0 := by ring
        rw [h7]
        simp
      have h6 : 0 < δ ^ (-loss_K) := h_pos2
      field_simp [h6.ne'] <;> linarith
    rw [h4] at h3
    exact h3

  -- Step 3: Multiply lower bounds
  have h3 : (NΔ / MΔ) * (NQ / MQ) * (M : ℝ) / (K : ℝ) ≥
      δ ^ (-(s / 2 + coarseGain)) * δ ^ (-(s / 2 - localLoss)) *
      δ ^ (-s + lambda + ρ_M) * δ ^ loss_K := by
    have h_coarse_ratio : NΔ / MΔ ≥ δ ^ (-(s / 2 + coarseGain)) := coarseData.hcoarse
    have h_fine_ratio : NQ / MQ ≥ δ ^ (-(s / 2 - localLoss)) := fineData.hfine
    have h_M : (M : ℝ) ≥ δ ^ (-s + lambda + ρ_M) := hM_lower
    have h_invK : 1 / (K : ℝ) ≥ δ ^ loss_K := h2
    have h_pos1 : 0 ≤ δ ^ (-(s / 2 + coarseGain)) := by positivity
    have h_pos2 : 0 ≤ δ ^ (-(s / 2 - localLoss)) := by positivity
    have h_pos3 : 0 ≤ δ ^ (-s + lambda + ρ_M) := by positivity
    have h_pos4 : 0 ≤ δ ^ loss_K := by positivity
    calc (NΔ / MΔ) * (NQ / MQ) * (M : ℝ) / (K : ℝ)
      = (NΔ / MΔ) * (NQ / MQ) * (M : ℝ) * (1 / (K : ℝ)) := by ring
    _ ≥ δ ^ (-(s / 2 + coarseGain)) * δ ^ (-(s / 2 - localLoss)) *
          δ ^ (-s + lambda + ρ_M) * δ ^ loss_K := by
      gcongr <;> linarith

  -- Step 4: Combine exponents
  have h4 : δ ^ (-(s / 2 + coarseGain)) * δ ^ (-(s / 2 - localLoss)) *
      δ ^ (-s + lambda + ρ_M) * δ ^ loss_K =
      δ ^ (-2 * s - coarseGain + localLoss + lambda + ρ_M + loss_K) := by
    rw [←Real.rpow_add hδ_pos, ←Real.rpow_add hδ_pos, ←Real.rpow_add hδ_pos] <;> ring_nf

  -- Step 5: Exponent budget
  have h5 : -2 * s - coarseGain + localLoss + lambda + ρ_M + loss_K ≤ -(2 * s + netGain) := by
    linarith [h_budget]

  -- Step 6: Since δ < 1, smaller exponent means larger value
  have h6 : δ ^ (-2 * s - coarseGain + localLoss + lambda + ρ_M + loss_K) ≥
      δ ^ (-(2 * s + netGain)) := by
    apply Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h5

  have h7 : (N₀ : ℝ) ≥ δ ^ (-(2 * s + netGain)) := by
    calc (N₀ : ℝ)
      ≥ (NΔ / MΔ) * (NQ / MQ) * (M : ℝ) / (K : ℝ) := h1
    _ ≥ δ ^ (-2 * s - coarseGain + localLoss + lambda + ρ_M + loss_K) := by
      rw [h4] at h3
      exact h3
    _ ≥ δ ^ (-(2 * s + netGain)) := h6

  have h8 : 0 ≤ δ ^ (-(2 * s + netGain)) := by positivity
  exact_mod_cast h7

/-- config card → original Ncover scaling inversion.

    If config.T₀.card ≤ δ^{-ρ_T} · Ncover(δ, T) and config.T₀.card ≥ A,
    then Ncover(δ, T) ≥ A · δ^{ρ_T}. -/
lemma config_card_to_original_ncover
    {n : ℕ} {δ ρ_T s C : ℝ} {M : ℕ} (hρ_T_nonneg : 0 ≤ ρ_T)
    {T : Set AffineLine} {config : MainConfig n s C M} {A : ℝ} (hA_nonneg : 0 ≤ A)
    (hT0_upper : (config.T₀.card : ENNReal) ≤
        ENNReal.ofReal ((DiscretisedFurstenbergEstimate.dyadicDelta n) ^ (-ρ_T)) * RegularIncidence.Ncover δ T)
    (h_configCard_lower : (config.T₀.card : ENNReal) ≥ ENNReal.ofReal A) :
    RegularIncidence.Ncover δ T ≥ ENNReal.ofReal (A * (DiscretisedFurstenbergEstimate.dyadicDelta n) ^ ρ_T) := by
  set δn : ℝ := DiscretisedFurstenbergEstimate.dyadicDelta n with hδn_def
  have hδn_pos : 0 < δn := DiscretisedFurstenbergEstimate.dyadicDelta_pos n
  have h1 : 0 ≤ δn ^ (-ρ_T) := by positivity
  have h2 : 0 ≤ δn ^ ρ_T := by positivity
  have h3 : ENNReal.ofReal (δn ^ ρ_T) * (config.T₀.card : ENNReal) ≤
      ENNReal.ofReal (δn ^ ρ_T) * (ENNReal.ofReal (δn ^ (-ρ_T)) * RegularIncidence.Ncover δ T) :=
    by gcongr <;> exact hT0_upper
  have h4 : ENNReal.ofReal (δn ^ ρ_T) * ENNReal.ofReal (δn ^ (-ρ_T)) = 1 := by
    have h5 : δn ^ ρ_T * δn ^ (-ρ_T) = 1 := by
      have h6 : δn ^ ρ_T * δn ^ (-ρ_T) = δn ^ (ρ_T + (-ρ_T)) := by
        rw [←Real.rpow_add hδn_pos] <;> ring
      have h7 : ρ_T + (-ρ_T) = 0 := by ring
      rw [h6, h7]
      exact Real.rpow_zero δn
    rw [←ENNReal.ofReal_mul h2, h5] <;> simp
  have h5 : ENNReal.ofReal (δn ^ ρ_T) * (ENNReal.ofReal (δn ^ (-ρ_T)) * RegularIncidence.Ncover δ T) =
      RegularIncidence.Ncover δ T := by
    rw [←mul_assoc, h4, one_mul]
  rw [h5] at h3
  have h6 : ENNReal.ofReal (δn ^ ρ_T) * (config.T₀.card : ENNReal) ≤ RegularIncidence.Ncover δ T := h3
  have h7 : ENNReal.ofReal (δn ^ ρ_T) * ENNReal.ofReal A ≤
      ENNReal.ofReal (δn ^ ρ_T) * (config.T₀.card : ENNReal) :=
    by gcongr <;> exact h_configCard_lower
  have h_mul : ENNReal.ofReal ((δn ^ ρ_T) * A) =
      ENNReal.ofReal (δn ^ ρ_T) * ENNReal.ofReal A := by
    exact ENNReal.ofReal_mul h2
  have h8 : ENNReal.ofReal (δn ^ ρ_T) * ENNReal.ofReal A =
      ENNReal.ofReal ((δn ^ ρ_T) * A) :=
    h_mul.symm
  have h9 : (δn ^ ρ_T) * A = A * δn ^ ρ_T := by ring
  have h10 : ENNReal.ofReal (A * δn ^ ρ_T) ≤ ENNReal.ofReal (δn ^ ρ_T) * (config.T₀.card : ENNReal) := by
    have h11 : ENNReal.ofReal (A * δn ^ ρ_T) = ENNReal.ofReal (δn ^ ρ_T) * ENNReal.ofReal A := by
      have h12 : A * δn ^ ρ_T = (δn ^ ρ_T) * A := by ring
      rw [h12]
      exact h_mul
    rw [h11]
    exact h7
  exact le_trans h10 h6

end DirecretisedFurstenbergEstimate.SourceFacingTheorem61

end
