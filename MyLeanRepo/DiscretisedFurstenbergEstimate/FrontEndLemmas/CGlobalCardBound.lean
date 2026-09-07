module

/-
  C_global_A2 cardinality bound via coarse failure + packing.

  This module provides the PACKING bound only. Orientation correction
  (swapLine, T_standard) is handled by bacon's TDeltaGlobalConstruction.

  Integration chain:
  1. bacon's `provenance_to_T_standard`: InParent → dist(toAffineLine U, ℓ_std) ≤ 10Δ
  2. bacon's `ncover_T_standard_eq`: Ncover(Δ, T_standard) = Ncover(Δ, T_oriented)
  3. `t_delta_card_bound_specialized`: |T_Delta_dyadic| ≤ Δ^{-(2s+3ε)}
  4. `c_global_card_le_t_delta_card`: subset → |C_global_A2| ≤ bound

  Uses `covering_movement_global_generalized`.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.CoveringMovementGeneralized
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas.CGlobalCardBound

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DyadicCardToNcover (toAffineLine)

/-- Packing constant K_pack for given slope bound B and movement C_move. -/
def kPack (B C_move : ℝ) : ℕ :=
  (2 * Nat.ceil (4 * (4 + B + 3 * B^2) * (C_move + 1)) + 1)^2

/-- Cardinality bound for a dyadic coarse tube family via
    `covering_movement_global_generalized` + coarse Ncover failure.

    T_standard is the swapLine image of T_oriented (handled by bacon's module).

    Given:
    - T_Delta has slope bound B, intercept bound 3
    - Each tube has provenance to T_standard: dist(toAffineLine U, ℓ_std) ≤ C_move*Δ
    - Ncover(Δ, T_standard) ≤ Δ^{-(2s + coarse_loss)}
    - K_pack ≤ Δ^{coarse_loss - 3ε} (constant absorption)

    Then: |T_Delta| ≤ Δ^{-(2s+3ε)}.
-/
lemma t_delta_card_bound {m : ℕ}
    (Δ : ℝ) (hΔ_eq : Δ = dyadicDelta m)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (s ε : ℝ) (hs_pos : 0 < s) (hε_pos : 0 < ε)
    (T_standard : Set AffineLine)
    (T_Delta : Finset (DyadicTube m))
    (B : ℝ) (hB_nonneg : 0 ≤ B)
    (h_slope : ∀ U ∈ T_Delta, |U.slope| ≤ B)
    (h_intercept : ∀ U ∈ T_Delta, |U.intercept| ≤ 3)
    (C_move : ℝ) (hC_move_nonneg : 0 ≤ C_move)
    (h_provenance : ∀ U ∈ T_Delta, ∃ (ℓ_std : AffineLine),
        ℓ_std ∈ T_standard ∧ dist (toAffineLine U) ℓ_std ≤ C_move * Δ)
    (coarse_loss : ℝ)
    (hNcover_coarse : Metric.externalCoveringNumber Δ.toNNReal T_standard ≤
        ENNReal.ofReal (Real.rpow Δ (-(2 * s + coarse_loss))))
    (h_absorb : (kPack B C_move : ℝ) ≤
        Real.rpow Δ (coarse_loss - 3 * ε)) :
    (T_Delta.card : ℝ) ≤ Real.rpow Δ (-(2 * s + 3 * ε)) := by
  let K_pack_nat : ℕ := kPack B C_move
  let K_pack : ℝ := (K_pack_nat : ℝ)
  have hK_nonneg : 0 ≤ K_pack := by positivity
  have hK_eq : (K_pack_nat : ENNReal) = ENNReal.ofReal K_pack := by
    simp [K_pack] <;> norm_cast
  have h_absorb' : K_pack ≤ Real.rpow Δ (coarse_loss - 3 * ε) := by
    simpa [K_pack, K_pack_nat, kPack] using h_absorb
  have h_scale : Δ < 2 * dyadicDelta m := by
    rw [hΔ_eq] <;> linarith [dyadicDelta_pos m]
  have h_main_raw : (T_Delta.card : ENNReal) ≤
      (K_pack_nat : ENNReal) * Metric.externalCoveringNumber Δ.toNNReal T_standard := by
    convert covering_movement_global_generalized
      (hδ_pos := hΔ_pos)
      (hC_move_nonneg := hC_move_nonneg)
      (hB_nonneg := hB_nonneg)
      (h_scale := h_scale)
      (T_oriented := T_standard)
      (T₀ := T_Delta)
      (hm := h_slope)
      (hb := h_intercept)
      (h_prov := h_provenance)
    <;> simp [K_pack_nat, kPack] <;> rfl
  have h_main_enn2 : (T_Delta.card : ENNReal) ≤
      ENNReal.ofReal K_pack * Metric.externalCoveringNumber Δ.toNNReal T_standard := by
    rw [hK_eq] at h_main_raw
    exact h_main_raw
  have h2 : (T_Delta.card : ENNReal) ≤
      ENNReal.ofReal K_pack *
        ENNReal.ofReal (Real.rpow Δ (-(2 * s + coarse_loss))) := by
    have h_rpow_nonneg : 0 ≤ Real.rpow Δ (-(2 * s + coarse_loss)) :=
      Real.rpow_nonneg hΔ_pos.le _
    have h_mul_le : ENNReal.ofReal K_pack * Metric.externalCoveringNumber Δ.toNNReal T_standard ≤
        ENNReal.ofReal K_pack * ENNReal.ofReal (Real.rpow Δ (-(2 * s + coarse_loss))) :=
      mul_le_mul_left' hNcover_coarse _
    exact h_main_enn2.trans h_mul_le
  have h_mul : ENNReal.ofReal K_pack *
        ENNReal.ofReal (Real.rpow Δ (-(2 * s + coarse_loss))) =
      ENNReal.ofReal (K_pack * Real.rpow Δ (-(2 * s + coarse_loss))) := by
    rw [ENNReal.ofReal_mul] <;> positivity
  rw [h_mul] at h2
  have h_exp_add : (coarse_loss - 3 * ε) + (-(2 * s + coarse_loss)) = -(2 * s + 3 * ε) := by ring
  have h5 : K_pack * Real.rpow Δ (-(2 * s + coarse_loss)) ≤
      Real.rpow Δ (-(2 * s + 3 * ε)) := by
    have h6 : K_pack ≤ Real.rpow Δ (coarse_loss - 3 * ε) := h_absorb'
    have h_rpow2_nonneg : 0 ≤ Real.rpow Δ (-(2 * s + coarse_loss)) :=
      Real.rpow_nonneg hΔ_pos.le _
    have h7 : Real.rpow Δ (coarse_loss - 3 * ε) *
          Real.rpow Δ (-(2 * s + coarse_loss)) =
        Real.rpow Δ ((coarse_loss - 3 * ε) + (-(2 * s + coarse_loss))) :=
      (Real.rpow_add hΔ_pos _ _).symm
    rw [h_exp_add] at h7
    have h8 : K_pack * Real.rpow Δ (-(2 * s + coarse_loss)) ≤
        Real.rpow Δ (coarse_loss - 3 * ε) * Real.rpow Δ (-(2 * s + coarse_loss)) :=
      mul_le_mul_of_nonneg_right h6 h_rpow2_nonneg
    rw [h7] at h8
    exact h8
  have h8 : (T_Delta.card : ENNReal) ≤
      ENNReal.ofReal (Real.rpow Δ (-(2 * s + 3 * ε))) :=
    h2.trans (ENNReal.ofReal_le_ofReal h5)
  have h10 : (T_Delta.card : ENNReal) = ENNReal.ofReal (T_Delta.card : ℝ) := by simp
  rw [h10] at h8
  have h_pos2 : 0 ≤ Real.rpow Δ (-(2 * s + 3 * ε)) := Real.rpow_nonneg hΔ_pos.le _
  have h_iff : ENNReal.ofReal (T_Delta.card : ℝ) ≤ ENNReal.ofReal (Real.rpow Δ (-(2 * s + 3 * ε))) ↔
      (T_Delta.card : ℝ) ≤ Real.rpow Δ (-(2 * s + 3 * ε)) :=
    ENNReal.ofReal_le_ofReal_iff h_pos2
  exact h_iff.mp h8

/-- Specialized cardinality bound with coarse_loss = 2*εA_int.

    εA_int = ε/25 (internal exponent after scale transfer).
    coarse_loss = 2*εA_int = 2ε/25.
    Absorption: K_pack ≤ Δ^(2*εA_int - 3*ε) = Δ^(-73ε/25).

    Given coarse Ncover failure on T_standard and K_pack absorption,
    produces |T_Delta| ≤ Δ^{-(2s+3ε)}.
-/
lemma t_delta_card_bound_specialized {m : ℕ}
    (Δ : ℝ) (hΔ_eq : Δ = dyadicDelta m)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (s ε : ℝ) (hs_pos : 0 < s) (hε_pos : 0 < ε)
    (T_standard : Set AffineLine)
    (T_Delta : Finset (DyadicTube m))
    (B : ℝ) (hB_nonneg : 0 ≤ B)
    (h_slope : ∀ U ∈ T_Delta, |U.slope| ≤ B)
    (h_intercept : ∀ U ∈ T_Delta, |U.intercept| ≤ 3)
    (C_move : ℝ) (hC_move_nonneg : 0 ≤ C_move)
    (h_provenance : ∀ U ∈ T_Delta, ∃ (ℓ_std : AffineLine),
        ℓ_std ∈ T_standard ∧ dist (toAffineLine U) ℓ_std ≤ C_move * Δ)
    (εA_int : ℝ) (hεA_int_eq : εA_int = ε / 25)
    (hNcover_coarse : Metric.externalCoveringNumber Δ.toNNReal T_standard ≤
        ENNReal.ofReal (Real.rpow Δ (-(2 * s + 2 * εA_int))))
    (h_absorb : (kPack B C_move : ℝ) ≤
        Real.rpow Δ (2 * εA_int - 3 * ε)) :
    (T_Delta.card : ℝ) ≤ Real.rpow Δ (-(2 * s + 3 * ε)) :=
  t_delta_card_bound Δ hΔ_eq hΔ_pos hΔ_lt_one s ε hs_pos hε_pos
    T_standard T_Delta B hB_nonneg h_slope h_intercept C_move hC_move_nonneg
    h_provenance (2 * εA_int) hNcover_coarse
    (by simpa [kPack] using h_absorb)

/-- Glue lemma: if C_global_A2 ⊆ T_Delta_global (as Finset AffineLine),
    then |C_global_A2| ≤ |T_Delta_global|.
-/
lemma c_global_card_le_t_delta_card
    (C_global_A2 T_Delta_global : Finset AffineLine)
    (h_sub : C_global_A2 ⊆ T_Delta_global) :
    C_global_A2.card ≤ T_Delta_global.card :=
  Finset.card_le_card h_sub

/-- Generic constant absorption: for any C > 0 and α > 0, there exists Δ₀ > 0
    such that for all 0 < Δ < Δ₀ and Δ < 1, C ≤ Δ^{-α}.

    Used to prove K_pack ≤ Δ^{-73ε/25} for sufficiently small Δ. -/
lemma constant_absorb_rpow (C α : ℝ) (hC_pos : 0 < C) (hα_pos : 0 < α) :
    ∃ (Δ₀ : ℝ), 0 < Δ₀ ∧ ∀ (Δ : ℝ), 0 < Δ → Δ < Δ₀ → Δ < 1 →
      C ≤ Real.rpow Δ (-α) := by
  by_cases hC : C ≤ 1
  · -- C ≤ 1: any Δ < 1 works since Δ^{-α} > 1 ≥ C
    use 1 / 2, by norm_num
    intro Δ hΔ_pos hΔ_lt hΔ_lt_one
    have h2 : Real.rpow Δ α < 1 := Real.rpow_lt_one hΔ_pos.le hΔ_lt_one hα_pos
    have h_pos : 0 < Real.rpow Δ α := Real.rpow_pos_of_pos hΔ_pos α
    have h3 : (Real.rpow Δ α)⁻¹ ≥ 1 := by
      have h4 : Real.rpow Δ α ≤ 1 := h2.le
      have h5 : (Real.rpow Δ α)⁻¹ ≥ 1 := by
        calc (Real.rpow Δ α)⁻¹
          ≥ 1⁻¹ := by gcongr
        _ = 1 := by norm_num
      exact h5
    have h6 : Real.rpow Δ (-α) = (Real.rpow Δ α)⁻¹ :=
      Real.rpow_neg hΔ_pos.le (y := α)
    rw [h6]
    linarith
  · -- C > 1: choose Δ₀ = C^{-1/α}
    have hC_gt_one : 1 < C := by linarith
    set Δ₀ : ℝ := Real.rpow C (-1 / α) with hΔ₀_def
    have hΔ₀_pos : 0 < Δ₀ := Real.rpow_pos_of_pos hC_pos _
    have h_neg : -1 / α < 0 := by
      have h2 : 0 < α := hα_pos
      exact div_neg_of_neg_of_pos (by linarith) h2
    have hΔ₀_lt_one : Δ₀ < 1 := by
      have h_pos_exp : 0 < 1 / α := by positivity
      have h1 : 1 < Real.rpow C (1 / α) := Real.one_lt_rpow hC_gt_one h_pos_exp
      have h2 : Δ₀ = (Real.rpow C (1 / α))⁻¹ := by
        simp only [hΔ₀_def]
        have h3 : Real.rpow C (-1 / α) = Real.rpow C (-(1 / α)) := by ring_nf
        rw [h3]
        exact Real.rpow_neg hC_pos.le (y := 1 / α)
      rw [h2]
      have h4 : (Real.rpow C (1 / α))⁻¹ < 1 := by
        have h5 : 1 < Real.rpow C (1 / α) := h1
        have h6 : (Real.rpow C (1 / α))⁻¹ < 1 := by
          calc (Real.rpow C (1 / α))⁻¹
            < 1⁻¹ := by gcongr
          _ = 1 := by norm_num
        exact h6
      exact h4
    use Δ₀, hΔ₀_pos
    intro Δ hΔ_pos hΔ_lt hΔ_lt_one
    have h4 : Real.rpow Δ α < Real.rpow Δ₀ α := Real.rpow_lt_rpow (by linarith) hΔ_lt hα_pos
    have h5 : Real.rpow Δ₀ α = C⁻¹ := by
      have h6 : Real.rpow Δ₀ α = Real.rpow C ((-1 / α) * α) := by
        rw [hΔ₀_def]
        exact (Real.rpow_mul hC_pos.le (-1 / α) α).symm
      rw [h6]
      have h7 : (-1 / α) * α = -1 := by field_simp [hα_pos.ne'] <;> ring
      rw [h7]
      have h8 : Real.rpow C (-1 : ℝ) = (Real.rpow C (1 : ℝ))⁻¹ :=
        Real.rpow_neg hC_pos.le (y := (1 : ℝ))
      rw [h8]
      have h9 : Real.rpow C (1 : ℝ) = C := by simp
      rw [h9] <;> ring
    rw [h5] at h4
    have h8 : Real.rpow Δ (-α) = (Real.rpow Δ α)⁻¹ :=
      Real.rpow_neg hΔ_pos.le (y := α)
    rw [h8]
    have h_pos2 : 0 < Real.rpow Δ α := Real.rpow_pos_of_pos hΔ_pos α
    have h10 : 1 / C⁻¹ < 1 / Real.rpow Δ α := one_div_lt_one_div_of_lt h_pos2 h4
    have h11 : 1 / C⁻¹ = C := by
      field_simp [hC_pos.ne'] <;> ring
    have h12 : 1 / Real.rpow Δ α = (Real.rpow Δ α)⁻¹ := by ring
    rw [h11, h12] at h10
    exact h10.le

end DirecretisedFurstenbergEstimate.FrontEndLemmas.CGlobalCardBound
