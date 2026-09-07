module

/-
  Obligation #12: Per-coarse-square S-set restriction from global S-set.

  Given a global (δ, t, δ^{-ε})-set S and a finite δ-separated subset S' ⊆ S
  with cardinality bounds |S| ≤ Δ^{-2t-ε/4} and |S'| ≥ Δ^{-t+ε},
  prove S' is a (δ, t, Δ^{-t-5ε})-set.

  Whiteprint node: b1_to_a1_conversion (obligation #12)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.BallGrowth
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A4_CQpiSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductPropBoundedHelpers2
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA4

/-- Restrict a global S-set to a finite δ-separated subset with known cardinality
    bounds, producing a per-square S-set with weakened constant. -/
lemma per_square_sset_restriction
    {δ Δ t ε : ℝ}
    (hδ_pos : 0 < δ)
    (hΔ_pos : 0 < Δ)
    (hδ_eq : δ = Δ ^ 2)
    (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    (hε_pos : 0 < ε)
    {S S' : Finset EuclideanPlane}
    (hS_sset : IsDeltaSSet δ t (Real.rpow δ (-2 * ε)) (S : Set EuclideanPlane))
    (hS'_sub : (S' : Set EuclideanPlane) ⊆ (S : Set EuclideanPlane))
    (hS'_sep : SSetBridges.SeparatedAt δ (S' : Set EuclideanPlane))
    (hS_card_upper : (S.card : ℝ) ≤ Real.rpow Δ (-2 * t - ε / 4))
    (hS'_card_lower : (S'.card : ℝ) ≥ Real.rpow Δ (-t + 3 * ε))
    (hS'_nonempty : S'.Nonempty) :
    IsDeltaSSet δ t (9 * Real.rpow Δ (-t - 29 * ε / 4)) (S' : Set EuclideanPlane) := by
  have hS_card_pos : 0 < (S.card : ℝ) := by
    have h3 : S.Nonempty := hS'_nonempty.mono hS'_sub
    exact_mod_cast Finset.card_pos.mpr h3
  have hS'_card_pos : 0 < (S'.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hS'_nonempty
  set ratio : ℝ := (S.card : ℝ) / (S'.card : ℝ) with hratio_def
  have h_ratio_pos : 0 < ratio := by positivity

  -- Step 1: covering_δ(S) ≤ |S|
  have h_cover_S_upper :
      (Metric.externalCoveringNumber δ.toNNReal (S : Set EuclideanPlane) : ENNReal) ≤
      (S.card : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_le_encard_self (S : Set EuclideanPlane)

  -- Step 2: |S'| ≤ 9 * covering_δ(S')
  have h_pack9 : ∀ (x : EuclideanPlane),
      (S'.filter (fun y => dist y x ≤ δ)).card ≤ 9 :=
    SSetBridges.max_points_in_delta_ball_EuclideanPlane hδ_pos S' hS'_sep
  have h_card_cover :
      (S'.card : ENNReal) ≤ (9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal (S' : Set EuclideanPlane) :=
    SSetBridges.packing_cover_generic hδ_pos hS'_sep (by norm_num) h_pack9

  -- Step 3: K = 9 * ratio
  set K : ℝ := 9 * ratio with hK_def
  have hK_pos : 0 < K := by positivity

  -- |S| = ratio * |S'| in ENNReal
  have h_div_eq : (S.card : ENNReal) = ENNReal.ofReal ratio * ENNReal.ofReal (S'.card : ℝ) := by
    have h4 : ratio * (S'.card : ℝ) = (S.card : ℝ) := by
      dsimp only [ratio]
      field_simp [hS'_card_pos.ne'] <;> ring
    have h : ENNReal.ofReal ratio * ENNReal.ofReal (S'.card : ℝ) =
        ENNReal.ofReal (ratio * (S'.card : ℝ)) := by
      rw [← ENNReal.ofReal_mul h_ratio_pos.le]
    rw [h, h4]
    <;> simp
  have h_card_cast : (S'.card : ENNReal) = ENNReal.ofReal (S'.card : ℝ) := by simp

  -- covering(S) ≤ K * covering(S')
  have h_cover_ratio :
      (Metric.externalCoveringNumber δ.toNNReal (S : Set EuclideanPlane) : ENNReal) ≤
      ENNReal.ofReal K * Metric.externalCoveringNumber δ.toNNReal (S' : Set EuclideanPlane) := by
    have h_mul9 : ENNReal.ofReal K = (9 : ENNReal) * ENNReal.ofReal ratio := by
      have h : ENNReal.ofReal (9 * ratio) = ENNReal.ofReal (9 : ℝ) * ENNReal.ofReal ratio := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
      simpa [hK_def] using h
    calc (Metric.externalCoveringNumber δ.toNNReal (S : Set EuclideanPlane) : ENNReal)
      ≤ (S.card : ENNReal) := h_cover_S_upper
    _ = ENNReal.ofReal ratio * (S'.card : ENNReal) := by
      rw [h_card_cast] at *; exact h_div_eq
    _ ≤ ENNReal.ofReal ratio * ((9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal (S' : Set EuclideanPlane)) := by
      gcongr
    _ = ENNReal.ofReal K * Metric.externalCoveringNumber δ.toNNReal (S' : Set EuclideanPlane) := by
      rw [h_mul9] <;> ring

  -- Step 4: Apply subset_with_cover_ratio
  have h_result : IsDeltaSSet δ t (K * Real.rpow δ (-2 * ε)) (S' : Set EuclideanPlane) :=
    IsDeltaSSet.subset_with_cover_ratio hK_pos hS_sset hS'_sub h_cover_ratio

  -- Step 5: Real arithmetic helpers
  have h_rpow_mul' : ∀ (a b : ℝ), Real.rpow Δ (a * b) = (Real.rpow Δ a) ^ b := by
    intro a b
    exact Real.rpow_mul hΔ_pos.le a b
  have h_rpow_add' : ∀ (a b : ℝ), Real.rpow Δ a * Real.rpow Δ b = Real.rpow Δ (a + b) := by
    intro a b
    exact (Real.rpow_add hΔ_pos a b).symm
  have h_rpow_sub' : ∀ (a b : ℝ), Real.rpow Δ a / Real.rpow Δ b = Real.rpow Δ (a - b) := by
    intro a b
    have h_pos : 0 < Real.rpow Δ b := Real.rpow_pos_of_pos hΔ_pos _
    have h_sum : Real.rpow Δ (a - b) * Real.rpow Δ b = Real.rpow Δ ((a - b) + b) := h_rpow_add' (a - b) b
    have h_ab : (a - b) + b = a := by ring
    rw [h_ab] at h_sum
    field_simp [h_pos.ne'] <;> linarith

  have hC_delta : Real.rpow δ (-2 * ε) = Real.rpow Δ (-4 * ε) := by
    rw [hδ_eq]
    have h2 : Real.rpow (Δ ^ 2) (-2 * ε) = Real.rpow Δ (2 * (-2 * ε)) := by
      have h3 : Real.rpow Δ 2 = (Δ ^ 2 : ℝ) := by simp [Real.rpow_two]
      have h4 : Real.rpow (Real.rpow Δ 2) (-2 * ε) = Real.rpow Δ (2 * (-2 * ε)) := (h_rpow_mul' 2 (-2 * ε)).symm
      rw [h3] at h4
      exact h4
    rw [h2]
    have h5 : 2 * (-2 * ε) = -4 * ε := by ring
    rw [h5]

  -- K ≤ 9 * Δ^{-t-5ε/4}
  have h_pos1 : 0 < Real.rpow Δ (-t + 3 * ε) := Real.rpow_pos_of_pos hΔ_pos _
  have h_div_val : Real.rpow Δ (-2 * t - ε / 4) / Real.rpow Δ (-t + 3 * ε) =
      Real.rpow Δ (-t - 13 * ε / 4) := by
    have h := h_rpow_sub' (-2 * t - ε / 4) (-t + 3 * ε)
    have h_exp : (-2 * t - ε / 4) - (-t + 3 * ε) = -t - 13 * ε / 4 := by ring
    rw [h_exp] at h
    exact h
  have hK_bound : K ≤ 9 * Real.rpow Δ (-t - 13 * ε / 4) := by
    rw [hK_def, hratio_def]
    have h5 : (S.card : ℝ) ≤ Real.rpow Δ (-2 * t - ε / 4) := hS_card_upper
    have h6 : 0 < (S'.card : ℝ) := hS'_card_pos
    have h7 : 0 < Real.rpow Δ (-t + 3 * ε) := h_pos1
    have h8 : (S'.card : ℝ) ≥ Real.rpow Δ (-t + 3 * ε) := hS'_card_lower
    set U := Real.rpow Δ (-2 * t - ε / 4) with hU_def
    set L := Real.rpow Δ (-t + 3 * ε) with hL_def
    have hU_pos : 0 < U := Real.rpow_pos_of_pos hΔ_pos _
    have hL_pos : 0 < L := h_pos1
    have h_denom_le : L ≤ (S'.card : ℝ) := hS'_card_lower
    have h_inv_le : 1 / (S'.card : ℝ) ≤ 1 / L := by
      exact one_div_le_one_div_of_le hL_pos h_denom_le
    have h_div_le : U / (S'.card : ℝ) ≤ U / L := by
      have h : U / (S'.card : ℝ) = U * (1 / (S'.card : ℝ)) := by ring
      have h2 : U / L = U * (1 / L) := by ring
      rw [h, h2]
      exact mul_le_mul_of_nonneg_left h_inv_le hU_pos.le
    have h9 : 9 * ((S.card : ℝ) / (S'.card : ℝ)) ≤ 9 * (U / (S'.card : ℝ)) := by gcongr
    have h10 : 9 * (U / (S'.card : ℝ)) ≤ 9 * (U / L) := by
      gcongr
    have h11 : U / L = Real.rpow Δ (-t - 13 * ε / 4) := h_div_val
    rw [h11] at h10
    exact le_trans h9 h10

  -- K * δ^{-2ε} ≤ 9 * Δ^{-t-29ε/4}
  have h_rpow_sum1 : Real.rpow Δ (-t - 13 * ε / 4) * Real.rpow Δ (-4 * ε) =
      Real.rpow Δ (-t - 29 * ε / 4) := by
    have h := h_rpow_add' (-t - 13 * ε / 4) (-4 * ε)
    have h_exp : (-t - 13 * ε / 4) + (-4 * ε) = -t - 29 * ε / 4 := by ring
    rw [h_exp] at h
    exact h
  have h_final : K * Real.rpow δ (-2 * ε) ≤ 9 * Real.rpow Δ (-t - 29 * ε / 4) := by
    rw [hC_delta]
    have h1 : K * Real.rpow Δ (-4 * ε) ≤
        (9 * Real.rpow Δ (-t - 13 * ε / 4)) * Real.rpow Δ (-4 * ε) := by
      have h_nonneg : 0 ≤ Real.rpow Δ (-4 * ε) := Real.rpow_nonneg hΔ_pos.le (-4 * ε)
      exact mul_le_mul_of_nonneg_right hK_bound h_nonneg
    have h2 : (9 * Real.rpow Δ (-t - 13 * ε / 4)) * Real.rpow Δ (-4 * ε) =
        9 * (Real.rpow Δ (-t - 13 * ε / 4) * Real.rpow Δ (-4 * ε)) := by ring
    rw [h2] at h1
    rw [h_rpow_sum1] at h1
    exact h1

  -- Step 6: Weaken constant
  exact IsDeltaSSet.mono_const h_result h_final

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
