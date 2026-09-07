module

/-
  B1 Bridge Helpers — Narrow wrappers for kestrel's assembly

  Provides two helper lemmas to replace the 3 sorrys:
  1. `b1_bridge_data_helper`: B1InductionData + coarse count + raw product
  2. `post_b1_retention_helper`: K_global + global retention + per-fiber band

  Each takes all hypotheses explicitly and returns an existential,
  so kestrel's assembly can call them with one-line `rcases`.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.B1Integration
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.B1InductionDataType
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.B1InductionDataConstructor
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.GlobalRetentionObligation
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionConfigurations
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.InductionConfigurations
open DirecretisedFurstenbergEstimate.Section6

/-- Narrow helper: produce B1InductionData + coarse count + raw product.

    Wraps b1_bridge_decomposition and B1InductionData packaging.
    Returns data, coarse parent retention, and raw product inequality. -/
lemma b1_bridge_data_helper
    {n m : ℕ} (hnm : m ≤ n)
    {s t C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration n s C₁ M}
    (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (hC₁ : 1 ≤ C₁) (hM : 0 < M)
    (hP_nonempty : config.P₀.Nonempty)
    (h_squares_unit : ∀ p ∈ config.P₀,
      0 ≤ (p : DiscretisedFurstenbergEstimate.DyadicSquare n).i ∧
      (p : DiscretisedFurstenbergEstimate.DyadicSquare n).i < (2 ^ n : ℤ) ∧
      0 ≤ (p : DiscretisedFurstenbergEstimate.DyadicSquare n).j ∧
      (p : DiscretisedFurstenbergEstimate.DyadicSquare n).j < (2 ^ n : ℤ))
    (h_tubes_strip : ∀ T ∈ config.T₀,
      -(2 ^ n : ℤ) ≤ (T : DiscretisedFurstenbergEstimate.DyadicTube n).a ∧
      (T : DiscretisedFurstenbergEstimate.DyadicTube n).a < (2 ^ n : ℤ))
    (h_tubes_bounded : config.T₀.card ≤ 12 * 16^n) :
    ∃ (data : B1InductionData n m hnm s t C₁ M config)
      (hK_bound : data.K ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7)
      (h_coarse_count : ((config.P₀.image (InductionConfigurations.containingSquare hnm)).card : ℝ) ≤
        data.K * (data.coarseConfig.P₀.card : ℝ))
      (h_fineP_eq_all : ∀ (Q : DiscretisedFurstenbergEstimate.DyadicSquare m)
        (hQ : Q ∈ data.coarseConfig.P₀),
        (data.fineConfig Q hQ).P₀ =
          (data.P.filter (fun p => InductionConfigurations.squareContained hnm p Q)).image
            (InductionConfigurations.squareHomothety hnm Q)),
      (∀ Q hQ, (data.K : ℝ) * (config.T₀.card : ℝ) * (data.MΔ : ℝ) * (data.MQ Q : ℝ) ≥
        (data.coarseConfig.T₀.card : ℝ) * ((data.fineConfig Q hQ).T₀.card : ℝ) * (M : ℝ)) := by
  rcases b1_bridge_decomposition hnm s hs hs_one C₁ hC₁ M hM
      config hP_nonempty h_squares_unit h_tubes_strip h_tubes_bounded
    with ⟨K, hK_ge1, hK_bound, P_b1, hP_b1_sub, tubeFamily_b1,
      CΔ, MΔ, hMΔ_pos, coarseConfig_b1, CQ_b1, MQ_b1, hMQ_b1,
      fineConfig_b1, fineConfig_B1_b1,
      hP_b1_nonempty, h_coarse_P_eq_b1, h_coarse_count_b1, h_per_Q_ret_b1,
      h_tube_sub_size_b1, hCΔ_le_b1, hC₁_le_b1, hCQ_compare_b1,
      h_tube_intersect_b1, h_tube_geometry_b1,
      h_fine_P_eq_b1, h_fine_tubes_b1, h_raw_product_b1, h_coarse_slope_b1⟩
  have h_tube_sub_b1 : ∀ p hp, tubeFamily_b1 p hp ⊆ config.tubeFamily p (hP_b1_sub hp) :=
    fun p hp => (h_tube_sub_size_b1 p hp).1
  have h_tube_size_b1 : ∀ p hp, (M : ℝ) ≤ K * ((tubeFamily_b1 p hp).card : ℝ) :=
    fun p hp => (h_tube_sub_size_b1 p hp).2
  have hCΔ_compare_b1 : CΔ ≤ K * C₁ ∧ C₁ ≤ K * CΔ := ⟨hCΔ_le_b1, hC₁_le_b1⟩
  let data : B1InductionData n m hnm s t C₁ M config :=
    b1_induction_data_from_raw hnm K hK_ge1 P_b1 hP_b1_sub hP_b1_nonempty
      tubeFamily_b1 CΔ MΔ hMΔ_pos coarseConfig_b1 CQ_b1 MQ_b1 hMQ_b1
      fineConfig_b1 fineConfig_B1_b1 h_coarse_P_eq_b1 h_per_Q_ret_b1
      h_tube_sub_b1 h_tube_size_b1
      (fun p hp T hT => h_tube_intersect_b1 p hp T hT)
      (fun p hp T hT => h_tube_geometry_b1 p hp T hT)
      hCΔ_compare_b1 hCQ_compare_b1 h_coarse_slope_b1
  exact ⟨data, hK_bound, h_coarse_count_b1, h_fine_P_eq_b1, h_raw_product_b1⟩

/-- Narrow helper: post-B1 global retention + per-fiber band.

    Given B1InductionData, coarse count, and pre-B1 uniform fiber bounds,
    produces K_global with global retention and per-fiber band. -/
lemma post_b1_retention_helper
    {n m : ℕ} (hnm : m ≤ n)
    {s t C₁ : ℝ} {M : ℕ}
    {config_heavy : CombiningTheorem.NiceConfiguration n s C₁ M}
    {data : B1InductionData n m hnm s t C₁ M config_heavy}
    {M_fiber : ℝ}
    (hM_fiber_pos : 0 < M_fiber)
    (h_coarse_count : ((config_heavy.P₀.image (InductionConfigurations.containingSquare hnm)).card : ℝ) ≤
      data.K * (data.coarseConfig.P₀.card : ℝ))
    -- Pre-B1 fiber bounds for all coarse squares hit by config_heavy
    (hF0_lower : ∀ Q ∈ config_heavy.P₀.image (InductionConfigurations.containingSquare hnm),
      M_fiber ≤ ((config_heavy.P₀.filter (fun p => squareContained hnm p Q)).card : ℝ))
    (hF0_upper : ∀ Q ∈ config_heavy.P₀.image (InductionConfigurations.containingSquare hnm),
      ((config_heavy.P₀.filter (fun p => squareContained hnm p Q)).card : ℝ) < 2 * M_fiber) :
    ∃ (K_global : ℝ), 0 < K_global ∧ K_global ≤ 2 * data.K^2 ∧
      (config_heavy.P₀.card : ℝ) ≤ K_global * (data.P.card : ℝ) ∧
      (∀ Q ∈ data.coarseConfig.P₀,
        M_fiber / data.K ≤ ((data.P.filter (fun p => squareContained hnm p Q)).card : ℝ) ∧
        ((data.P.filter (fun p => squareContained hnm p Q)).card : ℝ) < 2 * M_fiber) := by
  let K_B1 : ℝ := data.K
  have hK_B1_ge1 : 1 ≤ K_B1 := data.hK_ge1
  have hK_B1_pos : 0 < K_B1 := by linarith
  let Q0 := config_heavy.P₀.image (InductionConfigurations.containingSquare hnm)
  let Q_b1 := data.coarseConfig.P₀
  let F0 (Q : DiscretisedFurstenbergEstimate.DyadicSquare m) : ℕ :=
    (config_heavy.P₀.filter (fun p => squareContained hnm p Q)).card
  let F_b1 (Q : DiscretisedFurstenbergEstimate.DyadicSquare m) : ℕ :=
    (data.P.filter (fun p => squareContained hnm p Q)).card
  have hQ_b1_sub : Q_b1 ⊆ Q0 := by
    intro x hx
    have h1 : x ∈ data.P.image (InductionConfigurations.containingSquare hnm) := by
      rw [←data.h_coarse_P_eq]; exact hx
    have h2 : data.P.image (InductionConfigurations.containingSquare hnm) ⊆ Q0 := by
      apply Finset.image_subset_image; exact data.hP_sub
    exact h2 h1
  -- Fiber upper bound f(Q) ≤ f0(Q) from data.P ⊆ config_heavy.P₀
  have h_fiber_upper_b1 : ∀ Q ∈ Q_b1, (F_b1 Q : ℝ) ≤ (F0 Q : ℝ) := by
    intro Q hQ
    have h1 : data.P.filter (fun p => squareContained hnm p Q) ⊆
        config_heavy.P₀.filter (fun p => squareContained hnm p Q) := by
      apply Finset.filter_subset_filter; exact data.hP_sub
    exact_mod_cast Finset.card_le_card h1
  -- Sum decompositions
  have h_sum_F0 : (∑ Q ∈ Q0, (F0 Q : ℝ)) = (config_heavy.P₀.card : ℝ) := by
    have h_mapsTo : (config_heavy.P₀ : Set (DiscretisedFurstenbergEstimate.DyadicSquare n)).MapsTo
        (InductionConfigurations.containingSquare hnm) (Q0 : Set (DiscretisedFurstenbergEstimate.DyadicSquare m)) := by
      intro p hp; exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have h_card : config_heavy.P₀.card = ∑ Q ∈ Q0,
        (config_heavy.P₀.filter (fun p => InductionConfigurations.containingSquare hnm p = Q)).card :=
      Finset.card_eq_sum_card_fiberwise h_mapsTo
    have h_filter_eq : ∀ q ∈ Q0,
        config_heavy.P₀.filter (fun p => InductionConfigurations.containingSquare hnm p = q) =
        config_heavy.P₀.filter (fun p => squareContained hnm p q) := by
      intro q _; apply Finset.ext; intro p
      simp only [Finset.mem_filter] <;> rw [containingSquare_iff hnm p q]
    have h_sum : ∑ Q ∈ Q0, (F0 Q : ℝ) = ∑ Q ∈ Q0,
        ((config_heavy.P₀.filter (fun p => InductionConfigurations.containingSquare hnm p = Q)).card : ℝ) := by
      apply Finset.sum_congr rfl; intro Q hQ
      have h_eq : (config_heavy.P₀.filter (fun p => InductionConfigurations.containingSquare hnm p = Q)).card = F0 Q := by
        rw [h_filter_eq Q hQ] <;> rfl
      exact_mod_cast h_eq.symm
    rw [h_sum]; exact_mod_cast h_card.symm
  have h_sum_F : (∑ q ∈ Q_b1, (F_b1 q : ℝ)) = (data.P.card : ℝ) := by
    have h_mapsTo : (data.P : Set (DiscretisedFurstenbergEstimate.DyadicSquare n)).MapsTo
        (InductionConfigurations.containingSquare hnm) (Q_b1 : Set (DiscretisedFurstenbergEstimate.DyadicSquare m)) := by
      intro p hp
      have h1 : InductionConfigurations.containingSquare hnm p ∈ data.P.image (InductionConfigurations.containingSquare hnm) :=
        Finset.mem_image.mpr ⟨p, hp, rfl⟩
      have h_eq1 : Q_b1 = data.P.image (InductionConfigurations.containingSquare hnm) := by
        simpa [Q_b1] using data.h_coarse_P_eq
      rw [h_eq1] at *; exact h1
    have h_card : data.P.card = ∑ q ∈ Q_b1,
        (data.P.filter (fun p => InductionConfigurations.containingSquare hnm p = q)).card :=
      Finset.card_eq_sum_card_fiberwise h_mapsTo
    have h_filter_eq2 : ∀ q ∈ Q_b1,
        data.P.filter (fun p => InductionConfigurations.containingSquare hnm p = q) =
        data.P.filter (fun p => squareContained hnm p q) := by
      intro q _; apply Finset.ext; intro p
      simp only [Finset.mem_filter] <;> rw [containingSquare_iff hnm p q]
    have h_sum : ∑ q ∈ Q_b1, (F_b1 q : ℝ) = ∑ q ∈ Q_b1,
        ((data.P.filter (fun p => InductionConfigurations.containingSquare hnm p = q)).card : ℝ) := by
      apply Finset.sum_congr rfl; intro q hq
      have h_eq : (data.P.filter (fun p => InductionConfigurations.containingSquare hnm p = q)).card = F_b1 q := by
        rw [h_filter_eq2 q hq] <;> rfl
      exact_mod_cast h_eq.symm
    rw [h_sum]; exact_mod_cast h_card.symm
  have hF0_upper' : ∀ Q ∈ Q0, (F0 Q : ℝ) ≤ (2 : ℝ) * M_fiber := by
    intro Q hQ; have h : (F0 Q : ℝ) < 2 * M_fiber := hF0_upper Q hQ; exact le_of_lt h
  let K_global : ℝ := K_B1 * (1 + (K_B1 - 1) * (2 : ℝ))
  have hK_global_pos : 0 < K_global := by
    have h1 : 0 < K_B1 := hK_B1_pos
    have h2 : 0 < 1 + (K_B1 - 1) * (2 : ℝ) := by linarith
    positivity
  have hK_global_bound : K_global ≤ 2 * K_B1^2 := by
    dsimp only [K_global]
    have h3 : 0 ≤ K_B1 := by linarith
    have h4 : K_B1 * (1 + (K_B1 - 1) * (2 : ℝ)) = K_B1 * (2 * K_B1 - 1) := by ring
    rw [h4]
    have h5 : K_B1 * (2 * K_B1 - 1) ≤ 2 * K_B1^2 := by
      have h6 : K_B1 * (2 * K_B1 - 1) = 2 * K_B1^2 - K_B1 := by ring
      rw [h6]; have h7 : 0 ≤ K_B1 := h3; linarith
    exact h5
  have h_main_sum : (∑ i ∈ Q0, (F0 i : ℝ)) ≤ K_global * (∑ i ∈ Q_b1, (F_b1 i : ℝ)) :=
    global_retention_from_fiber_bounds Q0 Q_b1 F0 F_b1 K_B1 K_B1 (2 : ℝ) M_fiber
      hM_fiber_pos hK_B1_pos (by norm_num) hK_B1_ge1
      hQ_b1_sub h_coarse_count hF0_lower hF0_upper' data.h_per_Q_ret
  have h_global_card : (config_heavy.P₀.card : ℝ) ≤ K_global * (data.P.card : ℝ) := by
    rw [h_sum_F0, h_sum_F] at h_main_sum; exact h_main_sum
  -- Per-fiber retention band
  have h_retention_fiber : ∀ Q ∈ Q_b1,
      M_fiber / K_B1 ≤ (F_b1 Q : ℝ) ∧ (F_b1 Q : ℝ) < 2 * M_fiber := by
    intro Q hQ
    have hQ_in_Q0 : Q ∈ Q0 := hQ_b1_sub hQ
    have h_lower : M_fiber ≤ (F0 Q : ℝ) := hF0_lower Q hQ_in_Q0
    have h_upper : (F0 Q : ℝ) < 2 * M_fiber := hF0_upper Q hQ_in_Q0
    have h_ret : (F0 Q : ℝ) ≤ K_B1 * (F_b1 Q : ℝ) := data.h_per_Q_ret Q hQ
    have h_mon : (F_b1 Q : ℝ) ≤ (F0 Q : ℝ) := h_fiber_upper_b1 Q hQ
    have h1 : M_fiber / K_B1 ≤ (F_b1 Q : ℝ) := by
      have h2 : M_fiber ≤ K_B1 * (F_b1 Q : ℝ) := le_trans h_lower h_ret
      have h3 : M_fiber / K_B1 ≤ (K_B1 * (F_b1 Q : ℝ)) / K_B1 := by gcongr
      have h4 : (K_B1 * (F_b1 Q : ℝ)) / K_B1 = (F_b1 Q : ℝ) := by
        field_simp [hK_B1_pos.ne'] <;> ring
      rw [h4] at h3; exact h3
    have h5 : (F_b1 Q : ℝ) < 2 * M_fiber := by
      calc (F_b1 Q : ℝ) ≤ (F0 Q : ℝ) := h_mon
        _ < 2 * M_fiber := h_upper
    exact ⟨h1, h5⟩
  exact ⟨K_global, hK_global_pos, hK_global_bound, h_global_card, h_retention_fiber⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
