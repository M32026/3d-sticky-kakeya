module

/-
  B1 Expanded Bridge: concrete wrapper around inductionOnScalesBridge_expanded.

  Provides:
  - sset_transfer_expanded via sset_transfer_expanded_concrete (3-cell, factor 60)
  - sset_transfer_rev via sset_transfer_rev_concrete (factor 5)
  - h_expanded_bounded (3-cell expansion boundedness)

  Outputs all 11 clauses from the expanded bridge in main representation.

  Whiteprint node: B1_induction_on_scales / expanded_bridge
  Status: COMPLETE — h_expanded_bounded proved via 3*|T₀| ≤ 36*16^n
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge_Wrapper
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FormatConversionLemmas
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

namespace DiscretisedFurstenbergEstimate.Bridge

open DiscretisedFurstenbergEstimate.Bridge.Geometric
open DirecretisedFurstenbergEstimate.FormatConversion.M2

/-- Concrete wrapper around inductionOnScalesBridge_expanded.

    Uses 3-cell expansion (coveringCells) for forward S-set transfer,
    thinning (3-way choice) for incidence, and outputs all 11 clauses.

    Transfer constants:
    - Forward S-set (expanded): 60*C₁
    - Reverse S-set: 5*C
    - K scaling: 2700 (540 for C_stand × 5 for reverse)
-/
theorem inductionOnScalesBridge_expanded_concrete
    {n m : ℕ} (hnm : m ≤ n)
    (s : ℝ) (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁)
    (M : ℕ) (hM : 0 < M)
    (config : MainConfig n s C₁ M)
    (hP_nonempty : config.P₀.Nonempty)
    (h_squares_unit : ∀ p ∈ config.P₀,
      0 ≤ p.i ∧ p.i < (2 ^ n : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ n : ℤ))
    (h_tubes_strip : ∀ T ∈ config.T₀,
      -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ))
    (h_tubes_bounded : config.T₀.card ≤ 12 * 16^n) :
    ∃ (K : ℝ), 1 ≤ K ∧
      K ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7 ∧
      ∃ (P : Finset (MainSquare n))
      (hP_sub : P ⊆ config.P₀)
      (tubeFamily : (p : MainSquare n) → p ∈ P → Finset (MainTube n))
      (CΔ : ℝ) (MΔ : ℕ) (hMΔ : 0 < MΔ)
      (coarseConfig : MainConfig m s CΔ MΔ)
      (CQ : MainSquare m → ℝ)
      (MQ : MainSquare m → ℕ)
      (hMQ : ∀ Q ∈ coarseConfig.P₀, 0 < MQ Q)
      (fineConfig : (Q : MainSquare m) → Q ∈ coarseConfig.P₀ →
        MainConfig (n - m) s (CQ Q) (MQ Q))
      (fineConfig_B1 : (Q : MainSquare m) → (hQ : Q ∈ coarseConfig.P₀) →
        B1BridgeHypotheses (n - m) (fineConfig Q hQ)),
      P.Nonempty ∧
      coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm) ∧
      ((config.P₀.image (InductionConfigurations.containingSquare hnm)).card : ℝ) ≤
        K * (coarseConfig.P₀.card : ℝ) ∧
      (∀ Q ∈ coarseConfig.P₀,
        ((config.P₀.filter fun p =>
          InductionConfigurations.squareContained hnm p Q).card : ℝ) ≤
        K * ((P.filter fun p =>
          InductionConfigurations.squareContained hnm p Q).card : ℝ)) ∧
      (∀ p hp, tubeFamily p hp ⊆ config.tubeFamily p (hP_sub hp) ∧
        (M : ℝ) ≤ K * ((tubeFamily p hp).card : ℝ)) ∧
      CΔ ≤ K * C₁ ∧ C₁ ≤ K * CΔ ∧
      (∀ Q ∈ coarseConfig.P₀, CQ Q ≤ K * C₁ ∧ C₁ ≤ K * CQ Q) ∧
      (∀ p hp, ∀ T ∈ tubeFamily p hp,
        (T.toSet ∩ p.toSet).Nonempty) ∧
      (∀ p hp T, T ∈ tubeFamily p hp →
        ∃ (hQ : InductionConfigurations.containingSquare hnm p ∈ coarseConfig.P₀)
          (U_stand : StandTube m) (C : StandTube n),
          C ∈ coveringCells n T.a T.b ∧
          tubeToMainShifted U_stand ∈
            coarseConfig.tubeFamily (InductionConfigurations.containingSquare hnm p) hQ ∧
          C.toSet ⊆ U_stand.toSet) ∧
      (∀ Q, ∀ hQ : Q ∈ coarseConfig.P₀,
        (fineConfig Q hQ).P₀ =
          (P.filter fun p => InductionConfigurations.squareContained hnm p Q).image
            (InductionConfigurations.squareHomothety hnm Q)) ∧
      (∀ Q, ∀ hQ : Q ∈ coarseConfig.P₀,
        ∀ p, ∀ hp : p ∈ P,
          InductionConfigurations.squareContained hnm p Q →
          ∃ (hq : InductionConfigurations.squareHomothety hnm Q p ∈ (fineConfig Q hQ).P₀),
            ((fineConfig Q hQ).tubeFamily
                (InductionConfigurations.squareHomothety hnm Q p) hq).image (fun U => U.a) =
              (tubeFamily p hp).image
                (fun T => localSlopeCellIndex m T.a)) ∧
      (∀ (Q : MainSquare m) (hQ : Q ∈ coarseConfig.P₀),
        K * (config.T₀.card : ℝ) * MΔ * MQ Q ≥
          (coarseConfig.T₀.card : ℝ) * ((fineConfig Q hQ).T₀.card : ℝ) * M) ∧
      (∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1) := by
  -- ========================================================================
  -- Step 1: Provide S-set transfer (3-cell expansion, factor 60)
  -- ========================================================================
  let sset_transfer_expanded : ∀ (F : Finset (MainTube n)),
      IsDeltaSSet (DiscretisedFurstenbergEstimate.dyadicDelta n) s C₁ (F : Set (MainTube n)) →
      ∃ C', C' ≤ C₁ * 60 ∧ 1 ≤ C' ∧
        _root_.IsFiniteTubeSSet s C' (F.biUnion (fun T => coveringCells n T.a T.b)) :=
    fun F h => sset_transfer_expanded_concrete hs hs_one hC₁ F h

  -- ========================================================================
  -- Step 2: Provide reverse S-set transfer (factor 5)
  -- ========================================================================
  let sset_transfer_rev : ∀ (k : ℕ) (C : ℝ), 1 ≤ C →
      ∀ (F : Finset (StandTube k)),
        _root_.IsFiniteTubeSSet s C F →
        IsDeltaSSet (DiscretisedFurstenbergEstimate.dyadicDelta k) s (5 * C)
          (F.image tubeToMainShifted : Set (MainTube k)) :=
    fun k C hC_one F h => sset_transfer_rev_concrete hs hC_one F h

  -- ========================================================================
  -- Step 3: Prove expanded boundedness
  -- allExpanded is the 3-cell expansion of T₀, so |allExpanded| ≤ 3*|T₀| ≤ 36*16^n
  -- ========================================================================
  let allExpanded : Finset (StandTube n) :=
    config.P₀.biUnion (fun p =>
      if hp : p ∈ config.P₀ then
        (config.tubeFamily p hp).biUnion (fun T => coveringCells n T.a T.b)
      else ∅)

  have h_expanded_bounded : allExpanded.card ≤ 36 * 16^n := by
    have h1 : allExpanded ⊆ config.T₀.biUnion (fun T => coveringCells n T.a T.b) := by
      intro C hC
      rcases Finset.mem_biUnion.mp hC with ⟨p, hp, hC2⟩
      have hC3 : C ∈ (config.tubeFamily p hp).biUnion (fun T => coveringCells n T.a T.b) := by
        simpa [hp] using hC2
      rcases Finset.mem_biUnion.mp hC3 with ⟨T, hT, hC4⟩
      have hT_in_T0 : T ∈ config.T₀ := config.h_subset p hp hT
      exact Finset.mem_biUnion.mpr ⟨T, hT_in_T0, hC4⟩
    have h2 : allExpanded.card ≤ (config.T₀.biUnion (fun T => coveringCells n T.a T.b)).card :=
      Finset.card_le_card h1
    have h3 : (config.T₀.biUnion (fun T => coveringCells n T.a T.b)).card ≤
        ∑ T ∈ config.T₀, (coveringCells n T.a T.b).card := Finset.card_biUnion_le
    have h4 : ∑ T ∈ config.T₀, (coveringCells n T.a T.b).card = 3 * config.T₀.card := by
      simp [coveringCells_card, Finset.sum_const] <;> ring
    rw [h4] at h3
    have h5 : allExpanded.card ≤ 3 * config.T₀.card := by
      exact le_trans h2 h3
    have h6 : 3 * config.T₀.card ≤ 36 * 16^n := by
      have h7 : config.T₀.card ≤ 12 * 16^n := h_tubes_bounded
      omega
    exact le_trans h5 h6

  -- ========================================================================
  -- Step 4: Call expanded bridge
  -- ========================================================================
  exact inductionOnScalesBridge_expanded hnm s hs hs_one C₁ hC₁ M hM config
    hP_nonempty h_squares_unit h_tubes_strip h_tubes_bounded
    sset_transfer_expanded h_expanded_bounded sset_transfer_rev

end DiscretisedFurstenbergEstimate.Bridge
