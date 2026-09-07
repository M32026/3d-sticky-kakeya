module

/-
  SL-4: B1 Bridge Integration for Combining Theorem

  Applies the B1 induction-on-scales expanded bridge to a NiceConfiguration,
  producing a coarse configuration and fine configurations for the combining
  theorem inductive step.

  This is a thin wrapper around `inductionOnScalesBridge_expanded_concrete`
  that documents its role in the combining theorem proof and provides a
  single entry point for SL-5 (uniformization) and SL-6 (inductive assembly).

  Whiteprint node: combining_theorem_rework / combining_sl4_b1_integration
  Status: COMPLETE — direct application of expanded bridge

  Key facts:
  - MainConfig = NiceConfiguration (abbrev in Bridge.lean), so no type
    conversion is needed between B1 output and combining theorem input.
  - The expanded bridge uses 3-cell expansion for incidence, so it does NOT
    require the stand-coordinate incidence transfer hypothesis needed by
    the non-expanded bridge.
  - Geometric hypotheses (squares unit, tubes strip, tubes bounded) must be
    supplied by the caller. For configurations from DyadicBridgeGeneral,
    these are already proved.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge_Expanded
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FormatConversionLemmas
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.Bridge
open DiscretisedFurstenbergEstimate.Bridge.Geometric
open DirecretisedFurstenbergEstimate.FormatConversion.M2

-- Use Main abbreviations to avoid ambiguity with standalone InductionOnScales types
abbrev CTMainSquare (n : ℕ) := MainSquare n
abbrev CTMainTube (n : ℕ) := MainTube n
abbrev CTMainConfig (n : ℕ) (s C : ℝ) (M : ℕ) := MainConfig n s C M

/-- SL-4: B1 bridge decomposition for the combining theorem inductive step.

    Given a nice configuration at dyadic scale `n` with the required geometric
    hypotheses, apply the B1 induction-on-scales bridge to produce:
    - A coarse configuration at scale `m`
    - Fine configurations at scale `n - m` for each coarse square
    - Thinning, incidence, slope-cell matching, and cardinality relationships

    This is the engine of the combining theorem inductive step (OS Section 7):
    the coarse config corresponds to scale block 1, and the fine configs
    correspond to the remaining `n - 1` blocks.

    The coarse scale `m` should be chosen so that `dyadicDelta m ≈ Δ₁`
    (the first scale transition in the combining theorem). For example,
    `m = ⌊log₂(1/Δ₁)⌋`.

    Dependencies: `inductionOnScalesBridge_expanded_concrete`
-/
theorem b1_bridge_decomposition
    {n m : ℕ} (hnm : m ≤ n)
    (s : ℝ) (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁)
    (M : ℕ) (hM : 0 < M)
    (config : CTMainConfig n s C₁ M)
    (hP_nonempty : config.P₀.Nonempty)
    (h_squares_unit : ∀ p ∈ config.P₀,
      0 ≤ (p : CTMainSquare n).i ∧ (p : CTMainSquare n).i < (2 ^ n : ℤ) ∧
      0 ≤ (p : CTMainSquare n).j ∧ (p : CTMainSquare n).j < (2 ^ n : ℤ))
    (h_tubes_strip : ∀ T ∈ config.T₀,
      -(2 ^ n : ℤ) ≤ (T : CTMainTube n).a ∧ (T : CTMainTube n).a < (2 ^ n : ℤ))
    (h_tubes_bounded : config.T₀.card ≤ 12 * 16^n) :
    ∃ (K : ℝ), 1 ≤ K ∧
      K ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7 ∧
      ∃ (P : Finset (CTMainSquare n))
      (hP_sub : P ⊆ config.P₀)
      (tubeFamily : (p : CTMainSquare n) → p ∈ P → Finset (CTMainTube n))
      (CΔ : ℝ) (MΔ : ℕ) (hMΔ : 0 < MΔ)
      (coarseConfig : CTMainConfig m s CΔ MΔ)
      (CQ : CTMainSquare m → ℝ)
      (MQ : CTMainSquare m → ℕ)
      (hMQ : ∀ Q ∈ coarseConfig.P₀, 0 < MQ Q)
      (fineConfig : (Q : CTMainSquare m) → Q ∈ coarseConfig.P₀ →
        CTMainConfig (n - m) s (CQ Q) (MQ Q))
      (fineConfig_B1 : (Q : CTMainSquare m) → (hQ : Q ∈ coarseConfig.P₀) →
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
          (U_stand : StandTube m)
          (C : StandTube n),
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
      (∀ (Q : CTMainSquare m) (hQ : Q ∈ coarseConfig.P₀),
        K * (config.T₀.card : ℝ) * MΔ * MQ Q ≥
          (coarseConfig.T₀.card : ℝ) * ((fineConfig Q hQ).T₀.card : ℝ) * M) ∧
      (∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1) := by
  exact inductionOnScalesBridge_expanded_concrete hnm s hs hs_one C₁ hC₁ M hM
    config hP_nonempty h_squares_unit h_tubes_strip h_tubes_bounded

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
