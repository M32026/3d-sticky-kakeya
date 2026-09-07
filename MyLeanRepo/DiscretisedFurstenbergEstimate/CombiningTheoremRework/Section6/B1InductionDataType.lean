module

/-
  B1 Induction Data Structure

  Extracted from PerSquareRetention.lean to break the Prop73 import dependency.

  Contains the `B1InductionData` structure which packages the output of
  `b1_bridge_decomposition` (B1 induction on scales) into a single object
  for consumption by the Section 6 fine-ratio producer and coarse branch.

  Whiteprint node: b1_induction_data_type
  Status: COMPLETE (extraction)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FormatConversionLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionConfigurations
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge_Wrapper
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section6

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.InductionConfigurations
open DirecretisedFurstenbergEstimate.FormatConversion.M2

/-- δd abbreviation. -/
def δd (n : ℕ) : ℝ := DiscretisedFurstenbergEstimate.dyadicDelta n

/-- Data produced by the B1 bridge decomposition (Proposition 5.1).

    Packages coarse/fine configurations, per-square retention data, and
    geometry for the Section 6 integration.

    Given original configuration at scale `n`, B1 bridge at coarse scale `m`,
    this packages coarse/fine configurations, per-square retention data, and
    tube family information. -/
structure B1InductionData
    (n m : ℕ) (hnm : m ≤ n)
    (s t : ℝ) (C₁ : ℝ) (M : ℕ)
    (config : CombiningTheorem.NiceConfiguration n s C₁ M) where
  K : ℝ
  hK_ge1 : 1 ≤ K

  P : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n)
  hP_sub : P ⊆ config.P₀
  hP_nonempty : P.Nonempty

  CΔ : ℝ
  MΔ : ℕ
  hMΔ_pos : 0 < MΔ
  coarseConfig : CombiningTheorem.NiceConfiguration m s CΔ MΔ

  CQ : DiscretisedFurstenbergEstimate.DyadicSquare m → ℝ
  MQ : DiscretisedFurstenbergEstimate.DyadicSquare m → ℕ
  hMQ : ∀ Q ∈ coarseConfig.P₀, 0 < MQ Q
  fineConfig : (Q : DiscretisedFurstenbergEstimate.DyadicSquare m) → (hQ : Q ∈ coarseConfig.P₀) →
    CombiningTheorem.NiceConfiguration (n - m) s (CQ Q) (MQ Q)
  fineConfig_B1 : (Q : DiscretisedFurstenbergEstimate.DyadicSquare m) → (hQ : Q ∈ coarseConfig.P₀) →
    B1BridgeHypotheses (n - m) (fineConfig Q hQ)

  h_coarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm)
  h_per_Q_ret : ∀ Q ∈ coarseConfig.P₀,
      ((config.P₀.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card : ℝ) ≤
      K * ((P.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card : ℝ)

  tubeFamily : (p : DiscretisedFurstenbergEstimate.DyadicSquare n) → p ∈ P →
    Finset (DiscretisedFurstenbergEstimate.DyadicTube n)
  h_tube_sub : ∀ p hp, tubeFamily p hp ⊆ config.tubeFamily p (hP_sub hp)
  h_tube_size : ∀ p hp, (M : ℝ) ≤ K * ((tubeFamily p hp).card : ℝ)
  h_tube_intersect : ∀ p hp T, T ∈ tubeFamily p hp →
      (T.toSet ∩ p.toSet).Nonempty
  h_tube_geometry : ∀ (p : DiscretisedFurstenbergEstimate.DyadicSquare n) (hp : p ∈ P)
      (T : DiscretisedFurstenbergEstimate.DyadicTube n), T ∈ tubeFamily p hp →
    ∃ (hQ : InductionConfigurations.containingSquare hnm p ∈ coarseConfig.P₀)
      (U_stand : _root_.DyadicTube m)
      (C : _root_.DyadicTube n),
      C ∈ DiscretisedFurstenbergEstimate.Bridge.Geometric.coveringCells n T.a T.b ∧
      DiscretisedFurstenbergEstimate.Bridge.tubeToMainShifted U_stand ∈
        coarseConfig.tubeFamily (InductionConfigurations.containingSquare hnm p) hQ ∧
      C.toSet ⊆ U_stand.toSet

  hCΔ_compare : CΔ ≤ K * C₁ ∧ C₁ ≤ K * CΔ
  hCQ_compare : ∀ Q ∈ coarseConfig.P₀, CQ Q ≤ K * C₁ ∧ C₁ ≤ K * CQ Q
  h_coarse_slope : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1

end DirecretisedFurstenbergEstimate.Section6

end
