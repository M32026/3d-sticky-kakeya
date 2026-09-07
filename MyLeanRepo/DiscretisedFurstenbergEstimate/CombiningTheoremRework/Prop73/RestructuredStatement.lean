module

/-
  Restructured Prop73 Statement — Shared type definitions

  Contains the common types used by the restructured Prop73 induction:
  - Prop73Smallness
  - CombiningExtraHypotheses_v2 (with ε_inc from Theorem 6.1)
  - CombiningConclusion
  - CombiningInductionUniform (correct quantifier hierarchy)
  - CombiningInductionUniform_with_data

  Whiteprint node: combining_theorem_genuine / restructure
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformIncidenceData
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M2
open DirecretisedFurstenbergEstimate.RegularIncidence

/-- Smallness of ε_G, η relative to output exponent ε_0 from regular incidence
    estimate (Theorem 6.1). Type-valued so ε_0 is accessible as data. -/
structure Prop73Smallness (ε_G η s t : ℝ) where
  hεG_pos : 0 < ε_G
  hη_pos : 0 < η
  ε_0 : ℝ
  hε0_pos : 0 < ε_0
  hεG_lt : ε_G < ε_0
  h_small : (η + 2 * ε_G) * (1 - s) / (min t 1 - s) + η ≤ ε_0

/-- Extra hypotheses with ε_inc (output exponent from regular incidence).
    Replaces CombiningExtraHypotheses from Statement.lean. -/
structure CombiningExtraHypotheses_v2
    (s t ε_G η ε_N C_P ε_inc : ℝ) (n : ℕ) (lam : ℝ) (k M : ℕ)
    (config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
    (Δ : Fin (n + 1) → ℝ) (scaleClass : Fin n → ScaleClass) where
  h_slope : ∀ T ∈ config.T₀, |T.slope| ≤ 1
  h_tj_ge_t : ∀ (j : Fin n) (t_j : ℝ),
    scaleClass j = ScaleClass.good t_j → t ≤ t_j
  h_tj_le_two : ∀ (j : Fin n) (t_j : ℝ),
    scaleClass j = ScaleClass.good t_j → t_j ≤ 2
  hε_inc_pos : 0 < ε_inc
  h_exp_condition : (η + 2 * ε_G) * (1 - s) / (min t 1 - s) + η ≤ ε_inc

/-- Helper: the inner bound conclusion, parameterized over C, C', lam. -/
abbrev CombiningConclusion (s t τ ε_G η ε_N C_P C C' lam : ℝ) (n : ℕ)
    (Δ : Fin (n + 1) → ℝ) (scaleClass : Fin n → ScaleClass)
    (k M : ℕ)
    (config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M) : Prop :=
  (config.T₀.card : ENNReal) ≥
    ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η n Δ scaleClass)

/-- Uniform combining induction — correct quantifier hierarchy.

    Thresholds ε_G0, η0, lam_0, C' depend ONLY on s,t,τ,n.
    C may depend on C_P. -/
abbrev CombiningInductionUniform (s t τ : ℝ) (n : ℕ) : Prop :=
  ∃ (ε_G0 η0 lam_0 C' : ℝ),
    0 < ε_G0 ∧ 0 < η0 ∧ 0 < lam_0 ∧ 0 < C' ∧
    ∀ (C_P : ℝ), 1 ≤ C_P →
      ∃ (C : ℝ), 0 < C ∧
        ∀ (ε_G η ε_N lam : ℝ),
          0 < ε_G → ε_G ≤ ε_G0 →
          0 < η → η ≤ η0 →
          0 < ε_N → ε_N ≤ ε_G →
          0 < lam → lam ≤ lam_0 →
            ∃ (δ₀ : ℝ), 0 < δ₀ ∧
              ∀ (k : ℕ), dyadicDelta k ≤ δ₀ →
                ∀ (M : ℕ)
                  (config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
                  (Δ : Fin (n + 1) → ℝ)
                  (scaleClass : Fin n → ScaleClass)
                  (N : Fin n → ℕ)
                  (C_between : Fin n → ℝ),
                  CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N →
                  B1BridgeHypotheses k config →
                  CombiningConclusion s t τ ε_G η ε_N C_P C C' lam n Δ scaleClass k M config

/-- Uniform combining induction with extra hypotheses.

    ε_inc is fixed (from Theorem 6.1 for given s,t).
    Thresholds ε_G0, η0 are chosen so all admissible ε_G, η satisfy γ+η ≤ ε_inc.
    C' depends only on n,τ (outside C_P quantifier). -/
abbrev CombiningInductionUniform_with_data (s t τ ε_inc : ℝ) (n : ℕ) : Prop :=
  ∃ (ε_G0 η0 lam_0 C' : ℝ),
    0 < ε_G0 ∧ 0 < η0 ∧ 0 < lam_0 ∧ 0 < C' ∧
    (∀ (ε_G η : ℝ), 0 < ε_G → ε_G ≤ ε_G0 → 0 < η → η ≤ η0 →
      (η + 2 * ε_G) * (1 - s) / (min t 1 - s) + η ≤ ε_inc) ∧
    ∀ (C_P : ℝ), 1 ≤ C_P →
      ∃ (C : ℝ), 0 < C ∧
        ∀ (ε_G η ε_N lam : ℝ),
          0 < ε_G → ε_G ≤ ε_G0 →
          0 < η → η ≤ η0 →
          0 < ε_N → ε_N ≤ ε_G →
          0 < lam → lam ≤ lam_0 →
          (h_uniform : UniformIncidenceData s t ε_inc) →
            ∃ (δ₀ : ℝ), 0 < δ₀ ∧
              ∀ (k : ℕ), dyadicDelta k ≤ δ₀ →
                ∀ (M : ℕ)
                  (config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
                  (Δ : Fin (n + 1) → ℝ)
                  (scaleClass : Fin n → ScaleClass)
                  (N : Fin n → ℕ)
                  (C_between : Fin n → ℝ),
                  CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N →
                  B1BridgeHypotheses k config →
                  CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P ε_inc n lam k M config Δ scaleClass →
                  CombiningConclusion s t τ ε_G η ε_N C_P C C' lam n Δ scaleClass k M config

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
