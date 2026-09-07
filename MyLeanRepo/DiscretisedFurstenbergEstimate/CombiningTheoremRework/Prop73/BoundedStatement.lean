module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.RestructuredStatement

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate.FormatConversion.M2

def combiningC (τ K : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, C_P => K + C_P + 1
  | n + 2, C_P =>
      let C_n : ℝ := (n + 2 : ℝ) + 4
      let C_P_fine : ℝ := C_P + 2 * C_n
      (1 + 7) * (1 + 1 + combiningCprime (n + 1) τ) +
        K + C_P + 8 + combiningC τ K (n + 1) C_P_fine

abbrev CombiningInductionUniform_with_data_bounded
    (s t ε_inc K : ℝ) : Prop :=
  1 ≤ K →
  ∃ ε_G0 η0 : ℝ,
    0 < ε_G0 ∧ 0 < η0 ∧
    (∀ ε_G η : ℝ,
      0 < ε_G → ε_G ≤ ε_G0 →
      0 < η → η ≤ η0 →
      (η + 2 * ε_G) * (1 - s) / (min t 1 - s) + η ≤ ε_inc) ∧
    ∀ τ : ℝ, 0 < τ → τ < 1 →
    ∀ n : ℕ, 0 < n →
    ∃ lam_0 : ℝ, 0 < lam_0 ∧
      ∀ C_P : ℝ, 1 ≤ C_P →
        0 < combiningC τ K n C_P ∧
        ∀ ε_N lam : ℝ,
          0 < ε_N → 0 < lam → lam ≤ lam_0 →
          ∀ h_uniform : UniformIncidenceData s t ε_inc,
            ∃ δ₀ : ℝ, 0 < δ₀ ∧
            ∀ ε_G η : ℝ,
              0 < ε_G → ε_G ≤ ε_G0 → ε_N ≤ ε_G →
              0 < η → η ≤ η0 →
              ∀ k : ℕ, dyadicDelta k ≤ δ₀ →
              ∀ (M : ℕ)
                (config : CTNiceConfiguration k s
                  (Real.rpow (dyadicDelta k) (-lam)) M)
                (Δ : Fin (n + 1) → ℝ)
                (scaleClass : Fin n → ScaleClass)
                (N : Fin n → ℕ)
                (C_between : Fin n → ℝ),
                CombiningConfig s t τ n ε_G η lam ε_N C_P
                  C_between k M config Δ scaleClass N →
                B1BridgeHypotheses k config →
                CombiningExtraHypotheses_v2
                  s t ε_G η ε_N C_P ε_inc
                  n lam k M config Δ scaleClass →
                CombiningConclusion
                  s t τ ε_G η ε_N C_P
                  (combiningC τ K n C_P)
                  (combiningCprime n τ)
                  lam n Δ scaleClass k M config

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
