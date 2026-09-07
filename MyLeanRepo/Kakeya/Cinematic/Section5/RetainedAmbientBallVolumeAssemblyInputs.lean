import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientBallVolumeAssembly

/-!
# Retained ambient-ball volume assembly

The dyadic pointwise reduction retains `E₂` with
`volume E₀ ≤ logLoss * volume E₂`.  Ambient-ball assembly controls `E₂`.
This statement carries that retention loss through the bounded-overlap and
Katz--Tao sum, making the final real absorption factor explicit.
-/

open MeasureTheory

namespace Kakeya.Cinematic

def RetainedAmbientBallVolumeAssemblyStatement : Prop :=
  ∀ {E₀ E₂ : Set (ℝ × ℝ)}
    {F : FiniteFunctionFamily}
    {centers : Finset C2Function},
    ∀ (bins : C2Function → Set (ℝ × ℝ))
      (ambient : C2Function → FiniteFunctionFamily),
      ∀ {D delta C_KT logLoss target : ℝ} {B : ENNReal},
        0 ≤ D →
        0 < delta →
        0 ≤ logLoss →
        F.HasKatzTaoBound delta C_KT →
        B ≠ ⊤ →
        0 ≤ target →
        volume E₀ ≤ ENNReal.ofReal logLoss * volume E₂ →
        E₂ ⊆ ⋃ c ∈ (centers : Set C2Function), bins c →
        (∀ c ∈ centers,
          volume (bins c) ≤ B * (ambient c).card) →
        (∑ c ∈ centers, ((ambient c).card : ℝ)) ≤
          D ^ 3 * (F.card : ℝ) →
        logLoss * B.toReal * (D ^ 3 * (C_KT / delta)) ≤ target →
        volume E₀ ≤ ENNReal.ofReal target

end Kakeya.Cinematic
