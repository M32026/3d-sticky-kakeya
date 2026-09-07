import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Dyadic upper representatives
-/

namespace Kakeya.Cinematic

def DyadicUpperRepresentativeStatement : Prop :=
  ∀ {delta x : ℝ} {N k : ℕ},
    0 < delta →
    delta ≤ x →
    k < N →
    x ≤ (2 : ℝ) ^ (k + 1) * delta →
    (∀ j < k, ¬ x ≤ (2 : ℝ) ^ (j + 1) * delta) →
    (2 : ℝ) ^ (k + 1) * delta ≤ 2 * x

end Kakeya.Cinematic
