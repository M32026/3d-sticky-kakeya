import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Absorb the singleton retained-fiber regime

If the safe uniform fiber count is one, the two-ends retention lower bound
forces the original multiplicity to grow more slowly than the final
`mu ^ (-3 / 2)` budget allows.  This is a pure scale lemma, independent of
rectangle counting.
-/

namespace Kakeya.Cinematic

def SingletonFiberScaleAbsorptionStatement : Prop :=
  ∀ K metricExponent tangencyExponent targetExponent : ℝ,
    1 ≤ K →
    0 < metricExponent →
    0 < tangencyExponent →
    (3 / 2 : ℝ) * (metricExponent + tangencyExponent) <
      targetExponent →
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ {delta t Delta : ℝ} {mu : ℕ},
        0 < delta →
        delta ≤ delta₀ →
        delta ≤ Delta →
        Delta ≤ t →
        t ≤ 8 * K →
        0 < mu →
        Real.rpow (t / (8 * K)) metricExponent *
              Real.rpow (Delta / (2 * t)) tangencyExponent *
              (mu : ℝ) <
            8 →
        1 ≤
          Real.rpow delta (-targetExponent) *
            Real.rpow (mu : ℝ) (-3 / 2 : ℝ)

end Kakeya.Cinematic
