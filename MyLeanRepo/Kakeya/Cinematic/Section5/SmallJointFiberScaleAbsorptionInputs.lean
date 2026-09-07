import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Absorb the small joint retained-fiber regime

When the joint retained scale is smaller than the logarithmic threshold needed
for the separation-based Lemma 47 branch, the representative retention lower
bound directly controls the original multiplicity.  One additional exponent
absorbs the dyadic logarithmic loss.
-/

namespace Kakeya.Cinematic

def SmallJointFiberScaleAbsorptionStatement : Prop :=
  ∀ K metricExponent tangencyExponent logExponent targetExponent : ℝ,
    1 ≤ K →
    0 < metricExponent →
    0 < tangencyExponent →
    0 < logExponent →
    (3 / 2 : ℝ) *
        (metricExponent + tangencyExponent + logExponent) <
      targetExponent →
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ {delta t Delta logLoss : ℝ} {mu q : ℕ},
        0 < delta →
        delta ≤ delta₀ →
        delta ≤ Delta →
        Delta ≤ t →
        t ≤ 8 * K →
        0 < mu →
        1 ≤ logLoss →
        logLoss ≤ Real.rpow delta (-logExponent) →
        q < 8 * logLoss →
        Real.rpow (t / (8 * K)) metricExponent *
              Real.rpow (Delta / (2 * t)) tangencyExponent *
              (mu : ℝ) <
            4 * ((q : ℝ) + 1) →
        1 ≤
          Real.rpow delta (-targetExponent) *
            Real.rpow (mu : ℝ) (-3 / 2 : ℝ)

end Kakeya.Cinematic
