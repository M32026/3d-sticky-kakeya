import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Absorb the finite planar-volume loss at the terminal scale

After `steps` corrected transitions and the final terminal one-scale
inequality, telescoping gives

`delta ^ p ≤ 6889 ^ steps * V`,

where `p = innerEpsilon + innerEpsilon² * (2 - innerEpsilon)`.

If `p < targetEpsilon`, sufficiently small `delta` absorbs the fixed finite
factor and yields `delta ^ targetEpsilon ≤ V`.
-/

namespace Kakeya.Assouad

/-- Absorb the complete finite `6889 ^ steps` loss into the exponent gap. -/
def GridOSFinalConstantAbsorptionStatement : Prop :=
  ∀ innerEpsilon targetEpsilon : ℝ,
    0 < innerEpsilon →
    innerEpsilon < 1 →
    innerEpsilon +
        innerEpsilon ^ 2 * (2 - innerEpsilon) <
      targetEpsilon →
      ∀ steps : ℕ,
        ∃ delta₀ : ℝ,
          0 < delta₀ ∧
          delta₀ ≤ 1 ∧
          ∀ delta : ℝ,
            0 < delta →
            delta ≤ delta₀ →
            ∀ V : ENNReal,
              Kakeya.realRpowENN
                    delta
                    (innerEpsilon +
                      innerEpsilon ^ 2 *
                        (2 - innerEpsilon)) ≤
                  (6889 : ENNReal) ^ steps * V →
                Kakeya.realRpowENN delta targetEpsilon ≤ V

end Kakeya.Assouad
