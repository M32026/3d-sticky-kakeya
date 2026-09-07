import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Terminal-or-window-budget dichotomy for the corrected grid OS transition

The full-window transition clips both boundary caps.  Its raw density is
`(1 / 800) * scale ^ (4 * eta)`, and the additive loss is absorbed under the
budget

`ofReal (400 * rho) ≤ (1 / 800) * scale ^ (4 * eta)`.

If this budget fails at sufficiently small scale, the selected radius has
already reached the terminal threshold `scale ^ (epsilon ^ 2)`.
-/

namespace Kakeya.Assouad

/--
Every nonnegative selected radius is either terminal or satisfies the exact
two-sided clipping budget consumed by the corrected grid OS transition.
-/
def GridOSWindowBudgetDichotomyStatement : Prop :=
  ∀ epsilon eta : ℝ,
    0 < epsilon →
    epsilon < 1 →
    0 < eta →
    4 * eta < epsilon ^ 2 →
      ∃ scale₀ : ℝ,
        0 < scale₀ ∧
        scale₀ ≤ 1 ∧
        ∀ scale : ℝ,
          0 < scale →
          scale ≤ scale₀ →
          ∀ rho : ℝ,
            0 ≤ rho →
              Real.rpow scale (epsilon ^ 2) ≤ rho ∨
                ENNReal.ofReal (400 * rho) ≤
                  ENNReal.ofReal (1 / 800 : ℝ) *
                    Kakeya.realRpowENN scale (4 * eta)

end Kakeya.Assouad
