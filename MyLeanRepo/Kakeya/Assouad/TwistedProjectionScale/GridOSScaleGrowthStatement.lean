import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# Fixed-constant growth below the one-scale selected radius

The one-scale theorem selects

`rho > scale ^ (1 - epsilon ^ 2)`.

At sufficiently small `scale`, this is larger than any fixed multiple
`D * scale`.  The same arithmetic leaf is used with `D = 6` at every
nonterminal state and with `D = 6 * base` at the initial terminal grid,
whose mesh is only bounded by `base * delta`.
-/

namespace Kakeya.Assouad

/--
Absorb a fixed linear enlargement into the power gap between `scale` and
`scale ^ (1 - epsilon ^ 2)`.
-/
def GridOSScaleGrowthStatement : Prop :=
  ∀ epsilon D : ℝ,
    0 < epsilon →
    epsilon < 1 →
    0 ≤ D →
      ∃ scale₀ : ℝ,
        0 < scale₀ ∧
        scale₀ ≤ 1 ∧
        ∀ scale rho : ℝ,
          0 < scale →
          scale ≤ scale₀ →
          Real.rpow scale (1 - epsilon ^ 2) < rho →
            D * scale ≤ rho

end Kakeya.Assouad
