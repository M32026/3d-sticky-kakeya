import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Finite termination of the selected-scale iteration

At every nonterminal step the one-scale theorem gives

`scale (k + 1) > scale k ^ (1 - epsilon ^ 2)`.

After finitely many steps, depending only on `epsilon`, the scale therefore
exceeds the terminal threshold `delta ^ (epsilon ^ 2)`.
-/

namespace Kakeya.Assouad

/-- The paper's finite `epsilon⁻²`-type termination argument. -/
def GridOSTerminationStatement : Prop :=
  ∀ epsilon : ℝ,
    0 < epsilon →
    epsilon < 1 →
      ∃ steps : ℕ,
        (1 - epsilon ^ 2) ^ steps ≤ epsilon ^ 2 ∧
        ∀ delta : ℝ,
          0 < delta →
          delta < 1 →
          ∀ scale : ℕ → ℝ,
            scale 0 = delta →
            (∀ index : ℕ, index ≤ steps → 0 < scale index) →
            (∀ index : ℕ, index < steps →
              Real.rpow (scale index) (1 - epsilon ^ 2) <
                scale (index + 1)) →
              Real.rpow delta (epsilon ^ 2) < scale steps

end Kakeya.Assouad
