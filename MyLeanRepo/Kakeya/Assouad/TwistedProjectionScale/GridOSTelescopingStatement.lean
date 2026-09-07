import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Finite telescoping for corrected grid OS transitions

Each corrected transition supplies

`(scale k / scale (k+1))^epsilon * V(k+1) ≤ 6889 * V(k)`.

This leaf multiplies finitely many such inequalities without division or
cancellation.  It depends only on positivity of the scale sequence, not on
the tube or grid realization of the states.
-/

namespace Kakeya.Assouad

/-- Cancellation-free finite product of the corrected one-step bounds. -/
def GridOSTelescopingStatement : Prop :=
  ∀ epsilon : ℝ,
    ∀ steps : ℕ,
      ∀ scale : ℕ → ℝ,
        ∀ projectedVolume : ℕ → ENNReal,
          (∀ index : ℕ, index ≤ steps → 0 < scale index) →
          (∀ index : ℕ, index < steps →
            Kakeya.realRpowENN
                (scale index / scale (index + 1)) epsilon *
              projectedVolume (index + 1) ≤
                (6889 : ENNReal) * projectedVolume index) →
            Kakeya.realRpowENN
                (scale 0 / scale steps) epsilon *
              projectedVolume steps ≤
                (6889 : ENNReal) ^ steps * projectedVolume 0

end Kakeya.Assouad
