import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberGridParameterSelectionHelpers
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameter4OSShadingRetentionStatement

/-!
# Large-base parameters for the four-dimensional tube-parameter OS tree

Choose a sufficiently large fixed base after the structural loss `eta` is
known.  At every sufficiently small tube radius `delta`, choose the terminal
depth so the mesh is comparable to `delta`.

The exact terminal-cell fiber regularization costs one logarithm of the active
indexed cardinality.  The local OS tree costs one power of
`2 * (log₂((base+1)^4)+1)` per level.  Under the extremal cardinality upper
bound, both losses are absorbed by one additional power `delta^{-eta}`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Combined initial terminal-cell and OS branching cardinality loss. -/
def tubeParameterGridInitialLoss
    (activeCard base levels : ℕ) : ENNReal :=
  (Nat.log 2 activeCard + 1 : ENNReal) *
    (2 : ENNReal) *
      ((((2 * (Nat.log 2 ((base + 1) ^ 4) + 1)) ^ levels :
        ℕ)) : ENNReal)

/--
Choose a large base and a delta-scale terminal depth with uniformly
absorbable initial parameter-tree losses.
-/
def TubeParameterGridParameterSelectionStatement : Prop :=
  ∀ eta : ℝ,
    0 < eta →
      ∃ base : ℕ,
        3 ≤ base ∧
          ∃ delta₀ : ℝ,
            0 < delta₀ ∧ delta₀ < 1 ∧
              ∀ delta : ℝ,
                0 < delta →
                delta ≤ delta₀ →
                ∀ activeCard : ℕ,
                  (activeCard : ENNReal) ≤
                    Kakeya.realRpowENN delta (-3) →
                  ∃ levels : ℕ,
                    delta ≤ ((base ^ levels : ℝ)⁻¹) ∧
                    ((base ^ levels : ℝ)⁻¹) <
                      (base : ℝ) * delta ∧
                    tubeParameterGridInitialLoss
                        activeCard base levels ≤
                      Kakeya.realRpowENN delta (-eta)

end Kakeya.Assouad
