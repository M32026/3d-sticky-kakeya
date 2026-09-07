import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.Section7ProjectionRectangleGridCoverStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSDensityAbsorptionStatement

/-!
# Large-base terminal-grid parameters for projected-fiber uniformization

The local-child OS loss is exponential in the number of grid levels.  A
fixed small grid base would therefore cost a fixed negative power of
`delta`, which cannot be absorbed for arbitrarily small `eta`.  The paper
route instead chooses a sufficiently large fixed base after `eta` is known,
then chooses the terminal level so that the mesh is comparable to `delta`.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Choose a large grid base depending only on `eta`, and then at every sufficiently
small scale choose a terminal depth whose mesh is comparable to `delta`.

The atomization and local-child OS losses together cost at most
`delta^(-2*eta)`.  Combined with the separate band selector, this is exactly
the `delta^(-3*eta)` premise consumed by
`ProjectedFiberOSDensityAbsorptionStatement`.
-/
def ProjectedFiberGridParameterSelectionStatement : Prop :=
  ∀ eta : ℝ, 0 < eta →
    ∃ base : ℕ,
      3 ≤ base ∧
        ∃ delta₀ : ℝ,
          0 < delta₀ ∧ delta₀ < 1 ∧
            ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
              ∃ levels : ℕ,
                delta ≤ ((base ^ levels : ℝ)⁻¹) ∧
                ((base ^ levels : ℝ)⁻¹) <
                  (base : ℝ) * delta ∧
                projectedFiberAtomizationLoss
                    base levels
                    (section7GridIndexBound base levels) *
                    projectedFiberOSLoss base levels ≤
                  Kakeya.realRpowENN delta (-2 * eta)

end Kakeya.Assouad
