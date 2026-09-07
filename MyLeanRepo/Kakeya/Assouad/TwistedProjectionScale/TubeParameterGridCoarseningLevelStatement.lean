import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridOSStateStatements

/-!
# Select a coarser level after the one-scale radius is known

The terminal delta-grid mesh is only comparable to the original fine tube
radius.  After the one-scale theorem chooses a larger radius `rho`, the
small-scale threshold guarantees that the current mesh is at most `rho / 6`.

Choose the first grid level, moving from coarse to fine, whose mesh is at most
`rho / 6`.  It lies no finer than the current level and differs from `rho / 6`
by less than one factor of `base`.
-/

namespace Kakeya.Assouad

/--
Match a selected radius to a no-finer level of the same frozen delta-grid
parameter tree.
-/
def TubeParameterGridCoarseningLevelStatement : Prop :=
  ∀ base levels currentLevel : ℕ,
    2 ≤ base →
    currentLevel ≤ levels →
      ∀ rho : ℝ,
        0 < rho →
        rho ≤ 1 →
        6 * ((base ^ currentLevel : ℝ)⁻¹) ≤ rho →
          ∃ nextLevel : ℕ,
            nextLevel ≤ currentLevel ∧
            nextLevel ≤ levels ∧
            6 * ((base ^ nextLevel : ℝ)⁻¹) ≤ rho ∧
            rho <
              6 * (base : ℝ) *
                ((base ^ nextLevel : ℝ)⁻¹)

end Kakeya.Assouad
