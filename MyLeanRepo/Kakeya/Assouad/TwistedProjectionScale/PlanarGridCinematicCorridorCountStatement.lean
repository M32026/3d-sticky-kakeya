import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.PlanarGridPartitionTreeStatement
import MyLeanRepo.Kakeya.Cinematic.Definitions

/-!
# Grid cells meeting a bounded-slope cinematic corridor

A graph of bounded slope has one-dimensional complexity.  At mesh `h`, a
corridor of width `O(h)` around such a graph meets only `O(h⁻¹)` planar floor
grid cells, not `O(h⁻²)`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The graph of a cinematic extension over the unit interval, in `Point2`. -/
def cinematicExtensionGraph
    (g : Kakeya.Cinematic.C2Function) : Set Point2 :=
  {q |
    q 1 ∈ Set.Icc (0 : ℝ) 1 ∧
      q 0 = g.extension (q 1)}

/-- Occupied grid cells whose center set meets a cinematic corridor. -/
def planarGridCinematicCorridorCells
    (base level : ℕ)
    (A : DiscreteSet 2)
    (g : Kakeya.Cinematic.C2Function)
    (r : ℝ) :
    Finset (DiscreteSet 2) := by
  classical
  exact
    (planarGridPartition base level A).filter fun cell =>
      ((cell : Set Point2) ∩
        Metric.cthickening r (cinematicExtensionGraph g)).Nonempty

/--
An `L`-Lipschitz cinematic graph corridor of radius at most `D` grid meshes
meets an explicit `O_{L,D}(base^level)` number of occupied cells.

The bound is deliberately generous.  Its important feature is linear rather
than quadratic growth in `base^level`.
-/
def PlanarGridCinematicCorridorCountStatement : Prop :=
  ∀ A : DiscreteSet 2,
    ∀ base level slopeBlocks radiusBlocks : ℕ,
      2 ≤ base →
      ∀ g : Kakeya.Cinematic.C2Function,
        LipschitzOnWith (slopeBlocks : NNReal) g.extension
          (Set.Icc (0 : ℝ) 1) →
        ∀ r : ℝ,
          0 ≤ r →
          r ≤
            (radiusBlocks : ℝ) *
              ((base ^ level : ℝ)⁻¹) →
          (planarGridCinematicCorridorCells
              base level A g r).card ≤
            (base ^ level + 2 * radiusBlocks + 3) *
              (2 *
                  (2 * radiusBlocks +
                    slopeBlocks * (1 + 2 * radiusBlocks) + 2) +
                3)

end Kakeya.Assouad
