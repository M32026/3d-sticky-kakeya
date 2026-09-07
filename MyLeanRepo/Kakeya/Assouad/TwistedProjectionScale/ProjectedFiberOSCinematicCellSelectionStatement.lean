import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.PlanarGridCinematicCorridorCountStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSCellThickening
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSLevelCellSystemStatement

/-!
# Select occupied projected cells meeting one cinematic corridor

A point of an OS cell band lies in a terminal grid atom around one retained
center.  Thus a local subset lying in a cinematic corridor can meet only
coarse occupied cells whose retained centers meet the corridor enlarged by
two terminal meshes.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Corridor radius after moving a point to its terminal atom center. -/
def projectedFiberOSCinematicExpandedRadius
    {delta eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {f : SlopeFunction}
    (prepared : ProjectedFiberOSPreparationData (eta := eta) Y f)
    (r : ℝ) :
    ℝ :=
  r + 2 * ((prepared.base ^ prepared.levels : ℝ)⁻¹)

/--
Occupied coarse cells whose retained center set meets the enlarged cinematic
corridor.
-/
def projectedFiberOSCinematicCells
    {delta eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {f : SlopeFunction}
    (prepared : ProjectedFiberOSPreparationData (eta := eta) Y f)
    (level : ℕ)
    (g : Kakeya.Cinematic.C2Function)
    (r : ℝ) :
    Finset (DiscreteSet 2) := by
  classical
  exact
    (projectedFiberOSOccupiedCells prepared level).filter fun cell =>
      ((cell : Set Point2) ∩
        Metric.cthickening
          (projectedFiberOSCinematicExpandedRadius prepared r)
          (cinematicExtensionGraph g)).Nonempty

/--
Any local subset of the final global projected set that lies in one
cinematic corridor is supported on the selected occupied cell bands.

The cardinality comparison is with the exact cell family consumed by
`PlanarGridCinematicCorridorCountStatement`; the only radius increase is the
terminal-atom center error.
-/
def ProjectedFiberOSCinematicCellSelectionStatement : Prop :=
  ∀ {delta eta rho : ℝ},
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∀ Y : Kakeya.Streamlined.TubeShading F,
        ∀ f : SlopeFunction,
          ∀ prepared :
              ProjectedFiberOSPreparationData (eta := eta) Y f,
            ∀ level : ℕ,
              ∀ cellSystem :
                  ProjectedFiberOSLevelCellSystemData
                    (rho := rho) prepared level,
                ∀ g : Kakeya.Cinematic.C2Function,
                  ∀ r : ℝ, 0 ≤ r →
                    ∀ localSet : Set Point2,
                      localSet ⊆
                          twistedUnion
                            prepared.density.globalShading f →
                      localSet ⊆
                          Metric.cthickening r
                            (cinematicExtensionGraph g) →
                        (projectedFiberOSCinematicCells
                            prepared level g r).card ≤
                          (planarGridCinematicCorridorCells
                            prepared.base level
                            prepared.atomized.centers g
                            (projectedFiberOSCinematicExpandedRadius
                              prepared r)).card ∧
                        localSet ⊆
                          finiteAtomUnion
                            (projectedFiberOSCinematicCells
                              prepared level g r)
                            (projectedFiberOSPreparedCellSet prepared)

end Kakeya.Assouad
