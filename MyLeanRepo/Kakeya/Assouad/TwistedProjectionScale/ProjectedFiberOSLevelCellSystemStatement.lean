import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberGridLevelSelectionStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSCellThickeningStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSPreparationStatement

/-!
# Occupied projected-fiber cells at one local scale

At the grid level comparable to a requested scale `rho`, the final retained
projected set is the finite disjoint union of its nonempty occupied cell
bands.  Their areas are uniformly comparable and every individual
`rho`-thickening has the same explicit area bound.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- The same-level grid cells containing at least one retained OS center. -/
def projectedFiberOSOccupiedCells
    {delta eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {f : SlopeFunction}
    (prepared : ProjectedFiberOSPreparationData (eta := eta) Y f)
    (level : ℕ) :
    Finset (DiscreteSet 2) :=
  (planarGridPartition
      prepared.base level prepared.atomized.centers).filter fun cell =>
    (prepared.uniform.centers ∩ cell).Nonempty

/-- The retained planar band below one occupied same-level grid cell. -/
def projectedFiberOSPreparedCellSet
    {delta eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {f : SlopeFunction}
    (prepared : ProjectedFiberOSPreparationData (eta := eta) Y f)
    (cell : DiscreteSet 2) :
    Set Point2 :=
  projectedFiberOSCellBand
    Y f prepared.bandData prepared.base prepared.levels
      prepared.uniform.centers cell

/--
The finite uniform cell system at one scale.

The displayed `global_eq` is the exact input expected by
`FiniteUniformCellGlobalizationStatement`; no closure, null-set replacement,
or reindexed local shading occurs.
-/
structure ProjectedFiberOSLevelCellSystemData
    {delta eta rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {f : SlopeFunction}
    (prepared : ProjectedFiberOSPreparationData (eta := eta) Y f)
    (level : ℕ) where
  level_le : level ≤ prepared.levels + 1
  coarse_mesh_le :
    ((prepared.base ^ level : ℝ)⁻¹) ≤ rho
  rho_lt_coarse_mesh :
    rho <
      (prepared.base : ℝ) *
        ((prepared.base ^ level : ℝ)⁻¹)
  cells_nonempty :
    (projectedFiberOSOccupiedCells prepared level).Nonempty
  global_eq :
    twistedUnion prepared.density.globalShading f =
      finiteAtomUnion
        (projectedFiberOSOccupiedCells prepared level)
        (projectedFiberOSPreparedCellSet prepared)
  cell_measurable :
    ∀ cell ∈ projectedFiberOSOccupiedCells prepared level,
      MeasurableSet
        (projectedFiberOSPreparedCellSet prepared cell)
  cell_disjoint :
    ∀ cell₁ ∈ projectedFiberOSOccupiedCells prepared level,
      ∀ cell₂ ∈ projectedFiberOSOccupiedCells prepared level,
        cell₁ ≠ cell₂ →
          Disjoint
            (projectedFiberOSPreparedCellSet prepared cell₁)
            (projectedFiberOSPreparedCellSet prepared cell₂)
  cell_area_nonzero :
    ∀ cell ∈ projectedFiberOSOccupiedCells prepared level,
      volume (projectedFiberOSPreparedCellSet prepared cell) ≠ 0
  cell_area_ne_top :
    ∀ cell ∈ projectedFiberOSOccupiedCells prepared level,
      volume (projectedFiberOSPreparedCellSet prepared cell) ≠ ⊤
  cell_area_comparable :
    ∀ cell₁ ∈ projectedFiberOSOccupiedCells prepared level,
      ∀ cell₂ ∈ projectedFiberOSOccupiedCells prepared level,
        volume (projectedFiberOSPreparedCellSet prepared cell₁) ≤
          4 *
            volume
              (projectedFiberOSPreparedCellSet prepared cell₂)
  cell_thickening_bound :
    ∀ cell ∈ projectedFiberOSOccupiedCells prepared level,
      volume
          (Metric.cthickening rho
            (projectedFiberOSPreparedCellSet prepared cell)) ≤
        ENNReal.ofReal
          (((((2 * prepared.base + 3 : ℕ) : ℝ) * rho) ^ 2) *
            Real.pi)

/--
Choose the grid level comparable to `rho` and expose the exact finite cell
system used by local-to-global projection uniformity.
-/
def ProjectedFiberOSLevelCellSystemStatement : Prop :=
  ProjectedFiberGridLevelSelectionStatement →
    ProjectedFiberOSCellThickeningStatement →
      ∀ {delta eta : ℝ},
        0 < delta →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            ∀ f : SlopeFunction,
              ∀ prepared :
                  ProjectedFiberOSPreparationData (eta := eta) Y f,
                ∀ rho : ℝ,
                  0 < rho →
                  delta ≤ rho →
                  rho ≤ 1 →
                    ∃ level : ℕ,
                      Nonempty
                        (ProjectedFiberOSLevelCellSystemData
                          (rho := rho) prepared level)

end Kakeya.Assouad
