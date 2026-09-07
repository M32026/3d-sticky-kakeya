import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruningStatements

/-!
# Mass-retaining shifted-grid pruning for WZ2 `prop: sticky`

For non-commensurable `delta` and `rho`, a fixed-origin `delta`-cell can cross
a fixed-origin `rho`-grid boundary.  A common half-cell translate of the
`rho`-grid removes this obstruction without trimming any fine cell.

There are eight coordinatewise choices of shift, with every coordinate equal
to either `0` or `rho / 2`.  If `4 * delta ≤ rho`, every literal `delta`-cell
is contained in a cell of at least one shifted grid.  Assign each active fine
cell to one such shift and pigeonhole the eight choices by shaded mass.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- One of the eight coordinatewise half-cell shifts. -/
abbrev WZ2PaperGridShiftChoice := Fin 3 → Fin 2

/-- Coordinate shift, equal to either `0` or `rho / 2`. -/
def wz2PaperGridShiftCoordinate
    (rho : ℝ) (choice : WZ2PaperGridShiftChoice)
    (coordinate : Fin 3) : ℝ :=
  (choice coordinate : ℝ) * (rho / 2)

/-- Grid index after translating the origin coordinatewise by `0` or `rho/2`. -/
def wz2PaperShiftedGridIndex
    (rho : ℝ) (choice : WZ2PaperGridShiftChoice)
    (point : Point3) : WZ2PaperCellIndex :=
  (⌊(point 0 - wz2PaperGridShiftCoordinate rho choice 0) / rho⌋,
    ⌊(point 1 - wz2PaperGridShiftCoordinate rho choice 1) / rho⌋,
    ⌊(point 2 - wz2PaperGridShiftCoordinate rho choice 2) / rho⌋)

/-- One cell in the commonly shifted side-`rho` grid. -/
def wz2PaperShiftedGridCube
    (rho : ℝ) (choice : WZ2PaperGridShiftChoice)
    (cell : WZ2PaperCellIndex) : Set Point3 :=
  {point | wz2PaperShiftedGridIndex rho choice point = cell}

/--
Output of the eight-shift pigeonhole.

The selected fine cells remain literal whole cells of the original
fixed-origin `delta`-grid.  Only the coarse grid receives one common shift.
-/
structure WZ2PaperShiftedGridPruningData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta)
    (hrho : 0 < rho) where
  choice : WZ2PaperGridShiftChoice
  safeFineCells : Finset WZ2PaperCellIndex
  safeFineCells_subset :
    safeFineCells ⊆ wz1PaperActiveCells shading hdelta
  pruned : WZ1PaperTubeShading fine
  pruned_carrier_eq :
    ∀ index,
      pruned.carrier index =
        shading.carrier index ∩
          ⋃ fineCell ∈ safeFineCells,
            wz1PaperGridCube delta fineCell
  pruned_subshading :
    ∀ index, pruned.carrier index ⊆ shading.carrier index
  pruned_cubical :
    WZ1PaperIsCubicalShading pruned
  pruned_union_eq :
    pruned.union =
      ⋃ fineCell ∈ safeFineCells,
        wz1PaperGridCube delta fineCell
  retained_mass :
    (1 / 8 : ENNReal) * shading.mass ≤ pruned.mass
  pruned_mass_pos : 0 < pruned.mass
  safeFineCells_nonempty : safeFineCells.Nonempty
  coarseParent :
    WZ2PaperCellIndex → WZ2PaperCellIndex
  safeFineCell_contained :
    ∀ fineCell ∈ safeFineCells,
      wz1PaperGridCube delta fineCell ⊆
        wz2PaperShiftedGridCube rho choice
          (coarseParent fineCell)
  coarseCells : Finset WZ2PaperCellIndex
  coarseCells_eq :
    coarseCells = safeFineCells.image coarseParent
  coarseCells_nonempty : coarseCells.Nonempty
  availableFineCells :
    WZ2PaperCellIndex → Finset WZ2PaperCellIndex
  availableFineCells_eq :
    ∀ coarseCell,
      availableFineCells coarseCell =
        safeFineCells.filter fun fineCell =>
          coarseParent fineCell = coarseCell
  availableFineCells_nonempty :
    ∀ coarseCell ∈ coarseCells,
      (availableFineCells coarseCell).Nonempty
  availableFineCells_ready :
    ∀ coarseCell ∈ coarseCells,
      ∀ fineCell ∈ availableFineCells coarseCell,
        fineCell ∈ wz1PaperActiveCells pruned hdelta ∧
          wz1PaperGridCube delta fineCell ⊆
            wz2PaperShiftedGridCube rho choice coarseCell

/--
Choose a common half-cell shift that retains at least one eighth of the
shaded mass while deleting only whole literal `delta`-cells.
-/
def WZ2PropStickyShiftedGridPruningStatement : Prop :=
  ∀ {delta rho : ℝ},
    (hdelta : 0 < delta) →
    (hrho : 0 < rho) →
    4 * delta ≤ rho →
    rho ≤ 1 →
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ shading : WZ1PaperTubeShading fine,
        WZ1PaperIsCubicalShading shading →
        0 < shading.mass →
          Nonempty
            (WZ2PaperShiftedGridPruningData
              (delta := delta) (rho := rho)
              shading hdelta hrho)

end Kakeya.Assouad
