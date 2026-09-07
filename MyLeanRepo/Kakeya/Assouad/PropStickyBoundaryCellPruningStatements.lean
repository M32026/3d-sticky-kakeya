import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingStatements
import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement
import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers

/-!
# Boundary-cell pruning for WZ2 `prop: sticky`

The literal `delta`- and `rho`-grids need not be nested.  This module
isolates the geometric repair used before exact balancing: delete every
whole active `delta`-cell that is not contained in one literal `rho`-cell.

The crossing cells lie in an axis-parallel boundary layer of volume
`O(delta / rho)` inside the cropped paper window.  Under a pointwise
multiplicity cap this gives the corresponding aggregate shading-mass loss.
The surviving cells are grouped by their unique containing `rho`-cell and
are ready for `WZ2PropStickyExactCellBalancingStatement`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The literal `rho`-cell assigned to one active `delta`-cell corner. -/
def wz2PaperBoundaryCoarseParent
    (delta rho : ℝ) (cell : WZ2PaperCellIndex) :
    WZ2PaperCellIndex :=
  wz1PaperGridIndex rho (cellCorner delta cell)

/-- Active `delta`-cells contained in their assigned literal `rho`-cell. -/
def wz2PaperBoundarySafeFineCells
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta) : Finset WZ2PaperCellIndex :=
  (wz1PaperActiveCells shading hdelta).filter fun cell =>
    wz1PaperGridCube delta cell ⊆
      wz1PaperGridCube rho
        (wz2PaperBoundaryCoarseParent delta rho cell)

/-- Active `delta`-cells crossing a literal `rho`-grid hyperplane. -/
def wz2PaperBoundaryCrossingFineCells
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta) : Finset WZ2PaperCellIndex :=
  wz1PaperActiveCells shading hdelta \
    wz2PaperBoundarySafeFineCells (rho := rho) shading hdelta

/-- Union of all active whole `delta`-cells crossing the `rho`-grid. -/
def wz2PaperBoundaryCrossingRegion
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta) : Set Point3 :=
  ⋃ cell ∈
      wz2PaperBoundaryCrossingFineCells
        (rho := rho) shading hdelta,
    wz1PaperGridCube delta cell

/--
Output of whole-cell pruning at the non-commensurable `rho`-grid boundary.

The constant `1000` is deliberately inessential.  It pays for the three
coordinate directions, both sides of every grid hyperplane, and the cropped
window endpoints.
-/
structure WZ2PaperBoundaryCellPruningData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta)
    (multiplicityCap : ENNReal) where
  safeFineCells : Finset WZ2PaperCellIndex
  crossingFineCells : Finset WZ2PaperCellIndex
  safeFineCells_subset :
    safeFineCells ⊆ wz1PaperActiveCells shading hdelta
  crossingFineCells_eq :
    crossingFineCells =
      wz1PaperActiveCells shading hdelta \ safeFineCells
  activeCells_partition :
    wz1PaperActiveCells shading hdelta =
      safeFineCells ∪ crossingFineCells
  crossingRegion : Set Point3
  crossingRegion_eq :
    crossingRegion =
      ⋃ fineCell ∈ crossingFineCells,
        wz1PaperGridCube delta fineCell
  crossingRegion_eq_source :
    crossingRegion =
      ⋃ fineCell ∈
          (wz1PaperActiveCells shading hdelta \
            (wz1PaperActiveCells shading hdelta).filter fun cell =>
              wz1PaperGridCube delta cell ⊆
                wz1PaperGridCube rho
                  (wz1PaperGridIndex rho (cellCorner delta cell))),
        wz1PaperGridCube delta fineCell
  crossingRegion_measurable :
    MeasurableSet crossingRegion
  crossingRegion_volume :
    volume crossingRegion ≤
      ENNReal.ofReal (1000 * delta / rho)
  pruned : WZ1PaperTubeShading fine
  pruned_carrier_eq :
    ∀ index,
      pruned.carrier index =
        shading.carrier index ∩
          ⋃ fineCell ∈ safeFineCells,
            wz1PaperGridCube delta fineCell
  pruned_subshading :
    ∀ index,
      pruned.carrier index ⊆ shading.carrier index
  pruned_cubical :
    WZ1PaperIsCubicalShading pruned
  pruned_union_eq :
    pruned.union =
      ⋃ fineCell ∈ safeFineCells,
        wz1PaperGridCube delta fineCell
  source_mass_le :
    shading.mass ≤
      pruned.mass +
        multiplicityCap * volume crossingRegion
  source_mass_eq_crossing :
    shading.mass =
      pruned.mass +
        ∑ index : Fin fine.card,
          volume (shading.carrier index ∩ crossingRegion)
  source_mass_le_explicit :
    shading.mass ≤
      pruned.mass +
        multiplicityCap *
          ENNReal.ofReal (1000 * delta / rho)
  pruned_mass_pos : 0 < pruned.mass
  safeFineCells_nonempty : safeFineCells.Nonempty
  coarseParent :
    WZ2PaperCellIndex → WZ2PaperCellIndex
  safeFineCell_contained :
    ∀ fineCell ∈ safeFineCells,
      wz1PaperGridCube delta fineCell ⊆
        wz1PaperGridCube rho (coarseParent fineCell)
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
            wz1PaperGridCube rho coarseCell

/--
Prune crossing whole `delta`-cells and group all survivors by their unique
literal `rho`-cell.

The explicit smallness hypothesis is the caller's exponent arithmetic.  The
geometric content of this leaf is the uniform
`volume crossingRegion ≤ 1000 * delta / rho` estimate and the construction of
the whole-cell subshading.  No divisibility or dyadic relation between the
two scales is assumed.
-/
def WZ2PropStickyBoundaryCellPruningStatement : Prop :=
  ∀ {delta rho : ℝ},
    (hdelta : 0 < delta) →
    delta ≤ rho →
    (hrho : 0 < rho) →
    rho ≤ 1 →
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ (shading : WZ1PaperTubeShading fine),
        WZ1PaperIsCubicalShading shading →
        ∀ multiplicityCap : ENNReal,
          (∀ point,
            (shading.pointMultiplicity point : ENNReal) ≤
              multiplicityCap) →
          multiplicityCap *
              ENNReal.ofReal (1000 * delta / rho) <
            shading.mass →
            Nonempty
              (WZ2PaperBoundaryCellPruningData
                (delta := delta) (rho := rho)
                shading hdelta multiplicityCap)

end Kakeya.Assouad
