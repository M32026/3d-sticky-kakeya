import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperInfrastructure

/-!
# Exact whole-cell balancing for WZ2 `prop: sticky`

The paper defines a balanced cover by requiring

> `|E_T ∩ Q|` is the same for each `rho`-cube `Q ⊂ E_Ttilde`.

Before this finite step, the geometric argument must prune every literal
`delta`-cell that crosses a literal `rho`-grid boundary.  The present
interface starts after that pruning: every available whole `delta`-cell is
contained in its assigned `rho`-cell.

The target performs the remaining exact operation.  It dyadically
pigeonholes the number of available `delta`-cells, keeps the same number of
whole cells in every retained `rho`-cell, and restricts every fine-tube
shading by the resulting common cell set.  No measurable trimming is
allowed.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

abbrev WZ2PaperCellIndex := ℤ × ℤ × ℤ

/--
Output of the exact finite balancing step after boundary-cell pruning.

`availableFineCells coarseCell` is supplied by the preceding geometric
pruning argument.  The selected cells remain literal whole `delta`-cells.
The count-retention inequality includes the one dyadic pigeonhole and the
factor two lost by truncating every retained count to the bottom of its
dyadic band.
-/
structure WZ2PaperExactCellBalancingData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (coarseCells : Finset WZ2PaperCellIndex)
    (availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex) where
  level : ℕ
  retainedCoarseCells : Finset WZ2PaperCellIndex
  retainedCoarseCells_subset :
    retainedCoarseCells ⊆ coarseCells
  retainedCoarseCells_nonempty :
    retainedCoarseCells.Nonempty
  selectedFineCells :
    WZ2PaperCellIndex → Finset WZ2PaperCellIndex
  selectedFineCells_subset :
    ∀ coarseCell ∈ retainedCoarseCells,
      selectedFineCells coarseCell ⊆
        availableFineCells coarseCell
  selectedFineCells_card :
    ∀ coarseCell ∈ retainedCoarseCells,
      (selectedFineCells coarseCell).card = 2 ^ level
  availableFineCells_band :
    ∀ coarseCell ∈ retainedCoarseCells,
      2 ^ level ≤ (availableFineCells coarseCell).card ∧
        (availableFineCells coarseCell).card < 2 ^ (level + 1)
  retainedFineCells : Finset WZ2PaperCellIndex
  retainedFineCells_eq :
    retainedFineCells =
      retainedCoarseCells.biUnion selectedFineCells
  retainedFineCells_count :
    (∑ coarseCell ∈ coarseCells,
        (availableFineCells coarseCell).card) ≤
      2 *
        (Nat.log 2
            (∑ coarseCell ∈ coarseCells,
              (availableFineCells coarseCell).card) + 1) *
        retainedFineCells.card
  refined : WZ1PaperTubeShading fine
  refined_carrier_eq :
    ∀ index,
      refined.carrier index =
        shading.carrier index ∩
          ⋃ fineCell ∈ retainedFineCells,
            wz1PaperGridCube delta fineCell
  refined_subshading :
    ∀ index,
      refined.carrier index ⊆ shading.carrier index
  refined_cubical :
    WZ1PaperIsCubicalShading refined
  refined_union_eq :
    refined.union =
      ⋃ fineCell ∈ retainedFineCells,
        wz1PaperGridCube delta fineCell
  cellMass : ENNReal
  cellMass_eq :
    cellMass =
      (2 ^ level : ℕ) *
        volume
          (wz1PaperGridCube delta (0, 0, 0))
  cellMass_pos : 0 < cellMass
  cellMass_ne_top : cellMass ≠ ⊤
  fine_cell_mass :
    ∀ coarseCell ∈ retainedCoarseCells,
      volume
          (refined.union ∩
            wz1PaperGridCube rho coarseCell) =
        cellMass
  fine_cell_containment :
    ∀ coarseCell ∈ retainedCoarseCells,
      ∀ fineCell ∈ selectedFineCells coarseCell,
        wz1PaperGridCube delta fineCell ⊆
          wz1PaperGridCube rho coarseCell

/--
Exact whole-cell balancing after the geometric boundary layer has already
been removed.

Every available fine cell is an actual active cell of the supplied cubical
shading and lies wholly inside its assigned coarse cell.  The conclusion
performs only finite pigeonholing and whole-cell deletion.
-/
def WZ2PropStickyExactCellBalancingStatement : Prop :=
  ∀ {delta rho : ℝ},
    (hdelta : 0 < delta) →
    (hrho : 0 < rho) →
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ (shading : WZ1PaperTubeShading fine),
        WZ1PaperIsCubicalShading shading →
        ∀ (coarseCells : Finset WZ2PaperCellIndex),
          coarseCells.Nonempty →
          ∀ (availableFineCells :
              WZ2PaperCellIndex →
                Finset WZ2PaperCellIndex),
            (∀ coarseCell ∈ coarseCells,
              (availableFineCells coarseCell).Nonempty) →
            (∀ coarseCell ∈ coarseCells,
              ∀ fineCell ∈ availableFineCells coarseCell,
                fineCell ∈
                    wz1PaperActiveCells shading hdelta ∧
                  wz1PaperGridCube delta fineCell ⊆
                    wz1PaperGridCube rho coarseCell) →
              Nonempty
                (WZ2PaperExactCellBalancingData
                  (delta := delta) (rho := rho)
                  shading coarseCells availableFineCells)

end Kakeya.Assouad
