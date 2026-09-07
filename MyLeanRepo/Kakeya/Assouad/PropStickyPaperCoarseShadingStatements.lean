import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainmentStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyStatements

/-!
# Coarse paper shading from exactly balanced cells

After exact whole-cell balancing, assign a retained side-`rho` cell to every
coarse parent whose fine fiber meets that cell.  The parent-containment leaf
shows that each assigned whole cell lies in the corresponding cropped paper
tube.  The resulting coarse shading covers the refined fine shading and has
exactly the common cell mass required by the paper's balanced-cover
definition.

The crop condition on retained coarse cells is explicit.  It is a genuine
geometric pruning obligation and must not be inferred merely from the fact
that a contained fine cell lies in `[-1,1]^3`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

structure WZ2PaperCoarseShadingData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (sourceShading : WZ1PaperTubeShading fine)
    (coarseCells : Finset (ℤ × ℤ × ℤ))
    (availableFineCells :
      (ℤ × ℤ × ℤ) → Finset (ℤ × ℤ × ℤ))
    (balanced :
      WZ2PaperExactCellBalancingData
        (delta := delta) (rho := rho)
        sourceShading coarseCells availableFineCells) where
  parentCells :
    Fin coarse.card → Finset (ℤ × ℤ × ℤ)
  parentCells_subset :
    ∀ parent,
      parentCells parent ⊆ balanced.retainedCoarseCells
  parentCells_witness :
    ∀ parent cell, cell ∈ parentCells parent →
      ∃ source point,
        cover.parent source = parent ∧
        point ∈ balanced.refined.carrier source ∧
        point ∈ wz1PaperGridCube rho cell
  retained_cell_owned :
    ∀ cell ∈ balanced.retainedCoarseCells,
      ∃ parent, cell ∈ parentCells parent
  coarseShading : WZ1PaperTubeShading coarse
  coarseShading_carrier_eq :
    ∀ parent,
      coarseShading.carrier parent =
        ⋃ cell ∈ parentCells parent,
          wz1PaperGridCube rho cell
  balancedCover :
    WZ1PaperBalancedCoverData
      cover.toWZ1PaperTubeCover
      balanced.refined coarseShading

def WZ2PropStickyPaperCoarseShadingStatement : Prop :=
  WZ2PropStickyCoarseCellContainmentStatement →
  ∀ {delta rho : ℝ},
    (hdelta : 0 < delta) →
    (hrho : 0 < rho) →
    18 * delta ≤ rho →
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ (cover : WZ2PaperPartitioningCover fine coarse),
          WZ1PaperIsLineClass fine →
          WZ1PaperIsLineClass coarse →
          ∀ (sourceShading : WZ1PaperTubeShading fine),
            WZ1PaperIsCubicalShading sourceShading →
            ∀ (coarseCells : Finset (ℤ × ℤ × ℤ)),
              coarseCells.Nonempty →
              ∀ (availableFineCells :
                  (ℤ × ℤ × ℤ) → Finset (ℤ × ℤ × ℤ)),
                (∀ coarseCell ∈ coarseCells,
                  (availableFineCells coarseCell).Nonempty) →
                (∀ coarseCell ∈ coarseCells,
                  ∀ fineCell ∈ availableFineCells coarseCell,
                    fineCell ∈
                        wz1PaperActiveCells sourceShading hdelta ∧
                      wz1PaperGridCube delta fineCell ⊆
                        wz1PaperGridCube rho coarseCell) →
                ∀ balanced :
                    WZ2PaperExactCellBalancingData
                      (delta := delta) (rho := rho)
                      sourceShading coarseCells availableFineCells,
                  (∀ coarseCell ∈ balanced.retainedCoarseCells,
                    wz1PaperGridCube rho coarseCell ⊆
                      Kakeya.Streamlined.axisBox 2 2 2) →
                  Nonempty
                    (WZ2PaperCoarseShadingData
                      cover sourceShading coarseCells
                      availableFineCells balanced)

end Kakeya.Assouad

end
