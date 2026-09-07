import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoarseShadingStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers

/-!
# Active parent fibers in exact balanced cells

For every retained literal `rho`-cell, record the complete set of coarse
parents whose final fine fibers meet that cell.  The parent-cell weight is
the paper's shaded incidence mass

`sum_{T in fiber(parent)} |Y(T) intersect Q|`,

not the volume of the fiber union.  These incidence masses are additive over
the unique parent partition even when different parent fibers overlap in
space.  Cubicality shows that each active parent-cell pair contributes at
least one whole literal `delta`-cube.  Cubicality of the coarse shading
identifies the number of active parents with its point multiplicity at a
canonical point of the cell.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

def wz2PaperParentCellMass
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (pair : WZ2PaperCellIndex × Fin coarse.card) : ENNReal :=
  ∑ source :
      Fin (cover.fullFiberSubfamily pair.2).family.card,
    MeasureTheory.volume
      ((restrictPaperShading
        (cover.fullFiberSubfamily pair.2) shading).carrier source ∩
        wz1PaperGridCube rho pair.1)

def wz2PaperCellIncidenceMass
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (cell : WZ2PaperCellIndex) : ENNReal :=
  ∑ source : Fin fine.card,
    MeasureTheory.volume
      (shading.carrier source ∩
        wz1PaperGridCube rho cell)

structure WZ2PaperBalancedActiveParentCellsData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (sourceShading : WZ1PaperTubeShading fine)
    (coarseCells : Finset WZ2PaperCellIndex)
    (availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex)
    (balancing :
      WZ2PaperExactCellBalancingData
        sourceShading coarseCells availableFineCells)
    (coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells
        availableFineCells balancing)
    (hdelta : 0 < delta)
    (hrho : 0 < rho) where
  activeParents :
    WZ2PaperCellIndex → Finset (Fin coarse.card)
  activeParents_eq :
    ∀ cell,
      activeParents cell =
        Finset.univ.filter fun parent =>
          cell ∈ coarseData.parentCells parent
  activeParents_nonempty :
    ∀ cell ∈ balancing.retainedCoarseCells,
      (activeParents cell).Nonempty
  representative :
    WZ2PaperCellIndex → Point3
  representative_mem :
    ∀ cell,
      representative cell ∈ wz1PaperGridCube rho cell
  activeParents_card_eq :
    ∀ cell ∈ balancing.retainedCoarseCells,
      (activeParents cell).card =
        coarseData.coarseShading.pointMultiplicity
          (representative cell)
  sum_parent_mass_eq_cell_incidence :
    ∀ cell ∈ balancing.retainedCoarseCells,
      (∑ parent ∈ activeParents cell,
          wz2PaperParentCellMass
            cover balancing.refined (cell, parent)) =
        wz2PaperCellIncidenceMass
          (rho := rho) balancing.refined cell
  cell_mass_le_sum_parent :
    ∀ cell ∈ balancing.retainedCoarseCells,
      balancing.cellMass ≤
        ∑ parent ∈ activeParents cell,
          wz2PaperParentCellMass
            cover balancing.refined (cell, parent)
  fiberCellMass : ENNReal
  fiberCellMass_eq :
    fiberCellMass =
      MeasureTheory.volume
        (wz1PaperGridCube delta (0, 0, 0))
  fiberCellMass_pos : 0 < fiberCellMass
  fiberCellMass_ne_top : fiberCellMass ≠ ⊤
  fiber_cell_mass_lower :
    ∀ cell ∈ balancing.retainedCoarseCells,
      ∀ parent ∈ activeParents cell,
        fiberCellMass ≤
          MeasureTheory.volume
            ((restrictPaperShading
                (cover.fullFiberSubfamily parent)
                balancing.refined).union ∩
              wz1PaperGridCube rho cell)

def WZ2PaperBalancedActiveParentCellsStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ (hdelta : 0 < delta),
      ∀ (hrho : 0 < rho),
        ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
          ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
            ∀ (cover : WZ2PaperPartitioningCover fine coarse),
              ∀ (sourceShading : WZ1PaperTubeShading fine),
                ∀ (coarseCells : Finset WZ2PaperCellIndex),
                  ∀ (availableFineCells :
                      WZ2PaperCellIndex →
                        Finset WZ2PaperCellIndex),
                    ∀ (balancing :
                        WZ2PaperExactCellBalancingData
                          sourceShading coarseCells
                          availableFineCells),
                      ∀ (coarseData :
                          WZ2PaperCoarseShadingData
                            cover sourceShading coarseCells
                            availableFineCells balancing),
                        Nonempty
                          (WZ2PaperBalancedActiveParentCellsData
                            cover sourceShading coarseCells
                            availableFineCells balancing coarseData
                            hdelta hrho)

end Kakeya.Assouad

end
