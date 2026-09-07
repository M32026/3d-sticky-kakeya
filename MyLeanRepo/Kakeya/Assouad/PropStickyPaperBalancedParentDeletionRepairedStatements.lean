import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedParentDegreeStatements

/-!
# Repaired whole-cell deletion of low-mass parent fibers

This is the finite interface needed after exact balancing.  Unlike the
retired interface, it does not ask a finite type to be bijective with the
ambient infinite grid.  It stores the actual finite surviving cell family
directly.

Every deletion removes whole `rho`-cells from all fine shadings.  Hence the
surviving shading stays cubical and exactly balanced.  The quantitative
charging bound records the total shaded mass lost during deletion.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperBalancedParentDeletionRepairedData
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
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (active :
      WZ2PaperBalancedActiveParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData hdelta hrho)
    (referenceFiberMass : Fin coarse.card → ENNReal)
    (degreeCap : ℕ)
    (threshold : ENNReal) where
  goodCells : Finset WZ2PaperCellIndex
  goodCells_nonempty : goodCells.Nonempty
  goodCells_subset :
    goodCells ⊆ balancing.retainedCoarseCells
  retainedParents : Finset (Fin coarse.card)
  retainedParents_eq :
    retainedParents =
      goodCells.biUnion active.activeParents
  retainedParents_nonempty :
    retainedParents.Nonempty
  retainedFineCells : Finset WZ2PaperCellIndex
  retainedFineCells_eq :
    retainedFineCells =
      goodCells.biUnion balancing.selectedFineCells
  refined : WZ1PaperTubeShading fine
  refined_eq :
    refined =
      wz2RefinedShading balancing.refined retainedFineCells
  refined_subshading :
    ∀ index,
      refined.carrier index ⊆ balancing.refined.carrier index
  refined_cubical :
    WZ1PaperIsCubicalShading refined
  refined_union_eq :
    refined.union =
      ⋃ fineCell ∈ retainedFineCells,
        wz1PaperGridCube delta fineCell
  retained_cell_mass :
    ∀ cell ∈ goodCells,
      MeasureTheory.volume
          (refined.union ∩ wz1PaperGridCube rho cell) =
        balancing.cellMass
  parent_fiber_mass_floor :
    ∀ parent ∈ retainedParents,
      threshold * referenceFiberMass parent ≤
        (restrictPaperShading
          (cover.fullFiberSubfamily parent)
          refined).mass
  deleted_cell_mass :
    (balancing.retainedCoarseCells.card -
        goodCells.card : ℕ) * balancing.cellMass ≤
      2 * (degreeCap : ENNReal) * threshold *
        ∑ parent : Fin coarse.card, referenceFiberMass parent

def WZ2PaperBalancedParentDeletionRepairedStatement : Prop :=
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
                        ∀ (active :
                            WZ2PaperBalancedActiveParentCellsData
                              cover sourceShading coarseCells
                              availableFineCells balancing coarseData
                              hdelta hrho),
                          ∀ (degreeCap : ℕ),
                            (∀ cell ∈ balancing.retainedCoarseCells,
                              (active.activeParents cell).card ≤
                                2 * degreeCap) →
                            balancing.cellMass ≤
                              2 * (degreeCap : ENNReal) *
                                active.fiberCellMass →
                            ∀ (referenceFiberMass :
                                Fin coarse.card → ENNReal),
                            ∀ (threshold : ENNReal),
                              2 * (degreeCap : ENNReal) *
                                    threshold *
                                    (∑ parent : Fin coarse.card,
                                      referenceFiberMass parent) <
                                  balancing.cellMass *
                                    balancing.retainedCoarseCells.card →
                              Nonempty
                                (WZ2PaperBalancedParentDeletionRepairedData
                                  cover sourceShading coarseCells
                                  availableFineCells balancing
                                  coarseData active referenceFiberMass
                                  degreeCap threshold)

end Kakeya.Assouad

end
