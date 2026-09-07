import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantParentCellsStatements

/-!
# Fine cells owned by each dominant parent

Inside every selected literal `rho`-cell, retain the active literal
`delta`-cells whose final shading is met by at least one fine tube belonging
to the chosen dominant parent.  Their union is exactly the dominant
parent-cell shaded union, and the global fine multiplicity band converts its
mass into a quantitative lower bound for the number of owned fine cells.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure WZ2PaperDominantParentFineCellsData
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
        (rho := rho) sourceShading coarseCells
        availableFineCells)
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
    (multiplicityLevel : ℕ)
    (degree :
      WZ2PaperBalancedParentDegreeData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel)
    (dominant :
      WZ2PaperDominantParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree) where
  ownedFineCells :
    WZ2PaperCellIndex → Finset WZ2PaperCellIndex
  ownedFineCells_eq :
    ∀ cell,
      ownedFineCells cell =
        Finset.filter (fun fineCell =>
          (wz1PaperGridCube delta fineCell ∩
            (restrictPaperShading
              (cover.fullFiberSubfamily
                (dominant.dominantParent cell))
              balancing.refined).union).Nonempty)
          (balancing.selectedFineCells cell)
  ownedFineCells_subset :
    ∀ cell ∈ dominant.selectedCells,
      ownedFineCells cell ⊆
        balancing.selectedFineCells cell
  ownedFineCells_nonempty :
    ∀ cell ∈ dominant.selectedCells,
      (ownedFineCells cell).Nonempty
  owned_union_eq :
    ∀ cell ∈ dominant.selectedCells,
      ⋃ fineCell ∈ ownedFineCells cell,
          wz1PaperGridCube delta fineCell =
        (restrictPaperShading
            (cover.fullFiberSubfamily
              (dominant.dominantParent cell))
            balancing.refined).union ∩
          wz1PaperGridCube rho cell
  owned_cardinality_lower :
    ∀ cell ∈ dominant.selectedCells,
      dominant.dominantMass cell ≤
        (2 ^ (multiplicityLevel + 1) : ENNReal) *
          (ownedFineCells cell).card *
          active.fiberCellMass

def WZ2PaperDominantParentFineCellsStatement : Prop :=
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
                          (rho := rho) sourceShading coarseCells
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
                          ∀ (multiplicityLevel : ℕ),
                            (∀ point ∈ balancing.refined.union,
                              (balancing.refined.pointMultiplicity point :
                                  ENNReal) <
                                (2 ^ (multiplicityLevel + 1) :
                                  ENNReal)) →
                            ∀ (degree :
                                WZ2PaperBalancedParentDegreeData
                                  cover sourceShading coarseCells
                                  availableFineCells balancing
                                  coarseData active
                                  multiplicityLevel),
                              ∀ (dominant :
                                  WZ2PaperDominantParentCellsData
                                    cover sourceShading coarseCells
                                    availableFineCells balancing
                                    coarseData active
                                    multiplicityLevel degree),
                                Nonempty
                                  (WZ2PaperDominantParentFineCellsData
                                    cover sourceShading coarseCells
                                    availableFineCells balancing
                                    coarseData active multiplicityLevel
                                    degree dominant)

end Kakeya.Assouad

end
