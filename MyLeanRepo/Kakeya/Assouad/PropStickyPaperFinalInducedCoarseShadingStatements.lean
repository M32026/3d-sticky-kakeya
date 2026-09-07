import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainmentStatements

/-!
# Coarse shading induced by the actual final fine incidences

After final exact fine balancing, assign a retained literal `rho`-cell to a
coarse parent exactly when that parent's final full fiber meets the cell.
Every coarse parent-cell incidence is therefore genuine; there are no ghost
cells inherited from an earlier shading.

The inner-parent containment theorem puts each assigned whole cell inside
the corresponding cropped paper tube.  The induced coarse shading covers
the final fine shading and forms a balanced cover with the final exact cell
mass.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure WZ2PaperFinalInducedCoarseShadingData
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
    (fiberBand :
      WZ2PaperFiberMultiplicityBandData
        cover balancing.refined)
    (pairBand :
      WZ2PaperParentCellMassBandData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active fiberBand)
    (restriction :
      WZ2PaperParentCellRestrictionData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active fiberBand pairBand)
    (finalFine :
      WZ2PaperFinalFineExactBalancingData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active fiberBand pairBand restriction) where
  parentCells :
    Fin coarse.card → Finset WZ2PaperCellIndex
  parentCells_eq :
    ∀ parent,
      parentCells parent =
        finalFine.exact.retainedCoarseCells.filter fun cell =>
          ((restrictPaperShading
              (cover.fullFiberSubfamily parent)
              finalFine.exact.refined).union ∩
            wz1PaperGridCube rho cell).Nonempty
  parentCells_subset :
    ∀ parent,
      parentCells parent ⊆
        finalFine.exact.retainedCoarseCells
  retained_cell_owned :
    ∀ cell ∈ finalFine.exact.retainedCoarseCells,
      ∃ parent, cell ∈ parentCells parent
  coarseShading : WZ1PaperTubeShading coarse
  coarse_carrier_eq :
    ∀ parent,
      coarseShading.carrier parent =
        ⋃ cell ∈ parentCells parent,
          wz1PaperGridCube rho cell
  coarse_cubical :
    WZ1PaperIsCubicalShading coarseShading
  coarse_union_eq :
    coarseShading.union =
      ⋃ cell ∈ finalFine.exact.retainedCoarseCells,
        wz1PaperGridCube rho cell
  point_compatibility :
    ∀ source point,
      point ∈ finalFine.exact.refined.carrier source →
        point ∈ coarseShading.carrier (cover.parent source)
  balanced :
    WZ1PaperBalancedCoverData
      cover.toWZ1PaperTubeCover
      finalFine.exact.refined coarseShading
  balanced_activeCells_eq :
    balanced.activeCells =
      finalFine.exact.retainedCoarseCells
  balanced_cellMass_eq :
    balanced.cellMass = finalFine.exact.cellMass
  activeParents :
    WZ2PaperCellIndex → Finset (Fin coarse.card)
  activeParents_eq :
    ∀ cell,
      activeParents cell =
        Finset.univ.filter fun parent =>
          cell ∈ parentCells parent
  activeParents_nonempty :
    ∀ cell ∈ finalFine.exact.retainedCoarseCells,
      (activeParents cell).Nonempty
  representative :
    WZ2PaperCellIndex → Point3
  representative_mem :
    ∀ cell,
      representative cell ∈ wz1PaperGridCube rho cell
  activeParents_card_eq :
    ∀ cell ∈ finalFine.exact.retainedCoarseCells,
      (activeParents cell).card =
        coarseShading.pointMultiplicity (representative cell)
  parent_cell_nonempty :
    ∀ cell ∈ finalFine.exact.retainedCoarseCells,
      ∀ parent ∈ activeParents cell,
        ((restrictPaperShading
            (cover.fullFiberSubfamily parent)
            finalFine.exact.refined).union ∩
          wz1PaperGridCube rho cell).Nonempty

def WZ2PaperFinalInducedCoarseShadingStatement : Prop :=
  WZ2PropStickyCoarseCellContainmentStatement →
  ∀ {delta rho : ℝ},
    ∀ (hdelta : 0 < delta),
      ∀ (hrho : 0 < rho),
        18 * delta ≤ rho →
        ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
          ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
            ∀ (cover : WZ2PaperPartitioningCover fine coarse),
              WZ1PaperIsLineClass fine →
              WZ1PaperIsLineClass coarse →
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
                          ∀ (fiberBand :
                              WZ2PaperFiberMultiplicityBandData
                                cover balancing.refined),
                            ∀ (pairBand :
                                WZ2PaperParentCellMassBandData
                                  cover sourceShading coarseCells
                                  availableFineCells balancing coarseData
                                  active fiberBand),
                              ∀ (restriction :
                                  WZ2PaperParentCellRestrictionData
                                    cover sourceShading coarseCells
                                    availableFineCells balancing
                                    coarseData active fiberBand pairBand),
                                ∀ (finalFine :
                                    WZ2PaperFinalFineExactBalancingData
                                      cover sourceShading coarseCells
                                      availableFineCells balancing
                                      coarseData active fiberBand pairBand
                                      restriction),
                                  (∀ cell ∈
                                      finalFine.exact.retainedCoarseCells,
                                    wz1PaperGridCube rho cell ⊆
                                      Kakeya.Streamlined.axisBox 2 2 2) →
                                  Nonempty
                                    (WZ2PaperFinalInducedCoarseShadingData
                                      cover sourceShading coarseCells
                                      availableFineCells balancing
                                      coarseData active fiberBand pairBand
                                      restriction finalFine)

end Kakeya.Assouad

end
