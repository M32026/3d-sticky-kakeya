import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalCoarseMultiplicityBandStatements

/-!
# Final literal balanced cover, ghost-free version

The final coarse multiplicity band already restricts both the final fine
shading and the coarse shading induced from its actual parent-cell
incidences.  Package these shadings as the final literal balanced cover.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperFinalBalancedCoverV2Data
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
        balancing coarseData active fiberBand pairBand restriction)
    (induced :
      WZ2PaperFinalInducedCoarseShadingData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active fiberBand pairBand restriction
        finalFine)
    (coarseBand :
      WZ2PaperFinalCoarseMultiplicityBandData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active fiberBand pairBand restriction
        finalFine induced) where
  balanced :
    WZ1PaperBalancedCoverData
      cover.toWZ1PaperTubeCover
      coarseBand.selectedFineShading
      coarseBand.selectedCoarseShading
  activeCells_eq :
    balanced.activeCells = coarseBand.selectedCells
  cellMass_eq :
    balanced.cellMass = finalFine.exact.cellMass
  coarse_multiplicity_band :
    ∀ point ∈ coarseBand.selectedCoarseShading.union,
      (2 ^ coarseBand.level : ENNReal) ≤
          (coarseBand.selectedCoarseShading.pointMultiplicity point :
            ENNReal) ∧
        (coarseBand.selectedCoarseShading.pointMultiplicity point :
            ENNReal) <
          (2 ^ (coarseBand.level + 1) : ENNReal)
  fiber_multiplicity_band :
    ∀ parent point,
      point ∈
          (restrictPaperShading
            (cover.fullFiberSubfamily parent)
            coarseBand.selectedFineShading).union →
        (2 ^ fiberBand.level : ENNReal) ≤
            ((restrictPaperShading
              (cover.fullFiberSubfamily parent)
              coarseBand.selectedFineShading).pointMultiplicity point :
              ENNReal) ∧
          ((restrictPaperShading
              (cover.fullFiberSubfamily parent)
              coarseBand.selectedFineShading).pointMultiplicity point :
              ENNReal) <
            (2 ^ (fiberBand.level + 1) : ENNReal)

def WZ2PaperFinalBalancedCoverV2Statement : Prop :=
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
                                  ∀ (induced :
                                      WZ2PaperFinalInducedCoarseShadingData
                                        cover sourceShading coarseCells
                                        availableFineCells balancing
                                        coarseData active fiberBand pairBand
                                        restriction finalFine),
                                    ∀ (coarseBand :
                                        WZ2PaperFinalCoarseMultiplicityBandData
                                          cover sourceShading coarseCells
                                          availableFineCells balancing
                                          coarseData active fiberBand pairBand
                                          restriction finalFine induced),
                                      Nonempty
                                        (WZ2PaperFinalBalancedCoverV2Data
                                          cover sourceShading coarseCells
                                          availableFineCells balancing
                                          coarseData active fiberBand pairBand
                                          restriction finalFine induced
                                          coarseBand)

end Kakeya.Assouad

end
