import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalBalancedCoverV2Statements

/-!
# Producer for the ghost-free final balanced cover

This package records the complete paper-faithful refinement chain from the
initial exact balanced shading to the final fine-mass-weighted coarse
multiplicity band and its balanced-cover packaging.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperFinalBalancedCoverProducerData
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
    {hrho : 0 < rho} where
  active :
    WZ2PaperBalancedActiveParentCellsData
      cover sourceShading coarseCells availableFineCells
      balancing coarseData hdelta hrho
  fiberBand :
    WZ2PaperFiberMultiplicityBandData
      cover balancing.refined
  pairBand :
    WZ2PaperParentCellMassBandData
      cover sourceShading coarseCells availableFineCells
      balancing coarseData active fiberBand
  restriction :
    WZ2PaperParentCellRestrictionData
      cover sourceShading coarseCells availableFineCells
      balancing coarseData active fiberBand pairBand
  finalFine :
    WZ2PaperFinalFineExactBalancingData
      cover sourceShading coarseCells availableFineCells
      balancing coarseData active fiberBand pairBand restriction
  induced :
    WZ2PaperFinalInducedCoarseShadingData
      cover sourceShading coarseCells availableFineCells
      balancing coarseData active fiberBand pairBand restriction
      finalFine
  coarseBand :
    WZ2PaperFinalCoarseMultiplicityBandData
      cover sourceShading coarseCells availableFineCells
      balancing coarseData active fiberBand pairBand restriction
      finalFine induced
  finalCover :
    WZ2PaperFinalBalancedCoverV2Data
      cover sourceShading coarseCells availableFineCells
      balancing coarseData active fiberBand pairBand restriction
      finalFine induced coarseBand

def WZ2PaperFinalBalancedCoverProducerStatement : Prop :=
  WZ2PropStickyCoarseCellContainmentStatement →
  WZ2PaperBalancedActiveParentCellsStatement →
  WZ2PaperFiberMultiplicityBandStatement →
  WZ2PaperParentCellMassBandStatement →
  WZ2PaperParentCellRestrictionStatement →
  WZ2PaperFinalFineExactBalancingStatement →
  WZ2PaperFinalInducedCoarseShadingStatement →
  WZ2PaperFinalCoarseMultiplicityBandStatement →
  WZ2PaperFinalBalancedCoverV2Statement →
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
                        (∀ cell ∈ balancing.retainedCoarseCells,
                          wz1PaperGridCube rho cell ⊆
                            Kakeya.Streamlined.axisBox 2 2 2) →
                        Nonempty
                          (WZ2PaperFinalBalancedCoverProducerData
                            (hdelta := hdelta)
                            (hrho := hrho)
                            cover sourceShading coarseCells
                            availableFineCells balancing coarseData)

def WZ2PaperFinalBalancedCoverProducerClosedStatement : Prop :=
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
                        (∀ cell ∈ balancing.retainedCoarseCells,
                          wz1PaperGridCube rho cell ⊆
                            Kakeya.Streamlined.axisBox 2 2 2) →
                        Nonempty
                          (WZ2PaperFinalBalancedCoverProducerData
                            (hdelta := hdelta)
                            (hrho := hrho)
                            cover sourceShading coarseCells
                            availableFineCells balancing coarseData)

end Kakeya.Assouad

end
