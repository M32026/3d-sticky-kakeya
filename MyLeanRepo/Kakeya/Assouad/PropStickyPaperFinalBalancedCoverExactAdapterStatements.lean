import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalBalancedCoverProducerStatements

/-!
# Exact-cell view of the final multiplicity-banded cover

The final coarse multiplicity band restricts both shadings by one union of
whole retained `rho`-cells.  Repackage that pair as exact-cell balancing data
without any further selection.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperFinalBalancedCoverExactAdapterData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover sourceShading coarseCells availableFineCells
        balancing coarseData) where
  retainedFineCells : Finset WZ2PaperCellIndex
  retainedFineCells_eq :
    retainedFineCells =
      producer.coarseBand.selectedCells.biUnion
        producer.finalFine.exact.selectedFineCells
  exact :
    WZ2PaperExactCellBalancingData
      (rho := rho)
      producer.coarseBand.selectedFineShading
      producer.coarseBand.selectedCells
      producer.finalFine.exact.selectedFineCells
  exact_refined_eq :
    exact.refined =
      producer.coarseBand.selectedFineShading
  coarseData :
    WZ2PaperCoarseShadingData
      cover producer.coarseBand.selectedFineShading
      producer.coarseBand.selectedCells
      producer.finalFine.exact.selectedFineCells exact
  coarseData_coarseShading_eq :
    coarseData.coarseShading =
      producer.coarseBand.selectedCoarseShading
  fine_multiplicity_band :
    ∀ point ∈ exact.refined.union,
      (2 ^ producer.finalFine.fineLevel : ENNReal) ≤
          (exact.refined.pointMultiplicity point : ENNReal) ∧
        (exact.refined.pointMultiplicity point : ENNReal) <
          (2 ^ (producer.finalFine.fineLevel + 1) : ENNReal)

def WZ2PaperFinalBalancedCoverExactAdapterStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ {cover : WZ2PaperPartitioningCover fine coarse},
          ∀ {sourceShading : WZ1PaperTubeShading fine},
            ∀ {coarseCells : Finset WZ2PaperCellIndex},
              ∀ {availableFineCells :
                  WZ2PaperCellIndex → Finset WZ2PaperCellIndex},
                ∀ {balancing :
                    WZ2PaperExactCellBalancingData
                      (rho := rho) sourceShading coarseCells
                      availableFineCells},
                  ∀ {coarseData :
                      WZ2PaperCoarseShadingData
                        cover sourceShading coarseCells
                        availableFineCells balancing},
                    ∀ {hdelta : 0 < delta},
                      ∀ {hrho : 0 < rho},
                        ∀ (producer :
                            WZ2PaperFinalBalancedCoverProducerData
                              (hdelta := hdelta) (hrho := hrho)
                              cover sourceShading coarseCells
                              availableFineCells balancing coarseData),
                          Nonempty
                            (WZ2PaperFinalBalancedCoverExactAdapterData
                              producer)

end Kakeya.Assouad

end
