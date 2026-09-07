import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalBalancedCoverExactAdapterStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedParentDeletionRestrictionStatements

/-!
# Final quantitative parent deletion

Starting from the final multiplicity-banded balanced cover, expose its exact
cell structure, bound the number of active parents per cell, delete low-mass
parents by whole cells, and restrict to complete surviving fibers.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperFinalParentDeletionData
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
        balancing coarseData)
    (referenceFiberMass : Fin coarse.card → ENNReal)
    (threshold : ENNReal) where
  exactAdapter :
    WZ2PaperFinalBalancedCoverExactAdapterData producer
  active :
    WZ2PaperBalancedActiveParentCellsData
      cover producer.coarseBand.selectedFineShading
      producer.coarseBand.selectedCells
      producer.finalFine.exact.selectedFineCells
      exactAdapter.exact exactAdapter.coarseData hdelta hrho
  degree :
    WZ2PaperBalancedParentDegreeData
      cover producer.coarseBand.selectedFineShading
      producer.coarseBand.selectedCells
      producer.finalFine.exact.selectedFineCells
      exactAdapter.exact exactAdapter.coarseData active
      producer.finalFine.fineLevel
  deletion :
    WZ2PaperBalancedParentDeletionRepairedData
      cover producer.coarseBand.selectedFineShading
      producer.coarseBand.selectedCells
      producer.finalFine.exact.selectedFineCells
      exactAdapter.exact exactAdapter.coarseData active
      referenceFiberMass
      (wz2PaperBalancedParentDegreeCap
        exactAdapter.exact producer.finalFine.fineLevel)
      threshold
  restriction :
    WZ2PaperBalancedParentDeletionRestrictionData
      cover producer.coarseBand.selectedFineShading
      producer.coarseBand.selectedCells
      producer.finalFine.exact.selectedFineCells
      exactAdapter.exact exactAdapter.coarseData active
      referenceFiberMass
      (wz2PaperBalancedParentDegreeCap
        exactAdapter.exact producer.finalFine.fineLevel)
      threshold deletion
  final_subshading :
    ∀ index,
      restriction.selectedFineShading.carrier index ⊆
        producer.coarseBand.selectedFineShading.carrier
          (restriction.selected.embedding index)

def WZ2PaperFinalParentDeletionStatement : Prop :=
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
                          ∀ (referenceFiberMass :
                              Fin coarse.card → ENNReal),
                          ∀ (threshold : ENNReal),
                            (∀ exactAdapter :
                                WZ2PaperFinalBalancedCoverExactAdapterData
                                  producer,
                              2 *
                                    (wz2PaperBalancedParentDegreeCap
                                      exactAdapter.exact
                                      producer.finalFine.fineLevel :
                                      ENNReal) *
                                    threshold *
                                    (∑ parent : Fin coarse.card,
                                      referenceFiberMass parent) <
                                exactAdapter.exact.cellMass *
                                  exactAdapter.exact.retainedCoarseCells.card) →
                            Nonempty
                              (WZ2PaperFinalParentDeletionData
                                producer referenceFiberMass threshold)

end Kakeya.Assouad

end
