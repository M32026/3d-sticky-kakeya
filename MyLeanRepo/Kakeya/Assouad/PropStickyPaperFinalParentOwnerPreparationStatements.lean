import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParentDeletionAmbientExactStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantOwnerExactificationStatements

/-!
# Dominant-owner preparation after final parent deletion

Run the already closed dominant-owner chain on the ambient exact cover
exposed after whole-cell parent deletion.  This stage is purely finite and
geometric; nearby-scale regularization is performed only afterward.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperFinalParentOwnerPreparationData
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
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover sourceShading coarseCells availableFineCells
        balancing coarseData}
    {referenceFiberMass : Fin coarse.card → ENNReal}
    {threshold : ENNReal}
    {finalDeletion :
      WZ2PaperFinalParentDeletionData
        producer referenceFiberMass threshold}
    (ambient :
      WZ2PaperFinalParentDeletionAmbientExactData finalDeletion) where
  active :
    WZ2PaperBalancedActiveParentCellsData
      cover finalDeletion.deletion.refined
      finalDeletion.deletion.goodCells
      finalDeletion.exactAdapter.exact.selectedFineCells
      ambient.exact ambient.coarseData hdelta hrho
  degree :
    WZ2PaperBalancedParentDegreeData
      cover finalDeletion.deletion.refined
      finalDeletion.deletion.goodCells
      finalDeletion.exactAdapter.exact.selectedFineCells
      ambient.exact ambient.coarseData active
      producer.finalFine.fineLevel
  dominant :
    WZ2PaperDominantParentCellsData
      cover finalDeletion.deletion.refined
      finalDeletion.deletion.goodCells
      finalDeletion.exactAdapter.exact.selectedFineCells
      ambient.exact ambient.coarseData active
      producer.finalFine.fineLevel degree
  owned :
    WZ2PaperDominantParentFineCellsData
      cover finalDeletion.deletion.refined
      finalDeletion.deletion.goodCells
      finalDeletion.exactAdapter.exact.selectedFineCells
      ambient.exact ambient.coarseData active
      producer.finalFine.fineLevel degree dominant
  exactified :
    WZ2PaperDominantOwnerExactificationData
      cover finalDeletion.deletion.refined
      finalDeletion.deletion.goodCells
      finalDeletion.exactAdapter.exact.selectedFineCells
      ambient.exact ambient.coarseData active
      producer.finalFine.fineLevel degree dominant owned
  exactified_subshading :
    ∀ index,
      exactified.refined.carrier index ⊆
        ambient.exact.refined.carrier
          (exactified.selected.embedding index)

end Kakeya.Assouad

end
