import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParentDeletionStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoarseShadingStatements

/-!
# Ambient exact cover after final parent deletion

The final deletion keeps whole coarse cells but its public restriction
reindexes both the fine family and the retained coarse parents.  For the
subsequent ambient nearby-scale regularization, retain the original fine and
coarse index sets and expose the same surviving whole-cell shading as an exact
balanced cover.  Coarse parents not meeting a surviving cell simply receive
empty coarse shading.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperFinalParentDeletionAmbientExactData
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
    (finalDeletion :
      WZ2PaperFinalParentDeletionData
        producer referenceFiberMass threshold) where
  exact :
    WZ2PaperExactCellBalancingData
      (rho := rho)
      finalDeletion.deletion.refined
      finalDeletion.deletion.goodCells
      finalDeletion.exactAdapter.exact.selectedFineCells
  exact_refined_eq :
    exact.refined = finalDeletion.deletion.refined
  refined_subshading :
    ∀ index,
      exact.refined.carrier index ⊆
        finalDeletion.exactAdapter.exact.refined.carrier index
  coarseData :
    WZ2PaperCoarseShadingData
      cover finalDeletion.deletion.refined
      finalDeletion.deletion.goodCells
      finalDeletion.exactAdapter.exact.selectedFineCells
      exact
  parentCells_eq :
    ∀ parent,
      coarseData.parentCells parent =
        finalDeletion.deletion.goodCells.filter fun cell =>
          parent ∈ finalDeletion.active.activeParents cell
  coarse_union_eq_restriction :
    coarseData.coarseShading.union =
      finalDeletion.restriction.selectedCoarseShading.union

end Kakeya.Assouad

end
