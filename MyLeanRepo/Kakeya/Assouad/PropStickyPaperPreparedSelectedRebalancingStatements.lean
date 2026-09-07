import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPreparedCoarseParentPullbackStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperWholeCellRebalancingRepairedStatements

/-!
# Whole-cell rebalancing after coarse-parent regularization

The coarse-parent regularizer first selects complete caller fibers.  This
package then performs a global fine multiplicity band, fixed-origin CWA-aware
boundary pruning, exact whole-cell balancing, and crop-boundary pruning on
that selected complete-fiber cover.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperPreparedSelectedRebalancingData
    {delta sourceLoss stableLoss sigma floorLoss strongLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    {critical :
      WZ2PaperCriticalFloorSelectionData
        sigma floorLoss strongLoss}
    {structural :
      WZ2PaperPreparedParentwiseStructuralProducerData
        (outputLoss := outputLoss) prepared critical}
    {ambientConstant outputConstant normalizationWeight weightUpper :
      ENNReal}
    {levelCount parentExponent : ℕ}
    {regularization :
      WZ2PaperPreparedCoarseParentRegularizationData
        prepared critical structural
        ambientConstant outputConstant normalizationWeight weightUpper
        levelCount}
    (pullback :
      WZ2PaperPreparedCoarseParentPullbackData
        regularization parentExponent) where
  bandData :
    WZ2PaperGlobalMultiplicityBandData pullback.selectedFineShading
  rebalancing :
    WZ2PaperWholeCellRebalancingRepairedData
      pullback.cover pullback.selectedFineShading bandData
      prepared.delta_pos prepared.callerStrict.rho_pos
  source_mass_le_two_boundary_pruned :
    bandData.band.mass ≤
      2 * rebalancing.boundaryPruning.pruned.mass

end Kakeya.Assouad

end
