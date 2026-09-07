import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPreparedSelectedRebalancingStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRepairedFinalBalancedCoverStatements

/-!
# Final balanced cover after prepared coarse-parent selection

Starting from the complete-parent pullback and its CWA-aware whole-cell
rebalancing, construct the ghost-free final multiplicity bands and balanced
cover.  The final fine shading remains a subshading of the selected complete
parent family.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperPreparedSelectedFinalData
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
    {pullback :
      WZ2PaperPreparedCoarseParentPullbackData
        regularization parentExponent}
    (selectedRebalancing :
      WZ2PaperPreparedSelectedRebalancingData pullback)
    (finalLogExponent : ℕ) where
  finalData :
    WZ2PaperRepairedFinalBalancedCoverData
      pullback.cover pullback.selectedFineShading
      selectedRebalancing.bandData prepared.delta_pos
      prepared.callerStrict.rho_pos
      selectedRebalancing.rebalancing finalLogExponent
  final_subshading :
    ∀ index,
      finalData.producer.coarseBand.selectedFineShading.carrier index ⊆
        pullback.selectedFineShading.carrier index

end Kakeya.Assouad

end
