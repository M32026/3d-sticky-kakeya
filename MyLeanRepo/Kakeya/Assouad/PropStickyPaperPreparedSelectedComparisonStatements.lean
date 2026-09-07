import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPreparedSelectedFinalStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRepairedFinalMultiplicityComparisonStatements

/-!
# Multiplicity comparison on the repaired selected-parent mainline

The complete-parent coarse regularization and the subsequent whole-cell
rebalancing have already produced the final ghost-free balanced cover.  This
package records the global `mu_coarse * mu_fine` comparison before the final
`largeMass` parent deletion.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperPreparedSelectedComparisonData
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
    {selectedRebalancing :
      WZ2PaperPreparedSelectedRebalancingData pullback}
    {finalLogExponent : ℕ}
    (selectedFinal :
      WZ2PaperPreparedSelectedFinalData
        selectedRebalancing finalLogExponent)
    (massLower volumeUpper : ENNReal) where
  comparison :
    WZ2PaperRepairedFinalMultiplicityComparisonData
      pullback.cover pullback.selectedFineShading
      selectedRebalancing.bandData prepared.delta_pos
      prepared.callerStrict.rho_pos
      selectedRebalancing.rebalancing finalLogExponent
      selectedFinal.finalData massLower volumeUpper

end Kakeya.Assouad

end
