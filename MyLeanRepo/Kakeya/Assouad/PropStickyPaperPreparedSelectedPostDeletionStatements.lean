import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPreparedSelectedComparisonStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGeometricReferenceFiberMass
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParentDeletionMassRetentionStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParentMultiplicityBandsStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParentMultiplicityComparisonStatements

/-!
# Final parent deletion on the corrected selected-parent mainline

The global `mu_coarse * mu_fine` comparison is fixed before the paper's final
`largeMass` deletion.  The deletion uses the geometric mass of each complete
fine fiber as its reference weight.  Its half-mass estimate then supplies the
post-deletion mass lower bound, while the selected fine union remains inside
the pre-deletion union.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperPreparedSelectedPostDeletionData
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
    {selectedFinal :
      WZ2PaperPreparedSelectedFinalData
        selectedRebalancing finalLogExponent}
    {massLower volumeUpper : ENNReal}
    (selectedComparison :
      WZ2PaperPreparedSelectedComparisonData
        selectedFinal massLower volumeUpper)
    (threshold : ENNReal)
    (deletionExponent : ℕ) where
  deletion :
    WZ2PaperFinalParentDeletionData
      selectedFinal.finalData.producer
      (wz2PaperGeometricReferenceFiberMass pullback.cover)
      threshold
  massRetention :
    WZ2PaperFinalParentDeletionMassRetentionData
      deletion deletionExponent
  bands :
    WZ2PaperFinalParentMultiplicityBandsData deletion
  comparison :
    WZ2PaperFinalParentMultiplicityComparisonData
      deletion bands
      (wz1PaperRefinementFraction delta deletionExponent * massLower)
      volumeUpper

end Kakeya.Assouad

end
