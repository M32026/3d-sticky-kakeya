import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantAnchoredTwoScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinAnchoredLocalInput

/-!
# Active CommonBin adapter for anchored two-scale data

This adapter binds the CommonBin cells and genuine current anchors to the
same source-relative selected-cell witness that carries global AD.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2SourceCommonBinAnchoredTwoScaleInput
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho grainLoss
      outputEta selectedLoss sourceLoss seedLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    {firstOverlay : PureWZ2HierarchyReentrantFirstOverlayReceipt
      (current := current) kernelOutput}
    {anchored :
      PureWZ2HierarchyReentrantCurrentCoarseAnchoredReceipt firstOverlay}
    {selectedNormalizationExponent secondSeedLogExponent firstLogExponent : ℕ}
    {selection : PureWZ2Node05AnchoredSynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (sourceLoss := sourceLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      firstOverlay.ambient anchored.toAnchoredCoarseSource}
    {sqrtRequested : WZ2PaperRequestedScale kernelOutput.requested.1}
    {stage : PureWZ2Node05AnchoredSynchronizedTwoCallStage
      (seedLoss := seedLoss)
      (outputLoss := lossSchedule.ownerSchedule.stickyLoss)
      (firstLogExponent := firstLogExponent)
      (secondSeedLogExponent := secondSeedLogExponent)
      firstOverlay.ambient anchored.toAnchoredCoarseSource selection
      sqrtRequested}
    (receipt : PureWZ2HierarchyReentrantAnchoredTwoScaleReceipt
      (grainLoss := grainLoss) anchored selection sqrtRequested stage)
    (C : ENNReal) (g : ℝ → ℝ) where
  cells : Finset (ℤ × ℤ × ℤ)
  cells_subset_selected :
    cells ⊆ receipt.sourceRelative.selectedCells
  localReceipt :
    PureWZ2SourceCommonBinAnchoredLocalReceipt
      (rho := kernelOutput.requested.1) current C cells g

namespace PureWZ2SourceCommonBinAnchoredTwoScaleInput

variable
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho grainLoss
      outputEta selectedLoss sourceLoss seedLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    {firstOverlay : PureWZ2HierarchyReentrantFirstOverlayReceipt
      (current := current) kernelOutput}
    {anchored :
      PureWZ2HierarchyReentrantCurrentCoarseAnchoredReceipt firstOverlay}
    {selectedNormalizationExponent secondSeedLogExponent firstLogExponent : ℕ}
    {selection : PureWZ2Node05AnchoredSynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (sourceLoss := sourceLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      firstOverlay.ambient anchored.toAnchoredCoarseSource}
    {sqrtRequested : WZ2PaperRequestedScale kernelOutput.requested.1}
    {stage : PureWZ2Node05AnchoredSynchronizedTwoCallStage
      (seedLoss := seedLoss)
      (outputLoss := lossSchedule.ownerSchedule.stickyLoss)
      (firstLogExponent := firstLogExponent)
      (secondSeedLogExponent := secondSeedLogExponent)
      firstOverlay.ambient anchored.toAnchoredCoarseSource selection
      sqrtRequested}
    {receipt : PureWZ2HierarchyReentrantAnchoredTwoScaleReceipt
      (grainLoss := grainLoss) anchored selection sqrtRequested stage}
    {C : ENNReal} {g : ℝ → ℝ}
    (input : PureWZ2SourceCommonBinAnchoredTwoScaleInput receipt C g)

/-- Global AD is taken from the exact source-relative selected-cell pullback. -/
theorem global_ad
    (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    PureWZ2PaperADSet1
      (scalarProjection
        (globalGrainDirection (current.grain.globalGrains.slope z))
        (horizontalSlice receipt.sourceRelative.shading.union z))
      kernelOutput.requested.1 (1 - sigma)
      (Kakeya.realRpowENN kernelOutput.requested.1 (-selectedLoss)) :=
  receipt.fine_global_ad z hz

/-- Local CommonBin data uses genuine current anchors on the very same cell
set recorded by this adapter. -/
noncomputable def toHeterogeneousLocalBinInput :
    WZ1Lemma23HeterogeneousLocalBinInput
      kernelOutput.requested.1 sigma (2 * C) input.cells g :=
  input.localReceipt.toHeterogeneousLocalBinInput

end PureWZ2SourceCommonBinAnchoredTwoScaleInput

end Kakeya.Assouad

end
