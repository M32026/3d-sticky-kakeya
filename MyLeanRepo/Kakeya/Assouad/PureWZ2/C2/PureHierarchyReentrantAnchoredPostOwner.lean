import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinAnchoredPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinProductionScalar

/-!
# Minimal active anchored post-owner entrance

This entrance contains the source-relative selected cells, the current-source
global/local preparation, and both production scalar budgets.  It is the
replacement index for the old `twoScale/pullback/prepared` prefix.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2HierarchyReentrantAnchoredPostOwnerInput
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
      (grainLoss := grainLoss) anchored selection sqrtRequested stage) where
  prepared :
    PureWZ2AnchoredSourceCarrierPreparation receipt.sourceRelative
  B₀ : ENNReal :=
    pureWZ2SourceHeavyCommonBinBound sigma inputLoss delta
      kernelOutput.requested.1
  B₀_eq :
    B₀ = pureWZ2SourceHeavyCommonBinBound sigma inputLoss delta
      kernelOutput.requested.1
  B₀_pos : 0 < B₀
  B₀_ne_top : B₀ ≠ ⊤
  popular_budget :
    (20 * pureWZ2CommonBinPreBinHeightCost kernelOutput.requested.1) *
        (4 * B₀ *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta kernelOutput.requested.1) ≤
      Kakeya.realRpowENN delta (sigma + selectedLoss) *
        Kakeya.realRpowENN kernelOutput.requested.1
          (lossSchedule.ownerSchedule.stickyLoss + selectedLoss)
  graph_budget :
    (20 * pureWZ2CommonBinPreBinHeightCost kernelOutput.requested.1) *
        ((8 * B₀ *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta kernelOutput.requested.1) *
          (40 * pureWZ2CommonBinPreBinHeightCost kernelOutput.requested.1 *
            (5 : ENNReal) * 512 *
            Kakeya.realRpowENN (256 * kernelOutput.requested.1)
              (1 + sigma / 2 +
                lossSchedule.ownerSchedule.jointVolumeLoss))) ≤
      Kakeya.realRpowENN kernelOutput.requested.1
          (lossSchedule.ownerSchedule.stickyLoss + selectedLoss) *
        Kakeya.realRpowENN delta (sigma + selectedLoss) *
        Kakeya.realRpowENN kernelOutput.requested.1
          (3 / 2 + sigma / 2 +
            3 * lossSchedule.ownerSchedule.stickyLoss / 2)

theorem PureWZ2HierarchyReentrantAnchoredTwoScaleReceipt.postOwnerInput_nonempty
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
    (hinput : 0 < inputLoss)
    (hinputCeiling : inputLoss ≤ sourceLossCeiling)
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ lossSchedule.scalarDelta₀)
    (hrequestedPower :
      kernelOutput.requested.1 ≤ Real.rpow delta outputLoss) :
    Nonempty (PureWZ2HierarchyReentrantAnchoredPostOwnerInput receipt) := by
  rcases receipt.sourceRelative.prepareSourceCarrier
      lossSchedule.paperADBridge with
    ⟨prepared⟩
  let rho := kernelOutput.requested.1
  let B₀ := pureWZ2SourceHeavyCommonBinBound sigma inputLoss delta rho
  have hrho : 0 < rho := hdelta.trans_le kernelOutput.requested.property.1
  have hsourceCost :
      2 * inputLoss + selectedLoss ≤
        2 * sourceLossCeiling + lossSchedule.middleLoss := by
    rw [receipt.selectedLoss_eq]
    linarith
  have hdeltaCommon : delta ≤ lossSchedule.commonBinScalar.delta₀ :=
    hdeltaSmall.trans lossSchedule.scalarDelta₀_commonBin
  have hpopular := lossSchedule.commonBinScalar.popular_budget
    hinput.le hsourceCost
    (by rw [receipt.selectedLoss_eq]; exact lossSchedule.middleLoss_pos.le)
    (by rw [receipt.selectedLoss_eq])
    hdelta hdeltaCommon kernelOutput.requested.property.1
    kernelOutput.requested.property.2 hrequestedPower
  have hgraph := lossSchedule.commonBinScalar.graph_budget
    hinput.le hsourceCost
    (by rw [receipt.selectedLoss_eq]; exact lossSchedule.middleLoss_pos.le)
    (by rw [receipt.selectedLoss_eq])
    hdelta hdeltaCommon kernelOutput.requested.property.1
    kernelOutput.requested.property.2 hrequestedPower
  have hB₀Pos : 0 < B₀ := by
    dsimp only [B₀, pureWZ2SourceHeavyCommonBinBound]
    exact ENNReal.mul_pos
      (ENNReal.mul_pos (by norm_num)
        (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)).ne').ne'
      (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos (by positivity) _)).ne'
  have hB₀Top : B₀ ≠ ⊤ := by
    dsimp only [B₀, pureWZ2SourceHeavyCommonBinBound]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num)
        (by simp [Kakeya.realRpowENN]))
      (by simp [Kakeya.realRpowENN])
  exact ⟨{
    prepared := prepared
    B₀ := B₀
    B₀_eq := rfl
    B₀_pos := hB₀Pos
    B₀_ne_top := hB₀Top
    popular_budget := by
      simpa [B₀, rho, receipt.selectedLoss_eq] using hpopular
    graph_budget := by
      simpa [B₀, rho, receipt.selectedLoss_eq] using hgraph
  }⟩

end Kakeya.Assouad

end
