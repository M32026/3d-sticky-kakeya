import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderAllGlobalBins
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseRichPipeline

/-!
# Rich genuine-coarse pipelines on the selected ordinary global bins

For every source-relative regularized block, the all-bin volume argument has
already chosen one good global bin.  This module continues the graph and rich
construction from that exact stored preparation.  In particular, it does not
rerun the preparation constructor after the volume-good bin has been chosen.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- One exact chosen-bin rich pipeline for every regularized source block. -/
structure PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {allBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers}
    {coarseBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins}
    (selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
      (volumeLoss := volumeLoss) coarseBins) where
  pipeline : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
      (normalEta := normalEta)
      ((coarseBins.coarseFamily block.1).prep (selected.chosenBin block))
  rich : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData
      (finalLoss := finalLoss) (theoremEta := theoremEta) (pipeline block)

/-- Continue every chosen good bin through the exact preparation-indexed rich
pipeline.  All hypotheses are uniform scalar/analytic bounds; the graph-volume
input is discharged by the selected bin's stored receipt. -/
theorem PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData.toRichCoarseBins
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {allBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers}
    {coarseBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins}
    (selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
      (volumeLoss := volumeLoss) coarseBins)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hfinal : 0 < finalLoss) (hfinalOne : finalLoss < 1)
    (hfinalSigma : finalLoss / 2 < sigma)
    (hnormalEta : 0 < normalEta)
    (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (hlocalizationAbsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hlocalConstant :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * Kakeya.realRpowENN rho (-middleLoss)))
    (hCOne : (1 : ENNReal) ≤
      10 * Kakeya.realRpowENN rho (-middleLoss))
    (hCpower : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ∀ pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
          (normalEta := normalEta)
          ((coarseBins.coarseFamily block.1).prep
            (selected.chosenBin block)),
        (10 * Kakeya.realRpowENN rho (-middleLoss)).toReal ≤
          Real.rpow
            ((coarseBins.coarseFamily block.1).prep
              (selected.chosenBin block)).graphScale (-constantLoss))
    (hextraPower : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ∀ pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
          (normalEta := normalEta)
          ((coarseBins.coarseFamily block.1).prep
            (selected.chosenBin block)),
        (pipeline.preparedGraph.graph.residue.extraCost : ℝ) ≤
          Real.rpow
            ((coarseBins.coarseFamily block.1).prep
              (selected.chosenBin block)).graphScale (-extraLoss))
    (hedgeAbsorb : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      Real.rpow (wz1Lemma23Theorem22Scale
          ((coarseBins.coarseFamily block.1).prep
            (selected.chosenBin block)).graphScale) (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow
            ((coarseBins.coarseFamily block.1).prep
              (selected.chosenBin block)).graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss +
              4 * extraLoss))
    (hKatzTao : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      (4 : ENNReal) ≤ Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale
          ((coarseBins.coarseFamily block.1).prep
            (selected.chosenBin block)).graphScale) (-theoremEta))
    (hprojection : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ∀ pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
          (normalEta := normalEta)
          ((coarseBins.coarseFamily block.1).prep
            (selected.chosenBin block)),
      ∀ ready : PureWZ2SourceFixedBinCoarseReadyGraph
          (theoremEta := theoremEta) pipeline.sharp,
        WZ1Proposition8_9AlternativeAUnion
          ready.ready.deltaGraph finalLoss
          ready.common.F ready.common.G₁ ready.common.G₁)
    (hscaleOne : 5 * (256 * rho) ≤ 1)
    (hlengthLower :
      Real.rpow (5 * (256 * rho)) (1 / 2 + finalLoss) ≤
        twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) selected) := by
  have hpipeline : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      Nonempty (PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
        (normalEta := normalEta)
        ((coarseBins.coarseFamily block.1).prep
          (selected.chosenBin block))) := fun block =>
    ((coarseBins.coarseFamily block.1).prep
      (selected.chosenBin block)).coarseGraphPipelineAtPreparationFixedBin
        hbridge hsigma hsigmaOne hnormalEta hnormalEtaSigma hcertificateOne
        hsourceFloor hlocalPower hglobalPower hPlanarSmall hrootSmall20
      hlocalizationAbsorb hlocalConstant
      (lt_of_lt_of_le (by
        apply ENNReal.ofReal_pos.mpr
        apply Real.rpow_pos_of_pos
        exact ((coarseBins.coarseFamily block.1).prep
          (selected.chosenBin block)).graphScale_pos)
        (selected.chosenBin_volume_lower block))
  let pipeline : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
        (normalEta := normalEta)
        ((coarseBins.coarseFamily block.1).prep
          (selected.chosenBin block)) := fun block =>
    Classical.choice (hpipeline block)
  have hrich : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      Nonempty (PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData
        (finalLoss := finalLoss) (theoremEta := theoremEta)
        (pipeline block)) := fun block => by
    apply (pipeline block).toRichPipelineAtPreparationFixedBin
      hsigma hsigmaOne hCOne (hCpower block (pipeline block))
      (selected.chosenBin_volume_lower block)
      (hextraPower block (pipeline block)) (hedgeAbsorb block)
      (hKatzTao block) (hprojection block (pipeline block))
    · simpa [((coarseBins.coarseFamily block.1).prep
          (selected.chosenBin block)).graphScale_eq] using hscaleOne
    · simpa [((coarseBins.coarseFamily block.1).prep
          (selected.chosenBin block)).graphScale_eq] using hlengthLower
  exact ⟨{
    pipeline := pipeline
    rich := fun block => Classical.choice (hrich block)
  }⟩

end Kakeya.Assouad

end
