import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryAllBinNestedRegionalData

/-!
# Nested ordinary regional producer

Complete the prepared dependent family from the scalar geometric receipts.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

namespace PureWZ2OrdinaryAllBinNestedRegionalPreparationData

/-- Complete the prepared nested regional family once the explicit graph
volume and analytic thresholds hold.  The hypotheses are scalar estimates;
all geometric witnesses are constructed from `preparedRegional`. -/
theorem toNestedRegional
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta finalLoss
      theoremEta volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {companions : PureWZ2OrdinaryAllBinOuterPopularCompanionData carriers}
    (preparedRegional :
      PureWZ2OrdinaryAllBinNestedRegionalPreparationData carriers companions)
    (hscaled : ∀ block :
        {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ∀ bin : {bin //
          bin ∈ (preparedRegional.sourceBins block).line.globalBins},
        2 * ((((preparedRegional.nested block bin).fixedLine.line.globalBins.card :
              ENNReal) *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss))) *
            pureWZ2BalancedSafeNestedCoarseVolumeCost rho ≤
          volume (preparedRegional.sync block bin).parentRestriction.cellRestriction.shading.union)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
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
    (hCpower :
      (10 * Kakeya.realRpowENN rho (-middleLoss)).toReal ≤
        Real.rpow (256 * rho) (-constantLoss))
    (hextraPower : ∀ block :
        {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ∀ bin : {bin //
          bin ∈ (preparedRegional.sourceBins block).line.globalBins},
      ∀ good : PureWZ2BalancedSafeOuterPopularCoarseNestedGoodBinData
          (volumeLoss := volumeLoss) (preparedRegional.nested block bin),
      ∀ nestedBin : {nestedBin // nestedBin ∈ good.selected},
      ∀ pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
          (normalEta := normalEta)
          ((preparedRegional.nested block bin).preparation nestedBin.1).prep,
        (pipeline.preparedGraph.graph.residue.extraCost : ℝ) ≤
          Real.rpow ((preparedRegional.nested block bin).preparation
            nestedBin.1).prep.graphScale (-extraLoss))
    (hedgeAbsorb : ∀ block :
        {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ∀ bin : {bin //
          bin ∈ (preparedRegional.sourceBins block).line.globalBins},
      ∀ good : PureWZ2BalancedSafeOuterPopularCoarseNestedGoodBinData
          (volumeLoss := volumeLoss) (preparedRegional.nested block bin),
      ∀ nestedBin : {nestedBin // nestedBin ∈ good.selected},
        Real.rpow (wz1Lemma23Theorem22Scale
            ((preparedRegional.nested block bin).preparation
              nestedBin.1).prep.graphScale) (theoremEta - 3) ≤
          (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
            Real.rpow ((preparedRegional.nested block bin).preparation
              nestedBin.1).prep.graphScale
              (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss))
    (hKatzTao : ∀ block :
        {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ∀ bin : {bin //
          bin ∈ (preparedRegional.sourceBins block).line.globalBins},
      ∀ good : PureWZ2BalancedSafeOuterPopularCoarseNestedGoodBinData
          (volumeLoss := volumeLoss) (preparedRegional.nested block bin),
      ∀ nestedBin : {nestedBin // nestedBin ∈ good.selected},
        (4 : ENNReal) ≤ Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale
            ((preparedRegional.nested block bin).preparation
              nestedBin.1).prep.graphScale) (-theoremEta))
    (hprojection : ∀ block :
        {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ∀ bin : {bin //
          bin ∈ (preparedRegional.sourceBins block).line.globalBins},
      ∀ good : PureWZ2BalancedSafeOuterPopularCoarseNestedGoodBinData
          (volumeLoss := volumeLoss) (preparedRegional.nested block bin),
      ∀ nestedBin : {nestedBin // nestedBin ∈ good.selected},
      ∀ pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
          (normalEta := normalEta)
          ((preparedRegional.nested block bin).preparation nestedBin.1).prep,
      ∀ ready : PureWZ2SourceFixedBinCoarseReadyGraph
          (theoremEta := theoremEta) pipeline.sharp,
        WZ1Proposition8_9AlternativeAUnion
          ready.ready.deltaGraph finalLoss
          ready.common.F ready.common.G₁ ready.common.G₁)
    (hscaleOne : 5 * (256 * rho) ≤ 1)
    (hlengthLower :
      Real.rpow (5 * (256 * rho)) (1 / 2 + finalLoss) ≤
        twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions) := by
  let good : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ∀ bin : {bin //
          bin ∈ (preparedRegional.sourceBins block).line.globalBins},
        PureWZ2BalancedSafeOuterPopularCoarseNestedGoodBinData
          (volumeLoss := volumeLoss)
          (preparedRegional.nested block bin) := fun block bin =>
    Classical.choice
      (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseNestedGlobalBinFamilyData.selectGoodBins
        (preparedRegional.nested block bin) (hscaled block bin))
  let rich : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ∀ bin : {bin //
          bin ∈ (preparedRegional.sourceBins block).line.globalBins},
        PureWZ2BalancedSafeOuterPopularCoarseNestedRichFamilyData
          (normalEta := normalEta) (finalLoss := finalLoss)
          (theoremEta := theoremEta) (good block bin) := fun block bin =>
    Classical.choice
      (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseNestedGoodBinData.toRichFamily
        (good block bin) hbridge hsigma hsigmaOne hnormalEta
        hnormalEtaSigma hcertificateOne hsourceFloor hlocalPower hglobalPower
        hPlanarSmall hrootSmall20 hlocalizationAbsorb hlocalConstant hCOne
        hCpower (hextraPower block bin (good block bin))
        (hedgeAbsorb block bin (good block bin))
        (hKatzTao block bin (good block bin))
        (hprojection block bin (good block bin)) hscaleOne hlengthLower)
  exact ⟨{
    parentData := preparedRegional.parentData
    weightClass := preparedRegional.weightClass
    weightRestriction := preparedRegional.weightRestriction
    sourceWindow := preparedRegional.sourceWindow
    sourceBins := preparedRegional.sourceBins
    family := fun block => {
      sync := preparedRegional.sync block
      nested := preparedRegional.nested block
      good := good block
      rich := rich block
    }
  }⟩

end PureWZ2OrdinaryAllBinNestedRegionalPreparationData

end Kakeya.Assouad

end
