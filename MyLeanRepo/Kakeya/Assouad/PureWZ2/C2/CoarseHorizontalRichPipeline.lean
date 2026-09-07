import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseHorizontalPipeline
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineAlternativeA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineRichCells
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineRichShading
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineRichTrapezoid

/-!
# Rich Alternative-A output on one coarse Lemma-24 slab
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2CoarseHorizontalRichPipelineData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (pipeline : PureWZ2CoarseHorizontalPipelineData (eta := eta) twoScale) where
  ready : PureWZ2HorizontalFixedLineReadyGraph
    (eta := eta) (theoremEta := theoremEta)
    (graphParents := pipeline.graphParents)
    (sources := pipeline.sources)
    (fullGrains := pipeline.fullGrains) pipeline.sharp
  rich : PureWZ2HorizontalAlternativeAHeightData ready finalLoss
  richCells : PureWZ2HorizontalAlternativeARichCells
    (graphParents := pipeline.graphParents) rich
  richShading : PureWZ2HorizontalAlternativeARichShading richCells
  richTrapezoid : PureWZ2HorizontalAlternativeARichTrapezoid richShading

theorem PureWZ2CoarseHorizontalPipelineData.toRichPipeline
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta
      volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (pipeline : PureWZ2CoarseHorizontalPipelineData (eta := eta) twoScale)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCOne :
      (1 : ENNReal) ≤ 10 * Kakeya.realRpowENN
        twoScale.rhoRequested.1 (-middleLoss))
    (hCpower :
      (10 * Kakeya.realRpowENN
        twoScale.rhoRequested.1 (-middleLoss)).toReal ≤
        Real.rpow pipeline.prep.graphScale (-constantLoss))
    (hvolumeBudget :
      Kakeya.realRpowENN pipeline.prep.graphScale
            (1 + sigma / 2 + volumeLoss) *
          pureWZ2HorizontalFixedLineVolumeCost
            twoScale.rhoRequested.1 sigma middleLoss ≤
        pureWZ2HorizontalFixedLineVolumeSupply
          pipeline.window.volumeSupply
          twoScale.rhoRequested.1 sigma stickyLoss)
    (hextraPower :
      (pipeline.graph.residue.extraCost : ℝ) ≤
        Real.rpow pipeline.prep.graphScale (-extraLoss))
    (hedgeAbsorb :
      Real.rpow (wz1Lemma23Theorem22Scale pipeline.prep.graphScale)
          (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow pipeline.prep.graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss +
              4 * extraLoss))
    (hKatzTao :
      (4 : ENNReal) ≤
        Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale pipeline.prep.graphScale)
          (-theoremEta))
    (hprojection : ∀ data : PureWZ2HorizontalFixedLineReadyGraph
        (eta := eta) (theoremEta := theoremEta)
        (graphParents := pipeline.graphParents)
        (sources := pipeline.sources)
        (fullGrains := pipeline.fullGrains) pipeline.sharp,
      WZ1Proposition8_9AlternativeAUnion
        data.ready.deltaGraph finalLoss
        data.common.F data.common.G₁ data.common.G₁)
    (hscaleOne : 5 * pipeline.prep.graphScale ≤ 1)
    (hlengthLower :
      Real.rpow (5 * pipeline.prep.graphScale)
          (1 / 2 + finalLoss) ≤ twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2CoarseHorizontalRichPipelineData
      (finalLoss := finalLoss) (theoremEta := theoremEta) pipeline) := by
  rcases pipeline.sharp.toReadyGraph pipeline.heightFiberCost_eq
      hsigma hsigmaOne hCOne hCpower hvolumeBudget hextraPower
      hedgeAbsorb hKatzTao with ⟨ready⟩
  rcases ready.alternativeAHeights (hprojection ready) with ⟨rich⟩
  rcases rich.toRichCells pipeline.graphParents with ⟨richCells⟩
  rcases richCells.toRichShading with ⟨richShading⟩
  rcases richShading.toRichTrapezoid hscaleOne hlengthLower with
    ⟨richTrapezoid⟩
  exact ⟨{
    ready := ready
    rich := rich
    richCells := richCells
    richShading := richShading
    richTrapezoid := richTrapezoid
  }⟩

end Kakeya.Assouad
