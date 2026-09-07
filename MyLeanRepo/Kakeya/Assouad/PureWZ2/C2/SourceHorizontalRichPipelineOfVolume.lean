import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalBudgetedProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalReadyGraphOfVolume

/-!
# Complete a source-horizontal graph from its actual carrier volume
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

theorem PureWZ2SourceHorizontalPipelineData.toRichPipelineOfVolumeLower
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta
      volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (pipeline : PureWZ2SourceHorizontalPipelineData
      (normalEta := normalEta) twoScale)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon : 0 < finalLoss) (hepsilonOne : finalLoss < 1)
    (hepsilonSigma : finalLoss / 2 < sigma)
    (hCOne :
      (1 : ENNReal) ≤ 10 * Kakeya.realRpowENN delta (-inputLoss))
    (hCpower :
      (10 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
        Real.rpow pipeline.prep.graphScale (-constantLoss))
    (hvolume :
      Kakeya.realRpowENN pipeline.prep.graphScale
          (1 + sigma / 2 + volumeLoss) ≤
        volume pipeline.prep.shadow.union)
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
    (hprojection :
      ∀ data : PureWZ2SourceHorizontalReadyGraph
          (theoremEta := theoremEta) pipeline.sharp,
        WZ1Proposition8_9AlternativeAUnion
          data.ready.deltaGraph finalLoss
          data.common.F data.common.G₁ data.common.G₁)
    (hscaleOne : 5 * pipeline.prep.graphScale ≤ 1)
    (hlengthLower :
      Real.rpow (5 * pipeline.prep.graphScale)
          (1 / 2 + finalLoss) ≤ twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2SourceHorizontalRichPipelineData
      (finalLoss := finalLoss) (theoremEta := theoremEta) pipeline) := by
  rcases pipeline.sharp.toReadyGraphOfVolumeLower
      pipeline.heightFiberCost_eq hsigma hsigmaOne hCOne hCpower hvolume
      hextraPower hedgeAbsorb hKatzTao with ⟨ready⟩
  have hA := hprojection ready
  rcases ready.alternativeAHeights hA with ⟨rich⟩
  rcases rich.toRichCells pipeline.graphParents with ⟨richCells⟩
  rcases richCells.toRichShading with ⟨richShading⟩
  rcases richShading.toRichTrapezoid hscaleOne hlengthLower with
    ⟨richTrapezoid⟩
  rcases richTrapezoid.toHeightLift with ⟨heightLift⟩
  rcases heightLift.richHeightVolume pipeline.graph_residue_eq
      pipeline.rawResidue_eq pipeline.shadow_union with ⟨heightVolume⟩
  exact ⟨{
    ready := ready
    rich := rich
    richCells := richCells
    richShading := richShading
    richTrapezoid := richTrapezoid
    heightLift := heightLift
    heightVolume := heightVolume
  }⟩

end Kakeya.Assouad

end
