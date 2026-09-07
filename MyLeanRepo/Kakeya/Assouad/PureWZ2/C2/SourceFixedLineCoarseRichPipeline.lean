import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarsePipeline
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseReadyGraph
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseAlternativeA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseRichCells
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseRichShading
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseHeightLift

/-!
# Complete rich output on one genuine coarse Lemma-24 block
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2SourceFixedBinCoarseRichPipelineData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    (pipeline : PureWZ2SourceFixedBinCoarsePipelineData
      (normalEta := normalEta) carrier fineWitnesses) where
  ready : PureWZ2SourceFixedBinCoarseReadyGraph
    (theoremEta := theoremEta) pipeline.sharp
  rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData
    ready finalLoss
  richCells : PureWZ2SourceFixedBinCoarseRichCells
    (graphParents := pipeline.graphParents) rich
  richShading : PureWZ2SourceFixedBinCoarseRichShading richCells
  sourcePullback : PureWZ2SelectedCoarseRegionSourcePullbackData
    richShading.shading
  richTrapezoid : PureWZ2SourceFixedBinCoarseRichTrapezoid richShading
  heightLift : PureWZ2SourceFixedBinCoarseHeightLift richTrapezoid

/-- Complete rich output indexed by an already selected genuine-coarse
preparation.  This is the provenance-preserving form consumed by the
ordinary all-bin selector. -/
structure PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    (pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
      (normalEta := normalEta) prep) where
  ready : PureWZ2SourceFixedBinCoarseReadyGraph
    (theoremEta := theoremEta) pipeline.sharp
  rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData
    ready finalLoss
  richCells : PureWZ2SourceFixedBinCoarseRichCells
    (graphParents := pipeline.graphParents) rich
  richShading : PureWZ2SourceFixedBinCoarseRichShading richCells
  sourcePullback : PureWZ2SelectedCoarseRegionSourcePullbackData
    richShading.shading
  richTrapezoid : PureWZ2SourceFixedBinCoarseRichTrapezoid richShading
  heightLift : PureWZ2SourceFixedBinCoarseHeightLift richTrapezoid

abbrev PureWZ2SourceFixedLineCoarseRichPipelineData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    (pipeline : PureWZ2SourceFixedLineCoarsePipelineData
      (normalEta := normalEta) carriers) : Type :=
  PureWZ2SourceFixedBinCoarseRichPipelineData
    (finalLoss := finalLoss) (theoremEta := theoremEta) pipeline

/-- Build the rich output without changing the preparation selected by the
all-bin graph-volume argument. -/
theorem PureWZ2SourceFixedBinCoarsePipelineAtPreparationData.toRichPipelineAtPreparationFixedBin
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    (pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
      (normalEta := normalEta) prep)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCOne : (1 : ENNReal) ≤
      10 * Kakeya.realRpowENN rho (-middleLoss))
    (hCpower :
      (10 * Kakeya.realRpowENN rho (-middleLoss)).toReal ≤
        Real.rpow prep.graphScale (-constantLoss))
    (hvolume : Kakeya.realRpowENN prep.graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      MeasureTheory.volume prep.shadow.union)
    (hextraPower :
      (pipeline.preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow prep.graphScale (-extraLoss))
    (hedgeAbsorb :
      Real.rpow (wz1Lemma23Theorem22Scale prep.graphScale)
          (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow prep.graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss +
              4 * extraLoss))
    (hKatzTao : (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale prep.graphScale) (-theoremEta))
    (hprojection : ∀ data : PureWZ2SourceFixedBinCoarseReadyGraph
        (theoremEta := theoremEta) pipeline.sharp,
      WZ1Proposition8_9AlternativeAUnion
        data.ready.deltaGraph finalLoss
        data.common.F data.common.G₁ data.common.G₁)
    (hscaleOne : 5 * prep.graphScale ≤ 1)
    (hlengthLower :
      Real.rpow (5 * prep.graphScale) (1 / 2 + finalLoss) ≤
        twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData
      (finalLoss := finalLoss) (theoremEta := theoremEta) pipeline) := by
  rcases pipeline.sharp.toReadyGraphFixedBin hsigma hsigmaOne hCOne hCpower
      hvolume hextraPower hedgeAbsorb hKatzTao with ⟨ready⟩
  rcases ready.alternativeAHeightsFixedBin (hprojection ready) with ⟨rich⟩
  rcases rich.toRichCellsFixedBin pipeline.graphParents with ⟨richCells⟩
  rcases richCells.toRichShadingFixedBin with ⟨richShading⟩
  rcases richShading.pullbackToSourceFixedBin with ⟨sourcePullback⟩
  rcases richShading.toRichTrapezoidFixedBin hscaleOne hlengthLower with
    ⟨richTrapezoid⟩
  rcases richTrapezoid.toHeightLiftFixedBin with ⟨heightLift⟩
  exact ⟨{
    ready := ready
    rich := rich
    richCells := richCells
    richShading := richShading
    sourcePullback := sourcePullback
    richTrapezoid := richTrapezoid
    heightLift := heightLift
  }⟩

theorem PureWZ2SourceFixedBinCoarsePipelineData.toRichPipelineFixedBin
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    (pipeline : PureWZ2SourceFixedBinCoarsePipelineData
      (normalEta := normalEta) carrier fineWitnesses)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCOne : (1 : ENNReal) ≤
      10 * Kakeya.realRpowENN rho (-middleLoss))
    (hCpower :
      (10 * Kakeya.realRpowENN rho (-middleLoss)).toReal ≤
        Real.rpow pipeline.prep.graphScale (-constantLoss))
    (hvolume : Kakeya.realRpowENN pipeline.prep.graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      MeasureTheory.volume pipeline.prep.shadow.union)
    (hextraPower :
      (pipeline.preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow pipeline.prep.graphScale (-extraLoss))
    (hedgeAbsorb :
      Real.rpow (wz1Lemma23Theorem22Scale pipeline.prep.graphScale)
          (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow pipeline.prep.graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss +
              4 * extraLoss))
    (hKatzTao : (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale pipeline.prep.graphScale) (-theoremEta))
    (hprojection : ∀ data : PureWZ2SourceFixedBinCoarseReadyGraph
        (theoremEta := theoremEta) pipeline.sharp,
      WZ1Proposition8_9AlternativeAUnion
        data.ready.deltaGraph finalLoss
        data.common.F data.common.G₁ data.common.G₁)
    (hscaleOne : 5 * pipeline.prep.graphScale ≤ 1)
    (hlengthLower :
      Real.rpow (5 * pipeline.prep.graphScale) (1 / 2 + finalLoss) ≤
        twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2SourceFixedBinCoarseRichPipelineData
      (finalLoss := finalLoss) (theoremEta := theoremEta) pipeline) := by
  rcases pipeline.sharp.toReadyGraphFixedBin hsigma hsigmaOne hCOne hCpower
      hvolume hextraPower hedgeAbsorb hKatzTao with ⟨ready⟩
  rcases ready.alternativeAHeightsFixedBin (hprojection ready) with ⟨rich⟩
  rcases rich.toRichCellsFixedBin pipeline.graphParents with ⟨richCells⟩
  rcases richCells.toRichShadingFixedBin with ⟨richShading⟩
  rcases richShading.pullbackToSourceFixedBin with ⟨sourcePullback⟩
  rcases richShading.toRichTrapezoidFixedBin hscaleOne hlengthLower with
    ⟨richTrapezoid⟩
  rcases richTrapezoid.toHeightLiftFixedBin with ⟨heightLift⟩
  exact ⟨{
    ready := ready
    rich := rich
    richCells := richCells
    richShading := richShading
    sourcePullback := sourcePullback
    richTrapezoid := richTrapezoid
    heightLift := heightLift
  }⟩

theorem PureWZ2SourceFixedLineCoarsePipelineData.toRichPipeline
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    (pipeline : PureWZ2SourceFixedLineCoarsePipelineData
      (normalEta := normalEta) carriers)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCOne : (1 : ENNReal) ≤
      10 * Kakeya.realRpowENN rho (-middleLoss))
    (hCpower :
      (10 * Kakeya.realRpowENN rho (-middleLoss)).toReal ≤
        Real.rpow pipeline.prep.graphScale (-constantLoss))
    (hvolume : Kakeya.realRpowENN pipeline.prep.graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      MeasureTheory.volume pipeline.prep.shadow.union)
    (hextraPower :
      (pipeline.preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow pipeline.prep.graphScale (-extraLoss))
    (hedgeAbsorb :
      Real.rpow (wz1Lemma23Theorem22Scale pipeline.prep.graphScale)
          (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow pipeline.prep.graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss +
              4 * extraLoss))
    (hKatzTao : (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale pipeline.prep.graphScale) (-theoremEta))
    (hprojection : ∀ data : PureWZ2SourceFixedLineCoarseReadyGraph
        (theoremEta := theoremEta) pipeline.sharp,
      WZ1Proposition8_9AlternativeAUnion
        data.ready.deltaGraph finalLoss
        data.common.F data.common.G₁ data.common.G₁)
    (hscaleOne : 5 * pipeline.prep.graphScale ≤ 1)
    (hlengthLower :
      Real.rpow (5 * pipeline.prep.graphScale) (1 / 2 + finalLoss) ≤
        twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2SourceFixedLineCoarseRichPipelineData
      (finalLoss := finalLoss) (theoremEta := theoremEta) pipeline) :=
  PureWZ2SourceFixedBinCoarsePipelineData.toRichPipelineFixedBin
    pipeline hsigma hsigmaOne hCOne hCpower hvolume hextraPower hedgeAbsorb
    hKatzTao hprojection hscaleOne hlengthLower

end Kakeya.Assouad

end
