import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderGraph
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalRichPipelineOfVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalPreGraphMassBridge

/-!
# `Z_popular` and `Z_lin` in the paper-ordered ordinary graph

The graph is built only after the outer source-volume popularity restriction.
This module runs Alternative A, forms the rich-height lift, assigns every
selected linear height to one of the three adjacent outer-popular levels, and
returns the resulting fixed-loss lower bound to an original-family subshading.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

structure PureWZ2OrdinaryPaperOrderRichGraphData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {prepared : PureWZ2OrdinaryPaperOrderPreparationData carriers}
    (graphData : PureWZ2OrdinaryPaperOrderGraphData
      (normalEta := normalEta) prepared) where
  ready : PureWZ2SourceHorizontalReadyGraph
    (theoremEta := theoremEta) graphData.sharp
  rich : PureWZ2SourceAlternativeAHeightData ready finalLoss
  richCells : PureWZ2SourceAlternativeARichCells
    (graphParents := prepared.graphParents) rich
  richShading : PureWZ2SourceAlternativeARichShading richCells
  richTrapezoid : PureWZ2SourceAlternativeARichTrapezoid richShading
  heightLift : PureWZ2SourceAlternativeAHeightLift richTrapezoid
  heightAssignment : PureWZ2SourceEnvelopeHeightAssignmentData
    carriers.outerPopular rich
  source_mass_lower :
    (twoScale.coarse.fineMultiplicity : ENNReal) *
        ((rich.heightIndices.card : ENNReal) *
          carriers.outerPopular.popular.layerMass) ≤
      3 * heightLift.shading.mass

/-- Complete the `Z_popular` and `Z_lin` stages after the paper-ordered graph
has been constructed. -/
theorem PureWZ2OrdinaryPaperOrderGraphData.buildRichGraph
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {prepared : PureWZ2OrdinaryPaperOrderPreparationData carriers}
    (graphData : PureWZ2OrdinaryPaperOrderGraphData
      (normalEta := normalEta) prepared)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hfinal : 0 < finalLoss) (hfinalOne : finalLoss < 1)
    (hfinalSigma : finalLoss / 2 < sigma)
    (hCOne :
      (1 : ENNReal) ≤ 10 * Kakeya.realRpowENN delta (-inputLoss))
    (hCpower :
      (10 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
        Real.rpow prepared.prep.graphScale (-constantLoss))
    (hvolume :
      Kakeya.realRpowENN prepared.prep.graphScale
          (1 + sigma / 2 + volumeLoss) ≤
        volume prepared.prep.shadow.union)
    (hextraPower :
      (graphData.graph.residue.extraCost : ℝ) ≤
        Real.rpow prepared.prep.graphScale (-extraLoss))
    (hedgeAbsorb :
      Real.rpow (wz1Lemma23Theorem22Scale prepared.prep.graphScale)
          (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow prepared.prep.graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss +
              4 * extraLoss))
    (hKatzTao :
      (4 : ENNReal) ≤ Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale prepared.prep.graphScale) (-theoremEta))
    (hprojection :
      ∀ data : PureWZ2SourceHorizontalReadyGraph
          (theoremEta := theoremEta) graphData.sharp,
        WZ1Proposition8_9AlternativeAUnion
          data.ready.deltaGraph finalLoss
          data.common.F data.common.G₁ data.common.G₁)
    (hscaleOne : 5 * prepared.prep.graphScale ≤ 1)
    (hlengthLower :
      Real.rpow (5 * prepared.prep.graphScale)
          (1 / 2 + finalLoss) ≤ twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2OrdinaryPaperOrderRichGraphData
      (finalLoss := finalLoss) (theoremEta := theoremEta) graphData) := by
  rcases graphData.sharp.toReadyGraphOfVolumeLower
      graphData.heightFiberCost_eq hsigma hsigmaOne hCOne hCpower hvolume
      hextraPower hedgeAbsorb hKatzTao with ⟨ready⟩
  rcases ready.alternativeAHeights (hprojection ready) with ⟨rich⟩
  rcases rich.toRichCells prepared.graphParents with ⟨richCells⟩
  rcases richCells.toRichShading with ⟨richShading⟩
  rcases richShading.toRichTrapezoid hscaleOne hlengthLower with
    ⟨richTrapezoid⟩
  rcases richTrapezoid.toHeightLift with ⟨heightLift⟩
  rcases rich.envelopeHeightAssignment
      (graphParents := prepared.graphParents)
      prepared.prep.graphScale_eq
      prepared.graph_point_near_height_region with
    ⟨heightAssignment⟩
  have hwindow : carriers.outerPopular.popularWindow.shading.union =
      carriers.outerPopular.popular.shading.union := by
    rw [carriers.outerPopular.popularWindow_shading]
  exact ⟨{
    ready := ready
    rich := rich
    richCells := richCells
    richShading := richShading
    richTrapezoid := richTrapezoid
    heightLift := heightLift
    heightAssignment := heightAssignment
    source_mass_lower := heightLift.mass_lower_of_nearby_outer_popular
      heightAssignment hwindow
  }⟩

/-- The source window, rather than the auxiliary graph carrier, controls the
mass of the final height-only lift. This is the literal `Z_lin ⊆ Z_S`
bookkeeping in Lemma 24. -/
theorem PureWZ2OrdinaryPaperOrderRichGraphData.source_window_mass_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {prepared : PureWZ2OrdinaryPaperOrderPreparationData carriers}
    {graphData : PureWZ2OrdinaryPaperOrderGraphData
      (normalEta := normalEta) prepared}
    (data : PureWZ2OrdinaryPaperOrderRichGraphData
      (finalLoss := finalLoss) (theoremEta := theoremEta) graphData) :
    volume carriers.sourceWindow.shading.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
      (12 * carriers.outerPopular.popular.bins : ENNReal) *
        (carriers.outerPopular.popular.heightIndices.card : ENNReal) *
          data.heightLift.shading.mass := by
  let floor := pureWZ2SourceHorizontalRichFloor rho finalLoss
  have hpopular : volume carriers.sourceWindow.shading.union ≤
      (2 * carriers.outerPopular.popular.bins : ENNReal) *
        volume carriers.outerPopular.popular.shading.union := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat,
      carriers.outerPopular.popularWindow_supply] using
        carriers.source_volume_retention
  have hfloor : floor ≤ (data.rich.heightIndices.card : ENNReal) := by
    have hfloorEq : floor = Kakeya.realRpowENN
        data.ready.ready.deltaGraph (finalLoss - 1) := by
      dsimp only [floor]
      unfold pureWZ2SourceHorizontalRichFloor
      rw [data.ready.ready.deltaGraph_eq, prepared.prep.graphScale_eq]
    rw [hfloorEq]
    simpa [data.rich.heightIndices_card] using data.rich.richF_card
  have hpopularLayer : volume carriers.outerPopular.popular.shading.union ≤
      2 * (carriers.outerPopular.popular.heightIndices.card : ENNReal) *
        carriers.outerPopular.popular.layerMass := by
    rw [carriers.outerPopular.popular.volume_eq_sum]
    calc
      (∑ heightIndex ∈ carriers.outerPopular.popular.heightIndices,
          volume (carriers.sourceWindow.shading.union ∩
            wz1Lemma23HeightSlab (256 * rho) heightIndex)) ≤
        ∑ _heightIndex ∈ carriers.outerPopular.popular.heightIndices,
          2 * carriers.outerPopular.popular.layerMass := by
        exact Finset.sum_le_sum fun heightIndex hheight =>
          (carriers.outerPopular.popular.layer_volume_band
            heightIndex hheight).2
      _ = 2 * (carriers.outerPopular.popular.heightIndices.card : ENNReal) *
          carriers.outerPopular.popular.layerMass := by
        simp [Finset.sum_const]
        ring
  calc
    volume carriers.sourceWindow.shading.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) * floor =
        floor * volume carriers.sourceWindow.shading.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) := by ring
    _ ≤ floor * ((2 * carriers.outerPopular.popular.bins : ENNReal) *
          volume carriers.outerPopular.popular.shading.union) *
            (twoScale.coarse.fineMultiplicity : ENNReal) := by gcongr
    _ ≤ floor * ((2 * carriers.outerPopular.popular.bins : ENNReal) *
          (2 * (carriers.outerPopular.popular.heightIndices.card : ENNReal) *
            carriers.outerPopular.popular.layerMass)) *
            (twoScale.coarse.fineMultiplicity : ENNReal) := by gcongr
    _ ≤ (data.rich.heightIndices.card : ENNReal) *
          ((2 * carriers.outerPopular.popular.bins : ENNReal) *
            (2 * (carriers.outerPopular.popular.heightIndices.card : ENNReal) *
              carriers.outerPopular.popular.layerMass)) *
            (twoScale.coarse.fineMultiplicity : ENNReal) := by gcongr
    _ = (4 * carriers.outerPopular.popular.bins : ENNReal) *
          (carriers.outerPopular.popular.heightIndices.card : ENNReal) *
          ((twoScale.coarse.fineMultiplicity : ENNReal) *
            ((data.rich.heightIndices.card : ENNReal) *
              carriers.outerPopular.popular.layerMass)) := by ring
    _ ≤ (4 * carriers.outerPopular.popular.bins : ENNReal) *
          (carriers.outerPopular.popular.heightIndices.card : ENNReal) *
            (3 * data.heightLift.shading.mass) := by
      exact mul_le_mul_left' data.source_mass_lower
        ((4 * carriers.outerPopular.popular.bins : ENNReal) *
          (carriers.outerPopular.popular.heightIndices.card : ENNReal))
    _ = (12 * carriers.outerPopular.popular.bins : ENNReal) *
          (carriers.outerPopular.popular.heightIndices.card : ENNReal) *
            data.heightLift.shading.mass := by ring

/-- Build the graph and its `Z_lin` output from the actual positive
graph-volume lower bound. Positivity is derived from the same quantitative
certificate later consumed by the ready-graph theorem. -/
theorem PureWZ2OrdinaryPaperOrderPreparationData.buildRichGraphOfVolumeLower
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    (prepared : PureWZ2OrdinaryPaperOrderPreparationData carriers)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hfinal : 0 < finalLoss) (hfinalOne : finalLoss < 1)
    (hfinalSigma : finalLoss / 2 < sigma)
    (hnormalEta : 0 < normalEta) (hnormalEtaSigma : 4 * normalEta < sigma)
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
    (hCOne :
      (1 : ENNReal) ≤ 10 * Kakeya.realRpowENN delta (-inputLoss))
    (hCpower :
      (10 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
        Real.rpow prepared.prep.graphScale (-constantLoss))
    (hvolume :
      Kakeya.realRpowENN prepared.prep.graphScale
          (1 + sigma / 2 + volumeLoss) ≤
        volume prepared.prep.shadow.union)
    (hextraPower : ∀ graphData : PureWZ2OrdinaryPaperOrderGraphData
        (normalEta := normalEta) prepared,
      (graphData.graph.residue.extraCost : ℝ) ≤
        Real.rpow prepared.prep.graphScale (-extraLoss))
    (hedgeAbsorb :
      Real.rpow (wz1Lemma23Theorem22Scale prepared.prep.graphScale)
          (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow prepared.prep.graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss +
              4 * extraLoss))
    (hKatzTao :
      (4 : ENNReal) ≤ Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale prepared.prep.graphScale) (-theoremEta))
    (hprojection :
      ∀ graphData : PureWZ2OrdinaryPaperOrderGraphData
          (normalEta := normalEta) prepared,
        ∀ data : PureWZ2SourceHorizontalReadyGraph
          (theoremEta := theoremEta) graphData.sharp,
        WZ1Proposition8_9AlternativeAUnion
          data.ready.deltaGraph finalLoss
          data.common.F data.common.G₁ data.common.G₁)
    (hscaleOne : 5 * prepared.prep.graphScale ≤ 1)
    (hlengthLower :
      Real.rpow (5 * prepared.prep.graphScale)
          (1 / 2 + finalLoss) ≤ twoScale.sqrtRequested.1) :
    ∃ graphData : PureWZ2OrdinaryPaperOrderGraphData
        (normalEta := normalEta) prepared,
      Nonempty (PureWZ2OrdinaryPaperOrderRichGraphData
        (finalLoss := finalLoss) (theoremEta := theoremEta) graphData) := by
  have hshadowVolume : 0 < volume prepared.prep.shadow.union := by
    have hpowerPos : 0 < Kakeya.realRpowENN prepared.prep.graphScale
        (1 + sigma / 2 + volumeLoss) :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos prepared.prep.graphScale_pos _)
    exact hpowerPos.trans_le hvolume
  rcases prepared.buildGraph hbridge hsigma hsigmaOne hnormalEta
      hnormalEtaSigma hcertificateOne hsourceFloor hlocalPower hglobalPower
      hPlanarSmall hrootSmall20 hlocalizationAbsorb hshadowVolume with
    ⟨graphData⟩
  exact ⟨graphData, graphData.buildRichGraph hsigma hsigmaOne
    hfinal hfinalOne hfinalSigma hCOne hCpower hvolume
    (hextraPower graphData) hedgeAbsorb hKatzTao (hprojection graphData)
    hscaleOne hlengthLower⟩

end Kakeya.Assouad

end
