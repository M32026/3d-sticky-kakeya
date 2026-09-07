import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseSharpGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23CommonEndpointGraph

/-!
# Theorem-22-ready graph on the genuine coarse carrier

The only quantitative input not already stored in the sharp graph is the
actual lower bound for the genuine coarse shadow.  In particular, no volume
estimate for the old original-source graph carrier is used here.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2SourceFixedBinCoarseReadyGraph
    {sigma inputLoss delta rho middleLoss stickyLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale} {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared} {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line} {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection} {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue} {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData
      graphParents normalFirst}
    (sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph) where
  common : WZ1Lemma23UnitBallGraph prep.graphScale
    sharp.sharp.normalized.F
    (wz1Lemma23CommonLocalVertices prep.graphScale
      sharp.sharp.selectedLocal.g preparedGraph.graph.residue.cells)
    (wz1Lemma23CommonLocalVertices prep.graphScale
      sharp.sharp.selectedLocal.g preparedGraph.graph.residue.cells)
    sharp.sharp.normalized.H
  ready : WZ1Lemma23Theorem22ReadyGraph
    prep.graphScale theoremEta common
  heightFiberCost_eq : preparedGraph.graph.residue.heightFiberCost = 2

abbrev PureWZ2SourceFixedLineCoarseReadyGraph
    {sigma inputLoss delta rho middleLoss stickyLoss eta theoremEta : ℝ} {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {original : PureWZ2SourceFixedLineCoarseOriginalSlopeData carriers.coarseCarrier carriers.fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedLineCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedLineCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalNormalFirstCertificate (eta := eta) carriers.fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedLineCoarsePreparedGraphData graphParents normalFirst}
    (sharp : PureWZ2SourceFixedLineCoarseSharpGeometry preparedGraph) : Type :=
  PureWZ2SourceFixedBinCoarseReadyGraph (theoremEta := theoremEta) sharp

/-- Assemble the common-endpoint ready graph from the genuine-coarse volume
lower bound and the standard Lemma-23 power absorptions. -/
theorem PureWZ2SourceFixedBinCoarseSharpGeometry.toReadyGraphFixedBin
    {sigma inputLoss delta rho middleLoss stickyLoss eta theoremEta
      volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale} {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared} {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line} {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection} {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue} {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData graphParents normalFirst}
    (sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCOne : (1 : ENNReal) ≤
      10 * Kakeya.realRpowENN rho (-middleLoss))
    (hCpower :
      (10 * Kakeya.realRpowENN rho (-middleLoss)).toReal ≤
        Real.rpow prep.graphScale (-constantLoss))
    (hvolume : ENNReal.ofReal
        (Real.rpow prep.graphScale (1 + sigma / 2 + volumeLoss)) ≤
      MeasureTheory.volume prep.shadow.union)
    (hextraPower : (preparedGraph.graph.residue.extraCost : ℝ) ≤
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
        (wz1Lemma23Theorem22Scale prep.graphScale) (-theoremEta)) :
    Nonempty (PureWZ2SourceFixedBinCoarseReadyGraph
      (theoremEta := theoremEta) sharp) := by
  let C : ENNReal := 10 * Kakeya.realRpowENN rho (-middleLoss)
  have hCtop : C ≠ ⊤ := by
    dsimp only [C]
    exact ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  have hcoord : ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hcarrier : point ∈ carrier.shading.union := by
      exact prep.shadow_union_subset hpoint
    have hbox := shading_union_subset_axisBox
      (carrier.subshading.union_subset hcarrier)
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hedgeReal :
      Real.rpow (wz1Lemma23Theorem22Scale prep.graphScale)
          (theoremEta - 3) ≤
        (sharp.sharp.normalized.H.card : ℝ) := by
    apply hedgeAbsorb.trans
    exact sharp.sharp.power_edge_bound_of_coord prep.graphScale_one
      hsigma hsigmaOne hcoord hCOne hCtop volumeLoss constantLoss extraLoss
      hvolume hCpower hextraPower
  have hedgeNormalized :
      Kakeya.realRpowENN (wz1Lemma23Theorem22Scale prep.graphScale)
          (theoremEta - 3) ≤
        (sharp.sharp.normalized.H.card : ENNReal) := by
    rw [Kakeya.realRpowENN]
    have hcast : (sharp.sharp.normalized.H.card : ENNReal) =
        ENNReal.ofReal (sharp.sharp.normalized.H.card : ℝ) := by norm_cast
    rw [hcast]
    exact ENNReal.ofReal_le_ofReal hedgeReal
  have hedgeUnit :
      Kakeya.realRpowENN (wz1Lemma23Theorem22Scale prep.graphScale)
          (theoremEta - 3) ≤
        (sharp.geometry.unitBall.H.card : ENNReal) := by
    rw [sharp.geometry.unitBall.edge_card]
    exact hedgeNormalized
  rcases sharp.geometry.toCommonEndpointReadyGraph prep.graphScale_one hcoord
      hedgeUnit hKatzTao with ⟨common, ready⟩
  exact ⟨{
    common := common
    ready := Classical.choice ready
    heightFiberCost_eq := preparedGraph.heightFiberCost_eq
  }⟩

/-- Backwards-compatible maximal-bin constructor for the ready graph. -/
theorem PureWZ2SourceFixedLineCoarseSharpGeometry.toReadyGraph
    {sigma inputLoss delta rho middleLoss stickyLoss eta theoremEta volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ} {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {original : PureWZ2SourceFixedLineCoarseOriginalSlopeData carriers.coarseCarrier carriers.fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedLineCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedLineCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalNormalFirstCertificate (eta := eta) carriers.fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedLineCoarsePreparedGraphData graphParents normalFirst}
    (sharp : PureWZ2SourceFixedLineCoarseSharpGeometry preparedGraph)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCOne : (1 : ENNReal) ≤ 10 * Kakeya.realRpowENN rho (-middleLoss))
    (hCpower : (10 * Kakeya.realRpowENN rho (-middleLoss)).toReal ≤ Real.rpow prep.graphScale (-constantLoss))
    (hvolume : ENNReal.ofReal (Real.rpow prep.graphScale (1 + sigma / 2 + volumeLoss)) ≤ MeasureTheory.volume prep.shadow.union)
    (hextraPower : (preparedGraph.graph.residue.extraCost : ℝ) ≤ Real.rpow prep.graphScale (-extraLoss))
    (hedgeAbsorb : Real.rpow (wz1Lemma23Theorem22Scale prep.graphScale) (theoremEta - 3) ≤
      (wz1Lemma23EdgeConstant : ℝ)⁻¹ * Real.rpow prep.graphScale
        (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss))
    (hKatzTao : (4 : ENNReal) ≤ Kakeya.realRpowENN
      (wz1Lemma23Theorem22Scale prep.graphScale) (-theoremEta)) :
    Nonempty (PureWZ2SourceFixedLineCoarseReadyGraph (theoremEta := theoremEta) sharp) :=
  PureWZ2SourceFixedBinCoarseSharpGeometry.toReadyGraphFixedBin sharp
    hsigma hsigmaOne hCOne hCpower hvolume hextraPower hedgeAbsorb hKatzTao

end Kakeya.Assouad

end
