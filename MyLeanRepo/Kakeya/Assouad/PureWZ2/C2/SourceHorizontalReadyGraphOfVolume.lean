import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalReadyGraph

/-!
# Source-horizontal ready graphs from a direct carrier-volume certificate

The ordinary Corollary-5.6 construction prepares every safe block before
discarding the blocks with small graph carrier.  This is the direct-volume
form of the existing ready-graph assembly: all geometry is unchanged, while
the volume hypothesis is stated at the point where the proof actually uses
it.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

theorem PureWZ2SourceHorizontalFixedBinSharpGeometry.toReadyGraphOfVolumeLowerFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss theoremEta
      volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalFixedBinResiduePreparation retained}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    (sharp : PureWZ2SourceHorizontalFixedBinSharpGeometry graph)
    (hheightFiberCost : graph.residue.heightFiberCost = 2)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCOne :
      (1 : ENNReal) ≤
        10 * Kakeya.realRpowENN delta (-inputLoss))
    (hCpower :
      (10 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
        Real.rpow prep.graphScale (-constantLoss))
    (hvolume :
      Kakeya.realRpowENN prep.graphScale
          (1 + sigma / 2 + volumeLoss) ≤
        volume prep.shadow.union)
    (hextraPower :
      (graph.residue.extraCost : ℝ) ≤
        Real.rpow prep.graphScale (-extraLoss))
    (hedgeAbsorb :
      Real.rpow (wz1Lemma23Theorem22Scale prep.graphScale)
          (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow prep.graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss +
              4 * extraLoss))
    (hKatzTao :
      (4 : ENNReal) ≤
        Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale prep.graphScale) (-theoremEta)) :
    Nonempty (PureWZ2SourceHorizontalFixedBinReadyGraph
      (theoremEta := theoremEta) sharp) := by
  let C : ENNReal :=
    10 * Kakeya.realRpowENN delta (-inputLoss)
  have hCtop : C ≠ ⊤ := by
    dsimp only [C]
    exact ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN])
  have hcoord :
      ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hpaper : point ∈ retained.shading.union := by
      exact prep.shadow_union_subset hpoint
    have hbox := shading_union_subset_axisBox hpaper
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hedgeReal :
      Real.rpow (wz1Lemma23Theorem22Scale prep.graphScale)
          (theoremEta - 3) ≤
        (sharp.sharp.normalized.H.card : ℝ) := by
    apply hedgeAbsorb.trans
    exact sharp.sharp.power_edge_bound_of_coord
      prep.graphScale_one hsigma hsigmaOne hcoord
      hCOne hCtop volumeLoss constantLoss extraLoss
      hvolume hCpower hextraPower
  have hedgeNormalized :
      Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale prep.graphScale)
          (theoremEta - 3) ≤
        (sharp.sharp.normalized.H.card : ENNReal) := by
    rw [Kakeya.realRpowENN]
    have hcast :
        (sharp.sharp.normalized.H.card : ENNReal) =
          ENNReal.ofReal (sharp.sharp.normalized.H.card : ℝ) := by
      norm_cast
    rw [hcast]
    exact ENNReal.ofReal_le_ofReal hedgeReal
  have hedgeUnit :
      Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale prep.graphScale)
          (theoremEta - 3) ≤
        (sharp.geometry.unitBall.H.card : ENNReal) := by
    rw [sharp.geometry.unitBall.edge_card]
    exact hedgeNormalized
  rcases sharp.geometry.toCommonEndpointReadyGraph
      prep.graphScale_one hcoord hedgeUnit hKatzTao with
    ⟨common, ready⟩
  exact ⟨{ common := common
           ready := Classical.choice ready
           heightFiberCost_eq := hheightFiberCost }⟩

/-- Compatibility wrapper for the former maximal-bin direct-volume API. -/
theorem PureWZ2SourceHorizontalSharpGeometry.toReadyGraphOfVolumeLower
    {sigma inputLoss delta rho middleLoss outputLoss theoremEta
      volumeLoss constantLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    (sharp : PureWZ2SourceHorizontalSharpGeometry graph)
    (hheightFiberCost : graph.residue.heightFiberCost = 2)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCOne : (1 : ENNReal) ≤ 10 * Kakeya.realRpowENN delta (-inputLoss))
    (hCpower : (10 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
      Real.rpow prep.graphScale (-constantLoss))
    (hvolume : Kakeya.realRpowENN prep.graphScale
      (1 + sigma / 2 + volumeLoss) ≤ volume prep.shadow.union)
    (hextraPower : (graph.residue.extraCost : ℝ) ≤
      Real.rpow prep.graphScale (-extraLoss))
    (hedgeAbsorb : Real.rpow (wz1Lemma23Theorem22Scale prep.graphScale)
      (theoremEta - 3) ≤ (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
        Real.rpow prep.graphScale
          (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss))
    (hKatzTao : (4 : ENNReal) ≤ Kakeya.realRpowENN
      (wz1Lemma23Theorem22Scale prep.graphScale) (-theoremEta)) :
    Nonempty (PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp) :=
  PureWZ2SourceHorizontalFixedBinSharpGeometry.toReadyGraphOfVolumeLowerFixedBin
    sharp hheightFiberCost hsigma hsigmaOne hCOne hCpower hvolume hextraPower
    hedgeAbsorb hKatzTao

end Kakeya.Assouad
