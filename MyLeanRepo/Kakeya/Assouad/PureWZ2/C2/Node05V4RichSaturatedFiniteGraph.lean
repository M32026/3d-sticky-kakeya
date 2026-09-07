import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichNeighborhoodLocalBins
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinAnchoredTheorem52

/-!
# Same-witness saturated finite graph for Node 5

This record keeps the graph preparation, its source-witness parent map, the
saturated local grains, the resulting local graph, and the finite four-cycle
graph in one dependent object.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2Node05V4RichSaturatedFiniteGraphData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    (neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : neighborhood.saturatedGraphScale ≤ 1) where
  prep : PureWZ2AnchoredGraphPreparationData
    (neighborhood.graphInput hbridge hgraphOne)
  parents : PureWZ2Node05V4RichNeighborhoodGraphParentData prep
  saturated : PureWZ2Node05V4RichSaturatedNeighborhoodFullGrainData
    (eta := eta) neighborhood
  local_power :
    160 * Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN (4 * rhoRequested.1) (-eta)
  localGraph : PureWZ2Node05V4RichNeighborhoodGraphData
    (prep := prep) (eta := eta) parents
  localBins : WZ1Lemma23LocalBinPackage
    (rho := neighborhood.graphScale) (sigma := sigma)
    (160 * Kakeya.realRpowENN delta (-inputLoss))
    prep.windowed.global.cells
  finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins

namespace PureWZ2PreCommonBinGlobalGrainNeighborhoodData

/-- Construct the complete pre-Theorem-5.2 graph from one direct-rich
neighborhood without splicing independently chosen witnesses. -/
theorem saturatedFiniteGraph
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    (neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : neighborhood.saturatedGraphScale ≤ 1)
    (hheightAbsorb :
      neighborhood.saturatedGraphScale + 2 * Real.sqrt rho ≤
        16 * Real.sqrt rho)
    (hsourcePower :
      ((32 * Kakeya.realRpowENN delta (-inputLoss) *
            Kakeya.realRpowENN delta sigma *
            Kakeya.realRpowENN rho (2 - sigma)) *
          ENNReal.ofReal rho) *
          Kakeya.realRpowENN (4 * rhoRequested.1)
            (3 / 2 + sigma / 2 + eta) ≤
        (Kakeya.realRpowENN rhoRequested.1 3 *
            Kakeya.realRpowENN (delta / rhoRequested.1)
              (sigma + 2 * twoScale.first.rich.terminalLoss)) *
          Kakeya.realRpowENN rhoRequested.1
            (3 / 2 + sigma / 2 + twoScale.second.terminalLoss))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rhoRequested.1) (-eta))
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hcertificateOne : 4 * rhoRequested.1 ≤ 1)
    (hPlanarSmall : 32 * Real.rpow (4 * rhoRequested.1) eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rhoRequested.1) ≤ 1)
    (habsorb :
      Real.rpow (4 * rhoRequested.1) (1 - 4 * eta / sigma) ≤
        Real.sqrt (4 * rhoRequested.1) / 14) :
    Nonempty (PureWZ2Node05V4RichSaturatedFiniteGraphData
      (eta := eta) neighborhood hbridge hgraphOne) := by
  rcases neighborhood.graphPreparation hbridge hgraphOne hheightAbsorb with
    ⟨prep⟩
  rcases neighborhood.graphParents prep hheightAbsorb with ⟨parents⟩
  rcases neighborhood.saturatedFullGrains hbridge hcertificateOne
      hsourcePower hlocalPower with ⟨saturated⟩
  rcases parents.localGraph (prep := prep) (eta := eta) saturated
      hsigma hsigmaOne heta hetaSigma
      hlocalPower hcertificateOne hPlanarSmall hrootSmall20 habsorb with
    ⟨localGraph⟩
  rcases localGraph.localBins with ⟨localBins⟩
  have htargetPos : 0 < Kakeya.realRpowENN (4 * rhoRequested.1)
      (3 / 2 + sigma / 2 + eta) := by
    apply ENNReal.ofReal_pos.mpr
    apply Real.rpow_pos_of_pos
    have hrhoRequested : 0 < rhoRequested.1 :=
      twoScale.first.publicSticky.coarse_extremal.delta_pos
    positivity
  have hKPos : 0 < (neighborhood.K : ENNReal) := by
    rw [neighborhood.K_eq]
    exact_mod_cast neighborhood.sample_nonempty.card_pos
  have hvolumeLower := neighborhood.saturatedUnion_volume_lower
    (Kakeya.realRpowENN (4 * rhoRequested.1)
      (3 / 2 + sigma / 2 + eta))
    (fun y hy => pullback.sameHeightParentSaturation_volume_lower
      (neighborhood.cube_active hy) _ hsourcePower)
  have hvolumePos : 0 < volume neighborhood.graphShadow.union := by
    rw [neighborhood.graphShadow_union]
    exact (ENNReal.mul_pos hKPos.ne' htargetPos.ne').trans_le hvolumeLower
  rcases prep.prepareFiniteGraph localBins hvolumePos with ⟨finiteGraph⟩
  exact ⟨{
    prep := prep
    parents := parents
    saturated := saturated
    local_power := hlocalPower
    localGraph := localGraph
    localBins := localBins
    finiteGraph := finiteGraph
  }⟩

end PureWZ2PreCommonBinGlobalGrainNeighborhoodData

namespace PureWZ2Node05V4RichSaturatedFiniteGraphData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : neighborhood.saturatedGraphScale ≤ 1}
    (data : PureWZ2Node05V4RichSaturatedFiniteGraphData
      (eta := eta) neighborhood hbridge hgraphOne)

/-- Every occupied cell of the auxiliary graph retains an actual point of the
original source at exactly the representative's height.  This is the
source-layer receipt needed after height popularity; the auxiliary carrier is
never replaced by the whole graph cell. -/
theorem graphCell_actualSourceHeight
    (cell : WZ2PaperCellIndex)
    (hcell : cell ∈ data.prep.windowed.global.cells) :
    data.parents.sourceWitness cell ∈
        pullback.preCommonBinFinePullback
          (neighborhood.cube (data.parents.parentY cell)) ∧
      data.parents.sourceWitness cell (2 : Fin 3) =
        data.parents.representative cell (2 : Fin 3) ∧
      data.parents.representative cell ∈
        pullback.sameHeightParentSaturation
          (neighborhood.cube (data.parents.parentY cell)) ∧
      dist (data.parents.representative cell)
          (data.parents.sourceWitness cell) ≤ 2 * rho := by
  exact ⟨data.parents.sourceWitness_mem_pullback cell hcell,
    data.parents.sourceWitness_height cell hcell,
    data.parents.representative_mem_saturation cell hcell,
    data.parents.representative_source_dist cell hcell⟩

include data in
/-- The stored saturated local grains and the paper lower bound on the number
of selected parents give the graph-volume hypothesis from one scalar power
comparison.  No independently selected carrier-volume witness is used. -/
theorem graph_volume_lower
    (volumeLoss : ℝ)
    (hpower :
      Kakeya.realRpowENN neighborhood.graphScale
          (1 + sigma / 2 + volumeLoss) ≤
        Kakeya.realRpowENN rho
            (-1 / 2 + neighborhood.neighborhoodLoss) *
          Kakeya.realRpowENN (4 * rhoRequested.1)
            (3 / 2 + sigma / 2 + eta)) :
    Kakeya.realRpowENN neighborhood.graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      MeasureTheory.volume neighborhood.graphShadow.union := by
  rw [neighborhood.graphShadow_union]
  apply hpower.trans
  calc
    Kakeya.realRpowENN rho
          (-1 / 2 + neighborhood.neighborhoodLoss) *
        Kakeya.realRpowENN (4 * rhoRequested.1)
          (3 / 2 + sigma / 2 + eta) ≤
      (neighborhood.K : ENNReal) *
        Kakeya.realRpowENN (4 * rhoRequested.1)
          (3 / 2 + sigma / 2 + eta) := by
        simpa only [mul_comm] using
          (mul_le_mul_left neighborhood.paper_K_lower
            (Kakeya.realRpowENN (4 * rhoRequested.1)
              (3 / 2 + sigma / 2 + eta)))
    _ ≤ MeasureTheory.volume neighborhood.saturatedUnion := by
      apply neighborhood.saturatedUnion_volume_lower
      intro y hy
      let grain :=
        PureWZ2Node05V4RichSaturatedNeighborhoodFullGrainData.fullGrainFor
          (PureWZ2Node05V4RichSaturatedFiniteGraphData.saturated data) y hy
      simpa only [grain.certificateScale_eq, grain.saturatedSource_eq] using
        grain.saturatedSource_volume_lower

/-- Execute the already closed common-bin/four-cycle/Theorem-5.2 chain on
the saturated finite graph.  All analytic losses remain explicit scalar
premises for the P0 master schedule. -/
theorem theorem52
    {finalLoss : ℝ}
    (projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (houtput : 0 < finalLoss) (houtputOne : finalLoss < 1)
    (houtputSigma : finalLoss / 2 < sigma)
    (hCOne : (1 : ENNReal) ≤
      160 * Kakeya.realRpowENN delta (-inputLoss))
    (constantLoss volumeLoss extraLoss sourceCostLoss : ℝ)
    (hCpower :
      (160 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
        Real.rpow neighborhood.graphScale (-constantLoss))
    (hvolume : ENNReal.ofReal
        (Real.rpow neighborhood.graphScale
          (1 + sigma / 2 + volumeLoss)) ≤
      volume neighborhood.graphShadow.union)
    (hextraPower :
      (data.finiteGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow neighborhood.graphScale (-extraLoss))
    (hedgeAbsorb :
      Real.rpow (wz1Lemma23Theorem22Scale neighborhood.graphScale)
          (projection.theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow neighborhood.graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss))
    (hKatzTao : (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale neighborhood.graphScale)
        (-projection.theoremEta))
    (hCbound :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        10 * Kakeya.realRpowENN rhoRequested.1 (-eta))
    (hsourceCost :
      Kakeya.realRpowENN rhoRequested.1 (-eta) ≤
        Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale neighborhood.graphScale)
          (-sourceCostLoss))
    (hsourceCostLoss : 0 ≤ sourceCostLoss)
    (hsourceCostCeiling :
      sourceCostLoss ≤ projection.sourceCostLossCeiling)
    (hdeltaSmall :
      wz1Lemma23Theorem22Scale neighborhood.graphScale ≤
        projection.reductionDelta₀)
    (hconstantSmall :
      (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale neighborhood.graphScale)
          (-(projection.projectionEta * (sigma - finalLoss / 2) -
            (10 * projection.theoremEta + sourceCostLoss)) / 2)) :
    Nonempty (PureWZ2AnchoredTheorem52Output data.finiteGraph projection) :=
  data.finiteGraph.theorem52 (sourceScale := rhoRequested.1)
    (inputLoss := eta) projection hsigma hsigmaOne
    houtput houtputOne houtputSigma hCOne hCpower hvolume hextraPower
    hedgeAbsorb hKatzTao hCbound hsourceCost hsourceCostLoss
    hsourceCostCeiling hdeltaSmall hconstantSmall

end PureWZ2Node05V4RichSaturatedFiniteGraphData

end Kakeya.Assouad

end
