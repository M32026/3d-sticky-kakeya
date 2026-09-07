import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightLocalGraph
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSaturatedAnalytic

/-!
# Final finite graph on the joint-height production witness

This module assembles graph preparation, source-parent provenance, direct-rich
full grains, local `g`, local bins, and the finite four-cycle graph on one
dependent runtime witness.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2Node05V4RichJointFiniteGraphData
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
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    {volumePopular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex}
    {B₀ threshold : ENNReal}
    {block : volumePopular.JointHeightCommonBinData B₀ threshold}
    {oneParent : block.JointOneParentPerYData}
    (separated : PureWZ2Node05V4RichJointSeparatedParentData oneParent)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : separated.graphScale ≤ 1) where
  prep : PureWZ2AnchoredGraphPreparationData
    (separated.graphInput hbridge hgraphOne)
  parents : PureWZ2Node05V4RichJointGraphParentData prep
  grains : PureWZ2Node05V4RichJointFullGrainData
    (eta := eta) separated
  localGraph : PureWZ2Node05V4RichJointLocalGraphData parents grains
  localBins : WZ1Lemma23LocalBinPackage
    (rho := separated.graphScale) (sigma := sigma)
    (160 * Kakeya.realRpowENN delta (-inputLoss))
    prep.windowed.global.cells
  finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins
  local_power :
    160 * Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN (4 * rhoRequested.1) (-eta)

namespace PureWZ2Node05V4RichJointSeparatedParentData

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
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    {volumePopular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex}
    {B₀ threshold : ENNReal}
    {block : volumePopular.JointHeightCommonBinData B₀ threshold}
    {oneParent : block.JointOneParentPerYData}
    (separated : PureWZ2Node05V4RichJointSeparatedParentData oneParent)

theorem saturatedUnion_volume_pos :
    0 < volume separated.saturatedUnion := by
  have hintegratedPos :
      0 < volumePopular.jointIntegratedBinMass
        block.referenceHeight block.bin := by
    have hproductPos :
        0 < 4 * ((volumePopular.jointRichCommonBinLabels
          block.referenceHeight threshold).card : ENNReal) *
            volumePopular.jointIntegratedBinMass
              block.referenceHeight block.bin :=
      volumePopular.jointSourceSet_volume_pos.trans_le block.source_average
    by_contra hnot
    have hzero :
        volumePopular.jointIntegratedBinMass
          block.referenceHeight block.bin = 0 :=
      bot_unique (not_lt.mp hnot)
    rw [hzero, mul_zero] at hproductPos
    exact (lt_irrefl 0 hproductPos)
  have hallPos : 0 < volume block.jointSaturatedUnion :=
    hintegratedPos.trans_le block.jointFixedBin_volume_le_saturation
  have honePos : 0 < volume oneParent.saturatedUnion := by
    have hscaled :
        0 < 45 * volume oneParent.saturatedUnion :=
      hallPos.trans_le oneParent.volume_retention
    by_contra hnot
    have hzero : volume oneParent.saturatedUnion = 0 :=
      bot_unique (not_lt.mp hnot)
    rw [hzero, mul_zero] at hscaled
    exact (lt_irrefl 0 hscaled)
  have hscaled :
      0 < 512 * volume separated.saturatedUnion :=
    honePos.trans_le separated.volume_retention
  by_contra hnot
  have hzero : volume separated.saturatedUnion = 0 :=
    bot_unique (not_lt.mp hnot)
  rw [hzero, mul_zero] at hscaled
  exact (lt_irrefl 0 hscaled)

theorem finalFiniteGraph
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : separated.graphScale ≤ 1)
    (hheightAbsorb :
      separated.graphScale + 2 * Real.sqrt rho ≤ 16 * Real.sqrt rho)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hcertificateOne : 4 * rhoRequested.1 ≤ 1)
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
    (hPlanarSmall : 32 * Real.rpow (4 * rhoRequested.1) eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rhoRequested.1) ≤ 1)
    (habsorb :
      Real.rpow (4 * rhoRequested.1) (1 - 4 * eta / sigma) ≤
        Real.sqrt (4 * rhoRequested.1) / 14) :
    Nonempty (PureWZ2Node05V4RichJointFiniteGraphData
      (eta := eta) separated hbridge hgraphOne) := by
  have hsqrtGraph :
      Real.sqrt separated.graphScale = 16 * Real.sqrt rho := by
    unfold graphScale
    rw [Real.sqrt_mul (by norm_num),
      show Real.sqrt (256 : ℝ) = 16 by norm_num]
  rcases separated.graphPreparation hbridge hgraphOne
      (by
        rw [hsqrtGraph]
        have hroot : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
        linarith) with ⟨prep⟩
  rcases separated.graphParents prep with ⟨parents⟩
  rcases separated.fullGrains hbridge hcertificateOne hsourcePower
      hlocalPower with ⟨grains⟩
  rcases grains.localGraph parents hheightAbsorb hsigma hsigmaOne heta hetaSigma
      hlocalPower hcertificateOne hPlanarSmall hrootSmall20 habsorb with
    ⟨localGraph⟩
  rcases localGraph.localBins with ⟨localBins⟩
  have hvolumePos : 0 < volume separated.graphShading.union := by
    rw [separated.graphShading_union]
    exact separated.saturatedUnion_volume_pos
  rcases prep.prepareFiniteGraph localBins hvolumePos with ⟨finiteGraph⟩
  exact ⟨{
    prep := prep
    parents := parents
    grains := grains
    localGraph := localGraph
    localBins := localBins
    finiteGraph := finiteGraph
    local_power := hlocalPower
  }⟩

end PureWZ2Node05V4RichJointSeparatedParentData

namespace PureWZ2Node05V4RichJointFiniteGraphData

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
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    {volumePopular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex}
    {B₀ threshold : ENNReal}
    {block : volumePopular.JointHeightCommonBinData B₀ threshold}
    {oneParent : block.JointOneParentPerYData}
    {separated : PureWZ2Node05V4RichJointSeparatedParentData oneParent}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : separated.graphScale ≤ 1}
    (data : PureWZ2Node05V4RichJointFiniteGraphData
      (eta := eta) separated hbridge hgraphOne)

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
        Real.rpow separated.graphScale (-constantLoss))
    (hvolume : ENNReal.ofReal
        (Real.rpow separated.graphScale
          (1 + sigma / 2 + volumeLoss)) ≤
      volume separated.graphShading.union)
    (hextraPower :
      (data.finiteGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow separated.graphScale (-extraLoss))
    (hedgeAbsorb :
      Real.rpow (wz1Lemma23Theorem22Scale separated.graphScale)
          (projection.theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow separated.graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss))
    (hKatzTao : (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale separated.graphScale)
        (-projection.theoremEta))
    (hCbound :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        10 * Kakeya.realRpowENN rhoRequested.1 (-eta))
    (hsourceCost :
      Kakeya.realRpowENN rhoRequested.1 (-eta) ≤
        Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale separated.graphScale)
          (-sourceCostLoss))
    (hsourceCostLoss : 0 ≤ sourceCostLoss)
    (hsourceCostCeiling :
      sourceCostLoss ≤ projection.sourceCostLossCeiling)
    (hdeltaSmall :
      wz1Lemma23Theorem22Scale separated.graphScale ≤
        projection.reductionDelta₀)
    (hconstantSmall :
      (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale separated.graphScale)
          (-(projection.projectionEta * (sigma - finalLoss / 2) -
            (10 * projection.theoremEta + sourceCostLoss)) / 2)) :
    Nonempty (PureWZ2AnchoredTheorem52Output data.finiteGraph projection) :=
  data.finiteGraph.theorem52 (sourceScale := rhoRequested.1)
    (inputLoss := eta) projection hsigma hsigmaOne
    houtput houtputOne houtputSigma hCOne hCpower hvolume hextraPower
    hedgeAbsorb hKatzTao hCbound hsourceCost hsourceCostLoss
    hsourceCostCeiling hdeltaSmall hconstantSmall

/-- Apply the existing pre-runtime analytic and projection schedules to the
joint-height finite graph.  Only the direct graph-volume and AD-constant
power comparisons remain explicit. -/
theorem theorem52OfThresholds
    {finalLoss : ℝ}
    (projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss)
    (analytic : PureWZ2SourceHorizontalAnalyticThreshold projection.theoremEta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (houtput : 0 < finalLoss) (houtputOne : finalLoss < 1)
    (houtputSigma : finalLoss / 2 < sigma)
    (heta : 0 < eta)
    (hCOne : (1 : ENNReal) ≤
      160 * Kakeya.realRpowENN delta (-inputLoss))
    (hCpower :
      (160 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
        Real.rpow separated.graphScale (-analytic.budget.constantLoss))
    (hgraphVolume :
      Kakeya.realRpowENN separated.graphScale
          (1 + sigma / 2 + analytic.budget.volumeLoss) ≤
        volume separated.graphShading.union)
    (hsourceCost :
      Kakeya.realRpowENN rhoRequested.1 (-eta) ≤
        Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale separated.graphScale)
          (-projection.sourceCostLossCeiling))
    (hgraphAnalytic : separated.graphScale ≤ analytic.rho0)
    (hrhoProjection : rho ≤ projection.rho₀) :
    Nonempty (PureWZ2AnchoredTheorem52Output data.finiteGraph projection) := by
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hrhoRequested : 0 < rhoRequested.1 := by
    rw [pullback.rhoRequested_eq]
    exact hrho
  have hrhoAnalytic : rho ≤ analytic.rho0 := by
    apply (show rho ≤ separated.graphScale by
      unfold PureWZ2Node05V4RichJointSeparatedParentData.graphScale
      linarith).trans hgraphAnalytic
  have hcertificateToSource :
      Kakeya.realRpowENN (4 * rhoRequested.1) (-eta) ≤
        Kakeya.realRpowENN rhoRequested.1 (-eta) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_nonpos hrhoRequested
      (by nlinarith) (by linarith)
  have hCbound :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        10 * Kakeya.realRpowENN rhoRequested.1 (-eta) :=
    data.local_power.trans <| calc
      Kakeya.realRpowENN (4 * rhoRequested.1) (-eta) ≤
          Kakeya.realRpowENN rhoRequested.1 (-eta) := hcertificateToSource
      _ ≤ 10 * Kakeya.realRpowENN rhoRequested.1 (-eta) := by
        exact le_mul_of_one_le_left (by positivity) (by norm_num)
  apply data.theorem52 projection hsigma hsigmaOne houtput houtputOne
    houtputSigma hCOne analytic.budget.constantLoss
    analytic.budget.volumeLoss analytic.budget.extraLoss
    projection.sourceCostLossCeiling
    hCpower (by simpa only [Kakeya.realRpowENN] using hgraphVolume)
  · exact data.finiteGraph.extraCost_le_quadraticLog.trans
      (analytic.extraScalar rho separated.graphScale hrho hrhoAnalytic rfl)
  · exact analytic.edge separated.graphScale
      separated.graphScale_pos hgraphAnalytic
  · exact analytic.katzTao separated.graphScale
      separated.graphScale_pos hgraphAnalytic
  · exact hCbound
  · exact hsourceCost
  · exact projection.sourceCostLossCeiling_pos.le
  · exact le_rfl
  · simpa only [
      PureWZ2Node05V4RichJointSeparatedParentData.graphScale] using
      projection.graph_small rho hrho hrhoProjection
  · simpa only [
      PureWZ2Node05V4RichJointSeparatedParentData.graphScale] using
      projection.constant_small rho hrho hrhoProjection

/-- On the final same-height saturation, rich graph height indices belong
literally to the preselected source-volume-popular band. -/
theorem richHeightIndices_subset_popular
    {finalLoss : ℝ}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (output : PureWZ2AnchoredTheorem52Output data.finiteGraph projection) :
    output.richHeightIndices ⊆
      volumePopular.popular.heightIndices := by
  intro graphHeight hgraphHeight
  rw [PureWZ2AnchoredTheorem52Output.richHeightIndices] at hgraphHeight
  rcases Finset.mem_image.mp hgraphHeight with
    ⟨richPoint, hrichPoint, hgraphHeightEq⟩
  let cell := output.lineData.graphCell richPoint
  have hcellResidue :=
    output.lineData.graphCell_mem_residue richPoint hrichPoint
  have hcellGlobal :=
    data.finiteGraph.graph.residue.cells_subset hcellResidue
  have hsource :=
    data.parents.sourceWitness_mem cell hcellGlobal
  have hsourceJoint :
      data.parents.sourceWitness cell ∈ volumePopular.jointSourceSet :=
    hsource.1.1.1
  rw [PureWZ2Node05V4RichSourceVolumePopularHeightData.jointSourceSet,
    volumePopular.popular.union_eq] at hsourceJoint
  rw [volumePopular.popular.heightRegion_eq] at hsourceJoint
  rcases Set.mem_iUnion₂.mp hsourceJoint.2 with
    ⟨popularHeight, hpopularHeight, hsourceSlab⟩
  have hrepresentativeSlab :
      data.parents.representative cell ∈
        wz1Lemma23HeightSlab separated.graphScale popularHeight := by
    have hheight := data.parents.sourceWitness_height cell hcellGlobal
    change data.parents.sourceWitness cell (2 : Fin 3) ∈
      wz1Lemma23HeightInterval (256 * rho) popularHeight at hsourceSlab
    change data.parents.representative cell (2 : Fin 3) ∈
      wz1Lemma23HeightInterval separated.graphScale popularHeight
    rw [← hheight]
    simpa only [
      PureWZ2Node05V4RichJointSeparatedParentData.graphScale] using hsourceSlab
  have hfloorPopular := (wz1Lemma23_mem_heightSlab_iff
    separated.graphScale_pos popularHeight
      (data.parents.representative cell)).mp hrepresentativeSlab
  have hcellHeight := congrArg
    (fun index : WZ2PaperCellIndex => index.2.2)
    (data.parents.representative_index cell hcellGlobal)
  have hfloorCell :
      Int.floor
          (data.parents.representative cell (2 : Fin 3) /
            gridSide (separated.graphScale / 2)) = cell.2.2 := by
    simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using hcellHeight
  have hpopularEq : popularHeight = cell.2.2 := by
    exact hfloorPopular.symm.trans hfloorCell
  have hgraphEq : cell.2.2 = graphHeight := by
    simpa [cell,
      PureWZ2AnchoredTheorem52Output.richHeightIndex] using hgraphHeightEq
  rwa [hpopularEq, hgraphEq] at hpopularHeight

/-- Identity height assignment on the exact same-height production graph.
The fibre bound is one (recorded in the common bound-three interface). -/
theorem exactHeightAssignment
    {finalLoss : ℝ}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (output : PureWZ2AnchoredTheorem52Output data.finiteGraph projection) :
    ∃ assignment : PureWZ2Node05V4RichHeightAssignmentData
        output.richHeightIndices volumePopular.popular.heightIndices,
      assignment.assigned = id := by
  refine ⟨{
    assigned := id
    assigned_mem := fun height hheight =>
      data.richHeightIndices_subset_popular output hheight
    assigned_near := by simp
    assigned_fiber_card := ?_
  }, rfl⟩
  intro popularHeight
  have hsubset :
      output.richHeightIndices.filter
          (fun heightIndex => id heightIndex = popularHeight) ⊆
        {popularHeight} := by
    intro heightIndex hheight
    rw [Finset.mem_filter] at hheight
    simpa using hheight.2
  exact (Finset.card_le_card hsubset).trans (by simp)

/-- Bounded-fibre assignment of this exact Theorem-5.2 output to the
preselected comparable-volume band inside continuous `Z_S`. -/
theorem heightAssignment
    (outerEnvelope :
      PureWZ2Node05V4RichSourceVolumePopularEnvelopeData volumePopular)
    {finalLoss : ℝ}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (output : PureWZ2AnchoredTheorem52Output data.finiteGraph projection) :
    Nonempty
      (PureWZ2Node05V4RichHeightAssignmentData
        output.richHeightIndices volumePopular.popular.heightIndices) := by
  apply pureWZ2Node05V4Rich_sourceVolumePopularHeightAssignment
    outerEnvelope output
      (show separated.graphScale = 256 * rho from rfl)
      data.parents.representative
      data.parents.representative_mem
      data.parents.representative_index
  intro point hpoint
  rw [separated.graphShading_union] at hpoint
  rcases separated.saturatedUnion_exists_source_same_height hpoint with
    ⟨cell, _hcell, hpointSat, sourcePoint, hsourcePoint, _hheight⟩
  refine ⟨sourcePoint,
    volumePopular.jointFixedBinHeightRegion_subset_volumePopular
      block hsourcePoint.1, ?_⟩
  have hpointCube :=
    wz1PaperGridCubeSameHeightSaturation_subset_cube
      rho cell (block.jointCellSource cell) hpointSat
  exact wz1_paper_grid_cube_diameter_lt_two_rho
    (by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos)
    hpointCube hsourcePoint.2

/-- Weighted original-family source return on the same final Theorem-5.2
output and assignment. -/
theorem assignedSourceMass
    {finalLoss : ℝ}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (output : PureWZ2AnchoredTheorem52Output data.finiteGraph projection)
    (assignment : PureWZ2Node05V4RichHeightAssignmentData
      output.richHeightIndices volumePopular.popular.heightIndices) :
    Nonempty
      (PureWZ2Node05V4RichAssignedSourceMassData
        volumePopular output assignment) :=
  pureWZ2Node05V4Rich_assignedSourceMass
    volumePopular output assignment
      (show separated.graphScale = 256 * rho from rfl)

end PureWZ2Node05V4RichJointFiniteGraphData

end Kakeya.Assouad

end
