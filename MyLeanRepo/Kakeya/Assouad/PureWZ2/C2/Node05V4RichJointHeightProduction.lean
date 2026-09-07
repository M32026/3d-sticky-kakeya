import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightFiniteGraph

/-!
# Same-witness joint-height P3 production package

This package freezes the complete runtime chain from the source-volume
popular band through the integrated common bin, parent selections, final
finite graph, Theorem 5.2, height assignment, and original-family source-mass
return.  No witness is reselected after Theorem 5.2.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

structure PureWZ2Node05V4RichJointPreparedData
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
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback})
    (B₀ threshold : ENNReal)
    (hbridge : PureWZ2PaperADBridgeStatement) where
  volumePopular :
    PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex
  outerEnvelope :
    PureWZ2Node05V4RichSourceVolumePopularEnvelopeData volumePopular
  block : volumePopular.JointHeightCommonBinData B₀ threshold
  oneParent : block.JointOneParentPerYData
  separated : PureWZ2Node05V4RichJointSeparatedParentData oneParent
  graphScale_eq : separated.graphScale = 256 * rho
  graphScale_le_one : separated.graphScale ≤ 1
  finite :
    PureWZ2Node05V4RichJointFiniteGraphData
      (eta := eta) separated hbridge graphScale_le_one

namespace PureWZ2Node05V4RichTwoScaleCellPullbackData

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
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)

theorem jointHeightPrepared
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback})
    (B₀ threshold : ENNReal)
    (hB₀ :
      264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget :
      ∀ volumePopular :
        PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex,
        2 * B₀ * threshold ≤
          pureWZ2SourceCommonBinPopularThreshold
            volumePopular.jointSourceSet (Real.sqrt rho))
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * Real.sqrt rho ≤ 16 * Real.sqrt rho)
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
    Nonempty (PureWZ2Node05V4RichJointPreparedData
      (eta := eta) pullback heightIndex B₀ threshold hbridge) := by
  rcases pullback.sourceVolumePopularHeightData heightIndex with
    ⟨volumePopular⟩
  rcases volumePopular.wholeCellEnvelope with ⟨outerEnvelope⟩
  rcases volumePopular.jointHeightCommonBin B₀ threshold hB₀
      (hthresholdBudget volumePopular) with ⟨block⟩
  rcases block.jointOneParentPerY with ⟨oneParent⟩
  rcases volumePopular.jointSeparatedParents oneParent with ⟨separated⟩
  have hgraphOne' : separated.graphScale ≤ 1 := by
    simpa only [PureWZ2Node05V4RichJointSeparatedParentData.graphScale] using
      hgraphOne
  have hheightAbsorb' :
      separated.graphScale + 2 * Real.sqrt rho ≤ 16 * Real.sqrt rho := by
    simpa only [PureWZ2Node05V4RichJointSeparatedParentData.graphScale] using
      hheightAbsorb
  rcases separated.finalFiniteGraph hbridge hgraphOne' hheightAbsorb'
      hsigma hsigmaOne heta hetaSigma hcertificateOne hsourcePower
      hlocalPower hPlanarSmall hrootSmall20 habsorb with ⟨finite⟩
  exact ⟨{
    volumePopular := volumePopular
    outerEnvelope := outerEnvelope
    block := block
    oneParent := oneParent
    separated := separated
    graphScale_eq := rfl
    graphScale_le_one := hgraphOne'
    finite := finite
  }⟩

end PureWZ2Node05V4RichTwoScaleCellPullbackData

structure PureWZ2Node05V4RichJointTheorem52Data
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta finalLoss : ℝ}
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
    {B₀ threshold : ENNReal}
    {hbridge : PureWZ2PaperADBridgeStatement}
    (prepared : PureWZ2Node05V4RichJointPreparedData
      (eta := eta) pullback heightIndex B₀ threshold hbridge)
    (projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss) where
  output :
    PureWZ2AnchoredTheorem52Output prepared.finite.finiteGraph projection
  assignment : PureWZ2Node05V4RichHeightAssignmentData
    output.richHeightIndices prepared.volumePopular.popular.heightIndices
  assignment_exact : assignment.assigned = id
  sourceMass : PureWZ2Node05V4RichAssignedSourceMassData
    prepared.volumePopular output assignment

namespace PureWZ2Node05V4RichJointPreparedData

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
    {B₀ threshold : ENNReal}
    {hbridge : PureWZ2PaperADBridgeStatement}
    (prepared : PureWZ2Node05V4RichJointPreparedData
      (eta := eta) pullback heightIndex B₀ threshold hbridge)

theorem runTheorem52
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
        Real.rpow prepared.separated.graphScale (-constantLoss))
    (hvolume : ENNReal.ofReal
        (Real.rpow prepared.separated.graphScale
          (1 + sigma / 2 + volumeLoss)) ≤
      volume prepared.separated.graphShading.union)
    (hextraPower :
      (prepared.finite.finiteGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow prepared.separated.graphScale (-extraLoss))
    (hedgeAbsorb :
      Real.rpow (wz1Lemma23Theorem22Scale prepared.separated.graphScale)
          (projection.theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow prepared.separated.graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss))
    (hKatzTao : (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale prepared.separated.graphScale)
        (-projection.theoremEta))
    (hCbound :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        10 * Kakeya.realRpowENN rhoRequested.1 (-eta))
    (hsourceCost :
      Kakeya.realRpowENN rhoRequested.1 (-eta) ≤
        Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale prepared.separated.graphScale)
          (-sourceCostLoss))
    (hsourceCostLoss : 0 ≤ sourceCostLoss)
    (hsourceCostCeiling :
      sourceCostLoss ≤ projection.sourceCostLossCeiling)
    (hdeltaSmall :
      wz1Lemma23Theorem22Scale prepared.separated.graphScale ≤
        projection.reductionDelta₀)
    (hconstantSmall :
      (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale prepared.separated.graphScale)
          (-(projection.projectionEta * (sigma - finalLoss / 2) -
            (10 * projection.theoremEta + sourceCostLoss)) / 2)) :
    Nonempty (PureWZ2Node05V4RichJointTheorem52Data
      prepared projection) := by
  rcases prepared.finite.theorem52 projection hsigma hsigmaOne
      houtput houtputOne houtputSigma hCOne
      constantLoss volumeLoss extraLoss sourceCostLoss hCpower hvolume
      hextraPower hedgeAbsorb hKatzTao hCbound hsourceCost hsourceCostLoss
      hsourceCostCeiling hdeltaSmall hconstantSmall with ⟨output⟩
  rcases prepared.finite.exactHeightAssignment output with
    ⟨assignment, hassignment⟩
  rcases prepared.finite.assignedSourceMass output assignment with
    ⟨sourceMass⟩
  exact ⟨{
    output := output
    assignment := assignment
    assignment_exact := hassignment
    sourceMass := sourceMass
  }⟩

end PureWZ2Node05V4RichJointPreparedData

end Kakeya.Assouad

end
