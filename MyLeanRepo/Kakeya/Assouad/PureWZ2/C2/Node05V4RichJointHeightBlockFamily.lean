import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightSlopeReturn

/-!
# Joint-height block family on every heavy slab

This packages the already constructed same-witness Theorem-5.2 output,
whole-cell lift, and trapezoid for every source-heavy slab.  It does not rerun
or independently select any block witness.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2Node05V4RichJointBlockFamily
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
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (B₀ threshold : ENNReal)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss) where
  prepared : ∀ heightIndex :
      {heightIndex // heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback},
    PureWZ2Node05V4RichJointPreparedData
      (eta := eta) pullback heightIndex B₀ threshold hbridge
  theorem52 : ∀ heightIndex,
    PureWZ2Node05V4RichJointTheorem52Data
      (prepared heightIndex) projection
  lift : ∀ heightIndex,
    PureWZ2Node05V4RichJointWholeCellLiftData (theorem52 heightIndex)
  trapezoid : ∀ heightIndex,
    PureWZ2Node05V4RichJointBlockTrapezoid (lift heightIndex)

namespace PureWZ2Node05V4RichTwoScaleCellPullbackData

variable
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
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    {B₀ threshold : ENNReal}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}

theorem jointBlockFamily
    (prepared : ∀ heightIndex :
      {heightIndex // heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback},
      PureWZ2Node05V4RichJointPreparedData
        (eta := eta) pullback heightIndex B₀ threshold hbridge)
    (theorem52 : ∀ heightIndex,
      PureWZ2Node05V4RichJointTheorem52Data
        (prepared heightIndex) projection)
    (hscaleOne :
      ∀ heightIndex,
        5 * (prepared heightIndex).separated.graphScale ≤ 1)
    (hlengthLower :
      ∀ heightIndex,
        Real.rpow (5 * (prepared heightIndex).separated.graphScale)
            (1 / 2 + finalLoss) ≤ Real.sqrt rho + 4 * delta) :
    Nonempty (PureWZ2Node05V4RichJointBlockFamily
      (eta := eta) pullback B₀ threshold hbridge projection) := by
  let lift : ∀ heightIndex,
      PureWZ2Node05V4RichJointWholeCellLiftData
        (theorem52 heightIndex) := fun heightIndex =>
    Classical.choice (theorem52 heightIndex).wholeCellLift
  let trapezoid : ∀ heightIndex,
      PureWZ2Node05V4RichJointBlockTrapezoid
        (lift heightIndex) := fun heightIndex =>
    Classical.choice ((lift heightIndex).blockTrapezoid
      (hscaleOne heightIndex) (hlengthLower heightIndex))
  exact ⟨{
    prepared := prepared
    theorem52 := theorem52
    lift := lift
    trapezoid := trapezoid
  }⟩

end PureWZ2Node05V4RichTwoScaleCellPullbackData

end Kakeya.Assouad

end
