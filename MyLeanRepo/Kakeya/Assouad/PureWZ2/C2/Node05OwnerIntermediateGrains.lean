import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.StickyRefinementData
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ExactNode4ReentryAdapter

/-!
# Owner intermediate grains from an explicit re-entry schedule

This is a Node-5-private receipt.  It applies the explicitly supplied
same-extremizer schedule to the actual cropped coarse output of the first
sticky call; it does not add a conclusion to the frozen Node 4 interface.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Restore grains on the actual first coarse family and shading. -/
theorem pureWZ2Node05Owner_intermediateGrains
    {delta sigma outputLoss middleLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (first : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (schedule : PureWZ2Node05SameExtremizerSchedule sigma middleLoss)
    (outputLoss_le_input : outputLoss ≤ schedule.inputLoss)
    (rho_le_delta₀ : rho.1 ≤ schedule.delta₀) :
    Nonempty
      (PureWZ2GrainRefinementData
        first.croppedCoarseShading sigma middleLoss) :=
  schedule.restore rho.1 first.coarse_extremal.delta_pos rho_le_delta₀
    first.coarse first.croppedCoarseShading
    first.cover.coarse_line_class
    (first.coarse_extremal.mono_loss outputLoss_le_input)

end Kakeya.Assouad

end
