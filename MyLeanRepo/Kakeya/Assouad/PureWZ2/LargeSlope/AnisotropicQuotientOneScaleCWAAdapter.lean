import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ActualJohnPacketCWA

/-!
# Actual-John adapter for a quotient target parent

One public target fiber may merge several source Definition 2.12 fibers.  We
partition its canonical target John-body family by the source parent label,
prove CWA on each packet, and sum the estimates.  Because both contained
counts and body-family cardinalities add over the partition, this merge costs
no factor equal to the number of source parents.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Exact one-scale data for merging source actual-John fibers into target
quotient fibers. -/
structure PureWZ2AnisotropicQuotientOneScaleCWAAdapterData
    {sourceDelta targetDelta sourceRho targetRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceConstant targetConstant coverConstant bodyConstant : ENNReal}
    (sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant) where
  targetCoarse : Kakeya.Streamlined.TubeFamily targetRho
  target_delta_pos : 0 < targetDelta
  target_rho_pos : 0 < targetRho
  targetCover :
    WZ2PaperPurePartitioningCover targetFine targetCoarse
  target_full_fiber_uniform :
    WZ2PaperPureFullFibersAreCUniform
      targetFine targetCoarse coverConstant
  sourceOf : Fin targetFine.card → Fin sourceFine.card
  targetNormalization :
    ∀ targetParent : Fin targetCoarse.card,
      WZ2PaperAssouadUnitRescalingData
        (targetCoarse.tube targetParent)
  packetCWA :
    ∀ (targetParent : Fin targetCoarse.card)
      (sourceParent : Fin sourceScale.coarse.card),
      WZ2PaperBodyConvexWolffBound
        (pureWZ2BodyParentFiber
          (wz2PaperPureUnitRescaledFullFiberBodyFamily
            (fine := targetFine) (coarse := targetCoarse)
            targetParent (targetNormalization targetParent))
          (fun targetBody =>
            sourceScale.cover.parent
              (sourceOf
                ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
                  targetBody).1))
          sourceParent)
        bodyConstant
  source_parent_count_pos : 0 < sourceScale.coarse.card
  constant_budget :
    max coverConstant bodyConstant ≤ targetConstant

namespace PureWZ2AnisotropicQuotientOneScaleCWAAdapterData

/-- CWA on one complete target quotient fiber follows by summing its source
actual-parent packets. -/
theorem rescaledFiber
    {sourceDelta targetDelta sourceRho targetRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceConstant targetConstant coverConstant bodyConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    (data : PureWZ2AnisotropicQuotientOneScaleCWAAdapterData
      (targetRho := targetRho) (targetFine := targetFine)
      (targetConstant := targetConstant)
      (coverConstant := coverConstant) (bodyConstant := bodyConstant)
      sourceScale)
    (targetParent : Fin data.targetCoarse.card) :
    Nonempty
      (WZ2PaperPureUnitRescaledFullFiberData
        (fine := targetFine) (coarse := data.targetCoarse)
        targetParent targetConstant) := by
  let normalization := data.targetNormalization targetParent
  let targetBodies :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := targetFine) (coarse := data.targetCoarse)
      targetParent normalization
  let actualParent : Fin targetBodies.card →
      Fin sourceScale.coarse.card := fun targetBody =>
    sourceScale.cover.parent
      (data.sourceOf
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) targetBody).1)
  have hbody : WZ2PaperBodyConvexWolffBound
      targetBodies bodyConstant :=
    pureWZ2_bodyCWA_of_parent_fibers
      data.source_parent_count_pos actualParent
      (data.packetCWA targetParent)
  refine ⟨{ normalization := normalization, convex_wolff := ?_ }⟩
  intro convexSet hconvex
  exact (hbody convexSet hconvex).trans <| by
    gcongr
    exact (le_max_right coverConstant bodyConstant).trans
      data.constant_budget

/-- Assemble the target public scale after the packetwise actual-John proofs
have been supplied. -/
noncomputable def toScaleCoverData
    {sourceDelta targetDelta sourceRho targetRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceConstant targetConstant coverConstant bodyConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    (data : PureWZ2AnisotropicQuotientOneScaleCWAAdapterData
      (targetRho := targetRho) (targetFine := targetFine)
      (targetConstant := targetConstant)
      (coverConstant := coverConstant) (bodyConstant := bodyConstant)
      sourceScale) :
    WZ2PaperPureScaleCoverData
      targetFine targetRho targetConstant where
  delta_pos := data.target_delta_pos
  rho_pos := data.target_rho_pos
  coarse := data.targetCoarse
  cover := data.targetCover
  full_fiber_uniform first second :=
    (data.target_full_fiber_uniform first second).trans <| by
      gcongr
      exact (le_max_left coverConstant bodyConstant).trans
        data.constant_budget
  rescaledFiber := data.rescaledFiber

end PureWZ2AnisotropicQuotientOneScaleCWAAdapterData

end Kakeya.Assouad

end
