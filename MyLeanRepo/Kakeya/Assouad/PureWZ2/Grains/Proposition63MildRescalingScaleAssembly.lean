import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingBodyCWA

/-!
# One-scale actual-John assembly for Proposition 6.3

This module is the structural end of the last mild-rescaling step.  Once the
geometric construction has supplied a literal target partitioning cover,
uniform full fibers, and the bounded-fiber actual-John transport for every
parent, it builds the exact public Definition 2.12 scale witness.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- Complete one-scale data produced by the isotropic parent construction. -/
structure Proposition63MildRescalingOneScaleData
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceConstant targetConstant coverConstant bodyConstant : ENNReal}
    (sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant) where
  targetCoarse : Kakeya.Streamlined.TubeFamily targetRho
  target_delta_pos : 0 < targetDelta
  target_rho_pos : 0 < targetRho
  target_cover :
    WZ2PaperPurePartitioningCover targetFine targetCoarse
  target_full_fiber_uniform :
    WZ2PaperPureFullFibersAreCUniform
      targetFine targetCoarse coverConstant
  target_normalization :
    ∀ targetParent : Fin targetCoarse.card,
      WZ2PaperAssouadUnitRescalingData
        (targetCoarse.tube targetParent)
  source_parent :
    Fin targetCoarse.card → Fin sourceScale.coarse.card
  target_full_fiber_cwa :
    ∀ targetParent : Fin targetCoarse.card,
      Nonempty
        (WZ2PaperPureUnitRescaledFullFiberData
          (fine := targetFine) (coarse := targetCoarse)
          targetParent bodyConstant)
  constant_budget :
    max coverConstant bodyConstant ≤ targetConstant

namespace Proposition63MildRescalingOneScaleData

/-- Assemble the genuine target scale witness. -/
noncomputable def toScaleCoverData
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceConstant targetConstant coverConstant bodyConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    (data : Proposition63MildRescalingOneScaleData
      (targetRho := targetRho) (targetFine := targetFine)
      (targetConstant := targetConstant)
      (coverConstant := coverConstant) (bodyConstant := bodyConstant)
      sourceScale) :
    WZ2PaperPureScaleCoverData targetFine targetRho targetConstant where
  delta_pos := data.target_delta_pos
  rho_pos := data.target_rho_pos
  coarse := data.targetCoarse
  cover := data.target_cover
  full_fiber_uniform first second :=
    (data.target_full_fiber_uniform first second).trans <| by
      gcongr
      exact (le_max_left coverConstant bodyConstant).trans
        data.constant_budget
  rescaledFiber targetParent := by
    rcases data.target_full_fiber_cwa targetParent with ⟨fiber⟩
    refine ⟨{
      normalization := fiber.normalization
      convex_wolff := ?_
    }⟩
    intro convexSet hconvex
    exact (fiber.convex_wolff convexSet hconvex).trans <| by
      gcongr
      exact (le_max_right coverConstant bodyConstant).trans
        data.constant_budget

end Proposition63MildRescalingOneScaleData

end Kakeya.Assouad.PureWZ2

end
