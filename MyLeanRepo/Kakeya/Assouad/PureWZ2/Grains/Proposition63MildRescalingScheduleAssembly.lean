import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingFiberRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingScaleAssembly

/-!
# Assemble the finite mild-rescaling CWA schedule

This is the final combinatorial/Definition 2.12 layer of the mild-rescaling
argument.  The two finite selections have already supplied a common target
family, a literal strict cover at every representative scale, and uniform
target full fibers.  The remaining inputs in this structure are precisely
the per-parent actual-John transports.  They are kept explicit so the
geometric proof cannot be replaced by arbitrary subfamily inheritance.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

attribute [local instance] Classical.propDecidable

namespace Proposition63MildRescalingFiniteParentScheduleData

/-- Abbreviation for the common target-fiber regularization constant. -/
def fiberRegularizationConstant
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    (data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule)
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree) : ENNReal :=
  16 * (sourceSchedule.scaleCount : ENNReal) *
    (Nat.log 2 (2 * (selectedTarget selection).family.card) + 1 : ENNReal) ^
      sourceSchedule.scaleCount

/-- Complete post-selection actual-John input for the finite representative
schedule.  Each fiber certificate refers to the actual source scale witness
at the same coordinate and to the genuine target strict fiber. -/
structure Proposition63MildRescalingFiniteCWAData
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    (data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule)
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree)
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection))
    (bodyConstant targetConstant : ENNReal) where
  target_normalization : ∀ coordinate parent,
    WZ2PaperAssouadUnitRescalingData
      ((fiberRegularizedParents regularized coordinate).family.tube parent)
  source_parent : ∀ coordinate,
    Fin (fiberRegularizedParents regularized coordinate).family.card →
      Fin (sourceSchedule.witness coordinate).scaleData.coarse.card
  target_full_fiber_cwa : ∀ coordinate parent,
    Nonempty (WZ2PaperPureUnitRescaledFullFiberData
      (fine := (fiberRegularizedSubfamily regularized).family)
      (coarse := (fiberRegularizedParents regularized coordinate).family)
      parent bodyConstant)
  constant_budget :
    max (data.fiberRegularizationConstant selection) bodyConstant ≤
      targetConstant

/-- Assemble all actual-John fibers from the source finite schedule.  The
only remaining numerical input is the final error-budget absorption. -/
theorem Proposition63MildRescalingFiniteParentScheduleData.toFiniteCWAData
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    (data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule)
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection))
    (targetConstant : ENNReal)
    (hbudget : max (data.fiberRegularizationConstant selection)
        (data.actualJohnScheduleConstant regularized) ≤ targetConstant) :
    Nonempty (Proposition63MildRescalingFiniteCWAData data selection
      regularized (data.actualJohnScheduleConstant regularized)
        targetConstant) := by
  refine ⟨{
    target_normalization := fun coordinate parent =>
      WZ2PaperAssouadUnitRescalingData.ofTube
        ((data.fiberRegularizedParents regularized coordinate).family.tube
          parent)
        (data.parentCover coordinate).target_rho_pos
    source_parent := data.fiberRegularizedSourceParent regularized
    target_full_fiber_cwa := ?_
    constant_budget := hbudget
  }⟩
  intro coordinate parent
  rcases data.actualJohnFullFiber regularized coordinate parent with ⟨fiber⟩
  refine ⟨{
    normalization := fiber.normalization
    convex_wolff := ?_
  }⟩
  intro convexSet hconvex
  exact (fiber.convex_wolff convexSet hconvex).trans <| by
    gcongr
    exact data.actualJohnConstant_le_schedule regularized coordinate parent

namespace Proposition63MildRescalingFiniteCWAData

/-- Assemble the exact public one-scale witness at one representative
coordinate. -/
noncomputable def scaleData
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    {regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection)}
    {bodyConstant targetConstant : ENNReal}
    (cwa : Proposition63MildRescalingFiniteCWAData
      data selection regularized bodyConstant targetConstant)
    (coordinate : Fin sourceSchedule.scaleCount) :
    WZ2PaperPureScaleCoverData
      (fiberRegularizedSubfamily regularized).family
      (data.targetRho coordinate) targetConstant :=
  ({
    targetCoarse := (fiberRegularizedParents regularized coordinate).family
    target_delta_pos := mul_pos
      (lt_of_lt_of_le zero_lt_one hscale)
      (sourceSchedule.witness coordinate).scaleData.delta_pos
    target_rho_pos := (data.parentCover coordinate).target_rho_pos
    target_cover := fiberRegularizedCover regularized coordinate
    target_full_fiber_uniform := by
      simpa [fiberRegularizationConstant] using
        data.fiberRegularized_fullFiber_uniform regularized coordinate
    target_normalization := cwa.target_normalization coordinate
    source_parent := cwa.source_parent coordinate
    target_full_fiber_cwa := cwa.target_full_fiber_cwa coordinate
    constant_budget := cwa.constant_budget
  } : Proposition63MildRescalingOneScaleData
      ((sourceSchedule.witness coordinate).scaleData)
      (targetRho := data.targetRho coordinate)
      (targetFine := (fiberRegularizedSubfamily regularized).family)
      (targetConstant := targetConstant)
      (coverConstant := data.fiberRegularizationConstant selection)
      (bodyConstant := bodyConstant)).toScaleCoverData

/-- Turn the finite representative target witnesses into the full nearby-
scale predicate.  The exact pullback of a target request is the only scale
conversion: no nearby actual scale is silently identified with the request. -/
theorem toNearbyScales
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hsourceDelta : 0 < sourceDelta}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingFiniteParentScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount
      (fun coordinate => Fin
        (sourceSchedule.witness coordinate).scaleData.coarse.card)
      data.parent data.conflict data.degree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    {regularized : WZ2PaperFiniteParentRegularizationData
      (selectedTargetShading selection targetShading)
      sourceSchedule.scaleCount
      (fun coordinate =>
        Fin (selectedParents selection coordinate).family.card)
      (selectedFiberParent selection)}
    {bodyConstant targetConstant : ENNReal}
    (cwa : Proposition63MildRescalingFiniteCWAData
      data selection regularized bodyConstant targetConstant)
    (htargetDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct
      (fiberRegularizedSubfamily regularized).family)
    (htargetRho : ∀ coordinate,
      scale * (sourceSchedule.witness coordinate).rho ≤
        data.targetRho coordinate)
    (htargetFinite : WZ2PaperFiniteErrorConstant targetConstant)
    (htargetWindow : ∀ target :
      WZ2PaperRequestedScale (scale * sourceDelta),
      ENNReal.ofReal
          (data.targetRho
            (sourceSchedule.representative
              (proposition63MildRescalingSourceRequest
                hsourceDelta hscale target))) <
        targetConstant * ENNReal.ofReal target.1) :
    WZ2PaperPureCWAAtNearbyScales
      (fiberRegularizedSubfamily regularized).family targetConstant := by
  refine ⟨mul_pos (lt_of_lt_of_le zero_lt_one hscale) hsourceDelta,
    htargetFinite, ?_, ?_⟩
  · exact htargetDistinct
  · intro target
    let sourceRequest := proposition63MildRescalingSourceRequest
      hsourceDelta hscale target
    let coordinate := sourceSchedule.representative sourceRequest
    refine ⟨{
      rho := data.targetRho coordinate
      requested_le := ?_
      within_factor := htargetWindow target
      scaleData := cwa.scaleData coordinate
    }⟩
    exact (proposition63MildRescaling_requested_le_targetActual
      hsourceDelta hscale target
      (sourceSchedule.requested_le sourceRequest)).trans
        (htargetRho coordinate)

end Proposition63MildRescalingFiniteCWAData

end Proposition63MildRescalingFiniteParentScheduleData

end Kakeya.Assouad.PureWZ2

end
