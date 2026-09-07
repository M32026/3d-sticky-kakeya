import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSaturatedAllSlabs

/-!
# Paper trapezoids on the saturated all-heavy-slab tail

Each exact heavy-slab block already carries one Theorem-5.2 affine function
and a literal original-source restriction on complete selected heights.  This
module packages those data as the vertical trapezoids used by WZ Lemma 5.4.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- One paper trapezoid attached to the exact complete-height restriction in a
source-heavy standard slab. -/
structure PureWZ2Node05V4RichSaturatedBlockTrapezoid
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss neighborhoodLoss finalLoss eta : ℝ}
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
    {family : PureWZ2Node05V4RichHeavySlabNeighborhoodFamily
      pullback neighborhoodLoss}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {projection : PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (tail : PureWZ2Node05V4RichHeavySlabSaturatedTailFamily
      (eta := eta) family hbridge projection)
    (heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}) where
  scale : ℝ := pureWZ2SourceHorizontalFinalScale rho
  scale_eq : scale = pureWZ2SourceHorizontalFinalScale rho
  scale_le_one : scale ≤ 1
  trapezoid : WZ1VerticalTrapezoid
  height_eq : trapezoid.height = scale
  slope_bound : |trapezoid.slope| ≤ 2
  length_eq : trapezoid.length = Real.sqrt rho
  length_bounds :
    Real.rpow scale (1 / 2 + finalLoss) ≤ trapezoid.length ∧
      trapezoid.length ≤ Real.sqrt scale
  core_eq : trapezoid.core = Set.Icc
    ((heightIndex.1.1 : ℝ) * Real.sqrt rho)
    ((heightIndex.1.1 : ℝ) * Real.sqrt rho + Real.sqrt rho)
  active_height_coverage :
    ∀ z, horizontalSlice
        (tail.complete heightIndex).sourceRestriction.union z ≠ ∅ →
      z ∈ trapezoid.core
  slope_approximation :
    ∀ z ∈ trapezoid.core,
      horizontalSlice
          (tail.complete heightIndex).sourceRestriction.union z ≠ ∅ →
        |current.grain.globalGrains.slope z - trapezoid.affine z| ≤ scale

/-- The exact blockwise trapezoids on every heavy source slab. -/
structure PureWZ2Node05V4RichSaturatedTrapezoidFamily
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss neighborhoodLoss finalLoss eta : ℝ}
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
    {family : PureWZ2Node05V4RichHeavySlabNeighborhoodFamily
      pullback neighborhoodLoss}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {projection : PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (tail : PureWZ2Node05V4RichHeavySlabSaturatedTailFamily
      (eta := eta) family hbridge projection) where
  block : ∀ heightIndex,
    PureWZ2Node05V4RichSaturatedBlockTrapezoid tail heightIndex

namespace PureWZ2Node05V4RichHeavySlabSaturatedTailFamily

/-- Turn every block's exact `L_S` and complete source-height restriction into
the literal WZ Lemma-5.4 trapezoid at scale `1280 * rho`. -/
theorem trapezoidFamily
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss neighborhoodLoss finalLoss eta : ℝ}
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
    {family : PureWZ2Node05V4RichHeavySlabNeighborhoodFamily
      pullback neighborhoodLoss}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {projection : PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (tail : PureWZ2Node05V4RichHeavySlabSaturatedTailFamily
      (eta := eta) family hbridge projection)
    (hscaleOne : pureWZ2SourceHorizontalFinalScale rho ≤ 1)
    (hlengthLower :
      Real.rpow (pureWZ2SourceHorizontalFinalScale rho)
          (1 / 2 + finalLoss) ≤ Real.sqrt rho) :
    Nonempty (PureWZ2Node05V4RichSaturatedTrapezoidFamily tail) := by
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  let block : ∀ heightIndex,
      PureWZ2Node05V4RichSaturatedBlockTrapezoid tail heightIndex := by
    intro heightIndex
    let neighborhood := (family.block heightIndex).neighborhood
    let scheduled := tail.scheduled heightIndex
    let complete := tail.complete heightIndex
    let left := (heightIndex.1.1 : ℝ) * Real.sqrt rho
    let right := left + Real.sqrt rho
    let scale := pureWZ2SourceHorizontalFinalScale rho
    let lineData := scheduled.theorem52.output.lineData
    let trapezoid : WZ1VerticalTrapezoid := {
      left := left
      right := right
      left_lt_right := by
        dsimp only [right]
        linarith [Real.sqrt_pos.mpr hrho]
      slope := lineData.L_S_slope
      intercept := lineData.L_S_intercept
      height := scale
      height_pos := by
        dsimp only [scale, pureWZ2SourceHorizontalFinalScale]
        positivity
    }
    have hscaleEq : 5 * neighborhood.graphScale = scale := by
      dsimp only [neighborhood, scale,
        PureWZ2PreCommonBinGlobalGrainNeighborhoodData.graphScale,
        PureWZ2PreCommonBinGlobalGrainNeighborhoodData.saturatedGraphScale,
        pureWZ2SourceHorizontalFinalScale]
      ring
    exact {
      scale := scale
      scale_eq := rfl
      scale_le_one := hscaleOne
      trapezoid := trapezoid
      height_eq := rfl
      slope_bound := lineData.L_S_slope_bound
      length_eq := by
        dsimp only [trapezoid, WZ1VerticalTrapezoid.length, right, left]
        ring
      length_bounds := by
        constructor
        · simpa [trapezoid, WZ1VerticalTrapezoid.length, right, left, scale]
          using hlengthLower
        · have hrhoScale : rho ≤ scale := by
            dsimp only [scale, pureWZ2SourceHorizontalFinalScale]
            nlinarith
          simpa [trapezoid, WZ1VerticalTrapezoid.length, right, left]
            using Real.sqrt_le_sqrt hrhoScale
      core_eq := by
        rfl
      active_height_coverage := by
        intro z hslice
        rcases Set.nonempty_iff_ne_empty.mpr hslice with
          ⟨point, hpoint, hpointHeight⟩
        have hwindow := complete.sourceRestriction_height_window point hpoint
        rw [(family.block heightIndex).heightIndex_eq] at hwindow
        rw [hpointHeight] at hwindow
        change z ∈ Set.Icc left right
        exact ⟨hwindow.1, hwindow.2.le⟩
      slope_approximation := by
        intro z _hz hslice
        rcases Set.nonempty_iff_ne_empty.mpr hslice with
          ⟨point, hpoint, hpointHeight⟩
        have happ := complete.sourceRestriction_slope_approximation point hpoint
        rw [hpointHeight] at happ
        rw [show trapezoid.affine z = lineData.L_S z by
          rw [lineData.L_S_eq]
          rfl]
        rw [← hscaleEq]
        exact happ
    }
  exact ⟨{ block := block }⟩

end PureWZ2Node05V4RichHeavySlabSaturatedTailFamily

end Kakeya.Assouad

end
