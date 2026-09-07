import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryFinalMetricQuantitative

/-!
# Proposition 6.2: the metric-fiber `D_-` band after the final core

The parent bin is chosen before the one augmented-tree cleanup.  This module
shows that every surviving metric parent comes from that same bin, then
transfers the pre-core factor-two upper bound and the tree-density lower bound
through the exact final fiber image.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62AncestryMetricPreliminaryOutput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow}
    {scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {coordinateCount : ℕ}
    {Color : Fin coordinateCount → Type*}
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    {color : ∀ coordinate, Fin fine.card → Color coordinate}
    {weight : Fin fine.card → ENNReal}
    {preliminary :
      PureWZ2Prop62AncestryPreliminarySelectionData
        schedule scheduled rho width packetCoordinate
        Color color weight}
    {M : ℝ}
    (output :
      PureWZ2Prop62AncestryMetricPreliminaryOutput
        schedule scheduled width packetCoordinate
        Color color weight preliminary M)

/--
Every metric parent hit by the final core is one of the parents selected by
the pre-core `D_-` bin.
-/
theorem finalMetricParent_mem_cardinalityBin
    (parent :
      Fin output.finalMetricRestriction.coarseSelected.family.card) :
    output.finalMetricRestriction.coarseSelected.embedding parent ∈
      output.metricFiberCardinalityBin.selectedParents := by
  let restriction := output.finalMetricRestriction
  rcases restriction.section6Cover.parent_hit parent with
    ⟨source, sourceCovered⟩
  have sourceCore :
      restriction.fineSelected.embedding source ∈
        output.ancestryAuxiliaryCore.pullback.pulledBack := by
    exact
      (Finset.ext_iff.mp restriction.fine_image_univ
        (restriction.fineSelected.embedding source)).mp <|
        Finset.mem_image.mpr
          ⟨source, Finset.mem_univ source, rfl⟩
  have ambientCore :
      output.metric.mesh.complete.selectedFine.embedding
          (restriction.fineSelected.embedding source) ∈
        output.ancestryAuxiliaryCore.ambientCore := by
    exact
      (Finset.ext_iff.mp
        output.ancestryAuxiliaryCore.pullback.image_eq
        (output.metric.mesh.complete.selectedFine.embedding
          (restriction.fineSelected.embedding source))).mp <|
        Finset.mem_image.mpr
          ⟨restriction.fineSelected.embedding source, sourceCore, rfl⟩
  have ambientBinned :
      output.metric.mesh.complete.selectedFine.embedding
          (restriction.fineSelected.embedding source) ∈
        output.binnedAmbientPreliminary :=
    output.ancestryAuxiliaryCore.ambientCore_subset_preliminary
      ambientCore
  change
    output.metric.mesh.complete.selectedFine.embedding
          (restriction.fineSelected.embedding source) ∈
      output.metricFiberCardinalityBin.ambientPreliminary
    at ambientBinned
  rcases Finset.mem_image.mp ambientBinned with
    ⟨binnedSource, binnedMem, sourceEq⟩
  have binnedSourceEq :
      binnedSource = restriction.fineSelected.embedding source :=
    output.metric.mesh.complete.selectedFine.embedding.injective
      sourceEq
  have binnedParentMem :
      output.metricParentOf binnedSource ∈
        output.metricFiberCardinalityBin.selectedParents :=
    (Finset.mem_filter.mp binnedMem).2
  have ambientCovered :
      WZ1PaperTubeCovers
        (output.metric.selectedFine.tube
          (restriction.fineSelected.embedding source))
        (output.metric.metricParents.tube
          (restriction.coarseSelected.embedding parent)) := by
    simpa only [
      restriction.fineSelected.tube_eq,
      restriction.coarseSelected.tube_eq
    ] using sourceCovered
  have parentEq :
      output.metricParentOf
          (restriction.fineSelected.embedding source) =
        restriction.coarseSelected.embedding parent := by
    exact
      pureWZ2_prop62_metricParent_unique
        output.metric.metricInput.coarse_essentially_distinct
        (restriction.fineSelected.embedding source)
        (output.metricParentOf
          (restriction.fineSelected.embedding source))
        (restriction.coarseSelected.embedding parent)
        (output.metric.metricInput.packetParent_covers
          (restriction.fineSelected.embedding source))
        ambientCovered
  rw [binnedSourceEq, parentEq] at binnedParentMem
  exact binnedParentMem

theorem finalMetricFiber_card_eq_coreIntersection
    (parent :
      Fin output.finalMetricRestriction.coarseSelected.family.card) :
    (wz2PaperFullFiberIndices
        output.finalMetricRestriction.fineSelected.family
        output.finalMetricRestriction.coarseSelected.family
        parent).card =
      (output.ancestryAuxiliaryCore.pullback.pulledBack ∩
        wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents
          (output.finalMetricRestriction.coarseSelected.embedding parent)
        ).card := by
  rw [← output.finalMetricRestriction.fiber_image_eq parent]
  exact
    (Finset.card_image_of_injective _
      output.finalMetricRestriction.fineSelected.embedding.injective).symm

/-- The final core cannot increase the pre-core factor-two upper bound. -/
theorem finalMetricFiber_card_lt_two_fiberFloor
    (parent :
      Fin output.finalMetricRestriction.coarseSelected.family.card) :
    (wz2PaperFullFiberIndices
        output.finalMetricRestriction.fineSelected.family
        output.finalMetricRestriction.coarseSelected.family
        parent).card <
      2 * output.metricFiberCardinalityBin.fiberFloor := by
  have ambientBand :=
    output.preCoreMetricFiber_card_band
      (output.finalMetricRestriction.coarseSelected.embedding parent)
      (output.finalMetricParent_mem_cardinalityBin parent)
  rw [output.finalMetricFiber_card_eq_coreIntersection]
  exact
    (Finset.card_le_card Finset.inter_subset_right).trans_lt
      ambientBand.2

/--
The pre-core floor is at most `densityLoss` times every final metric-fiber
cardinality.  This is the paper inequality
`D_- ≤ θ⁻¹ #U₁[G_ω]`.
-/
theorem fiberFloor_le_ancestryDensityLoss_finalMetricFiber
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (parentCovers :
      ∀ coordinate source,
        WZ1PaperTubeCovers
          (fine.tube source)
          ((schedule.scaleData coordinate).coarse.tube
            ((schedule.scaleData coordinate).cover.parent source)))
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (parent :
      Fin output.finalMetricRestriction.coarseSelected.family.card) :
    (output.metricFiberCardinalityBin.fiberFloor : ENNReal) ≤
      output.ancestryDensityLoss *
        ((wz2PaperFullFiberIndices
          output.finalMetricRestriction.fineSelected.family
          output.finalMetricRestriction.coarseSelected.family
          parent).card : ENNReal) := by
  let ambientParent :=
    output.finalMetricRestriction.coarseSelected.embedding parent
  have ambientBand :=
    output.preCoreMetricFiber_card_band
      ambientParent
      (output.finalMetricParent_mem_cardinalityBin parent)
  have ambientLower :
      (output.metricFiberCardinalityBin.fiberFloor : ENNReal) ≤
        ((wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents ambientParent).card : ENNReal) := by
    exact_mod_cast ambientBand.1
  have coreLower :=
    output.metricFiber_le_ancestryDensityLoss_core
      rhoPos widthPos packetScaleLeRho sixWidthLe parentCovers
      allAncestryCoordinatesUpper ambientParent
      (output.finalAmbientCoreFiber_nonempty parent)
  rw [← output.finalMetricFiber_card_eq_coreIntersection parent]
    at coreLower
  exact ambientLower.trans coreLower

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end
