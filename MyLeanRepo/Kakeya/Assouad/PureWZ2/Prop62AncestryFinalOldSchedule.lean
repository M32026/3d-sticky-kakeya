import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryAuxiliaryCoreAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricFiberRequestedRoute

/-!
# Proposition 6.2: old exact-scale witnesses on the final fine family

The augmented-tree cleanup produces one exact old-scale witness on its ambient
core at every schedule coordinate.  Reindex those witnesses through the exact
final-to-ambient equivalence, obtaining the same old schedule on the final
Section 6 fine family.
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

abbrev finalCoreConstant : ENNReal :=
  output.ancestryAuxiliary.outputConstant
    output.binnedAmbientPreliminary

/-- Old exact-scale pure witness reindexed onto the final Section 6 family. -/
noncomputable def finalOldScaleData
    (coordinate : Fin schedule.levelCount) :
    WZ2PaperPureScaleCoverData
      output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family
      (schedule.actualScale coordinate)
      output.finalCoreConstant :=
  (output.ancestryAuxiliary.outputScaleData
    coordinate output.binnedAmbientPreliminary_nonempty).reindex
      output.finalToAuxiliaryCoreEquiv
      output.finalToAuxiliaryCoreEquiv_tube

theorem finalOldScaleData_parent_reindex
    (coordinate : Fin schedule.levelCount)
    (source :
      Fin
        output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family.card) :
    (output.finalOldScaleData coordinate).cover.parent source =
      (output.ancestryAuxiliary.outputScaleData
        coordinate output.binnedAmbientPreliminary_nonempty).cover.parent
          (output.finalToAuxiliaryCoreEquiv source) := by
  exact
    (output.ancestryAuxiliary.outputScaleData
      coordinate output.binnedAmbientPreliminary_nonempty).cover
      |>.reindex_parent_eq
        (output.ancestryAuxiliary.outputScaleData
          coordinate output.binnedAmbientPreliminary_nonempty).rho_pos.le
        output.finalToAuxiliaryCoreEquiv
        output.finalToAuxiliaryCoreEquiv_tube
        source

/-- Reindexing the final old witness preserves its paper line class. -/
theorem finalOldScaleData_coarse_line_class
    (coordinate : Fin schedule.levelCount) :
    WZ1PaperIsLineClass
      (output.finalOldScaleData coordinate).coarse := by
  change
    WZ1PaperIsLineClass
      (output.ancestryAuxiliary.outputScaleData
        coordinate output.binnedAmbientPreliminary_nonempty).coarse
  exact
    (schedule.coarse_line_class coordinate).subfamily
      (output.ancestryAuxiliary.coreCoarse
        coordinate output.binnedAmbientPreliminary).toTubeSubfamily

/--
The exact old-scale covers reindexed onto the final metric fine family retain
the original parent-map nesting.
-/
theorem finalOldScaleData_parent_eq_of_coordinate_le
    (coarseCoordinate fineCoordinate : Fin schedule.levelCount)
    (coordinateLe : coarseCoordinate.1 ≤ fineCoordinate.1)
    (first second :
      Fin
        output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family.card)
    (fineParentEq :
      (output.finalOldScaleData fineCoordinate).cover.parent first =
        (output.finalOldScaleData fineCoordinate).cover.parent second) :
    (output.finalOldScaleData coarseCoordinate).cover.parent first =
      (output.finalOldScaleData coarseCoordinate).cover.parent second := by
  have fineCoreParentEq :
      (output.ancestryAuxiliary.outputScaleData
          fineCoordinate output.binnedAmbientPreliminary_nonempty).cover.parent
          (output.finalToAuxiliaryCoreEquiv first) =
        (output.ancestryAuxiliary.outputScaleData
          fineCoordinate output.binnedAmbientPreliminary_nonempty).cover.parent
          (output.finalToAuxiliaryCoreEquiv second) := by
    rw [
      ← output.finalOldScaleData_parent_reindex fineCoordinate first,
      ← output.finalOldScaleData_parent_reindex fineCoordinate second
    ]
    exact fineParentEq
  have fineAmbientParentEq :
      (schedule.scaleData fineCoordinate).cover.parent
          ((output.ancestryAuxiliary.coreFine
            output.binnedAmbientPreliminary).embedding
            (output.finalToAuxiliaryCoreEquiv first)) =
        (schedule.scaleData fineCoordinate).cover.parent
          ((output.ancestryAuxiliary.coreFine
            output.binnedAmbientPreliminary).embedding
            (output.finalToAuxiliaryCoreEquiv second)) := by
    have embedded :=
      congrArg
        (output.ancestryAuxiliary.coreCoarse
          fineCoordinate output.binnedAmbientPreliminary).embedding
        fineCoreParentEq
    simpa only [
      output.ancestryAuxiliary.outputScale_parent_eq_hitParent,
      output.ancestryAuxiliary.coreCoarse_hitParent_ambient
    ] using embedded
  have coarseAmbientParentEq :
      (schedule.scaleData coarseCoordinate).cover.parent
          ((output.ancestryAuxiliary.coreFine
            output.binnedAmbientPreliminary).embedding
            (output.finalToAuxiliaryCoreEquiv first)) =
        (schedule.scaleData coarseCoordinate).cover.parent
          ((output.ancestryAuxiliary.coreFine
            output.binnedAmbientPreliminary).embedding
            (output.finalToAuxiliaryCoreEquiv second)) :=
    schedule.parent_eq_of_coordinate_le
      coarseCoordinate fineCoordinate coordinateLe _ _ fineAmbientParentEq
  have coarseCoreParentEq :
      (output.ancestryAuxiliary.outputScaleData
          coarseCoordinate output.binnedAmbientPreliminary_nonempty).cover.parent
          (output.finalToAuxiliaryCoreEquiv first) =
        (output.ancestryAuxiliary.outputScaleData
          coarseCoordinate output.binnedAmbientPreliminary_nonempty).cover.parent
          (output.finalToAuxiliaryCoreEquiv second) := by
    apply
      (output.ancestryAuxiliary.coreCoarse
        coarseCoordinate output.binnedAmbientPreliminary).embedding.injective
    simp only [
      output.ancestryAuxiliary.coreCoarse_hitParent_ambient,
      output.ancestryAuxiliary.outputScale_parent_eq_hitParent
    ]
    exact coarseAmbientParentEq
  rw [
    output.finalOldScaleData_parent_reindex coarseCoordinate first,
    output.finalOldScaleData_parent_reindex coarseCoordinate second
  ]
  exact coarseCoreParentEq

/--
The synchronized old line-cover provenance survives both the one-pass core
restriction and the exact final-family reindexing.
-/
theorem finalOldScaleData_parent_covers
    (coordinate : Fin schedule.levelCount)
    (source :
      Fin
        output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family.card) :
    WZ1PaperTubeCovers
      (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family.tube
        source)
      ((output.finalOldScaleData coordinate).coarse.tube
        ((output.finalOldScaleData coordinate).cover.parent source)) := by
  rw [output.finalToAuxiliaryCoreEquiv_tube,
    output.finalOldScaleData_parent_reindex]
  let coreSource :=
    output.finalToAuxiliaryCoreEquiv source
  change
    WZ1PaperTubeCovers
      ((output.ancestryAuxiliary.coreFine
        output.binnedAmbientPreliminary).family.tube coreSource)
      ((output.ancestryAuxiliary.coreCoarse
        coordinate output.binnedAmbientPreliminary).family.tube
          ((output.ancestryAuxiliary.outputScaleData
            coordinate output.binnedAmbientPreliminary_nonempty).cover.parent
              coreSource))
  rw [
    output.ancestryAuxiliary.outputScale_parent_eq_hitParent
      coordinate output.binnedAmbientPreliminary_nonempty coreSource,
    (output.ancestryAuxiliary.coreFine
      output.binnedAmbientPreliminary).tube_eq,
    (output.ancestryAuxiliary.coreCoarse
      coordinate output.binnedAmbientPreliminary).tube_eq,
    output.ancestryAuxiliary.coreCoarse_hitParent_ambient
      coordinate output.binnedAmbientPreliminary coreSource
  ]
  exact
    schedule.parent_covers coordinate
      ((output.ancestryAuxiliary.coreFine
        output.binnedAmbientPreliminary).embedding coreSource)

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end
