import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryFinalOldSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62SaturatedScaleRestriction

/-!
# Proposition 6.2: final metric fibers at old descendant scales

For an old coordinate at or below the selected `s`-packet level, equality of
old parents implies equality of `s`-parents.  Hence it implies equality of the
metric parent assigned by the mesh.  Every final genuine metric fiber is
therefore saturated for the final old-scale parent map and inherits that
exact-scale pure witness without additional loss.
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

theorem finalOldParentEq_implies_packetParentEq
    (coordinate : Fin schedule.levelCount)
    (packetLeCoordinate : packetCoordinate.1 ≤ coordinate.1)
    (first second :
      Fin output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family.card)
    (parentEq :
      (output.finalOldScaleData coordinate).cover.parent first =
        (output.finalOldScaleData coordinate).cover.parent second) :
    output.metric.metricInput.packetParent
          (output.metric.mesh.restrictedOldData.cover.parent
            (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding first)) =
      output.metric.metricInput.packetParent
        (output.metric.mesh.restrictedOldData.cover.parent
          (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding second)) := by
  have ambientParentEq :
      (output.ancestryAuxiliary.outputScaleData
        coordinate output.binnedAmbientPreliminary_nonempty).cover.parent
          (output.finalToAuxiliaryCoreEquiv first) =
        (output.ancestryAuxiliary.outputScaleData
          coordinate output.binnedAmbientPreliminary_nonempty).cover.parent
            (output.finalToAuxiliaryCoreEquiv second) := by
    rw [← output.finalOldScaleData_parent_reindex,
      ← output.finalOldScaleData_parent_reindex]
    exact parentEq
  have coreParentEq :
      (schedule.scaleData coordinate).cover.parent
          ((output.ancestryAuxiliary.coreFine
            output.binnedAmbientPreliminary).embedding
              (output.finalToAuxiliaryCoreEquiv first)) =
        (schedule.scaleData coordinate).cover.parent
          ((output.ancestryAuxiliary.coreFine
            output.binnedAmbientPreliminary).embedding
              (output.finalToAuxiliaryCoreEquiv second)) := by
    rw [
      output.ancestryAuxiliary.outputScale_parent_eq_hitParent
        coordinate output.binnedAmbientPreliminary_nonempty,
      output.ancestryAuxiliary.outputScale_parent_eq_hitParent
        coordinate output.binnedAmbientPreliminary_nonempty
    ] at ambientParentEq
    have embeddedEq :=
      congrArg
        (output.ancestryAuxiliary.coreCoarse
          coordinate output.binnedAmbientPreliminary).embedding
        ambientParentEq
    rw [
      output.ancestryAuxiliary.coreCoarse_hitParent_ambient
        coordinate output.binnedAmbientPreliminary
          (output.finalToAuxiliaryCoreEquiv first),
      output.ancestryAuxiliary.coreCoarse_hitParent_ambient
        coordinate output.binnedAmbientPreliminary
          (output.finalToAuxiliaryCoreEquiv second)
    ] at embeddedEq
    exact embeddedEq
  have packetParentAmbientEq :
      (schedule.scaleData packetCoordinate).cover.parent
          ((output.ancestryAuxiliary.coreFine
            output.binnedAmbientPreliminary).embedding
              (output.finalToAuxiliaryCoreEquiv first)) =
        (schedule.scaleData packetCoordinate).cover.parent
          ((output.ancestryAuxiliary.coreFine
            output.binnedAmbientPreliminary).embedding
              (output.finalToAuxiliaryCoreEquiv second)) :=
    schedule.parent_eq_of_coordinate_le
      packetCoordinate coordinate packetLeCoordinate _ _ coreParentEq
  have packetCellEq :
      schedule.packetLineCell packetCoordinate width
          (output.metric.mesh.complete.selectedFine.embedding
            (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding first)) =
        schedule.packetLineCell packetCoordinate width
          (output.metric.mesh.complete.selectedFine.embedding
            (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding second)) := by
    unfold PureWZ2Prop62PureSchedule.packetLineCell
    rw [← output.finalToAuxiliaryCoreEquiv_embedding,
      ← output.finalToAuxiliaryCoreEquiv_embedding,
      packetParentAmbientEq]
  exact
    (output.metricParent_eq_iff_packetLineCell_embedding_eq
      (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding first)
      (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding second)).mpr
      packetCellEq

theorem finalMetricFiber_saturated_for_descendant
    (coordinate : Fin schedule.levelCount)
    (packetLeCoordinate : packetCoordinate.1 ≤ coordinate.1)
    (parent :
      Fin output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.family.card) :
    let scaleData := output.finalOldScaleData coordinate
    ∀ first second,
      scaleData.cover.parent first = scaleData.cover.parent second →
        (first ∈
            wz2PaperFullFiberIndices
              output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family
              output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.family parent ↔
          second ∈
            wz2PaperFullFiberIndices
              output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family
              output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.family parent) := by
  dsimp only
  intro first second oldParentEq
  have metricParentEq :=
    output.finalOldParentEq_implies_packetParentEq
      coordinate packetLeCoordinate first second oldParentEq
  rw [mem_wz2PaperFullFiberIndices_iff,
    mem_wz2PaperFullFiberIndices_iff]
  have firstAmbient :
      WZ1PaperTubeCovers
          (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family.tube
            first)
          (output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.family.tube
            parent) ↔
        output.metric.metricInput.packetParent
            (output.metric.mesh.restrictedOldData.cover.parent
              (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
                first)) =
          output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.embedding
            parent := by
    constructor
    · intro covered
      have ambientCovered :
          WZ1PaperTubeCovers
            (output.metric.selectedFine.tube
              (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
                first))
            (output.metric.metricParents.tube
              (output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.embedding
                parent)) := by
        simpa only [
          output.ancestryAuxiliaryCore.metricRestriction.fineSelected.tube_eq,
          output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.tube_eq
        ] using covered
      exact
        pureWZ2_prop62_metricParent_unique
          output.metric.metricInput.coarse_essentially_distinct
          (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
            first)
          (output.metric.metricInput.packetParent
            (output.metric.mesh.restrictedOldData.cover.parent
              (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
                first)))
          (output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.embedding
            parent)
          (output.metric.metricInput.packetParent_covers
            (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
              first))
          ambientCovered
    · intro parentEq
      have covered :=
        output.metric.metricInput.packetParent_covers
          (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
            first)
      rw [parentEq] at covered
      simpa only [
        output.ancestryAuxiliaryCore.metricRestriction.fineSelected.tube_eq,
        output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.tube_eq
      ] using covered
  have secondAmbient :
      WZ1PaperTubeCovers
          (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family.tube
            second)
          (output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.family.tube
            parent) ↔
        output.metric.metricInput.packetParent
            (output.metric.mesh.restrictedOldData.cover.parent
              (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
                second)) =
          output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.embedding
            parent := by
    constructor
    · intro covered
      have ambientCovered :
          WZ1PaperTubeCovers
            (output.metric.selectedFine.tube
              (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
                second))
            (output.metric.metricParents.tube
              (output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.embedding
                parent)) := by
        simpa only [
          output.ancestryAuxiliaryCore.metricRestriction.fineSelected.tube_eq,
          output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.tube_eq
        ] using covered
      exact
        pureWZ2_prop62_metricParent_unique
          output.metric.metricInput.coarse_essentially_distinct
          (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
            second)
          (output.metric.metricInput.packetParent
            (output.metric.mesh.restrictedOldData.cover.parent
              (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
                second)))
          (output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.embedding
            parent)
          (output.metric.metricInput.packetParent_covers
            (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
              second))
          ambientCovered
    · intro parentEq
      have covered :=
        output.metric.metricInput.packetParent_covers
          (output.ancestryAuxiliaryCore.metricRestriction.fineSelected.embedding
            second)
      rw [parentEq] at covered
      simpa only [
        output.ancestryAuxiliaryCore.metricRestriction.fineSelected.tube_eq,
        output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.tube_eq
      ] using covered
  rw [firstAmbient, secondAmbient, metricParentEq]

noncomputable def finalMetricFiberDescendantScaleData
    (coordinate : Fin schedule.levelCount)
    (packetLeCoordinate : packetCoordinate.1 ≤ coordinate.1)
    (parent :
      Fin output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.family.card) :
    WZ2PaperPureScaleCoverData
      (output.ancestryAuxiliaryCore.metricRestriction.metricFiberSource parent).family
      (schedule.actualScale coordinate)
      output.finalCoreConstant :=
  let restriction := output.ancestryAuxiliaryCore.metricRestriction
  pureWZ2_prop62_restrictScaleToSaturated
    (output.finalOldScaleData coordinate)
    (wz2PaperFullFiberIndices
      output.ancestryAuxiliaryCore.metricRestriction.fineSelected.family
      output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.family parent)
    (by
      rcases restriction.section6Cover.parent_hit parent with
        ⟨source, covered⟩
      exact
        ⟨source,
          (mem_wz2PaperFullFiberIndices_iff parent source).mpr covered⟩)
    (output.finalMetricFiber_saturated_for_descendant
      coordinate packetLeCoordinate parent)

/--
Every final descendant witness keeps the synchronized strict line cover on
the exact complete genuine metric fiber.
-/
theorem finalMetricFiberDescendantScaleData_parent_covers
    (coordinate : Fin schedule.levelCount)
    (packetLeCoordinate : packetCoordinate.1 ≤ coordinate.1)
    (parent :
      Fin output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.family.card)
    (source :
      Fin
        (output.ancestryAuxiliaryCore.metricRestriction
          |>.metricFiberSource parent).family.card) :
    WZ1PaperTubeCovers
      ((output.ancestryAuxiliaryCore.metricRestriction
        |>.metricFiberSource parent).family.tube source)
      ((output.finalMetricFiberDescendantScaleData
          coordinate packetLeCoordinate parent).coarse.tube
        ((output.finalMetricFiberDescendantScaleData
          coordinate packetLeCoordinate parent).cover.parent source)) := by
  let restriction := output.ancestryAuxiliaryCore.metricRestriction
  let sourceIndices :=
    wz2PaperFullFiberIndices
      restriction.fineSelected.family
      restriction.coarseSelected.family parent
  have sourceIndicesNonempty : sourceIndices.Nonempty := by
    rcases restriction.section6Cover.parent_hit parent with
      ⟨ambientSource, sourceCovered⟩
    exact
      ⟨ambientSource,
        (mem_wz2PaperFullFiberIndices_iff parent ambientSource).mpr
          sourceCovered⟩
  exact
    pureWZ2_prop62_restrictScaleToSaturated_parent_covers
      (output.finalOldScaleData coordinate)
      sourceIndices sourceIndicesNonempty
      (output.finalMetricFiber_saturated_for_descendant
        coordinate packetLeCoordinate parent)
      (output.finalOldScaleData_parent_covers coordinate)
      source

/-- Final descendant coarse parents remain in the paper line class. -/
theorem finalMetricFiberDescendantScaleData_coarse_line_class
    (coordinate : Fin schedule.levelCount)
    (packetLeCoordinate : packetCoordinate.1 ≤ coordinate.1)
    (parent :
      Fin output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.family.card) :
    WZ1PaperIsLineClass
      (output.finalMetricFiberDescendantScaleData
        coordinate packetLeCoordinate parent).coarse := by
  let restriction := output.ancestryAuxiliaryCore.metricRestriction
  let sourceIndices :=
    wz2PaperFullFiberIndices
      restriction.fineSelected.family
      restriction.coarseSelected.family parent
  have sourceIndicesNonempty : sourceIndices.Nonempty := by
    rcases restriction.section6Cover.parent_hit parent with
      ⟨ambientSource, sourceCovered⟩
    exact
      ⟨ambientSource,
        (mem_wz2PaperFullFiberIndices_iff parent ambientSource).mpr
          sourceCovered⟩
  exact
    pureWZ2_prop62_restrictScaleToSaturated_coarse_line_class
      (output.finalOldScaleData coordinate)
      sourceIndices sourceIndicesNonempty
      (output.finalMetricFiber_saturated_for_descendant
        coordinate packetLeCoordinate parent)
      (by
        change WZ1PaperIsLineClass
          (output.ancestryAuxiliary.outputScaleData
            coordinate output.binnedAmbientPreliminary_nonempty).coarse
        exact
          (schedule.coarse_line_class coordinate).subfamily
            (output.ancestryAuxiliary.coreCoarse
              coordinate output.binnedAmbientPreliminary).toTubeSubfamily)

/--
Any fixed-factor separation on the final old witness passes unchanged to the
complete final metric-fiber restriction.
-/
theorem finalMetricFiberDescendantScaleData_coarse_separated
    (coordinate : Fin schedule.levelCount)
    (packetLeCoordinate : packetCoordinate.1 ≤ coordinate.1)
    (parent :
      Fin output.ancestryAuxiliaryCore.metricRestriction.coarseSelected.family.card)
    (oldSeparated :
      ∀ first second :
          Fin (output.finalOldScaleData coordinate).coarse.card,
        first ≠ second →
          wz2PaperLiteralSourceSeparationFactor *
                schedule.actualScale coordinate <
            wz1PaperLineDistance
              ((output.finalOldScaleData coordinate).coarse.tube first)
              ((output.finalOldScaleData coordinate).coarse.tube second)) :
    ∀ first second :
        Fin
          (output.finalMetricFiberDescendantScaleData
            coordinate packetLeCoordinate parent).coarse.card,
      first ≠ second →
        wz2PaperLiteralSourceSeparationFactor *
              schedule.actualScale coordinate <
          wz1PaperLineDistance
            ((output.finalMetricFiberDescendantScaleData
              coordinate packetLeCoordinate parent).coarse.tube first)
            ((output.finalMetricFiberDescendantScaleData
              coordinate packetLeCoordinate parent).coarse.tube second) := by
  let restriction := output.ancestryAuxiliaryCore.metricRestriction
  let sourceIndices :=
    wz2PaperFullFiberIndices
      restriction.fineSelected.family
      restriction.coarseSelected.family parent
  have sourceIndicesNonempty : sourceIndices.Nonempty := by
    rcases restriction.section6Cover.parent_hit parent with
      ⟨ambientSource, sourceCovered⟩
    exact
      ⟨ambientSource,
        (mem_wz2PaperFullFiberIndices_iff parent ambientSource).mpr
          sourceCovered⟩
  exact
    pureWZ2_prop62_restrictScaleToSaturated_coarse_separated
      (output.finalOldScaleData coordinate)
      sourceIndices sourceIndicesNonempty
      (output.finalMetricFiber_saturated_for_descendant
        coordinate packetLeCoordinate parent)
      oldSeparated

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end
