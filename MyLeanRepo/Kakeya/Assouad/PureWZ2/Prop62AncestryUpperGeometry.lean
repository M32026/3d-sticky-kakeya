import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryRequestedFiberRoute
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62UpperScaleGeometry

/-!
# Proposition 6.2: upper ancestors of final metric parents

At every old coordinate above `rho`, a final genuine metric fiber has one
complete ancestry label and therefore one old parent.  This module turns that
parent into the upper-ancestor map consumed by the factor-nineteen geometry.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62AncestryMetricPreliminaryOutput

private theorem centeredFamily_cast
    {rho : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily rho}
    (familyEq : source = target)
    (targetCentered :
      ∀ parent,
        wz2PaperCenteredLineTube (targetScale := rho)
            (target.tube parent) =
          target.tube parent) :
    ∀ parent,
      wz2PaperCenteredLineTube (targetScale := rho)
          (source.tube parent) =
        source.tube parent := by
  subst target
  exact targetCentered

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

/-- Canonical final fine representative of one final metric parent. -/
noncomputable def finalMetricFiberRepresentative
    (parent :
      Fin
        output.finalMetricRestriction.coarseSelected.family.card) :
    Fin
      output.finalMetricRestriction.fineSelected.family.card :=
  Classical.choose <| by
    rcases
        output.finalMetricRestriction.section6Cover.parent_hit parent
      with
      ⟨source, covered⟩
    exact
      ⟨source,
        (mem_wz2PaperFullFiberIndices_iff parent source).mpr covered⟩

theorem finalMetricFiberRepresentative_mem
    (parent :
      Fin
        output.finalMetricRestriction.coarseSelected.family.card) :
    finalMetricFiberRepresentative (output := output) parent ∈
      wz2PaperFullFiberIndices
        output.finalMetricRestriction.fineSelected.family
        output.finalMetricRestriction.coarseSelected.family
        parent :=
  Classical.choose_spec <| by
    rcases
        output.finalMetricRestriction.section6Cover.parent_hit parent
      with
      ⟨source, covered⟩
    exact
      ⟨source,
        (mem_wz2PaperFullFiberIndices_iff parent source).mpr covered⟩

/-- Old upper ancestor attached to one final metric parent. -/
noncomputable def finalUpperAncestor
    (coordinate : schedule.UpperCoordinate rho packetCoordinate)
    (parent :
      Fin
        output.finalMetricRestriction.coarseSelected.family.card) :
    Fin (output.finalOldScaleData coordinate.1).coarse.card :=
  (output.finalOldScaleData coordinate.1).cover.parent
    (finalMetricFiberRepresentative (output := output) parent)

/--
Every final source in one complete metric fiber has the same old parent at an
upper ancestry coordinate.
-/
theorem finalUpperAncestor_source
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate)
    (parent :
      Fin
        output.finalMetricRestriction.coarseSelected.family.card)
    (source :
      Fin
        output.finalMetricRestriction.fineSelected.family.card)
    (sourceMem :
      source ∈
        wz2PaperFullFiberIndices
          output.finalMetricRestriction.fineSelected.family
          output.finalMetricRestriction.coarseSelected.family
          parent) :
    (output.finalOldScaleData coordinate.1).cover.parent source =
      finalUpperAncestor (output := output) coordinate parent := by
  let restriction := output.finalMetricRestriction
  let representative :=
    finalMetricFiberRepresentative (output := output) parent
  have representativeMem :=
    finalMetricFiberRepresentative_mem (output := output) parent
  have sourceMetricParent :
      output.metric.metricInput.packetParent
          (output.metric.mesh.restrictedOldData.cover.parent
            (restriction.fineSelected.embedding source)) =
        restriction.coarseSelected.embedding parent := by
    have covered :=
      (mem_wz2PaperFullFiberIndices_iff parent source).mp sourceMem
    have ambientCovered :
        WZ1PaperTubeCovers
          (output.metric.selectedFine.tube
            (restriction.fineSelected.embedding source))
          (output.metric.metricParents.tube
            (restriction.coarseSelected.embedding parent)) := by
      rw [← restriction.fineSelected.tube_eq,
        ← restriction.coarseSelected.tube_eq]
      exact covered
    exact
      pureWZ2_prop62_metricParent_unique
        output.metric.metricInput.coarse_essentially_distinct
        (restriction.fineSelected.embedding source)
        (output.metric.metricInput.packetParent
          (output.metric.mesh.restrictedOldData.cover.parent
            (restriction.fineSelected.embedding source)))
        (restriction.coarseSelected.embedding parent)
        (output.metric.metricInput.packetParent_covers
          (restriction.fineSelected.embedding source))
        ambientCovered
  have representativeMetricParent :
      output.metric.metricInput.packetParent
          (output.metric.mesh.restrictedOldData.cover.parent
            (restriction.fineSelected.embedding representative)) =
        restriction.coarseSelected.embedding parent := by
    have covered :=
      (mem_wz2PaperFullFiberIndices_iff parent representative).mp
        representativeMem
    have ambientCovered :
        WZ1PaperTubeCovers
          (output.metric.selectedFine.tube
            (restriction.fineSelected.embedding representative))
          (output.metric.metricParents.tube
            (restriction.coarseSelected.embedding parent)) := by
      rw [← restriction.fineSelected.tube_eq,
        ← restriction.coarseSelected.tube_eq]
      exact covered
    exact
      pureWZ2_prop62_metricParent_unique
        output.metric.metricInput.coarse_essentially_distinct
        (restriction.fineSelected.embedding representative)
        (output.metric.metricInput.packetParent
          (output.metric.mesh.restrictedOldData.cover.parent
            (restriction.fineSelected.embedding representative)))
        (restriction.coarseSelected.embedding parent)
        (output.metric.metricInput.packetParent_covers
          (restriction.fineSelected.embedding representative))
        ambientCovered
  have metricParentEq :
      output.metric.metricInput.packetParent
          (output.metric.mesh.restrictedOldData.cover.parent
            (restriction.fineSelected.embedding source)) =
        output.metric.metricInput.packetParent
          (output.metric.mesh.restrictedOldData.cover.parent
            (restriction.fineSelected.embedding representative)) :=
    sourceMetricParent.trans representativeMetricParent.symm
  have labelEq :=
    (output.packetHull_label_eq_iff_metricParent_eq
      rhoPos widthPos packetScaleLeRho sixWidthLe
      schedule.parent_covers allAncestryCoordinatesUpper
      (restriction.fineSelected.embedding source)
      (restriction.fineSelected.embedding representative)).mpr
      metricParentEq
  have ancestryEq :
      schedule.ancestry packetCoordinate
          (output.metric.mesh.complete.selectedFine.embedding
            (restriction.fineSelected.embedding source)) =
        schedule.ancestry packetCoordinate
          (output.metric.mesh.complete.selectedFine.embedding
            (restriction.fineSelected.embedding representative)) :=
    congrArg Prod.snd labelEq
  let ancestryCoordinate :
      schedule.AncestryCoordinate packetCoordinate :=
    ⟨coordinate.1.1, coordinate.2.2⟩
  have ambientParentEq :=
    congrFun ancestryEq ancestryCoordinate
  unfold finalUpperAncestor
  rw [output.finalOldScaleData_parent_reindex,
    output.finalOldScaleData_parent_reindex]
  rw [
    output.ancestryAuxiliary.outputScale_parent_eq_hitParent,
    output.ancestryAuxiliary.outputScale_parent_eq_hitParent
  ]
  apply
    (output.ancestryAuxiliary.coreCoarse
      coordinate.1 output.binnedAmbientPreliminary).embedding.injective
  rw [
    output.ancestryAuxiliary.coreCoarse_hitParent_ambient,
    output.ancestryAuxiliary.coreCoarse_hitParent_ambient,
    output.finalToAuxiliaryCoreEquiv_embedding,
    output.finalToAuxiliaryCoreEquiv_embedding
  ]
  exact ambientParentEq

/-- Every old upper parent is hit by a final metric parent. -/
theorem finalUpperAncestor_surjective
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate) :
    Function.Surjective
      (finalUpperAncestor (output := output) coordinate) := by
  intro oldParent
  let oldData := output.finalOldScaleData coordinate.1
  have finalFineNonempty :
      output.finalMetricRestriction.fineSelected.family.Nonempty :=
    Fin.pos_iff_nonempty.mpr
      ⟨⟨0, by
        rw [output.finalMetricRestriction.fineSelected_eq]
        exact output.finalMetricRestriction.core_nonempty.card_pos⟩⟩
  have oldFiberNonempty :
      (wz2PaperOrdinaryFullFiberIndices
        output.finalMetricRestriction.fineSelected.family
        oldData.coarse oldParent).Nonempty :=
    oldData.cover.fullFiber_nonempty_of_uniform
      finalFineNonempty oldData.full_fiber_uniform oldParent
  rcases oldFiberNonempty with ⟨source, sourceMem⟩
  let metricParent :=
    output.finalMetricRestriction.lineCover.parent source
  have metricMem :
      source ∈
        wz2PaperFullFiberIndices
          output.finalMetricRestriction.fineSelected.family
          output.finalMetricRestriction.coarseSelected.family
          metricParent := by
    exact
      (mem_wz2PaperFullFiberIndices_iff metricParent source).mpr
        (output.finalMetricRestriction.lineCover.parent_covers source)
  refine ⟨metricParent, ?_⟩
  rw [←
    output.finalUpperAncestor_source
      rhoPos widthPos packetScaleLeRho sixWidthLe
      allAncestryCoordinatesUpper coordinate metricParent source metricMem]
  exact
    (oldData.cover.mem_fullFiber_iff_parent_eq
      oldData.rho_pos.le oldParent source).mp sourceMem

/-- Final metric parents are the centered exact-radius mesh tubes. -/
theorem finalMetricParents_centered
    (parent :
      Fin output.finalMetricRestriction.coarseSelected.family.card) :
    wz2PaperCenteredLineTube (targetScale := rho)
        (output.finalMetricRestriction.coarseSelected.family.tube parent) =
      output.finalMetricRestriction.coarseSelected.family.tube parent := by
  rw [output.finalMetricRestriction.coarseSelected.tube_eq]
  apply
    centeredFamily_cast output.metric.metric_coarse_eq
      (parent := output.finalMetricRestriction.coarseSelected.embedding parent)
  exact
    output.metric.mesh.coarse_centered
      (schedule.coarse_line_class packetCoordinate)

/-- A final metric parent is within one upper radius of its old ancestor. -/
theorem finalUpperAncestor_close
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate)
    (parent :
      Fin output.finalMetricRestriction.coarseSelected.family.card) :
    wz1PaperLineDistance
        (output.finalMetricRestriction.coarseSelected.family.tube parent)
        ((output.finalOldScaleData coordinate.1).coarse.tube
          (finalUpperAncestor (output := output) coordinate parent)) ≤
      schedule.actualScale coordinate.1 := by
  let representative :=
    finalMetricFiberRepresentative (output := output) parent
  have representativeMem :=
    finalMetricFiberRepresentative_mem (output := output) parent
  have fineToMetric :
      wz1PaperLineDistance
          (output.finalMetricRestriction.fineSelected.family.tube representative)
          (output.finalMetricRestriction.coarseSelected.family.tube parent) ≤
        rho / 2 :=
    (mem_wz2PaperFullFiberIndices_iff parent representative).mp
      representativeMem
  have fineToOld :
      wz1PaperLineDistance
          (output.finalMetricRestriction.fineSelected.family.tube representative)
          ((output.finalOldScaleData coordinate.1).coarse.tube
            ((output.finalOldScaleData coordinate.1).cover.parent
              representative)) ≤
        schedule.actualScale coordinate.1 / 2 := by
    exact
      output.finalOldScaleData_parent_covers coordinate.1 representative
  have triangle :=
    wz1PaperLineDistance_triangle
      (output.finalMetricRestriction.coarseSelected.family.tube parent)
      (output.finalMetricRestriction.fineSelected.family.tube representative)
      ((output.finalOldScaleData coordinate.1).coarse.tube
        (finalUpperAncestor (output := output) coordinate parent))
  have symmetry :
      wz1PaperLineDistance
          (output.finalMetricRestriction.coarseSelected.family.tube parent)
          (output.finalMetricRestriction.fineSelected.family.tube representative) =
        wz1PaperLineDistance
          (output.finalMetricRestriction.fineSelected.family.tube representative)
          (output.finalMetricRestriction.coarseSelected.family.tube parent) :=
    wz1PaperLineDistance_symm _ _
  rw [symmetry] at triangle
  calc
    wz1PaperLineDistance
        (output.finalMetricRestriction.coarseSelected.family.tube parent)
        ((output.finalOldScaleData coordinate.1).coarse.tube
          (finalUpperAncestor (output := output) coordinate parent)) ≤
        wz1PaperLineDistance
            (output.finalMetricRestriction.fineSelected.family.tube
              representative)
            (output.finalMetricRestriction.coarseSelected.family.tube
              parent) +
          wz1PaperLineDistance
            (output.finalMetricRestriction.fineSelected.family.tube
              representative)
            ((output.finalOldScaleData coordinate.1).coarse.tube
              (finalUpperAncestor (output := output) coordinate parent)) :=
      triangle
    _ ≤ rho / 2 + schedule.actualScale coordinate.1 / 2 := by
      gcongr
      simpa [finalUpperAncestor] using fineToOld
    _ ≤ schedule.actualScale coordinate.1 := by
      nlinarith [coordinate.2.1]

/-- The exact upper-ancestor geometry on the final metric parent family. -/
noncomputable def finalUpperScaleGeometryInput
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate) :
    PureWZ2Prop62UpperScaleGeometryInput
      output.finalMetricRestriction.coarseSelected.family
      (output.finalOldScaleData coordinate.1).coarse where
  rho_pos := rhoPos
  upper_pos := (output.finalOldScaleData coordinate.1).rho_pos
  rho_le_upper := coordinate.2.1
  children_line_class :=
    output.finalMetricRestriction.section6Cover.coarse_line_class
  children_centered :=
    output.finalMetricParents_centered
  old_line_class := by
    change
      WZ1PaperIsLineClass
        (output.ancestryAuxiliary.outputScaleData
          coordinate.1 output.binnedAmbientPreliminary_nonempty).coarse
    exact
      (schedule.coarse_line_class coordinate.1).subfamily
        (output.ancestryAuxiliary.coreCoarse
          coordinate.1 output.binnedAmbientPreliminary).toTubeSubfamily
  old_essentially_distinct := by
    intro first second indexNe
    have separated :=
      output.finalOldScaleData_coarse_separated
        coordinates coordinate.1 first second indexNe
    have scaleLt :
        schedule.actualScale coordinate.1 <
          wz2PaperLiteralSourceSeparationFactor *
            schedule.actualScale coordinate.1 := by
      unfold wz2PaperLiteralSourceSeparationFactor
      have scalePos :=
        (output.finalOldScaleData coordinate.1).rho_pos
      calc
        schedule.actualScale coordinate.1 =
            1 * schedule.actualScale coordinate.1 := by ring
        _ < 12000000 * schedule.actualScale coordinate.1 := by
          exact mul_lt_mul_of_pos_right (by norm_num) scalePos
    exact scaleLt.trans separated
  ancestor :=
    finalUpperAncestor (output := output) coordinate
  ancestor_surjective :=
    output.finalUpperAncestor_surjective
      rhoPos widthPos packetScaleLeRho sixWidthLe
      allAncestryCoordinatesUpper coordinate
  ancestor_close :=
    output.finalUpperAncestor_close
      rhoPos widthPos packetScaleLeRho sixWidthLe
      allAncestryCoordinatesUpper coordinate

/--
The modified-parent conflict graph has no edges on the frozen ancestry core:
an overlap would force the corresponding old ancestors within `2280 * r`,
while the already selected scheduled color separates them by
`12000000 * r`.
-/
theorem finalUpperScale_no_conflict
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate)
    (first second :
      Fin
        (output.finalUpperScaleGeometryInput
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate
          |>.modifiedParents.card))
    (indexNe : first ≠ second) :
    ¬(wz2PaperOrdinaryDilatedFiberIndices
          2 output.finalMetricRestriction.coarseSelected.family
          (output.finalUpperScaleGeometryInput
            coordinates rhoPos widthPos packetScaleLeRho
            sixWidthLe allAncestryCoordinatesUpper coordinate
            |>.modifiedParents) first ∩
        wz2PaperOrdinaryDilatedFiberIndices
          2 output.finalMetricRestriction.coarseSelected.family
          (output.finalUpperScaleGeometryInput
            coordinates rhoPos widthPos packetScaleLeRho
            sixWidthLe allAncestryCoordinatesUpper coordinate
            |>.modifiedParents) second).Nonempty := by
  intro overlap
  let geometry :=
    output.finalUpperScaleGeometryInput
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate
  have close :=
    geometry.conflict_lineDistance_le (first := first) (second := second)
      overlap
  have separated :=
    output.finalOldScaleData_coarse_separated
      coordinates coordinate.1 second first indexNe.symm
  unfold wz2PaperLiteralSourceSeparationFactor at separated
  have scalePos := (output.finalOldScaleData coordinate.1).rho_pos
  have bound :
      2280 * schedule.actualScale coordinate.1 <
        12000000 * schedule.actualScale coordinate.1 :=
    mul_lt_mul_of_pos_right (by norm_num) scalePos
  exact (not_le_of_gt (bound.trans separated)) close

/-- Degree-zero upper scale input on the full final metric parent family. -/
noncomputable def finalUpperScaleInput
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate) :
    PureWZ2Prop62UpperScaleInput
      output.finalMetricRestriction.coarseSelected.family
      (output.finalUpperScaleGeometryInput
        coordinates rhoPos widthPos packetScaleLeRho
        sixWidthLe allAncestryCoordinatesUpper coordinate
        |>.modifiedParents)
      0 where
  rho_pos := rhoPos
  upper_pos := mul_pos (by norm_num)
    (output.finalOldScaleData coordinate.1).rho_pos
  owner :=
    finalUpperAncestor (output := output) coordinate
  owner_surjective :=
    output.finalUpperAncestor_surjective
      rhoPos widthPos packetScaleLeRho sixWidthLe
      allAncestryCoordinatesUpper coordinate
  owner_containment :=
    (output.finalUpperScaleGeometryInput
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate).owner_containment
  conflict_degree := by
    intro fixed
    have empty :
        (Finset.univ.filter fun other =>
          other ≠ fixed ∧
            (wz2PaperOrdinaryDilatedFiberIndices
                2 output.finalMetricRestriction.coarseSelected.family
                (output.finalUpperScaleGeometryInput
                  coordinates rhoPos widthPos packetScaleLeRho
                  sixWidthLe allAncestryCoordinatesUpper coordinate
                  |>.modifiedParents) fixed ∩
              wz2PaperOrdinaryDilatedFiberIndices
                2 output.finalMetricRestriction.coarseSelected.family
                (output.finalUpperScaleGeometryInput
                  coordinates rhoPos widthPos packetScaleLeRho
                  sixWidthLe allAncestryCoordinatesUpper coordinate
                  |>.modifiedParents) other).Nonempty) = ∅ := by
      ext other
      constructor
      · intro otherMem
        have data := (Finset.mem_filter.mp otherMem).2
        exact
          (output.finalUpperScale_no_conflict
            coordinates rhoPos widthPos packetScaleLeRho sixWidthLe
            allAncestryCoordinatesUpper coordinate fixed other
            data.1.symm data.2).elim
      · intro otherEmpty
        simp at otherEmpty
    rw [empty]
    simp

/-- The unique degree-zero color on the upper conflict-free graph. -/
noncomputable def finalUpperScaleColoring
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate) :
    (output.finalUpperScaleInput
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate).ColoringData :=
  Classical.choice <|
    (output.finalUpperScaleInput
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate).exists_coloring

/-- Full-child monochromatic cover at one upper coordinate. -/
noncomputable def finalUpperMonochromaticCover
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (coordinate : schedule.UpperCoordinate rho packetCoordinate) :
    (output.finalUpperScaleInput
      coordinates rhoPos widthPos packetScaleLeRho
      sixWidthLe allAncestryCoordinatesUpper coordinate
      |>.MonochromaticCoverData
        (output.finalUpperScaleColoring
          coordinates rhoPos widthPos packetScaleLeRho
          sixWidthLe allAncestryCoordinatesUpper coordinate)
        (pureWZ2Prop62IdentitySubfamily
          output.finalMetricRestriction.coarseSelected.family)) :=
  Classical.choice <| by
    apply
      (output.finalUpperScaleColoring
        coordinates rhoPos widthPos packetScaleLeRho
        sixWidthLe allAncestryCoordinatesUpper coordinate
        |>.full_monochromatic_cover)
        0
    intro child
    exact Fin.eq_zero _

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end
