import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62SourceConflictColoring
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricPreliminaryAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AuxiliaryTreeCore

/-!
# Proposition 6.2 source separation on the one-pass tree core

The source-conflict coloring is one coordinate of the preliminary dependent
color vector.  The metric construction first takes the complete old-packet
hull of that color class, while the augmented-tree cleanup starts from the
pulled-back dyadic leaf set.  Consequently the one final leaf core remains
monochromatic for the source-conflict color and is strongly separated.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62SourceConflictCoordinateData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coordinateCount : ℕ}
    (Color : Fin coordinateCount → Type*)
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    (color : ∀ coordinate, Fin fine.card → Color coordinate) where
  coloring : PureWZ2Prop62SourceConflictColoringData fine
  coordinate : Fin coordinateCount
  decode :
    Color coordinate →
      Fin (pureWZ2OrdinaryLineConflictDegree + 1)
  decode_color :
    ∀ source,
      decode (color coordinate source) = coloring.color source

namespace PureWZ2Prop62SourceConflictCoordinateData

variable
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData fine scale C}
    {coordinateCount : ℕ}
    {Color : Fin coordinateCount → Type*}
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    {color : ∀ coordinate, Fin fine.card → Color coordinate}
    {weight : Fin fine.card → ENNReal}
    {preliminary :
      PureWZ2Prop62PreliminarySelectionData
        coordinateCount Color color weight}
    {width M : ℝ}
    (conflict :
      PureWZ2Prop62SourceConflictCoordinateData Color color)
    (output :
      PureWZ2Prop62MetricPreliminaryOutput
        (rho := rho) oldData Color color weight preliminary width M)

def selectedColor
    (preliminary :
      PureWZ2Prop62PreliminarySelectionData
        coordinateCount Color color weight) :
    Fin (pureWZ2OrdinaryLineConflictDegree + 1) :=
  conflict.decode (preliminary.colorVector conflict.coordinate)

theorem selectedPreliminary_monochromatic
    (source : Fin output.metric.selectedFine.card)
    (sourceMem : source ∈ output.selectedPreliminary) :
    conflict.coloring.color
        (output.metric.mesh.complete.selectedFine.embedding source) =
      conflict.selectedColor preliminary := by
  rw [← conflict.decode_color
    (output.metric.mesh.complete.selectedFine.embedding source)]
  exact congrArg conflict.decode <|
    output.selectedPreliminary_monochromatic
      source sourceMem conflict.coordinate

theorem core_stronglySeparated
    (conflict :
      PureWZ2Prop62SourceConflictCoordinateData Color color)
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        output.metric.selectedFine ambientConstant scaleWindow}
    (auxiliary :
      PureWZ2Prop62AuxiliaryLevel
        schedule (Fin output.metric.metricParents.card))
    (restriction :
      PureWZ2Prop62MetricCoreRestrictionData
        output.metric.section6Cover
        (auxiliary.coreIndices output.selectedPreliminary)) :
    ∀ first second, first ≠ second →
      wz2PaperLiteralSourceSeparationFactor * delta <
        wz1PaperLineDistance
          (restriction.fineSelected.family.tube first)
          (restriction.fineSelected.family.tube second) := by
  intro first second indexNe
  let firstSelected := restriction.fineSelected.embedding first
  let secondSelected := restriction.fineSelected.embedding second
  let firstAmbient :=
    output.metric.mesh.complete.selectedFine.embedding firstSelected
  let secondAmbient :=
    output.metric.mesh.complete.selectedFine.embedding secondSelected
  have firstCore :
      firstSelected ∈
        auxiliary.coreIndices output.selectedPreliminary := by
    rw [← restriction.fine_image_univ]
    exact
      Finset.mem_image.mpr
        ⟨first, Finset.mem_univ first, rfl⟩
  have secondCore :
      secondSelected ∈
        auxiliary.coreIndices output.selectedPreliminary := by
    rw [← restriction.fine_image_univ]
    exact
      Finset.mem_image.mpr
        ⟨second, Finset.mem_univ second, rfl⟩
  have firstPreliminary :
      firstSelected ∈ output.selectedPreliminary :=
    auxiliary.coreOutput output.selectedPreliminary
      |>.core_subset firstCore
  have secondPreliminary :
      secondSelected ∈ output.selectedPreliminary :=
    auxiliary.coreOutput output.selectedPreliminary
      |>.core_subset secondCore
  have ambientNe : firstAmbient ≠ secondAmbient := by
    exact
      output.metric.mesh.complete.selectedFine.embedding.injective.ne <|
        restriction.fineSelected.embedding.injective.ne indexNe
  have colorNe :=
    PureWZ2Prop62SourceConflictColoringData.proper
      conflict.coloring firstAmbient secondAmbient ambientNe
  have colorEq :
      conflict.coloring.color firstAmbient =
        conflict.coloring.color secondAmbient :=
    (conflict.selectedPreliminary_monochromatic
        output firstSelected firstPreliminary).trans
      (conflict.selectedPreliminary_monochromatic
        output secondSelected secondPreliminary).symm
  by_contra notSeparated
  have distanceClose :
      wz1PaperLineDistance
          (fine.tube firstAmbient) (fine.tube secondAmbient) ≤
        wz2PaperLiteralSourceSeparationFactor * delta := by
    simpa only [
      firstAmbient, secondAmbient, firstSelected, secondSelected,
      restriction.fineSelected.tube_eq,
      output.metric.mesh.complete.selectedFine.tube_eq
    ] using le_of_not_gt notSeparated
  exact (colorNe distanceClose) colorEq

end PureWZ2Prop62SourceConflictCoordinateData

end Kakeya.Assouad

end
