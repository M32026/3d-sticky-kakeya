import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryDescendantFiber
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryFinalMetricQuantitative
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryRequestedScaleDichotomy
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ScheduledParentConflictColoring
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62SourceConflictCore

/-!
# Proposition 6.2: requested old witnesses on final metric fibers

Combine the numerical descendant-or-top dichotomy with the exact descendant
restriction on one final genuine metric fiber.  No new cover and no new tube
subfamily are selected here.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal
open MeasureTheory

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
One finite constant absorbing the final-core witness, the inserted physical
CWA, the old rounding window, and the top-window scalar ratio.
-/
def finalMetricFiberRouteConstant : ENNReal :=
  max output.finalCoreConstant <|
    max
      (pureWZ2Prop62InsertedCWALoss
        rho (schedule.actualScale packetCoordinate) ambientConstant *
          output.ancestryDensityLoss)
      (max
        scaleWindow
        ((4 : ENNReal) *
          ((100 : ENNReal) * scaleWindow * ENNReal.ofReal rho) /
            ((81000000 : ENNReal) *
              ENNReal.ofReal
                (schedule.actualScale packetCoordinate))))

theorem finalMetricFiberRouteConstant_finite :
    WZ2PaperFiniteErrorConstant
      output.finalMetricFiberRouteConstant := by
  have actualPos :
      0 < schedule.actualScale packetCoordinate :=
    (schedule.scaleData packetCoordinate).rho_pos
  have insertedFinite :
      pureWZ2Prop62InsertedCWALoss
            rho (schedule.actualScale packetCoordinate) ambientConstant *
          output.ancestryDensityLoss ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · unfold pureWZ2Prop62InsertedCWALoss
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        schedule.ambient_finite.2
    · unfold ancestryDensityLoss
      have selectedZero :
          (output.binnedAmbientPreliminary.card : ENNReal) ≠ 0 := by
        exact_mod_cast
          (Finset.card_pos.mpr
            output.binnedAmbientPreliminary_nonempty).ne'
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by simp) (by
          simp [Kakeya.Streamlined.TubeFamily.enncard]))
        (ENNReal.inv_ne_top.mpr selectedZero)
  have denominatorNeZero :
      (81000000 : ENNReal) *
          ENNReal.ofReal (schedule.actualScale packetCoordinate) ≠ 0 := by
    exact mul_ne_zero (by norm_num)
      (ENNReal.ofReal_ne_zero_iff.mpr actualPos)
  have topFinite :
      (4 : ENNReal) *
            ((100 : ENNReal) * scaleWindow * ENNReal.ofReal rho) /
          ((81000000 : ENNReal) *
            ENNReal.ofReal
              (schedule.actualScale packetCoordinate)) ≠ ⊤ := by
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top
        (by norm_num)
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num)
            schedule.scaleWindow_finite.2)
          ENNReal.ofReal_ne_top)
    · exact denominatorNeZero
  have routeFinite :
      output.finalMetricFiberRouteConstant ≠ ⊤ := by
    unfold finalMetricFiberRouteConstant
    exact max_ne_top
      (output.ancestryAuxiliary.outputConstant_finite
        output.binnedAmbientPreliminary_nonempty).2
      (max_ne_top insertedFinite
        (max_ne_top schedule.scaleWindow_finite.2 topFinite))
  have routeOne :
      (1 : ENNReal) ≤ output.finalMetricFiberRouteConstant := by
    exact
      (output.ancestryAuxiliary.outputConstant_finite
        output.binnedAmbientPreliminary_nonempty).1.trans
        (le_max_left _ _)
  exact ⟨routeOne, routeFinite⟩

theorem finalCoreConstant_le_finalMetricFiberRouteConstant :
    output.finalCoreConstant ≤
      output.finalMetricFiberRouteConstant :=
  le_max_left _ _

theorem finalInsertedConstant_le_finalMetricFiberRouteConstant :
    pureWZ2Prop62InsertedCWALoss
          rho (schedule.actualScale packetCoordinate) ambientConstant *
        output.ancestryDensityLoss ≤
      output.finalMetricFiberRouteConstant :=
  le_max_of_le_right (le_max_left _ _)

theorem finalMetricFiberRouteConstant_windowAbsorption :
    (100 : ENNReal) * scaleWindow ≤
      (81000000 : ENNReal) *
        output.finalMetricFiberRouteConstant := by
  have windowLe :
      scaleWindow ≤
        output.finalMetricFiberRouteConstant :=
    calc
      scaleWindow ≤
          max
            scaleWindow
            ((4 : ENNReal) *
              ((100 : ENNReal) * scaleWindow * ENNReal.ofReal rho) /
                ((81000000 : ENNReal) *
                  ENNReal.ofReal
                    (schedule.actualScale packetCoordinate))) :=
        le_max_left _ _
      _ ≤
          max
            (pureWZ2Prop62InsertedCWALoss
              rho (schedule.actualScale packetCoordinate) ambientConstant *
                output.ancestryDensityLoss)
            (max
              scaleWindow
              ((4 : ENNReal) *
                ((100 : ENNReal) * scaleWindow * ENNReal.ofReal rho) /
                  ((81000000 : ENNReal) *
                    ENNReal.ofReal
                      (schedule.actualScale packetCoordinate)))) :=
        le_max_right _ _
      _ ≤ output.finalMetricFiberRouteConstant :=
        le_max_right _ _
  calc
    (100 : ENNReal) * scaleWindow ≤
        (81000000 : ENNReal) * scaleWindow := by
      gcongr
      norm_num
    _ ≤
        (81000000 : ENNReal) *
          output.finalMetricFiberRouteConstant :=
      mul_le_mul_left' windowLe _

theorem finalMetricFiberRouteConstant_topGate :
    (4 : ENNReal) *
        ((100 : ENNReal) * scaleWindow *
          ENNReal.ofReal rho) ≤
      ((81000000 : ENNReal) *
        output.finalMetricFiberRouteConstant) *
          ENNReal.ofReal
            (schedule.actualScale packetCoordinate) := by
  let numerator :=
    (4 : ENNReal) *
      ((100 : ENNReal) * scaleWindow * ENNReal.ofReal rho)
  let denominator :=
    (81000000 : ENNReal) *
      ENNReal.ofReal (schedule.actualScale packetCoordinate)
  have actualPos :
      0 < schedule.actualScale packetCoordinate :=
    (schedule.scaleData packetCoordinate).rho_pos
  have denominatorNeZero : denominator ≠ 0 := by
    dsimp only [denominator]
    exact mul_ne_zero (by norm_num)
      (ENNReal.ofReal_ne_zero_iff.mpr actualPos)
  have denominatorNeTop : denominator ≠ ⊤ := by
    dsimp only [denominator]
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have ratioLe :
      numerator / denominator ≤
        output.finalMetricFiberRouteConstant := by
    calc
      numerator / denominator ≤
          max
            scaleWindow
            (numerator / denominator) :=
        le_max_right _ _
      _ ≤
          max
            (pureWZ2Prop62InsertedCWALoss
              rho (schedule.actualScale packetCoordinate) ambientConstant *
                output.ancestryDensityLoss)
            (max
              scaleWindow
              (numerator / denominator)) :=
        le_max_right _ _
      _ ≤ output.finalMetricFiberRouteConstant :=
        le_max_right _ _
  have numeratorLe :
      numerator ≤
        output.finalMetricFiberRouteConstant * denominator :=
    (ENNReal.div_le_iff denominatorNeZero denominatorNeTop).mp ratioLe
  simpa only [numerator, denominator] using numeratorLe.trans_eq (by
    ring)

/--
Every final ancestry-core leaf has the globally selected scheduled-parent
color at every old coordinate.
-/
theorem ancestryCore_scheduled_monochromatic
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (coordinate : Fin schedule.levelCount)
    (source :
      Fin
        (output.ancestryAuxiliary.coreFine
          output.binnedAmbientPreliminary).family.card) :
    scheduled.leafColor coordinate
        ((output.ancestryAuxiliary.coreFine
          output.binnedAmbientPreliminary).embedding source) =
      coordinates.decode coordinate
        (preliminary.preliminary.colorVector
          (coordinates.slot coordinate)) := by
  let ambientSource :=
    (output.ancestryAuxiliary.coreFine
      output.binnedAmbientPreliminary).embedding source
  have coreMem :
      ambientSource ∈
        output.ancestryAuxiliary.coreIndices
          output.binnedAmbientPreliminary :=
    Finset.orderEmbOfFin_mem _ rfl source
  have binnedMem :
      ambientSource ∈ output.binnedAmbientPreliminary :=
    (output.ancestryAuxiliary.coreOutput
      output.binnedAmbientPreliminary).core_subset coreMem
  have selectedMem :
      ambientSource ∈ preliminary.preliminary.selected :=
    output.binnedAmbientPreliminary_subset_original binnedMem
  rw [← coordinates.decode_color coordinate ambientSource]
  exact congrArg (coordinates.decode coordinate) <|
    preliminary.preliminary.selected_monochromatic
      ambientSource selectedMem (coordinates.slot coordinate)

/-- Every hit old parent family on the ancestry core is strongly separated. -/
theorem ancestryCore_hitParents_stronglySeparated
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (coordinate : Fin schedule.levelCount) :
    ∀ first second :
        Fin
          (output.ancestryAuxiliary.coreCoarse
            coordinate output.binnedAmbientPreliminary).family.card,
      first ≠ second →
        wz2PaperLiteralSourceSeparationFactor *
              schedule.actualScale coordinate <
          wz1PaperLineDistance
            ((output.ancestryAuxiliary.coreCoarse
              coordinate output.binnedAmbientPreliminary).family.tube first)
            ((output.ancestryAuxiliary.coreCoarse
              coordinate output.binnedAmbientPreliminary).family.tube second) := by
  exact
    scheduled.hitParents_stronglySeparated
      coordinate
      (output.ancestryAuxiliary.coreFine
        output.binnedAmbientPreliminary)
      (coordinates.decode coordinate
        (preliminary.preliminary.colorVector
          (coordinates.slot coordinate)))
      (ancestryCore_scheduled_monochromatic
        (output := output)
        coordinates coordinate)

/-- The exact final old witness inherits the ancestry-core parent separation. -/
theorem finalOldScaleData_coarse_separated
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (coordinate : Fin schedule.levelCount) :
    ∀ first second : Fin (output.finalOldScaleData coordinate).coarse.card,
      first ≠ second →
        wz2PaperLiteralSourceSeparationFactor *
              schedule.actualScale coordinate <
          wz1PaperLineDistance
            ((output.finalOldScaleData coordinate).coarse.tube first)
            ((output.finalOldScaleData coordinate).coarse.tube second) := by
  exact
    ancestryCore_hitParents_stronglySeparated
      (output := output)
      coordinates coordinate

/-- The final Section 6 fine core keeps the preliminary source color. -/
theorem finalFine_stronglySeparated
    (conflict :
      PureWZ2Prop62SourceConflictCoordinateData Color color) :
    ∀ first second :
        Fin
          (output.ancestryAuxiliaryCore.metricRestriction
            |>.fineSelected.family.card),
      first ≠ second →
        wz2PaperLiteralSourceSeparationFactor * delta <
          wz1PaperLineDistance
            (output.ancestryAuxiliaryCore.metricRestriction
              |>.fineSelected.family.tube first)
            (output.ancestryAuxiliaryCore.metricRestriction
              |>.fineSelected.family.tube second) := by
  intro first second indexNe
  let restriction := output.ancestryAuxiliaryCore.metricRestriction
  let firstScheduled := restriction.fineSelected.embedding first
  let secondScheduled := restriction.fineSelected.embedding second
  let firstAmbient :=
    output.metric.mesh.complete.selectedFine.embedding firstScheduled
  let secondAmbient :=
    output.metric.mesh.complete.selectedFine.embedding secondScheduled
  have firstCore :
      firstScheduled ∈ output.ancestryAuxiliaryCore.pullback.pulledBack := by
    rw [← restriction.fine_image_univ]
    exact Finset.mem_image.mpr
      ⟨first, Finset.mem_univ first, rfl⟩
  have secondCore :
      secondScheduled ∈ output.ancestryAuxiliaryCore.pullback.pulledBack := by
    rw [← restriction.fine_image_univ]
    exact Finset.mem_image.mpr
      ⟨second, Finset.mem_univ second, rfl⟩
  have firstAmbientCore :
      firstAmbient ∈ output.ancestryAuxiliaryCore.ambientCore := by
    rw [← output.ancestryAuxiliaryCore.pullback.image_eq]
    exact Finset.mem_image.mpr
      ⟨firstScheduled, firstCore, rfl⟩
  have secondAmbientCore :
      secondAmbient ∈ output.ancestryAuxiliaryCore.ambientCore := by
    rw [← output.ancestryAuxiliaryCore.pullback.image_eq]
    exact Finset.mem_image.mpr
      ⟨secondScheduled, secondCore, rfl⟩
  have firstSelected :
      firstAmbient ∈ preliminary.preliminary.selected := by
    rw [output.ancestryAuxiliaryCore.ambientCore_eq] at firstAmbientCore
    apply output.binnedAmbientPreliminary_subset_original
    exact
      (output.ancestryAuxiliary.coreOutput
        output.binnedAmbientPreliminary).core_subset firstAmbientCore
  have secondSelected :
      secondAmbient ∈ preliminary.preliminary.selected := by
    rw [output.ancestryAuxiliaryCore.ambientCore_eq] at secondAmbientCore
    apply output.binnedAmbientPreliminary_subset_original
    exact
      (output.ancestryAuxiliary.coreOutput
        output.binnedAmbientPreliminary).core_subset secondAmbientCore
  have colorEq :
      conflict.coloring.color firstAmbient =
        conflict.coloring.color secondAmbient := by
    calc
      conflict.coloring.color firstAmbient =
          conflict.decode (color conflict.coordinate firstAmbient) :=
        (conflict.decode_color firstAmbient).symm
      _ =
          conflict.decode
            (preliminary.preliminary.colorVector conflict.coordinate) :=
        congrArg conflict.decode
          (preliminary.preliminary.selected_monochromatic
            firstAmbient firstSelected conflict.coordinate)
      _ =
          conflict.decode (color conflict.coordinate secondAmbient) :=
        congrArg conflict.decode
          (preliminary.preliminary.selected_monochromatic
            secondAmbient secondSelected conflict.coordinate).symm
      _ = conflict.coloring.color secondAmbient :=
        conflict.decode_color secondAmbient
  have ambientNe : firstAmbient ≠ secondAmbient :=
    output.metric.mesh.complete.selectedFine.embedding.injective.ne <|
      restriction.fineSelected.embedding.injective.ne indexNe
  by_contra notSeparated
  have notSeparated' :
      wz1PaperLineDistance
          (restriction.fineSelected.family.tube first)
          (restriction.fineSelected.family.tube second) ≤
        wz2PaperLiteralSourceSeparationFactor * delta :=
    le_of_not_gt notSeparated
  have close :
      wz1PaperLineDistance
          (fine.tube firstAmbient) (fine.tube secondAmbient) ≤
        wz2PaperLiteralSourceSeparationFactor * delta := by
    rw [← output.metric.mesh.complete.selectedFine.tube_eq,
      ← output.metric.mesh.complete.selectedFine.tube_eq,
      ← restriction.fineSelected.tube_eq,
      ← restriction.fineSelected.tube_eq]
    exact notSeparated'
  exact (conflict.coloring.proper firstAmbient secondAmbient
    ambientNe close) colorEq

/--
The inserted final-fiber estimate is exactly the Body-CWA estimate for the
literal images of the canonical complete metric fiber.
-/
theorem finalMetricFiberLiteralImageCWA
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
    (parent :
      Fin
        (output.ancestryAuxiliaryCore.metricRestriction
          |>.coarseSelected.family.card)) :
    WZ2PaperBodyConvexWolffBound
      (output.ancestryAuxiliaryCore.metricRestriction
        |>.metricFiberLiteralImageBodies
          output.metric.metricInput.rho_pos parent)
      (pureWZ2Prop62InsertedCWALoss
          rho (schedule.actualScale packetCoordinate) ambientConstant *
        output.ancestryDensityLoss) := by
  intro convexSet convex
  let restriction := output.ancestryAuxiliaryCore.metricRestriction
  let fiber :=
    wz2PaperFullFiberIndices
      restriction.fineSelected.family
      restriction.coarseSelected.family parent
  let sourceFamily := restriction.metricFiberSource parent
  let literalBodies :=
    restriction.metricFiberLiteralImageBodies
      output.metric.metricInput.rho_pos parent
  let ambientPredicate :
      Fin restriction.fineSelected.family.card → Prop :=
    fun source =>
      wz2PaperLiteralUnitRescalingMap
          (restriction.coarseSelected.family.tube parent)
          output.metric.metricInput.rho_pos ''
        (restriction.fineSelected.family.tube source).carrier ⊆ convexSet
  let localPredicate : Fin sourceFamily.family.card → Prop :=
    fun source =>
      (literalBodies.body source).carrier ⊆ convexSet
  have filteredImage :
      Finset.image sourceFamily.embedding
          (Finset.univ.filter localPredicate) =
        fiber.filter ambientPredicate := by
    ext ambientSource
    constructor
    · intro ambientMem
      rcases Finset.mem_image.mp ambientMem with
        ⟨source, sourceMem, rfl⟩
      have sourceData := Finset.mem_filter.mp sourceMem
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.orderEmbOfFin_mem fiber rfl source
      · change
          wz2PaperLiteralUnitRescalingMap
              (restriction.coarseSelected.family.tube parent)
              output.metric.metricInput.rho_pos ''
            (restriction.fineSelected.family.tube
              (sourceFamily.embedding source)).carrier ⊆ convexSet
        exact sourceData.2
    · intro ambientMem
      have ambientData := Finset.mem_filter.mp ambientMem
      let equivalence : Fin fiber.card ≃ fiber :=
        (fiber.orderIsoOfFin rfl).toEquiv
      let source : Fin sourceFamily.family.card :=
        equivalence.symm ⟨ambientSource, ambientData.1⟩
      have sourceEq :
          sourceFamily.embedding source = ambientSource :=
        congrArg Subtype.val
          (equivalence.apply_symm_apply
            ⟨ambientSource, ambientData.1⟩)
      apply Finset.mem_image.mpr
      refine ⟨source, Finset.mem_filter.mpr
        ⟨Finset.mem_univ source, ?_⟩, sourceEq⟩
      change
        wz2PaperLiteralUnitRescalingMap
            (restriction.coarseSelected.family.tube parent)
            output.metric.metricInput.rho_pos ''
          (sourceFamily.family.tube source).carrier ⊆ convexSet
      rw [sourceFamily.tube_eq, sourceEq]
      exact ambientData.2
  have filteredCard :
      (Finset.univ.filter localPredicate).card =
        (fiber.filter ambientPredicate).card := by
    rw [← filteredImage]
    exact
      (Finset.card_image_of_injective _
        sourceFamily.embedding.injective).symm
  have sourceCard :
      sourceFamily.family.card = fiber.card := rfl
  have inserted :=
    output.finalInsertedFiberCWA
      output.metric.metricInput.rho_pos widthPos
      packetScaleLeRho sixWidthLe schedule.parent_covers
      allAncestryCoordinatesUpper parent convexSet convex
  change
    ((Finset.univ.filter localPredicate).card : ENNReal) ≤
      (pureWZ2Prop62InsertedCWALoss
          rho (schedule.actualScale packetCoordinate) ambientConstant *
        output.ancestryDensityLoss) *
        volume convexSet * (sourceFamily.family.card : ENNReal)
  rw [filteredCard, sourceCard]
  exact inserted

/--
The canonical ordinary rescaled family of one final metric fiber has physical
Body CWA with the canonical route constant.
-/
theorem finalMetricFiberRescaledPhysicalCWA
    (rhoLeOne : rho ≤ 1)
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
    (parent :
      Fin
        (output.ancestryAuxiliaryCore.metricRestriction
          |>.coarseSelected.family.card)) :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperLiteralOrdinaryRescaledFamily
        (output.ancestryAuxiliaryCore.metricRestriction
          |>.metricFiberSource parent).family
        (output.ancestryAuxiliaryCore.metricRestriction
          |>.coarseSelected.family.tube parent)
        output.metric.metricInput.rho_pos).toBodyFamily
      output.finalMetricFiberRouteConstant := by
  let restriction := output.ancestryAuxiliaryCore.metricRestriction
  let source :=
    restriction.metricFiberLiteralImageBodies
      output.metric.metricInput.rho_pos parent
  let target :=
    (wz2PaperLiteralOrdinaryRescaledFamily
      (restriction.metricFiberSource parent).family
      (restriction.coarseSelected.family.tube parent)
      output.metric.metricInput.rho_pos).toBodyFamily
  have raw :
      WZ2PaperBodyConvexWolffBound target
        (pureWZ2Prop62InsertedCWALoss
            rho (schedule.actualScale packetCoordinate) ambientConstant *
          output.ancestryDensityLoss) := by
    apply WZ2PaperBodyConvexWolffBound.of_pointwise_subset
      (source := source) (target := target) rfl
    · intro index
      change
        wz2PaperLiteralUnitRescalingMap
            (restriction.coarseSelected.family.tube parent)
            output.metric.metricInput.rho_pos ''
          ((restriction.metricFiberSource parent).family.tube index).carrier ⊆
        (wz2PaperLiteralOrdinaryRescaledTube
          ((restriction.metricFiberSource parent).family.tube index)
          (restriction.coarseSelected.family.tube parent)
          output.metric.metricInput.rho_pos).carrier
      exact
        wz2PaperLiteral_image_carrier_subset_ordinary
          (schedule.scaleData packetCoordinate).delta_pos
          ((restriction.metricFiberSource parent).family.tube index)
          (restriction.coarseSelected.family.tube parent)
          output.metric.metricInput.rho_pos rhoLeOne
          (by
            rw [(restriction.metricFiberSource parent).tube_eq]
            exact
              (mem_wz2PaperFullFiberIndices_iff parent
                ((restriction.metricFiberSource parent).embedding index)).mp <|
                Finset.orderEmbOfFin_mem
                  (wz2PaperFullFiberIndices
                    restriction.fineSelected.family
                    restriction.coarseSelected.family parent)
                  rfl index)
    · exact
        output.finalMetricFiberLiteralImageCWA
          widthPos packetScaleLeRho sixWidthLe
          allAncestryCoordinatesUpper parent
  intro convexSet convex
  exact (raw convexSet convex).trans <| by
    gcongr
    exact output.finalInsertedConstant_le_finalMetricFiberRouteConstant

/--
Canonical lower-or-top route with all ordinary nested-scale geometry attached
to the same final genuine metric fiber.
-/
theorem finalMetricFiberCanonicalRequestedRoute
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (rhoLeOne : rho ≤ 1)
    (scaleSeparation : 100 * delta ≤ rho)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (fineBoundedBase : HasBoundedBase fine 4)
    (parent :
      Fin
        (output.ancestryAuxiliaryCore.metricRestriction
          |>.coarseSelected.family.card)) :
    ∀ requested : WZ2PaperRequestedScale (delta / rho),
      (∃ (actual : ℝ)
          (scaleData :
            WZ2PaperPureScaleCoverData
              (output.ancestryAuxiliaryCore.metricRestriction
                |>.metricFiberSource parent).family
              actual output.finalMetricFiberRouteConstant),
        100 * delta ≤ actual ∧
          actual ≤ rho ∧
          requested.1 ≤ actual / rho ∧
          ENNReal.ofReal (actual / rho) <
            ((81000000 : ENNReal) *
              output.finalMetricFiberRouteConstant) *
              ENNReal.ofReal requested.1 ∧
          WZ1PaperIsLineClass scaleData.coarse ∧
          (∀ source,
            WZ1PaperTubeCovers
              ((output.ancestryAuxiliaryCore.metricRestriction
                |>.metricFiberSource parent).family.tube source)
              (scaleData.coarse.tube
                (scaleData.cover.parent source))) ∧
          (∀ middle,
            WZ2PaperDilatedTubeCovers 2
              (scaleData.coarse.tube middle)
              (output.ancestryAuxiliaryCore.metricRestriction
                |>.coarseSelected.family.tube parent)) ∧
          (∀ first second, first ≠ second →
            wz2PaperLiteralSourceSeparationFactor * actual <
              wz1PaperLineDistance
                (scaleData.coarse.tube first)
                (scaleData.coarse.tube second)) ∧
          WZ2PaperOrdinaryNestedTargetLocalization
            (output.ancestryAuxiliaryCore.metricRestriction
              |>.metricFiberSource parent).family
            scaleData.coarse
            (output.ancestryAuxiliaryCore.metricRestriction
              |>.coarseSelected.family.tube parent)
            output.metric.metricInput.rho_pos) ∨
      (4 : ENNReal) <
        ((81000000 : ENNReal) *
          output.finalMetricFiberRouteConstant) *
          ENNReal.ofReal requested.1 := by
  intro requested
  rcases
      schedule.requested_descendant_or_top
        packetCoordinate output.metric.metricInput.rho_pos
        rhoLeOne scaleSeparation packetScaleLeRho
        output.finalMetricFiberRouteConstant
        output.finalMetricFiberRouteConstant_finite
        output.finalMetricFiberRouteConstant_windowAbsorption
        output.finalMetricFiberRouteConstant_topGate requested
    with descendant | topWindow
  · rcases descendant with
      ⟨coordinate, packetBefore, treeSafe,
        actualLeRho, requestedLe, within⟩
    let scaleData :=
      (output.finalMetricFiberDescendantScaleData
        coordinate packetBefore.le parent).mono
          output.finalCoreConstant_le_finalMetricFiberRouteConstant
    let restriction := output.ancestryAuxiliaryCore.metricRestriction
    let sourceFamily := restriction.metricFiberSource parent
    have sourceLine : WZ1PaperIsLineClass sourceFamily.family :=
      restriction.section6Cover.fine_line_class.subfamily
        sourceFamily.toTubeSubfamily
    have anchorLine :
        WZ1PaperTubeInLineClass
          (restriction.coarseSelected.family.tube parent) :=
      restriction.section6Cover.coarse_line_class parent
    have sourceCovered :
        ∀ source,
          WZ1PaperTubeCovers
            (sourceFamily.family.tube source)
            (restriction.coarseSelected.family.tube parent) := by
      intro source
      rw [sourceFamily.tube_eq]
      exact
        (mem_wz2PaperFullFiberIndices_iff parent
          (sourceFamily.embedding source)).mp
          (Finset.orderEmbOfFin_mem
            (wz2PaperFullFiberIndices
              restriction.fineSelected.family
              restriction.coarseSelected.family parent)
            rfl source)
    have sourceNonempty : sourceFamily.family.Nonempty := by
      change
        0 <
          (wz2PaperFullFiberIndices
            restriction.fineSelected.family
            restriction.coarseSelected.family parent).card
      exact Finset.card_pos.mpr <| by
        rcases restriction.section6Cover.parent_hit parent with
          ⟨source, covered⟩
        exact
          ⟨source,
            (mem_wz2PaperFullFiberIndices_iff parent source).mpr
              covered⟩
    have middleLine : WZ1PaperIsLineClass scaleData.coarse := by
      exact
        output.finalMetricFiberDescendantScaleData_coarse_line_class
          coordinate packetBefore.le parent
    have fineMiddle :
        ∀ source,
          WZ1PaperTubeCovers
            (sourceFamily.family.tube source)
            (scaleData.coarse.tube
              (scaleData.cover.parent source)) := by
      exact
        output.finalMetricFiberDescendantScaleData_parent_covers
          coordinate packetBefore.le parent
    have middleAnchor :
        ∀ middle,
          WZ2PaperDilatedTubeCovers 2
            (scaleData.coarse.tube middle)
            (restriction.coarseSelected.family.tube parent) := by
      intro middle
      have middleFiberNonempty :=
        scaleData.cover.fullFiber_nonempty_of_uniform
          sourceNonempty scaleData.full_fiber_uniform middle
      rcases middleFiberNonempty with ⟨source, sourceMem⟩
      have sourceParent :
          scaleData.cover.parent source = middle :=
        (scaleData.cover.mem_fullFiber_iff_parent_eq
          scaleData.rho_pos.le middle source).mp sourceMem
      have fineToMiddle := fineMiddle source
      rw [sourceParent] at fineToMiddle
      have fineToAnchor := sourceCovered source
      have triangle :=
        wz1PaperLineDistance_triangle
          (scaleData.coarse.tube middle)
          (sourceFamily.family.tube source)
          (restriction.coarseSelected.family.tube parent)
      have symmetry :
          wz1PaperLineDistance
              (scaleData.coarse.tube middle)
              (sourceFamily.family.tube source) =
            wz1PaperLineDistance
              (sourceFamily.family.tube source)
              (scaleData.coarse.tube middle) :=
        wz1PaperLineDistance_symm _ _
      rw [symmetry] at triangle
      unfold WZ1PaperTubeCovers at fineToMiddle fineToAnchor
      unfold WZ2PaperDilatedTubeCovers
      nlinarith
    have middleSeparated :
        ∀ first second, first ≠ second →
          wz2PaperLiteralSourceSeparationFactor *
                schedule.actualScale coordinate <
            wz1PaperLineDistance
              (scaleData.coarse.tube first)
              (scaleData.coarse.tube second) := by
      exact
        output.finalMetricFiberDescendantScaleData_coarse_separated
          coordinate packetBefore.le parent
          (output.finalOldScaleData_coarse_separated
            coordinates coordinate)
    have targetLocal :
        ∀ target,
          ‖wz2PaperTubeMidpoint
            ((wz2PaperLiteralOrdinaryRescaledFamily
              sourceFamily.family
              (restriction.coarseSelected.family.tube parent)
              output.metric.metricInput.rho_pos).tube target)‖ ≤ 3 := by
      intro target
      exact
        wz2PaperLiteralOrdinaryRescaledTube_midpoint_norm_le_three_of_boundedBase
          output.metric.metricInput.rho_pos rhoLeOne
          (sourceFamily.family.tube target)
          (restriction.coarseSelected.family.tube parent)
          (sourceLine target)
          (by
            rw [sourceFamily.tube_eq,
              restriction.fineSelected.tube_eq]
            exact fineBoundedBase
              (output.metric.mesh.complete.selectedFine.embedding
                (restriction.fineSelected.embedding
                  (sourceFamily.embedding target))))
          (sourceCovered target)
    have localization :
        WZ2PaperOrdinaryNestedTargetLocalization
          sourceFamily.family scaleData.coarse
          (restriction.coarseSelected.family.tube parent)
          output.metric.metricInput.rho_pos :=
      wz2PaperOrdinaryNestedTargetLocalization_of_sourceCovers
        (schedule.scaleData packetCoordinate).delta_pos
        scaleData.rho_pos output.metric.metricInput.rho_pos
        rhoLeOne sourceFamily.family scaleData.coarse
        (restriction.coarseSelected.family.tube parent)
        sourceLine middleLine anchorLine
        sourceCovered middleAnchor targetLocal
    exact
      Or.inl
        ⟨schedule.actualScale coordinate, scaleData,
          treeSafe, actualLeRho, requestedLe, within,
          middleLine, fineMiddle, middleAnchor,
          middleSeparated, localization⟩
  · exact Or.inr topWindow

/--
The complete ancestry-core construction supplies the canonical public
rescaling input for one final genuine metric fiber.  No post-final tube
selection occurs.
-/
noncomputable def finalMetricFiberRescalingInput
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (conflict :
      PureWZ2Prop62SourceConflictCoordinateData Color color)
    (rhoLeOne : rho ≤ 1)
    (scaleSeparation : 100 * delta ≤ rho)
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
    (fineBoundedBase : HasBoundedBase fine 4)
    (parent :
      Fin
        (output.ancestryAuxiliaryCore.metricRestriction
          |>.coarseSelected.family.card)) :
    PureWZ2Prop62MetricFiberRescalingInput
      output.ancestryAuxiliaryCore.metricRestriction.section6Cover
      parent output.finalMetricFiberRouteConstant := by
  let restriction := output.ancestryAuxiliaryCore.metricRestriction
  let sourceIndices :=
    wz2PaperFullFiberIndices
      restriction.fineSelected.family
      restriction.coarseSelected.family parent
  let sourceFamily := restriction.metricFiberSource parent
  let sourceEquiv :
      Fin sourceFamily.family.card ≃ sourceIndices :=
    (sourceIndices.orderIsoOfFin rfl).toEquiv
  have sourceLine : WZ1PaperIsLineClass sourceFamily.family :=
    restriction.section6Cover.fine_line_class.subfamily
      sourceFamily.toTubeSubfamily
  have sourceCovered :
      ∀ index,
        WZ1PaperTubeCovers
          (sourceFamily.family.tube index)
          (restriction.coarseSelected.family.tube parent) := by
    intro index
    rw [sourceFamily.tube_eq]
    exact
      (mem_wz2PaperFullFiberIndices_iff parent
        (sourceFamily.embedding index)).mp
        (Finset.orderEmbOfFin_mem sourceIndices rfl index)
  have targetLocality :
      ∀ index,
        ‖wz2PaperTubeMidpoint
          ((wz2PaperLiteralOrdinaryRescaledFamily
            sourceFamily.family
            (restriction.coarseSelected.family.tube parent)
            output.metric.metricInput.rho_pos).tube index)‖ ≤ 3 := by
    intro index
    exact
      wz2PaperLiteralOrdinaryRescaledTube_midpoint_norm_le_three_of_boundedBase
        output.metric.metricInput.rho_pos rhoLeOne
        (sourceFamily.family.tube index)
        (restriction.coarseSelected.family.tube parent)
        (sourceLine index)
        (by
          rw [sourceFamily.tube_eq,
            restriction.fineSelected.tube_eq]
          exact fineBoundedBase
            (output.metric.mesh.complete.selectedFine.embedding
              (restriction.fineSelected.embedding
                (sourceFamily.embedding index))))
        (sourceCovered index)
  exact
    {
      rho_pos := output.metric.metricInput.rho_pos
      rho_le_one := rhoLeOne
      delta_pos := (schedule.scaleData packetCoordinate).delta_pos
      scale_separation := scaleSeparation
      sourceIndices := sourceIndices
      sourceIndices_eq := rfl
      sourceIndices_nonempty := by
        rcases restriction.section6Cover.parent_hit parent with
          ⟨source, covered⟩
        exact
          ⟨source,
            (mem_wz2PaperFullFiberIndices_iff parent source).mpr
              covered⟩
      sourceFamily := sourceFamily.family
      sourceEquiv := sourceEquiv
      source_tube_eq := by
        intro index
        rfl
      source_line_class := sourceLine
      anchor_line_class :=
        restriction.section6Cover.coarse_line_class parent
      source_covered := sourceCovered
      source_strongly_separated := by
        intro first second indexNe
        rw [sourceFamily.tube_eq, sourceFamily.tube_eq]
        exact
          output.finalFine_stronglySeparated conflict
            (sourceFamily.embedding first)
            (sourceFamily.embedding second)
            (sourceFamily.embedding.injective.ne indexNe)
      source_constant_finite :=
        output.finalMetricFiberRouteConstant_finite
      target_locality := targetLocality
      rescaled_physical_cwa :=
        output.finalMetricFiberRescaledPhysicalCWA
          rhoLeOne widthPos packetScaleLeRho sixWidthLe
          allAncestryCoordinatesUpper parent
      requested_route :=
        output.finalMetricFiberCanonicalRequestedRoute
          coordinates rhoLeOne scaleSeparation packetScaleLeRho
          fineBoundedBase parent
    }

/-- Public nearby-scale pure CWA on the canonical ordinary rescaled family. -/
theorem finalMetricFiberPublicPureCWA
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (conflict :
      PureWZ2Prop62SourceConflictCoordinateData Color color)
    (rhoLeOne : rho ≤ 1)
    (scaleSeparation : 100 * delta ≤ rho)
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
    (fineBoundedBase : HasBoundedBase fine 4)
    (parent :
      Fin
        (output.ancestryAuxiliaryCore.metricRestriction
          |>.coarseSelected.family.card)) :
    WZ2PaperPureCWAAtNearbyScales
      (output.finalMetricFiberRescalingInput
        coordinates conflict rhoLeOne scaleSeparation
        widthPos packetScaleLeRho sixWidthLe
        allAncestryCoordinatesUpper fineBoundedBase parent
        |>.certificate.publicFamily)
      ((81000000 : ENNReal) *
        output.finalMetricFiberRouteConstant) :=
  (output.finalMetricFiberRescalingInput
    coordinates conflict rhoLeOne scaleSeparation
    widthPos packetScaleLeRho sixWidthLe
    allAncestryCoordinatesUpper fineBoundedBase parent).publicPureCWA

/--
At every normalized requested scale, either one exact old descendant witness
survives on the final metric fiber or the rescaled top window applies.
-/
theorem finalMetricFiber_requested_descendant_or_top
    (rhoLeOne : rho ≤ 1)
    (scaleSeparation : 100 * delta ≤ rho)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sourceConstant : ENNReal)
    (sourceConstantFinite :
      WZ2PaperFiniteErrorConstant sourceConstant)
    (coreConstantLe :
      output.finalCoreConstant ≤ sourceConstant)
    (windowAbsorption :
      (100 : ENNReal) * scaleWindow ≤
        (81000000 : ENNReal) * sourceConstant)
    (topGate :
      (4 : ENNReal) *
          ((100 : ENNReal) * scaleWindow *
            ENNReal.ofReal rho) ≤
        ((81000000 : ENNReal) * sourceConstant) *
          ENNReal.ofReal
            (schedule.actualScale packetCoordinate))
    (parent :
      Fin
        (output.ancestryAuxiliaryCore.metricRestriction
          |>.coarseSelected.family.card)) :
    ∀ requested : WZ2PaperRequestedScale (delta / rho),
      (∃ (coordinate : Fin schedule.levelCount)
          (scaleData :
            WZ2PaperPureScaleCoverData
              ((output.ancestryAuxiliaryCore.metricRestriction
                |>.metricFiberSource parent).family)
              (schedule.actualScale coordinate)
              sourceConstant),
        packetCoordinate.val < coordinate.val ∧
          100 * delta ≤ schedule.actualScale coordinate ∧
          schedule.actualScale coordinate ≤ rho ∧
          requested.1 ≤ schedule.actualScale coordinate / rho ∧
          ENNReal.ofReal
              (schedule.actualScale coordinate / rho) <
            ((81000000 : ENNReal) * sourceConstant) *
              ENNReal.ofReal requested.1) ∨
      (4 : ENNReal) <
        ((81000000 : ENNReal) * sourceConstant) *
          ENNReal.ofReal requested.1 := by
  intro requested
  rcases
      schedule.requested_descendant_or_top
        packetCoordinate output.metric.metricInput.rho_pos
        rhoLeOne scaleSeparation packetScaleLeRho
        sourceConstant sourceConstantFinite
        windowAbsorption topGate requested
    with descendant | topWindow
  · rcases descendant with
      ⟨coordinate, packetBefore, treeSafe, actualLeRho,
        requestedLe, within⟩
    let scaleData :=
      (output.finalMetricFiberDescendantScaleData
        coordinate packetBefore.le parent).mono coreConstantLe
    exact
      Or.inl
        ⟨coordinate, scaleData, packetBefore, treeSafe,
          actualLeRho, requestedLe, within⟩
  · exact Or.inr topWindow

/--
Canonical requested-scale dichotomy with all finite numerical losses absorbed
into `finalMetricFiberRouteConstant`.
-/
theorem finalMetricFiber_canonical_requested_descendant_or_top
    (rhoLeOne : rho ≤ 1)
    (scaleSeparation : 100 * delta ≤ rho)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (parent :
      Fin
        (output.ancestryAuxiliaryCore.metricRestriction
          |>.coarseSelected.family.card)) :
    ∀ requested : WZ2PaperRequestedScale (delta / rho),
      (∃ (coordinate : Fin schedule.levelCount)
          (scaleData :
            WZ2PaperPureScaleCoverData
              ((output.ancestryAuxiliaryCore.metricRestriction
                |>.metricFiberSource parent).family)
              (schedule.actualScale coordinate)
              output.finalMetricFiberRouteConstant),
        packetCoordinate.val < coordinate.val ∧
          100 * delta ≤ schedule.actualScale coordinate ∧
          schedule.actualScale coordinate ≤ rho ∧
          requested.1 ≤ schedule.actualScale coordinate / rho ∧
          ENNReal.ofReal
              (schedule.actualScale coordinate / rho) <
            ((81000000 : ENNReal) *
              output.finalMetricFiberRouteConstant) *
              ENNReal.ofReal requested.1) ∨
      (4 : ENNReal) <
        ((81000000 : ENNReal) *
          output.finalMetricFiberRouteConstant) *
          ENNReal.ofReal requested.1 :=
  output.finalMetricFiber_requested_descendant_or_top
    rhoLeOne scaleSeparation packetScaleLeRho
    output.finalMetricFiberRouteConstant
    output.finalMetricFiberRouteConstant_finite
    output.finalCoreConstant_le_finalMetricFiberRouteConstant
    output.finalMetricFiberRouteConstant_windowAbsorption
    output.finalMetricFiberRouteConstant_topGate
    parent

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end
