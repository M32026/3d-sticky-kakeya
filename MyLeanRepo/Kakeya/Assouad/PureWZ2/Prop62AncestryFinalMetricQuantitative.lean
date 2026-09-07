import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryMetricInsertedCWA

/-!
# Proposition 6.2: final metric-fiber quantitative outputs

Transport the ancestry-core inserted CWA and cardinality uniformity through
the final Section 6 hit-parent restriction.  The fiber image is exact, so this
step introduces no additional loss.
-/

noncomputable section

namespace Kakeya.Assouad

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

abbrev finalMetricRestriction :=
  output.ancestryAuxiliaryCore.metricRestriction

theorem finalAmbientCoreFiber_nonempty
    (parent :
      Fin output.finalMetricRestriction.coarseSelected.family.card) :
    (output.ancestryAuxiliaryCore.pullback.pulledBack ∩
      wz2PaperFullFiberIndices
        output.metric.selectedFine
        output.metric.metricParents
        (output.finalMetricRestriction.coarseSelected.embedding parent)
      ).Nonempty := by
  let restriction := output.finalMetricRestriction
  rcases restriction.lineCover.parent_surjective parent with
    ⟨source, parentEq⟩
  have sourceFiber :
      source ∈
        wz2PaperFullFiberIndices
          restriction.fineSelected.family
          restriction.coarseSelected.family parent :=
    (mem_wz2PaperFullFiberIndices_iff parent source).mpr <| by
      rw [← parentEq]
      exact restriction.lineCover.parent_covers source
  rw [← restriction.fiber_image_eq parent]
  exact
    ⟨restriction.fineSelected.embedding source,
      Finset.mem_image.mpr
        ⟨source, sourceFiber, rfl⟩⟩

theorem finalFullFiber_uniform
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
    (baseConstant : ENNReal)
    (ambientUniform :
      ∀ first second,
        ((wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents first).card : ENNReal) ≤
          baseConstant *
            ((wz2PaperFullFiberIndices
              output.metric.selectedFine
              output.metric.metricParents second).card : ENNReal)) :
    ∀ first second,
      ((wz2PaperFullFiberIndices
        output.finalMetricRestriction.fineSelected.family
        output.finalMetricRestriction.coarseSelected.family first).card :
          ENNReal) ≤
        (baseConstant * output.ancestryDensityLoss) *
          ((wz2PaperFullFiberIndices
            output.finalMetricRestriction.fineSelected.family
            output.finalMetricRestriction.coarseSelected.family second).card :
              ENNReal) := by
  intro first second
  let restriction := output.finalMetricRestriction
  have firstCard :
      (wz2PaperFullFiberIndices
        restriction.fineSelected.family
        restriction.coarseSelected.family first).card =
      (output.ancestryAuxiliaryCore.pullback.pulledBack ∩
        wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents
          (restriction.coarseSelected.embedding first)).card := by
    rw [← restriction.fiber_image_eq first]
    exact
      (Finset.card_image_of_injective _
        restriction.fineSelected.embedding.injective).symm
  have secondCard :
      (wz2PaperFullFiberIndices
        restriction.fineSelected.family
        restriction.coarseSelected.family second).card =
      (output.ancestryAuxiliaryCore.pullback.pulledBack ∩
        wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents
          (restriction.coarseSelected.embedding second)).card := by
    rw [← restriction.fiber_image_eq second]
    exact
      (Finset.card_image_of_injective _
        restriction.fineSelected.embedding.injective).symm
  rw [firstCard, secondCard]
  exact
    output.metricFiber_uniform_after_ancestryCore
      rhoPos widthPos packetScaleLeRho sixWidthLe parentCovers
      allAncestryCoordinatesUpper baseConstant ambientUniform
      (restriction.coarseSelected.embedding first)
      (restriction.coarseSelected.embedding second)
      (output.finalAmbientCoreFiber_nonempty second)

theorem finalInsertedFiberCWA
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
      Fin output.finalMetricRestriction.coarseSelected.family.card)
    (convexSet : Set Point3)
    (convex : Convex ℝ convexSet) :
    (((wz2PaperFullFiberIndices
        output.finalMetricRestriction.fineSelected.family
        output.finalMetricRestriction.coarseSelected.family parent).filter
        fun source =>
          wz2PaperLiteralUnitRescalingMap
              (output.finalMetricRestriction.coarseSelected.family.tube parent)
              output.metric.metricInput.rho_pos ''
            (output.finalMetricRestriction.fineSelected.family.tube source).carrier ⊆
              convexSet).card : ENNReal) ≤
      (pureWZ2Prop62InsertedCWALoss
          rho (schedule.actualScale packetCoordinate) ambientConstant *
        output.ancestryDensityLoss) *
        volume convexSet *
        ((wz2PaperFullFiberIndices
          output.finalMetricRestriction.fineSelected.family
          output.finalMetricRestriction.coarseSelected.family parent).card :
          ENNReal) := by
  let restriction := output.finalMetricRestriction
  let finalFiber :=
    wz2PaperFullFiberIndices
      restriction.fineSelected.family
      restriction.coarseSelected.family parent
  let ambientParent := restriction.coarseSelected.embedding parent
  let ambientFiber :=
    output.ancestryAuxiliaryCore.pullback.pulledBack ∩
      wz2PaperFullFiberIndices
        output.metric.selectedFine output.metric.metricParents ambientParent
  have fiberImageEq :
      Finset.image restriction.fineSelected.embedding finalFiber =
        ambientFiber := by
    simpa only [finalFiber, ambientFiber, ambientParent] using
      restriction.fiber_image_eq parent
  let finalPredicate :
      Fin restriction.fineSelected.family.card → Prop :=
    fun source =>
      wz2PaperLiteralUnitRescalingMap
          (restriction.coarseSelected.family.tube parent)
          output.metric.metricInput.rho_pos ''
        (restriction.fineSelected.family.tube source).carrier ⊆ convexSet
  let ambientPredicate : Fin output.metric.selectedFine.card → Prop :=
    fun source =>
      wz2PaperLiteralUnitRescalingMap
          (output.metric.metricParents.tube ambientParent)
          output.metric.metricInput.rho_pos ''
        (output.metric.selectedFine.tube source).carrier ⊆ convexSet
  have predicateCompatibility :
      ∀ source,
        finalPredicate source =
          ambientPredicate (restriction.fineSelected.embedding source) := by
    intro source
    apply propext
    simp only [finalPredicate, ambientPredicate]
    rw [restriction.fineSelected.tube_eq,
      restriction.coarseSelected.tube_eq]
  have filteredImage :
      Finset.image restriction.fineSelected.embedding
          (finalFiber.filter finalPredicate) =
        ambientFiber.filter ambientPredicate := by
    ext ambientSource
    constructor
    · intro sourceImage
      rcases Finset.mem_image.mp sourceImage with
        ⟨source, sourceMem, rfl⟩
      have sourceData := Finset.mem_filter.mp sourceMem
      exact
        Finset.mem_filter.mpr
          ⟨by
            rw [← fiberImageEq]
            exact Finset.mem_image.mpr
              ⟨source, sourceData.1, rfl⟩,
           by
            rw [← predicateCompatibility source]
            exact sourceData.2⟩
    · intro ambientMem
      have ambientData := Finset.mem_filter.mp ambientMem
      have sourceImage : ambientSource ∈
          Finset.image restriction.fineSelected.embedding finalFiber := by
        rw [fiberImageEq]
        exact ambientData.1
      rcases Finset.mem_image.mp sourceImage with
        ⟨source, sourceFiber, sourceEq⟩
      exact
        Finset.mem_image.mpr
          ⟨source,
            Finset.mem_filter.mpr
              ⟨sourceFiber, by
                rw [predicateCompatibility source, sourceEq]
                exact ambientData.2⟩,
            sourceEq⟩
  have filteredCard :
      (finalFiber.filter finalPredicate).card =
        (ambientFiber.filter ambientPredicate).card := by
    rw [← filteredImage]
    exact
      (Finset.card_image_of_injective _
        restriction.fineSelected.embedding.injective).symm
  have fiberCard :
      finalFiber.card = ambientFiber.card := by
    rw [← fiberImageEq]
    exact
      (Finset.card_image_of_injective _
        restriction.fineSelected.embedding.injective).symm
  have ambientBound :=
    output.insertedCWA_after_ancestryCore
      rhoPos widthPos packetScaleLeRho sixWidthLe parentCovers
      allAncestryCoordinatesUpper ambientParent
      (output.finalAmbientCoreFiber_nonempty parent)
      convexSet convex
  change
    ((finalFiber.filter finalPredicate).card : ENNReal) ≤
      (pureWZ2Prop62InsertedCWALoss
          rho (schedule.actualScale packetCoordinate) ambientConstant *
        output.ancestryDensityLoss) *
        volume convexSet * (finalFiber.card : ENNReal)
  rw [filteredCard, fiberCard]
  exact ambientBound

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end
