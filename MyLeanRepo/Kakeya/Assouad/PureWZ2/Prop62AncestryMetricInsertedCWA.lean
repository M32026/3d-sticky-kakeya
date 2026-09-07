import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryMetricCoreQuantitative

/-!
# Proposition 6.2: inserted metric-fiber CWA after the ancestry core

The final core is a subset of the preliminary complete metric fiber.  Bound
its convex contained count by the pre-core inserted CWA, then replace the
pre-core fiber cardinality by the exact ancestry-core density bound.
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

theorem insertedCWA_after_ancestryCore
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
    (parent : Fin output.metric.metricParents.card)
    (coreFiberNonempty :
      (output.ancestryAuxiliaryCore.pullback.pulledBack ∩
        wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents parent).Nonempty)
    (convexSet : Set Point3)
    (convex : Convex ℝ convexSet) :
    ((((output.ancestryAuxiliaryCore.pullback.pulledBack ∩
        wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents parent).filter
        fun source =>
          wz2PaperLiteralUnitRescalingMap
              (output.metric.metricParents.tube parent)
              output.metric.metricInput.rho_pos ''
            (output.metric.selectedFine.tube source).carrier ⊆
              convexSet).card : ENNReal)) ≤
      (pureWZ2Prop62InsertedCWALoss
          rho (schedule.actualScale packetCoordinate) ambientConstant *
        output.ancestryDensityLoss) *
        volume convexSet *
        (((output.ancestryAuxiliaryCore.pullback.pulledBack ∩
          wz2PaperFullFiberIndices
            output.metric.selectedFine
            output.metric.metricParents parent).card : ENNReal)) := by
  let metricFiber :=
    wz2PaperFullFiberIndices
      output.metric.selectedFine output.metric.metricParents parent
  let predicate : Fin output.metric.selectedFine.card → Prop :=
    fun source =>
      wz2PaperLiteralUnitRescalingMap
          (output.metric.metricParents.tube parent)
          output.metric.metricInput.rho_pos ''
        (output.metric.selectedFine.tube source).carrier ⊆ convexSet
  have filteredSubset :
      (output.ancestryAuxiliaryCore.pullback.pulledBack ∩
          metricFiber).filter predicate ⊆
        metricFiber.filter predicate := by
    intro source sourceMem
    have sourceData := Finset.mem_filter.mp sourceMem
    exact
      Finset.mem_filter.mpr
        ⟨(Finset.mem_inter.mp sourceData.1).2, sourceData.2⟩
  have filteredLe :
      ((((output.ancestryAuxiliaryCore.pullback.pulledBack ∩
          metricFiber).filter predicate).card : ENNReal)) ≤
        (((metricFiber.filter predicate).card : ENNReal)) := by
    exact_mod_cast Finset.card_le_card filteredSubset
  have ambientCWA :
      (((metricFiber.filter predicate).card : ENNReal)) ≤
        pureWZ2Prop62InsertedCWALoss
            rho (schedule.actualScale packetCoordinate) ambientConstant *
          volume convexSet *
          (metricFiber.card : ENNReal) := by
    exact output.metric.insertedFiberCWA parent convexSet convex
  have fiberDensity :=
    output.metricFiber_le_ancestryDensityLoss_core
      rhoPos widthPos packetScaleLeRho sixWidthLe parentCovers
      allAncestryCoordinatesUpper parent coreFiberNonempty
  calc
    ((((output.ancestryAuxiliaryCore.pullback.pulledBack ∩
        metricFiber).filter predicate).card : ENNReal)) ≤
        (((metricFiber.filter predicate).card : ENNReal)) :=
      filteredLe
    _ ≤
        pureWZ2Prop62InsertedCWALoss
            rho (schedule.actualScale packetCoordinate) ambientConstant *
          volume convexSet *
          (metricFiber.card : ENNReal) :=
      ambientCWA
    _ ≤
        pureWZ2Prop62InsertedCWALoss
            rho (schedule.actualScale packetCoordinate) ambientConstant *
          volume convexSet *
          (output.ancestryDensityLoss *
            ((output.ancestryAuxiliaryCore.pullback.pulledBack ∩
              metricFiber).card : ENNReal)) := by
      gcongr
    _ =
        (pureWZ2Prop62InsertedCWALoss
            rho (schedule.actualScale packetCoordinate) ambientConstant *
          output.ancestryDensityLoss) *
          volume convexSet *
          ((output.ancestryAuxiliaryCore.pullback.pulledBack ∩
            metricFiber).card : ENNReal) := by
      ring

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end
