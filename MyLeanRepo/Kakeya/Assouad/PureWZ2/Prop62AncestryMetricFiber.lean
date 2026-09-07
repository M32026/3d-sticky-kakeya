import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryMetricPreliminaryAssembly

/-!
# Proposition 6.2: complete-ancestry auxiliary fibers are metric fibers

On the one preliminary leaf set, each occupied packet cell carries exactly
one complete upper ancestry vector.  Hence equality of complete-ancestry
labels is equivalent to equality of the metric parent assigned by the
four-dimensional line mesh.
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

theorem packetHull_label_eq_iff_metricParent_eq
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
    (first second : Fin output.metric.selectedFine.card) :
    schedule.completeAncestryLabel packetCoordinate
          (schedule.packetLineCell packetCoordinate width)
          (output.metric.mesh.complete.selectedFine.embedding first) =
        schedule.completeAncestryLabel packetCoordinate
          (schedule.packetLineCell packetCoordinate width)
          (output.metric.mesh.complete.selectedFine.embedding second) ↔
      output.metric.metricInput.packetParent
            (output.metric.mesh.restrictedOldData.cover.parent first) =
        output.metric.metricInput.packetParent
          (output.metric.mesh.restrictedOldData.cover.parent second) := by
  have firstPerCell :
      output.metric.mesh.complete.selectedFine.embedding first ∈
        preliminary.perCell.selected := by
    rw [← output.packet_hull_eq_perCell]
    exact
      output.metric.mesh.complete.selectedFine_embedding_mem first
  have secondPerCell :
      output.metric.mesh.complete.selectedFine.embedding second ∈
        preliminary.perCell.selected := by
    rw [← output.packet_hull_eq_perCell]
    exact
      output.metric.mesh.complete.selectedFine_embedding_mem second
  constructor
  · intro labelEq
    have cellEq :
        schedule.packetLineCell packetCoordinate width
            (output.metric.mesh.complete.selectedFine.embedding first) =
          schedule.packetLineCell packetCoordinate width
            (output.metric.mesh.complete.selectedFine.embedding second) :=
      congrArg (fun label => label.1.1) labelEq
    exact
      (output.metricParent_eq_iff_packetLineCell_embedding_eq
        first second).mpr cellEq
  · intro parentEq
    have cellEq :=
      (output.metricParent_eq_iff_packetLineCell_embedding_eq
        first second).mp parentEq
    have upperAncestryEq :=
      preliminary.perCell_selected_upperAncestry_eq_of_sameCell
        rhoPos widthPos packetScaleLeRho sixWidthLe parentCovers
        (output.metric.mesh.complete.selectedFine.embedding first)
        (output.metric.mesh.complete.selectedFine.embedding second)
        firstPerCell secondPerCell
        cellEq
    have ancestryEq :=
      schedule.ancestry_eq_of_upperAncestry_eq
        rho packetCoordinate allAncestryCoordinatesUpper
        (output.metric.mesh.complete.selectedFine.embedding first)
        (output.metric.mesh.complete.selectedFine.embedding second)
        upperAncestryEq
    exact
      Prod.ext
        (by
          apply Subtype.ext
          exact cellEq)
        ancestryEq

theorem selected_label_eq_iff_metricParent_eq
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
    (first second : Fin output.metric.selectedFine.card)
    (firstMem : first ∈ output.selectedPreliminary)
    (secondMem : second ∈ output.selectedPreliminary) :
    schedule.completeAncestryLabel packetCoordinate
          (schedule.packetLineCell packetCoordinate width)
          (output.metric.mesh.complete.selectedFine.embedding first) =
        schedule.completeAncestryLabel packetCoordinate
          (schedule.packetLineCell packetCoordinate width)
          (output.metric.mesh.complete.selectedFine.embedding second) ↔
      output.metric.metricInput.packetParent
            (output.metric.mesh.restrictedOldData.cover.parent first) =
        output.metric.metricInput.packetParent
          (output.metric.mesh.restrictedOldData.cover.parent second) := by
  exact
    output.packetHull_label_eq_iff_metricParent_eq
      rhoPos widthPos packetScaleLeRho sixWidthLe parentCovers
      allAncestryCoordinatesUpper first second

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end
