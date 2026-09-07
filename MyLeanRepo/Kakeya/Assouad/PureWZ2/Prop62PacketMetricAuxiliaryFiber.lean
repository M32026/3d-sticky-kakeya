import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryAuxiliaryCoreAssembly

/-!
# Proposition 6.2: packet-hull auxiliary fibers are genuine metric fibers

Pull the complete-ancestry label from the ambient fine family to the complete
`s`-packet hull.  The global label/metric-parent equivalence proves that every
pulled-back auxiliary fiber is exactly one genuine Section 6 metric fiber.
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

/-- Complete-ancestry label pulled back to the packet hull. -/
def packetLabel
    (source : Fin output.metric.selectedFine.card) :
    schedule.CompleteAncestryLabel packetCoordinate
      (schedule.packetLineCell packetCoordinate width) :=
  schedule.completeAncestryLabel packetCoordinate
    (schedule.packetLineCell packetCoordinate width)
    (output.metric.mesh.complete.selectedFine.embedding source)

/-- Packet-hull fiber of one complete-ancestry label. -/
def packetAuxiliaryFiber
    (label :
      schedule.CompleteAncestryLabel packetCoordinate
        (schedule.packetLineCell packetCoordinate width)) :
    Finset (Fin output.metric.selectedFine.card) :=
  Finset.univ.filter fun source =>
    output.packetLabel source = label

/-- Every preliminary metric parent has a nonempty genuine metric fiber. -/
theorem metricFiber_nonempty
    (parent : Fin output.metric.metricParents.card) :
    (wz2PaperFullFiberIndices
      output.metric.selectedFine
      output.metric.metricParents parent).Nonempty := by
  rcases output.metric.section6Cover.parent_hit parent with
    ⟨source, sourceCovered⟩
  exact
    ⟨source,
      (mem_wz2PaperFullFiberIndices_iff parent source).mpr
        sourceCovered⟩

/-- Canonical fine representative of one genuine metric fiber. -/
noncomputable def metricFiberRepresentative
    (parent : Fin output.metric.metricParents.card) :
    Fin output.metric.selectedFine.card :=
  Classical.choose (output.metricFiber_nonempty parent)

theorem metricFiberRepresentative_mem
    (parent : Fin output.metric.metricParents.card) :
    output.metricFiberRepresentative parent ∈
      wz2PaperFullFiberIndices
        output.metric.selectedFine
        output.metric.metricParents parent :=
  Classical.choose_spec (output.metricFiber_nonempty parent)

theorem metricFiberRepresentative_parent
    (parent : Fin output.metric.metricParents.card) :
    output.metric.metricInput.packetParent
        (output.metric.mesh.restrictedOldData.cover.parent
          (output.metricFiberRepresentative parent)) =
      parent := by
  have representativeMem :=
    output.metricFiberRepresentative_mem parent
  rw [output.metric.metricFiber_eq_assignedPackets parent] at representativeMem
  exact
    (Finset.mem_filter.mp
      representativeMem).2

/-- Complete-ancestry label canonically attached to one metric parent. -/
def metricParentLabel
    (parent : Fin output.metric.metricParents.card) :
    schedule.CompleteAncestryLabel packetCoordinate
      (schedule.packetLineCell packetCoordinate width) :=
  output.packetLabel (output.metricFiberRepresentative parent)

theorem packetAuxiliaryFiber_eq_metricFiber
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
    (representative : Fin output.metric.selectedFine.card)
    (representativeParent :
      output.metric.metricInput.packetParent
          (output.metric.mesh.restrictedOldData.cover.parent representative) =
        parent) :
    output.packetAuxiliaryFiber
        (output.packetLabel representative) =
      wz2PaperFullFiberIndices
        output.metric.selectedFine
        output.metric.metricParents parent := by
  rw [output.metric.metricFiber_eq_assignedPackets parent]
  ext source
  simp only [packetAuxiliaryFiber, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change
    schedule.completeAncestryLabel packetCoordinate
          (schedule.packetLineCell packetCoordinate width)
          (output.metric.mesh.complete.selectedFine.embedding source) =
        schedule.completeAncestryLabel packetCoordinate
          (schedule.packetLineCell packetCoordinate width)
          (output.metric.mesh.complete.selectedFine.embedding
            representative) ↔
      output.metric.metricInput.packetParent
          (output.metric.mesh.restrictedOldData.cover.parent source) =
        parent
  rw [
    output.packetHull_label_eq_iff_metricParent_eq
      rhoPos widthPos packetScaleLeRho sixWidthLe parentCovers
      allAncestryCoordinatesUpper source representative,
    representativeParent
  ]

theorem packetAuxiliaryFiber_metricParentLabel_eq_metricFiber
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
    (parent : Fin output.metric.metricParents.card) :
    output.packetAuxiliaryFiber (output.metricParentLabel parent) =
      wz2PaperFullFiberIndices
        output.metric.selectedFine
        output.metric.metricParents parent :=
  output.packetAuxiliaryFiber_eq_metricFiber
    rhoPos widthPos packetScaleLeRho sixWidthLe parentCovers
    allAncestryCoordinatesUpper parent
    (output.metricFiberRepresentative parent)
    (output.metricFiberRepresentative_parent parent)

theorem ambientAuxiliaryFiber_subset_packetHull
    (representative : Fin output.metric.selectedFine.card) :
    output.ancestryAuxiliary.auxiliaryFiber
        (output.packetLabel representative) ⊆
      output.metric.mesh.complete.selectedFineIndices := by
  intro ambientSource sourceFiber
  have labelEq :
      schedule.completeAncestryLabel packetCoordinate
            (schedule.packetLineCell packetCoordinate width) ambientSource =
        schedule.completeAncestryLabel packetCoordinate
          (schedule.packetLineCell packetCoordinate width)
          (output.metric.mesh.complete.selectedFine.embedding
            representative) := by
    rw [PureWZ2Prop62AuxiliaryLevel.auxiliaryFiber] at sourceFiber
    simpa only [
      Finset.mem_filter, Finset.mem_univ, true_and,
      output.ancestryAuxiliary_label,
      packetLabel
    ] using sourceFiber
  have representativePerCell :
      output.metric.mesh.complete.selectedFine.embedding representative ∈
        preliminary.perCell.selected := by
    rw [← output.packet_hull_eq_perCell]
    exact
      output.metric.mesh.complete.selectedFine_embedding_mem representative
  have sourcePerCell :
      ambientSource ∈ preliminary.perCell.selected :=
    (preliminary.perCell_mem_iff_of_completeAncestryLabel_eq
      ambientSource
      (output.metric.mesh.complete.selectedFine.embedding representative)
      labelEq).mpr representativePerCell
  rwa [output.packet_hull_eq_perCell]

theorem packetAuxiliaryFiber_image_eq_ambientAuxiliaryFiber
    (representative : Fin output.metric.selectedFine.card) :
    Finset.image output.metric.mesh.complete.selectedFine.embedding
        (output.packetAuxiliaryFiber
          (output.packetLabel representative)) =
      output.ancestryAuxiliary.auxiliaryFiber
        (output.packetLabel representative) := by
  ext ambientSource
  constructor
  · intro sourceImage
    rcases Finset.mem_image.mp sourceImage with
      ⟨source, sourceMem, sourceEq⟩
    rw [PureWZ2Prop62AuxiliaryLevel.auxiliaryFiber]
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ ambientSource, ?_⟩
    change
      schedule.completeAncestryLabel packetCoordinate
          (schedule.packetLineCell packetCoordinate width) ambientSource =
        output.packetLabel representative
    rw [← sourceEq]
    exact (Finset.mem_filter.mp sourceMem).2
  · intro sourceFiber
    have sourceHull :=
      output.ambientAuxiliaryFiber_subset_packetHull
        representative sourceFiber
    rcases
        output.metric.mesh.complete.selectedFine_ambient_surjective
          ambientSource sourceHull
      with
      ⟨source, sourceEq⟩
    refine Finset.mem_image.mpr
      ⟨source, ?_, sourceEq⟩
    rw [packetAuxiliaryFiber]
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ source, ?_⟩
    change
      schedule.completeAncestryLabel packetCoordinate
          (schedule.packetLineCell packetCoordinate width)
          (output.metric.mesh.complete.selectedFine.embedding source) =
        output.packetLabel representative
    rw [sourceEq]
    rw [PureWZ2Prop62AuxiliaryLevel.auxiliaryFiber] at sourceFiber
    simpa only [
      Finset.mem_filter, Finset.mem_univ, true_and,
      output.ancestryAuxiliary_label
    ] using sourceFiber

theorem packetAuxiliaryFiber_metricParentLabel_image_eq
    (parent : Fin output.metric.metricParents.card) :
    Finset.image output.metric.mesh.complete.selectedFine.embedding
        (output.packetAuxiliaryFiber
          (output.metricParentLabel parent)) =
      output.ancestryAuxiliary.auxiliaryFiber
        (output.metricParentLabel parent) :=
  output.packetAuxiliaryFiber_image_eq_ambientAuxiliaryFiber
    (output.metricFiberRepresentative parent)

theorem coreMetricFiber_image_eq_ambientCoreAuxiliaryFiber
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
    (parent : Fin output.metric.metricParents.card) :
    Finset.image output.metric.mesh.complete.selectedFine.embedding
        (output.ancestryAuxiliaryCore.pullback.pulledBack ∩
          wz2PaperFullFiberIndices
            output.metric.selectedFine
            output.metric.metricParents parent) =
      output.ancestryAuxiliaryCore.ambientCore ∩
        output.ancestryAuxiliary.auxiliaryFiber
          (output.metricParentLabel parent) := by
  have packetFiberEq :
      output.packetAuxiliaryFiber (output.metricParentLabel parent) =
        wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents parent :=
    output.packetAuxiliaryFiber_metricParentLabel_eq_metricFiber
      rhoPos widthPos packetScaleLeRho sixWidthLe parentCovers
      allAncestryCoordinatesUpper parent
  have packetImageEq :
      Finset.image output.metric.mesh.complete.selectedFine.embedding
          (output.packetAuxiliaryFiber
            (output.metricParentLabel parent)) =
        output.ancestryAuxiliary.auxiliaryFiber
          (output.metricParentLabel parent) :=
    output.packetAuxiliaryFiber_metricParentLabel_image_eq parent
  ext ambientSource
  constructor
  · intro sourceImage
    rcases Finset.mem_image.mp sourceImage with
      ⟨source, sourceMem, sourceEq⟩
    have sourceData := Finset.mem_inter.mp sourceMem
    apply Finset.mem_inter.mpr
    constructor
    · rw [← output.ancestryAuxiliaryCore.pullback.image_eq]
      exact
        Finset.mem_image.mpr
          ⟨source, sourceData.1, sourceEq⟩
    · rw [← packetImageEq]
      exact
        Finset.mem_image.mpr
          ⟨source, by
            rw [packetFiberEq]
            exact sourceData.2,
            sourceEq⟩
  · intro ambientMem
    have ambientData := Finset.mem_inter.mp ambientMem
    have coreImage :
        ambientSource ∈
          Finset.image
            output.metric.mesh.complete.selectedFine.embedding
            output.ancestryAuxiliaryCore.pullback.pulledBack := by
      rw [output.ancestryAuxiliaryCore.pullback.image_eq]
      exact ambientData.1
    rcases Finset.mem_image.mp coreImage with
      ⟨coreSource, coreSourceMem, coreSourceEq⟩
    have fiberImage :
        ambientSource ∈
          Finset.image
            output.metric.mesh.complete.selectedFine.embedding
            (output.packetAuxiliaryFiber
              (output.metricParentLabel parent)) := by
      rw [packetImageEq]
      exact ambientData.2
    rcases Finset.mem_image.mp fiberImage with
      ⟨fiberSource, fiberSourceMem, fiberSourceEq⟩
    have sourceEq : coreSource = fiberSource := by
      apply output.metric.mesh.complete.selectedFine.embedding.injective
      exact coreSourceEq.trans fiberSourceEq.symm
    refine
      Finset.mem_image.mpr
        ⟨coreSource, Finset.mem_inter.mpr
          ⟨coreSourceMem, ?_⟩, coreSourceEq⟩
    rw [sourceEq, ← packetFiberEq]
    exact fiberSourceMem

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end
