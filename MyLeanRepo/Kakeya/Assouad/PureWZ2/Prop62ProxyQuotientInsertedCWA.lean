import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62InsertedCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientMetricCore

/-!
# Proposition 6.2 quotient-core inserted CWA

The inserted quotient label is exactly the genuine Section 6 metric-parent
label on the preliminary packet hull.  This module transports the one-pass
tree density estimate through that exact identification and through the final
hit-parent restriction.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62ProxyQuotientMetricCoreOutput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (output :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)

def quotientDensityLoss : ENNReal :=
  (2 ^ (schedule.levelCount + 1) : ENNReal) *
    fine.enncard *
    (output.cleanup.preliminary.card : ENNReal)⁻¹

def packetLabel
    (source : Fin output.metric.selectedFine.card) :
    PureWZ2Prop62ProxyQuotientAuxiliaryLabel
      schedule fineNonempty quotient rho width packetCoordinate :=
  output.cleanup.auxiliary.label
    (output.metric.mesh.complete.selectedFine.embedding source)

def packetAuxiliaryFiber
    (label :
      PureWZ2Prop62ProxyQuotientAuxiliaryLabel
        schedule fineNonempty quotient rho width packetCoordinate) :
    Finset (Fin output.metric.selectedFine.card) :=
  Finset.univ.filter fun source =>
    output.packetLabel source = label

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
    output.metric.section6Cover.toWZ1PaperTubeCover.parent
        (output.metricFiberRepresentative parent) =
      parent := by
  have representativeMem :=
    output.metricFiberRepresentative_mem parent
  exact
    (output.metric.section6Cover.toWZ1PaperTubeCover.parent_unique
      (output.metricFiberRepresentative parent) parent
      ((mem_wz2PaperFullFiberIndices_iff
        parent (output.metricFiberRepresentative parent)).mp
        representativeMem)).symm

def metricParentLabel
    (parent : Fin output.metric.metricParents.card) :
    PureWZ2Prop62ProxyQuotientAuxiliaryLabel
      schedule fineNonempty quotient rho width packetCoordinate :=
  output.packetLabel (output.metricFiberRepresentative parent)

theorem packetAuxiliaryFiber_eq_metricFiber
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (parent : Fin output.metric.metricParents.card) :
    output.packetAuxiliaryFiber (output.metricParentLabel parent) =
      wz2PaperFullFiberIndices
        output.metric.selectedFine
        output.metric.metricParents parent := by
  ext source
  simp only [packetAuxiliaryFiber, metricParentLabel,
    packetLabel, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [
    output.label_eq_iff_metricParent_eq
      fineLine fineBase rhoPos widthPos packetScaleLeRho
      sixWidthLe source
      (output.metricFiberRepresentative parent),
    output.metricFiberRepresentative_parent parent,
    mem_wz2PaperFullFiberIndices_iff
  ]
  constructor
  · intro parentEq
    rw [← parentEq]
    exact
      output.metric.section6Cover.toWZ1PaperTubeCover
        |>.parent_covers source
  · intro covered
    exact
      (output.metric.section6Cover.toWZ1PaperTubeCover
        |>.parent_unique source parent covered).symm

theorem ambientAuxiliaryFiber_subset_selection
    (parent : Fin output.metric.metricParents.card) :
    output.cleanup.auxiliary.auxiliaryFiber
        (output.metricParentLabel parent) ⊆
      output.cleanup.selection.selected := by
  intro ambientSource sourceFiber
  have labelEq :
      output.cleanup.auxiliary.label ambientSource =
        output.cleanup.auxiliary.label
          (output.metric.mesh.complete.selectedFine.embedding
            (output.metricFiberRepresentative parent)) := by
    exact (Finset.mem_filter.mp sourceFiber).2
  have representativeSelected :
      output.metric.mesh.complete.selectedFine.embedding
          (output.metricFiberRepresentative parent) ∈
        output.cleanup.selection.selected := by
    rw [output.selection_eq]
    exact output.selectedFine_embedding_mem_selection
      (output.metricFiberRepresentative parent)
  exact
    (output.cleanup.selection_mem_iff_of_auxiliary_label_eq
      ambientSource
      (output.metric.mesh.complete.selectedFine.embedding
        (output.metricFiberRepresentative parent))
      labelEq).2 representativeSelected

theorem packetAuxiliaryFiber_image_eq_ambientAuxiliaryFiber
    (parent : Fin output.metric.metricParents.card) :
    Finset.image output.metric.mesh.complete.selectedFine.embedding
        (output.packetAuxiliaryFiber
          (output.metricParentLabel parent)) =
      output.cleanup.auxiliary.auxiliaryFiber
        (output.metricParentLabel parent) := by
  ext ambientSource
  constructor
  · intro sourceImage
    rcases Finset.mem_image.mp sourceImage with
      ⟨source, sourceMem, sourceEq⟩
    rw [PureWZ2Prop62ProxyQuotientAuxiliaryLevel.auxiliaryFiber]
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ ambientSource, ?_⟩
    rw [← sourceEq]
    exact (Finset.mem_filter.mp sourceMem).2
  · intro sourceFiber
    have sourceSelected :
        ambientSource ∈ output.cleanup.selection.selected :=
      output.ambientAuxiliaryFiber_subset_selection parent sourceFiber
    have sourceHull :
        ambientSource ∈
          output.metric.mesh.complete.selectedFineIndices := by
      rw [output.metric.packet_hull_eq_selection,
        ← output.selection_eq]
      exact sourceSelected
    rcases
        output.metric.mesh.complete.selectedFine_ambient_surjective
          ambientSource sourceHull
      with ⟨source, sourceEq⟩
    refine Finset.mem_image.mpr
      ⟨source, ?_, sourceEq⟩
    rw [packetAuxiliaryFiber, Finset.mem_filter]
    refine ⟨Finset.mem_univ source, ?_⟩
    change
      output.cleanup.auxiliary.label
          (output.metric.mesh.complete.selectedFine.embedding source) =
        output.metricParentLabel parent
    rw [sourceEq]
    exact (Finset.mem_filter.mp sourceFiber).2

theorem metricFiber_image_eq_ambientAuxiliaryFiber
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (parent : Fin output.metric.metricParents.card) :
    Finset.image output.metric.mesh.complete.selectedFine.embedding
        (wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents parent) =
      output.cleanup.auxiliary.auxiliaryFiber
        (output.metricParentLabel parent) := by
  rw [← output.packetAuxiliaryFiber_eq_metricFiber
    fineLine fineBase rhoPos widthPos packetScaleLeRho
    sixWidthLe parent]
  exact output.packetAuxiliaryFiber_image_eq_ambientAuxiliaryFiber parent

theorem coreMetricFiber_image_eq_ambientCoreAuxiliaryFiber
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (parent : Fin output.metric.metricParents.card) :
    Finset.image output.metric.mesh.complete.selectedFine.embedding
        (output.pulledBack ∩
          wz2PaperFullFiberIndices
            output.metric.selectedFine
            output.metric.metricParents parent) =
      output.cleanup.core.core ∩
        output.cleanup.auxiliary.auxiliaryFiber
          (output.metricParentLabel parent) := by
  have fiberImageEq :=
    output.metricFiber_image_eq_ambientAuxiliaryFiber
      fineLine fineBase rhoPos widthPos packetScaleLeRho
      sixWidthLe parent
  ext ambientSource
  constructor
  · intro sourceImage
    rcases Finset.mem_image.mp sourceImage with
      ⟨source, sourceMem, sourceEq⟩
    have sourceData := Finset.mem_inter.mp sourceMem
    apply Finset.mem_inter.mpr
    constructor
    · rw [← output.ambientCore_eq, ← output.image_eq]
      exact Finset.mem_image.mpr
        ⟨source, sourceData.1, sourceEq⟩
    · rw [← fiberImageEq]
      exact Finset.mem_image.mpr
        ⟨source, sourceData.2, sourceEq⟩
  · intro ambientMem
    have ambientData := Finset.mem_inter.mp ambientMem
    have coreImage :
        ambientSource ∈
          Finset.image
            output.metric.mesh.complete.selectedFine.embedding
            output.pulledBack := by
      rw [output.image_eq, output.ambientCore_eq]
      exact ambientData.1
    rcases Finset.mem_image.mp coreImage with
      ⟨coreSource, coreSourceMem, coreSourceEq⟩
    have fiberImage :
        ambientSource ∈
          Finset.image
            output.metric.mesh.complete.selectedFine.embedding
            (wz2PaperFullFiberIndices
              output.metric.selectedFine
              output.metric.metricParents parent) := by
      rw [fiberImageEq]
      exact ambientData.2
    rcases Finset.mem_image.mp fiberImage with
      ⟨fiberSource, fiberSourceMem, fiberSourceEq⟩
    have sourceEq : coreSource = fiberSource :=
      output.metric.mesh.complete.selectedFine.embedding.injective
        (coreSourceEq.trans fiberSourceEq.symm)
    refine Finset.mem_image.mpr
      ⟨coreSource, Finset.mem_inter.mpr
        ⟨coreSourceMem, ?_⟩, coreSourceEq⟩
    rwa [sourceEq]

theorem ambientAuxiliaryFiberCWA
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (parent : Fin output.metric.metricParents.card)
    (convexSet : Set Point3)
    (convex : Convex ℝ convexSet) :
    (((output.cleanup.auxiliary.auxiliaryFiber
        (output.metricParentLabel parent)).filter fun source =>
          wz2PaperLiteralUnitRescalingMap
              (output.metric.metricParents.tube parent)
              output.metric.metricInput.rho_pos ''
            (fine.tube source).carrier ⊆ convexSet).card :
      ENNReal) ≤
      pureWZ2Prop62InsertedCWALoss
          rho (schedule.actualScale packetCoordinate) ambientConstant *
        volume convexSet *
        ((output.cleanup.auxiliary.auxiliaryFiber
          (output.metricParentLabel parent)).card : ENNReal) := by
  let metricFiber :=
    wz2PaperFullFiberIndices
      output.metric.selectedFine
      output.metric.metricParents parent
  let selectedPredicate :
      Fin output.metric.selectedFine.card → Prop :=
    fun source =>
      wz2PaperLiteralUnitRescalingMap
          (output.metric.metricParents.tube parent)
          output.metric.metricInput.rho_pos ''
        (output.metric.selectedFine.tube source).carrier ⊆ convexSet
  let ambientPredicate : Fin fine.card → Prop :=
    fun source =>
      wz2PaperLiteralUnitRescalingMap
          (output.metric.metricParents.tube parent)
          output.metric.metricInput.rho_pos ''
        (fine.tube source).carrier ⊆ convexSet
  have fiberImageEq :
      Finset.image output.metric.mesh.complete.selectedFine.embedding
          metricFiber =
        output.cleanup.auxiliary.auxiliaryFiber
          (output.metricParentLabel parent) := by
    simpa only [metricFiber] using
      output.metricFiber_image_eq_ambientAuxiliaryFiber
        fineLine fineBase rhoPos widthPos packetScaleLeRho
        sixWidthLe parent
  have predicateCompatibility :
      ∀ source,
        selectedPredicate source =
          ambientPredicate
            (output.metric.mesh.complete.selectedFine.embedding source) := by
    intro source
    apply propext
    simp only [selectedPredicate, ambientPredicate]
    rw [output.metric.mesh.complete.selectedFine.tube_eq]
  have filteredImage :
      Finset.image output.metric.mesh.complete.selectedFine.embedding
          (metricFiber.filter selectedPredicate) =
        (output.cleanup.auxiliary.auxiliaryFiber
          (output.metricParentLabel parent)).filter ambientPredicate := by
    ext ambientSource
    constructor
    · intro ambientMem
      rcases Finset.mem_image.mp ambientMem with
        ⟨source, sourceMem, rfl⟩
      have sourceData := Finset.mem_filter.mp sourceMem
      apply Finset.mem_filter.mpr
      constructor
      · rw [← fiberImageEq]
        exact Finset.mem_image.mpr
          ⟨source, sourceData.1, rfl⟩
      · rw [← predicateCompatibility source]
        exact sourceData.2
    · intro ambientMem
      have ambientData := Finset.mem_filter.mp ambientMem
      have ambientFiberImage :
          ambientSource ∈
            Finset.image
              output.metric.mesh.complete.selectedFine.embedding
              metricFiber := by
        rw [fiberImageEq]
        exact ambientData.1
      rcases Finset.mem_image.mp ambientFiberImage with
        ⟨source, sourceFiber, sourceEq⟩
      refine Finset.mem_image.mpr
        ⟨source, Finset.mem_filter.mpr ⟨sourceFiber, ?_⟩, sourceEq⟩
      rw [predicateCompatibility source, sourceEq]
      exact ambientData.2
  have filteredCard :
      (metricFiber.filter selectedPredicate).card =
        ((output.cleanup.auxiliary.auxiliaryFiber
          (output.metricParentLabel parent)).filter
            ambientPredicate).card := by
    rw [← filteredImage]
    exact
      (Finset.card_image_of_injective _
        output.metric.mesh.complete.selectedFine.embedding.injective).symm
  have fiberCard :
      metricFiber.card =
        (output.cleanup.auxiliary.auxiliaryFiber
          (output.metricParentLabel parent)).card := by
    calc
      metricFiber.card =
          (Finset.image
            output.metric.mesh.complete.selectedFine.embedding
            metricFiber).card :=
        (Finset.card_image_of_injective _
          output.metric.mesh.complete.selectedFine.embedding.injective).symm
      _ = _ := congrArg Finset.card fiberImageEq
  have metricBound :=
    output.metric.metricInput.insertedFiberCWA
      parent convexSet convex
  change
    (((output.cleanup.auxiliary.auxiliaryFiber
      (output.metricParentLabel parent)).filter
        ambientPredicate).card : ENNReal) ≤
      pureWZ2Prop62InsertedCWALoss
          rho (schedule.actualScale packetCoordinate) ambientConstant *
        volume convexSet *
        ((output.cleanup.auxiliary.auxiliaryFiber
          (output.metricParentLabel parent)).card : ENNReal)
  rw [← filteredCard, ← fiberCard]
  simpa only [metricFiber, selectedPredicate] using metricBound

theorem ambientCoreAuxiliaryFiberCWA
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (parent : Fin output.metric.metricParents.card)
    (coreFiberNonempty :
      (output.cleanup.core.core ∩
        output.cleanup.auxiliary.auxiliaryFiber
          (output.metricParentLabel parent)).Nonempty)
    (convexSet : Set Point3)
    (convex : Convex ℝ convexSet) :
    ((((output.cleanup.core.core ∩
        output.cleanup.auxiliary.auxiliaryFiber
          (output.metricParentLabel parent)).filter fun source =>
            wz2PaperLiteralUnitRescalingMap
                (output.metric.metricParents.tube parent)
                output.metric.metricInput.rho_pos ''
              (fine.tube source).carrier ⊆ convexSet).card :
      ENNReal)) ≤
      (pureWZ2Prop62InsertedCWALoss
          rho (schedule.actualScale packetCoordinate) ambientConstant *
        output.quotientDensityLoss) *
        volume convexSet *
        (((output.cleanup.core.core ∩
          output.cleanup.auxiliary.auxiliaryFiber
            (output.metricParentLabel parent)).card : ENNReal)) := by
  let predicate : Fin fine.card → Prop :=
    fun source =>
      wz2PaperLiteralUnitRescalingMap
          (output.metric.metricParents.tube parent)
          output.metric.metricInput.rho_pos ''
        (fine.tube source).carrier ⊆ convexSet
  have ambientCWA :
      (((output.cleanup.auxiliary.auxiliaryFiber
          (output.metricParentLabel parent)).filter predicate).card :
        ENNReal) ≤
        pureWZ2Prop62InsertedCWALoss
            rho (schedule.actualScale packetCoordinate) ambientConstant *
          volume convexSet *
          ((output.cleanup.auxiliary.auxiliaryFiber
            (output.metricParentLabel parent)).card : ENNReal) := by
    simpa only [predicate] using
      output.ambientAuxiliaryFiberCWA
        fineLine fineBase rhoPos widthPos packetScaleLeRho
        sixWidthLe parent convexSet convex
  have transferred :=
    pureWZ2_prop62_inserted_cwa_after_core
      output.cleanup.auxiliary.label
      output.cleanup.preliminary
      output.cleanup.core.core
      output.cleanup.core.core_subset
      (schedule.levelCount + 1)
      output.cleanup.auxiliary.auxiliaryFiber
      (fun _ => rfl)
      (fun label nonempty => by
        simpa only [Fintype.card_fin] using
          output.cleanup.auxiliary_density label nonempty)
      (output.metricParentLabel parent)
      coreFiberNonempty
      (pureWZ2Prop62InsertedCWALoss
        rho (schedule.actualScale packetCoordinate) ambientConstant)
      (volume convexSet) predicate ambientCWA
  simpa only [
    predicate, quotientDensityLoss,
    Kakeya.Streamlined.TubeFamily.enncard,
    Fintype.card_fin, mul_assoc
  ] using transferred

theorem pulledBackMetricFiberCWA
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (parent : Fin output.metric.metricParents.card)
    (coreFiberNonempty :
      (output.pulledBack ∩
        wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents parent).Nonempty)
    (convexSet : Set Point3)
    (convex : Convex ℝ convexSet) :
    ((((output.pulledBack ∩
        wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents parent).filter fun source =>
            wz2PaperLiteralUnitRescalingMap
                (output.metric.metricParents.tube parent)
                output.metric.metricInput.rho_pos ''
              (output.metric.selectedFine.tube source).carrier ⊆
                convexSet).card : ENNReal)) ≤
      (pureWZ2Prop62InsertedCWALoss
          rho (schedule.actualScale packetCoordinate) ambientConstant *
        output.quotientDensityLoss) *
        volume convexSet *
        (((output.pulledBack ∩
          wz2PaperFullFiberIndices
            output.metric.selectedFine
            output.metric.metricParents parent).card : ENNReal)) := by
  let coreFiber :=
    output.pulledBack ∩
      wz2PaperFullFiberIndices
        output.metric.selectedFine
        output.metric.metricParents parent
  let ambientCoreFiber :=
    output.cleanup.core.core ∩
      output.cleanup.auxiliary.auxiliaryFiber
        (output.metricParentLabel parent)
  let selectedPredicate :
      Fin output.metric.selectedFine.card → Prop :=
    fun source =>
      wz2PaperLiteralUnitRescalingMap
          (output.metric.metricParents.tube parent)
          output.metric.metricInput.rho_pos ''
        (output.metric.selectedFine.tube source).carrier ⊆ convexSet
  let ambientPredicate : Fin fine.card → Prop :=
    fun source =>
      wz2PaperLiteralUnitRescalingMap
          (output.metric.metricParents.tube parent)
          output.metric.metricInput.rho_pos ''
        (fine.tube source).carrier ⊆ convexSet
  have fiberImageEq :
      Finset.image output.metric.mesh.complete.selectedFine.embedding
          coreFiber =
        ambientCoreFiber := by
    simpa only [coreFiber, ambientCoreFiber] using
      output.coreMetricFiber_image_eq_ambientCoreAuxiliaryFiber
        fineLine fineBase rhoPos widthPos packetScaleLeRho
        sixWidthLe parent
  have ambientCoreFiberNonempty : ambientCoreFiber.Nonempty := by
    rcases coreFiberNonempty with ⟨source, sourceMem⟩
    exact
      ⟨output.metric.mesh.complete.selectedFine.embedding source, by
        rw [← fiberImageEq]
        exact Finset.mem_image.mpr ⟨source, sourceMem, rfl⟩⟩
  have predicateCompatibility :
      ∀ source,
        selectedPredicate source =
          ambientPredicate
            (output.metric.mesh.complete.selectedFine.embedding source) := by
    intro source
    apply propext
    simp only [selectedPredicate, ambientPredicate]
    rw [output.metric.mesh.complete.selectedFine.tube_eq]
  have filteredImage :
      Finset.image output.metric.mesh.complete.selectedFine.embedding
          (coreFiber.filter selectedPredicate) =
        ambientCoreFiber.filter ambientPredicate := by
    ext ambientSource
    constructor
    · intro ambientMem
      rcases Finset.mem_image.mp ambientMem with
        ⟨source, sourceMem, rfl⟩
      have sourceData := Finset.mem_filter.mp sourceMem
      apply Finset.mem_filter.mpr
      constructor
      · rw [← fiberImageEq]
        exact Finset.mem_image.mpr
          ⟨source, sourceData.1, rfl⟩
      · rw [← predicateCompatibility source]
        exact sourceData.2
    · intro ambientMem
      have ambientData := Finset.mem_filter.mp ambientMem
      have ambientFiberImage :
          ambientSource ∈
            Finset.image
              output.metric.mesh.complete.selectedFine.embedding
              coreFiber := by
        rw [fiberImageEq]
        exact ambientData.1
      rcases Finset.mem_image.mp ambientFiberImage with
        ⟨source, sourceFiber, sourceEq⟩
      refine Finset.mem_image.mpr
        ⟨source, Finset.mem_filter.mpr ⟨sourceFiber, ?_⟩, sourceEq⟩
      rw [predicateCompatibility source, sourceEq]
      exact ambientData.2
  have filteredCard :
      (coreFiber.filter selectedPredicate).card =
        (ambientCoreFiber.filter ambientPredicate).card := by
    rw [← filteredImage]
    exact
      (Finset.card_image_of_injective _
        output.metric.mesh.complete.selectedFine.embedding.injective).symm
  have fiberCard :
      coreFiber.card = ambientCoreFiber.card := by
    calc
      coreFiber.card =
          (Finset.image
            output.metric.mesh.complete.selectedFine.embedding
            coreFiber).card :=
        (Finset.card_image_of_injective _
          output.metric.mesh.complete.selectedFine.embedding.injective).symm
      _ = ambientCoreFiber.card := congrArg Finset.card fiberImageEq
  have ambientBound :=
    output.ambientCoreAuxiliaryFiberCWA
      fineLine fineBase rhoPos widthPos packetScaleLeRho
      sixWidthLe parent
      ambientCoreFiberNonempty convexSet convex
  change
    ((coreFiber.filter selectedPredicate).card : ENNReal) ≤
      (pureWZ2Prop62InsertedCWALoss
          rho (schedule.actualScale packetCoordinate) ambientConstant *
        output.quotientDensityLoss) *
        volume convexSet * (coreFiber.card : ENNReal)
  rw [filteredCard, fiberCard]
  simpa only [ambientCoreFiber, ambientPredicate] using ambientBound

theorem restrictedInsertedFiberCWA
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (parent : Fin output.restriction.coarseSelected.family.card)
    (convexSet : Set Point3)
    (convex : Convex ℝ convexSet) :
    (((wz2PaperFullFiberIndices
        output.restriction.fineSelected.family
        output.restriction.coarseSelected.family parent).filter
        fun source =>
          wz2PaperLiteralUnitRescalingMap
              (output.restriction.coarseSelected.family.tube parent)
              output.metric.metricInput.rho_pos ''
            (output.restriction.fineSelected.family.tube source).carrier ⊆
              convexSet).card : ENNReal) ≤
      (pureWZ2Prop62InsertedCWALoss
          rho (schedule.actualScale packetCoordinate) ambientConstant *
        output.quotientDensityLoss) *
        volume convexSet *
        ((wz2PaperFullFiberIndices
          output.restriction.fineSelected.family
          output.restriction.coarseSelected.family parent).card :
          ENNReal) := by
  let ambientParent :=
    output.restriction.coarseSelected.embedding parent
  let finalFiber :=
    wz2PaperFullFiberIndices
      output.restriction.fineSelected.family
      output.restriction.coarseSelected.family parent
  let pulledBackFiber :=
    output.pulledBack ∩
      wz2PaperFullFiberIndices
        output.metric.selectedFine
        output.metric.metricParents ambientParent
  have fiberImageEq :
      Finset.image output.restriction.fineSelected.embedding finalFiber =
        pulledBackFiber := by
    simpa only [finalFiber, pulledBackFiber, ambientParent] using
      output.restriction.fiber_image_eq parent
  have finalFiberNonempty : finalFiber.Nonempty := by
    rcases output.restriction.lineCover.parent_surjective parent with
      ⟨source, parentEq⟩
    exact
      ⟨source,
        (mem_wz2PaperFullFiberIndices_iff parent source).mpr <| by
          rw [← parentEq]
          exact output.restriction.lineCover.parent_covers source⟩
  have pulledBackFiberNonempty : pulledBackFiber.Nonempty := by
    rcases finalFiberNonempty with ⟨source, sourceMem⟩
    exact
      ⟨output.restriction.fineSelected.embedding source, by
        rw [← fiberImageEq]
        exact Finset.mem_image.mpr ⟨source, sourceMem, rfl⟩⟩
  let finalPredicate :
      Fin output.restriction.fineSelected.family.card → Prop :=
    fun source =>
      wz2PaperLiteralUnitRescalingMap
          (output.restriction.coarseSelected.family.tube parent)
          output.metric.metricInput.rho_pos ''
        (output.restriction.fineSelected.family.tube source).carrier ⊆
          convexSet
  let pulledBackPredicate :
      Fin output.metric.selectedFine.card → Prop :=
    fun source =>
      wz2PaperLiteralUnitRescalingMap
          (output.metric.metricParents.tube ambientParent)
          output.metric.metricInput.rho_pos ''
        (output.metric.selectedFine.tube source).carrier ⊆ convexSet
  have predicateCompatibility :
      ∀ source,
        finalPredicate source =
          pulledBackPredicate
            (output.restriction.fineSelected.embedding source) := by
    intro source
    apply propext
    simp only [finalPredicate, pulledBackPredicate]
    rw [output.restriction.fineSelected.tube_eq,
      output.restriction.coarseSelected.tube_eq]
  have filteredImage :
      Finset.image output.restriction.fineSelected.embedding
          (finalFiber.filter finalPredicate) =
        pulledBackFiber.filter pulledBackPredicate := by
    ext ambientSource
    constructor
    · intro ambientMem
      rcases Finset.mem_image.mp ambientMem with
        ⟨source, sourceMem, rfl⟩
      have sourceData := Finset.mem_filter.mp sourceMem
      apply Finset.mem_filter.mpr
      constructor
      · rw [← fiberImageEq]
        exact Finset.mem_image.mpr
          ⟨source, sourceData.1, rfl⟩
      · rw [← predicateCompatibility source]
        exact sourceData.2
    · intro ambientMem
      have ambientData := Finset.mem_filter.mp ambientMem
      have ambientFiberImage :
          ambientSource ∈
            Finset.image
              output.restriction.fineSelected.embedding finalFiber := by
        rw [fiberImageEq]
        exact ambientData.1
      rcases Finset.mem_image.mp ambientFiberImage with
        ⟨source, sourceFiber, sourceEq⟩
      refine Finset.mem_image.mpr
        ⟨source, Finset.mem_filter.mpr ⟨sourceFiber, ?_⟩, sourceEq⟩
      rw [predicateCompatibility source, sourceEq]
      exact ambientData.2
  have filteredCard :
      (finalFiber.filter finalPredicate).card =
        (pulledBackFiber.filter pulledBackPredicate).card := by
    rw [← filteredImage]
    exact
      (Finset.card_image_of_injective _
        output.restriction.fineSelected.embedding.injective).symm
  have fiberCard :
      finalFiber.card = pulledBackFiber.card := by
    calc
      finalFiber.card =
          (Finset.image output.restriction.fineSelected.embedding
            finalFiber).card :=
        (Finset.card_image_of_injective _
          output.restriction.fineSelected.embedding.injective).symm
      _ = pulledBackFiber.card := congrArg Finset.card fiberImageEq
  have pulledBackBound :=
    output.pulledBackMetricFiberCWA
      fineLine fineBase rhoPos widthPos packetScaleLeRho
      sixWidthLe ambientParent
      pulledBackFiberNonempty convexSet convex
  change
    ((finalFiber.filter finalPredicate).card : ENNReal) ≤
      (pureWZ2Prop62InsertedCWALoss
          rho (schedule.actualScale packetCoordinate) ambientConstant *
        output.quotientDensityLoss) *
        volume convexSet * (finalFiber.card : ENNReal)
  rw [filteredCard, fiberCard]
  simpa only [pulledBackFiber, pulledBackPredicate, ambientParent] using
    pulledBackBound

end PureWZ2Prop62ProxyQuotientMetricCoreOutput

end Kakeya.Assouad

end
