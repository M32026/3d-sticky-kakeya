import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientAuxiliaryTree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricCoreRestriction

/-!
# Proposition 6.2 quotient-ancestry metric core

The quotient-ancestry preliminary selection and the proxy metric construction
use the same leaf set.  This module applies the quotient-prefix tree cleanup
once, pulls the resulting ambient core back through the complete packet hull,
and restricts the genuine Section 6 metric cover to the surviving parents.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62ProxyQuotientMetricCoreOutput
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal) where
  metric :
    PureWZ2Prop62ProxyAncestryMetricOutput
      (rho := rho) schedule fineNonempty quotient width
        packetCoordinate strideBase weight
  cleanup :
    PureWZ2Prop62ProxyQuotientOnePassCleanupData
      schedule fineNonempty quotient rho width
        packetCoordinate strideBase weight
  selection_eq :
    cleanup.selection = metric.selection
  ambientCore : Finset (Fin fine.card)
  ambientCore_eq :
    ambientCore = cleanup.core.core
  ambientCore_nonempty : ambientCore.Nonempty
  ambientCore_subset_selection :
    ambientCore ⊆ metric.selection.selected
  ambientCore_subset_packetHull :
    ambientCore ⊆ metric.mesh.complete.selectedFineIndices
  pulledBack :
    Finset (Fin metric.selectedFine.card)
  pulledBack_eq :
    pulledBack =
      Finset.univ.filter fun source =>
        metric.mesh.complete.selectedFine.embedding source ∈ ambientCore
  image_eq :
    Finset.image metric.mesh.complete.selectedFine.embedding pulledBack =
      ambientCore
  pulledBack_nonempty : pulledBack.Nonempty
  restriction :
    PureWZ2Prop62MetricCoreRestrictionData
      metric.section6Cover pulledBack

theorem pureWZ2_prop62_proxy_quotient_metric_core_with_provenance
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (preliminary : Finset (Fin fine.card))
    (preliminaryNonempty : preliminary.Nonempty)
    (preliminarySubsetSelection :
      preliminary ⊆
        (quotient.selectProxyResidueUpperAncestryPerCell
          rho width packetCoordinate strideBase weight).selected)
    (receipt :
      PureWZ2Prop62CleanupReceipt
        (pureWZ2Prop62ProxyQuotientAuxiliaryLevel
          schedule fineNonempty quotient rho width packetCoordinate).tree
        preliminary)
    :
    ∃ output :
        PureWZ2Prop62ProxyQuotientMetricCoreOutput
          (rho := rho) schedule fineNonempty quotient width
            packetCoordinate strideBase weight,
      output.metric = metric ∧
        output.cleanup =
          pureWZ2Prop62ProxyQuotientOnePassCleanupOfReceipt
            schedule fineNonempty quotient rho width
              packetCoordinate strideBase weight
              preliminary preliminaryNonempty
              preliminarySubsetSelection receipt := by
  let cleanup :=
    pureWZ2Prop62ProxyQuotientOnePassCleanupOfReceipt
      schedule fineNonempty quotient rho width
        packetCoordinate strideBase weight
        preliminary preliminaryNonempty preliminarySubsetSelection receipt
  have selectionEq :
      cleanup.selection = metric.selection := by
    calc
      cleanup.selection =
          quotient.selectProxyResidueUpperAncestryPerCell
            rho width packetCoordinate strideBase weight :=
        cleanup.selection_eq
      _ = metric.selection := metric.selection_eq.symm
  let ambientCore := cleanup.core.core
  have ambientCoreNonempty : ambientCore.Nonempty :=
    cleanup.core_nonempty
  have ambientCoreSubsetSelection :
      ambientCore ⊆ metric.selection.selected := by
    intro source sourceMem
    have selectedMem :
        source ∈ cleanup.selection.selected :=
      cleanup.preliminary_subset_selection
        (cleanup.core.core_subset sourceMem)
    rw [selectionEq] at selectedMem
    exact selectedMem
  have ambientCoreSubsetPacketHull :
      ambientCore ⊆ metric.mesh.complete.selectedFineIndices := by
    intro source sourceMem
    rw [metric.packet_hull_eq_selection]
    exact ambientCoreSubsetSelection sourceMem
  let pulledBack :
      Finset (Fin metric.selectedFine.card) :=
    Finset.univ.filter fun source =>
      metric.mesh.complete.selectedFine.embedding source ∈ ambientCore
  have imageEq :
      Finset.image metric.mesh.complete.selectedFine.embedding pulledBack =
        ambientCore := by
    ext ambientSource
    constructor
    · intro sourceImage
      rcases Finset.mem_image.mp sourceImage with
        ⟨source, sourceMem, sourceEq⟩
      have sourceCore :
          metric.mesh.complete.selectedFine.embedding source ∈
            ambientCore :=
        (Finset.mem_filter.mp sourceMem).2
      rwa [sourceEq] at sourceCore
    · intro sourceCore
      have sourceHull :
          ambientSource ∈
            metric.mesh.complete.selectedFineIndices :=
        ambientCoreSubsetPacketHull sourceCore
      rcases
          metric.mesh.complete.selectedFine_ambient_surjective
            ambientSource sourceHull
        with ⟨source, sourceEq⟩
      exact
        Finset.mem_image.mpr
          ⟨source,
            Finset.mem_filter.mpr
              ⟨Finset.mem_univ source, by
                rwa [sourceEq]⟩,
            sourceEq⟩
  have pulledBackNonempty : pulledBack.Nonempty := by
    rcases ambientCoreNonempty with ⟨ambientSource, sourceCore⟩
    have sourceImage :
        ambientSource ∈
          Finset.image metric.mesh.complete.selectedFine.embedding pulledBack := by
      rw [imageEq]
      exact sourceCore
    rcases Finset.mem_image.mp sourceImage with
      ⟨source, sourceMem, _sourceEq⟩
    exact ⟨source, sourceMem⟩
  let restriction :=
    Classical.choice <|
      pureWZ2_prop62_metric_core_restriction
        metric.section6Cover pulledBack pulledBackNonempty
  let output :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight :=
    {
      metric := metric
      cleanup := cleanup
      selection_eq := selectionEq
      ambientCore := ambientCore
      ambientCore_eq := rfl
      ambientCore_nonempty := ambientCoreNonempty
      ambientCore_subset_selection := ambientCoreSubsetSelection
      ambientCore_subset_packetHull := ambientCoreSubsetPacketHull
      pulledBack := pulledBack
      pulledBack_eq := rfl
      image_eq := imageEq
      pulledBack_nonempty := pulledBackNonempty
      restriction := restriction
    }
  exact ⟨output, rfl, rfl⟩

theorem pureWZ2_prop62_proxy_quotient_metric_core_of_metric_and_receipt
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (preliminary : Finset (Fin fine.card))
    (preliminaryNonempty : preliminary.Nonempty)
    (preliminarySubsetSelection :
      preliminary ⊆
        (quotient.selectProxyResidueUpperAncestryPerCell
          rho width packetCoordinate strideBase weight).selected)
    (receipt :
      PureWZ2Prop62CleanupReceipt
        (pureWZ2Prop62ProxyQuotientAuxiliaryLevel
          schedule fineNonempty quotient rho width packetCoordinate).tree
        preliminary)
    :
    Nonempty
      (PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight) := by
  rcases
      pureWZ2_prop62_proxy_quotient_metric_core_with_provenance
        schedule fineNonempty quotient rho width packetCoordinate
          strideBase weight metric preliminary preliminaryNonempty
          preliminarySubsetSelection receipt
    with ⟨output, _metricEq, _cleanupEq⟩
  exact ⟨output⟩

theorem pureWZ2_prop62_proxy_quotient_metric_core_of_metric
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (preliminary : Finset (Fin fine.card))
    (preliminaryNonempty : preliminary.Nonempty)
    (preliminarySubsetSelection :
      preliminary ⊆
        (quotient.selectProxyResidueUpperAncestryPerCell
          rho width packetCoordinate strideBase weight).selected)
    :
    Nonempty
      (PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight) :=
  pureWZ2_prop62_proxy_quotient_metric_core_of_metric_and_receipt
    schedule fineNonempty quotient rho width packetCoordinate
      strideBase weight metric preliminary preliminaryNonempty
      preliminarySubsetSelection
      (pureWZ2Prop62CleanupReceipt
        (pureWZ2Prop62ProxyQuotientAuxiliaryLevel
          schedule fineNonempty quotient rho width packetCoordinate).tree
        preliminary)

theorem pureWZ2_prop62_proxy_quotient_metric_core_of_receipt
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (preliminary : Finset (Fin fine.card))
    (preliminaryNonempty : preliminary.Nonempty)
    (preliminarySubsetSelection :
      preliminary ⊆
        (quotient.selectProxyResidueUpperAncestryPerCell
          rho width packetCoordinate strideBase weight).selected)
    (receipt :
      PureWZ2Prop62CleanupReceipt
        (pureWZ2Prop62ProxyQuotientAuxiliaryLevel
          schedule fineNonempty quotient rho width packetCoordinate).tree
        preliminary)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (selectionNonempty :
      (quotient.selectProxyResidueUpperAncestryPerCell
        rho width packetCoordinate strideBase weight).selected.Nonempty)
    (strongSeparation :
      6 * rho <
        (((strideBase + 1 : ℕ) : ℝ) - 1) * width)
    (packetBound :
      600000 * schedule.actualScale packetCoordinate +
          6 * width ≤
        rho / 2) :
    Nonempty
      (PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight) := by
  let metric :=
    Classical.choice <|
      pureWZ2_prop62_proxy_ancestry_metric_output
        (rho := rho)
        schedule fineNonempty fineLine fineBase quotient
        rho width packetCoordinate strideBase weight
        rhoPos widthPos selectionNonempty strongSeparation packetBound
  exact
    pureWZ2_prop62_proxy_quotient_metric_core_of_metric_and_receipt
      (rho := rho)
      schedule fineNonempty quotient width packetCoordinate
      strideBase weight metric preliminary preliminaryNonempty
      preliminarySubsetSelection receipt

theorem pureWZ2_prop62_proxy_quotient_metric_core
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (preliminary : Finset (Fin fine.card))
    (preliminaryNonempty : preliminary.Nonempty)
    (preliminarySubsetSelection :
      preliminary ⊆
        (quotient.selectProxyResidueUpperAncestryPerCell
          rho width packetCoordinate strideBase weight).selected)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (selectionNonempty :
      (quotient.selectProxyResidueUpperAncestryPerCell
        rho width packetCoordinate strideBase weight).selected.Nonempty)
    (strongSeparation :
      6 * rho <
        (((strideBase + 1 : ℕ) : ℝ) - 1) * width)
    (packetBound :
      600000 * schedule.actualScale packetCoordinate +
          6 * width ≤
        rho / 2) :
    Nonempty
      (PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight) :=
  pureWZ2_prop62_proxy_quotient_metric_core_of_receipt
    (rho := rho)
    schedule fineNonempty fineLine fineBase quotient rho width
      packetCoordinate strideBase weight preliminary
      preliminaryNonempty preliminarySubsetSelection
      (pureWZ2Prop62CleanupReceipt
        (pureWZ2Prop62ProxyQuotientAuxiliaryLevel
          schedule fineNonempty quotient rho width packetCoordinate).tree
        preliminary)
      rhoPos widthPos selectionNonempty strongSeparation packetBound

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

theorem selectedFine_embedding_mem_selection
    (source : Fin output.metric.selectedFine.card) :
    output.metric.mesh.complete.selectedFine.embedding source ∈
      output.metric.selection.selected := by
  rw [← output.metric.packet_hull_eq_selection]
  exact
    output.metric.mesh.complete.selectedFine_embedding_mem source

theorem metricParent_eq_iff_proxyPacketLineCell_embedding_eq
    (first second : Fin output.metric.selectedFine.card) :
    output.metric.section6Cover.toWZ1PaperTubeCover.parent first =
        output.metric.section6Cover.toWZ1PaperTubeCover.parent second ↔
      schedule.proxyPacketLineCell fineNonempty packetCoordinate width
          (output.metric.mesh.complete.selectedFine.embedding first) =
        schedule.proxyPacketLineCell fineNonempty packetCoordinate width
          (output.metric.mesh.complete.selectedFine.embedding second) := by
  rw [output.metric.metricInput.section6_parent_eq_packetParent,
    output.metric.metricInput.section6_parent_eq_packetParent]
  exact
    output.metric.metric_parent_eq_iff_proxyPacketLineCell_embedding_eq
      first second

theorem label_eq_iff_metricParent_eq
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (first second : Fin output.metric.selectedFine.card) :
    output.cleanup.auxiliary.label
          (output.metric.mesh.complete.selectedFine.embedding first) =
        output.cleanup.auxiliary.label
          (output.metric.mesh.complete.selectedFine.embedding second) ↔
      output.metric.section6Cover.toWZ1PaperTubeCover.parent first =
        output.metric.section6Cover.toWZ1PaperTubeCover.parent second := by
  let firstAmbient :=
    output.metric.mesh.complete.selectedFine.embedding first
  let secondAmbient :=
    output.metric.mesh.complete.selectedFine.embedding second
  constructor
  · intro labelEq
    have cellEq :
        schedule.proxyPacketLineCell fineNonempty packetCoordinate width
            firstAmbient =
          schedule.proxyPacketLineCell fineNonempty packetCoordinate width
            secondAmbient := by
      rw [output.cleanup.auxiliary.label_eq] at labelEq
      exact congrArg Subtype.val (congrArg Prod.fst labelEq)
    exact
      (output.metricParent_eq_iff_proxyPacketLineCell_embedding_eq
        first second).2 cellEq
  · intro parentEq
    have sameCell :
        schedule.proxyPacketLineCell fineNonempty packetCoordinate width
            firstAmbient =
          schedule.proxyPacketLineCell fineNonempty packetCoordinate width
            secondAmbient :=
      (output.metricParent_eq_iff_proxyPacketLineCell_embedding_eq
        first second).1 parentEq
    have firstMem :
        firstAmbient ∈ output.metric.selection.selected :=
      output.selectedFine_embedding_mem_selection first
    have secondMem :
        secondAmbient ∈ output.metric.selection.selected :=
      output.selectedFine_embedding_mem_selection second
    have firstColor :=
      output.metric.selection.selected_monochromatic
        firstAmbient firstMem
    have secondColor :=
      output.metric.selection.selected_monochromatic
        secondAmbient secondMem
    have packetCellEq :
        schedule.proxyPacketCell
            (schedule.proxyPacketLineCell
              fineNonempty packetCoordinate width) firstAmbient =
          schedule.proxyPacketCell
            (schedule.proxyPacketLineCell
              fineNonempty packetCoordinate width) secondAmbient := by
      apply Subtype.ext
      exact sameCell
    rw [packetCellEq] at firstColor
    have colorEq :
        quotient.proxyUpperColorVector rho packetCoordinate firstAmbient =
          quotient.proxyUpperColorVector rho packetCoordinate secondAmbient :=
      firstColor.trans secondColor.symm
    have upperAncestryEq :
        quotient.proxyUpperAncestry rho packetCoordinate firstAmbient =
          quotient.proxyUpperAncestry rho packetCoordinate secondAmbient :=
      quotient.proxyUpperAncestry_eq_of_sameCell_and_colorVector_eq
        fineLine fineBase rho width packetCoordinate rhoPos widthPos
        packetScaleLeRho sixWidthLe firstAmbient secondAmbient
        sameCell colorEq
    rw [output.cleanup.auxiliary.label_eq]
    apply Prod.ext
    · exact packetCellEq
    · funext coordinate
      exact congrFun upperAncestryEq coordinate

end PureWZ2Prop62ProxyQuotientMetricCoreOutput

end Kakeya.Assouad

end
