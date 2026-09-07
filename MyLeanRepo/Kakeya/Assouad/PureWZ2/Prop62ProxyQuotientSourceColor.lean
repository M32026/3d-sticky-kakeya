import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientPreCoreAdapter
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62SourceConflictColoring
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientMetricCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricCoreRescaledPhysicalCWA

/-!
# Proposition 6.2 quotient source-conflict color

After the complete metric fibers and their `D_-` band are fixed, the paper
chooses one source-conflict color independently in every retained metric
fiber.  This leaf-level selection is distinct from both quotient ancestry and
the stronger upper-envelope color vector.

The canonical color below is the proper coloring of the frozen
`wz2PaperLiteralSourceSeparationFactor * delta` conflict graph.  The generic
pre-core adapter selects one such color in each metric parent.  Since the
one-pass core is contained in that preliminary set, every final metric fiber
is monochromatic and therefore strongly separated, exactly in the form
consumed by `pureWZ2_prop62_proxy_quotient_fiber_cwa`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

abbrev PureWZ2Prop62ProxyQuotientSourceColor :=
  Fin (pureWZ2OrdinaryLineConflictDegree + 1)

/-- The canonical ambient fine-tube source-conflict color. -/
noncomputable def pureWZ2Prop62ProxyQuotientSourceColoring
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (deltaPos : 0 < delta)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (fineDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine) :
    PureWZ2Prop62SourceConflictColoringData fine :=
  Classical.choice <|
    pureWZ2_prop62_source_conflict_coloring
      deltaPos fineLine
      (fun source => (fineBase source).trans (by norm_num))
      fineDistinct

/--
Concrete pre-core adapter using the proper source-conflict coloring.
-/
structure PureWZ2Prop62ProxyQuotientSourceColorPreCoreData
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
    (weight : Fin fine.card → ENNReal)
    (metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (upperColoring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate) where
  sourceConflict :
    PureWZ2Prop62SourceConflictColoringData fine
  adapter :
    PureWZ2Prop62ProxyQuotientPreCoreAdapterData
      schedule fineNonempty quotient width packetCoordinate
      strideBase weight metric upperColoring
      PureWZ2Prop62ProxyQuotientSourceColor sourceConflict.color
  source_color_loss_eq :
    adapter.preCore.retention.sourceColorLoss =
      pureWZ2OrdinaryLineConflictDegree + 1
  preliminary_source_monochromatic :
    ∀ leaf ∈ adapter.preCore.preliminary,
      sourceConflict.color leaf =
        adapter.preCore.leafBin.selectedColor
          (metric.ambientMetricParentOf leaf)
  preliminary_upper_monochromatic :
    ∀ leaf ∈ adapter.preCore.preliminary,
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        upperColoring.leafColor coordinate leaf =
          adapter.global.selectedColor coordinate

theorem pureWZ2_prop62_proxy_quotient_sourceColor_preCore
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
    (weight : Fin fine.card → ENNReal)
    (metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (upperColoring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate)
    (selectionWeightPos :
      0 <
        ∑ source ∈ metric.selection.selected,
          weight source)
    (weightFinite : ∀ source : Fin fine.card, weight source ≠ ⊤)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2) :
    Nonempty
      (PureWZ2Prop62ProxyQuotientSourceColorPreCoreData
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metric upperColoring) := by
  let sourceConflict :=
    pureWZ2Prop62ProxyQuotientSourceColoring
      (schedule.scaleData packetCoordinate).delta_pos
      fineLine fineBase schedule.fine_distinct
  let adapter :=
    Classical.choice <|
      pureWZ2_prop62_proxy_quotient_preCore_adapter
        schedule fineNonempty quotient width packetCoordinate
        strideBase weight metric upperColoring
        PureWZ2Prop62ProxyQuotientSourceColor sourceConflict.color
        selectionWeightPos weightFinite fineLine fineBase rhoPos widthPos
        packetScaleLeRho sixWidthLe
  exact
    ⟨{
      sourceConflict := sourceConflict
      adapter := adapter
      source_color_loss_eq := by
        rw [adapter.preCore.retention.sourceColorLoss_eq]
        simp [PureWZ2Prop62ProxyQuotientSourceColor]
      preliminary_source_monochromatic :=
        adapter.preCore.source_monochromatic
      preliminary_upper_monochromatic := by
        intro leaf leafMem coordinate
        exact
          adapter.leaf_monochromatic leaf
            (by
              rw [adapter.wholeLeaves_eq]
              exact
                adapter.preCore.preliminary_subset_whole_fibers leafMem)
            coordinate
    }⟩

namespace PureWZ2Prop62ProxyQuotientSourceColorPreCoreData

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
    {metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {upperColoring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    (data :
      PureWZ2Prop62ProxyQuotientSourceColorPreCoreData
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metric upperColoring)

/--
Every final genuine metric fiber is monochromatic for the color chosen in its
pre-core metric parent.
-/
theorem finalMetricFiber_monochromatic
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (metric_eq : metricCore.metric = metric)
    (preliminary_eq :
      metricCore.cleanup.preliminary =
        data.adapter.preCore.preliminary)
    (parent :
      Fin metricCore.restriction.coarseSelected.family.card) :
    ∃ selectedColor : PureWZ2Prop62ProxyQuotientSourceColor,
      ∀ source :
          Fin
            (metricCore.restriction.metricFiberSource parent).family.card,
        data.sourceConflict.color
            (metricCore.metric.mesh.complete.selectedFine.embedding
              (metricCore.restriction.fineSelected.embedding
                ((metricCore.restriction.metricFiberSource parent).embedding
                  source))) =
          selectedColor := by
  subst metric
  refine
    ⟨data.adapter.preCore.leafBin.selectedColor
      (metricCore.restriction.coarseSelected.embedding parent), ?_⟩
  intro source
  let fiberSource :=
    (metricCore.restriction.metricFiberSource parent).embedding source
  let selectedSource :=
    metricCore.restriction.fineSelected.embedding fiberSource
  let ambientSource :=
    metricCore.metric.mesh.complete.selectedFine.embedding selectedSource
  have selectedSourcePulledBack :
      selectedSource ∈ metricCore.pulledBack := by
    have sourceImage :
        selectedSource ∈
          Finset.image metricCore.restriction.fineSelected.embedding
            Finset.univ :=
      Finset.mem_image.mpr
        ⟨fiberSource, Finset.mem_univ fiberSource, rfl⟩
    rwa [metricCore.restriction.fine_image_univ] at sourceImage
  have ambientCore :
      ambientSource ∈ metricCore.cleanup.core.core := by
    rw [← metricCore.ambientCore_eq, ← metricCore.image_eq]
    exact Finset.mem_image.mpr
      ⟨selectedSource, selectedSourcePulledBack, rfl⟩
  have ambientPreliminary :
      ambientSource ∈ data.adapter.preCore.preliminary := by
    rw [← preliminary_eq]
    exact metricCore.cleanup.core.core_subset ambientCore
  have ownerEq :
      metricCore.metric.ambientMetricParentOf ambientSource =
        metricCore.restriction.coarseSelected.embedding parent := by
    have sourceFiber :
        fiberSource ∈
          wz2PaperFullFiberIndices
            metricCore.restriction.fineSelected.family
            metricCore.restriction.coarseSelected.family parent :=
      Finset.orderEmbOfFin_mem
        (wz2PaperFullFiberIndices
          metricCore.restriction.fineSelected.family
          metricCore.restriction.coarseSelected.family parent)
        rfl source
    have sourceCovered :
        WZ1PaperTubeCovers
          (metricCore.metric.selectedFine.tube selectedSource)
          (metricCore.metric.metricParents.tube
            (metricCore.restriction.coarseSelected.embedding parent)) := by
      have localCovered :=
        (mem_wz2PaperFullFiberIndices_iff parent fiberSource).mp
          sourceFiber
      simpa only [selectedSource, fiberSource,
        metricCore.restriction.fineSelected.tube_eq,
        metricCore.restriction.coarseSelected.tube_eq] using
          localCovered
    have canonicalParent :
        metricCore.metric.metricParentOf selectedSource =
          metricCore.restriction.coarseSelected.embedding parent :=
      (metricCore.metric.section6Cover.toWZ1PaperTubeCover
        |>.parent_unique selectedSource
          (metricCore.restriction.coarseSelected.embedding parent)
          sourceCovered).symm
    change
      metricCore.metric.ambientMetricParentOf
          (metricCore.metric.mesh.complete.selectedFine.embedding
            selectedSource) =
        metricCore.restriction.coarseSelected.embedding parent
    rw [metricCore.metric.ambientMetricParentOf_embedding]
    exact canonicalParent
  simpa only [ambientSource, selectedSource, fiberSource, ownerEq] using
    data.preliminary_source_monochromatic
      ambientSource ambientPreliminary

/--
The exact dependent function required by
`pureWZ2_prop62_proxy_quotient_fiber_cwa`.
-/
theorem sourceStronglySeparated
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (metric_eq : metricCore.metric = metric)
    (preliminary_eq :
      metricCore.cleanup.preliminary =
        data.adapter.preCore.preliminary) :
    ∀ parent :
        Fin metricCore.restriction.coarseSelected.family.card,
      ∀ first second :
          Fin
            (metricCore.restriction.metricFiberSource parent).family.card,
        first ≠ second →
          wz2PaperLiteralSourceSeparationFactor * delta <
            wz1PaperLineDistance
              ((metricCore.restriction.metricFiberSource parent).family.tube
                first)
              ((metricCore.restriction.metricFiberSource parent).family.tube
                second) := by
  subst metric
  intro parent
  rcases
      data.finalMetricFiber_monochromatic
        metricCore rfl preliminary_eq parent
    with ⟨selectedColor, monochromatic⟩
  intro first second indexNe
  let firstFiber :=
    (metricCore.restriction.metricFiberSource parent).embedding first
  let secondFiber :=
    (metricCore.restriction.metricFiberSource parent).embedding second
  let firstSelected :=
    metricCore.restriction.fineSelected.embedding firstFiber
  let secondSelected :=
    metricCore.restriction.fineSelected.embedding secondFiber
  let firstAmbient :=
    metricCore.metric.mesh.complete.selectedFine.embedding firstSelected
  let secondAmbient :=
    metricCore.metric.mesh.complete.selectedFine.embedding secondSelected
  have ambientNe : firstAmbient ≠ secondAmbient := by
    exact
      metricCore.metric.mesh.complete.selectedFine.embedding.injective.ne <|
        metricCore.restriction.fineSelected.embedding.injective.ne <|
          (metricCore.restriction.metricFiberSource parent).embedding.injective.ne
            indexNe
  have colorEq :
      data.sourceConflict.color firstAmbient =
        data.sourceConflict.color secondAmbient := by
    exact
      (monochromatic first).trans
        (monochromatic second).symm
  by_contra notSeparated
  have distanceClose :
      wz1PaperLineDistance
          (fine.tube firstAmbient) (fine.tube secondAmbient) ≤
        wz2PaperLiteralSourceSeparationFactor * delta := by
    simpa only [firstAmbient, secondAmbient, firstSelected, secondSelected,
      firstFiber, secondFiber,
      (metricCore.restriction.metricFiberSource parent).tube_eq,
      metricCore.restriction.fineSelected.tube_eq,
      metricCore.metric.mesh.complete.selectedFine.tube_eq] using
        le_of_not_gt notSeparated
  exact
    (data.sourceConflict.proper
      firstAmbient secondAmbient ambientNe distanceClose) colorEq

end PureWZ2Prop62ProxyQuotientSourceColorPreCoreData

end Kakeya.Assouad

end
