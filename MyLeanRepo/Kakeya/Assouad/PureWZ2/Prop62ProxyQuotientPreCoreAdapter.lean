import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentWeight
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62GlobalUpperEnvelopeParentSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PreCoreSelectionAssembly

/-!
# Proposition 6.2 quotient pre-core adapter

This module transports the genuine metric-parent fibers from the selected-fine
index type back to ambient fine indices.  It then performs the global upper
color-vector selection followed by the whole-fiber cardinality bin,
per-parent source-color selection, and the single global leaf-weight bin.

No tree cleanup or CWA argument is performed here.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62ProxyAncestryMetricOutput

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
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)

/-- A genuine metric fiber, transported to ambient fine indices. -/
def ambientCompleteMetricFiber
    (parent : Fin output.metricParents.card) :
    Finset (Fin fine.card) :=
  Finset.image output.mesh.complete.selectedFine.embedding
    (output.completeMetricFiber parent)

/-- The selected-fine family used by the metric is nonempty. -/
theorem selectedFine_nonempty :
    output.selectedFine.Nonempty := by
  rcases output.selected_nonempty with ⟨ambientSource, sourceMem⟩
  have sourceHull :
      ambientSource ∈
        output.mesh.complete.selectedFineIndices := by
    rw [output.selectedFineIndices_eq_selection]
    exact sourceMem
  rcases
      output.mesh.complete.selectedFine_ambient_surjective
        ambientSource sourceHull
    with ⟨source, _⟩
  exact Fin.pos_iff_nonempty.mpr ⟨source⟩

/--
The metric-parent owner on ambient leaves.  Outside the selected packet hull
it takes an irrelevant fixed value; on the hull it is the canonical
selected-fine metric parent.
-/
noncomputable def ambientMetricParentOf
    (ambientSource : Fin fine.card) :
    Fin output.metricParents.card :=
  if sourceMem :
      ambientSource ∈
        output.mesh.complete.selectedFineIndices then
    output.metricParentOf <|
      Classical.choose <|
        output.mesh.complete.selectedFine_ambient_surjective
          ambientSource sourceMem
  else
    output.metricParentOf ⟨0, output.selectedFine_nonempty⟩

@[simp] theorem ambientMetricParentOf_embedding
    (source : Fin output.selectedFine.card) :
    output.ambientMetricParentOf
        (output.mesh.complete.selectedFine.embedding source) =
      output.metricParentOf source := by
  have sourceMem :
      output.mesh.complete.selectedFine.embedding source ∈
        output.mesh.complete.selectedFineIndices :=
    output.mesh.complete.selectedFine_embedding_mem source
  rw [ambientMetricParentOf, dif_pos sourceMem]
  apply congrArg output.metricParentOf
  apply output.mesh.complete.selectedFine.embedding.injective
  exact
    Classical.choose_spec <|
      output.mesh.complete.selectedFine_ambient_surjective
        (output.mesh.complete.selectedFine.embedding source)
        sourceMem

@[simp] theorem mem_ambientCompleteMetricFiber_iff
    (parent : Fin output.metricParents.card)
    (ambientSource : Fin fine.card) :
    ambientSource ∈ output.ambientCompleteMetricFiber parent ↔
      ambientSource ∈
          output.mesh.complete.selectedFineIndices ∧
        output.ambientMetricParentOf ambientSource = parent := by
  constructor
  · intro sourceMem
    rcases Finset.mem_image.mp sourceMem with
      ⟨source, sourceFiber, rfl⟩
    exact
      ⟨output.mesh.complete.selectedFine_embedding_mem source,
        output.ambientMetricParentOf_embedding source |>.trans <|
          (output.mem_completeMetricFiber_iff parent source).mp
            sourceFiber⟩
  · rintro ⟨sourceHull, sourceParent⟩
    rcases
        output.mesh.complete.selectedFine_ambient_surjective
          ambientSource sourceHull
      with ⟨source, sourceEq⟩
    apply Finset.mem_image.mpr
    refine ⟨source, ?_, sourceEq⟩
    apply (output.mem_completeMetricFiber_iff parent source).mpr
    rw [← output.ambientMetricParentOf_embedding source, sourceEq]
    exact sourceParent

theorem ambientCompleteMetricFiber_nonempty
    (parent : Fin output.metricParents.card) :
    (output.ambientCompleteMetricFiber parent).Nonempty :=
  Finset.image_nonempty.mpr
    (output.completeMetricFiber_nonempty parent)

theorem ambientCompleteMetricFiber_card
    (parent : Fin output.metricParents.card) :
    (output.ambientCompleteMetricFiber parent).card =
      (output.completeMetricFiber parent).card := by
  exact
    Finset.card_image_of_injective
      (output.completeMetricFiber parent)
      output.mesh.complete.selectedFine.embedding.injective

theorem ambientCompleteMetricFiber_card_le
    (parent : Fin output.metricParents.card) :
    (output.ambientCompleteMetricFiber parent).card ≤
      output.selectedFine.card := by
  rw [output.ambientCompleteMetricFiber_card parent]
  simpa using
    Finset.card_le_card
      (Finset.subset_univ (output.completeMetricFiber parent))

theorem ambientCompleteMetricFiber_pairwiseDisjoint :
    Set.PairwiseDisjoint
      (Set.univ : Set (Fin output.metricParents.card))
      output.ambientCompleteMetricFiber := by
  intro first _ second _ distinct
  apply Finset.disjoint_left.mpr
  intro ambientSource firstMem secondMem
  have firstParent :
      output.ambientMetricParentOf ambientSource = first :=
    (output.mem_ambientCompleteMetricFiber_iff
      first ambientSource).mp firstMem |>.2
  have secondParent :
      output.ambientMetricParentOf ambientSource = second :=
    (output.mem_ambientCompleteMetricFiber_iff
      second ambientSource).mp secondMem |>.2
  exact distinct (firstParent.symm.trans secondParent)

theorem ambientCompleteMetricFiber_owner
    (parent : Fin output.metricParents.card)
    (ambientSource : Fin fine.card)
    (sourceMem :
      ambientSource ∈ output.ambientCompleteMetricFiber parent) :
    output.ambientMetricParentOf ambientSource = parent :=
  (output.mem_ambientCompleteMetricFiber_iff
    parent ambientSource).mp sourceMem |>.2

theorem metricParentWeight_eq_ambientFiber
    (parent : Fin output.metricParents.card) :
    output.metricParentWeight parent =
      ∑ ambientSource ∈
        output.ambientCompleteMetricFiber parent,
          weight ambientSource := by
  unfold
    metricParentWeight sourceWeight ambientCompleteMetricFiber
  rw [
    Finset.sum_image
      output.mesh.complete.selectedFine.embedding.injective.injOn
  ]

theorem metricParentWeight_ne_top
    (weightFinite : ∀ source : Fin fine.card, weight source ≠ ⊤)
    (parent : Fin output.metricParents.card) :
    output.metricParentWeight parent ≠ ⊤ := by
  unfold metricParentWeight sourceWeight
  exact
    ENNReal.sum_ne_top.mpr fun source _ =>
      weightFinite
        (output.mesh.complete.selectedFine.embedding source)

end PureWZ2Prop62ProxyAncestryMetricOutput

/--
The concrete output immediately before the unique tree cleanup.  Both the
global upper-color selection and the pre-core selection use the ambient images
of the same complete genuine metric fibers.
-/
structure PureWZ2Prop62ProxyQuotientPreCoreAdapterData
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
    (coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate)
    (SourceColor : Type*)
    [Fintype SourceColor] [DecidableEq SourceColor]
    [Nonempty SourceColor]
    (sourceColor : Fin fine.card → SourceColor) where
  global :
    PureWZ2Prop62GlobalUpperEnvelopeParentSelectionData
      schedule fineNonempty quotient width packetCoordinate
      strideBase weight metric coloring Finset.univ
      metric.ambientCompleteMetricFiber metric.metricParentWeight
  global_leaf_monochromatic :
    ∀ leaf ∈ global.wholeLeaves,
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        coloring.leafColor coordinate leaf =
          global.selectedColor coordinate
  preCore :
    PureWZ2Prop62PreCoreSelectionData
      (Fin fine.card) (Fin metric.metricParents.card) SourceColor
      global.selectedParents metric.ambientCompleteMetricFiber
      (fun parent => (metric.ambientCompleteMetricFiber parent).card)
      metric.metricParentWeight metric.ambientMetricParentOf
      sourceColor weight metric.selectedFine.card
  wholeLeaves : Finset (Fin fine.card)
  wholeLeaves_eq : wholeLeaves = preCore.wholeLeaves
  wholeLeaves_subset_global :
    wholeLeaves ⊆ global.wholeLeaves
  leaf_monochromatic :
    ∀ leaf ∈ wholeLeaves,
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        coloring.leafColor coordinate leaf =
          global.selectedColor coordinate

theorem pureWZ2_prop62_proxy_quotient_preCore_adapter
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
    (coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate)
    (SourceColor : Type*)
    [Fintype SourceColor] [DecidableEq SourceColor]
    [Nonempty SourceColor]
    (sourceColor : Fin fine.card → SourceColor)
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
      (PureWZ2Prop62ProxyQuotientPreCoreAdapterData
        schedule fineNonempty quotient width packetCoordinate
        strideBase weight metric coloring SourceColor sourceColor) := by
  have totalMetricParentWeightPos :
      0 <
        ∑ parent ∈
            (Finset.univ :
              Finset (Fin metric.metricParents.card)),
          metric.metricParentWeight parent := by
    simpa using
      (metric.sum_metricParentWeight_eq_selection (weight := weight) ▸
        selectionWeightPos)
  let global :=
    Classical.choice <|
      pureWZ2_prop62_global_upperEnvelope_parent_selection
        schedule fineNonempty quotient width packetCoordinate
        strideBase weight metric coloring Finset.univ
        metric.ambientCompleteMetricFiber metric.metricParentWeight
        totalMetricParentWeightPos
  have globalLeafMonochromatic :
      ∀ leaf ∈ global.wholeLeaves,
        ∀ coordinate :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          coloring.leafColor coordinate leaf =
            global.selectedColor coordinate := by
    intro leaf leafMem coordinate
    rw [global.wholeLeaves_eq] at leafMem
    rcases Finset.mem_biUnion.mp leafMem with
      ⟨parent, parentMem, leafFiber⟩
    rcases Finset.mem_image.mp leafFiber with
      ⟨source, sourceFiber, rfl⟩
    calc
      coloring.leafColor coordinate
          (metric.mesh.complete.selectedFine.embedding source) =
          coloring.metricParentColor metric coordinate
            (metric.section6Cover.toWZ1PaperTubeCover.parent source) :=
        coloring.leafColor_eq_metricParentColor
          metric fineLine fineBase rhoPos widthPos packetScaleLeRho
          sixWidthLe coordinate source
      _ = coloring.metricParentColor metric coordinate parent := by
        have sourceParent :=
          (metric.mem_completeMetricFiber_iff parent source).mp
            sourceFiber
        change
          metric.section6Cover.toWZ1PaperTubeCover.parent source =
            parent at sourceParent
        rw [sourceParent]
      _ = global.selectedColor coordinate :=
        global.monochromatic parent parentMem coordinate
  have globalParentWeightFinite :
      (∑ parent ∈ global.selectedParents,
          metric.metricParentWeight parent) ≠ ⊤ := by
    exact
      ENNReal.sum_ne_top.mpr fun parent _ =>
        metric.metricParentWeight_ne_top weightFinite parent
  have globalParentWeightPos :
      0 <
        ∑ parent ∈ global.selectedParents,
          metric.metricParentWeight parent := by
    by_contra notPositive
    have selectedZero :
        (∑ parent ∈ global.selectedParents,
          metric.metricParentWeight parent) = 0 := by
      exact bot_unique (not_lt.mp notPositive)
    have totalLeZero :
        (∑ parent ∈
            (Finset.univ :
              Finset (Fin metric.metricParents.card)),
          metric.metricParentWeight parent) ≤ 0 := by
      simpa [selectedZero] using global.weighted_retention
    exact (not_le_of_gt totalMetricParentWeightPos) totalLeZero
  let preCore :=
    Classical.choice <|
      pureWZ2_prop62_preCore_selection
        (Fin fine.card) (Fin metric.metricParents.card) SourceColor
        global.selectedParents metric.ambientCompleteMetricFiber
        (fun parent => (metric.ambientCompleteMetricFiber parent).card)
        metric.metricParentWeight metric.ambientMetricParentOf
        sourceColor weight metric.selectedFine.card
        (by
          intro parent _
          rfl)
        (by
          intro parent _
          exact
            Finset.card_pos.mpr
              (metric.ambientCompleteMetricFiber_nonempty parent))
        (by
          intro parent _
          exact metric.ambientCompleteMetricFiber_card_le parent)
        (by
          intro first firstMem second secondMem distinct
          exact
            metric.ambientCompleteMetricFiber_pairwiseDisjoint
              (Set.mem_univ first)
              (Set.mem_univ second)
              distinct)
        (by
          intro parent _ leaf leafMem
          exact
            metric.ambientCompleteMetricFiber_owner
              parent leaf leafMem)
        (by
          intro parent _
          exact metric.metricParentWeight_eq_ambientFiber parent)
        globalParentWeightFinite globalParentWeightPos
  have preCoreWholeLeavesSubsetGlobal :
      preCore.wholeLeaves ⊆ global.wholeLeaves := by
    rw [preCore.wholeLeaves_eq, global.wholeLeaves_eq]
    intro leaf leafMem
    rcases Finset.mem_biUnion.mp leafMem with
      ⟨parent, parentMem, leafFiber⟩
    exact
      Finset.mem_biUnion.mpr
        ⟨parent, preCore.fiberBin.selectedParents_subset parentMem,
          leafFiber⟩
  exact
    ⟨{
      global := global
      global_leaf_monochromatic := globalLeafMonochromatic
      preCore := preCore
      wholeLeaves := preCore.wholeLeaves
      wholeLeaves_eq := rfl
      wholeLeaves_subset_global := preCoreWholeLeavesSubsetGlobal
      leaf_monochromatic := by
        intro leaf leafMem coordinate
        exact
          globalLeafMonochromatic leaf
            (preCoreWholeLeavesSubsetGlobal leafMem) coordinate
    }⟩

end Kakeya.Assouad

end
