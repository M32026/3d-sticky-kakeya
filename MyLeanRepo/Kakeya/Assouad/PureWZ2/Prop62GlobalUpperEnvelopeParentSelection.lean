import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientPrefixBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.FiniteColoredDegreeSelection

/-!
# Global upper-envelope color selection on metric parents

Starting from an arbitrary nonempty weighted set of metric parents, perform
one dependent color-vector pigeonhole over all upper coordinates.  The
selected parents remain whole: the associated leaf set is exactly the union
of their supplied complete fibers.

This module performs no fiber-cardinality binning, leaf selection, or tree
cleanup.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The number of old upper coordinates is at most the full schedule depth. -/
theorem pureWZ2Prop62_proxyUpperCoordinate_card_le_levelCount
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (packetCoordinate : Fin schedule.levelCount) :
    Fintype.card
        (schedule.ProxyUpperCoordinate rho packetCoordinate) ≤
      schedule.levelCount := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective
      (fun coordinate :
        schedule.ProxyUpperCoordinate rho packetCoordinate =>
          coordinate.1)
      (fun first second equality => Subtype.ext equality)

/--
One global upper-envelope color-vector class of metric parents.

`completeFiber` is deliberately an input in the ambient leaf type.  The
selection changes only the parent set, and `wholeLeaves` is exactly the union
of complete fibers of the retained parents.
-/
structure PureWZ2Prop62GlobalUpperEnvelopeParentSelectionData
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
    (baseSelectedParents :
      Finset (Fin metric.metricParents.card))
    (completeFiber :
      Fin metric.metricParents.card → Finset (Fin fine.card))
    (parentWeight :
      Fin metric.metricParents.card → ENNReal) where
  selectedColor :
    ∀ coordinate :
        schedule.ProxyUpperCoordinate rho packetCoordinate,
      Fin (pureWZ2Prop62UpperEnvelopeConflictDegree + 1)
  selectedParents :
    Finset (Fin metric.metricParents.card)
  selectedParents_eq :
    selectedParents =
      baseSelectedParents.filter fun parent =>
        ∀ coordinate :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          coloring.metricParentColor metric coordinate parent =
            selectedColor coordinate
  selectedParents_nonempty :
    selectedParents.Nonempty
  selectedParents_subset :
    selectedParents ⊆ baseSelectedParents
  monochromatic :
    ∀ parent ∈ selectedParents,
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        coloring.metricParentColor metric coordinate parent =
          selectedColor coordinate
  colorVectorCardinality : ℕ
  colorVectorCardinality_eq :
    colorVectorCardinality =
      Fintype.card
        (∀ coordinate :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          Fin (pureWZ2Prop62UpperEnvelopeConflictDegree + 1))
  upperColorLoss : ENNReal
  upperColorLoss_eq :
    upperColorLoss = colorVectorCardinality
  weighted_retention :
    (∑ parent ∈ baseSelectedParents, parentWeight parent) ≤
      upperColorLoss *
        ∑ parent ∈ selectedParents, parentWeight parent
  wholeLeaves : Finset (Fin fine.card)
  wholeLeaves_eq :
    wholeLeaves =
      selectedParents.biUnion completeFiber
  complete_metric_fibers :
    ∀ parent ∈ selectedParents,
      completeFiber parent ⊆ wholeLeaves

theorem pureWZ2_prop62_global_upperEnvelope_parent_selection
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
    (baseSelectedParents :
      Finset (Fin metric.metricParents.card))
    (completeFiber :
      Fin metric.metricParents.card → Finset (Fin fine.card))
    (parentWeight :
      Fin metric.metricParents.card → ENNReal)
    (totalWeightPos :
      0 <
        ∑ parent ∈ baseSelectedParents,
          parentWeight parent) :
    Nonempty
      (PureWZ2Prop62GlobalUpperEnvelopeParentSelectionData
        schedule fineNonempty quotient width packetCoordinate
        strideBase weight metric coloring baseSelectedParents
        completeFiber parentWeight) := by
  let Parent :=
    {parent : Fin metric.metricParents.card //
      parent ∈ baseSelectedParents}
  let UpperCoordinate :=
    schedule.ProxyUpperCoordinate rho packetCoordinate
  let coordinateCount := Fintype.card UpperCoordinate
  let coordinateEquiv : Fin coordinateCount ≃ UpperCoordinate :=
    (Fintype.equivFin UpperCoordinate).symm
  let Color : Fin coordinateCount → Type :=
    fun _ => Fin (pureWZ2Prop62UpperEnvelopeConflictDegree + 1)
  let parentColor :
      ∀ coordinate : Fin coordinateCount, Parent → Color coordinate :=
    fun coordinate parent =>
      coloring.metricParentColor metric
        (coordinateEquiv coordinate) parent.1
  let restrictedWeight : Parent → ENNReal :=
    fun parent => parentWeight parent.1
  rcases
      wz2_finite_dependent_color_weighted_pigeonhole
        coordinateCount Color parentColor restrictedWeight
    with ⟨chosenVector, retained⟩
  let selectedColor :
      ∀ coordinate : UpperCoordinate,
        Fin (pureWZ2Prop62UpperEnvelopeConflictDegree + 1) :=
    fun coordinate =>
      chosenVector (coordinateEquiv.symm coordinate)
  let selectedSubtype : Finset Parent :=
    Finset.univ.filter fun parent =>
      ∀ coordinate : Fin coordinateCount,
        parentColor coordinate parent = chosenVector coordinate
  let selectedParents :
      Finset (Fin metric.metricParents.card) :=
    selectedSubtype.image fun parent => parent.1
  have selectedSubtypeSum :
      (∑ parent ∈ selectedSubtype, restrictedWeight parent) =
        ∑ parent ∈ selectedParents, parentWeight parent := by
    apply Finset.sum_bij
        (fun parent _ => parent.1)
    · intro parent parentMem
      exact Finset.mem_image.mpr ⟨parent, parentMem, rfl⟩
    · intro first _ second _ equality
      exact Subtype.ext equality
    · intro parent parentMem
      rcases Finset.mem_image.mp parentMem with
        ⟨selectedParent, selectedParentMem, equality⟩
      exact ⟨selectedParent, selectedParentMem, equality⟩
    · intro parent _
      rfl
  have baseWeightSum :
      (∑ parent : Parent, restrictedWeight parent) =
        ∑ parent ∈ baseSelectedParents, parentWeight parent :=
    Finset.sum_coe_sort baseSelectedParents parentWeight
  have colorCardinality :
      Fintype.card (∀ coordinate : Fin coordinateCount, Color coordinate) =
        Fintype.card
          (∀ coordinate : UpperCoordinate,
            Fin (pureWZ2Prop62UpperEnvelopeConflictDegree + 1)) := by
    simp [Color, coordinateCount, Fintype.card_pi]
  have weightedRetention :
      (∑ parent ∈ baseSelectedParents, parentWeight parent) ≤
        (Fintype.card
          (∀ coordinate : UpperCoordinate,
            Fin (pureWZ2Prop62UpperEnvelopeConflictDegree + 1)) :
          ENNReal) *
          ∑ parent ∈ selectedParents, parentWeight parent := by
    rw [← baseWeightSum, ← selectedSubtypeSum, ← colorCardinality]
    simpa only [selectedSubtype] using retained
  have selectedSubtypeNonempty : selectedSubtype.Nonempty := by
    by_contra selectedEmpty
    have selectedEq : selectedSubtype = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp selectedEmpty
    have totalLeZero :
        (∑ parent ∈ baseSelectedParents,
            parentWeight parent) ≤ 0 := by
      simpa [selectedParents, selectedEq] using weightedRetention
    exact (not_le_of_gt totalWeightPos) totalLeZero
  have selectedParentsNonempty : selectedParents.Nonempty := by
    exact Finset.image_nonempty.mpr selectedSubtypeNonempty
  have selectedParentsSubset :
      selectedParents ⊆ baseSelectedParents := by
    intro parent parentMem
    rcases Finset.mem_image.mp parentMem with
      ⟨selectedParent, _selectedParentMem, rfl⟩
    exact selectedParent.2
  have selectedParentsEq :
      selectedParents =
        baseSelectedParents.filter fun parent =>
          ∀ coordinate : UpperCoordinate,
            coloring.metricParentColor metric coordinate parent =
              selectedColor coordinate := by
    ext parent
    constructor
    · intro parentMem
      rcases Finset.mem_image.mp parentMem with
        ⟨selectedParent, selectedParentMem, parentEq⟩
      subst parent
      refine
        Finset.mem_filter.mpr
          ⟨selectedParent.2, ?_⟩
      have selectedCondition :=
        (Finset.mem_filter.mp selectedParentMem).2
      intro coordinate
      have coordinateCondition :=
        selectedCondition (coordinateEquiv.symm coordinate)
      simpa [parentColor, selectedColor] using coordinateCondition
    · intro parentMem
      have parentInBase := (Finset.mem_filter.mp parentMem).1
      have parentColorEq := (Finset.mem_filter.mp parentMem).2
      let selectedParent : Parent := ⟨parent, parentInBase⟩
      apply Finset.mem_image.mpr
      refine ⟨selectedParent, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ selectedParent, ?_⟩
      intro coordinate
      have upperColor :=
        parentColorEq (coordinateEquiv coordinate)
      change
        coloring.metricParentColor metric
            (coordinateEquiv coordinate) parent =
          chosenVector coordinate
      exact upperColor.trans <|
        congrArg chosenVector
          (coordinateEquiv.symm_apply_apply coordinate)
  let wholeLeaves : Finset (Fin fine.card) :=
    selectedParents.biUnion completeFiber
  exact
    ⟨{
      selectedColor := selectedColor
      selectedParents := selectedParents
      selectedParents_eq := selectedParentsEq
      selectedParents_nonempty := selectedParentsNonempty
      selectedParents_subset := selectedParentsSubset
      monochromatic := by
        intro parent parentMem coordinate
        rw [selectedParentsEq] at parentMem
        exact (Finset.mem_filter.mp parentMem).2 coordinate
      colorVectorCardinality :=
        Fintype.card
          (∀ coordinate : UpperCoordinate,
            Fin (pureWZ2Prop62UpperEnvelopeConflictDegree + 1))
      colorVectorCardinality_eq := rfl
      upperColorLoss :=
        Fintype.card
          (∀ coordinate : UpperCoordinate,
            Fin (pureWZ2Prop62UpperEnvelopeConflictDegree + 1))
      upperColorLoss_eq := rfl
      weighted_retention := weightedRetention
      wholeLeaves := wholeLeaves
      wholeLeaves_eq := rfl
      complete_metric_fibers := by
        intro parent parentMem
        exact Finset.subset_biUnion_of_mem completeFiber parentMem
    }⟩

namespace PureWZ2Prop62GlobalUpperEnvelopeParentSelectionData

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
    {coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {baseSelectedParents :
      Finset (Fin metric.metricParents.card)}
    {completeFiber :
      Fin metric.metricParents.card → Finset (Fin fine.card)}
    {parentWeight :
      Fin metric.metricParents.card → ENNReal}
    (selection :
      PureWZ2Prop62GlobalUpperEnvelopeParentSelectionData
        schedule fineNonempty quotient width packetCoordinate
        strideBase weight metric coloring baseSelectedParents
        completeFiber parentWeight)

theorem colorVectorCardinality_eq_power :
    selection.colorVectorCardinality =
      (pureWZ2Prop62UpperEnvelopeConflictDegree + 1) ^
        Fintype.card
          (schedule.ProxyUpperCoordinate rho packetCoordinate) := by
  rw [selection.colorVectorCardinality_eq]
  simp [Fintype.card_pi]

theorem upperColorLoss_eq_power :
    selection.upperColorLoss =
      ((pureWZ2Prop62UpperEnvelopeConflictDegree + 1 : ℕ) :
        ENNReal) ^
        Fintype.card
          (schedule.ProxyUpperCoordinate rho packetCoordinate) := by
  rw [selection.upperColorLoss_eq,
    selection.colorVectorCardinality_eq_power]
  norm_cast

theorem upperColorLoss_le_depthBound
    {depthBound : ℕ}
    (depthLe : schedule.levelCount ≤ depthBound) :
    selection.upperColorLoss ≤
      ((pureWZ2Prop62UpperEnvelopeConflictDegree + 1 : ℕ) :
        ENNReal) ^ depthBound := by
  rw [selection.upperColorLoss_eq_power]
  exact
    pow_le_pow_right₀ (by norm_num) <|
      (pureWZ2Prop62_proxyUpperCoordinate_card_le_levelCount
        schedule packetCoordinate).trans depthLe

theorem completeFiber_subset_wholeLeaves
    {parent : Fin metric.metricParents.card}
    (parentMem : parent ∈ selection.selectedParents) :
    completeFiber parent ⊆ selection.wholeLeaves :=
  selection.complete_metric_fibers parent parentMem

end PureWZ2Prop62GlobalUpperEnvelopeParentSelectionData

end Kakeya.Assouad

end
