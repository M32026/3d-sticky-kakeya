import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyAncestryMetricOutput

/-!
# Canonical metric-parent weights

The metric construction first forms a complete packet hull and then assigns
every selected fine tube to one genuine metric parent.  This module pulls an
ambient fine-tube weight through the selected-fine embedding and sums it over
the genuine full metric fibers.
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

/-- Ambient weight pulled back to the complete selected-fine packet hull. -/
def sourceWeight
    (source : Fin output.selectedFine.card) : ENNReal :=
  weight (output.mesh.complete.selectedFine.embedding source)

/-- The genuine Section 6 metric parent of one selected fine source. -/
def metricParentOf
    (source : Fin output.selectedFine.card) :
    Fin output.metricParents.card :=
  output.section6Cover.toWZ1PaperTubeCover.parent source

/-- The complete genuine geometric fiber of one metric parent. -/
def completeMetricFiber
    (parent : Fin output.metricParents.card) :
    Finset (Fin output.selectedFine.card) :=
  wz2PaperFullFiberIndices
    output.selectedFine output.metricParents parent

/-- Total pulled-back source weight in one complete metric fiber. -/
def metricParentWeight
    (parent : Fin output.metricParents.card) : ENNReal :=
  ∑ source ∈ output.completeMetricFiber parent,
    output.sourceWeight source

@[simp] theorem mem_completeMetricFiber_iff
    (parent : Fin output.metricParents.card)
    (source : Fin output.selectedFine.card) :
    source ∈ output.completeMetricFiber parent ↔
      output.metricParentOf source = parent := by
  unfold completeMetricFiber metricParentOf
  let cover := output.section6Cover.toWZ1PaperTubeCover
  constructor
  · intro sourceMem
    exact
      (cover.parent_unique source parent
        ((mem_wz2PaperFullFiberIndices_iff parent source).mp
          sourceMem)).symm
  · intro parentEq
    rw [← parentEq]
    exact
      (mem_wz2PaperFullFiberIndices_iff
        (cover.parent source) source).mpr
        (cover.parent_covers source)

theorem completeMetricFiber_nonempty
    (parent : Fin output.metricParents.card) :
    (output.completeMetricFiber parent).Nonempty := by
  rcases output.section6Cover.parent_hit parent with
    ⟨source, sourceCovers⟩
  refine ⟨source, ?_⟩
  exact
    (mem_wz2PaperFullFiberIndices_iff parent source).mpr
      sourceCovers

theorem metricParentWeight_pos
    (weightPos : ∀ source : Fin fine.card, 0 < weight source)
    (parent : Fin output.metricParents.card) :
    0 < output.metricParentWeight parent := by
  rcases output.completeMetricFiber_nonempty parent with
    ⟨source, sourceMem⟩
  exact
    (weightPos
      (output.mesh.complete.selectedFine.embedding source)).trans_le <|
      Finset.single_le_sum
        (f := fun selectedSource =>
          output.sourceWeight selectedSource)
        (fun _ _ => by positivity)
        sourceMem

theorem completeMetricFiber_pairwiseDisjoint :
    Set.PairwiseDisjoint
      (Set.univ : Set (Fin output.metricParents.card))
      output.completeMetricFiber := by
  intro first _ second _ distinct
  apply Finset.disjoint_left.mpr
  intro source sourceFirst sourceSecond
  have firstParent :
      output.metricParentOf source = first :=
    (output.mem_completeMetricFiber_iff first source).mp
      sourceFirst
  have secondParent :
      output.metricParentOf source = second :=
    (output.mem_completeMetricFiber_iff second source).mp
      sourceSecond
  exact distinct (firstParent.symm.trans secondParent)

theorem completeMetricFiber_biUnion_univ :
    (Finset.univ :
      Finset (Fin output.metricParents.card)).biUnion
        output.completeMetricFiber =
      Finset.univ := by
  ext source
  constructor
  · intro _
    exact Finset.mem_univ source
  · intro _
    exact
      Finset.mem_biUnion.mpr
        ⟨output.metricParentOf source,
          Finset.mem_univ _,
          (output.mem_completeMetricFiber_iff
            (output.metricParentOf source) source).mpr rfl⟩

theorem sum_metricParentWeight :
    (∑ parent : Fin output.metricParents.card,
        output.metricParentWeight parent) =
      ∑ source : Fin output.selectedFine.card,
        output.sourceWeight source := by
  unfold metricParentWeight
  have fibersDisjoint :
      (↑(Finset.univ :
        Finset (Fin output.metricParents.card)) :
          Set (Fin output.metricParents.card)).PairwiseDisjoint
        output.completeMetricFiber := by
    simpa using output.completeMetricFiber_pairwiseDisjoint
  rw [← Finset.sum_biUnion fibersDisjoint]
  rw [output.completeMetricFiber_biUnion_univ]

theorem sum_sourceWeight_eq_packetHull :
    (∑ source : Fin output.selectedFine.card,
        output.sourceWeight source) =
      ∑ ambientSource ∈
        output.mesh.complete.selectedFineIndices,
          weight ambientSource := by
  unfold sourceWeight
  have imageEq :
      Finset.image output.mesh.complete.selectedFine.embedding
          (Finset.univ :
            Finset (Fin output.selectedFine.card)) =
        output.mesh.complete.selectedFineIndices := by
    ext ambientSource
    constructor
    · intro sourceImage
      rcases Finset.mem_image.mp sourceImage with
        ⟨source, _sourceMem, rfl⟩
      exact
        output.mesh.complete.selectedFine_embedding_mem source
    · intro sourceMem
      rcases
          output.mesh.complete.selectedFine_ambient_surjective
            ambientSource sourceMem
        with ⟨source, sourceEq⟩
      exact
        Finset.mem_image.mpr
          ⟨source, Finset.mem_univ source, sourceEq⟩
  have imageSum :
      (∑ ambientSource ∈
          Finset.image output.mesh.complete.selectedFine.embedding
            (Finset.univ :
              Finset (Fin output.selectedFine.card)),
          weight ambientSource) =
        ∑ source : Fin output.selectedFine.card,
          weight
            (output.mesh.complete.selectedFine.embedding source) := by
    simpa only [Finset.sum_const_zero, Finset.sum_attach] using
      Finset.sum_image
        output.mesh.complete.selectedFine.embedding.injective.injOn
  rw [← imageSum, imageEq]

theorem sum_metricParentWeight_eq_packetHull :
    (∑ parent : Fin output.metricParents.card,
        output.metricParentWeight parent) =
      ∑ ambientSource ∈
        output.mesh.complete.selectedFineIndices,
          weight ambientSource := by
  rw [output.sum_metricParentWeight,
    output.sum_sourceWeight_eq_packetHull]

theorem sum_metricParentWeight_eq_selection :
    (∑ parent : Fin output.metricParents.card,
        output.metricParentWeight parent) =
      ∑ ambientSource ∈ output.selection.selected,
        weight ambientSource := by
  rw [output.sum_metricParentWeight_eq_packetHull,
    output.selectedFineIndices_eq_selection]

end PureWZ2Prop62ProxyAncestryMetricOutput

end Kakeya.Assouad

end
