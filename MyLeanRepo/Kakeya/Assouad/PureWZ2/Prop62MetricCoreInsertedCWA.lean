import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricInsertedCoreCWA

/-!
# Proposition 6.2 metric parents: final-core inserted CWA

The metric-core restriction reindexes both the final fine family and exactly
the metric parents still hit by it.  This module transports the ambient-index
inserted CWA to those final families without changing the fiber or adding a
loss.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem PureWZ2Prop62MetricCoreRestrictionData.insertedFiberCWA
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData fine scale C}
    {width M : ℝ}
    (metric :
      PureWZ2Prop62MetricPacketOutput
        (rho := rho) oldData width M)
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        metric.selectedFine ambientConstant scaleWindow}
    (auxiliary :
      PureWZ2Prop62AuxiliaryLevel
        schedule (Fin metric.metricParents.card))
    (label_eq :
      ∀ source,
        auxiliary.label source =
          metric.metricInput.packetParent
            (metric.mesh.restrictedOldData.cover.parent source))
    (selected : Finset (Fin metric.selectedFine.card))
    (restriction :
      PureWZ2Prop62MetricCoreRestrictionData
        metric.section6Cover
        (auxiliary.coreIndices selected))
    (parent : Fin restriction.coarseSelected.family.card)
    (convexSet : Set Point3)
    (convex : Convex ℝ convexSet) :
    (((wz2PaperFullFiberIndices
        restriction.fineSelected.family
        restriction.coarseSelected.family parent).filter
        fun source =>
          wz2PaperLiteralUnitRescalingMap
              (restriction.coarseSelected.family.tube parent)
              metric.metricInput.rho_pos ''
            (restriction.fineSelected.family.tube source).carrier ⊆
              convexSet).card : ENNReal) ≤
      (pureWZ2Prop62InsertedCWALoss rho scale C *
        auxiliary.densityLoss selected) *
        volume convexSet *
        ((wz2PaperFullFiberIndices
          restriction.fineSelected.family
          restriction.coarseSelected.family parent).card :
          ENNReal) := by
  let ambientParent :=
    restriction.coarseSelected.embedding parent
  let finalFiber :=
    wz2PaperFullFiberIndices
      restriction.fineSelected.family
      restriction.coarseSelected.family parent
  let ambientCoreFiber :=
    auxiliary.coreIndices selected ∩
      wz2PaperFullFiberIndices
        metric.selectedFine metric.metricParents ambientParent
  have fiberImageEq :
      Finset.image restriction.fineSelected.embedding finalFiber =
        ambientCoreFiber := by
    simpa only [finalFiber, ambientCoreFiber, ambientParent] using
      restriction.fiber_image_eq parent
  have finalFiberNonempty : finalFiber.Nonempty := by
    rcases restriction.lineCover.parent_surjective parent with
      ⟨source, parentEq⟩
    exact
      ⟨source,
        (mem_wz2PaperFullFiberIndices_iff parent source).mpr <| by
          rw [← parentEq]
          exact restriction.lineCover.parent_covers source⟩
  have ambientCoreFiberNonempty : ambientCoreFiber.Nonempty := by
    rcases finalFiberNonempty with ⟨source, sourceMem⟩
    refine
      ⟨restriction.fineSelected.embedding source, ?_⟩
    rw [← fiberImageEq]
    exact Finset.mem_image.mpr ⟨source, sourceMem, rfl⟩
  let finalPredicate :
      Fin restriction.fineSelected.family.card → Prop :=
    fun source =>
      wz2PaperLiteralUnitRescalingMap
          (restriction.coarseSelected.family.tube parent)
          metric.metricInput.rho_pos ''
        (restriction.fineSelected.family.tube source).carrier ⊆ convexSet
  let ambientPredicate : Fin metric.selectedFine.card → Prop :=
    fun source =>
      wz2PaperLiteralUnitRescalingMap
          (metric.metricParents.tube ambientParent)
          metric.metricInput.rho_pos ''
        (metric.selectedFine.tube source).carrier ⊆ convexSet
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
            Finset.image restriction.fineSelected.embedding finalFiber := by
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
        (ambientCoreFiber.filter ambientPredicate).card := by
    rw [← filteredImage]
    exact
      (Finset.card_image_of_injective _
        restriction.fineSelected.embedding.injective).symm
  have fiberCard :
      finalFiber.card = ambientCoreFiber.card := by
    calc
      finalFiber.card =
          (Finset.image restriction.fineSelected.embedding finalFiber).card :=
        (Finset.card_image_of_injective _
          restriction.fineSelected.embedding.injective).symm
      _ = ambientCoreFiber.card := congrArg Finset.card fiberImageEq
  have ambientBound :=
    metric.inserted_cwa_after_core
      auxiliary label_eq selected ambientParent
      ambientCoreFiberNonempty convexSet convex
  change
    ((finalFiber.filter finalPredicate).card : ENNReal) ≤
      (pureWZ2Prop62InsertedCWALoss rho scale C *
        auxiliary.densityLoss selected) *
        volume convexSet * (finalFiber.card : ENNReal)
  rw [filteredCard, fiberCard]
  exact ambientBound

end Kakeya.Assouad

end
