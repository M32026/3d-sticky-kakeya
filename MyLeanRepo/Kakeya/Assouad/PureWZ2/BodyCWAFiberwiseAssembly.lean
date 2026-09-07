import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12

/-!
# Convex-Wolff assembly from parent fibers

If a finite body family is partitioned by a parent map and every parent
fiber satisfies the same normalized Convex-Wolff bound, then the whole family
satisfies that bound.  Summing the fiber estimates introduces no factor
depending on the number of parent fibers.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The body subfamily in one fiber of an arbitrary finite parent map. -/
def wz2PaperBodyParentFiber
    (family : Kakeya.Streamlined.BodyFamily)
    {parentCount : ℕ}
    (parent : Fin family.card → Fin parentCount)
    (parentIndex : Fin parentCount) :
    Kakeya.Streamlined.BodyFamily where
  card :=
    (Finset.univ.filter fun index =>
      parent index = parentIndex).card
  body fiberIndex :=
    family.body
      ((Finset.univ.filter fun index =>
        parent index = parentIndex).orderEmbOfFin rfl fiberIndex)

/--
Uniform Convex-Wolff counting on all fibers of a finite parent map assembles
to uniform counting on the entire indexed family.
-/
theorem wz2PaperBodyConvexWolffBound_of_parent_fibers
    {family : Kakeya.Streamlined.BodyFamily}
    {parentCount : ℕ}
    (parentCountPos : 0 < parentCount)
    (parent : Fin family.card → Fin parentCount)
    {C : ENNReal}
    (fiberCWA :
      ∀ parentIndex,
        WZ2PaperBodyConvexWolffBound
          (wz2PaperBodyParentFiber
            family parent parentIndex) C) :
    WZ2PaperBodyConvexWolffBound family C := by
  intro convexSet hconvex
  let parents : Finset (Fin parentCount) :=
    Finset.univ
  let contained :=
    family.containedIndices convexSet
  have containedPartition :
      ∑ parentIndex ∈ parents,
          (contained.filter fun index =>
            parent index = parentIndex).card =
        contained.card := by
    simpa [parents] using
      (Finset.sum_card_fiberwise_eq_card_filter
        contained parents parent).trans (by
          simp [parents])
  have fiberContainedCount :
      ∀ parentIndex,
        (wz2PaperBodyParentFiber
          family parent parentIndex).containedCount convexSet =
        ((contained.filter fun index =>
          parent index = parentIndex).card : ENNReal) := by
    intro parentIndex
    let fiberIndices :=
      Finset.univ.filter fun index =>
        parent index = parentIndex
    let fiber :=
      wz2PaperBodyParentFiber family parent parentIndex
    let embedding :
        Fin fiber.card → Fin family.card :=
      fiberIndices.orderEmbOfFin rfl
    have imageContained :
        Finset.image embedding
            (fiber.containedIndices convexSet) =
          contained.filter fun index =>
            parent index = parentIndex := by
      ext index
      constructor
      · intro hindex
        rcases Finset.mem_image.mp hindex with
          ⟨fiberIndex, hfiberIndex, rfl⟩
        have hfiberCarrier :
            (fiber.body fiberIndex).carrier ⊆
              convexSet :=
          Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mp
            hfiberIndex
        have hparent :
            parent (embedding fiberIndex) =
              parentIndex :=
          (Finset.mem_filter.mp
            (Finset.orderEmbOfFin_mem
              fiberIndices rfl fiberIndex)).2
        exact
          Finset.mem_filter.mpr
            ⟨Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mpr
                hfiberCarrier,
              hparent⟩
      · intro hindex
        have hcontained :=
          (Finset.mem_filter.mp hindex).1
        have hparent :=
          (Finset.mem_filter.mp hindex).2
        have hindexFiber :
            index ∈ fiberIndices :=
          Finset.mem_filter.mpr
            ⟨Finset.mem_univ index, hparent⟩
        let fiberIndex : Fin fiber.card :=
          (fiberIndices.orderIsoOfFin rfl).symm
            ⟨index, hindexFiber⟩
        have embeddingEq :
            embedding fiberIndex = index :=
          congrArg Subtype.val
            (fiberIndices.orderIsoOfFin rfl
              |>.apply_symm_apply
                ⟨index, hindexFiber⟩)
        refine
          Finset.mem_image.mpr
            ⟨fiberIndex, ?_, embeddingEq⟩
        apply
          Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mpr
        change
          (family.body (embedding fiberIndex)).carrier ⊆
            convexSet
        rw [embeddingEq]
        exact
          Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mp
            hcontained
    unfold Kakeya.Streamlined.BodyFamily.containedCount
    rw [← imageContained]
    norm_cast
    exact
      (Finset.card_image_of_injective
        (fiber.containedIndices convexSet)
        (fiberIndices.orderEmbOfFin rfl).injective).symm
  have fiberCard :
      ∀ parentIndex,
        (wz2PaperBodyParentFiber
          family parent parentIndex).enncard =
        ((Finset.univ.filter fun index =>
          parent index = parentIndex).card : ENNReal) := by
    intro parentIndex
    rfl
  have totalFiberCard :
      ∑ parentIndex ∈ parents,
          (wz2PaperBodyParentFiber
            family parent parentIndex).enncard =
        family.enncard := by
    rw [show
      ∑ parentIndex ∈ parents,
          (wz2PaperBodyParentFiber
            family parent parentIndex).enncard =
        ∑ parentIndex ∈ parents,
          ((Finset.univ.filter fun index =>
            parent index = parentIndex).card :
            ENNReal) by
        apply Finset.sum_congr rfl
        intro parentIndex _
        exact fiberCard parentIndex]
    have hpartition :
        ∑ parentIndex ∈ parents,
            (Finset.univ.filter fun index =>
              parent index = parentIndex).card =
          family.card := by
      simpa [parents] using
        (Finset.sum_card_fiberwise_eq_card_filter
          (Finset.univ : Finset (Fin family.card))
          parents parent).trans (by simp [parents])
    change
      ∑ parentIndex ∈ parents,
          ((Finset.univ.filter fun index =>
            parent index = parentIndex).card : ENNReal) =
        (family.card : ENNReal)
    exact_mod_cast hpartition
  calc
    family.containedCount convexSet =
        ∑ parentIndex ∈ parents,
          (wz2PaperBodyParentFiber
            family parent parentIndex).containedCount convexSet := by
      unfold Kakeya.Streamlined.BodyFamily.containedCount
      rw [show
        (family.containedIndices convexSet).card =
          ∑ parentIndex ∈ parents,
            ((family.containedIndices convexSet).filter
              fun index =>
                parent index = parentIndex).card by
          exact containedPartition.symm]
      norm_cast
      apply Finset.sum_congr rfl
      intro parentIndex _
      change
        ((family.containedIndices convexSet).filter fun index =>
          parent index = parentIndex).card =
        ((wz2PaperBodyParentFiber
          family parent parentIndex).containedIndices convexSet).card
      have hcount := fiberContainedCount parentIndex
      unfold Kakeya.Streamlined.BodyFamily.containedCount at hcount
      exact_mod_cast hcount.symm
    _ ≤
        ∑ parentIndex ∈ parents,
          C * volume convexSet *
            (wz2PaperBodyParentFiber
              family parent parentIndex).enncard := by
      apply Finset.sum_le_sum
      intro parentIndex _
      exact fiberCWA parentIndex convexSet hconvex
    _ =
        C * volume convexSet *
          family.enncard := by
      calc
        ∑ parentIndex ∈ parents,
            C * volume convexSet *
              (wz2PaperBodyParentFiber
                family parent parentIndex).enncard =
            (C * volume convexSet) *
              ∑ parentIndex ∈ parents,
                (wz2PaperBodyParentFiber
                  family parent parentIndex).enncard := by
          exact
            (Finset.mul_sum parents
              (fun parentIndex =>
                (wz2PaperBodyParentFiber
                  family parent parentIndex).enncard)
              (C * volume convexSet)).symm
        _ = (C * volume convexSet) * family.enncard := by
          rw [totalFiberCard]
        _ = C * volume convexSet * family.enncard := rfl

end Kakeya.Assouad

end
