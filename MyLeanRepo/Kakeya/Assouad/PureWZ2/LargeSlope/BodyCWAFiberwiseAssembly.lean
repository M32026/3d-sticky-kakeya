import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12

/-!
# Convex--Wolff assembly from finite parent fibers

If a finite body family is partitioned by a parent map and every parent
fiber satisfies the same normalized Convex--Wolff bound, summing the fiber
estimates gives the same bound on the whole family.  There is no factor
depending on the number of fibers.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Reindex a finite body family by an embedding. -/
def pureWZ2BodySubfamilyByEmbedding
    (source : Kakeya.Streamlined.BodyFamily)
    {targetCard : ℕ}
    (embedding : Fin targetCard ↪ Fin source.card) :
    Kakeya.Streamlined.BodyFamily where
  card := targetCard
  body index := source.body (embedding index)

/-- A cardinality-retaining indexed subfamily of a body family inherits the
normalized CWA bound.  The embedding is explicit because actual-John packet
families are not ordinary tube subfamilies. -/
theorem pureWZ2_bodyCWA_of_weighted_indexed_subfamily
    {source target : Kakeya.Streamlined.BodyFamily}
    (embedding : Fin target.card ↪ Fin source.card)
    (carrier_eq : ∀ index,
      (target.body index).carrier =
        (source.body (embedding index)).carrier)
    {weight K C : ENNReal}
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hcardinality :
      weight * source.enncard ≤ K * target.enncard)
    (hsource : WZ2PaperBodyConvexWolffBound source C) :
    WZ2PaperBodyConvexWolffBound target ((weight⁻¹ * K) * C) := by
  intro convexSet hconvex
  let targetContained := target.containedIndices convexSet
  let sourceContained := source.containedIndices convexSet
  have himage : Finset.image embedding targetContained ⊆ sourceContained := by
    intro sourceIndex hsourceIndex
    rcases Finset.mem_image.mp hsourceIndex with
      ⟨targetIndex, htargetIndex, rfl⟩
    apply Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mpr
    rw [← carrier_eq targetIndex]
    exact Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mp
      htargetIndex
  have hcount : target.containedCount convexSet ≤
      source.containedCount convexSet := by
    change (targetContained.card : ENNReal) ≤
      (sourceContained.card : ENNReal)
    exact_mod_cast (show targetContained.card ≤ sourceContained.card by
      calc
        targetContained.card =
            (Finset.image embedding targetContained).card :=
          (Finset.card_image_of_injective
            targetContained embedding.injective).symm
        _ ≤ sourceContained.card := Finset.card_le_card himage)
  calc
    target.containedCount convexSet ≤ source.containedCount convexSet := hcount
    _ ≤ C * MeasureTheory.volume convexSet * source.enncard :=
      hsource convexSet hconvex
    _ = weight⁻¹ *
        (weight * (C * MeasureTheory.volume convexSet * source.enncard)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hweightZero hweightTop, one_mul]
    _ ≤ weight⁻¹ *
        (C * MeasureTheory.volume convexSet * (K * target.enncard)) := by
      apply mul_le_mul_left' _ weight⁻¹
      calc
        weight * (C * MeasureTheory.volume convexSet * source.enncard) =
            (C * MeasureTheory.volume convexSet) *
              (weight * source.enncard) := by ring
        _ ≤ (C * MeasureTheory.volume convexSet) *
              (K * target.enncard) :=
          mul_le_mul_left' hcardinality _
    _ = (weight⁻¹ * K) * C * MeasureTheory.volume convexSet *
        target.enncard := by ring

/-- Specialized constructor form of the weighted body-subfamily transfer. -/
theorem pureWZ2_bodyCWA_subfamilyByEmbedding
    {source : Kakeya.Streamlined.BodyFamily}
    {targetCard : ℕ}
    (embedding : Fin targetCard ↪ Fin source.card)
    {weight K C : ENNReal}
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hcardinality :
      weight * source.enncard ≤ K * (targetCard : ENNReal))
    (hsource : WZ2PaperBodyConvexWolffBound source C) :
    WZ2PaperBodyConvexWolffBound
      (pureWZ2BodySubfamilyByEmbedding source embedding)
      ((weight⁻¹ * K) * C) := by
  apply pureWZ2_bodyCWA_of_weighted_indexed_subfamily
    (source := source)
    (target := pureWZ2BodySubfamilyByEmbedding source embedding)
    embedding (fun _ => rfl) hweightZero hweightTop
  · simpa [pureWZ2BodySubfamilyByEmbedding,
      Kakeya.Streamlined.BodyFamily.enncard] using hcardinality
  · exact hsource

/-- The body subfamily in one fiber of an arbitrary finite parent map. -/
def pureWZ2BodyParentFiber
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

/-- Uniform body CWA on the fibers of a finite map assembles with no loss. -/
theorem pureWZ2_bodyCWA_of_parent_fibers
    {family : Kakeya.Streamlined.BodyFamily}
    {parentCount : ℕ}
    (parentCountPos : 0 < parentCount)
    (parent : Fin family.card → Fin parentCount)
    {C : ENNReal}
    (fiberCWA :
      ∀ parentIndex,
        WZ2PaperBodyConvexWolffBound
          (pureWZ2BodyParentFiber family parent parentIndex) C) :
    WZ2PaperBodyConvexWolffBound family C := by
  intro convexSet hconvex
  let parents : Finset (Fin parentCount) := Finset.univ
  let contained := family.containedIndices convexSet
  have containedPartition :
      ∑ parentIndex ∈ parents,
          (contained.filter fun index =>
            parent index = parentIndex).card =
        contained.card := by
    simpa [parents] using
      (Finset.sum_card_fiberwise_eq_card_filter
        contained parents parent).trans (by simp [parents])
  have fiberContainedCount :
      ∀ parentIndex,
        (pureWZ2BodyParentFiber
          family parent parentIndex).containedCount convexSet =
        ((contained.filter fun index =>
          parent index = parentIndex).card : ENNReal) := by
    intro parentIndex
    let fiberIndices :=
      Finset.univ.filter fun index => parent index = parentIndex
    let fiber := pureWZ2BodyParentFiber family parent parentIndex
    let embedding : Fin fiber.card → Fin family.card :=
      fiberIndices.orderEmbOfFin rfl
    have embeddingInjective : Function.Injective embedding :=
      (fiberIndices.orderEmbOfFin rfl).injective
    have imageContained :
        Finset.image embedding (fiber.containedIndices convexSet) =
          contained.filter fun index => parent index = parentIndex := by
      ext index
      constructor
      · intro hindex
        rcases Finset.mem_image.mp hindex with
          ⟨fiberIndex, hfiberIndex, rfl⟩
        have hfiberCarrier :
            (fiber.body fiberIndex).carrier ⊆ convexSet :=
          Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mp
            hfiberIndex
        have hparent : parent (embedding fiberIndex) = parentIndex :=
          (Finset.mem_filter.mp
            (Finset.orderEmbOfFin_mem fiberIndices rfl fiberIndex)).2
        exact Finset.mem_filter.mpr
          ⟨Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mpr
              hfiberCarrier, hparent⟩
      · intro hindex
        have hcontained := (Finset.mem_filter.mp hindex).1
        have hparent := (Finset.mem_filter.mp hindex).2
        have hindexFiber : index ∈ fiberIndices :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ index, hparent⟩
        let fiberIndex : Fin fiber.card :=
          (fiberIndices.orderIsoOfFin rfl).symm ⟨index, hindexFiber⟩
        have embeddingEq : embedding fiberIndex = index :=
          congrArg Subtype.val
            (fiberIndices.orderIsoOfFin rfl |>.apply_symm_apply
              ⟨index, hindexFiber⟩)
        refine Finset.mem_image.mpr ⟨fiberIndex, ?_, embeddingEq⟩
        apply Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mpr
        change (family.body (embedding fiberIndex)).carrier ⊆ convexSet
        rw [embeddingEq]
        exact Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mp
          hcontained
    unfold Kakeya.Streamlined.BodyFamily.containedCount
    rw [← imageContained]
    norm_cast
    exact (Finset.card_image_of_injective
      (fiber.containedIndices convexSet) embeddingInjective).symm
  have fiberCard :
      ∀ parentIndex,
        (pureWZ2BodyParentFiber family parent parentIndex).enncard =
          ((Finset.univ.filter fun index =>
            parent index = parentIndex).card : ENNReal) := fun _ => rfl
  have totalFiberCard :
      ∑ parentIndex ∈ parents,
          (pureWZ2BodyParentFiber
            family parent parentIndex).enncard =
        family.enncard := by
    rw [show
      ∑ parentIndex ∈ parents,
          (pureWZ2BodyParentFiber
            family parent parentIndex).enncard =
        ∑ parentIndex ∈ parents,
          ((Finset.univ.filter fun index =>
            parent index = parentIndex).card : ENNReal) by
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
          (pureWZ2BodyParentFiber
            family parent parentIndex).containedCount convexSet := by
      unfold Kakeya.Streamlined.BodyFamily.containedCount
      rw [show
        (family.containedIndices convexSet).card =
          ∑ parentIndex ∈ parents,
            ((family.containedIndices convexSet).filter
              fun index => parent index = parentIndex).card by
        exact containedPartition.symm]
      norm_cast
      apply Finset.sum_congr rfl
      intro parentIndex _
      change
        ((family.containedIndices convexSet).filter fun index =>
          parent index = parentIndex).card =
        ((pureWZ2BodyParentFiber
          family parent parentIndex).containedIndices convexSet).card
      have hcount := fiberContainedCount parentIndex
      unfold Kakeya.Streamlined.BodyFamily.containedCount at hcount
      exact_mod_cast hcount.symm
    _ ≤
        ∑ parentIndex ∈ parents,
          C * volume convexSet *
            (pureWZ2BodyParentFiber
              family parent parentIndex).enncard := by
      apply Finset.sum_le_sum
      intro parentIndex _
      exact fiberCWA parentIndex convexSet hconvex
    _ = C * volume convexSet * family.enncard := by
      calc
        ∑ parentIndex ∈ parents,
            C * volume convexSet *
              (pureWZ2BodyParentFiber
                family parent parentIndex).enncard =
            (C * volume convexSet) *
              ∑ parentIndex ∈ parents,
                (pureWZ2BodyParentFiber
                  family parent parentIndex).enncard := by
          exact (Finset.mul_sum parents
            (fun parentIndex =>
              (pureWZ2BodyParentFiber
                family parent parentIndex).enncard)
            (C * volume convexSet)).symm
        _ = (C * volume convexSet) * family.enncard := by
          rw [totalFiberCard]
        _ = C * volume convexSet * family.enncard := rfl

end Kakeya.Assouad

end
