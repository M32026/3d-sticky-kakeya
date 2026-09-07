import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12

/-!
# Body CWA transfer to a cardinality-retaining subfamily

The actual Definition 2.12 fibers are `BodyFamily`s rather than paper tube
families.  A selected indexed subfamily inherits normalized Convex-Wolff
counting after paying the explicit ambient-to-selected cardinality ratio.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem WZ2PaperBodyConvexWolffBound.subfamily_of_cardinality
    {family : Kakeya.Streamlined.BodyFamily}
    {C K : ENNReal}
    (hCWA : WZ2PaperBodyConvexWolffBound family C)
    (selected : Kakeya.Streamlined.Subfamily family)
    (hcardinality :
      family.enncard ≤ K * selected.family.enncard) :
    WZ2PaperBodyConvexWolffBound
      selected.family (K * C) := by
  intro convexSet hconvex
  let selectedContained :=
    selected.family.containedIndices convexSet
  let ambientContained :=
    family.containedIndices convexSet
  have himage :
      Finset.image selected.embedding selectedContained ⊆
        ambientContained := by
    intro ambientIndex hambientIndex
    rcases Finset.mem_image.mp hambientIndex with
      ⟨selectedIndex, hselectedIndex, rfl⟩
    rw [Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff]
    rw [← selected.carrier_eq selectedIndex]
    exact
      (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mp
        hselectedIndex
  have hcount :
      selected.family.containedCount convexSet ≤
        family.containedCount convexSet := by
    change (selectedContained.card : ENNReal) ≤
      (ambientContained.card : ENNReal)
    exact_mod_cast
      (calc
        selectedContained.card =
            (Finset.image selected.embedding
              selectedContained).card :=
          (Finset.card_image_of_injective
            selectedContained selected.embedding.injective).symm
        _ ≤ ambientContained.card :=
          Finset.card_le_card himage)
  calc
    selected.family.containedCount convexSet ≤
        family.containedCount convexSet :=
      hcount
    _ ≤ C * MeasureTheory.volume convexSet *
          family.enncard :=
      hCWA convexSet hconvex
    _ ≤ C * MeasureTheory.volume convexSet *
          (K * selected.family.enncard) := by
      gcongr
    _ =
        (K * C) * MeasureTheory.volume convexSet *
          selected.family.enncard := by
      ring

theorem WZ2PaperBodyConvexWolffBound.subfamily_of_weighted_cardinality
    {family : Kakeya.Streamlined.BodyFamily}
    {C weight K : ENNReal}
    (hCWA : WZ2PaperBodyConvexWolffBound family C)
    (selected : Kakeya.Streamlined.Subfamily family)
    (weight_ne_zero : weight ≠ 0)
    (weight_ne_top : weight ≠ ⊤)
    (hcardinality :
      weight * family.enncard ≤
        K * selected.family.enncard) :
    WZ2PaperBodyConvexWolffBound
      selected.family ((weight⁻¹ * K) * C) := by
  apply hCWA.subfamily_of_cardinality selected
  calc
    family.enncard =
        weight⁻¹ * (weight * family.enncard) := by
      rw [← mul_assoc,
        ENNReal.inv_mul_cancel weight_ne_zero weight_ne_top,
        one_mul]
    _ ≤ weight⁻¹ *
        (K * selected.family.enncard) := by
      gcongr
    _ =
        (weight⁻¹ * K) * selected.family.enncard := by
      ring

end Kakeya.Assouad

end
