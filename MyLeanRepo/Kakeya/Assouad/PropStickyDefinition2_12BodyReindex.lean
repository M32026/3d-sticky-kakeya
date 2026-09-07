import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12

/-!
# Reindexing actual Assouad affine-image families

The public Definition 2.12 witness is a `BodyFamily` of actual affine images.
Section 6 later chooses a one-to-one WZ tube parametrization of the same source
indices.  This module records the safe part of that comparison: changing only
the finite index type does not change contained counts or Convex-Wolff bounds.

No target `DeltaTube` carrier is compared with an affine image here.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Reindex a body family along an equivalence of finite index types. -/
def wz2PaperReindexedBodyFamily
    (family : Kakeya.Streamlined.BodyFamily)
    {targetCard : ℕ}
    (indexEquiv : Fin targetCard ≃ Fin family.card) :
    Kakeya.Streamlined.BodyFamily where
  card := targetCard
  body target := family.body (indexEquiv target)

namespace wz2PaperReindexedBodyFamily

theorem enncard_eq
    (family : Kakeya.Streamlined.BodyFamily)
    {targetCard : ℕ}
    (indexEquiv : Fin targetCard ≃ Fin family.card) :
    (wz2PaperReindexedBodyFamily family indexEquiv).enncard =
      family.enncard := by
  have hcard : targetCard = family.card := by
    simpa using Fintype.card_congr indexEquiv
  simp [wz2PaperReindexedBodyFamily,
    Kakeya.Streamlined.BodyFamily.enncard, hcard]

theorem containedIndices_image
    (family : Kakeya.Streamlined.BodyFamily)
    {targetCard : ℕ}
    (indexEquiv : Fin targetCard ≃ Fin family.card)
    (region : Set Point3) :
    Finset.image indexEquiv
        ((wz2PaperReindexedBodyFamily family indexEquiv).containedIndices
          region) =
      family.containedIndices region := by
  ext source
  constructor
  · intro hsource
    rcases Finset.mem_image.mp hsource with
      ⟨target, htarget, rfl⟩
    have hcarrier :
        (family.body (indexEquiv target)).carrier ⊆ region := by
      simpa [wz2PaperReindexedBodyFamily] using
        (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mp
          htarget
    exact
      (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mpr
        hcarrier
  · intro hsource
    refine Finset.mem_image.mpr
      ⟨indexEquiv.symm source, ?_, indexEquiv.apply_symm_apply source⟩
    have hcarrier :
        (family.body source).carrier ⊆ region :=
      (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mp
        hsource
    exact
      (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mpr
        (by
          simpa [wz2PaperReindexedBodyFamily] using hcarrier)

theorem containedCount_eq
    (family : Kakeya.Streamlined.BodyFamily)
    {targetCard : ℕ}
    (indexEquiv : Fin targetCard ≃ Fin family.card)
    (region : Set Point3) :
    (wz2PaperReindexedBodyFamily family indexEquiv).containedCount region =
      family.containedCount region := by
  have himage :=
    containedIndices_image family indexEquiv region
  have hcard :
      (Finset.image indexEquiv
        ((wz2PaperReindexedBodyFamily family indexEquiv).containedIndices
          region)).card =
        ((wz2PaperReindexedBodyFamily family indexEquiv).containedIndices
          region).card :=
    Finset.card_image_of_injective _ indexEquiv.injective
  unfold Kakeya.Streamlined.BodyFamily.containedCount
  rw [← himage, hcard]

theorem convexWolffBound_iff
    (family : Kakeya.Streamlined.BodyFamily)
    {targetCard : ℕ}
    (indexEquiv : Fin targetCard ≃ Fin family.card)
    (C : ENNReal) :
    WZ2PaperBodyConvexWolffBound
        (wz2PaperReindexedBodyFamily family indexEquiv) C ↔
      WZ2PaperBodyConvexWolffBound family C := by
  constructor
  · intro hbound convexSet hconvex
    rw [
      ← containedCount_eq family indexEquiv convexSet,
      ← enncard_eq family indexEquiv
    ]
    exact hbound convexSet hconvex
  · intro hbound convexSet hconvex
    rw [
      containedCount_eq family indexEquiv convexSet,
      enncard_eq family indexEquiv
    ]
    exact hbound convexSet hconvex

end wz2PaperReindexedBodyFamily

/--
Pointwise enlargement preserves the normalized Convex-Wolff bound.

If every source body is contained in the target body with the same index,
then a target body contained in a convex test set gives a source body
contained in the same test set.
-/
theorem WZ2PaperBodyConvexWolffBound.of_pointwise_subset
    {source target : Kakeya.Streamlined.BodyFamily}
    {C : ENNReal}
    (hcard : target.card = source.card)
    (hsubset :
      ∀ targetIndex : Fin target.card,
        (source.body
            ⟨targetIndex.1, by simpa [hcard] using targetIndex.2⟩).carrier ⊆
          (target.body targetIndex).carrier)
    (hsource : WZ2PaperBodyConvexWolffBound source C) :
    WZ2PaperBodyConvexWolffBound target C := by
  intro convexSet hconvex
  let toSource : Fin target.card → Fin source.card :=
    fun targetIndex =>
      ⟨targetIndex.1, by simpa [hcard] using targetIndex.2⟩
  have hinjective : Function.Injective toSource := by
    intro first second heq
    apply Fin.ext
    exact
      congrArg (fun index : Fin source.card => index.1) heq
  let targetContained := target.containedIndices convexSet
  let sourceContained := source.containedIndices convexSet
  have himage :
      Finset.image toSource targetContained ⊆ sourceContained := by
    intro sourceIndex hsourceIndex
    rcases Finset.mem_image.mp hsourceIndex with
      ⟨targetIndex, htargetIndex, rfl⟩
    exact
      (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mpr
        ((hsubset targetIndex).trans
          ((Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mp
            htargetIndex))
  have hcount :
      target.containedCount convexSet ≤
        source.containedCount convexSet := by
    change (targetContained.card : ENNReal) ≤
      (sourceContained.card : ENNReal)
    have hcardNat :
        targetContained.card ≤ sourceContained.card := by
      calc
        targetContained.card =
            (Finset.image toSource targetContained).card :=
          (Finset.card_image_of_injective
            targetContained hinjective).symm
        _ ≤ sourceContained.card :=
          Finset.card_le_card himage
    exact_mod_cast hcardNat
  calc
    target.containedCount convexSet ≤
        source.containedCount convexSet := hcount
    _ ≤ C * volume convexSet * source.enncard :=
      hsource convexSet hconvex
    _ = C * volume convexSet * target.enncard := by
      simp [Kakeya.Streamlined.BodyFamily.enncard, hcard]

/--
Generic normalized Convex-Wolff transfer through an indexed convex-envelope
comparison.  The source and target families may use different finite index
types; all geometric and Jacobian loss is exposed in `envelopeConstant`.
-/
theorem wz2PaperBodyConvexWolffBound_of_indexed_envelope
    {source target : Kakeya.Streamlined.BodyFamily}
    {C envelopeConstant : ENNReal}
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (envelope :
      ∀ targetConvexSet : Set Point3,
        Convex ℝ targetConvexSet →
          ∃ sourceConvexSet : Set Point3,
            Convex ℝ sourceConvexSet ∧
            volume sourceConvexSet ≤
              envelopeConstant * volume targetConvexSet ∧
            ∀ targetIndex,
              (target.body targetIndex).carrier ⊆ targetConvexSet →
                (source.body (indexEquiv targetIndex)).carrier ⊆
                  sourceConvexSet)
    (hsource : WZ2PaperBodyConvexWolffBound source C) :
    WZ2PaperBodyConvexWolffBound
      target (envelopeConstant * C) := by
  intro targetConvexSet htargetConvex
  rcases envelope targetConvexSet htargetConvex with
    ⟨sourceConvexSet, hsourceConvex, hvolume, hcontainment⟩
  let targetContained := target.containedIndices targetConvexSet
  let sourceContained := source.containedIndices sourceConvexSet
  have himage :
      Finset.image indexEquiv targetContained ⊆ sourceContained := by
    intro sourceIndex hsourceIndex
    rcases Finset.mem_image.mp hsourceIndex with
      ⟨targetIndex, htargetIndex, rfl⟩
    exact
      (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mpr
        (hcontainment targetIndex
          ((Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mp
            htargetIndex))
  have hcount :
      target.containedCount targetConvexSet ≤
        source.containedCount sourceConvexSet := by
    change (targetContained.card : ENNReal) ≤
      (sourceContained.card : ENNReal)
    have hcardNat :
        targetContained.card ≤ sourceContained.card := by
      calc
        targetContained.card =
            (Finset.image indexEquiv targetContained).card :=
          (Finset.card_image_of_injective
            targetContained indexEquiv.injective).symm
        _ ≤ sourceContained.card :=
          Finset.card_le_card himage
    exact_mod_cast hcardNat
  have henncard : source.enncard = target.enncard := by
    have hcard : target.card = source.card := by
      simpa using Fintype.card_congr indexEquiv
    simp [Kakeya.Streamlined.BodyFamily.enncard, hcard]
  calc
    target.containedCount targetConvexSet ≤
        source.containedCount sourceConvexSet := hcount
    _ ≤ C * volume sourceConvexSet * source.enncard :=
      hsource sourceConvexSet hsourceConvex
    _ ≤ C *
          (envelopeConstant * volume targetConvexSet) *
          source.enncard := by
      gcongr
    _ =
        (envelopeConstant * C) *
          volume targetConvexSet * target.enncard := by
      rw [henncard]
      ring

end Kakeya.Assouad

end
