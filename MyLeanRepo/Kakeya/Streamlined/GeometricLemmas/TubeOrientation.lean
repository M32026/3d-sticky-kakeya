import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeContainment
import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.SingleScaleCover

/-!
# Reversing tube orientation

A geometric tube is unoriented, while `DeltaTube` stores an oriented base and
direction.  Replacing `(base, direction)` by
`(base + direction, -direction)` preserves the underlying unit segment and
all carrier-based notions.
-/

noncomputable section

namespace Kakeya.Streamlined.GeometricLemmas

/-- Reverse the parametrization of a tube's unit segment. -/
def reverseTube {δ : ℝ} (T : Kakeya.DeltaTube δ) :
    Kakeya.DeltaTube δ where
  base := T.base + T.direction
  direction := -T.direction
  direction_unit := by simpa using T.direction_unit

lemma unitSegment_reverse {base direction : Point3} :
    Kakeya.unitSegment (base + direction) (-direction) =
      Kakeya.unitSegment base direction := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    module
  · rintro ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    module

@[simp] lemma reverseTube_carrier {δ : ℝ} (T : Kakeya.DeltaTube δ) :
    (reverseTube T).carrier = T.carrier := by
  simp only [reverseTube, Kakeya.DeltaTube.carrier]
  rw [unitSegment_reverse]

@[simp] lemma reverseTube_midpoint {δ : ℝ} (T : Kakeya.DeltaTube δ) :
    tubeMidpoint (reverseTube T) = tubeMidpoint T := by
  simp [reverseTube, tubeMidpoint]
  module

@[simp] lemma reverseTube_reverseTube {δ : ℝ} (T : Kakeya.DeltaTube δ) :
    reverseTube (reverseTube T) = T := by
  cases T with
  | mk base direction direction_unit =>
      simp [reverseTube]

@[simp] lemma reverseTube_volume {δ : ℝ} (T : Kakeya.DeltaTube δ) :
    (reverseTube T).volume = T.volume := by
  simp [Kakeya.DeltaTube.volume]

lemma reverseTube_isInUnitBall_iff {δ : ℝ} (T : Kakeya.DeltaTube δ) :
    (reverseTube T).IsInUnitBall ↔ T.IsInUnitBall := by
  simp [Kakeya.DeltaTube.IsInUnitBall]

lemma reverseTube_essentiallyDistinct_iff
    {δ : ℝ} (T U : Kakeya.DeltaTube δ) :
    (reverseTube T).EssentiallyDistinct U ↔
      T.EssentiallyDistinct U := by
  simp [Kakeya.DeltaTube.EssentiallyDistinct]

lemma essentiallyDistinct_reverseTube_iff
    {δ : ℝ} (T U : Kakeya.DeltaTube δ) :
    T.EssentiallyDistinct (reverseTube U) ↔
      T.EssentiallyDistinct U := by
  simp [Kakeya.DeltaTube.EssentiallyDistinct]

@[simp] lemma reverseTube_dilatedCarrier
    {δ A : ℝ} (T : Kakeya.DeltaTube δ) :
    dilatedTubeCarrier A (reverseTube T) =
      dilatedTubeCarrier A T := by
  change
    AffineMap.homothety (tubeMidpoint (reverseTube T)) A ''
        (reverseTube T).carrier =
      AffineMap.homothety (tubeMidpoint T) A '' T.carrier
  rw [reverseTube_midpoint, reverseTube_carrier]

end Kakeya.Streamlined.GeometricLemmas
