import MyLeanRepo.Kakeya.Assouad.Statements

/-!
# Tube reversal invariance

Reverse the parametrization of a unit tube axis without changing its carrier.
This is used when the leftmost segment of a consecutive cover is stored with
the opposite orientation to preserve the bounded-base budget.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Reverse the parametrization of a tube's unit axis segment. -/
def reverseTube {delta : ℝ}
    (T : Kakeya.DeltaTube delta) : Kakeya.DeltaTube delta where
  base := T.base + T.direction
  direction := -T.direction
  direction_unit := by simpa using T.direction_unit

lemma unitSegment_reverse (base direction : Point3) :
    Kakeya.unitSegment (base + direction) (-direction) =
      Kakeya.unitSegment base direction := by
  ext point
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    module
  · rintro ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    module

@[simp] lemma reverseTube_carrier {delta : ℝ}
    (T : Kakeya.DeltaTube delta) :
    (reverseTube T).carrier = T.carrier := by
  simp [reverseTube, Kakeya.DeltaTube.carrier, unitSegment_reverse]

@[simp] lemma reverseTube_volume {delta : ℝ}
    (T : Kakeya.DeltaTube delta) :
    (reverseTube T).volume = T.volume := by
  simp [Kakeya.DeltaTube.volume]

@[simp] lemma reverseTube_reverse {delta : ℝ}
    (T : Kakeya.DeltaTube delta) :
    reverseTube (reverseTube T) = T := by
  cases T
  simp [reverseTube, add_assoc]

@[simp] lemma reverseTube_direction_abs {delta : ℝ}
    (T : Kakeya.DeltaTube delta) (i : Fin 3) :
    |(reverseTube T).direction i| = |T.direction i| := by
  simp [reverseTube]

lemma reverseTube_essentiallyDistinct_left {delta : ℝ}
    (T U : Kakeya.DeltaTube delta)
    (h : T.EssentiallyDistinct U) :
    (reverseTube T).EssentiallyDistinct U := by
  simpa [Kakeya.DeltaTube.EssentiallyDistinct] using h

lemma reverseTube_essentiallyDistinct_right {delta : ℝ}
    (T U : Kakeya.DeltaTube delta)
    (h : T.EssentiallyDistinct U) :
    T.EssentiallyDistinct (reverseTube U) := by
  simpa [Kakeya.DeltaTube.EssentiallyDistinct] using h

end Kakeya.Assouad
