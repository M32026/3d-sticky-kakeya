import MyLeanRepo.Kakeya.Streamlined.Estimates

/-!
# Sticky Kakeya input boundary

`StickyInput` is only a proposition.  It is neither an axiom nor a theorem
with a hidden proof.  Every downstream target that needs sticky Kakeya must
receive a proof of this proposition as an ordinary hypothesis.
-/

namespace Kakeya.Streamlined

/-- Explicit hypothesis consumed by the streamlined reduction. -/
abbrev StickyInput : Prop :=
  StickyKakeyaHypothesis

end Kakeya.Streamlined
