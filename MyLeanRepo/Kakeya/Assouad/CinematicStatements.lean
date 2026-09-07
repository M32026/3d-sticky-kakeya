import MyLeanRepo.Kakeya.Assouad.CinematicBridge

/-!
# Cinematic bridge statement for WZ2

This isolates WZ1 Lemma 7.3 / Lemma 36 from PYZ: a nonsingular normalized
slope produces a uniformly cinematic three-parameter family.
-/

namespace Kakeya.Assouad

/--
The parameter family `a + b f(t) + d t f(t)` is cinematic with constants
independent of the particular normalized slope.
-/
def CinematicFamilyFromSlopeStatement : Prop :=
  ∃ K D : ℝ, 1 ≤ K ∧ 1 ≤ D ∧
    ∀ f : SlopeFunction,
      f.IsNonsingular →
      f 0 = 0 →
      ∃ family : Set Kakeya.Cinematic.C2Function,
        IsSlopeCurveFamily family f ∧
          Kakeya.Cinematic.IsCinematicFamily family K D

end Kakeya.Assouad
