import MyLeanRepo.Kakeya.Cinematic.Geometry

/-!
# Centered enlargement of a fine rectangle

The enlarged shading in PYZ Section 5 uses a thicker rectangle with the same
defining function and midpoint. The interval buffer comes from working on the
centered sixteenth of the controlled parameter interval.
-/

namespace Kakeya.Cinematic

def CenteredRectangleEnlargementStatement : Prop :=
  ∀ {family : Set C2Function} {I : ParameterInterval}
    {delta t lambda : ℝ},
    0 < delta →
    0 < t →
    1 ≤ lambda →
    ∀ R : CurvilinearRectangle delta t,
      R.function ∈ family →
      R.IsOverCentralQuarterOf I →
      Real.sqrt (lambda * delta / t) ≤ I.length / 8 →
      ∃ U : CurvilinearRectangle (lambda * delta) t,
        U.function = R.function ∧
        U.interval.midpoint = R.interval.midpoint ∧
        R.carrier ⊆ U.carrier ∧
        U.function ∈ family

end Kakeya.Cinematic
