import MyLeanRepo.Kakeya.Cinematic.Geometry

/-!
# Shorten a curvilinear rectangle at a larger scale parameter

The normal dyadic binning step replaces exact pointwise scale parameters by
dyadic upper representatives. Increasing the rectangle's second scale
shrinks its horizontal interval. The defining function and midpoint remain
fixed, so the distinguished midpoint point and all tangency certificates are
preserved.
-/

namespace Kakeya.Cinematic

def RectangleShorteningStatement : Prop :=
  ∀ {delta h₁ h₂ : ℝ},
    0 < delta →
    0 < h₁ →
    0 < h₂ →
    h₁ ≤ h₂ →
    ∀ R : CurvilinearRectangle delta h₁,
      ∃ S : CurvilinearRectangle delta h₂,
        S.function = R.function ∧
        S.interval.midpoint = R.interval.midpoint ∧
        S.interval.carrier ⊆ R.interval.carrier ∧
        S.carrier ⊆ R.carrier ∧
        (∀ p ∈ R.carrier,
          (p.1 : ℝ) = R.interval.midpoint →
            p ∈ S.carrier) ∧
        (∀ I : ParameterInterval,
          R.IsOverCentralQuarterOf I →
            S.IsOverCentralQuarterOf I) ∧
        ∀ f : C2Function, ∀ lambda : ℝ,
          R.IsLambdaTangent f lambda →
            S.IsLambdaTangent f lambda

end Kakeya.Cinematic
