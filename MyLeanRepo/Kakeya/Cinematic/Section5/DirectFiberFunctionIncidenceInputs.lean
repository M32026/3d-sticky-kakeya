import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs

/-!
# Direct fiber--function incidence counting

This is the singleton-safe alternative to good-pair incidence.  Each fine
rectangle contributes its retained functions individually, while generalized
packing bounds the number of incomparable rectangles tangent to one fixed
function.
-/

namespace Kakeya.Cinematic

def DirectFiberFunctionIncidenceStatement : Prop :=
  PairIncidenceCountingStatement →
    ∀ {K delta t : ℝ},
      1 ≤ K →
      0 < delta →
      delta ≤ t →
      ∀ {family : Set C2Function} {I : ParameterInterval},
        I.IsShort K →
        ∀ (R : RectangleFamily delta t),
          R.CentersIn family →
          R.IsOverCentralQuarterOf I →
          R.IsPairwiseIncomparable family 100 →
          ∀ center : C2Function,
            (∀ i,
              c2Distance center (R.rectangle i).function ≤ 3 * t) →
            ∀ (H : FiniteFunctionFamily)
              (fiber : Fin R.card → FiniteFunctionFamily),
              (∀ i, (fiber i).carrier ⊆ H.carrier) →
              (∀ i, ∀ f ∈ (fiber i).carrier,
                (R.rectangle i).IsLambdaTangent f 5) →
              ∀ q : ℕ,
                0 < q →
                (∀ i, q ≤ (fiber i).card) →
                (R.card : ℝ) * (q : ℝ) ≤
                  (H.card : ℝ) *
                    (42 * (100 : ℝ) ^ 2 * I.length /
                        Real.sqrt (delta / t) +
                      1)

end Kakeya.Cinematic
