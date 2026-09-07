import MyLeanRepo.Kakeya.Cinematic.Geometry

/-!
# Uniform fine-rectangle count in the metric-automatic regime

When the representative metric scale satisfies `t ≤ 16 * delta`, the fine
rectangle interval length has a fixed lower bound depending only on the
already frozen enlargement constant `C_R`.  Splitting the normalized
parameter interval into uniformly many midpoint clusters and applying the
scale-free generalized packing theorem gives a bound independent of
`delta`, `t`, `Delta`, and the rectangle family.
-/

namespace Kakeya.Cinematic

def NonThinFineRectangleCountStatement : Prop :=
  ∀ K C_R : ℝ,
    1 ≤ K →
    9216 * K ^ 2 ≤ C_R →
    ∃ C_non_thin : ℝ,
      0 < C_non_thin ∧
      ∀ {delta t Delta : ℝ},
        0 < delta →
        delta ≤ Delta →
        Delta ≤ t →
        t ≤ 16 * delta →
        ∀ {family : Set C2Function}
          {I : ParameterInterval},
          I.IsControlled K →
          ∀ (R : RectangleFamily
              delta (C_R * t * Delta / delta)),
            R.CentersIn family →
            R.IsOverCentralQuarterOf I →
            R.IsPairwiseIncomparable family 100 →
            ∀ center : C2Function,
              (∀ i,
                c2Distance center (R.rectangle i).function ≤
                  6 * t) →
              (R.card : ℝ) ≤ C_non_thin

end Kakeya.Cinematic
