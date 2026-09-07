import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Paper cluster radius and Proposition 26 parameter

Choose the variable cluster radius from the fixed-bin metric and tangency
scales.  The explicit `fiberRatio` is an upper bound for the metric-fiber
scale divided by the regularized retained-fiber scale.  In the paper,
`fiberRatio` is a constant and logarithmic factor times
`(t / Delta)^(epsilon^2)`, recovering the displayed radius
`t * c^(1/epsilon) * |log delta|^(-1/epsilon) *
  (Delta / t)^epsilon`.
-/

namespace Kakeya.Cinematic

noncomputable def ambientRestrictedPaperClusterRadius
    (t epsilon logLoss fiberRatio : ℝ) : ℝ :=
  t / 176 *
    Real.rpow (24 * logLoss * fiberRatio) (-1 / epsilon)

noncomputable def ambientRestrictedPaperClusterParameter
    (C_R t epsilon logLoss fiberRatio : ℝ) : ℝ :=
  C_R * t /
    (8 *
      ambientRestrictedPaperClusterRadius
        t epsilon logLoss fiberRatio)

noncomputable def ambientRestrictedPaperFiberCoefficient
    (t epsilon logLoss fiberRatio : ℝ) : ℝ :=
  4 *
    Real.rpow
      (176 *
        ambientRestrictedPaperClusterRadius
          t epsilon logLoss fiberRatio / t)
      epsilon *
    fiberRatio

def AmbientRestrictedPaperClusterScaleStatement : Prop :=
  ∀ (C_R delta t Delta epsilon logLoss fiberRatio : ℝ),
    1 ≤ C_R →
    0 < delta →
    0 < t →
    0 < Delta →
    delta ≤ Delta →
    Delta ≤ t →
    0 < epsilon →
    1 ≤ logLoss →
    1 ≤ fiberRatio →
    let radius :=
      ambientRestrictedPaperClusterRadius
        t epsilon logLoss fiberRatio
    let A :=
      ambientRestrictedPaperClusterParameter
        C_R t epsilon logLoss fiberRatio
    let coefficient :=
      ambientRestrictedPaperFiberCoefficient
        t epsilon logLoss fiberRatio
    0 < radius ∧
      11 * radius < t / 8 ∧
      1 ≤ A ∧
      C_R * t / A = 8 * radius ∧
      Delta ≤ A * (C_R * t) ∧
      4 * logLoss * coefficient ≤ 1

end Kakeya.Cinematic
