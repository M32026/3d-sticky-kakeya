import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedIncidenceCanonicalCutoffsInputs

/-!
# Scale exit when the canonical metric cutoff is too small

If the paper's metric cutoff does not meet the fixed-pair geometric lower
scale, then the joint retained-fiber inequality and a Katz--Tao upper bound
on `q_fiber` directly control the original multiplicity.  The logarithmic
loss and metric-to-retained ratio remain explicit.
-/

namespace Kakeya.Cinematic

def JointMetricCutoffScaleExitStatement : Prop :=
  ∀ K B targetExponent metricExponent : ℝ,
    1 ≤ K →
    0 < B →
    0 < targetExponent →
    0 < metricExponent →
    metricExponent ≤ 1 / 4 →
    8 * metricExponent ≤ targetExponent →
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ {delta t Delta heavyLogLoss fiberRatio
          tangencyExponent : ℝ}
        {mu q : ℕ},
        0 < delta →
        delta ≤ delta₀ →
        delta ≤ Delta →
        Delta ≤ t →
        t ≤ 8 * K →
        0 < mu →
        tangencyExponent = metricExponent ^ 2 →
        1 ≤ heavyLogLoss →
        heavyLogLoss ≤
          Real.rpow delta (-(metricExponent ^ 2)) →
        fiberRatio =
          4 * Real.rpow (2 * t / Delta) tangencyExponent →
        (q : ℝ) ≤ B * (t / delta) →
        Real.rpow (t / (8 * K)) metricExponent *
              Real.rpow (Delta / (2 * t)) tangencyExponent *
              (mu : ℝ) <
            4 * ((q : ℝ) + 1) →
        selectedIncidenceMetricCut
              heavyLogLoss fiberRatio metricExponent *
            t <
          480 * K * delta →
        1 ≤
          Real.rpow delta (-targetExponent) *
            Real.rpow (mu : ℝ) (-3 / 2 : ℝ)

end Kakeya.Cinematic
