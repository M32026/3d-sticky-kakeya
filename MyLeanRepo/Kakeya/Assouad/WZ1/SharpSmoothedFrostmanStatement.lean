import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothedMeasure.Basic

/-!
# Sharp linear Frostman bound after smoothing

The generic smoothing lemma bounds very small balls by a power of the
smoothing radius.  Proposition 41 needs the sharper one-dimensional estimate
that also uses delta separation and the source Frostman lower bound on
cardinality.
-/

namespace Kakeya.Assouad

/--
Smoothing a delta-separated one-dimensional Frostman set at radius
`delta / 10` gives an all-scale linear Frostman probability measure with a
fixed absolute loss.

For radii at least the smoothing radius, count the source centers whose
smoothing balls meet the test ball and apply the discrete Frostman estimate
at radius `r + delta / 10`.  For smaller radii, delta separation leaves at
most one contributing center; its ball fraction is quadratic in
`r / delta`, while the source Frostman condition at radius `delta` gives
`1 / #A <= C * delta`.  The output is stated directly in the `NNReal` form
consumed by `RadialBootstrappingMeasureThinTubesInput`.
-/
def WZ1SharpSmoothedFrostmanStatement : Prop :=
  ∀ {delta C : ℝ} (A : DiscreteSet 2) (hA : A.Nonempty),
    ∀ hdelta : 0 < delta,
    delta ≤ 1 →
    1 ≤ C →
    A.IsDeltaSeparated delta →
    A.IsFrostman delta 1 (ENNReal.ofReal C) →
      ∀ (x : Point2) (r : ℝ), 0 < r →
        smoothMeasure A hA (delta / 10) (by linarith)
            (Metric.ball x r) ≤
          Real.toNNReal (100 * C * r)

end Kakeya.Assouad
