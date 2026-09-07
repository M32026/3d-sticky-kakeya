import MyLeanRepo.Kakeya.Cinematic.Section5.RepresentativeMetricGoodPairInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.ProductScalePairIncidenceInputs

/-!
# Incidence double count with automatic tangency

When the desired tangency lower threshold is at most `delta`, tangency
nonnegativity makes it automatic. The per-rectangle input then needs only the
representative metric-good pair count.
-/

namespace Kakeya.Cinematic

def MetricGoodPairIncidenceStatement : Prop :=
  RepresentativeMetricGoodPairSelectionStatement →
    ProductScaleFixedPairIncidenceStatement →
    TangencyGeometryCompletionStatement →
    FinePairIncidenceBoundStatement →
    PairIncidenceCountingStatement →
    ∀ K D : ℝ,
      1 ≤ K →
      1 ≤ D →
      ∃ C_inc : ℝ, 0 < C_inc ∧
        ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
          {delta diameter epsilon eta tRep DeltaRep C_R
            metricCut tangencyLower Cc : ℝ},
          IsCinematicFamily family K D →
          0 < delta →
          0 < C_R →
          0 < metricCut →
          metricCut < 1 →
          0 < tangencyLower →
          tangencyLower ≤ delta →
          ∀ (data : DyadicFineAssignmentData
              family E K delta diameter epsilon eta tRep DeltaRep C_R),
            (∀ p : E, delta / data.exactT p < metricCut) →
            (∀ p : E,
              24 * Real.rpow (2 * metricCut) epsilon ≤
                Real.rpow
                  (data.exactDelta p / (4 * data.exactT p)) eta) →
            10 * delta ≤
              (metricCut * tRep / 8) / (6 * K) →
            100 ≤ Cc →
            Cc * delta ≤ C_R * tRep * DeltaRep / delta →
            ∀ (R : RectangleFamily
                delta (C_R * tRep * DeltaRep / delta)),
              ∀ source : Fin R.card → E,
                (∀ i, R.rectangle i =
                  data.assignment.rectangle (source i)) →
                R.IsOverCentralQuarterOf data.interval →
                R.IsPairwiseIncomparable family Cc →
                ∀ F_B : FiniteFunctionFamily,
                  F_B.carrier ⊆ family →
                  (∀ i,
                    (data.assignment.fiber (source i)).carrier ⊆
                      F_B.carrier) →
                  ∀ q : ℕ,
                    0 < q →
                    (∀ i, q ≤
                      (data.assignment.fiber (source i)).card) →
                    (R.card : ℝ) * (q : ℝ) ^ 2 ≤
                      3 * (F_B.card : ℝ) ^ 2 *
                        (C_inc *
                            Real.sqrt
                              (delta *
                                  (C_R * tRep * DeltaRep / delta) /
                                ((metricCut * tRep / 8) *
                                  tangencyLower)) +
                          1)

end Kakeya.Cinematic
