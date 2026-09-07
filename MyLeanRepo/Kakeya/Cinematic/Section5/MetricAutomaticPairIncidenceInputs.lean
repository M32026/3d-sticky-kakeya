import MyLeanRepo.Kakeya.Cinematic.Section5.ProductScalePairIncidenceInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicFineAssignmentData

/-!
# Pair incidence in the metric-automatic regime

This is the full finite double-counting interface after representative
metric-automatic good pairs have been selected honestly off the diagonal.
-/

namespace Kakeya.Cinematic

def MetricAutomaticPairIncidenceStatement : Prop :=
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
            metricLower tangencyCut Cc : ℝ},
          IsCinematicFamily family K D →
          0 < delta →
          0 < C_R →
          0 < metricLower →
          metricLower < (1 : ℝ) →
          0 < tangencyCut →
          tangencyCut < 1 →
          ∀ (data : DyadicFineAssignmentData
              family E K delta diameter epsilon eta tRep DeltaRep C_R),
            metricLower < data.separationScale →
            (∀ p : E, delta / data.exactDelta p < tangencyCut) →
            6 * Real.rpow tangencyCut eta ≤ 1 →
            10 * delta ≤ metricLower / (6 * K) →
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
                  (∀ i, 2 ≤
                    (data.assignment.fiber (source i)).card) →
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
                                (metricLower *
                                  (tangencyCut * DeltaRep / 2))) +
                          1)

end Kakeya.Cinematic
