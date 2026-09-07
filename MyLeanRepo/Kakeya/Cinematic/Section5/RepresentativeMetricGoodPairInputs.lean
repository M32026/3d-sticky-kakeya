import MyLeanRepo.Kakeya.Cinematic.Section5.PointwiseLemma45Inputs

/-!
# Metric-good pairs at the common representative scale

When the tangency lower threshold is at most `delta`, tangency nonnegativity
makes that condition automatic. Only the first two-ends metric bad set must
be removed.
-/

namespace Kakeya.Cinematic

def RepresentativeMetricGoodPairSelectionStatement : Prop :=
  GoodPairCountingStatement →
    ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
      {K delta diameter epsilon eta tRep DeltaRep C_R : ℝ},
      0 < delta →
      ∀ (data : DyadicFineAssignmentData
          family E K delta diameter epsilon eta tRep DeltaRep C_R),
        ∀ (p : E),
          ∀ metricCut : ℝ,
            0 < metricCut →
            metricCut < 1 →
            delta / data.exactT p < metricCut →
            24 * Real.rpow (2 * metricCut) epsilon ≤
              Real.rpow
                (data.exactDelta p / (4 * data.exactT p)) eta →
            let G := data.assignment.fiber p
            let goodPairs :=
              (G.toFinset.product G.toFinset).filter fun pair =>
                metricCut * tRep / 8 <
                  c2Distance pair.2 pair.1
            G.card ^ 2 ≤ 3 * goodPairs.card

end Kakeya.Cinematic
