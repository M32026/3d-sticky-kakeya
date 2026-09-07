import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedIncidenceFiberGoodPairsInputs

/-!
# Tangency-automatic good pairs in one selected incidence fiber

When the desired tangency lower threshold is at most `delta`, nonnegativity
of the tangency parameter makes that condition automatic.  Only the metric
bad-set budget must be removed from the selected incidence subfiber.
-/

namespace Kakeya.Cinematic

def SelectedIncidenceTangencyAutomaticGoodPairsStatement : Prop :=
  GoodPairCountingStatement →
    ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
      {K delta diameter epsilon eta tRep DeltaRep C_R : ℝ},
      0 < delta →
      ∀ (data : DyadicFineAssignmentData
          family E K delta diameter epsilon eta tRep DeltaRep C_R),
        ∀ (p : E) (selected : Finset C2Function),
          (selected : Set C2Function) ⊆
            (data.assignment.fiber p).carrier →
          ∀ metricCut : ℝ,
            0 < metricCut →
            metricCut < 1 →
            delta / data.exactT p < metricCut →
            12 * Real.rpow (2 * metricCut) epsilon *
                ((data.metricFiber p).card : ℝ) ≤
              (selected.card : ℝ) →
            selected.card ^ 2 ≤
              3 * ((selected.product selected).filter fun pair =>
                metricCut * tRep / 8 <
                  c2Distance pair.2 pair.1).card

end Kakeya.Cinematic
