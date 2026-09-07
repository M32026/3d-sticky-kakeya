import MyLeanRepo.Kakeya.Cinematic.Section5.PointwiseGoodPairInputs

/-!
# Good pairs in one selected incidence fiber

The degree-regularized incidence graph keeps only a selected subfiber
`G'(R)` of the original pointwise retained fiber.  This statement applies the
finite good-pair count directly to that selected finset.  The two bad-set
budgets remain explicit, so the caller must prove that both original
two-ends bounds are small relative to the selected subfiber cardinality.
-/

namespace Kakeya.Cinematic

def SelectedIncidenceFiberGoodPairsStatement : Prop :=
  GoodPairCountingStatement →
    ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
      {K delta diameter epsilon eta tRep DeltaRep C_R : ℝ},
      0 < delta →
      ∀ (data : DyadicFineAssignmentData
          family E K delta diameter epsilon eta tRep DeltaRep C_R),
        ∀ (p : E) (selected : Finset C2Function),
          (selected : Set C2Function) ⊆
            (data.assignment.fiber p).carrier →
          ∀ metricCut tangencyCut : ℝ,
            0 < metricCut →
            metricCut < 1 →
            delta / data.exactT p < metricCut →
            0 < tangencyCut →
            tangencyCut < 1 →
            delta / data.exactDelta p < tangencyCut →
            12 * Real.rpow (2 * metricCut) epsilon *
                ((data.metricFiber p).card : ℝ) ≤
              (selected.card : ℝ) →
            6 * Real.rpow tangencyCut eta *
                ((data.assignment.fiber p).card : ℝ) ≤
              (selected.card : ℝ) →
            selected.card ^ 2 ≤
              3 * ((selected.product selected).filter fun pair =>
                metricCut * tRep / 8 <
                    c2Distance pair.2 pair.1 ∧
                  tangencyCut * DeltaRep / 2 ≤
                    tangencyParameterOn data.interval
                      pair.2 pair.1 + delta).card

end Kakeya.Cinematic
