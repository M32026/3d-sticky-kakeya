import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicFineAssignmentData
import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs

/-!
# Pointwise Lemma 45 specialization

This proposition specializes the two pointwise two-ends estimates stored in
`DyadicFineAssignmentData` to metric and tangency cutoffs. The compatibility
condition compares the retained tangency mass with the metric bad-set loss.
-/

namespace Kakeya.Cinematic

def PointwiseLemma45BadSetBoundsStatement : Prop :=
  Lemma45BadSetBoundsStatement →
    ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
      {K delta diameter epsilon eta tRep DeltaRep C_R : ℝ},
      0 < delta →
      ∀ (data : DyadicFineAssignmentData
          family E K delta diameter epsilon eta tRep DeltaRep C_R),
        ∀ (p : E),
          ∀ metricCut tangencyCut : ℝ,
            0 < metricCut →
            metricCut < 1 →
            delta / data.exactT p < metricCut →
            0 < tangencyCut →
            tangencyCut < 1 →
            delta / data.exactDelta p < tangencyCut →
            24 * Real.rpow (2 * metricCut) epsilon ≤
              Real.rpow
                (data.exactDelta p / (4 * data.exactT p)) eta →
            6 * Real.rpow tangencyCut eta ≤ 1 →
            ∀ g ∈ (data.assignment.fiber p).carrier,
              3 * (((data.assignment.fiber p).carrier ∩
                    c2Ball g (metricCut * data.exactT p)).ncard : ℝ) ≤
                  (data.assignment.fiber p).card ∧
                3 * (((data.assignment.fiber p).carrier ∩
                    {f | tangencyParameterOn data.interval f g + delta <
                      tangencyCut * data.exactDelta p}).ncard : ℝ) ≤
                  (data.assignment.fiber p).card

end Kakeya.Cinematic
