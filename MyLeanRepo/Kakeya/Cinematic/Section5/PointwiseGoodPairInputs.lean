import MyLeanRepo.Kakeya.Cinematic.Section5.PointwiseLemma45Inputs

/-!
# Pointwise good-pair extraction

After both Lemma 45 bad sets occupy at most one third of one retained
pointwise fiber, the finite good-pair lemma leaves at least one third of all
ordered pairs.
-/

namespace Kakeya.Cinematic

def PointwiseGoodPairSelectionStatement : Prop :=
  PointwiseLemma45BadSetBoundsStatement →
    GoodPairCountingStatement →
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
              let G := data.assignment.fiber p
              let goodPairs :=
                (G.toFinset.product G.toFinset).filter fun pair =>
                  metricCut * data.exactT p <
                      c2Distance pair.2 pair.1 ∧
                    tangencyCut * data.exactDelta p ≤
                      tangencyParameterOn data.interval pair.2 pair.1 + delta
              G.card ^ 2 ≤ 3 * goodPairs.card

end Kakeya.Cinematic
