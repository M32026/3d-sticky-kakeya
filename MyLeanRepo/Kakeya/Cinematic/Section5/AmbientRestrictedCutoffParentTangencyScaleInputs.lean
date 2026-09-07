import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedAutomaticParentTangencyScaleInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedJointParentPairIncidenceInputs

/-!
# Parent tangency scale at the canonical cutoff

This interface combines the general good-pair route with the
tangency-automatic route.  Both branches are promoted to the same incidence
scale whose tangency denominator is the canonical cutoff
`tangencyCut * DeltaRep / 2`.
-/

namespace Kakeya.Cinematic

def AmbientRestrictedCutoffParentTangencyScaleStatement : Prop :=
  SelectedIncidenceCanonicalCutoffsStatement →
    SelectedIncidenceFiberGoodPairsStatement →
    SelectedIncidenceTangencyAutomaticGoodPairsStatement →
    SelectedFiberPairIncidenceStatement →
    AmbientRestrictedJointParentPairIncidenceStatement →
    AmbientRestrictedJointParentPairIncidenceTangencyAutomaticStatement →
    AmbientRestrictedAutomaticParentTangencyScaleStatement →
    AmbientRestrictedParentTangencyScaleStatement →
    ∀ K D : ℝ,
      1 ≤ K →
      1 ≤ D →
      ∃ C_inc : ℝ,
        0 < C_inc ∧
        ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
          {delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ},
          ∀ (data : DyadicFineAssignmentData
              family E K delta diameter epsilon eta
                tRep DeltaRep C_R₀)
            (center : C2Function)
            (hE : MeasurableSet E)
            {C_R C_count C_shading C_volume : ℝ}
            (fineSetup : AmbientRestrictedFSVSetupData
              data center hE C_R C_count C_shading C_volume)
            (coarseSetup : AmbientRestrictedCoarseSetupData
              data center hE fineSetup)
            {massExponent : ℝ}
            (refinement : AmbientRestrictedLargeBinRefinementData
              data center hE fineSetup coarseSetup massExponent)
            (incidence : AmbientRestrictedJointIncidenceSetupData
              data center hE fineSetup coarseSetup refinement),
            IsCinematicFamily family K D →
            0 < delta →
            0 < C_R →
            2 ≤ incidence.q_fiber →
            (∀ p : ambientRestrictedSet data center,
              delta /
                  (ambientRestrictedData data center hE).exactT p <
                selectedIncidenceMetricCut
                  incidence.heavySetup.heavyLogLoss
                  (4 * Real.rpow (2 * tRep / DeltaRep) eta)
                  epsilon) →
            10 * delta ≤
              (selectedIncidenceMetricCut
                    incidence.heavySetup.heavyLogLoss
                    (4 * Real.rpow (2 * tRep / DeltaRep) eta)
                    epsilon *
                  tRep / 8) /
                (6 * K) →
            100 * delta ≤
              C_R * tRep * DeltaRep / delta →
            (∀ p : E,
              ((data.assignment.fiber p).card : ℝ) <
                2 * (data.mu : ℝ)) →
            ((incidence.heavySetup.M_parent : ℕ) : ℝ) ≤
              ambientRestrictedParentTangencyScale
                  (C_inc *
                      Real.sqrt
                        (delta *
                            (C_R * tRep * DeltaRep / delta) /
                          ((selectedIncidenceMetricCut
                                incidence.heavySetup.heavyLogLoss
                                (4 *
                                  Real.rpow
                                    (2 * tRep / DeltaRep) eta)
                                epsilon *
                              tRep / 8) *
                            (selectedIncidenceTangencyCut
                                  incidence.heavySetup.heavyLogLoss eta *
                              DeltaRep / 2))) +
                    1)
                  4
                  incidence.heavySetup.degreeLoss
                  incidence.heavySetup.heavyLogLoss
                  incidence.retention *
                Real.rpow (data.mu : ℝ) (-2) *
                Real.rpow
                  (2 ^ incidence.heavySetup.supportLevel : ℕ) 2

end Kakeya.Cinematic
