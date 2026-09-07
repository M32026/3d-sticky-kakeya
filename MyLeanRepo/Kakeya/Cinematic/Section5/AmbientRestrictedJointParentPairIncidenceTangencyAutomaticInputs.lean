import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedJointIncidenceSetupInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedFiberPairIncidenceInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedIncidenceCanonicalCutoffsInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedIncidenceTangencyAutomaticGoodPairsInputs

/-!
# Joint parent pair incidence with automatic tangency

When the canonical tangency threshold is at most `delta`, tangency
nonnegativity makes the second good-pair condition automatic.  This caller
keeps the joint metric cutoff and selected incidence fibers, and uses
`delta` itself as the pair-incidence tangency lower scale.
-/

namespace Kakeya.Cinematic

def AmbientRestrictedJointParentPairIncidenceTangencyAutomaticStatement : Prop :=
  SelectedIncidenceCanonicalCutoffsStatement →
    SelectedIncidenceTangencyAutomaticGoodPairsStatement →
    SelectedFiberPairIncidenceStatement →
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
            selectedIncidenceTangencyCut
                  incidence.heavySetup.heavyLogLoss eta *
                DeltaRep / 2 ≤
              delta →
            10 * delta ≤
              (selectedIncidenceMetricCut
                    incidence.heavySetup.heavyLogLoss
                    (4 * Real.rpow (2 * tRep / DeltaRep) eta)
                    epsilon *
                  tRep / 8) /
                (6 * K) →
            100 * delta ≤
              C_R * tRep * DeltaRep / delta →
            ∀ index :
                Fin
                  (selectedCoarseSubfamily coarseSetup.coarseData
                    incidence.heavySetup.selectedCoarse).card,
              ((incidence.parentSetup.selectedRectangles index).card : ℝ) *
                    (incidence.parentSetup.pairLower index : ℝ) ^ 2 ≤
                3 *
                    ((selectedCoarseIncidenceSupport
                      coarseSetup.coarseData
                        incidence.degreeSetup.selectedEdges
                        incidence.heavySetup.selectedCoarse index).card :
                      ℝ) ^ 2 *
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
                            delta)) +
                    1)

end Kakeya.Cinematic
