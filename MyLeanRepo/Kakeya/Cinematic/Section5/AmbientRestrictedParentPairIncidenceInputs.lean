import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedParentFiberRegularizationInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedFiberPairIncidenceInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedIncidenceFiberGoodPairsInputs

/-!
# Good-pair incidence below each selected fixed-bin parent

Apply the pointwise two-ends good-pair estimate to the selected incidence
fibers `G'(R)`, then double count those ordered pairs against the uniform
fixed-pair incidence bound.  Every cutoff and smallness budget remains
explicit for the final parent tangency-scale audit.
-/

namespace Kakeya.Cinematic

def AmbientRestrictedParentPairIncidenceOnRetainedStatement : Prop :=
  SelectedIncidenceFiberGoodPairsStatement →
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
            (degreeSetup : RetainedIncidenceDegreeSetupData
              data center hE fineSetup coarseSetup refinement)
            (q_fiber : ℕ)
            (fiberBound : ℝ)
            (heavySetup : RetainedHeavySupportSetupData
              data center hE fineSetup coarseSetup refinement
                degreeSetup q_fiber fiberBound)
            (parentSetup : AmbientRestrictedParentFiberRegularizationData
              data center hE fineSetup coarseSetup refinement
                degreeSetup q_fiber fiberBound heavySetup)
            (metricCut tangencyCut retention fiberCoefficient : ℝ),
            IsCinematicFamily family K D →
            0 < delta →
            0 < C_R →
            2 ≤ q_fiber →
            0 < metricCut →
            metricCut < 1 →
            0 < tangencyCut →
            tangencyCut < 1 →
            (∀ p : ambientRestrictedSet data center,
              delta /
                  (ambientRestrictedData data center hE).exactT p <
                metricCut) →
            (∀ p : ambientRestrictedSet data center,
              delta /
                  (ambientRestrictedData data center hE).exactDelta p <
                tangencyCut) →
            0 < retention →
            0 < fiberCoefficient →
            retention * (data.mu : ℝ) <
              4 * ((q_fiber : ℝ) + 1) →
            (∀ rectangle ∈ degreeSetup.retained,
              (((ambientRestrictedData data center hE).metricFiber
                (fineSetup.source rectangle)).card : ℝ) ≤
                  fiberCoefficient * (data.mu : ℝ)) →
            (∀ p : ambientRestrictedSet data center,
              (((ambientRestrictedData data center hE).assignment.fiber p).card :
                  ℝ) ≤
                fiberCoefficient * (data.mu : ℝ)) →
            12 * heavySetup.heavyLogLoss * 12 *
                Real.rpow (2 * metricCut) epsilon *
                fiberCoefficient ≤
              retention →
            12 * heavySetup.heavyLogLoss * 6 *
                Real.rpow tangencyCut eta *
                fiberCoefficient ≤
              retention →
            10 * delta ≤
              (metricCut * tRep / 8) / (6 * K) →
            100 * delta ≤
              C_R * tRep * DeltaRep / delta →
            ∀ index :
                Fin
                  (selectedCoarseSubfamily coarseSetup.coarseData
                    heavySetup.selectedCoarse).card,
              ((parentSetup.selectedRectangles index).card : ℝ) *
                    (parentSetup.pairLower index : ℝ) ^ 2 ≤
                3 *
                    ((selectedCoarseIncidenceSupport
                      coarseSetup.coarseData degreeSetup.selectedEdges
                        heavySetup.selectedCoarse index).card : ℝ) ^ 2 *
                  (C_inc *
                      Real.sqrt
                        (delta *
                            (C_R * tRep * DeltaRep / delta) /
                          ((metricCut * tRep / 8) *
                            (tangencyCut * DeltaRep / 2))) +
                    1)

def AmbientRestrictedParentPairIncidenceStatement : Prop :=
  SelectedIncidenceFiberGoodPairsStatement →
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
            (degreeSetup : RetainedIncidenceDegreeSetupData
              data center hE fineSetup coarseSetup refinement)
            (q_fiber : ℕ)
            (fiberBound : ℝ)
            (heavySetup : RetainedHeavySupportSetupData
              data center hE fineSetup coarseSetup refinement
                degreeSetup q_fiber fiberBound)
            (parentSetup : AmbientRestrictedParentFiberRegularizationData
              data center hE fineSetup coarseSetup refinement
                degreeSetup q_fiber fiberBound heavySetup)
            (metricCut tangencyCut retention fiberCoefficient : ℝ),
            IsCinematicFamily family K D →
            0 < delta →
            0 < C_R →
            2 ≤ q_fiber →
            0 < metricCut →
            metricCut < 1 →
            0 < tangencyCut →
            tangencyCut < 1 →
            (∀ p : ambientRestrictedSet data center,
              delta /
                  (ambientRestrictedData data center hE).exactT p <
                metricCut) →
            (∀ p : ambientRestrictedSet data center,
              delta /
                  (ambientRestrictedData data center hE).exactDelta p <
                tangencyCut) →
            0 < retention →
            0 < fiberCoefficient →
            retention * (data.mu : ℝ) <
              4 * ((q_fiber : ℝ) + 1) →
            (∀ p : ambientRestrictedSet data center,
              (((ambientRestrictedData data center hE).metricFiber p).card :
                  ℝ) ≤
                fiberCoefficient * (data.mu : ℝ)) →
            (∀ p : ambientRestrictedSet data center,
              (((ambientRestrictedData data center hE).assignment.fiber p).card :
                  ℝ) ≤
                fiberCoefficient * (data.mu : ℝ)) →
            12 * heavySetup.heavyLogLoss * 12 *
                Real.rpow (2 * metricCut) epsilon *
                fiberCoefficient ≤
              retention →
            12 * heavySetup.heavyLogLoss * 6 *
                Real.rpow tangencyCut eta *
                fiberCoefficient ≤
              retention →
            10 * delta ≤
              (metricCut * tRep / 8) / (6 * K) →
            100 * delta ≤
              C_R * tRep * DeltaRep / delta →
            ∀ index :
                Fin
                  (selectedCoarseSubfamily coarseSetup.coarseData
                    heavySetup.selectedCoarse).card,
              ((parentSetup.selectedRectangles index).card : ℝ) *
                    (parentSetup.pairLower index : ℝ) ^ 2 ≤
                3 *
                    ((selectedCoarseIncidenceSupport
                      coarseSetup.coarseData degreeSetup.selectedEdges
                        heavySetup.selectedCoarse index).card : ℝ) ^ 2 *
                  (C_inc *
                      Real.sqrt
                        (delta *
                            (C_R * tRep * DeltaRep / delta) /
                          ((metricCut * tRep / 8) *
                            (tangencyCut * DeltaRep / 2))) +
                    1)

end Kakeya.Cinematic
