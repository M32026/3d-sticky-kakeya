import MyLeanRepo.Kakeya.Cinematic.Section5.RetainedIncidenceDegreeSetupInputs

/-!
# Fixed-ball upper bound for selected incidence fibers

At the one radius consumed by the cluster argument, transfer the pointwise
metric two-ends estimate from the ambient-restricted source point to every
selected incidence subfiber.  The explicit worst-case representative-scale
factor remains visible for the later comparison with `q_fiber`.
-/

noncomputable section

namespace Kakeya.Cinematic

local instance ambientRestrictedSelectedFiberBallBoundDecidableEq :
    DecidableEq C2Function := Classical.decEq _

def AmbientRestrictedSelectedFiberBallBoundOnRetainedStatement : Prop :=
  ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ},
    ∀ (data : DyadicFineAssignmentData
        family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
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
      (radius metricBound : ℝ),
      0 < delta →
      0 < radius →
      delta < 11 * radius →
      11 * radius < tRep / 8 →
      0 ≤ metricBound →
      (∀ rectangle ∈ degreeSetup.retained,
        (((ambientRestrictedData data center hE).metricFiber
          (fineSetup.source rectangle)).card : ℝ) ≤
            metricBound) →
      ∀ coarse rectangle,
        rectangle ∈
          incidenceRectangleSupport degreeSetup.selectedEdges
            coarseSetup.coarseData.parent coarse →
        ∀ testCenter,
          (((incidenceRectangleFiber degreeSetup.selectedEdges rectangle :
                Set C2Function) ∩
              c2Ball testCenter (11 * radius)).ncard : ℝ) ≤
            4 * Real.rpow (176 * radius / tRep) epsilon * metricBound

def AmbientRestrictedSelectedFiberBallBoundStatement : Prop :=
  ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ},
    ∀ (data : DyadicFineAssignmentData
        family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
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
      (radius metricBound : ℝ),
      0 < delta →
      0 < radius →
      delta < 11 * radius →
      11 * radius < tRep / 8 →
      0 ≤ metricBound →
      (∀ p : ambientRestrictedSet data center,
        (((ambientRestrictedData data center hE).metricFiber p).card : ℝ) ≤
          metricBound) →
      ∀ coarse rectangle,
        rectangle ∈
          incidenceRectangleSupport degreeSetup.selectedEdges
            coarseSetup.coarseData.parent coarse →
        ∀ testCenter,
          (((incidenceRectangleFiber degreeSetup.selectedEdges rectangle :
                Set C2Function) ∩
              c2Ball testCenter (11 * radius)).ncard : ℝ) ≤
            4 * Real.rpow (176 * radius / tRep) epsilon * metricBound

end Kakeya.Cinematic
