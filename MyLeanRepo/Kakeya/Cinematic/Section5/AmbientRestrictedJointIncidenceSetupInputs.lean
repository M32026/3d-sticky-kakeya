import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedParentFiberRegularizationInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedSelectedFiberBallBoundInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.RetainedHeavySupportSetupInputs

/-!
# Canonical incidence setup from the joint retained-fiber scale

After the paper's metric/retained fiber pigeonhole, the retained dyadic level
is the canonical `mu₂` scale.  Build every later finite incidence package from
that exact level rather than from an unrelated safe multiplicity lower bound.
-/

noncomputable section

namespace Kakeya.Cinematic

structure AmbientRestrictedJointIncidenceSetupData
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    (data : DyadicFineAssignmentData
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
      data center hE fineSetup coarseSetup massExponent) where
  q_fiber : ℕ
  q_fiber_eq :
    q_fiber = refinement.retainedScale
  fiberBound : ℝ
  fiberBound_eq :
    fiberBound = 2 * (q_fiber : ℝ)
  retention : ℝ
  retention_eq :
    retention =
      Real.rpow (tRep / (8 * diameter)) epsilon *
        Real.rpow (DeltaRep / (2 * tRep)) eta
  degreeSetup : RetainedIncidenceDegreeSetupData
    data center hE fineSetup coarseSetup refinement
  heavySetup : RetainedHeavySupportSetupData
    data center hE fineSetup coarseSetup refinement
      degreeSetup q_fiber fiberBound
  parentSetup : AmbientRestrictedParentFiberRegularizationData
    data center hE fineSetup coarseSetup refinement
      degreeSetup q_fiber fiberBound heavySetup
  q_fiber_pos : 0 < q_fiber
  fiberBound_pos : 0 < fiberBound
  retained_fiber_range :
    ∀ rectangle ∈ degreeSetup.retained,
      q_fiber ≤ (degreeSetup.fiber rectangle).card ∧
        ((degreeSetup.fiber rectangle).card : ℝ) ≤ fiberBound
  retention_pos : 0 < retention
  retention_mu :
    retention * (data.mu : ℝ) <
      4 * ((q_fiber : ℝ) + 1)
  metricBound : ℝ
  metricBound_eq :
    metricBound =
      (4 * Real.rpow (2 * tRep / DeltaRep) eta) *
        (q_fiber : ℝ)
  metricBound_nonneg : 0 ≤ metricBound
  retained_metric_bound :
    ∀ rectangle ∈ degreeSetup.retained,
      (((ambientRestrictedData data center hE).metricFiber
        (fineSetup.source rectangle)).card : ℝ) ≤ metricBound

def AmbientRestrictedJointIncidenceSetupStatement : Prop :=
  RetainedIncidenceDegreeSetupStatement →
    RetainedHeavySupportSetupStatement →
    AmbientRestrictedParentFiberRegularizationStatement →
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
          data center hE fineSetup coarseSetup massExponent),
        0 < delta →
        Nonempty
          (AmbientRestrictedJointIncidenceSetupData
            data center hE fineSetup coarseSetup refinement)

end Kakeya.Cinematic
