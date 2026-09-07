import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedJointIncidenceSetupInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedPaperClusterScaleInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedSupportNonconcentrationSetupInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedSupportTangentBallCoverInputs

/-!
# Canonical paper-radius cluster setup in one ambient bin

Combine the joint `mu₁`/`mu₂` incidence data with the variable paper radius,
the fixed-ball Lemma 47 transfer, and one common tangent-ball cover.  The
strict lower scale `delta < 11r` remains an explicit small-scale input.
-/

noncomputable section

namespace Kakeya.Cinematic

structure AmbientRestrictedJointClusterSetupData
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K D delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
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
      data center hE fineSetup coarseSetup massExponent)
    (incidence : AmbientRestrictedJointIncidenceSetupData
      data center hE fineSetup coarseSetup refinement) where
  fiberRatio : ℝ
  fiberRatio_eq :
    fiberRatio =
      4 * Real.rpow (2 * tRep / DeltaRep) eta
  fiberRatio_ge_one : 1 ≤ fiberRatio
  radius : ℝ
  radius_eq :
    radius =
      ambientRestrictedPaperClusterRadius
        tRep epsilon incidence.heavySetup.heavyLogLoss fiberRatio
  A : ℝ
  A_eq :
    A =
      ambientRestrictedPaperClusterParameter
        C_R tRep epsilon incidence.heavySetup.heavyLogLoss fiberRatio
  coefficient : ℝ
  coefficient_eq :
    coefficient =
      ambientRestrictedPaperFiberCoefficient
        tRep epsilon incidence.heavySetup.heavyLogLoss fiberRatio
  radius_pos : 0 < radius
  radius_upper : 11 * radius < tRep / 8
  A_ge_one : 1 ≤ A
  scale_identity :
    C_R * tRep / A = 8 * radius
  proposition26_admissible :
    DeltaRep ≤ A * (C_R * tRep)
  coefficient_small :
    4 * incidence.heavySetup.heavyLogLoss * coefficient ≤ 1
  nonconcentration :
    SelectedSupportNonconcentrationSetupData
      data center hE fineSetup coarseSetup refinement
        incidence.degreeSetup incidence.q_fiber incidence.fiberBound
        incidence.heavySetup
        ((2 * incidence.heavySetup.heavyLogLoss) * coefficient)
        radius
  ballCoefficient_small :
    2 * ((2 * incidence.heavySetup.heavyLogLoss) * coefficient) ≤ 1
  cover :
    SelectedSupportTangentBallCoverData
      (D := D) data center hE fineSetup coarseSetup refinement
        incidence.degreeSetup incidence.q_fiber incidence.fiberBound
        incidence.heavySetup radius

def AmbientRestrictedJointClusterSetupStatement : Prop :=
  AmbientRestrictedPaperClusterScaleStatement →
    AmbientRestrictedSelectedFiberBallBoundOnRetainedStatement →
    SelectedSupportNonconcentrationSetupStatement →
    SelectedSupportTangentBallCoverStatement →
    ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
      {K D delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ},
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
        (incidence : AmbientRestrictedJointIncidenceSetupData
          data center hE fineSetup coarseSetup refinement),
        1 ≤ C_R →
        1 ≤ D →
        IsCinematicFamily family K D →
        0 < delta →
        delta < 11 *
          ambientRestrictedPaperClusterRadius
            tRep epsilon incidence.heavySetup.heavyLogLoss
              (4 * Real.rpow (2 * tRep / DeltaRep) eta) →
        Nonempty
          (AmbientRestrictedJointClusterSetupData
            (D := D) data center hE fineSetup coarseSetup
              refinement incidence)

def AmbientRestrictedJointClusterSetupFromSeparationStatement : Prop :=
  AmbientRestrictedPaperClusterScaleStatement →
    SelectedSupportNonconcentrationSetupStatement →
    SelectedSupportTangentBallCoverStatement →
    ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
      {K D delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ},
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
        (incidence : AmbientRestrictedJointIncidenceSetupData
          data center hE fineSetup coarseSetup refinement),
        1 ≤ C_R →
        1 ≤ D →
        IsCinematicFamily family K D →
        0 < delta →
        22 *
            ambientRestrictedPaperClusterRadius
              tRep epsilon incidence.heavySetup.heavyLogLoss
                (4 * Real.rpow (2 * tRep / DeltaRep) eta) <
          data.separationScale →
        8 * incidence.heavySetup.heavyLogLoss ≤
          (incidence.q_fiber : ℝ) →
        Nonempty
          (AmbientRestrictedJointClusterSetupData
            (D := D) data center hE fineSetup coarseSetup
              refinement incidence)

end Kakeya.Cinematic
