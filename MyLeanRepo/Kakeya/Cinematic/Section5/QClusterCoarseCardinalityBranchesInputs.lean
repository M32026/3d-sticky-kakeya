import MyLeanRepo.Kakeya.Cinematic.Section5.ClusterLowerScale
import MyLeanRepo.Kakeya.Cinematic.Section5.NormalCoarseCountAlgebra
import MyLeanRepo.Kakeya.Cinematic.Section5.ScaleFreeNormalCoarseRectangleCount
import MyLeanRepo.Kakeya.Cinematic.Section5.ScaleFreeNormalCoarseCountFromPairs
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedSupportTangentBallCoverInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.SingletonClusterCoarseCardinalityWitnessInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.SingletonSeparatedTangentBallPairAtInputs

/-!
# The two cluster-cardinality branches

The common selected support scale is either large enough to choose a positive
cluster quotient, or it is smaller than twice the tangent-ball cover
cardinality.  The first branch exposes the support-decay factor.  The second
uses the singleton explicit-pair route and exposes an ambient-cardinality
tail without a negative support power.
-/

namespace Kakeya.Cinematic

inductive QClusterCoarseCardinalityResult
    (coarseCard support centers ambientCard : ℕ)
    (C_positive C_singleton tangency A : ℝ) : Prop where
  | positive :
      (coarseCard : ℝ) ≤
        ((centers : ℝ) ^ 2 *
          (C_positive * Real.rpow tangency C_positive *
            Real.rpow A C_positive)) *
        Real.rpow (support : ℝ) (-3 / 2 : ℝ) *
        (Real.rpow
            (8 * (centers : ℝ) * (ambientCard : ℝ))
            (3 / 2 : ℝ) *
          Real.log
            (8 * (centers : ℝ) * (ambientCard : ℝ) /
              (support : ℝ))) →
      QClusterCoarseCardinalityResult
        coarseCard support centers ambientCard
          C_positive C_singleton tangency A
  | singleton :
      support < 2 * centers →
      (coarseCard : ℝ) ≤
        ((centers : ℝ) ^ 2 *
          (C_singleton * Real.rpow tangency C_singleton *
            Real.rpow A C_singleton)) *
        (Real.rpow (2 * (ambientCard : ℝ)) (3 / 2 : ℝ) *
          Real.log (2 * (ambientCard : ℝ))) →
      QClusterCoarseCardinalityResult
        coarseCard support centers ambientCard
          C_positive C_singleton tangency A

def QClusterCoarseCardinalityBranchesStatement : Prop :=
  BipartiteTangencyRobustFullStatement →
    ScaleFreeNormalCoarseRectangleCountStatement →
    ScaleFreeNormalCoarseRectangleCountFromPairsStatement →
    SingletonSeparatedTangentBallPairAtStatement →
    SingletonClusterCoarseCardinalityWitnessStatement →
    ∀ K : ℝ, 1 ≤ K →
      ∃ C_positive C_singleton : ℝ,
        1 ≤ C_positive ∧
        1 ≤ C_singleton ∧
        ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
          {D delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ},
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
            (q_fiber : ℕ)
            (fiberBound : ℝ)
            (heavySetup : RetainedHeavySupportSetupData
              data center hE fineSetup coarseSetup refinement
                degreeSetup q_fiber fiberBound)
            (ballCoefficient : ℝ)
            (radius A : ℝ)
            (nonconcentration :
              SelectedSupportNonconcentrationSetupData
                data center hE fineSetup coarseSetup refinement
                  degreeSetup q_fiber fiberBound heavySetup
                    ballCoefficient radius)
            (cover : SelectedSupportTangentBallCoverData
              (D := D) data center hE fineSetup coarseSetup refinement
                degreeSetup q_fiber fiberBound heavySetup radius),
            IsCinematicFamily family K D →
            2 * ballCoefficient ≤ 1 →
            0 < radius →
            1 ≤ A →
            C_R * tRep / A = 8 * radius →
            delta ≤ A * (C_R * tRep) →
            QClusterCoarseCardinalityResult
              heavySetup.selectedCoarse.card
              (2 ^ heavySetup.supportLevel)
              cover.centers.card
              (data.ambientSource.cluster center (3 * tRep)).card
              C_positive C_singleton coarseSetup.tangency A

end Kakeya.Cinematic
