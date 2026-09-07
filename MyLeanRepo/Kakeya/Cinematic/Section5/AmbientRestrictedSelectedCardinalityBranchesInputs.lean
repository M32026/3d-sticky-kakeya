import MyLeanRepo.Kakeya.Cinematic.Section5.NormalSelectedTotalCardinalityInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.QClusterCoarseCardinalityBranchesInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.SmallSupportTotalCardinalityInputs

/-!
# Selected fine-cardinality branches inside one ambient bin

This is the structure-level caller for the two coarse-count branches.  It
transports the selected dyadic-layer cardinality through parent, incidence
degree, heavy-parent, and support regularizations, then applies either the
positive support-decay route or the singleton small-support route.
-/

namespace Kakeya.Cinematic

inductive AmbientRestrictedSelectedCardinalityResult
    (selected centers ambientCard support mu : ℕ)
    (parentLoss degreeLoss supportLoss retention
      measureScale tangencyScale C_positive C_singleton tangency A : ℝ) :
    Prop where
  | positive :
      (selected : ℝ) ≤
        (48 * parentLoss * degreeLoss * supportLoss *
          Real.rpow retention (-1)) *
        ((Real.rpow measureScale (1 / 4 : ℝ) *
            Real.rpow tangencyScale (3 / 4 : ℝ)) *
          ((centers : ℝ) ^ 2 *
            (C_positive * Real.rpow tangency C_positive *
              Real.rpow A C_positive)) *
          (Real.rpow
              (8 * (centers : ℝ) * (ambientCard : ℝ))
              (3 / 2 : ℝ) *
            Real.log
              (8 * (centers : ℝ) * (ambientCard : ℝ) /
                (support : ℝ))) *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ)) →
      AmbientRestrictedSelectedCardinalityResult
        selected centers ambientCard support mu
          parentLoss degreeLoss supportLoss retention
          measureScale tangencyScale C_positive C_singleton tangency A
  | singleton :
      (selected : ℝ) ≤
        (48 * parentLoss * degreeLoss * supportLoss *
          Real.rpow retention (-1)) *
        ((Real.rpow measureScale (1 / 4 : ℝ) *
            Real.rpow tangencyScale (3 / 4 : ℝ)) *
          ((centers : ℝ) ^ 2 *
            (C_singleton * Real.rpow tangency C_singleton *
              Real.rpow A C_singleton)) *
          (Real.rpow (2 * (ambientCard : ℝ)) (3 / 2 : ℝ) *
            Real.log (2 * (ambientCard : ℝ))) *
          Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ) *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ)) →
      AmbientRestrictedSelectedCardinalityResult
        selected centers ambientCard support mu
          parentLoss degreeLoss supportLoss retention
          measureScale tangencyScale C_positive C_singleton tangency A

def AmbientRestrictedSelectedCardinalityBranchesStatement : Prop :=
  CoarseMultiplicityInterpolationStatement →
    NormalSelectedTotalCardinalityStatement →
    SmallSupportTotalCardinalityStatement →
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
        (degreeSetup : RetainedIncidenceDegreeSetupData
          data center hE fineSetup coarseSetup refinement)
        (q_fiber : ℕ)
        (fiberBound : ℝ)
        (heavySetup : RetainedHeavySupportSetupData
          data center hE fineSetup coarseSetup refinement
            degreeSetup q_fiber fiberBound)
        (radius A : ℝ)
        (cover : SelectedSupportTangentBallCoverData
          (D := D) data center hE fineSetup coarseSetup refinement
            degreeSetup q_fiber fiberBound heavySetup radius)
        (C_positive C_singleton retention
          measureScale tangencyScale : ℝ),
        2 ≤ q_fiber →
        1 ≤ A →
        1 ≤ C_positive →
        1 ≤ C_singleton →
        0 < fiberBound →
        0 < retention →
        0 ≤ measureScale →
        0 ≤ tangencyScale →
        fiberBound ≤ 2 * (data.mu : ℝ) →
        retention * (data.mu : ℝ) <
          4 * ((q_fiber : ℝ) + 1) →
        (∀ rectangle ∈ degreeSetup.retained,
          q_fiber ≤ (degreeSetup.fiber rectangle).card) →
        ((heavySetup.M_parent : ℕ) : ℝ) ≤ measureScale →
        ((heavySetup.M_parent : ℕ) : ℝ) ≤
          tangencyScale *
            Real.rpow (data.mu : ℝ) (-2) *
            Real.rpow (2 ^ heavySetup.supportLevel : ℕ) 2 →
        QClusterCoarseCardinalityResult
          heavySetup.selectedCoarse.card
          (2 ^ heavySetup.supportLevel)
          cover.centers.card
          (data.ambientSource.cluster center (3 * tRep)).card
          C_positive C_singleton coarseSetup.tangency A →
        AmbientRestrictedSelectedCardinalityResult
          refinement.selected.card
          cover.centers.card
          (data.ambientSource.cluster center (3 * tRep)).card
          (2 ^ heavySetup.supportLevel)
          data.mu
          (Nat.log2 refinement.selected.card + 1)
          heavySetup.degreeLoss
          (Nat.log2 heavySetup.ambient.card + 1)
          retention measureScale tangencyScale
          C_positive C_singleton coarseSetup.tangency A

inductive AmbientRestrictedSelectedCardinalityResultOfFiber
    (selected centers ambientCard support mu : ℕ)
    (fiberCoefficient parentLoss degreeLoss supportLoss retention
      measureScale tangencyScale C_positive C_singleton tangency A : ℝ) :
    Prop where
  | positive :
      (selected : ℝ) ≤
        (24 * fiberCoefficient * parentLoss * degreeLoss * supportLoss *
          Real.rpow retention (-1)) *
        ((Real.rpow measureScale (1 / 4 : ℝ) *
            Real.rpow tangencyScale (3 / 4 : ℝ)) *
          ((centers : ℝ) ^ 2 *
            (C_positive * Real.rpow tangency C_positive *
              Real.rpow A C_positive)) *
          (Real.rpow
              (8 * (centers : ℝ) * (ambientCard : ℝ))
              (3 / 2 : ℝ) *
            Real.log
              (8 * (centers : ℝ) * (ambientCard : ℝ) /
                (support : ℝ))) *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ)) →
      AmbientRestrictedSelectedCardinalityResultOfFiber
        selected centers ambientCard support mu fiberCoefficient
          parentLoss degreeLoss supportLoss retention
          measureScale tangencyScale C_positive C_singleton tangency A
  | singleton :
      (selected : ℝ) ≤
        (24 * fiberCoefficient * parentLoss * degreeLoss * supportLoss *
          Real.rpow retention (-1)) *
        ((Real.rpow measureScale (1 / 4 : ℝ) *
            Real.rpow tangencyScale (3 / 4 : ℝ)) *
          ((centers : ℝ) ^ 2 *
            (C_singleton * Real.rpow tangency C_singleton *
              Real.rpow A C_singleton)) *
          (Real.rpow (2 * (ambientCard : ℝ)) (3 / 2 : ℝ) *
            Real.log (2 * (ambientCard : ℝ))) *
          Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ) *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ)) →
      AmbientRestrictedSelectedCardinalityResultOfFiber
        selected centers ambientCard support mu fiberCoefficient
          parentLoss degreeLoss supportLoss retention
          measureScale tangencyScale C_positive C_singleton tangency A

def AmbientRestrictedSelectedCardinalityBranchesOfFiberStatement : Prop :=
  CoarseMultiplicityInterpolationStatement →
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
      (degreeSetup : RetainedIncidenceDegreeSetupData
        data center hE fineSetup coarseSetup refinement)
      (q_fiber : ℕ)
      (fiberBound fiberCoefficient : ℝ)
      (heavySetup : RetainedHeavySupportSetupData
        data center hE fineSetup coarseSetup refinement
          degreeSetup q_fiber fiberBound)
      (radius A : ℝ)
      (cover : SelectedSupportTangentBallCoverData
        (D := D) data center hE fineSetup coarseSetup refinement
          degreeSetup q_fiber fiberBound heavySetup radius)
      (C_positive C_singleton retention
        measureScale tangencyScale : ℝ),
      2 ≤ q_fiber →
      1 ≤ A →
      1 ≤ C_positive →
      1 ≤ C_singleton →
      0 < fiberBound →
      0 < retention →
      0 ≤ fiberCoefficient →
      0 ≤ measureScale →
      0 ≤ tangencyScale →
      fiberBound ≤ fiberCoefficient * (data.mu : ℝ) →
      retention * (data.mu : ℝ) <
        4 * ((q_fiber : ℝ) + 1) →
      (∀ rectangle ∈ degreeSetup.retained,
        q_fiber ≤ (degreeSetup.fiber rectangle).card) →
      ((heavySetup.M_parent : ℕ) : ℝ) ≤ measureScale →
      ((heavySetup.M_parent : ℕ) : ℝ) ≤
        tangencyScale *
          Real.rpow (data.mu : ℝ) (-2) *
          Real.rpow (2 ^ heavySetup.supportLevel : ℕ) 2 →
      QClusterCoarseCardinalityResult
        heavySetup.selectedCoarse.card
        (2 ^ heavySetup.supportLevel)
        cover.centers.card
        (data.ambientSource.cluster center (3 * tRep)).card
        C_positive C_singleton coarseSetup.tangency A →
      AmbientRestrictedSelectedCardinalityResultOfFiber
        refinement.selected.card
        cover.centers.card
        (data.ambientSource.cluster center (3 * tRep)).card
        (2 ^ heavySetup.supportLevel)
        data.mu fiberCoefficient
        (Nat.log2 refinement.selected.card + 1)
        heavySetup.degreeLoss
        (Nat.log2 heavySetup.ambient.card + 1)
        retention measureScale tangencyScale
        C_positive C_singleton coarseSetup.tangency A

end Kakeya.Cinematic
