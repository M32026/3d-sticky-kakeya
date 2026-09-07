import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedSelectedCardinalityBranchesInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedSelectedFineVolumeInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.FixedAmbientRpowFineVolumeAssemblyInputs

/-!
# Fixed-bin local volume from the two selected-cardinality branches

The selected dyadic layer controls the full bin volume with one explicit area
factor.  Each selected-cardinality branch has one ambient-cardinality
`3/2`-power.  This module freezes the exact coefficients obtained after
linearizing that power while leaving the final small-scale absorption to the
caller.
-/

open MeasureTheory

namespace Kakeya.Cinematic

noncomputable def ambientRestrictedSelectedFineArea
    (massFactor : ℕ)
    (C_shading delta C_R tRep DeltaRep : ℝ) : ℝ :=
  (massFactor : ℝ) *
    (2 * (C_shading * delta) *
      Real.sqrt
        ((C_shading * delta) /
          (C_R * tRep * DeltaRep / delta)))

noncomputable def ambientRestrictedPositiveCardinalityCoefficient
    (parentLoss degreeLoss supportLoss retention
      measureScale tangencyScale : ℝ)
    (centers : ℕ)
    (C_positive tangency A : ℝ)
    (mu : ℕ) : ℝ :=
  (48 * parentLoss * degreeLoss * supportLoss *
      Real.rpow retention (-1)) *
    (Real.rpow measureScale (1 / 4 : ℝ) *
      Real.rpow tangencyScale (3 / 4 : ℝ)) *
    ((centers : ℝ) ^ 2 *
      (C_positive * Real.rpow tangency C_positive *
        Real.rpow A C_positive)) *
    Real.rpow (mu : ℝ) (-3 / 2 : ℝ)

noncomputable def ambientRestrictedSingletonCardinalityCoefficient
    (parentLoss degreeLoss supportLoss retention
      measureScale tangencyScale : ℝ)
    (centers : ℕ)
    (C_singleton tangency A : ℝ)
    (mu : ℕ) : ℝ :=
  (48 * parentLoss * degreeLoss * supportLoss *
      Real.rpow retention (-1)) *
    (Real.rpow measureScale (1 / 4 : ℝ) *
      Real.rpow tangencyScale (3 / 4 : ℝ)) *
    ((centers : ℝ) ^ 2 *
      (C_singleton * Real.rpow tangency C_singleton *
        Real.rpow A C_singleton)) *
    Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ) *
    Real.rpow (mu : ℝ) (-3 / 2 : ℝ)

noncomputable def ambientRestrictedPositiveCardinalityCoefficientOfFiber
    (fiberCoefficient parentLoss degreeLoss supportLoss retention
      measureScale tangencyScale : ℝ)
    (centers : ℕ)
    (C_positive tangency A : ℝ)
    (mu : ℕ) : ℝ :=
  (24 * fiberCoefficient * parentLoss * degreeLoss * supportLoss *
      Real.rpow retention (-1)) *
    (Real.rpow measureScale (1 / 4 : ℝ) *
      Real.rpow tangencyScale (3 / 4 : ℝ)) *
    ((centers : ℝ) ^ 2 *
      (C_positive * Real.rpow tangency C_positive *
        Real.rpow A C_positive)) *
    Real.rpow (mu : ℝ) (-3 / 2 : ℝ)

noncomputable def ambientRestrictedSingletonCardinalityCoefficientOfFiber
    (fiberCoefficient parentLoss degreeLoss supportLoss retention
      measureScale tangencyScale : ℝ)
    (centers : ℕ)
    (C_singleton tangency A : ℝ)
    (mu : ℕ) : ℝ :=
  (24 * fiberCoefficient * parentLoss * degreeLoss * supportLoss *
      Real.rpow retention (-1)) *
    (Real.rpow measureScale (1 / 4 : ℝ) *
      Real.rpow tangencyScale (3 / 4 : ℝ)) *
    ((centers : ℝ) ^ 2 *
      (C_singleton * Real.rpow tangency C_singleton *
        Real.rpow A C_singleton)) *
    Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ) *
    Real.rpow (mu : ℝ) (-3 / 2 : ℝ)

noncomputable def ambientRestrictedLinearizedLocalCoefficient
    (coefficient prefactor cardUpper logTail area : ℝ) : ℝ :=
  (coefficient * prefactor *
      Real.sqrt (prefactor * cardUpper) * logTail) *
    area

inductive AmbientRestrictedSelectedLocalVolumeResult
    (bin : Set (ℝ × ℝ))
    (ambientCard : ℕ)
    (positiveCoefficient singletonCoefficient : ℝ) : Prop where
  | positive :
      volume bin ≤
        ENNReal.ofReal positiveCoefficient * ambientCard →
      AmbientRestrictedSelectedLocalVolumeResult
        bin ambientCard positiveCoefficient singletonCoefficient
  | singleton :
      volume bin ≤
        ENNReal.ofReal singletonCoefficient * ambientCard →
      AmbientRestrictedSelectedLocalVolumeResult
        bin ambientCard positiveCoefficient singletonCoefficient

def AmbientRestrictedSelectedLocalVolumeBranchesStatement : Prop :=
  AmbientRestrictedSelectedFineVolumeStatement →
    FixedAmbientRpowFineVolumeAssemblyStatement →
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
          measureScale tangencyScale cardUpper : ℝ),
        1 ≤ A →
        1 ≤ C_positive →
        1 ≤ C_singleton →
        0 < retention →
        0 ≤ measureScale →
        0 ≤ tangencyScale →
        0 ≤ C_shading →
        0 ≤ delta →
        0 ≤ cardUpper →
        ((data.ambientSource.cluster center (3 * tRep)).card : ℝ) ≤
          cardUpper →
        0 ≤
          Real.log
            (8 * (cover.centers.card : ℝ) *
                ((data.ambientSource.cluster center (3 * tRep)).card : ℝ) /
              (2 ^ heavySetup.supportLevel : ℕ)) →
        0 ≤
          Real.log
            (2 *
              ((data.ambientSource.cluster center (3 * tRep)).card : ℝ)) →
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
          C_positive C_singleton coarseSetup.tangency A →
        AmbientRestrictedSelectedLocalVolumeResult
          (ambientRestrictedSet data center)
          (data.ambientSource.cluster center (3 * tRep)).card
          (ambientRestrictedLinearizedLocalCoefficient
            (ambientRestrictedPositiveCardinalityCoefficient
              (Nat.log2 refinement.selected.card + 1)
              heavySetup.degreeLoss
              (Nat.log2 heavySetup.ambient.card + 1)
              retention measureScale tangencyScale
              cover.centers.card C_positive
              coarseSetup.tangency A data.mu)
            (8 * (cover.centers.card : ℝ))
            cardUpper
            (Real.log
              (8 * (cover.centers.card : ℝ) *
                  ((data.ambientSource.cluster
                    center (3 * tRep)).card : ℝ) /
                (2 ^ heavySetup.supportLevel : ℕ)))
            (ambientRestrictedSelectedFineArea
              refinement.massFactor C_shading delta
                C_R tRep DeltaRep))
          (ambientRestrictedLinearizedLocalCoefficient
            (ambientRestrictedSingletonCardinalityCoefficient
              (Nat.log2 refinement.selected.card + 1)
              heavySetup.degreeLoss
              (Nat.log2 heavySetup.ambient.card + 1)
              retention measureScale tangencyScale
              cover.centers.card C_singleton
              coarseSetup.tangency A data.mu)
            2 cardUpper
            (Real.log
              (2 *
                ((data.ambientSource.cluster
                  center (3 * tRep)).card : ℝ)))
            (ambientRestrictedSelectedFineArea
              refinement.massFactor C_shading delta
                C_R tRep DeltaRep))

end Kakeya.Cinematic
