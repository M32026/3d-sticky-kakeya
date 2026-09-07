import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedSelectedCardinalityBranchesInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedSelectedLocalVolumeBranchesInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedLayerFixedAmbientVolumeAssemblyInputs

/-!
# Lambda-aware fixed-bin local-volume branches

This interface instantiates the selected-layer mass cancellation on one
ambient-restricted bin.  The parent multiplicity measure scale is explicitly
`parentArea / layerMass`; after cancellation the output contains only the
paper-faithful geometric mean of the parent-neighborhood area and the fine
shading area.
-/

open MeasureTheory

namespace Kakeya.Cinematic

noncomputable def ambientRestrictedSelectedFineGeometricArea
    (C_shading delta C_R tRep DeltaRep : ℝ) : ℝ :=
  2 * (C_shading * delta) *
    Real.sqrt
      ((C_shading * delta) /
        (C_R * tRep * DeltaRep / delta))

noncomputable def ambientRestrictedPositiveLayerBaseCoefficientOfFiber
    (fiberCoefficient parentLoss degreeLoss supportLoss retention
      tangencyScale : ℝ)
    (centers : ℕ)
    (C_positive tangency A : ℝ)
    (mu : ℕ) : ℝ :=
  (24 * fiberCoefficient * parentLoss * degreeLoss * supportLoss *
      Real.rpow retention (-1)) *
    Real.rpow tangencyScale (3 / 4 : ℝ) *
    ((centers : ℝ) ^ 2 *
      (C_positive * Real.rpow tangency C_positive *
        Real.rpow A C_positive)) *
    Real.rpow (mu : ℝ) (-3 / 2 : ℝ)

noncomputable def ambientRestrictedSingletonLayerBaseCoefficientOfFiber
    (fiberCoefficient parentLoss degreeLoss supportLoss retention
      tangencyScale : ℝ)
    (centers : ℕ)
    (C_singleton tangency A : ℝ)
    (mu : ℕ) : ℝ :=
  (24 * fiberCoefficient * parentLoss * degreeLoss * supportLoss *
      Real.rpow retention (-1)) *
    Real.rpow tangencyScale (3 / 4 : ℝ) *
    ((centers : ℝ) ^ 2 *
      (C_singleton * Real.rpow tangency C_singleton *
        Real.rpow A C_singleton)) *
    Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ) *
    Real.rpow (mu : ℝ) (-3 / 2 : ℝ)

noncomputable def ambientRestrictedLayerLinearizedLocalCoefficient
    (baseCoefficient prefactor cardUpper logTail layerFactor
      parentArea fineArea : ℝ) : ℝ :=
  ((baseCoefficient * prefactor *
      Real.sqrt (prefactor * cardUpper) * logTail) *
      layerFactor) *
    Real.rpow parentArea (1 / 4 : ℝ) *
    Real.rpow fineArea (3 / 4 : ℝ)

def AmbientRestrictedSelectedLayerLocalVolumeBranchesStatement : Prop :=
  SelectedLayerMassCancellationStatement →
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
          parentArea tangencyScale cardUpper : ℝ),
        1 ≤ A →
        1 ≤ C_positive →
        1 ≤ C_singleton →
        0 < retention →
        0 ≤ fiberCoefficient →
        0 ≤ parentArea →
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
        AmbientRestrictedSelectedCardinalityResultOfFiber
          refinement.selected.card
          cover.centers.card
          (data.ambientSource.cluster center (3 * tRep)).card
          (2 ^ heavySetup.supportLevel)
          data.mu fiberCoefficient
          (Nat.log2 refinement.selected.card + 1)
          heavySetup.degreeLoss
          (Nat.log2 heavySetup.ambient.card + 1)
          retention
          (parentArea /
            (((2 : ENNReal) ^ refinement.layer.val *
              refinement.cutoff).toReal))
          tangencyScale C_positive C_singleton coarseSetup.tangency A →
        AmbientRestrictedSelectedLocalVolumeResult
          (ambientRestrictedSet data center)
          (data.ambientSource.cluster center (3 * tRep)).card
          (ambientRestrictedLayerLinearizedLocalCoefficient
            (ambientRestrictedPositiveLayerBaseCoefficientOfFiber
              fiberCoefficient
              (Nat.log2 refinement.selected.card + 1)
              heavySetup.degreeLoss
              (Nat.log2 heavySetup.ambient.card + 1)
              retention tangencyScale cover.centers.card C_positive
              coarseSetup.tangency A data.mu)
            (8 * (cover.centers.card : ℝ))
            cardUpper
            (Real.log
              (8 * (cover.centers.card : ℝ) *
                  ((data.ambientSource.cluster
                    center (3 * tRep)).card : ℝ) /
                (2 ^ heavySetup.supportLevel : ℕ)))
            ((2 * refinement.massFactor : ℕ) : ℝ)
            parentArea
            (ambientRestrictedSelectedFineGeometricArea
              C_shading delta C_R tRep DeltaRep))
          (ambientRestrictedLayerLinearizedLocalCoefficient
            (ambientRestrictedSingletonLayerBaseCoefficientOfFiber
              fiberCoefficient
              (Nat.log2 refinement.selected.card + 1)
              heavySetup.degreeLoss
              (Nat.log2 heavySetup.ambient.card + 1)
              retention tangencyScale cover.centers.card C_singleton
              coarseSetup.tangency A data.mu)
            2 cardUpper
            (Real.log
              (2 *
                ((data.ambientSource.cluster
                  center (3 * tRep)).card : ℝ)))
            ((2 * refinement.massFactor : ℕ) : ℝ)
            parentArea
            (ambientRestrictedSelectedFineGeometricArea
              C_shading delta C_R tRep DeltaRep))

end Kakeya.Cinematic
