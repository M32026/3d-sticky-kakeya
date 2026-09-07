import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12InternalBridge
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Extremal
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12CroppedExtremal
import MyLeanRepo.Kakeya.Assouad.PropStickyOrdinaryToCroppedShading
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements

/-!
# Public Definition 2.12 to internal WZ preparation

This file freezes the provenance certificate needed before the existing
cropped full-line Section 6 proof can be used.  It is a statement boundary,
not a claim that the preparation is already constructed.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Cubical cropped preparation of one ordinary pure extremal pair. -/
structure WZ2PaperPureToCroppedShadingData
    {delta sigma loss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : Kakeya.Streamlined.TubeShading source)
    (sourceExtremal :
      WZ2PaperPureIsExtremal sigma loss source sourceShading)
    (logExponent : ℕ) where
  selected : Kakeya.Streamlined.TubeSubfamily source
  ordinaryRefined :
    Kakeya.Streamlined.TubeShading selected.family
  ordinary_subshading :
    ∀ index,
      ordinaryRefined.carrier index ⊆
        sourceShading.carrier (selected.embedding index)
  retained_mass :
    wz2PaperPureRefinementFraction delta logExponent *
        sourceShading.mass ≤
      ordinaryRefined.mass
  croppedRefined :
    WZ1PaperTubeShading selected.family
  cropped_carrier_eq :
    croppedRefined.carrier = ordinaryRefined.carrier
  cropped_cubical :
    WZ1PaperIsCubicalShading croppedRefined
  cropped_nonempty :
    ∀ index, (croppedRefined.carrier index).Nonempty
  cropped_extremal :
    WZ2PaperCroppedIsExtremal
      sigma loss selected.family croppedRefined

/--
One caller-scale cover carrying the public pure cover and the internal WZ
certificate on the same retained families.
-/
structure WZ2PaperPureToCroppedCoverData
    {delta sigma sourceLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    {sourceExtremal :
      WZ2PaperPureIsExtremal
        sigma sourceLoss source sourceShading}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperPureToCroppedShadingData
        sourceShading sourceExtremal preparationExponent)
    (rho : WZ2PaperRequestedScale delta)
    (C : ENNReal) where
  coarse : Kakeya.Streamlined.TubeFamily rho.1
  publicCover :
    WZ2PaperPurePartitioningCover prepared.selected.family coarse
  publicUniform :
    WZ2PaperPureFullFibersAreCUniform
      prepared.selected.family coarse C
  internalCover :
    WZ2PaperPartitioningCover prepared.selected.family coarse
  parent_eq :
    ∀ source,
      publicCover.parent source =
        internalCover.toWZ1PaperTubeCover.parent source
  ordinary_assigned_fiber_eq :
    ∀ parent,
      wz2PaperOrdinaryFullFiberIndices
          prepared.selected.family coarse parent =
        internalCover.toWZ1PaperTubeCover.fiberIndices parent
  cropped_assigned_fiber_eq :
    ∀ parent,
      wz2PaperLiteralFullFiberIndices
          prepared.selected.family coarse parent =
        internalCover.toWZ1PaperTubeCover.fiberIndices parent
  coarseCroppedShading :
    WZ1PaperTubeShading coarse
  point_compatibility :
    ∀ source point,
      point ∈ prepared.croppedRefined.carrier source →
        point ∈
          coarseCroppedShading.carrier
            (internalCover.toWZ1PaperTubeCover.parent source)

/--
The complete model-conversion and strictification producer needed before the
existing cropped Section 6 balancing proof.
-/
def WZ2PaperPureToCroppedPreparationStatement : Prop :=
  ∃ preparationExponent : ℕ,
  ∀ sigma outputLoss : ℝ,
    0 < sigma → sigma < 1 →
    0 < outputLoss →
    HasWZ2PaperCroppedCriticalVolumeFloor sigma →
      ∃ inputLoss delta₀ : ℝ,
        0 < inputLoss ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ source : Kakeya.Streamlined.TubeFamily delta,
            ∀ sourceShading :
                Kakeya.Streamlined.TubeShading source,
              ∀ sourceExtremal :
                  WZ2PaperPureIsExtremal
                    sigma inputLoss source sourceShading,
                ∀ rho : WZ2PaperRequestedScale delta,
                  Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                  rho.1 ≤ Real.rpow delta outputLoss →
                    ∃ prepared :
                        WZ2PaperPureToCroppedShadingData
                          sourceShading sourceExtremal
                          preparationExponent,
                      ∃ C : ENNReal,
                        WZ2PaperFiniteErrorConstant C ∧
                        Nonempty
                          (WZ2PaperPureToCroppedCoverData
                            prepared rho C)

end Kakeya.Assouad

end
