import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalGeometricNumericalHelpers

/-!
# Uniform numerical certificates for final geometric balancing

The scalar crossing, crop, post-balancing, and final balancing estimates are
independent of the prepared dependent pipeline.  This module chooses their
four physical-scale thresholds once and packages the resulting uniform
functions behind a shallow interface.
-/

noncomputable section

namespace Kakeya.Assouad

def WZ2PaperFinalCrossingScalarAtSmallScales
    (sourceLoss stableLoss : ℝ)
    (firstLevelCount secondLevelCount : ℕ)
    (delta₀ : ℝ) : Prop :=
  ∀ {delta rho : ℝ},
    ∀ (hdelta : 0 < delta),
      delta ≤ delta₀ →
      0 < rho →
      rho ≤ 1 →
      Real.rpow delta (1 - stableLoss) ≤ rho →
      ∀ (firstLog secondLog fineLog firstLoss secondLoss
        topLevelConstant : ENNReal),
        firstLog ≤
            ENNReal.ofReal
              (wz2PaperBoundaryLogCoefficient *
                (1 + Real.log delta⁻¹)) →
        secondLog ≤
            ENNReal.ofReal
              (wz2PaperBoundaryLogCoefficient *
                (1 + Real.log delta⁻¹)) →
        fineLog ≤
            ENNReal.ofReal
              (wz2PaperBoundaryLogCoefficient *
                (1 + Real.log delta⁻¹)) →
        firstLoss ≤ 8 * firstLog ^ (firstLevelCount + 2) →
        secondLoss ≤ 8 * secondLog ^ (secondLevelCount + 2) →
        topLevelConstant ≤
            Kakeya.realRpowENN delta (-4 * sourceLoss) →
        let fraction := wz1PaperRefinementFraction delta 20
        let bandFactor :=
          firstLoss * fraction⁻¹ * (secondLoss * fineLog)
        2 * bandFactor * 24000000 *
              (topLevelConstant * wz2PaperBoundaryGeometryConstant + 1) *
              ENNReal.ofReal (Real.sqrt (delta / rho)) <
          wz1PaperRefinementFraction delta 4 *
            ((1 / 2 : ENNReal) *
              Kakeya.realRpowENN delta sourceLoss)

def WZ2PaperFinalCropScalarAtSmallScales
    (sourceLoss outputLoss : ℝ)
    (firstLevelCount secondLevelCount : ℕ)
    (delta₀ : ℝ) : Prop :=
  ∀ {delta rho : ℝ},
    ∀ (hdelta : 0 < delta),
      delta ≤ delta₀ →
      0 < rho →
      rho ≤ 1 →
      rho ≤ Real.rpow delta outputLoss →
      ∀ (firstLog secondLog fineLog availableLog
        firstLoss secondLoss topLevelConstant : ENNReal),
        firstLog ≤
            ENNReal.ofReal
              (wz2PaperBoundaryLogCoefficient *
                (1 + Real.log delta⁻¹)) →
        secondLog ≤
            ENNReal.ofReal
              (wz2PaperBoundaryLogCoefficient *
                (1 + Real.log delta⁻¹)) →
        fineLog ≤
            ENNReal.ofReal
              (wz2PaperBoundaryLogCoefficient *
                (1 + Real.log delta⁻¹)) →
        availableLog ≤
            ENNReal.ofReal
              (wz2PaperBoundaryLogCoefficient *
                (1 + Real.log delta⁻¹)) →
        firstLoss ≤ 8 * firstLog ^ (firstLevelCount + 2) →
        secondLoss ≤ 8 * secondLog ^ (secondLevelCount + 2) →
        topLevelConstant ≤
            Kakeya.realRpowENN delta (-4 * sourceLoss) →
        let fraction := wz1PaperRefinementFraction delta 20
        let lossFactor :=
          firstLoss * fraction⁻¹ *
            (secondLoss * fineLog) * (8 * availableLog)
        2 * lossFactor * wz2PaperCropBoundaryMassConstant *
              (topLevelConstant + 1) *
              ENNReal.ofReal (Real.sqrt rho) <
          wz1PaperRefinementFraction delta 4 *
            ((1 / 2 : ENNReal) *
              Kakeya.realRpowENN delta sourceLoss)

def WZ2PaperPostBalancingAtSmallScales
    (delta₀ : ℝ) : Prop :=
  ∀ {delta rho : ℝ},
    ∀ (hdelta : 0 < delta),
      delta ≤ delta₀ →
      ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
        ∀ {shading : WZ1PaperTubeShading fine},
          ∀ {multiplicityCap : ENNReal},
            ∀ (pruning :
                WZ2PaperBoundaryCellPruningData
                  (rho := rho) shading hdelta multiplicityCap),
              wz1PaperRefinementFraction delta 2 *
                  wz2PaperPostBalancingLoss pruning ≤
                1

def WZ2PaperFinalBalancingAtSmallScales
    (delta₀ : ℝ) : Prop :=
  ∀ {delta rho : ℝ},
    ∀ (hdelta : 0 < delta),
      delta ≤ delta₀ →
      ∀ (hrho : 0 < rho),
        delta ≤ rho →
        rho ≤ 1 →
        ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
          ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
            fine.Nonempty →
            coarse.Nonempty →
            WZ1PaperIsLineClass fine →
            WZ1PaperIsEssentiallyDistinct fine →
            WZ1PaperIsLineClass coarse →
            WZ1PaperIsEssentiallyDistinct coarse →
            ∀ {cover : WZ2PaperPartitioningCover fine coarse},
              ∀ {sourceShading : WZ1PaperTubeShading fine},
                ∀ {coarseCells : Finset WZ2PaperCellIndex},
                  ∀ {availableFineCells :
                      WZ2PaperCellIndex → Finset WZ2PaperCellIndex},
                    ∀ {balancing :
                        WZ2PaperExactCellBalancingData
                          (rho := rho) sourceShading coarseCells
                          availableFineCells},
                      ∀ {coarseData :
                          WZ2PaperCoarseShadingData
                            cover sourceShading coarseCells
                            availableFineCells balancing},
                        ∀ (producer :
                            WZ2PaperFinalBalancedCoverProducerData
                              (hdelta := hdelta) (hrho := hrho)
                              cover sourceShading coarseCells
                              availableFineCells balancing coarseData),
                          wz1PaperRefinementFraction delta 14 *
                              wz2PaperFinalBalancedCoverLoss producer ≤
                            1

structure WZ2PaperFinalGeometricNumericalData
    (sourceLoss stableLoss outputLoss : ℝ)
    (firstLevelCount secondLevelCount : ℕ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  crossing :
    WZ2PaperFinalCrossingScalarAtSmallScales
      sourceLoss stableLoss firstLevelCount secondLevelCount delta₀
  crop :
    WZ2PaperFinalCropScalarAtSmallScales
      sourceLoss outputLoss firstLevelCount secondLevelCount delta₀
  post_balancing : WZ2PaperPostBalancingAtSmallScales delta₀
  final_balancing : WZ2PaperFinalBalancingAtSmallScales delta₀

theorem wz2_paper_final_geometric_numerical_data
    (sourceLoss stableLoss outputLoss : ℝ)
    (hSourcePos : 0 < sourceLoss)
    (hSourceStable : 16 * sourceLoss < stableLoss)
    (hSourceOutput : 16 * sourceLoss < outputLoss)
    (firstLevelCount secondLevelCount : ℕ) :
    Nonempty
      (WZ2PaperFinalGeometricNumericalData
        sourceLoss stableLoss outputLoss
        firstLevelCount secondLevelCount) := by
  rcases
      wz2_paper_final_geometric_crossing_scalar_absorption
        sourceLoss stableLoss hSourcePos hSourceStable
        firstLevelCount secondLevelCount
    with ⟨crossingScale, hCrossingPos, hCrossingOne, hCrossing⟩
  rcases
      wz2_paper_final_geometric_crop_scalar_absorption
        sourceLoss outputLoss hSourcePos hSourceOutput
        firstLevelCount secondLevelCount
    with ⟨cropScale, hCropPos, hCropOne, hCrop⟩
  rcases wz2_paper_final_geometric_post_balancing_loss_absorption with
    ⟨postScale, hPostPos, hPostOne, hPost⟩
  rcases
      wz2_paper_final_geometric_balanced_cover_loss_absorption_from_lines
    with
    ⟨finalScale, hFinalPos, hFinalOne, hFinal⟩
  let delta₀ :=
    min crossingScale (min cropScale (min postScale finalScale))
  refine
    ⟨{
      delta₀ := delta₀
      delta₀_pos :=
        lt_min hCrossingPos
          (lt_min hCropPos (lt_min hPostPos hFinalPos))
      delta₀_le_one := (min_le_left _ _).trans hCrossingOne
      crossing := ?_
      crop := ?_
      post_balancing := ?_
      final_balancing := ?_
    }⟩
  · intro delta rho hdelta hdeltaBound
    exact hCrossing hdelta
      (hdeltaBound.trans (min_le_left _ _))
  · intro delta rho hdelta hdeltaBound
    exact hCrop hdelta <|
      hdeltaBound.trans <| (min_le_right _ _).trans (min_le_left _ _)
  · intro delta rho hdelta hdeltaBound
    exact hPost hdelta <|
      hdeltaBound.trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
  · intro delta rho hdelta hdeltaBound
    exact hFinal hdelta <|
      hdeltaBound.trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_right _ _)

end Kakeya.Assouad

end
