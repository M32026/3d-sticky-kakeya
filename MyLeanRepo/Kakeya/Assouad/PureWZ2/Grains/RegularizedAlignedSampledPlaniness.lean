import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.StickyCoarseFiberMassRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RetainedZeroExtensionFinitePlaniness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.AlignedResidueFiniteRefinement

/-! # Aligned sampled planiness on synchronized complete fibers -/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory

/-- The selected complete-fiber restriction and its selected coarse shading
retain the exact point compatibility needed by aligned residue balancing. -/
def regularizedCompleteFiberCompatibleCover
    {delta sigma stickyLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent}
    {outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    {schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sticky.coarse)
        (Kakeya.realRpowENN rho.1 (-stickyLoss))
        outputConstant levelCount}
    (data : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) sticky schedule) :
    PureWZ2CompatibleCoverData data.restriction.restrictedCover
      data.restriction.selectedFineShading
      (restrictPaperShading data.restriction.selectedCoarse
        sticky.croppedCoarseShading) where
  point_compatibility := by
    intro fineIndex coarseIndex hcover point hpoint
    have hcanonical :
        data.restriction.restrictedCover.toPaperTubeCover.parent fineIndex =
          coarseIndex :=
      (data.restriction.restrictedCover.toPaperTubeCover.parent_unique
        fineIndex coarseIndex hcover).symm
    rw [← hcanonical]
    exact data.restriction.point_compatibility sticky.balanced
      fineIndex point hpoint
  coarse_cubical :=
    restrictPaperShading_cubical data.restriction.selectedCoarse
      sticky.balanced.coarse_cubical

/-- Finite planiness on the synchronized complete selected fibers, followed
by aligned residue balancing and honest coarse sampling.  All asymptotic
selection losses remain explicit premises. -/
structure RegularizedAlignedSampledPlaninessData
    {delta rho coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (compatible : PureWZ2CompatibleCoverData cover fineShading coarseShading)
    (hdelta : 0 < delta) (K : ℕ) where
  planiness : BoundedBalancedFinitePlaninessData
    (coefficient := coefficient) fineShading (rho / 4)
  coarseMap : AlignedFiniteCoarsePlaneMapData
    (target := rho) compatible planiness.data hdelta K

/-- Run finite planiness after a quantitative complete-fiber restriction. -/
theorem regularized_aligned_sampled_planiness
    {delta sigma sourceLoss targetLoss densityLoss kappa eta coefficient : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {stickyLoss : ℝ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent}
    {outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    {nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sticky.coarse)
        (Kakeya.realRpowENN rho.1 (-stickyLoss))
        outputConstant levelCount}
    (regularized : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) sticky nearbySchedule)
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss source sourceShading)
    (sourceLine : WZ1PaperIsLineClass source)
    (massLoss : ENNReal)
    (hmassLossPos : 0 < massLoss)
    (hmassLossTop : massLoss ≠ ⊤)
    (hmass : massLoss⁻¹ * sourceShading.mass ≤
      regularized.restriction.selectedFineShading.mass)
    (hsourceTarget : sourceLoss ≤ targetLoss)
    (hslack : massLoss * Kakeya.realRpowENN delta targetLoss ≤
      Kakeya.realRpowENN delta sourceLoss)
    (schedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hsmall : Kakeya.realRpowENN delta targetLoss < 1 / 4)
    (hfixedAbsorb :
      (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * targetLoss))
    (hsparsePackage : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa)
      (extendShading
        (sticky.selected.comp regularized.restriction.selectedFine)
        regularized.restriction.selectedFineShading)
      (Kakeya.realRpowENN delta (2 - sigma + 3 * targetLoss)),
        Nonempty (SparseRelativeBandCVPackage
          (extendShading
            (sticky.selected.comp regularized.restriction.selectedFine)
            regularized.restriction.selectedFineShading) prepared))
    (hdenseIncidence : eta ≤ rho.1 / 4)
    (hsparseIncidence : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa)
      (extendShading
        (sticky.selected.comp regularized.restriction.selectedFine)
        regularized.restriction.selectedFineShading)
      (Kakeya.realRpowENN delta (2 - sigma + 3 * targetLoss)),
      ∀ package : SparseRelativeBandCVPackage
        (extendShading
          (sticky.selected.comp regularized.restriction.selectedFine)
          regularized.restriction.selectedFineShading) prepared,
        package.tau / kappa ≤ rho.1 / 4)
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaPositive : 0 < kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (heta : 0 < eta)
    (hetaHalf : eta ≤ 1 / 2)
    (hcoefficientPositive : 0 < coefficient)
    (hactualSmall : ∀ coordinate, coordinate < 1 →
      ((transfer_cropped_extremal_to_subshading massLoss hmassLossPos
          hmassLossTop sourceExtremal
          (fun ambientIndex point hpoint => by
            by_cases himage : ∃ index,
                (sticky.selected.comp
                  regularized.restriction.selectedFine).embedding index =
                    ambientIndex
            · rcases himage with ⟨index, rfl⟩
              rw [extendShading_carrier_mem] at hpoint
              exact sticky.subshading
                (regularized.restriction.selectedFine.embedding index) <| by
                  rw [regularized.restriction.selectedFineShading_eq] at hpoint
                  exact hpoint
            · rw [extendShading_carrier_empty himage] at hpoint
              exact False.elim hpoint)
          (by rw [extendShading_mass]; exact hmass)
          (Kakeya.Assouad.extendShading_cubical
            (sticky.selected.comp regularized.restriction.selectedFine)
            regularized.restriction.selectedFine_cubical)
          hsourceTarget hslack sourceExtremal.delta_pos
          sourceExtremal.delta_le_one htargetLoss).cwa_nearby_scales.chosenNearby
        (schedule.requested coordinate)).rho < 1 / 8)
    (hparentKappa : ∀ coordinate, coordinate < 1 →
      8 * ((transfer_cropped_extremal_to_subshading massLoss hmassLossPos
          hmassLossTop sourceExtremal
          (fun ambientIndex point hpoint => by
            by_cases himage : ∃ index,
                (sticky.selected.comp
                  regularized.restriction.selectedFine).embedding index =
                    ambientIndex
            · rcases himage with ⟨index, rfl⟩
              rw [extendShading_carrier_mem] at hpoint
              exact sticky.subshading
                (regularized.restriction.selectedFine.embedding index) <| by
                  rw [regularized.restriction.selectedFineShading_eq] at hpoint
                  exact hpoint
            · rw [extendShading_carrier_empty himage] at hpoint
              exact False.elim hpoint)
          (by rw [extendShading_mass]; exact hmass)
          (Kakeya.Assouad.extendShading_cubical
            (sticky.selected.comp regularized.restriction.selectedFine)
            regularized.restriction.selectedFine_cubical)
          hsourceTarget hslack sourceExtremal.delta_pos
          sourceExtremal.delta_le_one htargetLoss).cwa_nearby_scales.chosenNearby
        (schedule.requested coordinate)).rho < kappa)
    (K : ℕ) (hK : 0 < K)
    (hrhoAligned : rho.1 = (K : ℝ) * delta)
    (hcoefficientNonnegative : 0 ≤ coefficient)
    (hcoefficient : coefficient ≤ 1 / 5)
    (hbudget : rho.1 / 4 + coefficient * (rho.1 * Real.sqrt 3) +
      rho.1 / 2 ≤ rho.1) :
    Nonempty (RegularizedAlignedSampledPlaninessData
      (coefficient := coefficient)
      (regularizedCompleteFiberCompatibleCover regularized)
      sourceExtremal.delta_pos K) := by
  rcases retained_zero_extension_finite_planiness
      (sticky.selected.comp regularized.restriction.selectedFine)
      sourceExtremal sourceLine (fun index point hpoint => by
        rw [regularized.restriction.selectedFineShading_eq] at hpoint
        exact sticky.subshading
          (regularized.restriction.selectedFine.embedding index) hpoint)
      regularized.restriction.selectedFine_cubical massLoss hmassLossPos
      hmassLossTop hmass hsourceTarget hslack schedule hdensityLoss
      htargetLoss hdeltaSmall hsmall hfixedAbsorb hsparsePackage
      hdenseIncidence hsparseIncidence hkappaNonnegative hkappaPositive
      hkappaHalf heta hetaHalf hcoefficientPositive hactualSmall
      hparentKappa with ⟨planiness⟩
  rcases aligned_finite_coarse_plane_map
      (regularizedCompleteFiberCompatibleCover regularized) planiness.data
      sourceExtremal.delta_pos sticky.coarse_extremal.delta_pos K hK
      hrhoAligned hcoefficientNonnegative hcoefficient (by
        calc
          planiness.data.incidence + coefficient * (rho.1 * Real.sqrt 3) +
              rho.1 / 2 ≤
            rho.1 / 4 + coefficient * (rho.1 * Real.sqrt 3) +
              rho.1 / 2 := by linarith [planiness.incidence_le]
          _ ≤ rho.1 := hbudget) with ⟨coarseMap⟩
  exact ⟨{ planiness := planiness, coarseMap := coarseMap }⟩

/-- Cropped extremality on the actual sampled coarse shading, without a
second tube-family regularization.  The only density premise is the explicit
aligned source-to-sampled loss from the preceding construction. -/
theorem RegularizedAlignedSampledPlaninessData.sampled_extremal
    {delta sigma stickyLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent}
    {outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    {nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sticky.coarse)
        (Kakeya.realRpowENN rho.1 (-stickyLoss))
        outputConstant levelCount}
    (regularized : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) sticky nearbySchedule)
    {coefficient : ℝ} {K : ℕ}
    (hdelta : 0 < delta)
    (data : RegularizedAlignedSampledPlaninessData
      (coefficient := coefficient)
      (regularizedCompleteFiberCompatibleCover regularized)
      hdelta K)
    (fiberCap : ENNReal)
    (hfiberCapTop : fiberCap ≠ ⊤)
    (hfiberCap : ∀ parent point,
      (regularized.restriction.restrictedCover.toPaperTubeCover
          |>.fiberPointMultiplicity
            data.coarseMap.residue.selected parent point : ENNReal) ≤
        fiberCap)
    (hloss : stickyLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hnearby : outputConstant ≤
      Kakeya.realRpowENN rho.1 (-outputLoss))
    (hbodyBudget : data.coarseMap.selectionLoss fiberCap *
      (Kakeya.realRpowENN rho.1 outputLoss *
        (wz1PaperBodyFamily
          regularized.restriction.selectedCoarse.family).mass) ≤
      regularized.restriction.selectedFineShading.mass) :
    WZ2PaperCroppedIsExtremal sigma outputLoss
      regularized.restriction.selectedCoarse.family
      data.coarseMap.sampled.selected := by
  have hrho : 0 < rho.1 := sticky.coarse_extremal.delta_pos
  have hrhoOne : rho.1 ≤ 1 := sticky.coarse_extremal.delta_le_one
  have houtputFinite : WZ2PaperFiniteErrorConstant
      (Kakeya.realRpowENN rho.1 (-outputLoss)) := by
    have hone : (1 : ENNReal) ≤
        Kakeya.realRpowENN rho.1 (-outputLoss) := by
      have hreal : 1 ≤ Real.rpow rho.1 (-outputLoss) := by
        have hzero : Real.rpow rho.1 0 ≤
            Real.rpow rho.1 (-outputLoss) :=
          Real.rpow_le_rpow_of_exponent_ge hrho hrhoOne (by linarith)
        simpa using hzero
      simpa [Kakeya.realRpowENN] using ENNReal.ofReal_mono hreal
    exact ⟨hone, by simp [Kakeya.realRpowENN]⟩
  have hcwaNearby : WZ2PaperPureCWAAtNearbyScales
      regularized.restriction.selectedCoarse.family
      (Kakeya.realRpowENN rho.1 (-outputLoss)) := by
    rw [regularized.restriction_coarse_eq]
    exact weaken_cwa_nearby_scales regularized.regularized.pure_cwa_nearby
      hnearby houtputFinite
  have hnonempty :
      regularized.restriction.selectedCoarse.family.Nonempty := by
    rw [regularized.restriction_coarse_eq]
    exact regularized.regularized.selected_nonempty
  have hsubSelected : PaperIsSubshading data.coarseMap.sampled.selected
      (restrictPaperShading regularized.restriction.selectedCoarse
        sticky.croppedCoarseShading) := fun parent =>
    (data.coarseMap.sampled.subshading parent).trans <|
      (data.coarseMap.sourceWitness.subshading parent).trans
        (data.coarseMap.residue.coarse_subshading parent)
  have hunion : data.coarseMap.sampled.selected.union ⊆
      sticky.croppedCoarseShading.union := by
    rintro point ⟨parent, hpoint⟩
    exact ⟨regularized.restriction.selectedCoarse.embedding parent,
      hsubSelected parent hpoint⟩
  have hvolume : volume data.coarseMap.sampled.selected.union ≤
      Kakeya.realRpowENN rho.1 (sigma - outputLoss) := by
    calc
      volume data.coarseMap.sampled.selected.union ≤
          volume sticky.croppedCoarseShading.union := measure_mono hunion
      _ ≤ Kakeya.realRpowENN rho.1 (sigma - stickyLoss) :=
        sticky.coarse_extremal.volume_upper
      _ ≤ Kakeya.realRpowENN rho.1 (sigma - outputLoss) := by
        apply ENNReal.ofReal_mono
        exact Real.rpow_le_rpow_of_exponent_ge hrho hrhoOne (by linarith)
  have hfineSampled : regularized.restriction.selectedFineShading.mass ≤
      data.coarseMap.selectionLoss fiberCap *
        data.coarseMap.sampled.selected.mass :=
    data.coarseMap.fine_to_sampled_mass_normalized fiberCap hfiberCap
  have hcostPos := data.coarseMap.selectionLoss_pos fiberCap
  have hcostTop := data.coarseMap.selectionLoss_ne_top
    fiberCap hfiberCapTop
  have hdense : Kakeya.realRpowENN rho.1 outputLoss *
      (wz1PaperBodyFamily
        regularized.restriction.selectedCoarse.family).mass ≤
      data.coarseMap.sampled.selected.mass := by
    have hscaled : data.coarseMap.selectionLoss fiberCap *
        (Kakeya.realRpowENN rho.1 outputLoss *
          (wz1PaperBodyFamily
            regularized.restriction.selectedCoarse.family).mass) ≤
        data.coarseMap.selectionLoss fiberCap *
          data.coarseMap.sampled.selected.mass :=
      hbodyBudget.trans hfineSampled
    exact (ENNReal.mul_le_mul_iff_right hcostPos.ne' hcostTop).mp hscaled
  exact {
    delta_pos := hrho
    delta_le_one := hrhoOne
    nonempty := hnonempty
    cwa_nearby_scales := hcwaNearby
    cubical := data.coarseMap.sampled.cubical
    dense := hdense
    volume_upper := hvolume
  }

end Kakeya.Assouad.PureWZ2

end
