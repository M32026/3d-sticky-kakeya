import MyLeanRepo.Kakeya.Assouad.PureWZ2.GenericOwnerPropSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerParentLeaves

/-!
# Universal same-family owner assembly

This module closes the family, shading, and provenance wiring from a frozen
cropped critical normalization through the actual nearby-scale witnesses and
the same-family owner-parent selection.  The only remaining input is one
package of scalar absorptions and critical rescaled-fiber witnesses.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace WZ2PaperOwnerParentSelectedData

/--
Forget the caller-specific construction fields of an owner-parent selection.
The selected families, balanced pullback, mass band, and pure CWA certificate
are unchanged.
-/
noncomputable def toGenericOwnerSelectedData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) fineShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover fineShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover fineShading coarseCells availableFineCells
        balancing coarseData}
    {owner : WZ2PaperDirectOwnerPreparationData producer}
    {outputConstant : ENNReal}
    (data : WZ2PaperOwnerParentSelectedData owner outputConstant) :
    PureWZ2GenericOwnerSelectedData owner outputConstant where
  selectedPacked := data.selectedPacked
  selected_nonempty := data.selected_nonempty
  regularizationLoss := data.regularizationLoss
  regularizationLoss_ne_top := data.regularizationLoss_ne_top
  selectedFiberMassLevel := data.selectedFiberMassLevel
  selectedFiberMassLevel_pos := data.selectedFiberMassLevel_pos
  selectedFiberMassLevel_ne_top := data.selectedFiberMassLevel_ne_top
  balancedPullback := data.balancedPullback
  retained_selected_mass := data.retained_selected_mass
  selected_fiber_mass_band := data.selected_fiber_mass_band
  pure_cwa := data.pure_cwa

/--
The genuine quantitative boundary of the universal owner assembly.

All family selections, complete-fiber pullbacks, balanced shadings, and source
embeddings are already fixed by the dependent parameters.  The first five
fields are scalar absorptions.  `final_multiplicity` is the existing critical
package that simultaneously produces the public rescaled fibers and H5--H6.
-/
structure SameFamilyOwnerUniversalWitness
    {delta sigma sourceLoss normalizationLoss outputLoss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent)
    {ambientConstant fiberConstant coarseConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        normalized.croppedFamily actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested normalized.croppedRefined)
    (support : PureWZ2PositiveCallerSupportData quotient)
    (coordinateCount : ℕ)
    (regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount)
    (merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized)
    (scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          normalized.croppedFamily
          (scales coordinate) ambientConstant)
    (sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled)
    (scaleSeparation : 18 * delta ≤ callerRequested.1)
    (fixedBalancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation)
    (owner :
      WZ2PaperDirectOwnerPreparationData
        fixedBalancing.balanced.finalData.producer)
    (data :
      WZ2PaperOwnerParentSelectedData owner outputConstant)
    (logExponent : ℕ)
    (floorLoss strongLoss : ℝ) where
  retention_absorption :
    wz2PaperPureRefinementFraction delta logExponent *
        ((((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            pureWZ2CompleteParentRegularizationLoss
              actualNearby.scaleData.coarse.card coordinateCount *
            sameFamily.retentionConstant) *
          pureWZ2SameFamilyOwnerLoss fixedBalancing owner) *
          data.regularizationLoss) ≤
      1
  coarse_cwa_absorption :
    outputConstant ≤
      Kakeya.realRpowENN callerRequested.1 (-outputLoss)
  rho_small : callerRequested.1 ≤ 1 / 24
  coarse_density_absorption :
    Kakeya.realRpowENN callerRequested.1 outputLoss *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN callerRequested.1 2) *
          data.selectedPacked.family.enncard *
          (2 ^
            (fixedBalancing.balanced.finalData.producer.fiberBand.level + 1) :
              ENNReal) ≤
      data.finalFineShading.mass
  coarse_volume_scalar :
    volume data.finalFineShading.union *
          volume
            (wz1PaperGridCube callerRequested.1 (0, 0, 0)) ≤
      Kakeya.realRpowENN callerRequested.1
          (sigma - outputLoss) *
        data.publicBalanced.cellMass
  final_multiplicity :
    PureWZ2GenericOwnerSelectedData.FinalMultiplicityInputs
      (sigma := sigma) (floorLoss := floorLoss)
      (strongLoss := strongLoss) (outputLoss := outputLoss)
      data.toGenericOwnerSelectedData

/--
Assemble the frozen `PureWZ2PropStickyData` from a normalized source, actual
nearby-scale witnesses, one same-family owner selection, and the concentrated
quantitative witness above.
-/
noncomputable def sameFamilyOwnerUniversalData
    {delta sigma sourceLoss normalizationLoss outputLoss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent)
    {ambientConstant fiberConstant coarseConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        normalized.croppedFamily actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested normalized.croppedRefined)
    (support : PureWZ2PositiveCallerSupportData quotient)
    (coordinateCount : ℕ)
    (regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount)
    (merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized)
    (scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          normalized.croppedFamily
          (scales coordinate) ambientConstant)
    (sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled)
    (scaleSeparation : 18 * delta ≤ callerRequested.1)
    (fixedBalancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation)
    (owner :
      WZ2PaperDirectOwnerPreparationData
        fixedBalancing.balanced.finalData.producer)
    (data :
      WZ2PaperOwnerParentSelectedData owner outputConstant)
    (logExponent : ℕ)
    {floorLoss strongLoss : ℝ}
    (witness :
      SameFamilyOwnerUniversalWitness
        (outputLoss := outputLoss)
        normalized actualNearby quotient support coordinateCount
        regularized merged scales scheduled sameFamily scaleSeparation
        fixedBalancing owner data logExponent floorLoss strongLoss) :
    PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      normalized.croppedRefined callerRequested logExponent := by
  let generic := data.toGenericOwnerSelectedData
  let geometric :
      PureWZ2GenericOwnerSelectedData.PropStickyGeometricLeaves
        (sigma := sigma) (outputLoss := outputLoss)
        (source := normalized.croppedFamily)
        (sourceShading := normalized.croppedRefined)
        generic logExponent :=
    {
      sourceEmbedding := data.selectedSource.embedding
      source_tube_eq := data.selectedSource.tube_eq
      source_subshading := data.finalFine_subshading
      source_nonempty := data.selectedSource_nonempty
      retained_mass :=
        data.retained_mass logExponent witness.retention_absorption
      final_fine_cubical :=
        data.balancedPullback.pullback.selectedFine_cubical
      fine_line :=
        sameFamily.pullback.section6Cover.fine_line_class
      coarse_line :=
        sameFamily.pullback.section6Cover.coarse_line_class
      coarse_distinct :=
        sameFamily.pullback.section6Cover.coarse_essentially_distinct
      delta_le_rho := callerRequested.2.1
      rho_le_one := callerRequested.2.2
      coarse_pure :=
        generic.pure_cwa.mono
          witness.coarse_cwa_absorption ENNReal.ofReal_ne_top
      coarse_density :=
        data.final_coarse_density
          (Kakeya.realRpowENN callerRequested.1 outputLoss)
          witness.rho_small witness.coarse_density_absorption
      coarse_volume :=
        data.final_coarse_volume_upper
          (Kakeya.realRpowENN callerRequested.1
            (sigma - outputLoss))
          witness.coarse_volume_scalar
    }
  let leaves :=
    PureWZ2GenericOwnerSelectedData.PropStickyGeometricLeaves.withFinalMultiplicity
      (data := generic) geometric witness.final_multiplicity
  exact leaves.assemble

variable
    {delta sigma sourceLoss normalizationLoss outputLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {ambientConstant fiberConstant coarseConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby : WZ2PaperPureNearbyScaleCoverData
      normalized.croppedFamily actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {quotient : PureWZ2ParentQuotientNetSelectionData
      actualNearby callerRequested normalized.croppedRefined}
    {support : PureWZ2PositiveCallerSupportData quotient}
    {coordinateCount : ℕ}
    {regularized : PureWZ2AllPositiveCallerRegularizationData
      (outputConstant := fiberConstant)
      actualNearby quotient support coordinateCount}
    {merged : PureWZ2MergedCallerClassRegularizationData
      actualNearby quotient support coordinateCount regularized}
    {scales : Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled : ∀ coordinate, WZ2PaperPureNearbyScaleCoverData
      normalized.croppedFamily (scales coordinate) ambientConstant}
    {sameFamily : PureWZ2SameFamilyCallerNearbyAssemblyData
      (coarseConstant := coarseConstant)
      actualNearby quotient support coordinateCount regularized merged
      scales scheduled}
    {scaleSeparation : 18 * delta ≤ callerRequested.1}
    {fixedBalancing : PureWZ2SameFamilyFixedOriginBalancingData
      actualNearby quotient support coordinateCount regularized merged
      scales scheduled sameFamily scaleSeparation}
    {owner : WZ2PaperDirectOwnerPreparationData
      fixedBalancing.balanced.finalData.producer}
    {data : WZ2PaperOwnerParentSelectedData owner outputConstant}
    {logExponent : ℕ}
    {floorLoss strongLoss : ℝ}
    {witness : SameFamilyOwnerUniversalWitness
      (outputLoss := outputLoss) normalized actualNearby quotient support
      coordinateCount regularized merged scales scheduled sameFamily
      scaleSeparation fixedBalancing owner data logExponent floorLoss strongLoss}

@[simp] theorem sameFamilyOwnerUniversalData_selected :
    (sameFamilyOwnerUniversalData normalized actualNearby quotient support
      coordinateCount regularized merged scales scheduled sameFamily
      scaleSeparation fixedBalancing owner data logExponent witness).selected =
      data.selectedSource := rfl

@[simp] theorem sameFamilyOwnerUniversalData_refined :
    (sameFamilyOwnerUniversalData normalized actualNearby quotient support
      coordinateCount regularized merged scales scheduled sameFamily
      scaleSeparation fixedBalancing owner data logExponent witness).refined =
      data.finalFineShading := rfl

@[simp] theorem sameFamilyOwnerUniversalData_coarse :
    (sameFamilyOwnerUniversalData normalized actualNearby quotient support
      coordinateCount regularized merged scales scheduled sameFamily
      scaleSeparation fixedBalancing owner data logExponent witness).coarse =
      data.selectedPacked.family := rfl

@[simp] theorem sameFamilyOwnerUniversalData_croppedCoarseShading :
    (sameFamilyOwnerUniversalData normalized actualNearby quotient support
      coordinateCount regularized merged scales scheduled sameFamily
      scaleSeparation fixedBalancing owner data logExponent witness).croppedCoarseShading =
      data.finalCoarseShading := rfl

@[simp] theorem sameFamilyOwnerUniversalData_balanced :
    (sameFamilyOwnerUniversalData normalized actualNearby quotient support
      coordinateCount regularized merged scales scheduled sameFamily
      scaleSeparation fixedBalancing owner data logExponent witness).balanced =
      data.toGenericOwnerSelectedData.publicBalanced
        sameFamily.pullback.section6Cover.fine_line_class
        sameFamily.pullback.section6Cover.coarse_line_class
        sameFamily.pullback.section6Cover.coarse_essentially_distinct := rfl

/-- The deterministic universal owner assembly supplies the original existential API. -/
theorem sameFamilyOwnerUniversalAssembly
    {delta sigma sourceLoss normalizationLoss outputLoss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent)
    {ambientConstant fiberConstant coarseConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        normalized.croppedFamily actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested normalized.croppedRefined)
    (support : PureWZ2PositiveCallerSupportData quotient)
    (coordinateCount : ℕ)
    (regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount)
    (merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized)
    (scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          normalized.croppedFamily
          (scales coordinate) ambientConstant)
    (sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled)
    (scaleSeparation : 18 * delta ≤ callerRequested.1)
    (fixedBalancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation)
    (owner :
      WZ2PaperDirectOwnerPreparationData
        fixedBalancing.balanced.finalData.producer)
    (data :
      WZ2PaperOwnerParentSelectedData owner outputConstant)
    (logExponent : ℕ)
    {floorLoss strongLoss : ℝ}
    (witness :
      SameFamilyOwnerUniversalWitness
        (outputLoss := outputLoss)
        normalized actualNearby quotient support coordinateCount
        regularized merged scales scheduled sameFamily scaleSeparation
        fixedBalancing owner data logExponent floorLoss strongLoss) :
    Nonempty
      (PureWZ2PropStickyData
        (sigma := sigma) (outputLoss := outputLoss)
        normalized.croppedRefined callerRequested logExponent) :=
  ⟨sameFamilyOwnerUniversalData
    normalized actualNearby quotient support coordinateCount regularized merged
    scales scheduled sameFamily scaleSeparation fixedBalancing owner data
    logExponent witness⟩

end WZ2PaperOwnerParentSelectedData

end Kakeya.Assouad

end
