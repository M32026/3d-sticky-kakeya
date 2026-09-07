import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerParentCoarseBounds
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerParentRefinement

/-!
# Final prop-sticky assembly on the owner-parent route

The final selected coarse family is chosen once, then realized by complete
fibers and whole owned cells.  Coarse nearby CWA, balancedness, coarse
density/volume, and both pointwise multiplicity conversions are mechanical.
The only geometric fiber input retained here is the complete public rescaled
output on each final fiber.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace WZ2PaperOwnerParentSelectedData

noncomputable def owner_parent_same_family_prop_sticky
    {delta sigma outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
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
          fine (scales coordinate) ambientConstant)
    (sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled)
    (scaleSeparation : 18 * delta ≤ callerRequested.1)
    (balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation)
    (owner :
      WZ2PaperDirectOwnerPreparationData
        balancing.balanced.finalData.producer)
    (data :
      WZ2PaperOwnerParentSelectedData owner outputConstant)
    (logExponent : ℕ)
    (retentionAbsorption :
      wz2PaperPureRefinementFraction delta logExponent *
          ((((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
              pureWZ2CompleteParentRegularizationLoss
                actualNearby.scaleData.coarse.card coordinateCount *
              sameFamily.retentionConstant) *
            pureWZ2SameFamilyOwnerLoss balancing owner) *
            data.regularizationLoss) ≤
        1)
    (coarseCWAAbsorption :
      outputConstant ≤
        Kakeya.realRpowENN callerRequested.1 (-outputLoss))
    (rhoSmall : callerRequested.1 ≤ 1 / 24)
    (coarseDensityAbsorption :
      Kakeya.realRpowENN callerRequested.1 outputLoss *
            ((55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN callerRequested.1 2) *
            data.selectedPacked.family.enncard *
            (2 ^
              (balancing.balanced.finalData.producer.fiberBand.level + 1) :
                ENNReal) ≤
        data.finalFineShading.mass)
    (coarseVolumeScalar :
      volume data.finalFineShading.union *
            volume
              (wz1PaperGridCube callerRequested.1 (0, 0, 0)) ≤
        Kakeya.realRpowENN callerRequested.1
            (sigma - outputLoss) *
          data.publicBalanced.cellMass)
    (rescaledFiber :
      ∀ parent : Fin data.selectedPacked.family.card,
        Nonempty
          (WZ2PaperPureRescaledFullFiberOutput
            (sigma := sigma) (loss := outputLoss)
            (restrictPaperShading
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                data.selectedFine.family
                (wz2PaperFullFiberIndices
                  data.selectedFine.family
                  data.selectedPacked.family parent))
              data.finalFineShading)
            (data.selectedPacked.family.tube parent)
            (actualNearby.scaleData.delta_pos.trans_le
              callerRequested.2.1)))
    (coarseMultiplicityScalar :
      (1 : ENNReal) ≤
        Kakeya.realRpowENN callerRequested.1
            (2 - sigma - outputLoss) *
          data.selectedPacked.family.enncard)
    (fiberCapUpper :
      ∀ parent : Fin data.selectedPacked.family.card,
        (2 ^
            (balancing.balanced.finalData.producer.fiberBand.level + 1) :
          ENNReal) ≤
          Kakeya.realRpowENN (delta / callerRequested.1)
              (2 - sigma - outputLoss) *
            ((wz2PaperFullFiberIndices
              data.selectedFine.family
              data.selectedPacked.family parent).card : ENNReal)) :
    PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      shading callerRequested logExponent := by
  let finalFine := data.finalFineShading
  let finalCoarse := data.finalCoarseShading
  let selected := data.selectedSource
  have selectedNonempty : selected.family.Nonempty :=
    data.selectedSource_nonempty
  have refinedSubshading :
      ∀ index,
        finalFine.carrier index ⊆
          shading.carrier (selected.embedding index) :=
    data.finalFine_subshading
  have retainedMass :
      wz2PaperPureRefinementFraction delta logExponent *
          shading.mass ≤
        finalFine.mass :=
    data.retained_mass logExponent retentionAbsorption
  have coarsePure :
      WZ2PaperPureCWAAtNearbyScales
        data.selectedPacked.family
        (Kakeya.realRpowENN callerRequested.1 (-outputLoss)) :=
    data.pure_cwa.mono coarseCWAAbsorption ENNReal.ofReal_ne_top
  let coarseExtremal :
      WZ2PaperCroppedIsExtremal
        sigma outputLoss data.selectedPacked.family finalCoarse :=
    {
      delta_pos :=
        actualNearby.scaleData.delta_pos.trans_le
          callerRequested.2.1
      delta_le_one := callerRequested.2.2
      nonempty := data.selected_nonempty
      cwa_nearby_scales := coarsePure
      cubical := data.publicBalanced.coarse_cubical
      dense :=
        data.final_coarse_density
          (Kakeya.realRpowENN callerRequested.1 outputLoss)
          rhoSmall coarseDensityAbsorption
      volume_upper :=
        data.final_coarse_volume_upper
          (Kakeya.realRpowENN callerRequested.1
            (sigma - outputLoss))
          coarseVolumeScalar
    }
  have coarseMultiplicityUpper :
      ∀ point,
        (finalCoarse.pointMultiplicity point : ENNReal) ≤
          Kakeya.realRpowENN callerRequested.1
              (2 - sigma - outputLoss) *
            data.selectedPacked.family.enncard := by
    intro point
    exact data.coarse_pointMultiplicity_le_one point
      |>.trans coarseMultiplicityScalar
  have fiberMultiplicityUpper :
      ∀ parent point,
        (((wz2PaperFullFiberIndices
          data.selectedFine.family
          data.selectedPacked.family parent).filter
          fun source =>
            point ∈ finalFine.carrier source).card :
          ENNReal) ≤
        Kakeya.realRpowENN (delta / callerRequested.1)
            (2 - sigma - outputLoss) *
          ((wz2PaperFullFiberIndices
            data.selectedFine.family
            data.selectedPacked.family parent).card : ENNReal) := by
    intro parent point
    have hMultiplicity :
        (((wz2PaperFullFiberIndices
          data.selectedFine.family
          data.selectedPacked.family parent).filter
          fun source =>
            point ∈ finalFine.carrier source).card : ENNReal) =
          (data.internalCover.toWZ1PaperTubeCover.fiberPointMultiplicity
            finalFine parent point : ENNReal) := by
      unfold WZ1PaperTubeCover.fiberPointMultiplicity
      rw [← data.internalCover.fullFiberIndices_eq parent]
    rw [hMultiplicity]
    exact
      (data.final_fiber_pointMultiplicity_le_cap parent point).trans
        (fiberCapUpper parent)
  exact
    {
      selected := selected
      selected_nonempty := selectedNonempty
      refined := finalFine
      subshading := refinedSubshading
      retained_mass := retainedMass
      refined_cubical :=
        data.balancedPullback.pullback.selectedFine_cubical
      coarse := data.selectedPacked.family
      cover := data.section6Cover
      croppedCoarseShading := finalCoarse
      balanced := data.publicBalanced
      coarse_extremal := coarseExtremal
      rescaledFiber := rescaledFiber
      coarse_multiplicity_upper := coarseMultiplicityUpper
      fiber_multiplicity_upper := fiberMultiplicityUpper
    }

end WZ2PaperOwnerParentSelectedData

end Kakeya.Assouad

end
