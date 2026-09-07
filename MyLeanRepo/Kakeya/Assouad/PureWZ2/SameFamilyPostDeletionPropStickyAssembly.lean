import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyPostDeletionCoarseDensity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyPostDeletionCoarseCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyPostDeletionCoarseVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDirectPositiveHalfMass
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalMultiplicityComparison

/-!
# Final prop-sticky assembly after positive parent deletion

The post-deletion family is the first configuration on the same-family route
for which every coarse parent has positive shaded mass.  This adapter keeps
that exact fine family, coarse family, shading, and parent map throughout.

The remaining mathematical inputs are:

* absorption of the restricted coarse pure-CWA constant;
* coarse density and volume upper bounds;
* one public rescaled output on every final complete strict fiber;
* scalar upper bounds for the two dyadic multiplicity caps.

The global refinement, final balanced cover, and pointwise coarse/fiber
multiplicity bounds are then mechanical consequences of the closed
post-deletion package.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2SameFamilyPositiveParentDeletionData

noncomputable def post_deletion_same_family_prop_sticky
    {delta sigma outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {support : PureWZ2PositiveCallerSupportData quotient}
    {coordinateCount : ℕ}
    {regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount}
    {merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized}
    {scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    {sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled}
    {scaleSeparation : 18 * delta ≤ callerRequested.1}
    {balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation}
    {deletionExponent : ℕ}
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent)
    (degreeConstant : ENNReal)
    (degreeConstant_ne_top : degreeConstant ≠ ⊤)
    (degreeUniform :
      data.PostDeletionCoarseClassDegreeUniform degreeConstant)
    (logExponent : ℕ)
    (retentionAbsorption :
      wz2PaperPureRefinementFraction delta logExponent *
          (2 *
            (((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
                pureWZ2CompleteParentRegularizationLoss
                  actualNearby.scaleData.coarse.card coordinateCount *
                sameFamily.retentionConstant) *
              pureWZ2SameFamilyFixedOriginBalancingLoss
                balancing.balanced)) ≤
        1)
    (coarseCWAAbsorption :
      postDeletionCoarseRestrictionConstant
          coarseConstant degreeConstant
          (pureWZ2SameFamilyFixedOriginBalancingLoss
            balancing.balanced) ≤
        Kakeya.realRpowENN callerRequested.1 (-outputLoss))
    (rhoSmall : callerRequested.1 ≤ 1 / 24)
    (coarseDensityAbsorption :
      Kakeya.realRpowENN callerRequested.1 outputLoss *
            ((55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN callerRequested.1 2) *
            data.selectedCoarse.family.enncard *
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
      ∀ parent : Fin data.selectedCoarse.family.card,
        Nonempty
          (WZ2PaperPureRescaledFullFiberOutput
            (sigma := sigma) (loss := outputLoss)
            (restrictPaperShading
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                data.selectedFine.family
                (wz2PaperFullFiberIndices
                  data.selectedFine.family
                  data.selectedCoarse.family parent))
              data.finalFineShading)
            (data.selectedCoarse.family.tube parent)
            (actualNearby.scaleData.delta_pos.trans_le
              callerRequested.2.1)))
    (coarseCapUpper :
      (2 ^
          (balancing.balanced.finalData.producer.coarseBand.level + 1) :
        ENNReal) ≤
        Kakeya.realRpowENN callerRequested.1
            (2 - sigma - outputLoss) *
          data.selectedCoarse.family.enncard)
    (fiberCapUpper :
      ∀ parent : Fin data.selectedCoarse.family.card,
        (2 ^
            (balancing.balanced.finalData.producer.fiberBand.level + 1) :
          ENNReal) ≤
          Kakeya.realRpowENN (delta / callerRequested.1)
              (2 - sigma - outputLoss) *
            ((wz2PaperFullFiberIndices
              data.selectedFine.family
              data.selectedCoarse.family parent).card : ENNReal)) :
    PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      shading callerRequested logExponent := by
  let finalFine := data.finalFineShading
  let finalCoarse := data.finalCoarseShading
  let selected :=
    merged.merged.toTubeSubfamily.comp
      (sameFamily.pullback.selectedFine.comp data.selectedFine)
  have selectedNonempty : selected.family.Nonempty := by
    have coarseNonempty : data.selectedCoarse.family.Nonempty := by
      change
        0 <
          (data.post.postDeletion.deletion.deletion.retainedParents).card
      exact
        data.post.postDeletion.deletion.deletion
          |>.retainedParents_nonempty.card_pos
    let parent : Fin data.selectedCoarse.family.card :=
      ⟨0, coarseNonempty⟩
    rcases data.section6Cover.parent_hit parent with ⟨source, _⟩
    exact Fin.pos_iff_nonempty.mpr ⟨source⟩
  have pullbackSubshading :
      ∀ index,
        sameFamily.pullback.selectedFineShading.carrier index ⊆
          shading.carrier
            ((merged.merged.toTubeSubfamily.comp
              sameFamily.pullback.selectedFine).embedding index) := by
    intro index
    rw [sameFamily.pullback.selectedFineShading_eq,
      merged.mergedShading_eq]
    exact Set.Subset.rfl
  have refinedSubshading :
      ∀ index,
        finalFine.carrier index ⊆
          shading.carrier (selected.embedding index) := by
    intro index
    exact
      (data.post.postDeletion.deletion.final_subshading index).trans <|
        (balancing.finalFine_subshading
          (data.selectedFine.embedding index)).trans <|
            pullbackSubshading (data.selectedFine.embedding index)
  have retainedMass :
      wz2PaperPureRefinementFraction delta logExponent *
          shading.mass ≤
        finalFine.mass := by
    let baseLoss : ENNReal :=
      ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          pureWZ2CompleteParentRegularizationLoss
            actualNearby.scaleData.coarse.card coordinateCount *
          sameFamily.retentionConstant) *
        pureWZ2SameFamilyFixedOriginBalancingLoss balancing.balanced
    calc
      wz2PaperPureRefinementFraction delta logExponent *
            shading.mass ≤
          wz2PaperPureRefinementFraction delta logExponent *
            (baseLoss *
              (balancing.balanced.finalData.producer.coarseBand
                |>.selectedFineShading).mass) := by
        gcongr
        simpa [baseLoss] using balancing.source_mass_retention
      _ ≤
          wz2PaperPureRefinementFraction delta logExponent *
            (baseLoss * (2 * finalFine.mass)) := by
        gcongr
        change
          (balancing.balanced.finalData.producer.coarseBand
              |>.selectedFineShading).mass ≤
            2 *
              (data.post.postDeletion.deletion.restriction
                |>.selectedFineShading).mass
        exact wz2_paper_direct_positive_half_mass data.post
      _ =
          (wz2PaperPureRefinementFraction delta logExponent *
            (2 * baseLoss)) * finalFine.mass := by
        ring
      _ ≤ 1 * finalFine.mass := by
        exact
          mul_le_mul_right'
            (by simpa [baseLoss] using retentionAbsorption)
            finalFine.mass
      _ = finalFine.mass := by simp
  have coarseNonempty : data.selectedCoarse.family.Nonempty := by
    change
      0 <
        (data.post.postDeletion.deletion.deletion.retainedParents).card
    exact
      data.post.postDeletion.deletion.deletion
        |>.retainedParents_nonempty.card_pos
  have coarsePure :
      WZ2PaperPureCWAAtNearbyScales
        data.selectedCoarse.family
        (Kakeya.realRpowENN callerRequested.1 (-outputLoss)) :=
    (data.post_deletion_coarse_pure_cwa
      degreeConstant degreeConstant_ne_top degreeUniform).mono
        coarseCWAAbsorption (by
          exact ENNReal.ofReal_ne_top)
  let coarseExtremal :
      WZ2PaperCroppedIsExtremal
        sigma outputLoss data.selectedCoarse.family finalCoarse :=
    {
      delta_pos :=
        actualNearby.scaleData.delta_pos.trans_le
          callerRequested.2.1
      delta_le_one := callerRequested.2.2
      nonempty := coarseNonempty
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
            data.selectedCoarse.family.enncard := by
    intro point
    by_cases hpoint : point ∈ finalCoarse.union
    · exact
        (data.post.bands.coarse_band point hpoint).2.le.trans
          coarseCapUpper
    · have hzero : finalCoarse.pointMultiplicity point = 0 := by
        simp [Kakeya.Streamlined.Shading.pointMultiplicity,
          show ∀ index, point ∉ finalCoarse.carrier index by
            intro index hindex
            exact hpoint ⟨index, hindex⟩]
      rw [hzero]
      simp
  have fiberMultiplicityUpper :
      ∀ parent point,
        (((wz2PaperFullFiberIndices
          data.selectedFine.family
          data.selectedCoarse.family parent).filter
          fun source =>
            point ∈ finalFine.carrier source).card :
          ENNReal) ≤
        Kakeya.realRpowENN (delta / callerRequested.1)
            (2 - sigma - outputLoss) *
          ((wz2PaperFullFiberIndices
            data.selectedFine.family
            data.selectedCoarse.family parent).card : ENNReal) := by
    intro parent point
    let fiberShading :=
      restrictPaperShading
        (data.internalCover.fullFiberSubfamily parent) finalFine
    have hMultiplicity :
        (((wz2PaperFullFiberIndices
          data.selectedFine.family
          data.selectedCoarse.family parent).filter
          fun source =>
            point ∈ finalFine.carrier source).card : ENNReal) =
          (fiberShading.pointMultiplicity point : ENNReal) := by
      have hEq :=
        data.internalCover.restrict_fullFiber_pointMultiplicity_eq
          finalFine parent point
      rw [hEq]
      unfold WZ1PaperTubeCover.fiberPointMultiplicity
      rw [← data.internalCover.fullFiberIndices_eq parent]
    rw [hMultiplicity]
    calc
      (fiberShading.pointMultiplicity point : ENNReal) ≤
          (2 ^
            (balancing.balanced.finalData.producer.fiberBand.level + 1) :
              ENNReal) := by
        by_cases hpoint : point ∈ fiberShading.union
        · exact (data.post.bands.fiber_band parent point hpoint).2.le
        · have hzero : fiberShading.pointMultiplicity point = 0 := by
            simp [Kakeya.Streamlined.Shading.pointMultiplicity,
              show ∀ index, point ∉ fiberShading.carrier index by
                intro index hindex
                exact hpoint ⟨index, hindex⟩]
          rw [hzero]
          simp
      _ ≤
          Kakeya.realRpowENN (delta / callerRequested.1)
              (2 - sigma - outputLoss) *
            ((wz2PaperFullFiberIndices
              data.selectedFine.family
              data.selectedCoarse.family parent).card : ENNReal) :=
        fiberCapUpper parent
  exact
    {
      selected := selected
      selected_nonempty := selectedNonempty
      refined := finalFine
      subshading := refinedSubshading
      retained_mass := retainedMass
      refined_cubical :=
        data.post.postDeletion.deletion.restriction.selectedFine_cubical
      coarse := data.selectedCoarse.family
      cover := data.section6Cover
      croppedCoarseShading := finalCoarse
      balanced := data.publicBalanced
      coarse_extremal := coarseExtremal
      rescaledFiber := rescaledFiber
      coarse_multiplicity_upper := coarseMultiplicityUpper
      fiber_multiplicity_upper := fiberMultiplicityUpper
    }

end PureWZ2SameFamilyPositiveParentDeletionData

end Kakeya.Assouad

end
