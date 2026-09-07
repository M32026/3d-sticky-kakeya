import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerParentStructure
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantOwnerRefinement

/-!
# Global refinement on the same-family owner-parent route

The final fine family is the composition of the merged source selection, the
complete caller pullback, the dominant-owner exactification, and the final
owner-parent pullback.  This module isolates the corresponding subshading and
mass-retention bookkeeping from the final prop-sticky assembly.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private theorem nested_carrier_subset
    {Index0 Index1 Index2 Index3 Index4 : Type*}
    (carrier0 : Index0 → Set Point3)
    (carrier1 : Index1 → Set Point3)
    (carrier2 carrier2Refined : Index2 → Set Point3)
    (carrier3 : Index3 → Set Point3)
    (carrier4 : Index4 → Set Point3)
    (embedding1 : Index1 → Index0)
    (embedding2 : Index2 → Index1)
    (embedding3 : Index3 → Index2)
    (embedding4 : Index4 → Index3)
    (h1 : ∀ index, carrier1 index ⊆ carrier0 (embedding1 index))
    (h2 : ∀ index, carrier2 index ⊆ carrier1 (embedding2 index))
    (h2Refined : ∀ index, carrier2Refined index ⊆ carrier2 index)
    (h3 : ∀ index, carrier3 index ⊆ carrier2Refined (embedding3 index))
    (h4 : ∀ index, carrier4 index ⊆ carrier3 (embedding4 index)) :
    ∀ index,
      carrier4 index ⊆
        carrier0
          (embedding1
            (embedding2
              (embedding3 (embedding4 index)))) := by
  intro index
  exact
    (h4 index).trans <|
      (h3 (embedding4 index)).trans <|
        (h2Refined (embedding3 (embedding4 index))).trans <|
          (h2 (embedding3 (embedding4 index))).trans <|
            h1 (embedding2 (embedding3 (embedding4 index)))

private theorem two_stage_retained_mass
    (fraction firstLoss secondLoss sourceMass middleMass finalMass : ENNReal)
    (sourceToMiddle : sourceMass ≤ firstLoss * middleMass)
    (middleToFinal : middleMass ≤ secondLoss * finalMass)
    (absorption : fraction * (firstLoss * secondLoss) ≤ 1) :
    fraction * sourceMass ≤ finalMass := by
  calc
    fraction * sourceMass ≤
        fraction * (firstLoss * middleMass) := by
      gcongr
    _ ≤
        fraction * (firstLoss * (secondLoss * finalMass)) := by
      gcongr
    _ =
        (fraction * (firstLoss * secondLoss)) * finalMass := by
      ring
    _ ≤ 1 * finalMass := by
      exact mul_le_mul_right' absorption finalMass
    _ = finalMass := by simp

namespace WZ2PaperOwnerParentSelectedData

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant outputConstant : ENNReal}
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
    {owner :
      WZ2PaperDirectOwnerPreparationData
        balancing.balanced.finalData.producer}
    (data : WZ2PaperOwnerParentSelectedData owner outputConstant)

noncomputable def selectedSource :
    Kakeya.Streamlined.TubeSubfamily fine :=
  merged.merged.toTubeSubfamily.comp
    (sameFamily.pullback.selectedFine.comp data.selectedFine)

theorem selectedSource_nonempty :
    data.selectedSource.family.Nonempty := by
  let parent : Fin data.selectedPacked.family.card :=
    ⟨0, data.selected_nonempty⟩
  rcases data.section6Cover.parent_hit parent with ⟨source, _⟩
  exact Fin.pos_iff_nonempty.mpr ⟨source⟩

theorem finalFine_subshading :
    ∀ index,
      data.finalFineShading.carrier index ⊆
        shading.carrier (data.selectedSource.embedding index) := by
  apply
    nested_carrier_subset
      shading.carrier
      merged.mergedShading.carrier
      sameFamily.pullback.selectedFineShading.carrier
      (balancing.balanced.finalData.producer.coarseBand
        |>.selectedFineShading).carrier
      owner.exactified.refined.carrier
      data.finalFineShading.carrier
      merged.merged.toTubeSubfamily.embedding
      sameFamily.pullback.selectedFine.embedding
      owner.exactified.selected.embedding
      data.balancedPullback.pullback.selectedFine.embedding
  · intro index
    rw [merged.mergedShading_eq]
    exact Set.Subset.rfl
  · intro index
    rw [sameFamily.pullback.selectedFineShading_eq]
    exact Set.Subset.rfl
  · exact balancing.finalFine_subshading
  · exact owner.exactified_subshading
  · exact data.balancedPullback.pullback.selectedFine_subshading

theorem source_mass_le_owner :
    shading.mass ≤
      (((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          pureWZ2CompleteParentRegularizationLoss
            actualNearby.scaleData.coarse.card coordinateCount *
          sameFamily.retentionConstant) *
        pureWZ2SameFamilyOwnerLoss balancing owner) *
        owner.exactified.refined.mass := by
  let structuralLoss : ENNReal :=
    (pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
      pureWZ2CompleteParentRegularizationLoss
        actualNearby.scaleData.coarse.card coordinateCount *
      sameFamily.retentionConstant
  let balancingLoss :=
    pureWZ2SameFamilyFixedOriginBalancingLoss balancing.balanced
  let ownerLoss := wz2PaperDominantOwnerLoss owner.exactified
  let finalBalancedFine :=
    balancing.balanced.finalData.producer.coarseBand
      |>.selectedFineShading
  have sourceToBalanced :
      shading.mass ≤
        (structuralLoss * balancingLoss) *
          finalBalancedFine.mass := by
    simpa [structuralLoss, balancingLoss, mul_assoc] using
      balancing.source_mass_retention
  have balancedToOwner :
      finalBalancedFine.mass ≤
        ownerLoss * owner.exactified.refined.mass := by
    calc
      finalBalancedFine.mass =
          owner.exactAdapter.exact.refined.mass := by
        exact congrArg
          Kakeya.Streamlined.Shading.mass
          owner.exactAdapter.exact_refined_eq.symm
      _ ≤ ownerLoss * owner.exactified.refined.mass :=
        wz2_paper_dominant_owner_mass_comparison
          owner.degree owner.dominant owner.exactified
  calc
    shading.mass ≤
        (structuralLoss * balancingLoss) *
          finalBalancedFine.mass :=
      sourceToBalanced
    _ ≤
        (structuralLoss * balancingLoss) *
          (ownerLoss * owner.exactified.refined.mass) := by
      gcongr
    _ =
        (structuralLoss *
          pureWZ2SameFamilyOwnerLoss balancing owner) *
            owner.exactified.refined.mass := by
      simp only [pureWZ2SameFamilyOwnerLoss, balancingLoss, ownerLoss]
      ring
    _ =
        (((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            pureWZ2CompleteParentRegularizationLoss
              actualNearby.scaleData.coarse.card coordinateCount *
            sameFamily.retentionConstant) *
          pureWZ2SameFamilyOwnerLoss balancing owner) *
          owner.exactified.refined.mass := by
      rfl

theorem retained_mass
    (logExponent : ℕ)
    (retentionAbsorption :
      wz2PaperPureRefinementFraction delta logExponent *
          ((((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
              pureWZ2CompleteParentRegularizationLoss
                actualNearby.scaleData.coarse.card coordinateCount *
              sameFamily.retentionConstant) *
            pureWZ2SameFamilyOwnerLoss balancing owner) *
            data.regularizationLoss) ≤
        1) :
    wz2PaperPureRefinementFraction delta logExponent *
        shading.mass ≤
      data.finalFineShading.mass := by
  let baseLoss : ENNReal :=
    ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
        pureWZ2CompleteParentRegularizationLoss
          actualNearby.scaleData.coarse.card coordinateCount *
        sameFamily.retentionConstant) *
      pureWZ2SameFamilyOwnerLoss balancing owner
  have ownerToSelected :
      owner.exactified.refined.mass ≤
        data.regularizationLoss * data.finalFineShading.mass := by
    exact data.retained_selected_mass
  exact
    two_stage_retained_mass
      (wz2PaperPureRefinementFraction delta logExponent)
      baseLoss data.regularizationLoss
      shading.mass owner.exactified.refined.mass
      data.finalFineShading.mass
      (by
        simpa [baseLoss] using
          source_mass_le_owner
            (balancing := balancing) (owner := owner))
      ownerToSelected
      (by simpa [baseLoss, mul_assoc] using retentionAbsorption)

end WZ2PaperOwnerParentSelectedData

end Kakeya.Assouad

end
