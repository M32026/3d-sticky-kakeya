import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPreparedSelectedPostDeletionStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementComposition

/-!
# Total paper refinement on the corrected selected-parent mainline

Compose the five actual source selections:

1. caller preparation;
2. merged one-parent structural refinements;
3. coarse-parent regularization and complete-fiber pullback;
4. global whole-cell balancing and multiplicity bands;
5. final `largeMass` deletion.

The fourth stage exposes its total retained-mass exponent explicitly; it is
not confused with the smaller internal exponent of the final balanced-cover
producer.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperPreparedSelectedTotalRefinementData
    {delta sourceLoss stableLoss sigma floorLoss strongLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    {critical :
      WZ2PaperCriticalFloorSelectionData
        sigma floorLoss strongLoss}
    {structural :
      WZ2PaperPreparedParentwiseStructuralProducerData
        (outputLoss := outputLoss) prepared critical}
    {ambientConstant outputConstant normalizationWeight weightUpper :
      ENNReal}
    {levelCount parentExponent : ℕ}
    {regularization :
      WZ2PaperPreparedCoarseParentRegularizationData
        prepared critical structural
        ambientConstant outputConstant normalizationWeight weightUpper
        levelCount}
    {pullback :
      WZ2PaperPreparedCoarseParentPullbackData
        regularization parentExponent}
    {selectedRebalancing :
      WZ2PaperPreparedSelectedRebalancingData pullback}
    {finalLogExponent : ℕ}
    {selectedFinal :
      WZ2PaperPreparedSelectedFinalData
        selectedRebalancing finalLogExponent}
    {massLower volumeUpper threshold : ENNReal}
    {selectedComparison :
      WZ2PaperPreparedSelectedComparisonData
        selectedFinal massLower volumeUpper}
    {deletionExponent : ℕ}
    (post :
      WZ2PaperPreparedSelectedPostDeletionData
        selectedComparison threshold deletionExponent)
    (globalBalancingExponent : ℕ) where
  global_mass_retention :
    wz1PaperRefinementFraction delta globalBalancingExponent *
          pullback.selectedFineShading.mass ≤
      selectedFinal.finalData.producer.coarseBand.selectedFineShading.mass
  preDeletionRefinement :
    WZ1PaperRefinement shading
      (((preparationExponent + 4) + parentExponent) +
        globalBalancingExponent)
  preDeletion_selected_family_eq :
    preDeletionRefinement.selected.family =
      pullback.selectedFine.family
  preDeletion_refined_heq :
    HEq preDeletionRefinement.refined
      selectedFinal.finalData.producer.coarseBand.selectedFineShading
  refinement :
    WZ1PaperRefinement shading
      ((((preparationExponent + 4) + parentExponent) +
        globalBalancingExponent) + deletionExponent)
  selected_family_eq :
    refinement.selected.family =
      post.deletion.restriction.selected.family
  refined_heq :
    HEq refinement.refined
      post.deletion.restriction.selectedFineShading

theorem wz2_paper_prepared_selected_total_refinement
    {delta sourceLoss stableLoss sigma floorLoss strongLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    {critical :
      WZ2PaperCriticalFloorSelectionData
        sigma floorLoss strongLoss}
    {structural :
      WZ2PaperPreparedParentwiseStructuralProducerData
        (outputLoss := outputLoss) prepared critical}
    {ambientConstant outputConstant normalizationWeight weightUpper :
      ENNReal}
    {levelCount parentExponent : ℕ}
    {regularization :
      WZ2PaperPreparedCoarseParentRegularizationData
        prepared critical structural
        ambientConstant outputConstant normalizationWeight weightUpper
        levelCount}
    {pullback :
      WZ2PaperPreparedCoarseParentPullbackData
        regularization parentExponent}
    {selectedRebalancing :
      WZ2PaperPreparedSelectedRebalancingData pullback}
    {finalLogExponent : ℕ}
    {selectedFinal :
      WZ2PaperPreparedSelectedFinalData
        selectedRebalancing finalLogExponent}
    {massLower volumeUpper threshold : ENNReal}
    {selectedComparison :
      WZ2PaperPreparedSelectedComparisonData
        selectedFinal massLower volumeUpper}
    {deletionExponent : ℕ}
    (post :
      WZ2PaperPreparedSelectedPostDeletionData
        selectedComparison threshold deletionExponent)
    (globalBalancingExponent : ℕ)
    (hGlobalRetention :
      wz1PaperRefinementFraction delta globalBalancingExponent *
          pullback.selectedFineShading.mass ≤
        selectedFinal.finalData.producer.coarseBand.selectedFineShading.mass) :
    Nonempty
      (WZ2PaperPreparedSelectedTotalRefinementData
        post globalBalancingExponent) := by
  let pullbackRefinement :
      WZ1PaperRefinement
        structural.merged.merged.refinement.refined parentExponent :=
    { selected := pullback.selectedFine
      refined := pullback.selectedFineShading
      subshading := pullback.selectedFine_subshading
      retained_mass := by
        calc
          wz1PaperRefinementFraction delta parentExponent *
                structural.merged.merged.refinement.refined.mass ≤
              pullback.refinement.refined.mass :=
            pullback.refinement.retained_mass
          _ = pullback.selectedFineShading.mass :=
            pullback.refinement_refined_mass_eq }
  let identitySelected :
      Kakeya.Streamlined.TubeSubfamily pullback.selectedFine.family :=
    { family := pullback.selectedFine.family
      embedding := Equiv.toEmbedding
        (Equiv.refl (Fin pullback.selectedFine.family.card))
      tube_eq := fun _ => rfl }
  let globalRefinement :
      WZ1PaperRefinement
        pullback.selectedFineShading globalBalancingExponent :=
    { selected := identitySelected
      refined :=
        selectedFinal.finalData.producer.coarseBand.selectedFineShading
      subshading := selectedFinal.final_subshading
      retained_mass := hGlobalRetention }
  let deletionRefinement :
      WZ1PaperRefinement
        selectedFinal.finalData.producer.coarseBand.selectedFineShading
        deletionExponent :=
    { selected := post.deletion.restriction.selected
      refined := post.deletion.restriction.selectedFineShading
      subshading := post.deletion.final_subshading
      retained_mass := by
        simpa [post.deletion.exactAdapter.exact_refined_eq] using
          post.massRetention.retained_mass_to_selected }
  rcases
      wz2_paper_refinement_composition
        shading preparationExponent 4
        prepared.refinement
        structural.merged.merged.refinement
    with ⟨firstTwo⟩
  rcases
      wz2_paper_refinement_composition
        shading (preparationExponent + 4) parentExponent
        firstTwo.toRefinement pullbackRefinement
    with ⟨firstThree⟩
  rcases
      wz2_paper_refinement_composition
        shading ((preparationExponent + 4) + parentExponent)
        globalBalancingExponent
        firstThree.toRefinement globalRefinement
    with ⟨firstFour⟩
  rcases
      wz2_paper_refinement_composition
        shading
        (((preparationExponent + 4) + parentExponent) +
          globalBalancingExponent)
        deletionExponent firstFour.toRefinement deletionRefinement
    with ⟨finalComposition⟩
  exact
    ⟨{
      global_mass_retention := hGlobalRetention
      preDeletionRefinement := firstFour.toRefinement
      preDeletion_selected_family_eq := rfl
      preDeletion_refined_heq := HEq.rfl
      refinement := finalComposition.toRefinement
      selected_family_eq := rfl
      refined_heq := HEq.rfl
    }⟩

end Kakeya.Assouad

end
