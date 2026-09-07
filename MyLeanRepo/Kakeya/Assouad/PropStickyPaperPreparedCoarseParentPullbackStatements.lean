import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPreparedCoarseParentRegularizationStatements

/-!
# Pull back a prepared coarse-parent selection by complete fibers

The coarse external-weight regularizer selects tubes in the canonical caller
coarse family.  Retain every merged fine tube whose caller parent is selected.
This preserves complete parent fibers and produces the exact partitioning
cover used by the subsequent whole-cell rebalancing.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperPreparedCoarseParentPullbackData
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
    {levelCount : ℕ}
    (regularization :
      WZ2PaperPreparedCoarseParentRegularizationData
        prepared critical structural
        ambientConstant outputConstant normalizationWeight weightUpper
        levelCount)
    (logExponent : ℕ) where
  selectedFineIndices :
    Finset (Fin structural.merged.merged.refinement.selected.family.card)
  selectedFineIndices_eq :
    selectedFineIndices =
      Finset.univ.filter fun sourceIndex =>
        ∃ parent :
            Fin regularization.regularized.selected.family.card,
          structural.merged.restrictedCover.parent sourceIndex =
            regularization.regularized.selected.embedding parent
  selectedFine :
    Kakeya.Streamlined.TubeSubfamily
      structural.merged.merged.refinement.selected.family
  selectedFine_eq :
    selectedFine =
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        structural.merged.merged.refinement.selected.family
        selectedFineIndices
  selectedFineShading :
    WZ1PaperTubeShading selectedFine.family
  selectedFineShading_eq :
    selectedFineShading =
      restrictPaperShading selectedFine
        structural.merged.merged.refinement.refined
  selectedFine_subshading :
    ∀ index,
      selectedFineShading.carrier index ⊆
        structural.merged.merged.refinement.refined.carrier
          (selectedFine.embedding index)
  selectedFine_cubical :
    WZ1PaperIsCubicalShading selectedFineShading
  parent :
    Fin selectedFine.family.card →
      Fin regularization.regularized.selected.family.card
  parent_ambient_eq :
    ∀ index,
      regularization.regularized.selected.embedding (parent index) =
        structural.merged.restrictedCover.parent
          (selectedFine.embedding index)
  cover :
    WZ2PaperPartitioningCover
      selectedFine.family
      regularization.regularized.selected.family
  cover_parent_eq :
    ∀ index, cover.parent index = parent index
  full_fiber_complete :
    ∀ parentIndex :
        Fin regularization.regularized.selected.family.card,
      Finset.image selectedFine.embedding
          (wz2PaperFullFiberIndices
            selectedFine.family
            regularization.regularized.selected.family
            parentIndex) =
        wz2PaperFullFiberIndices
          structural.merged.merged.refinement.selected.family
          prepared.callerStrict.coarse
          (regularization.regularized.selected.embedding parentIndex)
  selected_mass_eq :
    selectedFineShading.mass =
      regularization.regularized.selectedWeight
  full_fiber_mass_eq :
    ∀ parent,
      (restrictPaperShading
        (cover.fullFiberSubfamily parent)
        selectedFineShading).mass =
          regularization.selectedParentMass parent
  refinement :
    WZ1PaperRefinement
      structural.merged.merged.refinement.refined logExponent
  refinement_selected_eq :
    refinement.selected = selectedFine
  refinement_refined_heq :
    HEq refinement.refined selectedFineShading
  refinement_refined_mass_eq :
    refinement.refined.mass = selectedFineShading.mass

end Kakeya.Assouad

end
