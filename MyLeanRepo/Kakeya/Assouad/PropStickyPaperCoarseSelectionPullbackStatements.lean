import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoarseOwnerRegularization

/-!
# Pull back a regularized coarse selection by complete parent fibers

The ambient external-weight regularizer selects coarse tubes.  The paper
refines the fine family by retaining every fine tube in the complete fibers
of those selected parents.  This is a parentwise restriction, not an
individual fine-tube deletion.

The owner-specific exactification makes the induced spatial structure
explicit: the retained coarse cells are precisely those owned by a selected
parent, the retained fine union is precisely the union of their selected
literal `delta`-cells, and the restricted fine/coarse pair remains an exact
balanced cover with the same cell mass.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure WZ2PaperCoarseSelectionPullbackData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells
        availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells
        availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {active :
      WZ2PaperBalancedActiveParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData hdelta hrho}
    {multiplicityLevel : ℕ}
    {degree :
      WZ2PaperBalancedParentDegreeData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel}
    {dominant :
      WZ2PaperDominantParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree}
    {owned :
      WZ2PaperDominantParentFineCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree dominant}
    (exactified :
      WZ2PaperDominantOwnerExactificationData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree
        dominant owned)
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    (regularization :
      WZ2PaperCoarseOwnerRegularizationData
        exactified ambientConstant outputConstant
        normalizationWeight weightUpper packedConstant levelCount) where
  selectedFineIndices :
    Finset (Fin exactified.selected.family.card)
  selectedFineIndices_eq :
    selectedFineIndices =
      Finset.univ.filter fun source =>
        ∃ parent :
            Fin regularization.regularized.selected.family.card,
          exactified.restrictedCover.parent source =
            regularization.support.packedIndex parent
  selectedFine :
    Kakeya.Streamlined.TubeSubfamily exactified.selected.family
  selectedFine_eq :
    selectedFine =
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        exactified.selected.family selectedFineIndices
  selectedFineShading :
    WZ1PaperTubeShading selectedFine.family
  selectedFineShading_eq :
    selectedFineShading =
      restrictPaperShading selectedFine exactified.refined
  selectedFine_subshading :
    ∀ index,
      selectedFineShading.carrier index ⊆
        exactified.refined.carrier
          (selectedFine.embedding index)
  selectedFine_cubical :
    WZ1PaperIsCubicalShading selectedFineShading
  restrictedCover :
    WZ2PaperPartitioningCover
      selectedFine.family regularization.regularized.selected.family
  restricted_parent_eq :
    ∀ index,
      exactified.restrictedCover.parent
          (selectedFine.embedding index) =
        regularization.support.packedIndex
          (restrictedCover.parent index)
  full_fiber_complete_in_exactified :
    ∀ parent :
        Fin regularization.regularized.selected.family.card,
      Finset.image selectedFine.embedding
          (wz2PaperFullFiberIndices
            selectedFine.family
            regularization.regularized.selected.family
            parent) =
        wz2PaperFullFiberIndices
          exactified.selected.family
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            coarse exactified.retainedParents).family
          (regularization.support.packedIndex parent)
  full_fiber_complete :
    ∀ parent :
        Fin regularization.regularized.selected.family.card,
      Finset.image
          (fun source =>
            exactified.selected.embedding
              (selectedFine.embedding source))
          (wz2PaperFullFiberIndices
            selectedFine.family
            regularization.regularized.selected.family
            parent) =
        wz2PaperFullFiberIndices fine coarse
          ((Kakeya.Streamlined.TubeSubfamily.fromFinset
            coarse exactified.retainedParents).embedding
              (regularization.support.packedIndex parent))
  full_fiber_complete_ambient_selected :
    ∀ parent :
        Fin regularization.regularized.selected.family.card,
      Finset.image
          (fun source =>
            exactified.selected.embedding
              (selectedFine.embedding source))
          (wz2PaperFullFiberIndices
            selectedFine.family
            regularization.regularized.selected.family
            parent) =
        wz2PaperFullFiberIndices fine coarse
          (regularization.regularized.selected.embedding parent)
  selectedCells : Finset WZ2PaperCellIndex
  selectedCells_eq :
    selectedCells =
      exactified.retainedCells.filter fun cell =>
        ∃ parent :
            Fin regularization.regularized.selected.family.card,
          dominant.dominantParent cell =
            regularization.regularized.selected.embedding parent
  selectedCells_nonempty : selectedCells.Nonempty
  selected_coarse_carrier_eq :
    ∀ parent,
      regularization.selectedShading.carrier parent =
        ⋃ cell ∈ selectedCells,
          if
              regularization.regularized.selected.embedding parent =
                dominant.dominantParent cell
          then wz1PaperGridCube rho cell
          else ∅
  selected_fine_union_eq :
    selectedFineShading.union =
      ⋃ cell ∈ selectedCells,
        ⋃ fineCell ∈ exactified.selectedOwnerFineCells cell,
          wz1PaperGridCube delta fineCell
  fine_owner :
    ∀ index point,
      point ∈ selectedFineShading.carrier index →
        ∃ cell ∈ selectedCells,
          point ∈ wz1PaperGridCube rho cell ∧
            regularization.regularized.selected.embedding
                (restrictedCover.parent index) =
              dominant.dominantParent cell
  balanced :
    WZ1PaperBalancedCoverData
      restrictedCover.toWZ1PaperTubeCover
      selectedFineShading regularization.selectedShading
  balanced_activeCells_eq :
    balanced.activeCells = selectedCells
  balanced_cellMass_eq :
    balanced.cellMass = exactified.balanced_cellMass
  parent_fiber_mass_floor :
    ∀ parent :
        Fin regularization.regularized.selected.family.card,
      exactified.balanced_cellMass ≤
        (restrictPaperShading
          (restrictedCover.fullFiberSubfamily parent)
          selectedFineShading).mass

def WZ2PaperCoarseSelectionPullbackStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
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
                    ∀ {hdelta : 0 < delta},
                      ∀ {hrho : 0 < rho},
                        ∀ {active :
                            WZ2PaperBalancedActiveParentCellsData
                              cover sourceShading coarseCells
                              availableFineCells balancing coarseData
                              hdelta hrho},
                          ∀ {multiplicityLevel : ℕ},
                            ∀ {degree :
                                WZ2PaperBalancedParentDegreeData
                                  cover sourceShading coarseCells
                                  availableFineCells balancing
                                  coarseData active multiplicityLevel},
                              ∀ {dominant :
                                  WZ2PaperDominantParentCellsData
                                    cover sourceShading coarseCells
                                    availableFineCells balancing
                                    coarseData active
                                    multiplicityLevel degree},
                                ∀ {owned :
                                    WZ2PaperDominantParentFineCellsData
                                      cover sourceShading coarseCells
                                      availableFineCells balancing
                                      coarseData active
                                      multiplicityLevel degree dominant},
                                  ∀ (exactified :
                                      WZ2PaperDominantOwnerExactificationData
                                        cover sourceShading coarseCells
                                        availableFineCells balancing
                                        coarseData active
                                        multiplicityLevel degree dominant
                                        owned),
                                    ∀ {ambientConstant outputConstant
                                        normalizationWeight weightUpper
                                        packedConstant : ENNReal},
                                      ∀ {levelCount : ℕ},
                                        ∀ (regularization :
                                            WZ2PaperCoarseOwnerRegularizationData
                                              exactified ambientConstant
                                              outputConstant
                                              normalizationWeight
                                              weightUpper packedConstant
                                              levelCount),
                                          Nonempty
                                            (WZ2PaperCoarseSelectionPullbackData
                                              exactified regularization)

end Kakeya.Assouad

end
