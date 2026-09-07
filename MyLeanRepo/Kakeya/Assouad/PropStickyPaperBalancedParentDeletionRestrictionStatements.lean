import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedParentDeletionRepairedStatements

/-!
# Restrict a repaired parent deletion to complete retained fibers

The repaired deletion retains whole `rho`-cells and records every coarse
parent active in those cells.  Restrict the fine family by complete fibers of
exactly those parents and reindex the corresponding coarse family.  The
result remains an exact balanced cover and preserves the quantitative
per-parent mass floor.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperBalancedParentDeletionRestrictionData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (sourceShading : WZ1PaperTubeShading fine)
    (coarseCells : Finset WZ2PaperCellIndex)
    (availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex)
    (balancing :
      WZ2PaperExactCellBalancingData
        sourceShading coarseCells availableFineCells)
    (coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells availableFineCells balancing)
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (active :
      WZ2PaperBalancedActiveParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData hdelta hrho)
    (referenceFiberMass : Fin coarse.card → ENNReal)
    (degreeCap : ℕ)
    (threshold : ENNReal)
    (deletion :
      WZ2PaperBalancedParentDeletionRepairedData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active referenceFiberMass degreeCap threshold) where
  selectedFineIndices : Finset (Fin fine.card)
  selectedFineIndices_eq :
    selectedFineIndices =
      Finset.univ.filter fun source =>
        cover.parent source ∈ deletion.retainedParents
  source_parent_retained :
    ∀ source,
      (deletion.refined.carrier source).Nonempty →
        cover.parent source ∈ deletion.retainedParents
  selected :
    Kakeya.Streamlined.TubeSubfamily fine
  selected_eq :
    selected =
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        fine selectedFineIndices
  selectedFineShading :
    WZ1PaperTubeShading selected.family
  selectedFineShading_eq :
    selectedFineShading =
      restrictPaperShading selected deletion.refined
  selectedFine_subshading :
    ∀ index,
      selectedFineShading.carrier index ⊆
        balancing.refined.carrier (selected.embedding index)
  selectedFine_cubical :
    WZ1PaperIsCubicalShading selectedFineShading
  selectedFine_union_eq :
    selectedFineShading.union = deletion.refined.union
  selectedFine_mass_eq :
    selectedFineShading.mass = deletion.refined.mass
  restrictedCover :
    WZ2PaperPartitioningCover
      selected.family
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        coarse deletion.retainedParents).family
  restricted_parent_spec :
    ∀ index,
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        coarse deletion.retainedParents).embedding
          (restrictedCover.parent index) =
        cover.parent (selected.embedding index)
  full_fiber_complete :
    ∀ parent :
        Fin
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            coarse deletion.retainedParents).family.card,
      Finset.image selected.embedding
          (wz2PaperFullFiberIndices
            selected.family
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              coarse deletion.retainedParents).family
            parent) =
        wz2PaperFullFiberIndices fine coarse
          ((Kakeya.Streamlined.TubeSubfamily.fromFinset
            coarse deletion.retainedParents).embedding parent)
  parentCells :
    Fin
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          coarse deletion.retainedParents).family.card →
      Finset WZ2PaperCellIndex
  parentCells_eq :
    ∀ parent,
      parentCells parent =
        deletion.goodCells.filter fun cell =>
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            coarse deletion.retainedParents).embedding parent ∈
            active.activeParents cell
  selectedCoarseShading :
    WZ1PaperTubeShading
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        coarse deletion.retainedParents).family
  selectedCoarseShading_carrier_eq :
    ∀ parent,
      selectedCoarseShading.carrier parent =
        ⋃ cell ∈ parentCells parent,
          wz1PaperGridCube rho cell
  selectedCoarseShading_union_eq :
    selectedCoarseShading.union =
      ⋃ cell ∈ deletion.goodCells,
        wz1PaperGridCube rho cell
  exact :
    WZ2PaperExactCellBalancingData
      (rho := rho)
      selectedFineShading deletion.goodCells
      balancing.selectedFineCells
  exact_refined_eq :
    exact.refined = selectedFineShading
  coarseData :
    WZ2PaperCoarseShadingData
      restrictedCover selectedFineShading deletion.goodCells
      balancing.selectedFineCells exact
  coarseData_coarseShading_eq :
    coarseData.coarseShading = selectedCoarseShading
  balanced :
    WZ1PaperBalancedCoverData
      restrictedCover.toWZ1PaperTubeCover
      selectedFineShading selectedCoarseShading
  parent_fiber_mass_floor :
    ∀ parent :
        Fin
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            coarse deletion.retainedParents).family.card,
      threshold *
          referenceFiberMass
            ((Kakeya.Streamlined.TubeSubfamily.fromFinset
              coarse deletion.retainedParents).embedding parent) ≤
        (restrictPaperShading
          (restrictedCover.fullFiberSubfamily parent)
          selectedFineShading).mass

def WZ2PaperBalancedParentDeletionRestrictionStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ (cover : WZ2PaperPartitioningCover fine coarse),
          ∀ (sourceShading : WZ1PaperTubeShading fine),
            ∀ (coarseCells : Finset WZ2PaperCellIndex),
              ∀ (availableFineCells :
                  WZ2PaperCellIndex → Finset WZ2PaperCellIndex),
                ∀ (balancing :
                    WZ2PaperExactCellBalancingData
                      sourceShading coarseCells availableFineCells),
                  ∀ (coarseData :
                      WZ2PaperCoarseShadingData
                        cover sourceShading coarseCells
                        availableFineCells balancing),
                    ∀ {hdelta : 0 < delta},
                      ∀ {hrho : 0 < rho},
                        ∀ (active :
                            WZ2PaperBalancedActiveParentCellsData
                              cover sourceShading coarseCells
                              availableFineCells balancing coarseData
                              hdelta hrho),
                          ∀ (degreeCap : ℕ),
                            ∀ (referenceFiberMass :
                                Fin coarse.card → ENNReal),
                            ∀ (threshold : ENNReal),
                              ∀ (deletion :
                                  WZ2PaperBalancedParentDeletionRepairedData
                                    cover sourceShading coarseCells
                                    availableFineCells balancing coarseData
                                    active referenceFiberMass degreeCap
                                    threshold),
                                Nonempty
                                  (WZ2PaperBalancedParentDeletionRestrictionData
                                    cover sourceShading coarseCells
                                    availableFineCells balancing coarseData
                                    active referenceFiberMass degreeCap
                                    threshold deletion)

end Kakeya.Assouad

end
