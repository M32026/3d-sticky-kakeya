import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantParentFineCellsStatements

/-!
# Exact whole-cell balance inside dominant parent fibers

Dyadically pigeonhole the number of dominant-parent-owned literal
`delta`-cells in each selected `rho`-cell.  In every retained count band,
keep the same number of owned cells.  Retain the complete ambient full fiber
of every coarse parent that owns a retained cell, and restrict only its
shading to the selected whole cells.  The resulting cover is exactly balanced
and every retained complete coarse-parent fiber has a quantitative mass
floor.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure WZ2PaperDominantOwnerExactificationData
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
        (rho := rho) sourceShading coarseCells
        availableFineCells)
    (coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells
        availableFineCells balancing)
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (active :
      WZ2PaperBalancedActiveParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData hdelta hrho)
    (multiplicityLevel : ℕ)
    (degree :
      WZ2PaperBalancedParentDegreeData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel)
    (dominant :
      WZ2PaperDominantParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree)
    (owned :
      WZ2PaperDominantParentFineCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree dominant) where
  countBins : ℕ
  countBins_eq :
    countBins =
      Nat.log 2
        (2 *
          (∑ cell ∈ dominant.selectedCells,
            (owned.ownedFineCells cell).card)) + 1
  level : ℕ
  retainedCells : Finset WZ2PaperCellIndex
  retainedCells_subset :
    retainedCells ⊆ dominant.selectedCells
  retainedCells_nonempty : retainedCells.Nonempty
  owned_count_band :
    ∀ cell ∈ retainedCells,
      2 ^ level ≤ (owned.ownedFineCells cell).card ∧
        (owned.ownedFineCells cell).card < 2 ^ (level + 1)
  selectedOwnerFineCells :
    WZ2PaperCellIndex → Finset WZ2PaperCellIndex
  selectedOwnerFineCells_subset :
    ∀ cell ∈ retainedCells,
      selectedOwnerFineCells cell ⊆ owned.ownedFineCells cell
  selectedOwnerFineCells_card :
    ∀ cell ∈ retainedCells,
      (selectedOwnerFineCells cell).card = 2 ^ level
  retainedCells_cardinality :
    dominant.selectedCells.card ≤
      countBins * retainedCells.card
  retainedFineCells : Finset WZ2PaperCellIndex
  retainedFineCells_eq :
    retainedFineCells =
      retainedCells.biUnion selectedOwnerFineCells
  selectedFineIndices : Finset (Fin fine.card)
  selectedFineIndices_eq :
    selectedFineIndices =
      Finset.univ.filter fun source =>
        cover.parent source ∈
          retainedCells.image dominant.dominantParent
  selected :
    Kakeya.Streamlined.TubeSubfamily fine
  selected_eq :
    selected =
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        fine selectedFineIndices
  refined : WZ1PaperTubeShading selected.family
  refined_carrier_eq :
    ∀ index,
      refined.carrier index =
        balancing.refined.carrier (selected.embedding index) ∩
          ⋃ cell ∈ retainedCells,
            if cover.parent (selected.embedding index) =
                dominant.dominantParent cell then
              ⋃ fineCell ∈ selectedOwnerFineCells cell,
                wz1PaperGridCube delta fineCell
            else ∅
  refined_cubical : WZ1PaperIsCubicalShading refined
  refined_union_eq :
    refined.union =
      ⋃ cell ∈ retainedCells,
        ⋃ fineCell ∈ selectedOwnerFineCells cell,
          wz1PaperGridCube delta fineCell
  retainedParents : Finset (Fin coarse.card)
  retainedParents_eq :
    retainedParents =
      retainedCells.image dominant.dominantParent
  retainedParents_nonempty : retainedParents.Nonempty
  selectedFineIndices_eq_retainedParents :
    selectedFineIndices =
      Finset.univ.filter fun source =>
        cover.parent source ∈ retainedParents
  owner_surjective :
    ∀ parent ∈ retainedParents,
      ∃ cell ∈ retainedCells,
        dominant.dominantParent cell = parent
  restrictedCover :
    WZ2PaperPartitioningCover
      selected.family
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        coarse retainedParents).family
  full_fiber_complete :
    ∀ parent :
        Fin (Kakeya.Streamlined.TubeSubfamily.fromFinset
          coarse retainedParents).family.card,
      Finset.image selected.embedding
          (wz2PaperFullFiberIndices
            selected.family
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              coarse retainedParents).family
            parent) =
        wz2PaperFullFiberIndices fine coarse
          ((Kakeya.Streamlined.TubeSubfamily.fromFinset
            coarse retainedParents).embedding parent)
  coarseShading :
    WZ1PaperTubeShading
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        coarse retainedParents).family
  coarse_carrier_eq :
    ∀ parent,
      coarseShading.carrier parent =
        ⋃ cell ∈ retainedCells,
          if
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                coarse retainedParents).embedding parent =
                dominant.dominantParent cell
          then wz1PaperGridCube rho cell
          else ∅
  refined_owner :
    ∀ index point,
      point ∈ refined.carrier index →
        ∃ cell ∈ retainedCells,
          point ∈ wz1PaperGridCube rho cell ∧
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              coarse retainedParents).embedding
                (restrictedCover.parent index) =
              dominant.dominantParent cell
  balanced :
    WZ1PaperBalancedCoverData
      restrictedCover.toWZ1PaperTubeCover
      refined coarseShading
  balanced_activeCells_eq :
    balanced.activeCells = retainedCells
  balanced_cellMass : ENNReal
  balanced_cellMass_eq :
    balanced_cellMass =
      (2 ^ level : ENNReal) *
        active.fiberCellMass
  dominant_mass_retention :
    (∑ cell ∈ dominant.selectedCells,
        dominant.dominantMass cell) ≤
      (4 *
          (2 ^ (multiplicityLevel + 1) : ENNReal) *
          (countBins : ENNReal)) *
        refined.mass
  parent_fiber_mass_floor :
    ∀ parent :
        Fin (Kakeya.Streamlined.TubeSubfamily.fromFinset
          coarse retainedParents).family.card,
      balanced_cellMass ≤
        (restrictPaperShading
          (restrictedCover.fullFiberSubfamily parent)
          refined).mass

def WZ2PaperDominantOwnerExactificationStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ (hdelta : 0 < delta),
      ∀ (hrho : 0 < rho),
        ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
          ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
            ∀ (cover : WZ2PaperPartitioningCover fine coarse),
              ∀ (sourceShading : WZ1PaperTubeShading fine),
                ∀ (coarseCells : Finset WZ2PaperCellIndex),
                  ∀ (availableFineCells :
                      WZ2PaperCellIndex →
                        Finset WZ2PaperCellIndex),
                    ∀ (balancing :
                        WZ2PaperExactCellBalancingData
                          (rho := rho) sourceShading coarseCells
                          availableFineCells),
                      ∀ (coarseData :
                          WZ2PaperCoarseShadingData
                            cover sourceShading coarseCells
                            availableFineCells balancing),
                        ∀ (active :
                            WZ2PaperBalancedActiveParentCellsData
                              cover sourceShading coarseCells
                              availableFineCells balancing coarseData
                              hdelta hrho),
                          ∀ (multiplicityLevel : ℕ),
                            ∀ (degree :
                                WZ2PaperBalancedParentDegreeData
                                  cover sourceShading coarseCells
                                  availableFineCells balancing
                                  coarseData active
                                  multiplicityLevel),
                              ∀ (dominant :
                                  WZ2PaperDominantParentCellsData
                                    cover sourceShading coarseCells
                                    availableFineCells balancing
                                    coarseData active
                                    multiplicityLevel degree),
                                ∀ (owned :
                                    WZ2PaperDominantParentFineCellsData
                                      cover sourceShading coarseCells
                                      availableFineCells balancing
                                      coarseData active
                                      multiplicityLevel degree dominant),
                                  Nonempty
                                    (WZ2PaperDominantOwnerExactificationData
                                      cover sourceShading coarseCells
                                      availableFineCells balancing
                                      coarseData active
                                      multiplicityLevel degree dominant
                                      owned)

end Kakeya.Assouad

end
