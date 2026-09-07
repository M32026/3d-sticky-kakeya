import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalInducedCoarseShadingStatements

/-!
# Final coarse multiplicity band weighted by final fine mass

Dyadically pigeonhole the point multiplicity of the coarse shading induced
from actual final fine incidences.  Weight each band by the mass of the final
fine shading in the same union of whole literal `rho`-cells.

Restrict both shadings by the selected cells.  Since every induced
parent--cell incidence is genuine, and both restrictions use the same whole
cells, point compatibility and exact fine-cell balance remain valid.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure WZ2PaperFinalCoarseMultiplicityBandData
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
    (fiberBand :
      WZ2PaperFiberMultiplicityBandData
        cover balancing.refined)
    (pairBand :
      WZ2PaperParentCellMassBandData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active fiberBand)
    (restriction :
      WZ2PaperParentCellRestrictionData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active fiberBand pairBand)
    (finalFine :
      WZ2PaperFinalFineExactBalancingData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active fiberBand pairBand restriction)
    (induced :
      WZ2PaperFinalInducedCoarseShadingData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active fiberBand pairBand restriction
        finalFine) where
  level : ℕ
  selectedCells : Finset WZ2PaperCellIndex
  selectedCells_subset :
    selectedCells ⊆ finalFine.exact.retainedCoarseCells
  selectedCells_nonempty : selectedCells.Nonempty
  selectedRegion : Set Point3
  selectedRegion_eq :
    selectedRegion =
      ⋃ cell ∈ selectedCells,
        wz1PaperGridCube rho cell
  selectedCoarseShading : WZ1PaperTubeShading coarse
  selectedCoarse_carrier_eq :
    ∀ parent,
      selectedCoarseShading.carrier parent =
        induced.coarseShading.carrier parent ∩ selectedRegion
  selectedCoarse_cubical :
    WZ1PaperIsCubicalShading selectedCoarseShading
  selectedCoarse_union_eq :
    selectedCoarseShading.union = selectedRegion
  coarse_multiplicity_band :
    ∀ point ∈ selectedRegion,
      (2 ^ level : ENNReal) ≤
          (selectedCoarseShading.pointMultiplicity point : ENNReal) ∧
        (selectedCoarseShading.pointMultiplicity point : ENNReal) <
          (2 ^ (level + 1) : ENNReal)
  selectedFineShading : WZ1PaperTubeShading fine
  selectedFine_carrier_eq :
    ∀ source,
      selectedFineShading.carrier source =
        finalFine.exact.refined.carrier source ∩ selectedRegion
  selectedFine_subshading :
    ∀ source,
      selectedFineShading.carrier source ⊆
        finalFine.exact.refined.carrier source
  selectedFine_cubical :
    WZ1PaperIsCubicalShading selectedFineShading
  selectedFine_union_eq :
    selectedFineShading.union =
      finalFine.exact.refined.union ∩ selectedRegion
  point_compatibility :
    ∀ source point,
      point ∈ selectedFineShading.carrier source →
        point ∈ selectedCoarseShading.carrier (cover.parent source)
  selectedFine_mass_retention :
    finalFine.exact.refined.mass /
          ((Nat.log 2 coarse.card + 1 : ℕ) : ENNReal) ≤
      selectedFineShading.mass
  selected_cell_mass :
    ∀ cell ∈ selectedCells,
      MeasureTheory.volume
          (selectedFineShading.union ∩
            wz1PaperGridCube rho cell) =
        finalFine.exact.cellMass
  fiber_multiplicity_band :
    ∀ parent point,
      point ∈
          (restrictPaperShading
            (cover.fullFiberSubfamily parent)
            selectedFineShading).union →
        (2 ^ fiberBand.level : ENNReal) ≤
            ((restrictPaperShading
              (cover.fullFiberSubfamily parent)
              selectedFineShading).pointMultiplicity point : ENNReal) ∧
          ((restrictPaperShading
              (cover.fullFiberSubfamily parent)
              selectedFineShading).pointMultiplicity point : ENNReal) <
            (2 ^ (fiberBand.level + 1) : ENNReal)

def WZ2PaperFinalCoarseMultiplicityBandStatement : Prop :=
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
                          ∀ (fiberBand :
                              WZ2PaperFiberMultiplicityBandData
                                cover balancing.refined),
                            ∀ (pairBand :
                                WZ2PaperParentCellMassBandData
                                  cover sourceShading coarseCells
                                  availableFineCells balancing coarseData
                                  active fiberBand),
                              ∀ (restriction :
                                  WZ2PaperParentCellRestrictionData
                                    cover sourceShading coarseCells
                                    availableFineCells balancing
                                    coarseData active fiberBand pairBand),
                                ∀ (finalFine :
                                    WZ2PaperFinalFineExactBalancingData
                                      cover sourceShading coarseCells
                                      availableFineCells balancing
                                      coarseData active fiberBand pairBand
                                      restriction),
                                  ∀ (induced :
                                      WZ2PaperFinalInducedCoarseShadingData
                                        cover sourceShading coarseCells
                                        availableFineCells balancing
                                        coarseData active fiberBand pairBand
                                        restriction finalFine),
                                    Nonempty
                                      (WZ2PaperFinalCoarseMultiplicityBandData
                                        cover sourceShading coarseCells
                                        availableFineCells balancing
                                        coarseData active fiberBand pairBand
                                        restriction finalFine induced)

end Kakeya.Assouad

end
