import MyLeanRepo.Kakeya.Assouad.PropStickyPaperParentCellMassBandStatements

/-!
# Restrict the fine shading to selected parent--cell incidences

For every fine tube, retain its shading only in those literal `rho`-cells
whose pair with the tube's unique coarse parent lies in the selected
incidence-mass band.  The family itself is unchanged, and all restrictions
are by whole spatial cells.

Because parent fibers partition the fine tube indices and distinct
`rho`-cells are disjoint, the mass of the resulting shading is exactly the
sum of the retained additive parent--cell incidence masses.  Thus the
pair-band logarithmic retention becomes an actual fine-shading mass
retention statement.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure WZ2PaperParentCellRestrictionData
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
    (band :
      WZ2PaperParentCellMassBandData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active fiberBand) where
  selectedCells : Finset WZ2PaperCellIndex
  selectedCells_eq :
    selectedCells = band.retainedPairs.image Prod.fst
  selectedCells_nonempty : selectedCells.Nonempty
  selectedCells_subset :
    selectedCells ⊆ balancing.retainedCoarseCells
  selectedCellsForParent :
    Fin coarse.card → Finset WZ2PaperCellIndex
  selectedCellsForParent_eq :
    ∀ parent,
      selectedCellsForParent parent =
        selectedCells.filter fun cell =>
          (cell, parent) ∈ band.retainedPairs
  refined : WZ1PaperTubeShading fine
  refined_carrier_eq :
    ∀ source,
      refined.carrier source =
        fiberBand.refined.carrier source ∩
          ⋃ cell ∈ selectedCellsForParent (cover.parent source),
            wz1PaperGridCube rho cell
  refined_subshading :
    ∀ source,
      refined.carrier source ⊆
        fiberBand.refined.carrier source
  refined_cubical :
    WZ1PaperIsCubicalShading refined
  refined_union_subset :
    refined.union ⊆
      ⋃ cell ∈ selectedCells,
        wz1PaperGridCube rho cell
  refined_mass_eq :
    refined.mass =
      ∑ pair ∈ band.retainedPairs,
        wz2PaperParentCellMass cover fiberBand.refined pair
  ambient_mass_eq :
    fiberBand.refined.mass =
      ∑ pair ∈
          wz2PaperPositiveParentCellPairs active fiberBand.refined,
        wz2PaperParentCellMass cover fiberBand.refined pair
  retained_mass :
    fiberBand.refined.mass /
          (2 *
            (Nat.log 2
                (2 *
                  (wz2PaperPositiveParentCellPairs
                    active fiberBand.refined).card) + 1) :
            ENNReal) ≤
      refined.mass
  fiber_multiplicity_band :
    ∀ parent point,
      point ∈
          (restrictPaperShading
            (cover.fullFiberSubfamily parent)
            refined).union →
        (2 ^ fiberBand.level : ENNReal) ≤
            ((restrictPaperShading
              (cover.fullFiberSubfamily parent)
              refined).pointMultiplicity point : ENNReal) ∧
          ((restrictPaperShading
              (cover.fullFiberSubfamily parent)
              refined).pointMultiplicity point : ENNReal) <
            (2 ^ (fiberBand.level + 1) : ENNReal)

def WZ2PaperParentCellRestrictionStatement : Prop :=
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
                            ∀ (band :
                                WZ2PaperParentCellMassBandData
                                  cover sourceShading coarseCells
                                  availableFineCells balancing coarseData
                                  active fiberBand),
                              Nonempty
                                (WZ2PaperParentCellRestrictionData
                                  cover sourceShading coarseCells
                                  availableFineCells balancing coarseData
                                  active fiberBand band)

end Kakeya.Assouad

end
