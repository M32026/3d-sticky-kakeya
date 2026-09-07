import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedParentDegreeStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization.WeightBinning

/-!
# Dominant parent contribution in each balanced cell

For each retained literal `rho`-cell, choose an active coarse parent whose
final full-fiber contribution is maximal.  The active-parent degree bound
shows that this dominant contribution controls the total exact cell mass.
Dyadically pigeonhole the one dominant weight attached to each cell and keep
whole cells in one common dominant-parent mass band.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure WZ2PaperDominantParentCellsData
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
        balancing coarseData active multiplicityLevel) where
  dominantParent :
    WZ2PaperCellIndex → Fin coarse.card
  dominantParent_mem :
    ∀ cell ∈ balancing.retainedCoarseCells,
      dominantParent cell ∈ active.activeParents cell
  dominantMass :
    WZ2PaperCellIndex → ENNReal
  dominantMass_eq :
    ∀ cell,
      dominantMass cell =
        wz2PaperParentCellMass cover balancing.refined
          (cell, dominantParent cell)
  dominant_max :
    ∀ cell ∈ balancing.retainedCoarseCells,
      ∀ parent ∈ active.activeParents cell,
        wz2PaperParentCellMass cover balancing.refined
            (cell, parent) ≤
          dominantMass cell
  dominant_lower :
    ∀ cell ∈ balancing.retainedCoarseCells,
      balancing.cellMass ≤
        (2 *
          wz2PaperBalancedParentDegreeCap
            balancing multiplicityLevel : ENNReal) *
          dominantMass cell
  selectedCells : Finset WZ2PaperCellIndex
  selectedCells_subset :
    selectedCells ⊆ balancing.retainedCoarseCells
  selectedCells_nonempty : selectedCells.Nonempty
  dominantCellMass : ENNReal
  dominantCellMass_pos : 0 < dominantCellMass
  dominantCellMass_ne_top : dominantCellMass ≠ ⊤
  dominant_mass_band :
    ∀ cell ∈ selectedCells,
      dominantCellMass ≤ dominantMass cell ∧
        dominantMass cell ≤ 2 * dominantCellMass
  selected_mass_retention :
    (∑ cell ∈ balancing.retainedCoarseCells,
        dominantMass cell) /
          (2 *
            (Nat.log 2
                (2 * balancing.retainedCoarseCells.card) + 1) :
            ENNReal) ≤
      ∑ cell ∈ selectedCells, dominantMass cell

def WZ2PaperDominantParentCellsStatement : Prop :=
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
                              Nonempty
                                (WZ2PaperDominantParentCellsData
                                  cover sourceShading coarseCells
                                  availableFineCells balancing
                                  coarseData active
                                  multiplicityLevel degree)

end Kakeya.Assouad

end
