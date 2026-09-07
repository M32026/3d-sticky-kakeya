import MyLeanRepo.Kakeya.Assouad.PropStickyPaperParentCellRestrictionStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancing

/-!
# Final fine exact balancing before inducing the coarse shading

Select one global fine point-multiplicity band from the parent-cell
restriction.  Its active literal `delta`-cells already lie in selected
literal `rho`-cells.  Group them by their containing coarse cell and invoke
the closed exact balancing theorem.

No coarse shading is constructed at this stage.  It must be induced from the
actual final fine incidences afterward, preventing ghost parent--cell
incidences.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure WZ2PaperFinalFineExactBalancingData
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
        balancing coarseData active fiberBand pairBand) where
  fineLevel : ℕ
  fineBand : WZ1PaperTubeShading fine
  fineBand_carrier_eq :
    ∀ source,
      fineBand.carrier source =
        restriction.refined.carrier source ∩
          wz1PaperDyadicMultiplicityBand
            restriction.refined fineLevel
  fineBand_cubical :
    WZ1PaperIsCubicalShading fineBand
  fineBand_multiplicity :
    ∀ point ∈ fineBand.union,
      (2 ^ fineLevel : ENNReal) ≤
          (fineBand.pointMultiplicity point : ENNReal) ∧
        (fineBand.pointMultiplicity point : ENNReal) <
          (2 ^ (fineLevel + 1) : ENNReal)
  fineBand_mass_retention :
    restriction.refined.mass /
          ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) ≤
      fineBand.mass
  activeFineCells : Finset WZ2PaperCellIndex
  activeFineCells_eq :
    activeFineCells = wz1PaperActiveCells fineBand hdelta
  activeFineCells_nonempty : activeFineCells.Nonempty
  coarseParent :
    WZ2PaperCellIndex → WZ2PaperCellIndex
  activeFineCell_contained :
    ∀ fineCell ∈ activeFineCells,
      coarseParent fineCell ∈ restriction.selectedCells ∧
        wz1PaperGridCube delta fineCell ⊆
          wz1PaperGridCube rho (coarseParent fineCell)
  finalCoarseCells : Finset WZ2PaperCellIndex
  finalCoarseCells_eq :
    finalCoarseCells = activeFineCells.image coarseParent
  finalCoarseCells_nonempty : finalCoarseCells.Nonempty
  availableFinalFineCells :
    WZ2PaperCellIndex → Finset WZ2PaperCellIndex
  availableFinalFineCells_eq :
    ∀ cell,
      availableFinalFineCells cell =
        activeFineCells.filter fun fineCell =>
          coarseParent fineCell = cell
  availableFinalFineCells_nonempty :
    ∀ cell ∈ finalCoarseCells,
      (availableFinalFineCells cell).Nonempty
  availableFinalFineCells_ready :
    ∀ cell ∈ finalCoarseCells,
      ∀ fineCell ∈ availableFinalFineCells cell,
        fineCell ∈ wz1PaperActiveCells fineBand hdelta ∧
          wz1PaperGridCube delta fineCell ⊆
            wz1PaperGridCube rho cell
  exact :
    WZ2PaperExactCellBalancingData
      (rho := rho) fineBand finalCoarseCells
      availableFinalFineCells
  retained_coarse_subset :
    exact.retainedCoarseCells ⊆ restriction.selectedCells
  exact_multiplicity_band :
    ∀ point ∈ exact.refined.union,
      (2 ^ fineLevel : ENNReal) ≤
          (exact.refined.pointMultiplicity point : ENNReal) ∧
        (exact.refined.pointMultiplicity point : ENNReal) <
          (2 ^ (fineLevel + 1) : ENNReal)
  exact_mass_retention :
    fineBand.mass ≤
      (4 *
        ((Nat.log 2
            (∑ cell ∈ finalCoarseCells,
              (availableFinalFineCells cell).card) + 1 : ℕ) :
          ENNReal)) *
        exact.refined.mass
  fiber_multiplicity_band :
    ∀ parent point,
      point ∈
          (restrictPaperShading
            (cover.fullFiberSubfamily parent)
            exact.refined).union →
        (2 ^ fiberBand.level : ENNReal) ≤
            ((restrictPaperShading
              (cover.fullFiberSubfamily parent)
              exact.refined).pointMultiplicity point : ENNReal) ∧
          ((restrictPaperShading
              (cover.fullFiberSubfamily parent)
              exact.refined).pointMultiplicity point : ENNReal) <
            (2 ^ (fiberBand.level + 1) : ENNReal)

def WZ2PaperFinalFineExactBalancingStatement : Prop :=
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
                                Nonempty
                                  (WZ2PaperFinalFineExactBalancingData
                                    cover sourceShading coarseCells
                                    availableFineCells balancing
                                    coarseData active fiberBand pairBand
                                    restriction)

end Kakeya.Assouad

end
