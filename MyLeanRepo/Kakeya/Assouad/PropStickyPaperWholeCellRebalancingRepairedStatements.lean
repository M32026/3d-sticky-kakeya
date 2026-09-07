import MyLeanRepo.Kakeya.Assouad.PropStickyPaperInitialBalancingStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCropCellPruningStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoarseShadingStatements

/-!
# Repaired whole-cell rebalancing with crop-boundary pruning

The fixed-origin `rho`-grid requires two geometric deletions:

1. remove `delta`-cells crossing a `rho`-grid hyperplane;
2. after exact balancing, remove retained `rho`-cells crossing the boundary
   of the cropped paper window.

Both deletions remove whole cells.  The second deletion therefore preserves
the exact common cell mass and supplies the finite crop condition needed by
the coarse paper shading constructor.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperWholeCellRebalancingRepairedData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (bandData : WZ2PaperGlobalMultiplicityBandData shading)
    (hdelta : 0 < delta)
    (hrho : 0 < rho) where
  multiplicityCap : ENNReal
  multiplicityCap_eq :
    multiplicityCap =
      (2 ^ (bandData.level + 1) : ENNReal)
  boundaryPruning :
    WZ2PaperBoundaryCellPruningData
      (rho := rho) bandData.band hdelta multiplicityCap
  initialBalancing :
    WZ2PaperExactCellBalancingData
      (rho := rho)
      boundaryPruning.pruned
      boundaryPruning.coarseCells
      boundaryPruning.availableFineCells
  cropPruning :
    WZ2PaperCropCellPruningData
      boundaryPruning.pruned
      boundaryPruning.coarseCells
      boundaryPruning.availableFineCells
      initialBalancing multiplicityCap
  coarseData :
    WZ2PaperCoarseShadingData
      cover cropPruning.refined
      cropPruning.retainedCoarseCells
      cropPruning.selectedFineCells
      cropPruning.croppedBalancing

/--
Whole-cell rebalancing from direct aggregate mass bounds for both geometric
deletions.  This is the paper-facing route used after CWA boundary estimates.
-/
def WZ2PaperWholeCellRebalancingFromBoundaryMassStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ (hdelta : 0 < delta),
      ∀ (hrho : 0 < rho),
        delta ≤ rho →
        rho ≤ 1 →
        18 * delta ≤ rho →
        ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
          ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
            ∀ (cover : WZ2PaperPartitioningCover fine coarse),
              WZ1PaperIsLineClass fine →
              WZ1PaperIsLineClass coarse →
              ∀ (shading : WZ1PaperTubeShading fine),
                ∀ (bandData :
                    WZ2PaperGlobalMultiplicityBandData shading),
                  (∑ index : Fin fine.card,
                      MeasureTheory.volume
                        (bandData.band.carrier index ∩
                          wz2PaperBoundaryCrossingRegion
                            (rho := rho) bandData.band hdelta)) <
                    bandData.band.mass →
                  (∀ boundaryPruning :
                      WZ2PaperBoundaryCellPruningData
                        (rho := rho) bandData.band hdelta
                        (2 ^ (bandData.level + 1) : ENNReal),
                    ∀ initialBalancing :
                        WZ2PaperExactCellBalancingData
                          (rho := rho)
                          boundaryPruning.pruned
                          boundaryPruning.coarseCells
                          boundaryPruning.availableFineCells,
                      (∑ index : Fin fine.card,
                          MeasureTheory.volume
                            (initialBalancing.refined.carrier index ∩
                              wz2PaperCropBoundaryRegion rho)) <
                        initialBalancing.refined.mass) →
                  Nonempty
                    (WZ2PaperWholeCellRebalancingRepairedData
                      cover shading bandData hdelta hrho)

def WZ2PaperWholeCellRebalancingRepairedStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ (hdelta : 0 < delta),
      ∀ (hrho : 0 < rho),
        delta ≤ rho →
        rho ≤ 1 →
        18 * delta ≤ rho →
        ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
          ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
            ∀ (cover : WZ2PaperPartitioningCover fine coarse),
              WZ1PaperIsLineClass fine →
              WZ1PaperIsLineClass coarse →
              ∀ (shading : WZ1PaperTubeShading fine),
                ∀ (bandData :
                    WZ2PaperGlobalMultiplicityBandData shading),
                  (2 ^ (bandData.level + 1) : ENNReal) *
                        ENNReal.ofReal (1000 * delta / rho) <
                      bandData.band.mass →
                  (∀ boundaryPruning :
                      WZ2PaperBoundaryCellPruningData
                        (rho := rho) bandData.band hdelta
                        (2 ^ (bandData.level + 1) : ENNReal),
                    ∀ initialBalancing :
                        WZ2PaperExactCellBalancingData
                          (rho := rho)
                          boundaryPruning.pruned
                          boundaryPruning.coarseCells
                          boundaryPruning.availableFineCells,
                      (2 ^ (bandData.level + 1) : ENNReal) *
                          ENNReal.ofReal (48 * rho) <
                        initialBalancing.refined.mass) →
                  Nonempty
                    (WZ2PaperWholeCellRebalancingRepairedData
                      cover shading bandData hdelta hrho)

end Kakeya.Assouad

end
