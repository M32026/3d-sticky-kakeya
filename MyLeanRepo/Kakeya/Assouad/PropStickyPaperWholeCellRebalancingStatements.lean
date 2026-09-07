import MyLeanRepo.Kakeya.Assouad.PropStickyPaperInitialBalancingStatements

/-!
# Whole-cell rebalancing on a fixed complete-fiber cover

This is the reusable balancing stage needed after any parentwise restriction.
It first selects a global point-multiplicity band, deletes boundary-crossing
literal `delta`-cells, balances the surviving cells exactly inside literal
`rho`-cells, and induces the corresponding coarse shading.

The input cover is unchanged.  In particular, if it was obtained by retaining
complete coarse-parent fibers, this stage restricts only the shading and does
not delete individual fine tubes from those fibers.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperWholeCellRebalancingData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (bandData : WZ2PaperGlobalMultiplicityBandData shading)
    (hdelta : 0 < delta) where
  multiplicityCap : ENNReal
  multiplicityCap_eq :
    multiplicityCap =
      (2 ^ (bandData.level + 1) : ENNReal)
  pruning :
    WZ2PaperBoundaryCellPruningData
      (rho := rho) bandData.band hdelta multiplicityCap
  balancing :
    WZ2PaperExactCellBalancingData
      (rho := rho) pruning.pruned pruning.coarseCells
      pruning.availableFineCells
  coarseData :
    WZ2PaperCoarseShadingData
      cover pruning.pruned pruning.coarseCells
      pruning.availableFineCells balancing

def WZ2PaperWholeCellRebalancingStatement : Prop :=
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
                  (∀ cell : WZ2PaperCellIndex,
                    wz1PaperGridCube rho cell ⊆
                      Kakeya.Streamlined.axisBox 2 2 2) →
                  Nonempty
                    (WZ2PaperWholeCellRebalancingData
                      cover shading bandData hdelta)

end Kakeya.Assouad

end
