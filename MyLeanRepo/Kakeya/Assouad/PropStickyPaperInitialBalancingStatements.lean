import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCompleteParentwiseMergeStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoarseShadingStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruningStatements

/-!
# Initial whole-cell balancing after the parentwise merge

After every complete parent fiber has supplied its one-parent output and the
source refinements have been merged, select one global cubical
point-multiplicity band.  Delete boundary-crossing whole `delta`-cells,
exactly balance the surviving cells in literal `rho`-cells, and induce the
first coarse shading.

The boundary-layer and crop estimates are explicit premises.  Their later
small-scale absorption is not hidden in this finite/geometric package.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperGlobalMultiplicityBandData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine) where
  level : ℕ
  band : WZ1PaperTubeShading fine
  band_eq :
    band = wz1PaperDyadicBandSubshading shading level
  band_cubical : WZ1PaperIsCubicalShading band
  band_mass_retention :
    shading.mass /
          ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) ≤
      band.mass
  band_multiplicity :
    ∀ point ∈ band.union,
      (2 ^ level : ENNReal) ≤
          (band.pointMultiplicity point : ENNReal) ∧
        (band.pointMultiplicity point : ENNReal) <
          (2 ^ (level + 1) : ENNReal)

structure WZ2PaperInitialBalancingData
    {delta rho sigma strongLoss outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (heavy : WZ2PaperHeavyParentSelectionData cover shading)
    (hrho : 0 < rho)
    (logExponent : ℕ)
    (ambientFiberData :
      ∀ parent :
          Fin (cover.hitParentSubfamily heavy.selected).family.card,
        WZ2PaperLiteralLemma3_3Data
          (sigma := sigma)
          (strongLoss := strongLoss)
          (outputLoss := outputLoss)
          (restrictPaperShading
            (cover.fullFiberSubfamily
              ((cover.hitParentSubfamily heavy.selected).embedding
                parent))
            shading)
          ((cover.hitParentSubfamily heavy.selected).family.tube parent)
          hrho logExponent)
    (parentwise :
      WZ2PaperCompleteParentwiseMergeData
        cover shading heavy hrho logExponent ambientFiberData)
    (bandData :
      WZ2PaperGlobalMultiplicityBandData
        parentwise.parentwise.merged.refinement.refined)
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
      parentwise.parentwise.restrictedCover
      pruning.pruned pruning.coarseCells
      pruning.availableFineCells balancing

def WZ2PaperInitialBalancingStatement : Prop :=
  ∀ {delta rho sigma strongLoss outputLoss : ℝ},
    ∀ (hdelta : 0 < delta),
      ∀ (hrho : 0 < rho),
        delta ≤ rho →
        rho ≤ 1 →
        18 * delta ≤ rho →
        ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
          ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
            ∀ (cover : WZ2PaperPartitioningCover fine coarse),
              ∀ (shading : WZ1PaperTubeShading fine),
                ∀ (heavy :
                    WZ2PaperHeavyParentSelectionData cover shading),
                  ∀ (logExponent : ℕ),
                    ∀ (ambientFiberData :
                        ∀ parent :
                            Fin
                              (cover.hitParentSubfamily
                                heavy.selected).family.card,
                          WZ2PaperLiteralLemma3_3Data
                            (sigma := sigma)
                            (strongLoss := strongLoss)
                            (outputLoss := outputLoss)
                            (restrictPaperShading
                              (cover.fullFiberSubfamily
                                ((cover.hitParentSubfamily
                                  heavy.selected).embedding parent))
                              shading)
                            ((cover.hitParentSubfamily
                              heavy.selected).family.tube parent)
                            hrho logExponent),
                      ∀ (parentwise :
                          WZ2PaperCompleteParentwiseMergeData
                            cover shading heavy hrho logExponent
                            ambientFiberData),
                        WZ1PaperIsLineClass
                          parentwise.parentwise.merged.refinement.selected.family →
                        WZ1PaperIsLineClass
                          (cover.hitParentSubfamily
                            heavy.selected).family →
                        ∀ (bandData :
                            WZ2PaperGlobalMultiplicityBandData
                              (parentwise.parentwise.merged.refinement
                                |>.refined)),
                          (2 ^ (bandData.level + 1) : ENNReal) *
                              ENNReal.ofReal (1000 * delta / rho) <
                            bandData.band.mass →
                        (∀ cell : WZ2PaperCellIndex,
                          wz1PaperGridCube rho cell ⊆
                            Kakeya.Streamlined.axisBox 2 2 2) →
                        Nonempty
                          (WZ2PaperInitialBalancingData
                            cover shading heavy hrho logExponent
                            ambientFiberData parentwise bandData hdelta)

end Kakeya.Assouad

end
