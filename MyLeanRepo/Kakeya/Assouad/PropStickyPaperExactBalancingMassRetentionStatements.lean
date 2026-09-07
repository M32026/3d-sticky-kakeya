import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruningStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingStatements

/-!
# Shaded-mass retention through exact whole-cell balancing

The paper first puts the fine shading in one dyadic point-multiplicity band.
It then deletes whole `delta`-cells crossing the `rho`-grid and keeps the same
number of surviving whole `delta`-cells in every retained `rho`-cell.

This module freezes the quantitative bridge between those operations.  Since
both restrictions are global whole-cell restrictions, point multiplicity on
the retained union is unchanged.  The equal-count pigeonhole therefore
converts directly into shaded-mass retention.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperExactBalancingMassRetentionData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta)
    (multiplicityCap : ENNReal)
    (pruning :
      WZ2PaperBoundaryCellPruningData
        (rho := rho) shading hdelta multiplicityCap)
    (balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) pruning.pruned pruning.coarseCells
        pruning.availableFineCells)
    (multiplicityLevel : ℕ) where
  pointMultiplicity_eq :
    ∀ point ∈ balancing.refined.union,
      balancing.refined.pointMultiplicity point =
        shading.pointMultiplicity point
  refined_multiplicity_band :
    ∀ point ∈ balancing.refined.union,
      (2 ^ multiplicityLevel : ENNReal) ≤
          (balancing.refined.pointMultiplicity point : ENNReal) ∧
        (balancing.refined.pointMultiplicity point : ENNReal) <
          (2 ^ (multiplicityLevel + 1) : ENNReal)
  mass_retention :
    let availableCellCount :=
      ∑ coarseCell ∈ pruning.coarseCells,
        (pruning.availableFineCells coarseCell).card
    pruning.pruned.mass ≤
      ((4 : ENNReal) *
          ((Nat.log 2 availableCellCount + 1 : ℕ) : ENNReal)) *
        balancing.refined.mass

def WZ2PaperExactBalancingMassRetentionStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ (hdelta : 0 < delta),
      ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
        ∀ (shading : WZ1PaperTubeShading fine),
          ∀ (multiplicityLevel : ℕ),
            (∀ point ∈ shading.union,
              (2 ^ multiplicityLevel : ENNReal) ≤
                  (shading.pointMultiplicity point : ENNReal) ∧
                (shading.pointMultiplicity point : ENNReal) <
                  (2 ^ (multiplicityLevel + 1) : ENNReal)) →
            ∀ (multiplicityCap : ENNReal),
              ∀ (pruning :
                  WZ2PaperBoundaryCellPruningData
                    (rho := rho) shading hdelta multiplicityCap),
                ∀ (balancing :
                    WZ2PaperExactCellBalancingData
                      (rho := rho) pruning.pruned pruning.coarseCells
                      pruning.availableFineCells),
                  Nonempty
                    (WZ2PaperExactBalancingMassRetentionData
                      shading hdelta multiplicityCap pruning balancing
                      multiplicityLevel)

end Kakeya.Assouad

end
