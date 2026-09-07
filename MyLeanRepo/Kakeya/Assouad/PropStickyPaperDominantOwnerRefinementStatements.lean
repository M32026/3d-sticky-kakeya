import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantOwnerExactificationStatements

/-!
# Global refinement through dominant-owner exactification

The exact balanced shading first pays the balanced parent-degree bound, then
the dominant-cell dyadic selection, and finally the equal owned-cell count
selection.  Every finite loss is explicit.
-/

noncomputable section

namespace Kakeya.Assouad

def wz2PaperDominantOwnerLoss
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {active :
      WZ2PaperBalancedActiveParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData hdelta hrho}
    {multiplicityLevel : ℕ}
    {degree :
      WZ2PaperBalancedParentDegreeData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel}
    {dominant :
      WZ2PaperDominantParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree}
    {owned :
      WZ2PaperDominantParentFineCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree dominant}
    (exactified :
      WZ2PaperDominantOwnerExactificationData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree
        dominant owned) : ENNReal :=
  ((2 ^ (multiplicityLevel + 1) : ENNReal) *
      (2 *
        (wz2PaperBalancedParentDegreeCap
          balancing multiplicityLevel : ENNReal))) *
    (2 *
      ((Nat.log 2
          (2 * balancing.retainedCoarseCells.card) + 1 : ℕ) :
        ENNReal)) *
    (4 *
      (2 ^ (multiplicityLevel + 1) : ENNReal) *
      (exactified.countBins : ENNReal))

structure WZ2PaperDominantOwnerRefinementData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {active :
      WZ2PaperBalancedActiveParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData hdelta hrho}
    {multiplicityLevel : ℕ}
    {degree :
      WZ2PaperBalancedParentDegreeData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel}
    {dominant :
      WZ2PaperDominantParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree}
    {owned :
      WZ2PaperDominantParentFineCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree dominant}
    (exactified :
      WZ2PaperDominantOwnerExactificationData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree
        dominant owned)
    (logExponent : ℕ) where
  source_mass_le :
    balancing.refined.mass ≤
      wz2PaperDominantOwnerLoss exactified *
        exactified.refined.mass
  retained_mass :
    wz1PaperRefinementFraction delta logExponent *
        balancing.refined.mass ≤
      exactified.refined.mass

namespace WZ2PaperDominantOwnerRefinementData

noncomputable def toRefinement
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {active :
      WZ2PaperBalancedActiveParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData hdelta hrho}
    {multiplicityLevel : ℕ}
    {degree :
      WZ2PaperBalancedParentDegreeData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel}
    {dominant :
      WZ2PaperDominantParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree}
    {owned :
      WZ2PaperDominantParentFineCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree dominant}
    {exactified :
      WZ2PaperDominantOwnerExactificationData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree
        dominant owned}
    {logExponent : ℕ}
    (data :
      WZ2PaperDominantOwnerRefinementData
        exactified logExponent) :
    WZ1PaperRefinement balancing.refined logExponent where
  selected := exactified.selected
  refined := exactified.refined
  subshading index := by
    rw [exactified.refined_carrier_eq index]
    exact Set.inter_subset_left
  retained_mass := data.retained_mass

end WZ2PaperDominantOwnerRefinementData

def WZ2PaperDominantOwnerRefinementStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ {cover : WZ2PaperPartitioningCover fine coarse},
          ∀ {sourceShading : WZ1PaperTubeShading fine},
            ∀ {coarseCells : Finset WZ2PaperCellIndex},
              ∀ {availableFineCells :
                  WZ2PaperCellIndex → Finset WZ2PaperCellIndex},
                ∀ {balancing :
                    WZ2PaperExactCellBalancingData
                      (rho := rho) sourceShading coarseCells
                      availableFineCells},
                  ∀ {coarseData :
                      WZ2PaperCoarseShadingData
                        cover sourceShading coarseCells
                        availableFineCells balancing},
                    ∀ {hdelta : 0 < delta},
                      ∀ {hrho : 0 < rho},
                        ∀ {active :
                            WZ2PaperBalancedActiveParentCellsData
                              cover sourceShading coarseCells
                              availableFineCells balancing coarseData
                              hdelta hrho},
                          ∀ {multiplicityLevel : ℕ},
                            ∀ (degree :
                                WZ2PaperBalancedParentDegreeData
                                  cover sourceShading coarseCells
                                  availableFineCells balancing coarseData
                                  active multiplicityLevel),
                              ∀ (dominant :
                                  WZ2PaperDominantParentCellsData
                                    cover sourceShading coarseCells
                                    availableFineCells balancing coarseData
                                    active multiplicityLevel degree),
                                ∀ {owned :
                                    WZ2PaperDominantParentFineCellsData
                                      cover sourceShading coarseCells
                                      availableFineCells balancing coarseData
                                      active multiplicityLevel degree
                                      dominant},
                                  ∀ (exactified :
                                      WZ2PaperDominantOwnerExactificationData
                                        cover sourceShading coarseCells
                                        availableFineCells balancing
                                        coarseData active multiplicityLevel
                                        degree dominant owned),
                                    ∀ (logExponent : ℕ),
                                      wz1PaperRefinementFraction
                                            delta logExponent *
                                          wz2PaperDominantOwnerLoss
                                            exactified ≤
                                        1 →
                                      Nonempty
                                        (WZ2PaperDominantOwnerRefinementData
                                          exactified logExponent)

end Kakeya.Assouad

end
