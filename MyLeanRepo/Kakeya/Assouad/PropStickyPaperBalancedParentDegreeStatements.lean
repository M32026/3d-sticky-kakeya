import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedActiveParentCellsStatements

/-!
# Degree bound for balanced parent-cell incidence

Each retained `rho`-cell contains exactly `2^balancing.level` selected
literal `delta`-cells.  Every active parent contributes at least one
`delta`-cube of shaded incidence mass.  On the other hand, finite Fubini and
the fine multiplicity band bound the total shaded incidence mass in the cell
by `2^(multiplicityLevel + 1)` times its union volume.  Hence the number of
active coarse parents is at most twice the explicit product below.
-/

noncomputable section

namespace Kakeya.Assouad

def wz2PaperBalancedParentDegreeCap
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    (balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells
        availableFineCells)
    (multiplicityLevel : ℕ) : ℕ :=
  2 ^ balancing.level * 2 ^ multiplicityLevel

structure WZ2PaperBalancedParentDegreeData
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
    (multiplicityLevel : ℕ) where
  degreeCap_pos :
    0 <
      wz2PaperBalancedParentDegreeCap
        balancing multiplicityLevel
  active_parent_degree :
    ∀ cell ∈ balancing.retainedCoarseCells,
      (active.activeParents cell).card ≤
        2 *
          wz2PaperBalancedParentDegreeCap
            balancing multiplicityLevel
  cell_incidence_upper :
    ∀ cell ∈ balancing.retainedCoarseCells,
      wz2PaperCellIncidenceMass
          (rho := rho) balancing.refined cell ≤
        (2 ^ (multiplicityLevel + 1) : ENNReal) *
          balancing.cellMass
  cell_mass_upper :
    balancing.cellMass ≤
      2 *
          (wz2PaperBalancedParentDegreeCap
            balancing multiplicityLevel : ENNReal) *
        active.fiberCellMass

def WZ2PaperBalancedParentDegreeStatement : Prop :=
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
                            (∀ point ∈ balancing.refined.union,
                              (balancing.refined.pointMultiplicity point :
                                  ENNReal) <
                                (2 ^ (multiplicityLevel + 1) :
                                  ENNReal)) →
                            Nonempty
                              (WZ2PaperBalancedParentDegreeData
                                cover sourceShading coarseCells
                                availableFineCells balancing coarseData
                                active multiplicityLevel)

end Kakeya.Assouad

end
