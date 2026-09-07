import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedActiveParentCellsStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFiberMultiplicityBandStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization.WeightBinning

/-!
# Common incidence-mass band for active parent-cell pairs

Select one dyadic band of the positive shaded incidence masses carried by
active coarse-parent/literal-`rho`-cell pairs.  The parent-cell weight is the
additive quantity

`sum_{T in fiber(parent)} |Y(T) intersect Q|`.

The output retains a logarithmic fraction of the total active incidence mass
and gives one common interval `[fiberCellMass, 2 * fiberCellMass]`.

This is intentionally only an incidence-pair selection.  A downstream step
must synchronize it by whole-cell restriction before rebuilding a balanced
cover.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

def wz2PaperParentCellPairs
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
        (rho := rho) sourceShading coarseCells
        availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells
        availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (active :
      WZ2PaperBalancedActiveParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData hdelta hrho) :
    Finset (WZ2PaperCellIndex × Fin coarse.card) :=
  balancing.retainedCoarseCells.biUnion fun cell =>
    (active.activeParents cell).image fun parent => (cell, parent)

def wz2PaperPositiveParentCellPairs
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
        (rho := rho) sourceShading coarseCells
        availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells
        availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (active :
      WZ2PaperBalancedActiveParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData hdelta hrho)
    (shading : WZ1PaperTubeShading fine) :
    Finset (WZ2PaperCellIndex × Fin coarse.card) :=
  (wz2PaperParentCellPairs active).filter fun pair =>
    wz2PaperParentCellMass cover shading pair ≠ 0

structure WZ2PaperParentCellMassBandData
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
        cover balancing.refined) where
  level : ℕ
  retainedPairs :
    Finset (WZ2PaperCellIndex × Fin coarse.card)
  retainedPairs_subset :
    retainedPairs ⊆
      wz2PaperPositiveParentCellPairs active fiberBand.refined
  retainedPairs_nonempty :
    retainedPairs.Nonempty
  total_pair_mass_eq :
    (∑ pair ∈
        wz2PaperPositiveParentCellPairs active fiberBand.refined,
        wz2PaperParentCellMass cover fiberBand.refined pair) =
      ∑ cell ∈ balancing.retainedCoarseCells,
        wz2PaperCellIncidenceMass
          (rho := rho) fiberBand.refined cell
  total_pair_mass_pos :
    0 <
      ∑ pair ∈
          wz2PaperPositiveParentCellPairs active fiberBand.refined,
        wz2PaperParentCellMass cover fiberBand.refined pair
  total_pair_mass_ne_top :
    (∑ pair ∈
        wz2PaperPositiveParentCellPairs active fiberBand.refined,
        wz2PaperParentCellMass cover fiberBand.refined pair) ≠
      ⊤
  fiberCellMass : ENNReal
  fiberCellMass_pos : 0 < fiberCellMass
  fiberCellMass_ne_top : fiberCellMass ≠ ⊤
  mass_band :
    ∀ pair ∈ retainedPairs,
      fiberCellMass ≤
          wz2PaperParentCellMass cover fiberBand.refined pair ∧
        wz2PaperParentCellMass cover fiberBand.refined pair ≤
          2 * fiberCellMass
  retained_mass :
    (∑ pair ∈
        wz2PaperPositiveParentCellPairs active fiberBand.refined,
        wz2PaperParentCellMass cover fiberBand.refined pair) /
          (2 *
            (Nat.log 2
                (2 *
                  (wz2PaperPositiveParentCellPairs
                    active fiberBand.refined).card) + 1) :
            ENNReal) ≤
      ∑ pair ∈ retainedPairs,
        wz2PaperParentCellMass cover fiberBand.refined pair

def WZ2PaperParentCellMassBandStatement : Prop :=
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
                            Nonempty
                              (WZ2PaperParentCellMassBandData
                                cover sourceShading coarseCells
                                availableFineCells balancing coarseData
                                active fiberBand)

end Kakeya.Assouad

end
