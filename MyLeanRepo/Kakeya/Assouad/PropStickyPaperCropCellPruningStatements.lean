import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCropBoundaryGeometry

/-!
# Delete coarse cells that cross the cropped paper window

After exact cell balancing, delete every retained side-`rho` cell that is not
contained in `[-1,1]^3`, together with all of its selected whole `delta`
cells.  The surviving data remains exactly balanced with the same cell mass.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure WZ2PaperCropCellPruningData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (coarseCells : Finset WZ2PaperCellIndex)
    (availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex)
    (balanced :
      WZ2PaperExactCellBalancingData
        (rho := rho) shading coarseCells availableFineCells)
    (multiplicityCap : ENNReal) where
  retainedCoarseCells : Finset WZ2PaperCellIndex
  retainedCoarseCells_eq :
    retainedCoarseCells =
      balanced.retainedCoarseCells.filter fun cell =>
        wz1PaperGridCube rho cell ⊆
          Kakeya.Streamlined.axisBox 2 2 2
  retainedCoarseCells_nonempty : retainedCoarseCells.Nonempty
  selectedFineCells :
    WZ2PaperCellIndex → Finset WZ2PaperCellIndex
  selectedFineCells_eq :
    ∀ cell,
      selectedFineCells cell =
        balanced.selectedFineCells cell
  retainedFineCells : Finset WZ2PaperCellIndex
  retainedFineCells_eq :
    retainedFineCells =
      retainedCoarseCells.biUnion selectedFineCells
  refined : WZ1PaperTubeShading fine
  refined_eq :
    refined =
      wz2RefinedShading balanced.refined retainedFineCells
  refined_subshading :
    ∀ index, refined.carrier index ⊆ balanced.refined.carrier index
  refined_cubical : WZ1PaperIsCubicalShading refined
  refined_union_eq :
    refined.union =
      ⋃ fineCell ∈ retainedFineCells,
        wz1PaperGridCube delta fineCell
  croppedBalancing :
    WZ2PaperExactCellBalancingData
      (rho := rho) refined retainedCoarseCells selectedFineCells
  croppedBalancing_refined_eq :
    croppedBalancing.refined = refined
  crop :
    ∀ cell ∈ croppedBalancing.retainedCoarseCells,
      wz1PaperGridCube rho cell ⊆
        Kakeya.Streamlined.axisBox 2 2 2
  source_mass_le_boundary :
    balanced.refined.mass ≤
      refined.mass +
        ∑ index : Fin fine.card,
          MeasureTheory.volume
            (balanced.refined.carrier index ∩
              wz2PaperCropBoundaryRegion rho)
  source_mass_le :
    balanced.refined.mass ≤
      refined.mass +
        multiplicityCap *
          ENNReal.ofReal (48 * rho)

/--
Crop pruning from a direct aggregate shaded-mass estimate on the crop
boundary.  This is the quantitative interface used by the paper-facing CWA
route; the pointwise cap is retained only to populate the historical explicit
`48 * rho` output bound.
-/
def WZ2PaperCropCellPruningFromBoundaryMassStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ (hdelta : 0 < delta),
      ∀ (hrho : 0 < rho),
        rho ≤ 1 →
        ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
          ∀ (shading : WZ1PaperTubeShading fine),
            ∀ (coarseCells : Finset WZ2PaperCellIndex),
              ∀ (availableFineCells :
                  WZ2PaperCellIndex → Finset WZ2PaperCellIndex),
                ∀ (balanced :
                    WZ2PaperExactCellBalancingData
                      (rho := rho) shading coarseCells
                      availableFineCells),
                  ∀ (multiplicityCap : ENNReal),
                    (∀ point,
                      (balanced.refined.pointMultiplicity point : ENNReal) ≤
                        multiplicityCap) →
                    (∑ index : Fin fine.card,
                        MeasureTheory.volume
                          (balanced.refined.carrier index ∩
                            wz2PaperCropBoundaryRegion rho)) <
                      balanced.refined.mass →
                    Nonempty
                      (WZ2PaperCropCellPruningData
                        shading coarseCells availableFineCells
                        balanced multiplicityCap)

def WZ2PaperCropCellPruningStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ (hdelta : 0 < delta),
      ∀ (hrho : 0 < rho),
        rho ≤ 1 →
        ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
          ∀ (shading : WZ1PaperTubeShading fine),
            ∀ (coarseCells : Finset WZ2PaperCellIndex),
              ∀ (availableFineCells :
                  WZ2PaperCellIndex → Finset WZ2PaperCellIndex),
                ∀ (balanced :
                    WZ2PaperExactCellBalancingData
                      (rho := rho) shading coarseCells
                      availableFineCells),
                  ∀ (multiplicityCap : ENNReal),
                    (∀ point,
                      (balanced.refined.pointMultiplicity point : ENNReal) ≤
                        multiplicityCap) →
                    multiplicityCap *
                        ENNReal.ofReal (48 * rho) <
                      balanced.refined.mass →
                    Nonempty
                      (WZ2PaperCropCellPruningData
                        shading coarseCells availableFineCells
                        balanced multiplicityCap)

end Kakeya.Assouad

end
