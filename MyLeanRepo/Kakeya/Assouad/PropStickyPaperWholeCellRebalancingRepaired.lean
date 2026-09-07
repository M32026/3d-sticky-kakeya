import MyLeanRepo.Kakeya.Assouad.PropStickyPaperWholeCellRebalancingRepairedStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruning
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancing
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCropCellPruning
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoarseShading
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment

/-! # Repaired whole-cell rebalancing with crop pruning -/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

private theorem pointMultiplicity_le_of_carrier_subset
    {family : Kakeya.Streamlined.BodyFamily}
    (first second : Kakeya.Streamlined.Shading family)
    (hcarrier :
      ∀ index, first.carrier index ⊆ second.carrier index)
    (point : Point3) :
    (first.pointMultiplicity point : ENNReal) ≤
      (second.pointMultiplicity point : ENNReal) := by
  classical
  exact_mod_cast
    Finset.card_le_card
      (show
        (Finset.univ.filter fun index =>
          point ∈ first.carrier index) ⊆
        (Finset.univ.filter fun index =>
          point ∈ second.carrier index) by
        intro index hindex
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,
            hcarrier index (Finset.mem_filter.mp hindex).2⟩)

structure WZ2PaperWholeCellRebalancingFromPruningData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (bandData : WZ2PaperGlobalMultiplicityBandData shading)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (boundaryPruning :
      WZ2PaperBoundaryCellPruningData
        (rho := rho) bandData.band hdelta
        (2 ^ (bandData.level + 1) : ENNReal)) where
  rebalancing :
    WZ2PaperWholeCellRebalancingRepairedData
      cover shading bandData hdelta hrho
  boundaryPruning_heq :
    HEq rebalancing.boundaryPruning boundaryPruning
  boundaryPruning_pruned_mass_eq :
    rebalancing.boundaryPruning.pruned.mass =
      boundaryPruning.pruned.mass

theorem wz2_paper_whole_cell_rebalancing_repaired_from_pruning
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hscale : 18 * delta ≤ rho)
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (fineLine : WZ1PaperIsLineClass fine)
    (coarseLine : WZ1PaperIsLineClass coarse)
    (shading : WZ1PaperTubeShading fine)
    (bandData : WZ2PaperGlobalMultiplicityBandData shading)
    (boundaryPruning :
      WZ2PaperBoundaryCellPruningData
        (rho := rho) bandData.band hdelta
        (2 ^ (bandData.level + 1) : ENNReal))
    (hCropBoundary :
      ∀ initialBalancing :
          WZ2PaperExactCellBalancingData
            (rho := rho)
            boundaryPruning.pruned
            boundaryPruning.coarseCells
            boundaryPruning.availableFineCells,
        (∑ index : Fin fine.card,
            volume
              (initialBalancing.refined.carrier index ∩
                wz2PaperCropBoundaryRegion rho)) <
          initialBalancing.refined.mass) :
    Nonempty
      (WZ2PaperWholeCellRebalancingFromPruningData
        cover shading bandData hdelta hrho boundaryPruning) := by
  let multiplicityCap : ENNReal :=
    (2 ^ (bandData.level + 1) : ENNReal)
  have hCap :
      ∀ point,
        (bandData.band.pointMultiplicity point : ENNReal) ≤
          multiplicityCap := by
    intro point
    by_cases hpoint : point ∈ bandData.band.union
    · exact (bandData.band_multiplicity point hpoint).2.le
    · have hzero :
          bandData.band.pointMultiplicity point = 0 := by
        classical
        simp [Kakeya.Streamlined.Shading.pointMultiplicity,
          show ∀ index, point ∉ bandData.band.carrier index by
            intro index hindex
            exact hpoint ⟨index, hindex⟩]
      rw [hzero]
      simp
  rcases
      wz2_prop_sticky_exact_cell_balancing
        hdelta hrho boundaryPruning.pruned
        boundaryPruning.pruned_cubical
        boundaryPruning.coarseCells
        boundaryPruning.coarseCells_nonempty
        boundaryPruning.availableFineCells
        boundaryPruning.availableFineCells_nonempty
        boundaryPruning.availableFineCells_ready
    with ⟨initialBalancing⟩
  have hInitialCap :
      ∀ point,
        (initialBalancing.refined.pointMultiplicity point : ENNReal) ≤
          multiplicityCap := by
    intro point
    have hSub :
        (initialBalancing.refined.pointMultiplicity point : ENNReal) ≤
          (boundaryPruning.pruned.pointMultiplicity point : ENNReal) :=
      pointMultiplicity_le_of_carrier_subset
        initialBalancing.refined
        boundaryPruning.pruned
        initialBalancing.refined_subshading point
    have hPruned :
        (boundaryPruning.pruned.pointMultiplicity point : ENNReal) ≤
          (bandData.band.pointMultiplicity point : ENNReal) :=
      pointMultiplicity_le_of_carrier_subset
        boundaryPruning.pruned bandData.band
        boundaryPruning.pruned_subshading point
    exact hSub.trans (hPruned.trans (hCap point))
  rcases
      wz2_paper_crop_cell_pruning_from_boundary_mass
        hdelta hrho hrhoOne
        boundaryPruning.pruned boundaryPruning.coarseCells
        boundaryPruning.availableFineCells initialBalancing
        multiplicityCap hInitialCap
        (hCropBoundary initialBalancing)
    with ⟨cropPruning⟩
  rcases
      wz2_prop_sticky_paper_coarse_shading
        wz2_prop_sticky_coarse_cell_containment
        hdelta hrho hscale cover fineLine coarseLine
        cropPruning.refined cropPruning.refined_cubical
        cropPruning.retainedCoarseCells
        cropPruning.retainedCoarseCells_nonempty
        cropPruning.selectedFineCells
        (by
          intro cell hcell
          have hcellInitial :
              cell ∈ initialBalancing.retainedCoarseCells := by
            rw [cropPruning.retainedCoarseCells_eq] at hcell
            exact (Finset.mem_filter.mp hcell).1
          have hcard :=
            initialBalancing.selectedFineCells_card
              cell hcellInitial
          have hpositive :
              0 <
                (initialBalancing.selectedFineCells cell).card := by
            rw [hcard]
            exact Nat.pow_pos (by norm_num)
          rw [cropPruning.selectedFineCells_eq cell]
          exact Finset.card_pos.mp hpositive)
        (by
          intro cell hcell fineCell hfine
          exact
            ⟨by
              let point : Point3 := cellCorner delta fineCell
              have hp : point ∈ wz1PaperGridCube delta fineCell :=
                cellCorner_mem_gridCube hdelta fineCell
              have hpointUnion : point ∈ cropPruning.refined.union := by
                rw [cropPruning.refined_union_eq]
                exact Set.mem_iUnion₂.mpr
                  ⟨fineCell,
                    by
                      rw [cropPruning.retainedFineCells_eq]
                      exact Finset.mem_biUnion.mpr
                        ⟨cell, hcell, hfine⟩,
                    hp⟩
              rw [mem_wz1PaperActiveCells]
              have hindex :
                  wz1PaperGridIndex delta point = fineCell :=
                (mem_wz1PaperGridCube delta fineCell point).mp hp
              exact
                ⟨by
                  rw [← hindex]
                  exact paper_point_gridIndex_in_window hdelta
                    (shading_union_subset_axisBox hpointUnion),
                  ⟨point, hpointUnion, hp⟩⟩,
              initialBalancing.fine_cell_containment
                cell
                (by
                  rw [cropPruning.retainedCoarseCells_eq] at hcell
                  exact (Finset.mem_filter.mp hcell).1)
                fineCell
                (by
                  rw [cropPruning.selectedFineCells_eq cell] at hfine
                  exact hfine)⟩)
        (by
          simpa using cropPruning.croppedBalancing)
        (by
          intro cell hcell
          exact cropPruning.crop cell hcell)
    with ⟨coarseData⟩
  let rebalancing :
      WZ2PaperWholeCellRebalancingRepairedData
        cover shading bandData hdelta hrho :=
    {
      multiplicityCap := multiplicityCap
      multiplicityCap_eq := rfl
      boundaryPruning := boundaryPruning
      initialBalancing := initialBalancing
      cropPruning := cropPruning
      coarseData := coarseData
    }
  exact
    ⟨{
      rebalancing := rebalancing
      boundaryPruning_heq := by rfl
      boundaryPruning_pruned_mass_eq := rfl
    }⟩

theorem wz2_paper_whole_cell_rebalancing_repaired :
    WZ2PaperWholeCellRebalancingRepairedStatement := by
  intro delta rho hdelta hrho hdeltaRho hrhoOne hscale
    fine coarse cover fineLine coarseLine shading bandData
    hBoundary hCropAbsorb
  let multiplicityCap : ENNReal :=
    (2 ^ (bandData.level + 1) : ENNReal)
  have hCap :
      ∀ point,
        (bandData.band.pointMultiplicity point : ENNReal) ≤
          multiplicityCap := by
    intro point
    by_cases hpoint : point ∈ bandData.band.union
    · exact (bandData.band_multiplicity point hpoint).2.le
    · have hzero :
          bandData.band.pointMultiplicity point = 0 := by
        classical
        simp [Kakeya.Streamlined.Shading.pointMultiplicity,
          show ∀ index, point ∉ bandData.band.carrier index by
            intro index hindex
            exact hpoint ⟨index, hindex⟩]
      rw [hzero]
      simp
  rcases
      wz2_prop_sticky_boundary_cell_pruning
        hdelta hdeltaRho hrho hrhoOne
        bandData.band bandData.band_cubical
        multiplicityCap hCap hBoundary
    with ⟨boundaryPruning⟩
  have hCropBoundary :
      ∀ initialBalancing :
          WZ2PaperExactCellBalancingData
            (rho := rho)
            boundaryPruning.pruned
            boundaryPruning.coarseCells
            boundaryPruning.availableFineCells,
        (∑ index : Fin fine.card,
            volume
              (initialBalancing.refined.carrier index ∩
                wz2PaperCropBoundaryRegion rho)) <
          initialBalancing.refined.mass := by
    intro initialBalancing
    exact
      (wz2_paper_crop_boundary_mass_le_of_multiplicity_cap
        hrho initialBalancing.refined
        (2 ^ (bandData.level + 1) : ENNReal)
        (by
          intro point
          exact
            pointMultiplicity_le_of_carrier_subset
              initialBalancing.refined boundaryPruning.pruned
              initialBalancing.refined_subshading point
            |>.trans <|
              pointMultiplicity_le_of_carrier_subset
                boundaryPruning.pruned bandData.band
                boundaryPruning.pruned_subshading point
            |>.trans <| by
              by_cases hpoint : point ∈ bandData.band.union
              · exact (bandData.band_multiplicity point hpoint).2.le
              · have hzero :
                    bandData.band.pointMultiplicity point = 0 := by
                  classical
                  simp [Kakeya.Streamlined.Shading.pointMultiplicity,
                    show ∀ index,
                        point ∉ bandData.band.carrier index by
                      intro index hindex
                      exact hpoint ⟨index, hindex⟩]
                rw [hzero]
                simp)).trans_lt
        (hCropAbsorb boundaryPruning initialBalancing)
  exact
    (wz2_paper_whole_cell_rebalancing_repaired_from_pruning
      hdelta hrho hrhoOne hscale
      cover fineLine coarseLine shading bandData boundaryPruning
      hCropBoundary).map
        WZ2PaperWholeCellRebalancingFromPruningData.rebalancing

theorem wz2_paper_whole_cell_rebalancing_from_boundary_mass :
    WZ2PaperWholeCellRebalancingFromBoundaryMassStatement := by
  intro delta rho hdelta hrho hdeltaRho hrhoOne hscale
    fine coarse cover fineLine coarseLine shading bandData
    hBoundary hCropBoundary
  let multiplicityCap : ENNReal :=
    (2 ^ (bandData.level + 1) : ENNReal)
  have hCap :
      ∀ point,
        (bandData.band.pointMultiplicity point : ENNReal) ≤
          multiplicityCap := by
    intro point
    by_cases hpoint : point ∈ bandData.band.union
    · exact (bandData.band_multiplicity point hpoint).2.le
    · have hzero :
          bandData.band.pointMultiplicity point = 0 := by
        classical
        simp [Kakeya.Streamlined.Shading.pointMultiplicity,
          show ∀ index, point ∉ bandData.band.carrier index by
            intro index hindex
            exact hpoint ⟨index, hindex⟩]
      rw [hzero]
      simp
  rcases
      wz2_paper_boundary_cell_pruning_of_crossing_mass
        hdelta hdeltaRho hrho hrhoOne
        bandData.band bandData.band_cubical
        multiplicityCap hCap hBoundary with
    ⟨boundaryPruning⟩
  exact
    (wz2_paper_whole_cell_rebalancing_repaired_from_pruning
      hdelta hrho hrhoOne hscale
      cover fineLine coarseLine shading bandData boundaryPruning
      (hCropBoundary boundaryPruning)).map
        WZ2PaperWholeCellRebalancingFromPruningData.rebalancing

end Kakeya.Assouad

end
