import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSCinematicGlobalizationStatement

/-!
# Cinematic finite-cell globalization

Globalize one local cinematic projected-area certificate across the prepared
uniform occupied cells without division.
-/

namespace Kakeya.Assouad

theorem projected_fiber_os_cinematic_globalization :
    ProjectedFiberOSCinematicGlobalizationStatement := by
  intro h_corr_count h_cell_sel delta eta rho F Y f prepared level cellSystem g
    slopeBlocks radiusBlocks hlip r hr hr' localSet hlocal1 hlocal2 L hL
  classical
  -- Step 1: Cell selection gives cardinality comparison and local-set containment
  have h_sel := h_cell_sel (F := F) (Y := Y) (f := f) prepared level cellSystem g r hr
    localSet hlocal1 hlocal2
  have h_card1 : (projectedFiberOSCinematicCells prepared level g r).card ≤
      (planarGridCinematicCorridorCells prepared.base level prepared.atomized.centers g
        (projectedFiberOSCinematicExpandedRadius prepared r)).card := h_sel.1
  have h_local : localSet ⊆ finiteAtomUnion
      (projectedFiberOSCinematicCells prepared level g r)
      (projectedFiberOSPreparedCellSet prepared) := h_sel.2
  -- Step 2: Base ≥ 2 and expanded radius non-negativity
  have hbase2 : 2 ≤ prepared.base := by linarith [prepared.base_ge_three]
  have hr'_nonneg : 0 ≤ projectedFiberOSCinematicExpandedRadius prepared r := by
    simp only [projectedFiberOSCinematicExpandedRadius]
    have h2 : 0 < ((prepared.base ^ prepared.levels : ℝ)⁻¹) := by
      apply inv_pos.mpr
      positivity
    linarith
  -- Step 3: Corridor count bounds the planar grid corridor cells by M
  have h_corr : (planarGridCinematicCorridorCells prepared.base level prepared.atomized.centers g
        (projectedFiberOSCinematicExpandedRadius prepared r)).card ≤
      projectedFiberOSCinematicCellBound prepared.base level slopeBlocks radiusBlocks :=
    h_corr_count prepared.atomized.centers prepared.base level slopeBlocks radiusBlocks
      hbase2 g hlip (projectedFiberOSCinematicExpandedRadius prepared r) hr'_nonneg hr'
  -- Step 4: Transitivity gives selected.card ≤ M
  have h_card : (projectedFiberOSCinematicCells prepared level g r).card ≤
      projectedFiberOSCinematicCellBound prepared.base level slopeBlocks radiusBlocks :=
    le_trans h_card1 h_corr
  -- Step 5: selected cells are a subset of all occupied cells
  have hsel : projectedFiberOSCinematicCells prepared level g r ⊆
      projectedFiberOSOccupiedCells prepared level := by
    exact Finset.filter_subset _ _
  -- Step 6: 0 ≤ rho from coarse mesh bound
  have hrho : 0 ≤ rho := by
    have h1 : ((prepared.base ^ level : ℝ)⁻¹) ≤ rho := cellSystem.coarse_mesh_le
    have h2 : 0 < ((prepared.base ^ level : ℝ)⁻¹) := by
      apply inv_pos.mpr
      positivity
    linarith
  -- Step 7: Apply finite uniform cell globalization
  exact finite_uniform_cell_globalization
    (α := DiscreteSet 2)
    (cells := projectedFiberOSOccupiedCells prepared level)
    cellSystem.cells_nonempty
    (cellSet := projectedFiberOSPreparedCellSet prepared)
    cellSystem.cell_measurable
    cellSystem.cell_disjoint
    cellSystem.cell_area_nonzero
    (R := 4)
    cellSystem.cell_area_comparable
    (globalSet := twistedUnion prepared.density.globalShading f)
    cellSystem.global_eq
    rho hrho
    (V := projectedFiberOSPreparedCellThickeningBound prepared rho)
    cellSystem.cell_thickening_bound
    (selected := projectedFiberOSCinematicCells prepared level g r)
    hsel
    (M := projectedFiberOSCinematicCellBound prepared.base level slopeBlocks radiusBlocks)
    h_card
    localSet h_local
    L hL

end Kakeya.Assouad
