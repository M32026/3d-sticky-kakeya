import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSLevelCellSystemStatement

/-!
# Occupied projected-fiber cell system

Expose the exact finite occupied-cell decomposition at the grid level
comparable to a requested local scale.
-/

open MeasureTheory

namespace Kakeya.Assouad

theorem projected_fiber_os_level_cell_system :
    ProjectedFiberOSLevelCellSystemStatement :=
  fun h_level_sel h_thickening {delta eta} hδ_pos F Y f prepared rho hrho_pos hδ_rho hrho_one => by
  have hbase_ge_three : 3 ≤ prepared.base := prepared.base_ge_three
  have hbase_ge_two : 2 ≤ prepared.base := by linarith
  -- Step 1: Level selection
  rcases h_level_sel prepared.base prepared.levels hbase_ge_two delta hδ_pos
      prepared.atomic_mesh_lt rho hδ_rho hrho_one with
    ⟨level, hlevel_le, hmesh_le, hrho_lt_mesh⟩
  let occupiedCells := projectedFiberOSOccupiedCells prepared level
  let cellSet := projectedFiberOSPreparedCellSet prepared
  let atom := projectedFiberGridAtom prepared.bandData.band prepared.base prepared.levels
  have h_mesh_premise :
      ((prepared.base ^ prepared.levels : ℝ)⁻¹) < (prepared.base : ℝ) * rho := by
    have h1 : ((prepared.base ^ prepared.levels : ℝ)⁻¹) < (prepared.base : ℝ) * delta :=
      prepared.mesh_upper
    have h2 : (prepared.base : ℝ) * delta ≤ (prepared.base : ℝ) * rho := by
      gcongr
    linarith
  -- Partition helper: distinct cells are disjoint
  have h_partition_disjoint : ∀ (cell₁ cell₂ : DiscreteSet 2),
      cell₁ ∈ planarGridPartition prepared.base level prepared.atomized.centers →
      cell₂ ∈ planarGridPartition prepared.base level prepared.atomized.centers →
      cell₁ ≠ cell₂ → Disjoint cell₁ cell₂ := by
    intro cell₁ cell₂ h₁ h₂ hne
    rcases Finset.mem_image.mp h₁ with ⟨p₁, hp₁, rfl⟩
    rcases Finset.mem_image.mp h₂ with ⟨p₂, hp₂, rfl⟩
    by_contra h
    rw [Finset.not_disjoint_iff] at h
    rcases h with ⟨x, hx₁, hx₂⟩
    have h_idx1 : planarGridIndex prepared.base level x = planarGridIndex prepared.base level p₁ :=
      (Finset.mem_filter.mp hx₁).2
    have h_idx2 : planarGridIndex prepared.base level x = planarGridIndex prepared.base level p₂ :=
      (Finset.mem_filter.mp hx₂).2
    have h_eq : planarGridIndex prepared.base level p₁ = planarGridIndex prepared.base level p₂ := by
      rw [←h_idx1, h_idx2]
    have h_cell_eq : planarGridCell prepared.base level prepared.atomized.centers p₁ =
        planarGridCell prepared.base level prepared.atomized.centers p₂ := by
      simp only [planarGridCell, h_eq]
    exact hne h_cell_eq
  -- Every center belongs to its own occupied cell
  have h_center_in_occupied : ∀ (c : Point2), c ∈ prepared.uniform.centers →
      ∃ (cell : DiscreteSet 2), cell ∈ occupiedCells ∧ c ∈ prepared.uniform.centers ∩ cell := by
    intro c hc
    let cell := planarGridCell prepared.base level prepared.atomized.centers c
    have hc_atomized : c ∈ prepared.atomized.centers := prepared.uniform.centers_subset hc
    have hcell_in_partition : cell ∈ planarGridPartition prepared.base level prepared.atomized.centers := by
      apply Finset.mem_image.mpr
      exact ⟨c, hc_atomized, rfl⟩
    have hc_in_cell : c ∈ cell := by
      apply Finset.mem_filter.mpr
      exact ⟨hc_atomized, rfl⟩
    have h_nonempty : (prepared.uniform.centers ∩ cell).Nonempty := by
      exact ⟨c, Finset.mem_inter.mpr ⟨hc, hc_in_cell⟩⟩
    have hcell_occupied : cell ∈ occupiedCells := by
      simp only [occupiedCells, projectedFiberOSOccupiedCells, Finset.mem_filter]
      exact ⟨hcell_in_partition, h_nonempty⟩
    have hc_in_inter : c ∈ prepared.uniform.centers ∩ cell :=
      Finset.mem_inter.mpr ⟨hc, hc_in_cell⟩
    exact ⟨cell, hcell_occupied, hc_in_inter⟩
  -- Global equality
  have h_global_eq : twistedUnion prepared.density.globalShading f =
      finiteAtomUnion occupiedCells cellSet := by
    have h1 : twistedUnion prepared.density.globalShading f = prepared.uniform.retainedBand :=
      prepared.global_twisted_eq
    have h2 : prepared.uniform.retainedBand = finiteAtomUnion prepared.uniform.centers atom :=
      prepared.uniform.retainedBand_eq
    have h3 : finiteAtomUnion prepared.uniform.centers atom = finiteAtomUnion occupiedCells cellSet := by
      apply Set.Subset.antisymm
      · -- LHS ⊆ RHS
        intro x hx
        rcases Set.mem_iUnion₂.mp hx with ⟨c, hc, hxatom⟩
        rcases h_center_in_occupied c hc with ⟨cell, hcell_occ, hc_inter⟩
        apply Set.mem_iUnion₂.mpr
        exact ⟨cell, hcell_occ, Set.mem_iUnion₂.mpr ⟨c, hc_inter, hxatom⟩⟩
      · -- RHS ⊆ LHS
        intro x hx
        rcases Set.mem_iUnion₂.mp hx with ⟨cell, _hcell_occ, hxcell⟩
        rcases Set.mem_iUnion₂.mp hxcell with ⟨c, hc_inter, hxatom⟩
        have hc : c ∈ prepared.uniform.centers := (Finset.mem_inter.mp hc_inter).1
        apply Set.mem_iUnion₂.mpr
        exact ⟨c, hc, hxatom⟩
    rw [h1, h2, h3]
  -- Occupied cells nonempty
  have h_cells_nonempty : occupiedCells.Nonempty := by
    rcases prepared.uniform.centers_nonempty with ⟨c, hc⟩
    rcases h_center_in_occupied c hc with ⟨cell, hcell_occ, _⟩
    exact ⟨cell, hcell_occ⟩
  -- Cell measurable
  have h_cell_measurable : ∀ cell ∈ occupiedCells, MeasurableSet (cellSet cell) := by
    intro cell hcell
    have hcell_in_partition : cell ∈ planarGridPartition prepared.base level prepared.atomized.centers :=
      (Finset.mem_filter.mp hcell).1
    exact prepared.cellMass.cellBand_measurable level hlevel_le cell hcell_in_partition
  -- Cell disjoint
  have h_cell_disjoint : ∀ cell₁ ∈ occupiedCells, ∀ cell₂ ∈ occupiedCells,
      cell₁ ≠ cell₂ → Disjoint (cellSet cell₁) (cellSet cell₂) := by
    intro cell₁ hcell₁ cell₂ hcell₂ hne
    have hp₁ : cell₁ ∈ planarGridPartition prepared.base level prepared.atomized.centers :=
      (Finset.mem_filter.mp hcell₁).1
    have hp₂ : cell₂ ∈ planarGridPartition prepared.base level prepared.atomized.centers :=
      (Finset.mem_filter.mp hcell₂).1
    have h_disj_cells : Disjoint cell₁ cell₂ := h_partition_disjoint cell₁ cell₂ hp₁ hp₂ hne
    have h_disj_centers : Disjoint (prepared.uniform.centers ∩ cell₁) (prepared.uniform.centers ∩ cell₂) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 : x ∈ cell₁ := (Finset.mem_inter.mp hx1).2
      have h2 : x ∈ cell₂ := (Finset.mem_inter.mp hx2).2
      exact Finset.disjoint_left.mp h_disj_cells h1 h2
    have h_main : ∀ (c₁ : Point2), c₁ ∈ prepared.uniform.centers ∩ cell₁ →
        ∀ (c₂ : Point2), c₂ ∈ prepared.uniform.centers ∩ cell₂ → Disjoint (atom c₁) (atom c₂) := by
      intro c₁ hc₁ c₂ hc₂
      have hc₁' : c₁ ∈ prepared.uniform.centers := (Finset.mem_inter.mp hc₁).1
      have hc₂' : c₂ ∈ prepared.uniform.centers := (Finset.mem_inter.mp hc₂).1
      have hne' : c₁ ≠ c₂ := by
        intro h
        exact Finset.disjoint_left.mp h_disj_centers hc₁ (h ▸ hc₂)
      have ha₁ : c₁ ∈ prepared.atomized.centers := prepared.uniform.centers_subset hc₁'
      have ha₂ : c₂ ∈ prepared.atomized.centers := prepared.uniform.centers_subset hc₂'
      exact prepared.atomized.atom_disjoint c₁ ha₁ c₂ ha₂ hne'
    simp only [cellSet, projectedFiberOSPreparedCellSet, projectedFiberOSCellBand, finiteAtomUnion]
    apply Set.disjoint_iUnion₂_left.mpr
    intro c₁ hc₁
    apply Set.disjoint_iUnion₂_right.mpr
    intro c₂ hc₂
    exact h_main c₁ hc₁ c₂ hc₂
  -- Cell area nonzero
  have h_cell_area_nonzero : ∀ cell ∈ occupiedCells, volume (cellSet cell) ≠ 0 := by
    intro cell hcell
    have hp : cell ∈ planarGridPartition prepared.base level prepared.atomized.centers :=
      (Finset.mem_filter.mp hcell).1
    have hnonempty : (prepared.uniform.centers ∩ cell).Nonempty :=
      (Finset.mem_filter.mp hcell).2
    exact prepared.cellArea.cellBand_area_nonzero level hlevel_le cell hp hnonempty
  -- Cell area ne top
  have h_cell_area_ne_top : ∀ cell ∈ occupiedCells, volume (cellSet cell) ≠ ⊤ := by
    intro cell hcell
    have hp : cell ∈ planarGridPartition prepared.base level prepared.atomized.centers :=
      (Finset.mem_filter.mp hcell).1
    exact prepared.cellArea.cellBand_area_ne_top level hlevel_le cell hp
  -- Cell area comparable
  have h_cell_area_comparable : ∀ cell₁ ∈ occupiedCells, ∀ cell₂ ∈ occupiedCells,
      volume (cellSet cell₁) ≤ 4 * volume (cellSet cell₂) := by
    intro cell₁ hcell₁ cell₂ hcell₂
    have hp₁ : cell₁ ∈ planarGridPartition prepared.base level prepared.atomized.centers :=
      (Finset.mem_filter.mp hcell₁).1
    have hp₂ : cell₂ ∈ planarGridPartition prepared.base level prepared.atomized.centers :=
      (Finset.mem_filter.mp hcell₂).1
    have hne₁ : (prepared.uniform.centers ∩ cell₁).Nonempty := (Finset.mem_filter.mp hcell₁).2
    have hne₂ : (prepared.uniform.centers ∩ cell₂).Nonempty := (Finset.mem_filter.mp hcell₂).2
    exact prepared.cellArea.cell_area_comparable level hlevel_le cell₁ hp₁ hne₁ cell₂ hp₂ hne₂
  -- Cell thickening bound
  have h_cell_thickening_bound : ∀ cell ∈ occupiedCells,
      volume (Metric.cthickening rho (cellSet cell)) ≤
        ENNReal.ofReal ((((2 * prepared.base + 3 : ℕ) : ℝ) * rho) ^ 2 * Real.pi) := by
    intro cell hcell
    have hp : cell ∈ planarGridPartition prepared.base level prepared.atomized.centers :=
      (Finset.mem_filter.mp hcell).1
    have hnonempty : (prepared.uniform.centers ∩ cell).Nonempty :=
      (Finset.mem_filter.mp hcell).2
    rcases h_thickening F Y f prepared.bandData prepared.base prepared.levels
        (section7GridIndexBound prepared.base prepared.levels) hbase_ge_three
        prepared.atomized prepared.uniform level hlevel_le rho hrho_pos
        hmesh_le h_mesh_premise cell hp hnonempty with
      ⟨center, _hcenter, _hsubset, hbound⟩
    exact hbound
  refine' ⟨level, _⟩
  exact ⟨{
    level_le := hlevel_le,
    coarse_mesh_le := hmesh_le,
    rho_lt_coarse_mesh := hrho_lt_mesh,
    cells_nonempty := h_cells_nonempty,
    global_eq := h_global_eq,
    cell_measurable := h_cell_measurable,
    cell_disjoint := h_cell_disjoint,
    cell_area_nonzero := h_cell_area_nonzero,
    cell_area_ne_top := h_cell_area_ne_top,
    cell_area_comparable := h_cell_area_comparable,
    cell_thickening_bound := h_cell_thickening_bound
  }⟩

end Kakeya.Assouad
