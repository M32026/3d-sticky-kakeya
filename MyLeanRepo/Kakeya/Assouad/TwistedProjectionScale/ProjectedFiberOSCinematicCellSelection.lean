import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSCinematicCellSelectionStatement

/-!
# Cinematic occupied-cell selection

Select the occupied projected cells supporting one local cinematic corridor
certificate, accounting for the terminal-atom center error.
-/

namespace Kakeya.Assouad

theorem projected_fiber_os_cinematic_cell_selection :
    ProjectedFiberOSCinematicCellSelectionStatement := by
  intro delta eta rho F Y f prepared level cellSystem g r hr localSet hlocal1 hlocal2
  set expandedRadius : ℝ :=
    projectedFiberOSCinematicExpandedRadius prepared r with hexpanded
  set graph : Set Point2 := cinematicExtensionGraph g with hgraph
  set occupiedCells : Finset (DiscreteSet 2) :=
    projectedFiberOSOccupiedCells prepared level with hoccupiedCells
  set selectedCells : Finset (DiscreteSet 2) :=
    projectedFiberOSCinematicCells prepared level g r with hselectedCells
  set corridorCells : Finset (DiscreteSet 2) :=
    planarGridCinematicCorridorCells prepared.base level
      prepared.atomized.centers g expandedRadius with hcorridorCells
  have hbase_pos : 0 < prepared.base := by
    linarith [prepared.base_ge_three]
  have hterm_pos : 0 < (prepared.base ^ prepared.levels : ℝ)⁻¹ := by
    positivity
  have hexpanded_nonneg : 0 ≤ expandedRadius := by
    rw [hexpanded, projectedFiberOSCinematicExpandedRadius]
    linarith [hr, hterm_pos]

  -- Part 1: selectedCells ⊆ corridorCells
  have h1 : selectedCells ⊆ corridorCells := by
    intro cell hcell
    simp only [hselectedCells, projectedFiberOSCinematicCells,
      Finset.mem_filter] at hcell
    rcases hcell with ⟨hcell_occupied, hcond⟩
    have hcell_in_partition :
        cell ∈ planarGridPartition prepared.base level
          prepared.atomized.centers := by
      simp only [projectedFiberOSOccupiedCells,
        Finset.mem_filter] at hcell_occupied
      exact hcell_occupied.1
    simp only [hcorridorCells, planarGridCinematicCorridorCells,
      Finset.mem_filter]
    exact ⟨hcell_in_partition, hcond⟩
  have hcard : selectedCells.card ≤ corridorCells.card :=
    Finset.card_le_card h1

  -- Part 2: localSet containment
  have hcontainment : localSet ⊆
      finiteAtomUnion selectedCells (projectedFiberOSPreparedCellSet prepared) := by
    intro x hx
    have hx1 : x ∈ twistedUnion prepared.density.globalShading f :=
      hlocal1 hx
    have hx2 : x ∈ Metric.cthickening r graph := hlocal2 hx
    have hglobal : x ∈ finiteAtomUnion occupiedCells
        (projectedFiberOSPreparedCellSet prepared) := by
      rw [cellSystem.global_eq] at hx1
      exact hx1
    rcases Set.mem_iUnion₂.mp hglobal with
      ⟨cell, hcell_occupied, hx_in_cell⟩
    have hcell_band_def :
        x ∈ finiteAtomUnion (prepared.uniform.centers ∩ cell)
          (projectedFiberGridAtom prepared.bandData.band
            prepared.base prepared.levels) := by
      simpa [projectedFiberOSPreparedCellSet, projectedFiberOSCellBand]
        using hx_in_cell
    rcases Set.mem_iUnion₂.mp hcell_band_def with
      ⟨c, hc_in_inter, hx_in_atom⟩
    have hc_in_cell : c ∈ cell :=
      (Finset.mem_inter.mp hc_in_inter).2
    have h_same_index :
        planarGridIndex prepared.base prepared.levels x =
        planarGridIndex prepared.base prepared.levels c := by
      simpa [projectedFiberGridAtom, Set.mem_inter_iff,
        Set.mem_setOf_eq] using hx_in_atom.2
    have h_coord : ∀ i : Fin 2,
        |x i - c i| < (prepared.base ^ prepared.levels : ℝ)⁻¹ :=
      planarGridIndex_same_coord_bound hbase_pos h_same_index
    have h_dist : dist x c <
        2 * (prepared.base ^ prepared.levels : ℝ)⁻¹ :=
      dist_lt_two_of_coord_lt h_coord

    -- Use infEDist triangle inequality to show c is in enlarged thickening
    have h_inf_x : Metric.infEDist x graph ≤ ENNReal.ofReal r :=
      (Metric.mem_cthickening_iff).mp hx2
    have h_edist : edist x c = ENNReal.ofReal (dist x c) :=
      edist_dist x c
    have h_inf_c : Metric.infEDist c graph ≤
        ENNReal.ofReal expandedRadius := by
      have h_tri : Metric.infEDist c graph ≤
          Metric.infEDist x graph + edist c x :=
        Metric.infEDist_le_infEDist_add_edist
      have h_comm : edist c x = edist x c := edist_comm c x
      rw [h_comm] at h_tri
      have h_edist_le : edist x c ≤
          ENNReal.ofReal (2 * (prepared.base ^ prepared.levels : ℝ)⁻¹) := by
        rw [h_edist]
        exact ENNReal.ofReal_le_ofReal h_dist.le
      have h4 : Metric.infEDist x graph + edist x c ≤
          ENNReal.ofReal r +
          ENNReal.ofReal (2 * (prepared.base ^ prepared.levels : ℝ)⁻¹) :=
        add_le_add h_inf_x h_edist_le
      have h5 : ENNReal.ofReal r +
            ENNReal.ofReal (2 * (prepared.base ^ prepared.levels : ℝ)⁻¹) =
          ENNReal.ofReal expandedRadius := by
        rw [← ENNReal.ofReal_add (by linarith) (by positivity)]
        apply congr_arg
        simp [hexpanded, projectedFiberOSCinematicExpandedRadius]
      rw [h5] at h4
      exact h_tri.trans h4
    have hc_in_thickening :
        c ∈ Metric.cthickening expandedRadius graph :=
      (Metric.mem_cthickening_iff).mpr h_inf_c
    have hc_in_cell_set : c ∈ (cell : Set Point2) := by
      exact_mod_cast hc_in_cell
    have h_inter_nonempty :
        ((cell : Set Point2) ∩
          Metric.cthickening expandedRadius graph).Nonempty :=
      ⟨c, hc_in_cell_set, hc_in_thickening⟩
    have hcell_selected : cell ∈ selectedCells := by
      simp only [hselectedCells, projectedFiberOSCinematicCells,
        Finset.mem_filter]
      exact ⟨hcell_occupied, h_inter_nonempty⟩
    exact Set.mem_iUnion₂.mpr ⟨cell, hcell_selected, hx_in_cell⟩

  exact ⟨hcard, hcontainment⟩

end Kakeya.Assouad
