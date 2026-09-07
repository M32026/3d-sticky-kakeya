import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridOSStateStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterTerminalCellOSLiftStatement
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.SelectedTubeFamily

/-!
# Helper: construct terminal-level GridOS state data

Builds the `cells`, `parent`, `representative`, and fiber/cell properties
for `TubeParameterGridOSStateData` at the terminal level (`level = levels`).
-/

noncomputable section

namespace Kakeya.Assouad

def build_terminal_grid_os_state
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {active : Finset (Fin family.card)} {base levels : ℕ}
    (terminal : TubeParameterTerminalCellFiberRegularizationData family active base levels)
    (representatives : TubeParameterTerminalCellRepresentativesData terminal)
    (uniform : TubeParameterTerminalCellOSLiftData terminal representatives)
    (selectedFamily : Kakeya.Streamlined.TubeFamily delta)
    (hselectedFamily : selectedFamily = selectedTubeFamily family uniform.selected)
    (selectedShading : Kakeya.Streamlined.TubeShading selectedFamily)
    (densityConstant : ENNReal)
    (hdensity : selectedShading.IsLambdaDense densityConstant)
    (parameterConstant : ENNReal)
    (hparam : TubeParameterFrostmanBound selectedFamily parameterConstant)
    (hvertical : IsInVerticalChart selectedFamily)
    (hparams : ∀ (index : Fin selectedFamily.card),
      |(tubeParams index).a| ≤ 12 ∧
      |(tubeParams index).b| ≤ 12 ∧
      |(tubeParams index).c| ≤ 2 ∧
      |(tubeParams index).d| ≤ 2)
    (hslope : IsInSlopeWindow selectedShading)
    (hdensity_nonzero : densityConstant ≠ 0)
    (hdensity_top : densityConstant ≠ ⊤)
    (hparam_one : 1 ≤ parameterConstant)
    (hparam_top : parameterConstant ≠ ⊤)
    (hscale_pos : 0 < delta) (hscale_le_one : delta ≤ 1) :
    TubeParameterGridOSStateData terminal representatives uniform delta levels
      selectedFamily selectedShading := by
  classical
  subst hselectedFamily
  let partition : ℕ → Finset (Finset (Point 4)) :=
    fun level => tubeParameterGridPartition base level representatives.parameters
  let cells : Finset (Finset (Point 4)) :=
    occupiedPartitionCells uniform.selectedRepresentatives partition levels

  have h_singleton : ∀ (cell : Finset (Point 4)), cell ∈ partition levels → cell.card = 1 := by
    intro cell hcell
    rcases Finset.mem_image.mp hcell with ⟨p, hp, rfl⟩
    have hp_in : p ∈ tubeParameterGridCell base levels representatives.parameters p := by
      simp [tubeParameterGridCell, hp]
    have h1 : ∀ q ∈ tubeParameterGridCell base levels representatives.parameters p, q = p := by
      intro q hq
      have hqA : q ∈ representatives.parameters := (Finset.mem_filter.mp hq).1
      have hq_idx : tubeParameterGridIndex base levels q = tubeParameterGridIndex base levels p :=
        (Finset.mem_filter.mp hq).2
      rcases representatives.parameter_terminal_cell p hp with ⟨cellP, hpeq, hpidx⟩
      rcases representatives.parameter_terminal_cell q hqA with ⟨cellQ, hqeq, hqidx⟩
      have h_cell_eq : cellP.1 = cellQ.1 := by
        rw [← hpidx, ← hqidx, hq_idx]
      have h_subtype_eq : cellP = cellQ := by
        apply Subtype.ext
        exact h_cell_eq
      have h_point_eq : p = q := by
        rw [hpeq, hqeq, h_subtype_eq]
      exact h_point_eq.symm
    have h_card : tubeParameterGridCell base levels representatives.parameters p = {p} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨hp_in, h1⟩
    rw [h_card]
    simp

  have h_selected_cells_subset : uniform.selectedCells ⊆ terminal.cells := by
    rw [uniform.selectedCells_eq]
    exact Finset.filter_subset _ _

  have h_has_point : ∀ (ci : Fin 4 → ℤ), ci ∈ uniform.selectedCells →
      ∃ (point : Point 4), point ∈ uniform.selectedRepresentatives ∧
        tubeParameterGridIndex base levels point = ci := by
    intro ci hci
    rw [uniform.selectedCells_eq] at hci
    exact (Finset.mem_filter.mp hci).2

  let pickPoint (ci : Fin 4 → ℤ) (hci : ci ∈ uniform.selectedCells) : Point 4 :=
    Classical.choose (h_has_point ci hci)
  have hpick1 : ∀ ci hci, pickPoint ci hci ∈ uniform.selectedRepresentatives := by
    intro ci hci
    exact (Classical.choose_spec (h_has_point ci hci)).1
  have hpick2 : ∀ ci hci, tubeParameterGridIndex base levels (pickPoint ci hci) = ci := by
    intro ci hci
    exact (Classical.choose_spec (h_has_point ci hci)).2

  let cellOfIndex (ci : Fin 4 → ℤ) (hci : ci ∈ uniform.selectedCells) : Finset (Point 4) :=
    tubeParameterGridCell base levels representatives.parameters (pickPoint ci hci)

  have h_cellOfIndex_mem : ∀ (ci : Fin 4 → ℤ) (hci : ci ∈ uniform.selectedCells),
      cellOfIndex ci hci ∈ cells := by
    intro ci hci
    let point := pickPoint ci hci
    have hpoint1 : point ∈ uniform.selectedRepresentatives := hpick1 ci hci
    have hpoint_params : point ∈ representatives.parameters :=
      uniform.selectedRepresentatives_subset hpoint1
    have h_in_partition : cellOfIndex ci hci ∈ partition levels := by
      exact Finset.mem_image.mpr ⟨point, hpoint_params, rfl⟩
    have h_intersect : (uniform.selectedRepresentatives ∩ cellOfIndex ci hci).Nonempty := by
      refine ⟨point, ?_⟩
      simp only [Finset.mem_inter]
      constructor
      · exact hpoint1
      · exact Finset.mem_filter.mpr ⟨hpoint_params, rfl⟩
    exact Finset.mem_filter.mpr ⟨h_in_partition, h_intersect⟩

  let pickPointFromCell (cell : Finset (Point 4)) (hcell : cell ∈ cells) : Point 4 :=
    Classical.choose ((Finset.mem_filter.mp hcell).2)
  have hpickCell1 : ∀ cell hcell,
      pickPointFromCell cell hcell ∈ uniform.selectedRepresentatives := by
    intro cell hcell
    have h : pickPointFromCell cell hcell ∈ (uniform.selectedRepresentatives ∩ cell) :=
      Classical.choose_spec ((Finset.mem_filter.mp hcell).2)
    exact (Finset.mem_inter.mp h).1
  have hpickCell2 : ∀ cell hcell, pickPointFromCell cell hcell ∈ cell := by
    intro cell hcell
    have h : pickPointFromCell cell hcell ∈ (uniform.selectedRepresentatives ∩ cell) :=
      Classical.choose_spec ((Finset.mem_filter.mp hcell).2)
    exact (Finset.mem_inter.mp h).2

  let indexOfCell (cell : Finset (Point 4)) (hcell : cell ∈ cells) : Fin 4 → ℤ :=
    tubeParameterGridIndex base levels (pickPointFromCell cell hcell)

  have h_indexOfCell_mem : ∀ (cell : Finset (Point 4)) (hcell : cell ∈ cells),
      indexOfCell cell hcell ∈ uniform.selectedCells := by
    intro cell hcell
    let point := pickPointFromCell cell hcell
    have hpoint1 : point ∈ uniform.selectedRepresentatives := hpickCell1 cell hcell
    have hpoint_params : point ∈ representatives.parameters :=
      uniform.selectedRepresentatives_subset hpoint1
    have h_in_selected_cells : tubeParameterGridIndex base levels point ∈ uniform.selectedCells := by
      rw [uniform.selectedCells_eq]
      have h_term_cell : tubeParameterGridIndex base levels point ∈ terminal.cells := by
        rcases representatives.parameter_terminal_cell point hpoint_params with ⟨cellP, _, hpidx⟩
        rw [hpidx]
        exact cellP.2
      exact Finset.mem_filter.mpr ⟨h_term_cell, ⟨point, hpoint1, rfl⟩⟩
    simpa [indexOfCell] using h_in_selected_cells

  have h_right_inv : ∀ (cell : Finset (Point 4)) (hcell : cell ∈ cells),
      cellOfIndex (indexOfCell cell hcell) (h_indexOfCell_mem cell hcell) = cell := by
    intro cell hcell
    let point := pickPointFromCell cell hcell
    have hpoint1 : point ∈ uniform.selectedRepresentatives := hpickCell1 cell hcell
    have hpoint_params : point ∈ representatives.parameters :=
      uniform.selectedRepresentatives_subset hpoint1
    have hpoint2 : point ∈ cell := hpickCell2 cell hcell
    have h_cell_in_partition : cell ∈ partition levels :=
      (Finset.mem_filter.mp hcell).1
    have h_cell_is_gridcell : cell = tubeParameterGridCell base levels representatives.parameters point := by
      rcases Finset.mem_image.mp h_cell_in_partition with ⟨p, hp, rfl⟩
      have hpoint_in : point ∈ tubeParameterGridCell base levels representatives.parameters p := hpoint2
      have h_idx_eq : tubeParameterGridIndex base levels point = tubeParameterGridIndex base levels p :=
        (Finset.mem_filter.mp hpoint_in).2
      apply Finset.filter_congr
      intro q _
      rw [h_idx_eq]
    let ci := indexOfCell cell hcell
    have hci : ci ∈ uniform.selectedCells := h_indexOfCell_mem cell hcell
    have hci_eq : ci = tubeParameterGridIndex base levels point := by
      dsimp only [ci, indexOfCell, point]
      <;> rfl
    have h_same_idx : tubeParameterGridIndex base levels (pickPoint ci hci) =
        tubeParameterGridIndex base levels point := by
      have h1 : tubeParameterGridIndex base levels (pickPoint ci hci) = ci := hpick2 ci hci
      rw [h1, hci_eq]
    have h_cells_eq : tubeParameterGridCell base levels representatives.parameters (pickPoint ci hci) =
        tubeParameterGridCell base levels representatives.parameters point := by
      apply Finset.filter_congr
      intro q _
      rw [h_same_idx]
    calc
      cellOfIndex ci hci
        = tubeParameterGridCell base levels representatives.parameters (pickPoint ci hci) := rfl
      _ = tubeParameterGridCell base levels representatives.parameters point := h_cells_eq
      _ = cell := h_cell_is_gridcell.symm

  have h_left_inv : ∀ (ci : Fin 4 → ℤ) (hci : ci ∈ uniform.selectedCells),
      indexOfCell (cellOfIndex ci hci) (h_cellOfIndex_mem ci hci) = ci := by
    intro ci hci
    let point := pickPoint ci hci
    have hpoint1 : point ∈ uniform.selectedRepresentatives := hpick1 ci hci
    have hpoint_params : point ∈ representatives.parameters :=
      uniform.selectedRepresentatives_subset hpoint1
    have hpoint2 : tubeParameterGridIndex base levels point = ci := hpick2 ci hci
    have h_cell_in_partition : cellOfIndex ci hci ∈ partition levels :=
      (Finset.mem_filter.mp (h_cellOfIndex_mem ci hci)).1
    have h_cell_singleton : (cellOfIndex ci hci).card = 1 :=
      h_singleton (cellOfIndex ci hci) h_cell_in_partition
    have h_point_in_cell : point ∈ cellOfIndex ci hci := by
      dsimp only [point, cellOfIndex]
      exact Finset.mem_filter.mpr ⟨hpoint_params, rfl⟩
    have h_cell_eq : cellOfIndex ci hci = {point} := by
      rcases Finset.card_eq_one.mp h_cell_singleton with ⟨x, hx⟩
      have h_point_eq_x : point = x := by
        have h : point ∈ ({x} : Finset (Point 4)) := by
          rw [←hx]
          exact h_point_in_cell
        simpa using h
      rw [hx, h_point_eq_x]
    let p := pickPointFromCell (cellOfIndex ci hci) (h_cellOfIndex_mem ci hci)
    have h_p_in : p ∈ cellOfIndex ci hci := hpickCell2 (cellOfIndex ci hci) (h_cellOfIndex_mem ci hci)
    have h_p_eq_point : p = point := by
      rcases Finset.card_eq_one.mp h_cell_singleton with ⟨x, hx⟩
      have hpx : p = x := by
        have h : p ∈ ({x} : Finset (Point 4)) := by
          rw [←hx]
          exact h_p_in
        simpa using h
      have hpt : point = x := by
        have h : point ∈ ({x} : Finset (Point 4)) := by
          rw [←hx]
          exact h_point_in_cell
        simpa using h
      rw [hpx, hpt]
    have h_pick_cell_idx : tubeParameterGridIndex base levels p =
        tubeParameterGridIndex base levels point := by
      rw [h_p_eq_point]
    have h_main : indexOfCell (cellOfIndex ci hci) (h_cellOfIndex_mem ci hci) =
        tubeParameterGridIndex base levels point := by
      dsimp only [indexOfCell]
      rw [h_pick_cell_idx]
    rw [h_main, hpoint2]

  let eSubtype : {ci // ci ∈ uniform.selectedCells} ≃ {cell // cell ∈ cells} :=
    {
      toFun := fun ⟨ci, hci⟩ => ⟨cellOfIndex ci hci, h_cellOfIndex_mem ci hci⟩,
      invFun := fun ⟨cell, hcell⟩ => ⟨indexOfCell cell hcell, h_indexOfCell_mem cell hcell⟩,
      left_inv := by
        intro ⟨ci, hci⟩
        apply Subtype.ext
        exact h_left_inv ci hci,
      right_inv := by
        intro ⟨cell, hcell⟩
        apply Subtype.ext
        exact h_right_inv cell hcell
    }

  let ciEquiv : Fin uniform.selectedCells.card ≃ Fin cells.card :=
    (Finset.equivFin uniform.selectedCells).symm.trans eSubtype |>.trans (Finset.equivFin cells)

  have h_cells_nonempty : cells.Nonempty := by
    have h : uniform.selectedCells.Nonempty := uniform.selectedCells_nonempty
    rcases h with ⟨ci, hci⟩
    exact ⟨cellOfIndex ci hci, h_cellOfIndex_mem ci hci⟩

  let cellIndexOf (j : Fin (selectedTubeFamily family uniform.selected).card) : Fin 4 → ℤ :=
    indexedTubeTerminalCellIndex base levels ((uniform.selected.equivFin.symm j).1)

  have h_cellIndexOf_mem : ∀ j, cellIndexOf j ∈ uniform.selectedCells := by
    intro j
    let i : Fin family.card := (uniform.selected.equivFin.symm j).1
    have hi : i ∈ uniform.selected := (uniform.selected.equivFin.symm j).2
    have h : cellIndexOf j ∈ uniform.selected.image (indexedTubeTerminalCellIndex base levels) :=
      Finset.mem_image.mpr ⟨i, hi, rfl⟩
    rw [uniform.selected_image_cells] at h
    exact h

  let parent (j : Fin (selectedTubeFamily family uniform.selected).card) : Fin cells.card :=
    ciEquiv (uniform.selectedCells.equivFin ⟨cellIndexOf j, h_cellIndexOf_mem j⟩)

  let repIdxOf (c : Fin cells.card) : Fin family.card :=
    let k : Fin uniform.selectedCells.card := ciEquiv.symm c
    let ci := (uniform.selectedCells.equivFin.symm k).1
    let hci := (uniform.selectedCells.equivFin.symm k).2
    representatives.index ⟨ci, h_selected_cells_subset hci⟩

  have h_repIdxOf_selected : ∀ c, repIdxOf c ∈ uniform.selected := by
    intro c
    let k : Fin uniform.selectedCells.card := ciEquiv.symm c
    let ci := (uniform.selectedCells.equivFin.symm k).1
    let hci := (uniform.selectedCells.equivFin.symm k).2
    have h1 : repIdxOf c ∈ terminal.selected := representatives.index_mem_selected ⟨ci, _⟩
    have h2 : indexedTubeTerminalCellIndex base levels (repIdxOf c) = ci :=
      representatives.index_cell ⟨ci, _⟩
    exact uniform.selected_complete_cells (repIdxOf c) h1 (h2 ▸ hci)

  let representative (c : Fin cells.card) : Fin (selectedTubeFamily family uniform.selected).card :=
    uniform.selected.equivFin ⟨repIdxOf c, h_repIdxOf_selected c⟩

  have h_rep_cell_index : ∀ c, indexedTubeTerminalCellIndex base levels (repIdxOf c) =
      cellIndexOf (representative c) := by
    intro c
    dsimp only [cellIndexOf, representative]
    have h_eq : (uniform.selected.equivFin.symm (uniform.selected.equivFin ⟨repIdxOf c, h_repIdxOf_selected c⟩)).1 = repIdxOf c := by
      have h : uniform.selected.equivFin.symm (uniform.selected.equivFin ⟨repIdxOf c, h_repIdxOf_selected c⟩) =
          ⟨repIdxOf c, h_repIdxOf_selected c⟩ :=
        uniform.selected.equivFin.symm_apply_apply _
      rw [h] <;> rfl
    rw [h_eq]
    <;> rfl

  have h_representative_parent : ∀ c, parent (representative c) = c := by
    intro c
    dsimp only [parent]
    let x : {ci // ci ∈ uniform.selectedCells} := ⟨cellIndexOf (representative c), h_cellIndexOf_mem (representative c)⟩
    let y : {ci // ci ∈ uniform.selectedCells} := uniform.selectedCells.equivFin.symm (ciEquiv.symm c)
    have h_val : x.1 = y.1 := by
      have h_a : indexedTubeTerminalCellIndex base levels (repIdxOf c) = cellIndexOf (representative c) :=
        h_rep_cell_index c
      have h_b : indexedTubeTerminalCellIndex base levels (repIdxOf c) = y.1 :=
        representatives.index_cell _
      exact h_a.symm.trans h_b
    have h_xy : x = y := by
      apply Subtype.ext
      exact h_val
    have h2 : uniform.selectedCells.equivFin x = ciEquiv.symm c := by
      have h3 : uniform.selectedCells.equivFin y = ciEquiv.symm c :=
        uniform.selectedCells.equivFin.apply_symm_apply _
      rw [h_xy]
      exact h3
    rw [h2]
    exact ciEquiv.apply_symm_apply c

  have h_parent_surjective : Function.Surjective parent := by
    intro c
    refine ⟨representative c, h_representative_parent c⟩

  have h_parent_cell_index : ∀ j, cellIndexOf (representative (parent j)) = cellIndexOf j := by
    intro j
    dsimp only [parent, representative, cellIndexOf]
    have h_eq : (uniform.selected.equivFin.symm (uniform.selected.equivFin ⟨repIdxOf (parent j), h_repIdxOf_selected (parent j)⟩)).1 = repIdxOf (parent j) := by
      simp
    rw [h_eq]
    have h3 : indexedTubeTerminalCellIndex base levels (repIdxOf (parent j)) =
        (uniform.selectedCells.equivFin.symm (ciEquiv.symm (parent j))).1 := by
      exact representatives.index_cell _
    rw [h3]
    have h4 : ciEquiv.symm (parent j) = uniform.selectedCells.equivFin ⟨cellIndexOf j, h_cellIndexOf_mem j⟩ := by
      exact ciEquiv.symm_apply_apply _
    rw [h4]
    have h9 : (uniform.selectedCells.equivFin.symm (uniform.selectedCells.equivFin ⟨cellIndexOf j, h_cellIndexOf_mem j⟩)).1 = cellIndexOf j := by
      have h10 : uniform.selectedCells.equivFin.symm (uniform.selectedCells.equivFin ⟨cellIndexOf j, h_cellIndexOf_mem j⟩) = ⟨cellIndexOf j, h_cellIndexOf_mem j⟩ :=
        uniform.selectedCells.equivFin.symm_apply_apply _
      rw [h10] <;> rfl
    exact h9

  have h_parameter_cell : ∀ (index : Fin (selectedTubeFamily family uniform.selected).card),
      tubeParameterGridIndex base levels (indexedTubeParameterPoint4 index) =
      tubeParameterGridIndex base levels
        (indexedTubeParameterPoint4 (representative (parent index))) := by
    intro index
    have h_eq1 : indexedTubeParameterPoint4 index =
        indexedTubeParameterPoint4 ((uniform.selected.equivFin.symm index).1) := by rfl
    have h_eq2 : indexedTubeParameterPoint4 (representative (parent index)) =
        indexedTubeParameterPoint4 ((uniform.selected.equivFin.symm (representative (parent index))).1) := by rfl
    rw [h_eq1, h_eq2]
    have h5 : cellIndexOf (representative (parent index)) = cellIndexOf index :=
      h_parent_cell_index index
    simpa [indexedTubeTerminalCellIndex, cellIndexOf] using h5.symm

  have h_representative_parameter : ∀ (c : Fin cells.card),
      ∃ point ∈ (cells.equivFin.symm c).1,
        tubeParameterGridIndex base levels
            (indexedTubeParameterPoint4 (representative c)) =
          tubeParameterGridIndex base levels point := by
    intro c
    let cellWithMem := cells.equivFin.symm c
    let ciSubtype : {ci // ci ∈ uniform.selectedCells} := eSubtype.symm cellWithMem
    let ci := ciSubtype.1
    let hci := ciSubtype.2
    let repIdx : Fin family.card := representatives.index ⟨ci, h_selected_cells_subset hci⟩
    let point := indexedTubeParameterPoint4 repIdx

    have h_ciEquiv_unfold : ciEquiv.symm c = uniform.selectedCells.equivFin ciSubtype := by
      simp [ciEquiv, cellWithMem, ciSubtype]
      <;> rfl
    have h_ci_eq : ci = (uniform.selectedCells.equivFin.symm (ciEquiv.symm c)).1 := by
      rw [h_ciEquiv_unfold]
      have h : (uniform.selectedCells.equivFin.symm (uniform.selectedCells.equivFin ciSubtype)) = ciSubtype :=
        uniform.selectedCells.equivFin.symm_apply_apply _
      rw [h] <;> rfl
    have h_subtype_eq : (⟨ci, h_selected_cells_subset hci⟩ : {ci // ci ∈ terminal.cells}) =
        (⟨(uniform.selectedCells.equivFin.symm (ciEquiv.symm c)).1,
          h_selected_cells_subset (uniform.selectedCells.equivFin.symm (ciEquiv.symm c)).2⟩) := by
      apply Subtype.ext
      exact h_ci_eq
    have h_repIdx_eq : repIdx = repIdxOf c := by
      dsimp only [repIdxOf, repIdx]
      exact congr_arg representatives.index h_subtype_eq
    have hpoint_in_params : point ∈ representatives.parameters := by
      rw [representatives.parameters_eq]
      exact Finset.mem_image.mpr ⟨⟨ci, h_selected_cells_subset hci⟩, Finset.mem_univ _, rfl⟩
    have h_eSubtype_apply : eSubtype ciSubtype = cellWithMem :=
      eSubtype.right_inv cellWithMem
    have h_cell_eq : (cellWithMem : Finset (Point 4)) = cellOfIndex ci hci := by
      exact congr_arg Subtype.val h_eSubtype_apply.symm
    have h_idx_point : tubeParameterGridIndex base levels point = ci := by
      have h5 : indexedTubeTerminalCellIndex base levels repIdx = ci :=
        representatives.index_cell ⟨ci, h_selected_cells_subset hci⟩
      exact h5
    have hpoint_in_cell : point ∈ (cellWithMem : Finset (Point 4)) := by
      rw [h_cell_eq]
      have h6 : tubeParameterGridIndex base levels (pickPoint ci hci) = ci := hpick2 ci hci
      have h7 : point ∈ tubeParameterGridCell base levels representatives.parameters (pickPoint ci hci) := by
        apply Finset.mem_filter.mpr
        exact ⟨hpoint_in_params, by rw [h_idx_point, h6]⟩
      exact h7
    have h10 : (uniform.selected.equivFin.symm (representative c)).1 = repIdxOf c := by
      simp [representative] <;> rfl
    have h_main_eq : tubeParameterGridIndex base levels (indexedTubeParameterPoint4 (representative c)) =
        tubeParameterGridIndex base levels point := by
      have h11 : tubeParameterGridIndex base levels (indexedTubeParameterPoint4 (representative c)) =
          tubeParameterGridIndex base levels (indexedTubeParameterPoint4 ((uniform.selected.equivFin.symm (representative c)).1)) := by
        rfl
      rw [h11]
      have h12 : (uniform.selected.equivFin.symm (representative c)).1 = repIdx := by
        exact h10.trans h_repIdx_eq.symm
      have h13 : indexedTubeParameterPoint4 ((uniform.selected.equivFin.symm (representative c)).1) =
          indexedTubeParameterPoint4 repIdx := by
        rw [h12]
      rw [h13]
      <;> rfl
    exact ⟨point, hpoint_in_cell, h_main_eq⟩

  let fiberMultiplicity := terminal.fiberMultiplicity

  have h_fiber_eq : ∀ (c : Fin cells.card),
      (Finset.univ.filter fun index : Fin (selectedTubeFamily family uniform.selected).card =>
        parent index = c).card =
      (uniform.selected.filter fun idx : Fin family.card =>
        indexedTubeTerminalCellIndex base levels idx =
        (eSubtype.symm (cells.equivFin.symm c)).1).card := by
    intro c
    let cellWithMem := cells.equivFin.symm c
    let ci := (eSubtype.symm cellWithMem).1
    let hci := (eSubtype.symm cellWithMem).2
    let f : Fin (selectedTubeFamily family uniform.selected).card → Fin family.card :=
      fun j => (uniform.selected.equivFin.symm j).1
    let s1 : Finset (Fin (selectedTubeFamily family uniform.selected).card) :=
      Finset.univ.filter fun index => parent index = c
    let s2 : Finset (Fin family.card) :=
      uniform.selected.filter fun idx => indexedTubeTerminalCellIndex base levels idx = ci
    have h_inj : Set.InjOn f s1 := by
      intro j1 _ j2 _ h
      apply uniform.selected.equivFin.symm.injective
      apply Subtype.ext
      exact h
    have h_eq_set : s1.image f = s2 := by
      ext i
      simp only [s1, s2, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hj, rfl⟩
        have h4 : parent j = c := hj
        have h5 : indexedTubeTerminalCellIndex base levels (f j) = ci := by
          dsimp only [parent, f] at h4
          have h6 : ciEquiv (uniform.selectedCells.equivFin ⟨cellIndexOf j, h_cellIndexOf_mem j⟩) = c := h4
          have h7 : uniform.selectedCells.equivFin ⟨cellIndexOf j, h_cellIndexOf_mem j⟩ = ciEquiv.symm c := by
            exact (ciEquiv.apply_eq_iff_eq_symm_apply).mp h6
          have h8 : cellIndexOf j = ci := by
            have h9 : (uniform.selectedCells.equivFin.symm (uniform.selectedCells.equivFin ⟨cellIndexOf j, h_cellIndexOf_mem j⟩)).1 =
                (uniform.selectedCells.equivFin.symm (ciEquiv.symm c)).1 := by
              rw [h7]
            have h10 : (uniform.selectedCells.equivFin.symm (ciEquiv.symm c)).1 = ci := by
              let ciSubtype' : {ci // ci ∈ uniform.selectedCells} := eSubtype.symm cellWithMem
              have h11 : uniform.selectedCells.equivFin.symm (ciEquiv.symm c) = ciSubtype' := by
                simp [ciEquiv, cellWithMem, ciSubtype'] <;> rfl
              rw [h11] <;> rfl
            have h12 : cellIndexOf j = (uniform.selectedCells.equivFin.symm (ciEquiv.symm c)).1 := by
              simpa using h9
            rw [h12, h10]
          simpa [cellIndexOf, f] using h8
        exact ⟨(uniform.selected.equivFin.symm j).2, h5⟩
      · rintro ⟨hi, hidx⟩
        let j : Fin (selectedTubeFamily family uniform.selected).card :=
          uniform.selected.equivFin ⟨i, hi⟩
        have hfj : f j = i := by
          dsimp only [f, j]
          simp
        have h_parent_j : parent j = c := by
          dsimp only [parent, j]
          have h9 : cellIndexOf j = ci := by
            simpa [cellIndexOf, j] using hidx
          have h95 : uniform.selectedCells.equivFin ⟨cellIndexOf j, h_cellIndexOf_mem j⟩ =
              uniform.selectedCells.equivFin ⟨ci, hci⟩ := by
            congr
            <;> exact h9
          rw [h95]
          have h10 : uniform.selectedCells.equivFin ⟨ci, hci⟩ = ciEquiv.symm c := by
            let ciSubtype' : {ci // ci ∈ uniform.selectedCells} := eSubtype.symm cellWithMem
            have h11 : uniform.selectedCells.equivFin.symm (ciEquiv.symm c) = ciSubtype' := by
              simp [ciEquiv, cellWithMem, ciSubtype'] <;> rfl
            have h12 : uniform.selectedCells.equivFin (uniform.selectedCells.equivFin.symm (ciEquiv.symm c)) = ciEquiv.symm c :=
              uniform.selectedCells.equivFin.apply_symm_apply _
            rw [h11] at h12
            have h13 : ciSubtype' = ⟨ci, hci⟩ := by
              apply Subtype.ext <;> rfl
            rw [h13] at h12
            exact h12.symm
          rw [h10]
          exact ciEquiv.apply_symm_apply c
        exact ⟨j, h_parent_j, hfj⟩
    have h_card : (s1.image f).card = s1.card := Finset.card_image_of_injOn (H := h_inj)
    rw [h_card.symm, h_eq_set]

  have h_fiber_lower : ∀ (c : Fin cells.card),
      fiberMultiplicity ≤
        (Finset.univ.filter fun index : Fin (selectedTubeFamily family uniform.selected).card =>
          parent index = c).card := by
    intro c
    let cellWithMem := cells.equivFin.symm c
    let ci := (eSubtype.symm cellWithMem).1
    let hci := (eSubtype.symm cellWithMem).2
    rw [h_fiber_eq c]
    exact uniform.fiber_lower ci hci

  have h_fiber_upper : ∀ (c : Fin cells.card),
      (Finset.univ.filter fun index : Fin (selectedTubeFamily family uniform.selected).card =>
        parent index = c).card < 2 * fiberMultiplicity := by
    intro c
    let cellWithMem := cells.equivFin.symm c
    let ci := (eSubtype.symm cellWithMem).1
    let hci := (eSubtype.symm cellWithMem).2
    rw [h_fiber_eq c]
    exact uniform.fiber_upper ci hci

  let result : TubeParameterGridOSStateData terminal representatives uniform delta levels
      (selectedTubeFamily family uniform.selected) selectedShading := by
    refine' ⟨
      by rfl,
      hscale_pos,
      hscale_le_one,
      Or.inl rfl,
      _,
      hvertical,
      hparams,
      cells,
      _,
      h_cells_nonempty,
      parent,
      h_parent_surjective,
      representative,
      h_representative_parent,
      h_parameter_cell,
      h_representative_parameter,
      fiberMultiplicity,
      terminal.fiberMultiplicity_pos,
      h_fiber_lower,
      h_fiber_upper,
      densityConstant,
      hdensity_nonzero,
      hdensity_top,
      hdensity,
      hslope,
      parameterConstant,
      hparam_one,
      hparam_top,
      hparam
    ⟩
    · have h : 0 < (selectedTubeFamily family uniform.selected).card :=
        uniform.selected_nonempty.card_pos
      exact h
    · dsimp only
      <;> rfl
  exact result

end Kakeya.Assouad
