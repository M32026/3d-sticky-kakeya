import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridOSFourBlockPackageStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridCoarseningHelpers

/-!
WZ2 Proposition 7.1: assemble one factor-two uniform four-block package at a
coarser occupied level of the corrected delta-grid OS tree.
-/

namespace Kakeya.Assouad

theorem tube_parameter_grid_os_four_block_package :
    TubeParameterGridOSFourBlockPackageStatement := by
  intro hRepTree hBranching hDiameter hWindowBlock
  dsimp only [TubeParameterGridOSFourBlockPackageInput]
  intro delta source active base levels hbase terminal representatives uniform
  intro currentScale currentLevel currentFamily currentShading state fineShading
  intro hsubshading hslope rho hrho_pos hrho_le nextLevel hnext_le hbudget

  let partition : ℕ → Finset (Finset (Point 4)) :=
    fun gridLevel => tubeParameterGridPartition base gridLevel representatives.parameters

  let nextCells : Finset (Finset (Point 4)) :=
    occupiedPartitionCells uniform.selectedRepresentatives partition nextLevel

  have hpart_all :=
    hRepTree (delta := delta) source active base levels hbase terminal representatives
  have hpart_props : ∀ level ≤ levels,
      (∀ cell ∈ partition level, cell.Nonempty ∧ cell ⊆ representatives.parameters) ∧
      (∀ cell₁ ∈ partition level, ∀ cell₂ ∈ partition level,
        cell₁ ≠ cell₂ → Disjoint cell₁ cell₂) ∧
      representatives.parameters ⊆ Finset.biUnion (partition level) id :=
    hpart_all.1
  have hterminal_singletons :
      ∀ cell ∈ partition levels, cell.card = 1 :=
    hpart_all.2.1
  have hnesting : ∀ level, level < levels → ∀ child ∈ partition (level + 1),
      ∃ parent ∈ partition level, child ⊆ parent :=
    hpart_all.2.2.1

  have hcurrent_le_levels : currentLevel ≤ levels := state.level_le
  have hnext_le_levels : nextLevel ≤ levels := by linarith
  have hbase1 : 1 ≤ base := by linarith

  rcases hBranching (α := Point 4) representatives.parameters levels partition
      hpart_props hterminal_singletons hnesting
      uniform.selectedRepresentatives uniform.selectedRepresentatives_nonempty
      uniform.selectedRepresentatives_subset
      uniform.branchExponent uniform.branch_uniform
      nextLevel currentLevel hnext_le hcurrent_le_levels with
    ⟨descendantCount, hdesc_pos, hdesc_card⟩

  have hunique_parent : ∀ (currentCell : Finset (Point 4)),
      currentCell ∈ state.cells →
      ∃! (nextCell : Finset (Point 4)),
        nextCell ∈ nextCells ∧ currentCell ⊆ nextCell := by
    intro currentCell hcurrentCell
    have hcurrentCell' :
        currentCell ∈
          occupiedPartitionCells uniform.selectedRepresentatives partition currentLevel := by
      rw [state.cells_eq] at hcurrentCell
      exact hcurrentCell
    exact occupiedPartitionCells_unique_parent hpart_props hnesting
      hnext_le hcurrent_le_levels hcurrentCell'

  let parentCell
      (currentCell : Finset (Point 4))
      (hcurrentCell : currentCell ∈ state.cells) : Finset (Point 4) :=
    Classical.choose (hunique_parent currentCell hcurrentCell)

  have hparentCell_spec :
      ∀ (currentCell : Finset (Point 4)) (hcurrentCell : currentCell ∈ state.cells),
        parentCell currentCell hcurrentCell ∈ nextCells ∧
          currentCell ⊆ parentCell currentCell hcurrentCell := by
    intro currentCell hcurrentCell
    exact (Classical.choose_spec (hunique_parent currentCell hcurrentCell)).1

  let cellToNext (cell : Fin state.cells.card) : Fin nextCells.card :=
    let currentCell := (state.cells.equivFin.symm cell).1
    have hcurrentCell : currentCell ∈ state.cells :=
      (state.cells.equivFin.symm cell).2
    nextCells.equivFin
      ⟨parentCell currentCell hcurrentCell,
        (hparentCell_spec currentCell hcurrentCell).1⟩

  have hcellToNext_spec : ∀ (cell : Fin state.cells.card),
      (state.cells.equivFin.symm cell).1 ⊆
        (nextCells.equivFin.symm (cellToNext cell)).1 := by
    intro cell
    dsimp only [cellToNext]
    rw [Equiv.symm_apply_apply]
    exact (hparentCell_spec (state.cells.equivFin.symm cell).1
      (state.cells.equivFin.symm cell).2).2

  let fineParent : Fin currentFamily.card → Fin nextCells.card :=
    fun i => cellToNext (state.parent i)

  let containedCells (nextCell : Finset (Point 4)) :
      Finset (Finset (Point 4)) :=
    state.cells.filter fun cell => cell ⊆ nextCell

  have hcontainedCells_card :
      ∀ (nextCell : Finset (Point 4)), nextCell ∈ nextCells →
        (containedCells nextCell).card = descendantCount := by
    intro nextCell hnextCell
    have h1 : containedCells nextCell =
        (occupiedPartitionCells uniform.selectedRepresentatives partition currentLevel).filter
          fun cell => cell ⊆ nextCell := by
      simp only [containedCells, state.cells_eq] <;> rfl
    rw [h1]
    exact hdesc_card nextCell hnextCell

  have hcontainedCells_nonempty :
      ∀ (nextCell : Finset (Point 4)), nextCell ∈ nextCells →
        (containedCells nextCell).Nonempty := by
    intro nextCell hnextCell
    have hcard : (containedCells nextCell).card = descendantCount :=
      hcontainedCells_card nextCell hnextCell
    have hpos : 0 < (containedCells nextCell).card := by
      rw [hcard]
      exact hdesc_pos
    exact Finset.card_pos.mp hpos

  let chooseContainedCell
      (nextCell : Finset (Point 4))
      (hnextCell : nextCell ∈ nextCells) : Finset (Point 4) :=
    Classical.choose (hcontainedCells_nonempty nextCell hnextCell)

  have hchooseContainedCell_mem :
      ∀ (nextCell : Finset (Point 4)) (hnextCell : nextCell ∈ nextCells),
        chooseContainedCell nextCell hnextCell ∈ containedCells nextCell := by
    intro nextCell hnextCell
    exact Classical.choose_spec (hcontainedCells_nonempty nextCell hnextCell)

  have hchooseContainedCell_sub :
      ∀ (nextCell : Finset (Point 4)) (hnextCell : nextCell ∈ nextCells),
        chooseContainedCell nextCell hnextCell ⊆ nextCell := by
    intro nextCell hnextCell
    have h := hchooseContainedCell_mem nextCell hnextCell
    exact (Finset.mem_filter.mp h).2

  let representative (nextCell : Fin nextCells.card) : Fin currentFamily.card :=
    let nextCell' := (nextCells.equivFin.symm nextCell).1
    let hnextCell' := (nextCells.equivFin.symm nextCell).2
    let currentCell := chooseContainedCell nextCell' hnextCell'
    let currentCell' : Fin state.cells.card :=
      state.cells.equivFin
        ⟨currentCell,
          (Finset.mem_filter.mp
            (hchooseContainedCell_mem nextCell' hnextCell')).1⟩
    state.representative currentCell'

  have hrepresentative_parent :
      ∀ (nextCell : Fin nextCells.card),
        fineParent (representative nextCell) = nextCell := by
    intro nextCell
    let nextCell' := (nextCells.equivFin.symm nextCell).1
    let hnextCell' := (nextCells.equivFin.symm nextCell).2
    let currentCell := chooseContainedCell nextCell' hnextCell'
    have hcurrentCell_in : currentCell ∈ state.cells :=
      (Finset.mem_filter.mp
        (hchooseContainedCell_mem nextCell' hnextCell')).1
    let currentCell' : Fin state.cells.card :=
      state.cells.equivFin ⟨currentCell, hcurrentCell_in⟩
    have h1 : (state.cells.equivFin.symm currentCell').1 = currentCell := by
      simp [currentCell'] <;> rfl
    have h2 : currentCell ⊆ nextCell' :=
      hchooseContainedCell_sub nextCell' hnextCell'
    have h3 : (state.cells.equivFin.symm currentCell').1 ⊆ nextCell' := by
      rw [h1]
      exact h2
    have h5 := hcellToNext_spec currentCell'
    let currentCellVal := (state.cells.equivFin.symm currentCell').1
    have hcurrentCellVal : currentCellVal ∈ state.cells :=
      (state.cells.equivFin.symm currentCell').2
    let huniq := hunique_parent currentCellVal hcurrentCellVal
    have h6 :
        (nextCells.equivFin.symm (cellToNext currentCell')).1 = nextCell' := by
      exact huniq.unique
        ⟨(nextCells.equivFin.symm (cellToNext currentCell')).2, h5⟩
        ⟨hnextCell', h3⟩
    have h7 :
        nextCells.equivFin.symm (cellToNext currentCell') =
          nextCells.equivFin.symm nextCell := by
      apply Subtype.ext
      exact h6
    have h4 : cellToNext currentCell' = nextCell :=
      nextCells.equivFin.symm.injective h7
    have hrep_parent : state.parent (representative nextCell) = currentCell' := by
      simp [representative, currentCell']
      <;> exact state.representative_parent currentCell'
    have h_goal : fineParent (representative nextCell) = nextCell := by
      dsimp only [fineParent]
      rw [hrep_parent]
      exact h4
    exact h_goal

  let indices (nextCell : Fin nextCells.card) :
      Finset (Fin currentFamily.card) :=
    Finset.univ.filter fun i => fineParent i = nextCell

  have hindices_nonempty :
      ∀ (nextCell : Fin nextCells.card), (indices nextCell).Nonempty := by
    intro nextCell
    refine ⟨representative nextCell, ?_⟩
    simp [indices, hrepresentative_parent]

  have hrepresentative_in_indices :
      ∀ (nextCell : Fin nextCells.card),
        representative nextCell ∈ indices nextCell := by
    intro nextCell
    simp [indices, hrepresentative_parent]

  have h_all_points_in_cell_same_index :
      ∀ (nextCell : Finset (Point 4)), nextCell ∈ partition nextLevel →
        ∀ (p q : Point 4), p ∈ nextCell → q ∈ nextCell →
          tubeParameterGridIndex base nextLevel p =
            tubeParameterGridIndex base nextLevel q := by
    intro nextCell hnextCell p q hp hq
    rcases Finset.mem_image.mp hnextCell with ⟨r, hr, rfl⟩
    have hp_idx :
        tubeParameterGridIndex base nextLevel p =
          tubeParameterGridIndex base nextLevel r :=
      (Finset.mem_filter.mp hp).2
    have hq_idx :
        tubeParameterGridIndex base nextLevel q =
          tubeParameterGridIndex base nextLevel r :=
      (Finset.mem_filter.mp hq).2
    rw [hp_idx, hq_idx]

  have h_same_nextLevel_index : ∀ (fineIndex : Fin currentFamily.card),
      tubeParameterGridIndex base nextLevel
          (indexedTubeParameterPoint4 fineIndex) =
        tubeParameterGridIndex base nextLevel
          (indexedTubeParameterPoint4
            (representative (fineParent fineIndex))) := by
    intro fineIndex
    let currentCellFin := state.parent fineIndex
    let currentCell := (state.cells.equivFin.symm currentCellFin).1
    let nextCellFin := fineParent fineIndex
    let nextCell := (nextCells.equivFin.symm nextCellFin).1
    have hnextCell_in_partition : nextCell ∈ partition nextLevel :=
      (Finset.mem_filter.mp (nextCells.equivFin.symm nextCellFin).2).1
    have hcurrentCell_sub_nextCell : currentCell ⊆ nextCell :=
      hcellToNext_spec currentCellFin

    have h1 :
        tubeParameterGridIndex base currentLevel
            (indexedTubeParameterPoint4 fineIndex) =
          tubeParameterGridIndex base currentLevel
            (indexedTubeParameterPoint4
              (state.representative currentCellFin)) :=
      state.parameter_cell fineIndex

    rcases state.representative_parameter currentCellFin with
      ⟨p, hp_in_cell, hp_idx⟩

    have h2 :
        tubeParameterGridIndex base currentLevel
            (indexedTubeParameterPoint4 fineIndex) =
          tubeParameterGridIndex base currentLevel p := by
      rw [h1, hp_idx]

    have h3 :
        tubeParameterGridIndex base nextLevel
            (indexedTubeParameterPoint4 fineIndex) =
          tubeParameterGridIndex base nextLevel p :=
      tubeParameterGridIndex_coarsening hbase1 h2 hnext_le

    have hp_in_nextCell : p ∈ nextCell :=
      hcurrentCell_sub_nextCell hp_in_cell

    let nextRep := representative nextCellFin
    let nextRepCurrentCellFin := state.parent nextRep
    let nextRepCurrentCell :=
      (state.cells.equivFin.symm nextRepCurrentCellFin).1
    have hnextRepParent :
        cellToNext nextRepCurrentCellFin = nextCellFin :=
      hrepresentative_parent nextCellFin
    have hnextRepCurrentCell_sub_nextCell :
        nextRepCurrentCell ⊆ nextCell := by
      have h := hcellToNext_spec nextRepCurrentCellFin
      rw [hnextRepParent] at h
      exact h

    rcases state.representative_parameter nextRepCurrentCellFin with
      ⟨q, hq_in_cell, hq_idx⟩

    have h4 :
        tubeParameterGridIndex base currentLevel
            (indexedTubeParameterPoint4 nextRep) =
          tubeParameterGridIndex base currentLevel q := by
      rw [state.parameter_cell nextRep, hq_idx]

    have h5 :
        tubeParameterGridIndex base nextLevel
            (indexedTubeParameterPoint4 nextRep) =
          tubeParameterGridIndex base nextLevel q :=
      tubeParameterGridIndex_coarsening hbase1 h4 hnext_le

    have hq_in_nextCell : q ∈ nextCell :=
      hnextRepCurrentCell_sub_nextCell hq_in_cell

    have h6 :
        tubeParameterGridIndex base nextLevel p =
          tubeParameterGridIndex base nextLevel q :=
      h_all_points_in_cell_same_index nextCell hnextCell_in_partition
        p q hp_in_nextCell hq_in_nextCell

    rw [h3, h5, h6]

  have hmesh_pos : 0 < (base ^ nextLevel : ℝ) := by positivity
  have hparameter_close : ∀ (fineIndex : Fin currentFamily.card),
      let reference := representative (fineParent fineIndex)
      |(tubeParams fineIndex).a - (tubeParams reference).a| ≤
          (base ^ nextLevel : ℝ)⁻¹ ∧
      |(tubeParams fineIndex).b - (tubeParams reference).b| ≤
          (base ^ nextLevel : ℝ)⁻¹ ∧
      |(tubeParams fineIndex).c - (tubeParams reference).c| ≤
          (base ^ nextLevel : ℝ)⁻¹ ∧
      |(tubeParams fineIndex).d - (tubeParams reference).d| ≤
          (base ^ nextLevel : ℝ)⁻¹ := by
    intro fineIndex
    let reference := representative (fineParent fineIndex)
    have hsame :
        tubeParameterGridIndex base nextLevel
            (indexedTubeParameterPoint4 fineIndex) =
          tubeParameterGridIndex base nextLevel
            (indexedTubeParameterPoint4 reference) :=
      h_same_nextLevel_index fineIndex
    have ha :
        |(tubeParams fineIndex).a - (tubeParams reference).a| <
          (base ^ nextLevel : ℝ)⁻¹ := by
      have h := congrFun hsame 0
      have h' := same_floor_abs_sub_lt_one_div hmesh_pos h
      have h_eq :
          (indexedTubeParameterPoint4 fineIndex) 0 =
            (tubeParams fineIndex).a := by
        simp [indexedTubeParameterPoint4, tubeParameterPoint4] <;> rfl
      have h_eq2 :
          (indexedTubeParameterPoint4 reference) 0 =
            (tubeParams reference).a := by
        simp [indexedTubeParameterPoint4, tubeParameterPoint4] <;> rfl
      rw [h_eq, h_eq2] at h'
      simpa [one_div] using h'
    have hb :
        |(tubeParams fineIndex).b - (tubeParams reference).b| <
          (base ^ nextLevel : ℝ)⁻¹ := by
      have h := congrFun hsame 1
      have h' := same_floor_abs_sub_lt_one_div hmesh_pos h
      have h_eq :
          (indexedTubeParameterPoint4 fineIndex) 1 =
            (tubeParams fineIndex).b := by
        simp [indexedTubeParameterPoint4, tubeParameterPoint4] <;> rfl
      have h_eq2 :
          (indexedTubeParameterPoint4 reference) 1 =
            (tubeParams reference).b := by
        simp [indexedTubeParameterPoint4, tubeParameterPoint4] <;> rfl
      rw [h_eq, h_eq2] at h'
      simpa [one_div] using h'
    have hc :
        |(tubeParams fineIndex).c - (tubeParams reference).c| <
          (base ^ nextLevel : ℝ)⁻¹ := by
      have h := congrFun hsame 2
      have h' := same_floor_abs_sub_lt_one_div hmesh_pos h
      have h_eq :
          (indexedTubeParameterPoint4 fineIndex) 2 =
            (tubeParams fineIndex).c := by
        simp [indexedTubeParameterPoint4, tubeParameterPoint4] <;> rfl
      have h_eq2 :
          (indexedTubeParameterPoint4 reference) 2 =
            (tubeParams reference).c := by
        simp [indexedTubeParameterPoint4, tubeParameterPoint4] <;> rfl
      rw [h_eq, h_eq2] at h'
      simpa [one_div] using h'
    have hd :
        |(tubeParams fineIndex).d - (tubeParams reference).d| <
          (base ^ nextLevel : ℝ)⁻¹ := by
      have h := congrFun hsame 3
      have h' := same_floor_abs_sub_lt_one_div hmesh_pos h
      have h_eq :
          (indexedTubeParameterPoint4 fineIndex) 3 =
            (tubeParams fineIndex).d := by
        simp [indexedTubeParameterPoint4, tubeParameterPoint4] <;> rfl
      have h_eq2 :
          (indexedTubeParameterPoint4 reference) 3 =
            (tubeParams reference).d := by
        simp [indexedTubeParameterPoint4, tubeParameterPoint4] <;> rfl
      rw [h_eq, h_eq2] at h'
      simpa [one_div] using h'
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

  let blockData (nextCell : Fin nextCells.card) :
      WindowParameterCellFourBlockData
        (rho := rho) fineShading (indices nextCell)
          (representative nextCell) :=
    (hWindowBlock
      (delta := currentScale) (rho := rho)
      state.scale_pos hrho_pos hrho_le state.scale_le_one
      ((base ^ nextLevel : ℝ)⁻¹) (by positivity) hbudget
      currentFamily state.vertical state.parameter_bounds
      fineShading hslope
      (indices nextCell) (hindices_nonempty nextCell)
      (representative nextCell) (hrepresentative_in_indices nextCell)
      (fun i hi => by
        have hfi : fineParent i = nextCell :=
          (Finset.mem_filter.mp hi).2
        have h := hparameter_close i
        rw [hfi] at h
        exact h)).some

  let block : Fin nextCells.card → Kakeya.Streamlined.TubeFamily rho :=
    fun nextCell => (blockData nextCell).coarse

  have hblock_card :
      ∀ (nextCell : Fin nextCells.card), (block nextCell).card = 4 :=
    fun nextCell => (blockData nextCell).coarse_card

  let fineFiber (nextCell : Fin nextCells.card) :
      Finset (Fin currentFamily.card) :=
    Finset.univ.filter fun i => fineParent i = nextCell

  let stateFiber (c : Finset (Point 4)) :
      Finset (Fin currentFamily.card) :=
    Finset.univ.filter fun i =>
      (state.cells.equivFin.symm (state.parent i)).1 = c

  have hfineFiber_biUnion : ∀ (nextCell : Fin nextCells.card),
      fineFiber nextCell =
        (containedCells (nextCells.equivFin.symm nextCell).1).biUnion
          stateFiber := by
    intro nextCell
    let nextCell' := (nextCells.equivFin.symm nextCell).1
    ext i
    simp only [fineFiber, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion]
    constructor
    · intro hfine
      set currentCellFin : Fin state.cells.card := state.parent i with
        hcurrentCellFin_def
      set currentCell : Finset (Point 4) :=
        (state.cells.equivFin.symm currentCellFin).1 with hcurrentCell_def
      have hcurrentCell_in_cells : currentCell ∈ state.cells :=
        (state.cells.equivFin.symm currentCellFin).2
      have hcurrentCell_sub : currentCell ⊆ nextCell' := by
        have h : cellToNext currentCellFin = nextCell := hfine
        have h' := hcellToNext_spec currentCellFin
        rw [h] at h'
        exact h'
      have hcurrentCell_in_contained :
          currentCell ∈ containedCells nextCell' := by
        simp only [containedCells, Finset.mem_filter]
        exact ⟨hcurrentCell_in_cells, hcurrentCell_sub⟩
      refine ⟨currentCell, hcurrentCell_in_contained, ?_⟩
      simp only [stateFiber, Finset.mem_filter, Finset.mem_univ, true_and]
      <;> rfl
    · rintro ⟨currentCell, hcurrentCell_in_contained, hi⟩
      simp only [stateFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hcurrentCell_sub : currentCell ⊆ nextCell' :=
        (Finset.mem_filter.mp hcurrentCell_in_contained).2
      have hc_in_cells : currentCell ∈ state.cells :=
        (Finset.mem_filter.mp hcurrentCell_in_contained).1
      set currentCellFin : Fin state.cells.card :=
        state.cells.equivFin ⟨currentCell, hc_in_cells⟩ with
        hcurrentCellFin_def
      have h1 :
          (state.cells.equivFin.symm (state.parent i)).1 = currentCell :=
        hi
      have h2 : state.parent i = currentCellFin := by
        have h21 :
            state.cells.equivFin.symm (state.parent i) =
              state.cells.equivFin.symm currentCellFin := by
          apply Subtype.ext
          simpa [hcurrentCellFin_def] using h1
        exact state.cells.equivFin.symm.injective h21
      have h4' :
          currentCell ⊆
            (nextCells.equivFin.symm (cellToNext currentCellFin)).1 := by
        have h_eq :
            (state.cells.equivFin.symm currentCellFin).1 = currentCell := by
          simp [currentCellFin]
        have h_spec := hcellToNext_spec currentCellFin
        rw [h_eq] at h_spec
        exact h_spec
      have huniq := hunique_parent currentCell hc_in_cells
      have h5 :
          (nextCells.equivFin.symm (cellToNext currentCellFin)).1 =
            (nextCells.equivFin.symm nextCell).1 :=
        huniq.unique
          ⟨(nextCells.equivFin.symm (cellToNext currentCellFin)).2, h4'⟩
          ⟨(nextCells.equivFin.symm nextCell).2, hcurrentCell_sub⟩
      have h6 :
          nextCells.equivFin.symm (cellToNext currentCellFin) =
            nextCells.equivFin.symm nextCell :=
        Subtype.ext h5
      have h3 : cellToNext currentCellFin = nextCell :=
        nextCells.equivFin.symm.injective h6
      change cellToNext (state.parent i) = nextCell
      rw [h2]
      exact h3

  have hfineFiber_card : ∀ (nextCell : Fin nextCells.card),
      (fineFiber nextCell).card =
        ∑ c ∈ containedCells (nextCells.equivFin.symm nextCell).1,
          (stateFiber c).card := by
    intro nextCell
    rw [hfineFiber_biUnion nextCell]
    apply Finset.card_biUnion
    intro c1 hc1 c2 hc2 hne
    simp only [Finset.disjoint_left, stateFiber]
    intro i hi1 hi2
    have h1 : (state.cells.equivFin.symm (state.parent i)).1 = c1 :=
      (Finset.mem_filter.mp hi1).2
    have h2 : (state.cells.equivFin.symm (state.parent i)).1 = c2 :=
      (Finset.mem_filter.mp hi2).2
    have h3 : c1 = c2 := by rw [←h1, h2]
    exact hne h3

  have hstateFiber_eq :
      ∀ (c : Finset (Point 4)) (hc : c ∈ state.cells),
        stateFiber c =
          Finset.univ.filter fun i : Fin currentFamily.card =>
            state.parent i = state.cells.equivFin ⟨c, hc⟩ := by
    intro c hc
    ext i
    simp only [stateFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h1
      have h2 : state.parent i = state.cells.equivFin ⟨c, hc⟩ := by
        have h_tmp :
            (state.cells.equivFin.symm
              (state.cells.equivFin ⟨c, hc⟩)).1 = c := by
          simp
        have h21 :
            state.cells.equivFin.symm (state.parent i) =
              state.cells.equivFin.symm
                (state.cells.equivFin ⟨c, hc⟩) := by
          apply Subtype.ext
          rw [h_tmp]
          exact h1
        exact state.cells.equivFin.symm.injective h21
      exact h2
    · intro h1
      have h2 : (state.cells.equivFin.symm (state.parent i)).1 = c := by
        rw [h1] <;> simp
      exact h2

  have hfineFiber_lower : ∀ (nextCell : Fin nextCells.card),
      descendantCount * state.fiberMultiplicity ≤
        (fineFiber nextCell).card := by
    intro nextCell
    let nextCell' := (nextCells.equivFin.symm nextCell).1
    rw [hfineFiber_card nextCell]
    have hcard : (containedCells nextCell').card = descendantCount :=
      hcontainedCells_card nextCell'
        (nextCells.equivFin.symm nextCell).2
    have hsum_lower :
        ∑ c ∈ containedCells nextCell', (stateFiber c).card ≥
          (containedCells nextCell').card *
            state.fiberMultiplicity := by
      calc
        _ ≥ ∑ c ∈ containedCells nextCell',
              state.fiberMultiplicity := by
          apply Finset.sum_le_sum
          intro c hc
          have hc' : c ∈ state.cells :=
            (Finset.mem_filter.mp hc).1
          have h_eq :
              stateFiber c =
                Finset.univ.filter fun i : Fin currentFamily.card =>
                  state.parent i =
                    state.cells.equivFin ⟨c, hc'⟩ :=
            hstateFiber_eq c hc'
          rw [h_eq]
          exact state.fiber_lower
            (state.cells.equivFin ⟨c, hc'⟩)
        _ = (containedCells nextCell').card *
              state.fiberMultiplicity := by
          simp [Finset.sum_const] <;> ring
    rw [hcard] at hsum_lower
    exact hsum_lower

  have hfineFiber_upper : ∀ (nextCell : Fin nextCells.card),
      (fineFiber nextCell).card <
        2 * (descendantCount * state.fiberMultiplicity) := by
    intro nextCell
    let nextCell' := (nextCells.equivFin.symm nextCell).1
    rw [hfineFiber_card nextCell]
    have hcard : (containedCells nextCell').card = descendantCount :=
      hcontainedCells_card nextCell'
        (nextCells.equivFin.symm nextCell).2
    have hfm_pos : 0 < state.fiberMultiplicity :=
      state.fiberMultiplicity_pos
    have hsum_upper :
        ∑ c ∈ containedCells nextCell', (stateFiber c).card <
          (containedCells nextCell').card *
            (2 * state.fiberMultiplicity) := by
      calc
        _ ≤ ∑ c ∈ containedCells nextCell',
              (2 * state.fiberMultiplicity - 1) := by
          apply Finset.sum_le_sum
          intro c hc
          have hc' : c ∈ state.cells :=
            (Finset.mem_filter.mp hc).1
          have h_eq :
              stateFiber c =
                Finset.univ.filter fun i : Fin currentFamily.card =>
                  state.parent i =
                    state.cells.equivFin ⟨c, hc'⟩ :=
            hstateFiber_eq c hc'
          rw [h_eq]
          have h :
              (Finset.univ.filter fun i : Fin currentFamily.card =>
                state.parent i =
                  state.cells.equivFin ⟨c, hc'⟩).card <
                2 * state.fiberMultiplicity :=
            state.fiber_upper
              (state.cells.equivFin ⟨c, hc'⟩)
          have hfm_pos : 0 < state.fiberMultiplicity :=
            state.fiberMultiplicity_pos
          omega
        _ = (containedCells nextCell').card *
              (2 * state.fiberMultiplicity - 1) := by
          simp [Finset.sum_const] <;> ring
        _ < (containedCells nextCell').card *
              (2 * state.fiberMultiplicity) := by
          have hpos : 0 < (containedCells nextCell').card := by
            rw [hcard]
            exact hdesc_pos
          have h : 0 < 2 * state.fiberMultiplicity := by positivity
          gcongr
          <;> omega
    rw [hcard] at hsum_upper
    convert hsum_upper using 1 <;> ring

  have hnextCells_nonempty : nextCells.Nonempty := by
    rcases state.cells_nonempty with ⟨currentCell, hcurrentCell⟩
    rcases hunique_parent currentCell hcurrentCell with
      ⟨nextCell, ⟨hnextCell, _⟩, _⟩
    exact ⟨nextCell, hnextCell⟩

  have hparentCount_pos : 0 < nextCells.card :=
    Finset.card_pos.mpr hnextCells_nonempty

  have hfiber_mult_pos :
      0 < descendantCount * state.fiberMultiplicity :=
    Nat.mul_pos hdesc_pos state.fiberMultiplicity_pos

  let blocks :
      UniformFourBlockRelationData
        (rho := rho) currentFamily fineShading := {
    parentCount := nextCells.card
    parentCount_pos := hparentCount_pos
    parent := fineParent
    parent_surjective := by
      intro nextCell
      refine ⟨representative nextCell, ?_⟩
      exact hrepresentative_parent nextCell
    block := block
    block_card := hblock_card
    shading_cover := by
      intro fineIndex
      let nextCell := fineParent fineIndex
      have hi : fineIndex ∈ indices nextCell := by
        have h_eq : fineParent fineIndex = nextCell := by rfl
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ fineIndex, h_eq⟩
      have hcover :
          fineShading.carrier fineIndex ⊆
            (block nextCell).toBodyFamily.union :=
        (blockData nextCell).shading_cover fineIndex hi
      exact hcover
    fiberMultiplicity := descendantCount * state.fiberMultiplicity
    fiberMultiplicity_pos := hfiber_mult_pos
    fiber_lower := by
      intro nextCell
      simpa [fineFiber] using hfineFiber_lower nextCell
    fiber_upper := by
      intro nextCell
      simpa [fineFiber] using hfineFiber_upper nextCell
  }

  let coarseFamily : Kakeya.Streamlined.TubeFamily rho :=
    blocks.coarse

  have hcoarse_card :
      coarseFamily.card = nextCells.card * 4 := by
    simp [coarseFamily, UniformFourBlockRelationData.coarse,
      flattenFixedBlocks_card] <;> rfl

  let coarseParent :
      Fin coarseFamily.card → Fin nextCells.card :=
    fixedBlockIndex

  have hcoarseParent_surjective :
      Function.Surjective coarseParent := by
    intro cell
    refine ⟨finProdFinEquiv (cell, (0 : Fin 4)), ?_⟩
    simp [coarseParent, fixedBlockIndex_finProdFinEquiv]

  let coarseRepresentative
      (cell : Fin nextCells.card) : Fin coarseFamily.card :=
    finProdFinEquiv (cell, (0 : Fin 4))

  have hcoarseRepresentative_parent :
      ∀ (cell : Fin nextCells.card),
        coarseParent (coarseRepresentative cell) = cell := by
    intro cell
    simp [coarseParent, coarseRepresentative,
      fixedBlockIndex_finProdFinEquiv]

  have hcoarse_params_all :
      ∀ (index : Fin coarseFamily.card),
        tubeParamsOfTube (coarseFamily.tube index) =
          tubeParams (representative (coarseParent index)) := by
    intro index
    let cell := coarseParent index
    have h :
        tubeParamsOfTube (coarseFamily.tube index) =
          tubeParams (representative cell) := by
      have h2 := (blockData cell).coarse_parameters
      simpa [coarseFamily, UniformFourBlockRelationData.coarse,
        flattenFixedBlocks_tube_block_slot] using h2 _
    exact h

  have hcoarse_parameter_cell :
      ∀ (index : Fin coarseFamily.card),
        tubeParameterGridIndex base nextLevel
            (indexedTubeParameterPoint4 index) =
          tubeParameterGridIndex base nextLevel
            (indexedTubeParameterPoint4
              (coarseRepresentative (coarseParent index))) := by
    intro index
    let cell := coarseParent index
    have h1 :
        tubeParamsOfTube (coarseFamily.tube index) =
          tubeParams (representative cell) :=
      hcoarse_params_all index
    have hrep_par :
        coarseParent (coarseRepresentative cell) = cell :=
      hcoarseRepresentative_parent cell
    have h2 :
        tubeParamsOfTube
            (coarseFamily.tube (coarseRepresentative cell)) =
          tubeParams (representative cell) := by
      have h2' := hcoarse_params_all (coarseRepresentative cell)
      rw [h2', hrep_par]
    have h4 :
        indexedTubeParameterPoint4 index =
          indexedTubeParameterPoint4
            (coarseRepresentative cell) := by
      simp [indexedTubeParameterPoint4, tubeParams, h1, h2] <;> rfl
    rw [h4]

  have hcoarse_representative_parameter :
      ∀ (cell : Fin nextCells.card),
        ∃ (point : Point 4),
          point ∈ (nextCells.equivFin.symm cell).1 ∧
            tubeParameterGridIndex base nextLevel
                (indexedTubeParameterPoint4
                  (coarseRepresentative cell)) =
              tubeParameterGridIndex base nextLevel point := by
    intro cell
    let nextCell' := (nextCells.equivFin.symm cell).1
    have hnextCell'_in_partition :
        nextCell' ∈ partition nextLevel :=
      (Finset.mem_filter.mp
        (nextCells.equivFin.symm cell).2).1
    have hnextCell'_nonempty : nextCell'.Nonempty :=
      (hpart_props nextLevel hnext_le_levels).1
        nextCell' hnextCell'_in_partition |>.1
    rcases hnextCell'_nonempty with ⟨point, hpoint⟩
    have h4 :
        indexedTubeParameterPoint4 (coarseRepresentative cell) =
          indexedTubeParameterPoint4 (representative cell) := by
      have hrep_par2 :
          coarseParent (coarseRepresentative cell) = cell :=
        hcoarseRepresentative_parent cell
      have hparams1 :
          tubeParamsOfTube
              (coarseFamily.tube (coarseRepresentative cell)) =
            tubeParams (representative cell) := by
        have htmp := hcoarse_params_all
          (coarseRepresentative cell)
        rw [htmp, hrep_par2]
      simp [indexedTubeParameterPoint4, tubeParams, hparams1] <;> rfl
    have h6 :
        tubeParameterGridIndex base nextLevel
            (indexedTubeParameterPoint4 (representative cell)) =
          tubeParameterGridIndex base nextLevel point := by
      rcases state.representative_parameter
          (state.parent (representative cell)) with
        ⟨q, hq_in_cell, hq_idx⟩
      have hq_in_nextCell : q ∈ nextCell' := by
        have hspec := hcellToNext_spec
          (state.parent (representative cell))
        have hrep :
            cellToNext (state.parent (representative cell)) = cell :=
          hrepresentative_parent cell
        rw [hrep] at hspec
        exact hspec hq_in_cell
      have h7 :
          tubeParameterGridIndex base nextLevel
              (indexedTubeParameterPoint4 (representative cell)) =
            tubeParameterGridIndex base nextLevel q :=
        tubeParameterGridIndex_coarsening hbase1 (by
          rw [state.parameter_cell (representative cell), hq_idx])
          hnext_le
      have h8 :
          tubeParameterGridIndex base nextLevel q =
            tubeParameterGridIndex base nextLevel point :=
        h_all_points_in_cell_same_index nextCell'
          hnextCell'_in_partition q point hq_in_nextCell hpoint
      rw [h7, h8]
    refine ⟨point, hpoint, ?_⟩
    rw [h4, h6]

  have hcoarse_fiber_card :
      ∀ (cell : Fin nextCells.card),
        (Finset.univ.filter fun index : Fin coarseFamily.card =>
          coarseParent index = cell).card = 4 := by
    intro cell
    let f : Fin 4 → Fin coarseFamily.card :=
      fun k => finProdFinEquiv (cell, k)
    have h_inj : Function.Injective f := by
      intro k1 k2 h
      have h' : (cell, k1) = (cell, k2) :=
        finProdFinEquiv.injective h
      exact Prod.ext_iff.mp h' |>.2
    have h_equiv :
        (Finset.univ.filter fun index : Fin coarseFamily.card =>
          coarseParent index = cell) =
            Finset.image f Finset.univ := by
      ext index
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        let k : Fin 4 := fixedBlockSlot index
        have h_fbi : fixedBlockIndex index = cell := h
        have h_k : f k = index := by
          have h1 :
              finProdFinEquiv.symm index =
                (fixedBlockIndex index, fixedBlockSlot index) := by
            rfl
          have h2 :
              index =
                finProdFinEquiv
                  (fixedBlockIndex index, fixedBlockSlot index) := by
            exact (finProdFinEquiv.right_inv index).symm
          rw [h2, h_fbi]
          <;> rfl
        exact Finset.mem_image.mpr
          ⟨k, Finset.mem_univ k, h_k⟩
      · intro h
        rcases Finset.mem_image.mp h with ⟨k, _, hk⟩
        have h3 : index = f k := hk.symm
        rw [h3]
        simp [coarseParent, f,
          fixedBlockIndex_finProdFinEquiv]
    rw [h_equiv]
    rw [Finset.card_image_of_injective]
    · simp
    · intro k1 k2 h
      have h' : (cell, k1) = (cell, k2) :=
        finProdFinEquiv.injective h
      exact Prod.ext_iff.mp h' |>.2

  have hcoarse_fiber_lower :
      ∀ (cell : Fin nextCells.card),
        4 ≤ (Finset.univ.filter fun index : Fin coarseFamily.card =>
          coarseParent index = cell).card := by
    intro cell
    rw [hcoarse_fiber_card cell] <;> norm_num

  have hcoarse_fiber_upper :
      ∀ (cell : Fin nextCells.card),
        (Finset.univ.filter fun index : Fin coarseFamily.card =>
          coarseParent index = cell).card < 8 := by
    intro cell
    rw [hcoarse_fiber_card cell] <;> norm_num

  have hcoarse_nonempty : coarseFamily.Nonempty := by
    have h : coarseFamily.card = nextCells.card * 4 :=
      hcoarse_card
    rw [Kakeya.Streamlined.TubeFamily.Nonempty]
    omega

  have hcoarse_vertical : IsInVerticalChart coarseFamily := by
    apply flattenFixedBlocks_isInVerticalChart
    intro j
    exact (blockData j).coarse_vertical

  have hcoarse_parameter_bounds :
      ∀ (index : Fin coarseFamily.card),
        |(tubeParams index).a| ≤ 12 ∧
          |(tubeParams index).b| ≤ 12 ∧
          |(tubeParams index).c| ≤ 2 ∧
          |(tubeParams index).d| ≤ 2 := by
    intro index
    let cell := fixedBlockIndex index
    have h1 :
        tubeParamsOfTube (coarseFamily.tube index) =
          tubeParams (representative cell) :=
      hcoarse_params_all index
    have h3 :
        tubeParams index = tubeParams (representative cell) := by
      simpa [tubeParams] using h1
    rw [h3]
    exact state.parameter_bounds (representative cell)

  exact ⟨{
    nextLevel_le_current := hnext_le
    nextLevel_le := hnext_le_levels
    blocks := blocks
    representative := representative
    representative_parent := hrepresentative_parent
    nextCells := nextCells
    nextCells_eq := by rfl
    nextCells_nonempty := hnextCells_nonempty
    parentCount_eq := by rfl
    parameter_close := hparameter_close
    block_vertical :=
      fun parentIndex => (blockData parentIndex).coarse_vertical
    block_base :=
      fun parentIndex => (blockData parentIndex).coarse_base
    block_parameters :=
      fun parentIndex slot =>
        (blockData parentIndex).coarse_parameters slot
    coarse_nonempty := hcoarse_nonempty
    coarse_vertical := hcoarse_vertical
    coarse_parameter_bounds := hcoarse_parameter_bounds
    coarse_cells := nextCells
    coarse_cells_eq := by rfl
    coarse_parent := coarseParent
    coarse_parent_surjective := hcoarseParent_surjective
    coarse_parameter_cell := hcoarse_parameter_cell
    coarse_representative := coarseRepresentative
    coarse_representative_parent := hcoarseRepresentative_parent
    coarse_representative_parameter :=
      hcoarse_representative_parameter
    coarse_fiber_lower := hcoarse_fiber_lower
    coarse_fiber_upper := hcoarse_fiber_upper
  }⟩

end Kakeya.Assouad
