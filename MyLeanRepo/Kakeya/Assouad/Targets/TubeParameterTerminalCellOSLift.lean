import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterTerminalCellOSLiftStatement

/-!
WZ2 Proposition 7.1: run OS branching on terminal-cell representatives and
lift every surviving complete delta-scale cell fiber.
-/

namespace Kakeya.Assouad

theorem tube_parameter_terminal_cell_os_lift :
    TubeParameterTerminalCellOSLiftStatement := by
  intro hOS hRepTree delta family active base levels hbase regularized representatives
  let A : DiscreteSet 4 := representatives.parameters
  have hA_nonempty : A.Nonempty := representatives.parameters_nonempty
  let P : ℕ → Finset (Finset (Point 4)) :=
    fun level => tubeParameterGridPartition base level A
  have h_tree := hRepTree (family := family) (active := active) base levels hbase regularized representatives
  rcases h_tree with ⟨h_partition, h_atomic, h_child_parent, h_children_bound⟩
  have h_childBound_pos : 0 < (base + 1) ^ 4 := by positivity
  rcases hOS (α := Point 4) A hA_nonempty levels ((base + 1) ^ 4) h_childBound_pos P
      h_partition h_atomic h_child_parent h_children_bound with
    ⟨A', hA'_nonempty, hA'_sub, h_retention, branchExponent, h_branch_bound, h_branch_uniform⟩

  let g : Fin family.card → Fin 4 → ℤ := indexedTubeTerminalCellIndex base levels
  let h : Point 4 → Fin 4 → ℤ := tubeParameterGridIndex base levels
  let selectedCells : Finset (Fin 4 → ℤ) :=
    regularized.cells.filter fun cell => ∃ point ∈ A', h point = cell
  let selected : Finset (Fin family.card) :=
    regularized.selected.filter fun index => g index ∈ selectedCells

  -- h is injective on A (representatives of distinct cells are distinct points)
  have h_inj_A : Set.InjOn h (A : Set (Point 4)) := by
    intro p1 hp1 p2 hp2 heq
    rcases representatives.parameter_terminal_cell p1 hp1 with ⟨c1, hc11, hc12⟩
    rcases representatives.parameter_terminal_cell p2 hp2 with ⟨c2, hc21, hc22⟩
    have h_eq1 : tubeParameterGridIndex base levels p1 = tubeParameterGridIndex base levels p2 := by
      simpa [h] using heq
    have h3 : c1.1 = c2.1 := by
      rw [←hc12, ←hc22]
      exact h_eq1
    have h4 : c1 = c2 := Subtype.ext h3
    rw [hc11, hc21, h4]

  have h_inj_A' : Set.InjOn h (A' : Set (Point 4)) := by
    intro p1 hp1 p2 hp2 heq
    exact h_inj_A (hA'_sub hp1) (hA'_sub hp2) heq

  -- A'.image h = selectedCells
  have h_img_eq : A'.image h = selectedCells := by
    ext cell
    simp only [Finset.mem_image, selectedCells, Finset.mem_filter]
    constructor
    · rintro ⟨point, hpoint, rfl⟩
      have h2 : point ∈ A := hA'_sub hpoint
      rcases representatives.parameter_terminal_cell point h2 with ⟨c, _, hc2⟩
      have h4 : h point = c.1 := by simpa [h] using hc2
      have h3 : h point ∈ regularized.cells := by
        rw [h4]
        exact c.2
      exact ⟨h3, point, hpoint, rfl⟩
    · rintro ⟨_, point, hpoint, rfl⟩
      exact ⟨point, hpoint, rfl⟩

  have h_selectedCells_card : selectedCells.card = A'.card := by
    have h1 : (A'.image h).card = A'.card := Finset.card_image_of_injOn h_inj_A'
    have h2 : selectedCells = A'.image h := h_img_eq.symm
    rw [h2]
    exact h1

  have h_selectedCells_nonempty : selectedCells.Nonempty := by
    rcases hA'_nonempty with ⟨point, hpoint⟩
    have h2 : h point ∈ selectedCells := by
      rw [←h_img_eq]
      exact Finset.mem_image.mpr ⟨point, hpoint, rfl⟩
    exact ⟨h point, h2⟩

  let fiberSize : (Fin 4 → ℤ) → ℕ := fun cell =>
    (regularized.selected.filter fun i => g i = cell).card

  -- regularized.selected partitions as union of its cell fibers
  have h_reg_sum : regularized.selected.card = ∑ cell ∈ regularized.cells, fiberSize cell := by
    have h1 : regularized.selected = regularized.cells.biUnion (fun cell => regularized.selected.filter (fun i => g i = cell)) := by
      ext i
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro hi
        have h2 : g i ∈ regularized.cells := by
          rw [regularized.cells_eq]
          exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
        exact ⟨g i, h2, hi, rfl⟩
      · rintro ⟨cell, _, hi, _⟩
        exact hi
    have h_disj : ∀ cell1 ∈ regularized.cells, ∀ cell2 ∈ regularized.cells, cell1 ≠ cell2 →
        Disjoint (regularized.selected.filter (fun i => g i = cell1))
          (regularized.selected.filter (fun i => g i = cell2)) := by
      intro cell1 _ cell2 _ hne
      apply Finset.disjoint_left.mpr
      intro i hi1 hi2
      have h3 : g i = cell1 := (Finset.mem_filter.mp hi1).2
      have h4 : g i = cell2 := (Finset.mem_filter.mp hi2).2
      rw [h3] at h4
      exact hne h4
    rw [h1, Finset.card_biUnion h_disj]

  -- selected fibers equal regularized fibers on selectedCells
  have h_fiber_eq : ∀ cell ∈ selectedCells,
      (selected.filter fun i => g i = cell) = regularized.selected.filter (fun i => g i = cell) := by
    intro cell hcell
    ext i
    simp only [selected, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hi, _⟩, hgi⟩
      exact ⟨hi, hgi⟩
    · rintro ⟨hi, hgi⟩
      have h2 : g i ∈ selectedCells := by
        rw [hgi]
        exact hcell
      exact ⟨⟨hi, h2⟩, hgi⟩

  -- selected partitions as union of its cell fibers
  have h_sel_sum : selected.card = ∑ cell ∈ selectedCells, fiberSize cell := by
    have h1 : selected = selectedCells.biUnion (fun cell => selected.filter (fun i => g i = cell)) := by
      ext i
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro hi
        have h2 : g i ∈ selectedCells := (Finset.mem_filter.mp hi).2
        exact ⟨g i, h2, hi, rfl⟩
      · rintro ⟨cell, _, hi, _⟩
        exact hi
    have h_disj : ∀ cell1 ∈ selectedCells, ∀ cell2 ∈ selectedCells, cell1 ≠ cell2 →
        Disjoint (selected.filter (fun i => g i = cell1))
          (selected.filter (fun i => g i = cell2)) := by
      intro cell1 _ cell2 _ hne
      apply Finset.disjoint_left.mpr
      intro i hi1 hi2
      have h3 : g i = cell1 := (Finset.mem_filter.mp hi1).2
      have h4 : g i = cell2 := (Finset.mem_filter.mp hi2).2
      rw [h3] at h4
      exact hne h4
    rw [h1, Finset.card_biUnion h_disj]
    apply Finset.sum_congr rfl
    intro cell hcell
    rw [h_fiber_eq cell hcell]

  -- cells.card = A.card
  have h_cells_card : regularized.cells.card = A.card := by
    let f : regularized.cells → Point 4 := fun cell => indexedTubeParameterPoint4 (representatives.index cell)
    have h_inj : Function.Injective f := representatives.representative_injective
    have h_univ : (Finset.univ : Finset regularized.cells) = regularized.cells.attach := by
      ext ⟨x, hx⟩
      simp
    have h1 : A = regularized.cells.attach.image f := by
      have h3 : A = representatives.parameters := by rfl
      rw [h3, representatives.parameters_eq, h_univ]
    have h2 : A.card = regularized.cells.attach.card := by
      rw [h1]
      exact Finset.card_image_of_injective _ h_inj
    have h3 : regularized.cells.attach.card = regularized.cells.card := Finset.card_attach
    rw [←h3, ←h2]

  -- upper sum bound
  have h_upper_sum : (∑ cell ∈ regularized.cells, fiberSize cell) ≤ 2 * regularized.fiberMultiplicity * regularized.cells.card := by
    have h1 : ∀ cell ∈ regularized.cells, fiberSize cell ≤ 2 * regularized.fiberMultiplicity := by
      intro cell hcell
      have h2 : fiberSize cell < 2 * regularized.fiberMultiplicity := regularized.fiber_upper cell hcell
      exact le_of_lt h2
    calc
      (∑ cell ∈ regularized.cells, fiberSize cell)
        ≤ ∑ cell ∈ regularized.cells, (2 * regularized.fiberMultiplicity) := Finset.sum_le_sum h1
      _ = 2 * regularized.fiberMultiplicity * regularized.cells.card := by
        simp [Finset.sum_const, mul_comm]

  -- lower sum bound
  have h_lower_sum : (∑ cell ∈ selectedCells, fiberSize cell) ≥ regularized.fiberMultiplicity * selectedCells.card := by
    have h1 : ∀ cell ∈ selectedCells, fiberSize cell ≥ regularized.fiberMultiplicity := by
      intro cell hcell
      have h2 : cell ∈ regularized.cells := (Finset.mem_filter.mp hcell).1
      exact regularized.fiber_lower cell h2
    calc
      (∑ cell ∈ selectedCells, fiberSize cell)
        ≥ ∑ cell ∈ selectedCells, regularized.fiberMultiplicity := Finset.sum_le_sum h1
      _ = regularized.fiberMultiplicity * selectedCells.card := by
        simp [Finset.sum_const, mul_comm]

  -- selected_nonempty
  have h_selected_nonempty : selected.Nonempty := by
    rcases h_selectedCells_nonempty with ⟨cell, hcell⟩
    have h2 : cell ∈ regularized.cells := (Finset.mem_filter.mp hcell).1
    have h3 : 0 < fiberSize cell := by
      have h4 : regularized.fiberMultiplicity ≤ fiberSize cell := regularized.fiber_lower cell h2
      exact lt_of_lt_of_le regularized.fiberMultiplicity_pos h4
    have h5 : (regularized.selected.filter (fun i => g i = cell)).Nonempty := Finset.card_pos.mp h3
    rcases h5 with ⟨i, hi⟩
    have h6 : i ∈ regularized.selected := (Finset.mem_filter.mp hi).1
    have h7 : g i = cell := (Finset.mem_filter.mp hi).2
    have h8 : i ∈ selected := by
      simp only [selected, Finset.mem_filter]
      exact ⟨h6, by { rw [h7]; exact hcell }⟩
    exact ⟨i, h8⟩

  -- selected.image g = selectedCells
  have h_selected_image_cells : selected.image g = selectedCells := by
    ext cell
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact (Finset.mem_filter.mp hi).2
    · intro hcell
      have h2 : cell ∈ regularized.cells := (Finset.mem_filter.mp hcell).1
      have h3 : 0 < fiberSize cell := by
        have h4 : regularized.fiberMultiplicity ≤ fiberSize cell := regularized.fiber_lower cell h2
        exact lt_of_lt_of_le regularized.fiberMultiplicity_pos h4
      have h5 : (regularized.selected.filter (fun i => g i = cell)).Nonempty := Finset.card_pos.mp h3
      rcases h5 with ⟨i, hi⟩
      have h6 : i ∈ regularized.selected := (Finset.mem_filter.mp hi).1
      have h7 : g i = cell := (Finset.mem_filter.mp hi).2
      have h8 : i ∈ selected := by
        simp only [selected, Finset.mem_filter]
        exact ⟨h6, by { rw [h7]; exact hcell }⟩
      exact ⟨i, h8, h7⟩

  -- retention bound
  have h_retention' : (regularized.selected.card : ℝ) ≤
      2 * (2 * (Nat.log 2 ((base + 1) ^ 4) + 1) : ℝ) ^ levels * (selected.card : ℝ) := by
    let C : ℝ := (2 * (Nat.log 2 ((base + 1) ^ 4) + 1) : ℝ)
    have h1 : (regularized.selected.card : ℝ) ≤ (2 * regularized.fiberMultiplicity * regularized.cells.card : ℝ) := by
      exact_mod_cast (calc
        regularized.selected.card = ∑ cell ∈ regularized.cells, fiberSize cell := h_reg_sum
        _ ≤ 2 * regularized.fiberMultiplicity * regularized.cells.card := h_upper_sum)
    have h2 : (regularized.fiberMultiplicity * selectedCells.card : ℝ) ≤ (selected.card : ℝ) := by
      exact_mod_cast (calc
        regularized.fiberMultiplicity * selectedCells.card ≤ ∑ cell ∈ selectedCells, fiberSize cell := h_lower_sum
        _ = selected.card := h_sel_sum.symm)
    have h3 : (regularized.cells.card : ℝ) = (A.card : ℝ) := by exact_mod_cast h_cells_card
    have h4 : (selectedCells.card : ℝ) = (A'.card : ℝ) := by exact_mod_cast h_selectedCells_card
    have h5 : (A.card : ℝ) ≤ C ^ levels * (A'.card : ℝ) := h_retention
    calc
      (regularized.selected.card : ℝ)
        ≤ (2 * regularized.fiberMultiplicity * regularized.cells.card : ℝ) := h1
      _ = 2 * (regularized.fiberMultiplicity : ℝ) * (A.card : ℝ) := by
          rw [h3]
      _ ≤ 2 * (regularized.fiberMultiplicity : ℝ) * (C ^ levels * (A'.card : ℝ)) := by
          gcongr
      _ = 2 * C ^ levels * ((regularized.fiberMultiplicity : ℝ) * (selectedCells.card : ℝ)) := by
          rw [←h4]
          ring
      _ ≤ 2 * C ^ levels * (selected.card : ℝ) := by
          have h_pos : 0 ≤ (2 * C ^ levels : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_left h2 h_pos

  refine' ⟨A', hA'_nonempty, hA'_sub, selectedCells, rfl, h_selectedCells_nonempty,
    selected, rfl, h_selected_nonempty, Finset.filter_subset _ _,
    (fun index hindex hcell => by
      simp only [selected, Finset.mem_filter]
      exact ⟨hindex, hcell⟩),
    h_selected_image_cells,
    (fun cell hcell => by
      have h_eq := h_fiber_eq cell hcell
      rw [h_eq]
      have h2 : cell ∈ regularized.cells := (Finset.mem_filter.mp hcell).1
      exact regularized.fiber_lower cell h2),
    (fun cell hcell => by
      have h_eq := h_fiber_eq cell hcell
      rw [h_eq]
      have h2 : cell ∈ regularized.cells := (Finset.mem_filter.mp hcell).1
      exact regularized.fiber_upper cell h2),
    h_retention', branchExponent, h_branch_bound, h_branch_uniform⟩

end Kakeya.Assouad
