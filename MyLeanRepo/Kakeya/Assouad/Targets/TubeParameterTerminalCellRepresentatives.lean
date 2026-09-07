import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterTerminalCellRepresentativesStatement

/-!
WZ2 Proposition 7.1: choose one actual parameter representative from every
occupied terminal delta-scale parameter cell.
-/

namespace Kakeya.Assouad

theorem tube_parameter_terminal_cell_representatives :
    TubeParameterTerminalCellRepresentativesStatement := by
  intro delta family active base levels regularized
  let fiber (cell : regularized.cells) : Finset (Fin family.card) :=
    regularized.selected.filter fun index =>
      indexedTubeTerminalCellIndex base levels index = cell.1
  have h_fiber_nonempty : ∀ (cell : regularized.cells), (fiber cell).Nonempty := by
    intro cell
    have h1 : regularized.fiberMultiplicity ≤ (fiber cell).card :=
      regularized.fiber_lower cell.1 cell.2
    have h2 : 0 < regularized.fiberMultiplicity := regularized.fiberMultiplicity_pos
    have h3 : 0 < (fiber cell).card := lt_of_lt_of_le h2 h1
    exact Finset.card_pos.mp h3
  let index (cell : regularized.cells) : Fin family.card :=
    Classical.choose (h_fiber_nonempty cell)
  have h_index_mem : ∀ (cell : regularized.cells), index cell ∈ fiber cell := by
    intro cell
    exact Classical.choose_spec (h_fiber_nonempty cell)
  have h_index_selected : ∀ (cell : regularized.cells), index cell ∈ regularized.selected := by
    intro cell
    have h : index cell ∈ fiber cell := h_index_mem cell
    exact (Finset.mem_filter.mp h).1
  have h_index_cell : ∀ (cell : regularized.cells),
      indexedTubeTerminalCellIndex base levels (index cell) = cell.1 := by
    intro cell
    have h : index cell ∈ fiber cell := h_index_mem cell
    exact (Finset.mem_filter.mp h).2
  let parameters : DiscreteSet 4 :=
    Finset.univ.image fun cell : regularized.cells =>
      indexedTubeParameterPoint4 (index cell)
  have h_parameters_nonempty : parameters.Nonempty := by
    rcases regularized.cells_nonempty with ⟨x, hx⟩
    let cell : regularized.cells := ⟨x, hx⟩
    have h : indexedTubeParameterPoint4 (index cell) ∈ parameters := by
      apply Finset.mem_image.mpr
      exact ⟨cell, Finset.mem_univ cell, rfl⟩
    exact ⟨_, h⟩
  have h_injective : Function.Injective (fun cell : regularized.cells => indexedTubeParameterPoint4 (index cell)) := by
    intro c1 c2 h
    have h1 : indexedTubeTerminalCellIndex base levels (index c1) = indexedTubeTerminalCellIndex base levels (index c2) := by
      simp only [indexedTubeTerminalCellIndex]
      exact congr_arg (tubeParameterGridIndex base levels) h
    have h2 : c1.1 = c2.1 := by
      rw [h_index_cell c1, h_index_cell c2] at h1
      exact h1
    exact Subtype.ext h2
  have h_parameter_terminal_cell : ∀ point ∈ parameters,
      ∃ cell : regularized.cells,
        point = indexedTubeParameterPoint4 (index cell) ∧
        tubeParameterGridIndex base levels point = cell.1 := by
    intro point hpoint
    have h_exists : ∃ (cell : regularized.cells), indexedTubeParameterPoint4 (index cell) = point := by
      simpa [parameters, Finset.mem_image] using hpoint
    rcases h_exists with ⟨cell, hcell⟩
    have hcell' : point = indexedTubeParameterPoint4 (index cell) := hcell.symm
    refine ⟨cell, hcell', ?_⟩
    rw [hcell']
    exact h_index_cell cell
  exact ⟨index, h_index_selected, h_index_cell, parameters, rfl, h_parameters_nonempty, h_injective, h_parameter_terminal_cell⟩

end Kakeya.Assouad
