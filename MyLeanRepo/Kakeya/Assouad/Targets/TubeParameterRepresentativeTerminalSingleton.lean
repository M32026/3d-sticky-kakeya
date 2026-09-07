import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterRepresentativeTerminalSingletonStatement

/-!
WZ2 Proposition 7.1: prove terminal singleton cells for one actual parameter
representative per occupied delta-scale terminal cell.
-/

namespace Kakeya.Assouad

theorem tube_parameter_representative_terminal_singleton :
    TubeParameterRepresentativeTerminalSingletonStatement := by
  intro delta family active base levels regularized representatives cell hcell
  have h_main : ∃ (point : Point 4), point ∈ representatives.parameters ∧
      tubeParameterGridCell base levels representatives.parameters point = cell := by
    simpa [tubeParameterGridPartition, Finset.mem_image] using hcell
  rcases h_main with ⟨point, hpoint_in, hcell_eq⟩
  have h_point_in_cell : point ∈ cell := by
    rw [←hcell_eq]
    simp [tubeParameterGridCell, hpoint_in]
  have h_all_eq : ∀ candidate ∈ cell, candidate = point := by
    intro candidate hcand
    have hcand' : candidate ∈ tubeParameterGridCell base levels representatives.parameters point :=
      hcell_eq.symm ▸ hcand
    have hcand_and : candidate ∈ representatives.parameters ∧
        tubeParameterGridIndex base levels candidate = tubeParameterGridIndex base levels point := by
      simpa [tubeParameterGridCell, Finset.mem_filter] using hcand'
    have hcand_in : candidate ∈ representatives.parameters := hcand_and.1
    have hcand_idx : tubeParameterGridIndex base levels candidate =
        tubeParameterGridIndex base levels point := hcand_and.2
    rcases representatives.parameter_terminal_cell candidate hcand_in with ⟨cell_c, hcand_eq, hcand_cell⟩
    rcases representatives.parameter_terminal_cell point hpoint_in with ⟨cell_p, hpoint_eq, hpoint_cell⟩
    have h_val_eq : cell_c.val = cell_p.val := by
      rw [←hcand_cell, ←hpoint_cell, hcand_idx]
    have h_cells_eq : cell_c = cell_p := by
      exact Subtype.ext h_val_eq
    rw [hcand_eq, hpoint_eq, h_cells_eq]
  have h_cell_singleton : cell = {point} := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_singleton]
    constructor
    · intro hx
      exact h_all_eq x hx
    · intro hx
      rw [hx]
      exact h_point_in_cell
  rw [h_cell_singleton]
  simp

end Kakeya.Assouad
