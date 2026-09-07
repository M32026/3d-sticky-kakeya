import MyLeanRepo.Kakeya.Assouad.Targets.CoaxialShiftedTubesEssentiallyDistinct
import MyLeanRepo.Kakeya.Assouad.Targets.TubeParameterRepresentativeGridTreeFromSingleton
import MyLeanRepo.Kakeya.Assouad.Targets.TubeParameterRepresentativeTerminalSingleton
import MyLeanRepo.Kakeya.Assouad.Targets.TubeParameterTerminalCellOSLift
import MyLeanRepo.Kakeya.Assouad.Targets.TubeParameterTerminalCellOSSelectionTransfer
import MyLeanRepo.Kakeya.Assouad.Targets.UniformFourBlockRelationDensity
import MyLeanRepo.Kakeya.Assouad.Targets.WindowParameterCellFourBlock
import MyLeanRepo.Kakeya.Assouad.TubePieceThickeningDensity
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingUniformRefinement

/-!
# Closed direct inputs for the corrected grid OS iteration

The underlying proved theorems retain conditional adapter statements for
modularity.  This module discharges those already closed leaves once and
exports the direct callable producers consumed by the higher-level finite
iteration.
-/

namespace Kakeya.Assouad

theorem tube_parameter_representative_grid_tree_input :
    TubeParameterRepresentativeGridTreeStatement :=
  tube_parameter_representative_grid_tree_from_singleton
    tube_parameter_representative_terminal_singleton

theorem tube_parameter_terminal_cell_os_lift_input :
    TubeParameterTerminalCellOSLiftInput :=
  tube_parameter_terminal_cell_os_lift
    os_branching_uniform_refinement
    tube_parameter_representative_grid_tree_input

theorem tube_parameter_terminal_cell_os_selection_transfer_input :
    TubeParameterTerminalCellOSSelectionTransferInput :=
  tube_parameter_terminal_cell_os_selection_transfer
    tube_volume_scaling

theorem window_parameter_cell_four_block_input :
    WindowParameterCellFourBlockInput :=
  window_parameter_cell_four_block
    coaxial_shifted_tubes_essentially_distinct

theorem uniform_four_block_relation_density_input :
    UniformFourBlockRelationDensityInput :=
  uniform_four_block_relation_density
    tube_volume_scaling
    tube_piece_thickening_density

end Kakeya.Assouad
