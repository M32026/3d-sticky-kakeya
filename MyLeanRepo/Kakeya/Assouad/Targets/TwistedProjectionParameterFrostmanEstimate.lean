import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.FinalAssemblyStatements
import MyLeanRepo.Kakeya.Assouad.Targets.FullWindowLiftedDensityAbsorption
import MyLeanRepo.Kakeya.Assouad.Targets.GridOSEffectiveLossSchedule
import MyLeanRepo.Kakeya.Assouad.Targets.GridOSFinalConstantAbsorption
import MyLeanRepo.Kakeya.Assouad.Targets.GridOSFiniteRun
import MyLeanRepo.Kakeya.Assouad.Targets.GridOSFiniteStepSchedule
import MyLeanRepo.Kakeya.Assouad.Targets.GridOSFiniteThreshold
import MyLeanRepo.Kakeya.Assouad.Targets.GridOSLastStepTerminal
import MyLeanRepo.Kakeya.Assouad.Targets.GridOSParameterFrostmanEstimate
import MyLeanRepo.Kakeya.Assouad.Targets.GridOSScaleGrowth
import MyLeanRepo.Kakeya.Assouad.Targets.GridOSStateDichotomy
import MyLeanRepo.Kakeya.Assouad.Targets.GridOSTelescoping
import MyLeanRepo.Kakeya.Assouad.Targets.GridOSTerminalClosure
import MyLeanRepo.Kakeya.Assouad.Targets.GridOSTermination
import MyLeanRepo.Kakeya.Assouad.Targets.GridOSTransitionReadyState
import MyLeanRepo.Kakeya.Assouad.Targets.GridOSWindowBudgetDichotomy
import MyLeanRepo.Kakeya.Assouad.Targets.PerTubeMassPruning
import MyLeanRepo.Kakeya.Assouad.Targets.SelectedScaleTerminalProjection
import MyLeanRepo.Kakeya.Assouad.Targets.TubeParameterGridCoarseningLevel
import MyLeanRepo.Kakeya.Assouad.Targets.TubeParameterGridOSFourBlockPackage
import MyLeanRepo.Kakeya.Assouad.Targets.TubeParameterGridOSInitialState
import MyLeanRepo.Kakeya.Assouad.Targets.TubeParameterGridOSStateTransition
import MyLeanRepo.Kakeya.Assouad.Targets.TubeParameterGridParameterSelection
import MyLeanRepo.Kakeya.Assouad.Targets.TubeParameterTerminalCellFiberRegularization
import MyLeanRepo.Kakeya.Assouad.Targets.TubeParameterTerminalCellRepresentatives
import MyLeanRepo.Kakeya.Assouad.Targets.UniformFourBlockParameterFrostmanTransfer
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSBoundedOneScaleFromBlock
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSClosedLeafInputs
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSInitialReadyStateInput
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingIntervalCellCount
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.PlanarThickeningFortyVolume
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.RelationInducedShadingFromParameters
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SelectedTubeNonconcentrationTransfer
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridCellDiameter

/-!
WZ2 Section 7: prove the final twisted-projection lower bound from the two
non-concentration certificates actually exported by WZ Lemma 8.

The indexed four-parameter Frostman bound is an explicit input. It is not
inferred from the carrier-model Tube-Wolff predicate.
-/

namespace Kakeya.Assouad

theorem twisted_projection_parameter_frostman_estimate :
    TwistedProjectionParameterFrostmanEstimateFromBlockStatement := by
  intro hScaleProfile hParameterCluster hWindowCluster hLocalBlock
    hAmplification hHalfParameterPYZ hCompactSelection hCompactArea
    hAssignedContainment hBlockPullback hBlockProjectionUniformity
    hBlockAssembly
  have hBounded : GridOSBoundedOneScaleInput :=
    grid_os_bounded_one_scale_from_block
      hScaleProfile hParameterCluster hWindowCluster hLocalBlock
      hAmplification hHalfParameterPYZ hCompactSelection hCompactArea
      hAssignedContainment hBlockPullback hBlockProjectionUniformity
      hBlockAssembly
  have hInitial : TubeParameterGridOSInitialStateInput :=
    tube_parameter_grid_os_initial_state
      tube_parameter_grid_parameter_selection
      per_tube_mass_pruning
      tube_parameter_terminal_cell_fiber_regularization
      tube_parameter_terminal_cell_representatives
      tube_parameter_terminal_cell_os_lift_input
      tube_parameter_terminal_cell_os_selection_transfer_input
      selected_tube_nonconcentration_transfer
  have hFourBlock : TubeParameterGridOSFourBlockPackageInput :=
    tube_parameter_grid_os_four_block_package
      tube_parameter_representative_grid_tree_input
      os_branching_interval_cell_count
      tube_parameter_grid_cell_diameter
      window_parameter_cell_four_block_input
  have hTransition : TubeParameterGridOSStateTransitionInput :=
    tube_parameter_grid_os_state_transition
      hFourBlock
      uniform_four_block_relation_density_input
      uniform_four_block_parameter_frostman_transfer
      full_window_lifted_density_absorption
      twisted_projection_relation_induced_shading_from_parameters
      planar_thickening_forty_volume
  have hDichotomy : GridOSStateDichotomyInput :=
    grid_os_state_dichotomy
      grid_os_scale_growth
      grid_os_window_budget_dichotomy
      tube_parameter_grid_coarsening_level
      hTransition
  have hFinite : GridOSFiniteStepScheduleInput :=
    grid_os_finite_step_schedule
      grid_os_finite_threshold
      grid_os_last_step_terminal
      hBounded
      hDichotomy
      grid_os_transition_ready_state
  have hTerminal : GridOSTerminalClosureInput :=
    grid_os_terminal_closure
      grid_os_telescoping
      selected_scale_terminal_projection
  exact
    grid_os_parameter_frostman_estimate
      hBounded
      hInitial
      grid_os_effective_loss_schedule
      grid_os_initial_ready_state_input
      hDichotomy
      grid_os_transition_ready_state
      hFinite
      grid_os_finite_run
      grid_os_termination
      hTerminal
      grid_os_final_constant_absorption

end Kakeya.Assouad
