import MyLeanRepo.Kakeya.Assouad.Targets.TwistedProjectionParameterFrostmanEstimate
import MyLeanRepo.Kakeya.Assouad.Targets.ScaleProfileCrossing
import MyLeanRepo.Kakeya.Assouad.Targets.TubeParameterClusterFrostman
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterWindowClusterCardinality
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalSpacingCandidateFromInterval
import MyLeanRepo.Kakeya.Assouad.Targets.ParameterSpacingIntervalCertificate
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalFrostmanBlockPruning
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalFullBlockFromSpacing
import MyLeanRepo.Kakeya.Assouad.Targets.ParameterBlockAmplification
import MyLeanRepo.Kakeya.Assouad.Targets.HalfParameterCinematicPYZGeneral
import MyLeanRepo.Kakeya.Assouad.Targets.CompactSubshadingSelection
import MyLeanRepo.Kakeya.Assouad.Targets.CompactTubeTwistedProjectionArea
import MyLeanRepo.Kakeya.Assouad.Targets.AssignedCurveProjectionContainment
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockRepresentativeCinematicPullback
import MyLeanRepo.Kakeya.Assouad.Targets.ParameterBlockProjectionUniformizationFromOS
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockProjectionArithmetic
import MyLeanRepo.Kakeya.Assouad.Targets.PerTubeMassPruning
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSPreparation
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSLevelCellSystem
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalBlockProjectionCorridor
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSCinematicGlobalization
import MyLeanRepo.Kakeya.Assouad.Targets.ParameterBlockPositiveWindowAssembly

/-!
# Pure WZ2 parameter-Frostman lower bound

This module assembles the already sorry-free Section 7 twisted-projection
parameter-Frostman estimate into a standalone theorem for Node 8.
-/

namespace Kakeya.Assouad

/-- The closed Section 7 parameter-Frostman projection lower bound. -/
theorem pure_wz2_twisted_projection_parameter_frostman_lower_bound :
    TwistedProjectionParameterFrostmanEstimateStatement := by
  have hScaleProfile : ScaleProfileCrossingStatement :=
    scale_profile_crossing
  have hParameterCluster : TubeParameterClusterFrostmanStatement :=
    tube_parameter_cluster_frostman
  have hWindowCluster : ParameterWindowClusterCardinalityStatement :=
    parameter_window_cluster_cardinality
  have hSpacing : ParameterLocalSpacingCandidateStatement :=
    parameter_local_spacing_candidate_from_interval
      parameter_spacing_interval_certificate
  have hLocalBlock : ParameterLocalFullBlockSelectionStatement :=
    parameter_local_full_block_from_spacing
      hSpacing parameter_local_frostman_block_pruning
  have hAmplification : ParameterBlockAmplificationStatement :=
    parameter_block_amplification
  have hHalfPYZ : HalfParameterCinematicPYZGeneralStatement :=
    half_parameter_cinematic_pyz_general
  have hCompactSelection : CompactSubshadingSelectionStatement :=
    compact_subshading_selection
  have hCompactArea : CompactTubeTwistedProjectionAreaStatement :=
    compact_tube_twisted_projection_area
  have hContainment :
      AssignedCurveProjectionContainmentFromVerticalChartStatement :=
    assigned_curve_projection_containment_from_vertical_chart
  have hPullback :
      ParameterBlockRepresentativeCinematicPullbackStatement :=
    parameter_block_representative_cinematic_pullback
  have hUniformity :
      ParameterBlockProjectionUniformizationStatement :=
    parameter_block_projection_uniformization_from_os
      parameter_block_projection_arithmetic
      per_tube_mass_pruning
      projected_fiber_os_preparation
      projected_fiber_os_level_cell_system
      parameter_local_block_projection_corridor
      projected_fiber_os_cinematic_globalization
  have hAssembly : ParameterBlockPositiveWindowAssemblyStatement :=
    parameter_block_positive_window_assembly
  exact twisted_projection_parameter_frostman_estimate
    hScaleProfile hParameterCluster hWindowCluster hLocalBlock
    hAmplification hHalfPYZ hCompactSelection hCompactArea
    hContainment hPullback hUniformity hAssembly

end Kakeya.Assouad
