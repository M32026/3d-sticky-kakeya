import MyLeanRepo.Kakeya.Assouad.PYZInput
import MyLeanRepo.Kakeya.Assouad.Targets.HalfWindowMassSelection
import MyLeanRepo.Kakeya.Assouad.Targets.ReflectedSlopeCinematic
import MyLeanRepo.Kakeya.Assouad.Targets.SignedWindowParameterFrostmanScaleFromParametersBoundedNoDistinct
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CompactAssignedCinematicHolder
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSFiniteStepScheduleStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockPositiveWindowAssemblyStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.Section7Reflection

/-!
# Bounded signed one-scale input from the weighted block theorem

This is the mechanical analytic adapter used by the corrected finite grid OS
iteration.  It preserves the explicit substantial leaves of the historical
Theorem 5.2 final boundary and changes only the output interface.
-/

namespace Kakeya.Assouad

/-- Assemble the bounded signed one-scale oracle from the weighted block route. -/
def GridOSBoundedOneScaleFromBlockStatement : Prop :=
  ScaleProfileCrossingStatement →
    TubeParameterClusterFrostmanStatement →
      ParameterWindowClusterCardinalityStatement →
        ParameterLocalFullBlockSelectionStatement →
          ParameterBlockAmplificationStatement →
            HalfParameterCinematicPYZGeneralStatement →
              CompactSubshadingSelectionStatement →
                CompactTubeTwistedProjectionAreaStatement →
                  AssignedCurveProjectionContainmentFromVerticalChartStatement →
                    ParameterBlockRepresentativeCinematicPullbackStatement →
                      ParameterBlockProjectionUniformizationStatement →
                        ParameterBlockPositiveWindowAssemblyStatement →
                          GridOSBoundedOneScaleInput

theorem grid_os_bounded_one_scale_from_block :
    GridOSBoundedOneScaleFromBlockStatement := by
  intro hScaleProfile hParameterCluster hWindowCluster hLocalBlock
    hAmplification hHalfParameterPYZ hCompactSelection hCompactArea
    hAssignedContainment hBlockPullback hBlockProjectionUniformity
    hBlockAssembly
  have hPositive :
      PositiveWindowParameterFrostmanScaleAdjustableEtaFromParametersBoundedNoDistinctStatement :=
    hBlockAssembly
      hScaleProfile hParameterCluster hWindowCluster hLocalBlock
      hAmplification hHalfParameterPYZ hCompactSelection hCompactArea
      hAssignedContainment hBlockPullback hBlockProjectionUniformity
  exact
    signed_window_parameter_frostman_scale_from_parameters_bounded_no_distinct
      half_window_mass_selection
      reflected_slope_cinematic
      section7_vertical_reflection
      hPositive
      compact_assigned_cinematic_holder_from_vertical_chart
      pyz_input

end Kakeya.Assouad
