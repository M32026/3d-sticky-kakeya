import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockPositiveWindowAssemblyStatements

/-!
# Final parameter-Frostman projection assembly

The weighted positive-window block theorem is the substantial analytic input.
This boundary performs the signed-window and selected-scale iteration without
re-proving that local-block theorem.
-/

namespace Kakeya.Assouad

/--
Assemble the final parameter-Frostman projection estimate from the weighted
positive-window block theorem.
-/
def TwistedProjectionParameterFrostmanEstimateFromBlockStatement : Prop :=
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
                          TwistedProjectionParameterFrostmanEstimateStatement

end Kakeya.Assouad
