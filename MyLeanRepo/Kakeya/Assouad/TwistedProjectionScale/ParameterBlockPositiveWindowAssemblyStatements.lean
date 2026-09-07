import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockRepresentativeCinematicStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockProjectionUniformityStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterWindowClusterCardinalityStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.PositiveWindowStatements

/-!
# Assemble the weighted parameter-block route

The replication-invariant Section 7 route is now split at its genuine
mathematical boundaries:

* weighted collapsed-parameter clustering;
* selection and recentering of one full local block;
* translation amplification of that complete local pattern;
* copied-shading cinematic Hölder/PYZ and pullback to the source block.

This module freezes the remaining exponent and scale assembly.  It must
produce the bounded no-distinct positive-window estimate, including the
selected radius, same-family subshading, retained density, and projection
neighborhood inequality.  It may not replace the copied local shading by a
parameter-only or cardinality-only surrogate.
-/

namespace Kakeya.Assouad

/--
Assemble the paper-faithful weighted parameter-block proof of the bounded
positive-window one-scale estimate.

The explicit premises are either completed repository theorems whose proofs
still reside behind compatibility target paths, or the two substantial leaves
currently being proved.  Keeping them explicit prevents an open target from
importing another target and makes the final quantitative assembly auditable.

The projection-uniformization premise is essential.  The cinematic pullback
is indexed by one reindexed local parameter block, whereas the conclusion must
return a dense shading on the original family and compare its entire twisted
projection with its coarse neighborhood.  A local volume lower bound alone
does not provide that local-to-global comparison.
-/
def ParameterBlockPositiveWindowAssemblyStatement : Prop :=
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
                        PositiveWindowParameterFrostmanScaleAdjustableEtaFromParametersBoundedNoDistinctStatement

end Kakeya.Assouad
