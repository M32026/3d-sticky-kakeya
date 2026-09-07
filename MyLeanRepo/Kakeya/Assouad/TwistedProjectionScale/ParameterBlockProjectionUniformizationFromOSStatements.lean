import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockProjectionUniformityStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockProjectionArithmeticStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalBlockProjectionCorridorStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSCinematicGlobalizationStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSLevelCellSystemStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSPreparationStatement

/-!
# Projection uniformization from the completed projected-fiber OS packages

This is the remaining quantitative assembly in the proof of the one-scale
estimate used for paper Proposition 7.1.

The projected-fiber preparation retains a same-family dense shading and the
actual planar OS tree.  At the scale selected after the local cinematic
pullback, the level-cell package gives a finite disjoint decomposition with
uniform cell areas and controlled cell thickenings.  The local parameter block
lies in one genuine cinematic corridor, so the closed cinematic globalization
theorem compares its area lower bound with the coarse neighborhood of the
global projected set.

No new geometric assertion is hidden here.  In particular, this boundary does
not use projected-tube pair overlaps, replace fiber-integrated multiplicity by
tube-count multiplicity, or manufacture an unrelated global shading.
-/

namespace Kakeya.Assouad

/--
Assemble the projection-uniform continuation from the four already frozen
paper-faithful geometric producers.

The proof is responsible only for choosing the comparison radius and absorbing
the explicit corridor-cell and single-cell constants into the exponent budget
of `ParameterBlockProjectionUniformizationStatement`.
-/
def ParameterBlockProjectionUniformizationFromOSStatement : Prop :=
  ParameterBlockProjectionArithmeticStatement →
    PerTubeMassPruningStatement →
      ProjectedFiberOSPreparationStatement →
        ProjectedFiberOSLevelCellSystemStatement →
          ParameterLocalBlockProjectionCorridorStatement →
            ProjectedFiberOSCinematicGlobalizationStatement →
              ParameterBlockProjectionUniformizationStatement

end Kakeya.Assouad
