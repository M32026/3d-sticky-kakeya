import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockProjectionUniformityStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSCinematicGlobalizationStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSLevelCellSystemStatement

/-!
# Quantitative arithmetic in paper Lemma 7.12

The comparison radius is the scale of the local block selected by Lemma 7.10.
At this radius the cinematic corridor meets only `O_base(rho⁻¹)` projected
OS cells, while each cell has `rho`-thickening area `O_base(rho²)`.
Consequently the globalization cost is `O_base(rho)`.

The representative cinematic pullback gives the matching local lower bound.
Using

* approximately `rho⁻¹` translated copies;
* approximately `(rho / delta)^(1 - 20 epsilon²)` local parameters;
* one mass floor of size `delta^(2 + 4 eta)` per representative tube; and
* PYZ loss `epsilon³ / 100`,

its area is at least

`c_base * rho * (delta / rho)^q`

with `q < epsilon` when `epsilon < 1/100` and
`1000 eta < epsilon³`.  The remaining fixed constant is absorbed by
shrinking `delta`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
A base-dependent integer large enough for the Lemma 7.12 corridor after
choosing `rho = localBlock.blockScale`.
-/
def parameterBlockProjectionRadiusBlocks (base : ℕ) : ℕ :=
  (30100 + 2 * base) * base + 1

/--
The sole quantitative absorption leaf remaining in the corrected
Lemma 7.12 route.

The grid base is fixed before `delta`; all constants depending on it may
therefore be absorbed into the returned small-scale threshold.
-/
def ParameterBlockProjectionArithmeticStatement : Prop :=
  ∀ base : ℕ,
    3 ≤ base →
    ∀ epsilon eta : ℝ,
      0 < epsilon →
      epsilon < 1 / 100 →
      0 < eta →
      1000 * eta < epsilon ^ 3 →
      ∃ delta₀ : ℝ,
        0 < delta₀ ∧
        delta₀ < 1 ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              ∀ f : SlopeFunction,
                ∀ prepared :
                    ProjectedFiberOSPreparationData
                      (eta := eta) Y f,
                  prepared.base = base →
                  ∀ windowedShading :
                      Kakeya.Streamlined.TubeShading F,
                    ∀ C lambda : ENNReal,
                      ∀ clustered :
                          TubeParameterClusterFrostmanData
                            F windowedShading C lambda delta,
                        ∀ localBlock :
                            ParameterLocalFullBlockData
                              clustered epsilon,
                          ∀ representatives :
                              ParameterLocalRepresentativeBlockData
                                localBlock,
                            ∀ amplification :
                                ParameterBlockAmplificationData
                                  delta localBlock.blockScale
                                  (1 - 20 * epsilon ^ 2)
                                  localBlock.centeredPoints,
                              ∀ pullback :
                                  ParameterBlockRepresentativeCinematicPullbackData
                                    localBlock representatives
                                    amplification f
                                    (parameterBlockProjectionPYZLoss
                                      epsilon)
                                    (parameterBlockProjectionPerTubeThreshold
                                      delta eta),
                                ∀ level : ℕ,
                                  ∀ cellSystem :
                                      ProjectedFiberOSLevelCellSystemData
                                        (rho := localBlock.blockScale)
                                        prepared level,
                                    volume (twistedUnion pullback.shading f) ≥
                                      Kakeya.realRpowENN
                                          (delta / localBlock.blockScale)
                                          epsilon *
                                        4 *
                                        (projectedFiberOSCinematicCellBound
                                          prepared.base level 131
                                          (parameterBlockProjectionRadiusBlocks
                                            base) : ENNReal) *
                                        projectedFiberOSPreparedCellThickeningBound
                                          prepared localBlock.blockScale

end Kakeya.Assouad
