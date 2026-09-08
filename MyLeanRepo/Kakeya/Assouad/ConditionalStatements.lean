import MyLeanRepo.Kakeya.Assouad.Inputs
import MyLeanRepo.Kakeya.Assouad.Statements

/-!
# WZ2 internal reductions with explicit black-box boundaries

Each statement below proves only a WZ2-owned transition.  External analytic
results are supplied as ordinary hypotheses, preventing SeedProver runs from
silently re-formalizing CV, OSW, or PYZ.
-/

namespace Kakeya.Assouad

/-- Build the C²-grain counterexamples using the frozen WZ1/CV/OSW output. -/
def C2GrainsFromInputsStatement : Prop :=
  SubunitAdmissibleCeilingInput →
    ExtremalCounterexamplesFromFailureStatement →
      C2GrainsInput →
        C2GrainsFromFailureStatement

/--
Assemble the geometric lower bound in WZ Lemma 30 from the local estimate for
one scalar-projection cover ball.  The hard cylinder/Fubini estimate remains
an explicit predecessor rather than being duplicated inside the covering
argument.
-/
def TubeSegmentProjectionCoveringFromFiberStatement : Prop :=
  TubeSegmentProjectionFiberVolumeStatement →
    TubeSegmentProjectionCoveringLowerBoundStatement

/--
Carry out the WZ2 scale-selection argument while receiving the normalized PYZ
maximal estimate as a black-box hypothesis.
-/
def TwistedProjectionScaleFromInputsStatement : Prop :=
  PYZInput →
    TwistedProjectionScaleStatement

/--
Iterate the one-scale projection estimate to obtain the final lower bound,
using the paper-exact induced-shading geometry after each scale selected by
the one-scale lemma.  The scale choice and the uniform refinement cannot be
split into an unconditional arbitrary-scale coarsening proposition.
-/
def TwistedProjectionEstimateFromScaleStatement : Prop :=
  TwistedProjectionScaleStatement →
    TwistedProjectionInducedShadingStatement →
    TwistedProjectionEstimateStatement

/--
Convert the every-scale Frostman fiber bound to the Tube-Wolff count using the
independent tube-volume comparison.  The same absolute constant is exposed in
the conclusion so no geometric factor is hidden.
-/
def FrostmanToTubeWolffStatement : Prop :=
  TubeVolumeScalingStatement →
    ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∀ F : Kakeya.Streamlined.TubeFamily delta,
        ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
          ∀ C : ENNReal,
            U.IsFrostmanAtEveryScale C →
              TubeWolffBound F (24 * C)

/--
Close the large-slope contradiction once the geometric overload certificate
has been produced.  The every-scale Frostman hypothesis inside
`IsExtremalPair` supplies the normalized Convex-Wolff count.
-/
def LargeSlopeTechnicalFromOverloadStatement : Prop :=
  TubeVolumeScalingStatement →
    LargeSlopeStep4WitnessStatement →
      LargeSlopeConvexOverloadStatement →
        LargeSlopeTechnicalStatement

/--
Assemble the extremal, C²-grain, and large-slope outputs into a small twisted
projection.  The five substantial predecessor theorems are explicit inputs.
-/
def SmallTwistedProjectionFromInputsStatement : Prop :=
  C2GrainsFromFailureStatement →
    LargeSlopeRefinementStatement →
    LargeSlopeTechnicalStatement →
      AnisotropicRescalingStatement →
        TubeVolumeScalingStatement →
          SmallTwistedProjectionFromFailureStatement

/--
Assemble WZ Lemma 8 from the frozen cleaned-target leaves.

The source every-scale Frostman constant is the extremal constant
`delta^(-theta/1000)`.  It is deliberately distinct from the grain AD
constant used by the projection estimate.  The assembly constructs no target
`UniformTubeStructure`; it returns the direct Section 7 package.
-/
def AnisotropicRescalingFromCleanedInputsStatement : Prop :=
  WeightedEssentiallyDistinctSelectionStatement →
    NonessentialTubeAxisAlignmentStatement →
      NonessentialTargetTubeParameterClusterStatement →
        AnisotropicTubeParamsInverseClusterStatement →
          TubeParameterClusterPrismContainmentStatement →
            TubeParameterPrismGeometryStatement →
              BoundedCoaxialThreeTubeImageCoverStatement →
                AnisotropicParameterPreparationStatement →
                  CleanedAnisotropicTargetNonemptyStatement →
                    CleanedTargetCardinalityUpperStatement →
                        CleanedTargetCardinalityScaleTransferStatement →
                          CleanedTargetCardinalityProductStatement →
                            CleanedTargetCardinalityLossStatement →
                              CommonContainerTargetTubeParameterClusterStatement →
                                CleanedTargetTubeWolffFromSourceStatement →
                                  CleanedTargetParameterFrostmanFromSourceStatement →
                                  CleanedAnisotropicMassLossAbsorptionStatement →
                                    CleanedTargetDensityTransferStatement →
                                      CleanedTargetLambdaDensityAbsorptionStatement →
                                        CleanedTargetTubeWolffAbsorptionStatement →
                                          CleanedTargetParameterFrostmanAbsorptionStatement →
                                            CleanedAnisotropicTwistedProjectionUpperStatement →
                                              CleanedProjectionConstantTransferStatement →
                                                CleanedAnisotropicProjectionAbsorptionStatement →
                                                  AnisotropicRescalingStatement

end Kakeya.Assouad
