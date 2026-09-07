import MyLeanRepo.Kakeya.Assouad.WZ1.BalancedCoarseGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.InducedTripleRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9WideSplitStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.WideBranchProjectionHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseAffineMaps
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarsePreparationLemmas

/-!
# Paper-faithful leaves for Proposition 8.9 wide coarse preparation

The wide branch is split at the two genuine mathematical boundaries left
after the affine algebra and exponent arithmetic have been closed:

1. apply Lemma 8.12 three times to the current active coordinate projection,
   refining the induced graph after every selection;
2. transfer source strip nonconcentration through the common affine map and
   the balanced-cell assignment.

The final conditional assembly then uses the already closed balanced coarse
graph, exact transpose identity, and parameter-absorption lemmas.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/--
The output of the three sequential anisotropic rescaling rounds in PDF
Proposition 8.9.

Each rescaling is applied to the active coordinate projection of the graph
produced by the preceding round.  This prevents the invalid shortcut of
choosing three unrelated large subsets and intersecting them afterwards.
The same endpoint affine map is used for both `G₁` and `G₂`, so the exact
transpose dot identity remains available.
-/
structure WZ1Proposition8_9WideSequentialRescalingData
    (delta epsilon eta : ℝ)
    (parameters : WZ1Proposition8_9Parameters epsilon)
    (F G₁ G₂ : DiscreteSet 2)
    (H : Finset (Point2 × Point2 × Point2))
    (data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H) where
  firstRescale :
    WZ1AnisotropicFrostmanRescalingData
      (wz1ActiveTripleProjection data.refinedH 1)
      (wideCoarsePhiG
        data.direction data.width data.width_pos
        data.base 0 data.direction_unit)
      delta data.width
      (parameters.stripEpsilon * eta / 10)
      (Kakeya.realRpowENN
        delta (-(2 * parameters.workingLambda)))
  firstGraph : Finset (Point2 × Point2 × Point2)
  firstGraph_subset : firstGraph ⊆ data.refinedH
  firstUniform :
    WZ1UniformTripleDensity
      (((1 / 256 : ENNReal) *
          Kakeya.realRpowENN delta eta) / 16)
      data.selectedF firstRescale.selected data.selectedG₂
      firstGraph
  secondRescale :
    WZ1AnisotropicFrostmanRescalingData
      (wz1ActiveTripleProjection firstGraph 2)
      (wideCoarsePhiG
        data.direction data.width data.width_pos
        data.base 0 data.direction_unit)
      delta data.width
      (parameters.stripEpsilon * eta / 10)
      (Kakeya.realRpowENN
        delta (-(2 * parameters.workingLambda)))
  secondGraph : Finset (Point2 × Point2 × Point2)
  secondGraph_subset : secondGraph ⊆ firstGraph
  secondUniform :
    WZ1UniformTripleDensity
      ((((1 / 256 : ENNReal) *
          Kakeya.realRpowENN delta eta) / 16) / 16)
      data.selectedF firstRescale.selected secondRescale.selected
      secondGraph
  thirdRescale :
    WZ1AnisotropicFrostmanRescalingData
      (wz1ActiveTripleProjection secondGraph 0)
      (wideCoarsePhiF
        data.direction data.width data.width_pos
        data.direction_unit)
      delta data.width
      (parameters.stripEpsilon * eta / 10)
      (Kakeya.realRpowENN
        delta (-(2 * parameters.workingLambda)))
  sourceGraph : Finset (Point2 × Point2 × Point2)
  sourceGraph_subset : sourceGraph ⊆ secondGraph
  sourceUniform :
    WZ1UniformTripleDensity
      (((((1 / 256 : ENNReal) *
          Kakeya.realRpowENN delta eta) / 16) / 16) / 16)
      thirdRescale.selected firstRescale.selected secondRescale.selected
      sourceGraph

/--
Produce the three synchronized rescaling rounds.

The active-projection restriction can worsen the source Frostman constant.
That loss must be paid explicitly and absorbed into
`delta^(-2 * workingLambda)`; the original
`delta^(-workingLambda)` constant may not simply be reused.
-/
def WZ1Proposition8_9WideSequentialRescalingStatement : Prop :=
  WZ1TripartiteHypergraphRefinementStatement →
    WZ1AnisotropicFrostmanRescalingStatement →
      ∀ epsilon : ℝ,
        ∀ parameters : WZ1Proposition8_9Parameters epsilon,
        0 < epsilon → epsilon < 1 →
          ∃ etaCap : ℝ,
            0 < etaCap ∧
            ∀ eta : ℝ, 0 < eta → eta ≤ etaCap →
              ∃ delta₀ : ℝ,
                0 < delta₀ ∧ delta₀ ≤ 1 ∧
                ∀ {delta : ℝ}
                  {F G₁ G₂ : DiscreteSet 2}
                  {H : Finset (Point2 × Point2 × Point2)},
                  0 < delta → delta ≤ delta₀ →
                  ∀ data :
                    WZ1Proposition8_9CommonStripData
                      delta epsilon eta parameters F G₁ G₂ H,
                    Real.rpow delta (1 - epsilon / 10) <
                        data.width →
                      Nonempty
                        (WZ1Proposition8_9WideSequentialRescalingData
                          delta epsilon eta parameters F G₁ G₂ H data)

/--
Transfer the two weighted source strip-nonconcentration estimates in one
common-strip package to the balanced coarse endpoint sets produced by the
sequential rescaling, retaining a factor-two exponent margin.

This is stated directly at the Proposition 8.9 parameter boundary.  In
particular, the theorem itself must derive every active-projection,
rescaling-retention, balanced-fiber, strip-pullback, and fixed-constant loss;
the caller is not allowed to postulate a summary constant inequality.
-/
def WZ1Proposition8_9WideCoarseLineNonconcentrationStatement : Prop :=
  ∀ epsilon : ℝ,
    ∀ parameters : WZ1Proposition8_9Parameters epsilon,
    0 < epsilon → epsilon < 1 →
      ∃ etaCap : ℝ,
        0 < etaCap ∧
        ∀ eta : ℝ, 0 < eta → eta ≤ etaCap →
          ∃ delta₀ : ℝ,
            0 < delta₀ ∧ delta₀ ≤ 1 ∧
            ∀ {delta : ℝ}
              {F G₁ G₂ : DiscreteSet 2}
              {H : Finset (Point2 × Point2 × Point2)},
              0 < delta → delta ≤ delta₀ →
              ∀ data :
                WZ1Proposition8_9CommonStripData
                  delta epsilon eta parameters F G₁ G₂ H,
                Real.rpow delta (1 - epsilon / 10) <
                    data.width →
                  ∀ sequential :
                    WZ1Proposition8_9WideSequentialRescalingData
                      delta epsilon eta parameters F G₁ G₂ H data,
                    WZ1LineNonConcentration
                        (delta / data.width)
                        (parameters.projectionLambda / 2)
                        parameters.zeta
                        sequential.firstRescale.coarse ∧
                      WZ1LineNonConcentration
                        (delta / data.width)
                        (parameters.projectionLambda / 2)
                        parameters.zeta
                        sequential.secondRescale.coarse

/--
Assemble the original wide-coarse package from the two genuine leaves.

This stage applies `anisotropic_balanced_coarse_graph_uniform`, weakens the
three coarse Frostman constants, invokes the line-nonconcentration transfer
twice, and constructs the actual-source witness using
`wideCoarseDotIdentity`.  It must not identify a snapped coarse dot value
with its actual transformed source value.
-/
def WZ1Proposition8_9WideCoarseFromSplitStatement : Prop :=
  WZ1Proposition8_9WideSequentialRescalingStatement →
    WZ1Proposition8_9WideCoarseLineNonconcentrationStatement →
      WZ1Proposition8_9WideCoarsePreparationStatement

end Kakeya.Assouad
