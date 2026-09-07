import MyLeanRepo.Kakeya.Assouad.WZ1.BalancedCoarseGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.Theorem5_2LeafStatements

/-!
# Paper-faithful split of the wide branch of PDF Proposition 8.9

The paper first performs three sequential anisotropic rescalings.  Each
retained vertex set is immediately synchronized with the current graph by an
induced restriction and a fresh application of the hypergraph refinement
lemma.  Only after all three restrictions does the proof snap the transformed
graph to `tau`-cells.

The second stage performs the fixed-scale cell localization and affine
normalization needed for exact standard separation.  These stages are split
because independent applications of the rescaling lemma do not by themselves
produce one graph supported on all three selected vertex sets.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/--
The synchronized coarse package produced by the sequential rescaling stage.

`source_witness` keeps both the actual source edge and the actual transformed
triple that was snapped to a coarse edge.  The dot identity is the paper's
anisotropic relation

`sourceDot = width * transformedDot`.

It is deliberately not replaced by equality between the source dot value and
the snapped coarse dot value.
-/
structure WZ1Proposition8_9WideCoarseData
    (delta epsilon eta : ℝ)
    (parameters : WZ1Proposition8_9Parameters epsilon)
    (F G₁ G₂ : DiscreteSet 2)
    (H : Finset (Point2 × Point2 × Point2))
    (data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H) where
  scale : ℝ
  scale_eq : scale = delta / data.width
  scale_pos : 0 < scale
  scale_le_projectionDelta₀ :
    scale ≤ parameters.projectionDelta₀
  coarseF : DiscreteSet 2
  coarseG₁ : DiscreteSet 2
  coarseG₂ : DiscreteSet 2
  coarseH : Finset (Point2 × Point2 × Point2)
  coarseF_nonempty : coarseF.Nonempty
  coarseG₁_nonempty : coarseG₁.Nonempty
  coarseG₂_nonempty : coarseG₂.Nonempty
  coarseF_bounded :
    ∀ point ∈ coarseF, dist point 0 ≤ 3
  coarseG₁_bounded :
    ∀ point ∈ coarseG₁, dist point 0 ≤ 3
  coarseG₂_bounded :
    ∀ point ∈ coarseG₂, dist point 0 ≤ 3
  coarseF_separated :
    coarseF.IsDeltaSeparated scale
  coarseG₁_separated :
    coarseG₁.IsDeltaSeparated scale
  coarseG₂_separated :
    coarseG₂.IsDeltaSeparated scale
  coarseF_frostman :
    coarseF.IsFrostman scale 1
      (Kakeya.realRpowENN
        scale (-parameters.projectionLambda))
  coarseF_frostman_margin :
    coarseF.IsFrostman scale 1
      (Kakeya.realRpowENN
        scale (-(parameters.projectionLambda / 2)))
  coarseG₁_frostman :
    coarseG₁.IsFrostman scale 1
      (Kakeya.realRpowENN
        scale (-parameters.projectionLambda))
  coarseG₁_frostman_margin :
    coarseG₁.IsFrostman scale 1
      (Kakeya.realRpowENN
        scale (-(parameters.projectionLambda / 2)))
  coarseG₂_frostman :
    coarseG₂.IsFrostman scale 1
      (Kakeya.realRpowENN
        scale (-parameters.projectionLambda))
  coarseG₂_frostman_margin :
    coarseG₂.IsFrostman scale 1
      (Kakeya.realRpowENN
        scale (-(parameters.projectionLambda / 2)))
  first_line_nonconcentration :
    WZ1LineNonConcentration
      scale parameters.projectionLambda parameters.zeta coarseG₁
  first_line_nonconcentration_margin :
    WZ1LineNonConcentration
      scale (parameters.projectionLambda / 2)
        parameters.zeta coarseG₁
  second_line_nonconcentration :
    WZ1LineNonConcentration
      scale parameters.projectionLambda parameters.zeta coarseG₂
  second_line_nonconcentration_margin :
    WZ1LineNonConcentration
      scale (parameters.projectionLambda / 2)
        parameters.zeta coarseG₂
  uniform_margin :
    WZ1UniformTripleDensity
      (Kakeya.realRpowENN delta eta / (2 ^ 27 : ENNReal))
      coarseF coarseG₁ coarseG₂ coarseH
  uniform :
    WZ1UniformTripleDensity
      (Kakeya.realRpowENN scale parameters.alpha)
      coarseF coarseG₁ coarseG₂ coarseH
  source_witness :
    ∀ coarseEdge ∈ coarseH,
      ∃ sourceEdge ∈ data.refinedH,
        ∃ transformedEdge : Point2 × Point2 × Point2,
          inner ℝ sourceEdge.1
              (sourceEdge.2.1 - sourceEdge.2.2) =
            data.width *
              inner ℝ transformedEdge.1
                (transformedEdge.2.1 - transformedEdge.2.2) ∧
          dist transformedEdge.1 coarseEdge.1 ≤ scale ∧
          dist transformedEdge.2.1 coarseEdge.2.1 ≤ scale ∧
          dist transformedEdge.2.2 coarseEdge.2.2 ≤ scale ∧
          dist transformedEdge.1 0 ≤ 2 ∧
          dist transformedEdge.2.1 0 ≤ 2 ∧
          dist transformedEdge.2.2 0 ≤ 2 ∧
          1 / 2 ≤ dist transformedEdge.1 0 ∧
          1 / 2 ≤ dist transformedEdge.2.1 transformedEdge.2.2

/--
Construct the synchronized coarse package in the wide common-strip branch.

The intended proof order is exactly the paper order:

1. rescale the active `G₁` projection and refine the induced graph;
2. rescale the active `G₂` projection and refine again;
3. rescale the active `F` projection by the matching transpose map and refine;
4. snap the resulting literal transformed graph to balanced `tau`-cells;
5. refine the coarse graph once more.
-/
def WZ1Proposition8_9WideCoarsePreparationStatement : Prop :=
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
                        (WZ1Proposition8_9WideCoarseData
                          delta epsilon eta parameters F G₁ G₂ H data)

/--
Finish the wide package from the synchronized coarse package.

This stage may pass to one fixed-scale coarse-cell triple and apply a common
affine normalization.  It must preserve the two line-nonconcentration
estimates and transport the normalized covering conclusion through the source
witnesses; it must not identify snapped coarse dot values with actual source
dot values.
-/
def WZ1Proposition8_9WideNormalizedFromCoarseStatement : Prop :=
  WZ1Proposition8_9WideCoarsePreparationStatement →
    WZ1Proposition8_9WideNormalizedPreparationStatement

/-- Mechanical assembly of the two paper-faithful wide stages. -/
def WZ1Proposition8_9WideSplitAssemblyStatement : Prop :=
  WZ1Proposition8_9WideCoarsePreparationStatement →
    WZ1Proposition8_9WideNormalizedFromCoarseStatement →
      WZ1Proposition8_9WideNormalizedPreparationStatement

end Kakeya.Assouad
