import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9WideSplitStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.GridCenter
import MyLeanRepo.Kakeya.Assouad.WZ1.WideBranchProjectionHelpers

/-!
# Fixed-cell normalization for Proposition 8.9 wide branch

The coarse package is normalized in three dependent stages:

1. retain one fixed absolute-size cell triple with quantitative density,
   Frostman, and line-nonconcentration bounds;
2. normalize those same retained cells by the common endpoint similarity and
   contragredient first-coordinate map;
3. transport normalized covering through the recorded snapped-dot error to
   the actual source graph.

The intermediate records retain one coherent graph throughout.  In
particular, the transport stage cannot replace actual source witnesses by
unrelated coarse centers.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/--
One fixed absolute-size cell triple in the synchronized coarse package.

The fields already absorb the fixed cell-count loss using the stronger
Frostman, line, and density margins stored in the coarse package.
-/
structure WZ1Proposition8_9WideFixedCellData
    {delta epsilon eta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    (coarse :
      WZ1Proposition8_9WideCoarseData
        delta epsilon eta parameters F G₁ G₂ H data) where
  ambientCellF : DiscreteSet 2
  ambientCellG₁ : DiscreteSet 2
  ambientCellG₂ : DiscreteSet 2
  inducedH : Finset (Point2 × Point2 × Point2)
  cellH : Finset (Point2 × Point2 × Point2)
  cellF : DiscreteSet 2
  cellG₁ : DiscreteSet 2
  cellG₂ : DiscreteSet 2
  centerF : Point2
  centerG₁ : Point2
  centerG₂ : Point2
  ambientCellF_eq :
    ambientCellF =
      coarse.coarseF.filter
        (fun point =>
          gridCenter (1 / 100) point = centerF)
  ambientCellG₁_eq :
    ambientCellG₁ =
      coarse.coarseG₁.filter
        (fun point =>
          gridCenter (1 / 100) point = centerG₁)
  ambientCellG₂_eq :
    ambientCellG₂ =
      coarse.coarseG₂.filter
        (fun point =>
          gridCenter (1 / 100) point = centerG₂)
  inducedH_eq :
    inducedH =
      coarse.coarseH.filter
        (fun edge =>
          gridCenter (1 / 100) edge.1 = centerF ∧
            gridCenter (1 / 100) edge.2.1 = centerG₁ ∧
            gridCenter (1 / 100) edge.2.2 = centerG₂)
  cellH_subset : cellH ⊆ inducedH
  cellF_eq :
    cellF = wz1ActiveTripleProjection cellH 0
  cellG₁_eq :
    cellG₁ = wz1ActiveTripleProjection cellH 1
  cellG₂_eq :
    cellG₂ = wz1ActiveTripleProjection cellH 2
  cellF_subset : cellF ⊆ ambientCellF
  cellG₁_subset : cellG₁ ⊆ ambientCellG₁
  cellG₂_subset : cellG₂ ⊆ ambientCellG₂
  cellF_nonempty : cellF.Nonempty
  cellG₁_nonempty : cellG₁.Nonempty
  cellG₂_nonempty : cellG₂.Nonempty
  cellH_nonempty : cellH.Nonempty
  cellF_ball :
    ∀ point ∈ cellF, dist point centerF ≤ 1 / 100
  cellG₁_ball :
    ∀ point ∈ cellG₁, dist point centerG₁ ≤ 1 / 100
  cellG₂_ball :
    ∀ point ∈ cellG₂, dist point centerG₂ ≤ 1 / 100
  cellH_support :
    ∀ edge ∈ cellH,
      edge.1 ∈ cellF ∧
        edge.2.1 ∈ cellG₁ ∧
        edge.2.2 ∈ cellG₂
  cellF_separated :
    cellF.IsDeltaSeparated coarse.scale
  cellG₁_separated :
    cellG₁.IsDeltaSeparated coarse.scale
  cellG₂_separated :
    cellG₂.IsDeltaSeparated coarse.scale
  cellF_frostman :
    cellF.IsFrostman coarse.scale 1
      (Kakeya.realRpowENN
        coarse.scale (-parameters.projectionLambda))
  cellF_frostman_margin :
    cellF.IsFrostman coarse.scale 1
      (Kakeya.realRpowENN
        coarse.scale (-(3 * parameters.projectionLambda / 4)))
  cellG₁_frostman :
    cellG₁.IsFrostman coarse.scale 1
      (Kakeya.realRpowENN
        coarse.scale (-parameters.projectionLambda))
  cellG₁_frostman_margin :
    cellG₁.IsFrostman coarse.scale 1
      (Kakeya.realRpowENN
        coarse.scale (-(3 * parameters.projectionLambda / 4)))
  cellG₂_frostman :
    cellG₂.IsFrostman coarse.scale 1
      (Kakeya.realRpowENN
        coarse.scale (-parameters.projectionLambda))
  cellG₂_frostman_margin :
    cellG₂.IsFrostman coarse.scale 1
      (Kakeya.realRpowENN
        coarse.scale (-(3 * parameters.projectionLambda / 4)))
  first_line_nonconcentration :
    WZ1LineNonConcentration
      coarse.scale parameters.projectionLambda
        parameters.zeta cellG₁
  first_line_nonconcentration_margin :
    WZ1LineNonConcentration
      coarse.scale (3 * parameters.projectionLambda / 4)
        parameters.zeta cellG₁
  second_line_nonconcentration :
    WZ1LineNonConcentration
      coarse.scale parameters.projectionLambda
        parameters.zeta cellG₂
  second_line_nonconcentration_margin :
    WZ1LineNonConcentration
      coarse.scale (3 * parameters.projectionLambda / 4)
        parameters.zeta cellG₂
  uniform :
    WZ1UniformTripleDensity
      (Kakeya.realRpowENN coarse.scale parameters.alpha)
      cellF cellG₁ cellG₂ cellH
  quantitative_separation :
    ∀ edge ∈ cellH,
      1 / 3 ≤ dist edge.1 0 ∧
        2 / 5 ≤ dist edge.2.1 edge.2.2

/-- A global producer for one fixed-cell package at every small scale. -/
def WZ1Proposition8_9WideFixedCellProducer : Prop :=
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
                  ∀ coarse :
                    WZ1Proposition8_9WideCoarseData
                      delta epsilon eta parameters F G₁ G₂ H data,
                    Nonempty
                      (WZ1Proposition8_9WideFixedCellData coarse)

/-- Select fixed cells from the existing synchronized coarse producer. -/
def WZ1Proposition8_9WideFixedCellSelectionStatement : Prop :=
  WZ1Proposition8_9WideCoarsePreparationStatement →
    WZ1Proposition8_9WideFixedCellProducer

/--
The normalized package before the final snapped-dot covering transport.

`source_approximation` retains an actual source edge for every normalized
edge and records the quantitative perturbation instead of asserting false
equality between snapped and actual dot values.
-/
structure WZ1Proposition8_9WideNormalizedCoreData
    {delta epsilon eta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {coarse :
      WZ1Proposition8_9WideCoarseData
        delta epsilon eta parameters F G₁ G₂ H data}
    (fixed : WZ1Proposition8_9WideFixedCellData coarse) where
  scale : ℝ
  scale_pos : 0 < scale
  scale_le_projectionDelta₀ :
    scale ≤ parameters.projectionDelta₀
  firstScale : ℝ
  firstScale_pos : 0 < firstScale
  firstScale_lower : 1 / 4 ≤ firstScale
  firstScale_le : firstScale ≤ 100
  endpointScale : ℝ
  endpointScale_pos : 0 < endpointScale
  endpointScale_lower : 1 / 4 ≤ endpointScale
  endpointScale_le : endpointScale ≤ 100
  scaleFactor : ℝ
  scaleFactor_eq :
    scaleFactor = min 1 (min firstScale endpointScale)
  scaleFactor_pos : 0 < scaleFactor
  scaleFactor_lower : 1 / 4 ≤ scaleFactor
  scaleFactor_le_one : scaleFactor ≤ 1
  scaleFactor_le_first : scaleFactor ≤ firstScale
  scaleFactor_le_endpoint : scaleFactor ≤ endpointScale
  scale_product_lower :
    1 / 16 ≤ firstScale * endpointScale
  scale_product_le :
    firstScale * endpointScale ≤ 100
  scale_eq :
    scale = scaleFactor * coarse.scale
  endpointTranslation : Point2
  normalizedF : DiscreteSet 2
  normalizedG₁ : DiscreteSet 2
  normalizedG₂ : DiscreteSet 2
  normalizedH : Finset (Point2 × Point2 × Point2)
  normalizedF_eq :
    normalizedF =
      fixed.cellF.image
        (fun point => firstScale • point)
  normalizedG₁_eq :
    normalizedG₁ =
      fixed.cellG₁.image
        (fun point =>
          endpointScale • point + endpointTranslation)
  normalizedG₂_eq :
    normalizedG₂ =
      fixed.cellG₂.image
        (fun point =>
          endpointScale • point + endpointTranslation)
  normalizedH_eq :
    normalizedH =
      fixed.cellH.image
        (fun edge =>
          (firstScale • edge.1,
            endpointScale • edge.2.1 + endpointTranslation,
            endpointScale • edge.2.2 + endpointTranslation))
  normalizedF_nonempty : normalizedF.Nonempty
  normalizedG₁_nonempty : normalizedG₁.Nonempty
  normalizedG₂_nonempty : normalizedG₂.Nonempty
  normalizedF_ball : normalizedF.IsInUnitBall
  normalizedG₁_ball : normalizedG₁.IsInUnitBall
  normalizedG₂_ball : normalizedG₂.IsInUnitBall
  normalizedF_separated :
    normalizedF.IsDeltaSeparated scale
  normalizedG₁_separated :
    normalizedG₁.IsDeltaSeparated scale
  normalizedG₂_separated :
    normalizedG₂.IsDeltaSeparated scale
  normalizedF_frostman :
    normalizedF.IsFrostman scale 1
      (Kakeya.realRpowENN
        scale (-parameters.projectionLambda))
  normalizedG₁_frostman :
    normalizedG₁.IsFrostman scale 1
      (Kakeya.realRpowENN
        scale (-parameters.projectionLambda))
  normalizedG₂_frostman :
    normalizedG₂.IsFrostman scale 1
      (Kakeya.realRpowENN
        scale (-parameters.projectionLambda))
  standardSeparation :
    WZ1StandardSeparation
      normalizedF normalizedG₁ normalizedG₂
  first_line_nonconcentration :
    WZ1LineNonConcentration
      scale parameters.projectionLambda parameters.zeta
      normalizedG₁
  second_line_nonconcentration :
    WZ1LineNonConcentration
      scale parameters.projectionLambda parameters.zeta
      normalizedG₂
  uniform :
    WZ1UniformTripleDensity
      (Kakeya.realRpowENN scale parameters.alpha)
      normalizedF normalizedG₁ normalizedG₂ normalizedH
  effectiveWidth : ℝ
  effectiveWidth_pos : 0 < effectiveWidth
  effectiveWidth_eq :
    effectiveWidth =
      data.width / (firstScale * endpointScale)
  effectiveWidth_scale_eq :
    effectiveWidth * scale =
      delta * scaleFactor / (firstScale * endpointScale)
  effectiveWidth_scale_lower :
    delta / 100 ≤ effectiveWidth * scale
  effectiveWidth_scale_upper :
    effectiveWidth * scale ≤ 4 * delta
  effectiveWidth_lower :
    data.width / 100 ≤ effectiveWidth
  effectiveWidth_upper :
    effectiveWidth ≤ 100 * data.width
  sourceError : ℝ
  sourceError_nonneg : 0 ≤ sourceError
  sourceError_bound :
    sourceError ≤ 1200 * effectiveWidth * coarse.scale
  normalized_dot_bound :
    ∀ value ∈ wz1DotDifferenceSet normalizedH,
      |value| ≤ 2
  source_approximation :
    ∀ normalizedEdge ∈ normalizedH,
      ∃ sourceEdge ∈ data.refinedH,
        |inner ℝ sourceEdge.1
              (sourceEdge.2.1 - sourceEdge.2.2) -
            effectiveWidth *
              inner ℝ normalizedEdge.1
                (normalizedEdge.2.1 -
                  normalizedEdge.2.2)| ≤
          sourceError

/-- A global producer for the coherent normalized core. -/
def WZ1Proposition8_9WideNormalizedCoreProducer : Prop :=
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
                  ∀ coarse :
                    WZ1Proposition8_9WideCoarseData
                      delta epsilon eta parameters F G₁ G₂ H data,
                    ∀ fixed :
                      WZ1Proposition8_9WideFixedCellData coarse,
                      Nonempty
                        (WZ1Proposition8_9WideNormalizedCoreData fixed)

/-- Normalize the exact fixed-cell producer without reselecting its graph. -/
def WZ1Proposition8_9WideFixedCellNormalizationStatement : Prop :=
  WZ1Proposition8_9WideFixedCellProducer →
    WZ1Proposition8_9WideNormalizedCoreProducer

/--
Discharge the snapped-dot perturbation and return to the original graph.

This leaf consumes the same normalized core; it cannot assume exact equality
between snapped and source dot-difference sets.
-/
def WZ1Proposition8_9WideSnappedCoveringTransportStatement : Prop :=
  WZ1Proposition8_9WideCoarsePreparationStatement →
    WZ1Proposition8_9WideFixedCellProducer →
      WZ1Proposition8_9WideNormalizedCoreProducer →
        WZ1Proposition8_9WideNormalizedPreparationStatement

/-- The three dependent leaves imply the historical wide normalization API. -/
def WZ1Proposition8_9WideNormalizedFromFixedCellsStatement : Prop :=
  WZ1Proposition8_9WideFixedCellSelectionStatement →
    WZ1Proposition8_9WideFixedCellNormalizationStatement →
      WZ1Proposition8_9WideSnappedCoveringTransportStatement →
        WZ1Proposition8_9WideNormalizedFromCoarseStatement

end Kakeya.Assouad
