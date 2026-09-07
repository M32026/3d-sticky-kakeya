import MyLeanRepo.Kakeya.Assouad.WZ1.Theorem5_2LeafStatements

/-!
# Split leaves for PDF Lemma 8.13, Step 2

The normalized Kaufman preparation is split without allowing its three stages
to choose unrelated witnesses:

1. affine normalization and coarsening produce one literal normalized graph;
2. radial projection equips that same graph with dense Kaufman fibers; and
3. exponent arithmetic and covering transport close the package.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- One residual common-strip input to PDF Lemma 8.13, Step 2. -/
structure WZ1Lemma8_13ResidualInput
    (delta epsilon eta : ℝ) where
  F : DiscreteSet 2
  G₁ : DiscreteSet 2
  G₂ : DiscreteSet 2
  H : Finset (Point2 × Point2 × Point2)
  F_nonempty : F.Nonempty
  G₁_nonempty : G₁.Nonempty
  G₂_nonempty : G₂.Nonempty
  F_ball : F.IsInUnitBall
  G₁_ball : G₁.IsInUnitBall
  G₂_ball : G₂.IsInUnitBall
  F_separated : F.IsDeltaSeparated delta
  G₁_separated : G₁.IsDeltaSeparated delta
  G₂_separated : G₂.IsDeltaSeparated delta
  F_frostman :
    F.IsFrostman delta 1
      (Kakeya.realRpowENN delta (-eta))
  G₁_frostman :
    G₁.IsFrostman delta 1
      (Kakeya.realRpowENN delta (-eta))
  G₂_frostman :
    G₂.IsFrostman delta 1
      (Kakeya.realRpowENN delta (-eta))
  standardSeparation : WZ1StandardSeparation F G₁ G₂
  density :
    WZ1UniformTripleDensity
      (Kakeya.realRpowENN delta eta) F G₁ G₂ H
  base : Point2
  direction : Point2
  direction_unit : ‖direction‖ = 1
  width : ℝ
  width_pos : 0 < width
  delta_le_width : delta ≤ width
  G₁_strip :
    ∀ point ∈ G₁,
      point ∈
        wz1LineNeighborhood base direction width
  F_strip :
    ∀ edge ∈ H,
      edge.1 ∈
        wz1LineNeighborhood 0
          (wz1Perp2 direction)
          (Real.rpow delta
            (-wz1Lemma49AuxiliaryEpsilon epsilon) *
              wz1ActiveCommonWidth
                delta H density.1 base direction)
  active_width_large :
    Real.rpow delta
        (-epsilon + wz1Lemma49AuxiliaryEpsilon epsilon) *
        width <
      wz1ActiveCommonWidth
        delta H density.1 base direction

/--
The paper's affine normalization and coarsening output.

The graph is already literal at this stage, so all later incidence and
transport fields refer to exactly these four normalized objects.
-/
structure WZ1Lemma8_13NormalizedGeometryData
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta) where
  scale : ℝ
  scale_pos : 0 < scale
  scale_le_one : scale ≤ 1
  scale_le_quarter : scale ≤ 1 / 4
  normalizedEta : ℝ
  normalizedEta_pos : 0 < normalizedEta
  normalizedEta_lt_epsilon_quarter :
    normalizedEta < epsilon / 4
  normalizedF : DiscreteSet 2
  normalizedG₁ : DiscreteSet 2
  normalizedG₂ : DiscreteSet 2
  normalizedH : Finset (Point2 × Point2 × Point2)
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  graphDensity : ℝ
  graphDensity_pos : 0 < graphDensity
  normalizedF_nonempty : normalizedF.Nonempty
  normalizedF_ball : normalizedF.IsInUnitBall
  normalizedG₁_ball : normalizedG₁.IsInUnitBall
  normalizedG₂_ball : normalizedG₂.IsInUnitBall
  normalizedF_separated :
    normalizedF.IsDeltaSeparated scale
  normalizedF_frostman :
    normalizedF.IsFrostman scale 1
      (ENNReal.ofReal constant)
  mutualSeparation :
    WZ1MutuallySeparated normalizedG₁ normalizedG₂ (1 / 2)
  normalizedH_support :
    ∀ edge ∈ normalizedH,
      edge.1 ∈ normalizedF ∧
        edge.2.1 ∈ normalizedG₁ ∧
        edge.2.2 ∈ normalizedG₂
  normalizedUniform :
    WZ1UniformTripleDensity
      (ENNReal.ofReal graphDensity)
      normalizedF normalizedG₁ normalizedG₂ normalizedH

/--
A paper-scale radial source attached to one fixed normalized graph.

The `source_actual` field preserves literal graph provenance: every selected
first endpoint occurs with the fixed viewpoint in an actual normalized edge.
-/
structure WZ1Lemma8_13RadialSourceData
    {delta epsilon eta : ℝ}
    {input : WZ1Lemma8_13ResidualInput delta epsilon eta}
    (geometry : WZ1Lemma8_13NormalizedGeometryData input) where
  source : DiscreteSet 2
  source_subset : source ⊆ geometry.normalizedG₁
  source_nonempty : source.Nonempty
  sourceScale : ℝ
  sourceScale_pos : 0 < sourceScale
  sourceConstant : ℝ
  sourceConstant_nonneg : 0 ≤ sourceConstant
  base : Point2
  direction : Point2
  direction_unit : ‖direction‖ = 1
  viewpoint : Point2
  viewpoint_mem : viewpoint ∈ geometry.normalizedG₂
  side : ℝ
  side_pos : 0 < side
  width : ℝ
  width_pos : 0 < width
  source_separated : source.IsDeltaSeparated sourceScale
  source_frostman :
    source.IsFrostman sourceScale 1
      (ENNReal.ofReal sourceConstant)
  source_strip :
    ∀ point ∈ source,
      |inner ℝ (point - base)
        (wz1Perp2 direction)| ≤ width / 2
  source_side :
    ∀ point ∈ source,
      side / 2 ≤
        inner ℝ (point - viewpoint)
          (wz1Perp2 direction)
  source_actual :
    ∀ second ∈ source,
      ∃ first ∈ geometry.normalizedF,
        (first, second, viewpoint) ∈ geometry.normalizedH
  width_scale :
    width ≤ 120 * side * geometry.scale
  source_scale_lower :
    (2050 * side + 604 + 16 / side) * geometry.scale ≤
      sourceScale
  sourceScale_le_one : sourceScale ≤ 1
  source_scale_upper :
    sourceScale ≤
      3000 * (side + 1 / side) * geometry.scale
  constant_eq :
    geometry.constant =
      sourceConstant * 10000 * (side + 1 / side)

/--
One coherent choice of normalized geometry and its attached radial source.

Bundling the dependent witnesses prevents separate issues from choosing
incompatible normalized graphs.
-/
structure WZ1Lemma8_13NormalizedCoreData
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta) where
  geometry : WZ1Lemma8_13NormalizedGeometryData input
  radialSource : WZ1Lemma8_13RadialSourceData geometry
  exponent_arithmetic :
    (2 : ENNReal) *
        realRpowENN (2 / geometry.scale) (1 - epsilon) ≤
      ENNReal.ofReal
          (geometry.graphDensity ^ 2 /
            (2 *
              kaufman_total_const
                (max 1 geometry.constant) 1 1
                (2 * geometry.normalizedEta + 1 -
                  epsilon / 2) *
              (2 : ℝ) ^
                (2 * geometry.normalizedEta + 1 -
                  epsilon / 2))) *
        realRpowENN geometry.scale
          (-(2 * geometry.normalizedEta + 1 -
            epsilon / 2))
  transport :
    WZ1StripLocalizationLongProjection
        geometry.scale epsilon geometry.normalizedEta
        geometry.normalizedH →
      WZ1StripLocalizationLongProjection
        delta epsilon eta input.H

/--
Radial directions and dense literal fibers on one fixed normalized graph.
-/
structure WZ1Lemma8_13NormalizedIncidenceData
    {delta epsilon eta : ℝ}
    {input : WZ1Lemma8_13ResidualInput delta epsilon eta}
    (geometry : WZ1Lemma8_13NormalizedGeometryData input) where
  incidenceDensity : ℝ
  incidenceDensity_pos : 0 < incidenceDensity
  incidenceDensity_eq :
    incidenceDensity = geometry.graphDensity
  directions : DiscreteSet 2
  directions_nonempty : directions.Nonempty
  directions_unit :
    ∀ direction ∈ directions, ‖direction‖ = 1
  directions_separated :
    directions.IsDeltaSeparated geometry.scale
  directions_frostman :
    directions.IsFrostman geometry.scale 1
      (ENNReal.ofReal geometry.constant)
  firstEndpoint : Point2 → Point2
  secondEndpoint : Point2 → Point2
  firstEndpoint_mem :
    ∀ direction ∈ directions,
      firstEndpoint direction ∈ geometry.normalizedG₁
  secondEndpoint_mem :
    ∀ direction ∈ directions,
      secondEndpoint direction ∈ geometry.normalizedG₂
  direction_eq :
    ∀ direction ∈ directions,
      direction =
        (‖firstEndpoint direction -
            secondEndpoint direction‖⁻¹ : ℝ) •
          (firstEndpoint direction -
            secondEndpoint direction)
  fiber_density :
    ∀ direction ∈ directions,
      ((kaufmanFiber geometry.normalizedH
          (firstEndpoint direction)
          (secondEndpoint direction)).card : ENNReal) ≥
        ENNReal.ofReal incidenceDensity *
          geometry.normalizedF.enncard

/--
The final numerical inequality and transport back to the original graph.
-/
structure WZ1Lemma8_13NormalizedClosingData
    {delta epsilon eta : ℝ}
    {input : WZ1Lemma8_13ResidualInput delta epsilon eta}
    {geometry : WZ1Lemma8_13NormalizedGeometryData input}
    (incidence :
      WZ1Lemma8_13NormalizedIncidenceData geometry) where
  exponent_arithmetic :
    (2 : ENNReal) *
        realRpowENN (2 / geometry.scale) (1 - epsilon) ≤
      ENNReal.ofReal
          (incidence.incidenceDensity ^ 2 /
            (2 *
              kaufman_total_const
                (max 1 geometry.constant) 1 1
                (2 * geometry.normalizedEta + 1 -
                  epsilon / 2) *
              (2 : ℝ) ^
                (2 * geometry.normalizedEta + 1 -
                  epsilon / 2))) *
        realRpowENN geometry.scale
          (-(2 * geometry.normalizedEta + 1 -
            epsilon / 2))
  transport :
    WZ1StripLocalizationLongProjection
        geometry.scale epsilon geometry.normalizedEta
        geometry.normalizedH →
      WZ1StripLocalizationLongProjection
        delta epsilon eta input.H

/-- Assemble the complete normalized Kaufman package from coherent stages. -/
def WZ1Lemma8_13NormalizedKaufmanData.ofSplit
    {delta epsilon eta : ℝ}
    {input : WZ1Lemma8_13ResidualInput delta epsilon eta}
    (geometry : WZ1Lemma8_13NormalizedGeometryData input)
    (incidence :
      WZ1Lemma8_13NormalizedIncidenceData geometry)
    (closing :
      WZ1Lemma8_13NormalizedClosingData incidence) :
    WZ1Lemma8_13NormalizedKaufmanData
      delta epsilon eta input.F input.G₁ input.G₂ input.H where
  scale := geometry.scale
  scale_pos := geometry.scale_pos
  scale_le_one := geometry.scale_le_one
  scale_le_quarter := geometry.scale_le_quarter
  normalizedEta := geometry.normalizedEta
  normalizedEta_pos := geometry.normalizedEta_pos
  normalizedEta_lt_epsilon_quarter :=
    geometry.normalizedEta_lt_epsilon_quarter
  normalizedF := geometry.normalizedF
  normalizedG₁ := geometry.normalizedG₁
  normalizedG₂ := geometry.normalizedG₂
  normalizedH := geometry.normalizedH
  constant := geometry.constant
  constant_nonneg := geometry.constant_nonneg
  incidenceDensity := incidence.incidenceDensity
  incidenceDensity_pos := incidence.incidenceDensity_pos
  normalizedF_nonempty := geometry.normalizedF_nonempty
  normalizedF_ball := geometry.normalizedF_ball
  normalizedG₁_ball := geometry.normalizedG₁_ball
  normalizedG₂_ball := geometry.normalizedG₂_ball
  normalizedF_separated := geometry.normalizedF_separated
  normalizedF_frostman := geometry.normalizedF_frostman
  mutualSeparation := geometry.mutualSeparation
  directions := incidence.directions
  directions_nonempty := incidence.directions_nonempty
  directions_unit := incidence.directions_unit
  directions_separated := incidence.directions_separated
  directions_frostman := incidence.directions_frostman
  firstEndpoint := incidence.firstEndpoint
  secondEndpoint := incidence.secondEndpoint
  firstEndpoint_mem := incidence.firstEndpoint_mem
  secondEndpoint_mem := incidence.secondEndpoint_mem
  direction_eq := incidence.direction_eq
  normalizedH_support := geometry.normalizedH_support
  fiber_density := incidence.fiber_density
  exponent_arithmetic := closing.exponent_arithmetic
  transport := closing.transport

/--
Stage 1: construct one coherent normalized geometry and radial-source
package at every small scale.
-/
def WZ1Lemma8_13NormalizedCorePreparationStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ input : WZ1Lemma8_13ResidualInput
          delta epsilon eta,
          Nonempty
            (WZ1Lemma8_13NormalizedCoreData input)

/-- Mechanical implication from the coherent core to the old API. -/
def WZ1Lemma8_13NormalizedSplitAssemblyStatement : Prop :=
  WZ1Lemma8_13NormalizedCorePreparationStatement →
    WZ1Lemma8_13NormalizedKaufmanPreparationStatement

end Kakeya.Assouad
