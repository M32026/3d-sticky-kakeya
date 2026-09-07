import MyLeanRepo.Kakeya.Assouad.WZ1.ActiveProjectionFrostmanTransfer
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49ActiveFiberSeparatedSelectionStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49EndpointConstruction
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49RadialProjectionStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13ActualRepresentativeStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13SplitStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseAffineMaps

/-!
# Paper-faithful interfaces for PDF Lemma 8.13, Step 2

The former normalized-core interface allowed a singleton first class and an
unrelated identity subgraph.  The replacement starts in the order used by the
paper:

1. fix one actual outside viewpoint and its actual endpoint fiber;
2. select a separated subset of that fiber;
3. refine the graph while the viewpoint is already fixed; and
4. apply the paper's common endpoint affine map and matching transpose map.

Every normalized edge below is therefore the literal image of an actual
source edge with the fixed viewpoint.
-/

namespace Kakeya.Assouad

open scoped ENNReal

noncomputable section

/-- The paper's auxiliary loss `epsilon₁`. -/
def wz1Lemma8_13FaithfulEpsilonOne (epsilon : ℝ) : ℝ :=
  epsilon ^ 2 / 100

/-- The source density loss used by the repaired preparation. -/
def wz1Lemma8_13FaithfulEta (epsilon : ℝ) : ℝ :=
  epsilon ^ 2 / 1000

/-- The common normalized Frostman/density loss reserved for Kaufman. -/
def wz1Lemma8_13FaithfulNormalizedEta (epsilon : ℝ) : ℝ :=
  epsilon ^ 2 / 25

/-- Exact active common width of the residual graph. -/
def wz1Lemma8_13FaithfulActiveWidth
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta) : ℝ :=
  wz1ActiveCommonWidth
    delta input.H input.density.1 input.base input.direction

/-- Width `T = delta^(-epsilon₁) * t` of the paper's containing rectangles. -/
def wz1Lemma8_13FaithfulNormalizationWidth
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta) : ℝ :=
  Real.rpow delta (-wz1Lemma8_13FaithfulEpsilonOne epsilon) *
    wz1Lemma8_13FaithfulActiveWidth input

/-- Contraction ledger for the affine maps. -/
def wz1Lemma8_13FaithfulAspect
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta) : ℝ :=
  max 1 (wz1Lemma8_13FaithfulNormalizationWidth input)

/-- Original separated-fiber scale chosen before normalization. -/
def wz1Lemma8_13FaithfulSelectionScale
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta) : ℝ :=
  128 * wz1Lemma8_13FaithfulAspect input *
    input.width / wz1Lemma8_13FaithfulActiveWidth input

/-- Fine scale after the common factor `1/2` and possible `T⁻¹` contraction. -/
def wz1Lemma8_13FaithfulFineScale
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta) : ℝ :=
  delta / (2 * wz1Lemma8_13FaithfulAspect input)

/-- Kaufman angular scale `s = width / T`. -/
def wz1Lemma8_13FaithfulAngularScale
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta) : ℝ :=
  input.width / wz1Lemma8_13FaithfulNormalizationWidth input

/-- Euclidean separation retained by the normalized endpoint source. -/
def wz1Lemma8_13FaithfulSourceScale
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta) : ℝ :=
  64 * input.width / wz1Lemma8_13FaithfulActiveWidth input

/-- One-sided strip parameter after normalization. -/
def wz1Lemma8_13FaithfulSide
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta) : ℝ :=
  (wz1Lemma8_13FaithfulActiveWidth input - input.width) /
    wz1Lemma8_13FaithfulNormalizationWidth input

/-- Cardinality parameter reserved for the radial direction Frostman bound. -/
def wz1Lemma8_13FaithfulDirectionKappa
    (delta epsilon : ℝ) : ℝ :=
  Real.rpow delta
      (4 * wz1Lemma8_13FaithfulEta epsilon +
        2 * wz1Lemma8_13FaithfulEpsilonOne epsilon) /
    1572864

/-- Positive real density used by the final Kaufman incidence graph. -/
def wz1Lemma8_13FaithfulGraphDensity
    (delta epsilon : ℝ) : ℝ :=
  Real.rpow delta (wz1Lemma8_13FaithfulNormalizedEta epsilon)

/-- Common factor `1/2` used to place all affine images in the unit ball. -/
def wz1Lemma8_13HalfLinear : Point2 ≃ₗ[ℝ] Point2 :=
  LinearEquiv.smulOfNeZero ℝ Point2 (1 / 2 : ℝ) (by norm_num)

/-- Paper transpose map on the first coordinate, followed by the common
factor `1/2`. -/
def wz1Lemma8_13FaithfulFMap
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hwidth : 0 < wz1Lemma8_13FaithfulNormalizationWidth input) :
    Point2 ≃ Point2 :=
  (wideCoarsePhiF
      input.direction
      (wz1Lemma8_13FaithfulNormalizationWidth input)
      hwidth input.direction_unit).toEquiv.trans
    wz1Lemma8_13HalfLinear.toEquiv

/-- Common endpoint affine map, followed by the common factor `1/2`. -/
def wz1Lemma8_13FaithfulGMap
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hwidth : 0 < wz1Lemma8_13FaithfulNormalizationWidth input) :
    Point2 ≃ Point2 :=
  (wideCoarsePhiG
      input.direction
      (wz1Lemma8_13FaithfulNormalizationWidth input)
      hwidth input.base 0 input.direction_unit).toEquiv.trans
    wz1Lemma8_13HalfLinear.toEquiv

/-- Coordinatewise literal image of a source triple. -/
def wz1Lemma8_13FaithfulTripleMap
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hwidth : 0 < wz1Lemma8_13FaithfulNormalizationWidth input)
    (edge : Point2 × Point2 × Point2) :
    Point2 × Point2 × Point2 :=
  (wz1Lemma8_13FaithfulFMap input hwidth edge.1,
    wz1Lemma8_13FaithfulGMap input hwidth edge.2.1,
    wz1Lemma8_13FaithfulGMap input hwidth edge.2.2)

/--
The fixed-viewpoint and literal-affine output.

The first refinement occurs after the actual viewpoint and separated source
have been fixed.  The three source vertex classes are exactly the active
projections of that same refined graph.  The normalized graph is its literal
coordinatewise image.
-/
structure WZ1Lemma8_13FaithfulViewpointAffineData
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hdelta : 0 < delta) where
  eta_eq : eta = wz1Lemma8_13FaithfulEta epsilon
  normalizationWidth_pos :
    0 < wz1Lemma8_13FaithfulNormalizationWidth input
  normalizationWidth_upper :
    wz1Lemma8_13FaithfulNormalizationWidth input ≤
      3 * Real.rpow delta
        (-wz1Lemma8_13FaithfulEpsilonOne epsilon)
  normalizationWidth_lower :
    Real.rpow delta
        (1 - wz1Lemma8_13FaithfulEpsilonOne epsilon) ≤
      wz1Lemma8_13FaithfulNormalizationWidth input
  aspect_upper :
    wz1Lemma8_13FaithfulAspect input ≤
      3 * Real.rpow delta
        (-wz1Lemma8_13FaithfulEpsilonOne epsilon)
  width_le_eighth :
    input.width ≤ 1 / 8
  angularScale_pos :
    0 < wz1Lemma8_13FaithfulAngularScale input
  angularScale_le_quarter :
    wz1Lemma8_13FaithfulAngularScale input ≤ 1 / 4
  fineScale_pos :
    0 < wz1Lemma8_13FaithfulFineScale input
  fineScale_le_angular :
    wz1Lemma8_13FaithfulFineScale input ≤
      wz1Lemma8_13FaithfulAngularScale input
  selectionScale_pos :
    0 < wz1Lemma8_13FaithfulSelectionScale input
  delta_le_selectionScale :
    delta ≤ wz1Lemma8_13FaithfulSelectionScale input
  selectionScale_le_one :
    wz1Lemma8_13FaithfulSelectionScale input ≤ 1
  sourceScale_pos :
    0 < wz1Lemma8_13FaithfulSourceScale input
  sourceScale_le_one :
    wz1Lemma8_13FaithfulSourceScale input ≤ 1
  side_pos :
    0 < wz1Lemma8_13FaithfulSide input
  radial_threshold :
    wz1Lemma8_13FaithfulAngularScale input +
          4 * wz1Lemma8_13FaithfulAngularScale input /
            wz1Lemma8_13FaithfulSide input <
      wz1Lemma8_13FaithfulSourceScale input
  radial_angular_bound :
    wz1Lemma8_13FaithfulAngularScale input ≤
      (wz1Lemma8_13FaithfulSourceScale input -
          wz1Lemma8_13FaithfulAngularScale input -
          4 * wz1Lemma8_13FaithfulAngularScale input /
            wz1Lemma8_13FaithfulSide input) /
        (2 + 8 / wz1Lemma8_13FaithfulSide input)
  viewpoint :
    WZ1Lemma49ActiveViewpointData
      input.F input.G₁ input.G₂ input.H
      (Kakeya.realRpowENN delta eta)
      input.base input.direction input.width
      (wz1Lemma8_13FaithfulActiveWidth input)
  separatedSource :
    WZ1Lemma49ActiveFiberSeparatedSelectionData
      (C := Kakeya.realRpowENN delta (-eta))
      (u := wz1Lemma8_13FaithfulSelectionScale input)
      viewpoint
  fixedH : Finset (Point2 × Point2 × Point2)
  fixedH_eq :
    fixedH =
      input.H.filter fun edge =>
        edge.2.1 ∈ separatedSource.selected ∧
          edge.2.2 = viewpoint.viewpoint
  fixedH_nonempty : fixedH.Nonempty
  fixedH_subset : fixedH ⊆ input.H
  refinedH : Finset (Point2 × Point2 × Point2)
  refinedH_subset : refinedH ⊆ fixedH
  sourceF : DiscreteSet 2
  sourceG₁ : DiscreteSet 2
  sourceG₂ : DiscreteSet 2
  sourceF_eq :
    sourceF = wz1ActiveTripleProjection refinedH 0
  sourceG₁_eq :
    sourceG₁ = wz1ActiveTripleProjection refinedH 1
  sourceG₂_eq :
    sourceG₂ = wz1ActiveTripleProjection refinedH 2
  sourceG₁_subset :
    sourceG₁ ⊆ separatedSource.selected
  sourceG₂_eq_singleton :
    sourceG₂ = {viewpoint.viewpoint}
  sourceUniform :
    WZ1UniformTripleDensity
      (Kakeya.realRpowENN delta eta / 16)
      sourceF sourceG₁ sourceG₂ refinedH
  normalizedF : DiscreteSet 2
  normalizedG₁ : DiscreteSet 2
  normalizedG₂ : DiscreteSet 2
  normalizedH : Finset (Point2 × Point2 × Point2)
  normalizedF_eq :
    normalizedF =
      sourceF.image
        (wz1Lemma8_13FaithfulFMap input normalizationWidth_pos)
  normalizedG₁_eq :
    normalizedG₁ =
      sourceG₁.image
        (wz1Lemma8_13FaithfulGMap input normalizationWidth_pos)
  normalizedG₂_eq :
    normalizedG₂ =
      sourceG₂.image
        (wz1Lemma8_13FaithfulGMap input normalizationWidth_pos)
  normalizedH_eq :
    normalizedH =
      refinedH.image
        (wz1Lemma8_13FaithfulTripleMap
          input normalizationWidth_pos)
  normalizedUniform :
    WZ1UniformTripleDensity
      (Kakeya.realRpowENN delta eta / 16)
      normalizedF normalizedG₁ normalizedG₂ normalizedH
  normalizedF_ball : normalizedF.IsInUnitBall
  normalizedG₁_ball : normalizedG₁.IsInUnitBall
  normalizedG₂_ball : normalizedG₂.IsInUnitBall
  fineConstant : ℝ
  fineConstant_ge_one : 1 ≤ fineConstant
  fineConstant_bound :
    fineConstant ≤
      96 * Real.rpow delta
        (-(2 * eta +
          wz1Lemma8_13FaithfulEpsilonOne epsilon))
  normalizedF_separated :
    normalizedF.IsDeltaSeparated
      (wz1Lemma8_13FaithfulFineScale input)
  normalizedF_frostman :
    normalizedF.IsFrostman
      (wz1Lemma8_13FaithfulFineScale input) 1
      (ENNReal.ofReal fineConstant)
  normalizedViewpoint : Point2
  normalizedViewpoint_eq :
    normalizedViewpoint =
      wz1Lemma8_13FaithfulGMap input
        normalizationWidth_pos viewpoint.viewpoint
  normalizedViewpoint_mem :
    normalizedViewpoint ∈ normalizedG₂
  normalizedSource_separated :
    normalizedG₁.IsDeltaSeparated
      (wz1Lemma8_13FaithfulSourceScale input)
  normalizedBase : Point2
  normalizedBase_eq :
    normalizedBase =
      wz1Lemma8_13FaithfulGMap input
        normalizationWidth_pos input.base
  normalizedSource_strip :
    ∀ point ∈ normalizedG₁,
      |inner ℝ (point - normalizedBase)
        (wz1Perp2 viewpoint.orientedDirection)| ≤
          wz1Lemma8_13FaithfulAngularScale input / 2
  normalizedSource_side :
    ∀ point ∈ normalizedG₁,
      wz1Lemma8_13FaithfulSide input / 2 ≤
        inner ℝ (point - normalizedViewpoint)
          (wz1Perp2 viewpoint.orientedDirection)
  normalizedSource_cardinality :
    Kakeya.realRpowENN delta (3 * eta) ≤
      16 *
        Kakeya.realRpowENN
          (wz1Lemma8_13FaithfulSelectionScale input) 1 *
        normalizedG₁.enncard
  normalizedSupport :
    ∀ edge ∈ normalizedH,
      edge.1 ∈ normalizedF ∧
        edge.2.1 ∈ normalizedG₁ ∧
        edge.2.2 ∈ normalizedG₂
  sourceWitness :
    ∀ normalizedEdge ∈ normalizedH,
      ∃ sourceEdge ∈ input.H,
        sourceEdge.2.2 = viewpoint.viewpoint ∧
          normalizedEdge =
            wz1Lemma8_13FaithfulTripleMap
              input normalizationWidth_pos sourceEdge
  sourceDot_eq :
    ∀ sourceEdge ∈ input.H,
      inner ℝ sourceEdge.1
          (sourceEdge.2.1 - sourceEdge.2.2) =
        4 * wz1Lemma8_13FaithfulNormalizationWidth input *
          inner ℝ
            (wz1Lemma8_13FaithfulFMap
              input normalizationWidth_pos sourceEdge.1)
            (wz1Lemma8_13FaithfulGMap
                input normalizationWidth_pos sourceEdge.2.1 -
              wz1Lemma8_13FaithfulGMap
                input normalizationWidth_pos sourceEdge.2.2)

/--
First replacement leaf: fix the actual viewpoint and fiber, refine that
fixed-viewpoint graph, and construct its literal affine image.
-/
def WZ1Lemma8_13FaithfulViewpointAffineStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ (delta : ℝ) (hdelta : 0 < delta), delta ≤ delta₀ →
        ∀ input :
          WZ1Lemma8_13ResidualInput
            delta epsilon (wz1Lemma8_13FaithfulEta epsilon),
          Nonempty
            (WZ1Lemma8_13FaithfulViewpointAffineData
              input hdelta)

/--
The final paper-scale Kaufman input over the already fixed affine geometry.

Lemma 48 is applied only to the actual affine first-coordinate class.  The
validated representative theorem replaces coarse cells by actual affine
points and refines the same literal graph.  The endpoint direction set is
then formed from the active endpoint projection of that final graph and the
same fixed normalized viewpoint.
-/
structure WZ1Lemma8_13FaithfulKaufmanInputData
    {delta epsilon : ℝ}
    {input :
      WZ1Lemma8_13ResidualInput
        delta epsilon (wz1Lemma8_13FaithfulEta epsilon)}
    {hdelta : 0 < delta}
    (affine :
      WZ1Lemma8_13FaithfulViewpointAffineData
        input hdelta) where
  normalizedEta_pos :
    0 < wz1Lemma8_13FaithfulNormalizedEta epsilon
  normalizedEta_lt_epsilon_quarter :
    wz1Lemma8_13FaithfulNormalizedEta epsilon < epsilon / 4
  directionKappa_pos :
    0 < wz1Lemma8_13FaithfulDirectionKappa delta epsilon
  coarsening :
    WZ1FrostmanCoarseningData
      affine.normalizedF
      (wz1Lemma8_13FaithfulFineScale input)
      (wz1Lemma8_13FaithfulAngularScale input)
      1 (ENNReal.ofReal affine.fineConstant)
  coarsening_selected_active :
    ∀ point ∈ coarsening.selected,
      ∃ edge ∈ affine.normalizedH, edge.1 = point
  representatives :
    WZ1Lemma8_13ActualRepresentativeData
      (G₁ := affine.normalizedG₁)
      (G₂ := affine.normalizedG₂)
      coarsening
      (Kakeya.realRpowENN delta
        (wz1Lemma8_13FaithfulEta epsilon) / 16)
      affine.normalizedH
  finalF : DiscreteSet 2 := representatives.normalizedF
  finalH : Finset (Point2 × Point2 × Point2) :=
    representatives.normalizedH
  finalG₁ : DiscreteSet 2 :=
    wz1ActiveTripleProjection finalH 1
  finalG₂ : DiscreteSet 2 :=
    wz1ActiveTripleProjection finalH 2
  finalF_eq :
    finalF = representatives.normalizedF
  finalH_eq :
    finalH = representatives.normalizedH
  finalG₁_eq :
    finalG₁ = wz1ActiveTripleProjection finalH 1
  finalG₂_eq :
    finalG₂ = wz1ActiveTripleProjection finalH 2
  finalH_subset : finalH ⊆ affine.normalizedH
  finalG₁_subset : finalG₁ ⊆ affine.normalizedG₁
  finalG₂_eq_singleton :
    finalG₂ = {affine.normalizedViewpoint}
  commonConstant : ℝ
  commonConstant_ge_one : 1 ≤ commonConstant
  commonConstant_bound :
    commonConstant ≤
      Real.rpow delta
        (-wz1Lemma8_13FaithfulNormalizedEta epsilon)
  graphDensity_eq :
    wz1Lemma8_13FaithfulGraphDensity delta epsilon =
      Real.rpow delta
        (wz1Lemma8_13FaithfulNormalizedEta epsilon)
  finalUniformRaw :
    WZ1UniformTripleDensity
      (Kakeya.realRpowENN delta
          (wz1Lemma8_13FaithfulEta epsilon) / 256)
      finalF finalG₁ finalG₂ finalH
  finalUniform :
    WZ1UniformTripleDensity
      (ENNReal.ofReal
        (wz1Lemma8_13FaithfulGraphDensity delta epsilon))
      finalF finalG₁ finalG₂ finalH
  finalF_nonempty : finalF.Nonempty
  finalF_ball : finalF.IsInUnitBall
  finalF_separated :
    finalF.IsDeltaSeparated
      (wz1Lemma8_13FaithfulAngularScale input)
  finalF_frostman :
    finalF.IsFrostman
      (wz1Lemma8_13FaithfulAngularScale input) 1
      (ENNReal.ofReal commonConstant)
  finalG₁_nonempty : finalG₁.Nonempty
  finalG₁_ball : finalG₁.IsInUnitBall
  finalG₂_ball : finalG₂.IsInUnitBall
  finalG₁_separated :
    finalG₁.IsDeltaSeparated
      (wz1Lemma8_13FaithfulSourceScale input)
  finalG₁_strip :
    ∀ point ∈ finalG₁,
      |inner ℝ (point - affine.normalizedBase)
        (wz1Perp2 affine.viewpoint.orientedDirection)| ≤
          wz1Lemma8_13FaithfulAngularScale input / 2
  finalG₁_side :
    ∀ point ∈ finalG₁,
      wz1Lemma8_13FaithfulSide input / 2 ≤
        inner ℝ (point - affine.normalizedViewpoint)
          (wz1Perp2 affine.viewpoint.orientedDirection)
  finalG₁_cardinality :
    wz1Lemma8_13FaithfulDirectionKappa delta epsilon /
        wz1Lemma8_13FaithfulAngularScale input ≤
      (finalG₁.card : ℝ)
  radial :
    WZ1Lemma49RadialProjectionData
      finalG₁ affine.normalizedViewpoint
      (wz1Lemma8_13FaithfulAngularScale input)
      commonConstant
  firstEndpoint : Point2 → Point2
  secondEndpoint : Point2 → Point2
  firstEndpoint_mem :
    ∀ direction ∈ radial.directions,
      firstEndpoint direction ∈ finalG₁
  secondEndpoint_eq :
    ∀ direction,
      secondEndpoint direction = affine.normalizedViewpoint
  secondEndpoint_mem :
    ∀ direction ∈ radial.directions,
      secondEndpoint direction ∈ finalG₂
  direction_eq :
    ∀ direction ∈ radial.directions,
      direction =
        (‖firstEndpoint direction -
            secondEndpoint direction‖⁻¹ : ℝ) •
          (firstEndpoint direction -
            secondEndpoint direction)
  endpointDistance_lower :
    ∀ direction ∈ radial.directions,
      1 / (4 * wz1Lemma8_13FaithfulAspect input) ≤
        dist (firstEndpoint direction)
          (secondEndpoint direction)
  endpointDistance_upper :
    ∀ direction ∈ radial.directions,
      dist (firstEndpoint direction)
          (secondEndpoint direction) ≤ 2
  finalSupport :
    ∀ edge ∈ finalH,
      edge.1 ∈ finalF ∧
        edge.2.1 ∈ finalG₁ ∧
        edge.2.2 ∈ finalG₂
  fiber_density :
    ∀ direction ∈ radial.directions,
      ((kaufmanFiber finalH
          (firstEndpoint direction)
          (secondEndpoint direction)).card : ENNReal) ≥
        ENNReal.ofReal
            (wz1Lemma8_13FaithfulGraphDensity delta epsilon) *
          finalF.enncard
  sourceWitness :
    ∀ finalEdge ∈ finalH,
      ∃ sourceEdge ∈ input.H,
        sourceEdge.2.2 = affine.viewpoint.viewpoint ∧
          finalEdge =
            wz1Lemma8_13FaithfulTripleMap
              input affine.normalizationWidth_pos sourceEdge
  sourceDot_eq :
    ∀ sourceEdge ∈ input.H,
      inner ℝ sourceEdge.1
          (sourceEdge.2.1 - sourceEdge.2.2) =
        4 * wz1Lemma8_13FaithfulNormalizationWidth input *
          inner ℝ
            (wz1Lemma8_13FaithfulFMap
              input affine.normalizationWidth_pos sourceEdge.1)
            (wz1Lemma8_13FaithfulGMap
                input affine.normalizationWidth_pos sourceEdge.2.1 -
              wz1Lemma8_13FaithfulGMap
                input affine.normalizationWidth_pos sourceEdge.2.2)

/--
Second replacement leaf: coarsen the actual affine first class, retain actual
representatives in the same graph, and build the radial Kaufman input at the
paper scale.
-/
def WZ1Lemma8_13FaithfulKaufmanInputStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ (delta : ℝ) (hdelta : 0 < delta), delta ≤ delta₀ →
        ∀ input :
          WZ1Lemma8_13ResidualInput
            delta epsilon (wz1Lemma8_13FaithfulEta epsilon),
          ∀ affine :
            WZ1Lemma8_13FaithfulViewpointAffineData
              input hdelta,
            Nonempty
              (WZ1Lemma8_13FaithfulKaufmanInputData affine)

/--
Explicit output of the faithful Kaufman closing.

The selected direction comes from the supplied radial set, and every
transport scale is fixed by the selected endpoint and the exact affine
factor.  This rules out an unrelated existential witness for the final long
projection.
-/
structure WZ1Lemma8_13FaithfulClosingData
    {delta epsilon : ℝ}
    {input :
      WZ1Lemma8_13ResidualInput
        delta epsilon (wz1Lemma8_13FaithfulEta epsilon)}
    {hdelta : 0 < delta}
    {affine :
      WZ1Lemma8_13FaithfulViewpointAffineData
        input hdelta}
    (kaufman :
      WZ1Lemma8_13FaithfulKaufmanInputData affine) where
  direction : Point2
  direction_mem : direction ∈ kaufman.radial.directions
  normalizedFiberCovering :
    let normalizedEta :=
      wz1Lemma8_13FaithfulNormalizedEta epsilon
    let gamma :=
      2 * normalizedEta + 1 - epsilon / 2
    ENNReal.ofReal
          (wz1Lemma8_13FaithfulGraphDensity delta epsilon ^ 2 /
            (2 *
              kaufman_total_const
                (max 1 kaufman.commonConstant) 1 1 gamma *
              (2 : ℝ) ^ gamma)) *
        Kakeya.realRpowENN
          (wz1Lemma8_13FaithfulAngularScale input) (-gamma) ≤
      (↑(Metric.externalCoveringNumber
        (Real.toNNReal
          (wz1Lemma8_13FaithfulAngularScale input))
        (inner ℝ direction ''
          (kaufmanFiber kaufman.finalH
            (kaufman.firstEndpoint direction)
            (kaufman.secondEndpoint direction) :
              Set Point2))) : ENNReal)
  endpointDistance : ℝ :=
    dist (kaufman.firstEndpoint direction)
      (kaufman.secondEndpoint direction)
  endpointDistance_eq :
    endpointDistance =
      dist (kaufman.firstEndpoint direction)
        (kaufman.secondEndpoint direction)
  endpointDistance_lower :
    1 / (4 * wz1Lemma8_13FaithfulAspect input) ≤
      endpointDistance
  endpointDistance_upper : endpointDistance ≤ 2
  transportedRadius : ℝ :=
    4 * wz1Lemma8_13FaithfulNormalizationWidth input *
      endpointDistance
  transportedRadius_eq :
    transportedRadius =
      4 * wz1Lemma8_13FaithfulNormalizationWidth input *
        endpointDistance
  transportedScale : ℝ :=
    transportedRadius *
      wz1Lemma8_13FaithfulAngularScale input
  transportedScale_eq :
    transportedScale =
      transportedRadius *
        wz1Lemma8_13FaithfulAngularScale input
  rho : ℝ := max delta transportedScale
  rho_eq : rho = max delta transportedScale
  rho_lower : delta ≤ rho
  rho_upper : rho ≤ 1
  transportedRadius_pos : 0 < transportedRadius
  long_radius :
    Real.rpow delta
        (-wz1Lemma8_13FaithfulEta epsilon) *
        rho ≤
      2 * transportedRadius
  covering :
    Kakeya.realRpowENN
        (2 * transportedRadius / rho) (1 - epsilon) ≤
      (↑(Metric.externalCoveringNumber
        (Real.toNNReal rho)
        (wz1DotDifferenceSet input.H ∩
          Metric.closedBall 0 transportedRadius)) :
        ENNReal)

/--
Third replacement leaf: apply Kaufman's theorem to the faithful bipartite
incidence package and transport the selected fiber covering to the original
dot-difference graph.

The proof must use the explicit endpoint-distance window and the exact
`4 * normalizationWidth` dot identity.  If the transported scale is below
`delta`, it must use the one-dimensional covering coarsening theorem rather
than silently replacing the scale.
-/
def WZ1Lemma8_13FaithfulClosingStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ (delta : ℝ) (hdelta : 0 < delta), delta ≤ delta₀ →
        ∀ input :
          WZ1Lemma8_13ResidualInput
            delta epsilon (wz1Lemma8_13FaithfulEta epsilon),
          ∀ affine :
            WZ1Lemma8_13FaithfulViewpointAffineData
              input hdelta,
            ∀ kaufman :
              WZ1Lemma8_13FaithfulKaufmanInputData affine,
              Nonempty
                (WZ1Lemma8_13FaithfulClosingData kaufman)

/--
The three repaired leaves imply the original residual Kaufman branch.

This is only a dependency boundary.  Its proof selects the minimum of the
three small-scale thresholds and threads the same dependent witnesses from
the viewpoint stage through the Kaufman-input and closing stages.
-/
def WZ1Lemma8_13FaithfulAssemblyStatement : Prop :=
  WZ1Lemma8_13FaithfulViewpointAffineStatement →
    WZ1Lemma8_13FaithfulKaufmanInputStatement →
      WZ1Lemma8_13FaithfulClosingStatement →
        WZ1StripLocalizationKaufmanCaseStatement

end

end Kakeya.Assouad
