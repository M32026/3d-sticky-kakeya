import MyLeanRepo.Kakeya.Assouad.WZ1.KaufmanEnergyTotal
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49ActiveViewpoint
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49RadialProjectionStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition45TwoEndsStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFinalStatements

/-!
# Remaining paper leaves for WZ1 Theorem 5.2

The declarations use the PDF numbering.  Historical source modules call
Lemma 8.13 “Lemma 49” and Proposition 8.9 “Proposition 45”.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/--
The complete normalized input to Kaufman's projection theorem produced in
Step 2 of PDF Lemma 8.13.

The normalized graph is produced by the paper's affine rescaling and
coarsening route.  Its loss exponent may differ from the original one, and
`transport` returns the normalized long projection to the original
dot-difference graph.
-/
structure WZ1Lemma8_13NormalizedKaufmanData
    (delta epsilon eta : ℝ)
    (F G₁ G₂ : DiscreteSet 2)
    (H : Finset (Point2 × Point2 × Point2)) where
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
  incidenceDensity : ℝ
  incidenceDensity_pos : 0 < incidenceDensity
  normalizedF_nonempty : normalizedF.Nonempty
  normalizedF_ball : normalizedF.IsInUnitBall
  normalizedG₁_ball : normalizedG₁.IsInUnitBall
  normalizedG₂_ball : normalizedG₂.IsInUnitBall
  normalizedF_separated : normalizedF.IsDeltaSeparated scale
  normalizedF_frostman :
    normalizedF.IsFrostman scale 1 (ENNReal.ofReal constant)
  mutualSeparation :
    WZ1MutuallySeparated normalizedG₁ normalizedG₂ (1 / 2)
  directions : DiscreteSet 2
  directions_nonempty : directions.Nonempty
  directions_unit :
    ∀ direction ∈ directions, ‖direction‖ = 1
  directions_separated :
    directions.IsDeltaSeparated scale
  directions_frostman :
    directions.IsFrostman scale 1 (ENNReal.ofReal constant)
  firstEndpoint : Point2 → Point2
  secondEndpoint : Point2 → Point2
  firstEndpoint_mem :
    ∀ direction ∈ directions,
      firstEndpoint direction ∈ normalizedG₁
  secondEndpoint_mem :
    ∀ direction ∈ directions,
      secondEndpoint direction ∈ normalizedG₂
  direction_eq :
    ∀ direction ∈ directions,
      direction =
        (‖firstEndpoint direction - secondEndpoint direction‖⁻¹ : ℝ) •
          (firstEndpoint direction - secondEndpoint direction)
  normalizedH_support :
    ∀ edge ∈ normalizedH,
      edge.1 ∈ normalizedF ∧
        edge.2.1 ∈ normalizedG₁ ∧
        edge.2.2 ∈ normalizedG₂
  fiber_density :
    ∀ direction ∈ directions,
      ((kaufmanFiber normalizedH
          (firstEndpoint direction)
          (secondEndpoint direction)).card : ENNReal) ≥
        ENNReal.ofReal incidenceDensity * normalizedF.enncard
  exponent_arithmetic :
    (2 : ENNReal) *
        realRpowENN (2 / scale) (1 - epsilon) ≤
      ENNReal.ofReal
          (incidenceDensity ^ 2 /
            (2 *
              kaufman_total_const
                (max 1 constant) 1 1
                (2 * normalizedEta + 1 - epsilon / 2) *
              (2 : ℝ) ^
                (2 * normalizedEta + 1 - epsilon / 2))) *
        realRpowENN scale
          (-(2 * normalizedEta + 1 - epsilon / 2))
  transport :
    WZ1StripLocalizationLongProjection
        scale epsilon normalizedEta normalizedH →
      WZ1StripLocalizationLongProjection
        delta epsilon eta H

/--
PDF Lemma 8.13, Step 2: construct the normalized Kaufman package from the
residual common-strip configuration.
-/
def WZ1Lemma8_13NormalizedKaufmanPreparationStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F G₁ G₂ : DiscreteSet 2,
          F.Nonempty → G₁.Nonempty → G₂.Nonempty →
          F.IsInUnitBall → G₁.IsInUnitBall → G₂.IsInUnitBall →
          F.IsDeltaSeparated delta →
          G₁.IsDeltaSeparated delta →
          G₂.IsDeltaSeparated delta →
          F.IsFrostman delta 1
            (Kakeya.realRpowENN delta (-eta)) →
          G₁.IsFrostman delta 1
            (Kakeya.realRpowENN delta (-eta)) →
          G₂.IsFrostman delta 1
            (Kakeya.realRpowENN delta (-eta)) →
          WZ1StandardSeparation F G₁ G₂ →
          ∀ H : Finset (Point2 × Point2 × Point2),
            ∀ hDensity :
                WZ1UniformTripleDensity
                  (Kakeya.realRpowENN delta eta)
                  F G₁ G₂ H,
              ∀ base direction : Point2,
                ‖direction‖ = 1 →
                ∀ width : ℝ, 0 < width → delta ≤ width →
                  (∀ point ∈ G₁,
                    point ∈
                      wz1LineNeighborhood base direction width) →
                  let activeWidth :=
                    wz1ActiveCommonWidth
                      delta H hDensity.1 base direction
                  (∀ edge ∈ H,
                    edge.1 ∈
                      wz1LineNeighborhood 0
                        (wz1Perp2 direction)
                        (Real.rpow delta
                          (-wz1Lemma49AuxiliaryEpsilon epsilon) *
                            activeWidth)) →
                  Real.rpow delta
                      (-epsilon + wz1Lemma49AuxiliaryEpsilon epsilon) *
                      width < activeWidth →
                    Nonempty
                      (WZ1Lemma8_13NormalizedKaufmanData
                        delta epsilon eta F G₁ G₂ H)

/--
The normalized Kaufman package implies the residual branch of PDF Lemma 8.13.
-/
def WZ1Lemma8_13FromNormalizedKaufmanStatement : Prop :=
  WZ1Lemma8_13NormalizedKaufmanPreparationStatement →
    WZ1StripLocalizationKaufmanCaseStatement

/--
The output of the two two-ends restrictions and induced graph refinements at
the start of the proof of PDF Proposition 8.9.
-/
structure WZ1Proposition8_9TwoEndsPreparationData
    (delta eta zeta : ℝ)
    (F G₁ G₂ : DiscreteSet 2)
    (H : Finset (Point2 × Point2 × Point2)) where
  firstNormal : Point2
  firstLevel : ℝ
  firstWidth : ℝ
  firstNormal_unit : ‖firstNormal‖ = 1
  firstWidth_lower : delta ≤ firstWidth
  firstWidth_upper : firstWidth ≤ 1
  firstSelected : DiscreteSet 2
  firstSelected_subset : firstSelected ⊆ G₁
  firstSelected_nonempty : firstSelected.Nonempty
  firstSelected_retention :
    Kakeya.realRpowENN delta (eta + zeta) * G₁.enncard ≤
      firstSelected.enncard
  firstSelected_strip :
    ∀ point ∈ firstSelected,
      |inner ℝ point firstNormal - firstLevel| ≤ firstWidth
  firstRawNonconcentration :
    WZ1RawStripNonconcentration
      delta zeta firstWidth firstSelected
  firstRefinedGraph : Finset (Point2 × Point2 × Point2)
  firstRefinedGraph_subset : firstRefinedGraph ⊆ H
  firstDensity : ENNReal
  firstDensity_lower :
    (1 / 16 : ENNReal) *
        Kakeya.realRpowENN delta eta ≤
      firstDensity
  firstUniform :
    WZ1UniformTripleDensity
      firstDensity F firstSelected G₂ firstRefinedGraph
  secondNormal : Point2
  secondLevel : ℝ
  secondWidth : ℝ
  secondNormal_unit : ‖secondNormal‖ = 1
  secondWidth_lower : delta ≤ secondWidth
  secondWidth_upper : secondWidth ≤ 1
  secondSelected : DiscreteSet 2
  secondSelected_subset : secondSelected ⊆ G₂
  secondSelected_nonempty : secondSelected.Nonempty
  secondSelected_retention :
    (1 / 16 : ENNReal) *
        Kakeya.realRpowENN delta (eta + zeta) *
        G₂.enncard ≤
      secondSelected.enncard
  secondSelected_strip :
    ∀ point ∈ secondSelected,
      |inner ℝ point secondNormal - secondLevel| ≤ secondWidth
  secondRawNonconcentration :
    WZ1RawStripNonconcentration
      delta zeta secondWidth secondSelected
  refinedGraph : Finset (Point2 × Point2 × Point2)
  refinedGraph_subset : refinedGraph ⊆ firstRefinedGraph
  density : ENNReal
  density_lower :
    firstDensity / 16 ≤ density
  uniform :
    WZ1UniformTripleDensity
      density F firstSelected secondSelected refinedGraph

/--
PDF Proposition 8.9 preparation: run Lemma 8.10 on both endpoint classes and
recover uniform density after each induced restriction.
-/
def WZ1Proposition8_9TwoEndsPreparationStatement : Prop :=
  WZ1TripartiteHypergraphRefinementStatement →
    ∀ {delta eta zeta : ℝ},
      0 < delta → delta ≤ 1 →
      0 < eta → 0 < zeta →
      ∀ F G₁ G₂ : DiscreteSet 2,
        F.Nonempty → G₁.Nonempty → G₂.Nonempty →
        F.IsInUnitBall → G₁.IsInUnitBall → G₂.IsInUnitBall →
        F.IsDeltaSeparated delta →
        G₁.IsDeltaSeparated delta →
        G₂.IsDeltaSeparated delta →
        F.IsFrostman delta 1
          (Kakeya.realRpowENN delta (-eta)) →
        G₁.IsFrostman delta 1
          (Kakeya.realRpowENN delta (-eta)) →
        G₂.IsFrostman delta 1
          (Kakeya.realRpowENN delta (-eta)) →
        WZ1StandardSeparation F G₁ G₂ →
        ∀ H : Finset (Point2 × Point2 × Point2),
          WZ1UniformTripleDensity
              (Kakeya.realRpowENN delta eta)
              F G₁ G₂ H →
            Nonempty
              (WZ1Proposition8_9TwoEndsPreparationData
                delta eta zeta F G₁ G₂ H)

/--
The strong three-class Alternative (A) displayed in PDF Proposition 8.9.
-/
def WZ1Proposition8_9AlternativeA
    (delta epsilon : ℝ)
    (F G₁ G₂ : DiscreteSet 2) : Prop :=
  ∃ base direction : Point2,
    ‖direction‖ = 1 ∧
    Kakeya.realRpowENN delta (epsilon - 1) ≤
      wz1DiscreteLineCount
        F 0 (wz1Perp2 direction) delta ∧
    Kakeya.realRpowENN delta (epsilon - 1) ≤
      wz1DiscreteLineCount
        G₁ base direction delta ∧
    Kakeya.realRpowENN delta (epsilon - 1) ≤
      wz1DiscreteLineCount
        G₂ base direction delta

/--
The union Alternative (A) sufficient for the 3D Kakeya main line.

This is weaker than the three-class conclusion displayed in Proposition 8.9:
it retains a significant part of at least one endpoint class.  The paper
ultimately applies Theorem 22 with one ambient endpoint set `G` in both
coordinates.  After the two active endpoint classes are transported back
into that common ambient set, either disjunct gives the required line count
for `G`.
-/
def WZ1Proposition8_9AlternativeAUnion
    (delta epsilon : ℝ)
    (F G₁ G₂ : DiscreteSet 2) : Prop :=
  ∃ base direction : Point2,
    ‖direction‖ = 1 ∧
    Kakeya.realRpowENN delta (epsilon - 1) ≤
      wz1DiscreteLineCount
        F 0 (wz1Perp2 direction) delta ∧
    (Kakeya.realRpowENN delta (epsilon - 1) ≤
        wz1DiscreteLineCount G₁ base direction delta ∨
      Kakeya.realRpowENN delta (epsilon - 1) ≤
        wz1DiscreteLineCount G₂ base direction delta)

/-- One fixed-output instance of PDF Lemma 8.13. -/
def WZ1StripLocalizationAt
    (epsilon eta delta₀ : ℝ) : Prop :=
  ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
    ∀ F G₁ G₂ : DiscreteSet 2,
      F.Nonempty → G₁.Nonempty → G₂.Nonempty →
      F.IsInUnitBall → G₁.IsInUnitBall → G₂.IsInUnitBall →
      F.IsDeltaSeparated delta →
      G₁.IsDeltaSeparated delta →
      G₂.IsDeltaSeparated delta →
      F.IsFrostman delta 1
        (Kakeya.realRpowENN delta (-eta)) →
      G₁.IsFrostman delta 1
        (Kakeya.realRpowENN delta (-eta)) →
      G₂.IsFrostman delta 1
        (Kakeya.realRpowENN delta (-eta)) →
      WZ1StandardSeparation F G₁ G₂ →
      ∀ H : Finset (Point2 × Point2 × Point2),
        WZ1UniformTripleDensity
            (Kakeya.realRpowENN delta eta)
            F G₁ G₂ H →
        ∀ base direction : Point2,
          ‖direction‖ = 1 →
          ∀ width : ℝ, 0 < width → delta ≤ width →
            (∀ point ∈ G₁,
              point ∈
                wz1LineNeighborhood base direction width) →
              ((∀ edge ∈ H,
                  edge.2.2 ∈
                    wz1LineNeighborhood base direction
                      (Real.rpow delta (-epsilon) * width)) ∧
                (∀ edge ∈ H,
                  edge.1 ∈
                    wz1LineNeighborhood 0
                      (wz1Perp2 direction)
                      (Real.rpow delta (-epsilon) * width))) ∨
                WZ1StripLocalizationLongProjection
                  delta epsilon eta H

/--
The fixed Proposition 8.5 parameter instance shared by every branch of one
Proposition 8.9 proof.
-/
structure WZ1Proposition8_9Parameters (epsilon : ℝ) where
  epsilon_le_tenth : epsilon ≤ 1 / 10
  projectionLambda : ℝ
  projectionLambda_pos : 0 < projectionLambda
  projectionLambda_le_one : projectionLambda ≤ 1
  workingLambda : ℝ
  workingLambda_pos : 0 < workingLambda
  workingLambda_le_projection :
    workingLambda ≤ projectionLambda
  workingLambda_le_epsilon_projection :
    workingLambda ≤ epsilon * projectionLambda / 100
  workingLambda_le_epsilon :
    workingLambda ≤ epsilon / 100
  stripEpsilon : ℝ
  stripEpsilon_pos : 0 < stripEpsilon
  stripEpsilon_lt_epsilon : stripEpsilon < epsilon
  stripEpsilon_le_epsilon_lambda :
    stripEpsilon ≤ epsilon * projectionLambda / 100
  stripEta : ℝ
  stripEta_pos : 0 < stripEta
  stripDelta₀ : ℝ
  stripDelta₀_pos : 0 < stripDelta₀
  stripDelta₀_le_one : stripDelta₀ ≤ 1
  strip :
    WZ1StripLocalizationAt
      stripEpsilon stripEta stripDelta₀
  zeta : ℝ
  zeta_pos : 0 < zeta
  zeta_lt_one : zeta < 1
  zeta_le_stripEta : zeta ≤ stripEta / 2
  zeta_le_epsilon_workingLambda :
    zeta ≤ epsilon * workingLambda / 30
  zeta_le_epsilon_lambda :
    zeta ≤ epsilon * projectionLambda / 30
  alpha : ℝ
  alpha_pos : 0 < alpha
  alpha_le_zeta_projectionLambda :
    alpha ≤ zeta * projectionLambda / 16
  projectionDelta₀ : ℝ
  projectionDelta₀_pos : 0 < projectionDelta₀
  projectionDelta₀_le_one : projectionDelta₀ ≤ 1
  projection :
    ∀ tau : ℝ, 0 < tau → tau ≤ projectionDelta₀ →
      ∀ F G₁ G₂ : DiscreteSet 2,
        F.Nonempty → G₁.Nonempty → G₂.Nonempty →
        F.IsInUnitBall → G₁.IsInUnitBall → G₂.IsInUnitBall →
        F.IsDeltaSeparated tau →
        G₁.IsDeltaSeparated tau →
        G₂.IsDeltaSeparated tau →
        F.IsFrostman tau 1
          (Kakeya.realRpowENN tau (-projectionLambda)) →
        G₁.IsFrostman tau 1
          (Kakeya.realRpowENN tau (-projectionLambda)) →
        G₂.IsFrostman tau 1
          (Kakeya.realRpowENN tau (-projectionLambda)) →
        WZ1StandardSeparation F G₁ G₂ →
        WZ1LineNonConcentration tau projectionLambda zeta G₁ →
        WZ1LineNonConcentration tau projectionLambda zeta G₂ →
        ∀ H : Finset (Point2 × Point2 × Point2),
          WZ1UniformTripleDensity
              (Kakeya.realRpowENN tau alpha)
              F G₁ G₂ H →
            Kakeya.realRpowENN tau (epsilon / 2 - 1) ≤
              (↑(Metric.externalCoveringNumber
                (Real.toNNReal tau)
                (wz1DotDifferenceSet H)) : ENNReal)

/-- Select one shared Proposition 8.5 instance for the output loss. -/
def WZ1Proposition8_9ParameterSelectionStatement : Prop :=
  WZ1LineNonconcentrationProjectionStatement →
    RadialBootstrappingMeasureThinTubesInput →
      WZ1StripLocalizationDichotomyStatement →
        ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 / 10 →
          Nonempty (WZ1Proposition8_9Parameters epsilon)

/--
The common-strip output after the two applications of PDF Lemma 8.13 in the
proof of Proposition 8.9.
-/
structure WZ1Proposition8_9CommonStripData
    (delta epsilon eta : ℝ)
    (parameters : WZ1Proposition8_9Parameters epsilon)
    (F G₁ G₂ : DiscreteSet 2)
    (H : Finset (Point2 × Point2 × Point2)) where
  selectedF : DiscreteSet 2
  selectedG₁ : DiscreteSet 2
  selectedG₂ : DiscreteSet 2
  refinedH : Finset (Point2 × Point2 × Point2)
  selectedF_subset : selectedF ⊆ F
  selectedG₁_subset : selectedG₁ ⊆ G₁
  selectedG₂_subset : selectedG₂ ⊆ G₂
  refinedH_subset : refinedH ⊆ H
  selectedF_nonempty : selectedF.Nonempty
  selectedG₁_nonempty : selectedG₁.Nonempty
  selectedG₂_nonempty : selectedG₂.Nonempty
  selectedF_ball : selectedF.IsInUnitBall
  selectedG₁_ball : selectedG₁.IsInUnitBall
  selectedG₂_ball : selectedG₂.IsInUnitBall
  selectedF_separated : selectedF.IsDeltaSeparated delta
  selectedG₁_separated : selectedG₁.IsDeltaSeparated delta
  selectedG₂_separated : selectedG₂.IsDeltaSeparated delta
  selectedF_frostman :
    selectedF.IsFrostman delta 1
      (Kakeya.realRpowENN delta (-parameters.workingLambda))
  selectedG₁_frostman :
    selectedG₁.IsFrostman delta 1
      (Kakeya.realRpowENN delta (-parameters.workingLambda))
  selectedG₂_frostman :
    selectedG₂.IsFrostman delta 1
      (Kakeya.realRpowENN delta (-parameters.workingLambda))
  firstRawNormal : Point2
  firstRawLevel : ℝ
  firstRawWidth : ℝ
  firstRawNormal_unit : ‖firstRawNormal‖ = 1
  firstRawWidth_pos : 0 < firstRawWidth
  first_raw_strip :
    ∀ point ∈ selectedG₁,
      |inner ℝ point firstRawNormal - firstRawLevel| ≤
        firstRawWidth
  secondRawNormal : Point2
  secondRawLevel : ℝ
  secondRawWidth : ℝ
  secondRawNormal_unit : ‖secondRawNormal‖ = 1
  secondRawWidth_pos : 0 < secondRawWidth
  second_raw_strip :
    ∀ point ∈ selectedG₂,
      |inner ℝ point secondRawNormal - secondRawLevel| ≤
        secondRawWidth
  first_raw_nonconcentration :
    WZ1WeightedRawStripNonconcentration
      delta parameters.zeta firstRawWidth
      ((256 : ENNReal) *
        Kakeya.realRpowENN delta (-eta))
      selectedG₁
  second_raw_nonconcentration :
    WZ1WeightedRawStripNonconcentration
      delta parameters.zeta secondRawWidth
      ((256 : ENNReal) *
        Kakeya.realRpowENN delta (-eta))
      selectedG₂
  standardSeparation :
    WZ1StandardSeparation selectedF selectedG₁ selectedG₂
  uniform :
    WZ1UniformTripleDensity
      ((1 / 256 : ENNReal) *
        Kakeya.realRpowENN delta eta)
      selectedF selectedG₁ selectedG₂ refinedH
  base : Point2
  direction : Point2
  direction_unit : ‖direction‖ = 1
  width : ℝ
  width_pos : 0 < width
  delta_le_width : delta ≤ width
  width_le_one : width ≤ 1
  width_le_first_raw :
    width ≤
      Real.rpow delta (-parameters.stripEpsilon) *
        firstRawWidth
  width_le_second_raw :
    width ≤
      Real.rpow delta (-parameters.stripEpsilon) *
        secondRawWidth
  first_strip :
    ∀ point ∈ selectedG₁,
      point ∈ wz1LineNeighborhood base direction width
  second_strip :
    ∀ point ∈ selectedG₂,
      point ∈ wz1LineNeighborhood base direction width
  orthogonal_strip :
    ∀ point ∈ selectedF,
      point ∈
        wz1LineNeighborhood 0 (wz1Perp2 direction) width

/-- The common-strip or long-projection conclusion used by Proposition 8.9. -/
def WZ1Proposition8_9CommonStripConclusion : Prop :=
  ∀ epsilon : ℝ,
    ∀ parameters : WZ1Proposition8_9Parameters epsilon,
    ∀ etaCap deltaCap : ℝ,
    0 < epsilon → epsilon < 1 →
    0 < etaCap → 0 < deltaCap →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧ eta ≤ etaCap ∧
      0 < delta₀ ∧ delta₀ ≤ deltaCap ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F G₁ G₂ : DiscreteSet 2,
          F.Nonempty → G₁.Nonempty → G₂.Nonempty →
          F.IsInUnitBall → G₁.IsInUnitBall → G₂.IsInUnitBall →
          F.IsDeltaSeparated delta →
          G₁.IsDeltaSeparated delta →
          G₂.IsDeltaSeparated delta →
          F.IsFrostman delta 1
            (Kakeya.realRpowENN delta (-eta)) →
          G₁.IsFrostman delta 1
            (Kakeya.realRpowENN delta (-eta)) →
          G₂.IsFrostman delta 1
            (Kakeya.realRpowENN delta (-eta)) →
          WZ1StandardSeparation F G₁ G₂ →
          ∀ H : Finset (Point2 × Point2 × Point2),
            WZ1UniformTripleDensity
                (Kakeya.realRpowENN delta eta)
                F G₁ G₂ H →
              WZ1StripLocalizationLongProjection
                  delta epsilon eta H ∨
                Nonempty
                  (WZ1Proposition8_9CommonStripData
                    delta epsilon eta parameters F G₁ G₂ H)

/--
Apply PDF Lemma 8.13 in both endpoint orders to the explicit two-ends
preparation and obtain one common-strip configuration.
-/
def WZ1Proposition8_9CommonStripFromPreparationStatement : Prop :=
  WZ1TripartiteHypergraphRefinementStatement →
    WZ1Proposition8_9TwoEndsPreparationStatement →
      WZ1Proposition8_9CommonStripConclusion

/--
Close the union-valued narrow branch used by the 3D Kakeya main line.

This statement does not claim the stronger arbitrary-`G₁,G₂` Alternative
(A) displayed in Proposition 8.9.
-/
def WZ1Proposition8_9NarrowStripStatement : Prop :=
  ∀ epsilon : ℝ,
    ∀ parameters : WZ1Proposition8_9Parameters epsilon,
    0 < epsilon → epsilon < 1 →
    ∃ etaCap delta₀ : ℝ,
      0 < etaCap ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta eta : ℝ}
        {F G₁ G₂ : DiscreteSet 2}
        {H : Finset (Point2 × Point2 × Point2)},
        0 < delta → delta ≤ delta₀ →
        0 < eta → eta ≤ etaCap →
        ∀ data :
          WZ1Proposition8_9CommonStripData
            delta epsilon eta parameters F G₁ G₂ H,
          data.width ≤ Real.rpow delta (1 - epsilon / 10) →
            WZ1Proposition8_9AlternativeAUnion
                delta epsilon F G₁ G₂ ∨
              WZ1StripLocalizationLongProjection
                delta epsilon eta H

/--
The direct same-endpoint specialization of the narrow branch used in the
two-set Theorem 22 application.
-/
def WZ1Proposition8_9NarrowSameEndpointStatement : Prop :=
  ∀ epsilon : ℝ,
    ∀ parameters : WZ1Proposition8_9Parameters epsilon,
    0 < epsilon → epsilon < 1 →
    ∃ etaCap delta₀ : ℝ,
      0 < etaCap ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta eta : ℝ}
        {F G : DiscreteSet 2}
        {H : Finset (Point2 × Point2 × Point2)},
        0 < delta → delta ≤ delta₀ →
        0 < eta → eta ≤ etaCap →
        ∀ data :
          WZ1Proposition8_9CommonStripData
            delta epsilon eta parameters F G G H,
          data.width ≤ Real.rpow delta (1 - epsilon / 10) →
            WZ1Proposition8_9AlternativeA
                delta epsilon F G G ∨
              WZ1StripLocalizationLongProjection
                delta epsilon eta H

/-- The genuinely strong narrow branch required for arbitrary independent
endpoint classes.  This is intentionally separate from the union-valued
main-line theorem above. -/
def WZ1Proposition8_9NarrowStrongStatement : Prop :=
  ∀ epsilon : ℝ,
    ∀ parameters : WZ1Proposition8_9Parameters epsilon,
    0 < epsilon → epsilon < 1 →
    ∃ etaCap delta₀ : ℝ,
      0 < etaCap ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta eta : ℝ}
        {F G₁ G₂ : DiscreteSet 2}
        {H : Finset (Point2 × Point2 × Point2)},
        0 < delta → delta ≤ delta₀ →
        0 < eta → eta ≤ etaCap →
        ∀ data :
          WZ1Proposition8_9CommonStripData
            delta epsilon eta parameters F G₁ G₂ H,
          data.width ≤ Real.rpow delta (1 - epsilon / 10) →
            WZ1Proposition8_9AlternativeA delta epsilon F G₁ G₂ ∨
              WZ1StripLocalizationLongProjection delta epsilon eta H

/--
The complete normalized Proposition 8.5 input produced in the wide branch.
The transport field records the return from scale `scale` to the original
dot-difference graph.
-/
structure WZ1Proposition8_9WideNormalizedData
    (delta epsilon eta : ℝ)
    (parameters : WZ1Proposition8_9Parameters epsilon)
    (F G₁ G₂ : DiscreteSet 2)
    (H : Finset (Point2 × Point2 × Point2)) where
  scale : ℝ
  scale_pos : 0 < scale
  scale_le_projectionDelta₀ :
    scale ≤ parameters.projectionDelta₀
  normalizedF : DiscreteSet 2
  normalizedG₁ : DiscreteSet 2
  normalizedG₂ : DiscreteSet 2
  normalizedH : Finset (Point2 × Point2 × Point2)
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
  transport :
    Kakeya.realRpowENN scale (epsilon / 2 - 1) ≤
        (↑(Metric.externalCoveringNumber
          (Real.toNNReal scale)
          (wz1DotDifferenceSet normalizedH)) : ENNReal) →
      WZ1StripLocalizationLongProjection
        delta epsilon eta H

/--
Prepare the paper's anisotropically normalized Proposition 8.5 input in the
wide common-strip branch.
-/
def WZ1Proposition8_9WideNormalizedPreparationStatement : Prop :=
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
                        (WZ1Proposition8_9WideNormalizedData
                          delta epsilon eta parameters F G₁ G₂ H)

/-- Close the wide common-strip branch by the paper's anisotropic rescaling. -/
def WZ1Proposition8_9WideStripStatement : Prop :=
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
                      Real.rpow delta (1 - epsilon / 10) < data.width →
                        WZ1StripLocalizationLongProjection
                          delta epsilon eta H

/-- Mechanical wide-branch assembly from the normalized package. -/
def WZ1Proposition8_9WideFromNormalizedStatement : Prop :=
  WZ1Proposition8_9WideNormalizedPreparationStatement →
    WZ1Proposition8_9WideStripStatement

/-- Mechanical assembly of PDF Proposition 8.9 from its three repaired leaves. -/
def WZ1Proposition8_9SplitAssemblyStatement : Prop :=
  WZ1Proposition8_9ParameterSelectionStatement →
    WZ1Proposition8_9CommonStripConclusion →
      WZ1Proposition8_9NarrowStrongStatement →
        WZ1Proposition8_9WideStripStatement →
          WZ1TripartiteHypergraphRefinementStatement →
            WZ1AnisotropicFrostmanRescalingStatement →
              WZ1LineNonconcentrationProjectionStatement →
                WZ1StripLocalizationDichotomyStatement →
                  RadialBootstrappingMeasureThinTubesInput →
                    WZ1WellSeparatedProjectionConclusion

/-- Faithful split assembly for the union-valued narrow theorem used by the
common-endpoint Lemma-23 graph. -/
def WZ1Proposition8_9UnionSplitAssemblyStatement : Prop :=
  WZ1Proposition8_9ParameterSelectionStatement →
    WZ1Proposition8_9CommonStripConclusion →
      WZ1Proposition8_9NarrowStripStatement →
        WZ1Proposition8_9WideStripStatement →
          WZ1TripartiteHypergraphRefinementStatement →
            WZ1AnisotropicFrostmanRescalingStatement →
              WZ1LineNonconcentrationProjectionStatement →
                WZ1StripLocalizationDichotomyStatement →
                  RadialBootstrappingMeasureThinTubesInput →
                    WZ1WellSeparatedProjectionUnionConclusion

/-- Recovery of the historical Proposition 8.9 input boundary. -/
def WZ1Proposition8_9LeafAssemblyStatement : Prop :=
  WZ1Proposition8_9ParameterSelectionStatement →
    WZ1Proposition8_9TwoEndsPreparationStatement →
      WZ1Proposition8_9CommonStripFromPreparationStatement →
        WZ1Proposition8_9NarrowStrongStatement →
          WZ1Proposition8_9WideNormalizedPreparationStatement →
            WZ1WellSeparatedProjectionFromLeavesStatement

end Kakeya.Assouad
