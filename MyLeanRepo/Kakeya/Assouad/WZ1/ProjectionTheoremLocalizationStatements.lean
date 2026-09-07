import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements

/-!
# Localization leaves for WZ1 Theorem 22

This module freezes the first unresolved result above the completed
first-layer projection theorems: WZ1 Lemma 49.  A tripartite graph whose
second vertex class lies in one narrow strip either localizes its other two
active projections to the same strip and the orthogonal origin-centered
strip, or already has the long-interval dot-difference conclusion required
by Theorem 22.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Active vertices in one coordinate projection of a tripartite graph. -/
def wz1ActiveTripleProjection
    (H : Finset (Point2 × Point2 × Point2))
    (i : Fin 3) : DiscreteSet 2 :=
  H.image fun edge => wz1TripleCoordinate edge i

/--
The paper's common active strip width for the second and third coordinate
projections.

The maximum is taken only over vertices occurring in `H`, not over unused
ambient vertices of `G₁` or `G₂`.  The lower truncation by `delta` records the
paper convention `delta ≤ t`.
-/
noncomputable def wz1ActiveCommonWidth
    (delta : ℝ)
    (H : Finset (Point2 × Point2 × Point2))
    (hH : H.Nonempty)
    (base direction : Point2) : ℝ :=
  let perpendicular := wz1Perp2 direction
  let widths : Finset ℝ :=
    H.image fun edge =>
      max
        |inner ℝ (edge.2.1 - base) perpendicular|
        |inner ℝ (edge.2.2 - base) perpendicular|
  max delta
    (widths.max' <| hH.image fun edge =>
      max
        |inner ℝ (edge.2.1 - base) perpendicular|
        |inner ℝ (edge.2.2 - base) perpendicular|)

/-- The long dot-difference projection alternative in WZ1 Lemma 49. -/
def WZ1StripLocalizationLongProjection
    (delta epsilon eta : ℝ)
    (H : Finset (Point2 × Point2 × Point2)) : Prop :=
  ∃ rho center radius : ℝ,
    delta ≤ rho ∧ rho ≤ 1 ∧
    0 < radius ∧
    Real.rpow delta (-eta) * rho ≤ 2 * radius ∧
    Kakeya.realRpowENN
        (2 * radius / rho) (1 - epsilon) ≤
      (↑(Metric.externalCoveringNumber
        (Real.toNNReal rho)
        (wz1DotDifferenceSet H ∩
          Metric.closedBall center radius)) :
        ENNReal)

/-- Fixed paper hierarchy parameter `epsilon₁ ≪ epsilon²` for Lemma 49. -/
def wz1Lemma49AuxiliaryEpsilon (epsilon : ℝ) : ℝ :=
  epsilon ^ 2 / 100

/--
WZ1 Lemma 49, in the finite-point model used by the projection theorem.

Only the points that occur in the graph are forced into the two strips in
the first alternative.  This matches the paper's preliminary reduction to
surjective coordinate projections and avoids imposing a condition on unused
vertices.
-/
def WZ1StripLocalizationDichotomyStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
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
            WZ1UniformTripleDensity
                (Kakeya.realRpowENN delta eta)
                F G₁ G₂ H →
            ∀ base direction : Point2,
              ‖direction‖ = 1 →
              ∀ w : ℝ, 0 < w → delta ≤ w →
                (∀ b ∈ G₁,
                  b ∈ wz1LineNeighborhood base direction w) →
                  ((∀ edge ∈ H,
                      edge.2.2 ∈
                        wz1LineNeighborhood base direction
                          (Real.rpow delta (-epsilon) * w)) ∧
                    (∀ edge ∈ H,
                      edge.1 ∈
                        wz1LineNeighborhood 0
                          (wz1Perp2 direction)
                          (Real.rpow delta (-epsilon) * w))) ∨
                    WZ1StripLocalizationLongProjection
                      delta epsilon eta H

/--
The residual Kaufman branch of WZ1 Lemma 49.

The common width is the exact maximum over the active `G₁` and `G₂`
projections.  The other active projection is assumed to lie in the
corresponding orthogonal strip, while the strict lower bound on the common
width excludes the elementary localization alternative.  Under precisely
these hypotheses the anisotropic-rescaling, radial-projection, and Kaufman
argument must produce the long dot-difference projection.
-/
def WZ1StripLocalizationKaufmanCaseStatement : Prop :=
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
                ∀ w : ℝ, 0 < w → delta ≤ w →
                  (∀ b ∈ G₁,
                    b ∈ wz1LineNeighborhood base direction w) →
                  let t :=
                    wz1ActiveCommonWidth
                      delta H hDensity.1 base direction
                  (∀ edge ∈ H,
                    edge.1 ∈
                      wz1LineNeighborhood 0
                        (wz1Perp2 direction)
                        (Real.rpow delta
                          (-wz1Lemma49AuxiliaryEpsilon epsilon) * t)) →
                  Real.rpow delta
                      (-epsilon + wz1Lemma49AuxiliaryEpsilon epsilon) * w < t →
                    WZ1StripLocalizationLongProjection
                      delta epsilon eta H

/-- Assemble all elementary branches of Lemma 49 around its Kaufman case. -/
def WZ1StripLocalizationDichotomyFromKaufmanStatement : Prop :=
  WZ1StripLocalizationKaufmanCaseStatement →
    WZ1StripLocalizationDichotomyStatement

end Kakeya.Assouad
