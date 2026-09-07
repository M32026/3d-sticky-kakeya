import MyLeanRepo.Kakeya.Assouad.WZ1.LineNonconcentrationProjectionStatement
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremLocalizationStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Statements

/-!
# Final paper boundaries for WZ1 Theorem 22

The completed first-layer projection results and Proposition 41 feed two
remaining paper-level steps:

* Proposition 45 under the standard separation hypotheses;
* the final affine reduction removing standard separation.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The `Point2`, three-coordinate instance of WZ1 Lemma 37. -/
def WZ1TripartiteHypergraphRefinementStatement : Prop :=
  ∀ A : Fin 3 → Finset Point2,
    ∀ H : Finset (Fin 3 → Point2),
      (∀ edge ∈ H, ∀ i, edge i ∈ A i) →
      ∀ epsilon : ENNReal, 0 < epsilon → epsilon < 1 →
        ∃ H' : Finset (Fin 3 → Point2),
          H' ⊆ H ∧
          (1 - epsilon) * (H.card : ENNReal) ≤
            (H'.card : ENNReal) ∧
          WZ1UniformHypergraphDensity
            ((epsilon / (2 : ENNReal) ^ (3 : ℕ)) *
              ((H.card : ENNReal) /
                wz1VertexCardProduct A Finset.univ))
            A H'

/-- WZ1 Proposition 45 in the finite-point model. -/
def WZ1WellSeparatedProjectionConclusion : Prop :=
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
              (∃ base direction : Point2,
                  ‖direction‖ = 1 ∧
                  Kakeya.realRpowENN delta (epsilon - 1) ≤
                    wz1DiscreteLineCount
                      F 0 (wz1Perp2 direction) delta ∧
                  Kakeya.realRpowENN delta (epsilon - 1) ≤
                    wz1DiscreteLineCount
                      G₁ base direction delta ∧
                  Kakeya.realRpowENN delta (epsilon - 1) ≤
                    wz1DiscreteLineCount
                      G₂ base direction delta) ∨
                (∃ rho center radius : ℝ,
                  delta ≤ rho ∧ rho ≤ 1 ∧
                  0 < radius ∧
                  Real.rpow delta (-eta) * rho ≤ 2 * radius ∧
                  Kakeya.realRpowENN
                      (2 * radius / rho) (1 - epsilon) ≤
                    (↑(Metric.externalCoveringNumber
                      (Real.toNNReal rho)
                      (wz1DotDifferenceSet H ∩
                        Metric.closedBall center radius)) :
                      ENNReal))

/-- The well-separated conclusion sufficient for the common-endpoint
application in Lemma 23.  The two active endpoint classes are refinements of
one ambient local-graph set, so retaining either endpoint line count is
enough after transport back to that ambient set. -/
def WZ1WellSeparatedProjectionUnionConclusion : Prop :=
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
                (Kakeya.realRpowENN delta eta) F G₁ G₂ H →
              (∃ base direction : Point2,
                  ‖direction‖ = 1 ∧
                  Kakeya.realRpowENN delta (epsilon - 1) ≤
                    wz1DiscreteLineCount
                      F 0 (wz1Perp2 direction) delta ∧
                  (Kakeya.realRpowENN delta (epsilon - 1) ≤
                      wz1DiscreteLineCount G₁ base direction delta ∨
                    Kakeya.realRpowENN delta (epsilon - 1) ≤
                      wz1DiscreteLineCount G₂ base direction delta)) ∨
                WZ1StripLocalizationLongProjection
                  delta epsilon eta H

/--
Assemble Proposition 45 from the already separated paper leaves.

The two-ends reduction and its conversion to strip non-concentration are
closed repository lemmas.  The explicit predecessors here are precisely the
non-mechanical producers used after that reduction.
-/
def WZ1WellSeparatedProjectionFromLeavesStatement : Prop :=
  WZ1TripartiteHypergraphRefinementStatement →
    WZ1AnisotropicFrostmanRescalingStatement →
      WZ1LineNonconcentrationProjectionStatement →
        WZ1StripLocalizationDichotomyStatement →
          RadialBootstrappingMeasureThinTubesInput →
            WZ1WellSeparatedProjectionConclusion

/--
Remove standard separation from Proposition 45.

This is the paper's final affine normalization: place the three active vertex
classes in fixed separated balls, refine the transformed hypergraph
uniformly, apply Proposition 45, and transport either conclusion back.
-/
def WZ1ProjectionDichotomyFromWellSeparatedStatement : Prop :=
  WZ1TripartiteHypergraphRefinementStatement →
    WZ1WellSeparatedProjectionConclusion →
      WZ1ProjectionDichotomyConclusion

/-- Mechanical assembly of the final WZ1 Theorem 22 statement. -/
def WZ1ProjectionDichotomyFromLeavesStatement : Prop :=
  WZ1WellSeparatedProjectionFromLeavesStatement →
    WZ1ProjectionDichotomyFromWellSeparatedStatement →
      WZ1StripLocalizationDichotomyStatement →
        WZ1ProjectionDichotomyStatement

end Kakeya.Assouad
