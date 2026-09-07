import MyLeanRepo.Kakeya.Assouad.WZ1.Theorem5_2LeafStatements

/-!
# Honest split of the narrow branch of PDF Proposition 8.9

The hard geometric step either produces Alternative (A), with one common
affine line for both endpoint classes and its origin-centered orthogonal line
for the first class, or produces actual separated dot-difference values.
The latter package is exactly the finite input consumed by the already closed
covering transport.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/--
Finite separated dot-difference evidence for the long-projection conclusion.

The radius in `cardinality` is the paper interval radius enlarged only when
needed to meet the required lower bound on interval length.
-/
structure WZ1Proposition8_9NarrowDotSpreadData
    (delta epsilon eta : ℝ)
    (H : Finset (Point2 × Point2 × Point2)) where
  values : Finset ℝ
  lower : ℝ
  upper : ℝ
  lower_mem : lower ∈ values
  upper_mem : upper ∈ values
  separated :
    ∀ first ∈ values, ∀ second ∈ values,
      first ≠ second → 2 * delta < |first - second|
  values_dot :
    (values : Set ℝ) ⊆ wz1DotDifferenceSet H
  between :
    ∀ value ∈ values, lower ≤ value ∧ value ≤ upper
  cardinality :
    Kakeya.realRpowENN
        (2 *
            max ((upper - lower) / 2)
              (Real.rpow delta (1 - eta) / 2) /
          delta)
        (1 - epsilon) ≤
      (values.card : ENNReal)

/--
The hard finite geometry in the narrow common-strip branch.

This statement deliberately preserves the paper's disjunction.  Independent
one-dimensional pigeonholes do not by themselves put the two endpoint
classes on the same affine line or put the first class on its
origin-centered orthogonal line.  Failure to synchronize those choices must
instead produce genuine separated values of `a · (b₁ - b₂)`.
-/
def WZ1Proposition8_9NarrowDotSpreadStatement : Prop :=
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
            WZ1Proposition8_9AlternativeA
                delta epsilon F G₁ G₂ ∨
              Nonempty
                (WZ1Proposition8_9NarrowDotSpreadData
                  delta epsilon eta H)

/--
Mechanical assembly of the narrow branch from separated dot-spread evidence.
-/
def WZ1Proposition8_9NarrowFromDotSpreadStatement : Prop :=
  WZ1Proposition8_9NarrowDotSpreadStatement →
    WZ1Proposition8_9NarrowStripStatement

end Kakeya.Assouad
