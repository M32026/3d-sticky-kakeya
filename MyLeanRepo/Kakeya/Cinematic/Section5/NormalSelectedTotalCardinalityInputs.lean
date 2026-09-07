import MyLeanRepo.Kakeya.Cinematic.Section5.NormalCoarseCountAlgebra

/-!
# Total selected-normal cardinality algebra

The faithful Section 5 normal route has two independent losses:

* finite regularization transports the original fine-rectangle count to
  `M_parent * selectedCoarse`; and
* measure/tangency interpolation followed by Proposition 26 controls that
  product with exact support cancellation.

This statement composes those two already-closed steps while keeping every
parent, degree, support, and retention loss explicit.
-/

namespace Kakeya.Cinematic

def NormalSelectedTotalCardinalityStatement : Prop :=
  CoarseMultiplicityInterpolationStatement →
    ∀ (original retained rawEdges selectedEdges heavy selectedCoarse
        M q mu support : ℕ)
      (parentLoss degreeLoss supportLoss fiberBound retention
        measureScale tangencyScale coefficient tail : ℝ),
      0 < M →
      2 ≤ q →
      0 < mu →
      0 < support →
      0 ≤ parentLoss →
      0 ≤ degreeLoss →
      0 ≤ supportLoss →
      0 < fiberBound →
      0 < retention →
      0 ≤ measureScale →
      0 ≤ tangencyScale →
      0 ≤ coefficient →
      0 ≤ tail →
      (original : ℝ) ≤ parentLoss * (retained : ℝ) →
      (retained : ℝ) * (q : ℝ) ≤ (rawEdges : ℝ) →
      (rawEdges : ℝ) ≤ degreeLoss * (selectedEdges : ℝ) →
      ((selectedEdges : ℝ) / 2) /
          ((2 * (M : ℝ)) * fiberBound) ≤ (heavy : ℝ) →
      (heavy : ℝ) ≤ supportLoss * (selectedCoarse : ℝ) →
      fiberBound ≤ 2 * (mu : ℝ) →
      retention * (mu : ℝ) < 4 * ((q : ℝ) + 1) →
      (M : ℝ) ≤ measureScale →
      (M : ℝ) ≤
        tangencyScale * Real.rpow (mu : ℝ) (-2) *
          Real.rpow (support : ℝ) 2 →
      (selectedCoarse : ℝ) ≤
        coefficient * Real.rpow (support : ℝ) (-3 / 2 : ℝ) *
          tail →
      (original : ℝ) ≤
        (48 * parentLoss * degreeLoss * supportLoss *
          Real.rpow retention (-1)) *
        ((Real.rpow measureScale (1 / 4 : ℝ) *
          Real.rpow tangencyScale (3 / 4 : ℝ)) *
          coefficient * tail *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ))

end Kakeya.Cinematic
