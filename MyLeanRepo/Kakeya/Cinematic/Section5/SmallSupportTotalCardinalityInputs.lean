import MyLeanRepo.Kakeya.Cinematic.Section5.NormalCoarseCountAlgebra

/-!
# Total selected cardinality in the small-support branch

When the support scale is smaller than twice the tangent-ball cover
cardinality, the `q_cluster = 1` fallback does not create a negative support
power.  Instead the positive `support^(3/2)` from interpolation is absorbed by
`(2 * centers)^(3/2)`.
-/

namespace Kakeya.Cinematic

def SmallSupportTotalCardinalityStatement : Prop :=
  CoarseMultiplicityInterpolationStatement →
    ∀ (original retained rawEdges selectedEdges heavy selectedCoarse
        M q mu support centers : ℕ)
      (parentLoss degreeLoss supportLoss fiberBound retention
        measureScale tangencyScale coefficient tail : ℝ),
      0 < M →
      2 ≤ q →
      0 < mu →
      0 < support →
      support < 2 * centers →
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
      (selectedCoarse : ℝ) ≤ coefficient * tail →
      (original : ℝ) ≤
        (48 * parentLoss * degreeLoss * supportLoss *
          Real.rpow retention (-1)) *
        ((Real.rpow measureScale (1 / 4 : ℝ) *
          Real.rpow tangencyScale (3 / 4 : ℝ)) *
          coefficient * tail *
          Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ) *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ))

end Kakeya.Cinematic
