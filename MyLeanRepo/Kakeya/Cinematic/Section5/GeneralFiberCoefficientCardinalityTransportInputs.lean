import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Selected-cardinality transport with a general fiber coefficient

The joint retained-fiber scale gives a fiber upper bound of the form
`fiberBound ≤ fiberCoefficient * mu`, where the coefficient is not
necessarily the old special value `2`.  This pure algebraic statement keeps
that coefficient explicit in the finite-regularization loss.
-/

namespace Kakeya.Cinematic

def GeneralFiberCoefficientCardinalityTransportStatement : Prop :=
  ∀ (original retained rawEdges selectedEdges heavy
      selectedCoarse M q mu : ℕ)
    (parentLoss degreeLoss supportLoss fiberBound
      retention fiberCoefficient : ℝ),
    0 < M →
    2 ≤ q →
    0 < mu →
    0 ≤ parentLoss →
    0 ≤ degreeLoss →
    0 ≤ supportLoss →
    0 < fiberBound →
    0 < retention →
    0 ≤ fiberCoefficient →
    (original : ℝ) ≤ parentLoss * (retained : ℝ) →
    (retained : ℝ) * (q : ℝ) ≤ (rawEdges : ℝ) →
    (rawEdges : ℝ) ≤ degreeLoss * (selectedEdges : ℝ) →
    ((selectedEdges : ℝ) / 2) /
        ((2 * (M : ℝ)) * fiberBound) ≤ (heavy : ℝ) →
    (heavy : ℝ) ≤ supportLoss * (selectedCoarse : ℝ) →
    fiberBound ≤ fiberCoefficient * (mu : ℝ) →
    retention * (mu : ℝ) < 4 * ((q : ℝ) + 1) →
    (original : ℝ) ≤
      (24 * fiberCoefficient * parentLoss * degreeLoss *
          supportLoss * Real.rpow retention (-1)) *
        (((M * selectedCoarse : ℕ) : ℝ))

end Kakeya.Cinematic
