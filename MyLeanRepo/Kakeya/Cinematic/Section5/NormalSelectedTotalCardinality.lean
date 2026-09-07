import MyLeanRepo.Kakeya.Cinematic.Section5.GeneralFiberCoefficientCardinalityTransport
import MyLeanRepo.Kakeya.Cinematic.Section5.NormalSelectedTotalCardinalityInputs

/-!
# Total selected-normal cardinality algebra
-/

namespace Kakeya.Cinematic

theorem normal_selected_total_cardinality :
    NormalSelectedTotalCardinalityStatement := by
  intro hInterpolate original retained rawEdges selectedEdges heavy
    selectedCoarse M q mu support parentLoss degreeLoss supportLoss
    fiberBound retention measureScale tangencyScale coefficient tail
    hM hq hmu hsupport hparentLoss hdegreeLoss hsupportLoss
    hfiberBound hretention hmeasureScale htangencyScale hcoefficient htail
    horiginal hrawLower hedgeRetention hheavyLower hsupportRetention
    hfiberScale hqRetention hmeasure htangency hcoarse
  have h1 : (original : ℝ) ≤
      (48 * parentLoss * degreeLoss * supportLoss *
        Real.rpow retention (-1)) *
        (((M * selectedCoarse : ℕ) : ℝ)) :=
    normal_selected_cardinality_transport
      original retained rawEdges selectedEdges heavy selectedCoarse M q mu
      parentLoss degreeLoss supportLoss fiberBound retention
      hM hq hmu hparentLoss hdegreeLoss hsupportLoss hfiberBound hretention
      horiginal hrawLower hedgeRetention hheavyLower hsupportRetention
      hfiberScale hqRetention
  have h2 : ((M * selectedCoarse : ℕ) : ℝ) ≤
      (Real.rpow measureScale (1 / 4 : ℝ) *
        Real.rpow tangencyScale (3 / 4 : ℝ)) *
        coefficient * tail *
        Real.rpow (mu : ℝ) (-3 / 2 : ℝ) :=
    normal_fine_card_bound_from_interpolation
      hInterpolate M selectedCoarse mu support
      measureScale tangencyScale coefficient tail
      hM hmu hsupport hmeasureScale htangencyScale hcoefficient htail
      hmeasure htangency hcoarse
  have hlossNonneg : 0 ≤
      48 * parentLoss * degreeLoss * supportLoss *
        Real.rpow retention (-1) :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) hparentLoss)
          hdegreeLoss)
        hsupportLoss)
      (Real.rpow_nonneg hretention.le _)
  have h3 : (48 * parentLoss * degreeLoss * supportLoss *
        Real.rpow retention (-1)) *
        (((M * selectedCoarse : ℕ) : ℝ)) ≤
      (48 * parentLoss * degreeLoss * supportLoss *
        Real.rpow retention (-1)) *
        ((Real.rpow measureScale (1 / 4 : ℝ) *
          Real.rpow tangencyScale (3 / 4 : ℝ)) *
          coefficient * tail *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left h2 hlossNonneg
  exact h1.trans h3

theorem normal_selected_total_cardinality_of_fiber_coefficient
    (hInterpolate : CoarseMultiplicityInterpolationStatement)
    (original retained rawEdges selectedEdges heavy selectedCoarse
      M q mu support : ℕ)
    (parentLoss degreeLoss supportLoss fiberBound retention
      fiberCoefficient measureScale tangencyScale coefficient tail : ℝ)
    (hM : 0 < M)
    (hq : 2 ≤ q)
    (hmu : 0 < mu)
    (hsupport : 0 < support)
    (hparentLoss : 0 ≤ parentLoss)
    (hdegreeLoss : 0 ≤ degreeLoss)
    (hsupportLoss : 0 ≤ supportLoss)
    (hfiberBound : 0 < fiberBound)
    (hretention : 0 < retention)
    (hfiberCoefficient : 0 ≤ fiberCoefficient)
    (hmeasureScale : 0 ≤ measureScale)
    (htangencyScale : 0 ≤ tangencyScale)
    (hcoefficient : 0 ≤ coefficient)
    (htail : 0 ≤ tail)
    (horiginal :
      (original : ℝ) ≤ parentLoss * (retained : ℝ))
    (hrawLower :
      (retained : ℝ) * (q : ℝ) ≤ (rawEdges : ℝ))
    (hedgeRetention :
      (rawEdges : ℝ) ≤ degreeLoss * (selectedEdges : ℝ))
    (hheavyLower :
      ((selectedEdges : ℝ) / 2) /
          ((2 * (M : ℝ)) * fiberBound) ≤ (heavy : ℝ))
    (hsupportRetention :
      (heavy : ℝ) ≤ supportLoss * (selectedCoarse : ℝ))
    (hfiberScale :
      fiberBound ≤ fiberCoefficient * (mu : ℝ))
    (hqRetention :
      retention * (mu : ℝ) < 4 * ((q : ℝ) + 1))
    (hmeasure : (M : ℝ) ≤ measureScale)
    (htangency :
      (M : ℝ) ≤
        tangencyScale * Real.rpow (mu : ℝ) (-2) *
          Real.rpow (support : ℝ) 2)
    (hcoarse :
      (selectedCoarse : ℝ) ≤
        coefficient * Real.rpow (support : ℝ) (-3 / 2 : ℝ) *
          tail) :
    (original : ℝ) ≤
      (24 * fiberCoefficient * parentLoss * degreeLoss *
          supportLoss * Real.rpow retention (-1)) *
        ((Real.rpow measureScale (1 / 4 : ℝ) *
          Real.rpow tangencyScale (3 / 4 : ℝ)) *
          coefficient * tail *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ)) := by
  have h1 :=
    general_fiber_coefficient_cardinality_transport
      original retained rawEdges selectedEdges heavy selectedCoarse
      M q mu parentLoss degreeLoss supportLoss fiberBound retention
      fiberCoefficient hM hq hmu hparentLoss hdegreeLoss
      hsupportLoss hfiberBound hretention hfiberCoefficient
      horiginal hrawLower hedgeRetention hheavyLower
      hsupportRetention hfiberScale hqRetention
  have h2 :=
    normal_fine_card_bound_from_interpolation
      hInterpolate M selectedCoarse mu support
      measureScale tangencyScale coefficient tail
      hM hmu hsupport hmeasureScale htangencyScale
      hcoefficient htail hmeasure htangency hcoarse
  have hlossNonneg :
      0 ≤ 24 * fiberCoefficient * parentLoss * degreeLoss *
        supportLoss * Real.rpow retention (-1) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) hparentLoss)
          hdegreeLoss)
        hsupportLoss)
      (Real.rpow_nonneg hretention.le _)
  exact h1.trans <|
    mul_le_mul_of_nonneg_left h2 hlossNonneg

end Kakeya.Cinematic
