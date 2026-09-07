import MyLeanRepo.Kakeya.Cinematic.Section5.GeneralFiberCoefficientCardinalityTransport
import MyLeanRepo.Kakeya.Cinematic.Section5.SmallSupportTotalCardinalityInputs

/-!
# Total selected cardinality in the small-support branch
-/

namespace Kakeya.Cinematic

theorem small_support_total_cardinality :
    SmallSupportTotalCardinalityStatement := by
  intro hInterpolate
  intro original retained rawEdges selectedEdges heavy selectedCoarse
    M q mu support centers
  intro parentLoss degreeLoss supportLoss fiberBound retention
    measureScale tangencyScale coefficient tail
  intro hM hq hmu hsupport hsmall hparentLoss hdegreeLoss hsupportLoss
    hfiberBound hretention hmeasureScale htangencyScale hcoefficient htail
  intro horiginal hrawLower hedgeRetention hheavyLower hsupportRetention
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
  have h2 : (M : ℝ) ≤
      (Real.rpow measureScale (1 / 4 : ℝ) *
        Real.rpow tangencyScale (3 / 4 : ℝ)) *
        Real.rpow (mu : ℝ) (-3 / 2 : ℝ) *
        Real.rpow (support : ℝ) (3 / 2 : ℝ) :=
    coarse_interpolation_factorized
      hInterpolate (M : ℝ) measureScale tangencyScale
      (mu : ℝ) (support : ℝ)
      (by exact_mod_cast hM.le) hmeasureScale htangencyScale
      (by exact_mod_cast hmu) (by exact_mod_cast hsupport)
      hmeasure htangency
  set scale : ℝ :=
    Real.rpow measureScale (1 / 4 : ℝ) *
    Real.rpow tangencyScale (3 / 4 : ℝ) with hscaleDef
  have hscaleNonneg : 0 ≤ scale := by
    rw [hscaleDef]
    exact mul_nonneg
      (Real.rpow_nonneg hmeasureScale _)
      (Real.rpow_nonneg htangencyScale _)
  have h3 : ((M * selectedCoarse : ℕ) : ℝ) ≤
      scale * coefficient * tail *
        Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ) *
        Real.rpow (mu : ℝ) (-3 / 2 : ℝ) :=
    small_support_normal_fine_card_bound
      M selectedCoarse mu support centers
      scale coefficient tail
      hmu hsupport hsmall hscaleNonneg hcoefficient htail
      h2 hcoarse
  have hretentionRpowNonneg :
      0 ≤ Real.rpow retention (-1) :=
    Real.rpow_nonneg hretention.le _
  have hprefactorNonneg :
      0 ≤ (48 * parentLoss * degreeLoss * supportLoss *
            Real.rpow retention (-1)) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) hparentLoss)
          hdegreeLoss)
        hsupportLoss)
      hretentionRpowNonneg
  calc
    (original : ℝ) ≤
        (48 * parentLoss * degreeLoss * supportLoss *
            Real.rpow retention (-1)) *
          (((M * selectedCoarse : ℕ) : ℝ)) := h1
    _ ≤
        (48 * parentLoss * degreeLoss * supportLoss *
            Real.rpow retention (-1)) *
          (scale * coefficient * tail *
            Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ) *
            Real.rpow (mu : ℝ) (-3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left h3 hprefactorNonneg
    _ =
        (48 * parentLoss * degreeLoss * supportLoss *
            Real.rpow retention (-1)) *
          ((Real.rpow measureScale (1 / 4 : ℝ) *
              Real.rpow tangencyScale (3 / 4 : ℝ)) *
            coefficient * tail *
            Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ) *
            Real.rpow (mu : ℝ) (-3 / 2 : ℝ)) := by
      simp [hscaleDef, mul_assoc]

theorem small_support_total_cardinality_of_fiber_coefficient
    (hInterpolate : CoarseMultiplicityInterpolationStatement)
    (original retained rawEdges selectedEdges heavy selectedCoarse
      M q mu support centers : ℕ)
    (parentLoss degreeLoss supportLoss fiberBound retention
      fiberCoefficient measureScale tangencyScale coefficient tail : ℝ)
    (hM : 0 < M)
    (hq : 2 ≤ q)
    (hmu : 0 < mu)
    (hsupport : 0 < support)
    (hsmall : support < 2 * centers)
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
      (selectedCoarse : ℝ) ≤ coefficient * tail) :
    (original : ℝ) ≤
      (24 * fiberCoefficient * parentLoss * degreeLoss *
          supportLoss * Real.rpow retention (-1)) *
        ((Real.rpow measureScale (1 / 4 : ℝ) *
            Real.rpow tangencyScale (3 / 4 : ℝ)) *
          coefficient * tail *
          Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ) *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ)) := by
  have h1 :=
    general_fiber_coefficient_cardinality_transport
      original retained rawEdges selectedEdges heavy selectedCoarse
      M q mu parentLoss degreeLoss supportLoss fiberBound retention
      fiberCoefficient hM hq hmu hparentLoss hdegreeLoss
      hsupportLoss hfiberBound hretention hfiberCoefficient
      horiginal hrawLower hedgeRetention hheavyLower
      hsupportRetention hfiberScale hqRetention
  set scale : ℝ :=
    Real.rpow measureScale (1 / 4 : ℝ) *
      Real.rpow tangencyScale (3 / 4 : ℝ) with hscaleDef
  have hscaleNonneg : 0 ≤ scale := by
    rw [hscaleDef]
    exact mul_nonneg
      (Real.rpow_nonneg hmeasureScale _)
      (Real.rpow_nonneg htangencyScale _)
  have h2 :=
    coarse_interpolation_factorized
      hInterpolate (M : ℝ) measureScale tangencyScale
      (mu : ℝ) (support : ℝ)
      (by exact_mod_cast hM.le) hmeasureScale htangencyScale
      (by exact_mod_cast hmu) (by exact_mod_cast hsupport)
      hmeasure htangency
  have h3 :=
    small_support_normal_fine_card_bound
      M selectedCoarse mu support centers
      scale coefficient tail
      hmu hsupport hsmall hscaleNonneg hcoefficient htail
      h2 hcoarse
  have hprefactorNonneg :
      0 ≤ 24 * fiberCoefficient * parentLoss * degreeLoss *
        supportLoss * Real.rpow retention (-1) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) hparentLoss)
          hdegreeLoss)
        hsupportLoss)
      (Real.rpow_nonneg hretention.le _)
  exact h1.trans <| by
    simpa [hscaleDef, mul_assoc] using
      mul_le_mul_of_nonneg_left h3 hprefactorNonneg

end Kakeya.Cinematic
