import MyLeanRepo.Kakeya.Cinematic.Section5.GeneralFiberCoefficientCardinalityTransportInputs

/-!
# Selected-cardinality transport with a general fiber coefficient
-/

namespace Kakeya.Cinematic

theorem general_fiber_coefficient_cardinality_transport :
    GeneralFiberCoefficientCardinalityTransportStatement := by
  intro original retained rawEdges selectedEdges heavy selectedCoarse M q mu
    parentLoss degreeLoss supportLoss fiberBound retention fiberCoefficient
    hM hq hmu hparentLoss hdegreeLoss hsupportLoss hfiberBound hretention
    hfiberCoefficient horiginal hrawLower hedgeRetention hheavyLower
    hsupportRetention hfiberScale hqRetention
  have hMReal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hqReal : 2 ≤ (q : ℝ) := by exact_mod_cast hq
  have hqPos : 0 < (q : ℝ) := by linarith
  have hmuReal : 0 < (mu : ℝ) := by exact_mod_cast hmu
  have hupper : 0 < (2 * (M : ℝ)) * fiberBound := by positivity
  have hselectedUpper :
      (selectedEdges : ℝ) ≤ 4 * (M : ℝ) * fiberBound * (heavy : ℝ) := by
    have h := (div_le_iff₀ hupper).mp hheavyLower
    nlinarith
  have horiginalQ :
      (original : ℝ) * (q : ℝ) ≤
        4 * parentLoss * degreeLoss * (M : ℝ) *
          fiberBound * (heavy : ℝ) := by
    calc
      (original : ℝ) * (q : ℝ) ≤
          (parentLoss * (retained : ℝ)) * (q : ℝ) :=
        mul_le_mul_of_nonneg_right horiginal hqPos.le
      _ = parentLoss * ((retained : ℝ) * (q : ℝ)) := by ring
      _ ≤ parentLoss * (rawEdges : ℝ) :=
        mul_le_mul_of_nonneg_left hrawLower hparentLoss
      _ ≤ parentLoss * (degreeLoss * (selectedEdges : ℝ)) :=
        mul_le_mul_of_nonneg_left hedgeRetention hparentLoss
      _ ≤ parentLoss *
          (degreeLoss *
            (4 * (M : ℝ) * fiberBound * (heavy : ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hselectedUpper hdegreeLoss)
          hparentLoss
      _ = 4 * parentLoss * degreeLoss * (M : ℝ) *
          fiberBound * (heavy : ℝ) := by ring
  have horiginalQSelected :
      (original : ℝ) * (q : ℝ) ≤
        4 * parentLoss * degreeLoss * supportLoss *
          (M : ℝ) * fiberBound * (selectedCoarse : ℝ) := by
    calc
      (original : ℝ) * (q : ℝ) ≤
          4 * parentLoss * degreeLoss * (M : ℝ) *
            fiberBound * (heavy : ℝ) :=
        horiginalQ
      _ ≤ 4 * parentLoss * degreeLoss * (M : ℝ) *
          fiberBound * (supportLoss * (selectedCoarse : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          hsupportRetention (by positivity)
      _ = 4 * parentLoss * degreeLoss * supportLoss *
          (M : ℝ) * fiberBound * (selectedCoarse : ℝ) := by ring
  have hqUpper :
      4 * ((q : ℝ) + 1) ≤ 6 * (q : ℝ) := by
    linarith
  have hretentionMu :
      retention * (mu : ℝ) ≤ 6 * (q : ℝ) :=
    (hqRetention.trans_le hqUpper).le
  have hretentionFiber :
      retention * fiberBound ≤ 6 * fiberCoefficient * (q : ℝ) := by
    calc
      retention * fiberBound ≤
          retention * (fiberCoefficient * (mu : ℝ)) :=
        mul_le_mul_of_nonneg_left hfiberScale hretention.le
      _ = fiberCoefficient * (retention * (mu : ℝ)) := by ring
      _ ≤ fiberCoefficient * (6 * (q : ℝ)) := by
        gcongr
      _ = 6 * fiberCoefficient * (q : ℝ) := by ring
  have hscaled :
      ((original : ℝ) * retention) * (q : ℝ) ≤
        (24 * fiberCoefficient * parentLoss * degreeLoss * supportLoss *
          ((M * selectedCoarse : ℕ) : ℝ)) * (q : ℝ) := by
    calc
      ((original : ℝ) * retention) * (q : ℝ) =
          retention * ((original : ℝ) * (q : ℝ)) := by ring
      _ ≤ retention *
          (4 * parentLoss * degreeLoss * supportLoss *
            (M : ℝ) * fiberBound * (selectedCoarse : ℝ)) :=
        mul_le_mul_of_nonneg_left
          horiginalQSelected hretention.le
      _ = (4 * parentLoss * degreeLoss * supportLoss *
          (M : ℝ) * (selectedCoarse : ℝ)) *
            (retention * fiberBound) := by ring
      _ ≤ (4 * parentLoss * degreeLoss * supportLoss *
          (M : ℝ) * (selectedCoarse : ℝ)) *
            (6 * fiberCoefficient * (q : ℝ)) :=
        mul_le_mul_of_nonneg_left hretentionFiber
          (by positivity)
      _ = (24 * fiberCoefficient * parentLoss * degreeLoss * supportLoss *
          ((M * selectedCoarse : ℕ) : ℝ)) * (q : ℝ) := by
        norm_num [Nat.cast_mul]
        ring
  have hretainedCancel :
      (original : ℝ) * retention ≤
        24 * fiberCoefficient * parentLoss * degreeLoss * supportLoss *
          ((M * selectedCoarse : ℕ) : ℝ) :=
    le_of_mul_le_mul_right hscaled hqPos
  have hrpowRetention :
      Real.rpow retention (-1) = retention⁻¹ := by
    calc
      Real.rpow retention (-1) =
          (Real.rpow retention (1 : ℝ))⁻¹ :=
        Real.rpow_neg hretention.le (1 : ℝ)
      _ = retention⁻¹ := by simp
  rw [hrpowRetention]
  rw [show
    24 * fiberCoefficient * parentLoss * degreeLoss * supportLoss * retention⁻¹ *
        ((M * selectedCoarse : ℕ) : ℝ) =
      (24 * fiberCoefficient * parentLoss * degreeLoss * supportLoss *
        ((M * selectedCoarse : ℕ) : ℝ)) * retention⁻¹ by ring]
  exact (le_mul_inv_iff₀ hretention).2 hretainedCancel

end Kakeya.Cinematic
