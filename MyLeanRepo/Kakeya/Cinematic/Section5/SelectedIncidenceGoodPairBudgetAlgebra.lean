import MyLeanRepo.Kakeya.Cinematic.Section5.NormalCoarseCountAlgebra

/-!
# Scale budgets for selected-incidence good pairs

The uniform retained-fiber lower scale controls the original multiplicity
through a natural `q`.  After selecting rectangle fibers at the lower scale
`pairLower`, this module converts small metric and tangency bad-set factors
into the two cardinality budgets required by the selected-subfiber form of
PYZ Lemma 45.
-/

namespace Kakeya.Cinematic

lemma selected_incidence_fiber_bad_budget
    (q pairLower mu selectedCard fiberCard : ℕ)
    (retention rectangleLoss fiberCoefficient
      badCoefficient badScale : ℝ)
    (hq : 2 ≤ q)
    (hmu : 0 < mu)
    (hrectangleLoss : 0 < rectangleLoss)
    (hbadCoefficient : 0 ≤ badCoefficient)
    (hbadScale : 0 ≤ badScale)
    (hqRetention :
      retention * (mu : ℝ) < 4 * ((q : ℝ) + 1))
    (hpairLower :
      (q : ℝ) ≤ 2 * rectangleLoss * (pairLower : ℝ))
    (hselected : pairLower ≤ selectedCard)
    (hfiberCard :
      (fiberCard : ℝ) ≤ fiberCoefficient * (mu : ℝ))
    (hsmall :
      12 * rectangleLoss * badCoefficient * badScale *
          fiberCoefficient ≤ retention) :
    badCoefficient * badScale * (fiberCard : ℝ) ≤
      (selectedCard : ℝ) := by
  have hqReal : 2 ≤ (q : ℝ) := by
    exact_mod_cast hq
  have hmuReal : 0 < (mu : ℝ) := by
    exact_mod_cast hmu
  have hselectedReal :
      (pairLower : ℝ) ≤ (selectedCard : ℝ) := by
    exact_mod_cast hselected
  have hqUpper :
      4 * ((q : ℝ) + 1) ≤ 6 * (q : ℝ) := by
    linarith
  have hretentionMu :
      retention * (mu : ℝ) ≤ 6 * (q : ℝ) :=
    (hqRetention.trans_le hqUpper).le
  have hqPair :
      6 * (q : ℝ) ≤
        12 * rectangleLoss * (pairLower : ℝ) := by
    nlinarith
  have hretentionPair :
      retention * (mu : ℝ) ≤
        12 * rectangleLoss * (pairLower : ℝ) :=
    hretentionMu.trans hqPair
  have hsmallMu :
      (12 * rectangleLoss * badCoefficient * badScale *
          fiberCoefficient) * (mu : ℝ) ≤
        retention * (mu : ℝ) :=
    mul_le_mul_of_nonneg_right hsmall hmuReal.le
  have hcancel :
      badCoefficient * badScale *
          (fiberCoefficient * (mu : ℝ)) ≤
        (pairLower : ℝ) := by
    have hfull := hsmallMu.trans hretentionPair
    have hfactor : 0 < 12 * rectangleLoss := by
      positivity
    apply le_of_mul_le_mul_left
      (a := 12 * rectangleLoss)
    · calc
        (12 * rectangleLoss) *
              (badCoefficient * badScale *
                (fiberCoefficient * (mu : ℝ))) =
            (12 * rectangleLoss * badCoefficient * badScale *
              fiberCoefficient) * (mu : ℝ) := by ring
        _ ≤ 12 * rectangleLoss * (pairLower : ℝ) := hfull
    · exact hfactor
  calc
    badCoefficient * badScale * (fiberCard : ℝ) ≤
        badCoefficient * badScale *
          (fiberCoefficient * (mu : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hfiberCard
        (mul_nonneg hbadCoefficient hbadScale)
    _ ≤ (pairLower : ℝ) := hcancel
    _ ≤ (selectedCard : ℝ) := hselectedReal

lemma selected_incidence_fiber_good_pair_budgets
    (q pairLower mu selectedCard metricFiberCard
      tangencyFiberCard : ℕ)
    (retention rectangleLoss fiberCoefficient
      metricBadScale tangencyBadScale : ℝ)
    (hq : 2 ≤ q)
    (hmu : 0 < mu)
    (hrectangleLoss : 0 < rectangleLoss)
    (hmetricBadScale : 0 ≤ metricBadScale)
    (htangencyBadScale : 0 ≤ tangencyBadScale)
    (hqRetention :
      retention * (mu : ℝ) < 4 * ((q : ℝ) + 1))
    (hpairLower :
      (q : ℝ) ≤ 2 * rectangleLoss * (pairLower : ℝ))
    (hselected : pairLower ≤ selectedCard)
    (hmetricFiber :
      (metricFiberCard : ℝ) ≤
        fiberCoefficient * (mu : ℝ))
    (htangencyFiber :
      (tangencyFiberCard : ℝ) ≤
        fiberCoefficient * (mu : ℝ))
    (hmetricSmall :
      12 * rectangleLoss * 12 * metricBadScale *
          fiberCoefficient ≤ retention)
    (htangencySmall :
      12 * rectangleLoss * 6 * tangencyBadScale *
          fiberCoefficient ≤ retention) :
    12 * metricBadScale * (metricFiberCard : ℝ) ≤
        (selectedCard : ℝ) ∧
      6 * tangencyBadScale * (tangencyFiberCard : ℝ) ≤
        (selectedCard : ℝ) := by
  constructor
  · exact selected_incidence_fiber_bad_budget
      q pairLower mu selectedCard metricFiberCard
      retention rectangleLoss fiberCoefficient
      12 metricBadScale hq hmu hrectangleLoss
      (by norm_num) hmetricBadScale hqRetention
      hpairLower hselected hmetricFiber hmetricSmall
  · exact selected_incidence_fiber_bad_budget
      q pairLower mu selectedCard tangencyFiberCard
      retention rectangleLoss fiberCoefficient
      6 tangencyBadScale hq hmu hrectangleLoss
      (by norm_num) htangencyBadScale hqRetention
      hpairLower hselected htangencyFiber htangencySmall

lemma selected_incidence_fiber_good_pair_budgets_of_joint_scales
    (q pairLower selectedCard metricFiberCard
      tangencyFiberCard : ℕ)
    (heavyLogLoss fiberRatio metricBadScale tangencyBadScale : ℝ)
    (hheavyLogLoss : 0 ≤ heavyLogLoss)
    (hfiberRatio : 0 ≤ fiberRatio)
    (hmetricBadScale : 0 ≤ metricBadScale)
    (htangencyBadScale : 0 ≤ tangencyBadScale)
    (hqPair :
      (q : ℝ) ≤
        2 * heavyLogLoss * (pairLower : ℝ))
    (hselected : pairLower ≤ selectedCard)
    (hmetricFiber :
      (metricFiberCard : ℝ) ≤
        fiberRatio * (q : ℝ))
    (htangencyFiber :
      (tangencyFiberCard : ℝ) ≤
        2 * (q : ℝ))
    (hmetricSmall :
      24 * heavyLogLoss * metricBadScale * fiberRatio ≤ 1)
    (htangencySmall :
      24 * heavyLogLoss * tangencyBadScale ≤ 1) :
    12 * metricBadScale * (metricFiberCard : ℝ) ≤
        (selectedCard : ℝ) ∧
      6 * tangencyBadScale * (tangencyFiberCard : ℝ) ≤
        (selectedCard : ℝ) := by
  have hselectedReal :
      (pairLower : ℝ) ≤ (selectedCard : ℝ) := by
    exact_mod_cast hselected
  constructor
  · calc
      12 * metricBadScale * (metricFiberCard : ℝ) ≤
          12 * metricBadScale *
            (fiberRatio * (q : ℝ)) := by
        gcongr
      _ ≤
          12 * metricBadScale *
            (fiberRatio *
              (2 * heavyLogLoss * (pairLower : ℝ))) := by
        gcongr
      _ =
          (24 * heavyLogLoss * metricBadScale * fiberRatio) *
            (pairLower : ℝ) := by ring
      _ ≤ 1 * (pairLower : ℝ) := by
        gcongr
      _ ≤ (selectedCard : ℝ) := by
        simpa using hselectedReal
  · calc
      6 * tangencyBadScale * (tangencyFiberCard : ℝ) ≤
          6 * tangencyBadScale * (2 * (q : ℝ)) := by
        gcongr
      _ ≤
          6 * tangencyBadScale *
            (2 * (2 * heavyLogLoss * (pairLower : ℝ))) := by
        gcongr
      _ =
          (24 * heavyLogLoss * tangencyBadScale) *
            (pairLower : ℝ) := by ring
      _ ≤ 1 * (pairLower : ℝ) := by
        gcongr
      _ ≤ (selectedCard : ℝ) := by
        simpa using hselectedReal

end Kakeya.Cinematic
