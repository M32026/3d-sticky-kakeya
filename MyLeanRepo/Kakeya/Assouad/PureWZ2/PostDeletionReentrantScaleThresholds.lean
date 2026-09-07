import MyLeanRepo.Kakeya.Assouad.PureWZ2.PostDeletionUniversalWitnessProducer

/-!
# Source-independent post-deletion scale thresholds

These thresholds use only a ceiling for the normalization loss and the
strictly larger caller loss.  They are therefore selected before the runtime
tube family.  The resulting estimates are exactly the small actual-scale
window, actual-to-caller gap, and one-log deletion bound used by the
post-deletion construction.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2PostDeletionReentrantScaleThresholds
    (internalLossCeiling callerLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  actual_window :
    ∀ {internalLoss delta : ℝ},
      internalLoss ≤ internalLossCeiling →
      0 < delta → delta ≤ delta₀ →
        Real.rpow delta (1 - internalLoss) ≤ 1 / 10000
  actual_to_caller_window :
    ∀ {internalLoss delta : ℝ},
      internalLoss ≤ internalLossCeiling →
      0 < delta → delta ≤ delta₀ →
        2400000 * Real.rpow delta (1 - internalLoss) ≤
          Real.rpow delta (1 - callerLoss)
  deletion_fraction_small :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      wz1PaperRefinementFraction delta 1 ≤ (1 / 2 : ENNReal)

/-- Select all post-deletion scale cutoffs before the runtime family. -/
theorem pureWZ2_postDeletion_reentrant_scale_thresholds
    {internalLossCeiling callerLoss : ℝ}
    (lossGap : internalLossCeiling < callerLoss)
    (callerLossLeHalf : callerLoss ≤ 1 / 2) :
    Nonempty
      (PureWZ2PostDeletionReentrantScaleThresholds
        internalLossCeiling callerLoss) := by
  have ceilingExponentPos : 0 < 1 - internalLossCeiling := by
    linarith
  rcases
      exists_delta_mul_rpow_le_rpow
        10000 (by norm_num)
        (alpha := 1 - internalLossCeiling) (beta := 0)
        ceilingExponentPos
    with
    ⟨actualScale, actualScalePos, actualScaleOne, actualSmall⟩
  rcases
      exists_delta_mul_rpow_le_rpow
        2400000 (by norm_num)
        (alpha := 1 - internalLossCeiling)
        (beta := 1 - callerLoss)
        (by linarith)
    with
    ⟨gapScale, gapScalePos, gapScaleOne, gapSmall⟩
  let delta₀ :=
    min actualScale (min gapScale (Real.exp (-2)))
  have delta₀Pos : 0 < delta₀ := by
    dsimp only [delta₀]
    exact lt_min actualScalePos
      (lt_min gapScalePos (Real.exp_pos _))
  have delta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans actualScaleOne
  refine
    ⟨{
      delta₀ := delta₀
      delta₀_pos := delta₀Pos
      delta₀_le_one := delta₀One
      actual_window := ?_
      actual_to_caller_window := ?_
      deletion_fraction_small := ?_
    }⟩
  · intro internalLoss delta hinternal hdelta hdeltaSmall
    have hdeltaOne : delta ≤ 1 :=
      hdeltaSmall.trans delta₀One
    have exponentMono :
        Real.rpow delta (1 - internalLoss) ≤
          Real.rpow delta (1 - internalLossCeiling) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith)
    have absorbed :=
      actualSmall delta hdelta
        (hdeltaSmall.trans (min_le_left _ _))
    have ceilingSmall :
        Real.rpow delta (1 - internalLossCeiling) ≤ 1 / 10000 := by
      have powerNonnegative :
          0 ≤ Real.rpow delta (1 - internalLossCeiling) :=
        Real.rpow_nonneg hdelta.le _
      norm_num at absorbed ⊢
      nlinarith
    exact exponentMono.trans ceilingSmall
  · intro internalLoss delta hinternal hdelta hdeltaSmall
    have hdeltaOne : delta ≤ 1 :=
      hdeltaSmall.trans delta₀One
    have exponentMono :
        Real.rpow delta (1 - internalLoss) ≤
          Real.rpow delta (1 - internalLossCeiling) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith)
    calc
      2400000 * Real.rpow delta (1 - internalLoss) ≤
          2400000 * Real.rpow delta (1 - internalLossCeiling) := by
        gcongr
      _ ≤ Real.rpow delta (1 - callerLoss) :=
        gapSmall delta hdelta
          (hdeltaSmall.trans <|
            (min_le_right _ _).trans (min_le_left _ _))
  · intro delta hdelta hdeltaSmall
    have hdeltaExp : delta ≤ Real.exp (-2) :=
      hdeltaSmall.trans <|
        (min_le_right _ _).trans (min_le_right _ _)
    have hinverse : Real.exp 2 ≤ delta⁻¹ := by
      have h := (inv_le_inv₀ (Real.exp_pos (-2)) hdelta).mpr hdeltaExp
      simpa [Real.exp_neg] using h
    have hlog : 2 ≤ Real.log delta⁻¹ := by
      rw [← Real.log_exp 2]
      exact Real.log_le_log (Real.exp_pos 2) hinverse
    unfold wz1PaperRefinementFraction
    simp only [pow_one, one_div]
    rw [ENNReal.inv_le_inv]
    have htwo : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by
      norm_num
    rw [htwo]
    simpa [one_div] using ENNReal.ofReal_mono hlog

end Kakeya.Assouad

end
