import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentSelectionAbsorptionStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLinePackingCardinality

/-! # Absorb the fixed one-parent selection losses -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_prop_sticky_prepared_one_parent_selection_absorption :
    WZ2PropStickyPreparedOneParentSelectionAbsorptionStatement := by
  intro sourceLoss hsourceLoss
  let depth := wz2PaperPreparedOneParentDepth sourceLoss
  let coefficient : ℝ :=
    max (packingConstant10000 : ℝ) ((2 : ℝ) ^ depth)
  let logCoefficient : ℝ := 5 / Real.log 2
  let additiveConstant : ℝ :=
    5 * Real.log 163 / Real.log 2 + 1
  let logThreshold : ℝ :=
    Real.exp
      (-(coefficient * (logCoefficient + additiveConstant)))
  have hcoefficientPos : 0 < coefficient := by
    dsimp only [coefficient]
    exact lt_of_lt_of_le
      (by norm_num [packingConstant10000])
      (le_max_left _ _)
  have hlogCoefficientPos : 0 < logCoefficient := by
    dsimp only [logCoefficient]
    positivity
  have hadditivePos : 0 < additiveConstant := by
    dsimp only [additiveConstant]
    positivity
  have hlogThreshold : 0 < logThreshold := by
    dsimp only [logThreshold]
    positivity
  have hlogThresholdOne : logThreshold ≤ 1 := by
    dsimp only [logThreshold]
    rw [Real.exp_le_one_iff]
    have hnonnegative :
        0 ≤ coefficient * (logCoefficient + additiveConstant) := by
      positivity
    linarith
  let delta₀ : ℝ := min (1 / 10000) logThreshold
  have hdelta₀ : 0 < delta₀ := by
    exact lt_min (by norm_num) hlogThreshold
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_right _ _).trans hlogThresholdOne
  refine
    ⟨{
      delta₀ := delta₀
      delta₀_pos := hdelta₀
      delta₀_le_one := hdelta₀One
      absorb := ?_
    }⟩
  intro delta stableLoss hdelta hdeltaBound source shading caller
    preparationExponent prepared parent
  have hdeltaSmall : delta ≤ 1 / 10000 :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaLog : delta ≤ logThreshold :=
    hdeltaBound.trans (min_le_right _ _)
  have hdeltaOne : delta ≤ 1 := hdeltaBound.trans hdelta₀One
  have hdeltaStrict : delta < 1 := by linarith
  have hlogPos : 0 < Real.log (1 / delta) := by
    apply Real.log_pos
    exact one_lt_one_div hdelta hdeltaStrict
  let logTerm : ENNReal :=
    ENNReal.ofReal (Real.log (1 / delta))
  have hlogZero : logTerm ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hlogPos).ne'
  have hlogTop : logTerm ≠ ⊤ := by
    simp [logTerm]
  have hlogLower :
      coefficient * (logCoefficient + additiveConstant) ≤
        Real.log (1 / delta) := by
    have hreciprocal :
        Real.exp
            (coefficient *
              (logCoefficient + additiveConstant)) ≤
          1 / delta := by
      have hinv :=
        one_div_le_one_div_of_le hdelta hdeltaLog
      simpa [logThreshold, Real.exp_neg] using hinv
    have hlog :=
      Real.log_le_log
        (Real.exp_pos
          (coefficient *
            (logCoefficient + additiveConstant)))
        hreciprocal
    simpa using hlog
  have hcoefficientOne : 1 ≤ coefficient := by
    exact
      (show (1 : ℝ) ≤ packingConstant10000 by
        norm_num [packingConstant10000]).trans
        (le_max_left _ _)
  have hadditiveOne : 1 ≤ additiveConstant := by
    dsimp only [additiveConstant]
    have hnonnegative :
        0 ≤ 5 * Real.log 163 / Real.log 2 := by
      positivity
    linarith
  have hsumOne :
      1 ≤ logCoefficient + additiveConstant := by
    linarith [hlogCoefficientPos]
  have hlogOneReal : 1 ≤ Real.log (1 / delta) := by
    have hproduct :
        (1 : ℝ) * 1 ≤
          coefficient * (logCoefficient + additiveConstant) :=
      mul_le_mul hcoefficientOne hsumOne
        (by norm_num) (by linarith)
    simpa using hproduct.trans hlogLower
  have hlogOne : (1 : ENNReal) ≤ logTerm := by
    dsimp only [logTerm]
    simpa using ENNReal.ofReal_mono hlogOneReal
  have hdepth :
      wz2PaperPreparedOneParentFineScaleCount prepared parent ≤ depth := by
    dsimp only [wz2PaperPreparedOneParentFineScaleCount, depth,
      wz2PaperPreparedOneParentDepth]
    calc
      prepared.strictScaleCount - prepared.callerLevel.val ≤
          prepared.strictScaleCount := Nat.sub_le _ _
      _ ≤ prepared.levelCount + 1 := prepared.strictScaleCount_le
      _ = Nat.ceil (1 / sourceLoss) + 2 := by
        rw [prepared.levelCount_eq]
  have hline :
      WZ1PaperIsLineClass
        (wz2PaperPreparedOneParentFiber prepared parent).family :=
    prepared.cwa_nearby.2.1.subfamily
      (wz2PaperPreparedOneParentFiber prepared parent)
  have hdistinct :
      WZ1PaperIsEssentiallyDistinct
        (wz2PaperPreparedOneParentFiber prepared parent).family :=
    prepared.cwa_nearby.2.2.1.subfamily
      (wz2PaperPreparedOneParentFiber prepared parent)
  have hnonempty :
      0 < (wz2PaperPreparedOneParentFiber prepared parent).family.card := by
    change
      0 <
        (wz2PaperFullFiberIndices
          prepared.refinement.selected.family
          prepared.callerStrict.coarse parent).card
    exact Finset.card_pos.mpr
      (prepared.callerStrict.cover.fullFiber_nonempty parent)
  have hband :=
    paper_log_card_bound
      hdistinct hline hdelta hdeltaOne hnonempty
  have hcoefficientPacking :
      (packingConstant10000 : ℝ) ≤ coefficient :=
    le_max_left _ _
  have hcoefficientBranch :
      ((2 : ℝ) ^ depth) ≤ coefficient :=
    le_max_right _ _
  have hquadratic :
      coefficient *
          (logCoefficient * Real.log (1 / delta) +
            additiveConstant) ≤
        (Real.log (1 / delta)) ^ 2 := by
    calc
      coefficient *
            (logCoefficient * Real.log (1 / delta) +
              additiveConstant) =
          coefficient * logCoefficient * Real.log (1 / delta) +
            coefficient * additiveConstant := by ring
      _ ≤
          coefficient * logCoefficient * Real.log (1 / delta) +
            coefficient * additiveConstant *
              Real.log (1 / delta) := by
        have hnonnegative :
            0 ≤ coefficient * additiveConstant := by positivity
        nlinarith
      _ =
          coefficient * (logCoefficient + additiveConstant) *
            Real.log (1 / delta) := by ring
      _ ≤
          Real.log (1 / delta) * Real.log (1 / delta) := by
        gcongr
      _ = (Real.log (1 / delta)) ^ 2 := by ring
  have hpackingReal :
      (packingConstant10000 : ℝ) ≤
        (Real.log (1 / delta)) ^ 2 := by
    calc
      (packingConstant10000 : ℝ) ≤ coefficient :=
        hcoefficientPacking
      _ ≤ coefficient * 1 := by simp
      _ ≤ coefficient *
          (logCoefficient * Real.log (1 / delta) +
            additiveConstant) := by
        gcongr
        have hmiddle :
            1 ≤
              logCoefficient * Real.log (1 / delta) +
                additiveConstant := by
          have hnonnegative :
              0 ≤ logCoefficient * Real.log (1 / delta) := by
            positivity
          linarith
        exact hmiddle
      _ ≤ (Real.log (1 / delta)) ^ 2 := hquadratic
  have hbranchReal :
      ((2 : ℝ) ^
            (wz2PaperPreparedOneParentFineScaleCount
              prepared parent)) *
          (Nat.log 2
              (wz2PaperPreparedOneParentFiber
                prepared parent).family.card + 1 : ℝ) ≤
        (Real.log (1 / delta)) ^ 2 := by
    have hbranchPower :
        ((2 : ℝ) ^
            (wz2PaperPreparedOneParentFineScaleCount
              prepared parent)) ≤
          (2 : ℝ) ^ depth := by
      exact pow_le_pow_right₀ (by norm_num) hdepth
    calc
      ((2 : ℝ) ^
            (wz2PaperPreparedOneParentFineScaleCount
              prepared parent)) *
          (Nat.log 2
              (wz2PaperPreparedOneParentFiber
                prepared parent).family.card + 1 : ℝ) ≤
        coefficient *
          (Nat.log 2
              (wz2PaperPreparedOneParentFiber
                prepared parent).family.card + 1 : ℝ) := by
          gcongr
          exact hbranchPower.trans hcoefficientBranch
      _ ≤ coefficient *
          (logCoefficient * Real.log (1 / delta) +
            additiveConstant) := by
        gcongr
      _ ≤ (Real.log (1 / delta)) ^ 2 := hquadratic
  have hpackingENN :
      (packingConstant10000 : ENNReal) ≤ logTerm ^ 2 := by
    have hnonnegative : 0 ≤ Real.log (1 / delta) :=
      hlogOneReal.trans' (by norm_num)
    rw [show
      (packingConstant10000 : ENNReal) =
        ENNReal.ofReal (packingConstant10000 : ℝ) by
          simp]
    rw [show
      logTerm ^ 2 =
        ENNReal.ofReal ((Real.log (1 / delta)) ^ 2) by
          dsimp only [logTerm]
          exact (ENNReal.ofReal_pow hnonnegative 2).symm]
    exact ENNReal.ofReal_mono hpackingReal
  have hbranchENN :
      (2 : ENNReal) ^
            (wz2PaperPreparedOneParentFineScaleCount
              prepared parent) *
          (Nat.log 2
              (wz2PaperPreparedOneParentFiber
                prepared parent).family.card + 1 : ENNReal) ≤
        logTerm ^ 2 := by
    have hleft :
        (2 : ENNReal) ^
              (wz2PaperPreparedOneParentFineScaleCount
                prepared parent) *
            (Nat.log 2
                (wz2PaperPreparedOneParentFiber
                  prepared parent).family.card + 1 : ENNReal) =
          ENNReal.ofReal
            (((2 : ℝ) ^
                (wz2PaperPreparedOneParentFineScaleCount
                  prepared parent)) *
              (Nat.log 2
                (wz2PaperPreparedOneParentFiber
                  prepared parent).family.card + 1 : ℝ)) := by
      norm_cast
    have hnonnegative : 0 ≤ Real.log (1 / delta) :=
      hlogOneReal.trans' (by norm_num)
    rw [hleft]
    rw [show
      logTerm ^ 2 =
        ENNReal.ofReal ((Real.log (1 / delta)) ^ 2) by
          dsimp only [logTerm]
          exact (ENNReal.ofReal_pow hnonnegative 2).symm]
    exact ENNReal.ofReal_mono hbranchReal
  have hpacking :
      wz1PaperRefinementFraction delta 2 *
          (packingConstant10000 : ENNReal) ≤ 1 := by
    dsimp only [wz1PaperRefinementFraction]
    calc
      logTerm⁻¹ ^ 2 * (packingConstant10000 : ENNReal) ≤
          logTerm⁻¹ ^ 2 * logTerm ^ 2 := by gcongr
      _ = 1 := by
        rw [← mul_pow, ENNReal.inv_mul_cancel hlogZero hlogTop]
        norm_num
  have hbranch :
      wz1PaperRefinementFraction delta 2 *
          ((2 : ENNReal) ^
              (wz2PaperPreparedOneParentFineScaleCount
                prepared parent) *
            (Nat.log 2
                (wz2PaperPreparedOneParentFiber
                  prepared parent).family.card + 1 : ENNReal)) ≤
        1 := by
    dsimp only [wz1PaperRefinementFraction]
    calc
      logTerm⁻¹ ^ 2 *
            ((2 : ENNReal) ^
                (wz2PaperPreparedOneParentFineScaleCount
                  prepared parent) *
              (Nat.log 2
                  (wz2PaperPreparedOneParentFiber
                    prepared parent).family.card + 1 : ENNReal)) ≤
          logTerm⁻¹ ^ 2 * logTerm ^ 2 := by gcongr
      _ = 1 := by
        rw [← mul_pow, ENNReal.inv_mul_cancel hlogZero hlogTop]
        norm_num
  exact ⟨hdeltaSmall, hpacking, by simpa using hbranch⟩

end Kakeya.Assouad

end
