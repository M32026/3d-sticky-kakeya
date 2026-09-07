import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantTerminalPaperOrderProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63CrossDegreeAbsorption

/-! # Family-independent scalar schedules for the direct-rich endpoint -/

noncomputable section

namespace Kakeya.Assouad

/-- Pay the ten-power rich terminal regularity by increasing the fixed sticky
refinement exponent from `61` to `72`. -/
structure PureWZ2RichEndpointExactCoreAbsorption where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_exp_neg_one : delta₀ ≤ Real.exp (-1)
  absorb : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    ∀ {regularity : ℕ},
      (regularity : ENNReal) ≤
          Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 →
        (regularity : ENNReal) *
            wz2PaperPureRefinementFraction delta 72 ≤
          wz2PaperPureRefinementFraction delta 61

/-- Family-independent scalar threshold for the indexed-mass receipt of the
same concrete paper-order residue. -/
structure PureWZ2RichEndpointQuantitativeMassAbsorption
    (inputLoss localMassLoss densityLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorb : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    pureWZ2TerminalPairSourceMassLogCost delta *
        Kakeya.realRpowENN delta densityLoss ≤
      Kakeya.realRpowENN delta localMassLoss *
        wz2PaperPureRefinementFraction delta 72 *
        Kakeya.realRpowENN delta inputLoss

namespace PureWZ2RichEndpointQuantitativeMassAbsorption

theorem absorb_actual_cost
    {inputLoss localMassLoss densityLoss : ℝ}
    (absorption : PureWZ2RichEndpointQuantitativeMassAbsorption
      inputLoss localMassLoss densityLoss)
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ absorption.delta₀)
    {sourceMassCost : ENNReal}
    (hcost : 32 * sourceMassCost ≤
      pureWZ2TerminalPairSourceMassLogCost delta) :
    32 * sourceMassCost * Kakeya.realRpowENN delta densityLoss ≤
      Kakeya.realRpowENN delta localMassLoss *
        wz2PaperPureRefinementFraction delta 72 *
        Kakeya.realRpowENN delta inputLoss := by
  exact (mul_le_mul_right' hcost
    (Kakeya.realRpowENN delta densityLoss)).trans
      (absorption.absorb hdelta hdeltaSmall)

end PureWZ2RichEndpointQuantitativeMassAbsorption

namespace PureWZ2RichEndpointExactCoreAbsorption

theorem fraction_le_sixty_one
    (absorption : PureWZ2RichEndpointExactCoreAbsorption)
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ absorption.delta₀) :
    wz2PaperPureRefinementFraction delta 72 ≤
      wz2PaperPureRefinementFraction delta 61 := by
  have hlogOne : 1 ≤ Real.log (1 / delta) := by
    apply (Real.le_log_iff_exp_le (one_div_pos.mpr hdelta)).2
    apply (le_div_iff₀ hdelta).2
    exact (mul_le_mul_of_nonneg_left
      (hdeltaSmall.trans absorption.delta₀_le_exp_neg_one)
      (Real.exp_pos 1).le).trans_eq <| by
        rw [← Real.exp_add]
        norm_num
  unfold wz2PaperPureRefinementFraction
  apply pow_le_pow_of_le_one (by positivity)
    (ENNReal.inv_le_one.mpr <| by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_mono hlogOne)
    (by omega)

end PureWZ2RichEndpointExactCoreAbsorption

theorem pureWZ2_richEndpointExactCore_absorption :
    Nonempty PureWZ2RichEndpointExactCoreAbsorption := by
  let coefficient : ℝ := 4 ^ (10 : ℕ)
  let delta₀ := Real.exp (-coefficient)
  have hcoefficientOne : 1 ≤ coefficient := by
    dsimp only [coefficient]
    norm_num
  exact ⟨{
    delta₀ := delta₀
    delta₀_pos := Real.exp_pos _
    delta₀_le_exp_neg_one := by
      dsimp only [delta₀]
      exact Real.exp_le_exp.mpr (by linarith)
    absorb := by
      intro delta hdelta hdeltaSmall regularity hregularity
      have hdeltaOne : delta ≤ 1 := hdeltaSmall.trans <| by
        dsimp only [delta₀]
        exact (Real.exp_lt_one_iff.mpr <| by
          dsimp only [coefficient]
          norm_num).le
      have hlogCoefficient : coefficient ≤ Real.log (1 / delta) := by
        apply (Real.le_log_iff_exp_le (one_div_pos.mpr hdelta)).2
        apply (le_div_iff₀ hdelta).2
        exact (mul_le_mul_of_nonneg_left hdeltaSmall
          (Real.exp_pos coefficient).le).trans_eq <| by
            dsimp only [delta₀]
            rw [← Real.exp_add]
            simp
      let logTerm := ENNReal.ofReal (Real.log (1 / delta))
      have hlogTermOne : (1 : ENNReal) ≤ logTerm := by
        dsimp only [logTerm]
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_mono (hcoefficientOne.trans hlogCoefficient)
      let L : ENNReal := ENNReal.ofReal (1 + Real.log delta⁻¹)
      have hlogarithmic :
          Prop62PaperAudit.V4.logarithmicLoss delta ≤ 2 * L := by
        simpa only [Prop62PaperAudit.V4.logarithmicLoss, L] using
          PureWZ2.proposition63_logarithmicLoss_le_two_logEnvelope
            hdelta hdeltaOne
      have hL : L ≤ 2 * logTerm := by
        dsimp only [L, logTerm]
        rw [show delta⁻¹ = 1 / delta by simp]
        have hlogOne : 1 ≤ Real.log (1 / delta) :=
          hcoefficientOne.trans hlogCoefficient
        calc
          ENNReal.ofReal (1 + Real.log (1 / delta)) ≤
              ENNReal.ofReal (2 * Real.log (1 / delta)) := by
            apply ENNReal.ofReal_mono
            linarith
          _ = 2 * ENNReal.ofReal (Real.log (1 / delta)) := by
            rw [ENNReal.ofReal_mul (by norm_num)]
            norm_num
      have hlogarithmicTerm :
          Prop62PaperAudit.V4.logarithmicLoss delta ≤ 4 * logTerm :=
        hlogarithmic.trans <| by
          calc
            2 * L ≤ 2 * (2 * logTerm) := mul_le_mul_left' hL 2
            _ = 4 * logTerm := by ring
      have hregularityLog : (regularity : ENNReal) ≤ logTerm ^ 11 := by
        calc
          (regularity : ENNReal) ≤
              (Prop62PaperAudit.V4.logarithmicLoss delta) ^ 10 := hregularity
          _ ≤ (4 * logTerm) ^ 10 := pow_le_pow_left' hlogarithmicTerm 10
          _ = (4 : ENNReal) ^ 10 * logTerm ^ 10 := by rw [mul_pow]
          _ ≤ logTerm * logTerm ^ 10 := by
            gcongr
            calc
              (4 : ENNReal) ^ 10 = ENNReal.ofReal ((4 : ℝ) ^ 10) := by
                rw [ENNReal.ofReal_pow (by norm_num)]
                norm_num
              _ ≤ logTerm := ENNReal.ofReal_mono hlogCoefficient
          _ = logTerm ^ 11 := by
            rw [show 11 = 1 + 10 by norm_num, pow_add]
            simp
      unfold wz2PaperPureRefinementFraction
      change (regularity : ENNReal) * logTerm⁻¹ ^ 72 ≤ logTerm⁻¹ ^ 61
      calc
        (regularity : ENNReal) * logTerm⁻¹ ^ 72 ≤
            logTerm ^ 11 * logTerm⁻¹ ^ 72 := by gcongr
        _ = logTerm⁻¹ ^ 61 := by
          rw [show 72 = 11 + 61 by norm_num, pow_add]
          calc
            logTerm ^ 11 * (logTerm⁻¹ ^ 11 * logTerm⁻¹ ^ 61) =
                (logTerm ^ 11 * logTerm⁻¹ ^ 11) * logTerm⁻¹ ^ 61 := by ring
            _ = logTerm⁻¹ ^ 61 := by
              rw [← ENNReal.inv_pow, ENNReal.mul_inv_cancel
                (pow_ne_zero _ <| ne_of_gt <| zero_lt_one.trans_le hlogTermOne)
                (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
              simp }⟩

theorem pureWZ2_richEndpointQuantitativeMass_absorption
    (inputLoss localMassLoss densityLoss : ℝ)
    (hgap : inputLoss + localMassLoss < densityLoss) :
    Nonempty (PureWZ2RichEndpointQuantitativeMassAbsorption
      inputLoss localMassLoss densityLoss) := by
  let gap := densityLoss - (inputLoss + localMassLoss)
  have hgapPos : 0 < gap := by dsimp only [gap]; linarith
  let coefficient : ENNReal :=
    (1024 : ENNReal) * ENNReal.ofReal wz2PaperBoundaryLogCoefficient
  have hcoefficientTop : coefficient ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  rcases exists_delta_C_pow_log_absorbed_ennreal coefficient
      hcoefficientTop 1 (by norm_num) hgapPos
      (show 0 < (73 : ℕ) by norm_num) with
    ⟨logDelta₀, hlogDelta₀, hlogDelta₀One, habsorb⟩
  let delta₀ := min logDelta₀ (Real.exp (-1))
  exact ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min hlogDelta₀ (Real.exp_pos _)
    delta₀_le_one := (min_le_left _ _).trans hlogDelta₀One
    absorb := by
      intro delta hdelta hdeltaSmall
      let logTerm : ENNReal := ENNReal.ofReal (Real.log (1 / delta))
      let L : ENNReal := ENNReal.ofReal (1 + Real.log delta⁻¹)
      have hdeltaLog : delta ≤ logDelta₀ := hdeltaSmall.trans (min_le_left _ _)
      have hdeltaOne : delta ≤ 1 := hdeltaLog.trans hlogDelta₀One
      have hlogNonnegative : 0 ≤ Real.log delta⁻¹ :=
        Real.log_nonneg ((one_le_inv₀ hdelta).mpr hdeltaOne)
      have hlogTermL : logTerm ≤ L := by
        dsimp only [logTerm, L]
        rw [show 1 / delta = delta⁻¹ by simp]
        exact ENNReal.ofReal_mono (by linarith)
      have hcostPower :
          pureWZ2TerminalPairSourceMassLogCost delta * logTerm ^ 72 ≤
            Kakeya.realRpowENN delta (-gap) := by
        calc
          pureWZ2TerminalPairSourceMassLogCost delta * logTerm ^ 72 =
              coefficient * L * logTerm ^ 72 := by
            simp [pureWZ2TerminalPairSourceMassLogCost, coefficient, L]
          _ ≤ coefficient * L * L ^ 72 := by gcongr
          _ = coefficient * L ^ 73 := by
            rw [show 73 = 1 + 72 by norm_num, pow_add]
            simp only [pow_one]
            rw [mul_assoc]
          _ ≤ Kakeya.realRpowENN delta (-gap) := by
            simpa only [L, one_mul] using habsorb delta hdelta hdeltaLog
      have hlogTermPos : 0 < logTerm := by
        dsimp only [logTerm]
        apply ENNReal.ofReal_pos.mpr
        apply Real.log_pos
        exact one_lt_one_div hdelta <|
          hdeltaSmall.trans_lt <|
            (min_le_right _ _).trans_lt
              (Real.exp_lt_one_iff.mpr (by norm_num))
      have hlogTermTop : logTerm ≠ ⊤ := ENNReal.ofReal_ne_top
      have hcostLe : pureWZ2TerminalPairSourceMassLogCost delta ≤
          logTerm⁻¹ ^ 72 * Kakeya.realRpowENN delta (-gap) := by
        calc
          pureWZ2TerminalPairSourceMassLogCost delta =
              logTerm⁻¹ ^ 72 *
                (pureWZ2TerminalPairSourceMassLogCost delta * logTerm ^ 72) := by
            rw [show logTerm⁻¹ ^ 72 *
                (pureWZ2TerminalPairSourceMassLogCost delta * logTerm ^ 72) =
              pureWZ2TerminalPairSourceMassLogCost delta *
                (logTerm⁻¹ ^ 72 * logTerm ^ 72) by ring]
            rw [← ENNReal.inv_pow, ENNReal.inv_mul_cancel
              (pow_ne_zero _ hlogTermPos.ne')
              (ENNReal.pow_ne_top hlogTermTop)]
            simp
          _ ≤ logTerm⁻¹ ^ 72 * Kakeya.realRpowENN delta (-gap) := by gcongr
      unfold wz2PaperPureRefinementFraction
      change pureWZ2TerminalPairSourceMassLogCost delta *
          Kakeya.realRpowENN delta densityLoss ≤
        Kakeya.realRpowENN delta localMassLoss * logTerm⁻¹ ^ 72 *
          Kakeya.realRpowENN delta inputLoss
      calc
        pureWZ2TerminalPairSourceMassLogCost delta *
            Kakeya.realRpowENN delta densityLoss ≤
          (logTerm⁻¹ ^ 72 * Kakeya.realRpowENN delta (-gap)) *
            Kakeya.realRpowENN delta densityLoss := by gcongr
        _ = Kakeya.realRpowENN delta localMassLoss * logTerm⁻¹ ^ 72 *
            Kakeya.realRpowENN delta inputLoss := by
          calc
            logTerm⁻¹ ^ 72 * Kakeya.realRpowENN delta (-gap) *
                Kakeya.realRpowENN delta densityLoss =
              logTerm⁻¹ ^ 72 *
                (Kakeya.realRpowENN delta (-gap) *
                  Kakeya.realRpowENN delta densityLoss) := by ring
            _ = logTerm⁻¹ ^ 72 *
                Kakeya.realRpowENN delta ((-gap) + densityLoss) := by
              rw [realRpowENN_add hdelta]
            _ = logTerm⁻¹ ^ 72 *
                Kakeya.realRpowENN delta (inputLoss + localMassLoss) := by
              congr 1
              dsimp only [gap]
              ring
            _ = logTerm⁻¹ ^ 72 *
                (Kakeya.realRpowENN delta inputLoss *
                  Kakeya.realRpowENN delta localMassLoss) := by
              rw [realRpowENN_add hdelta]
            _ = _ := by ring }⟩

end Kakeya.Assouad

end
