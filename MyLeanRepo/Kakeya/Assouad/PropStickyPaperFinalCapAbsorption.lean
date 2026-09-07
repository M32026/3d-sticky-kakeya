import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalComponentScale
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26DeltaBudget
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements

/-!
# Fixed-loss absorption for the final normalized caps

The internal cap loss is chosen strictly smaller than the component loss.
At sufficiently small scales, the gap absorbs the dyadic factor two, the
factor eight from final parent retention, and one fixed polylogarithmic
factor.
-/

noncomputable section

namespace Kakeya.Assouad

theorem wz1PaperRefinementFraction_ne_zero
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (exponent : ℕ) :
    wz1PaperRefinementFraction delta exponent ≠ 0 := by
  let logTerm : ENNReal :=
    ENNReal.ofReal (Real.log (1 / delta))
  have hlog : 0 < Real.log (1 / delta) :=
    Real.log_pos (one_lt_one_div hdelta hdeltaOne)
  have hLogTop : logTerm ≠ ⊤ := by
    simp [logTerm]
  change logTerm⁻¹ ^ exponent ≠ 0
  exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr hLogTop)

theorem wz1PaperRefinementFraction_ne_top
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (exponent : ℕ) :
    wz1PaperRefinementFraction delta exponent ≠ ⊤ := by
  let logTerm : ENNReal :=
    ENNReal.ofReal (Real.log (1 / delta))
  have hlog : 0 < Real.log (1 / delta) :=
    Real.log_pos (one_lt_one_div hdelta hdeltaOne)
  have hLogZero : logTerm ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hlog).ne'
  change logTerm⁻¹ ^ exponent ≠ ⊤
  exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hLogZero)

structure WZ2PaperFinalCapAbsorptionData
    (capLoss componentLoss : ℝ)
    (globalBalancingExponent : ℕ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_lt_one : delta₀ < 1
  absorb :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      ∀ rho : ℝ, 0 < rho →
        Real.rpow delta (1 - componentLoss) ≤ rho →
        rho ≤ Real.rpow delta componentLoss →
        2 * Kakeya.realRpowENN (delta / rho)
              (2 - capLoss) ≤
            Kakeya.realRpowENN (delta / rho)
              (2 - componentLoss) ∧
          8 * Kakeya.realRpowENN rho (2 - capLoss) ≤
            wz1PaperRefinementFraction delta
                globalBalancingExponent *
              Kakeya.realRpowENN rho (2 - componentLoss)

theorem wz2_paper_final_cap_absorption
    (capLoss componentLoss : ℝ)
    (globalBalancingExponent : ℕ)
    (hCapComponent : capLoss < componentLoss)
    (hComponentPos : 0 < componentLoss) :
    Nonempty
      (WZ2PaperFinalCapAbsorptionData
        capLoss componentLoss globalBalancingExponent) := by
  let gap := componentLoss - capLoss
  have hGap : 0 < gap := by
    dsimp only [gap]
    linarith
  let absorptionGap := componentLoss * gap
  have hAbsorptionGap : 0 < absorptionGap := by
    dsimp only [absorptionGap]
    positivity
  rcases
      exists_delta_rpow_le_single
        absorptionGap (1 / 2)
        hAbsorptionGap (by norm_num) (by norm_num)
    with ⟨fineScale, hFineScale, hFineScaleOne, hFineAbsorb⟩
  let coefficient : ENNReal := 8
  have hCoefficientTop : coefficient ≠ ⊤ := by
    norm_num [coefficient]
  rcases
      exists_delta_log_absorbed_ennreal
        coefficient hCoefficientTop hAbsorptionGap
        (show 0 < globalBalancingExponent + 1 by omega)
    with ⟨coarseScale, hCoarseScale, hCoarseScaleOne,
      hCoarseAbsorb⟩
  let delta₀ := min fineScale (min coarseScale (Real.exp (-1)))
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    exact lt_min hFineScale <|
      lt_min hCoarseScale (Real.exp_pos _)
  have hdelta₀One : delta₀ < 1 := by
    exact (min_le_right _ _).trans_lt <|
      (min_le_right _ _).trans_lt <|
        Real.exp_lt_one_iff.mpr (by norm_num)
  refine
    ⟨{
      delta₀ := delta₀
      delta₀_pos := hdelta₀
      delta₀_lt_one := hdelta₀One
      absorb := ?_
    }⟩
  intro delta hdelta hdeltaBound rho hrho hlower hupper
  have hFineScale' : delta ≤ fineScale :=
    hdeltaBound.trans (min_le_left _ _)
  have hCoarseScale' : delta ≤ coarseScale :=
    hdeltaBound.trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaOne : delta < 1 :=
    hdeltaBound.trans_lt hdelta₀One
  have hratioPos : 0 < delta / rho := div_pos hdelta hrho
  have hratioUpper :
      delta / rho ≤ Real.rpow delta componentLoss := by
    rw [div_le_iff₀ hrho]
    have hsplit :
        delta =
          Real.rpow delta (1 - componentLoss) *
            Real.rpow delta componentLoss := by
      calc
        delta = Real.rpow delta 1 := by simp
        _ =
            Real.rpow delta
              ((1 - componentLoss) + componentLoss) := by
          congr 1
          ring
        _ =
            Real.rpow delta (1 - componentLoss) *
              Real.rpow delta componentLoss :=
          Real.rpow_add hdelta _ _
    calc
      delta =
          Real.rpow delta (1 - componentLoss) *
            Real.rpow delta componentLoss := hsplit
      _ ≤ rho * Real.rpow delta componentLoss := by
        exact mul_le_mul_of_nonneg_right hlower
          (Real.rpow_nonneg hdelta.le componentLoss)
      _ = Real.rpow delta componentLoss * rho := by ring
  have hFinePower :
      Kakeya.realRpowENN (delta / rho) gap ≤
        (1 / 2 : ENNReal) := by
    have hReal :
        Real.rpow (delta / rho) gap ≤ 1 / 2 := by
      calc
      Real.rpow (delta / rho) gap ≤
          Real.rpow (Real.rpow delta componentLoss) gap :=
        Real.rpow_le_rpow hratioPos.le hratioUpper hGap.le
      _ =
          Real.rpow delta absorptionGap := by
        dsimp only [absorptionGap]
        exact (Real.rpow_mul hdelta.le _ _).symm
      _ ≤ 1 / 2 :=
        hFineAbsorb delta hdelta hFineScale'
    simpa [Kakeya.realRpowENN] using
      ENNReal.ofReal_mono hReal
  have hFine :
      2 * Kakeya.realRpowENN (delta / rho) (2 - capLoss) ≤
        Kakeya.realRpowENN (delta / rho) (2 - componentLoss) := by
    have hSplit :
        Kakeya.realRpowENN (delta / rho) (2 - capLoss) =
          Kakeya.realRpowENN (delta / rho) (2 - componentLoss) *
            Kakeya.realRpowENN (delta / rho) gap := by
      rw [← realRpowENN_add hratioPos]
      congr 1
      dsimp only [gap]
      ring
    rw [hSplit]
    calc
      2 *
            (Kakeya.realRpowENN (delta / rho)
                (2 - componentLoss) *
              Kakeya.realRpowENN (delta / rho) gap) =
          Kakeya.realRpowENN (delta / rho)
              (2 - componentLoss) *
            (2 * Kakeya.realRpowENN (delta / rho) gap) := by
        ring
      _ ≤
          Kakeya.realRpowENN (delta / rho)
              (2 - componentLoss) *
            (2 * (1 / 2 : ENNReal)) := by
        gcongr
      _ =
          Kakeya.realRpowENN (delta / rho)
              (2 - componentLoss) := by
        have hCancel :
            (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
          simpa [one_div] using
            ENNReal.mul_inv_cancel
              (show (2 : ENNReal) ≠ 0 by norm_num)
              (show (2 : ENNReal) ≠ ⊤ by norm_num)
        rw [hCancel, mul_one]
  let logTerm : ENNReal :=
    ENNReal.ofReal (Real.log (1 / delta))
  let enlargedLog : ENNReal :=
    ENNReal.ofReal (1 + Real.log delta⁻¹)
  have hInvEq : delta⁻¹ = 1 / delta := by
    field_simp [hdelta.ne']
  have hLogRealPos : 0 < Real.log (1 / delta) :=
    Real.log_pos (one_lt_one_div hdelta hdeltaOne)
  have hLogZero : logTerm ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hLogRealPos).ne'
  have hLogTop : logTerm ≠ ⊤ := by simp [logTerm]
  have hLogLe : logTerm ≤ enlargedLog := by
    dsimp only [logTerm, enlargedLog]
    apply ENNReal.ofReal_mono
    rw [hInvEq]
    linarith
  have hEnlargedOne : (1 : ENNReal) ≤ enlargedLog := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_mono
    rw [hInvEq]
    linarith
  have hLogPow :
      logTerm ^ globalBalancingExponent ≤
        enlargedLog ^ (globalBalancingExponent + 1) := by
    calc
      logTerm ^ globalBalancingExponent ≤
          enlargedLog ^ globalBalancingExponent := by gcongr
      _ ≤ enlargedLog ^ (globalBalancingExponent + 1) := by
        rw [pow_succ]
        simpa using
          mul_le_mul_left' hEnlargedOne
            (enlargedLog ^ globalBalancingExponent)
  have hCoarseLog :
      coefficient * logTerm ^ globalBalancingExponent ≤
        Kakeya.realRpowENN delta (-absorptionGap) := by
    calc
      coefficient * logTerm ^ globalBalancingExponent ≤
          coefficient *
            enlargedLog ^ (globalBalancingExponent + 1) := by
        gcongr
      _ ≤ Kakeya.realRpowENN delta (-absorptionGap) :=
        hCoarseAbsorb delta hdelta hCoarseScale'
  have hFractionEq :
      wz1PaperRefinementFraction delta globalBalancingExponent =
        (logTerm ^ globalBalancingExponent)⁻¹ := by
    change logTerm⁻¹ ^ globalBalancingExponent =
      (logTerm ^ globalBalancingExponent)⁻¹
    exact ENNReal.inv_pow.symm
  have hCoefficient :
      coefficient ≤
        wz1PaperRefinementFraction delta globalBalancingExponent *
          Kakeya.realRpowENN delta (-absorptionGap) := by
    have hLogPowZero :
        logTerm ^ globalBalancingExponent ≠ 0 :=
      pow_ne_zero _ hLogZero
    have hLogPowTop :
        logTerm ^ globalBalancingExponent ≠ ⊤ :=
      ENNReal.pow_ne_top hLogTop
    have hScaled :
        coefficient * logTerm ^ globalBalancingExponent *
              (logTerm ^ globalBalancingExponent)⁻¹ ≤
          Kakeya.realRpowENN delta (-absorptionGap) *
            (logTerm ^ globalBalancingExponent)⁻¹ := by
      gcongr
    rw [mul_assoc,
      ENNReal.mul_inv_cancel hLogPowZero hLogPowTop,
      mul_one] at hScaled
    simpa [hFractionEq, mul_comm] using hScaled
  have hWindow :
      Kakeya.realRpowENN delta (-absorptionGap) *
          Kakeya.realRpowENN rho gap ≤ 1 := by
    have hRhoPower :
        Kakeya.realRpowENN rho gap ≤
          Kakeya.realRpowENN delta absorptionGap := by
      apply ENNReal.ofReal_mono
      calc
        Real.rpow rho gap ≤
            Real.rpow (Real.rpow delta componentLoss) gap :=
          Real.rpow_le_rpow hrho.le hupper hGap.le
        _ = Real.rpow delta absorptionGap := by
          dsimp only [absorptionGap]
          exact (Real.rpow_mul hdelta.le _ _).symm
    calc
      Kakeya.realRpowENN delta (-absorptionGap) *
            Kakeya.realRpowENN rho gap ≤
          Kakeya.realRpowENN delta (-absorptionGap) *
            Kakeya.realRpowENN delta absorptionGap := by
        gcongr
      _ = 1 := by
        rw [← realRpowENN_add hdelta]
        simp [Kakeya.realRpowENN]
  have hCoarse :
      8 * Kakeya.realRpowENN rho (2 - capLoss) ≤
        wz1PaperRefinementFraction delta globalBalancingExponent *
          Kakeya.realRpowENN rho (2 - componentLoss) := by
    have hSplit :
        Kakeya.realRpowENN rho (2 - capLoss) =
          Kakeya.realRpowENN rho (2 - componentLoss) *
            Kakeya.realRpowENN rho gap := by
      rw [← realRpowENN_add hrho]
      congr 1
      dsimp only [gap]
      ring
    rw [hSplit]
    have hInner :
        (wz1PaperRefinementFraction delta
              globalBalancingExponent *
            Kakeya.realRpowENN delta (-absorptionGap)) *
            Kakeya.realRpowENN rho gap ≤
          wz1PaperRefinementFraction delta
            globalBalancingExponent * 1 := by
      calc
        (wz1PaperRefinementFraction delta
              globalBalancingExponent *
            Kakeya.realRpowENN delta (-absorptionGap)) *
            Kakeya.realRpowENN rho gap =
          wz1PaperRefinementFraction delta
              globalBalancingExponent *
            (Kakeya.realRpowENN delta (-absorptionGap) *
              Kakeya.realRpowENN rho gap) := by ring
        _ ≤
          wz1PaperRefinementFraction delta
              globalBalancingExponent * 1 := by
            gcongr
    calc
      8 *
            (Kakeya.realRpowENN rho (2 - componentLoss) *
              Kakeya.realRpowENN rho gap) =
          Kakeya.realRpowENN rho (2 - componentLoss) *
            (coefficient * Kakeya.realRpowENN rho gap) := by
        simp [coefficient]
        ring
      _ ≤
          Kakeya.realRpowENN rho (2 - componentLoss) *
            ((wz1PaperRefinementFraction delta
                globalBalancingExponent *
              Kakeya.realRpowENN delta (-absorptionGap)) *
              Kakeya.realRpowENN rho gap) := by
        gcongr
      _ ≤
          Kakeya.realRpowENN rho (2 - componentLoss) *
            (wz1PaperRefinementFraction delta
              globalBalancingExponent * 1) := by
        exact mul_le_mul_left' hInner _
      _ =
          wz1PaperRefinementFraction delta
              globalBalancingExponent *
            Kakeya.realRpowENN rho (2 - componentLoss) := by
        ring
  exact ⟨hFine, hCoarse⟩

end Kakeya.Assouad

end
