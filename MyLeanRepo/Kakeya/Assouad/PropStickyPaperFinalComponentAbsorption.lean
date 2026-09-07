import MyLeanRepo.Kakeya.Assouad.PropStickyPaperStructuralParentCardinalityUniform
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Uniform numerical absorption for the final component floors

After the geometric and cardinality reductions, both final component floors
have the same scalar loss.  The positive exponent gap below absorbs the fixed
one-parent loss and any fixed polylogarithmic refinement exponent.
-/

noncomputable section

namespace Kakeya.Assouad

def wz2PaperFinalComponentGap
    (sourceLoss structuralLoss capLoss componentFloorLoss outputLoss : ℝ) :
    ℝ :=
  outputLoss * (componentFloorLoss + capLoss) -
    capLoss - 3 * sourceLoss - structuralLoss

structure WZ2PaperFinalComponentAbsorptionData
    (sourceLoss structuralLoss capLoss componentFloorLoss outputLoss : ℝ)
    (totalExponent : ℕ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorb :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      (2 *
            (Kakeya.realRpowENN delta (-structuralLoss) *
              (wz2PaperPreparedOneParentFiniteLoss sourceLoss *
                (55296 * Kakeya.deltaTubeVolume 1)))) *
          Kakeya.realRpowENN delta
            (2 - sourceLoss - capLoss +
              outputLoss * (componentFloorLoss + capLoss)) ≤
        (1 / 2 : ENNReal) *
          wz1PaperRefinementFraction delta totalExponent *
          Kakeya.realRpowENN delta (2 + 2 * sourceLoss)

theorem wz2_paper_final_component_absorption
    (sourceLoss structuralLoss capLoss componentFloorLoss outputLoss : ℝ)
    (totalExponent : ℕ)
    (hGap :
      0 <
        wz2PaperFinalComponentGap
          sourceLoss structuralLoss capLoss componentFloorLoss
          outputLoss) :
    Nonempty
      (WZ2PaperFinalComponentAbsorptionData
        sourceLoss structuralLoss capLoss componentFloorLoss
        outputLoss totalExponent) := by
  let fixedLoss : ENNReal :=
    wz2PaperPreparedOneParentFiniteLoss sourceLoss *
      (55296 * Kakeya.deltaTubeVolume 1)
  let coefficient : ENNReal := 4 * fixedLoss
  have hFixedTop : fixedLoss ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (by simp [wz2PaperPreparedOneParentFiniteLoss,
          packingConstant10000])
        (ENNReal.pow_ne_top (by norm_num)))
      (ENNReal.mul_ne_top
        (ENNReal.natCast_ne_top 55296)
        deltaTubeVolume_one_ne_top)
  have hCoefficientTop : coefficient ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hFixedTop
  rcases
      exists_delta_log_absorbed_ennreal
        coefficient hCoefficientTop hGap
        (show 0 < totalExponent + 1 by omega)
    with ⟨logScale, hLogScale, hLogScaleOne, hLogAbsorb⟩
  let delta₀ := min logScale (Real.exp (-1))
  have hExpPos : 0 < Real.exp (-1) := Real.exp_pos _
  have hExpOne : Real.exp (-1) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num)
  have hdelta₀ : 0 < delta₀ :=
    lt_min hLogScale hExpPos
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans hLogScaleOne
  refine
    ⟨{
      delta₀ := delta₀
      delta₀_pos := hdelta₀
      delta₀_le_one := hdelta₀One
      absorb := ?_
    }⟩
  intro delta hdelta hdeltaBound
  have hdeltaLog : delta ≤ logScale :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaExp : delta ≤ Real.exp (-1) :=
    hdeltaBound.trans (min_le_right _ _)
  have hdeltaOne : delta ≤ 1 :=
    hdeltaBound.trans hdelta₀One
  have hdeltaStrict : delta < 1 := by
    exact hdeltaExp.trans_lt <|
      (Real.exp_lt_one_iff.mpr (by norm_num))
  let logTerm : ENNReal :=
    ENNReal.ofReal (Real.log (1 / delta))
  let enlargedLog : ENNReal :=
    ENNReal.ofReal (1 + Real.log delta⁻¹)
  have hInvEq : delta⁻¹ = 1 / delta := by
    field_simp [hdelta.ne']
  have hLogRealPos : 0 < Real.log (1 / delta) := by
    exact Real.log_pos (one_lt_one_div hdelta hdeltaStrict)
  have hLogZero : logTerm ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hLogRealPos).ne'
  have hLogTop : logTerm ≠ ⊤ := by
    simp [logTerm]
  have hEnlargedOne : (1 : ENNReal) ≤ enlargedLog := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_mono
    rw [hInvEq]
    linarith
  have hLogLe : logTerm ≤ enlargedLog := by
    dsimp only [logTerm, enlargedLog]
    apply ENNReal.ofReal_mono
    rw [hInvEq]
    linarith
  have hLogPow :
      logTerm ^ totalExponent ≤
        enlargedLog ^ (totalExponent + 1) := by
    calc
      logTerm ^ totalExponent ≤
          enlargedLog ^ totalExponent := by
        gcongr
      _ ≤ enlargedLog ^ (totalExponent + 1) := by
        rw [pow_succ]
        simpa using
          mul_le_mul_left' hEnlargedOne
            (enlargedLog ^ totalExponent)
  have hCoefficientLog :
      coefficient * logTerm ^ totalExponent ≤
        Kakeya.realRpowENN delta
          (-(wz2PaperFinalComponentGap
            sourceLoss structuralLoss capLoss componentFloorLoss
            outputLoss)) := by
    calc
      coefficient * logTerm ^ totalExponent ≤
          coefficient * enlargedLog ^ (totalExponent + 1) := by
        gcongr
      _ ≤
          Kakeya.realRpowENN delta
            (-(wz2PaperFinalComponentGap
              sourceLoss structuralLoss capLoss componentFloorLoss
              outputLoss)) :=
        hLogAbsorb delta hdelta hdeltaLog
  have hLogPowZero : logTerm ^ totalExponent ≠ 0 :=
    pow_ne_zero _ hLogZero
  have hLogPowTop : logTerm ^ totalExponent ≠ ⊤ :=
    ENNReal.pow_ne_top hLogTop
  have hFractionEq :
      wz1PaperRefinementFraction delta totalExponent =
        (logTerm ^ totalExponent)⁻¹ := by
    change logTerm⁻¹ ^ totalExponent =
      (logTerm ^ totalExponent)⁻¹
    exact ENNReal.inv_pow.symm
  have hCoefficient :
      coefficient ≤
        wz1PaperRefinementFraction delta totalExponent *
          Kakeya.realRpowENN delta
            (-(wz2PaperFinalComponentGap
              sourceLoss structuralLoss capLoss componentFloorLoss
              outputLoss)) := by
    have hScaled :
        coefficient * logTerm ^ totalExponent *
              (logTerm ^ totalExponent)⁻¹ ≤
          Kakeya.realRpowENN delta
              (-(wz2PaperFinalComponentGap
                sourceLoss structuralLoss capLoss componentFloorLoss
                outputLoss)) *
            (logTerm ^ totalExponent)⁻¹ := by
      gcongr
    rw [mul_assoc,
      ENNReal.mul_inv_cancel hLogPowZero hLogPowTop,
      mul_one] at hScaled
    simpa [hFractionEq, mul_comm] using hScaled
  let gap :=
    wz2PaperFinalComponentGap
      sourceLoss structuralLoss capLoss componentFloorLoss outputLoss
  let targetExponent : ℝ :=
    2 - sourceLoss - capLoss +
      outputLoss * (componentFloorLoss + capLoss)
  have hExponent :
      targetExponent - structuralLoss =
        (2 + 2 * sourceLoss) + gap := by
    dsimp only [targetExponent, gap, wz2PaperFinalComponentGap]
    ring
  have hPower :
      Kakeya.realRpowENN delta (-structuralLoss) *
          Kakeya.realRpowENN delta targetExponent =
        Kakeya.realRpowENN delta (2 + 2 * sourceLoss) *
          Kakeya.realRpowENN delta gap := by
    calc
      Kakeya.realRpowENN delta (-structuralLoss) *
            Kakeya.realRpowENN delta targetExponent =
          Kakeya.realRpowENN delta
            ((-structuralLoss) + targetExponent) := by
        exact
          (realRpowENN_add hdelta
            (-structuralLoss) targetExponent).symm
      _ =
          Kakeya.realRpowENN delta
            ((2 + 2 * sourceLoss) + gap) := by
        congr 1
        linarith [hExponent]
      _ =
          Kakeya.realRpowENN delta (2 + 2 * sourceLoss) *
            Kakeya.realRpowENN delta gap :=
        realRpowENN_add hdelta _ _
  have hGapCancel :
      Kakeya.realRpowENN delta (-gap) *
          Kakeya.realRpowENN delta gap = 1 := by
    rw [← realRpowENN_add hdelta]
    simp [Kakeya.realRpowENN]
  calc
    (2 *
          (Kakeya.realRpowENN delta (-structuralLoss) *
            fixedLoss)) *
        Kakeya.realRpowENN delta targetExponent =
      (1 / 2 : ENNReal) * coefficient *
        (Kakeya.realRpowENN delta (-structuralLoss) *
          Kakeya.realRpowENN delta targetExponent) := by
      dsimp only [coefficient]
      have hHalfFour :
          (1 / 2 : ENNReal) * 4 = 2 := by
        have hCancel :
            (2 : ENNReal)⁻¹ * 2 = 1 :=
          ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
        calc
          (1 / 2 : ENNReal) * 4 =
              (2 : ENNReal)⁻¹ * 4 := by rw [one_div]
          _ = ((2 : ENNReal)⁻¹ * 2) * 2 := by ring
          _ = 1 * 2 := by rw [hCancel]
          _ = 2 := by simp
      calc
        (2 *
              (Kakeya.realRpowENN delta (-structuralLoss) *
                fixedLoss)) *
            Kakeya.realRpowENN delta targetExponent =
          2 *
            (Kakeya.realRpowENN delta (-structuralLoss) *
              fixedLoss *
              Kakeya.realRpowENN delta targetExponent) := by ring
        _ =
          ((1 / 2 : ENNReal) * 4) *
            (Kakeya.realRpowENN delta (-structuralLoss) *
              fixedLoss *
              Kakeya.realRpowENN delta targetExponent) := by
            rw [hHalfFour]
        _ =
          (1 / 2 : ENNReal) * (4 * fixedLoss) *
            (Kakeya.realRpowENN delta (-structuralLoss) *
              Kakeya.realRpowENN delta targetExponent) := by ring
    _ =
      (1 / 2 : ENNReal) * coefficient *
        (Kakeya.realRpowENN delta (2 + 2 * sourceLoss) *
          Kakeya.realRpowENN delta gap) := by
      rw [hPower]
    _ ≤
      (1 / 2 : ENNReal) *
        (wz1PaperRefinementFraction delta totalExponent *
          Kakeya.realRpowENN delta (-gap)) *
        (Kakeya.realRpowENN delta (2 + 2 * sourceLoss) *
          Kakeya.realRpowENN delta gap) := by
      gcongr
    _ =
      (1 / 2 : ENNReal) *
        wz1PaperRefinementFraction delta totalExponent *
        Kakeya.realRpowENN delta (2 + 2 * sourceLoss) := by
      calc
        (1 / 2 : ENNReal) *
              (wz1PaperRefinementFraction delta totalExponent *
                Kakeya.realRpowENN delta (-gap)) *
              (Kakeya.realRpowENN delta (2 + 2 * sourceLoss) *
                Kakeya.realRpowENN delta gap) =
            ((1 / 2 : ENNReal) *
                wz1PaperRefinementFraction delta totalExponent *
                Kakeya.realRpowENN delta (2 + 2 * sourceLoss)) *
              (Kakeya.realRpowENN delta (-gap) *
                Kakeya.realRpowENN delta gap) := by
          ring
        _ =
            (1 / 2 : ENNReal) *
              wz1PaperRefinementFraction delta totalExponent *
              Kakeya.realRpowENN delta (2 + 2 * sourceLoss) := by
          rw [hGapCancel, mul_one]

end Kakeya.Assouad

end
