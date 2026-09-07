import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalLossHierarchy
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperStructuralParentCardinalityUniform
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Absorption for the final owner-route fiber density

After the component floors and the exact owner-cell identity are inserted,
the remaining scalar inequality has exponent gap

`outputLoss * (densityLoss - componentLoss - capLoss)
  - 2 * sourceLoss - structuralLoss`.

The explicit hierarchy makes this gap positive.  A fixed polylogarithmic
refinement loss and the one-parent finite constant can therefore be absorbed
by taking the source scale sufficiently small.
-/

noncomputable section

namespace Kakeya.Assouad

def wz2PaperFinalFiberDensityGap
    (sourceLoss structuralLoss capLoss componentLoss densityLoss
      outputLoss : ℝ) : ℝ :=
  outputLoss * (densityLoss - componentLoss - capLoss) -
    2 * sourceLoss - structuralLoss

structure WZ2PaperFinalFiberDensityAbsorptionData
    (sourceLoss structuralLoss capLoss componentLoss densityLoss
      outputLoss : ℝ)
    (totalExponent : ℕ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorb :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      (4 *
          (wz2PaperPreparedOneParentFiniteLoss sourceLoss *
            (55296 * Kakeya.deltaTubeVolume 1) *
            (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3))⁻¹)) *
        Kakeya.realRpowENN delta (-structuralLoss) *
        Kakeya.realRpowENN delta
          (outputLoss * (densityLoss - componentLoss - capLoss)) ≤
      wz1PaperRefinementFraction delta totalExponent *
        Kakeya.realRpowENN delta (2 * sourceLoss)

theorem wz2_paper_final_fiber_density_absorption
    (sourceLoss structuralLoss capLoss componentLoss densityLoss
      outputLoss : ℝ)
    (totalExponent : ℕ)
    (hGap :
      0 <
        wz2PaperFinalFiberDensityGap
          sourceLoss structuralLoss capLoss componentLoss
          densityLoss outputLoss) :
    Nonempty
      (WZ2PaperFinalFiberDensityAbsorptionData
        sourceLoss structuralLoss capLoss componentLoss densityLoss
        outputLoss totalExponent) := by
  let fixedLoss : ENNReal :=
    wz2PaperPreparedOneParentFiniteLoss sourceLoss *
      (55296 * Kakeya.deltaTubeVolume 1) *
      (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3))⁻¹
  let coefficient : ENNReal := 4 * fixedLoss
  have hFixedTop : fixedLoss ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (by simp [wz2PaperPreparedOneParentFiniteLoss,
            packingConstant10000])
          (ENNReal.pow_ne_top (by norm_num)))
        (ENNReal.mul_ne_top
          (ENNReal.natCast_ne_top 55296)
          deltaTubeVolume_one_ne_top))
      (ENNReal.inv_ne_top.mpr (by positivity))
  have hCoefficientTop : coefficient ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hFixedTop
  rcases
      exists_delta_log_absorbed_ennreal
        coefficient hCoefficientTop hGap
        (show 0 < totalExponent + 1 by omega)
    with ⟨logScale, hLogScale, hLogScaleOne, hLogAbsorb⟩
  let delta₀ := min logScale (Real.exp (-1))
  have hdelta₀ : 0 < delta₀ :=
    lt_min hLogScale (Real.exp_pos _)
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
  have hdeltaStrict : delta < 1 :=
    hdeltaExp.trans_lt (Real.exp_lt_one_iff.mpr (by norm_num))
  let logTerm : ENNReal :=
    ENNReal.ofReal (Real.log (1 / delta))
  let enlargedLog : ENNReal :=
    ENNReal.ofReal (1 + Real.log delta⁻¹)
  have hInvEq : delta⁻¹ = 1 / delta := by
    field_simp [hdelta.ne']
  have hLogRealPos : 0 < Real.log (1 / delta) :=
    Real.log_pos (one_lt_one_div hdelta hdeltaStrict)
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
      logTerm ^ totalExponent ≤
        enlargedLog ^ (totalExponent + 1) := by
    calc
      logTerm ^ totalExponent ≤
          enlargedLog ^ totalExponent := by gcongr
      _ ≤ enlargedLog ^ (totalExponent + 1) := by
        rw [pow_succ]
        simpa using
          mul_le_mul_left' hEnlargedOne
            (enlargedLog ^ totalExponent)
  have hCoefficientLog :
      coefficient * logTerm ^ totalExponent ≤
        Kakeya.realRpowENN delta
          (-(wz2PaperFinalFiberDensityGap
            sourceLoss structuralLoss capLoss componentLoss
            densityLoss outputLoss)) := by
    calc
      coefficient * logTerm ^ totalExponent ≤
          coefficient * enlargedLog ^ (totalExponent + 1) := by
        gcongr
      _ ≤
          Kakeya.realRpowENN delta
            (-(wz2PaperFinalFiberDensityGap
              sourceLoss structuralLoss capLoss componentLoss
              densityLoss outputLoss)) :=
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
            (-(wz2PaperFinalFiberDensityGap
              sourceLoss structuralLoss capLoss componentLoss
              densityLoss outputLoss)) := by
    have hScaled :
        coefficient * logTerm ^ totalExponent *
              (logTerm ^ totalExponent)⁻¹ ≤
          Kakeya.realRpowENN delta
              (-(wz2PaperFinalFiberDensityGap
                sourceLoss structuralLoss capLoss componentLoss
                densityLoss outputLoss)) *
            (logTerm ^ totalExponent)⁻¹ := by
      gcongr
    rw [mul_assoc,
      ENNReal.mul_inv_cancel hLogPowZero hLogPowTop,
      mul_one] at hScaled
    simpa [hFractionEq, mul_comm] using hScaled
  let targetExponent : ℝ :=
    outputLoss * (densityLoss - componentLoss - capLoss)
  let desiredExponent : ℝ := 2 * sourceLoss
  have hExponent :
      targetExponent - structuralLoss =
        desiredExponent +
          wz2PaperFinalFiberDensityGap
            sourceLoss structuralLoss capLoss componentLoss
            densityLoss outputLoss := by
    dsimp only [targetExponent, desiredExponent,
      wz2PaperFinalFiberDensityGap]
    ring
  have hPower :
      Kakeya.realRpowENN delta (-structuralLoss) *
          Kakeya.realRpowENN delta targetExponent =
        Kakeya.realRpowENN delta desiredExponent *
          Kakeya.realRpowENN delta
            (wz2PaperFinalFiberDensityGap
              sourceLoss structuralLoss capLoss componentLoss
              densityLoss outputLoss) := by
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
            (desiredExponent +
              wz2PaperFinalFiberDensityGap
                sourceLoss structuralLoss capLoss componentLoss
                densityLoss outputLoss) := by
        congr 1
        linarith [hExponent]
      _ =
          Kakeya.realRpowENN delta desiredExponent *
            Kakeya.realRpowENN delta
              (wz2PaperFinalFiberDensityGap
                sourceLoss structuralLoss capLoss componentLoss
                densityLoss outputLoss) :=
        realRpowENN_add hdelta _ _
  have hGapCancel :
      Kakeya.realRpowENN delta
            (-(wz2PaperFinalFiberDensityGap
              sourceLoss structuralLoss capLoss componentLoss
              densityLoss outputLoss)) *
          Kakeya.realRpowENN delta
            (wz2PaperFinalFiberDensityGap
              sourceLoss structuralLoss capLoss componentLoss
              densityLoss outputLoss) = 1 := by
    rw [← realRpowENN_add hdelta]
    simp [Kakeya.realRpowENN]
  change
    (4 * fixedLoss) *
          Kakeya.realRpowENN delta (-structuralLoss) *
          Kakeya.realRpowENN delta targetExponent ≤
      wz1PaperRefinementFraction delta totalExponent *
        Kakeya.realRpowENN delta desiredExponent
  calc
    (4 * fixedLoss) *
        Kakeya.realRpowENN delta (-structuralLoss) *
        Kakeya.realRpowENN delta targetExponent =
      coefficient *
        (Kakeya.realRpowENN delta (-structuralLoss) *
          Kakeya.realRpowENN delta targetExponent) := by
      dsimp only [coefficient, fixedLoss]
      ring
    _ =
      coefficient *
        (Kakeya.realRpowENN delta desiredExponent *
          Kakeya.realRpowENN delta
            (wz2PaperFinalFiberDensityGap
              sourceLoss structuralLoss capLoss componentLoss
              densityLoss outputLoss)) := by
      rw [hPower]
    _ ≤
      (wz1PaperRefinementFraction delta totalExponent *
          Kakeya.realRpowENN delta
            (-(wz2PaperFinalFiberDensityGap
              sourceLoss structuralLoss capLoss componentLoss
              densityLoss outputLoss))) *
        (Kakeya.realRpowENN delta desiredExponent *
          Kakeya.realRpowENN delta
            (wz2PaperFinalFiberDensityGap
              sourceLoss structuralLoss capLoss componentLoss
              densityLoss outputLoss)) := by
      gcongr
    _ =
      wz1PaperRefinementFraction delta totalExponent *
        Kakeya.realRpowENN delta desiredExponent := by
      rw [show
        (wz1PaperRefinementFraction delta totalExponent *
            Kakeya.realRpowENN delta
              (-(wz2PaperFinalFiberDensityGap
                sourceLoss structuralLoss capLoss componentLoss
                densityLoss outputLoss))) *
          (Kakeya.realRpowENN delta desiredExponent *
            Kakeya.realRpowENN delta
              (wz2PaperFinalFiberDensityGap
                sourceLoss structuralLoss capLoss componentLoss
                densityLoss outputLoss)) =
          wz1PaperRefinementFraction delta totalExponent *
            Kakeya.realRpowENN delta desiredExponent *
              (Kakeya.realRpowENN delta
                  (-(wz2PaperFinalFiberDensityGap
                    sourceLoss structuralLoss capLoss componentLoss
                    densityLoss outputLoss)) *
                Kakeya.realRpowENN delta
                  (wz2PaperFinalFiberDensityGap
                    sourceLoss structuralLoss capLoss componentLoss
                    densityLoss outputLoss)) by ring]
      rw [hGapCancel, mul_one]
    _ =
      wz1PaperRefinementFraction delta totalExponent *
        Kakeya.realRpowENN delta (2 * sourceLoss) := rfl

theorem wz2_paper_final_fiber_density_scalar
    {delta rho sigma sourceLoss structuralLoss capLoss componentLoss
      densityLoss outputLoss : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hRelativeGap :
      0 < densityLoss - componentLoss - capLoss)
    (hratio :
      delta / rho ≤ Real.rpow delta outputLoss)
    {totalExponent : ℕ}
    (absorption :
      WZ2PaperFinalFiberDensityAbsorptionData
        sourceLoss structuralLoss capLoss componentLoss densityLoss
        outputLoss totalExponent)
    (hdeltaAbsorb : delta ≤ absorption.delta₀)
    (sourceCardinality : ENNReal) :
    let jacobianInverse :=
      (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3))⁻¹
    let targetDensity :=
      jacobianInverse *
        Kakeya.realRpowENN (delta / rho) densityLoss
    let lowerCoefficient :=
      Kakeya.realRpowENN (delta / rho)
        (2 - sigma + componentLoss)
    let upperCoefficient :=
      Kakeya.realRpowENN (delta / rho)
        (2 - sigma - capLoss)
    let weight :=
      (1 / 2 : ENNReal) *
        Kakeya.realRpowENN delta sourceLoss
    let constant :=
      Kakeya.realRpowENN delta (-structuralLoss) *
        (wz2PaperPreparedOneParentFiniteLoss sourceLoss *
          (55296 * Kakeya.deltaTubeVolume 1))
    let globalMass :=
      wz1PaperRefinementFraction delta totalExponent *
        Kakeya.realRpowENN delta sourceLoss *
        Kakeya.realRpowENN delta 2 *
        sourceCardinality
    (2 * targetDensity *
          Kakeya.realRpowENN delta 2 * upperCoefficient) *
        (constant * sourceCardinality) ≤
      (lowerCoefficient * globalMass) * weight := by
  dsimp only
  let relativeGap := densityLoss - componentLoss - capLoss
  have hratioPos : 0 < delta / rho := div_pos hdelta hrho
  have hRelativePower :
      Kakeya.realRpowENN (delta / rho) relativeGap ≤
        Kakeya.realRpowENN delta (outputLoss * relativeGap) := by
    apply ENNReal.ofReal_mono
    calc
      Real.rpow (delta / rho) relativeGap ≤
          Real.rpow (Real.rpow delta outputLoss) relativeGap :=
        Real.rpow_le_rpow hratioPos.le hratio hRelativeGap.le
      _ = Real.rpow delta (outputLoss * relativeGap) := by
        exact (Real.rpow_mul hdelta.le _ _).symm
  have hAbsorb :=
    absorption.absorb delta hdelta hdeltaAbsorb
  have hCoefficient :
      (4 *
          (wz2PaperPreparedOneParentFiniteLoss sourceLoss *
            (55296 * Kakeya.deltaTubeVolume 1) *
            (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3))⁻¹)) *
          Kakeya.realRpowENN delta (-structuralLoss) *
          Kakeya.realRpowENN (delta / rho) relativeGap ≤
        wz1PaperRefinementFraction delta totalExponent *
          Kakeya.realRpowENN delta (2 * sourceLoss) := by
    calc
      (4 *
          (wz2PaperPreparedOneParentFiniteLoss sourceLoss *
            (55296 * Kakeya.deltaTubeVolume 1) *
            (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3))⁻¹)) *
          Kakeya.realRpowENN delta (-structuralLoss) *
          Kakeya.realRpowENN (delta / rho) relativeGap ≤
        (4 *
          (wz2PaperPreparedOneParentFiniteLoss sourceLoss *
            (55296 * Kakeya.deltaTubeVolume 1) *
            (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3))⁻¹)) *
          Kakeya.realRpowENN delta (-structuralLoss) *
          Kakeya.realRpowENN delta (outputLoss * relativeGap) := by
        gcongr
      _ ≤
        wz1PaperRefinementFraction delta totalExponent *
          Kakeya.realRpowENN delta (2 * sourceLoss) := by
        simpa [relativeGap, mul_assoc] using hAbsorb
  have hHalfCoefficient :
      (2 *
          ((ENNReal.ofReal ((1 / 100 : ℝ) ^ 3))⁻¹ *
            (wz2PaperPreparedOneParentFiniteLoss sourceLoss *
              (55296 * Kakeya.deltaTubeVolume 1)) *
            Kakeya.realRpowENN delta (-structuralLoss) *
            Kakeya.realRpowENN (delta / rho) relativeGap)) ≤
        (1 / 2 : ENNReal) *
          (wz1PaperRefinementFraction delta totalExponent *
            Kakeya.realRpowENN delta (2 * sourceLoss)) := by
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
      2 *
          ((ENNReal.ofReal ((1 / 100 : ℝ) ^ 3))⁻¹ *
            (wz2PaperPreparedOneParentFiniteLoss sourceLoss *
              (55296 * Kakeya.deltaTubeVolume 1)) *
            Kakeya.realRpowENN delta (-structuralLoss) *
            Kakeya.realRpowENN (delta / rho) relativeGap) =
        ((1 / 2 : ENNReal) * 4) *
          ((ENNReal.ofReal ((1 / 100 : ℝ) ^ 3))⁻¹ *
            (wz2PaperPreparedOneParentFiniteLoss sourceLoss *
              (55296 * Kakeya.deltaTubeVolume 1)) *
            Kakeya.realRpowENN delta (-structuralLoss) *
            Kakeya.realRpowENN (delta / rho) relativeGap) := by
        rw [hHalfFour]
      _ =
        (1 / 2 : ENNReal) *
          ((4 *
            (wz2PaperPreparedOneParentFiniteLoss sourceLoss *
              (55296 * Kakeya.deltaTubeVolume 1) *
              (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3))⁻¹)) *
            Kakeya.realRpowENN delta (-structuralLoss) *
            Kakeya.realRpowENN (delta / rho) relativeGap) := by
        ring
      _ ≤
        (1 / 2 : ENNReal) *
          (wz1PaperRefinementFraction delta totalExponent *
            Kakeya.realRpowENN delta (2 * sourceLoss)) := by
        gcongr
  have hRatioPower :
      Kakeya.realRpowENN (delta / rho) densityLoss *
          Kakeya.realRpowENN (delta / rho)
            (2 - sigma - capLoss) =
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma + componentLoss) *
          Kakeya.realRpowENN (delta / rho) relativeGap := by
    rw [← realRpowENN_add hratioPos,
      ← realRpowENN_add hratioPos]
    congr 1
    dsimp only [relativeGap]
    ring
  have hSourcePower :
      Kakeya.realRpowENN delta sourceLoss *
          Kakeya.realRpowENN delta sourceLoss =
        Kakeya.realRpowENN delta (2 * sourceLoss) := by
    rw [← realRpowENN_add hdelta]
    congr 1
    ring
  calc
    (2 *
          ((ENNReal.ofReal ((1 / 100 : ℝ) ^ 3))⁻¹ *
            Kakeya.realRpowENN (delta / rho) densityLoss) *
          Kakeya.realRpowENN delta 2 *
          Kakeya.realRpowENN (delta / rho)
            (2 - sigma - capLoss)) *
        ((Kakeya.realRpowENN delta (-structuralLoss) *
          (wz2PaperPreparedOneParentFiniteLoss sourceLoss *
            (55296 * Kakeya.deltaTubeVolume 1))) *
          sourceCardinality) =
      (2 *
        ((ENNReal.ofReal ((1 / 100 : ℝ) ^ 3))⁻¹ *
          (wz2PaperPreparedOneParentFiniteLoss sourceLoss *
            (55296 * Kakeya.deltaTubeVolume 1)) *
          Kakeya.realRpowENN delta (-structuralLoss) *
          (Kakeya.realRpowENN (delta / rho) densityLoss *
            Kakeya.realRpowENN (delta / rho)
              (2 - sigma - capLoss)))) *
        (Kakeya.realRpowENN delta 2 * sourceCardinality) := by
      ring
    _ =
      (2 *
        ((ENNReal.ofReal ((1 / 100 : ℝ) ^ 3))⁻¹ *
          (wz2PaperPreparedOneParentFiniteLoss sourceLoss *
            (55296 * Kakeya.deltaTubeVolume 1)) *
          Kakeya.realRpowENN delta (-structuralLoss) *
          Kakeya.realRpowENN (delta / rho) relativeGap)) *
        (Kakeya.realRpowENN (delta / rho)
          (2 - sigma + componentLoss) *
          (Kakeya.realRpowENN delta 2 * sourceCardinality)) := by
      rw [hRatioPower]
      ring
    _ ≤
      ((1 / 2 : ENNReal) *
        (wz1PaperRefinementFraction delta totalExponent *
          Kakeya.realRpowENN delta (2 * sourceLoss))) *
        (Kakeya.realRpowENN (delta / rho)
          (2 - sigma + componentLoss) *
          (Kakeya.realRpowENN delta 2 * sourceCardinality)) := by
      gcongr
    _ =
      (Kakeya.realRpowENN (delta / rho)
          (2 - sigma + componentLoss) *
        (wz1PaperRefinementFraction delta totalExponent *
          Kakeya.realRpowENN delta sourceLoss *
          Kakeya.realRpowENN delta 2 * sourceCardinality)) *
        ((1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta sourceLoss) := by
      rw [← hSourcePower]
      ring

end Kakeya.Assouad

end
