import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentUniformAbsorptionStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentSelectionAbsorption
import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentQuantitativeEnvelope
import MyLeanRepo.Kakeya.Assouad.PropStickyRelativeScaleAbsorption
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26DeltaBudget

/-! # Uniform numerical absorption for every prepared parent -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_prop_sticky_prepared_one_parent_uniform_absorption :
    WZ2PropStickyPreparedOneParentUniformAbsorptionStatement := by
  intro sigma floorLoss strongLoss outputLoss critical
    hfloorLoss hfloorStrong hbudget sourceLoss stableLoss
    hsourceLoss hsourceStable henvelopeGap
  have houtputLoss : 0 < outputLoss := by
    have hstrongLoss : 0 < strongLoss :=
      critical.structuralLoss_pos.trans_le
        critical.structuralLoss_le
    linarith
  have hstableLoss : 0 < stableLoss :=
    hsourceLoss.trans hsourceStable
  rcases
      wz2_prop_sticky_prepared_one_parent_selection_absorption
        sourceLoss hsourceLoss with
    ⟨selectionAbsorption⟩
  let envelope := wz2PaperPreparedOneParentEnvelope sourceLoss
  have hfiniteLossTop :
      wz2PaperPreparedOneParentFiniteLoss sourceLoss ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (by simp [packingConstant10000])
      (ENNReal.pow_ne_top (by norm_num))
  have hgeometryTop :
      55296 * Kakeya.deltaTubeVolume 1 ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top 55296)
      deltaTubeVolume_one_ne_top
  have henvelopeTop : envelope ≠ ⊤ := by
    dsimp only [envelope, wz2PaperPreparedOneParentEnvelope]
    apply ENNReal.mul_ne_top
    · norm_num
    · apply max_ne_top
      · norm_num
      · apply max_ne_top
        · exact ENNReal.mul_ne_top
            (ENNReal.mul_ne_top (by norm_num) hfiniteLossTop)
            hgeometryTop
        · exact ENNReal.mul_ne_top
            (by norm_num)
            (ENNReal.pow_ne_top
              (ENNReal.mul_ne_top hfiniteLossTop hgeometryTop))
  let envelopeGap : ℝ :=
    critical.structuralLoss ^ 2 - 5 * stableLoss
  have henvelopeGapPos : 0 < envelopeGap := by
    dsimp only [envelopeGap]
    linarith
  rcases
      exists_delta_realRpowENN_bound
        envelope henvelopeTop henvelopeGapPos with
    ⟨envelopeScale, henvelopeScale, henvelopeScaleOne,
      hEnvelopeAbsorb⟩
  let densityConstant : ENNReal :=
    (2 : ENNReal) *
      (55296 * Kakeya.deltaTubeVolume 1) *
      (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3))⁻¹
  have hdensityConstantTop : densityConstant ≠ ⊤ := by
    dsimp only [densityConstant]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top
          (ENNReal.natCast_ne_top 55296)
          deltaTubeVolume_one_ne_top))
      (ENNReal.inv_ne_top.mpr (by
        simp [ENNReal.ofReal_eq_zero]))
  let densityGap : ℝ :=
    outputLoss * critical.structuralLoss - sourceLoss
  have hdensityGapPos : 0 < densityGap := by
    dsimp only [densityGap]
    have hcriticalPositive := critical.structuralLoss_pos
    have hcriticalStrong := critical.structuralLoss_le
    nlinarith [hbudget, hsourceStable, henvelopeGap]
  rcases
      exists_delta_log_absorbed_ennreal
        densityConstant hdensityConstantTop hdensityGapPos
        (show 0 < (4 : ℕ) by omega) with
    ⟨densityScale, hdensityScale, hdensityScaleOne,
      hDensityAbsorb⟩
  let cardinalityConstant : ENNReal :=
    2 * (55296 * Kakeya.deltaTubeVolume 1)
  have hcardinalityConstantTop : cardinalityConstant ≠ ⊤ := by
    dsimp only [cardinalityConstant]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top
        (ENNReal.natCast_ne_top 55296)
        deltaTubeVolume_one_ne_top)
  rcases
      exists_delta_realRpowENN_bound
        cardinalityConstant hcardinalityConstantTop
        (show 0 < strongLoss ^ 2 by
          have hstrongLoss :=
            critical.structuralLoss_pos.trans_le
              critical.structuralLoss_le
          positivity) with
    ⟨cardinalityScale, hcardinalityScale,
      hcardinalityScaleOne, hCardinalityAbsorb⟩
  have hmultiplicityGap : 0 < strongLoss - floorLoss := by
    linarith
  rcases
      exists_delta_realRpowENN_bound
        cardinalityConstant hcardinalityConstantTop
        (show 0 < (strongLoss - floorLoss) ^ 2 by
          positivity) with
    ⟨multiplicityScale, hmultiplicityScale,
      hmultiplicityScaleOne, hMultiplicityAbsorb⟩
  rcases
      exists_delta_rpow_le_single
        outputLoss (1 / 24)
        houtputLoss (by norm_num) (by norm_num) with
    ⟨ratioScale, hratioScale, hratioScaleOne, hRatioSmall⟩
  let criticalThreshold : ℝ := min critical.delta₀ (1 / 2)
  have hcriticalThreshold : 0 < criticalThreshold := by
    dsimp only [criticalThreshold]
    exact lt_min critical.delta₀_pos (by norm_num)
  have hcriticalThresholdOne : criticalThreshold < 1 := by
    exact (min_le_right _ _).trans_lt (by norm_num)
  rcases
      exists_delta_rpow_le_single
        outputLoss criticalThreshold
        houtputLoss hcriticalThreshold
        hcriticalThresholdOne with
    ⟨criticalScale, hcriticalScale, hcriticalScaleOne,
      hCriticalScale⟩
  let delta₀ : ℝ :=
    min selectionAbsorption.delta₀
      (min envelopeScale
        (min densityScale
          (min cardinalityScale
            (min multiplicityScale
              (min ratioScale criticalScale)))))
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    exact lt_min selectionAbsorption.delta₀_pos <|
      lt_min henvelopeScale <|
        lt_min hdensityScale <|
          lt_min hcardinalityScale <|
            lt_min hmultiplicityScale <|
              lt_min hratioScale hcriticalScale
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans selectionAbsorption.delta₀_le_one
  refine
    ⟨{
      delta₀ := delta₀
      delta₀_pos := hdelta₀
      delta₀_le_one := hdelta₀One
      absorb := ?_
    }⟩
  intro delta hdelta hdeltaBound source shading caller
    hcallerLower hcallerUpper preparationExponent prepared parent
  have hselectionScale : delta ≤ selectionAbsorption.delta₀ :=
    hdeltaBound.trans (min_le_left _ _)
  have henvelopeScale' : delta ≤ envelopeScale :=
    hdeltaBound.trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have hdensityScale' : delta ≤ densityScale :=
    hdeltaBound.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have hcardinalityScale' : delta ≤ cardinalityScale :=
    hdeltaBound.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
  have hmultiplicityScale' : delta ≤ multiplicityScale :=
    hdeltaBound.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_left _ _)
  have hratioScale' : delta ≤ ratioScale :=
    hdeltaBound.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans <|
              (min_le_right _ _).trans (min_le_left _ _)
  have hcriticalScale' : delta ≤ criticalScale :=
    hdeltaBound.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans <|
              (min_le_right _ _).trans (min_le_right _ _)
  have hcallerPos : 0 < caller.1 :=
    (hdelta.trans_le caller.2.1)
  have hratio :
      delta / caller.1 ≤ Real.rpow delta outputLoss := by
    rw [div_le_iff₀ hcallerPos]
    have hsplit :
        Real.rpow delta 1 =
          Real.rpow delta (1 - outputLoss) *
            Real.rpow delta outputLoss := by
      calc
        Real.rpow delta 1 =
            Real.rpow delta ((1 - outputLoss) + outputLoss) := by
          congr 1
          ring
        _ =
            Real.rpow delta (1 - outputLoss) *
              Real.rpow delta outputLoss :=
          Real.rpow_add hdelta _ _
    calc
      delta = Real.rpow delta 1 := by simp
      _ = Real.rpow delta (1 - outputLoss) *
            Real.rpow delta outputLoss := hsplit
      _ ≤ caller.1 * Real.rpow delta outputLoss := by
        exact mul_le_mul_of_nonneg_right hcallerLower
          (Real.rpow_nonneg hdelta.le outputLoss)
      _ = Real.rpow delta outputLoss * caller.1 := by ring
  have hratioSmall :
      delta / caller.1 ≤ 1 / 24 :=
    hratio.trans (hRatioSmall delta hdelta hratioScale')
  have hcriticalRatio :
      delta / caller.1 ≤ critical.delta₀ :=
    hratio.trans <|
      (hCriticalScale delta hdelta hcriticalScale').trans
        (min_le_left _ _)
  rcases
      selectionAbsorption.absorb hdelta hselectionScale
        prepared parent with
    ⟨hdeltaSmall, hpacking, hbranch⟩
  refine
    ⟨hdeltaSmall, hratioSmall, hcriticalRatio,
      hpacking, hbranch, ?_⟩
  intro selection quantitative
  dsimp only
  have hdeltaOne : delta ≤ 1 := hdeltaBound.trans hdelta₀One
  have hEnvelope :=
    wz2_prop_sticky_prepared_one_parent_quantitative_envelope
      hdelta hdeltaOne hstableLoss hsourceStable
      prepared parent selection quantitative
  let restrictedConstant : ENNReal :=
    max 1
      (max quantitative.selectedUniformConstant
        ((quantitative.weight⁻¹ *
            (prepared.structuralConstant *
              quantitative.cardinalityRetentionConstant *
              quantitative.selectedUniformConstant)) *
          prepared.structuralConstant))
  let rootConstant : ENNReal :=
    max 1
      ((quantitative.weight⁻¹ *
          quantitative.cardinalityRetentionConstant) *
        prepared.structuralConstant)
  have hstrongOutput : strongLoss ≤ outputLoss := by
    have hstrongPositive :
        0 < strongLoss :=
      critical.structuralLoss_pos.trans_le
        critical.structuralLoss_le
    linarith
  have hcriticalOutput :
      critical.structuralLoss ≤ outputLoss :=
    critical.structuralLoss_le.trans hstrongOutput
  have hmultiplicityOutput :
      strongLoss - floorLoss ≤ outputLoss := by
    linarith
  have hcallerLowerCritical :
      Real.rpow delta
          (1 - critical.structuralLoss) ≤ caller.1 := by
    exact
      (Real.rpow_le_rpow_of_exponent_ge
        hdelta hdeltaOne (by linarith)).trans
        hcallerLower
  have hcallerLowerStrong :
      Real.rpow delta (1 - strongLoss) ≤ caller.1 := by
    exact
      (Real.rpow_le_rpow_of_exponent_ge
        hdelta hdeltaOne (by linarith)).trans
        hcallerLower
  have hcallerLowerMultiplicity :
      Real.rpow delta
          (1 - (strongLoss - floorLoss)) ≤ caller.1 := by
    exact
      (Real.rpow_le_rpow_of_exponent_ge
        hdelta hdeltaOne (by linarith)).trans
        hcallerLower
  have hTargetLower :
      Kakeya.realRpowENN delta
          (-(critical.structuralLoss ^ 2)) ≤
        Kakeya.realRpowENN
          (delta / caller.1) (-critical.structuralLoss) :=
    target_constant_lower_bound
      critical.structuralLoss_pos hdelta hcallerLowerCritical
  have hEnvelopeDelta :
      envelope *
          Kakeya.realRpowENN delta (-5 * stableLoss) ≤
        Kakeya.realRpowENN delta
          (-(critical.structuralLoss ^ 2)) := by
    have hconstant :=
      hEnvelopeAbsorb delta hdelta henvelopeScale'
    calc
      envelope *
            Kakeya.realRpowENN delta (-5 * stableLoss) ≤
          Kakeya.realRpowENN delta (-envelopeGap) *
            Kakeya.realRpowENN delta (-5 * stableLoss) := by
        gcongr
      _ =
          Kakeya.realRpowENN delta
            (-(critical.structuralLoss ^ 2)) := by
        rw [← realRpowENN_add hdelta]
        congr 2
        dsimp only [envelopeGap]
        ring
  have hRoot :
      (1000000 : ENNReal) * rootConstant ≤
        Kakeya.realRpowENN
          (delta / caller.1) (-critical.structuralLoss) :=
    hEnvelope.1.trans (hEnvelopeDelta.trans hTargetLower)
  have hRestricted :
      (1000000 : ENNReal) * restrictedConstant ≤
        Kakeya.realRpowENN
          (delta / caller.1) (-critical.structuralLoss) :=
    hEnvelope.2.1.trans (hEnvelopeDelta.trans hTargetLower)
  have hNestedRestricted :
      (81000000 : ENNReal) * restrictedConstant ≤
        Kakeya.realRpowENN
          (delta / caller.1) (-critical.structuralLoss) :=
    hEnvelope.2.2.1.trans (hEnvelopeDelta.trans hTargetLower)
  have hStructural :
      (200 : ENNReal) * prepared.structuralConstant ≤
        Kakeya.realRpowENN
          (delta / caller.1) (-critical.structuralLoss) :=
    hEnvelope.2.2.2.trans (hEnvelopeDelta.trans hTargetLower)
  have hDensity :
      Kakeya.realRpowENN
            (delta / caller.1) critical.structuralLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          (wz1PaperRefinementFraction delta 4 *
            ((1 / 2 : ENNReal) *
              Kakeya.realRpowENN delta sourceLoss)) := by
    let jacobian : ENNReal :=
      ENNReal.ofReal ((1 / 100 : ℝ) ^ 3)
    let geometry : ENNReal :=
      55296 * Kakeya.deltaTubeVolume 1
    let logTerm : ENNReal :=
      ENNReal.ofReal (Real.log (1 / delta))
    have hdeltaStrict : delta < 1 := by
      have hratioSmallDelta : delta ≤ 1 / 10000 := hdeltaSmall
      linarith
    have hlogPos : 0 < Real.log (1 / delta) := by
      apply Real.log_pos
      exact one_lt_one_div hdelta hdeltaStrict
    have hlogZero : logTerm ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hlogPos).ne'
    have hlogTop : logTerm ≠ ⊤ := by
      simp [logTerm]
    have hjacobianZero : jacobian ≠ 0 := by
      dsimp only [jacobian]
      simp [ENNReal.ofReal_eq_zero]
    have hjacobianTop : jacobian ≠ ⊤ := by
      simp [jacobian]
    have hconstant :=
      hDensityAbsorb delta hdelta hdensityScale'
    have hlogBound :
        densityConstant * logTerm ^ 4 ≤
          Kakeya.realRpowENN delta (-densityGap) := by
      calc
        densityConstant * logTerm ^ 4 ≤
            densityConstant *
              (ENNReal.ofReal (1 + Real.log delta⁻¹)) ^ 4 := by
          gcongr
          apply ENNReal.ofReal_mono
          have hinv : delta⁻¹ = 1 / delta := by
            field_simp [hdelta.ne']
          rw [hinv]
          linarith
        _ ≤ Kakeya.realRpowENN delta (-densityGap) := hconstant
    have hTargetPower :
        Kakeya.realRpowENN
              (delta / caller.1) critical.structuralLoss ≤
          Kakeya.realRpowENN delta
            (outputLoss * critical.structuralLoss) := by
      apply ENNReal.ofReal_mono
      have hbase : 0 ≤ delta / caller.1 := (div_pos hdelta hcallerPos).le
      calc
        Real.rpow (delta / caller.1)
              critical.structuralLoss ≤
            Real.rpow (Real.rpow delta outputLoss)
              critical.structuralLoss :=
          Real.rpow_le_rpow hbase hratio
            critical.structuralLoss_pos.le
        _ =
            Real.rpow delta
              (outputLoss * critical.structuralLoss) :=
          (Real.rpow_mul hdelta.le outputLoss
            critical.structuralLoss).symm
    have hPowerProduct :
        Kakeya.realRpowENN delta (-densityGap) *
            Kakeya.realRpowENN delta
              (outputLoss * critical.structuralLoss) =
          Kakeya.realRpowENN delta sourceLoss := by
      rw [← realRpowENN_add hdelta]
      congr 2
      dsimp only [densityGap]
      ring
    have hScaled :
        densityConstant * logTerm ^ 4 *
            Kakeya.realRpowENN delta
              (outputLoss * critical.structuralLoss) ≤
          Kakeya.realRpowENN delta sourceLoss := by
      calc
        densityConstant * logTerm ^ 4 *
              Kakeya.realRpowENN delta
                (outputLoss * critical.structuralLoss) ≤
            Kakeya.realRpowENN delta (-densityGap) *
              Kakeya.realRpowENN delta
                (outputLoss * critical.structuralLoss) := by
          gcongr
        _ = Kakeya.realRpowENN delta sourceLoss := hPowerProduct
    let multiplier : ENNReal :=
      2 * jacobian⁻¹ * logTerm ^ 4
    have hmultiplierZero : multiplier ≠ 0 := by
      dsimp only [multiplier]
      exact mul_ne_zero
        (mul_ne_zero (by norm_num)
          (ENNReal.inv_ne_zero.mpr hjacobianTop))
        (pow_ne_zero _ hlogZero)
    have hmultiplierTop : multiplier ≠ ⊤ := by
      dsimp only [multiplier]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num)
          (ENNReal.inv_ne_top.mpr hjacobianZero))
        (ENNReal.pow_ne_top hlogTop)
    have hjacobianCancel : jacobian⁻¹ * jacobian = 1 :=
      ENNReal.inv_mul_cancel hjacobianZero hjacobianTop
    have hlogCancel :
        logTerm ^ 4 * logTerm⁻¹ ^ 4 = 1 := by
      rw [mul_comm, ← mul_pow,
        ENNReal.inv_mul_cancel hlogZero hlogTop]
      norm_num
    have htwoCancel : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    have htwoHalf : (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
      rw [one_div]
      exact htwoCancel
    have hcancel :
        multiplier *
            (jacobian *
              (wz1PaperRefinementFraction delta 4 *
                ((1 / 2 : ENNReal) *
                  Kakeya.realRpowENN delta sourceLoss))) =
          Kakeya.realRpowENN delta sourceLoss := by
      change
        (2 * jacobian⁻¹ * logTerm ^ 4) *
            (jacobian *
              (logTerm⁻¹ ^ 4 *
                ((1 / 2 : ENNReal) *
                  Kakeya.realRpowENN delta sourceLoss))) =
          Kakeya.realRpowENN delta sourceLoss
      calc
        (2 * jacobian⁻¹ * logTerm ^ 4) *
              (jacobian *
                (logTerm⁻¹ ^ 4 *
                  ((1 / 2 : ENNReal) *
                    Kakeya.realRpowENN delta sourceLoss))) =
            (jacobian⁻¹ * jacobian) *
              (logTerm ^ 4 * logTerm⁻¹ ^ 4) *
              (2 * (1 / 2 : ENNReal)) *
              Kakeya.realRpowENN delta sourceLoss := by ring
        _ = Kakeya.realRpowENN delta sourceLoss := by
          rw [hjacobianCancel, hlogCancel]
          rw [one_mul, one_mul, htwoHalf, one_mul]
    apply (ENNReal.mul_le_mul_iff_left
      hmultiplierZero hmultiplierTop).mp
    have hleft :
        multiplier *
            (Kakeya.realRpowENN
                (delta / caller.1) critical.structuralLoss *
              geometry) ≤
          Kakeya.realRpowENN delta sourceLoss := by
      calc
        multiplier *
              (Kakeya.realRpowENN
                  (delta / caller.1) critical.structuralLoss *
                geometry) ≤
            multiplier *
              (Kakeya.realRpowENN delta
                  (outputLoss * critical.structuralLoss) *
                geometry) := by
          gcongr
        _ =
            densityConstant * logTerm ^ 4 *
              Kakeya.realRpowENN delta
                (outputLoss * critical.structuralLoss) := by
          dsimp only [multiplier, densityConstant, geometry,
            jacobian]
          ring
        _ ≤ Kakeya.realRpowENN delta sourceLoss := hScaled
    calc
      (Kakeya.realRpowENN
            (delta / caller.1) critical.structuralLoss *
          geometry) * multiplier =
        multiplier *
          (Kakeya.realRpowENN
              (delta / caller.1) critical.structuralLoss *
            geometry) := by ring
      _ ≤ Kakeya.realRpowENN delta sourceLoss := hleft
      _ =
        multiplier *
          (jacobian *
            (wz1PaperRefinementFraction delta 4 *
              ((1 / 2 : ENNReal) *
                Kakeya.realRpowENN delta sourceLoss))) :=
        hcancel.symm
      _ =
        (jacobian *
            (wz1PaperRefinementFraction delta 4 *
              ((1 / 2 : ENNReal) *
                Kakeya.realRpowENN delta sourceLoss))) *
          multiplier := by ring
  have hCardinality :
      55296 * Kakeya.deltaTubeVolume 1 ≤
        Kakeya.realRpowENN
          (delta / caller.1) (-strongLoss) := by
    have hconstant :=
      hCardinalityAbsorb delta hdelta hcardinalityScale'
    exact (show
      55296 * Kakeya.deltaTubeVolume 1 ≤ cardinalityConstant by
        dsimp only [cardinalityConstant]
        calc
          55296 * Kakeya.deltaTubeVolume 1 =
              1 * (55296 * Kakeya.deltaTubeVolume 1) := by
            rw [one_mul]
          _ ≤ 2 * (55296 * Kakeya.deltaTubeVolume 1) :=
            mul_le_mul_right'
              (by norm_num : (1 : ENNReal) ≤ 2) _).trans <|
      hconstant.trans <|
        wz2_realRpowENN_to_fiber_scale
          hdelta
          (critical.structuralLoss_pos.trans_le
            critical.structuralLoss_le)
          hcallerPos hcallerLowerStrong
  have hMultiplicity :
      2 * (55296 * Kakeya.deltaTubeVolume 1) ≤
        Kakeya.realRpowENN
          (delta / caller.1) (-(strongLoss - floorLoss)) := by
    have hconstant :=
      hMultiplicityAbsorb delta hdelta hmultiplicityScale'
    exact hconstant.trans <|
      wz2_realRpowENN_to_fiber_scale
        hdelta hmultiplicityGap hcallerPos
          hcallerLowerMultiplicity
  exact
    ⟨hRoot, hRestricted, hNestedRestricted, hStructural, hDensity,
      hCardinality, hMultiplicity⟩

end Kakeya.Assouad

end
