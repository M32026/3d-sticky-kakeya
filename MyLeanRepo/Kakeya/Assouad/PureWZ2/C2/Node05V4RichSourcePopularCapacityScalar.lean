import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightScalarSchedule

/-!
# Source-popular common-bin capacity schedule

This file selects, before any runtime family, the cutoff which guarantees that
the integrated common-bin threshold can support
`rho ^ (-1/2 + eta)` distinct spatial cells.  The conclusion deliberately
retains the first-call refinement fraction and terminal ratio: at runtime these
are compared with the exact post-two-call source-volume receipt, and the
positive finite regularity cost is cancelled on both sides.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

private theorem capacity_realRpowENN_div_mul
    {delta rho exponent : ℝ} (hdelta : 0 < delta) (hrho : 0 < rho) :
    Kakeya.realRpowENN (delta / rho) exponent *
        Kakeya.realRpowENN rho exponent =
      Kakeya.realRpowENN delta exponent := by
  have hmul := realRpowENN_mul (div_pos hdelta hrho) hrho exponent
  rw [show delta / rho * rho = delta by field_simp [hrho.ne']] at hmul
  exact hmul.symm

private theorem capacity_inverseSqrt_mul_spatialPower
    {rho sigma eta : ℝ} (hrho : 0 < rho) :
    Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) *
        (Kakeya.realRpowENN rho (-1 / 2 + eta) *
          Kakeya.realRpowENN rho (1 - sigma / 2)) =
      Kakeya.realRpowENN rho eta := by
  have hbase : 1 / Real.sqrt rho = Real.rpow rho (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    simpa [one_div] using
      (Real.rpow_neg hrho.le (1 / 2 : ℝ)).symm
  have hnested :
      Real.rpow (Real.rpow rho (-(1 / 2 : ℝ))) (1 - sigma) =
        Real.rpow rho ((-(1 / 2 : ℝ)) * (1 - sigma)) :=
    (Real.rpow_mul hrho.le (-(1 / 2 : ℝ)) (1 - sigma)).symm
  have hfirst :
      Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) =
        Kakeya.realRpowENN rho ((-(1 / 2 : ℝ)) * (1 - sigma)) := by
    unfold Kakeya.realRpowENN
    rw [hbase, hnested]
  rw [hfirst, ← realRpowENN_add hrho, ← realRpowENN_add hrho]
  congr 1
  ring

private theorem capacity_lhs_normalize
    {sigma eta inputLoss firstTerminalLoss delta rho : ℝ}
    {regularity : ℕ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    (regularity : ENNReal) *
          ((160 *
              (264 * Kakeya.realRpowENN delta (-inputLoss) *
                Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma)) *
              (23 * ENNReal.ofReal
                (Real.log (1 / (256 * rho)) + 1))) *
            (Kakeya.realRpowENN rho (-1 / 2 + eta) *
              PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
                sigma inputLoss delta rho)) =
      (160 * 264 * 23 * 32) *
        ((regularity : ENNReal) *
          ENNReal.ofReal (Real.log (1 / (256 * rho)) + 1)) *
        (Kakeya.realRpowENN delta
            (-(2 * inputLoss + 2 * firstTerminalLoss)) *
          Kakeya.realRpowENN delta
            (sigma + 2 * firstTerminalLoss)) *
        Kakeya.realRpowENN rho eta := by
  have hinverseSqrt := capacity_inverseSqrt_mul_spatialPower
    (rho := rho) (sigma := sigma) (eta := eta) hrho
  have hdeltaSplit :
      Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN delta sigma =
        Kakeya.realRpowENN delta
            (-(2 * inputLoss + 2 * firstTerminalLoss)) *
          Kakeya.realRpowENN delta
            (sigma + 2 * firstTerminalLoss) := by
    rw [← realRpowENN_add hdelta, ← realRpowENN_add hdelta]
    rw [← realRpowENN_add hdelta]
    congr 1
    ring
  unfold PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
  calc
    _ = (160 * 264 * 23 * 32) *
        ((regularity : ENNReal) *
          ENNReal.ofReal (Real.log (1 / (256 * rho)) + 1)) *
        (Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN delta sigma) *
        (Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) *
          (Kakeya.realRpowENN rho (-1 / 2 + eta) *
            Kakeya.realRpowENN rho (1 - sigma / 2))) := by ring
    _ = (160 * 264 * 23 * 32) *
        ((regularity : ENNReal) *
          ENNReal.ofReal (Real.log (1 / (256 * rho)) + 1)) *
        (Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN delta sigma) *
        Kakeya.realRpowENN rho eta := by rw [hinverseSqrt]
    _ = _ := by rw [hdeltaSplit]

private theorem capacity_log_factor_le
    {rho : ℝ} {regularity : ℕ} {L : ENNReal}
    (hlogs :
      (regularity : ENNReal) *
          ENNReal.ofReal (Real.log (1 / (256 * rho)) + 1) ≤
        2 ^ (10 : ℕ) * L ^ 11) :
    (160 * 264 * 23 * 32) *
          ((regularity : ENNReal) *
            ENNReal.ofReal (Real.log (1 / (256 * rho)) + 1)) ≤
      (160 * 264 * 23 * 32 * 2 ^ (10 : ℕ)) * L ^ 11 := by
  calc
    _ ≤ (160 * 264 * 23 * 32) * (2 ^ (10 : ℕ) * L ^ 11) :=
      mul_le_mul_left' hlogs _
    _ = _ := by ring

private theorem capacity_finish
    {sigma eta firstLossCeiling firstTerminalLoss capacityGain delta rho : ℝ}
    {A : ENNReal}
    (hdelta : 0 < delta) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hterminalNonneg : 0 ≤ firstTerminalLoss)
    (hcapacityGain :
      capacityGain = (eta - 2 * firstLossCeiling) / 2)
    (hbase : A ≤ Kakeya.realRpowENN rho (-capacityGain))
    (hrefinement :
      Kakeya.realRpowENN rho capacityGain ≤
        wz2PaperPureRefinementFraction rho 61) :
    A *
          (Kakeya.realRpowENN delta (sigma + 2 * firstTerminalLoss) *
            Kakeya.realRpowENN rho eta) ≤
      wz2PaperPureRefinementFraction rho 61 *
        Kakeya.realRpowENN rho (sigma + 2 * firstLossCeiling) *
        Kakeya.realRpowENN (delta / rho)
          (sigma + 2 * firstTerminalLoss) := by
  have hgainSplit :
      Kakeya.realRpowENN rho (-capacityGain) *
          Kakeya.realRpowENN rho eta =
        Kakeya.realRpowENN rho capacityGain *
          Kakeya.realRpowENN rho (2 * firstLossCeiling) := by
    rw [← realRpowENN_add hrho, ← realRpowENN_add hrho]
    congr 1
    rw [hcapacityGain]
    ring
  have hterminalMono :
      Kakeya.realRpowENN rho (2 * firstLossCeiling) ≤
        Kakeya.realRpowENN rho
          (2 * firstLossCeiling - 2 * firstTerminalLoss) :=
    realRpowENN_antitone hrho hrhoOne (by linarith)
  have hrhoCombine :
      Kakeya.realRpowENN rho (sigma + 2 * firstTerminalLoss) *
          Kakeya.realRpowENN rho
            (2 * firstLossCeiling - 2 * firstTerminalLoss) =
        Kakeya.realRpowENN rho (sigma + 2 * firstLossCeiling) := by
    rw [← realRpowENN_add hrho]
    congr 1
    ring
  have hquotient := capacity_realRpowENN_div_mul
    (delta := delta) (rho := rho)
    (exponent := sigma + 2 * firstTerminalLoss) hdelta hrho
  calc
    A *
          (Kakeya.realRpowENN delta (sigma + 2 * firstTerminalLoss) *
            Kakeya.realRpowENN rho eta) ≤
        Kakeya.realRpowENN rho (-capacityGain) *
          (Kakeya.realRpowENN delta (sigma + 2 * firstTerminalLoss) *
            Kakeya.realRpowENN rho eta) := mul_le_mul_right' hbase _
    _ = Kakeya.realRpowENN delta (sigma + 2 * firstTerminalLoss) *
          (Kakeya.realRpowENN rho capacityGain *
            Kakeya.realRpowENN rho (2 * firstLossCeiling)) := by
      rw [show Kakeya.realRpowENN rho (-capacityGain) *
              (Kakeya.realRpowENN delta (sigma + 2 * firstTerminalLoss) *
                Kakeya.realRpowENN rho eta) =
            Kakeya.realRpowENN delta (sigma + 2 * firstTerminalLoss) *
              (Kakeya.realRpowENN rho (-capacityGain) *
                Kakeya.realRpowENN rho eta) by ring, hgainSplit]
    _ ≤ Kakeya.realRpowENN delta (sigma + 2 * firstTerminalLoss) *
          (Kakeya.realRpowENN rho capacityGain *
            Kakeya.realRpowENN rho
              (2 * firstLossCeiling - 2 * firstTerminalLoss)) := by
      exact mul_le_mul_left' (mul_le_mul_left' hterminalMono _) _
    _ ≤ Kakeya.realRpowENN delta (sigma + 2 * firstTerminalLoss) *
          (wz2PaperPureRefinementFraction rho 61 *
            Kakeya.realRpowENN rho
              (2 * firstLossCeiling - 2 * firstTerminalLoss)) := by
      exact mul_le_mul_left' (mul_le_mul_right' hrefinement _) _
    _ = wz2PaperPureRefinementFraction rho 61 *
          (Kakeya.realRpowENN (delta / rho)
              (sigma + 2 * firstTerminalLoss) *
            (Kakeya.realRpowENN rho (sigma + 2 * firstTerminalLoss) *
              Kakeya.realRpowENN rho
                (2 * firstLossCeiling - 2 * firstTerminalLoss))) := by
      rw [← hquotient]
      ring
    _ = wz2PaperPureRefinementFraction rho 61 *
          (Kakeya.realRpowENN (delta / rho)
              (sigma + 2 * firstTerminalLoss) *
            Kakeya.realRpowENN rho (sigma + 2 * firstLossCeiling)) := by
      rw [hrhoCombine]
    _ = _ := by ring

/-- Family-independent capacity certificate for the source-popular common-bin
selection. -/
structure PureWZ2Node05V4RichSourcePopularCapacityThreshold
    (sigma sourceLossCeiling firstLossCeiling eta volumeLoss scaleLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  rho₀ : ℝ
  rho₀_pos : 0 < rho₀
  rho₀_le_one : rho₀ ≤ 1
  capacity_power :
    ∀ {inputLoss firstTerminalLoss delta rho : ℝ} {regularity : ℕ},
      0 ≤ inputLoss → inputLoss ≤ sourceLossCeiling →
      0 ≤ firstTerminalLoss → firstTerminalLoss ≤ firstLossCeiling →
      0 < delta → delta ≤ delta₀ → delta ≤ rho →
      0 < rho → rho ≤ rho₀ → 256 * rho ≤ 1 →
      rho ≤ Real.rpow delta scaleLoss →
      (regularity : ENNReal) ≤
        Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 →
      (regularity : ENNReal) *
          ((160 *
              pureWZ2Node05V4RichJointOccupiedBinBound
                sigma inputLoss delta rho *
              pureWZ2Node05V4RichJointHeightBinBound rho) *
            (Kakeya.realRpowENN rho (-1 / 2 + eta) *
              PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
                sigma inputLoss delta rho)) ≤
        wz2PaperPureRefinementFraction rho 61 *
          Kakeya.realRpowENN rho (sigma + 2 * firstLossCeiling) *
          Kakeya.realRpowENN (delta / rho)
            (sigma + 2 * firstTerminalLoss)
  graph_power :
    ∀ {rho : ℝ}, 0 < rho → rho ≤ rho₀ →
      (20 * 512 * 45 : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss) ≤
        (Kakeya.realRpowENN rho (-1 / 2 + eta) / 2) *
          Kakeya.realRpowENN (4 * rho)
            (3 / 2 + sigma / 2 + eta)
  joint_graph_power :
    ∀ {rho : ℝ}, 0 < rho → rho ≤ rho₀ →
      (80 * 512 * 45 : ENNReal) *
          pureWZ2Node05V4RichJointHeightBinBound rho *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss) ≤
        (Kakeya.realRpowENN rho (-1 / 2 + eta) / 2) *
          Kakeya.realRpowENN (4 * rho)
            (3 / 2 + sigma / 2 + eta)

/-- Select the common-bin capacity cutoff before the source family and runtime
scale. -/
theorem pureWZ2Node05V4Rich_sourcePopularCapacity_threshold
    {sigma sourceLossCeiling firstLossCeiling eta volumeLoss scaleLoss : ℝ}
    (hsigma : 0 < sigma)
    (hsourceLoss : 0 ≤ sourceLossCeiling)
    (hfirstLoss : 0 ≤ firstLossCeiling)
    (heta : 0 < eta)
    (hscaleLoss : 0 < scaleLoss)
    (hcapacityGap :
      2 * sourceLossCeiling + 2 * firstLossCeiling <
        scaleLoss * ((eta - 2 * firstLossCeiling) / 2))
    (hvolumeGap : 2 * eta < volumeLoss) :
    Nonempty (PureWZ2Node05V4RichSourcePopularCapacityThreshold
      sigma sourceLossCeiling firstLossCeiling eta volumeLoss scaleLoss) := by
  let capacityGain := (eta - 2 * firstLossCeiling) / 2
  have hcapacityGain : 0 < capacityGain := by
    have hpositive : 0 < scaleLoss * capacityGain :=
      (show 0 ≤ 2 * sourceLossCeiling + 2 * firstLossCeiling by positivity)
        |>.trans_lt (by simpa only [capacityGain] using hcapacityGap)
    exact pos_of_mul_pos_right hpositive hscaleLoss.le
  let capacityCost := 2 * sourceLossCeiling + 2 * firstLossCeiling
  have hcapacityCost : 0 ≤ capacityCost := by
    dsimp only [capacityCost]
    positivity
  let capacityLogLoss := (scaleLoss * capacityGain - capacityCost) / 2
  let capacityIntermediate := capacityCost + capacityLogLoss
  have hcapacityLogLoss : 0 < capacityLogLoss := by
    dsimp only [capacityLogLoss, capacityCost, capacityGain] at *
    linarith
  have hcapacityIntermediateNonneg : 0 ≤ capacityIntermediate := by
    dsimp only [capacityIntermediate]
    positivity
  have hcapacityIntermediateGap :
      capacityIntermediate < scaleLoss * capacityGain := by
    dsimp only [capacityIntermediate, capacityLogLoss, capacityCost,
      capacityGain]
    linarith
  let capacityCoefficient : ENNReal := 160 * 264 * 23 * 32 * 2 ^ (10 : ℕ)
  have hcapacityCoefficientTop : capacityCoefficient ≠ ⊤ := by
    dsimp only [capacityCoefficient]
    norm_num
  rcases exists_delta_log_absorbed_ennreal capacityCoefficient
      hcapacityCoefficientTop hcapacityLogLoss
      (show 0 < (11 : ℕ) by norm_num) with
    ⟨capacityDelta₀, hcapacityDelta₀, hcapacityDelta₀One,
      hcapacityAbsorb⟩
  rcases exists_scale_power_conversion
      (C := 1) (p := scaleLoss) (a := capacityIntermediate)
      (b := capacityGain) (by norm_num) hscaleLoss
      hcapacityIntermediateNonneg hcapacityIntermediateGap with
    ⟨capacityTransportDelta₀, hcapacityTransportDelta₀,
      hcapacityTransportDelta₀One, hcapacityTransport⟩
  rcases pureWZ2_refinementFraction_power_schedule 61 hcapacityGain with
    ⟨capacityRho₀, hcapacityRho₀, hcapacityRho₀One, hcapacityRefinement⟩
  let graphExponent := 1 + sigma / 2 + volumeLoss
  let graphTargetExponent := 1 + sigma / 2 + 2 * eta
  have hgraphExponent : 0 < graphExponent := by
    dsimp only [graphExponent]
    have hvolumePos : 0 < volumeLoss := by linarith
    linarith
  have hgraphGap : graphTargetExponent < graphExponent := by
    dsimp only [graphTargetExponent, graphExponent]
    linarith
  let graphCoefficient : ℝ :=
    2 * (20 * 512 * 45) * Real.rpow 256 graphExponent
  have hgraphCoefficient : 0 < graphCoefficient := by
    dsimp only [graphCoefficient]
    exact mul_pos (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) graphExponent)
  rcases exists_delta₀_const_mul_rpow_le graphCoefficient hgraphCoefficient
      graphTargetExponent graphExponent hgraphGap with
    ⟨graphRho₀, hgraphRho₀, hgraphRho₀One, hgraphAbsorb⟩
  let jointGraphGap := graphExponent - graphTargetExponent
  have hjointGraphGap : 0 < jointGraphGap := by
    dsimp only [jointGraphGap, graphExponent, graphTargetExponent]
    linarith
  let jointGraphCoefficient : ENNReal :=
    2 * (80 * 512 * 45 * 23 : ENNReal) *
      Kakeya.realRpowENN 256 graphExponent
  have hjointGraphCoefficientTop : jointGraphCoefficient ≠ ⊤ := by
    dsimp only [jointGraphCoefficient]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (by norm_num))
      (by simp [Kakeya.realRpowENN])
  rcases exists_delta_log_absorbed_ennreal jointGraphCoefficient
      hjointGraphCoefficientTop hjointGraphGap
      (show 0 < (1 : ℕ) by norm_num) with
    ⟨jointGraphRho₀, hjointGraphRho₀, hjointGraphRho₀One,
      hjointGraphAbsorb⟩
  let delta₀ := min capacityDelta₀ capacityTransportDelta₀
  let rho₀ := min capacityRho₀
    (min graphRho₀ (min jointGraphRho₀ (1 / 256 : ℝ)))
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min hcapacityDelta₀ hcapacityTransportDelta₀
    delta₀_le_one := (min_le_left _ _).trans hcapacityDelta₀One
    rho₀ := rho₀
    rho₀_pos := lt_min hcapacityRho₀
      (lt_min hgraphRho₀ (lt_min hjointGraphRho₀ (by norm_num)))
    rho₀_le_one := (min_le_left _ _).trans hcapacityRho₀One
    capacity_power := ?_
    graph_power := ?_
    joint_graph_power := ?_
  }⟩
  intro inputLoss firstTerminalLoss delta rho regularity
    hinput hinputCeiling hterminal _hterminalCeiling hdelta hdeltaSmall
    hdeltaRho hrho hrhoSmall _hgraphOne hrhoPower hregularity
  have hdeltaCapacity : delta ≤ capacityDelta₀ :=
    hdeltaSmall.trans (min_le_left _ _)
  have hdeltaTransport : delta ≤ capacityTransportDelta₀ :=
    hdeltaSmall.trans (min_le_right _ _)
  have hrhoCapacity : rho ≤ capacityRho₀ :=
    hrhoSmall.trans (min_le_left _ _)
  have hdeltaOne : delta ≤ 1 :=
    hdeltaCapacity.trans hcapacityDelta₀One
  have hrhoOne : rho ≤ 1 :=
    hrhoCapacity.trans hcapacityRho₀One
  have hlogRho :
      ENNReal.ofReal (Real.log (1 / (256 * rho)) + 1) ≤
        ENNReal.ofReal (1 + Real.log delta⁻¹) := by
    apply ENNReal.ofReal_mono
    have hinverse : 1 / (256 * rho) ≤ delta⁻¹ := by
      rw [one_div]
      exact inv_anti₀ hdelta (by nlinarith [hdeltaRho])
    linarith [Real.log_le_log (by positivity : 0 < 1 / (256 * rho)) hinverse]
  have hlogarithmic :
      Prop62PaperAudit.V4.logarithmicLoss delta ≤
        2 * ENNReal.ofReal (1 + Real.log delta⁻¹) := by
    simpa only [Prop62PaperAudit.V4.logarithmicLoss,
      show ENNReal.ofReal (2 * (1 + Real.log delta⁻¹)) =
          2 * ENNReal.ofReal (1 + Real.log delta⁻¹) by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num] using
      PureWZ2.proposition63_logarithmicLoss_le_two_logEnvelope
        hdelta hdeltaOne
  let L := ENNReal.ofReal (1 + Real.log delta⁻¹)
  have hlogs :
      (regularity : ENNReal) *
          ENNReal.ofReal (Real.log (1 / (256 * rho)) + 1) ≤
        2 ^ (10 : ℕ) * L ^ 11 := by
    have hlogarithmic' :
        Prop62PaperAudit.V4.logarithmicLoss delta ≤ 2 * L := by
      simpa only [L] using hlogarithmic
    have hregularity' :
        (regularity : ENNReal) ≤ (2 * L) ^ 10 :=
      hregularity.trans (pow_le_pow_left' hlogarithmic' 10)
    calc
      _ ≤ (2 * L) ^ 10 * L :=
        mul_le_mul hregularity' (by simpa only [L] using hlogRho) bot_le bot_le
      _ = 2 ^ (10 : ℕ) * L ^ 11 := by
        rw [mul_pow]
        ring
  have hactualCost :
      2 * inputLoss + 2 * firstTerminalLoss ≤ capacityCost := by
    dsimp only [capacityCost]
    linarith
  have hactualPower :
      Kakeya.realRpowENN delta
          (-(2 * inputLoss + 2 * firstTerminalLoss)) ≤
        Kakeya.realRpowENN delta (-capacityCost) :=
    realRpowENN_antitone hdelta hdeltaOne (by linarith)
  have hlogPower :
      capacityCoefficient * L ^ 11 ≤
        Kakeya.realRpowENN delta (-capacityLogLoss) :=
    hcapacityAbsorb delta hdelta hdeltaCapacity
  have hbase :
      capacityCoefficient * L ^ 11 *
          Kakeya.realRpowENN delta
            (-(2 * inputLoss + 2 * firstTerminalLoss)) ≤
        Kakeya.realRpowENN rho (-capacityGain) := by
    calc
      _ ≤ Kakeya.realRpowENN delta (-capacityLogLoss) *
            Kakeya.realRpowENN delta (-capacityCost) :=
        mul_le_mul hlogPower hactualPower bot_le bot_le
      _ = Kakeya.realRpowENN delta (-capacityIntermediate) := by
        rw [← realRpowENN_add hdelta]
        congr 1
        dsimp only [capacityIntermediate]
        ring
      _ ≤ Kakeya.realRpowENN rho (-capacityGain) :=
        hcapacityTransport delta rho hdelta hdeltaTransport hrho hrhoOne
          (by simpa using hrhoPower)
  have hrefinement :
      Kakeya.realRpowENN rho capacityGain ≤
        wz2PaperPureRefinementFraction rho 61 :=
    hcapacityRefinement rho hrho hrhoCapacity
  rw [pureWZ2Node05V4RichJointOccupiedBinBound,
    pureWZ2Node05V4RichJointHeightBinBound,
    capacity_lhs_normalize (firstTerminalLoss := firstTerminalLoss) hdelta hrho]
  have hlogFactor := capacity_log_factor_le hlogs
  have hcombined :
      (160 * 264 * 23 * 32) *
            ((regularity : ENNReal) *
              ENNReal.ofReal (Real.log (1 / (256 * rho)) + 1)) *
            Kakeya.realRpowENN delta
              (-(2 * inputLoss + 2 * firstTerminalLoss)) ≤
        capacityCoefficient * L ^ 11 *
          Kakeya.realRpowENN delta
            (-(2 * inputLoss + 2 * firstTerminalLoss)) := by
    dsimp only [capacityCoefficient]
    exact mul_le_mul_right' hlogFactor _
  rw [show
    (160 * 264 * 23 * 32) *
          ((regularity : ENNReal) *
            ENNReal.ofReal (Real.log (1 / (256 * rho)) + 1)) *
          (Kakeya.realRpowENN delta
              (-(2 * inputLoss + 2 * firstTerminalLoss)) *
            Kakeya.realRpowENN delta (sigma + 2 * firstTerminalLoss)) *
          Kakeya.realRpowENN rho eta =
      ((160 * 264 * 23 * 32) *
          ((regularity : ENNReal) *
            ENNReal.ofReal (Real.log (1 / (256 * rho)) + 1)) *
          Kakeya.realRpowENN delta
            (-(2 * inputLoss + 2 * firstTerminalLoss))) *
        (Kakeya.realRpowENN delta (sigma + 2 * firstTerminalLoss) *
          Kakeya.realRpowENN rho eta) by ring]
  exact capacity_finish (sigma := sigma) (eta := eta)
    (firstLossCeiling := firstLossCeiling)
    (firstTerminalLoss := firstTerminalLoss)
    (capacityGain := capacityGain) (delta := delta) (rho := rho)
    hdelta hrho hrhoOne hterminal rfl (hcombined.trans hbase) hrefinement
  · intro rho hrho hrhoSmall
    have hrhoGraph : rho ≤ graphRho₀ :=
      hrhoSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hraw := hgraphAbsorb rho hrho hrhoGraph
    have hleft :
        (2 * (20 * 512 * 45 : ENNReal)) *
            Kakeya.realRpowENN (256 * rho) graphExponent =
          ENNReal.ofReal graphCoefficient *
            Kakeya.realRpowENN rho graphExponent := by
      rw [realRpowENN_mul (by norm_num) hrho graphExponent]
      dsimp only [graphCoefficient]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2 * (20 * 512 * 45))]
      norm_num [Kakeya.realRpowENN]
      ring
    have hright :
        Kakeya.realRpowENN rho (-1 / 2 + eta) *
            Kakeya.realRpowENN (4 * rho)
              (3 / 2 + sigma / 2 + eta) =
          Kakeya.realRpowENN 4 (3 / 2 + sigma / 2 + eta) *
            Kakeya.realRpowENN rho graphTargetExponent := by
      rw [realRpowENN_mul (by norm_num) hrho
        (3 / 2 + sigma / 2 + eta)]
      rw [show Kakeya.realRpowENN rho (-1 / 2 + eta) *
              (Kakeya.realRpowENN 4 (3 / 2 + sigma / 2 + eta) *
                Kakeya.realRpowENN rho (3 / 2 + sigma / 2 + eta)) =
            Kakeya.realRpowENN 4 (3 / 2 + sigma / 2 + eta) *
              (Kakeya.realRpowENN rho (-1 / 2 + eta) *
                Kakeya.realRpowENN rho (3 / 2 + sigma / 2 + eta)) by ring]
      rw [← realRpowENN_add hrho]
      congr 1
      dsimp only [graphTargetExponent]
      ring
    have hfull :
        (2 * (20 * 512 * 45 : ENNReal)) *
              Kakeya.realRpowENN (256 * rho)
                (1 + sigma / 2 + volumeLoss) ≤
          Kakeya.realRpowENN rho (-1 / 2 + eta) *
            Kakeya.realRpowENN (4 * rho)
              (3 / 2 + sigma / 2 + eta) := by
      rw [show 1 + sigma / 2 + volumeLoss = graphExponent by rfl, hleft, hright]
      exact hraw.trans <| le_mul_of_one_le_left (by positivity) <| by
        apply ENNReal.one_le_ofReal.mpr
        exact Real.one_le_rpow (by norm_num) (by linarith)
    have htwo : (2 : ENNReal) ≠ 0 := by norm_num
    have htwoTop : (2 : ENNReal) ≠ ⊤ := by norm_num
    refine (ENNReal.mul_le_mul_iff_right
      (a := (2 : ENNReal))
      (b := (20 * 512 * 45 : ENNReal) *
        Kakeya.realRpowENN (256 * rho)
          (1 + sigma / 2 + volumeLoss))
      (c := (Kakeya.realRpowENN rho (-1 / 2 + eta) / 2) *
        Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + eta)) htwo htwoTop).mp ?_
    calc
      2 * ((20 * 512 * 45 : ENNReal) *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss)) =
          (2 * (20 * 512 * 45 : ENNReal)) *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss) := by ring
      _ ≤ Kakeya.realRpowENN rho (-1 / 2 + eta) *
          Kakeya.realRpowENN (4 * rho)
            (3 / 2 + sigma / 2 + eta) := hfull
      _ = 2 * ((Kakeya.realRpowENN rho (-1 / 2 + eta) / 2) *
          Kakeya.realRpowENN (4 * rho)
            (3 / 2 + sigma / 2 + eta)) := by
        rw [show 2 * ((Kakeya.realRpowENN rho (-1 / 2 + eta) / 2) *
              Kakeya.realRpowENN (4 * rho)
                (3 / 2 + sigma / 2 + eta)) =
            (Kakeya.realRpowENN rho (-1 / 2 + eta) / 2 * 2) *
              Kakeya.realRpowENN (4 * rho)
                (3 / 2 + sigma / 2 + eta) by ring,
          ENNReal.div_mul_cancel htwo htwoTop]
  · intro rho hrho hrhoSmall
    have hrhoJoint : rho ≤ jointGraphRho₀ :=
      hrhoSmall.trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
    have hrhoOne : rho ≤ 1 :=
      hrhoJoint.trans hjointGraphRho₀One
    let L : ENNReal := ENNReal.ofReal (1 + Real.log rho⁻¹)
    have hlog :
        ENNReal.ofReal (Real.log (1 / (256 * rho)) + 1) ≤ L := by
      dsimp only [L]
      apply ENNReal.ofReal_mono
      have hinverse : 1 / (256 * rho) ≤ rho⁻¹ := by
        rw [one_div]
        exact inv_anti₀ hrho (by nlinarith)
      linarith [Real.log_le_log (by positivity : 0 < 1 / (256 * rho)) hinverse]
    have habsorb :
        jointGraphCoefficient * L ≤
          Kakeya.realRpowENN rho (-jointGraphGap) := by
      simpa only [pow_one] using
        hjointGraphAbsorb rho hrho hrhoJoint
    have hgraphScale :
        Kakeya.realRpowENN (256 * rho) graphExponent =
          Kakeya.realRpowENN 256 graphExponent *
            Kakeya.realRpowENN rho graphExponent :=
      realRpowENN_mul (by norm_num) hrho graphExponent
    have htargetPower :
        Kakeya.realRpowENN rho (-jointGraphGap) *
            Kakeya.realRpowENN rho graphExponent =
          Kakeya.realRpowENN rho graphTargetExponent := by
      rw [← realRpowENN_add hrho]
      congr 1
      dsimp only [jointGraphGap]
      ring
    have hright :
        Kakeya.realRpowENN rho (-1 / 2 + eta) *
            Kakeya.realRpowENN (4 * rho)
              (3 / 2 + sigma / 2 + eta) =
          Kakeya.realRpowENN 4 (3 / 2 + sigma / 2 + eta) *
            Kakeya.realRpowENN rho graphTargetExponent := by
      rw [realRpowENN_mul (by norm_num) hrho
        (3 / 2 + sigma / 2 + eta)]
      rw [show Kakeya.realRpowENN rho (-1 / 2 + eta) *
              (Kakeya.realRpowENN 4 (3 / 2 + sigma / 2 + eta) *
                Kakeya.realRpowENN rho (3 / 2 + sigma / 2 + eta)) =
            Kakeya.realRpowENN 4 (3 / 2 + sigma / 2 + eta) *
              (Kakeya.realRpowENN rho (-1 / 2 + eta) *
                Kakeya.realRpowENN rho (3 / 2 + sigma / 2 + eta)) by ring]
      rw [← realRpowENN_add hrho]
      congr 1
      dsimp only [graphTargetExponent]
      ring
    have hfull :
        (2 : ENNReal) *
            ((80 * 512 * 45 : ENNReal) *
              pureWZ2Node05V4RichJointHeightBinBound rho *
              Kakeya.realRpowENN (256 * rho) graphExponent) ≤
          Kakeya.realRpowENN rho (-1 / 2 + eta) *
            Kakeya.realRpowENN (4 * rho)
              (3 / 2 + sigma / 2 + eta) := by
      rw [pureWZ2Node05V4RichJointHeightBinBound, hgraphScale]
      calc
        2 * ((80 * 512 * 45 : ENNReal) *
              (23 * ENNReal.ofReal
                (Real.log (1 / (256 * rho)) + 1)) *
              (Kakeya.realRpowENN 256 graphExponent *
                Kakeya.realRpowENN rho graphExponent)) =
            jointGraphCoefficient *
              ENNReal.ofReal (Real.log (1 / (256 * rho)) + 1) *
              Kakeya.realRpowENN rho graphExponent := by
          dsimp only [jointGraphCoefficient]
          ring
        _ ≤ jointGraphCoefficient * L *
              Kakeya.realRpowENN rho graphExponent := by gcongr
        _ ≤ Kakeya.realRpowENN rho (-jointGraphGap) *
              Kakeya.realRpowENN rho graphExponent := by gcongr
        _ = Kakeya.realRpowENN rho graphTargetExponent := htargetPower
        _ ≤ Kakeya.realRpowENN 4 (3 / 2 + sigma / 2 + eta) *
              Kakeya.realRpowENN rho graphTargetExponent := by
          exact le_mul_of_one_le_left (by positivity) <| by
            apply ENNReal.one_le_ofReal.mpr
            exact Real.one_le_rpow (by norm_num) (by linarith)
        _ = _ := hright.symm
    have htwo : (2 : ENNReal) ≠ 0 := by norm_num
    have htwoTop : (2 : ENNReal) ≠ ⊤ := by norm_num
    refine (ENNReal.mul_le_mul_iff_right htwo htwoTop).mp ?_
    calc
      2 * ((80 * 512 * 45 : ENNReal) *
            pureWZ2Node05V4RichJointHeightBinBound rho *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss)) ≤
          Kakeya.realRpowENN rho (-1 / 2 + eta) *
            Kakeya.realRpowENN (4 * rho)
              (3 / 2 + sigma / 2 + eta) := by
        simpa only [graphExponent] using hfull
      _ = 2 * ((Kakeya.realRpowENN rho (-1 / 2 + eta) / 2) *
          Kakeya.realRpowENN (4 * rho)
            (3 / 2 + sigma / 2 + eta)) := by
        rw [show 2 * ((Kakeya.realRpowENN rho (-1 / 2 + eta) / 2) *
              Kakeya.realRpowENN (4 * rho)
                (3 / 2 + sigma / 2 + eta)) =
            (Kakeya.realRpowENN rho (-1 / 2 + eta) / 2 * 2) *
              Kakeya.realRpowENN (4 * rho)
                (3 / 2 + sigma / 2 + eta) by ring,
          ENNReal.div_mul_cancel htwo htwoTop]

namespace PureWZ2Node05V4RichTwoScaleCellPullbackData

/-- At runtime, the preselected capacity power and the exact pullback volume
receipt cancel the positive finite regularity cost.  The resulting inequality
is precisely the cell-count hypothesis for a uniform
`rho ^ (-1/2 + eta)` rich-bin multiplicity. -/
theorem sourcePopular_commonBin_capacity
    {capability : PureWZ2PropStickyCapability}
    {sigma sourceLossCeiling firstLossCeiling eta volumeLoss scaleLoss
      inputLoss delta rho stickyLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (threshold : PureWZ2Node05V4RichSourcePopularCapacityThreshold
      sigma sourceLossCeiling firstLossCeiling eta volumeLoss scaleLoss)
    (hfirstCeiling : schedule.firstOutputLoss = firstLossCeiling)
    (hinputNonneg : 0 ≤ inputLoss)
    (hinputCeiling : inputLoss ≤ sourceLossCeiling)
    (hdeltaSmall : delta ≤ threshold.delta₀)
    (hrhoSmall : rho ≤ threshold.rho₀)
    (hgraphOne : 256 * rho ≤ 1)
    (hrhoPower : rho ≤ Real.rpow delta scaleLoss)
    (hrhoSmallTwelve : rhoRequested.1 ≤ 1 / 12) :
    Kakeya.realRpowENN rho (-1 / 2 + eta) *
        PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
          sigma inputLoss delta rho ≤
      pureWZ2Node05V4RichJointCommonBinThreshold pullback := by
  let regularity : ENNReal := twoScale.first.fourDegreeReceipts.regularity
  let denom : ENNReal :=
    160 * pureWZ2Node05V4RichJointOccupiedBinBound
      sigma inputLoss delta rho *
      pureWZ2Node05V4RichJointHeightBinBound rho
  let desired : ENNReal :=
    Kakeya.realRpowENN rho (-1 / 2 + eta) *
      PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
        sigma inputLoss delta rho
  have hdelta : 0 < delta := current.grain.extremal.delta_pos
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hdeltaRho : delta ≤ rho := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.1
  have hregularity :
      (twoScale.first.fourDegreeReceipts.regularity : ENNReal) ≤
        Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 :=
    twoScale.first.rich.terminal_regularity_bound
  have hcapacity := threshold.capacity_power hinputNonneg hinputCeiling
    twoScale.first.rich.terminalLoss_pos.le
    (twoScale.first.rich.terminalLoss_le_output.trans_eq hfirstCeiling)
    hdelta hdeltaSmall hdeltaRho hrho hrhoSmall hgraphOne hrhoPower hregularity
  have hsource := pullback.source_volume_relative_lower hrhoSmallTwelve
  have hcapacity' :
      regularity * (denom * desired) ≤
        wz2PaperPureRefinementFraction rho 61 *
          Kakeya.realRpowENN rho (sigma + 2 * firstLossCeiling) *
          Kakeya.realRpowENN (delta / rho)
            (sigma + 2 * twoScale.first.rich.terminalLoss) := by
    simpa only [regularity, denom, desired, hfirstCeiling,
      pullback.rhoRequested_eq] using hcapacity
  have hsource' :
      wz2PaperPureRefinementFraction rho 61 *
            Kakeya.realRpowENN rho (sigma + 2 * firstLossCeiling) *
            Kakeya.realRpowENN (delta / rho)
              (sigma + 2 * twoScale.first.rich.terminalLoss) ≤
        regularity * volume pullback.shading.union := by
    simpa only [regularity, hfirstCeiling, pullback.rhoRequested_eq] using hsource
  have hscaled : regularity * (denom * desired) ≤
      regularity * volume pullback.shading.union := by
    exact hcapacity'.trans hsource'
  have hregularityPos : 0 < regularity := by
    dsimp only [regularity]
    exact_mod_cast twoScale.first.fourDegreeReceipts.regularity_pos
  have hregularityTop : regularity ≠ ⊤ := by
    dsimp only [regularity]
    exact ENNReal.natCast_ne_top _
  have hcancelled : denom * desired ≤ volume pullback.shading.union :=
    (ENNReal.mul_le_mul_iff_right hregularityPos.ne' hregularityTop).mp <| by
      simpa [mul_comm] using hscaled
  have hdenomPos : 0 < denom := by
    dsimp only [denom]
    exact ENNReal.mul_pos
      (ENNReal.mul_pos (by norm_num)
        (jointOccupiedBinBound_pos (sigma := sigma) (inputLoss := inputLoss)
          hdelta hrho).ne').ne'
      (jointHeightBinBound_pos hrho hgraphOne).ne'
  have hdenomTop : denom ≠ ⊤ := by
    dsimp only [denom]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num)
        (jointOccupiedBinBound_ne_top (sigma := sigma)
          (inputLoss := inputLoss) (delta := delta) (rho := rho)))
      (jointHeightBinBound_ne_top (rho := rho))
  unfold pureWZ2Node05V4RichJointCommonBinThreshold
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl hdenomPos.ne') (Or.inl hdenomTop)).2
  simpa only [desired, denom, mul_comm] using hcancelled

end PureWZ2Node05V4RichTwoScaleCellPullbackData

end Kakeya.Assouad

end
