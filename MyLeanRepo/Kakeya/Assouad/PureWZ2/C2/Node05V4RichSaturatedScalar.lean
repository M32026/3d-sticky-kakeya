import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSaturatedAnalytic
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.ExponentArithmetic

/-!
# Pre-runtime power bounds for the saturated Node-5 graph

These bounds depend only on frozen losses and absolute constants.  Runtime
families, graph residues, and selected parents do not occur in the threshold.
-/

noncomputable section

namespace Kakeya.Assouad

private theorem saturated_realRpowENN_div_mul
    {delta rho exponent : ℝ} (hdelta : 0 < delta) (hrho : 0 < rho) :
    Kakeya.realRpowENN (delta / rho) exponent *
        Kakeya.realRpowENN rho exponent =
      Kakeya.realRpowENN delta exponent := by
  have hmul := realRpowENN_mul (div_pos hdelta hrho) hrho exponent
  rw [show delta / rho * rho = delta by field_simp [hrho.ne']] at hmul
  exact hmul.symm

/-- Exact cancellation of the main `sigma` powers in the same-height
saturation bound. -/
theorem pureWZ2Node05V4Rich_saturation_power_of_normalized_budget
    {sigma inputLoss delta rho firstLoss secondLoss eta : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hbudget :
      (32 * Kakeya.realRpowENN 4
          (3 / 2 + sigma / 2 + eta)) *
          Kakeya.realRpowENN delta (-(inputLoss + 2 * firstLoss)) *
          Kakeya.realRpowENN rho
            (eta + 2 * firstLoss - secondLoss) ≤ 1) :
    ((32 * Kakeya.realRpowENN delta (-inputLoss) *
            Kakeya.realRpowENN delta sigma *
            Kakeya.realRpowENN rho (2 - sigma)) *
          ENNReal.ofReal rho) *
          Kakeya.realRpowENN (4 * rho)
            (3 / 2 + sigma / 2 + eta) ≤
      (Kakeya.realRpowENN rho 3 *
            Kakeya.realRpowENN (delta / rho)
              (sigma + 2 * firstLoss)) *
          Kakeya.realRpowENN rho
            (3 / 2 + sigma / 2 + secondLoss) := by
  let saturationExponent := 3 / 2 + sigma / 2 + eta
  let leftRhoExponent := 9 / 2 - sigma / 2 + eta
  let rightRhoExponent :=
    9 / 2 - sigma / 2 - 2 * firstLoss + secondLoss
  let gain := eta + 2 * firstLoss - secondLoss
  have hdeltaSplit :
      Kakeya.realRpowENN delta (-(inputLoss + 2 * firstLoss)) *
          Kakeya.realRpowENN delta (sigma + 2 * firstLoss) =
        Kakeya.realRpowENN delta (sigma - inputLoss) := by
    rw [← realRpowENN_add hdelta]
    congr 1
    ring
  have hrhoSplit :
      Kakeya.realRpowENN rho gain *
          Kakeya.realRpowENN rho rightRhoExponent =
        Kakeya.realRpowENN rho leftRhoExponent := by
    rw [← realRpowENN_add hrho]
    congr 1
    dsimp only [gain, rightRhoExponent, leftRhoExponent]
    ring
  have hleft :
      ((32 * Kakeya.realRpowENN delta (-inputLoss) *
              Kakeya.realRpowENN delta sigma *
              Kakeya.realRpowENN rho (2 - sigma)) *
            ENNReal.ofReal rho) *
            Kakeya.realRpowENN (4 * rho) saturationExponent =
        (32 * Kakeya.realRpowENN 4 saturationExponent) *
          Kakeya.realRpowENN delta (sigma - inputLoss) *
          Kakeya.realRpowENN rho leftRhoExponent := by
    have hrhoOne : ENNReal.ofReal rho = Kakeya.realRpowENN rho 1 := by
      simp [Kakeya.realRpowENN, Real.rpow_one]
    have hdeltaMain :
        Kakeya.realRpowENN delta (-inputLoss) *
            Kakeya.realRpowENN delta sigma =
          Kakeya.realRpowENN delta (sigma - inputLoss) := by
      rw [← realRpowENN_add hdelta]
      congr 1
      ring
    have hrhoMain :
        Kakeya.realRpowENN rho (2 - sigma) *
            Kakeya.realRpowENN rho 1 *
            Kakeya.realRpowENN rho saturationExponent =
          Kakeya.realRpowENN rho leftRhoExponent := by
      rw [← realRpowENN_add hrho, ← realRpowENN_add hrho]
      congr 1
      dsimp only [leftRhoExponent, saturationExponent]
      ring
    rw [realRpowENN_mul (by norm_num) hrho saturationExponent, hrhoOne]
    calc
      32 * Kakeya.realRpowENN delta (-inputLoss) *
            Kakeya.realRpowENN delta sigma *
            Kakeya.realRpowENN rho (2 - sigma) *
            Kakeya.realRpowENN rho 1 *
            (Kakeya.realRpowENN 4 saturationExponent *
              Kakeya.realRpowENN rho saturationExponent) =
          (32 * Kakeya.realRpowENN 4 saturationExponent) *
            (Kakeya.realRpowENN delta (-inputLoss) *
              Kakeya.realRpowENN delta sigma) *
            (Kakeya.realRpowENN rho (2 - sigma) *
              Kakeya.realRpowENN rho 1 *
              Kakeya.realRpowENN rho saturationExponent) := by ring
      _ = _ := by rw [hdeltaMain, hrhoMain]
  have hright :
      (Kakeya.realRpowENN rho 3 *
            Kakeya.realRpowENN (delta / rho)
              (sigma + 2 * firstLoss)) *
          Kakeya.realRpowENN rho
            (3 / 2 + sigma / 2 + secondLoss) =
        Kakeya.realRpowENN delta (sigma + 2 * firstLoss) *
          Kakeya.realRpowENN rho rightRhoExponent := by
    let exponent := sigma + 2 * firstLoss
    have hsplit :
        Kakeya.realRpowENN rho 3 =
          Kakeya.realRpowENN rho exponent *
            Kakeya.realRpowENN rho (3 - exponent) := by
      rw [← realRpowENN_add hrho]
      congr 1
      ring
    rw [hsplit]
    have hquotient := saturated_realRpowENN_div_mul
      (delta := delta) (rho := rho) (exponent := exponent) hdelta hrho
    have hrhoRest :
        Kakeya.realRpowENN rho (3 - exponent) *
            Kakeya.realRpowENN rho
              (3 / 2 + sigma / 2 + secondLoss) =
          Kakeya.realRpowENN rho rightRhoExponent := by
      rw [← realRpowENN_add hrho]
      congr 1
      dsimp only [exponent, rightRhoExponent]
      ring
    calc
      (Kakeya.realRpowENN rho exponent *
            Kakeya.realRpowENN rho (3 - exponent) *
            Kakeya.realRpowENN (delta / rho) exponent) *
          Kakeya.realRpowENN rho
            (3 / 2 + sigma / 2 + secondLoss) =
        (Kakeya.realRpowENN (delta / rho) exponent *
            Kakeya.realRpowENN rho exponent) *
          (Kakeya.realRpowENN rho (3 - exponent) *
            Kakeya.realRpowENN rho
              (3 / 2 + sigma / 2 + secondLoss)) := by ring
      _ = Kakeya.realRpowENN delta exponent *
          Kakeya.realRpowENN rho rightRhoExponent := by
            rw [hquotient, hrhoRest]
  rw [hleft, hright]
  have hfactorization :
      ((32 * Kakeya.realRpowENN 4 saturationExponent) *
          Kakeya.realRpowENN delta (-(inputLoss + 2 * firstLoss)) *
          Kakeya.realRpowENN rho gain) *
        (Kakeya.realRpowENN delta (sigma + 2 * firstLoss) *
          Kakeya.realRpowENN rho rightRhoExponent) =
      (32 * Kakeya.realRpowENN 4 saturationExponent) *
          Kakeya.realRpowENN delta (sigma - inputLoss) *
          Kakeya.realRpowENN rho leftRhoExponent := by
    calc
      _ = (32 * Kakeya.realRpowENN 4 saturationExponent) *
            (Kakeya.realRpowENN delta
                (-(inputLoss + 2 * firstLoss)) *
              Kakeya.realRpowENN delta (sigma + 2 * firstLoss)) *
            (Kakeya.realRpowENN rho gain *
              Kakeya.realRpowENN rho rightRhoExponent) := by ac_rfl
      _ = _ := by rw [hdeltaSplit, hrhoSplit]
  calc
    (32 * Kakeya.realRpowENN 4 saturationExponent) *
          Kakeya.realRpowENN delta (sigma - inputLoss) *
          Kakeya.realRpowENN rho leftRhoExponent =
      ((32 * Kakeya.realRpowENN 4 saturationExponent) *
          Kakeya.realRpowENN delta (-(inputLoss + 2 * firstLoss)) *
          Kakeya.realRpowENN rho gain) *
        (Kakeya.realRpowENN delta (sigma + 2 * firstLoss) *
          Kakeya.realRpowENN rho rightRhoExponent) := by
            exact hfactorization.symm
    _ ≤ 1 *
        (Kakeya.realRpowENN delta (sigma + 2 * firstLoss) *
          Kakeya.realRpowENN rho rightRhoExponent) := by gcongr
    _ = _ := by simp

structure PureWZ2Node05V4RichSaturatedGraphThreshold
    (sigma sourceLossCeiling firstLossCeiling secondLossCeiling eta
      neighborhoodLoss volumeLoss
      constantLoss sourceCostLoss scaleLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  rho₀ : ℝ
  rho₀_pos : 0 < rho₀
  rho₀_le_one : rho₀ ≤ 1
  local_power :
    ∀ {inputLoss delta rho : ℝ},
      0 ≤ inputLoss → inputLoss ≤ sourceLossCeiling →
      0 < delta → delta ≤ delta₀ →
      0 < rho → 4 * rho ≤ 1 →
      rho ≤ Real.rpow delta scaleLoss →
        160 * Kakeya.realRpowENN delta (-inputLoss) ≤
          Kakeya.realRpowENN (4 * rho) (-eta)
  saturation_power :
    ∀ {inputLoss firstLoss secondLoss delta rho : ℝ},
      0 ≤ inputLoss → inputLoss ≤ sourceLossCeiling →
      0 ≤ firstLoss → firstLoss ≤ firstLossCeiling →
      secondLoss ≤ secondLossCeiling →
      0 < delta → delta ≤ delta₀ →
      0 < rho → rho ≤ rho₀ → rho ≤ Real.rpow delta scaleLoss →
      ((32 * Kakeya.realRpowENN delta (-inputLoss) *
            Kakeya.realRpowENN delta sigma *
            Kakeya.realRpowENN rho (2 - sigma)) *
          ENNReal.ofReal rho) *
          Kakeya.realRpowENN (4 * rho)
            (3 / 2 + sigma / 2 + eta) ≤
        (Kakeya.realRpowENN rho 3 *
            Kakeya.realRpowENN (delta / rho)
              (sigma + 2 * firstLoss)) *
          Kakeya.realRpowENN rho
            (3 / 2 + sigma / 2 + secondLoss)
  constant_power :
    ∀ {inputLoss delta rho : ℝ},
      0 ≤ inputLoss → inputLoss ≤ sourceLossCeiling →
      0 < delta → delta ≤ delta₀ →
      0 < rho → 256 * rho ≤ 1 →
      rho ≤ Real.rpow delta scaleLoss →
        (160 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
          Real.rpow (256 * rho) (-constantLoss)
  volume_power :
    ∀ {rho : ℝ}, 0 < rho → rho ≤ rho₀ →
      Kakeya.realRpowENN (256 * rho)
          (1 + sigma / 2 + volumeLoss) ≤
        Kakeya.realRpowENN rho (-1 / 2 + neighborhoodLoss) *
          Kakeya.realRpowENN (4 * rho)
            (3 / 2 + sigma / 2 + eta)
  source_cost :
    ∀ {rho : ℝ}, 0 < rho → rho ≤ rho₀ →
      Kakeya.realRpowENN rho (-eta) ≤
        Kakeya.realRpowENN (wz1Lemma23Theorem22Scale (256 * rho))
          (-sourceCostLoss)

/-- Select all graph-side power bounds before the runtime source and scale. -/
theorem pureWZ2Node05V4Rich_saturatedGraph_threshold
    {sigma sourceLossCeiling firstLossCeiling secondLossCeiling eta
      neighborhoodLoss volumeLoss
      constantLoss sourceCostLoss scaleLoss : ℝ}
    (hsigma : 0 < sigma)
    (hsourceLoss : 0 ≤ sourceLossCeiling)
    (hfirstLoss : 0 ≤ firstLossCeiling)
    (hsecondLoss : 0 ≤ secondLossCeiling)
    (heta : 0 < eta)
    (hneighborhoodLoss : 0 ≤ neighborhoodLoss)
    (hscaleLoss : 0 < scaleLoss)
    (hconstantLoss : 0 < constantLoss)
    (hconstantGap : sourceLossCeiling < scaleLoss * constantLoss)
    (hsecondEta : secondLossCeiling < eta)
    (hsaturationGap :
      sourceLossCeiling + 2 * firstLossCeiling <
        scaleLoss * (eta - secondLossCeiling))
    (hvolumeGap : neighborhoodLoss + eta < volumeLoss)
    (_hsourceCostLoss : 0 < sourceCostLoss)
    (hsourceCostGap : eta < (1 / 2 : ℝ) * sourceCostLoss) :
    Nonempty (PureWZ2Node05V4RichSaturatedGraphThreshold
      sigma sourceLossCeiling firstLossCeiling secondLossCeiling eta
        neighborhoodLoss volumeLoss
        constantLoss sourceCostLoss scaleLoss) := by
  let saturationConstant : ENNReal :=
    32 * Kakeya.realRpowENN 4 (3 / 2 + sigma / 2 + eta)
  let saturationCost := sourceLossCeiling + 2 * firstLossCeiling
  let saturationGain := eta - secondLossCeiling
  have hsaturationCost : 0 ≤ saturationCost := by
    dsimp only [saturationCost]
    positivity
  have hsaturationGain : 0 < saturationGain := by
    dsimp only [saturationGain]
    linarith
  let saturationIntermediate :=
    (saturationCost + scaleLoss * saturationGain) / 2
  have hsaturationIntermediateLeft :
      saturationCost < saturationIntermediate := by
    dsimp only [saturationIntermediate, saturationCost, saturationGain] at *
    linarith
  have hsaturationIntermediateNonneg : 0 ≤ saturationIntermediate := by
    dsimp only [saturationIntermediate]
    positivity
  have hsaturationIntermediateRight :
      saturationIntermediate < scaleLoss * saturationGain := by
    dsimp only [saturationIntermediate, saturationCost, saturationGain] at *
    linarith
  have hsaturationConstantTop : saturationConstant ≠ ⊤ := by
    dsimp only [saturationConstant]
    exact ENNReal.mul_ne_top (by norm_num) (by simp [Kakeya.realRpowENN])
  rcases exists_scale_absorb_constant saturationConstant
      hsaturationConstantTop hsaturationCost hsaturationIntermediateLeft with
    ⟨saturationConstantDelta₀, hsaturationConstantDelta₀,
      hsaturationConstantDelta₀One, hsaturationConstantAbsorb⟩
  rcases exists_scale_power_conversion
      (C := 1) (p := scaleLoss) (a := saturationIntermediate)
      (b := saturationGain) (by norm_num) hscaleLoss
      hsaturationIntermediateNonneg hsaturationIntermediateRight with
    ⟨saturationTransportDelta₀, hsaturationTransportDelta₀,
      hsaturationTransportDelta₀One, hsaturationTransport⟩
  have hlocalGap : sourceLossCeiling < scaleLoss * eta := by
    have hgainLe :
        scaleLoss * (eta - secondLossCeiling) ≤ scaleLoss * eta := by
      nlinarith
    linarith
  let localIntermediate := (sourceLossCeiling + scaleLoss * eta) / 2
  have hsourceLocalIntermediate : sourceLossCeiling < localIntermediate := by
    dsimp only [localIntermediate]
    linarith
  have hlocalIntermediateNonneg : 0 ≤ localIntermediate := by
    dsimp only [localIntermediate]
    positivity
  have hlocalIntermediateGap : localIntermediate < scaleLoss * eta := by
    dsimp only [localIntermediate]
    linarith
  rcases exists_scale_absorb_constant (160 : ENNReal) (by norm_num)
      hsourceLoss hsourceLocalIntermediate with
    ⟨localConstantDelta₀, hlocalConstantDelta₀, hlocalConstantDelta₀One,
      hlocalConstantAbsorb⟩
  rcases exists_scale_power_conversion
      (C := 4) (p := scaleLoss) (a := localIntermediate) (b := eta)
      (by norm_num) hscaleLoss hlocalIntermediateNonneg hlocalIntermediateGap with
    ⟨localTransportDelta₀, hlocalTransportDelta₀, hlocalTransportDelta₀One,
      hlocalTransport⟩
  let constantIntermediate :=
    (sourceLossCeiling + scaleLoss * constantLoss) / 2
  have hsourceIntermediate : sourceLossCeiling < constantIntermediate := by
    dsimp only [constantIntermediate]
    linarith
  have hconstantIntermediateNonneg : 0 ≤ constantIntermediate := by
    dsimp only [constantIntermediate]
    positivity
  have hconstantIntermediateGap :
      constantIntermediate < scaleLoss * constantLoss := by
    dsimp only [constantIntermediate]
    linarith
  rcases exists_scale_absorb_constant (160 : ENNReal) (by norm_num)
      hsourceLoss hsourceIntermediate with
    ⟨constantDelta₀, hconstantDelta₀, hconstantDelta₀One,
      hconstantAbsorb⟩
  rcases exists_scale_power_conversion
      (C := 256) (p := scaleLoss) (a := constantIntermediate)
      (b := constantLoss) (by norm_num) hscaleLoss
      hconstantIntermediateNonneg hconstantIntermediateGap with
    ⟨transportDelta₀, htransportDelta₀, htransportDelta₀One,
      hconstantTransport⟩
  let graphExponent := 1 + sigma / 2 + volumeLoss
  let saturationExponent := 3 / 2 + sigma / 2 + eta
  let volumeTargetExponent :=
    1 + sigma / 2 + neighborhoodLoss + eta
  have hgraphExponent : 0 < graphExponent := by
    dsimp only [graphExponent]
    nlinarith
  have hsaturationExponent : 0 < saturationExponent := by
    dsimp only [saturationExponent]
    nlinarith
  have hvolumeExponentGap : volumeTargetExponent < graphExponent := by
    dsimp only [volumeTargetExponent, graphExponent]
    linarith
  rcases exists_delta₀_const_mul_rpow_le
      (Real.rpow 256 graphExponent)
      (Real.rpow_pos_of_pos (by norm_num) graphExponent)
      volumeTargetExponent graphExponent hvolumeExponentGap with
    ⟨volumeRho₀, hvolumeRho₀, hvolumeRho₀One, hvolumeAbsorb⟩
  rcases exists_scale_power_conversion
      (C := 2) (p := (1 / 2 : ℝ)) (a := eta) (b := sourceCostLoss)
      (by norm_num) (by norm_num) heta.le hsourceCostGap with
    ⟨sourceCostRho₀, hsourceCostRho₀, hsourceCostRho₀One,
      hsourceCostConvert⟩
  let delta₀ := min saturationConstantDelta₀
    (min saturationTransportDelta₀
      (min localConstantDelta₀
        (min localTransportDelta₀ (min constantDelta₀ transportDelta₀))))
  let rho₀ := min volumeRho₀ (min sourceCostRho₀ (1 / 256 : ℝ))
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min hsaturationConstantDelta₀
      (lt_min hsaturationTransportDelta₀
        (lt_min hlocalConstantDelta₀
          (lt_min hlocalTransportDelta₀
            (lt_min hconstantDelta₀ htransportDelta₀))))
    delta₀_le_one := (min_le_left _ _).trans hsaturationConstantDelta₀One
    rho₀ := rho₀
    rho₀_pos := lt_min hvolumeRho₀
      (lt_min hsourceCostRho₀ (by norm_num))
    rho₀_le_one := (min_le_left _ _).trans hvolumeRho₀One
    local_power := ?_
    saturation_power := ?_
    constant_power := ?_
    volume_power := ?_
    source_cost := ?_
  }⟩
  · intro inputLoss delta rho hinput hinputCeiling hdelta hdeltaSmall
      hrho hfourRho hrhoPower
    have hdeltaConstant : delta ≤ localConstantDelta₀ :=
      hdeltaSmall.trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
    have hdeltaTransport : delta ≤ localTransportDelta₀ :=
      hdeltaSmall.trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))
    have hdeltaOne : delta ≤ 1 :=
      hdeltaConstant.trans hlocalConstantDelta₀One
    have hinputMono :
        Kakeya.realRpowENN delta (-inputLoss) ≤
          Kakeya.realRpowENN delta (-sourceLossCeiling) :=
      realRpowENN_antitone hdelta hdeltaOne (by linarith)
    have hsourceAbsorb :
        160 * Kakeya.realRpowENN delta (-inputLoss) ≤
          Kakeya.realRpowENN delta (-localIntermediate) :=
      (mul_le_mul_right hinputMono 160).trans
        (hlocalConstantAbsorb delta hdelta hdeltaConstant)
    exact hsourceAbsorb.trans
      (hlocalTransport delta (4 * rho) hdelta hdeltaTransport
        (by positivity) hfourRho (by
          calc
            4 * rho ≤ 4 * Real.rpow delta scaleLoss := by gcongr
            _ = 4 * delta ^ scaleLoss := by rfl))
  · intro inputLoss firstLoss secondLoss delta rho hinput hinputCeiling
      hfirst hfirstCeiling hsecondCeiling hdelta hdeltaSmall hrho hrhoSmall
      hrhoPower
    have hdeltaConstant : delta ≤ saturationConstantDelta₀ :=
      hdeltaSmall.trans (min_le_left _ _)
    have hdeltaTransport : delta ≤ saturationTransportDelta₀ :=
      hdeltaSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hdeltaOne : delta ≤ 1 :=
      hdeltaConstant.trans hsaturationConstantDelta₀One
    have hrhoOne : rho ≤ 1 := hrhoSmall.trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (by norm_num)))
    have hactualCost : inputLoss + 2 * firstLoss ≤ saturationCost := by
      dsimp only [saturationCost]
      linarith
    have hactualGain : saturationGain ≤ eta + 2 * firstLoss - secondLoss := by
      dsimp only [saturationGain]
      linarith
    have hdeltaPower :
        Kakeya.realRpowENN delta (-(inputLoss + 2 * firstLoss)) ≤
          Kakeya.realRpowENN delta (-saturationCost) := by
      exact realRpowENN_antitone hdelta hdeltaOne (by linarith)
    have hrhoPowerMono :
        Kakeya.realRpowENN rho (eta + 2 * firstLoss - secondLoss) ≤
          Kakeya.realRpowENN rho saturationGain :=
      realRpowENN_antitone hrho hrhoOne hactualGain
    have hconstantBound :
        saturationConstant *
            Kakeya.realRpowENN delta (-(inputLoss + 2 * firstLoss)) ≤
          Kakeya.realRpowENN delta (-saturationIntermediate) :=
      (mul_le_mul_right hdeltaPower saturationConstant).trans
        (hsaturationConstantAbsorb delta hdelta hdeltaConstant)
    have htransportBound :
        Kakeya.realRpowENN delta (-saturationIntermediate) ≤
          Kakeya.realRpowENN rho (-saturationGain) :=
      hsaturationTransport delta rho hdelta hdeltaTransport hrho hrhoOne
        (by simpa using hrhoPower)
    have hcancel :
        Kakeya.realRpowENN rho (-saturationGain) *
            Kakeya.realRpowENN rho saturationGain = 1 := by
      rw [← realRpowENN_add hrho]
      simp [Kakeya.realRpowENN]
    apply pureWZ2Node05V4Rich_saturation_power_of_normalized_budget
      hdelta hrho
    change saturationConstant *
        Kakeya.realRpowENN delta (-(inputLoss + 2 * firstLoss)) *
        Kakeya.realRpowENN rho (eta + 2 * firstLoss - secondLoss) ≤ 1
    calc
      _ ≤ Kakeya.realRpowENN delta (-saturationIntermediate) *
          Kakeya.realRpowENN rho saturationGain := by gcongr
      _ ≤ Kakeya.realRpowENN rho (-saturationGain) *
          Kakeya.realRpowENN rho saturationGain := by gcongr
      _ = 1 := hcancel
  · intro inputLoss delta rho hinput hinputCeiling hdelta hdeltaSmall
      hrho hgraphOne hrhoPower
    have hdeltaConstant : delta ≤ constantDelta₀ :=
      hdeltaSmall.trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_left _ _)))))
    have hdeltaTransport : delta ≤ transportDelta₀ :=
      hdeltaSmall.trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_right _ _)))))
    have hdeltaOne : delta ≤ 1 :=
      hdeltaConstant.trans hconstantDelta₀One
    have hinputMono :
        Kakeya.realRpowENN delta (-inputLoss) ≤
          Kakeya.realRpowENN delta (-sourceLossCeiling) := by
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith)
    have hsourceAbsorb :
        160 * Kakeya.realRpowENN delta (-inputLoss) ≤
          Kakeya.realRpowENN delta (-constantIntermediate) :=
      (mul_le_mul_right hinputMono 160).trans
        (hconstantAbsorb delta hdelta hdeltaConstant)
    have hgraphPos : 0 < 256 * rho := by positivity
    have hgraphPower : 256 * rho ≤ 256 * Real.rpow delta scaleLoss := by
      gcongr
    have htransport := hconstantTransport delta (256 * rho) hdelta
      hdeltaTransport hgraphPos hgraphOne hgraphPower
    have hENN := hsourceAbsorb.trans htransport
    have hrightTop :
        Kakeya.realRpowENN (256 * rho) (-constantLoss) ≠ ⊤ := by
      simp [Kakeya.realRpowENN]
    have hreal := ENNReal.toReal_mono hrightTop hENN
    simpa [Kakeya.realRpowENN,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hgraphPos.le _)] using hreal
  · intro rho hrho hrhoSmall
    have hrhoVolume : rho ≤ volumeRho₀ :=
      hrhoSmall.trans (min_le_left _ _)
    have hbase := hvolumeAbsorb rho hrho hrhoVolume
    have hleft :
        Kakeya.realRpowENN (256 * rho) graphExponent =
          ENNReal.ofReal (Real.rpow 256 graphExponent) *
            Kakeya.realRpowENN rho graphExponent := by
      exact realRpowENN_mul (by norm_num) hrho graphExponent
    have hright :
        Kakeya.realRpowENN rho (-1 / 2 + neighborhoodLoss) *
            Kakeya.realRpowENN (4 * rho) saturationExponent =
          Kakeya.realRpowENN 4 saturationExponent *
            Kakeya.realRpowENN rho volumeTargetExponent := by
      rw [realRpowENN_mul (by norm_num) hrho saturationExponent]
      have hrhoCombine :
          Kakeya.realRpowENN rho (-1 / 2 + neighborhoodLoss) *
              Kakeya.realRpowENN rho saturationExponent =
            Kakeya.realRpowENN rho volumeTargetExponent := by
        rw [← realRpowENN_add hrho]
        congr 1
        dsimp only [volumeTargetExponent, saturationExponent]
        ring
      calc
        Kakeya.realRpowENN rho (-1 / 2 + neighborhoodLoss) *
            (Kakeya.realRpowENN 4 saturationExponent *
              Kakeya.realRpowENN rho saturationExponent) =
          Kakeya.realRpowENN 4 saturationExponent *
            (Kakeya.realRpowENN rho (-1 / 2 + neighborhoodLoss) *
              Kakeya.realRpowENN rho saturationExponent) := by ring
        _ = Kakeya.realRpowENN 4 saturationExponent *
            Kakeya.realRpowENN rho volumeTargetExponent := by
              rw [hrhoCombine]
    rw [hleft, hright]
    apply hbase.trans
    exact le_mul_of_one_le_left (by positivity) <| by
      apply ENNReal.one_le_ofReal.mpr
      exact Real.one_le_rpow (by norm_num) hsaturationExponent.le
  · intro rho hrho hrhoSmall
    have hrhoSource : rho ≤ sourceCostRho₀ :=
      hrhoSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hrhoOne : rho ≤ 1 :=
      hrhoSource.trans hsourceCostRho₀One
    have hgraphOne : 256 * rho ≤ 1 := by
      have hsmall : rho ≤ 1 / 256 :=
        hrhoSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
      nlinarith
    have hgraphPos : 0 < wz1Lemma23Theorem22Scale (256 * rho) := by
      dsimp only [wz1Lemma23Theorem22Scale]
      positivity
    have hgraphScaleOne :
        wz1Lemma23Theorem22Scale (256 * rho) ≤ 1 := by
      dsimp only [wz1Lemma23Theorem22Scale]
      exact (div_le_self (Real.sqrt_nonneg _) (by
        have hsqrtThree : 1 ≤ Real.sqrt 3 :=
          (Real.one_le_sqrt).2 (by norm_num)
        nlinarith)).trans (Real.sqrt_le_one.mpr hgraphOne)
    have hgraphUpper :
        wz1Lemma23Theorem22Scale (256 * rho) ≤
          2 * Real.rpow rho (1 / 2 : ℝ) := by
      calc
        wz1Lemma23Theorem22Scale (256 * rho) ≤ 2 * Real.sqrt rho :=
          pureWZ2_sourceFixedBinCoarse_deltaGraph_le_two_sqrt hrho
        _ = 2 * Real.rpow rho (1 / 2 : ℝ) := by
          exact congrArg (fun value : ℝ => 2 * value)
            (Real.sqrt_eq_rpow rho)
    exact hsourceCostConvert rho
      (wz1Lemma23Theorem22Scale (256 * rho)) hrho hrhoSource
      hgraphPos hgraphScaleOne hgraphUpper

namespace PureWZ2Node05V4RichSaturatedGraphThreshold

/-- Instantiate the pre-runtime saturation budget on the two terminal losses
actually stored by the dependent V4 two-call witness. -/
theorem twoCall_saturation_power
    {capability : PureWZ2PropStickyCapability}
    {sigma sourceLossCeiling firstLossCeiling secondLossCeiling eta
      neighborhoodLoss volumeLoss constantLoss sourceCostLoss scaleLoss
      inputLoss delta rho stickyLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    (threshold : PureWZ2Node05V4RichSaturatedGraphThreshold
      sigma sourceLossCeiling firstLossCeiling secondLossCeiling eta
        neighborhoodLoss volumeLoss constantLoss sourceCostLoss scaleLoss)
    (twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested)
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (hinputNonneg : 0 ≤ inputLoss)
    (hinputCeiling : inputLoss ≤ sourceLossCeiling)
    (hfirstCeiling : schedule.firstOutputLoss ≤ firstLossCeiling)
    (hsecondCeiling : stickyLoss ≤ secondLossCeiling)
    (hdeltaSmall : delta ≤ threshold.delta₀)
    (hrhoSmall : rho ≤ threshold.rho₀)
    (hrhoPower : rho ≤ Real.rpow delta scaleLoss) :
    ((32 * Kakeya.realRpowENN delta (-inputLoss) *
            Kakeya.realRpowENN delta sigma *
            Kakeya.realRpowENN rho (2 - sigma)) *
          ENNReal.ofReal rho) *
          Kakeya.realRpowENN (4 * rhoRequested.1)
            (3 / 2 + sigma / 2 + eta) ≤
      (Kakeya.realRpowENN rhoRequested.1 3 *
            Kakeya.realRpowENN (delta / rhoRequested.1)
              (sigma + 2 * twoScale.first.rich.terminalLoss)) *
          Kakeya.realRpowENN rhoRequested.1
            (3 / 2 + sigma / 2 + twoScale.second.terminalLoss) := by
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hraw := threshold.saturation_power hinputNonneg hinputCeiling
    twoScale.first.rich.terminalLoss_pos.le
    (twoScale.first.rich.terminalLoss_le_output.trans hfirstCeiling)
    (twoScale.second.terminalLoss_le_output.trans hsecondCeiling)
    current.grain.extremal.delta_pos hdeltaSmall hrho hrhoSmall hrhoPower
  simpa only [pullback.rhoRequested_eq] using hraw

end PureWZ2Node05V4RichSaturatedGraphThreshold

structure PureWZ2Node05V4RichSaturatedTheorem52Data
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss finalLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : neighborhood.saturatedGraphScale ≤ 1}
    (finite : PureWZ2Node05V4RichSaturatedFiniteGraphData
      (eta := eta) neighborhood hbridge hgraphOne)
    (projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss) where
  output : PureWZ2AnchoredTheorem52Output finite.finiteGraph projection
  provenance :
    PureWZ2Node05V4RichSaturatedTheorem52Provenance output

/-- One dependent output containing both the saturated finite graph and the
Theorem-5.2 data constructed from that exact graph. -/
structure PureWZ2Node05V4RichSaturatedScheduledTheorem52Data
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss finalLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    (neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : neighborhood.saturatedGraphScale ≤ 1)
    (projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss) where
  finite : PureWZ2Node05V4RichSaturatedFiniteGraphData
    (eta := eta) neighborhood hbridge hgraphOne
  theorem52 : PureWZ2Node05V4RichSaturatedTheorem52Data finite projection

namespace PureWZ2Node05V4RichSaturatedFiniteGraphData

/-- Run the saturated graph through the preselected analytic thresholds and
retain the exact source provenance of the resulting `Z_lin` witnesses. -/
theorem theorem52WithProvenance
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss finalLoss eta
      sourceLossCeiling firstLossCeiling secondLossCeiling scaleLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : neighborhood.saturatedGraphScale ≤ 1}
    (finite : PureWZ2Node05V4RichSaturatedFiniteGraphData
      (eta := eta) neighborhood hbridge hgraphOne)
    (projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss)
    (analytic : PureWZ2SourceHorizontalAnalyticThreshold projection.theoremEta)
    (threshold : PureWZ2Node05V4RichSaturatedGraphThreshold
      sigma sourceLossCeiling firstLossCeiling secondLossCeiling eta
        neighborhood.neighborhoodLoss analytic.budget.volumeLoss
        analytic.budget.constantLoss projection.sourceCostLossCeiling
        scaleLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hfinal : 0 < finalLoss) (hfinalOne : finalLoss < 1)
    (hfinalSigma : finalLoss / 2 < sigma)
    (heta : 0 < eta)
    (hinputNonneg : 0 ≤ inputLoss)
    (hinputCeiling : inputLoss ≤ sourceLossCeiling)
    (hdeltaSmall : delta ≤ threshold.delta₀)
    (hrhoSmall : rho ≤ threshold.rho₀)
    (hrhoPower : rho ≤ Real.rpow delta scaleLoss)
    (hgraphAnalytic : neighborhood.graphScale ≤ analytic.rho0)
    (hrhoProjection : rho ≤ projection.rho₀)
    (hCOne : (1 : ENNReal) ≤
      160 * Kakeya.realRpowENN delta (-inputLoss)) :
    Nonempty (PureWZ2Node05V4RichSaturatedTheorem52Data
      finite projection) := by
  have hsourceCost := threshold.source_cost
    (by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos)
    hrhoSmall
  have hsourceCost' :
      Kakeya.realRpowENN rhoRequested.1 (-eta) ≤
        Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale neighborhood.graphScale)
          (-projection.sourceCostLossCeiling) := by
    simpa only [PureWZ2PreCommonBinGlobalGrainNeighborhoodData.graphScale,
      PureWZ2PreCommonBinGlobalGrainNeighborhoodData.saturatedGraphScale,
      pullback.rhoRequested_eq] using hsourceCost
  have hconstant := threshold.constant_power hinputNonneg hinputCeiling
    current.grain.extremal.delta_pos hdeltaSmall
    (by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos)
    hgraphOne hrhoPower
  have hvolumePower := threshold.volume_power
    (by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos)
    hrhoSmall
  have hvolumePower' :
      Kakeya.realRpowENN neighborhood.graphScale
          (1 + sigma / 2 + analytic.budget.volumeLoss) ≤
        Kakeya.realRpowENN rho
            (-1 / 2 + neighborhood.neighborhoodLoss) *
          Kakeya.realRpowENN (4 * rhoRequested.1)
            (3 / 2 + sigma / 2 + eta) := by
    simpa only [PureWZ2PreCommonBinGlobalGrainNeighborhoodData.graphScale,
      PureWZ2PreCommonBinGlobalGrainNeighborhoodData.saturatedGraphScale,
      pullback.rhoRequested_eq] using hvolumePower
  rcases finite.theorem52OfThresholds projection analytic hsigma hsigmaOne
      hfinal hfinalOne hfinalSigma heta hCOne hconstant hvolumePower' hsourceCost'
      hgraphAnalytic hrhoProjection with ⟨output⟩
  rcases output.saturatedProvenance with ⟨provenance⟩
  exact ⟨{ output := output, provenance := provenance }⟩

end PureWZ2Node05V4RichSaturatedFiniteGraphData

namespace PureWZ2PreCommonBinGlobalGrainNeighborhoodData

/-- Construct the saturated finite graph and execute Theorem 5.2 on that
same graph using only pre-runtime scalar thresholds.  The two direct-rich
terminal losses are read from the dependent `twoScale` witness. -/
theorem saturatedTheorem52OfThresholds
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss finalLoss eta
      sourceLossCeiling firstLossCeiling secondLossCeiling scaleLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    (neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss)
    (analytic : PureWZ2SourceHorizontalAnalyticThreshold projection.theoremEta)
    (threshold : PureWZ2Node05V4RichSaturatedGraphThreshold
      sigma sourceLossCeiling firstLossCeiling secondLossCeiling eta
        neighborhood.neighborhoodLoss analytic.budget.volumeLoss
        analytic.budget.constantLoss projection.sourceCostLossCeiling
        scaleLoss)
    (hgraphOne : neighborhood.saturatedGraphScale ≤ 1)
    (hheightAbsorb :
      neighborhood.saturatedGraphScale + 2 * Real.sqrt rho ≤
        16 * Real.sqrt rho)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hcertificateOne : 4 * rhoRequested.1 ≤ 1)
    (hPlanarSmall : 32 * Real.rpow (4 * rhoRequested.1) eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rhoRequested.1) ≤ 1)
    (habsorb :
      Real.rpow (4 * rhoRequested.1) (1 - 4 * eta / sigma) ≤
        Real.sqrt (4 * rhoRequested.1) / 14)
    (hfinal : 0 < finalLoss) (hfinalOne : finalLoss < 1)
    (hfinalSigma : finalLoss / 2 < sigma)
    (hinputNonneg : 0 ≤ inputLoss)
    (hinputCeiling : inputLoss ≤ sourceLossCeiling)
    (hfirstCeiling : schedule.firstOutputLoss ≤ firstLossCeiling)
    (hsecondCeiling : stickyLoss ≤ secondLossCeiling)
    (hdeltaSmall : delta ≤ threshold.delta₀)
    (hrhoSmall : rho ≤ threshold.rho₀)
    (hrhoPower : rho ≤ Real.rpow delta scaleLoss)
    (hgraphAnalytic : neighborhood.graphScale ≤ analytic.rho0)
    (hrhoProjection : rho ≤ projection.rho₀)
    (hCOne : (1 : ENNReal) ≤
      160 * Kakeya.realRpowENN delta (-inputLoss)) :
    Nonempty (PureWZ2Node05V4RichSaturatedScheduledTheorem52Data
      (eta := eta) neighborhood hbridge hgraphOne projection) := by
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hsourcePower := threshold.twoCall_saturation_power twoScale pullback
    hinputNonneg hinputCeiling hfirstCeiling hsecondCeiling hdeltaSmall
    hrhoSmall hrhoPower
  have hlocalPowerRaw := threshold.local_power hinputNonneg hinputCeiling
    current.grain.extremal.delta_pos hdeltaSmall hrho
    (by simpa only [pullback.rhoRequested_eq] using hcertificateOne) hrhoPower
  have hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rhoRequested.1) (-eta) := by
    simpa only [pullback.rhoRequested_eq] using hlocalPowerRaw
  rcases neighborhood.saturatedFiniteGraph hbridge hgraphOne hheightAbsorb
      hsourcePower hlocalPower hsigma hsigmaOne heta hetaSigma hcertificateOne
      hPlanarSmall hrootSmall20 habsorb with ⟨finite⟩
  rcases finite.theorem52WithProvenance projection analytic threshold
      hsigma hsigmaOne hfinal hfinalOne hfinalSigma heta hinputNonneg
      hinputCeiling hdeltaSmall hrhoSmall hrhoPower hgraphAnalytic
      hrhoProjection hCOne with ⟨theorem52⟩
  exact ⟨{ finite := finite, theorem52 := theorem52 }⟩

end PureWZ2PreCommonBinGlobalGrainNeighborhoodData

end Kakeya.Assouad

end
