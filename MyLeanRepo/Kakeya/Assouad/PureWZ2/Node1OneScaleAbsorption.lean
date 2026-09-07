import MyLeanRepo.Kakeya.Assouad.PureWZ2.CenteredStrictFiberBounds
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ProbabilisticAnalyticCore
import MyLeanRepo.Kakeya.Assouad.Targets.ProbabilisticKatzTaoSubfamily

/-!
# One-scale absorptions for pure WZ2 Node 1

This file packages the remaining explicit monomial estimates at the centered
target scale.  The inputs are only source/target scale comparisons and the
small-scale scalar inequalities selected before the source scale.
-/

noncomputable section

open Kakeya.Streamlined
open Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Assouad

/-- Public centered CWA times target tube volume is absorbed by the centered
pointwise density constant. -/
theorem pure_wz2_centered_cwa_volume_le_density
    {delta rho targetScale inputEta pruneEta : ℝ}
    (hdelta : 0 < delta)
    (htarget : 0 < targetScale)
    (htargetOne : targetScale ≤ 1)
    (hCwaVolume :
      ((Kakeya.realRpowENN delta pruneEta)⁻¹ *
          ((4000000 : ENNReal) *
            Kakeya.realRpowENN delta (-inputEta))) *
          Kakeya.deltaTubeVolume targetScale ≤
        (48000000 : ENNReal) *
          Kakeya.realRpowENN delta
            (-(inputEta + pruneEta)) *
          Kakeya.realRpowENN targetScale 2)
    (hDensity :
      ENNReal.ofReal (1 / 12000000 : ℝ) *
          Kakeya.realRpowENN delta pruneEta ≤
        pureWZ2CenteredDensityConstant
          delta rho
          (Kakeya.realRpowENN delta pruneEta))
    (habsorb :
      (576000000000000 : ENNReal) *
          Kakeya.realRpowENN delta
            (-(inputEta + 2 * pruneEta)) *
          Kakeya.realRpowENN targetScale 2 ≤
        1) :
    ((Kakeya.realRpowENN delta pruneEta)⁻¹ *
        ((4000000 : ENNReal) *
          Kakeya.realRpowENN delta (-inputEta))) *
        Kakeya.deltaTubeVolume targetScale ≤
      pureWZ2CenteredDensityConstant
        delta rho
        (Kakeya.realRpowENN delta pruneEta) := by
  calc
    ((Kakeya.realRpowENN delta pruneEta)⁻¹ *
        ((4000000 : ENNReal) *
          Kakeya.realRpowENN delta (-inputEta))) *
        Kakeya.deltaTubeVolume targetScale ≤
      (48000000 : ENNReal) *
        Kakeya.realRpowENN delta
          (-(inputEta + pruneEta)) *
        Kakeya.realRpowENN targetScale 2 := hCwaVolume
    _ =
      ((576000000000000 : ENNReal) *
        Kakeya.realRpowENN delta
          (-(inputEta + 2 * pruneEta)) *
        Kakeya.realRpowENN targetScale 2) *
        (ENNReal.ofReal (1 / 12000000 : ℝ) *
          Kakeya.realRpowENN delta pruneEta) := by
      have hconstant :
          (576000000000000 : ENNReal) *
              ENNReal.ofReal (1 / 12000000 : ℝ) =
            48000000 := by
        rw [show (576000000000000 : ENNReal) =
            ENNReal.ofReal (576000000000000 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num)]
        norm_num
      have hpowers :
          Kakeya.realRpowENN delta
                (-(inputEta + 2 * pruneEta)) *
              Kakeya.realRpowENN delta pruneEta =
            Kakeya.realRpowENN delta
              (-(inputEta + pruneEta)) := by
        rw [Subunit.realRpowENN_mul hdelta]
        congr 1
        ring
      rw [show
        ((576000000000000 : ENNReal) *
            Kakeya.realRpowENN delta
              (-(inputEta + 2 * pruneEta)) *
            Kakeya.realRpowENN targetScale 2) *
            (ENNReal.ofReal (1 / 12000000 : ℝ) *
              Kakeya.realRpowENN delta pruneEta) =
          ((576000000000000 : ENNReal) *
            ENNReal.ofReal (1 / 12000000 : ℝ)) *
            (Kakeya.realRpowENN delta
                (-(inputEta + 2 * pruneEta)) *
              Kakeya.realRpowENN delta pruneEta) *
            Kakeya.realRpowENN targetScale 2 by ring,
        hconstant, hpowers]
    _ ≤ 1 *
        (ENNReal.ofReal (1 / 12000000 : ℝ) *
          Kakeya.realRpowENN delta pruneEta) := by
      gcongr
    _ ≤ pureWZ2CenteredDensityConstant
        delta rho
        (Kakeya.realRpowENN delta pruneEta) := by
      simpa using hDensity

/-- Inverting the centered CWA-volume upper bound gives the monomial lower
bound used by both the second Chernoff term and the final cardinality
coefficient. -/
theorem pure_wz2_centeredCWA_volume_inv_lower
    {delta targetScale inputEta pruneEta : ℝ}
    (hdelta : 0 < delta)
    (htarget : 0 < targetScale)
    (hCwaVolume :
      ((Kakeya.realRpowENN delta pruneEta)⁻¹ *
          ((4000000 : ENNReal) *
            Kakeya.realRpowENN delta (-inputEta))) *
          Kakeya.deltaTubeVolume targetScale ≤
        (48000000 : ENNReal) *
          Kakeya.realRpowENN delta
            (-(inputEta + pruneEta)) *
          Kakeya.realRpowENN targetScale 2) :
    (48000000 : ENNReal)⁻¹ *
          Kakeya.realRpowENN delta (inputEta + pruneEta) *
          Kakeya.realRpowENN targetScale (-2) ≤
      (((Kakeya.realRpowENN delta pruneEta)⁻¹ *
          ((4000000 : ENNReal) *
            Kakeya.realRpowENN delta (-inputEta))) *
          Kakeya.deltaTubeVolume targetScale)⁻¹ := by
  have hinverse :=
    (ENNReal.inv_le_inv).2 hCwaVolume
  have hconstantZero : (48000000 : ENNReal) ≠ 0 := by
    norm_num
  have hconstantTop : (48000000 : ENNReal) ≠ ⊤ := by
    norm_num
  have hdeltaPowerZero :
      Kakeya.realRpowENN delta
          (-(inputEta + pruneEta)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hdelta _)).ne'
  have hdeltaPowerTop :
      Kakeya.realRpowENN delta
          (-(inputEta + pruneEta)) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have htargetPowerZero :
      Kakeya.realRpowENN targetScale 2 ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos htarget _)).ne'
  have htargetPowerTop :
      Kakeya.realRpowENN targetScale 2 ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hdeltaInv :
      (Kakeya.realRpowENN delta
        (-(inputEta + pruneEta)))⁻¹ =
      Kakeya.realRpowENN delta (inputEta + pruneEta) := by
    rw [pure_wz2_realRpowENN_inv hdelta]
    congr 1
    ring
  have htargetInv :
      (Kakeya.realRpowENN targetScale 2)⁻¹ =
        Kakeya.realRpowENN targetScale (-2) :=
    pure_wz2_realRpowENN_inv htarget
  have hproductInv :
      ((48000000 : ENNReal) *
          Kakeya.realRpowENN delta
            (-(inputEta + pruneEta)) *
          Kakeya.realRpowENN targetScale 2)⁻¹ =
        (48000000 : ENNReal)⁻¹ *
          Kakeya.realRpowENN delta (inputEta + pruneEta) *
          Kakeya.realRpowENN targetScale (-2) := by
    calc
      ((48000000 : ENNReal) *
            Kakeya.realRpowENN delta
              (-(inputEta + pruneEta)) *
            Kakeya.realRpowENN targetScale 2)⁻¹ =
          ((48000000 : ENNReal) *
            Kakeya.realRpowENN delta
              (-(inputEta + pruneEta)))⁻¹ *
            (Kakeya.realRpowENN targetScale 2)⁻¹ :=
        ENNReal.mul_inv
          (Or.inl (mul_ne_zero
            hconstantZero hdeltaPowerZero))
          (Or.inl (ENNReal.mul_ne_top
            hconstantTop hdeltaPowerTop))
      _ =
          ((48000000 : ENNReal)⁻¹ *
            (Kakeya.realRpowENN delta
              (-(inputEta + pruneEta)))⁻¹) *
            (Kakeya.realRpowENN targetScale 2)⁻¹ := by
        rw [ENNReal.mul_inv
          (Or.inl hconstantZero)
          (Or.inl hconstantTop)]
      _ =
          (48000000 : ENNReal)⁻¹ *
            Kakeya.realRpowENN delta
              (inputEta + pruneEta) *
            Kakeya.realRpowENN targetScale (-2) := by
        rw [hdeltaInv, htargetInv]
  rw [hproductInv] at hinverse
  exact hinverse

/-- Real-valued inverse form of
`pure_wz2_centeredCWA_volume_inv_lower`. -/
theorem pure_wz2_centeredCWA_volume_inv_lower_toReal
    {delta targetScale inputEta pruneEta : ℝ}
    (hdelta : 0 < delta)
    (htarget : 0 < targetScale)
    (hCwaVolume :
      ((Kakeya.realRpowENN delta pruneEta)⁻¹ *
          ((4000000 : ENNReal) *
            Kakeya.realRpowENN delta (-inputEta))) *
          Kakeya.deltaTubeVolume targetScale ≤
        (48000000 : ENNReal) *
          Kakeya.realRpowENN delta
            (-(inputEta + pruneEta)) *
          Kakeya.realRpowENN targetScale 2)
    (hrightTop :
      ((((Kakeya.realRpowENN delta pruneEta)⁻¹ *
          ((4000000 : ENNReal) *
            Kakeya.realRpowENN delta (-inputEta))) *
          Kakeya.deltaTubeVolume targetScale)⁻¹) ≠ ⊤) :
    (1 / 48000000 : ℝ) *
        Real.rpow delta (inputEta + pruneEta) *
        Real.rpow targetScale (-2) ≤
      (((Kakeya.realRpowENN delta pruneEta)⁻¹ *
          ((4000000 : ENNReal) *
            Kakeya.realRpowENN delta (-inputEta))) *
          Kakeya.deltaTubeVolume targetScale).toReal⁻¹ := by
  have hmain :=
    pure_wz2_centeredCWA_volume_inv_lower
      hdelta htarget hCwaVolume
  have hleftTop :
      (48000000 : ENNReal)⁻¹ *
          Kakeya.realRpowENN delta (inputEta + pruneEta) *
          Kakeya.realRpowENN targetScale (-2) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hreal :=
    (ENNReal.toReal_le_toReal hleftTop hrightTop).mpr hmain
  calc
    (1 / 48000000 : ℝ) *
          Real.rpow delta (inputEta + pruneEta) *
          Real.rpow targetScale (-2) =
        ((48000000 : ENNReal)⁻¹ *
          Kakeya.realRpowENN delta (inputEta + pruneEta) *
          Kakeya.realRpowENN targetScale (-2)).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_inv,
        Subunit.realRpowENN_toReal hdelta,
        Subunit.realRpowENN_toReal htarget]
      norm_num
    _ ≤
        ((((Kakeya.realRpowENN delta pruneEta)⁻¹ *
            ((4000000 : ENNReal) *
              Kakeya.realRpowENN delta (-inputEta))) *
            Kakeya.deltaTubeVolume targetScale)⁻¹).toReal :=
      hreal
    _ =
        (((Kakeya.realRpowENN delta pruneEta)⁻¹ *
            ((4000000 : ENNReal) *
              Kakeya.realRpowENN delta (-inputEta))) *
            Kakeya.deltaTubeVolume targetScale).toReal⁻¹ := by
      rw [ENNReal.toReal_inv]

/-- Transport the centered CWA inverse lower bound from the target scale to
the source-scale exponent used in the second Chernoff term. -/
theorem pure_wz2_source_failure_inverse_lower
    {delta targetScale scaleExponent inputEta pruneEta inverseBound : ℝ}
    (hdelta : 0 < delta)
    (htarget : 0 < targetScale)
    (htargetUpper :
      targetScale ≤ Real.rpow delta scaleExponent)
    (hinverse :
      (1 / 48000000 : ℝ) *
          Real.rpow delta (inputEta + pruneEta) *
          Real.rpow targetScale (-2) ≤
        inverseBound) :
    (1 / 48000000 : ℝ) *
        Real.rpow delta
          (inputEta + pruneEta - 2 * scaleExponent) ≤
      inverseBound := by
  have htargetNegTwo :
      Real.rpow delta (-2 * scaleExponent) ≤
        Real.rpow targetScale (-2) := by
    have hmain :=
      Real.rpow_le_rpow_of_nonpos
        htarget htargetUpper (by norm_num : (-2 : ℝ) ≤ 0)
    change
      Real.rpow (Real.rpow delta scaleExponent) (-2) ≤
        Real.rpow targetScale (-2) at hmain
    have hidentity :
        Real.rpow (Real.rpow delta scaleExponent) (-2) =
          Real.rpow delta (-2 * scaleExponent) := by
      calc
        Real.rpow (Real.rpow delta scaleExponent) (-2) =
            Real.rpow delta (scaleExponent * (-2)) :=
          (Real.rpow_mul hdelta.le scaleExponent (-2)).symm
        _ = Real.rpow delta (-2 * scaleExponent) := by
          congr 1
          ring
    rw [hidentity] at hmain
    exact hmain
  have hsplit :
      Real.rpow delta
          (inputEta + pruneEta - 2 * scaleExponent) =
        Real.rpow delta (inputEta + pruneEta) *
          Real.rpow delta (-2 * scaleExponent) := by
    calc
      Real.rpow delta
          (inputEta + pruneEta - 2 * scaleExponent) =
        Real.rpow delta
          ((inputEta + pruneEta) + (-2 * scaleExponent)) := by
            congr 1
            ring
      _ =
        Real.rpow delta (inputEta + pruneEta) *
          Real.rpow delta (-2 * scaleExponent) :=
            Real.rpow_add hdelta _ _
  rw [hsplit]
  have hscaled :
      (1 / 48000000 : ℝ) *
          (Real.rpow delta (inputEta + pruneEta) *
            Real.rpow delta (-2 * scaleExponent)) ≤
        (1 / 48000000 : ℝ) *
          (Real.rpow delta (inputEta + pruneEta) *
            Real.rpow targetScale (-2)) := by
    exact
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          htargetNegTwo
          (Real.rpow_nonneg hdelta.le _))
        (by norm_num)
  exact hscaled.trans (by
    simpa only [mul_assoc] using hinverse)

/-- Any explicit lower bound whose coefficient exceeds `log 16` makes the
second Chernoff failure probability smaller than `1/16`. -/
theorem pure_wz2_thinning_failure_of_log_lower
    {lowerBound z : ℝ}
    (hcoefficient : 0 < 3 - Real.exp 1)
    (hz : lowerBound ≤ z)
    (hlog :
      (3 - Real.exp 1) * lowerBound >
        Real.log 16) :
    Real.exp (-(3 - Real.exp 1) * z) < 1 / 16 := by
  have hcoefficientLower :
      (3 - Real.exp 1) * lowerBound ≤
        (3 - Real.exp 1) * z :=
    mul_le_mul_of_nonneg_left hz hcoefficient.le
  have hstrict :
      Real.exp (-((3 - Real.exp 1) * z)) <
        Real.exp (-Real.log 16) :=
    Real.exp_strictMono
      (neg_lt_neg (hlog.trans_le hcoefficientLower))
  have hexp :
      Real.exp (-Real.log 16) = 1 / 16 := by
    rw [Real.exp_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 16)]
    field_simp
  have hargument :
      -(3 - Real.exp 1) * z =
        -((3 - Real.exp 1) * z) := by
    ring
  rw [hargument]
  exact hstrict.trans_eq hexp

/-- Specialized count-threshold form used by the centered CWA inverse
estimate. -/
theorem pure_wz2_thinning_failure_of_count_lower
    {delta exponent z : ℝ}
    (hcoefficient : 0 < 3 - Real.exp 1)
    (hz :
      (1 / 48000000 : ℝ) *
          Real.rpow delta exponent ≤
        z)
    (hcount :
      ((3 - Real.exp 1) / 48000000) *
          Real.rpow delta exponent >
        Real.log 16) :
    Real.exp (-(3 - Real.exp 1) * z) < 1 / 16 := by
  apply
    pure_wz2_thinning_failure_of_log_lower
      hcoefficient hz
  have heq :
      (3 - Real.exp 1) *
          ((1 / 48000000 : ℝ) *
            Real.rpow delta exponent) =
        ((3 - Real.exp 1) / 48000000) *
          Real.rpow delta exponent := by
    ring
  rw [heq]
  exact hcount

/-- Absorb the final target-scale cardinality power into the explicit source
scale coefficient. -/
theorem pure_wz2_final_cardinality_monomial
    {delta targetScale scaleExponent cardLoss thinningEta
      inputEta pruneEta : ℝ}
    (hdelta : 0 < delta)
    (htarget : 0 < targetScale)
    (htargetUpper :
      targetScale ≤ Real.rpow delta scaleExponent)
    (hcardGap : 0 ≤ cardLoss - thinningEta)
    (habsorb :
      ENNReal.ofReal
          (2 * 97200000000000001 *
            12000000 ^ 2 * 48000000 : ℝ) *
          Kakeya.realRpowENN delta
            (scaleExponent * (cardLoss - thinningEta) -
              inputEta - 3 * pruneEta) ≤
        1) :
    Kakeya.realRpowENN targetScale (-2 + cardLoss) ≤
      ENNReal.ofReal
          (2 * 97200000000000001 *
            12000000 ^ 2 * 48000000 : ℝ)⁻¹ *
        Kakeya.realRpowENN delta
          (inputEta + 3 * pruneEta) *
        Kakeya.realRpowENN targetScale
          (-2 + thinningEta) := by
  let constant : ℝ :=
    2 * 97200000000000001 *
      12000000 ^ 2 * 48000000
  have hconstant : 0 < constant := by
    dsimp [constant]
    positivity
  have hsource :
      Kakeya.realRpowENN delta
          (scaleExponent * (cardLoss - thinningEta)) ≤
        ENNReal.ofReal constant⁻¹ *
          Kakeya.realRpowENN delta
            (inputEta + 3 * pruneEta) := by
    have habsorb' :
        ENNReal.ofReal constant *
            Kakeya.realRpowENN delta
              (scaleExponent * (cardLoss - thinningEta) -
                (inputEta + 3 * pruneEta)) ≤
          1 := by
      rw [show
        scaleExponent * (cardLoss - thinningEta) -
            (inputEta + 3 * pruneEta) =
          scaleExponent * (cardLoss - thinningEta) -
            inputEta - 3 * pruneEta by ring]
      simpa [constant] using habsorb
    apply
      pure_wz2_density_power_from_absorption
        hdelta hconstant
    exact habsorb'
  have htargetGap :
      Kakeya.realRpowENN targetScale
          (cardLoss - thinningEta) ≤
        Kakeya.realRpowENN delta
          (scaleExponent * (cardLoss - thinningEta)) :=
    pure_wz2_target_power_upper
      hdelta htarget.le htargetUpper hcardGap
  have hcoefficient :
      Kakeya.realRpowENN targetScale
          (cardLoss - thinningEta) ≤
        ENNReal.ofReal constant⁻¹ *
          Kakeya.realRpowENN delta
            (inputEta + 3 * pruneEta) :=
    htargetGap.trans hsource
  have hsplit :
      Kakeya.realRpowENN targetScale (-2 + cardLoss) =
        Kakeya.realRpowENN targetScale
            (cardLoss - thinningEta) *
          Kakeya.realRpowENN targetScale
            (-2 + thinningEta) := by
    rw [Subunit.realRpowENN_mul htarget]
    congr 1
    ring
  rw [hsplit]
  calc
    Kakeya.realRpowENN targetScale
          (cardLoss - thinningEta) *
        Kakeya.realRpowENN targetScale
          (-2 + thinningEta) ≤
      (ENNReal.ofReal constant⁻¹ *
          Kakeya.realRpowENN delta
            (inputEta + 3 * pruneEta)) *
        Kakeya.realRpowENN targetScale
          (-2 + thinningEta) := by
      gcongr
    _ =
      ENNReal.ofReal
          (2 * 97200000000000001 *
            12000000 ^ 2 * 48000000 : ℝ)⁻¹ *
        Kakeya.realRpowENN delta
          (inputEta + 3 * pruneEta) *
        Kakeya.realRpowENN targetScale
          (-2 + thinningEta) := by
      rfl

/-- The explicit conflict, density, and CWA-volume bounds imply the exact
cardinality coefficient required by the probabilistic Assertion-D core. -/
theorem pure_wz2_final_cardinality_coefficient
    {delta targetScale scaleExponent cardLoss thinningEta
      inputEta pruneEta : ℝ}
    (hdelta : 0 < delta)
    (htarget : 0 < targetScale)
    (htargetOne : targetScale ≤ 1)
    (htargetUpper :
      targetScale ≤ Real.rpow delta scaleExponent)
    (hcardGap : 0 ≤ cardLoss - thinningEta)
    (hthinningEta : 0 ≤ thinningEta)
    (net : TubeDensityTestNet targetScale)
    (hnetLoss : net.lossFactor ≤ 10 ^ 7)
    (densityConstant cwaVolume : ENNReal)
    (hDensity :
      ENNReal.ofReal (1 / 12000000 : ℝ) *
          Kakeya.realRpowENN delta pruneEta ≤
        densityConstant)
    (hCwaInverse :
      (48000000 : ENNReal)⁻¹ *
          Kakeya.realRpowENN delta (inputEta + pruneEta) *
          Kakeya.realRpowENN targetScale (-2) ≤
        cwaVolume⁻¹)
    (habsorb :
      ENNReal.ofReal
          (2 * 97200000000000001 *
            12000000 ^ 2 * 48000000 : ℝ) *
          Kakeya.realRpowENN delta
            (scaleExponent * (cardLoss - thinningEta) -
              inputEta - 3 * pruneEta) ≤
        1) :
    Kakeya.realRpowENN targetScale (-2 + cardLoss) ≤
      (pureWZ2ThinnedAnalyticConflictBound
          net thinningEta + 1)⁻¹ *
        densityConstant *
        ((1 / 2 : ENNReal) *
          cwaVolume⁻¹ * densityConstant) := by
  let conflictConstant : ENNReal := 97200000000000001
  have honeTarget :
      (1 : ENNReal) ≤
        Kakeya.realRpowENN targetScale (-thinningEta) := by
    simpa [Kakeya.realRpowENN] using
      pure_wz2_rpowENN_antitone
        htarget htargetOne
        (by linarith : -thinningEta ≤ 0)
  have hdeltaMax :
      pureWZ2ThinnedDeltaMax net thinningEta ≤
        (100000000 : ENNReal) *
          Kakeya.realRpowENN targetScale (-thinningEta) := by
    dsimp [pureWZ2ThinnedDeltaMax]
    calc
      net.lossFactor * 10 *
          Kakeya.realRpowENN targetScale (-thinningEta) ≤
        (10 ^ 7 : ENNReal) * 10 *
          Kakeya.realRpowENN targetScale (-thinningEta) := by
            gcongr
      _ = (100000000 : ENNReal) *
          Kakeya.realRpowENN targetScale (-thinningEta) := by
        norm_num
  have hconflict :
      pureWZ2ThinnedAnalyticConflictBound
            net thinningEta + 1 ≤
        conflictConstant *
          Kakeya.realRpowENN targetScale (-thinningEta) := by
    dsimp [pureWZ2ThinnedAnalyticConflictBound, conflictConstant]
    calc
      972000000 * pureWZ2ThinnedDeltaMax net thinningEta + 1 ≤
        972000000 *
              ((100000000 : ENNReal) *
                Kakeya.realRpowENN targetScale (-thinningEta)) +
            Kakeya.realRpowENN targetScale (-thinningEta) := by
          gcongr
      _ =
        (97200000000000001 : ENNReal) *
          Kakeya.realRpowENN targetScale (-thinningEta) := by
        ring
  have hconflictInverse :
      (conflictConstant *
          Kakeya.realRpowENN targetScale (-thinningEta))⁻¹ ≤
        (pureWZ2ThinnedAnalyticConflictBound
          net thinningEta + 1)⁻¹ :=
    (ENNReal.inv_le_inv).2 hconflict
  have hconflictConstantZero : conflictConstant ≠ 0 := by
    norm_num [conflictConstant]
  have hconflictConstantTop : conflictConstant ≠ ⊤ := by
    norm_num [conflictConstant]
  have htargetPowerZero :
      Kakeya.realRpowENN targetScale (-thinningEta) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos htarget _)).ne'
  have htargetPowerTop :
      Kakeya.realRpowENN targetScale (-thinningEta) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hconflictInverse' :
      conflictConstant⁻¹ *
          Kakeya.realRpowENN targetScale thinningEta ≤
        (pureWZ2ThinnedAnalyticConflictBound
          net thinningEta + 1)⁻¹ := by
    have hproduct :
        (conflictConstant *
            Kakeya.realRpowENN targetScale (-thinningEta))⁻¹ =
          conflictConstant⁻¹ *
            Kakeya.realRpowENN targetScale thinningEta := by
      rw [ENNReal.mul_inv
        (Or.inl hconflictConstantZero)
        (Or.inl hconflictConstantTop)]
      rw [pure_wz2_realRpowENN_inv htarget]
      congr 1
      ring
    rw [← hproduct]
    exact hconflictInverse
  have hmonomial :=
    pure_wz2_final_cardinality_monomial
      hdelta htarget htargetUpper hcardGap habsorb
  have hconstantIdentity :
      ENNReal.ofReal
          (2 * 97200000000000001 *
            12000000 ^ 2 * 48000000 : ℝ)⁻¹ =
        conflictConstant⁻¹ *
          ENNReal.ofReal (1 / 12000000 : ℝ) *
          ((1 / 2 : ENNReal) *
            (48000000 : ENNReal)⁻¹ *
            ENNReal.ofReal (1 / 12000000 : ℝ)) := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity :
      (0 : ℝ) <
        2 * 97200000000000001 *
          12000000 ^ 2 * 48000000)]
    rw [show
      ENNReal.ofReal
          (2 * 97200000000000001 *
            12000000 ^ 2 * 48000000 : ℝ) =
        (2 : ENNReal) * 97200000000000001 *
          12000000 ^ 2 * 48000000 by norm_num]
    rw [show
      ENNReal.ofReal (1 / 12000000 : ℝ) =
        (12000000 : ENNReal)⁻¹ by
      rw [show (1 / 12000000 : ℝ) =
          (12000000 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num]
    dsimp [conflictConstant]
    have hinv
        (first second : ENNReal)
        (hfirstZero : first ≠ 0)
        (hfirstTop : first ≠ ⊤) :
        (first * second)⁻¹ =
          first⁻¹ * second⁻¹ :=
      ENNReal.mul_inv
        (Or.inl hfirstZero) (Or.inl hfirstTop)
    rw [show
      (2 : ENNReal) * 97200000000000001 *
            12000000 ^ 2 * 48000000 =
        97200000000000001 * 12000000 *
          (2 * 48000000 * 12000000) by ring]
    rw [hinv _ _ (by norm_num) (by norm_num)]
    rw [hinv _ _ (by norm_num) (by norm_num)]
    rw [hinv _ _ (by norm_num) (by norm_num)]
    rw [hinv _ _ (by norm_num) (by norm_num)]
    rw [show (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ by
      norm_num]
  rw [hconstantIdentity] at hmonomial
  have hlower :
      conflictConstant⁻¹ *
            Kakeya.realRpowENN targetScale thinningEta *
          (ENNReal.ofReal (1 / 12000000 : ℝ) *
            Kakeya.realRpowENN delta pruneEta) *
          ((1 / 2 : ENNReal) *
            ((48000000 : ENNReal)⁻¹ *
              Kakeya.realRpowENN delta
                (inputEta + pruneEta) *
              Kakeya.realRpowENN targetScale (-2)) *
            (ENNReal.ofReal (1 / 12000000 : ℝ) *
              Kakeya.realRpowENN delta pruneEta)) ≤
        (pureWZ2ThinnedAnalyticConflictBound
              net thinningEta + 1)⁻¹ *
          densityConstant *
          ((1 / 2 : ENNReal) *
            cwaVolume⁻¹ * densityConstant) := by
    gcongr
  apply hmonomial.trans
  calc
    conflictConstant⁻¹ *
          ENNReal.ofReal (1 / 12000000 : ℝ) *
          ((1 / 2 : ENNReal) *
            (48000000 : ENNReal)⁻¹ *
            ENNReal.ofReal (1 / 12000000 : ℝ)) *
          Kakeya.realRpowENN delta
            (inputEta + 3 * pruneEta) *
          Kakeya.realRpowENN targetScale
            (-2 + thinningEta) =
      conflictConstant⁻¹ *
            Kakeya.realRpowENN targetScale thinningEta *
          (ENNReal.ofReal (1 / 12000000 : ℝ) *
            Kakeya.realRpowENN delta pruneEta) *
          ((1 / 2 : ENNReal) *
            ((48000000 : ENNReal)⁻¹ *
              Kakeya.realRpowENN delta
                (inputEta + pruneEta) *
              Kakeya.realRpowENN targetScale (-2)) *
            (ENNReal.ofReal (1 / 12000000 : ℝ) *
              Kakeya.realRpowENN delta pruneEta)) := by
        rw [show
          Kakeya.realRpowENN delta
              (inputEta + 3 * pruneEta) =
            Kakeya.realRpowENN delta pruneEta *
              Kakeya.realRpowENN delta
                (inputEta + pruneEta) *
              Kakeya.realRpowENN delta pruneEta by
          rw [Subunit.realRpowENN_mul hdelta,
            Subunit.realRpowENN_mul hdelta]
          congr 1
          ring]
        rw [show
          Kakeya.realRpowENN targetScale
              (-2 + thinningEta) =
            Kakeya.realRpowENN targetScale thinningEta *
              Kakeya.realRpowENN targetScale (-2) by
          rw [Subunit.realRpowENN_mul htarget]
          congr 1
          ring]
        ring
    _ ≤
      (pureWZ2ThinnedAnalyticConflictBound
            net thinningEta + 1)⁻¹ *
        densityConstant *
        ((1 / 2 : ENNReal) *
          cwaVolume⁻¹ * densityConstant) := hlower

/-- Centered-CWA specialization of the final cardinality coefficient. -/
theorem pure_wz2_final_cardinality_from_centered_bounds
    {delta targetScale scaleExponent cardLoss thinningEta
      inputEta pruneEta : ℝ}
    (hdelta : 0 < delta)
    (htarget : 0 < targetScale)
    (htargetOne : targetScale ≤ 1)
    (htargetUpper :
      targetScale ≤ Real.rpow delta scaleExponent)
    (hcardGap : 0 ≤ cardLoss - thinningEta)
    (hthinningEta : 0 ≤ thinningEta)
    (net : TubeDensityTestNet targetScale)
    (hnetLoss : net.lossFactor ≤ 10 ^ 7)
    (densityConstant : ENNReal)
    (hDensity :
      ENNReal.ofReal (1 / 12000000 : ℝ) *
          Kakeya.realRpowENN delta pruneEta ≤
        densityConstant)
    (hCwaVolume :
      ((Kakeya.realRpowENN delta pruneEta)⁻¹ *
          ((4000000 : ENNReal) *
            Kakeya.realRpowENN delta (-inputEta))) *
          Kakeya.deltaTubeVolume targetScale ≤
        (48000000 : ENNReal) *
          Kakeya.realRpowENN delta
            (-(inputEta + pruneEta)) *
          Kakeya.realRpowENN targetScale 2)
    (habsorb :
      ENNReal.ofReal
          (2 * 97200000000000001 *
            12000000 ^ 2 * 48000000 : ℝ) *
          Kakeya.realRpowENN delta
            (scaleExponent * (cardLoss - thinningEta) -
              inputEta - 3 * pruneEta) ≤
        1) :
    Kakeya.realRpowENN targetScale (-2 + cardLoss) ≤
      (pureWZ2ThinnedAnalyticConflictBound
          net thinningEta + 1)⁻¹ *
        densityConstant *
        ((1 / 2 : ENNReal) *
          (((Kakeya.realRpowENN delta pruneEta)⁻¹ *
              ((4000000 : ENNReal) *
                Kakeya.realRpowENN delta (-inputEta))) *
              Kakeya.deltaTubeVolume targetScale)⁻¹ *
          densityConstant) := by
  have hCwaInverse :=
    pure_wz2_centeredCWA_volume_inv_lower
      hdelta htarget hCwaVolume
  exact
    pure_wz2_final_cardinality_coefficient
      hdelta htarget htargetOne htargetUpper
      hcardGap hthinningEta net hnetLoss densityConstant
      (((Kakeya.realRpowENN delta pruneEta)⁻¹ *
          ((4000000 : ENNReal) *
            Kakeya.realRpowENN delta (-inputEta))) *
        Kakeya.deltaTubeVolume targetScale)
      hDensity hCwaInverse habsorb

/-- The polynomial test-net failure term is bounded by the source-scale
exponential domination inequality. -/
theorem pure_wz2_density_net_failure_at_target
    {delta targetScale scaleExponent thinningEta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (htarget : 0 < targetScale)
    (hdeltaTarget : delta ≤ targetScale)
    (htargetUpper :
      targetScale ≤ Real.rpow delta scaleExponent)
    (hscaleExponent : 0 ≤ scaleExponent)
    (hthinningEta : 0 < thinningEta)
    (net : TubeDensityTestNet targetScale)
    (hnetCard :
      (net.testSets.card : ℝ) ≤
        (1 / targetScale) ^ (200 : ℕ))
    (hsourceFailure :
      Real.rpow (1 / delta) (200 : ℝ) *
          Real.exp (-(11 - Real.exp 1) *
            Real.rpow delta
              (-(scaleExponent * thinningEta))) <
        1 / 16) :
    (net.testSets.card : ℝ) *
        Real.exp (-(11 - Real.exp 1) *
          (Kakeya.realRpowENN targetScale
            (-thinningEta)).toReal) <
      1 / 16 := by
  have htargetInv :
      1 / targetScale ≤
        1 / delta :=
    one_div_le_one_div_of_le hdelta hdeltaTarget
  have hnetSource :
      (net.testSets.card : ℝ) ≤
        (1 / delta) ^ (200 : ℕ) := by
    calc
      (net.testSets.card : ℝ) ≤
          (1 / targetScale) ^ (200 : ℕ) := hnetCard
      _ ≤ (1 / delta) ^ (200 : ℕ) := by
        exact pow_le_pow_left₀ (by positivity) htargetInv 200
  have htargetPower :
      (Kakeya.realRpowENN targetScale
        (-thinningEta)).toReal =
        Real.rpow targetScale (-thinningEta) := by
    exact
      ENNReal.toReal_ofReal
        (Real.rpow_nonneg htarget.le _)
  have htargetExponent :
      Real.rpow delta
          (-(scaleExponent * thinningEta)) ≤
        Real.rpow targetScale (-thinningEta) := by
    have hmain :
        Real.rpow (Real.rpow delta scaleExponent)
            (-thinningEta) ≤
          Real.rpow targetScale (-thinningEta) :=
      Real.rpow_le_rpow_of_nonpos
        htarget htargetUpper
        (by linarith : -thinningEta ≤ 0)
    have hidentity :
        Real.rpow (Real.rpow delta scaleExponent)
            (-thinningEta) =
          Real.rpow delta
            (-(scaleExponent * thinningEta)) := by
      calc
        Real.rpow (Real.rpow delta scaleExponent)
            (-thinningEta) =
          Real.rpow delta
            (scaleExponent * (-thinningEta)) :=
              (Real.rpow_mul hdelta.le
                scaleExponent (-thinningEta)).symm
        _ = Real.rpow delta
            (-(scaleExponent * thinningEta)) := by
              congr 1
              ring
    rw [hidentity] at hmain
    exact hmain
  have hexp :
      Real.exp (-(11 - Real.exp 1) *
          Real.rpow targetScale (-thinningEta)) ≤
        Real.exp (-(11 - Real.exp 1) *
          Real.rpow delta
            (-(scaleExponent * thinningEta))) := by
    apply Real.exp_le_exp.mpr
    have hcoefficient : 0 < 11 - Real.exp 1 := by
      linarith [Real.exp_one_lt_three]
    nlinarith
  rw [htargetPower]
  calc
    (net.testSets.card : ℝ) *
        Real.exp (-(11 - Real.exp 1) *
          Real.rpow targetScale (-thinningEta)) ≤
      (1 / delta) ^ (200 : ℕ) *
        Real.exp (-(11 - Real.exp 1) *
          Real.rpow delta
            (-(scaleExponent * thinningEta))) := by
      calc
        (net.testSets.card : ℝ) *
            Real.exp (-(11 - Real.exp 1) *
              Real.rpow targetScale (-thinningEta)) ≤
          (1 / delta) ^ (200 : ℕ) *
            Real.exp (-(11 - Real.exp 1) *
              Real.rpow targetScale (-thinningEta)) :=
          mul_le_mul_of_nonneg_right hnetSource
            (Real.exp_pos _).le
        _ ≤
          (1 / delta) ^ (200 : ℕ) *
            Real.exp (-(11 - Real.exp 1) *
              Real.rpow delta
                (-(scaleExponent * thinningEta))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
    _ < 1 / 16 := by
      have hpower :
          Real.rpow (1 / delta) (200 : ℝ) =
            (1 / delta) ^ (200 : ℕ) := by
        convert Real.rpow_natCast (1 / delta) 200 using 1 <;>
          norm_num
      rw [hpower] at hsourceFailure
      exact hsourceFailure

end Kakeya.Assouad

end
