import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperScalarBounds
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# Pre-runtime envelope for the first four-call scalar

The first covering constant is selected on a runtime ordered pair.  This file
keeps its scale dependence explicit and bounds it by a fixed power of the
original fine scale.  Consequently the nested-interval absorption cutoff can
be selected before the runtime family and ordered pair exist.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- The loss exponent paid by the first, non-square-root arithmetic
requirement after using `tau ≤ sqrt rho` and the paper target scale
`rho^(1-discreteLoss)`. -/
noncomputable def proposition63FourCallPaperFirstExponent
    (sigma discreteLoss normalizationLoss outputLoss epsilon₁ angular : ℝ) : ℝ :=
  (1 / 2 : ℝ) + 7 * epsilon₁ + angular + normalizationLoss -
    discreteLoss * sigma + 2 * (1 - discreteLoss) * outputLoss

noncomputable def proposition63FourCallPaperNormalizedFirstExponent
    (_discreteLoss normalizationLoss outputLoss epsilon₁ angular : ℝ) : ℝ :=
  normalizationLoss + 7 * epsilon₁ + angular +
    2 * (1 - outputLoss) * outputLoss

theorem Proposition63FourCallInnerLossSeed.normalizedFirstExponent_lt
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed sigma outputLoss discreteLoss) :
    proposition63FourCallPaperNormalizedFirstExponent discreteLoss
        seed.schedule.third.normalizationLoss seed.schedule.thirdOutputLoss
        seed.epsilon₁ seed.paperAngularExponent <
      seed.alignedAbsorption.internalLoss := by
  rw [seed.alignedAbsorption.internal_loss_eq]
  rw [seed.epsilon₁_eq]
  have angular_le : seed.paperAngularExponent ≤ discreteLoss / 4 := by
    rw [seed.paperAngularExponent_eq,
      proposition63FourCallPaperAngularExponent]
    exact min_le_left _ _
  have angular_pos := seed.paperAngularExponent_pos
  have third_output_lt : seed.schedule.thirdOutputLoss <
      seed.paperAngularExponent * sigma / 3200 := by
    rw [seed.schedule.thirdOutputLoss_eq]
    nlinarith [seed.schedule.fourth.sourceLoss_le_half,
      seed.criticalStructural_le_paperSigma,
      seed.fourthKernel.internalLoss_lt_tail,
      seed.fourthNormalization_lt_internalLoss]
  have third_normalization_lt : seed.schedule.third.normalizationLoss <
      seed.paperAngularExponent * sigma / 3200 :=
    seed.schedule.third.normalizationLoss_lt_output.trans third_output_lt
  have sigma_one := seed.sigma_lt_one
  have output_nonneg := seed.schedule.thirdOutputLoss_pos.le
  have discrete_lt_one : discreteLoss < 1 := by
    have robust_pos := seed.robustExponent_pos
    rw [seed.robustExponent_eq] at robust_pos
    linarith
  dsimp only [proposition63FourCallPaperNormalizedFirstExponent]
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - discreteLoss) output_nonneg]

/-- Exact simplification of the normalized first arithmetic quotient when the
paper target is the lower endpoint of its admissible window. -/
theorem proposition63_four_call_normalized_first_analytic_quotient_eq
    {rho tau sigma normalizationLoss outputLoss epsilon₁ angular : ℝ}
    (rho_pos : 0 < rho) (tau_pos : 0 < tau) :
    (proposition63RobustTauTotalVolume rho sigma normalizationLoss outputLoss
          tau tau /
        (Real.rpow rho (1 + 7 * epsilon₁ + angular) * tau ^ 2 / 200)) /
        Real.rpow (tau / rho) (1 - sigma) =
      (216 * 27 * 200 : ℝ) *
        Real.rpow rho (-(normalizationLoss + 7 * epsilon₁ + angular)) *
        Real.rpow tau (-2 * outputLoss) := by
  have ratio_pos : 0 < tau / rho := div_pos tau_pos rho_pos
  have denominator_pos : 0 <
      Real.rpow rho (1 + 7 * epsilon₁ + angular) * tau ^ 2 / 200 := by
    exact div_pos (mul_pos (Real.rpow_pos_of_pos rho_pos _)
      (sq_pos_of_pos tau_pos)) (by norm_num)
  have ratio_power : Real.rpow (tau / rho) (1 - sigma) =
      Real.rpow tau (1 - sigma) / Real.rpow rho (1 - sigma) :=
    Real.div_rpow tau_pos.le rho_pos.le _
  rw [proposition63RobustTauTotalVolume]
  rw [show 3 * tau / tau = 3 by field_simp]
  rw [ratio_power]
  have rho_power_pos : 0 < Real.rpow rho (1 - sigma) :=
    Real.rpow_pos_of_pos rho_pos _
  have tau_power_pos : 0 < Real.rpow tau (1 - sigma) :=
    Real.rpow_pos_of_pos tau_pos _
  have rho_den_pos : 0 < Real.rpow rho (1 + 7 * epsilon₁ + angular) :=
    Real.rpow_pos_of_pos rho_pos _
  have tau_two_pos : 0 < tau ^ 2 := sq_pos_of_pos tau_pos
  field_simp [tau_pos.ne', ratio_pos.ne', rho_power_pos.ne',
    tau_power_pos.ne', rho_den_pos.ne', tau_two_pos.ne']
  have hrho : Real.rpow rho (sigma - normalizationLoss) *
        Real.rpow rho (1 - sigma) =
      Real.rpow rho (1 + 7 * epsilon₁ + angular) *
        Real.rpow rho (-(normalizationLoss + 7 * epsilon₁ + angular)) := by
    calc
      Real.rpow rho (sigma - normalizationLoss) *
            Real.rpow rho (1 - sigma) =
          Real.rpow rho ((sigma - normalizationLoss) + (1 - sigma)) :=
        (Real.rpow_add rho_pos _ _).symm
      _ = Real.rpow rho ((1 + 7 * epsilon₁ + angular) +
            (-(normalizationLoss + 7 * epsilon₁ + angular))) := by
        congr 1
        ring
      _ = Real.rpow rho (1 + 7 * epsilon₁ + angular) *
            Real.rpow rho (-(normalizationLoss + 7 * epsilon₁ + angular)) :=
        Real.rpow_add rho_pos _ _
  have htau : Real.rpow tau (3 - sigma - 2 * outputLoss) =
      tau ^ 2 * Real.rpow tau (1 - sigma) *
        Real.rpow tau (-(2 * outputLoss)) := by
    calc
      Real.rpow tau (3 - sigma - 2 * outputLoss) =
          Real.rpow tau ((2 : ℝ) + (1 - sigma) + (-(2 * outputLoss))) := by
        congr 1
        ring
      _ = Real.rpow tau ((2 : ℝ) + (1 - sigma)) *
            Real.rpow tau (-(2 * outputLoss)) := Real.rpow_add tau_pos _ _
      _ = (Real.rpow tau (2 : ℝ) * Real.rpow tau (1 - sigma)) *
            Real.rpow tau (-(2 * outputLoss)) := by
        exact congrArg
          (fun value : ℝ => value * Real.rpow tau (-(2 * outputLoss)))
          (Real.rpow_add tau_pos (2 : ℝ) (1 - sigma))
      _ = tau ^ 2 * Real.rpow tau (1 - sigma) *
            Real.rpow tau (-(2 * outputLoss)) := by
        exact congrArg
          (fun value : ℝ => value * Real.rpow tau (1 - sigma) *
            Real.rpow tau (-(2 * outputLoss)))
          (Real.rpow_natCast tau 2)
  calc
    3 ^ 3 * Real.rpow rho (sigma - normalizationLoss) *
          Real.rpow tau (3 - sigma - 2 * outputLoss) *
          Real.rpow rho (1 - sigma) =
        27 * (Real.rpow rho (sigma - normalizationLoss) *
          Real.rpow rho (1 - sigma)) *
          Real.rpow tau (3 - sigma - 2 * outputLoss) := by ring
    _ = 27 * (Real.rpow rho (1 + 7 * epsilon₁ + angular) *
          Real.rpow rho (-(normalizationLoss + 7 * epsilon₁ + angular))) *
          (tau ^ 2 * Real.rpow tau (1 - sigma) *
            Real.rpow tau (-(2 * outputLoss))) := by rw [hrho, htau]
    _ = Real.rpow rho (1 + 7 * epsilon₁ + angular) * tau ^ 2 *
          Real.rpow tau (1 - sigma) * 27 *
          Real.rpow rho (-(normalizationLoss + 7 * epsilon₁ + angular)) *
          Real.rpow tau (-(2 * outputLoss)) := by ring

/-- Enlarging the target scale inside its legal range only decreases the
normalized first arithmetic requirement. -/
theorem proposition63_four_call_normalized_first_requirement_mono_target
    {rho tau sigma normalizationLoss outputLoss targetScale epsilon₁ angular
      incidence : ℝ} {coefficient : NNReal}
    (rho_pos : 0 < rho) (tau_pos : 0 < tau)
    (target_pos : 0 < targetScale) (tau_le_target : tau ≤ targetScale)
    (incidence_nonneg : 0 ≤ incidence)
    (target_decay_nonneg : 0 ≤ sigma + 2 * outputLoss) :
    proposition63FourCallFirstArithmeticRequirement rho tau sigma
        normalizationLoss outputLoss targetScale epsilon₁ angular incidence
        coefficient /
      Kakeya.realRpowENN (tau / rho) (1 - sigma) ≤
    proposition63FourCallFirstArithmeticRequirement rho tau sigma
        normalizationLoss outputLoss tau epsilon₁ angular incidence
        coefficient /
      Kakeya.realRpowENN (tau / rho) (1 - sigma) := by
  have target_decay : Real.rpow targetScale (-(sigma + 2 * outputLoss)) ≤
      Real.rpow tau (-(sigma + 2 * outputLoss)) :=
    Real.rpow_le_rpow_of_nonpos tau_pos tau_le_target (by linarith)
  unfold proposition63FourCallFirstArithmeticRequirement
  apply ENNReal.div_le_div_right
  apply ENNReal.ofReal_mono
  unfold proposition63RobustTauTotalVolume
  have target_ne := target_pos.ne'
  have tau_ne := tau_pos.ne'
  have target_identity : ((3 * tau) / targetScale) ^ 3 *
      Real.rpow targetScale (3 - sigma - 2 * outputLoss) =
      27 * tau ^ 3 * Real.rpow targetScale
        (-(sigma + 2 * outputLoss)) := by
    have hsplit : Real.rpow targetScale (3 - sigma - 2 * outputLoss) =
        Real.rpow targetScale (3 : ℝ) *
          Real.rpow targetScale (-(sigma + 2 * outputLoss)) := by
      calc
        Real.rpow targetScale (3 - sigma - 2 * outputLoss) =
            Real.rpow targetScale ((3 : ℝ) +
              (-(sigma + 2 * outputLoss))) := by
          congr 1
          ring
        _ = Real.rpow targetScale (3 : ℝ) *
              Real.rpow targetScale (-(sigma + 2 * outputLoss)) :=
          Real.rpow_add target_pos _ _
    rw [hsplit]
    have target_cube : Real.rpow targetScale (3 : ℝ) = targetScale ^ 3 :=
      Real.rpow_natCast targetScale 3
    rw [target_cube]
    field_simp [target_ne]
    ring
  have tau_identity : ((3 * tau) / tau) ^ 3 *
      Real.rpow tau (3 - sigma - 2 * outputLoss) =
      27 * tau ^ 3 * Real.rpow tau (-(sigma + 2 * outputLoss)) := by
    have hsplit : Real.rpow tau (3 - sigma - 2 * outputLoss) =
        Real.rpow tau (3 : ℝ) *
          Real.rpow tau (-(sigma + 2 * outputLoss)) := by
      calc
        Real.rpow tau (3 - sigma - 2 * outputLoss) =
            Real.rpow tau ((3 : ℝ) +
              (-(sigma + 2 * outputLoss))) := by
          congr 1
          ring
        _ = Real.rpow tau (3 : ℝ) *
              Real.rpow tau (-(sigma + 2 * outputLoss)) :=
          Real.rpow_add tau_pos _ _
    rw [hsplit]
    have tau_cube : Real.rpow tau (3 : ℝ) = tau ^ 3 :=
      Real.rpow_natCast tau 3
    rw [tau_cube]
    field_simp [tau_ne]
    ring
  have rho_power_nonneg : 0 ≤ Real.rpow rho (sigma - normalizationLoss) :=
    Real.rpow_nonneg rho_pos.le _
  have denominator_pos : 0 <
      Real.rpow rho (1 + 7 * epsilon₁ + angular) * tau ^ 2 / 200 := by
    exact div_pos (mul_pos (Real.rpow_pos_of_pos rho_pos _)
      (sq_pos_of_pos tau_pos)) (by norm_num)
  have core : 216 * (27 * tau ^ 3 *
      Real.rpow targetScale (-(sigma + 2 * outputLoss))) *
      Real.rpow rho (sigma - normalizationLoss) ≤
      216 * (27 * tau ^ 3 *
        Real.rpow tau (-(sigma + 2 * outputLoss))) *
        Real.rpow rho (sigma - normalizationLoss) := by
    gcongr
  have numerator : 216 * ((3 * tau / targetScale) ^ 3 *
        Real.rpow targetScale (3 - sigma - 2 * outputLoss)) *
        Real.rpow rho (sigma - normalizationLoss) ≤
      216 * ((3 * tau / tau) ^ 3 *
        Real.rpow tau (3 - sigma - 2 * outputLoss)) *
        Real.rpow rho (sigma - normalizationLoss) := by
    rw [target_identity, tau_identity]
    simpa only [mul_assoc] using core
  have numerator' : 216 * (3 * tau / targetScale) ^ 3 *
        Real.rpow rho (sigma - normalizationLoss) *
        Real.rpow targetScale (3 - sigma - 2 * outputLoss) ≤
      216 * (3 * tau / tau) ^ 3 *
        Real.rpow rho (sigma - normalizationLoss) *
        Real.rpow tau (3 - sigma - 2 * outputLoss) := by
    calc
      216 * (3 * tau / targetScale) ^ 3 *
            Real.rpow rho (sigma - normalizationLoss) *
            Real.rpow targetScale (3 - sigma - 2 * outputLoss) =
          216 * ((3 * tau / targetScale) ^ 3 *
            Real.rpow targetScale (3 - sigma - 2 * outputLoss)) *
            Real.rpow rho (sigma - normalizationLoss) := by ring
      _ ≤ 216 * ((3 * tau / tau) ^ 3 *
            Real.rpow tau (3 - sigma - 2 * outputLoss)) *
            Real.rpow rho (sigma - normalizationLoss) := numerator
      _ = 216 * (3 * tau / tau) ^ 3 *
            Real.rpow rho (sigma - normalizationLoss) *
            Real.rpow tau (3 - sigma - 2 * outputLoss) := by ring
  have quotient := div_le_div_of_nonneg_right numerator' denominator_pos.le
  exact mul_le_mul_of_nonneg_right
    quotient (by
      have coarse_nonneg : 0 ≤ proposition63DependentCoarseIncidence rho
          incidence coefficient := by
        unfold proposition63DependentCoarseIncidence
        positivity
      have slab_nonneg : 0 ≤ proposition63DependentSlabWidth rho tau
          (proposition63DependentCoarseIncidence rho incidence coefficient)
          coefficient := by
        unfold proposition63DependentSlabWidth
        positivity
      positivity)

/-- The Córdoba slab estimate used for the first target remains linear in
`rho` for every interval scale between `rho` and `sqrt rho`. -/
theorem proposition63_dependent_interval_slab_width_le
    {rho tau incidence : ℝ} {coefficient : NNReal}
    (rho_pos : 0 < rho) (_rho_le_one : rho ≤ 1)
    (rho_le_tau : rho ≤ tau) (tau_le_sqrt : tau ≤ Real.sqrt rho)
    (incidence_nonneg : 0 ≤ incidence) (incidence_le : incidence ≤ rho)
    (coefficient_one : 1 ≤ (coefficient : ℝ)) :
    proposition63DependentSlabWidth rho tau
        (proposition63DependentCoarseIncidence rho incidence coefficient)
        coefficient ≤
      167 * (coefficient : ℝ) * rho := by
  have rho_nonneg : 0 ≤ rho := rho_pos.le
  have sqrt_nonneg : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg _
  have sqrt_sq : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt rho_nonneg
  have rho_le_sqrt : rho ≤ Real.sqrt rho := rho_le_tau.trans tau_le_sqrt
  have tau_nonneg : 0 ≤ tau := rho_pos.le.trans rho_le_tau
  have coarse_le := proposition63_dependent_coarse_incidence_le rho_pos
    incidence_nonneg incidence_le coefficient_one
  have coefficient_nonneg : 0 ≤ (coefficient : ℝ) := by positivity
  have first_le : tau + 12 * rho ≤ 13 * Real.sqrt rho := by
    linarith
  have coarse_nonneg :
      0 ≤ proposition63DependentCoarseIncidence rho incidence coefficient := by
    dsimp only [proposition63DependentCoarseIncidence]
    positivity
  have second_le :
      2 * proposition63DependentCoarseIncidence rho incidence coefficient +
          3 * (coefficient : ℝ) * tau ≤
        11 * (coefficient : ℝ) * Real.sqrt rho := by
    nlinarith
  dsimp only [proposition63DependentSlabWidth]
  calc
    (tau + 12 * rho) *
          (2 * proposition63DependentCoarseIncidence rho incidence coefficient +
            3 * (coefficient : ℝ) * tau) + 24 * rho
        ≤ (13 * Real.sqrt rho) *
            (11 * (coefficient : ℝ) * Real.sqrt rho) + 24 * rho := by
          gcongr
    _ = 143 * (coefficient : ℝ) * rho + 24 * rho := by
      nlinarith [sqrt_sq]
    _ ≤ 167 * (coefficient : ℝ) * rho := by
      nlinarith

/-- The factor-three alignment between the requested lower target and the
actual interval scale costs at most a factor nine in the relevant negative
power. -/
theorem proposition63_interval_tau_negative_power_le
    {rho tau outputLoss : ℝ}
    (rho_pos : 0 < rho)
    (output_pos : 0 < outputLoss) (output_le_one : outputLoss ≤ 1)
    (target_le_tau : Real.rpow rho (1 - outputLoss) ≤ 3 * tau) :
    Kakeya.realRpowENN tau (-2 * outputLoss) ≤
      (9 : ENNReal) * Kakeya.realRpowENN rho
        (-(2 * (1 - outputLoss) * outputLoss)) := by
  let lower : ℝ := Real.rpow rho (1 - outputLoss) / 3
  have lower_pos : 0 < lower := by
    dsimp only [lower]
    exact div_pos (Real.rpow_pos_of_pos rho_pos _) (by norm_num)
  have lower_le_tau : lower ≤ tau := by
    dsimp only [lower]
    linarith
  have hmono : Real.rpow tau (-2 * outputLoss) ≤
      Real.rpow lower (-2 * outputLoss) :=
    Real.rpow_le_rpow_of_nonpos lower_pos lower_le_tau (by linarith)
  have three_power : Real.rpow 3 (2 * outputLoss) ≤ 9 := by
    calc
      Real.rpow 3 (2 * outputLoss) ≤ Real.rpow 3 2 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 9 := by norm_num
  have lower_power : Real.rpow lower (-2 * outputLoss) =
      Real.rpow 3 (2 * outputLoss) *
        Real.rpow rho (-(2 * (1 - outputLoss) * outputLoss)) := by
    dsimp only [lower]
    have hdiv := Real.div_rpow
      (Real.rpow_nonneg rho_pos.le (1 - outputLoss))
      (by norm_num : (0 : ℝ) ≤ 3) (-2 * outputLoss)
    have hthreeNeg : Real.rpow 3 (-2 * outputLoss) =
        (Real.rpow 3 (2 * outputLoss))⁻¹ := by
      rw [show -2 * outputLoss = -(2 * outputLoss) by ring]
      exact Real.rpow_neg (by norm_num) _
    have hrhoNeg : Real.rpow (Real.rpow rho (1 - outputLoss))
        (-2 * outputLoss) =
        (Real.rpow (Real.rpow rho (1 - outputLoss))
          (2 * outputLoss))⁻¹ := by
      rw [show -2 * outputLoss = -(2 * outputLoss) by ring]
      exact Real.rpow_neg (Real.rpow_nonneg rho_pos.le _) _
    have nested : Real.rpow (Real.rpow rho (1 - outputLoss))
        (2 * outputLoss) =
        Real.rpow rho ((1 - outputLoss) * (2 * outputLoss)) :=
      (Real.rpow_mul rho_pos.le _ _).symm
    have three_pos : 0 < Real.rpow 3 (2 * outputLoss) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have rho_power_pos : 0 < Real.rpow rho
        ((1 - outputLoss) * (2 * outputLoss)) :=
      Real.rpow_pos_of_pos rho_pos _
    calc
      Real.rpow (Real.rpow rho (1 - outputLoss) / (3 : ℝ))
            (-2 * outputLoss) =
          Real.rpow (Real.rpow rho (1 - outputLoss)) (-2 * outputLoss) /
            Real.rpow 3 (-2 * outputLoss) := hdiv
      _ = (Real.rpow (Real.rpow rho (1 - outputLoss))
              (2 * outputLoss))⁻¹ /
            (Real.rpow 3 (2 * outputLoss))⁻¹ := by
        rw [hrhoNeg, hthreeNeg]
      _ = Real.rpow 3 (2 * outputLoss) *
            (Real.rpow (Real.rpow rho (1 - outputLoss))
              (2 * outputLoss))⁻¹ := by
        field_simp [three_pos.ne', rho_power_pos.ne', nested]
      _ = Real.rpow 3 (2 * outputLoss) *
            (Real.rpow rho ((1 - outputLoss) * (2 * outputLoss)))⁻¹ := by
        rw [nested]
      _ = Real.rpow 3 (2 * outputLoss) *
            Real.rpow rho (-((1 - outputLoss) * (2 * outputLoss))) := by
        exact congrArg (fun value : ℝ =>
          Real.rpow 3 (2 * outputLoss) * value)
          (Real.rpow_neg rho_pos.le
            ((1 - outputLoss) * (2 * outputLoss))).symm
      _ = Real.rpow 3 (2 * outputLoss) *
            Real.rpow rho (-(2 * (1 - outputLoss) * outputLoss)) := by
        congr 1
        ring
  have real_bound : Real.rpow tau (-2 * outputLoss) ≤
      9 * Real.rpow rho (-(2 * (1 - outputLoss) * outputLoss)) := by
    calc
      Real.rpow tau (-2 * outputLoss) ≤
          Real.rpow lower (-2 * outputLoss) := hmono
      _ = Real.rpow 3 (2 * outputLoss) *
            Real.rpow rho (-(2 * (1 - outputLoss) * outputLoss)) := lower_power
      _ ≤ 9 * Real.rpow rho
            (-(2 * (1 - outputLoss) * outputLoss)) := by
        exact mul_le_mul_of_nonneg_right three_power
          (Real.rpow_nonneg rho_pos.le _)
  simp only [Kakeya.realRpowENN]
  rw [show (9 : ENNReal) = ENNReal.ofReal (9 : ℝ) by norm_num]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9)]
  exact ENNReal.ofReal_mono real_bound

/-- The normalized first constant is controlled by the small loss exponent,
provided the interval-scale negative power has already been compared to the
aligned coarse scale. -/
theorem proposition63_four_call_normalized_first_requirement_le
    {rho tau sigma normalizationLoss outputLoss targetScale epsilon₁ angular
      incidence : ℝ} {coefficient : NNReal}
    (rho_pos : 0 < rho) (rho_le_one : rho ≤ 1)
    (rho_le_tau : rho ≤ tau) (tau_le_sqrt : tau ≤ Real.sqrt rho)
    (target_pos : 0 < targetScale) (tau_le_target : tau ≤ targetScale)
    (target_decay_nonneg : 0 ≤ sigma + 2 * outputLoss)
    (incidence_nonneg : 0 ≤ incidence) (incidence_le : incidence ≤ rho)
    (coefficient_one : 1 ≤ (coefficient : ℝ))
    (tau_power : Kakeya.realRpowENN tau (-2 * outputLoss) ≤
      (9 : ENNReal) * Kakeya.realRpowENN rho
        (-(2 * (1 - outputLoss) * outputLoss))) :
    proposition63FourCallFirstArithmeticRequirement rho tau sigma
        normalizationLoss outputLoss targetScale epsilon₁ angular incidence
        coefficient /
      Kakeya.realRpowENN (tau / rho) (1 - sigma) ≤
    (3527193600 : ENNReal) * (coefficient : ENNReal) ^ 2 *
      Kakeya.realRpowENN rho
        (-(proposition63FourCallPaperNormalizedFirstExponent 0
          normalizationLoss outputLoss epsilon₁ angular)) := by
  have tau_pos : 0 < tau := rho_pos.trans_le rho_le_tau
  have mono := proposition63_four_call_normalized_first_requirement_mono_target
    (rho := rho) (tau := tau) (sigma := sigma)
    (normalizationLoss := normalizationLoss) (outputLoss := outputLoss)
    (targetScale := targetScale) (epsilon₁ := epsilon₁) (angular := angular)
    (incidence := incidence) (coefficient := coefficient) rho_pos tau_pos
    target_pos tau_le_target incidence_nonneg target_decay_nonneg
  apply mono.trans
  have slab_le := proposition63_dependent_interval_slab_width_le rho_pos
    rho_le_one rho_le_tau tau_le_sqrt incidence_nonneg incidence_le
    coefficient_one
  have slab_div_le : proposition63DependentSlabWidth rho tau
      (proposition63DependentCoarseIncidence rho incidence coefficient)
      coefficient / rho ≤ 167 * (coefficient : ℝ) :=
    (div_le_iff₀ rho_pos).2 (by nlinarith)
  have cordoba_le : 2 * proposition63DependentSlabWidth rho tau
      (proposition63DependentCoarseIncidence rho incidence coefficient)
      coefficient / rho + 2 ≤ 336 * (coefficient : ℝ) ^ 2 := by
    calc
      2 * proposition63DependentSlabWidth rho tau
            (proposition63DependentCoarseIncidence rho incidence coefficient)
            coefficient / rho + 2 =
          2 * (proposition63DependentSlabWidth rho tau
            (proposition63DependentCoarseIncidence rho incidence coefficient)
            coefficient / rho) + 2 := by ring
      _ ≤ 2 * (167 * (coefficient : ℝ)) + 2 := by gcongr
      _ = 334 * (coefficient : ℝ) + 2 := by ring
      _ ≤ 336 * (coefficient : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((coefficient : ℝ) - 1)]
  let volumeQuotient : ℝ :=
    proposition63RobustTauTotalVolume rho sigma normalizationLoss outputLoss
        tau tau /
      (Real.rpow rho (1 + 7 * epsilon₁ + angular) * tau ^ 2 / 200)
  let cordoba : ℝ := 2 * proposition63DependentSlabWidth rho tau
      (proposition63DependentCoarseIncidence rho incidence coefficient)
      coefficient / rho + 2
  let ratioPower : ℝ := Real.rpow (tau / rho) (1 - sigma)
  have ratio_pos : 0 < ratioPower := by
    dsimp only [ratioPower]
    exact Real.rpow_pos_of_pos (div_pos tau_pos rho_pos) _
  have volume_nonneg : 0 ≤ volumeQuotient := by
    dsimp only [volumeQuotient, proposition63RobustTauTotalVolume]
    have ratio_nonneg : 0 ≤ (3 * tau / tau) ^ 3 := by positivity
    have numerator_nonneg : 0 ≤ 216 * (3 * tau / tau) ^ 3 *
        Real.rpow rho (sigma - normalizationLoss) *
        Real.rpow tau (3 - sigma - 2 * outputLoss) := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ratio_nonneg)
        (Real.rpow_nonneg rho_pos.le _)) (Real.rpow_nonneg tau_pos.le _)
    have denominator_nonneg : 0 ≤
        Real.rpow rho (1 + 7 * epsilon₁ + angular) * tau ^ 2 / 200 := by
      exact div_nonneg (mul_nonneg (Real.rpow_nonneg rho_pos.le _)
        (sq_nonneg tau)) (by norm_num)
    exact div_nonneg numerator_nonneg denominator_nonneg
  have cordoba_nonneg : 0 ≤ cordoba := by
    dsimp only [cordoba]
    have coarse_nonneg : 0 ≤ proposition63DependentCoarseIncidence rho
        incidence coefficient := by
      unfold proposition63DependentCoarseIncidence
      positivity
    have slab_nonneg : 0 ≤ proposition63DependentSlabWidth rho tau
        (proposition63DependentCoarseIncidence rho incidence coefficient)
        coefficient := by
      unfold proposition63DependentSlabWidth
      positivity
    positivity
  have analytic := proposition63_four_call_normalized_first_analytic_quotient_eq
    (rho := rho) (tau := tau) (sigma := sigma)
    (normalizationLoss := normalizationLoss) (outputLoss := outputLoss)
    (epsilon₁ := epsilon₁) (angular := angular) rho_pos tau_pos
  have real_bound : volumeQuotient / ratioPower * cordoba ≤
      (391910400 : ℝ) * (coefficient : ℝ) ^ 2 *
        Real.rpow rho (-(normalizationLoss + 7 * epsilon₁ + angular)) *
        Real.rpow tau (-2 * outputLoss) := by
    rw [show volumeQuotient / ratioPower =
        (216 * 27 * 200 : ℝ) *
          Real.rpow rho (-(normalizationLoss + 7 * epsilon₁ + angular)) *
          Real.rpow tau (-2 * outputLoss) by simpa only [volumeQuotient,
            ratioPower] using analytic]
    have base_nonneg : 0 ≤ (216 * 27 * 200 : ℝ) *
        Real.rpow rho (-(normalizationLoss + 7 * epsilon₁ + angular)) *
        Real.rpow tau (-2 * outputLoss) := by
      exact mul_nonneg (mul_nonneg (by norm_num)
        (Real.rpow_nonneg rho_pos.le _)) (Real.rpow_nonneg tau_pos.le _)
    calc
      (216 * 27 * 200 : ℝ) *
            Real.rpow rho (-(normalizationLoss + 7 * epsilon₁ + angular)) *
            Real.rpow tau (-2 * outputLoss) * cordoba ≤
          (216 * 27 * 200 : ℝ) *
            Real.rpow rho (-(normalizationLoss + 7 * epsilon₁ + angular)) *
            Real.rpow tau (-2 * outputLoss) *
            (336 * (coefficient : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left cordoba_le base_nonneg
      _ = (391910400 : ℝ) * (coefficient : ℝ) ^ 2 *
            Real.rpow rho (-(normalizationLoss + 7 * epsilon₁ + angular)) *
            Real.rpow tau (-2 * outputLoss) := by ring
  have enn_bound : proposition63FourCallFirstArithmeticRequirement rho tau sigma
        normalizationLoss outputLoss tau epsilon₁ angular incidence coefficient /
      Kakeya.realRpowENN (tau / rho) (1 - sigma) ≤
      (391910400 : ENNReal) * (coefficient : ENNReal) ^ 2 *
        Kakeya.realRpowENN rho
          (-(normalizationLoss + 7 * epsilon₁ + angular)) *
        Kakeya.realRpowENN tau (-2 * outputLoss) := by
    unfold proposition63FourCallFirstArithmeticRequirement
    change ENNReal.ofReal (volumeQuotient * cordoba) /
        ENNReal.ofReal ratioPower ≤ _
    rw [← ENNReal.ofReal_div_of_pos ratio_pos]
    have quotient_mul : volumeQuotient * cordoba / ratioPower =
        volumeQuotient / ratioPower * cordoba := by ring
    rw [quotient_mul]
    calc
      ENNReal.ofReal (volumeQuotient / ratioPower * cordoba) ≤
          ENNReal.ofReal ((391910400 : ℝ) * (coefficient : ℝ) ^ 2 *
            Real.rpow rho (-(normalizationLoss + 7 * epsilon₁ + angular)) *
            Real.rpow tau (-2 * outputLoss)) := ENNReal.ofReal_mono real_bound
      _ = (391910400 : ENNReal) * (coefficient : ENNReal) ^ 2 *
            Kakeya.realRpowENN rho
              (-(normalizationLoss + 7 * epsilon₁ + angular)) *
            Kakeya.realRpowENN tau (-2 * outputLoss) := by
        have coefficient_sq_nonneg : 0 ≤ (coefficient : ℝ) ^ 2 := sq_nonneg _
        have rho_nonneg : 0 ≤ Real.rpow rho
            (-(normalizationLoss + 7 * epsilon₁ + angular)) :=
          Real.rpow_nonneg rho_pos.le _
        have tau_nonneg : 0 ≤ Real.rpow tau (-2 * outputLoss) :=
          Real.rpow_nonneg tau_pos.le _
        have first_three_nonneg : 0 ≤ (391910400 : ℝ) *
            (coefficient : ℝ) ^ 2 *
            Real.rpow rho (-(normalizationLoss + 7 * epsilon₁ + angular)) :=
          mul_nonneg (mul_nonneg (by norm_num) coefficient_sq_nonneg) rho_nonneg
        simp only [Kakeya.realRpowENN]
        rw [show (391910400 : ℝ) * (coefficient : ℝ) ^ 2 *
              Real.rpow rho (-(normalizationLoss + 7 * epsilon₁ + angular)) *
              Real.rpow tau (-2 * outputLoss) =
            ((391910400 : ℝ) * (coefficient : ℝ) ^ 2 *
              Real.rpow rho (-(normalizationLoss + 7 * epsilon₁ + angular))) *
              Real.rpow tau (-2 * outputLoss) by ring]
        rw [ENNReal.ofReal_mul first_three_nonneg]
        have first_three : ENNReal.ofReal ((391910400 : ℝ) *
              (coefficient : ℝ) ^ 2 *
              Real.rpow rho (-(normalizationLoss + 7 * epsilon₁ + angular))) =
            (391910400 : ENNReal) * (coefficient : ENNReal) ^ 2 *
              ENNReal.ofReal
                (Real.rpow rho
                  (-(normalizationLoss + 7 * epsilon₁ + angular))) := by
          rw [show (391910400 : ℝ) * (coefficient : ℝ) ^ 2 *
              Real.rpow rho (-(normalizationLoss + 7 * epsilon₁ + angular)) =
            ((391910400 : ℝ) * (coefficient : ℝ) ^ 2) *
              Real.rpow rho
                (-(normalizationLoss + 7 * epsilon₁ + angular)) by ring]
          rw [ENNReal.ofReal_mul
            (mul_nonneg (by norm_num) coefficient_sq_nonneg),
            ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_coe_nnreal]
          norm_num
        rw [first_three]
  calc
    proposition63FourCallFirstArithmeticRequirement rho tau sigma
          normalizationLoss outputLoss tau epsilon₁ angular incidence coefficient /
        Kakeya.realRpowENN (tau / rho) (1 - sigma) ≤
        (391910400 : ENNReal) * (coefficient : ENNReal) ^ 2 *
          Kakeya.realRpowENN rho
            (-(normalizationLoss + 7 * epsilon₁ + angular)) *
          Kakeya.realRpowENN tau (-2 * outputLoss) := enn_bound
    _ ≤ (391910400 : ENNReal) * (coefficient : ENNReal) ^ 2 *
          Kakeya.realRpowENN rho
            (-(normalizationLoss + 7 * epsilon₁ + angular)) *
          ((9 : ENNReal) * Kakeya.realRpowENN rho
            (-(2 * (1 - outputLoss) * outputLoss))) := by gcongr
    _ = (3527193600 : ENNReal) * (coefficient : ENNReal) ^ 2 *
          Kakeya.realRpowENN rho
            (-(proposition63FourCallPaperNormalizedFirstExponent 0
              normalizationLoss outputLoss epsilon₁ angular)) := by
      calc
        (391910400 : ENNReal) * (coefficient : ENNReal) ^ 2 *
              Kakeya.realRpowENN rho
                (-(normalizationLoss + 7 * epsilon₁ + angular)) *
              ((9 : ENNReal) * Kakeya.realRpowENN rho
                (-(2 * (1 - outputLoss) * outputLoss))) =
            (3527193600 : ENNReal) * (coefficient : ENNReal) ^ 2 *
              (Kakeya.realRpowENN rho
                (-(normalizationLoss + 7 * epsilon₁ + angular)) *
                Kakeya.realRpowENN rho
                  (-(2 * (1 - outputLoss) * outputLoss))) := by ring
        _ = (3527193600 : ENNReal) * (coefficient : ENNReal) ^ 2 *
              Kakeya.realRpowENN rho
                (-(normalizationLoss + 7 * epsilon₁ + angular) +
                  -(2 * (1 - outputLoss) * outputLoss)) := by
          rw [realRpowENN_mul' rho_pos]
        _ = (3527193600 : ENNReal) * (coefficient : ENNReal) ^ 2 *
              Kakeya.realRpowENN rho
                (-(proposition63FourCallPaperNormalizedFirstExponent 0
                  normalizationLoss outputLoss epsilon₁ angular)) := by
          congr 1
          dsimp only [proposition63FourCallPaperNormalizedFirstExponent]
          ring

/-- Uniform fine-scale bound for the normalized first constant at one frozen
ordered pair.  Every exponent and amplitude in the conclusion precedes the
runtime family and current shading. -/
theorem proposition63_four_call_first_constant_delta_envelope
    {delta sigma discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {outputLoss incidence : ℝ}
    (seed : Proposition63FourCallInnerLossSeed sigma outputLoss discreteLoss)
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    (targetRequested : WZ2PaperRequestedScale scales.rhoHat.1)
    (coefficient : NNReal)
    (first : Proposition63FourCallFirstConstantChoice scales.rhoHat.1
      scales.tau sigma seed.schedule.third.normalizationLoss
      seed.schedule.thirdOutputLoss targetRequested.1
      seed.epsilon₁ seed.paperAngularExponent incidence coefficient)
    (delta_pos : 0 < delta) (incidence_nonneg : 0 ≤ incidence)
    (incidence_le_delta : incidence ≤ delta)
    (tau_le_target : scales.tau ≤ targetRequested.1)
    (targetLower : Real.rpow scales.rhoHat.1
      (1 - seed.schedule.thirdOutputLoss) ≤ targetRequested.1)
    (targetTau : targetRequested.1 ≤ 3 * scales.tau)
    (coefficient_one : 1 ≤ (coefficient : ℝ)) :
    first.firstConstant ≤
      (3527193600 : ENNReal) * (coefficient : ENNReal) ^ 2 *
        Kakeya.realRpowENN delta
          (-((1 - discreteLoss) *
            proposition63FourCallPaperNormalizedFirstExponent discreteLoss
              seed.schedule.third.normalizationLoss
              seed.schedule.thirdOutputLoss seed.epsilon₁
              seed.paperAngularExponent)) := by
  have rho_pos : 0 < scales.rhoHat.1 :=
    (grid.scale_pos _
      (scales.first_lt_second.le.trans scales.second_le_gridN)).trans_le
        scales.logicalR_le_rhoHat
  have tau_pos : 0 < scales.tau := scales.tau_pos
  have target_decay_nonneg :
      0 ≤ sigma + 2 * seed.schedule.thirdOutputLoss := by
    linarith [seed.schedule.thirdOutputLoss_pos,
      seed.paperAngularExponent_lt_sigma, seed.paperAngularExponent_pos]
  have output_le_one : seed.schedule.thirdOutputLoss ≤ 1 :=
    seed.thirdOutputLoss_le_discrete.trans <| by
      have robust_pos := seed.robustExponent_pos
      rw [seed.robustExponent_eq] at robust_pos
      linarith
  have target_le_tau : Real.rpow scales.rhoHat.1
      (1 - seed.schedule.thirdOutputLoss) ≤ 3 * scales.tau :=
    targetLower.trans targetTau
  have tau_power := proposition63_interval_tau_negative_power_le rho_pos
    seed.schedule.thirdOutputLoss_pos output_le_one target_le_tau
  have normalized_bound :=
    proposition63_four_call_normalized_first_requirement_le
      (rho := scales.rhoHat.1) (tau := scales.tau) (sigma := sigma)
      (normalizationLoss := seed.schedule.third.normalizationLoss)
      (outputLoss := seed.schedule.thirdOutputLoss)
      (targetScale := targetRequested.1)
      (epsilon₁ := seed.epsilon₁) (angular := seed.paperAngularExponent)
      (incidence := incidence) (coefficient := coefficient)
      rho_pos scales.rhoHat.property.2 scales.rhoHat_le_tau
      (scales.tau_le_sqrt_logicalR.trans
        (Real.sqrt_le_sqrt scales.logicalR_le_rhoHat))
      (rho_pos.trans_le targetRequested.property.1) tau_le_target
      target_decay_nonneg incidence_nonneg
      (incidence_le_delta.trans scales.rhoHat.property.1) coefficient_one tau_power
  have first_rho : first.firstConstant ≤
      (3527193600 : ENNReal) * (coefficient : ENNReal) ^ 2 *
        Kakeya.realRpowENN scales.rhoHat.1
          (-(proposition63FourCallPaperNormalizedFirstExponent discreteLoss
            seed.schedule.third.normalizationLoss
            seed.schedule.thirdOutputLoss seed.epsilon₁
            seed.paperAngularExponent)) := by
    rw [first.value_eq]
    simpa only [proposition63FourCallPaperNormalizedFirstExponent] using
      normalized_bound
  let envelope := proposition63FourCallPaperNormalizedFirstExponent discreteLoss
    seed.schedule.third.normalizationLoss seed.schedule.thirdOutputLoss
    seed.epsilon₁ seed.paperAngularExponent
  have envelope_pos : 0 < envelope := by
    dsimp only [envelope, proposition63FourCallPaperNormalizedFirstExponent]
    have output_small : seed.schedule.thirdOutputLoss < 1 :=
      seed.thirdOutputLoss_le_discrete.trans_lt <| by
        have robust_pos := seed.robustExponent_pos
        rw [seed.robustExponent_eq] at robust_pos
        linarith
    have normalization_pos := seed.schedule.third.normalizationLoss_pos
    have epsilon_pos := seed.epsilon₁_pos
    have angular_pos := seed.paperAngularExponent_pos
    have output_pos := seed.schedule.thirdOutputLoss_pos
    have product_nonneg : 0 ≤
        2 * (1 - seed.schedule.thirdOutputLoss) *
          seed.schedule.thirdOutputLoss := by
      exact mul_nonneg
        (mul_nonneg (by norm_num) (by linarith :
          0 ≤ 1 - seed.schedule.thirdOutputLoss)) output_pos.le
    linarith
  have delta_rho : Real.rpow delta (1 - discreteLoss) ≤ scales.rhoHat.1 :=
    (grid.scale_window discreteLoss (by
        have internal_pos := seed.alignedAbsorption.internal_loss_pos
        rw [seed.alignedAbsorption.internal_loss_eq] at internal_pos
        linarith) le_rfl
      _ (scales.first_lt_second.le.trans scales.second_le_gridN)).1.trans
        scales.logicalR_le_rhoHat
  have source_pos : 0 < Real.rpow delta (1 - discreteLoss) :=
    Real.rpow_pos_of_pos delta_pos _
  have power_le : Kakeya.realRpowENN scales.rhoHat.1 (-envelope) ≤
      Kakeya.realRpowENN delta (-((1 - discreteLoss) * envelope)) := by
    apply ENNReal.ofReal_mono
    calc
      Real.rpow scales.rhoHat.1 (-envelope) ≤
          Real.rpow (Real.rpow delta (1 - discreteLoss)) (-envelope) :=
        Real.rpow_le_rpow_of_nonpos source_pos delta_rho (by linarith)
      _ = Real.rpow delta ((1 - discreteLoss) * (-envelope)) :=
        (Real.rpow_mul delta_pos.le _ _).symm
      _ = Real.rpow delta (-((1 - discreteLoss) * envelope)) := by
        congr 1
        ring
  exact first_rho.trans (mul_le_mul_right power_le _)

/-- A cutoff chosen from a fixed power envelope before the runtime constant
is known. -/
structure Proposition63NestedIntervalUniformEnvelopeData
    (K : ℝ) (amplitude : ENNReal) (envelopeLoss internalLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  specialize : ∀ {delta : ℝ} (firstConstant : ENNReal),
    0 < delta → delta ≤ delta₀ →
    firstConstant ≤ amplitude * Kakeya.realRpowENN delta (-envelopeLoss) →
      { absorption : Proposition63NestedIntervalAbsorptionData
          K firstConstant internalLoss // absorption.delta₀ = delta }

theorem proposition63_nested_interval_uniform_envelope
    (K : ℝ) (amplitude : ENNReal) (amplitude_finite : amplitude ≠ ⊤)
    {envelopeLoss internalLoss : ℝ}
    (envelope_nonneg : 0 ≤ envelopeLoss)
    (loss_gap : envelopeLoss < internalLoss) :
    Nonempty (Proposition63NestedIntervalUniformEnvelopeData K amplitude
      envelopeLoss internalLoss) := by
  let fixed := proposition63NestedIntervalCoefficient K * amplitude
  have fixed_finite : fixed ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top amplitude_finite
  have gap_pos : 0 < internalLoss - envelopeLoss := by linarith
  rcases exists_delta_realRpowENN_bound fixed fixed_finite gap_pos with
    ⟨delta₀, delta₀_pos, delta₀_le_one, bound⟩
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := delta₀_pos
    delta₀_le_one := delta₀_le_one
    specialize := ?_
  }⟩
  intro delta firstConstant delta_pos delta_le first_le
  refine ⟨{
    delta₀ := delta
    delta₀_pos := delta_pos
    delta₀_le_one := delta_le.trans delta₀_le_one
    absorb := ?_
  }, rfl⟩
  intro fineDelta fine_pos fine_le
  have fixed_bound : fixed ≤
      Kakeya.realRpowENN delta (-(internalLoss - envelopeLoss)) :=
    bound delta delta_pos delta_le
  have at_delta : proposition63NestedIntervalCoefficient K * firstConstant ≤
      Kakeya.realRpowENN delta (-internalLoss) := by
    calc
      proposition63NestedIntervalCoefficient K * firstConstant ≤
          proposition63NestedIntervalCoefficient K *
            (amplitude * Kakeya.realRpowENN delta (-envelopeLoss)) :=
        mul_le_mul_right first_le _
      _ = fixed * Kakeya.realRpowENN delta (-envelopeLoss) := by
        dsimp only [fixed]
        ring
      _ ≤ Kakeya.realRpowENN delta (-(internalLoss - envelopeLoss)) *
          Kakeya.realRpowENN delta (-envelopeLoss) :=
        mul_le_mul_left fixed_bound _
      _ = Kakeya.realRpowENN delta (-internalLoss) := by
        rw [realRpowENN_mul' delta_pos]
        congr 1
        ring
  exact at_delta.trans <| by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_nonpos fine_pos fine_le (by
      linarith [envelope_nonneg, loss_gap])

/-- Build the same uniform envelope with a prescribed outer cutoff.  This is
the specialization used when the amplitude itself is controlled by a power
of a later runtime scale: the caller proves the single endpoint inequality
before that scale is selected, and this constructor retains the exact cutoff
instead of choosing a coefficient-dependent one. -/
def proposition63_nested_interval_uniform_envelope_at
    (K : ℝ) (amplitude : ENNReal) {delta₀ envelopeLoss internalLoss : ℝ}
    (delta₀_pos : 0 < delta₀) (delta₀_le_one : delta₀ ≤ 1)
    (envelope_nonneg : 0 ≤ envelopeLoss)
    (loss_gap : envelopeLoss < internalLoss)
    (endpoint : proposition63NestedIntervalCoefficient K * amplitude ≤
      Kakeya.realRpowENN delta₀ (-(internalLoss - envelopeLoss))) :
    Proposition63NestedIntervalUniformEnvelopeData K amplitude
      envelopeLoss internalLoss where
  delta₀ := delta₀
  delta₀_pos := delta₀_pos
  delta₀_le_one := delta₀_le_one
  specialize := by
    intro delta firstConstant delta_pos delta_le first_le
    refine ⟨{
      delta₀ := delta
      delta₀_pos := delta_pos
      delta₀_le_one := delta_le.trans delta₀_le_one
      absorb := ?_
    }, rfl⟩
    intro fineDelta fine_pos fine_le
    have fixed_bound : proposition63NestedIntervalCoefficient K * amplitude ≤
        Kakeya.realRpowENN delta (-(internalLoss - envelopeLoss)) :=
      endpoint.trans <| by
        apply ENNReal.ofReal_mono
        exact Real.rpow_le_rpow_of_nonpos delta_pos delta_le (by linarith)
    have at_delta : proposition63NestedIntervalCoefficient K * firstConstant ≤
        Kakeya.realRpowENN delta (-internalLoss) := by
      calc
        proposition63NestedIntervalCoefficient K * firstConstant ≤
            proposition63NestedIntervalCoefficient K *
              (amplitude * Kakeya.realRpowENN delta (-envelopeLoss)) :=
          mul_le_mul_right first_le _
        _ = (proposition63NestedIntervalCoefficient K * amplitude) *
              Kakeya.realRpowENN delta (-envelopeLoss) := by ring
        _ ≤ Kakeya.realRpowENN delta (-(internalLoss - envelopeLoss)) *
              Kakeya.realRpowENN delta (-envelopeLoss) :=
          mul_le_mul_left fixed_bound _
        _ = Kakeya.realRpowENN delta (-internalLoss) := by
          rw [realRpowENN_mul' delta_pos]
          congr 1
          ring
    exact at_delta.trans <| by
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_nonpos fine_pos fine_le (by
        linarith [envelope_nonneg, loss_gap])

noncomputable def proposition63FourCallNormalizedFirstEnvelopeLoss
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed sigma outputLoss discreteLoss) : ℝ :=
  (1 - discreteLoss) *
    proposition63FourCallPaperNormalizedFirstExponent discreteLoss
      seed.schedule.third.normalizationLoss seed.schedule.thirdOutputLoss
      seed.epsilon₁ seed.paperAngularExponent

theorem Proposition63FourCallInnerLossSeed.normalizedFirstEnvelopeLoss_pos
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed sigma outputLoss discreteLoss) :
    0 < proposition63FourCallNormalizedFirstEnvelopeLoss seed := by
  have discrete_pos : 0 < discreteLoss := by
    have internal_pos := seed.alignedAbsorption.internal_loss_pos
    rw [seed.alignedAbsorption.internal_loss_eq] at internal_pos
    linarith
  have discrete_lt_one : discreteLoss < 1 := by
    have robust_pos := seed.robustExponent_pos
    rw [seed.robustExponent_eq] at robust_pos
    linarith
  have normalized_pos : 0 <
      proposition63FourCallPaperNormalizedFirstExponent discreteLoss
        seed.schedule.third.normalizationLoss seed.schedule.thirdOutputLoss
        seed.epsilon₁ seed.paperAngularExponent := by
    dsimp only [proposition63FourCallPaperNormalizedFirstExponent]
    have output_small : seed.schedule.thirdOutputLoss < 1 :=
      seed.thirdOutputLoss_le_discrete.trans_lt discrete_lt_one
    have product_nonneg : 0 ≤
        2 * (1 - seed.schedule.thirdOutputLoss) *
          seed.schedule.thirdOutputLoss := by
      exact mul_nonneg
        (mul_nonneg (by norm_num) (by linarith :
          0 ≤ 1 - seed.schedule.thirdOutputLoss))
        seed.schedule.thirdOutputLoss_pos.le
    linarith [seed.schedule.third.normalizationLoss_pos,
      seed.epsilon₁_pos, seed.paperAngularExponent_pos]
  dsimp only [proposition63FourCallNormalizedFirstEnvelopeLoss]
  positivity

theorem Proposition63FourCallInnerLossSeed.normalizedFirstEnvelopeLoss_lt
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed sigma outputLoss discreteLoss) :
    proposition63FourCallNormalizedFirstEnvelopeLoss seed <
      seed.alignedAbsorption.internalLoss := by
  have discrete_pos : 0 < discreteLoss := by
    have internal_pos := seed.alignedAbsorption.internal_loss_pos
    rw [seed.alignedAbsorption.internal_loss_eq] at internal_pos
    linarith
  have discrete_lt_one : discreteLoss < 1 := by
    have robust_pos := seed.robustExponent_pos
    rw [seed.robustExponent_eq] at robust_pos
    linarith
  let exponent := proposition63FourCallPaperNormalizedFirstExponent
    discreteLoss seed.schedule.third.normalizationLoss
    seed.schedule.thirdOutputLoss seed.epsilon₁ seed.paperAngularExponent
  have exponent_pos : 0 < exponent := by
    dsimp only [exponent, proposition63FourCallPaperNormalizedFirstExponent]
    have output_small : seed.schedule.thirdOutputLoss < 1 :=
      seed.thirdOutputLoss_le_discrete.trans_lt discrete_lt_one
    have product_nonneg : 0 ≤
        2 * (1 - seed.schedule.thirdOutputLoss) *
          seed.schedule.thirdOutputLoss := by
      exact mul_nonneg
        (mul_nonneg (by norm_num) (by linarith :
          0 ≤ 1 - seed.schedule.thirdOutputLoss))
        seed.schedule.thirdOutputLoss_pos.le
    linarith [seed.schedule.third.normalizationLoss_pos,
      seed.epsilon₁_pos, seed.paperAngularExponent_pos]
  have scaled_lt : (1 - discreteLoss) * exponent < exponent :=
    mul_lt_of_lt_one_left exponent_pos (by linarith)
  dsimp only [proposition63FourCallNormalizedFirstEnvelopeLoss]
  exact scaled_lt.trans seed.normalizedFirstExponent_lt

noncomputable def proposition63FourCallNormalizedFirstAmplitude
    (coefficient : NNReal) : ENNReal :=
  (3527193600 : ENNReal) * (coefficient : ENNReal) ^ 2

/-- Polynomial majorant for the fixed nested-cover coefficient.  Both
ceiling factors are linear once `K ≥ 1`, so the coefficient is quadratic in
`K`. -/
theorem proposition63_nested_interval_coefficient_le_quadratic
    (K : NNReal) (K_one : 1 ≤ (K : ℝ)) :
    proposition63NestedIntervalCoefficient (K : ℝ) ≤
      (1898208000 : ENNReal) * (K : ENNReal) ^ 2 := by
  have hsqrt : Nat.ceil (Real.sqrt 3) ≤ 2 := by
    apply Nat.ceil_le.mpr
    norm_num
    nlinarith [Real.sqrt_nonneg 3,
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hsqrtFactor :
      (2 * Nat.ceil (Real.sqrt 3) + 2 : ENNReal) ≤ 6 := by
    exact_mod_cast (show 2 * Nat.ceil (Real.sqrt 3) + 2 ≤ 6 by omega)
  have hceilEight : (Nat.ceil (8 * (K : ℝ)) : ℝ) <
      8 * (K : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hfactorEightReal :
      2 * (Nat.ceil (8 * (K : ℝ)) : ℝ) + 2 ≤
        (20 : ℝ) * (K : ℝ) := by
    exact (calc
      2 * (Nat.ceil (8 * (K : ℝ)) : ℝ) + 2 <
          2 * (8 * (K : ℝ) + 1) + 2 := by linarith
      _ ≤ 20 * (K : ℝ) := by nlinarith).le
  have hfactorEight :
      (2 * Nat.ceil (8 * (K : ℝ)) + 2 : ENNReal) ≤
        20 * (K : ENNReal) := by
    exact_mod_cast hfactorEightReal
  have hceilTwo : (Nat.ceil (2 * (K : ℝ)) : ℝ) <
      2 * (K : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hfactorTwoReal :
      2 * (Nat.ceil (2 * (K : ℝ)) : ℝ) + 2 ≤
        (8 : ℝ) * (K : ℝ) := by
    exact (calc
      2 * (Nat.ceil (2 * (K : ℝ)) : ℝ) + 2 <
          2 * (2 * (K : ℝ) + 1) + 2 := by linarith
      _ ≤ 8 * (K : ℝ) := by nlinarith).le
  have hfactorTwo :
      (2 * Nat.ceil (2 * (K : ℝ)) + 2 : ENNReal) ≤
        8 * (K : ENNReal) := by
    exact_mod_cast hfactorTwoReal
  unfold proposition63NestedIntervalCoefficient
  push_cast
  calc
    (2 * (Nat.ceil (Real.sqrt 3) : ENNReal) + 2) * 5 *
          (2 * (Nat.ceil (8 * (K : ℝ)) : ENNReal) + 2) * 2197 * 5 * 4 * 9 *
          (2 * (Nat.ceil (2 * (K : ℝ)) : ENNReal) + 2) ≤
        (6 : ENNReal) * 5 * (20 * (K : ENNReal)) * 2197 * 5 * 4 * 9 *
          (8 * (K : ENNReal)) := by gcongr
    _ = (1898208000 : ENNReal) * (K : ENNReal) ^ 2 := by ring

/-- The whole normalized-first endpoint is quartic in its amplified
Lipschitz coefficient. -/
theorem proposition63_normalized_first_fixed_le_quartic
    (coefficient : NNReal) (coefficient_one : 1 ≤ (coefficient : ℝ)) :
    proposition63NestedIntervalCoefficient (coefficient : ℝ) *
        proposition63FourCallNormalizedFirstAmplitude coefficient ≤
      (6695347109068800000 : ENNReal) * (coefficient : ENNReal) ^ 4 := by
  rw [proposition63FourCallNormalizedFirstAmplitude]
  calc
    proposition63NestedIntervalCoefficient (coefficient : ℝ) *
          ((3527193600 : ENNReal) * (coefficient : ENNReal) ^ 2) ≤
        ((1898208000 : ENNReal) * (coefficient : ENNReal) ^ 2) *
          ((3527193600 : ENNReal) * (coefficient : ENNReal) ^ 2) := by
      gcongr
      exact proposition63_nested_interval_coefficient_le_quadratic
        coefficient coefficient_one
    _ = (6695347109068800000 : ENNReal) *
          (coefficient : ENNReal) ^ 4 := by ring

structure Proposition63FourCallFirstUniformCutoffData
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed sigma outputLoss discreteLoss)
    (coefficient : NNReal) where
  nested : Proposition63NestedIntervalUniformEnvelopeData
    (coefficient : ℝ)
    (proposition63FourCallNormalizedFirstAmplitude coefficient)
    (proposition63FourCallNormalizedFirstEnvelopeLoss seed)
    seed.alignedAbsorption.internalLoss

theorem proposition63_four_call_first_uniform_cutoff
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed sigma outputLoss discreteLoss)
    (coefficient : NNReal) :
    Nonempty (Proposition63FourCallFirstUniformCutoffData seed coefficient) := by
  let envelope := proposition63FourCallPaperNormalizedFirstExponent discreteLoss
    seed.schedule.third.normalizationLoss seed.schedule.thirdOutputLoss
    seed.epsilon₁ seed.paperAngularExponent
  have envelope_pos : 0 < envelope := by
    dsimp only [envelope, proposition63FourCallPaperNormalizedFirstExponent]
    have output_small : seed.schedule.thirdOutputLoss < 1 :=
      seed.thirdOutputLoss_le_discrete.trans_lt <| by
        have robust_pos := seed.robustExponent_pos
        rw [seed.robustExponent_eq] at robust_pos
        linarith
    have product_nonneg : 0 ≤
        2 * (1 - seed.schedule.thirdOutputLoss) *
          seed.schedule.thirdOutputLoss := by
      exact mul_nonneg (mul_nonneg (by norm_num) (by linarith))
        seed.schedule.thirdOutputLoss_pos.le
    linarith [seed.schedule.third.normalizationLoss_pos,
      seed.epsilon₁_pos, seed.paperAngularExponent_pos]
  have discrete_pos : 0 < discreteLoss := by
    have internal_pos := seed.alignedAbsorption.internal_loss_pos
    rw [seed.alignedAbsorption.internal_loss_eq] at internal_pos
    linarith
  have discrete_lt_one : discreteLoss < 1 := by
    have robust_pos := seed.robustExponent_pos
    rw [seed.robustExponent_eq] at robust_pos
    linarith
  have envelopeLoss_nonneg : 0 ≤
      proposition63FourCallNormalizedFirstEnvelopeLoss seed := by
    dsimp only [proposition63FourCallNormalizedFirstEnvelopeLoss]
    exact mul_nonneg (by linarith) envelope_pos.le
  have envelopeLoss_lt :
      proposition63FourCallNormalizedFirstEnvelopeLoss seed <
        seed.alignedAbsorption.internalLoss := by
    have hfactor : 1 - discreteLoss < 1 := by linarith
    have hscaled : (1 - discreteLoss) * envelope < envelope :=
      mul_lt_of_lt_one_left envelope_pos hfactor
    exact hscaled.trans seed.normalizedFirstExponent_lt
  have amplitude_finite :
      proposition63FourCallNormalizedFirstAmplitude coefficient ≠ ⊤ := by
    unfold proposition63FourCallNormalizedFirstAmplitude
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  rcases proposition63_nested_interval_uniform_envelope
      (coefficient : ℝ)
      (proposition63FourCallNormalizedFirstAmplitude coefficient)
      amplitude_finite envelopeLoss_nonneg envelopeLoss_lt with ⟨nested⟩
  exact ⟨{ nested := nested }⟩

/-- Instantiate the first-constant cutoff at an externally prescribed fine
scale.  The endpoint inequality is the only place where a scale-dependent
source Lipschitz coefficient must be paid. -/
noncomputable def proposition63_four_call_first_uniform_cutoff_at
    {sigma outputLoss discreteLoss delta₀ : ℝ}
    (seed : Proposition63FourCallInnerLossSeed sigma outputLoss discreteLoss)
    (coefficient : NNReal)
    (delta₀_pos : 0 < delta₀) (delta₀_le_one : delta₀ ≤ 1)
    (endpoint : proposition63NestedIntervalCoefficient (coefficient : ℝ) *
        proposition63FourCallNormalizedFirstAmplitude coefficient ≤
      Kakeya.realRpowENN delta₀
        (-(seed.alignedAbsorption.internalLoss -
          proposition63FourCallNormalizedFirstEnvelopeLoss seed))) :
    Proposition63FourCallFirstUniformCutoffData seed coefficient := by
  refine ⟨proposition63_nested_interval_uniform_envelope_at
    (coefficient : ℝ)
    (proposition63FourCallNormalizedFirstAmplitude coefficient)
    delta₀_pos delta₀_le_one ?_ ?_ endpoint⟩
  · exact seed.normalizedFirstEnvelopeLoss_pos.le
  · exact seed.normalizedFirstEnvelopeLoss_lt

noncomputable def Proposition63FourCallFirstUniformCutoffData.nestedInterval
    {delta sigma discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {outputLoss incidence : ℝ}
    {seed : Proposition63FourCallInnerLossSeed sigma outputLoss discreteLoss}
    {scales : Proposition63FourCallOrderedPairIndexScales grid index}
    {targetRequested : WZ2PaperRequestedScale scales.rhoHat.1}
    {coefficient : NNReal}
    (cutoff : Proposition63FourCallFirstUniformCutoffData seed coefficient)
    (first : Proposition63FourCallFirstConstantChoice scales.rhoHat.1
      scales.tau sigma seed.schedule.third.normalizationLoss
      seed.schedule.thirdOutputLoss targetRequested.1 seed.epsilon₁
      seed.paperAngularExponent incidence coefficient)
    (delta_pos : 0 < delta) (delta_le : delta ≤ cutoff.nested.delta₀)
    (incidence_nonneg : 0 ≤ incidence) (incidence_le_delta : incidence ≤ delta)
    (tau_le_target : scales.tau ≤ targetRequested.1)
    (targetLower : Real.rpow scales.rhoHat.1
      (1 - seed.schedule.thirdOutputLoss) ≤ targetRequested.1)
    (targetTau : targetRequested.1 ≤ 3 * scales.tau)
    (coefficient_one : 1 ≤ (coefficient : ℝ)) :
    Proposition63NestedIntervalAbsorptionData (coefficient : ℝ)
      first.firstConstant seed.alignedAbsorption.internalLoss := by
  exact (cutoff.nested.specialize first.firstConstant delta_pos delta_le (by
    simpa only [proposition63FourCallNormalizedFirstAmplitude,
      proposition63FourCallNormalizedFirstEnvelopeLoss] using
      proposition63_four_call_first_constant_delta_envelope seed scales
        targetRequested coefficient first delta_pos incidence_nonneg
        incidence_le_delta tau_le_target targetLower targetTau
        coefficient_one)).1

@[simp] theorem Proposition63FourCallFirstUniformCutoffData.nestedInterval_delta₀
    {delta sigma discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {outputLoss incidence : ℝ}
    {seed : Proposition63FourCallInnerLossSeed sigma outputLoss discreteLoss}
    {scales : Proposition63FourCallOrderedPairIndexScales grid index}
    {targetRequested : WZ2PaperRequestedScale scales.rhoHat.1}
    {coefficient : NNReal}
    (cutoff : Proposition63FourCallFirstUniformCutoffData seed coefficient)
    (first : Proposition63FourCallFirstConstantChoice scales.rhoHat.1
      scales.tau sigma seed.schedule.third.normalizationLoss
      seed.schedule.thirdOutputLoss targetRequested.1 seed.epsilon₁
      seed.paperAngularExponent incidence coefficient)
    (delta_pos : 0 < delta) (delta_le : delta ≤ cutoff.nested.delta₀)
    (incidence_nonneg : 0 ≤ incidence) (incidence_le_delta : incidence ≤ delta)
    (tau_le_target : scales.tau ≤ targetRequested.1)
    (targetLower : Real.rpow scales.rhoHat.1
      (1 - seed.schedule.thirdOutputLoss) ≤ targetRequested.1)
    (targetTau : targetRequested.1 ≤ 3 * scales.tau)
    (coefficient_one : 1 ≤ (coefficient : ℝ)) :
    (cutoff.nestedInterval first delta_pos delta_le incidence_nonneg
      incidence_le_delta tau_le_target targetLower targetTau
      coefficient_one).delta₀ = delta := by
  exact (cutoff.nested.specialize first.firstConstant delta_pos delta_le (by
    simpa only [proposition63FourCallNormalizedFirstAmplitude,
      proposition63FourCallNormalizedFirstEnvelopeLoss] using
      proposition63_four_call_first_constant_delta_envelope seed scales
        targetRequested coefficient first delta_pos incidence_nonneg
        incidence_le_delta tau_le_target targetLower targetTau
        coefficient_one)).2

/-- Exact quotient identity before replacing the interval scale by
`sqrt rho`. -/
theorem proposition63_four_call_first_analytic_quotient_eq
    {rho tau sigma discreteLoss normalizationLoss outputLoss epsilon₁ angular : ℝ}
    (rho_pos : 0 < rho) (tau_pos : 0 < tau) :
    proposition63RobustTauTotalVolume rho sigma normalizationLoss outputLoss
          (Real.rpow rho (1 - discreteLoss)) tau /
        (Real.rpow rho (1 + 7 * epsilon₁ + angular) * tau ^ 2 / 200) =
      (216 * 27 * 200 : ℝ) * tau *
        Real.rpow rho
          (sigma - normalizationLoss - (1 + 7 * epsilon₁ + angular) -
            (1 - discreteLoss) * (sigma + 2 * outputLoss)) := by
  have rho_ne : rho ≠ 0 := rho_pos.ne'
  have tau_ne : tau ≠ 0 := tau_pos.ne'
  have target_pos : 0 < Real.rpow rho (1 - discreteLoss) :=
    Real.rpow_pos_of_pos rho_pos _
  have target_ne : Real.rpow rho (1 - discreteLoss) ≠ 0 := target_pos.ne'
  have target_power :
      Real.rpow (Real.rpow rho (1 - discreteLoss))
          (3 - sigma - 2 * outputLoss) =
        Real.rpow rho ((1 - discreteLoss) *
          (3 - sigma - 2 * outputLoss)) := by
    exact (Real.rpow_mul rho_pos.le _ _).symm
  rw [proposition63RobustTauTotalVolume, target_power]
  have denominator_power_ne :
      Real.rpow rho (1 + 7 * epsilon₁ + angular) ≠ 0 :=
    (Real.rpow_pos_of_pos rho_pos _).ne'
  field_simp
  have target_cube : (Real.rpow rho (1 - discreteLoss)) ^ 3 =
      Real.rpow rho (3 * (1 - discreteLoss)) := by
    calc
      (Real.rpow rho (1 - discreteLoss)) ^ 3 =
          Real.rpow (Real.rpow rho (1 - discreteLoss)) (3 : ℝ) := by
            exact (Real.rpow_natCast _ 3).symm
      _ = Real.rpow rho ((1 - discreteLoss) * 3) :=
        (Real.rpow_mul rho_pos.le _ _).symm
      _ = Real.rpow rho (3 * (1 - discreteLoss)) := by ring
  rw [target_cube]
  calc
    3 ^ 3 * Real.rpow rho (sigma - normalizationLoss) *
          Real.rpow rho ((1 - discreteLoss) *
            (3 - sigma - 2 * outputLoss)) =
        27 * Real.rpow rho ((sigma - normalizationLoss) +
          ((1 - discreteLoss) * (3 - sigma - 2 * outputLoss))) := by
      calc
        3 ^ 3 * Real.rpow rho (sigma - normalizationLoss) *
              Real.rpow rho ((1 - discreteLoss) *
                (3 - sigma - 2 * outputLoss)) =
            27 * (Real.rpow rho (sigma - normalizationLoss) *
              Real.rpow rho ((1 - discreteLoss) *
                (3 - sigma - 2 * outputLoss))) := by
          norm_num
          ac_rfl
        _ = 27 * Real.rpow rho ((sigma - normalizationLoss) +
              ((1 - discreteLoss) *
                (3 - sigma - 2 * outputLoss))) := by
          exact congrArg (fun value : ℝ => 27 * value)
            (Real.rpow_add rho_pos _ _).symm
    _ = 27 * Real.rpow rho (3 * (1 - discreteLoss) +
          (1 + 7 * epsilon₁ + angular) +
          (sigma - normalizationLoss - (1 + 7 * epsilon₁ + angular) -
            (1 - discreteLoss) * (sigma + 2 * outputLoss))) := by
      congr 2
      ring
    _ = Real.rpow rho (3 * (1 - discreteLoss)) *
          Real.rpow rho (1 + 7 * epsilon₁ + angular) * 27 *
          Real.rpow rho
            (sigma - normalizationLoss - (1 + 7 * epsilon₁ + angular) -
              (1 - discreteLoss) * (sigma + 2 * outputLoss)) := by
      have houter := Real.rpow_add rho_pos
        (3 * (1 - discreteLoss))
        ((1 + 7 * epsilon₁ + angular) +
          (sigma - normalizationLoss - (1 + 7 * epsilon₁ + angular) -
            (1 - discreteLoss) * (sigma + 2 * outputLoss)))
      have hinner := Real.rpow_add rho_pos
        (1 + 7 * epsilon₁ + angular)
        (sigma - normalizationLoss - (1 + 7 * epsilon₁ + angular) -
          (1 - discreteLoss) * (sigma + 2 * outputLoss))
      calc
        27 * Real.rpow rho
              (3 * (1 - discreteLoss) + (1 + 7 * epsilon₁ + angular) +
                (sigma - normalizationLoss -
                  (1 + 7 * epsilon₁ + angular) -
                  (1 - discreteLoss) * (sigma + 2 * outputLoss))) =
            27 * Real.rpow rho
              (3 * (1 - discreteLoss) +
                ((1 + 7 * epsilon₁ + angular) +
                  (sigma - normalizationLoss -
                    (1 + 7 * epsilon₁ + angular) -
                    (1 - discreteLoss) * (sigma + 2 * outputLoss)))) := by
          congr 2
          ring
        _ = 27 * (Real.rpow rho (3 * (1 - discreteLoss)) *
              Real.rpow rho
                ((1 + 7 * epsilon₁ + angular) +
                  (sigma - normalizationLoss -
                    (1 + 7 * epsilon₁ + angular) -
                    (1 - discreteLoss) * (sigma + 2 * outputLoss)))) := by
          exact congrArg (fun value : ℝ => 27 * value) houter
        _ = 27 * (Real.rpow rho (3 * (1 - discreteLoss)) *
              (Real.rpow rho (1 + 7 * epsilon₁ + angular) *
                Real.rpow rho
                  (sigma - normalizationLoss -
                    (1 + 7 * epsilon₁ + angular) -
                    (1 - discreteLoss) * (sigma + 2 * outputLoss)))) := by
          exact congrArg
            (fun value : ℝ => 27 *
              (Real.rpow rho (3 * (1 - discreteLoss)) * value)) hinner
        _ = Real.rpow rho (3 * (1 - discreteLoss)) *
              Real.rpow rho (1 + 7 * epsilon₁ + angular) * 27 *
              Real.rpow rho
                (sigma - normalizationLoss -
                  (1 + 7 * epsilon₁ + angular) -
                  (1 - discreteLoss) * (sigma + 2 * outputLoss)) := by ring

/-- The first arithmetic requirement is bounded by one fixed coefficient
times a negative power of the aligned coarse scale. -/
theorem proposition63_four_call_first_arithmetic_requirement_le
    {rho tau sigma discreteLoss normalizationLoss outputLoss epsilon₁ angular
      incidence : ℝ} {coefficient : NNReal}
    (rho_pos : 0 < rho) (rho_le_one : rho ≤ 1)
    (rho_le_tau : rho ≤ tau) (tau_le_sqrt : tau ≤ Real.sqrt rho)
    (incidence_nonneg : 0 ≤ incidence) (incidence_le : incidence ≤ rho)
    (coefficient_one : 1 ≤ (coefficient : ℝ)) :
    proposition63FourCallFirstArithmeticRequirement rho tau sigma
        normalizationLoss outputLoss (Real.rpow rho (1 - discreteLoss))
        epsilon₁ angular incidence coefficient ≤
      (391910400 : ENNReal) * (coefficient : ENNReal) ^ 2 *
        Kakeya.realRpowENN rho
          (-(proposition63FourCallPaperFirstExponent sigma discreteLoss
            normalizationLoss outputLoss epsilon₁ angular)) := by
  have slab_le := proposition63_dependent_interval_slab_width_le rho_pos
    rho_le_one rho_le_tau tau_le_sqrt incidence_nonneg incidence_le
    coefficient_one
  have coefficient_nonneg : 0 ≤ (coefficient : ℝ) := by positivity
  have slab_div_le :
      proposition63DependentSlabWidth rho tau
          (proposition63DependentCoarseIncidence rho incidence coefficient)
          coefficient / rho ≤ 167 * (coefficient : ℝ) := by
    exact (div_le_iff₀ rho_pos).2 (by nlinarith)
  have cordoba_factor_le :
      2 * proposition63DependentSlabWidth rho tau
          (proposition63DependentCoarseIncidence rho incidence coefficient)
          coefficient / rho + 2 ≤
        336 * (coefficient : ℝ) ^ 2 := by
    calc
      2 * proposition63DependentSlabWidth rho tau
            (proposition63DependentCoarseIncidence rho incidence coefficient)
            coefficient / rho + 2
          ≤ 334 * (coefficient : ℝ) + 2 := by
        calc
          2 * proposition63DependentSlabWidth rho tau
                (proposition63DependentCoarseIncidence rho incidence coefficient)
                coefficient / rho + 2 =
              2 * (proposition63DependentSlabWidth rho tau
                (proposition63DependentCoarseIncidence rho incidence coefficient)
                coefficient / rho) + 2 := by ring
          _ ≤ 2 * (167 * (coefficient : ℝ)) + 2 := by gcongr
          _ = 334 * (coefficient : ℝ) + 2 := by ring
      _ ≤ 336 * (coefficient : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((coefficient : ℝ) - 1)]
  have quotient_eq := proposition63_four_call_first_analytic_quotient_eq
    (rho := rho) (tau := tau) (sigma := sigma)
    (discreteLoss := discreteLoss) (normalizationLoss := normalizationLoss)
    (outputLoss := outputLoss) (epsilon₁ := epsilon₁) (angular := angular)
    rho_pos (rho_pos.trans_le rho_le_tau)
  have power_nonneg : 0 ≤ Real.rpow rho
      (sigma - normalizationLoss - (1 + 7 * epsilon₁ + angular) -
        (1 - discreteLoss) * (sigma + 2 * outputLoss)) :=
    Real.rpow_nonneg rho_pos.le _
  have tau_power_le :
      tau * Real.rpow rho
          (sigma - normalizationLoss - (1 + 7 * epsilon₁ + angular) -
            (1 - discreteLoss) * (sigma + 2 * outputLoss)) ≤
        Real.rpow rho
          (-(proposition63FourCallPaperFirstExponent sigma discreteLoss
            normalizationLoss outputLoss epsilon₁ angular)) := by
    calc
      tau * Real.rpow rho
            (sigma - normalizationLoss - (1 + 7 * epsilon₁ + angular) -
              (1 - discreteLoss) * (sigma + 2 * outputLoss))
          ≤ Real.sqrt rho * Real.rpow rho
              (sigma - normalizationLoss - (1 + 7 * epsilon₁ + angular) -
                (1 - discreteLoss) * (sigma + 2 * outputLoss)) := by
            exact mul_le_mul_of_nonneg_right tau_le_sqrt power_nonneg
      _ = Real.rpow rho
            (-(proposition63FourCallPaperFirstExponent sigma discreteLoss
              normalizationLoss outputLoss epsilon₁ angular)) := by
        calc
          Real.sqrt rho * Real.rpow rho
                (sigma - normalizationLoss -
                  (1 + 7 * epsilon₁ + angular) -
                  (1 - discreteLoss) * (sigma + 2 * outputLoss)) =
              Real.rpow rho (1 / 2 : ℝ) * Real.rpow rho
                (sigma - normalizationLoss -
                  (1 + 7 * epsilon₁ + angular) -
                  (1 - discreteLoss) * (sigma + 2 * outputLoss)) := by
            exact congrArg
              (fun value : ℝ => value * Real.rpow rho
                (sigma - normalizationLoss -
                  (1 + 7 * epsilon₁ + angular) -
                  (1 - discreteLoss) * (sigma + 2 * outputLoss)))
              (Real.sqrt_eq_rpow rho)
          _ = Real.rpow rho ((1 / 2 : ℝ) +
                (sigma - normalizationLoss -
                  (1 + 7 * epsilon₁ + angular) -
                  (1 - discreteLoss) * (sigma + 2 * outputLoss))) :=
            (Real.rpow_add rho_pos _ _).symm
          _ = Real.rpow rho
                (-(proposition63FourCallPaperFirstExponent sigma discreteLoss
                  normalizationLoss outputLoss epsilon₁ angular)) := by
            congr 1
            dsimp only [proposition63FourCallPaperFirstExponent]
            ring
  have fixed_power_nonneg : 0 ≤ (216 * 27 * 200 : ℝ) * tau *
      Real.rpow rho
        (sigma - normalizationLoss - (1 + 7 * epsilon₁ + angular) -
          (1 - discreteLoss) * (sigma + 2 * outputLoss)) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (rho_pos.le.trans rho_le_tau)) power_nonneg
  have real_bound :
      (proposition63RobustTauTotalVolume rho sigma normalizationLoss outputLoss
          (Real.rpow rho (1 - discreteLoss)) tau /
        (Real.rpow rho (1 + 7 * epsilon₁ + angular) * tau ^ 2 / 200)) *
        (2 * proposition63DependentSlabWidth rho tau
            (proposition63DependentCoarseIncidence rho incidence coefficient)
            coefficient / rho + 2) ≤
      (391910400 : ℝ) * (coefficient : ℝ) ^ 2 *
        Real.rpow rho
          (-(proposition63FourCallPaperFirstExponent sigma discreteLoss
            normalizationLoss outputLoss epsilon₁ angular)) := by
    rw [quotient_eq]
    calc
      (216 * 27 * 200 : ℝ) * tau *
            Real.rpow rho
              (sigma - normalizationLoss -
                (1 + 7 * epsilon₁ + angular) -
                (1 - discreteLoss) * (sigma + 2 * outputLoss)) *
            (2 * proposition63DependentSlabWidth rho tau
              (proposition63DependentCoarseIncidence rho incidence coefficient)
              coefficient / rho + 2)
          ≤ (216 * 27 * 200 : ℝ) * tau *
              Real.rpow rho
                (sigma - normalizationLoss -
                  (1 + 7 * epsilon₁ + angular) -
                  (1 - discreteLoss) * (sigma + 2 * outputLoss)) *
              (336 * (coefficient : ℝ) ^ 2) := by
            exact mul_le_mul_of_nonneg_left cordoba_factor_le
              fixed_power_nonneg
      _ = (391910400 : ℝ) * (coefficient : ℝ) ^ 2 *
            (tau * Real.rpow rho
              (sigma - normalizationLoss -
                (1 + 7 * epsilon₁ + angular) -
                (1 - discreteLoss) * (sigma + 2 * outputLoss))) := by ring
      _ ≤ (391910400 : ℝ) * (coefficient : ℝ) ^ 2 *
            Real.rpow rho
              (-(proposition63FourCallPaperFirstExponent sigma discreteLoss
                normalizationLoss outputLoss epsilon₁ angular)) := by
        exact mul_le_mul_of_nonneg_left tau_power_le (by positivity)
  dsimp only [proposition63FourCallFirstArithmeticRequirement]
  calc
    ENNReal.ofReal
        ((proposition63RobustTauTotalVolume rho sigma normalizationLoss outputLoss
            (Real.rpow rho (1 - discreteLoss)) tau /
          (Real.rpow rho (1 + 7 * epsilon₁ + angular) * tau ^ 2 / 200)) *
          (2 * proposition63DependentSlabWidth rho tau
              (proposition63DependentCoarseIncidence rho incidence coefficient)
              coefficient / rho + 2))
        ≤ ENNReal.ofReal ((391910400 : ℝ) * (coefficient : ℝ) ^ 2 *
            Real.rpow rho
              (-(proposition63FourCallPaperFirstExponent sigma discreteLoss
                normalizationLoss outputLoss epsilon₁ angular))) :=
          ENNReal.ofReal_le_ofReal real_bound
    _ = (391910400 : ENNReal) * (coefficient : ENNReal) ^ 2 *
          Kakeya.realRpowENN rho
            (-(proposition63FourCallPaperFirstExponent sigma discreteLoss
              normalizationLoss outputLoss epsilon₁ angular)) := by
      simp only [Kakeya.realRpowENN]
      rw [ENNReal.ofReal_mul (by positivity)]
      rw [ENNReal.ofReal_mul (by positivity)]
      have hcoeff : ENNReal.ofReal ((coefficient : ℝ) ^ 2) =
          (coefficient : ENNReal) ^ 2 := by
        rw [ENNReal.ofReal_pow (by positivity)]
        rw [ENNReal.ofReal_coe_nnreal]
      rw [hcoeff]
      norm_num

/-- Replace the runtime aligned-scale power by the corresponding power of the
original fine scale. -/
theorem proposition63_four_call_first_arithmetic_requirement_delta_le
    {delta rho tau sigma discreteLoss normalizationLoss outputLoss epsilon₁
      angular incidence : ℝ} {coefficient : NNReal}
    (delta_pos : 0 < delta) (rho_pos : 0 < rho) (rho_le_one : rho ≤ 1)
    (rho_le_tau : rho ≤ tau) (tau_le_sqrt : tau ≤ Real.sqrt rho)
    (delta_lower : Real.rpow delta (1 - discreteLoss) ≤ rho)
    (exponent_nonneg : 0 ≤ proposition63FourCallPaperFirstExponent sigma
      discreteLoss normalizationLoss outputLoss epsilon₁ angular)
    (incidence_nonneg : 0 ≤ incidence) (incidence_le : incidence ≤ rho)
    (coefficient_one : 1 ≤ (coefficient : ℝ)) :
    proposition63FourCallFirstArithmeticRequirement rho tau sigma
        normalizationLoss outputLoss (Real.rpow rho (1 - discreteLoss))
        epsilon₁ angular incidence coefficient ≤
      (391910400 : ENNReal) * (coefficient : ENNReal) ^ 2 *
        Kakeya.realRpowENN delta
          (-((1 - discreteLoss) *
            proposition63FourCallPaperFirstExponent sigma discreteLoss
              normalizationLoss outputLoss epsilon₁ angular)) := by
  let exponent := proposition63FourCallPaperFirstExponent sigma discreteLoss
    normalizationLoss outputLoss epsilon₁ angular
  have source_pos : 0 < Real.rpow delta (1 - discreteLoss) :=
    Real.rpow_pos_of_pos delta_pos _
  have power_le : Kakeya.realRpowENN rho (-exponent) ≤
      Kakeya.realRpowENN delta (-((1 - discreteLoss) * exponent)) := by
    apply ENNReal.ofReal_mono
    calc
      Real.rpow rho (-exponent) ≤
          Real.rpow (Real.rpow delta (1 - discreteLoss)) (-exponent) :=
        Real.rpow_le_rpow_of_nonpos source_pos delta_lower (by
          dsimp only [exponent]
          linarith)
      _ = Real.rpow delta ((1 - discreteLoss) * (-exponent)) :=
        (Real.rpow_mul delta_pos.le _ _).symm
      _ = Real.rpow delta (-((1 - discreteLoss) * exponent)) := by
        congr 1
        ring
  exact (proposition63_four_call_first_arithmetic_requirement_le rho_pos
    rho_le_one rho_le_tau tau_le_sqrt incidence_nonneg incidence_le
    coefficient_one).trans (mul_le_mul_left' power_le _)

end Kakeya.Assouad.PureWZ2
