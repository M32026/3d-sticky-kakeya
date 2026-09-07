import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPairScalarChoices

/-!
# Uniform scalar bounds for the paper-ordered Proposition 6.3 tail

The constants in this file are frozen before the runtime scale is supplied.
In particular, no power of the runtime `rho` is hidden in a constant.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- The transported plane-incidence error is uniformly linear in the coarse
scale. -/
theorem proposition63_dependent_coarse_incidence_le
    {rho incidence : ℝ} {coefficient : NNReal}
    (rho_pos : 0 < rho) (_incidence_nonneg : 0 ≤ incidence)
    (incidence_le : incidence ≤ rho)
    (coefficient_one : 1 ≤ (coefficient : ℝ)) :
    proposition63DependentCoarseIncidence rho incidence coefficient ≤
      4 * (coefficient : ℝ) * rho := by
  have hsqrt : Real.sqrt 3 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  have hcoefficient : 0 ≤ (coefficient : ℝ) := by positivity
  have hrhoCoefficient : rho ≤ (coefficient : ℝ) * rho := by
    nlinarith
  have hsqrtTerm :
      (coefficient : ℝ) * (rho * Real.sqrt 3) ≤
        2 * (coefficient : ℝ) * rho := by
    calc
      (coefficient : ℝ) * (rho * Real.sqrt 3) ≤
          (coefficient : ℝ) * (rho * 2) := by gcongr
      _ = 2 * (coefficient : ℝ) * rho := by ring
  dsimp only [proposition63DependentCoarseIncidence]
  nlinarith

/-- At the paper square-root scale, the Córdoba slab width is uniformly
`O(coefficient * rho)`. -/
theorem proposition63_dependent_sqrt_slab_width_le
    {rho incidence : ℝ} {coefficient : NNReal}
    (rho_pos : 0 < rho) (rho_le_one : rho ≤ 1)
    (incidence_nonneg : 0 ≤ incidence) (incidence_le : incidence ≤ rho)
    (coefficient_one : 1 ≤ (coefficient : ℝ)) :
    proposition63DependentSlabWidth rho (Real.sqrt rho)
        (proposition63DependentCoarseIncidence rho incidence coefficient)
        coefficient ≤
      167 * (coefficient : ℝ) * rho := by
  have rho_nonneg : 0 ≤ rho := rho_pos.le
  have sqrt_nonneg : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg _
  have sqrt_sq : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt rho_nonneg
  have rho_le_sqrt : rho ≤ Real.sqrt rho := by
    nlinarith
  have coarse_le := proposition63_dependent_coarse_incidence_le rho_pos
    incidence_nonneg incidence_le coefficient_one
  have coefficient_nonneg : 0 ≤ (coefficient : ℝ) := by positivity
  have first_nonneg :
      0 ≤ Real.sqrt rho + 12 * rho := by positivity
  have first_le :
      Real.sqrt rho + 12 * rho ≤ 13 * Real.sqrt rho := by
    linarith
  have coarse_nonneg :
      0 ≤ proposition63DependentCoarseIncidence rho incidence coefficient := by
    dsimp only [proposition63DependentCoarseIncidence]
    positivity
  have second_nonneg :
      0 ≤ 2 * proposition63DependentCoarseIncidence rho incidence coefficient +
        3 * (coefficient : ℝ) * Real.sqrt rho := by positivity
  have second_le :
      2 * proposition63DependentCoarseIncidence rho incidence coefficient +
          3 * (coefficient : ℝ) * Real.sqrt rho ≤
        11 * (coefficient : ℝ) * Real.sqrt rho := by
    nlinarith
  dsimp only [proposition63DependentSlabWidth]
  calc
    (Real.sqrt rho + 12 * rho) *
          (2 * proposition63DependentCoarseIncidence rho incidence coefficient +
            3 * (coefficient : ℝ) * Real.sqrt rho) + 24 * rho
        ≤ (13 * Real.sqrt rho) *
            (11 * (coefficient : ℝ) * Real.sqrt rho) + 24 * rho := by
          gcongr
    _ = 143 * (coefficient : ℝ) * rho + 24 * rho := by
      calc
        (13 * Real.sqrt rho) *
              (11 * (coefficient : ℝ) * Real.sqrt rho) + 24 * rho =
            143 * (coefficient : ℝ) * (Real.sqrt rho) ^ 2 + 24 * rho := by
              ring
        _ = 143 * (coefficient : ℝ) * rho + 24 * rho := by rw [sqrt_sq]
    _ ≤ 167 * (coefficient : ℝ) * rho := by
      nlinarith

/-- The exponent of the final paper scalar requirement. -/
noncomputable def proposition63FourCallPaperFinalExponent
    (sigma normalizationLoss outputLoss epsilon₁ angular : ℝ) : ℝ :=
  (1 - sigma) / 2 + normalizationLoss + outputLoss +
    7 * epsilon₁ + angular

/-- Exact simplification of the volume-and-denominator quotient at the
square-root scale. -/
theorem proposition63_four_call_final_analytic_quotient_eq
    {rho sigma normalizationLoss outputLoss epsilon₁ angular : ℝ}
    (rho_pos : 0 < rho) :
    proposition63RobustTauTotalVolume rho sigma normalizationLoss outputLoss
          (Real.sqrt rho) (Real.sqrt rho) /
        (Real.rpow rho (1 + 7 * epsilon₁ + angular) *
          (Real.sqrt rho) ^ 2 / 200) =
      (216 * 27 * 200 : ℝ) *
        Real.rpow rho
          (-(proposition63FourCallPaperFinalExponent sigma normalizationLoss
            outputLoss epsilon₁ angular)) := by
  have rho_ne : rho ≠ 0 := rho_pos.ne'
  have sqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.2 rho_pos
  have sqrt_ne : Real.sqrt rho ≠ 0 := sqrt_pos.ne'
  have sqrt_sq : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt rho_pos.le
  have sqrt_power :
      Real.rpow (Real.sqrt rho) (3 - sigma - 2 * outputLoss) =
        Real.rpow rho ((1 / 2 : ℝ) * (3 - sigma - 2 * outputLoss)) := by
    rw [Real.sqrt_eq_rpow]
    exact (Real.rpow_mul rho_pos.le _ _).symm
  rw [proposition63RobustTauTotalVolume]
  rw [show (3 * Real.sqrt rho) / Real.sqrt rho = 3 by field_simp]
  rw [sqrt_sq]
  rw [sqrt_power]
  have power_ne : Real.rpow rho (1 + 7 * epsilon₁ + angular) ≠ 0 :=
    (Real.rpow_pos_of_pos rho_pos _).ne'
  field_simp
  calc
    3 ^ 3 * Real.rpow rho (sigma - normalizationLoss) *
          Real.rpow rho ((3 - sigma - 2 * outputLoss) / 2) =
        27 * (Real.rpow rho (sigma - normalizationLoss) *
          Real.rpow rho ((3 - sigma - 2 * outputLoss) / 2)) := by ring
    _ = 27 * Real.rpow rho
        ((sigma - normalizationLoss) +
          (3 - sigma - 2 * outputLoss) / 2) := by
      exact congrArg (fun x : ℝ => 27 * x)
        (Real.rpow_add rho_pos _ _).symm
    _ = 27 * Real.rpow rho
        ((1 + 7 * epsilon₁ + angular) + 1 +
          (-(proposition63FourCallPaperFinalExponent sigma normalizationLoss
            outputLoss epsilon₁ angular))) := by
      congr 2
      dsimp only [proposition63FourCallPaperFinalExponent]
      ring
    _ = 27 * (Real.rpow rho (1 + 7 * epsilon₁ + angular) *
          Real.rpow rho 1 *
          Real.rpow rho
            (-(proposition63FourCallPaperFinalExponent sigma normalizationLoss
              outputLoss epsilon₁ angular))) := by
      have houter := Real.rpow_add rho_pos
        ((1 + 7 * epsilon₁ + angular) + 1)
        (-(proposition63FourCallPaperFinalExponent sigma normalizationLoss
          outputLoss epsilon₁ angular))
      have hinner := Real.rpow_add rho_pos
        (1 + 7 * epsilon₁ + angular) 1
      calc
        27 * Real.rpow rho
              ((1 + 7 * epsilon₁ + angular) + 1 +
                (-(proposition63FourCallPaperFinalExponent sigma
                  normalizationLoss outputLoss epsilon₁ angular))) =
            27 * (Real.rpow rho ((1 + 7 * epsilon₁ + angular) + 1) *
              Real.rpow rho
                (-(proposition63FourCallPaperFinalExponent sigma
                  normalizationLoss outputLoss epsilon₁ angular))) :=
          congrArg (fun x : ℝ => 27 * x) houter
        _ = 27 * (Real.rpow rho (1 + 7 * epsilon₁ + angular) *
              Real.rpow rho 1 *
              Real.rpow rho
                (-(proposition63FourCallPaperFinalExponent sigma
                  normalizationLoss outputLoss epsilon₁ angular))) := by
          exact congrArg (fun x : ℝ => 27 *
            (x * Real.rpow rho
              (-(proposition63FourCallPaperFinalExponent sigma
                normalizationLoss outputLoss epsilon₁ angular)))) hinner
    _ = Real.rpow rho (1 + 7 * epsilon₁ + angular) * rho * 27 *
          Real.rpow rho
            (-(proposition63FourCallPaperFinalExponent sigma normalizationLoss
              outputLoss epsilon₁ angular)) := by
      rw [show Real.rpow rho 1 = rho by exact Real.rpow_one rho]
      ring

/-- The entire final arithmetic requirement is bounded by one fixed
coefficient times the advertised negative power of `rho`. -/
theorem proposition63_four_call_final_arithmetic_requirement_le
    {rho sigma normalizationLoss outputLoss epsilon₁ angular incidence : ℝ}
    {coefficient : NNReal}
    (rho_pos : 0 < rho) (rho_le_one : rho ≤ 1)
    (incidence_nonneg : 0 ≤ incidence) (incidence_le : incidence ≤ rho)
    (coefficient_one : 1 ≤ (coefficient : ℝ)) :
    proposition63FourCallFinalArithmeticRequirement rho sigma
        normalizationLoss outputLoss (Real.sqrt rho) epsilon₁ angular
        incidence coefficient ≤
      (391910400 : ENNReal) * (coefficient : ENNReal) ^ 2 *
        Kakeya.realRpowENN rho
          (-(proposition63FourCallPaperFinalExponent sigma normalizationLoss
            outputLoss epsilon₁ angular)) := by
  have slab_le := proposition63_dependent_sqrt_slab_width_le rho_pos
    rho_le_one incidence_nonneg incidence_le coefficient_one
  have coefficient_nonneg : 0 ≤ (coefficient : ℝ) := by positivity
  have coefficient_sq_one : 1 ≤ (coefficient : ℝ) ^ 2 := by nlinarith
  have slab_div_le :
      proposition63DependentSlabWidth rho (Real.sqrt rho)
          (proposition63DependentCoarseIncidence rho incidence coefficient)
          coefficient / rho ≤ 167 * (coefficient : ℝ) := by
    exact (div_le_iff₀ rho_pos).2 (by nlinarith)
  have cordoba_factor_le :
      2 * proposition63DependentSlabWidth rho (Real.sqrt rho)
          (proposition63DependentCoarseIncidence rho incidence coefficient)
          coefficient / rho + 2 ≤
        336 * (coefficient : ℝ) ^ 2 := by
    calc
      2 * proposition63DependentSlabWidth rho (Real.sqrt rho)
            (proposition63DependentCoarseIncidence rho incidence coefficient)
            coefficient / rho + 2
          ≤ 334 * (coefficient : ℝ) + 2 := by
        calc
          2 * proposition63DependentSlabWidth rho (Real.sqrt rho)
                (proposition63DependentCoarseIncidence rho incidence coefficient)
                coefficient / rho + 2 =
              2 * (proposition63DependentSlabWidth rho (Real.sqrt rho)
                (proposition63DependentCoarseIncidence rho incidence coefficient)
                coefficient / rho) + 2 := by ring
          _ ≤ 2 * (167 * (coefficient : ℝ)) + 2 := by gcongr
          _ = 334 * (coefficient : ℝ) + 2 := by ring
      _ ≤ 336 * (coefficient : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((coefficient : ℝ) - 1)]
  have quotient_eq := proposition63_four_call_final_analytic_quotient_eq
    (rho := rho) (sigma := sigma)
    (normalizationLoss := normalizationLoss) (outputLoss := outputLoss)
    (epsilon₁ := epsilon₁) (angular := angular) rho_pos
  have fixed_power_nonneg :
      0 ≤ (216 * 27 * 200 : ℝ) *
        Real.rpow rho
          (-(proposition63FourCallPaperFinalExponent sigma normalizationLoss
            outputLoss epsilon₁ angular)) := by
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg rho_pos.le _)
  have real_bound :
      (proposition63RobustTauTotalVolume rho sigma normalizationLoss outputLoss
          (Real.sqrt rho) (Real.sqrt rho) /
        (Real.rpow rho (1 + 7 * epsilon₁ + angular) *
          (Real.sqrt rho) ^ 2 / 200)) *
        (2 * proposition63DependentSlabWidth rho (Real.sqrt rho)
            (proposition63DependentCoarseIncidence rho incidence coefficient)
            coefficient / rho + 2) ≤
      (391910400 : ℝ) * (coefficient : ℝ) ^ 2 *
        Real.rpow rho
          (-(proposition63FourCallPaperFinalExponent sigma normalizationLoss
            outputLoss epsilon₁ angular)) := by
    rw [quotient_eq]
    calc
    (216 * 27 * 200 : ℝ) *
          Real.rpow rho
            (-(proposition63FourCallPaperFinalExponent sigma normalizationLoss
              outputLoss epsilon₁ angular)) *
          (2 * proposition63DependentSlabWidth rho (Real.sqrt rho)
              (proposition63DependentCoarseIncidence rho incidence coefficient)
              coefficient / rho + 2)
        ≤ (216 * 27 * 200 : ℝ) *
            Real.rpow rho
              (-(proposition63FourCallPaperFinalExponent sigma normalizationLoss
                outputLoss epsilon₁ angular)) *
            (336 * (coefficient : ℝ) ^ 2) := by
          exact mul_le_mul_of_nonneg_left cordoba_factor_le fixed_power_nonneg
    _ = (391910400 : ℝ) * (coefficient : ℝ) ^ 2 *
          Real.rpow rho
            (-(proposition63FourCallPaperFinalExponent sigma normalizationLoss
              outputLoss epsilon₁ angular)) := by ring
  dsimp only [proposition63FourCallFinalArithmeticRequirement]
  calc
    ENNReal.ofReal
        ((proposition63RobustTauTotalVolume rho sigma normalizationLoss outputLoss
            (Real.sqrt rho) (Real.sqrt rho) /
          (Real.rpow rho (1 + 7 * epsilon₁ + angular) *
            (Real.sqrt rho) ^ 2 / 200)) *
          (2 * proposition63DependentSlabWidth rho (Real.sqrt rho)
              (proposition63DependentCoarseIncidence rho incidence coefficient)
              coefficient / rho + 2))
        ≤ ENNReal.ofReal ((391910400 : ℝ) * (coefficient : ℝ) ^ 2 *
            Real.rpow rho
              (-(proposition63FourCallPaperFinalExponent sigma normalizationLoss
                outputLoss epsilon₁ angular))) :=
          ENNReal.ofReal_le_ofReal real_bound
    _ = (391910400 : ENNReal) * (coefficient : ENNReal) ^ 2 *
          Kakeya.realRpowENN rho
            (-(proposition63FourCallPaperFinalExponent sigma normalizationLoss
              outputLoss epsilon₁ angular)) := by
      simp only [Kakeya.realRpowENN]
      rw [ENNReal.ofReal_mul (by positivity)]
      rw [ENNReal.ofReal_mul (by positivity)]
      have hcoeff : ENNReal.ofReal ((coefficient : ℝ) ^ 2) =
          (coefficient : ENNReal) ^ 2 := by
        rw [ENNReal.ofReal_pow (by positivity)]
        rw [ENNReal.ofReal_coe_nnreal]
      rw [hcoeff]
      norm_num

/-- The exact integer cover budget selected from the normalized final choice
has a uniform pre-runtime upper bound. -/
theorem proposition63_four_call_exact_cover_budget_upper
    {rho sigma normalizationLoss outputLoss epsilon₁ angular incidence : ℝ}
    {coefficient : NNReal}
    (rho_pos : 0 < rho) (rho_le_one : rho ≤ 1)
    (incidence_nonneg : 0 ≤ incidence) (incidence_le : incidence ≤ rho)
    (coefficient_one : 1 ≤ (coefficient : ℝ))
    (final : Proposition63FourCallFinalConstantChoice rho sigma
      normalizationLoss outputLoss (Real.sqrt rho) epsilon₁ angular incidence
      coefficient)
    (cover : Proposition63FourCallCoverBudgetChoice
      (proposition63FourCallCoverRequirement coefficient final.finalConstant
        rho (Real.sqrt rho) sigma)) :
    (cover.coverBudget : ENNReal) ≤
      (1605264998400 : ENNReal) * (coefficient : ENNReal) ^ 3 *
        Kakeya.realRpowENN rho
          (-(proposition63FourCallPaperFinalExponent sigma normalizationLoss
            outputLoss epsilon₁ angular)) + 2 := by
  have hceilReal :
      (Nat.ceil (2 * (coefficient : ℝ)) : ℝ) <
        2 * (coefficient : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hfactorReal :
      (2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ℕ) ≤
        8 * (coefficient : ℝ) := by
    norm_cast
    nlinarith
  have hfactor :
      (2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) ≤
        8 * (coefficient : ENNReal) := by
    exact_mod_cast hfactorReal
  have harithmetic := proposition63_four_call_final_arithmetic_requirement_le
    (rho := rho) (sigma := sigma)
    (normalizationLoss := normalizationLoss) (outputLoss := outputLoss)
    (epsilon₁ := epsilon₁) (angular := angular)
    (incidence := incidence) (coefficient := coefficient) rho_pos rho_le_one
    incidence_nonneg incidence_le coefficient_one
  have hrequirement :
      proposition63FourCallCoverRequirement coefficient final.finalConstant
          rho (Real.sqrt rho) sigma =
        (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            proposition63FourCallFinalArithmeticRequirement rho sigma
              normalizationLoss outputLoss (Real.sqrt rho) epsilon₁ angular
              incidence coefficient) := by
    dsimp only [proposition63FourCallCoverRequirement]
    rw [final.normalized]
  calc
    (cover.coverBudget : ENNReal) ≤
        proposition63FourCallCoverRequirement coefficient final.finalConstant
            rho (Real.sqrt rho) sigma + 2 := cover.upper_bound
    _ = (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            proposition63FourCallFinalArithmeticRequirement rho sigma
              normalizationLoss outputLoss (Real.sqrt rho) epsilon₁ angular
              incidence coefficient) + 2 := by rw [hrequirement]
    _ ≤ (1605264998400 : ENNReal) * (coefficient : ENNReal) ^ 3 *
          Kakeya.realRpowENN rho
            (-(proposition63FourCallPaperFinalExponent sigma normalizationLoss
              outputLoss epsilon₁ angular)) + 2 := by
      have hrough : (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            proposition63FourCallFinalArithmeticRequirement rho sigma
              normalizationLoss outputLoss (Real.sqrt rho) epsilon₁ angular
              incidence coefficient)
        ≤ 512 * ((8 * (coefficient : ENNReal)) *
            ((391910400 : ENNReal) * (coefficient : ENNReal) ^ 2 *
              Kakeya.realRpowENN rho
                (-(proposition63FourCallPaperFinalExponent sigma
                  normalizationLoss outputLoss epsilon₁ angular)))) := by
          gcongr
      have hsimplify : (512 : ENNReal) * ((8 * (coefficient : ENNReal)) *
            ((391910400 : ENNReal) * (coefficient : ENNReal) ^ 2 *
              Kakeya.realRpowENN rho
                (-(proposition63FourCallPaperFinalExponent sigma
                  normalizationLoss outputLoss epsilon₁ angular)))) =
          (1605264998400 : ENNReal) * (coefficient : ENNReal) ^ 3 *
          Kakeya.realRpowENN rho
            (-(proposition63FourCallPaperFinalExponent sigma normalizationLoss
              outputLoss epsilon₁ angular)) := by
        ring
      have hmain := hrough.trans_eq hsimplify
      simpa [add_comm] using add_le_add_right hmain 2

end Kakeya.Assouad.PureWZ2
