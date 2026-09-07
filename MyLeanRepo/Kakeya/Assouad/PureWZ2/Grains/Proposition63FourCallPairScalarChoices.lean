import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallOrderedPairFrozenStep
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallInnerLossSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63UniformLineHitBudget

/-!
# Explicit pair-local scalar choices for the Proposition 6.3 four-call tail

This module isolates the choices in `Proposition63FourCallFrozenScalarReceiptsAt`
which do not depend on the backward construction of `firstConstant`.  In
particular, it does not claim to construct the complete scalar receipt.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- The left side of the first arithmetic receipt. -/
noncomputable def proposition63FourCallFirstArithmeticRequirement
    (rho tau sigma normalizationLoss outputLoss robustScale epsilon₁ epsilon₃
      incidence : ℝ) (coefficient : NNReal) : ENNReal :=
  ENNReal.ofReal
    ((proposition63RobustTauTotalVolume rho sigma normalizationLoss outputLoss
        robustScale tau /
      (Real.rpow rho (1 + 7 * epsilon₁ + epsilon₃) * tau ^ 2 / 200)) *
      (2 * proposition63DependentSlabWidth rho tau
        (proposition63DependentCoarseIncidence rho incidence coefficient)
        coefficient / rho + 2))

/-- Explicit pair-local first constant and its arithmetic and finiteness
receipts.  This choice is independent of the backward loss seed. -/
structure Proposition63FourCallFirstConstantChoice
    (rho tau sigma normalizationLoss outputLoss robustScale epsilon₁ epsilon₃
      incidence : ℝ) (coefficient : NNReal) where
  firstConstant : ENNReal
  arithmetic : proposition63FourCallFirstArithmeticRequirement rho tau sigma
      normalizationLoss outputLoss robustScale epsilon₁ epsilon₃ incidence
      coefficient ≤
    firstConstant * Kakeya.realRpowENN (tau / rho) (1 - sigma)
  normalized : firstConstant *
      Kakeya.realRpowENN (tau / rho) (1 - sigma) =
    proposition63FourCallFirstArithmeticRequirement rho tau sigma
      normalizationLoss outputLoss robustScale epsilon₁ epsilon₃ incidence
      coefficient
  value_eq : firstConstant =
    proposition63FourCallFirstArithmeticRequirement rho tau sigma
        normalizationLoss outputLoss robustScale epsilon₁ epsilon₃ incidence
        coefficient /
      Kakeya.realRpowENN (tau / rho) (1 - sigma)
  finite : firstConstant ≠ ⊤

noncomputable def proposition63_four_call_first_constant_choice
    {rho tau sigma normalizationLoss outputLoss robustScale epsilon₁ epsilon₃
      incidence : ℝ} {coefficient : NNReal}
    (rho_pos : 0 < rho) (rho_le_tau : rho ≤ tau)
    (sigma_lt_one : sigma < 1) :
    Proposition63FourCallFirstConstantChoice rho tau sigma normalizationLoss
      outputLoss robustScale epsilon₁ epsilon₃ incidence coefficient := by
  let requirement := proposition63FourCallFirstArithmeticRequirement rho tau
    sigma normalizationLoss outputLoss robustScale epsilon₁ epsilon₃ incidence
    coefficient
  let power : ENNReal :=
    Kakeya.realRpowENN (tau / rho) (1 - sigma)
  have ratio_pos : 0 < tau / rho :=
    div_pos (rho_pos.trans_le rho_le_tau) rho_pos
  have power_pos : 0 < power := by
    dsimp only [power, Kakeya.realRpowENN]
    exact ENNReal.ofReal_pos.mpr <| Real.rpow_pos_of_pos ratio_pos _
  have power_top : power ≠ ⊤ := by
    exact ENNReal.ofReal_ne_top
  exact {
    firstConstant := requirement / power
    arithmetic := by
      dsimp only [power]
      rw [ENNReal.div_mul_cancel power_pos.ne' power_top]
    normalized := by
      dsimp only [power]
      rw [ENNReal.div_mul_cancel power_pos.ne' power_top]
    value_eq := rfl
    finite := ENNReal.div_ne_top ENNReal.ofReal_ne_top power_pos.ne'
  }

/-- The left side of the final arithmetic receipt. -/
noncomputable def proposition63FourCallFinalArithmeticRequirement
    (rho sigma normalizationLoss outputLoss sqrtScale epsilon₁ epsilon₃
      incidence : ℝ) (coefficient : NNReal) : ENNReal :=
  ENNReal.ofReal
    ((proposition63RobustTauTotalVolume rho sigma normalizationLoss outputLoss
        sqrtScale sqrtScale /
      (Real.rpow rho (1 + 7 * epsilon₁ + epsilon₃) *
        sqrtScale ^ 2 / 200)) *
      (2 * proposition63DependentSlabWidth rho sqrtScale
        (proposition63DependentCoarseIncidence rho incidence coefficient)
        coefficient / rho + 2))

/-- The final point-cover constant.  Its constructor below divides out the
scale-ratio factor which the covering conclusion multiplies back in, so the
resulting bound is exactly the arithmetic requirement. -/
structure Proposition63FourCallFinalConstantChoice
    (rho sigma normalizationLoss outputLoss sqrtScale epsilon₁ epsilon₃
      incidence : ℝ) (coefficient : NNReal) where
  finalConstant : ENNReal
  arithmetic : proposition63FourCallFinalArithmeticRequirement rho sigma
      normalizationLoss outputLoss sqrtScale epsilon₁ epsilon₃ incidence
      coefficient ≤
    finalConstant * Kakeya.realRpowENN (sqrtScale / rho) (1 - sigma)
  normalized : finalConstant *
      Kakeya.realRpowENN (sqrtScale / rho) (1 - sigma) =
    proposition63FourCallFinalArithmeticRequirement rho sigma
      normalizationLoss outputLoss sqrtScale epsilon₁ epsilon₃ incidence
      coefficient
  finite : finalConstant *
    Kakeya.realRpowENN (sqrtScale / rho) (1 - sigma) ≠ ⊤

noncomputable def proposition63_four_call_final_constant_choice
    {rho sigma normalizationLoss outputLoss sqrtScale epsilon₁ epsilon₃
      incidence : ℝ} {coefficient : NNReal}
    (rho_pos : 0 < rho) (rho_le_sqrt : rho ≤ sqrtScale)
    (_sigma_le_one : sigma ≤ 1) :
    Proposition63FourCallFinalConstantChoice rho sigma normalizationLoss
      outputLoss sqrtScale epsilon₁ epsilon₃ incidence coefficient := by
  let requirement := proposition63FourCallFinalArithmeticRequirement rho sigma
    normalizationLoss outputLoss sqrtScale epsilon₁ epsilon₃ incidence coefficient
  let power : ENNReal :=
    Kakeya.realRpowENN (sqrtScale / rho) (1 - sigma)
  have power_pos : 0 < power := by
    dsimp only [power, Kakeya.realRpowENN]
    exact ENNReal.ofReal_pos.mpr <|
      Real.rpow_pos_of_pos (div_pos (rho_pos.trans_le rho_le_sqrt) rho_pos) _
  have power_top : power ≠ ⊤ := by
    exact ENNReal.ofReal_ne_top
  exact {
    finalConstant := requirement / power
    arithmetic := by
      dsimp only [power]
      rw [ENNReal.div_mul_cancel power_pos.ne' power_top]
    normalized := by
      dsimp only [power]
      rw [ENNReal.div_mul_cancel power_pos.ne' power_top]
    finite := by
      exact ENNReal.mul_ne_top
        (ENNReal.div_ne_top ENNReal.ofReal_ne_top power_pos.ne') power_top
  }

/-- Pair-local positive cell floor together with its exact budget inequality. -/
structure Proposition63FourCallCellVolumeFloorChoice
    (rho sqrtScale sigma outputLoss floorLoss : ℝ) where
  cellVolumeFloor : ℝ
  positive : 0 < cellVolumeFloor
  budget : ENNReal.ofReal cellVolumeFloor *
      Kakeya.realRpowENN sqrtScale (sigma - outputLoss) ≤
    Kakeya.realRpowENN rho (sigma + floorLoss) *
      Kakeya.realRpowENN sqrtScale 3

noncomputable def proposition63_four_call_cell_volume_floor_choice
    {rho sqrtScale sigma outputLoss floorLoss : ℝ}
    (rho_pos : 0 < rho) (sqrt_pos : 0 < sqrtScale) :
    Proposition63FourCallCellVolumeFloorChoice
      rho sqrtScale sigma outputLoss floorLoss := by
  let numerator : ENNReal :=
    Kakeya.realRpowENN rho (sigma + floorLoss) *
      Kakeya.realRpowENN sqrtScale 3
  let denominator : ENNReal :=
    Kakeya.realRpowENN sqrtScale (sigma - outputLoss)
  have numerator_pos : 0 < numerator := by
    dsimp only [numerator]
    exact ENNReal.mul_pos
      (by simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos rho_pos])
      (by simp [Kakeya.realRpowENN]; positivity)
  have numerator_top : numerator ≠ ⊤ := by
    dsimp only [numerator]
    exact ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN])
      (by simp [Kakeya.realRpowENN])
  have denominator_pos : 0 < denominator := by
    dsimp only [denominator]
    simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos sqrt_pos]
  have denominator_top : denominator ≠ ⊤ := by
    dsimp only [denominator]
    simp [Kakeya.realRpowENN]
  let floor : ℝ := (numerator / denominator).toReal
  have quotient_pos : 0 < numerator / denominator :=
    ENNReal.div_pos numerator_pos.ne' denominator_top
  have quotient_top : numerator / denominator ≠ ⊤ :=
    ENNReal.div_ne_top numerator_top denominator_pos.ne'
  refine {
    cellVolumeFloor := floor
    positive := by
      dsimp only [floor]
      exact ENNReal.toReal_pos quotient_pos.ne' quotient_top
    budget := ?_
  }
  change ENNReal.ofReal floor * denominator ≤ numerator
  rw [show ENNReal.ofReal floor = numerator / denominator by
    dsimp only [floor]
    exact ENNReal.ofReal_toReal quotient_top]
  rw [ENNReal.div_mul_cancel denominator_pos.ne' denominator_top]

/-- A positive natural cover budget for the exact final cover requirement. -/
structure Proposition63FourCallCoverBudgetChoice
    (requirement : ENNReal) where
  coverBudget : ℕ
  positive : 0 < coverBudget
  bound : requirement ≤ (coverBudget : ENNReal)
  upper_bound : (coverBudget : ENNReal) ≤ requirement + 2

noncomputable def proposition63_four_call_cover_budget_choice
    (requirement : ENNReal) (requirement_finite : requirement ≠ ⊤) :
    Proposition63FourCallCoverBudgetChoice requirement := {
  coverBudget := Nat.ceil requirement.toNNReal + 1
  positive := Nat.zero_lt_succ _
  bound := by
    rw [Nat.cast_add, Nat.cast_one]
    calc
      requirement = (requirement.toNNReal : ENNReal) :=
        (ENNReal.coe_toNNReal requirement_finite).symm
      _ ≤ (Nat.ceil requirement.toNNReal : ℕ) := by
        exact_mod_cast Nat.le_ceil requirement.toNNReal
      _ ≤ (Nat.ceil requirement.toNNReal : ℕ) + 1 := le_add_right le_rfl
  upper_bound := by
    rw [Nat.cast_add, Nat.cast_one]
    have hceil : ((Nat.ceil requirement.toNNReal : ℕ) : ENNReal) <
        requirement + 1 := by
      calc
        ((Nat.ceil requirement.toNNReal : ℕ) : ENNReal) <
            (requirement.toNNReal : ENNReal) + 1 := by
          exact_mod_cast Nat.ceil_lt_add_one
            (show 0 ≤ requirement.toNNReal from bot_le)
        _ = requirement + 1 := by rw [ENNReal.coe_toNNReal requirement_finite]
    calc
      ((Nat.ceil requirement.toNNReal : ℕ) : ENNReal) + 1 ≤
          (requirement + 1) + 1 := by gcongr
      _ = requirement + 2 := by rw [show (2 : ENNReal) = 1 + 1 by norm_num]; ac_rfl
}

/-- The exact cover requirement occurring in the frozen scalar receipt. -/
noncomputable def proposition63FourCallCoverRequirement
    (coefficient : NNReal) (finalConstant : ENNReal)
    (rho sqrtScale sigma : ℝ) : ENNReal :=
  (512 : ENNReal) *
    ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
      (finalConstant *
        Kakeya.realRpowENN (sqrtScale / rho) (1 - sigma)))

/-- Construct the exact natural cover budget once the final square-root
constant has been shown finite. -/
noncomputable def proposition63_four_call_exact_cover_budget_choice
    (coefficient : NNReal) (finalConstant : ENNReal)
    (rho sqrtScale sigma : ℝ)
    (final_finite : finalConstant *
      Kakeya.realRpowENN (sqrtScale / rho) (1 - sigma) ≠ ⊤) :
    Proposition63FourCallCoverBudgetChoice
      (proposition63FourCallCoverRequirement coefficient finalConstant
        rho sqrtScale sigma) := by
  apply proposition63_four_call_cover_budget_choice
  dsimp only [proposition63FourCallCoverRequirement]
  exact ENNReal.mul_ne_top (by norm_num)
    (ENNReal.mul_ne_top
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _),
          by norm_num⟩)
      final_finite)

/-- The maximum of the two canonical level counts is a common level bound. -/
structure Proposition63FourCallUniformLevelChoice
    (currentNormalizationLoss nestedNormalizationLoss : ℝ) where
  uniformLevel : ℕ
  current_le : proposition63CanonicalNearbyLevelCount currentNormalizationLoss ≤
    uniformLevel
  nested_le : proposition63CanonicalNearbyLevelCount nestedNormalizationLoss ≤
    uniformLevel

noncomputable def proposition63_four_call_uniform_level_choice
    (currentNormalizationLoss nestedNormalizationLoss : ℝ) :
    Proposition63FourCallUniformLevelChoice currentNormalizationLoss
      nestedNormalizationLoss := {
  uniformLevel := max
    (proposition63CanonicalNearbyLevelCount currentNormalizationLoss)
    (proposition63CanonicalNearbyLevelCount nestedNormalizationLoss)
  current_le := le_max_left _ _
  nested_le := le_max_right _ _
}

/-- Canonical choices for the next loss and the supplied natural spatial scale. -/
structure Proposition63FourCallNextScalarChoice
    (loss : ℕ → ℝ) (index : ℕ) (naturalSpatialScale : ℝ) where
  outputCandidateLoss : ℝ
  spatialScale : ℝ
  next_loss : outputCandidateLoss = loss (index + 1)
  spatial_eq : spatialScale = naturalSpatialScale

def proposition63_four_call_next_scalar_choice
    (loss : ℕ → ℝ) (index : ℕ) (naturalSpatialScale : ℝ) :
    Proposition63FourCallNextScalarChoice loss index naturalSpatialScale := {
  outputCandidateLoss := loss (index + 1)
  spatialScale := naturalSpatialScale
  next_loss := rfl
  spatial_eq := rfl
}

/-- Construct the nested-interval absorption after the pair-local first
constant has been chosen. -/
noncomputable def proposition63_four_call_nested_interval_choice
    (coefficient : NNReal) (firstConstant : ENNReal)
    (firstConstant_finite : firstConstant ≠ ⊤)
    {discreteLoss : ℝ} (discreteLoss_pos : 0 < discreteLoss) :
    Proposition63NestedIntervalAbsorptionData
      (coefficient : ℝ) firstConstant discreteLoss :=
  Classical.choice <| proposition63_nested_interval_absorption
    (coefficient : ℝ) firstConstant firstConstant_finite discreteLoss_pos

/-- All pair-local scalar choices which are independent of the exact left and
right factor functions.  The spatial scale is the natural square-root scale. -/
structure Proposition63FourCallPairScalarCoreAt
    {delta sigma discreteLoss intervalLoss gridOutputLoss queryScale outputLoss : ℝ}
    {gridN index : ℕ}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (loss : ℕ → ℝ)
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss)
    (sourceCoefficient : NNReal)
    (incidence : ℝ)
    (currentNormalizationLoss : ℝ)
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    (sqrtRequested : WZ2PaperRequestedScale scales.rhoHat.1)
    (robustScale : WZ2PaperRequestedScale scales.rhoHat.1) where
  first : Proposition63FourCallFirstConstantChoice scales.rhoHat.1 scales.tau
    sigma seed.schedule.third.normalizationLoss
    seed.schedule.thirdOutputLoss robustScale.1 seed.epsilon₁
    seed.epsilon₃ incidence
    ((4 : NNReal) * (lipschitzExtensionConstant Point3 * sourceCoefficient))
  nestedInterval : Proposition63NestedIntervalAbsorptionData
    ((((4 : NNReal) *
      (lipschitzExtensionConstant Point3 * sourceCoefficient)) : NNReal) : ℝ)
    first.firstConstant seed.alignedAbsorption.internalLoss
  final : Proposition63FourCallFinalConstantChoice scales.rhoHat.1 sigma
    seed.schedule.fourth.normalizationLoss outputLoss
    sqrtRequested.1 seed.epsilon₁ seed.epsilon₃ incidence
    ((4 : NNReal) * (lipschitzExtensionConstant Point3 * sourceCoefficient))
  cell : Proposition63FourCallCellVolumeFloorChoice scales.rhoHat.1
    sqrtRequested.1 sigma outputLoss seed.floorLoss
  cover : Proposition63FourCallCoverBudgetChoice
    (proposition63FourCallCoverRequirement
      ((4 : NNReal) * (lipschitzExtensionConstant Point3 * sourceCoefficient))
      final.finalConstant scales.rhoHat.1 sqrtRequested.1 sigma)
  level : Proposition63FourCallUniformLevelChoice
    currentNormalizationLoss seed.schedule.third.normalizationLoss
  hpaperNestedLevel :
    proposition63CanonicalNearbyLevelCount
      seed.schedule.second.normalizationLoss ≤ level.uniformLevel
  next : Proposition63FourCallNextScalarChoice loss index
    sqrtRequested.1

noncomputable def proposition63_four_call_pair_scalar_core
    {delta sigma discreteLoss intervalLoss gridOutputLoss queryScale outputLoss : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    (loss : ℕ → ℝ)
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss)
    (sourceCoefficient : NNReal)
    (incidence : ℝ)
    (currentNormalizationLoss : ℝ)
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    (sqrtRequested : WZ2PaperRequestedScale scales.rhoHat.1)
    (robustScale : WZ2PaperRequestedScale scales.rhoHat.1)
    (sigma_lt_one : sigma < 1) :
    Proposition63FourCallPairScalarCoreAt grid loss seed sourceCoefficient incidence
      currentNormalizationLoss scales sqrtRequested robustScale := by
  let amplified : NNReal :=
    (4 : NNReal) * (lipschitzExtensionConstant Point3 * sourceCoefficient)
  have rho_pos : 0 < scales.rhoHat.1 :=
    (grid.scale_pos _
      (scales.first_lt_second.le.trans scales.second_le_gridN)).trans_le
        scales.logicalR_le_rhoHat
  let first := proposition63_four_call_first_constant_choice
    (rho := scales.rhoHat.1)
    (tau := scales.tau)
    (sigma := sigma)
    (normalizationLoss := seed.schedule.third.normalizationLoss)
    (outputLoss := seed.schedule.thirdOutputLoss)
    (robustScale := robustScale.1)
    (epsilon₁ := seed.epsilon₁)
    (epsilon₃ := seed.epsilon₃)
    (incidence := incidence)
    (coefficient := amplified)
    rho_pos scales.rhoHat_le_tau sigma_lt_one
  let nestedInterval := proposition63_four_call_nested_interval_choice
    amplified first.firstConstant first.finite
      (discreteLoss := seed.alignedAbsorption.internalLoss)
      seed.alignedAbsorption.internal_loss_pos
  let final := proposition63_four_call_final_constant_choice
    (rho := scales.rhoHat.1)
    (sigma := sigma)
    (normalizationLoss := seed.schedule.fourth.normalizationLoss)
    (outputLoss := outputLoss)
    (sqrtScale := sqrtRequested.1)
    (epsilon₁ := seed.epsilon₁)
    (epsilon₃ := seed.epsilon₃)
    (incidence := incidence)
    (coefficient := amplified)
    rho_pos sqrtRequested.property.1 sigma_lt_one.le
  let cell := proposition63_four_call_cell_volume_floor_choice
    (rho := scales.rhoHat.1)
    (sqrtScale := sqrtRequested.1)
    (sigma := sigma)
    (outputLoss := outputLoss)
    (floorLoss := seed.floorLoss)
    rho_pos (rho_pos.trans_le sqrtRequested.property.1)
  let cover := proposition63_four_call_exact_cover_budget_choice amplified
    final.finalConstant scales.rhoHat.1 sqrtRequested.1 sigma
    final.finite
  let uniformLevel := max
    (proposition63CanonicalNearbyLevelCount currentNormalizationLoss)
    (max
      (proposition63CanonicalNearbyLevelCount seed.schedule.second.normalizationLoss)
      (proposition63CanonicalNearbyLevelCount seed.schedule.third.normalizationLoss))
  let level : Proposition63FourCallUniformLevelChoice
      currentNormalizationLoss seed.schedule.third.normalizationLoss := {
    uniformLevel := uniformLevel
    current_le := le_max_left _ _
    nested_le := le_max_of_le_right (le_max_right _ _)
  }
  exact {
    first := first
    nestedInterval := nestedInterval
    final := final
    cell := cell
    cover := cover
    level := level
    hpaperNestedLevel := le_max_of_le_right (le_max_left _ _)
    next := proposition63_four_call_next_scalar_choice loss index
      sqrtRequested.1
  }

end Kakeya.Assouad.PureWZ2
