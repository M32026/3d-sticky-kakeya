import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSReadyStateStatements

/-!
WZ2 Theorem 5.2: absorb the exact initial terminal-cell cardinality loss into
the scheduled step-zero parameter-Frostman constant.
-/

namespace Kakeya.Assouad

theorem grid_os_initial_parameter_absorption :
    GridOSInitialParameterAbsorptionStatement := by
  intro epsilon etaMax steps schedule delta hdelta_pos hdelta_le family shading initial
  let sourceEta := schedule.sourceEta
  have h_eta_pos : 0 < sourceEta := schedule.sourceEta_pos

  -- Helper: realRpowENN multiplication
  have h_rpow_mul : ∀ (a b : ℝ),
      Kakeya.realRpowENN delta a * Kakeya.realRpowENN delta b =
      Kakeya.realRpowENN delta (a + b) := by
    intro a b
    simp only [Kakeya.realRpowENN]
    have ha : 0 ≤ Real.rpow delta a := Real.rpow_nonneg hdelta_pos.le a
    have h_real : Real.rpow delta (a + b) = Real.rpow delta a * Real.rpow delta b :=
      Real.rpow_add hdelta_pos a b
    rw [h_real, ← ENNReal.ofReal_mul ha]

  -- Helper: realRpowENN inverse
  have h_rpow_inv : ∀ (a : ℝ),
      (Kakeya.realRpowENN delta a)⁻¹ = Kakeya.realRpowENN delta (-a) := by
    intro a
    have hpos : 0 < Real.rpow delta a := Real.rpow_pos_of_pos hdelta_pos a
    have h1 : (Kakeya.realRpowENN delta a)⁻¹ = ENNReal.ofReal ((Real.rpow delta a)⁻¹) := by
      simp only [Kakeya.realRpowENN]
      exact (ENNReal.ofReal_inv_of_pos hpos).symm
    rw [h1]
    have h2 : (Real.rpow delta a)⁻¹ = Real.rpow delta (-a) := by
      have h3 : Real.rpow delta (-a) = (Real.rpow delta a)⁻¹ := Real.rpow_neg hdelta_pos.le a
      exact h3.symm
    rw [h2]
    rfl

  -- Step 1: loss ≤ delta^(-sourceEta) implies delta^(sourceEta) ≤ loss⁻¹
  have h_loss_bound : initial.loss ≤ Kakeya.realRpowENN delta (-sourceEta) :=
    initial.loss_bound
  have h_inv_eq : (Kakeya.realRpowENN delta (-sourceEta))⁻¹ =
      Kakeya.realRpowENN delta sourceEta := by
    rw [h_rpow_inv (-sourceEta)]
    have hneg : -(-sourceEta) = sourceEta := by ring
    rw [hneg]
  have h_loss_inv_lower : Kakeya.realRpowENN delta sourceEta ≤ initial.loss⁻¹ := by
    have h : (Kakeya.realRpowENN delta (-sourceEta))⁻¹ ≤ initial.loss⁻¹ :=
      ENNReal.inv_le_inv.mpr h_loss_bound
    rw [h_inv_eq] at h
    exact h

  -- Step 2: cardinalityFraction ≥ (1/2) * delta^(2*sourceEta)
  have h3 : Kakeya.realRpowENN delta sourceEta * Kakeya.realRpowENN delta sourceEta =
      Kakeya.realRpowENN delta (2 * sourceEta) := by
    rw [h_rpow_mul sourceEta sourceEta]
    have h4 : sourceEta + sourceEta = 2 * sourceEta := by ring
    rw [h4]

  have h_card_lower : initial.cardinalityFraction ≥
      (1 / 2 : ENNReal) * Kakeya.realRpowENN delta (2 * sourceEta) := by
    have h1 : initial.cardinalityFraction =
        terminalCellInitialDensity delta sourceEta * initial.loss⁻¹ :=
      initial.cardinalityFraction_eq
    rw [h1]
    have h_density : terminalCellInitialDensity delta sourceEta =
        (1 / 2 : ENNReal) * Kakeya.realRpowENN delta sourceEta := by rfl
    rw [h_density]
    have h2 : (1 / 2 : ENNReal) * Kakeya.realRpowENN delta sourceEta * initial.loss⁻¹ ≥
        (1 / 2 : ENNReal) * Kakeya.realRpowENN delta sourceEta *
          Kakeya.realRpowENN delta sourceEta := by
      gcongr
    have h4 : (1 / 2 : ENNReal) * Kakeya.realRpowENN delta sourceEta *
          Kakeya.realRpowENN delta sourceEta =
        (1 / 2 : ENNReal) * (Kakeya.realRpowENN delta sourceEta *
          Kakeya.realRpowENN delta sourceEta) := by
      exact mul_assoc (1 / 2 : ENNReal) (Kakeya.realRpowENN delta sourceEta) (Kakeya.realRpowENN delta sourceEta)
    rw [h4, h3] at h2
    exact h2

  -- Step 3: Invert the lower bound
  let lower := (1 / 2 : ENNReal) * Kakeya.realRpowENN delta (2 * sourceEta)
  have h_lower_ne_zero : lower ≠ 0 := by
    simp only [lower]
    have h1 : (1 / 2 : ENNReal) ≠ 0 := by norm_num
    have h2 : Kakeya.realRpowENN delta (2 * sourceEta) ≠ 0 := by
      simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hdelta_pos]
    exact mul_ne_zero h1 h2
  have h_lower_ne_top : lower ≠ ⊤ := by
    simp only [lower]
    have h1 : (1 / 2 : ENNReal) ≠ ⊤ := by norm_num
    have h2 : Kakeya.realRpowENN delta (2 * sourceEta) ≠ ⊤ := by
      simp [Kakeya.realRpowENN]
    exact ENNReal.mul_ne_top h1 h2

  have h2_rpow : Kakeya.realRpowENN delta (2 * sourceEta) *
      Kakeya.realRpowENN delta (-2 * sourceEta) = 1 := by
    rw [h_rpow_mul (2 * sourceEta) (-2 * sourceEta)]
    have h3 : (2 * sourceEta) + (-2 * sourceEta) = 0 := by ring
    rw [h3]
    simp [Kakeya.realRpowENN]

  -- Product: lower * (2 * delta^(-2*sourceEta)) = 1
  have h_half_two : (1 / 2 : ENNReal) * (2 : ENNReal) = 1 := by
    have h_eq : (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by simp
    rw [h_eq]
    exact ENNReal.inv_mul_cancel (by simp) (by simp)
  have h_lower_prod : lower * ((2 : ENNReal) * Kakeya.realRpowENN delta (-2 * sourceEta)) = 1 := by
    simp only [lower]
    calc
      ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta (2 * sourceEta)) *
          ((2 : ENNReal) * Kakeya.realRpowENN delta (-2 * sourceEta))
        = ((1 / 2 : ENNReal) * (2 : ENNReal)) *
            (Kakeya.realRpowENN delta (2 * sourceEta) * Kakeya.realRpowENN delta (-2 * sourceEta)) := by
          rw [mul_mul_mul_comm]
      _ = 1 * 1 := by rw [h_half_two, h2_rpow]
      _ = 1 := by simp

  have h_lower_inv : lower⁻¹ = (2 : ENNReal) * Kakeya.realRpowENN delta (-2 * sourceEta) := by
    calc
      lower⁻¹
        = lower⁻¹ * 1 := by simp
      _ = lower⁻¹ * (lower * ((2 : ENNReal) * Kakeya.realRpowENN delta (-2 * sourceEta))) := by
          rw [h_lower_prod]
      _ = (lower⁻¹ * lower) * ((2 : ENNReal) * Kakeya.realRpowENN delta (-2 * sourceEta)) := by ring
      _ = 1 * ((2 : ENNReal) * Kakeya.realRpowENN delta (-2 * sourceEta)) := by
          have h_cancel : lower⁻¹ * lower = 1 :=
            ENNReal.inv_mul_cancel h_lower_ne_zero h_lower_ne_top
          rw [h_cancel]
      _ = (2 : ENNReal) * Kakeya.realRpowENN delta (-2 * sourceEta) := by simp

  have h_card_inv_upper : initial.cardinalityFraction⁻¹ ≤
      (2 : ENNReal) * Kakeya.realRpowENN delta (-2 * sourceEta) := by
    have h : initial.cardinalityFraction⁻¹ ≤ lower⁻¹ :=
      ENNReal.inv_le_inv.mpr h_card_lower
    rw [h_lower_inv] at h
    exact h

  -- Step 4: parameterConstant ≤ 2 * delta^(-3*sourceEta)
  have h_main : initial.state.parameterConstant =
      Kakeya.realRpowENN delta (-sourceEta) * initial.cardinalityFraction⁻¹ := by
    calc
      initial.state.parameterConstant
        = initial.parameterConstant := initial.state_parameter_eq
      _ = Kakeya.realRpowENN delta (-sourceEta) * initial.cardinalityFraction⁻¹ :=
          initial.parameterConstant_eq

  have h5 : Kakeya.realRpowENN delta (-sourceEta) *
        ((2 : ENNReal) * Kakeya.realRpowENN delta (-2 * sourceEta)) =
      (2 : ENNReal) * Kakeya.realRpowENN delta (-3 * sourceEta) := by
    have h51 : Kakeya.realRpowENN delta (-sourceEta) *
          ((2 : ENNReal) * Kakeya.realRpowENN delta (-2 * sourceEta)) =
        (2 : ENNReal) * (Kakeya.realRpowENN delta (-sourceEta) *
          Kakeya.realRpowENN delta (-2 * sourceEta)) := by ring
    rw [h51]
    have h52 : Kakeya.realRpowENN delta (-sourceEta) *
        Kakeya.realRpowENN delta (-2 * sourceEta) =
        Kakeya.realRpowENN delta ((-sourceEta) + (-2 * sourceEta)) := by
      rw [h_rpow_mul (-sourceEta) (-2 * sourceEta)]
    rw [h52]
    have h53 : (-sourceEta) + (-2 * sourceEta) = -3 * sourceEta := by ring
    rw [h53]

  have h_bound : initial.state.parameterConstant ≤
      (2 : ENNReal) * Kakeya.realRpowENN delta (-3 * sourceEta) := by
    rw [h_main]
    have h4 : Kakeya.realRpowENN delta (-sourceEta) * initial.cardinalityFraction⁻¹ ≤
        Kakeya.realRpowENN delta (-sourceEta) *
          ((2 : ENNReal) * Kakeya.realRpowENN delta (-2 * sourceEta)) := by
      gcongr
    rw [h5] at h4
    exact h4

  -- Final step from schedule
  exact h_bound.trans (schedule.initial_parameter_ready delta hdelta_pos hdelta_le)

end Kakeya.Assouad
