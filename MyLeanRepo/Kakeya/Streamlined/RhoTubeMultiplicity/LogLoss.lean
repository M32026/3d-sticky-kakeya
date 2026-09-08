import MyLeanRepo.Kakeya.Streamlined.SubpolynomialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Logarithmic to polynomial loss conversion

Converts the `(log N)^3` mass-retention loss from
`factoring_multiplicity_regularization_main` into a polynomial loss of the form
`delta^epsilon * (N+1)^(-epsilon) * A^(-1)`.

Whiteprint node: `rho-tube-log-loss`.
-/

noncomputable section

namespace Kakeya.Streamlined

/--
For any `epsilon > 0`, there exists `A ≥ 1` such that for all `N : ℕ` and
`0 < delta ≤ 1`:
`((Nat.log 2 N + 1)^3 : ENNReal) ≤ A * delta^(-epsilon) * (N+1)^epsilon`.
-/
lemma rho_tube_log_loss_bound (epsilon : ℝ) (hε : 0 < epsilon) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (N : ℕ) (delta : ℝ), 0 < delta → delta ≤ 1 →
      ((Nat.log 2 N + 1 : ℕ) : ENNReal) ^ 3 ≤
        ENNReal.ofReal A * Kakeya.realRpowENN delta (-epsilon) *
        ENNReal.rpow (N + 1) epsilon := by
  let C : ℝ := 216 / ((Real.log 2)^3 * epsilon^3)
  let A : ℝ := max 1 C
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA2 : C ≤ A := le_max_right _ _
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_eps3_pos : 0 < epsilon / 3 := by positivity
  have hA_pos : 0 < A := by linarith

  have h_main_real : ∀ (N : ℕ),
      ((Nat.log 2 N + 1 : ℕ) : ℝ)^3 ≤ A * ((↑N + 1 : ℝ)^epsilon) := by
    intro N
    by_cases hN : N ≤ 1
    · -- N ≤ 1
      have h_log_one : (Nat.log 2 N + 1 : ℕ) = 1 := by
        interval_cases N <;> simp
      rw [h_log_one]
      have h3 : (1 : ℝ) ≤ ((↑N + 1 : ℝ)^epsilon) := by
        have h4 : (1 : ℝ) ≤ (↑N + 1 : ℝ) := by exact_mod_cast (by omega)
        exact Real.one_le_rpow h4 hε.le
      have h5 : (1 : ℝ) ≤ A * ((↑N + 1 : ℝ)^epsilon) := by
        calc (1 : ℝ)
          ≤ A := hA1
          _ = A * 1 := by ring
          _ ≤ A * ((↑N + 1 : ℝ)^epsilon) := by gcongr
      simpa using h5
    · -- N ≥ 2
      have hN2 : N ≥ 2 := by omega
      have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
      have hN_ge2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2

      have h_pow : (2 : ℝ)^(Nat.log 2 N) ≤ (N : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have h_log_mul : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
        have h : Real.log ((2 : ℝ)^(Nat.log 2 N)) ≤ Real.log (N : ℝ) :=
          Real.log_le_log (by positivity) h_pow
        have h2 : Real.log ((2 : ℝ)^(Nat.log 2 N)) =
            (Nat.log 2 N : ℝ) * Real.log 2 := by
          rw [Real.log_pow] <;> norm_num
        rw [h2] at h
        exact h
      have h_div : ((Nat.log 2 N : ℝ) * Real.log 2) / Real.log 2 = (Nat.log 2 N : ℝ) := by
        have h : ((Nat.log 2 N : ℝ) * Real.log 2) / Real.log 2 =
            (Nat.log 2 N : ℝ) * (Real.log 2 / Real.log 2) := by ring
        rw [h]
        have h2 : Real.log 2 / Real.log 2 = 1 := by
          exact div_self h_log2_pos.ne'
        rw [h2] <;> ring
      have h1 : (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
        calc (Nat.log 2 N : ℝ)
          = ((Nat.log 2 N : ℝ) * Real.log 2) / Real.log 2 := h_div.symm
          _ ≤ Real.log (N : ℝ) / Real.log 2 := by gcongr

      have h2 : (1 : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
        have h_logN_ge : Real.log (N : ℝ) ≥ Real.log 2 :=
          Real.log_le_log (by positivity) hN_ge2
        have h : Real.log (N : ℝ) / Real.log 2 ≥ Real.log 2 / Real.log 2 := by gcongr
        have h' : Real.log 2 / Real.log 2 = 1 := by
          exact div_self h_log2_pos.ne'
        rw [h'] at h
        exact h

      have h_sum : (Nat.log 2 N : ℝ) + 1 ≤ (Real.log (N : ℝ) / Real.log 2) + (Real.log (N : ℝ) / Real.log 2) :=
        add_le_add h1 h2
      have h_eq : (Real.log (N : ℝ) / Real.log 2) + (Real.log (N : ℝ) / Real.log 2) = 2 * Real.log (N : ℝ) / Real.log 2 := by ring
      have h3 : ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) / Real.log 2 := by
        have h4 : ((Nat.log 2 N + 1 : ℕ) : ℝ) = (Nat.log 2 N : ℝ) + 1 := by simp
        rw [h4]
        rw [h_eq] at h_sum
        exact h_sum

      have h5 : Real.log (N : ℝ) ≤ (N : ℝ)^(epsilon / 3) / (epsilon / 3) :=
        Real.log_le_rpow_div (by linarith) h_eps3_pos

      have h10_rpow : ((N : ℝ)^(epsilon / 3))^3 = (N : ℝ)^epsilon := by
        have h11 : ((N : ℝ)^(epsilon / 3))^3 = ((N : ℝ)^(epsilon / 3))^(3 : ℝ) := by norm_cast
        rw [h11]
        have h12 : ((N : ℝ)^(epsilon / 3))^(3 : ℝ) = (N : ℝ)^((epsilon / 3) * 3) := by
          rw [Real.rpow_mul (by linarith)]
        rw [h12]
        have h13 : (epsilon / 3) * 3 = epsilon := by ring
        rw [h13]
      have h9 : ((N : ℝ)^(epsilon / 3) / (epsilon / 3))^3 =
          (N : ℝ)^epsilon / (epsilon / 3)^3 := by
        have h_div3 : ((N : ℝ)^(epsilon / 3) / (epsilon / 3))^3 =
            ((N : ℝ)^(epsilon / 3))^3 / (epsilon / 3)^3 := by ring
        rw [h_div3, h10_rpow]
      have h6 : (Real.log (N : ℝ))^3 ≤ (N : ℝ)^epsilon / (epsilon / 3)^3 := by
        have h7 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
        have h8 : (Real.log (N : ℝ))^3 ≤
            ((N : ℝ)^(epsilon / 3) / (epsilon / 3))^3 := by gcongr
        rw [h9] at h8
        exact h8

      have h10 : (((Nat.log 2 N + 1 : ℕ) : ℝ)^3) ≤ C * ((N : ℝ)^epsilon) := by
        have h11 : (((Nat.log 2 N + 1 : ℕ) : ℝ)^3) ≤
            (2 * Real.log (N : ℝ) / Real.log 2)^3 := by gcongr <;> linarith
        have h12 : (2 * Real.log (N : ℝ) / Real.log 2)^3 =
            8 / (Real.log 2)^3 * (Real.log (N : ℝ))^3 := by ring
        rw [h12] at h11
        have h13 : 8 / (Real.log 2)^3 * (Real.log (N : ℝ))^3 ≤
            8 / (Real.log 2)^3 * ((N : ℝ)^epsilon / (epsilon / 3)^3) := by gcongr
        have h14 : 8 / (Real.log 2)^3 * ((N : ℝ)^epsilon / (epsilon / 3)^3) =
            C * ((N : ℝ)^epsilon) := by
          dsimp only [C]
          have h15 : (epsilon / 3)^3 = epsilon^3 / 27 := by ring
          rw [h15]
          field_simp [h_log2_pos.ne', hε.ne'] <;> ring
        rw [h14] at h13
        exact h11.trans h13

      have h15 : (N : ℝ)^epsilon ≤ ((↑N + 1 : ℝ)^epsilon) := by
        have h16 : (N : ℝ) ≤ ((↑N + 1 : ℝ)) := by linarith
        exact Real.rpow_le_rpow (by linarith) h16 (by linarith)

      calc (((Nat.log 2 N + 1 : ℕ) : ℝ)^3)
        ≤ C * ((N : ℝ)^epsilon) := h10
        _ ≤ C * ((↑N + 1 : ℝ)^epsilon) := by gcongr
        _ ≤ A * ((↑N + 1 : ℝ)^epsilon) := by gcongr

  have h_goal : ∀ (N : ℕ) (delta : ℝ), 0 < delta → delta ≤ 1 →
      ((Nat.log 2 N + 1 : ℕ) : ENNReal) ^ 3 ≤
        ENNReal.ofReal A * Kakeya.realRpowENN delta (-epsilon) *
        ENNReal.rpow (N + 1) epsilon := by
    intro N delta hdelta_pos hdelta_le_one

    have h1 : Real.rpow delta epsilon ≤ 1 := by
      have h2 : Real.rpow delta epsilon ≤ Real.rpow 1 epsilon :=
        Real.rpow_le_rpow (by linarith) hdelta_le_one (by linarith)
      have h3 : Real.rpow 1 epsilon = 1 := by simp
      linarith
    have h4 : 0 < Real.rpow delta epsilon := Real.rpow_pos_of_pos hdelta_pos _
    have h5 : Real.rpow delta (-epsilon) = (Real.rpow delta epsilon)⁻¹ :=
      Real.rpow_neg hdelta_pos.le epsilon
    have h6 : (1 : ℝ) ≤ Real.rpow delta (-epsilon) := by
      rw [h5]
      have h7 : (1 : ℝ) ≤ (Real.rpow delta epsilon)⁻¹ := by
        calc (1 : ℝ)
          = (1 : ℝ)⁻¹ := by norm_num
          _ ≤ (Real.rpow delta epsilon)⁻¹ := by gcongr
      exact h7
    have h_delta_rpow_ge_one : (1 : ENNReal) ≤ Kakeya.realRpowENN delta (-epsilon) := by
      have h7 : Kakeya.realRpowENN delta (-epsilon) =
          ENNReal.ofReal (Real.rpow delta (-epsilon)) := by rfl
      rw [h7]
      have h8 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (Real.rpow delta (-epsilon)) := by
        exact ENNReal.ofReal_le_ofReal h6
      simpa using h8

    have h_real : (((Nat.log 2 N + 1 : ℕ) : ℝ)^3) ≤ A * ((↑N + 1 : ℝ)^epsilon) :=
      h_main_real N

    have h_rpow_conv : ENNReal.rpow (N + 1) epsilon =
        ENNReal.ofReal (((↑N + 1 : ℝ)^epsilon)) := by
      have h_pos : (0 : ℝ) < (↑(N + 1) : ℝ) := by positivity
      have h1 : (↑(N + 1) : ENNReal) = ENNReal.ofReal ((↑(N + 1) : ℝ)) := by norm_cast
      have h2 : ENNReal.ofReal ((↑(N + 1) : ℝ)) ^ epsilon =
          ENNReal.ofReal (((↑(N + 1) : ℝ)^epsilon)) :=
        ENNReal.ofReal_rpow_of_pos h_pos
      have h3 : (↑(N + 1) : ℝ) = (↑N + 1 : ℝ) := by norm_cast
      have h4 : (↑N + 1 : ENNReal) = (↑(N + 1) : ENNReal) := by norm_cast
      calc ENNReal.rpow (N + 1) epsilon
        = (↑N + 1 : ENNReal) ^ epsilon := by rfl
        _ = (↑(N + 1) : ENNReal) ^ epsilon := by rw [h4]
        _ = ENNReal.ofReal ((↑(N + 1) : ℝ)) ^ epsilon := by rw [h1]
        _ = ENNReal.ofReal (((↑(N + 1) : ℝ)^epsilon)) := h2
        _ = ENNReal.ofReal (((↑N + 1 : ℝ)^epsilon)) := by rw [h3]

    have h_mul_conv : ENNReal.ofReal (A * ((↑N + 1 : ℝ)^epsilon)) =
        ENNReal.ofReal A * ENNReal.rpow (N + 1) epsilon := by
      have h_pos : 0 ≤ A := by linarith
      have h_pos2 : 0 ≤ ((↑N + 1 : ℝ)^epsilon) := by positivity
      rw [ENNReal.ofReal_mul h_pos, h_rpow_conv]

    have h_lhs_conv : ENNReal.ofReal (((Nat.log 2 N + 1 : ℕ) : ℝ)^3) =
        ((Nat.log 2 N + 1 : ℕ) : ENNReal) ^ 3 := by
      have h : ENNReal.ofReal (((Nat.log 2 N + 1 : ℕ) : ℝ)^3) =
          ↑(((Nat.log 2 N + 1 : ℕ) ^ 3)) := by norm_cast
      rw [h] <;> norm_cast

    have h_ennreal : ((Nat.log 2 N + 1 : ℕ) : ENNReal) ^ 3 ≤
        ENNReal.ofReal A * ENNReal.rpow (N + 1) epsilon := by
      rw [← h_lhs_conv, ← h_mul_conv]
      exact ENNReal.ofReal_le_ofReal (h_main_real N)

    have h10 : ENNReal.ofReal A ≤ ENNReal.ofReal A * Kakeya.realRpowENN delta (-epsilon) := by
      have h11 : ENNReal.ofReal A * (1 : ENNReal) ≤ ENNReal.ofReal A * Kakeya.realRpowENN delta (-epsilon) :=
        mul_le_mul_of_nonneg_left h_delta_rpow_ge_one (by simp)
      simpa using h11

    have h_final : ENNReal.ofReal A * ENNReal.rpow (N + 1) epsilon ≤
        ENNReal.ofReal A * Kakeya.realRpowENN delta (-epsilon) *
          ENNReal.rpow (N + 1) epsilon :=
      mul_le_mul_of_nonneg_right h10 (by simp)

    exact h_ennreal.trans h_final

  exact ⟨A, hA1, h_goal⟩

end Kakeya.Streamlined
