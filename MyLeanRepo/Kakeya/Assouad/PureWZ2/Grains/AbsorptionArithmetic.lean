import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperCV
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Absorption arithmetic for the broad mass budget
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set ENNReal
open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- Core real arithmetic for the absorption condition. -/
lemma absorption_arithmetic_core
    (L sigma outputLoss : ℝ)
    (N : ℕ)
    (C M mass F_mass Q tau : ℝ)
    (hL_pos : 0 < L)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (houtputLoss_pos : 0 < outputLoss)
    (hN_pos : 0 < N)
    (hC_pos : 0 < C)
    (hM_nonneg : 0 ≤ M)
    (hmass_nonneg : 0 ≤ mass)
    (hQ_nonneg : 0 ≤ Q)
    (htau_pos : 0 < tau)
    (c : ℝ)
    (hc_pos : 0 < c)
    (hM : M ≤ L ^ (2 - sigma - outputLoss) * (N : ℝ))
    (hmass : L ^ (-outputLoss) * F_mass ≤ mass)
    (hF_mass : c * (N : ℝ) * L ^ 2 ≤ F_mass)
    (htau_eq : tau = L * Real.sqrt 3)
    (hQ : (4 * C^2 / (c^2 * Real.sqrt 3)) * (N : ℝ)^3 * L^(5 - 2 * sigma) ≤ Q) :
    2 * M * C * (L^2 * (N : ℝ))^(3 / 2 : ℝ) ≤
      Real.sqrt (Q * tau) * mass := by
  set N' : ℝ := (N : ℝ) with hN'_def
  have hN'_pos : 0 < N' := by
    simpa [hN'_def] using show (0 : ℝ) < (N : ℝ) from by exact_mod_cast hN_pos
  have hsqrt3_pos : 0 < Real.sqrt 3 := by positivity

  -- Helper: product to sum
  have h_rpow_add : ∀ (a b : ℝ), Real.rpow L a * Real.rpow L b = Real.rpow L (a + b) := by
    intro a b
    exact (Real.rpow_add hL_pos a b).symm
  have h_rpow_addN : ∀ (a b : ℝ), Real.rpow N' a * Real.rpow N' b = Real.rpow N' (a + b) := by
    intro a b
    exact (Real.rpow_add hN'_pos a b).symm

  -- Conversions
  have hL2 : L^2 = Real.rpow L 2 := by
    have h : Real.rpow L 2 = L^2 := by simp
    exact h.symm
  have hL3 : L^3 = Real.rpow L 3 := by
    have h : Real.rpow L 3 = L^3 := by simp
    exact h.symm
  have hL1 : L = Real.rpow L 1 := by simp

  -- Abstract rpow values
  set A : ℝ := Real.rpow L (2 - sigma - outputLoss) with hA_def
  set B : ℝ := Real.rpow L (2 - outputLoss) with hB_def
  set D : ℝ := Real.rpow L (3 - sigma) with hD_def
  set E : ℝ := Real.rpow L (5 - sigma - outputLoss) with hE_def
  set Fval : ℝ := Real.rpow L (5 - 2 * sigma) with hF_def
  set H : ℝ := N'^(3 / 2 : ℝ) with hH_def
  set I : ℝ := N'^(5 / 2 : ℝ) with hI_def

  -- A * L^3 = E
  have h1 : A * L^3 = E := by
    calc
      A * L^3
        = A * Real.rpow L 3 := by exact congr_arg (fun x => A * x) hL3
      _ = Real.rpow L (2 - sigma - outputLoss) * Real.rpow L 3 := by
          exact congr_arg (fun x => x * Real.rpow L 3) (by simp only [hA_def])
      _ = Real.rpow L ((2 - sigma - outputLoss) + 3) := h_rpow_add (2 - sigma - outputLoss) 3
      _ = Real.rpow L (5 - sigma - outputLoss) := by ring_nf
      _ = E := by simp only [hE_def]

  -- D * B = E
  have h2 : D * B = E := by
    calc
      D * B
        = Real.rpow L (3 - sigma) * Real.rpow L (2 - outputLoss) := by
          simp only [hD_def, hB_def]
      _ = Real.rpow L ((3 - sigma) + (2 - outputLoss)) := h_rpow_add (3 - sigma) (2 - outputLoss)
      _ = Real.rpow L (5 - sigma - outputLoss) := by ring_nf
      _ = E := by simp only [hE_def]

  -- D^2 = Real.rpow L (6 - 2*sigma)
  have hD2 : D^2 = Real.rpow L (6 - 2 * sigma) := by
    calc
      D^2
        = D * D := by ring
      _ = Real.rpow L (3 - sigma) * Real.rpow L (3 - sigma) := by simp only [hD_def]
      _ = Real.rpow L ((3 - sigma) + (3 - sigma)) := h_rpow_add (3 - sigma) (3 - sigma)
      _ = Real.rpow L (6 - 2 * sigma) := by ring_nf

  -- Real.rpow L (6-2σ) * L = Real.rpow L (7-2σ)
  have h5 : Real.rpow L (6 - 2 * sigma) * L = Real.rpow L (7 - 2 * sigma) := by
    calc
      Real.rpow L (6 - 2 * sigma) * L
        = Real.rpow L (6 - 2 * sigma) * Real.rpow L 1 := by
          exact congr_arg (fun x => Real.rpow L (6 - 2 * sigma) * x) hL1
      _ = Real.rpow L ((6 - 2 * sigma) + 1) := h_rpow_add (6 - 2 * sigma) 1
      _ = Real.rpow L (7 - 2 * sigma) := by ring_nf

  -- Real.rpow L (7-2σ) = Fval * L^2
  have h6 : Real.rpow L (7 - 2 * sigma) = Fval * L^2 := by
    calc
      Real.rpow L (7 - 2 * sigma)
        = Real.rpow L ((5 - 2 * sigma) + 2) := by ring_nf
      _ = Real.rpow L (5 - 2 * sigma) * Real.rpow L 2 := (h_rpow_add (5 - 2 * sigma) 2).symm
      _ = Fval * Real.rpow L 2 := by simp only [hF_def]
      _ = Fval * L^2 := by exact congr_arg (fun x => Fval * x) hL2.symm

  -- D^2 * L * √3 = Fval * L^2 * √3
  have h3 : D^2 * L * Real.sqrt 3 = Fval * L^2 * Real.sqrt 3 := by
    calc
      D^2 * L * Real.sqrt 3
        = (D^2) * (L * Real.sqrt 3) := by ring
      _ = Real.rpow L (6 - 2 * sigma) * (L * Real.sqrt 3) := by rw [hD2]
      _ = (Real.rpow L (6 - 2 * sigma) * L) * Real.sqrt 3 := by ring
      _ = Real.rpow L (7 - 2 * sigma) * Real.sqrt 3 := by rw [h5]
      _ = (Fval * L^2) * Real.sqrt 3 := by rw [h6]
      _ = Fval * L^2 * Real.sqrt 3 := by ring

  -- H * N' = I
  have h7 : H * N' = I := by
    have hN1 : N' = Real.rpow N' 1 := by simp
    calc
      H * N'
        = N'^(3 / 2 : ℝ) * N' := by simp only [hH_def]
      _ = N'^(3 / 2 : ℝ) * Real.rpow N' 1 := by exact congr_arg (fun x => N'^(3 / 2 : ℝ) * x) hN1
      _ = Real.rpow N' ((3 / 2 : ℝ) + 1) := h_rpow_addN (3 / 2 : ℝ) 1
      _ = Real.rpow N' (5 / 2 : ℝ) := by ring_nf
      _ = N'^(5 / 2 : ℝ) := by simp
      _ = I := by simp only [hI_def]

  -- H^2 = N'^3
  have h8 : H^2 = N'^3 := by
    calc
      H^2
        = H * H := by ring
      _ = N'^(3 / 2 : ℝ) * N'^(3 / 2 : ℝ) := by simp only [hH_def]
      _ = Real.rpow N' ((3 / 2 : ℝ) + (3 / 2 : ℝ)) := h_rpow_addN (3 / 2 : ℝ) (3 / 2 : ℝ)
      _ = Real.rpow N' 3 := by ring_nf
      _ = N'^3 := by simp

  -- (L^2 * N')^(3/2) = L^3 * H
  have h9 : (L^2 * N')^(3 / 2 : ℝ) = L^3 * H := by
    have h10 : 0 ≤ L^2 := by positivity
    have h11 : (L^2 * N')^(3 / 2 : ℝ) = (L^2)^(3 / 2 : ℝ) * N'^(3 / 2 : ℝ) := by
      exact Real.mul_rpow h10 hN'_pos.le
    have h12 : (L^2)^(3 / 2 : ℝ) = L^3 := by
      calc
        (L^2)^(3 / 2 : ℝ)
          = (Real.rpow L 2)^(3 / 2 : ℝ) := by exact congr_arg (fun x => x^(3 / 2 : ℝ)) hL2
        _ = Real.rpow L (2 * (3 / 2 : ℝ)) := by
          exact (Real.rpow_mul hL_pos.le 2 (3 / 2 : ℝ)).symm
        _ = Real.rpow L 3 := by norm_num
        _ = L^3 := by exact hL3.symm
    calc
      (L^2 * N')^(3 / 2 : ℝ)
        = (L^2)^(3 / 2 : ℝ) * N'^(3 / 2 : ℝ) := h11
      _ = L^3 * N'^(3 / 2 : ℝ) := by rw [h12]
      _ = L^3 * H := by simp only [hH_def]

  -- Real.rpow L (-outputLoss) * L^2 = B
  have h13 : Real.rpow L (-outputLoss) * L^2 = B := by
    calc
      Real.rpow L (-outputLoss) * L^2
        = Real.rpow L (-outputLoss) * Real.rpow L 2 := by
          exact congr_arg (fun x => Real.rpow L (-outputLoss) * x) hL2
      _ = Real.rpow L ((-outputLoss) + 2) := h_rpow_add (-outputLoss) 2
      _ = Real.rpow L (2 - outputLoss) := by ring_nf
      _ = B := by simp only [hB_def]

  -- mass ≥ c * N' * B
  have h_mass_lower : c * N' * B ≤ mass := by
    have h31 : Real.rpow L (-outputLoss) * (c * N' * L^2) = c * N' * B := by
      calc
        Real.rpow L (-outputLoss) * (c * N' * L^2)
          = c * N' * (Real.rpow L (-outputLoss) * L^2) := by ring
        _ = c * N' * B := by rw [h13]
    have h_rpow_nonneg : 0 ≤ Real.rpow L (-outputLoss) := Real.rpow_nonneg hL_pos.le (-outputLoss)
    calc c * N' * B
      = Real.rpow L (-outputLoss) * (c * N' * L^2) := h31.symm
    _ ≤ Real.rpow L (-outputLoss) * F_mass := by exact mul_le_mul_of_nonneg_left hF_mass h_rpow_nonneg
    _ ≤ mass := hmass

  -- M ≤ A * N'
  have hM' : M ≤ A * N' := by
    simpa [hA_def] using hM

  -- LHS ≤ 2 * C * I * E
  have h_lhs : 2 * M * C * (L^2 * N')^(3 / 2 : ℝ) ≤ 2 * C * I * E := by
    rw [h9]
    have h4 : 2 * M * C * (L^3 * H) ≤ 2 * C * I * E := by
      calc
        2 * M * C * (L^3 * H)
          ≤ 2 * (A * N') * C * (L^3 * H) := by gcongr
        _ = 2 * C * (H * N') * (A * L^3) := by ring
        _ = 2 * C * I * E := by rw [h7, h1] <;> ring
    exact h4

  -- X = (2C/c) * H * D
  set X : ℝ := (2 * C / c) * H * D with hX_def
  have hH_pos : 0 < H := by
    simp only [hH_def]
    exact Real.rpow_pos_of_pos hN'_pos (3 / 2 : ℝ)
  have hD_pos : 0 < D := by
    simp only [hD_def]
    exact Real.rpow_pos_of_pos hL_pos (3 - sigma)
  have hX_nonneg : 0 ≤ X := by positivity

  -- D^2 = Fval * L
  have hD2_FvalL : D^2 = Fval * L := by
    calc
      D^2 = Real.rpow L (6 - 2 * sigma) := hD2
      _ = Real.rpow L ((5 - 2 * sigma) + 1) := by ring_nf
      _ = Real.rpow L (5 - 2 * sigma) * Real.rpow L 1 := (h_rpow_add (5 - 2 * sigma) 1).symm
      _ = Fval * L := by
        have h : Real.rpow L (5 - 2 * sigma) * Real.rpow L 1 = Fval * L := by
          rw [hF_def, hL1.symm] <;> ring
        exact h

  -- X^2 = threshold * (L*√3)
  have hX2 : X^2 = (4 * C^2 / (c^2 * Real.sqrt 3)) * N'^3 * Fval * (L * Real.sqrt 3) := by
    calc
      X^2
        = X * X := by ring
      _ = ((2 * C / c) * H * D) * ((2 * C / c) * H * D) := by simp only [hX_def]
      _ = (2 * C / c)^2 * (H * H) * (D * D) := by ring
      _ = (4 * C^2 / c^2) * H^2 * D^2 := by ring
      _ = (4 * C^2 / c^2) * N'^3 * D^2 := by rw [h8] <;> ring
      _ = (4 * C^2 / c^2) * N'^3 * (Fval * L) := by rw [hD2_FvalL] <;> ring
      _ = (4 * C^2 / (c^2 * Real.sqrt 3)) * N'^3 * Fval * (L * Real.sqrt 3) := by
          have hsqrt3_pos' : 0 < Real.sqrt 3 := by positivity
          field_simp [hc_pos.ne', hsqrt3_pos'.ne'] <;> ring

  -- X^2 ≤ Q * tau
  have hX2_le : X^2 ≤ Q * tau := by
    rw [htau_eq, hX2]
    have h12 : (4 * C^2 / (c^2 * Real.sqrt 3)) * N'^3 * Fval ≤ Q := by
      simpa [hF_def] using hQ
    have h13 : 0 ≤ L * Real.sqrt 3 := by positivity
    have h14 : ((4 * C^2 / (c^2 * Real.sqrt 3)) * N'^3 * Fval) * (L * Real.sqrt 3) ≤ Q * (L * Real.sqrt 3) := by
      exact mul_le_mul_of_nonneg_right h12 h13
    simpa [htau_eq] using h14

  -- √(Q*tau) ≥ X
  have h_sqrt : X ≤ Real.sqrt (Q * tau) := by
    have h14 : 0 ≤ Q * tau := by positivity
    exact Real.le_sqrt_of_sq_le hX2_le

  -- c * X * N' * B = 2 * C * I * E
  have h_combine : c * X * N' * B = 2 * C * I * E := by
    have h15 : c * (2 * C / c) = 2 * C := by
      field_simp [hc_pos.ne'] <;> ring
    calc
      c * X * N' * B
        = c * ((2 * C / c) * H * D) * N' * B := by rw [hX_def]
      _ = (c * (2 * C / c)) * (H * N') * (D * B) := by ring
      _ = 2 * C * I * E := by rw [h15, h7, h2] <;> ring

  have hB_pos : 0 < B := by
    simp only [hB_def]
    exact Real.rpow_pos_of_pos hL_pos (2 - outputLoss)
  have h_cN'B_pos : 0 < c * N' * B := by positivity

  calc
    2 * M * C * (L^2 * N')^(3 / 2 : ℝ)
      ≤ 2 * C * I * E := h_lhs
    _ = c * X * N' * B := h_combine.symm
    _ ≤ c * Real.sqrt (Q * tau) * N' * B := by
      have h_factor : c * X * N' * B = (c * N' * B) * X := by ring
      have h_factor2 : c * Real.sqrt (Q * tau) * N' * B = (c * N' * B) * Real.sqrt (Q * tau) := by ring
      rw [h_factor, h_factor2]
      exact mul_le_mul_of_nonneg_left h_sqrt h_cN'B_pos.le
    _ = Real.sqrt (Q * tau) * (c * N' * B) := by ring
    _ ≤ Real.sqrt (Q * tau) * mass := by gcongr

/-- ENNReal bridge: lifts the real absorption inequality to the ENNReal
condition required by `paper_broad_mass_budget_main`. -/
lemma absorption_ennreal_bridge
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (L sigma outputLoss : ℝ)
    (N : ℕ)
    (C_enn : ENNReal)
    (hC_ne_top : C_enn ≠ ⊤)
    (M mass F_mass tau : ℝ)
    (Q : ℕ)
    (hL_pos : 0 < L)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (houtputLoss_pos : 0 < outputLoss)
    (hN_pos : 0 < N)
    (hM_nonneg : 0 ≤ M)
    (hmass_nonneg : 0 ≤ mass)
    (htau_pos : 0 < tau)
    (c : ℝ)
    (hc_pos : 0 < c)
    (hM : M ≤ L ^ (2 - sigma - outputLoss) * (N : ℝ))
    (hmass : L ^ (-outputLoss) * F_mass ≤ mass)
    (hF_mass : c * (N : ℝ) * L ^ 2 ≤ F_mass)
    (htau_eq : tau = L * Real.sqrt 3)
    (hQ : (4 * (C_enn.toReal)^2 / (c^2 * Real.sqrt 3)) * (N : ℝ)^3 * L^(5 - 2 * sigma) ≤ (Q : ℝ))
    (hS_mass : ENNReal.ofReal mass ≤ S.mass)
    (hF_enncard : F.enncard = (N : ENNReal))
    (hdelta_eq : delta = L) :
    (2 : ENNReal) * ENNReal.ofReal M * C_enn *
      (ENNReal.ofReal (delta ^ 2) * F.enncard) ^ (3 / 2 : ℝ) ≤
    (((Q : ENNReal) * ENNReal.ofReal tau) ^ (1 / 2 : ℝ)) * S.mass := by
  by_cases hC_zero : C_enn = 0
  · -- C_enn = 0: LHS is 0, inequality trivial
    rw [hC_zero]
    <;> simp
  · -- C_enn ≠ 0 (and ≠ ⊤), so C_real > 0
    set C_real : ℝ := C_enn.toReal with hC_real_def
    have hC_real_nonneg : 0 ≤ C_real := by
      exact ENNReal.toReal_nonneg
    have hC_real_pos : 0 < C_real := by
      have h : C_enn ≠ 0 := hC_zero
      have h' : C_real ≠ 0 := by
        intro h_eq
        have h_eq2 : C_enn = 0 ∨ C_enn = ⊤ := by
          simpa [hC_real_def, ENNReal.toReal_eq_zero_iff] using h_eq
        rcases h_eq2 with (h0 | htop)
        · exact h h0
        · exact hC_ne_top htop
      have h_nonneg : 0 ≤ C_real := hC_real_nonneg
      exact lt_of_le_of_ne h_nonneg h'.symm
    have hQ_pos : 0 < Q := by
      by_contra h
      have h' : Q = 0 := by omega
      rw [h'] at hQ
      have h_pos : 0 < (4 * (C_enn.toReal)^2 / (c^2 * Real.sqrt 3)) * (N : ℝ)^3 * L^(5 - 2 * sigma) := by positivity
      linarith
    have h_main_real : 2 * M * C_real * (L^2 * (N : ℝ))^(3 / 2 : ℝ) ≤
        Real.sqrt ((Q : ℝ) * tau) * mass :=
      absorption_arithmetic_core L sigma outputLoss N C_real M mass F_mass (Q : ℝ) tau
        hL_pos hsigma_pos hsigma_lt_one houtputLoss_pos hN_pos hC_real_pos hM_nonneg
        hmass_nonneg (by positivity) htau_pos c hc_pos hM hmass hF_mass htau_eq hQ
    have h1 : (2 : ENNReal) * ENNReal.ofReal M * C_enn *
          (ENNReal.ofReal (delta ^ 2) * F.enncard) ^ (3 / 2 : ℝ) =
        ENNReal.ofReal (2 * M * C_real * (L^2 * (N : ℝ))^(3 / 2 : ℝ)) := by
      have hC_eq : C_enn = ENNReal.ofReal C_real := by
        rw [ENNReal.ofReal_toReal hC_ne_top] <;> rfl
      rw [hC_eq, hF_enncard, hdelta_eq]
      have h2 : ENNReal.ofReal (L ^ 2) * (N : ENNReal) = ENNReal.ofReal (L ^ 2 * (N : ℝ)) := by
        rw [ENNReal.ofReal_mul (by positivity)] <;> simp
      rw [h2]
      have h3 : (ENNReal.ofReal (L ^ 2 * (N : ℝ))) ^ (3 / 2 : ℝ) =
          ENNReal.ofReal ((L ^ 2 * (N : ℝ)) ^ (3 / 2 : ℝ)) := by
        exact ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
      rw [h3]
      have h_pos1 : 0 ≤ M := hM_nonneg
      have h_pos2 : 0 ≤ C_real := hC_real_nonneg
      have h_combine : (2 : ENNReal) * ENNReal.ofReal M * ENNReal.ofReal C_real *
            ENNReal.ofReal ((L ^ 2 * (N : ℝ)) ^ (3 / 2 : ℝ)) =
          ENNReal.ofReal (2 * M * C_real * ((L ^ 2 * (N : ℝ)) ^ (3 / 2 : ℝ))) := by
        have h2 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by simp
        rw [h2]
        have h3 : ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal M = ENNReal.ofReal (2 * M) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
        rw [h3]
        have h4 : ENNReal.ofReal (2 * M) * ENNReal.ofReal C_real = ENNReal.ofReal (2 * M * C_real) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
        rw [h4]
        have h5 : ENNReal.ofReal (2 * M * C_real) * ENNReal.ofReal ((L ^ 2 * (N : ℝ)) ^ (3 / 2 : ℝ)) =
            ENNReal.ofReal (2 * M * C_real * ((L ^ 2 * (N : ℝ)) ^ (3 / 2 : ℝ))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
        rw [h5] <;> rfl
      exact h_combine
    have h4 : (((Q : ENNReal) * ENNReal.ofReal tau) ^ (1 / 2 : ℝ)) * S.mass ≥
        ENNReal.ofReal (Real.sqrt ((Q : ℝ) * tau) * mass) := by
      have h5 : (Q : ENNReal) * ENNReal.ofReal tau = ENNReal.ofReal ((Q : ℝ) * tau) := by
        rw [ENNReal.ofReal_mul (by positivity)] <;> simp
      rw [h5]
      have h6 : (ENNReal.ofReal ((Q : ℝ) * tau)) ^ (1 / 2 : ℝ) =
          ENNReal.ofReal (Real.sqrt ((Q : ℝ) * tau)) := by
        have h7 : (ENNReal.ofReal ((Q : ℝ) * tau)) ^ (1 / 2 : ℝ) =
            ENNReal.ofReal (((Q : ℝ) * tau) ^ (1 / 2 : ℝ)) :=
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
        rw [h7]
        have h8 : ((Q : ℝ) * tau) ^ (1 / 2 : ℝ) = Real.sqrt ((Q : ℝ) * tau) := by
          rw [Real.sqrt_eq_rpow] <;> rfl
        rw [h8]
      rw [h6]
      have h7 : ENNReal.ofReal (Real.sqrt ((Q : ℝ) * tau)) * S.mass ≥
          ENNReal.ofReal (Real.sqrt ((Q : ℝ) * tau)) * ENNReal.ofReal mass := by gcongr
      have h8 : ENNReal.ofReal (Real.sqrt ((Q : ℝ) * tau)) * ENNReal.ofReal mass =
          ENNReal.ofReal (Real.sqrt ((Q : ℝ) * tau) * mass) := by
        rw [ENNReal.ofReal_mul (by positivity)] <;> rfl
      rw [h8] at h7
      exact h7
    rw [h1]
    exact le_trans (ENNReal.ofReal_le_ofReal h_main_real) h4

end Kakeya.Assouad

end
