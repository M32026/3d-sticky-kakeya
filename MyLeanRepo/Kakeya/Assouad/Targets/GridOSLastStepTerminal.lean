import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSFiniteStepScheduleStatements

/-! WZ2 Section 7: prove the last scheduled one-scale output is terminal. -/

namespace Kakeya.Assouad

theorem grid_os_last_step_terminal :
    GridOSLastStepTerminalStatement := by
  intro delta epsilon currentScale rho hdelta_pos hdelta_lt_one
    hepsilon_pos hepsilon_lt_one steps h_exp h_scale h_rho
  set a : ℝ := 1 - epsilon ^ 2 with ha_def
  have ha_pos : 0 < a := by nlinarith
  have ha_le_one : a ≤ 1 := by nlinarith
  have ha_nonneg : 0 ≤ a := by linarith
  have h_pow_succ : a ^ (steps + 1) ≤ a ^ steps := by
    calc
      a ^ (steps + 1) = a ^ steps * a := by ring
      _ ≤ a ^ steps * 1 := by gcongr
      _ = a ^ steps := by ring
  have h_exp_succ : a ^ (steps + 1) ≤ epsilon ^ 2 := by
    calc
      a ^ (steps + 1) ≤ a ^ steps := h_pow_succ
      _ ≤ epsilon ^ 2 := h_exp
  have h_delta_pos' : 0 < delta := hdelta_pos
  have h_delta_le_one : delta ≤ 1 := by linarith
  have h6 : Real.rpow delta (epsilon ^ 2) ≤ Real.rpow delta (a ^ (steps + 1)) := by
    apply Real.rpow_le_rpow_of_exponent_ge h_delta_pos' h_delta_le_one
    exact h_exp_succ
  have h_rpow_mul : Real.rpow delta (a ^ (steps + 1)) =
      Real.rpow (Real.rpow delta (a ^ steps)) a := by
    have h_mul : (a ^ (steps + 1) : ℝ) = (a ^ steps : ℝ) * a := by ring
    rw [h_mul]
    exact Real.rpow_mul (by linarith) (a ^ steps) a
  have h8 : 0 ≤ Real.rpow delta (a ^ steps) := by
    exact Real.rpow_nonneg (by linarith) _
  have h9 : 0 ≤ currentScale := by
    have h_pos : 0 < Real.rpow delta (a ^ steps) := Real.rpow_pos_of_pos hdelta_pos _
    linarith [h_scale]
  have h10 : Real.rpow (Real.rpow delta (a ^ steps)) a ≤
      Real.rpow currentScale a := by
    apply Real.rpow_le_rpow h8 h_scale ha_nonneg
  have h11 : Real.rpow delta (epsilon ^ 2) ≤ Real.rpow currentScale a := by
    calc
      Real.rpow delta (epsilon ^ 2)
        ≤ Real.rpow delta (a ^ (steps + 1)) := h6
      _ = Real.rpow (Real.rpow delta (a ^ steps)) a := h_rpow_mul
      _ ≤ Real.rpow currentScale a := h10
  have h12 : Real.rpow delta (epsilon ^ 2) ≤ rho := by
    have h13 : Real.rpow currentScale a < rho := h_rho
    exact le_trans h11 (le_of_lt h13)
  exact h12

end Kakeya.Assouad
