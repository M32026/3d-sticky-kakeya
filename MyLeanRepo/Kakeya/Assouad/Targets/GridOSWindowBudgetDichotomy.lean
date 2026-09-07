import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSWindowBudgetDichotomyStatement

/-!
WZ2 Proposition 7.1: prove the corrected terminal-or-two-sided-window-budget
dichotomy used by every grid OS transition.
-/

namespace Kakeya.Assouad

theorem grid_os_window_budget_dichotomy :
    GridOSWindowBudgetDichotomyStatement := by
  intro epsilon eta h_eps_pos h_eps_lt_one h_eta_pos h_eta_lt
  set delta : ℝ := epsilon^2 - 4 * eta with hdelta_def
  have hdelta_pos : 0 < delta := by linarith
  set scale₀ : ℝ := (1 / 320000 : ℝ) ^ (1 / delta) with hscale₀_def
  have hscale₀_pos : 0 < scale₀ := by
    apply Real.rpow_pos_of_pos
    positivity
  have hscale₀_le_one : scale₀ ≤ 1 := by
    have h1 : (1 / 320000 : ℝ) < 1 := by norm_num
    have h2 : 0 < 1 / delta := by positivity
    have h3 : ((1 / 320000 : ℝ) ^ (1 / delta)) < 1 :=
      Real.rpow_lt_one (by positivity) h1 h2
    exact h3.le
  refine' ⟨scale₀, hscale₀_pos, hscale₀_le_one, _⟩
  intro scale hscale_pos hscale_le rho hrho_nonneg
  by_cases h : Real.rpow scale (epsilon^2) ≤ rho
  · exact Or.inl h
  · -- Case rho < Real.rpow scale (epsilon^2)
    have h' : rho < Real.rpow scale (epsilon^2) := by linarith
    have h1 : Real.rpow scale delta ≤ Real.rpow scale₀ delta :=
      Real.rpow_le_rpow (by linarith) hscale_le (by linarith)
    have h2 : Real.rpow scale₀ delta = 1 / 320000 := by
      rw [hscale₀_def]
      have h_pos : (0 : ℝ) ≤ 1 / 320000 := by positivity
      have h_mul : Real.rpow (1 / 320000 : ℝ) ((1 / delta) * delta) =
          Real.rpow ((1 / 320000 : ℝ) ^ (1 / delta)) delta :=
        Real.rpow_mul h_pos (1 / delta) delta
      rw [←h_mul]
      have h3 : (1 / delta) * delta = 1 := by
        field_simp [hdelta_pos.ne'] <;> ring
      rw [h3]
      simp
    have h3 : Real.rpow scale delta ≤ 1 / 320000 := by
      rw [h2] at h1
      exact h1
    have h4 : epsilon^2 = 4 * eta + delta := by linarith
    have h5 : Real.rpow scale (epsilon^2) =
        Real.rpow scale (4 * eta) * Real.rpow scale delta := by
      rw [h4]
      exact Real.rpow_add hscale_pos (4 * eta) delta
    have h6 : 320000 * Real.rpow scale (epsilon^2) ≤ Real.rpow scale (4 * eta) := by
      rw [h5]
      have hpos1 : 0 < Real.rpow scale (4 * eta) := Real.rpow_pos_of_pos hscale_pos _
      calc
        320000 * (Real.rpow scale (4 * eta) * Real.rpow scale delta)
          = Real.rpow scale (4 * eta) * (320000 * Real.rpow scale delta) := by ring
        _ ≤ Real.rpow scale (4 * eta) * 1 := by gcongr <;> linarith
        _ = Real.rpow scale (4 * eta) := by ring
    have h7 : 400 * Real.rpow scale (epsilon^2) ≤
        (1 / 800 : ℝ) * Real.rpow scale (4 * eta) := by
      calc
        400 * Real.rpow scale (epsilon^2)
          = (1 / 800 : ℝ) * (320000 * Real.rpow scale (epsilon^2)) := by ring
        _ ≤ (1 / 800 : ℝ) * Real.rpow scale (4 * eta) := by gcongr
    have h81 : 400 * rho < 400 * Real.rpow scale (epsilon^2) := by gcongr
    have h8 : 400 * rho ≤ (1 / 800 : ℝ) * Real.rpow scale (4 * eta) :=
      h81.le.trans h7
    have h9 : ENNReal.ofReal (400 * rho) ≤
        ENNReal.ofReal ((1 / 800 : ℝ) * Real.rpow scale (4 * eta)) :=
      ENNReal.ofReal_le_ofReal h8
    have h10 : ENNReal.ofReal ((1 / 800 : ℝ) * Real.rpow scale (4 * eta)) =
        ENNReal.ofReal (1 / 800 : ℝ) * ENNReal.ofReal (Real.rpow scale (4 * eta)) := by
      rw [ENNReal.ofReal_mul] <;> positivity
    have h11 : Kakeya.realRpowENN scale (4 * eta) =
        ENNReal.ofReal (Real.rpow scale (4 * eta)) := by
      rfl
    have h12 : ENNReal.ofReal (400 * rho) ≤
        ENNReal.ofReal (1 / 800 : ℝ) * Kakeya.realRpowENN scale (4 * eta) := by
      rw [h11]
      rw [←h10]
      exact h9
    exact Or.inr h12

end Kakeya.Assouad
