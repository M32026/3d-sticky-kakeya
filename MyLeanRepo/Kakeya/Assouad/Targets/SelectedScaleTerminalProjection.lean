import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SelectedScaleStatements

/-!
WZ2 Section 7: close the terminal branch once the iterated scale reaches the
original `delta^(epsilon²)` threshold.
-/

namespace Kakeya.Assouad

theorem selected_scale_terminal_projection :
    SelectedScaleTerminalProjectionStatement := by
  intro delta rho epsilon hdelta hdelta_lt_one hrho hepsilon
    hepsilon_lt_one hrho_ge X hX V hV
  rcases hX with ⟨x, hx⟩
  have hdelta_nonneg : 0 ≤ delta := by linarith
  have hrho_nonneg : 0 ≤ rho := by linarith
  have h_two_minus_epsilon_nonneg : 0 ≤ 2 - epsilon := by linarith
  have h1 : Metric.ball x rho ⊆ Metric.closedBall x rho :=
    Metric.ball_subset_closedBall
  have h2 : Metric.closedBall x rho ⊆ Metric.cthickening rho X :=
    Metric.closedBall_subset_cthickening hx rho
  have h_ball_subset :
      Metric.ball x rho ⊆ Metric.cthickening rho X := by
    intro y hy
    exact h2 (h1 hy)
  have h_vol_mono :
      MeasureTheory.volume (Metric.ball x rho) ≤
        MeasureTheory.volume (Metric.cthickening rho X) :=
    MeasureTheory.measure_mono h_ball_subset
  have h_vol_ball :
      MeasureTheory.volume (Metric.ball x rho) =
        ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi :=
    EuclideanSpace.volume_ball_fin_two x rho
  have h_rho_mul : rho * rho = rho ^ 2 := by ring
  have h_ofReal_rho_sq :
      ENNReal.ofReal rho ^ 2 = ENNReal.ofReal (rho ^ 2) := by
    have h :
        ENNReal.ofReal rho ^ 2 =
          ENNReal.ofReal rho * ENNReal.ofReal rho := by
      ring
    rw [h]
    have h2 :
        ENNReal.ofReal rho * ENNReal.ofReal rho =
          ENNReal.ofReal (rho * rho) :=
      (ENNReal.ofReal_mul hrho_nonneg).symm
    rw [h2, h_rho_mul]
  have hpi : (1 : ℝ) ≤ Real.pi := by
    have h : (3 : ℝ) < Real.pi := Real.pi_gt_three
    linarith
  have h_pi_ge_one : (1 : ENNReal) ≤ ENNReal.ofReal Real.pi := by
    have h' : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal Real.pi :=
      ENNReal.ofReal_le_ofReal hpi
    simpa using h'
  have h_vol_ball_lower :
      ENNReal.ofReal (rho ^ 2) ≤
        MeasureTheory.volume (Metric.ball x rho) := by
    rw [h_vol_ball, h_ofReal_rho_sq]
    calc
      ENNReal.ofReal (rho ^ 2) =
          ENNReal.ofReal (rho ^ 2) * 1 := by simp
      _ ≤ ENNReal.ofReal (rho ^ 2) *
          ENNReal.ofReal Real.pi := by gcongr
  have h_vol_lower :
      ENNReal.ofReal (rho ^ 2) ≤
        MeasureTheory.volume (Metric.cthickening rho X) :=
    le_trans h_vol_ball_lower h_vol_mono
  have h_a_in :
      Real.rpow delta (epsilon ^ 2) ∈ Set.Ici (0 : ℝ) := by
    simp [Real.rpow_nonneg hdelta_nonneg]
  have h_b_in : rho ∈ Set.Ici (0 : ℝ) := by
    simp [hrho_nonneg]
  have h_rpow_mono :
      Real.rpow (Real.rpow delta (epsilon ^ 2)) (2 - epsilon) ≤
        Real.rpow rho (2 - epsilon) :=
    Real.monotoneOn_rpow_Ici_of_exponent_nonneg
      h_two_minus_epsilon_nonneg h_a_in h_b_in hrho_ge
  have h_rpow_mul_eq :
      Real.rpow (Real.rpow delta (epsilon ^ 2)) (2 - epsilon) =
        Real.rpow delta (epsilon ^ 2 * (2 - epsilon)) :=
    Eq.symm
      (Real.rpow_mul hdelta_nonneg (epsilon ^ 2) (2 - epsilon))
  have h9 :
      Real.rpow delta (epsilon ^ 2 * (2 - epsilon)) ≤
        Real.rpow rho (2 - epsilon) := by
    rw [← h_rpow_mul_eq]
    exact h_rpow_mono
  have h_div :
      Real.rpow (delta / rho) epsilon =
        Real.rpow delta epsilon / Real.rpow rho epsilon :=
    Real.div_rpow hdelta_nonneg hrho_nonneg epsilon
  have h_rpow_sub :
      Real.rpow rho (2 : ℝ) / Real.rpow rho epsilon =
        Real.rpow rho (2 - epsilon) := by
    have h :
        Real.rpow rho ((2 : ℝ) - epsilon) =
          Real.rpow rho (2 : ℝ) / Real.rpow rho epsilon :=
      Real.rpow_sub hrho (2 : ℝ) epsilon
    exact h.symm
  have h_rho2_eq : (rho ^ 2 : ℝ) = Real.rpow rho (2 : ℝ) := by
    simp
  have h10 :
      Real.rpow (delta / rho) epsilon * rho ^ 2 =
        Real.rpow delta epsilon * Real.rpow rho (2 - epsilon) := by
    rw [h_div, h_rho2_eq]
    have h :
        (Real.rpow delta epsilon / Real.rpow rho epsilon) *
              Real.rpow rho (2 : ℝ) =
          Real.rpow delta epsilon *
            (Real.rpow rho (2 : ℝ) / Real.rpow rho epsilon) := by
      ring
    rw [h, h_rpow_sub] <;> ring
  have h_rpow_add :
      Real.rpow delta epsilon *
            Real.rpow delta (epsilon ^ 2 * (2 - epsilon)) =
        Real.rpow delta
          (epsilon + epsilon ^ 2 * (2 - epsilon)) := by
    have h :
        Real.rpow delta
              (epsilon + epsilon ^ 2 * (2 - epsilon)) =
          Real.rpow delta epsilon *
            Real.rpow delta (epsilon ^ 2 * (2 - epsilon)) :=
      Real.rpow_add
        hdelta epsilon (epsilon ^ 2 * (2 - epsilon))
    exact h.symm
  have h_delta_rpow_nonneg : 0 ≤ Real.rpow delta epsilon :=
    Real.rpow_nonneg hdelta_nonneg _
  have h11 :
      Real.rpow delta epsilon * Real.rpow rho (2 - epsilon) ≥
        Real.rpow delta epsilon *
          Real.rpow delta (epsilon ^ 2 * (2 - epsilon)) :=
    mul_le_mul_of_nonneg_left h9 h_delta_rpow_nonneg
  have h12 :
      Real.rpow (delta / rho) epsilon * rho ^ 2 ≥
        Real.rpow delta
          (epsilon + epsilon ^ 2 * (2 - epsilon)) := by
    calc
      Real.rpow (delta / rho) epsilon * rho ^ 2 =
          Real.rpow delta epsilon *
            Real.rpow rho (2 - epsilon) := h10
      _ ≥ Real.rpow delta epsilon *
          Real.rpow delta (epsilon ^ 2 * (2 - epsilon)) := h11
      _ = Real.rpow delta
          (epsilon + epsilon ^ 2 * (2 - epsilon)) := h_rpow_add
  have h_rpow_nonneg' :
      0 ≤ Real.rpow (delta / rho) epsilon :=
    Real.rpow_nonneg (by positivity) _
  have h13 :
      ENNReal.ofReal (Real.rpow (delta / rho) epsilon) *
            ENNReal.ofReal (rho ^ 2) =
        ENNReal.ofReal
          (Real.rpow (delta / rho) epsilon * rho ^ 2) :=
    (ENNReal.ofReal_mul h_rpow_nonneg').symm
  have h15 :
      Kakeya.realRpowENN delta
            (epsilon + epsilon ^ 2 * (2 - epsilon)) ≤
        Kakeya.realRpowENN (delta / rho) epsilon *
          ENNReal.ofReal (rho ^ 2) := by
    simp only [Kakeya.realRpowENN]
    rw [h13]
    exact ENNReal.ofReal_le_ofReal h12
  have h16 :
      Kakeya.realRpowENN (delta / rho) epsilon *
            ENNReal.ofReal (rho ^ 2) ≤
        Kakeya.realRpowENN (delta / rho) epsilon *
          MeasureTheory.volume (Metric.cthickening rho X) :=
    mul_le_mul_right h_vol_lower
      (Kakeya.realRpowENN (delta / rho) epsilon)
  exact le_trans h15 (le_trans h16 hV)

end Kakeya.Assouad
