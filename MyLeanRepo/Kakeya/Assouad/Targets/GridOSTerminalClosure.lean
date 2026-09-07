import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSTerminalClosureStatement

/-!
WZ2 Proposition 7.1: close a finite corrected grid OS run after its final
selected radius reaches the terminal threshold.
-/

namespace Kakeya.Assouad

theorem grid_os_terminal_closure :
    GridOSTerminalClosureStatement := by
  intro h_telescoping h_terminal delta epsilon hdelta_pos hdelta_lt_one
    hepsilon_pos hepsilon_lt_one steps scale projectedVolume h_scale0
    h_scale_pos h_transitions rho hrho_pos h_rho_threshold X hX_nonempty
    h_volume_bound

  -- Step 1: Apply finite telescoping to the transition inequalities
  have h_telescope : Kakeya.realRpowENN (scale 0 / scale steps) epsilon *
        projectedVolume steps ≤
      (6889 : ENNReal) ^ steps * projectedVolume 0 :=
    h_telescoping epsilon steps scale projectedVolume h_scale_pos h_transitions

  -- Rewrite scale 0 as delta
  rw [h_scale0] at h_telescope

  -- Step 2: Positivity of intermediate scale
  have h_scale_steps_pos : 0 < scale steps := h_scale_pos steps (by linarith)

  -- Step 3: Multiplicativity of realRpowENN over positive bases
  have h_pos1 : 0 ≤ delta / scale steps := by positivity
  have h_pos2 : 0 ≤ scale steps / rho := by positivity
  have h_eq_ratio : delta / rho = (delta / scale steps) * (scale steps / rho) := by
    field_simp [h_scale_steps_pos.ne', hrho_pos.ne']
  have h_mul_real : Real.rpow (delta / rho) epsilon =
      Real.rpow (delta / scale steps) epsilon * Real.rpow (scale steps / rho) epsilon := by
    rw [h_eq_ratio]
    exact Real.mul_rpow h_pos1 h_pos2
  have h_rpow1_nonneg : 0 ≤ Real.rpow (delta / scale steps) epsilon :=
    Real.rpow_nonneg h_pos1 _
  have h_rpow2_nonneg : 0 ≤ Real.rpow (scale steps / rho) epsilon :=
    Real.rpow_nonneg h_pos2 _
  have h_mul_enn : Kakeya.realRpowENN (delta / rho) epsilon =
      Kakeya.realRpowENN (delta / scale steps) epsilon *
      Kakeya.realRpowENN (scale steps / rho) epsilon := by
    simp only [Kakeya.realRpowENN]
    rw [h_mul_real]
    rw [ENNReal.ofReal_mul h_rpow1_nonneg]

  -- Step 4: Combine multiplicativity with the terminal volume bound
  have h2 : Kakeya.realRpowENN (delta / rho) epsilon *
        MeasureTheory.volume (Metric.cthickening rho X) ≤
      Kakeya.realRpowENN (delta / scale steps) epsilon * projectedVolume steps := by
    rw [h_mul_enn]
    have h3 : Kakeya.realRpowENN (scale steps / rho) epsilon *
          MeasureTheory.volume (Metric.cthickening rho X) ≤
        projectedVolume steps := h_volume_bound
    calc
      (Kakeya.realRpowENN (delta / scale steps) epsilon *
        Kakeya.realRpowENN (scale steps / rho) epsilon) *
        MeasureTheory.volume (Metric.cthickening rho X)
        = Kakeya.realRpowENN (delta / scale steps) epsilon *
          (Kakeya.realRpowENN (scale steps / rho) epsilon *
            MeasureTheory.volume (Metric.cthickening rho X)) := by ring
      _ ≤ Kakeya.realRpowENN (delta / scale steps) epsilon * projectedVolume steps := by
          gcongr

  -- Step 5: Transitivity with the telescoping bound
  have h4 : Kakeya.realRpowENN (delta / rho) epsilon *
        MeasureTheory.volume (Metric.cthickening rho X) ≤
      (6889 : ENNReal) ^ steps * projectedVolume 0 :=
    le_trans h2 h_telescope

  -- Step 6: Apply terminal projection theorem
  exact h_terminal (delta := delta) (rho := rho) (epsilon := epsilon)
    hdelta_pos hdelta_lt_one hrho_pos hepsilon_pos hepsilon_lt_one
    h_rho_threshold X hX_nonempty
    ((6889 : ENNReal) ^ steps * projectedVolume 0) h4

end Kakeya.Assouad
