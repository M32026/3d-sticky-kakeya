import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientCardinalityRpowLinearizationInputs

/-!
# Linearize the ambient cardinality power
-/

namespace Kakeya.Cinematic

theorem ambient_cardinality_rpow_linearization :
    AmbientCardinalityRpowLinearizationStatement := by
  intro ambientCard prefactor cardUpper coefficient logTail
    hpref hcardUpper hle hcoeff hlog
  set x : ℝ := prefactor * (ambientCard : ℝ) with hx
  have hx_nonneg : 0 ≤ x := by positivity
  by_cases h_x0 : x = 0
  · have h_lhs :
        coefficient * Real.rpow x (3 / 2 : ℝ) * logTail = 0 := by
      rw [h_x0]
      simp
    rw [h_lhs]
    positivity
  · have hx_pos : 0 < x := by
      exact lt_of_le_of_ne hx_nonneg (Ne.symm h_x0)
    have h_rpow :
        Real.rpow x (3 / 2 : ℝ) = x * Real.sqrt x := by
      have h1 :
          Real.rpow x (3 / 2 : ℝ) =
            Real.rpow x (1 + (1 / 2 : ℝ)) := by
        norm_num
      rw [h1]
      have h2 :
          Real.rpow x (1 + (1 / 2 : ℝ)) =
            Real.rpow x 1 * Real.rpow x (1 / 2 : ℝ) :=
        Real.rpow_add hx_pos 1 (1 / 2 : ℝ)
      rw [h2]
      have h3 : Real.rpow x 1 = x := by simp
      have h4 :
          Real.rpow x (1 / 2 : ℝ) = Real.sqrt x := by
        exact Eq.symm (Real.sqrt_eq_rpow x)
      rw [h3, h4]
    have h_upper : x ≤ prefactor * cardUpper := by
      calc
        x = prefactor * (ambientCard : ℝ) := by rfl
        _ ≤ prefactor * cardUpper := by gcongr
    have h_sqrt :
        Real.sqrt x ≤ Real.sqrt (prefactor * cardUpper) :=
      Real.sqrt_le_sqrt h_upper
    have h_main :
        coefficient * (x * Real.sqrt x) * logTail ≤
          coefficient *
            (x * Real.sqrt (prefactor * cardUpper)) * logTail := by
      gcongr
    have h_final :
        coefficient *
            (x * Real.sqrt (prefactor * cardUpper)) * logTail =
          (ambientCard : ℝ) *
            (coefficient * prefactor *
              Real.sqrt (prefactor * cardUpper) * logTail) := by
      simp only [hx]
      ring
    rw [h_rpow]
    exact le_trans h_main (le_of_eq h_final)

end Kakeya.Cinematic
