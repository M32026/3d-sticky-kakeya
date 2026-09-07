import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientCardinalityRpowLinearization
import MyLeanRepo.Kakeya.Cinematic.Section5.FixedAmbientRpowFineVolumeAssemblyInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.LinearAmbientFineVolumeAssembly

/-!
# Fixed-ambient volume from a Proposition 26 cardinality bound
-/

namespace Kakeya.Cinematic

theorem fixed_ambient_rpow_fine_volume_assembly :
    FixedAmbientRpowFineVolumeAssemblyStatement := by
  intro h1 h2 E fineCard ambientCard prefactor cardUpper
    coefficient logTail area h_prefactor_nonneg
    h_cardUpper_nonneg h_ambient_le h_coefficient_nonneg
    h_logTail_nonneg h_area_nonneg h_card h_vol
  set cardCoefficient : ℝ :=
    coefficient * prefactor *
      Real.sqrt (prefactor * cardUpper) * logTail
    with h_cardCoefficient
  have h1' :
      coefficient *
          Real.rpow
            (prefactor * (ambientCard : ℝ)) (3 / 2 : ℝ) *
          logTail ≤
        (ambientCard : ℝ) * cardCoefficient := by
    simpa [h_cardCoefficient] using
      h1 ambientCard prefactor cardUpper coefficient logTail
        h_prefactor_nonneg h_cardUpper_nonneg h_ambient_le
        h_coefficient_nonneg h_logTail_nonneg
  have h_card' :
      (fineCard : ℝ) ≤
        (ambientCard : ℝ) * cardCoefficient :=
    h_card.trans h1'
  have h_cardCoefficient_nonneg :
      0 ≤ cardCoefficient := by
    rw [h_cardCoefficient]
    have hproduct :
        0 ≤ prefactor * cardUpper :=
      mul_nonneg h_prefactor_nonneg h_cardUpper_nonneg
    have hsqrt :
        0 ≤ Real.sqrt (prefactor * cardUpper) :=
      Real.sqrt_nonneg _
    positivity
  exact h2 fineCard ambientCard cardCoefficient area
    h_cardCoefficient_nonneg h_area_nonneg h_card' h_vol

end Kakeya.Cinematic
