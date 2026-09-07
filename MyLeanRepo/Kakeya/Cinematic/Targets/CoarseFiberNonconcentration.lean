import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs

/-!
# Non-concentration of one coarse rectangle fiber
-/

namespace Kakeya.Cinematic

theorem coarse_fiber_nonconcentration :
    CoarseFiberNonconcentrationStatement := by
  intro M q mu₁ mu₂ coefficient logLoss hq _ hcoefficient _ hmu H G _
    hM hincidenceLower hincidenceUpper center radius
  have hq_real : (0 : ℝ) < q := by
    exact_mod_cast hq
  have hcount :
      (q : ℝ) *
          ((H.carrier ∩ c2Ball center radius).ncard : ℝ) ≤
        (q : ℝ) * (logLoss * coefficient * (H.card : ℝ)) := by
    calc
      (q : ℝ) *
            ((H.carrier ∩ c2Ball center radius).ncard : ℝ) ≤
          ∑ i, (((G i).carrier ∩
            c2Ball center radius).ncard : ℝ) :=
        hincidenceLower center radius
      _ ≤ M * mu₁ := hincidenceUpper center radius
      _ ≤ M * (coefficient * mu₂) :=
        mul_le_mul_of_nonneg_left hmu (by positivity)
      _ = coefficient * (M * mu₂) := by ring
      _ ≤ coefficient * (logLoss * q * (H.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hM hcoefficient
      _ = (q : ℝ) * (logLoss * coefficient * (H.card : ℝ)) := by ring
  exact le_of_mul_le_mul_left hcount hq_real

end Kakeya.Cinematic
