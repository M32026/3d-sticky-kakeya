import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs

/-!
# Interpolate the two coarse multiplicity bounds
-/

namespace Kakeya.Cinematic

theorem coarse_multiplicity_interpolation :
    CoarseMultiplicityInterpolationStatement := by
  intro M measureBound tangencyBound hM hMeasure hTangency
    hMMeasure hMTangency
  rcases hM.eq_or_lt with rfl | hMPos
  · exact mul_nonneg (Real.rpow_nonneg hMeasure _) (Real.rpow_nonneg hTangency _)
  calc
    M = Real.rpow M (1 / 4 : ℝ) * Real.rpow M (3 / 4 : ℝ) := by
      have hAdd := Real.rpow_add hMPos (1 / 4 : ℝ) (3 / 4 : ℝ)
      norm_num at hAdd
      exact hAdd
    _ ≤ Real.rpow measureBound (1 / 4 : ℝ) *
        Real.rpow tangencyBound (3 / 4 : ℝ) := by
      exact mul_le_mul
        (Real.rpow_le_rpow hM hMMeasure (by norm_num))
        (Real.rpow_le_rpow hM hMTangency (by norm_num))
        (Real.rpow_nonneg hM _)
        (Real.rpow_nonneg hMeasure _)

end Kakeya.Cinematic
