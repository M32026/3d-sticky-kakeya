import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSScaleGrowthStatement

/-!
WZ2 Proposition 7.1: absorb fixed mesh and current-scale constants below a
one-scale selected radius.
-/

namespace Kakeya.Assouad

theorem grid_os_scale_growth :
    GridOSScaleGrowthStatement := by
  intro epsilon D hε_pos hε_lt_one hD_nonneg
  have hε2_pos : 0 < epsilon ^ 2 := by positivity
  have h_beta_lt_alpha : (1 - epsilon ^ 2) < (1 : ℝ) := by linarith
  have h_main := exists_delta_mul_rpow_le_rpow D hD_nonneg h_beta_lt_alpha
  rcases h_main with ⟨scale₀, hscale₀_pos, hscale₀_one, h_absorb⟩
  refine ⟨scale₀, hscale₀_pos, hscale₀_one, ?_⟩
  intro scale rho hscale_pos hscale_le hrho
  have h1 : D * Real.rpow scale (1 : ℝ) ≤ Real.rpow scale (1 - epsilon ^ 2) :=
    h_absorb scale hscale_pos hscale_le
  have h2 : Real.rpow scale (1 : ℝ) = scale := Real.rpow_one scale
  rw [h2] at h1
  exact h1.trans hrho.le

end Kakeya.Assouad
