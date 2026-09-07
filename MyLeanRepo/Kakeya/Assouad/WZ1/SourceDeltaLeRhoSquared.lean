import Mathlib.Tactic

/-!
# Lemma: sourceDelta ≤ rho² given the WZ1 scale relation

Given `rho = sourceDelta^(σ/(2+σ))` with `0 < σ < 1` and `0 < sourceDelta < 1`,
prove `sourceDelta ≤ rho²`.

Since `rho² = sourceDelta^(2σ/(2+σ))` and `2σ/(2+σ) < 1` (because σ < 2),
and `0 < sourceDelta < 1`, we have `sourceDelta^1 ≤ sourceDelta^(2σ/(2+σ))`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Given `rho = sourceDelta^(σ/(2+σ))` with `0 < σ < 1` and `0 < sourceDelta < 1`,
prove `sourceDelta ≤ rho²`. -/
lemma sourceDelta_le_rho_squared
    {sourceDelta rho sigma : ℝ}
    (hsigma_pos : 0 < sigma)
    (hsigma_one : sigma < 1)
    (hsourceDelta_pos : 0 < sourceDelta)
    (hsourceDelta_lt_one : sourceDelta < 1)
    (hrho_eq : rho = Real.rpow sourceDelta (sigma / (2 + sigma))) :
    sourceDelta ≤ rho ^ 2 := by
  have h1 : 0 < 2 + sigma := by linarith
  have h2 : 0 < sigma / (2 + sigma) := by positivity
  have h3 : sigma / (2 + sigma) < 1 := by
    apply (div_lt_one h1).mpr
    linarith
  have h4 : 2 * sigma / (2 + sigma) < 1 := by
    apply (div_lt_one h1).mpr
    linarith
  have h5 : 0 ≤ 2 * sigma / (2 + sigma) := by positivity
  have h6 : rho ^ 2 = Real.rpow sourceDelta (2 * sigma / (2 + sigma)) := by
    rw [hrho_eq]
    have h7 : (Real.rpow sourceDelta (sigma / (2 + sigma))) ^ 2 =
        Real.rpow sourceDelta ((sigma / (2 + sigma)) * 2) :=
      (Real.rpow_mul_natCast (by linarith) (sigma / (2 + sigma)) 2).symm
    rw [h7]
    have h8 : (sigma / (2 + sigma)) * 2 = 2 * sigma / (2 + sigma) := by ring
    rw [h8]
  have h10 : (2 * sigma / (2 + sigma)) ≤ (1 : ℝ) := by linarith
  have h11 : Real.rpow sourceDelta 1 ≤ Real.rpow sourceDelta (2 * sigma / (2 + sigma)) :=
    Real.rpow_le_rpow_of_exponent_ge hsourceDelta_pos (by linarith) h10
  rw [h6]
  have h12 : sourceDelta = Real.rpow sourceDelta 1 := (Real.rpow_one sourceDelta).symm
  calc sourceDelta
    = Real.rpow sourceDelta 1 := h12
    _ ≤ Real.rpow sourceDelta (2 * sigma / (2 + sigma)) := h11

end Kakeya.Assouad
