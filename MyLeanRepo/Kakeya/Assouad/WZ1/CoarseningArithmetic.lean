import MyLeanRepo.Kakeya.Assouad.WZ1.CoarseningHelpers

/-!
# ENNReal arithmetic for the coarsening branch of the faithful closing

Combines the one-dimensional coarsening factor bound with the Kaufman
covering lower bound to produce a bound at scale `delta`.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal

/-- General ENNReal cancellation: if `B ≤ K * N` and `K ≤ R` with `R` nonzero
and finite, then `R⁻¹ * B ≤ N`. -/
lemma ennreal_coarsening_cancel
    {B N R : ENNReal} {K : ℕ}
    (hR_pos : R ≠ 0)
    (hR_top : R ≠ ⊤)
    (hK_le_R : (K : ENNReal) ≤ R)
    (hB_le : B ≤ (K : ENNReal) * N) :
    R⁻¹ * B ≤ N := by
  have h1 : B ≤ R * N := by
    calc
      B ≤ (K : ENNReal) * N := hB_le
      _ ≤ R * N := by gcongr
  exact (ENNReal.inv_mul_le_iff hR_pos hR_top).mpr h1

/-- Combine the natural coarsening factor bound `K ≤ 7 * delta^(-epsilonOne)`
with a Kaufman lower bound `B ≤ K * N` to conclude
`(7 * delta^(-epsilonOne))⁻¹ * B ≤ N` in ENNReal.

Here `K = Nat.floor (2 * delta / rho0) + 1` is the 1D coarsening factor. -/
lemma ennreal_coarsening_factor_cancel
    {B N : ENNReal}
    {delta rho0 epsilonOne : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hepsilonOne : 0 < epsilonOne)
    (hrho0 : 0 < rho0)
    (hscaleLower : delta ≤ 3 * Real.rpow delta (-epsilonOne) * rho0)
    (hB_le : B ≤ ((Nat.floor (2 * delta / rho0) + 1 : ℕ) : ENNReal) * N) :
    (ENNReal.ofReal (7 * Real.rpow delta (-epsilonOne)))⁻¹ * B ≤ N := by
  let K : ℕ := Nat.floor (2 * delta / rho0) + 1
  let R : ENNReal := ENNReal.ofReal (7 * Real.rpow delta (-epsilonOne))
  have hfactor_pos : 0 < 7 * Real.rpow delta (-epsilonOne) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hdelta _)
  have hR_pos : R ≠ 0 := by
    rw [show R = ENNReal.ofReal (7 * Real.rpow delta (-epsilonOne)) from rfl]
    intro h
    have h5 : (7 * Real.rpow delta (-epsilonOne)) ≤ 0 := ENNReal.ofReal_eq_zero.mp h
    linarith
  have hR_top : R ≠ ⊤ := ENNReal.ofReal_ne_top
  have hK_le_R : (K : ENNReal) ≤ R :=
    coarsening_factor_ennreal hdelta hdeltaOne hepsilonOne hrho0 hscaleLower
  exact ennreal_coarsening_cancel hR_pos hR_top hK_le_R hB_le

/-- Lift a real numerical inequality to ENNReal and combine with the
coarsening cancellation.

Given the real inequality
`7 * delta^(-epsilonOne) * target ≤ coefficient`,
conclude
`ENNReal.ofReal target ≤ R⁻¹ * ENNReal.ofReal coefficient`
where `R = ENNReal.ofReal (7 * delta^(-epsilonOne))`. -/
lemma ennreal_coarsening_numerical_lift
    {delta epsilonOne target coefficient : ℝ}
    (hdelta : 0 < delta)
    (_hepsilonOne : 0 < epsilonOne)
    (_htarget_pos : 0 ≤ target)
    (_hcoefficient_pos : 0 ≤ coefficient)
    (h_numerical :
      7 * Real.rpow delta (-epsilonOne) * target ≤ coefficient) :
    ENNReal.ofReal target ≤
      (ENNReal.ofReal (7 * Real.rpow delta (-epsilonOne)))⁻¹ *
        ENNReal.ofReal coefficient := by
  set factor : ℝ := 7 * Real.rpow delta (-epsilonOne) with hfactor_def
  have hfactor_pos : 0 < factor :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hdelta _)
  have hfactor_nonneg : 0 ≤ factor := hfactor_pos.le
  set R : ENNReal := ENNReal.ofReal factor with hR_def
  have hR_pos : R ≠ 0 := by
    rw [hR_def]
    intro h
    have h5 : factor ≤ 0 := ENNReal.ofReal_eq_zero.mp h
    linarith
  have hR_top : R ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_mul : R * ENNReal.ofReal target ≤ ENNReal.ofReal coefficient := by
    have h1 : R * ENNReal.ofReal target = ENNReal.ofReal (factor * target) := by
      rw [hR_def, ← ENNReal.ofReal_mul hfactor_nonneg]
    rw [h1]
    exact ENNReal.ofReal_le_ofReal h_numerical
  have h2 : R⁻¹ * (R * ENNReal.ofReal target) ≤ R⁻¹ * ENNReal.ofReal coefficient := by
    gcongr
  have h3 : R⁻¹ * (R * ENNReal.ofReal target) = ENNReal.ofReal target := by
    have h4 : R⁻¹ * (R * ENNReal.ofReal target) = (R⁻¹ * R) * ENNReal.ofReal target := by
      rw [← mul_assoc]
    rw [h4, ENNReal.inv_mul_cancel hR_pos hR_top, one_mul]
  rw [h3] at h2
  exact h2

end Kakeya.Assouad
