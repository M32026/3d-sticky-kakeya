import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulExtremeCases

/-!
# ENNReal arithmetic helpers for the Kaufman closing coarsening branch

These lemmas handle the one-dimensional covering coarsening factor and
ENNReal division cancellation.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- The natural coarsening factor `K = floor(2 * delta / rho0) + 1` is
bounded by `7 * delta^(-epsilonOne)` as an ENNReal. -/
lemma coarsening_factor_ennreal
    {delta rho0 epsilonOne : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hepsilonOne : 0 < epsilonOne)
    (hrho0 : 0 < rho0)
    (hscaleLower : delta ≤ 3 * Real.rpow delta (-epsilonOne) * rho0) :
    let K : ℕ := Nat.floor (2 * delta / rho0) + 1
    (K : ENNReal) ≤ ENNReal.ofReal (7 * Real.rpow delta (-epsilonOne)) := by
  dsimp only
  set K : ℕ := Nat.floor (2 * delta / rho0) + 1 with hK_def
  have h_real_bound :
      (2 * delta / rho0 + 1 : ℝ) ≤ 7 * Real.rpow delta (-epsilonOne) :=
    wz1Lemma8_13_coarsening_factor_bound
      hdelta hdeltaOne hepsilonOne hrho0 hscaleLower
  have h_nonneg_arg : 0 ≤ 2 * delta / rho0 := by positivity
  have h_floor_le : (Nat.floor (2 * delta / rho0) : ℝ) ≤ 2 * delta / rho0 :=
    Nat.floor_le h_nonneg_arg
  have hK_real_le : (K : ℝ) ≤ 7 * Real.rpow delta (-epsilonOne) := by
    rw [hK_def]
    have h : ((Nat.floor (2 * delta / rho0) + 1 : ℕ) : ℝ) =
        (Nat.floor (2 * delta / rho0) : ℝ) + 1 := by
      simp
    rw [h]
    linarith
  have h_nonneg : 0 ≤ 7 * Real.rpow delta (-epsilonOne) := by
    have h : 0 ≤ Real.rpow delta (-epsilonOne) := Real.rpow_nonneg hdelta.le _
    positivity
  have h_ennreal :
      (K : ENNReal) = ENNReal.ofReal (K : ℝ) := by
    simp
  rw [h_ennreal]
  exact ENNReal.ofReal_le_ofReal hK_real_le

/-- Cancel a positive natural coefficient on the left of an ENNReal
inequality. -/
lemma ennreal_div_cancel
    {a b : ENNReal} {K : ℕ} (hKpos : 0 < K)
    (h : a ≤ (K : ENNReal) * b) :
    (K : ENNReal)⁻¹ * a ≤ b := by
  have hK_ne_zero : (K : ENNReal) ≠ 0 := by
    exact_mod_cast hKpos.ne'
  have hK_ne_top : (K : ENNReal) ≠ ⊤ := by
    simp
  have h_mul_inv : (K : ENNReal)⁻¹ * (K : ENNReal) = 1 :=
    ENNReal.inv_mul_cancel hK_ne_zero hK_ne_top
  calc
    (K : ENNReal)⁻¹ * a
      ≤ (K : ENNReal)⁻¹ * ((K : ENNReal) * b) := by
        gcongr
    _ = ((K : ENNReal)⁻¹ * (K : ENNReal)) * b := by
      rw [mul_assoc]
    _ = 1 * b := by rw [h_mul_inv]
    _ = b := by simp

end Kakeya.Assouad
