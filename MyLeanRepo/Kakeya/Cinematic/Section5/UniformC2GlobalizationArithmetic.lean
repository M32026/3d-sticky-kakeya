import MyLeanRepo.Kakeya.Cinematic.Section5.LocalAssembly.LogAbsorption

/-!
# Scale arithmetic for uniform centered Taylor globalization

These lemmas isolate the two losses introduced by Taylor transport and the
logarithmic interval cover.
-/

noncomputable section

namespace Kakeya.Cinematic

theorem centeredTaylor_transported_delta_rpow_le
    {K delta epsilon : ℝ}
    (hK : 1 ≤ K) (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hscale :
      Real.rpow (3 * K) (epsilon / 4) ≤
        Real.rpow delta (-(epsilon / 4))) :
    Real.rpow (delta / (3 * K)) (-(epsilon / 4)) ≤
      Real.rpow delta (-(epsilon / 2)) := by
  have h3K_pos : 0 < 3 * K := by positivity
  have hscale_eq :
      Real.rpow (delta / (3 * K)) (-(epsilon / 4)) =
        Real.rpow delta (-(epsilon / 4)) *
          Real.rpow (3 * K) (epsilon / 4) := by
    change
      (delta / (3 * K)) ^ (-(epsilon / 4)) =
        delta ^ (-(epsilon / 4)) * (3 * K) ^ (epsilon / 4)
    rw [Real.div_rpow hdelta.le h3K_pos.le]
    rw [Real.rpow_neg h3K_pos.le]
    have hpow_ne :
        Real.rpow (3 * K) (epsilon / 4) ≠ 0 :=
      (Real.rpow_pos_of_pos h3K_pos _).ne'
    field_simp [hpow_ne]
  rw [hscale_eq]
  calc
    Real.rpow delta (-(epsilon / 4)) *
        Real.rpow (3 * K) (epsilon / 4)
        ≤ Real.rpow delta (-(epsilon / 4)) *
            Real.rpow delta (-(epsilon / 4)) := by
      exact mul_le_mul_of_nonneg_left hscale
        (Real.rpow_nonneg hdelta.le _)
    _ = Real.rpow delta (-(epsilon / 2)) := by
      have h :=
        Real.rpow_add hdelta (-(epsilon / 4)) (-(epsilon / 4))
      have hexp :
          -(epsilon / 4) + -(epsilon / 4) = -(epsilon / 2) := by
        ring
      rw [hexp] at h
      exact h.symm

theorem centeredTaylor_cover_card_add_two_le
    {card : ℕ} {C_cover lambda delta epsilon : ℝ}
    (hC_cover : 0 < C_cover)
    (hlambda : 1 ≤ lambda)
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hrho_one : lambda * delta ≤ 1)
    (hepsilon : 0 < epsilon)
    (hcard :
      (card : ℝ) ≤
        C_cover * (|Real.log (lambda * delta)| + 1))
    (habsorb :
      (C_cover + 2) * (Real.log (1 / delta) + 1) ≤
        Real.rpow delta (-(epsilon / 2))) :
    (card + 2 : ℕ) ≤ Real.rpow delta (-(epsilon / 2)) := by
  have hlambda_pos : 0 < lambda := by linarith
  have hrho_pos : 0 < lambda * delta := mul_pos hlambda_pos hdelta
  have hdelta_rho : delta ≤ lambda * delta := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hlambda hdelta.le
  have hlog_mono :
      Real.log delta ≤ Real.log (lambda * delta) :=
    Real.log_le_log hdelta hdelta_rho
  have hlog_delta_nonpos : Real.log delta ≤ 0 :=
    Real.log_nonpos hdelta.le hdelta_one
  have hlog_rho_nonpos : Real.log (lambda * delta) ≤ 0 :=
    Real.log_nonpos hrho_pos.le hrho_one
  have habs_rho :
      |Real.log (lambda * delta)| = -Real.log (lambda * delta) :=
    abs_of_nonpos hlog_rho_nonpos
  have hlog_inv : Real.log (1 / delta) = -Real.log delta := by
    rw [one_div, Real.log_inv]
  have habs_le :
      |Real.log (lambda * delta)| ≤ Real.log (1 / delta) := by
    rw [habs_rho, hlog_inv]
    linarith
  have hlog_term : 1 ≤ Real.log (1 / delta) + 1 := by
    rw [hlog_inv]
    linarith
  have hcard_real :
      (card + 2 : ℕ) ≤
        (C_cover + 2) * (Real.log (1 / delta) + 1) := by
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    calc
      (card : ℝ) + 2
          ≤ C_cover * (|Real.log (lambda * delta)| + 1) + 2 := by
        linarith
      _ ≤ C_cover * (Real.log (1 / delta) + 1) + 2 := by
        gcongr
      _ ≤ (C_cover + 2) * (Real.log (1 / delta) + 1) := by
        nlinarith
  exact_mod_cast hcard_real.trans habsorb

end Kakeya.Cinematic
