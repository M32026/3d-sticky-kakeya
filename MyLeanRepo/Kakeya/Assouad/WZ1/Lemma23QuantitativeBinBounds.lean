import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedPreparedGeometry

/-!
# Explicit quantitative bin bounds for WZ1 Lemma 23

The local and localized global packages store natural bounds as
`ceil(X.toReal) + 1`.  This module converts them to convenient real bounds and
absorbs the additive two into the main term using `1 ≤ C` and
`1 ≤ sqrt rho / rho`.
-/

namespace Kakeya.Assouad

noncomputable section

private lemma wz1Lemma23_ceil_add_one_real
    {X : ENNReal} (hX : X ≠ ⊤) :
    ((Nat.ceil X.toReal + 1 : ℕ) : ℝ) ≤ X.toReal + 2 := by
  have hceil :
      (Nat.ceil X.toReal : ℝ) < X.toReal + 1 :=
    Nat.ceil_lt_add_one_of_gt_neg_one
      (by linarith [ENNReal.toReal_nonneg (a := X)])
  norm_cast at hceil
  simp only [Nat.cast_add, Nat.cast_one]
  linarith

private lemma wz1Lemma23_sqrt_div_rho_one
    {rho : ℝ} (hrho : 0 < rho) (hrho_one : rho ≤ 1) :
    1 ≤ Real.sqrt rho / rho := by
  apply (le_div_iff₀ hrho).2
  have hsqrt : rho ≤ Real.sqrt rho := by
    nlinarith [Real.sqrt_nonneg rho,
      Real.sq_sqrt hrho.le]
  simpa using hsqrt

private lemma wz1Lemma23_main_bin_factor_one
    {rho sigma : ℝ} {C : ENNReal}
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hC : 1 ≤ C) (hCfinite : C ≠ ⊤) :
    1 ≤ C.toReal *
      Real.rpow (Real.sqrt rho / rho) (1 - sigma) := by
  have hCreal : 1 ≤ C.toReal := by
    rw [← ENNReal.toReal_one]
    exact
      (ENNReal.toReal_le_toReal (by norm_num) hCfinite).mpr hC
  have hbase :
      1 ≤ Real.sqrt rho / rho :=
    wz1Lemma23_sqrt_div_rho_one hrho hrho_one
  have hexponent : 0 ≤ 1 - sigma := by linarith
  have hrpow :
      1 ≤ Real.rpow (Real.sqrt rho / rho) (1 - sigma) :=
    Real.one_le_rpow hbase hexponent
  nlinarith [ENNReal.toReal_nonneg (a := C),
    Real.rpow_nonneg (by positivity : 0 ≤ Real.sqrt rho / rho)
      (1 - sigma)]

/-- Explicit real upper bound for the local-bin package. -/
lemma WZ1Lemma23LocalBinPackage.localBinBound_real_le
    {rho sigma : ℝ} {C : ENNReal}
    {cells : Finset (ℤ × ℤ × ℤ)}
    (package :
      WZ1Lemma23LocalBinPackage
        (rho := rho) (sigma := sigma) C cells)
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hC : 1 ≤ C) (hCtop : C ≠ ⊤) :
    (package.localBinBound : ℝ) ≤
      21 * C.toReal *
        Real.rpow (Real.sqrt rho / rho) (1 - sigma) := by
  let X : ENNReal :=
    19 * C *
      Kakeya.realRpowENN
        (Real.sqrt rho / rho) (1 - sigma)
  have hX : X ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hCtop)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  have hceil :
      (package.localBinBound : ℝ) ≤ X.toReal + 2 := by
    rw [package.localBinBound_eq]
    exact wz1Lemma23_ceil_add_one_real hX
  have hratioNonneg : 0 ≤ Real.sqrt rho / rho := by positivity
  have hrpowNonneg :
      0 ≤ Real.rpow (Real.sqrt rho / rho) (1 - sigma) :=
    Real.rpow_nonneg hratioNonneg _
  have hrpowToReal :
      (Kakeya.realRpowENN
        (Real.sqrt rho / rho) (1 - sigma)).toReal =
        Real.rpow (Real.sqrt rho / rho) (1 - sigma) := by
    exact ENNReal.toReal_ofReal hrpowNonneg
  have hXreal :
      X.toReal =
        19 * C.toReal *
          Real.rpow (Real.sqrt rho / rho) (1 - sigma) := by
    calc
      X.toReal =
          (19 : ENNReal).toReal * C.toReal *
            (Kakeya.realRpowENN
              (Real.sqrt rho / rho) (1 - sigma)).toReal := by
        simp [X, ENNReal.toReal_mul]
      _ = 19 * C.toReal *
          Real.rpow (Real.sqrt rho / rho) (1 - sigma) := by
        rw [hrpowToReal]
        norm_num
  have hmain :
      1 ≤ C.toReal *
        Real.rpow (Real.sqrt rho / rho) (1 - sigma) :=
    wz1Lemma23_main_bin_factor_one
      hrho hrho_one hsigma hsigma_one hC hCtop
  rw [hXreal] at hceil
  nlinarith

/-- Explicit real upper bound for the sharp localized global-bin package. -/
lemma WZ1Lemma23LocalizedGlobalBinPackage.globalBinBound_real_le
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {globalPackage :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C}
    (package :
      WZ1Lemma23LocalizedGlobalBinPackage globalPackage)
    (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hC : 1 ≤ C) (hCtop : C ≠ ⊤) :
    (package.globalBinBound : ℝ) ≤
      35 * C.toReal *
        Real.rpow (Real.sqrt rho / rho) (1 - sigma) := by
  let X : ENNReal :=
    33 * C *
      Kakeya.realRpowENN
        (Real.sqrt rho / rho) (1 - sigma)
  have hX : X ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hCtop)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  have hceil :
      (package.globalBinBound : ℝ) ≤ X.toReal + 2 := by
    rw [package.globalBinBound_eq]
    exact wz1Lemma23_ceil_add_one_real hX
  have hratioNonneg : 0 ≤ Real.sqrt rho / rho :=
    div_nonneg (Real.sqrt_nonneg rho) globalPackage.rho_pos.le
  have hrpowNonneg :
      0 ≤ Real.rpow (Real.sqrt rho / rho) (1 - sigma) :=
    Real.rpow_nonneg hratioNonneg _
  have hrpowToReal :
      (Kakeya.realRpowENN
        (Real.sqrt rho / rho) (1 - sigma)).toReal =
        Real.rpow (Real.sqrt rho / rho) (1 - sigma) := by
    exact ENNReal.toReal_ofReal hrpowNonneg
  have hXreal :
      X.toReal =
        33 * C.toReal *
          Real.rpow (Real.sqrt rho / rho) (1 - sigma) := by
    calc
      X.toReal =
          (33 : ENNReal).toReal * C.toReal *
            (Kakeya.realRpowENN
              (Real.sqrt rho / rho) (1 - sigma)).toReal := by
        simp [X, ENNReal.toReal_mul]
      _ = 33 * C.toReal *
          Real.rpow (Real.sqrt rho / rho) (1 - sigma) := by
        rw [hrpowToReal]
        norm_num
  have hmain :
      1 ≤ C.toReal *
        Real.rpow (Real.sqrt rho / rho) (1 - sigma) :=
    wz1Lemma23_main_bin_factor_one
      globalPackage.rho_pos hrho_one hsigma hsigma_one hC hCtop
  rw [hXreal] at hceil
  nlinarith

end

end Kakeya.Assouad
