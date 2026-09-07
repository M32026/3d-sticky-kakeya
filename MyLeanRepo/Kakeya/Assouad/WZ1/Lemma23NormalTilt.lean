import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23NormalTiltGeometry

/-!
# WZ1 Lemma 23 Step 1: full projection versus AD control

The projected full-grain slice fills a definite fraction of an interval.
Exact-slice global AD control bounds the measure inside that interval.  The
exponent gap forces the interval radius to be small, and the rectangle
geometry then forces the local normal to have small tilt.
-/

namespace Kakeya.Assouad

noncomputable section

open MeasureTheory

private lemma wz1Lemma23_radius_power_bound
    {rho sigma eta radius : ℝ}
    (hrho : 0 < rho) (hsigma : 0 < sigma)
    (hradius : 0 < radius)
    (h :
      Real.rpow rho (3 * eta) * (2 * radius) ≤
        Real.rpow rho (-eta) *
          Real.rpow (radius / rho) (1 - sigma) *
          (2 * rho)) :
    radius ≤ Real.rpow rho (1 - 4 * eta / sigma) := by
  have hratio :
      Real.rpow (radius / rho) (1 - sigma) =
        Real.rpow radius (1 - sigma) /
          Real.rpow rho (1 - sigma) :=
    Real.div_rpow hradius.le hrho.le (1 - sigma)
  have hrhoRatio :
      Real.rpow rho (-eta) /
            Real.rpow rho (1 - sigma) * rho =
        Real.rpow rho (sigma - eta) := by
    have hden : Real.rpow rho (1 - sigma) ≠ 0 :=
      (Real.rpow_pos_of_pos hrho _).ne'
    calc
      Real.rpow rho (-eta) /
              Real.rpow rho (1 - sigma) * rho
          = (Real.rpow rho (-eta) * rho) /
              Real.rpow rho (1 - sigma) := by ring
      _ = Real.rpow rho (sigma - eta) := by
        apply (div_eq_iff hden).2
        have hleft :
            Real.rpow rho (-eta) * rho =
              Real.rpow rho (1 - eta) := by
          calc
            Real.rpow rho (-eta) * rho
                = Real.rpow rho (-eta) *
                    Real.rpow rho 1 := by simp
            _ = Real.rpow rho (-eta + 1) :=
              (Real.rpow_add hrho (-eta) 1).symm
            _ = Real.rpow rho (1 - eta) := by ring_nf
        have hright :
            Real.rpow rho (sigma - eta) *
                Real.rpow rho (1 - sigma) =
              Real.rpow rho (1 - eta) := by
          calc
            Real.rpow rho (sigma - eta) *
                  Real.rpow rho (1 - sigma)
                = Real.rpow rho
                    ((sigma - eta) + (1 - sigma)) :=
                  (Real.rpow_add hrho _ _).symm
            _ = Real.rpow rho (1 - eta) := by ring_nf
        exact hleft.trans hright.symm
  have hright :
      Real.rpow rho (-eta) *
            (Real.rpow radius (1 - sigma) /
              Real.rpow rho (1 - sigma)) *
            (2 * rho) =
        2 * Real.rpow rho (sigma - eta) *
          Real.rpow radius (1 - sigma) := by
    calc
      Real.rpow rho (-eta) *
              (Real.rpow radius (1 - sigma) /
                Real.rpow rho (1 - sigma)) *
              (2 * rho)
          = 2 * Real.rpow radius (1 - sigma) *
              (Real.rpow rho (-eta) /
                Real.rpow rho (1 - sigma) * rho) := by ring
      _ = 2 * Real.rpow radius (1 - sigma) *
              Real.rpow rho (sigma - eta) := by
            rw [hrhoRatio]
      _ = 2 * Real.rpow rho (sigma - eta) *
              Real.rpow radius (1 - sigma) := by ring
  have hnormalized :
      Real.rpow rho (3 * eta) * radius ≤
        Real.rpow rho (sigma - eta) *
          Real.rpow radius (1 - sigma) := by
    rw [hratio, hright] at h
    nlinarith
  have hradiusFactor :
      Real.rpow radius (1 - sigma) *
          Real.rpow radius sigma = radius := by
    calc
      Real.rpow radius (1 - sigma) *
            Real.rpow radius sigma
          = Real.rpow radius ((1 - sigma) + sigma) :=
            (Real.rpow_add hradius _ _).symm
      _ = radius := by simp
  have hrhoFactor :
      Real.rpow rho (3 * eta) *
          Real.rpow rho (sigma - 4 * eta) =
        Real.rpow rho (sigma - eta) := by
    calc
      Real.rpow rho (3 * eta) *
            Real.rpow rho (sigma - 4 * eta)
          = Real.rpow rho
              ((3 * eta) + (sigma - 4 * eta)) :=
            (Real.rpow_add hrho _ _).symm
      _ = Real.rpow rho (sigma - eta) := by ring_nf
  let factor :=
    Real.rpow rho (3 * eta) *
      Real.rpow radius (1 - sigma)
  have hfactor : 0 < factor := by
    dsimp [factor]
    positivity
  have hpow :
      Real.rpow radius sigma ≤
        Real.rpow rho (sigma - 4 * eta) := by
    apply le_of_mul_le_mul_left (a := factor) _ hfactor
    dsimp [factor]
    calc
      Real.rpow rho (3 * eta) *
            Real.rpow radius (1 - sigma) *
            Real.rpow radius sigma
          = Real.rpow rho (3 * eta) * radius := by
              rw [mul_assoc, hradiusFactor]
      _ ≤ Real.rpow rho (sigma - eta) *
            Real.rpow radius (1 - sigma) := hnormalized
      _ = Real.rpow rho (3 * eta) *
            Real.rpow radius (1 - sigma) *
            Real.rpow rho (sigma - 4 * eta) := by
              calc
                Real.rpow rho (sigma - eta) *
                      Real.rpow radius (1 - sigma)
                    = (Real.rpow rho (3 * eta) *
                        Real.rpow rho (sigma - 4 * eta)) *
                          Real.rpow radius (1 - sigma) := by
                            rw [hrhoFactor]
                _ = _ := by ring
  have htarget :
      Real.rpow
          (Real.rpow rho (1 - 4 * eta / sigma)) sigma =
        Real.rpow rho (sigma - 4 * eta) := by
    calc
      Real.rpow
            (Real.rpow rho (1 - 4 * eta / sigma)) sigma
          = Real.rpow rho
              ((1 - 4 * eta / sigma) * sigma) :=
            (Real.rpow_mul hrho.le _ _).symm
      _ = Real.rpow rho (sigma - 4 * eta) := by
            congr 1
            field_simp [hsigma.ne']
  apply (Real.rpow_le_rpow_iff
    hradius.le
    (Real.rpow_nonneg hrho.le _)
    hsigma).mp
  change Real.rpow radius sigma ≤
    Real.rpow
      (Real.rpow rho (1 - 4 * eta / sigma)) sigma
  rw [htarget]
  exact hpow

theorem wz1_lemma23_normal_tilt :
    WZ1Lemma23NormalTiltStatement := by
  intro rho sigma eta C slope normal
    hrho hrho_one hsigma hsigma_one
    heta heta_sigma hC hCpower habsorb witness
  have hADUpper :
      volume witness.globalProjection ≤
        (C * Kakeya.realRpowENN
            (witness.projectionRadius / rho)
            (1 - sigma)) *
          ENNReal.ofReal (2 * rho) :=
    witness.globalAD.volume_subset_closedBall_le
      hC (by
        rw [witness.projectionRadius_eq]
        have hsqrt : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
        have htilt :
            0 ≤ |normal 1 -
              slope witness.sliceHeight * normal 0| := abs_nonneg _
        nlinarith)
      witness.projectionRadius_upper
      (witness.globalProjection_sub hrho)
  have hfull :
      Kakeya.realRpowENN rho (3 * eta) *
          ENNReal.ofReal (2 * witness.projectionRadius) ≤
        volume witness.globalProjection :=
    (mul_le_mul_right'
      witness.density_lower
      (ENNReal.ofReal
        (2 * witness.projectionRadius))).trans
      witness.globalProjection_full
  have hCUpper :
      (C * Kakeya.realRpowENN
          (witness.projectionRadius / rho)
          (1 - sigma)) *
          ENNReal.ofReal (2 * rho) ≤
        (Kakeya.realRpowENN rho (-eta) *
          Kakeya.realRpowENN
            (witness.projectionRadius / rho)
            (1 - sigma)) *
          ENNReal.ofReal (2 * rho) := by
    gcongr
  have hENN :
      Kakeya.realRpowENN rho (3 * eta) *
          ENNReal.ofReal (2 * witness.projectionRadius) ≤
        (Kakeya.realRpowENN rho (-eta) *
          Kakeya.realRpowENN
            (witness.projectionRadius / rho)
            (1 - sigma)) *
          ENNReal.ofReal (2 * rho) :=
    hfull.trans (hADUpper.trans hCUpper)
  have hrightTop :
      (Kakeya.realRpowENN rho (-eta) *
          Kakeya.realRpowENN
            (witness.projectionRadius / rho)
            (1 - sigma)) *
          ENNReal.ofReal (2 * rho) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono hrightTop hENN
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul] at hreal
  simp only [Kakeya.realRpowENN] at hreal
  have hradiusPos : 0 < witness.projectionRadius := by
    rw [witness.projectionRadius_eq]
    have hsqrt : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
    have htilt :
        0 ≤ |normal 1 -
          slope witness.sliceHeight * normal 0| := abs_nonneg _
    nlinarith
  have h1 :
      (ENNReal.ofReal (Real.rpow rho (3 * eta))).toReal =
        Real.rpow rho (3 * eta) :=
    ENNReal.toReal_ofReal (Real.rpow_nonneg hrho.le _)
  have h2 :
      (ENNReal.ofReal
        (2 * witness.projectionRadius)).toReal =
          2 * witness.projectionRadius :=
    ENNReal.toReal_ofReal
      (mul_nonneg (by norm_num) hradiusPos.le)
  have h3 :
      (ENNReal.ofReal (Real.rpow rho (-eta))).toReal =
        Real.rpow rho (-eta) :=
    ENNReal.toReal_ofReal (Real.rpow_nonneg hrho.le _)
  have h4 :
      (ENNReal.ofReal
        (Real.rpow
          (witness.projectionRadius / rho)
          (1 - sigma))).toReal =
        Real.rpow
          (witness.projectionRadius / rho)
          (1 - sigma) :=
    ENNReal.toReal_ofReal
      (Real.rpow_nonneg
        (div_nonneg hradiusPos.le hrho.le) _)
  have h5 :
      (ENNReal.ofReal (2 * rho)).toReal = 2 * rho :=
    ENNReal.toReal_ofReal (by positivity)
  rw [h1, h2, h3, h4, h5] at hreal
  have hradius :
      witness.projectionRadius ≤
        Real.rpow rho (1 - 4 * eta / sigma) :=
    wz1Lemma23_radius_power_bound
      hrho hsigma hradiusPos hreal
  have htiltNumerator :
      Real.sqrt rho *
          |normal (1 : Fin 3) -
            slope witness.sliceHeight *
              normal (0 : Fin 3)| ≤
        Real.sqrt rho / 10 := by
    exact (witness.tilt_radius hrho).trans
      (hradius.trans habsorb)
  have hsqrt : 0 < Real.sqrt rho :=
    Real.sqrt_pos.mpr hrho
  have htilt :
      |normal (1 : Fin 3) -
          slope witness.sliceHeight *
            normal (0 : Fin 3)| ≤ 1 / 10 := by
    have hscaled :
        Real.sqrt rho *
            |normal (1 : Fin 3) -
              slope witness.sliceHeight *
                normal (0 : Fin 3)| ≤
          Real.sqrt rho * (1 / 10 : ℝ) := by
      convert htiltNumerator using 1 <;> ring
    exact le_of_mul_le_mul_left hscaled hsqrt
  exact ⟨hradius, htilt⟩

/-- The AD-versus-fullness tilt bound for generalized witnesses. -/
theorem wz1_lemma23_normal_tilt_generalized :
    WZ1Lemma23NormalTiltStatementGeneralized := by
  intro rho sigma eta C slope normal
    hrho hrho_one hsigma hsigma_one
    heta heta_sigma hC hCpower habsorb witness
  have hADUpper :
      volume witness.globalProjection ≤
        (C * Kakeya.realRpowENN
            (witness.projectionRadius / rho)
            (1 - sigma)) *
          ENNReal.ofReal (2 * rho) :=
    witness.globalAD.volume_subset_closedBall_le
      hC (by
        rw [witness.projectionRadius_eq]
        have hsqrt : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
        have htilt :
            0 ≤ |normal 1 -
              slope witness.sliceHeight * normal 0| := abs_nonneg _
        nlinarith)
      witness.projectionRadius_upper
      (witness.globalProjection_sub hrho)
  have hfull :
      Kakeya.realRpowENN rho (3 * eta) *
          ENNReal.ofReal (2 * witness.projectionRadius) ≤
        volume witness.globalProjection :=
    (mul_le_mul_right'
      witness.density_lower
      (ENNReal.ofReal
        (2 * witness.projectionRadius))).trans
      witness.globalProjection_full
  have hCUpper :
      (C * Kakeya.realRpowENN
          (witness.projectionRadius / rho)
          (1 - sigma)) *
          ENNReal.ofReal (2 * rho) ≤
        (Kakeya.realRpowENN rho (-eta) *
          Kakeya.realRpowENN
            (witness.projectionRadius / rho)
            (1 - sigma)) *
          ENNReal.ofReal (2 * rho) := by
    gcongr
  have hENN :
      Kakeya.realRpowENN rho (3 * eta) *
          ENNReal.ofReal (2 * witness.projectionRadius) ≤
        (Kakeya.realRpowENN rho (-eta) *
          Kakeya.realRpowENN
            (witness.projectionRadius / rho)
            (1 - sigma)) *
          ENNReal.ofReal (2 * rho) :=
    hfull.trans (hADUpper.trans hCUpper)
  have hrightTop :
      (Kakeya.realRpowENN rho (-eta) *
          Kakeya.realRpowENN
            (witness.projectionRadius / rho)
            (1 - sigma)) *
          ENNReal.ofReal (2 * rho) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono hrightTop hENN
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul] at hreal
  simp only [Kakeya.realRpowENN] at hreal
  have hradiusPos : 0 < witness.projectionRadius := by
    rw [witness.projectionRadius_eq]
    have hsqrt : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
    have htilt :
        0 ≤ |normal 1 -
          slope witness.sliceHeight * normal 0| := abs_nonneg _
    nlinarith
  have h1 :
      (ENNReal.ofReal (Real.rpow rho (3 * eta))).toReal =
        Real.rpow rho (3 * eta) :=
    ENNReal.toReal_ofReal (Real.rpow_nonneg hrho.le _)
  have h2 :
      (ENNReal.ofReal
        (2 * witness.projectionRadius)).toReal =
          2 * witness.projectionRadius :=
    ENNReal.toReal_ofReal
      (mul_nonneg (by norm_num) hradiusPos.le)
  have h3 :
      (ENNReal.ofReal (Real.rpow rho (-eta))).toReal =
        Real.rpow rho (-eta) :=
    ENNReal.toReal_ofReal (Real.rpow_nonneg hrho.le _)
  have h4 :
      (ENNReal.ofReal
        (Real.rpow
          (witness.projectionRadius / rho)
          (1 - sigma))).toReal =
        Real.rpow
          (witness.projectionRadius / rho)
          (1 - sigma) :=
    ENNReal.toReal_ofReal
      (Real.rpow_nonneg
        (div_nonneg hradiusPos.le hrho.le) _)
  have h5 :
      (ENNReal.ofReal (2 * rho)).toReal = 2 * rho :=
    ENNReal.toReal_ofReal (by positivity)
  rw [h1, h2, h3, h4, h5] at hreal
  have hradius :
      witness.projectionRadius ≤
        Real.rpow rho (1 - 4 * eta / sigma) :=
    wz1Lemma23_radius_power_bound
      hrho hsigma hradiusPos hreal
  have htiltNumerator :
      Real.sqrt rho *
          |normal (1 : Fin 3) -
            slope witness.sliceHeight *
              normal (0 : Fin 3)| ≤
        Real.sqrt rho / 14 := by
    exact (witness.tilt_radius hrho).trans
      (hradius.trans habsorb)
  have hsqrt : 0 < Real.sqrt rho :=
    Real.sqrt_pos.mpr hrho
  have htilt :
      |normal (1 : Fin 3) -
          slope witness.sliceHeight *
            normal (0 : Fin 3)| ≤ 1 / 14 := by
    have hscaled :
        Real.sqrt rho *
            |normal (1 : Fin 3) -
              slope witness.sliceHeight *
                normal (0 : Fin 3)| ≤
          Real.sqrt rho * (1 / 14 : ℝ) := by
      convert htiltNumerator using 1 <;> ring
    exact le_of_mul_le_mul_left hscaled hsqrt
  exact ⟨hradius, htilt⟩

end

end Kakeya.Assouad
