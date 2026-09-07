import MyLeanRepo.Kakeya.Assouad.PropStickyStatements

/-! # Absolute-to-relative scale absorption -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_realRpowENN_to_coarse_scale
    {delta outputLoss rho : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (houtput : 0 < outputLoss)
    (hrho : 0 < rho)
    (hrhoUpper : rho ≤ Real.rpow delta outputLoss) :
    Kakeya.realRpowENN delta (-(outputLoss ^ 2)) ≤
      Kakeya.realRpowENN rho (-outputLoss) := by
  have hpow :
      Real.rpow (Real.rpow delta outputLoss) (-outputLoss) ≤
        Real.rpow rho (-outputLoss) :=
    Real.rpow_le_rpow_of_nonpos hrho hrhoUpper (by linarith)
  have hrewrite :
      Real.rpow (Real.rpow delta outputLoss) (-outputLoss) =
        Real.rpow delta (-(outputLoss ^ 2)) := by
    calc
      Real.rpow (Real.rpow delta outputLoss) (-outputLoss) =
          Real.rpow delta (outputLoss * (-outputLoss)) :=
        (Real.rpow_mul hdelta.le outputLoss (-outputLoss)).symm
      _ = Real.rpow delta (-(outputLoss ^ 2)) := by
        congr 1
        ring
  rw [hrewrite] at hpow
  exact ENNReal.ofReal_mono hpow

theorem wz2_realRpowENN_to_fiber_scale
    {delta outputLoss rho : ℝ}
    (hdelta : 0 < delta)
    (houtput : 0 < outputLoss)
    (hrho : 0 < rho)
    (hrhoLower : Real.rpow delta (1 - outputLoss) ≤ rho) :
    Kakeya.realRpowENN delta (-(outputLoss ^ 2)) ≤
      Kakeya.realRpowENN (delta / rho) (-outputLoss) := by
  have hsplit :
      Real.rpow delta 1 =
        Real.rpow delta (1 - outputLoss) *
          Real.rpow delta outputLoss := by
    calc
      Real.rpow delta 1 =
          Real.rpow delta ((1 - outputLoss) + outputLoss) := by
        congr 1
        ring
      _ = Real.rpow delta (1 - outputLoss) *
            Real.rpow delta outputLoss :=
        Real.rpow_add hdelta (1 - outputLoss) outputLoss
  have hratio :
      delta / rho ≤ Real.rpow delta outputLoss := by
    rw [div_le_iff₀ hrho]
    calc
      delta = Real.rpow delta 1 := by simp
      _ = Real.rpow delta (1 - outputLoss) *
            Real.rpow delta outputLoss := hsplit
      _ ≤ rho * Real.rpow delta outputLoss :=
        mul_le_mul_of_nonneg_right hrhoLower
          (Real.rpow_nonneg hdelta.le outputLoss)
      _ = Real.rpow delta outputLoss * rho := mul_comm _ _
  have hpow :=
    Real.rpow_le_rpow_of_nonpos
      (x := delta / rho)
      (y := Real.rpow delta outputLoss)
      (z := -outputLoss)
      (div_pos hdelta hrho) hratio (by linarith)
  change
    Real.rpow (Real.rpow delta outputLoss) (-outputLoss) ≤
      Real.rpow (delta / rho) (-outputLoss) at hpow
  have hrewrite :
      Real.rpow (Real.rpow delta outputLoss) (-outputLoss) =
        Real.rpow delta (-(outputLoss ^ 2)) := by
    calc
      Real.rpow (Real.rpow delta outputLoss) (-outputLoss) =
          Real.rpow delta (outputLoss * (-outputLoss)) :=
        (Real.rpow_mul hdelta.le outputLoss (-outputLoss)).symm
      _ = Real.rpow delta (-(outputLoss ^ 2)) := by
        congr 1
        ring
  rw [hrewrite] at hpow
  exact ENNReal.ofReal_mono hpow

end Kakeya.Assouad

end
