import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6Absorption

/-! # Elementary power-scale identities for Section 6 -/

noncomputable section

namespace Kakeya.Assouad

lemma section6_power_relative_rpow
    {delta rho power exponent : ℝ}
    (hdelta : 0 < delta) (hrho : rho = Real.rpow delta power) :
    Kakeya.realRpowENN (delta / rho) exponent =
      Kakeya.realRpowENN delta ((1 - power) * exponent) := by
  have hratio : delta / rho = Real.rpow delta (1 - power) := by
    rw [hrho]
    calc
      delta / Real.rpow delta power =
          Real.rpow delta 1 / Real.rpow delta power := by
        congr 1
        exact (Real.rpow_one delta).symm
      _ = Real.rpow delta (1 - power) :=
        (Real.rpow_sub hdelta 1 power).symm
  rw [hratio]
  simp only [Kakeya.realRpowENN]
  congr 1
  exact (Real.rpow_mul hdelta.le (1 - power) exponent).symm

end Kakeya.Assouad

end
