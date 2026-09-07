import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-! # Small-scale ENNReal power absorption -/

noncomputable section

namespace Kakeya.Assouad

lemma ennreal_constant_mul_rpow_le_rpow_of_real
    {constant delta sourceExponent targetExponent : ℝ}
    (hconstant : 0 ≤ constant) (hdelta : 0 < delta)
    (hreal : constant * Real.rpow delta sourceExponent ≤
      Real.rpow delta targetExponent) :
    ENNReal.ofReal constant * Kakeya.realRpowENN delta sourceExponent ≤
      Kakeya.realRpowENN delta targetExponent := by
  have h := ENNReal.ofReal_mono hreal
  rw [ENNReal.ofReal_mul hconstant] at h
  simpa [Kakeya.realRpowENN] using h

lemma realRpowENN_mono_constant
    {delta first second : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (h : first ≤ second) :
    Kakeya.realRpowENN delta second ≤ Kakeya.realRpowENN delta first := by
  apply ENNReal.ofReal_mono
  exact Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one h

end Kakeya.Assouad

end
