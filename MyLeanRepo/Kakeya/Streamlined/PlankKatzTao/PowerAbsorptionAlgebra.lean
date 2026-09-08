import MyLeanRepo.Kakeya.Streamlined.GeneralizedKatzTao.AbsorptionHelpers

/-!
# ENNReal algebra for arbitrary-power absorption
-/

noncomputable section

namespace Kakeya.Streamlined

lemma realRpowENN_ne_zero
    {a exponent : ℝ} (ha : 0 < a) :
    Kakeya.realRpowENN a exponent ≠ 0 := by
  dsimp only [Kakeya.realRpowENN]
  exact
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos ha exponent)).ne'

lemma realRpowENN_ne_top
    {a exponent : ℝ} :
    Kakeya.realRpowENN a exponent ≠ ⊤ :=
  ENNReal.ofReal_ne_top

lemma absorption_upper_mul
    {a p q : ℝ}
    (ha : 0 < a)
    {X Y : ENNReal}
    (hX : X ≤ Kakeya.realRpowENN a (-p))
    (hY : Y ≤ Kakeya.realRpowENN a (-q)) :
    X * Y ≤ Kakeya.realRpowENN a (-(p + q)) := by
  calc
    X * Y ≤
        Kakeya.realRpowENN a (-p) *
          Kakeya.realRpowENN a (-q) := by gcongr
    _ = Kakeya.realRpowENN a (-(p + q)) := by
      rw [← realRpowENN_add' ha]
      congr 1
      ring

lemma absorption_lower_mul
    {a p q : ℝ}
    (ha : 0 < a)
    {X Y : ENNReal}
    (hX : Kakeya.realRpowENN a p ≤ X)
    (hY : Kakeya.realRpowENN a q ≤ Y) :
    Kakeya.realRpowENN a (p + q) ≤ X * Y := by
  calc
    Kakeya.realRpowENN a (p + q) =
        Kakeya.realRpowENN a p *
          Kakeya.realRpowENN a q := by
      rw [realRpowENN_add' ha]
    _ ≤ X * Y := by gcongr

lemma absorption_lower_div
    {a p r : ℝ}
    (ha : 0 < a)
    {X C : ENNReal}
    (hX : Kakeya.realRpowENN a p ≤ X)
    (hCZero : C ≠ 0)
    (hCTop : C ≠ ⊤)
    (hC : C ≤ Kakeya.realRpowENN a (-r)) :
    Kakeya.realRpowENN a (p + r) ≤ X / C := by
  apply
    (ENNReal.le_div_iff_mul_le
      (Or.inl hCZero) (Or.inl hCTop)).mpr
  calc
    Kakeya.realRpowENN a (p + r) * C
        ≤ Kakeya.realRpowENN a (p + r) *
            Kakeya.realRpowENN a (-r) := by gcongr
    _ = Kakeya.realRpowENN a p := by
      rw [← realRpowENN_add' ha]
      congr 1
      ring
    _ ≤ X := hX

lemma absorption_inverse_upper
    {a p : ℝ}
    (ha : 0 < a)
    {X : ENNReal}
    (hX : Kakeya.realRpowENN a p ≤ X) :
    X⁻¹ ≤ Kakeya.realRpowENN a (-p) := by
  calc
    X⁻¹ ≤ (Kakeya.realRpowENN a p)⁻¹ := by
      exact ENNReal.inv_le_inv.mpr hX
    _ = Kakeya.realRpowENN a (-p) := by
      have hpos : 0 < a ^ p := Real.rpow_pos_of_pos ha p
      dsimp only [Kakeya.realRpowENN]
      calc
        (ENNReal.ofReal (a ^ p))⁻¹ =
            ENNReal.ofReal ((a ^ p)⁻¹) :=
          (ENNReal.ofReal_inv_of_pos hpos).symm
        _ = ENNReal.ofReal (a ^ (-p)) := by
          rw [Real.rpow_neg ha.le]

lemma absorption_upper_div_by_lower
    {a p q : ℝ}
    (ha : 0 < a)
    {X Y : ENNReal}
    (hX : X ≤ Kakeya.realRpowENN a (-p))
    (hY : Kakeya.realRpowENN a q ≤ Y) :
    X / Y ≤ Kakeya.realRpowENN a (-(p + q)) := by
  simp only [div_eq_mul_inv]
  exact absorption_upper_mul (p := p) (q := q) ha hX
    (absorption_inverse_upper (p := q) ha hY)

end Kakeya.Streamlined
