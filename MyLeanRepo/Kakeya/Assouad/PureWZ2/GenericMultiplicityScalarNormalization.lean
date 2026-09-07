import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.ExtremalHelpers

/-!
# Quotient-free multiplicity scalar normalization

The final owner-parent construction only needs two numerical consequences of
the strong paper estimates:

* the coarse cardinality floor makes the unit coarse point cap
  cardinality-normalized; and
* a strong absolute fine point cap, together with the corresponding fiber
  cardinality floor, gives the public relative multiplicity cap.

These statements carry no historical quotient or prepared-family types.
-/

noncomputable section

namespace Kakeya.Assouad

theorem pureWZ2_cardinality_lower_of_power_product
    {scale strongLoss : ℝ}
    {cardinality : ENNReal}
    (hscale : 0 < scale)
    (hproduct :
      (1 : ENNReal) ≤
        Kakeya.realRpowENN scale (2 - 2 * strongLoss) *
          cardinality) :
    Kakeya.realRpowENN scale (-2 + 2 * strongLoss) ≤
      cardinality := by
  let power :=
    Kakeya.realRpowENN scale (2 - 2 * strongLoss)
  have power_pos : 0 < power := by
    exact ENNReal.ofReal_pos.mpr <|
      Real.rpow_pos_of_pos hscale _
  have power_ne_top : power ≠ ⊤ := by
    simp [power, Kakeya.realRpowENN]
  have inverse_le : power⁻¹ ≤ cardinality := by
    calc
      power⁻¹ = (1 : ENNReal) * power⁻¹ := by simp
      _ ≤ (power * cardinality) * power⁻¹ := by
        gcongr
      _ = cardinality * (power * power⁻¹) := by ring
      _ = cardinality := by
        rw [ENNReal.mul_inv_cancel power_pos.ne' power_ne_top]
        simp
  have inverse_eq :
      power⁻¹ =
        Kakeya.realRpowENN scale (-2 + 2 * strongLoss) := by
    have real_pos :
        0 < Real.rpow scale (2 - 2 * strongLoss) :=
      Real.rpow_pos_of_pos hscale _
    calc
      power⁻¹ =
          ENNReal.ofReal
            ((Real.rpow scale (2 - 2 * strongLoss))⁻¹) := by
        dsimp only [power, Kakeya.realRpowENN]
        exact (ENNReal.ofReal_inv_of_pos real_pos).symm
      _ =
          ENNReal.ofReal
            (Real.rpow scale (-(2 - 2 * strongLoss))) := by
        exact congrArg ENNReal.ofReal
          (Real.rpow_neg hscale.le
            (2 - 2 * strongLoss)).symm
      _ =
          Kakeya.realRpowENN scale
            (-2 + 2 * strongLoss) := by
        congr 2
        ring
  rw [← inverse_eq]
  exact inverse_le

theorem pureWZ2_coarse_multiplicity_scalar_of_cardinality_lower
    {rho sigma strongLoss outputLoss : ℝ}
    {cardinality : ENNReal}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hsigma : 0 < sigma)
    (hstrongLoss : 0 ≤ strongLoss)
    (hbudget : 3 * strongLoss ≤ outputLoss)
    (hcardinality :
      Kakeya.realRpowENN rho (-2 + 2 * strongLoss) ≤
        cardinality) :
    (1 : ENNReal) ≤
      Kakeya.realRpowENN rho (2 - sigma - outputLoss) *
        cardinality := by
  have hexponent :
      -sigma - outputLoss + 2 * strongLoss ≤ 0 := by
    linarith
  have hpower :
      (1 : ENNReal) ≤
        Kakeya.realRpowENN rho
          (-sigma - outputLoss + 2 * strongLoss) := by
    simpa [Kakeya.realRpowENN] using
      realRpowENN_antitone hrho hrhoOne hexponent
  calc
    (1 : ENNReal) ≤
        Kakeya.realRpowENN rho
          (-sigma - outputLoss + 2 * strongLoss) :=
      hpower
    _ =
        Kakeya.realRpowENN rho (2 - sigma - outputLoss) *
          Kakeya.realRpowENN rho (-2 + 2 * strongLoss) := by
      rw [← realRpowENN_add hrho]
      congr 1
      ring
    _ ≤
        Kakeya.realRpowENN rho (2 - sigma - outputLoss) *
          cardinality := by
      gcongr

theorem pureWZ2_fiber_cap_upper_of_strong_cap_and_cardinality_lower
    {scale sigma strongLoss outputLoss : ℝ}
    {cap cardinality : ENNReal}
    (hscale : 0 < scale)
    (hscaleOne : scale ≤ 1)
    (hbudget : 3 * strongLoss ≤ outputLoss)
    (hcap :
      cap ≤
        Kakeya.realRpowENN scale (-sigma - strongLoss))
    (hcardinality :
      Kakeya.realRpowENN scale (-2 + 2 * strongLoss) ≤
        cardinality) :
    cap ≤
      Kakeya.realRpowENN scale (2 - sigma - outputLoss) *
        cardinality := by
  have hcardinalityPublic :
      Kakeya.realRpowENN scale
          (-2 + outputLoss - strongLoss) ≤
        cardinality := by
    exact
      (realRpowENN_antitone hscale hscaleOne (by linarith)).trans
        hcardinality
  calc
    cap ≤
        Kakeya.realRpowENN scale (-sigma - strongLoss) :=
      hcap
    _ =
        Kakeya.realRpowENN scale (2 - sigma - outputLoss) *
          Kakeya.realRpowENN scale
            (-2 + outputLoss - strongLoss) := by
      rw [← realRpowENN_add hscale]
      congr 1
      ring
    _ ≤
        Kakeya.realRpowENN scale (2 - sigma - outputLoss) *
          cardinality := by
      gcongr

end Kakeya.Assouad

end
