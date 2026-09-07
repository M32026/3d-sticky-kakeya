import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockRepresentativeCinematicStatements

/-!
# Algebraic simplification of the Lemma 7.12 cubic volume bound

Pure `ENNReal` algebra for the representative cinematic pullback formula.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
Rewrite the nested cubic Hölder/PYZ lower bound in flat product form.
-/
lemma parameterBlockPYZ_volume_simplification
    (translations mass fiberCap : ENNReal)
    (delta pyzLoss : ℝ)
    (htranslations : 0 < translations)
    (htranslations_top : translations ≠ ⊤)
    (hmass : 0 < mass)
    (hmass_top : mass ≠ ⊤)
    (hfiberCap : 0 < fiberCap)
    (hfiberCap_top : fiberCap ≠ ⊤)
    (hdelta : 0 < delta)
    (hpyzLoss : 0 < pyzLoss) :
    (((translations * mass / ENNReal.ofReal (20 * delta)) /
        (fiberCap *
          ENNReal.ofReal (Real.rpow delta (-pyzLoss)))) ^ 3) /
        translations =
      translations ^ 2 * mass ^ 3 /
        ((ENNReal.ofReal (20 * delta)) ^ 3 *
          fiberCap ^ 3 *
          ENNReal.ofReal
            (Real.rpow delta (-3 * pyzLoss))) := by
  let deltaFactor : ENNReal :=
    ENNReal.ofReal (20 * delta)
  let lossFactor : ENNReal :=
    ENNReal.ofReal (Real.rpow delta (-pyzLoss))
  have hdeltaFactor_zero :
      deltaFactor ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hdeltaFactor_top :
      deltaFactor ≠ ⊤ := ENNReal.ofReal_ne_top
  have hloss_pos :
      0 < Real.rpow delta (-pyzLoss) :=
    Real.rpow_pos_of_pos hdelta _
  have hlossFactor_zero :
      lossFactor ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hloss_pos).ne'
  have hlossFactor_top :
      lossFactor ≠ ⊤ := ENNReal.ofReal_ne_top
  have htranslations_zero : translations ≠ 0 :=
    htranslations.ne'
  have hfiberCap_zero : fiberCap ≠ 0 :=
    hfiberCap.ne'
  have hloss_cube :
      lossFactor ^ 3 =
        ENNReal.ofReal
          (Real.rpow delta (-3 * pyzLoss)) := by
    have hreal :
        (Real.rpow delta (-pyzLoss)) ^ 3 =
          Real.rpow delta (-3 * pyzLoss) := by
      calc
        (Real.rpow delta (-pyzLoss)) ^ 3 =
            Real.rpow delta ((3 : ℝ) * (-pyzLoss)) := by
          exact rpow_nat_pow hdelta (-pyzLoss) 3
        _ = Real.rpow delta (-3 * pyzLoss) := by
          congr 1
          ring
    simp only [lossFactor, pow_three]
    have hmul :
        ENNReal.ofReal (Real.rpow delta (-pyzLoss)) *
            (ENNReal.ofReal (Real.rpow delta (-pyzLoss)) *
              ENNReal.ofReal (Real.rpow delta (-pyzLoss))) =
          ENNReal.ofReal
            ((Real.rpow delta (-pyzLoss)) ^ 3) := by
      rw [← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      simp [pow_three]
    rw [hmul, hreal]
  have hdenom_inv :
      (deltaFactor * fiberCap * lossFactor)⁻¹ =
        deltaFactor⁻¹ * fiberCap⁻¹ * lossFactor⁻¹ := by
    rw [ENNReal.mul_inv
      (Or.inl
        (mul_ne_zero hdeltaFactor_zero hfiberCap_zero))
      (Or.inl
        (ENNReal.mul_ne_top
          hdeltaFactor_top hfiberCap_top))]
    rw [ENNReal.mul_inv
      (Or.inl hdeltaFactor_zero)
      (Or.inl hdeltaFactor_top)]
  have hcombine :
      (translations * mass / deltaFactor) /
          (fiberCap * lossFactor) =
        (translations * mass) /
          (deltaFactor * fiberCap * lossFactor) := by
    simp only [div_eq_mul_inv]
    rw [ENNReal.mul_inv
      (Or.inl hfiberCap_zero)
      (Or.inl hfiberCap_top),
      hdenom_inv]
    ring
  have hdenom_zero :
      deltaFactor * fiberCap * lossFactor ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero hdeltaFactor_zero hfiberCap_zero)
      hlossFactor_zero
  have hdenom_top :
      deltaFactor * fiberCap * lossFactor ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        hdeltaFactor_top hfiberCap_top)
      hlossFactor_top
  have hinv_cube :
      (deltaFactor * fiberCap * lossFactor)⁻¹ ^ 3 =
        ((deltaFactor * fiberCap * lossFactor) ^ 3)⁻¹ := by
    set denominator :=
      deltaFactor * fiberCap * lossFactor
    have hsquare :
        denominator⁻¹ ^ 2 =
          (denominator ^ 2)⁻¹ := by
      rw [pow_two, pow_two,
        ENNReal.mul_inv
          (Or.inl hdenom_zero)
          (Or.inr hdenom_zero)]
    calc
      denominator⁻¹ ^ 3 =
          denominator⁻¹ ^ 2 * denominator⁻¹ := by
        rw [pow_succ]
      _ = (denominator ^ 2)⁻¹ *
          denominator⁻¹ := by rw [hsquare]
      _ = (denominator ^ 2 *
          denominator)⁻¹ := by
        rw [ENNReal.mul_inv
          (Or.inl (pow_ne_zero 2 hdenom_zero))
          (Or.inr hdenom_zero)]
      _ = (denominator ^ 3)⁻¹ := by
        congr 1
        ring
  have hdivision_cube :
      ((translations * mass) /
          (deltaFactor * fiberCap * lossFactor)) ^ 3 =
        (translations * mass) ^ 3 /
          (deltaFactor * fiberCap * lossFactor) ^ 3 := by
    simp only [div_eq_mul_inv, mul_pow]
    rw [hinv_cube]
    congr 1
    ring_nf
  have htranslations_cancel :
      translations ^ 3 / translations =
        translations ^ 2 := by
    simp only [div_eq_mul_inv]
    have hcancel :
        translations * translations⁻¹ = 1 :=
      ENNReal.mul_inv_cancel
        htranslations_zero htranslations_top
    calc
      translations ^ 3 * translations⁻¹ =
          translations ^ 2 *
            (translations * translations⁻¹) := by
        ring
      _ = translations ^ 2 := by rw [hcancel, mul_one]
  calc
    (((translations * mass /
          ENNReal.ofReal (20 * delta)) /
        (fiberCap *
          ENNReal.ofReal
            (Real.rpow delta (-pyzLoss)))) ^ 3) /
        translations =
      (((translations * mass /
          deltaFactor) /
        (fiberCap * lossFactor)) ^ 3) /
        translations := by rfl
    _ =
      (((translations * mass) /
        (deltaFactor * fiberCap * lossFactor)) ^ 3) /
        translations := by rw [hcombine]
    _ =
      ((translations * mass) ^ 3 /
        (deltaFactor * fiberCap * lossFactor) ^ 3) /
        translations := by rw [hdivision_cube]
    _ =
      translations ^ 2 * mass ^ 3 /
        (deltaFactor ^ 3 *
          fiberCap ^ 3 * lossFactor ^ 3) := by
      simp only [mul_pow, div_eq_mul_inv]
      rw [show
        translations ^ 3 * mass ^ 3 *
            (deltaFactor ^ 3 *
              fiberCap ^ 3 * lossFactor ^ 3)⁻¹ *
            translations⁻¹ =
          (translations ^ 3 *
            translations⁻¹) *
            (mass ^ 3 *
              (deltaFactor ^ 3 *
                fiberCap ^ 3 *
                  lossFactor ^ 3)⁻¹) by ring,
        show
          translations ^ 3 *
              translations⁻¹ =
            translations ^ 3 /
              translations by rfl,
        htranslations_cancel]
      ring
    _ =
      translations ^ 2 * mass ^ 3 /
        ((ENNReal.ofReal (20 * delta)) ^ 3 *
          fiberCap ^ 3 *
          ENNReal.ofReal
            (Real.rpow delta (-3 * pyzLoss))) := by
      rw [hloss_cube]

end Kakeya.Assouad
