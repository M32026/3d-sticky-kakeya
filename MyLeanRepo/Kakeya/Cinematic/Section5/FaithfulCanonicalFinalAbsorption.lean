import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalActualLocalVolume
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulScaleAbsorption

/-!
# Final scale absorption for the faithful canonical assembly

These two lemmas absorb the fixed common local coefficient after the physical
Katz--Tao summation and dominate the cubic contribution of a small ambient
bin. The dyadic retention loss is already part of the scaled local estimate
and is therefore counted exactly once.
-/

namespace Kakeya.Cinematic

lemma faithful_canonical_scaled_local_ambient_absorption
    (localConstant geometricConstant scaleFactor D C_KT loss epsilon : ℝ)
    (hlocalConstant : 0 < localConstant)
    (hgeometricConstant : 0 < geometricConstant)
    (hscaleFactor : 1 ≤ scaleFactor)
    (hD : 0 < D)
    (hC_KT : 0 < C_KT)
    (hloss : 0 ≤ loss)
    (hlossTarget : loss < epsilon) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ {delta mu : ℝ},
        0 < delta →
        delta ≤ delta₀ →
        0 ≤ mu →
        localConstant *
              Real.rpow (scaleFactor * delta) (-loss) *
              (geometricConstant * (scaleFactor * delta)) *
              Real.rpow mu (-3 / 2 : ℝ) *
              (D ^ 3 * (C_KT / delta)) ≤
            Real.rpow delta (-epsilon) *
              Real.rpow mu (-3 / 2 : ℝ) := by
  let coefficient :=
    localConstant * geometricConstant * scaleFactor * D ^ 3 * C_KT
  have hscaleFactorPos : 0 < scaleFactor :=
    zero_lt_one.trans_le hscaleFactor
  have hcoefficient : 0 < coefficient := by
    dsimp only [coefficient]
    positivity
  rcases polynomial_loss_absorption
      coefficient loss 1 epsilon hcoefficient (by simpa using hlossTarget) with
    ⟨delta₀, hdelta₀, hdelta₀One, hmain⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta mu hdelta hdeltaBound hmu
  have hdeltaScaled : delta ≤ scaleFactor * delta := by
    nlinarith
  have hpower :
      Real.rpow (scaleFactor * delta) (-loss) ≤
        Real.rpow delta (-loss) :=
    Real.rpow_le_rpow_of_nonpos hdelta hdeltaScaled (by linarith)
  have hmuPower :
      0 ≤ Real.rpow mu (-3 / 2 : ℝ) :=
    Real.rpow_nonneg hmu _
  have hambient :
      0 ≤ D ^ 3 * (C_KT / delta) := by positivity
  calc
    localConstant *
          Real.rpow (scaleFactor * delta) (-loss) *
          (geometricConstant * (scaleFactor * delta)) *
          Real.rpow mu (-3 / 2 : ℝ) *
          (D ^ 3 * (C_KT / delta)) ≤
        localConstant *
          Real.rpow delta (-loss) *
          (geometricConstant * (scaleFactor * delta)) *
          Real.rpow mu (-3 / 2 : ℝ) *
          (D ^ 3 * (C_KT / delta)) := by
      gcongr
    _ =
        coefficient * Real.rpow delta (-loss) *
          Real.rpow mu (-3 / 2 : ℝ) := by
      dsimp only [coefficient]
      field_simp [hdelta.ne']
    _ ≤
        Real.rpow delta (-epsilon) *
          Real.rpow mu (-3 / 2 : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (by simpa using hmain hdelta hdeltaBound) hmuPower

lemma faithful_canonical_scaled_small_bin_absorption
    (localConstant geometricConstant scaleFactor C_KT loss outerExponent : ℝ)
    (hlocalConstant : 0 < localConstant)
    (hgeometricConstant : 0 < geometricConstant)
    (hscaleFactor : 0 < scaleFactor)
    (hC_KT : 0 < C_KT)
    (hgap : 0 < 1 / 2 + loss - outerExponent) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ {delta mu outerLoss : ℝ},
        0 < delta →
        scaleFactor * delta ≤ delta₀ →
        0 < mu →
        mu ≤ C_KT / delta →
        0 ≤ outerLoss →
        outerLoss ≤
          Real.rpow (scaleFactor * delta) (-outerExponent) →
        outerLoss * (scaleFactor * delta) ^ 3 ≤
          localConstant *
            Real.rpow (scaleFactor * delta) (-loss) *
            (geometricConstant * (scaleFactor * delta)) *
            Real.rpow mu (-3 / 2 : ℝ) := by
  let ratio :=
    Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) /
      (localConstant * geometricConstant)
  have hdenominator :
      0 < localConstant * geometricConstant :=
    mul_pos hlocalConstant hgeometricConstant
  have hratio : 0 < ratio := by
    dsimp only [ratio]
    exact div_pos
      (Real.rpow_pos_of_pos (mul_pos hscaleFactor hC_KT) _)
      (mul_pos hlocalConstant hgeometricConstant)
  rcases fixed_constant_rpow_absorption ratio
      (1 / 2 + loss - outerExponent) hratio hgap with
    ⟨delta₀, hdelta₀, hdelta₀One, hsmall⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta mu outerLoss hdelta hdeltaBound hmu hmuUpper
    houterLoss houter
  let deltaVert := scaleFactor * delta
  have hdeltaVert : 0 < deltaVert := by
    dsimp only [deltaVert]
    positivity
  have hlocalKT : 0 < scaleFactor * C_KT :=
    mul_pos hscaleFactor hC_KT
  have hmuUpper' :
      mu ≤ (scaleFactor * C_KT) / deltaVert := by
    dsimp only [deltaVert]
    calc
      mu ≤ C_KT / delta := hmuUpper
      _ = (scaleFactor * C_KT) / (scaleFactor * delta) := by
        field_simp [hscaleFactor.ne', hdelta.ne']
      _ = (scaleFactor * C_KT) / deltaVert := rfl
  have hmuPower :
      Real.rpow mu (3 / 2 : ℝ) ≤
        Real.rpow ((scaleFactor * C_KT) / deltaVert)
          (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hmu.le hmuUpper' (by norm_num)
  have hquotientPower :
      Real.rpow ((scaleFactor * C_KT) / deltaVert)
          (3 / 2 : ℝ) =
        Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) *
          Real.rpow deltaVert (-3 / 2 : ℝ) := by
    calc
      Real.rpow ((scaleFactor * C_KT) / deltaVert)
            (3 / 2 : ℝ) =
          Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) /
            Real.rpow deltaVert (3 / 2 : ℝ) :=
        Real.div_rpow hlocalKT.le hdeltaVert.le _
      _ =
          Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) *
            Real.rpow deltaVert (-3 / 2 : ℝ) := by
        rw [div_eq_mul_inv]
        have hinverse :
            (Real.rpow deltaVert (3 / 2 : ℝ))⁻¹ =
              Real.rpow deltaVert (-3 / 2 : ℝ) := by
          calc
            (Real.rpow deltaVert (3 / 2 : ℝ))⁻¹ =
                Real.rpow deltaVert (-(3 / 2 : ℝ)) :=
              (Real.rpow_neg hdeltaVert.le (3 / 2 : ℝ)).symm
            _ = Real.rpow deltaVert (-3 / 2 : ℝ) := by
              congr 1
              ring
        rw [hinverse]
  have hleftScaled :
      outerLoss * deltaVert ^ 3 *
          Real.rpow mu (3 / 2 : ℝ) ≤
        Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) *
          Real.rpow deltaVert
            (3 / 2 - outerExponent) := by
    calc
      outerLoss * deltaVert ^ 3 *
            Real.rpow mu (3 / 2 : ℝ) ≤
          Real.rpow deltaVert (-outerExponent) *
            deltaVert ^ 3 *
            Real.rpow mu (3 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right houter
            (pow_nonneg hdeltaVert.le 3))
          (Real.rpow_nonneg hmu.le _)
      _ ≤
          Real.rpow deltaVert (-outerExponent) *
            deltaVert ^ 3 *
            Real.rpow ((scaleFactor * C_KT) / deltaVert)
              (3 / 2 : ℝ) := by
        have hfactor :
            0 ≤ Real.rpow deltaVert (-outerExponent) *
              deltaVert ^ 3 :=
          mul_nonneg
            (Real.rpow_nonneg hdeltaVert.le _)
            (pow_nonneg hdeltaVert.le 3)
        exact mul_le_mul_of_nonneg_left hmuPower hfactor
      _ =
          Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) *
            Real.rpow deltaVert
              (3 / 2 - outerExponent) := by
        rw [hquotientPower]
        have hpowers :
            Real.rpow deltaVert (-outerExponent) *
                deltaVert ^ 3 *
                Real.rpow deltaVert (-3 / 2 : ℝ) =
              Real.rpow deltaVert
                (3 / 2 - outerExponent) := by
          have hnatPower :
              deltaVert ^ (3 : ℕ) =
                Real.rpow deltaVert (3 : ℝ) :=
            (Real.rpow_natCast deltaVert 3).symm
          calc
            Real.rpow deltaVert (-outerExponent) *
                  deltaVert ^ 3 *
                  Real.rpow deltaVert (-3 / 2 : ℝ) =
                (Real.rpow deltaVert (-outerExponent) *
                    Real.rpow deltaVert (3 : ℝ)) *
                  Real.rpow deltaVert (-3 / 2 : ℝ) := by
              rw [hnatPower]
            _ =
                Real.rpow deltaVert
                    ((-outerExponent) + 3) *
                  Real.rpow deltaVert (-3 / 2 : ℝ) := by
              exact congrArg
                (fun value =>
                  value * Real.rpow deltaVert (-3 / 2 : ℝ))
                (Real.rpow_add hdeltaVert
                  (-outerExponent) 3).symm
            _ =
                Real.rpow deltaVert
                  (((-outerExponent) + 3) + (-3 / 2)) := by
              exact (Real.rpow_add hdeltaVert
                ((-outerExponent) + 3) (-3 / 2)).symm
            _ =
                Real.rpow deltaVert
                  (3 / 2 - outerExponent) := by
              congr 1
              ring
        calc
          Real.rpow deltaVert (-outerExponent) *
                deltaVert ^ 3 *
                (Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) *
                  Real.rpow deltaVert (-3 / 2 : ℝ)) =
              Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) *
                (Real.rpow deltaVert (-outerExponent) *
                  deltaVert ^ 3 *
                  Real.rpow deltaVert (-3 / 2 : ℝ)) := by ring
          _ =
              Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) *
                Real.rpow deltaVert
                  (3 / 2 - outerExponent) := by
            rw [hpowers]
  have hsmall' :
      Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) *
          Real.rpow deltaVert
            (1 / 2 + loss - outerExponent) ≤
        localConstant * geometricConstant := by
    have hraw :=
      hsmall hdeltaVert (show deltaVert ≤ delta₀ from hdeltaBound)
    dsimp only [ratio] at hraw
    calc
      Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) *
            Real.rpow deltaVert
              (1 / 2 + loss - outerExponent) =
          (Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) /
              (localConstant * geometricConstant) *
            Real.rpow deltaVert
              (1 / 2 + loss - outerExponent)) *
            (localConstant * geometricConstant) := by
        field_simp [hdenominator.ne']
      _ ≤ 1 * (localConstant * geometricConstant) := by
        gcongr
      _ = localConstant * geometricConstant := one_mul _
  have hcoefficientBound :
      Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) *
          Real.rpow deltaVert
            (3 / 2 - outerExponent) ≤
        localConstant * geometricConstant *
          Real.rpow deltaVert (1 - loss) := by
    have hexponent :
        (1 / 2 + loss - outerExponent) + (1 - loss) =
          3 / 2 - outerExponent := by ring
    calc
      Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) *
            Real.rpow deltaVert
              (3 / 2 - outerExponent) =
          (Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) *
              Real.rpow deltaVert
                (1 / 2 + loss - outerExponent)) *
            Real.rpow deltaVert (1 - loss) := by
        rw [← hexponent]
        calc
          Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) *
                Real.rpow deltaVert
                  ((1 / 2 + loss - outerExponent) + (1 - loss)) =
              Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) *
                (Real.rpow deltaVert
                    (1 / 2 + loss - outerExponent) *
                  Real.rpow deltaVert (1 - loss)) := by
            change
              Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) *
                    deltaVert ^
                      ((1 / 2 + loss - outerExponent) + (1 - loss)) =
                Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) *
                  (deltaVert ^ (1 / 2 + loss - outerExponent) *
                    deltaVert ^ (1 - loss))
            rw [Real.rpow_add hdeltaVert]
          _ =
              (Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) *
                  Real.rpow deltaVert
                    (1 / 2 + loss - outerExponent)) *
                Real.rpow deltaVert (1 - loss) := by ring
      _ ≤
          (localConstant * geometricConstant) *
            Real.rpow deltaVert (1 - loss) := by
        exact mul_le_mul_of_nonneg_right hsmall'
          (Real.rpow_nonneg hdeltaVert.le _)
  have hrightScaled :
      localConstant * geometricConstant *
            Real.rpow deltaVert (1 - loss) =
        (localConstant *
            Real.rpow deltaVert (-loss) *
            (geometricConstant * deltaVert) *
            Real.rpow mu (-3 / 2 : ℝ)) *
          Real.rpow mu (3 / 2 : ℝ) := by
    have hmuCancel :
        Real.rpow mu (-3 / 2 : ℝ) *
            Real.rpow mu (3 / 2 : ℝ) = 1 := by
      calc
        Real.rpow mu (-3 / 2 : ℝ) *
              Real.rpow mu (3 / 2 : ℝ) =
            Real.rpow mu ((-3 / 2 : ℝ) + 3 / 2) :=
          (Real.rpow_add hmu _ _).symm
        _ = 1 := by norm_num
    have hdeltaPower :
        Real.rpow deltaVert (-loss) * deltaVert =
          Real.rpow deltaVert (1 - loss) := by
      calc
        Real.rpow deltaVert (-loss) * deltaVert =
            Real.rpow deltaVert (-loss) *
              Real.rpow deltaVert 1 := by
          exact congrArg
            (fun value => Real.rpow deltaVert (-loss) * value)
            (Real.rpow_one deltaVert).symm
        _ = Real.rpow deltaVert ((-loss) + 1) :=
          (Real.rpow_add hdeltaVert _ _).symm
        _ = Real.rpow deltaVert (1 - loss) := by
          congr 1
          ring
    calc
      localConstant * geometricConstant *
            Real.rpow deltaVert (1 - loss) =
          localConstant * geometricConstant *
            Real.rpow deltaVert (1 - loss) * 1 := by ring
      _ =
          localConstant * geometricConstant *
            (Real.rpow deltaVert (-loss) * deltaVert) *
            (Real.rpow mu (-3 / 2 : ℝ) *
              Real.rpow mu (3 / 2 : ℝ)) := by
        rw [hdeltaPower, hmuCancel]
      _ =
          (localConstant *
              Real.rpow deltaVert (-loss) *
              (geometricConstant * deltaVert) *
              Real.rpow mu (-3 / 2 : ℝ)) *
            Real.rpow mu (3 / 2 : ℝ) := by ring
  have hscaled :
      (outerLoss * deltaVert ^ 3) *
          Real.rpow mu (3 / 2 : ℝ) ≤
        (localConstant *
            Real.rpow deltaVert (-loss) *
            (geometricConstant * deltaVert) *
            Real.rpow mu (-3 / 2 : ℝ)) *
          Real.rpow mu (3 / 2 : ℝ) := by
    calc
      (outerLoss * deltaVert ^ 3) *
            Real.rpow mu (3 / 2 : ℝ) ≤
          Real.rpow (scaleFactor * C_KT) (3 / 2 : ℝ) *
            Real.rpow deltaVert
              (3 / 2 - outerExponent) := hleftScaled
      _ ≤
          localConstant * geometricConstant *
            Real.rpow deltaVert (1 - loss) := hcoefficientBound
      _ =
          (localConstant *
              Real.rpow deltaVert (-loss) *
              (geometricConstant * deltaVert) *
              Real.rpow mu (-3 / 2 : ℝ)) *
            Real.rpow mu (3 / 2 : ℝ) := hrightScaled
  have hmuPowerPos : 0 < Real.rpow mu (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hmu _
  have hresult :=
    le_of_mul_le_mul_right hscaled hmuPowerPos
  simpa only [deltaVert] using hresult

end Kakeya.Cinematic
