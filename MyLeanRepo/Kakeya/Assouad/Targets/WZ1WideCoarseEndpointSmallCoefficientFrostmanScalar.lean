import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointFrostmanSplitAssembly

/-!
PDF Proposition 8.9 wide branch: in the target-coefficient `< 2` regime,
prove the small-coefficient angle-denominator Frostman ball is admissible and
its explicit scalar coefficient is absorbed by the target projection power.
-/

namespace Kakeya.Assouad

theorem wz1_wide_coarse_endpoint_small_coefficient_frostman_scalar :
    WZ1WideCoarseEndpointSmallCoefficientFrostmanScalarStatement := by
  intro epsilon parameters hepsilon hepsilonOne
  let etaCap : ℝ :=
    epsilon * parameters.projectionLambda *
      parameters.zeta / 100
  have hetaCap : 0 < etaCap := by
    dsimp only [etaCap]
    exact div_pos
      (mul_pos
        (mul_pos hepsilon parameters.projectionLambda_pos)
        parameters.zeta_pos)
      (by norm_num)
  refine ⟨etaCap, hetaCap, ?_⟩
  intro eta heta hetaSmall
  let loss : ℝ :=
    wideCoarseEndpointFrostmanLoss parameters eta
  let widthExponent : ℝ :=
    3 * parameters.projectionLambda / 20
  let targetWidthExponent : ℝ :=
    parameters.zeta * (1 - parameters.projectionLambda / 2)
  let ballConstant : ℝ :=
    24 * (1 + Real.rpow 2 (1 / parameters.zeta))
  let coefficientConstant : ℝ := 8192 * ballConstant
  have hballConstant : 0 < ballConstant := by
    dsimp only [ballConstant]
    exact mul_pos (by norm_num)
      (add_pos_of_pos_of_nonneg (by norm_num)
        (Real.rpow_nonneg (by norm_num) _))
  have hcoefficientConstant : 0 < coefficientConstant := by
    dsimp only [coefficientConstant]
    exact mul_pos (by norm_num) hballConstant
  have hwidthGap :
      targetWidthExponent < widthExponent - loss := by
    have hgap :=
      wz1WideCoarseEndpoint_frostman_width_parameter_gap
        parameters hepsilon hepsilonOne heta
        (by simpa [etaCap] using hetaSmall)
    dsimp only [targetWidthExponent, widthExponent, loss] at *
    linarith
  rcases
      wideCoarseEndpoint_exists_delta_absorb_tau_power
        ballConstant hballConstant hepsilon
        (show (0 : ℝ) < widthExponent by
          dsimp only [widthExponent]
          exact div_pos
            (mul_pos (by norm_num)
              parameters.projectionLambda_pos)
            (by norm_num)) with
    ⟨deltaBall, hdeltaBall, hdeltaBallOne, hballAbsorb⟩
  rcases
      wideCoarseEndpoint_exists_delta_absorb_tau_power
        coefficientConstant hcoefficientConstant
        hepsilon hwidthGap with
    ⟨deltaCoefficient, hdeltaCoefficient,
      hdeltaCoefficientOne, hcoefficientAbsorb⟩
  let delta₀ := min deltaBall deltaCoefficient
  have hdelta₀ : 0 < delta₀ := by
    simp [delta₀, hdeltaBall, hdeltaCoefficient]
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans hdeltaBallOne
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta F G₁ G₂ ambient active H
    hdelta hdeltaSmall data input normal hnormal haxial
    hnotProjective hsmallCoefficient radius hradius _hradiusOne
    htarget
  let tau := delta / data.width
  let ballRadius :=
    wideCoarseEndpointSmallCoefficientFrostmanBallRadius
      data normal radius
  have htau : 0 < tau := div_pos hdelta data.width_pos
  have hradiusPos : 0 < radius := htau.trans_le hradius
  have hdeltaBallSmall : delta ≤ deltaBall :=
    hdeltaSmall.trans (min_le_left _ _)
  have hdeltaCoefficientSmall : delta ≤ deltaCoefficient :=
    hdeltaSmall.trans (min_le_right _ _)
  have hballTau :
      ballRadius ≤
        ballConstant * Real.rpow tau widthExponent := by
    simpa [ballRadius, ballConstant, tau, widthExponent] using
      wideCoarseEndpoint_smallCoefficient_frostmanBall_tau_upper
        hdelta hnormal haxial hnotProjective hsmallCoefficient
        hradius htarget
  have hballAbsorbAt :=
    hballAbsorb hdelta hdeltaBallSmall
      data.width_pos input.width_large
  have hballOneENN : ENNReal.ofReal ballRadius ≤ 1 := by
    calc
      ENNReal.ofReal ballRadius ≤
          ENNReal.ofReal ballConstant *
            Kakeya.realRpowENN tau widthExponent := by
        calc
          ENNReal.ofReal ballRadius ≤
              ENNReal.ofReal
                (ballConstant * Real.rpow tau widthExponent) :=
            ENNReal.ofReal_mono hballTau
          _ =
              ENNReal.ofReal ballConstant *
                Kakeya.realRpowENN tau widthExponent := by
            rw [ENNReal.ofReal_mul hballConstant.le]
            rfl
      _ ≤ Kakeya.realRpowENN tau 0 := hballAbsorbAt
      _ = 1 := by simp [Kakeya.realRpowENN]
  have hballOne : ballRadius ≤ 1 :=
    ENNReal.ofReal_le_one.mp hballOneENN
  refine ⟨hballOne, ?_⟩
  have hcoefficientBase :=
    wideCoarseEndpoint_frostmanCoefficient_upper
      (ballRadius := ballRadius)
      input hdelta hepsilon heta
  have hballPower :
      Kakeya.realRpowENN ballRadius 1 ≤
        ENNReal.ofReal ballConstant *
          Kakeya.realRpowENN tau widthExponent := by
    simp only [Kakeya.realRpowENN]
    calc
      ENNReal.ofReal (Real.rpow ballRadius 1) =
          ENNReal.ofReal ballRadius := by simp
      _ ≤
          ENNReal.ofReal
            (ballConstant * Real.rpow tau widthExponent) :=
        ENNReal.ofReal_mono hballTau
      _ =
          ENNReal.ofReal ballConstant *
            ENNReal.ofReal (Real.rpow tau widthExponent) := by
        rw [ENNReal.ofReal_mul hballConstant.le]
  have hcoefficientAbsorbAt :=
    hcoefficientAbsorb hdelta hdeltaCoefficientSmall
      data.width_pos input.width_large
  have htargetLower :=
    wideCoarseEndpoint_tau_power_le_target
      htau hradiusPos hradius parameters.zeta_pos
      (lambda := parameters.projectionLambda)
  have htargetIdentity :
      wideCoarseEndpointTargetCoefficient
          parameters data radius =
        Kakeya.realRpowENN tau
            (-(parameters.projectionLambda *
              parameters.zeta / 2)) *
          Kakeya.realRpowENN radius parameters.zeta := by
    change
      Kakeya.realRpowENN
          (Real.rpow tau
              (-(parameters.projectionLambda / 2)) *
            radius)
          parameters.zeta =
        Kakeya.realRpowENN tau
            (-(parameters.projectionLambda *
              parameters.zeta / 2)) *
          Kakeya.realRpowENN radius parameters.zeta
    rw [wideCoarseEndpoint_target_power_identity
      (lambda := parameters.projectionLambda / 2)
      (zeta := parameters.zeta)
      htau hradiusPos]
    congr 1
    ring
  rw [htargetIdentity]
  calc
    wideCoarseEndpointFrostmanCoefficient
        parameters input ballRadius
        ≤
      (8192 : ENNReal) *
        Kakeya.realRpowENN tau (-loss) *
        Kakeya.realRpowENN ballRadius 1 := by
          simpa [tau, loss, ballRadius] using hcoefficientBase
    _ ≤
      ENNReal.ofReal coefficientConstant *
        Kakeya.realRpowENN tau
          (widthExponent - loss) := by
            have hconstant :
                ENNReal.ofReal coefficientConstant =
                  (8192 : ENNReal) *
                    ENNReal.ofReal ballConstant := by
              simp [coefficientConstant, ENNReal.ofReal_mul,
                hballConstant.le]
            calc
              (8192 : ENNReal) *
                    Kakeya.realRpowENN tau (-loss) *
                    Kakeya.realRpowENN ballRadius 1
                  ≤
                (8192 : ENNReal) *
                  Kakeya.realRpowENN tau (-loss) *
                  (ENNReal.ofReal ballConstant *
                    Kakeya.realRpowENN tau widthExponent) := by
                      exact mul_le_mul_of_nonneg_left
                        hballPower
                        (by positivity)
              _ =
                ENNReal.ofReal coefficientConstant *
                  (Kakeya.realRpowENN tau widthExponent *
                    Kakeya.realRpowENN tau (-loss)) := by
                      rw [hconstant]
                      ac_rfl
              _ =
                ENNReal.ofReal coefficientConstant *
                  Kakeya.realRpowENN tau
                    (widthExponent - loss) := by
                      simpa only [sub_eq_add_neg] using
                        congrArg
                          (fun value : ENNReal =>
                            ENNReal.ofReal coefficientConstant * value)
                          (realRpowENN_add
                            htau widthExponent (-loss)).symm
    _ ≤
      Kakeya.realRpowENN tau targetWidthExponent :=
        hcoefficientAbsorbAt
    _ ≤
      Kakeya.realRpowENN tau
          (-(parameters.projectionLambda *
            parameters.zeta / 2)) *
        Kakeya.realRpowENN radius parameters.zeta := by
      simpa [targetWidthExponent] using htargetLower

end Kakeya.Assouad
