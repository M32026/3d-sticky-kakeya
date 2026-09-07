import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointFrostmanSplitAssembly

/-!
PDF Proposition 8.9 wide branch: in the target-coefficient `< 2` regime,
prove the fixed-angle Frostman ball is admissible and its explicit scalar
coefficient is absorbed by the target projection power.
-/

namespace Kakeya.Assouad

theorem wz1_wide_coarse_endpoint_projective_frostman_scalar :
    WZ1WideCoarseEndpointProjectiveFrostmanScalarStatement := by
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
  let widthExponent : ℝ := 3 * parameters.projectionLambda / 20
  let radiusExponent : ℝ := parameters.projectionLambda / 2
  let targetWidthExponent : ℝ :=
    parameters.zeta * (1 - parameters.projectionLambda / 2)
  let targetRadiusExponent : ℝ :=
    -(parameters.projectionLambda * parameters.zeta / 2)
  let radiusConstant : ℝ :=
    24 * Real.rpow 2 (1 / parameters.zeta)
  let radiusLossConstant : ℝ :=
    8192 * 24 *
      Real.rpow 2 ((1 - parameters.zeta) / parameters.zeta)
  let widthLossConstant : ℝ := 8192 * 24
  have hwidthExponent : 0 < widthExponent := by
    dsimp only [widthExponent]
    exact div_pos
      (mul_pos (by norm_num) parameters.projectionLambda_pos)
      (by norm_num)
  have hradiusExponent : 0 < radiusExponent := by
    dsimp only [radiusExponent]
    exact div_pos parameters.projectionLambda_pos (by norm_num)
  have hradiusConstant : 0 < radiusConstant := by
    dsimp only [radiusConstant]
    exact mul_pos
      (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hradiusLossConstant : 0 < radiusLossConstant := by
    dsimp only [radiusLossConstant]
    exact mul_pos
      (mul_pos (by norm_num) (by norm_num))
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hwidthLossConstant : 0 < widthLossConstant := by
    norm_num [widthLossConstant]
  have hwidthGap :
      targetWidthExponent < widthExponent - loss := by
    have hgap :=
      wz1WideCoarseEndpoint_frostman_width_parameter_gap
        parameters hepsilon hepsilonOne heta
        (by simpa [etaCap] using hetaSmall)
    dsimp only [targetWidthExponent, widthExponent, loss] at *
    linarith
  have hradiusGap :
      targetRadiusExponent <
        -loss + radiusExponent * (1 - parameters.zeta) := by
    have hgap :=
      wz1WideCoarseEndpoint_frostman_radius_parameter_gap
        parameters hepsilon hepsilonOne heta
        (by simpa [etaCap] using hetaSmall)
    dsimp only [targetRadiusExponent, radiusExponent, loss] at *
    linarith
  rcases
      wideCoarseEndpoint_exists_delta_absorb_tau_power
        24 (by norm_num) hepsilon
        (show (0 : ℝ) < widthExponent by exact hwidthExponent) with
    ⟨deltaBallWidth, hdeltaBallWidth,
      hdeltaBallWidthOne, hballWidth⟩
  rcases
      wideCoarseEndpoint_exists_delta_absorb_tau_power
        radiusConstant hradiusConstant hepsilon
        (show (0 : ℝ) < radiusExponent by exact hradiusExponent) with
    ⟨deltaBallRadius, hdeltaBallRadius,
      hdeltaBallRadiusOne, hballRadius⟩
  rcases
      wideCoarseEndpoint_exists_delta_absorb_tau_power
        widthLossConstant hwidthLossConstant hepsilon hwidthGap with
    ⟨deltaCoefficientWidth, hdeltaCoefficientWidth,
      hdeltaCoefficientWidthOne, hcoefficientWidth⟩
  rcases
      wideCoarseEndpoint_exists_delta_absorb_tau_power
        radiusLossConstant hradiusLossConstant hepsilon hradiusGap with
    ⟨deltaCoefficientRadius, hdeltaCoefficientRadius,
      hdeltaCoefficientRadiusOne, hcoefficientRadius⟩
  let delta₀ :=
    min deltaBallWidth
      (min deltaBallRadius
        (min deltaCoefficientWidth deltaCoefficientRadius))
  have hdelta₀ : 0 < delta₀ := by
    simp [delta₀, hdeltaBallWidth, hdeltaBallRadius,
      hdeltaCoefficientWidth, hdeltaCoefficientRadius]
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans hdeltaBallWidthOne
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta F G₁ G₂ ambient active H
    hdelta hdeltaSmall data input normal hnormal haxial
    _hprojective hsmallWidth radius hradius _hradiusOne htarget
  let tau := delta / data.width
  let ballRadius :=
    wideCoarseEndpointProjectiveFrostmanBallRadius
      data normal radius
  have htau : 0 < tau :=
    div_pos hdelta data.width_pos
  have hradiusPos : 0 < radius :=
    htau.trans_le hradius
  have hdeltaBallWidthSmall : delta ≤ deltaBallWidth :=
    hdeltaSmall.trans (min_le_left _ _)
  have hdeltaBallRadiusSmall : delta ≤ deltaBallRadius :=
    hdeltaSmall.trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaCoefficientWidthSmall :
      delta ≤ deltaCoefficientWidth :=
    hdeltaSmall.trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hdeltaCoefficientRadiusSmall :
      delta ≤ deltaCoefficientRadius :=
    hdeltaSmall.trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  have hballUpper :
      ballRadius ≤ 24 * max data.width radius := by
    simpa [ballRadius] using
      wideCoarseEndpoint_projective_frostmanBall_upper
        hdelta hnormal haxial hradius
  have hradiusBound :
      radius <
        Real.rpow 2 (1 / parameters.zeta) *
          Real.rpow tau radiusExponent := by
    apply
      wideCoarseEndpoint_radius_lt_of_target_lt_two
        htau hradiusPos parameters.zeta_pos
    simpa [wideCoarseEndpointTargetCoefficient,
      tau, radiusExponent] using htarget
  have htargetIdentity :
      wideCoarseEndpointTargetCoefficient
          parameters data radius =
        Kakeya.realRpowENN tau targetRadiusExponent *
          Kakeya.realRpowENN radius parameters.zeta := by
    change
      Kakeya.realRpowENN
          (Real.rpow tau
              (-(parameters.projectionLambda / 2)) *
            radius)
          parameters.zeta =
        Kakeya.realRpowENN tau targetRadiusExponent *
          Kakeya.realRpowENN radius parameters.zeta
    rw [wideCoarseEndpoint_target_power_identity
      (lambda := parameters.projectionLambda / 2)
      (zeta := parameters.zeta)
      htau hradiusPos]
    congr 1
    dsimp only [targetRadiusExponent]
    ring
  have hcoefficientBase :=
    wideCoarseEndpoint_frostmanCoefficient_upper
      (ballRadius := ballRadius)
      input hdelta hepsilon heta
  by_cases hwidthRadius : data.width ≤ radius
  · have hballByRadius :
        ballRadius ≤ 24 * radius := by
      calc
        ballRadius ≤ 24 * max data.width radius := hballUpper
        _ = 24 * radius := by rw [max_eq_right hwidthRadius]
    have hballAbsorb :=
      hballRadius hdelta hdeltaBallRadiusSmall
        data.width_pos input.width_large
    have hcoefficientAbsorb :=
      hcoefficientRadius hdelta hdeltaCoefficientRadiusSmall
        data.width_pos input.width_large
    have hballOneENN :
        ENNReal.ofReal ballRadius ≤ 1 := by
      calc
        ENNReal.ofReal ballRadius ≤
            ENNReal.ofReal radiusConstant *
              Kakeya.realRpowENN tau radiusExponent := by
          have hreal :
              ballRadius ≤
                radiusConstant * Real.rpow tau radiusExponent := by
            dsimp only [radiusConstant]
            nlinarith
          calc
            ENNReal.ofReal ballRadius ≤
                ENNReal.ofReal
                  (radiusConstant *
                    Real.rpow tau radiusExponent) :=
              ENNReal.ofReal_mono hreal
            _ =
                ENNReal.ofReal radiusConstant *
                  Kakeya.realRpowENN tau radiusExponent := by
              rw [ENNReal.ofReal_mul hradiusConstant.le]
              rfl
        _ ≤ Kakeya.realRpowENN tau 0 := hballAbsorb
        _ = 1 := by simp [Kakeya.realRpowENN]
    have hballOne : ballRadius ≤ 1 :=
      ENNReal.ofReal_le_one.mp hballOneENN
    refine ⟨hballOne, ?_⟩
    rw [htargetIdentity]
    have hradiusLoss :=
      wideCoarseEndpoint_radius_loss_power_upper
        htau hradiusPos parameters.zeta_pos
        parameters.zeta_lt_one hradiusBound
    have hradiusSplit :=
      wideCoarseEndpoint_radius_power_split
        (zeta := parameters.zeta) hradiusPos
    have hballPowerRadius :
        Kakeya.realRpowENN ballRadius 1 ≤
          (24 : ENNReal) *
            Kakeya.realRpowENN radius 1 := by
      simpa [Kakeya.realRpowENN] using
        ENNReal.ofReal_mono hballByRadius
    calc
      wideCoarseEndpointFrostmanCoefficient
          parameters input ballRadius
          ≤
        (8192 : ENNReal) *
          Kakeya.realRpowENN tau (-loss) *
          Kakeya.realRpowENN ballRadius 1 := by
            simpa [tau, loss, ballRadius] using hcoefficientBase
      _ ≤
        ((8192 : ENNReal) * 24) *
          Kakeya.realRpowENN tau (-loss) *
          Kakeya.realRpowENN radius 1 := by
            let context : ENNReal :=
              (8192 : ENNReal) *
                Kakeya.realRpowENN tau (-loss)
            calc
              (8192 : ENNReal) *
                    Kakeya.realRpowENN tau (-loss) *
                    Kakeya.realRpowENN ballRadius 1 =
                  context *
                    Kakeya.realRpowENN ballRadius 1 := by rfl
              _ ≤
                  context *
                    ((24 : ENNReal) *
                      Kakeya.realRpowENN radius 1) :=
                mul_le_mul_of_nonneg_left hballPowerRadius
                  (by positivity)
              _ = _ := by
                dsimp only [context]
                ac_rfl
      _ =
        ((8192 : ENNReal) * 24) *
          Kakeya.realRpowENN tau (-loss) *
          (Kakeya.realRpowENN radius (1 - parameters.zeta) *
            Kakeya.realRpowENN radius parameters.zeta) := by
              rw [hradiusSplit]
      _ ≤
        ENNReal.ofReal radiusLossConstant *
          Kakeya.realRpowENN tau
            (-loss + radiusExponent * (1 - parameters.zeta)) *
          Kakeya.realRpowENN radius parameters.zeta := by
            have hconstant :
                ((8192 : ENNReal) * 24) *
                    Kakeya.realRpowENN 2
                      ((1 - parameters.zeta) / parameters.zeta) =
                  ENNReal.ofReal radiusLossConstant := by
              simp [radiusLossConstant, Kakeya.realRpowENN,
                ENNReal.ofReal_mul]
            calc
              ((8192 : ENNReal) * 24) *
                    Kakeya.realRpowENN tau (-loss) *
                    (Kakeya.realRpowENN radius
                        (1 - parameters.zeta) *
                      Kakeya.realRpowENN radius parameters.zeta)
                  ≤
                ((8192 : ENNReal) * 24) *
                    Kakeya.realRpowENN tau (-loss) *
                    (Kakeya.realRpowENN 2
                        ((1 - parameters.zeta) / parameters.zeta) *
                      Kakeya.realRpowENN tau
                        (radiusExponent * (1 - parameters.zeta)) *
                      Kakeya.realRpowENN radius parameters.zeta) := by
                        gcongr
              _ =
                ENNReal.ofReal radiusLossConstant *
                  (Kakeya.realRpowENN tau (-loss) *
                    Kakeya.realRpowENN tau
                      (radiusExponent * (1 - parameters.zeta))) *
                  Kakeya.realRpowENN radius parameters.zeta := by
                    rw [← hconstant]
                    ac_rfl
              _ =
                ENNReal.ofReal radiusLossConstant *
                  Kakeya.realRpowENN tau
                    (-loss + radiusExponent * (1 - parameters.zeta)) *
                  Kakeya.realRpowENN radius parameters.zeta := by
                    rw [realRpowENN_add htau]
      _ ≤
        Kakeya.realRpowENN tau targetRadiusExponent *
          Kakeya.realRpowENN radius parameters.zeta := by
            gcongr
  · have hradiusWidth : radius ≤ data.width :=
      le_of_not_ge hwidthRadius
    have hwidthPower :
        data.width ≤ Real.rpow tau widthExponent := by
      simpa [WZ1WideCoarseEndpointAxialProjectiveSmallWidth,
        tau, widthExponent] using hsmallWidth
    have hballByWidth :
        ballRadius ≤ 24 * Real.rpow tau widthExponent := by
      calc
        ballRadius ≤ 24 * max data.width radius := hballUpper
        _ = 24 * data.width := by rw [max_eq_left hradiusWidth]
        _ ≤ 24 * Real.rpow tau widthExponent := by gcongr
    have hballAbsorb :=
      hballWidth hdelta hdeltaBallWidthSmall
        data.width_pos input.width_large
    have hcoefficientAbsorb :=
      hcoefficientWidth hdelta hdeltaCoefficientWidthSmall
        data.width_pos input.width_large
    have hballOneENN :
        ENNReal.ofReal ballRadius ≤ 1 := by
      calc
        ENNReal.ofReal ballRadius ≤
            ENNReal.ofReal 24 *
              Kakeya.realRpowENN tau widthExponent := by
          calc
            ENNReal.ofReal ballRadius ≤
                ENNReal.ofReal
                  (24 * Real.rpow tau widthExponent) :=
              ENNReal.ofReal_mono hballByWidth
            _ =
                ENNReal.ofReal 24 *
                  Kakeya.realRpowENN tau widthExponent := by
              rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 24)]
              rfl
        _ ≤ Kakeya.realRpowENN tau 0 := hballAbsorb
        _ = 1 := by simp [Kakeya.realRpowENN]
    have hballOne : ballRadius ≤ 1 :=
      ENNReal.ofReal_le_one.mp hballOneENN
    refine ⟨hballOne, ?_⟩
    rw [htargetIdentity]
    have htargetLower :=
      wideCoarseEndpoint_tau_power_le_target
        htau hradiusPos hradius parameters.zeta_pos
        (lambda := parameters.projectionLambda)
    have hballPowerWidth :
        Kakeya.realRpowENN ballRadius 1 ≤
          (24 : ENNReal) *
            Kakeya.realRpowENN tau widthExponent := by
      simpa [Kakeya.realRpowENN] using
        ENNReal.ofReal_mono hballByWidth
    calc
      wideCoarseEndpointFrostmanCoefficient
          parameters input ballRadius
          ≤
        (8192 : ENNReal) *
          Kakeya.realRpowENN tau (-loss) *
          Kakeya.realRpowENN ballRadius 1 := by
            simpa [tau, loss, ballRadius] using hcoefficientBase
      _ ≤
        ENNReal.ofReal widthLossConstant *
          Kakeya.realRpowENN tau
            (widthExponent - loss) := by
              have hconstant :
                  ENNReal.ofReal widthLossConstant =
                    (8192 : ENNReal) * 24 := by
                norm_num [widthLossConstant]
              calc
                (8192 : ENNReal) *
                      Kakeya.realRpowENN tau (-loss) *
                      Kakeya.realRpowENN ballRadius 1
                    ≤
                  ((8192 : ENNReal) * 24) *
                    Kakeya.realRpowENN tau (-loss) *
                    Kakeya.realRpowENN tau widthExponent := by
                      let context : ENNReal :=
                        (8192 : ENNReal) *
                          Kakeya.realRpowENN tau (-loss)
                      calc
                        (8192 : ENNReal) *
                              Kakeya.realRpowENN tau (-loss) *
                              Kakeya.realRpowENN ballRadius 1 =
                            context *
                              Kakeya.realRpowENN ballRadius 1 := by rfl
                        _ ≤
                            context *
                              ((24 : ENNReal) *
                                Kakeya.realRpowENN tau widthExponent) :=
                          mul_le_mul_of_nonneg_left hballPowerWidth
                            (by positivity)
                        _ = _ := by
                          dsimp only [context]
                          ac_rfl
                _ =
                  ENNReal.ofReal widthLossConstant *
                    (Kakeya.realRpowENN tau widthExponent *
                      Kakeya.realRpowENN tau (-loss)) := by
                        rw [hconstant]
                        ac_rfl
                _ =
                  ENNReal.ofReal widthLossConstant *
                    Kakeya.realRpowENN tau
                      (widthExponent - loss) := by
                        simpa only [sub_eq_add_neg] using
                          congrArg
                            (fun value : ENNReal =>
                              ENNReal.ofReal widthLossConstant * value)
                            (realRpowENN_add
                              htau widthExponent (-loss)).symm
      _ ≤ Kakeya.realRpowENN tau targetWidthExponent :=
        hcoefficientAbsorb
      _ ≤
        Kakeya.realRpowENN tau targetRadiusExponent *
          Kakeya.realRpowENN radius parameters.zeta := by
            simpa [targetWidthExponent, targetRadiusExponent] using
              htargetLower

end Kakeya.Assouad
