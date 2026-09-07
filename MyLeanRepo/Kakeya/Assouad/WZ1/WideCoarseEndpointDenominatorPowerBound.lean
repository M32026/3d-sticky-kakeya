import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointAxialBudgetStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointTransversePowerBound

/-!
# Denominator-regime endpoint raw-coefficient power bound
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- Total loss in either axial raw-strip leaf. -/
noncomputable def wideCoarseEndpointAxialRawLoss
    {epsilon : ℝ}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    (eta : ℝ) : ℝ :=
  wideCoarseEndpointBaseLoss parameters eta +
    3 * parameters.projectionLambda * parameters.zeta / 20

/-- The large perpendicular coefficient contributes at most the reserved
`3 * projectionLambda * zeta / 20` coarse-scale loss. -/
lemma wideCoarseEndpoint_large_perp_inverse_power
    {tau coefficient lambda zeta : ℝ}
    (htau : 0 < tau)
    (hcoefficient :
      Real.rpow tau (3 * lambda / 20) < coefficient)
    (hzeta : 0 < zeta) :
    Kakeya.realRpowENN coefficient (-zeta) ≤
      Kakeya.realRpowENN tau
        (-(3 * lambda * zeta / 20)) := by
  have hcoefficientPos : 0 < coefficient :=
    (Real.rpow_pos_of_pos htau _).trans hcoefficient
  have hreal :
      Real.rpow coefficient (-zeta) ≤
        Real.rpow
          (Real.rpow tau (3 * lambda / 20)) (-zeta) :=
    Real.rpow_le_rpow_of_nonpos
      (Real.rpow_pos_of_pos htau _)
      hcoefficient.le (by linarith)
  have hrewrite :
      Real.rpow
          (Real.rpow tau (3 * lambda / 20)) (-zeta) =
        Real.rpow tau
          (-(3 * lambda * zeta / 20)) := by
    calc
      Real.rpow
          (Real.rpow tau (3 * lambda / 20)) (-zeta) =
        Real.rpow tau
          ((3 * lambda / 20) * (-zeta)) := by
            exact
              (Real.rpow_mul
                htau.le (3 * lambda / 20) (-zeta)).symm
      _ = Real.rpow tau
          (-(3 * lambda * zeta / 20)) := by
            congr 1
            ring
  rw [hrewrite] at hreal
  exact ENNReal.ofReal_mono hreal

/-- If the enlarged raw radius is controlled by
`4 * width * radius / scale` and `scale` is above the reserved coarse-scale
threshold, the explicit raw coefficient has the common axial raw loss. -/
lemma wideCoarseEndpoint_axial_rawCoefficient_bound_of_scale
    {epsilon eta delta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ ambient active : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    (input :
      WZ1WideCoarseEndpointLineInput
        (ambient := ambient) (active := active)
        parameters data)
    (hdelta : 0 < delta)
    (hepsilon : 0 < epsilon)
    (heta : 0 < eta)
    (normal : Point2)
    (scale : ℝ)
    (hscaleLarge :
      Real.rpow
          (delta / data.width)
          (3 * parameters.projectionLambda / 20) <
        scale)
    {radius : ℝ}
    (hradius : delta / data.width ≤ radius)
    (hrawRadiusUpper :
      max delta
          ((radius + delta / data.width) /
            ‖wideCoarsePhiGPullbackVector
              data.direction data.width normal‖) ≤
        4 * data.width * radius / scale) :
    let pullback :=
      wideCoarsePhiGPullbackVector
        data.direction data.width normal
    let sourceRadius :=
      (radius + delta / data.width) / ‖pullback‖
    let rawRadius := max delta sourceRadius
    wideCoarseEndpointRawCoefficient
        parameters input rawRadius ≤
      wideCoarseEndpointTransverseConstant parameters.zeta *
        Kakeya.realRpowENN
          (delta / data.width)
          (-(wideCoarseEndpointAxialRawLoss parameters eta)) *
        Kakeya.realRpowENN radius parameters.zeta := by
  dsimp only
  let tau := delta / data.width
  let coefficient := scale
  let rawRadius :=
    max delta
      ((radius + delta / data.width) /
        ‖wideCoarsePhiGPullbackVector
          data.direction data.width normal‖)
  have htau : 0 < tau := div_pos hdelta data.width_pos
  have hradiusPos : 0 < radius := htau.trans_le hradius
  have hcoefficientLarge :
      Real.rpow tau
          (3 * parameters.projectionLambda / 20) <
        coefficient := by
    simpa [tau, coefficient] using hscaleLarge
  have hcoefficientPos : 0 < coefficient :=
    (Real.rpow_pos_of_pos htau _).trans hcoefficientLarge
  have hrawRadius :
      rawRadius ≤
        4 * data.width * radius / coefficient := by
    simpa [rawRadius, coefficient] using hrawRadiusUpper
  have hrawRadiusNonnegative : 0 ≤ rawRadius :=
    hdelta.le.trans (le_max_left _ _)
  have htargetRadiusPos :
      0 < 4 * data.width * radius / coefficient := by
    exact div_pos
      (mul_pos
        (mul_pos (by norm_num) data.width_pos)
        hradiusPos)
      hcoefficientPos
  have hrawPower :
      Kakeya.realRpowENN rawRadius parameters.zeta ≤
        Kakeya.realRpowENN
          (4 * data.width * radius / coefficient)
          parameters.zeta := by
    simp only [Kakeya.realRpowENN]
    exact ENNReal.ofReal_mono
      (Real.rpow_le_rpow hrawRadiusNonnegative
        hrawRadius parameters.zeta_pos.le)
  have hproductPower :
      Kakeya.realRpowENN
          (4 * data.width * radius / coefficient)
          parameters.zeta =
        Kakeya.realRpowENN 4 parameters.zeta *
          Kakeya.realRpowENN data.width parameters.zeta *
          Kakeya.realRpowENN radius parameters.zeta *
          Kakeya.realRpowENN coefficient (-parameters.zeta) := by
    have hcoefficientInverse :
        Kakeya.realRpowENN (1 / coefficient) parameters.zeta =
          Kakeya.realRpowENN coefficient (-parameters.zeta) := by
      simp only [Kakeya.realRpowENN]
      congr 1
      have hinverse :
          Real.rpow (1 / coefficient) parameters.zeta =
            (Real.rpow coefficient parameters.zeta)⁻¹ := by
        rw [show 1 / coefficient = coefficient⁻¹ by ring]
        exact Real.inv_rpow hcoefficientPos.le parameters.zeta
      have hnegative :
          Real.rpow coefficient (-parameters.zeta) =
            (Real.rpow coefficient parameters.zeta)⁻¹ :=
        Real.rpow_neg hcoefficientPos.le parameters.zeta
      exact hinverse.trans hnegative.symm
    calc
      Kakeya.realRpowENN
          (4 * data.width * radius / coefficient)
          parameters.zeta =
        Kakeya.realRpowENN
          ((4 * data.width * radius) * (1 / coefficient))
          parameters.zeta := by
            congr 2
            field_simp [hcoefficientPos.ne']
      _ =
        Kakeya.realRpowENN
            (4 * data.width * radius) parameters.zeta *
          Kakeya.realRpowENN
            (1 / coefficient) parameters.zeta := by
              rw [realRpowENN_mul
                (mul_pos
                  (mul_pos (by norm_num) data.width_pos)
                  hradiusPos)
                (one_div_pos.mpr hcoefficientPos)]
      _ =
        (Kakeya.realRpowENN
            (4 * data.width) parameters.zeta *
          Kakeya.realRpowENN radius parameters.zeta) *
          Kakeya.realRpowENN
            (1 / coefficient) parameters.zeta := by
              rw [realRpowENN_mul
                (mul_pos (by norm_num) data.width_pos)
                hradiusPos]
      _ =
        ((Kakeya.realRpowENN 4 parameters.zeta *
          Kakeya.realRpowENN data.width parameters.zeta) *
          Kakeya.realRpowENN radius parameters.zeta) *
          Kakeya.realRpowENN
            (1 / coefficient) parameters.zeta := by
              rw [realRpowENN_mul
                (by norm_num) data.width_pos]
      _ = _ := by
        rw [hcoefficientInverse]
  have hrawWidthCancel' :
      Kakeya.realRpowENN input.rawWidth (-parameters.zeta) *
          Kakeya.realRpowENN data.width parameters.zeta ≤
        Kakeya.realRpowENN delta
          (-(parameters.stripEpsilon * parameters.zeta)) := by
    simpa only [neg_mul] using
      wideCoarseEndpoint_rawWidth_cancel
        hdelta data.width_pos input.rawWidth_pos
        parameters.zeta_pos input.width_le_raw
  have hcoefficientPower :=
    wideCoarseEndpoint_large_perp_inverse_power
      htau hcoefficientLarge parameters.zeta_pos
  have hactiveInv :=
    wideCoarseEndpoint_activeFraction_inv
      (delta := delta) (eta := eta) hdelta
  have hrescaleInv :=
    wideCoarseEndpoint_rescaleFraction_inv
      (delta := delta) (width := data.width)
      (exponent := parameters.stripEpsilon * eta / 10)
      hdelta data.width_pos
  have htauPower :
      tau ≤ Real.rpow delta (epsilon / 10) :=
    (wideCoarseScaleBound hdelta data.width_pos
      hepsilon input.width_large).le
  have hdeltaEta :=
    wideCoarseEndpoint_delta_loss_to_tau
      hdelta htau hepsilon (by linarith)
      (loss := 2 * eta) htauPower
  have hdeltaStrip :=
    wideCoarseEndpoint_delta_loss_to_tau
      hdelta htau hepsilon
      (mul_nonneg parameters.stripEpsilon_pos.le
        parameters.zeta_pos.le)
      (loss := parameters.stripEpsilon * parameters.zeta)
      htauPower
  have hdeltaCombined :
      Kakeya.realRpowENN delta (-eta) *
          Kakeya.realRpowENN delta (-eta) *
          Kakeya.realRpowENN delta
            (-(parameters.stripEpsilon * parameters.zeta)) ≤
        Kakeya.realRpowENN tau (-(20 * eta / epsilon)) *
          Kakeya.realRpowENN tau
            (-(10 * parameters.stripEpsilon *
              parameters.zeta / epsilon)) := by
    have hetaPair :
        Kakeya.realRpowENN delta (-eta) *
            Kakeya.realRpowENN delta (-eta) =
          Kakeya.realRpowENN delta (-(2 * eta)) := by
      rw [← realRpowENN_add hdelta]
      congr 1
      ring
    rw [hetaPair]
    have hproduct := mul_le_mul hdeltaEta hdeltaStrip
      (by positivity) (by positivity)
    convert hproduct using 1 <;>
      congr 2 <;> field_simp [hepsilon.ne'] <;> ring
  have htauAdd :
      Kakeya.realRpowENN tau (-(20 * eta / epsilon)) *
          Kakeya.realRpowENN tau
            (-(10 * parameters.stripEpsilon *
              parameters.zeta / epsilon)) *
          Kakeya.realRpowENN tau
            (-(parameters.stripEpsilon * eta / 10)) *
          Kakeya.realRpowENN tau
            (-(3 * parameters.projectionLambda *
              parameters.zeta / 20)) =
        Kakeya.realRpowENN tau
          (-(wideCoarseEndpointAxialRawLoss parameters eta)) := by
    rw [← realRpowENN_add htau,
      ← realRpowENN_add htau,
      ← realRpowENN_add htau]
    congr 1
    simp [wideCoarseEndpointAxialRawLoss,
      wideCoarseEndpointBaseLoss]
    ring
  rw [wideCoarseEndpointRawCoefficient,
    hactiveInv, hrescaleInv]
  calc
    ((256 : ENNReal) *
          Kakeya.realRpowENN delta (-eta)) *
        Kakeya.realRpowENN input.rawWidth (-parameters.zeta) *
        Kakeya.realRpowENN rawRadius parameters.zeta *
        ((4096 : ENNReal) *
          Kakeya.realRpowENN delta (-eta)) *
        Kakeya.realRpowENN tau
          (-(parameters.stripEpsilon * eta / 10)) *
        2
        ≤
      ((256 : ENNReal) *
          Kakeya.realRpowENN delta (-eta)) *
        Kakeya.realRpowENN input.rawWidth (-parameters.zeta) *
        (Kakeya.realRpowENN 4 parameters.zeta *
          Kakeya.realRpowENN data.width parameters.zeta *
          Kakeya.realRpowENN radius parameters.zeta *
          Kakeya.realRpowENN coefficient (-parameters.zeta)) *
        ((4096 : ENNReal) *
          Kakeya.realRpowENN delta (-eta)) *
        Kakeya.realRpowENN tau
          (-(parameters.stripEpsilon * eta / 10)) *
        2 := by
          gcongr
          simpa [hproductPower] using hrawPower
    _ ≤
      (2097152 : ENNReal) *
        Kakeya.realRpowENN 4 parameters.zeta *
        (Kakeya.realRpowENN delta (-eta) *
          Kakeya.realRpowENN delta (-eta)) *
        Kakeya.realRpowENN delta
          (-(parameters.stripEpsilon * parameters.zeta)) *
        Kakeya.realRpowENN tau
          (-(parameters.stripEpsilon * eta / 10)) *
        Kakeya.realRpowENN tau
          (-(3 * parameters.projectionLambda *
            parameters.zeta / 20)) *
        Kakeya.realRpowENN radius parameters.zeta := by
          let context : ENNReal :=
            ((256 : ENNReal) * 4096 * 2) *
              Kakeya.realRpowENN 4 parameters.zeta *
              (Kakeya.realRpowENN delta (-eta) *
                Kakeya.realRpowENN delta (-eta)) *
              Kakeya.realRpowENN tau
                (-(parameters.stripEpsilon * eta / 10)) *
              Kakeya.realRpowENN radius parameters.zeta
          calc
            _ = context *
                (Kakeya.realRpowENN input.rawWidth
                    (-parameters.zeta) *
                  Kakeya.realRpowENN data.width
                    parameters.zeta) *
                Kakeya.realRpowENN coefficient
                  (-parameters.zeta) := by
                    dsimp only [context]
                    ac_rfl
            _ ≤ context *
                Kakeya.realRpowENN delta
                  (-(parameters.stripEpsilon *
                    parameters.zeta)) *
                Kakeya.realRpowENN coefficient
                  (-parameters.zeta) := by
                    gcongr
            _ ≤ context *
                Kakeya.realRpowENN delta
                  (-(parameters.stripEpsilon *
                    parameters.zeta)) *
                Kakeya.realRpowENN tau
                  (-(3 * parameters.projectionLambda *
                    parameters.zeta / 20)) := by
                    gcongr
            _ = _ := by
              dsimp only [context]
              norm_num
              ac_rfl
    _ ≤
      wideCoarseEndpointTransverseConstant parameters.zeta *
        (Kakeya.realRpowENN tau (-(20 * eta / epsilon)) *
          Kakeya.realRpowENN tau
            (-(10 * parameters.stripEpsilon *
              parameters.zeta / epsilon)) *
          Kakeya.realRpowENN tau
            (-(parameters.stripEpsilon * eta / 10)) *
          Kakeya.realRpowENN tau
            (-(3 * parameters.projectionLambda *
              parameters.zeta / 20))) *
        Kakeya.realRpowENN radius parameters.zeta := by
          unfold wideCoarseEndpointTransverseConstant
          let context : ENNReal :=
            (2097152 : ENNReal) *
              Kakeya.realRpowENN 4 parameters.zeta *
              Kakeya.realRpowENN tau
                (-(parameters.stripEpsilon * eta / 10)) *
              Kakeya.realRpowENN tau
                (-(3 * parameters.projectionLambda *
                  parameters.zeta / 20)) *
              Kakeya.realRpowENN radius parameters.zeta
          calc
            _ = context *
                (Kakeya.realRpowENN delta (-eta) *
                  Kakeya.realRpowENN delta (-eta) *
                  Kakeya.realRpowENN delta
                    (-(parameters.stripEpsilon *
                      parameters.zeta))) := by
                      dsimp only [context]
                      ac_rfl
            _ ≤ context *
                (Kakeya.realRpowENN tau
                    (-(20 * eta / epsilon)) *
                  Kakeya.realRpowENN tau
                    (-(10 * parameters.stripEpsilon *
                      parameters.zeta / epsilon))) :=
              mul_le_mul_of_nonneg_left
                hdeltaCombined (by positivity)
            _ = _ := by
              dsimp only [context]
              ac_rfl
    _ =
      wideCoarseEndpointTransverseConstant parameters.zeta *
        Kakeya.realRpowENN tau
          (-(wideCoarseEndpointAxialRawLoss parameters eta)) *
        Kakeya.realRpowENN radius parameters.zeta := by
          rw [htauAdd]

/-- In the large-perpendicular-coefficient axial regime, the explicit raw
coefficient has the common axial raw loss. -/
lemma wideCoarseEndpoint_denominator_rawCoefficient_bound
    {epsilon eta delta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ ambient active : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    (input :
      WZ1WideCoarseEndpointLineInput
        (ambient := ambient) (active := active)
        parameters data)
    (hdelta : 0 < delta)
    (hepsilon : 0 < epsilon)
    (heta : 0 < eta)
    (normal : Point2)
    (hnormal : ‖normal‖ = 1)
    (hlarge :
      ¬ WZ1WideCoarseEndpointAxialSmallCoefficient
        parameters data normal)
    {radius : ℝ}
    (hradius : delta / data.width ≤ radius) :
    let pullback :=
      wideCoarsePhiGPullbackVector
        data.direction data.width normal
    let sourceRadius :=
      (radius + delta / data.width) / ‖pullback‖
    let rawRadius := max delta sourceRadius
    wideCoarseEndpointRawCoefficient
        parameters input rawRadius ≤
      wideCoarseEndpointTransverseConstant parameters.zeta *
        Kakeya.realRpowENN
          (delta / data.width)
          (-(wideCoarseEndpointAxialRawLoss parameters eta)) *
        Kakeya.realRpowENN radius parameters.zeta := by
  dsimp only
  let tau := delta / data.width
  let coefficient :=
    |inner ℝ normal (wz1Perp2 data.direction)|
  have hcoefficientLarge :
      Real.rpow tau
          (3 * parameters.projectionLambda / 20) <
        coefficient := by
    simpa [WZ1WideCoarseEndpointAxialSmallCoefficient,
      tau, coefficient] using lt_of_not_ge hlarge
  have hcoefficientPos : 0 < coefficient :=
    (Real.rpow_pos_of_pos
      (div_pos hdelta data.width_pos) _).trans
      hcoefficientLarge
  apply
    wideCoarseEndpoint_axial_rawCoefficient_bound_of_scale
      input hdelta hepsilon heta normal coefficient
      (by simpa [tau] using hcoefficientLarge) hradius
  simpa [coefficient] using
    wideCoarseEndpoint_axial_denominator_rawRadius_upper
      hdelta data.width_pos hradius
      data.direction_unit hnormal hcoefficientPos

/-- In the large-common-width projective regime, the explicit raw
coefficient has the same common axial raw loss. -/
lemma wideCoarseEndpoint_projective_rawCoefficient_bound
    {epsilon eta delta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ ambient active : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    (input :
      WZ1WideCoarseEndpointLineInput
        (ambient := ambient) (active := active)
        parameters data)
    (hdelta : 0 < delta)
    (hepsilon : 0 < epsilon)
    (heta : 0 < eta)
    (normal : Point2)
    (hnormal : ‖normal‖ = 1)
    (haxial :
      |inner ℝ normal (wz1Perp2 data.direction)| < 1 / 2)
    (hlarge :
      ¬ WZ1WideCoarseEndpointAxialProjectiveSmallWidth
        parameters data)
    {radius : ℝ}
    (hradius : delta / data.width ≤ radius) :
    let pullback :=
      wideCoarsePhiGPullbackVector
        data.direction data.width normal
    let sourceRadius :=
      (radius + delta / data.width) / ‖pullback‖
    let rawRadius := max delta sourceRadius
    wideCoarseEndpointRawCoefficient
        parameters input rawRadius ≤
      wideCoarseEndpointTransverseConstant parameters.zeta *
        Kakeya.realRpowENN
          (delta / data.width)
          (-(wideCoarseEndpointAxialRawLoss parameters eta)) *
        Kakeya.realRpowENN radius parameters.zeta := by
  dsimp only
  let tau := delta / data.width
  have hwidthLarge :
      Real.rpow tau
          (3 * parameters.projectionLambda / 20) <
        data.width := by
    simpa [WZ1WideCoarseEndpointAxialProjectiveSmallWidth,
      tau] using lt_of_not_ge hlarge
  apply
    wideCoarseEndpoint_axial_rawCoefficient_bound_of_scale
      input hdelta hepsilon heta normal data.width
      (by simpa [tau] using hwidthLarge) hradius
  have hraw :=
    wideCoarseEndpoint_axial_rawRadius_upper
      hdelta data.width_pos data.width_le_one hradius
      data.direction_unit hnormal haxial
  convert hraw using 1
  field_simp [data.width_pos.ne']

end Kakeya.Assouad
