import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointTransverseBudgetStatements

/-!
# Transverse endpoint raw-coefficient power bound
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- The finite constant left after the transverse raw-radius estimate. -/
noncomputable def wideCoarseEndpointTransverseConstant
    (zeta : ℝ) : ENNReal :=
  (2097152 : ENNReal) *
    Kakeya.realRpowENN 4 zeta

/-- The total coarse-scale exponent loss before the final parameter gap. -/
noncomputable def wideCoarseEndpointBaseLoss
    {epsilon : ℝ}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    (eta : ℝ) : ℝ :=
  20 * eta / epsilon +
    10 * parameters.stripEpsilon * parameters.zeta / epsilon +
    parameters.stripEpsilon * eta / 10

/--
In the transverse coefficient regime, the explicit raw coefficient is
bounded by one finite constant times the base coarse-scale loss and
`radius^zeta`.
-/
lemma wideCoarseEndpoint_transverse_rawCoefficient_bound
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
    (hdeltaOne : delta ≤ 1)
    (hepsilon : 0 < epsilon)
    (heta : 0 < eta)
    (normal : Point2)
    (htransverse :
      1 / 2 ≤
        |inner ℝ normal (wz1Perp2 data.direction)|)
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
          (-(wideCoarseEndpointBaseLoss parameters eta)) *
        Kakeya.realRpowENN radius parameters.zeta := by
  dsimp only
  let tau := delta / data.width
  let rawRadius :=
    max delta
      ((radius + delta / data.width) /
        ‖wideCoarsePhiGPullbackVector
          data.direction data.width normal‖)
  have htau : 0 < tau := div_pos hdelta data.width_pos
  have htauOne : tau ≤ 1 := by
    exact (div_le_one data.width_pos).2 data.delta_le_width
  have hradiusPos : 0 < radius := htau.trans_le hradius
  have hrawRadius :
      rawRadius ≤ 4 * data.width * radius := by
    exact
      wideCoarseEndpoint_transverse_rawRadius_upper
        hdelta data.width_pos hradius
        data.direction_unit htransverse
  have hrawRadiusNonnegative : 0 ≤ rawRadius := by
    exact hdelta.le.trans (le_max_left _ _)
  have hrawPower :
      Kakeya.realRpowENN rawRadius parameters.zeta ≤
        Kakeya.realRpowENN (4 * data.width * radius)
          parameters.zeta := by
    simp only [Kakeya.realRpowENN]
    exact ENNReal.ofReal_mono
      (Real.rpow_le_rpow hrawRadiusNonnegative
        hrawRadius parameters.zeta_pos.le)
  have hproductPower :
      Kakeya.realRpowENN (4 * data.width * radius)
          parameters.zeta =
        Kakeya.realRpowENN 4 parameters.zeta *
          Kakeya.realRpowENN data.width parameters.zeta *
          Kakeya.realRpowENN radius parameters.zeta := by
    rw [show 4 * data.width * radius =
      (4 * data.width) * radius by ring,
      realRpowENN_mul
        (mul_pos (by norm_num) data.width_pos) hradiusPos,
      realRpowENN_mul (by norm_num) data.width_pos]
  have hrawWidthCancel :=
    wideCoarseEndpoint_rawWidth_cancel
      hdelta data.width_pos input.rawWidth_pos
      parameters.zeta_pos input.width_le_raw
  have hrawWidthCancel' :
      Kakeya.realRpowENN input.rawWidth (-parameters.zeta) *
          Kakeya.realRpowENN data.width parameters.zeta ≤
        Kakeya.realRpowENN delta
          (-(parameters.stripEpsilon * parameters.zeta)) := by
    simpa only [neg_mul] using hrawWidthCancel
  have hactiveInv :=
    wideCoarseEndpoint_activeFraction_inv
      (delta := delta) (eta := eta) hdelta
  have hrescaleInv :=
    wideCoarseEndpoint_rescaleFraction_inv
      (delta := delta) (width := data.width)
      (exponent := parameters.stripEpsilon * eta / 10)
      hdelta data.width_pos
  have htauPower :
      tau ≤ Real.rpow delta (epsilon / 10) := by
    exact
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
  have htauAdd :
      Kakeya.realRpowENN tau (-(20 * eta / epsilon)) *
          Kakeya.realRpowENN tau
            (-(10 * parameters.stripEpsilon *
              parameters.zeta / epsilon)) *
          Kakeya.realRpowENN tau
            (-(parameters.stripEpsilon * eta / 10)) =
        Kakeya.realRpowENN tau
          (-(wideCoarseEndpointBaseLoss parameters eta)) := by
    rw [← realRpowENN_add htau,
      ← realRpowENN_add htau]
    congr 1
    simp [wideCoarseEndpointBaseLoss]
    ring
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
    convert hproduct using 1 <;> congr 2 <;> field_simp [hepsilon.ne'] <;> ring
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
          Kakeya.realRpowENN radius parameters.zeta) *
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
        Kakeya.realRpowENN radius parameters.zeta := by
          have hconstant : (256 : ENNReal) * 4096 * 2 = 2097152 := by
            norm_num
          calc
            _ =
              ((256 : ENNReal) * 4096 * 2) *
                Kakeya.realRpowENN 4 parameters.zeta *
                (Kakeya.realRpowENN delta (-eta) *
                  Kakeya.realRpowENN delta (-eta)) *
                (Kakeya.realRpowENN input.rawWidth (-parameters.zeta) *
                  Kakeya.realRpowENN data.width parameters.zeta) *
                Kakeya.realRpowENN tau
                  (-(parameters.stripEpsilon * eta / 10)) *
                Kakeya.realRpowENN radius parameters.zeta := by
                  ac_rfl
            _ ≤
              ((256 : ENNReal) * 4096 * 2) *
                Kakeya.realRpowENN 4 parameters.zeta *
                (Kakeya.realRpowENN delta (-eta) *
                  Kakeya.realRpowENN delta (-eta)) *
                Kakeya.realRpowENN delta
                  (-(parameters.stripEpsilon * parameters.zeta)) *
                Kakeya.realRpowENN tau
                  (-(parameters.stripEpsilon * eta / 10)) *
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
                          parameters.zeta) := by
                            dsimp only [context]
                            ac_rfl
                    _ ≤ context *
                        Kakeya.realRpowENN delta
                          (-(parameters.stripEpsilon *
                            parameters.zeta)) :=
                      mul_le_mul_of_nonneg_left
                        hrawWidthCancel' (by positivity)
                    _ = _ := by
                      dsimp only [context]
                      ac_rfl
            _ = _ := by rw [hconstant]
    _ ≤
      wideCoarseEndpointTransverseConstant parameters.zeta *
        (Kakeya.realRpowENN tau (-(20 * eta / epsilon)) *
          Kakeya.realRpowENN tau
            (-(10 * parameters.stripEpsilon *
              parameters.zeta / epsilon)) *
          Kakeya.realRpowENN tau
            (-(parameters.stripEpsilon * eta / 10))) *
        Kakeya.realRpowENN radius parameters.zeta := by
          unfold wideCoarseEndpointTransverseConstant
          let context : ENNReal :=
            (2097152 : ENNReal) *
              Kakeya.realRpowENN 4 parameters.zeta *
              Kakeya.realRpowENN tau
                (-(parameters.stripEpsilon * eta / 10)) *
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
          (-(wideCoarseEndpointBaseLoss parameters eta)) *
        Kakeya.realRpowENN radius parameters.zeta := by
          rw [htauAdd]

end Kakeya.Assouad
