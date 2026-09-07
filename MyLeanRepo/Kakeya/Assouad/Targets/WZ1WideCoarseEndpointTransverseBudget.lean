import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointParameterGap
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointTransverseBudgetStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointTransversePowerBound

/-!
PDF Proposition 8.9 wide branch: bound the one enlarged exact source strip
in the transverse coarse-normal regime.  Exact pullback and balanced-fiber
cancellation are already closed.
-/

namespace Kakeya.Assouad

theorem wz1_wide_coarse_endpoint_transverse_budget :
    WZ1WideCoarseEndpointTransverseBudgetStatement := by
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
    wideCoarseEndpointBaseLoss parameters eta
  let targetLoss : ℝ :=
    parameters.projectionLambda * parameters.zeta / 2
  have hloss : 0 ≤ loss := by
    dsimp only [loss, wideCoarseEndpointBaseLoss]
    have hfirst : 0 ≤ 20 * eta / epsilon := by positivity
    have hsecond :
        0 ≤
          10 * parameters.stripEpsilon * parameters.zeta /
            epsilon := by
      exact div_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            parameters.stripEpsilon_pos.le)
          parameters.zeta_pos.le)
        hepsilon.le
    have hthird :
        0 ≤ parameters.stripEpsilon * eta / 10 := by
      exact div_nonneg
        (mul_nonneg parameters.stripEpsilon_pos.le heta.le)
        (by norm_num)
    linarith
  have hgap : loss < targetLoss := by
    dsimp only [loss, targetLoss,
      wideCoarseEndpointBaseLoss]
    exact
      wz1WideCoarseEndpoint_parameter_gap
        parameters hepsilon hepsilonOne
        heta (by simpa [etaCap] using hetaSmall)
  have hconstantTop :
      wideCoarseEndpointTransverseConstant
          parameters.zeta ≠ ⊤ := by
    unfold wideCoarseEndpointTransverseConstant
    exact ENNReal.mul_ne_top
      (by simp)
      (by simp [Kakeya.realRpowENN])
  rcases
      wideCoarseEndpoint_exists_delta_absorb_tau_constant
        (wideCoarseEndpointTransverseConstant parameters.zeta)
        hconstantTop hepsilon hloss hgap with
    ⟨delta₀, hdelta₀, hdelta₀One, habsorb⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta F G₁ G₂ ambient active H
    hdelta hdeltaSmall data input normal hnormal htransverse
    level radius hradius hradiusOne
  let tau := delta / data.width
  let pullback :=
    wideCoarsePhiGPullbackVector
      data.direction data.width normal
  let sourceRadius :=
    (radius + delta / data.width) / ‖pullback‖
  let rawRadius := max delta sourceRadius
  have hdeltaOne : delta ≤ 1 :=
    hdeltaSmall.trans hdelta₀One
  have htau : 0 < tau :=
    div_pos hdelta data.width_pos
  have hradiusPos : 0 < radius :=
    htau.trans_le hradius
  have hrawBound :
      wideCoarseEndpointRawCoefficient
          parameters input rawRadius ≤
        wideCoarseEndpointTransverseConstant parameters.zeta *
          Kakeya.realRpowENN tau (-loss) *
          Kakeya.realRpowENN radius parameters.zeta := by
    simpa [tau, pullback, sourceRadius, rawRadius, loss] using
      wideCoarseEndpoint_transverse_rawCoefficient_bound
        input hdelta hdeltaOne hepsilon heta
        normal htransverse hradius
  have habsorbAt :
      wideCoarseEndpointTransverseConstant parameters.zeta *
          Kakeya.realRpowENN tau (-loss) ≤
        Kakeya.realRpowENN tau (-targetLoss) := by
    exact
      habsorb hdelta hdeltaSmall data.width_pos
        input.width_large
  have hscalar :
      wideCoarseEndpointRawCoefficient
          parameters input rawRadius ≤
        Kakeya.realRpowENN
          (Real.rpow tau
              (-(parameters.projectionLambda / 2)) *
            radius)
          parameters.zeta := by
    calc
      wideCoarseEndpointRawCoefficient
          parameters input rawRadius
          ≤
        wideCoarseEndpointTransverseConstant parameters.zeta *
          Kakeya.realRpowENN tau (-loss) *
          Kakeya.realRpowENN radius parameters.zeta :=
        hrawBound
      _ ≤
        Kakeya.realRpowENN tau (-targetLoss) *
          Kakeya.realRpowENN radius parameters.zeta := by
            exact mul_le_mul_of_nonneg_right
              habsorbAt (by positivity)
      _ =
        Kakeya.realRpowENN
          (Real.rpow tau
              (-(parameters.projectionLambda / 2)) *
            radius)
          parameters.zeta := by
            rw [wideCoarseEndpoint_target_power_identity
              htau hradiusPos]
            congr 1
            dsimp only [targetLoss]
            ring
  apply
    wideCoarseEndpoint_sourceBudget_of_rawCoefficient
      hdelta normal hnormal level radius hradius
  simpa [tau, pullback, sourceRadius, rawRadius] using hscalar

end Kakeya.Assouad
