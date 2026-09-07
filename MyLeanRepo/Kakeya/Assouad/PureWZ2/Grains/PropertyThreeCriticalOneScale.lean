import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeOneScaleOutput
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinePullbackAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LossGapAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.AlignedCoarseScale

/-!
# Complete critical-scale output on the honest Property-Three pullback

This module composes the closed geometric and analytic leaves at the genuine
critical query scale `48 * L^2`.  It deliberately leaves the one-scale mass
factor and its loss absorption explicit.  In particular, it does not assert
near-full retention or any hereditary relationship between independently
chosen Node-3 sticky witnesses.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

/-- Assemble a full one-scale grain output at the Córdoba critical scale.
The analytic loss gap pays only the final paper-to-internal bridge factor
`10`; all geometric pruning is recorded separately by `massLoss`. -/
theorem propertyThreeCommonHull_critical_one_scale_output
    {delta sigma stickyDataLoss sourceLoss sourceADLoss targetLoss tau
      epsilon₁ epsilon₃ : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (planeMap : {point : Point3 // point ∈ sourceShading.union} → Point3)
    (hplaneUnit : ∀ point, ‖planeMap point‖ = 1)
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyDataLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (hsourceCubical : WZ1PaperIsCubicalShading sourceShading)
    (scaleFactor : ℕ) (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * delta)
    (sourceExtremal :
      WZ2PaperCroppedIsExtremal
        sigma sourceLoss family sourceShading)
    (sourceCWA :
      WZ2PaperConvexWolffBound family
        (Kakeya.realRpowENN delta (-sourceLoss)))
    (massLoss : ENNReal)
    (hmassLossPos : 0 < massLoss)
    (hmassLossFinite : massLoss ≠ ⊤)
    (hmass : massLoss⁻¹ * sourceShading.mass ≤
      (ambientPropertyThreeCommonHull sticky propP.propertyThree).mass)
    (hloss : sourceLoss ≤ targetLoss)
    (hslack : massLoss * Kakeya.realRpowENN delta targetLoss ≤
      Kakeya.realRpowENN delta sourceLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (htargetLoss : 0 < targetLoss)
    (hsourceADLoss : 0 < sourceADLoss)
    (hADGap : sourceADLoss < targetLoss)
    (hADSmall :
      delta ≤ Real.rpow (10 : ℝ)
        (-1 / (targetLoss - sourceADLoss)))
    (htau_def : tau = rho.1 * Real.sqrt 3)
    (htau_pos : 0 < tau)
    (htau_le_20L : tau ≤ 20 * rho.1)
    (hL_le_tau : rho.1 ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * rho.1)
    (htau_le_one : tau ≤ 1)
    (hL_small : rho.1 ≤ 1 / 1000)
    (hL_pos : 0 < rho.1)
    (hL_half : rho.1 ≤ 1 / 2)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (heps₁_pos : 0 < epsilon₁)
    (heps₁_lt : epsilon₁ < 1 / 20)
    (heps₃_pos : 0 < epsilon₃)
    (heps₃_def : epsilon₃ = 1 - 2 * epsilon₁)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (L₀_log : ℝ)
    (hL_le_L0_log : rho.1 ≤ L₀_log)
    (h_log_main : 0 < epsilon₁ → ∀ (L' : ℝ), 0 < L' → L' ≤ L₀_log →
      ∀ (k : ℕ), 0 < k → (k : ℝ) ≤ 100 / L' ^ 3 →
        Real.rpow L' epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (h_propertyThree_full :
      ∀ (j : Fin sticky.coarse.card) (p : Point3),
        p ∈ propP.propertyThree.carrier j →
          Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
            volume (propP.propertyThree.carrier j ∩ Metric.closedBall p tau))
    (h_ax_condition :
      4 * (6 * rho.1) ^ 2 ≤
        (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2)
    (hL_lower : Real.rpow delta stickyDataLoss ≤ rho.1)
    (hL_bound : rho.1 ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
    (hstickyLoss_le_sourceAD : 3 * stickyDataLoss ≤ sourceADLoss) :
    ∃ data : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := targetLoss)
        (rho := 48 * rho.1 ^ 2) (Y := sourceShading) planeMap,
      data.shading =
        ambientPropertyThreeCommonHull sticky propP.propertyThree := by
  let paperConstant : ENNReal :=
    Kakeya.realRpowENN delta (-sourceADLoss)
  apply propertyThreeCommonHull_one_scale_output_of_paperAD
    (stickyLoss := sourceLoss) (targetLoss := targetLoss)
    (queryScale := 48 * rho.1 ^ 2)
    planeMap hplaneUnit sticky propP hsourceCubical
    scaleFactor hscaleFactor hrhoAligned sourceExtremal sourceCWA
    massLoss paperConstant hmassLossPos hmassLossFinite hmass hloss hslack
    hdelta hdeltaOne.le htargetLoss
  · intro point hpoint
    have hpullback : point ∈
        (propertyThreeFinePullbackShading
          sticky.cover sticky.refined propP.propertyThree).union := by
      rw [← ambientPropertyThreeCommonHull_union sticky propP.propertyThree]
      exact hpoint
    let sourcePoint : {point : Point3 // point ∈ sourceShading.union} :=
      ⟨point, paperSubshading_union
        (ambientPropertyThreeCommonHull_subshading
          sticky propP.propertyThree) hpoint⟩
    let S : Set Point3 := sticky.croppedCoarseShading.union ∩
      Metric.closedBall point (4 * tau)
    have hinvCube : Real.rpow rho.1 (-3 : ℝ) ≤
        Real.rpow delta (-sourceADLoss) :=
      aligned_scale_inv_cube_bound hdelta hdeltaOne hL_lower
        hstickyLoss_le_sourceAD
    have hcritical :=
      propertyThreeFinePullback_high_local_ad_at_critical_scale_of_inv_cube_bound
        sticky.balanced epsilon₁ epsilon₃ propP
        (planeMap sourcePoint) (hplaneUnit sourcePoint) point hpullback
        S rfl
        (sticky.croppedCoarseShading.union_measurable.inter
          Metric.isClosed_closedBall.measurableSet)
        (by intro other hother; exact hother.2)
        htau_def htau_pos htau_le_20L hL_le_tau htau_sq htau_le_one
        hL_small hL_pos hL_half hsigma_pos hsigma_lt_one heps₁_pos
        heps₁_lt heps₃_pos heps₃_def heps_sum L₀_log hL_le_L0_log
        h_log_main h_propertyThree_full h_ax_condition hdelta hdeltaOne
        hsourceADLoss hL_bound hinvCube
    exact ambientPropertyThreeCommonHull_ad
      sticky propP.propertyThree (planeMap sourcePoint) point
      paperConstant hcritical
  · have habsorb := realRpowENN_neg_loss_gap_absorb
      (factor := (10 : ℝ)) (delta := delta)
      (sourceLoss := sourceADLoss) (targetLoss := targetLoss)
      (by norm_num) hADGap hdelta hADSmall
    norm_num [paperConstant] at habsorb ⊢
    exact habsorb

end Kakeya.Assouad.PureWZ2

end
