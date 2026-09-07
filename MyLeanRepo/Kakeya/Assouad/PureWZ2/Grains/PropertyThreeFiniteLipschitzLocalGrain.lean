import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSpatialPropertyThreePullback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ExtremalCWATransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinePullbackAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SingleCriticalEveryScaleLocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.AlignedCoarseScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TransversePairPaper
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RelaxedLocalGrainData

/-!
# Property-Three local grains after finite plane-map coordination

The finite nearby-cover construction first produces a genuine Lipschitz plane
map on a subshading of the Property-Three common hull.  The Córdoba estimate
is monotone under this final spatial restriction, so it may be proved on the
whole Property-Three pullback and then restricted to the same final shading.

This module records that composition without extending the final plane map to
points on which it was never constructed.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

/-- Put a finitely coordinated genuine plane map and the Property-Three
Córdoba estimate on one final shading.  The mass retained by the finite
coordination is an explicit premise. -/
theorem propertyThree_subshading_every_scale_relaxed_local_grain
    {delta sigma stickyLoss sourceADLoss targetLoss tau epsilon₁ epsilon₃ : ℝ}
    {L : NNReal}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading final : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (planeMap : PaperWZ1WeakPlaneMapData final delta)
    (hplaneLipschitz : LipschitzWith L
      (fun point : {point : Point3 // point ∈ final.union} =>
        planeMap.planeMap point))
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (hfinalSub : PaperIsSubshading final
      (ambientPropertyThreeCommonHull sticky propP.propertyThree))
    (hfinalCubical : WZ1PaperIsCubicalShading final)
    (scaleFactor : ℕ)
    (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * delta)
    (sourceExtremal :
      WZ2PaperCroppedIsExtremal
        sigma stickyLoss family sourceShading)
    (sourceCWA :
      WZ2PaperConvexWolffBound family
        (Kakeya.realRpowENN delta (-stickyLoss)))
    (massLoss : ENNReal)
    (hmassLossPos : 0 < massLoss)
    (hmassLossFinite : massLoss ≠ ⊤)
    (hmass : massLoss⁻¹ * sourceShading.mass ≤ final.mass)
    (hloss : stickyLoss ≤ targetLoss)
    (hslack : massLoss * Kakeya.realRpowENN delta targetLoss ≤
      Kakeya.realRpowENN delta stickyLoss)
    (hdelta : 0 < delta)
    (hdeltaOne : delta < 1)
    (htargetLoss : 0 < targetLoss)
    (hsourceADLoss : 0 < sourceADLoss)
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
    (h_log_main : 0 < epsilon₁ → ∀ L' : ℝ, 0 < L' → L' ≤ L₀_log →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / L' ^ 3 →
        Real.rpow L' epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (h_propertyThree_full :
      ∀ parent : Fin sticky.coarse.card, ∀ point : Point3,
        point ∈ propP.propertyThree.carrier parent →
          Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
              ENNReal.ofReal tau ≤
            volume (propP.propertyThree.carrier parent ∩
              Metric.closedBall point tau))
    (h_ax_condition :
      4 * (6 * rho.1) ^ 2 ≤
        (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2)
    (hL_lower : Real.rpow delta stickyLoss ≤ rho.1)
    (hL_bound : rho.1 ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
    (hstickyLoss_le_sourceAD : 3 * stickyLoss ≤ sourceADLoss)
    (hsmallCost :
      let criticalScale := 48 * rho.1 ^ 2
      let sourceConstant := Kakeya.realRpowENN delta (-sourceADLoss)
      10 * ((10 * sourceConstant) *
          ENNReal.ofReal (10 * criticalScale / delta)) ≤
        Kakeya.realRpowENN delta (-targetLoss))
    (hlargeEndpoint :
      let criticalScale := 48 * rho.1 ^ 2
      3 * (2 / Real.sqrt criticalScale) ^ sigma ≤
        delta ^ (-targetLoss)) :
    WZ2PaperCroppedIsExtremal sigma targetLoss family final ∧
      WZ2PaperConvexWolffBound family
        (Kakeya.realRpowENN delta (-targetLoss)) ∧
      Nonempty (PureWZ2RelaxedLocalGrainData final sigma
        (Kakeya.realRpowENN delta (-targetLoss)) L) := by
  have hcommonSub : PaperIsSubshading
      (ambientPropertyThreeCommonHull sticky propP.propertyThree)
      sourceShading :=
    ambientPropertyThreeCommonHull_subshading sticky propP.propertyThree
  have hfinalSourceSub : PaperIsSubshading final sourceShading :=
    fun index => (hfinalSub index).trans (hcommonSub index)
  have hfinalExtremal :
      WZ2PaperCroppedIsExtremal sigma targetLoss family final :=
    transfer_cropped_extremal_to_subshading
      massLoss hmassLossPos hmassLossFinite sourceExtremal hfinalSourceSub
      hmass hfinalCubical hloss hslack hdelta hdeltaOne.le htargetLoss
  have hfinalCWA : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-targetLoss)) :=
    transfer_cwa_to_subshading
      (_shading1 := sourceShading) (_shading2 := final)
      sourceCWA hloss hdelta hdeltaOne.le
  let finalPlaneMap : {point : Point3 // point ∈ final.union} → Point3 :=
    fun point => planeMap.planeMap point
  have hfinalLipschitz : LipschitzWith L finalPlaneMap :=
    hplaneLipschitz
  have hfinalUnit : ∀ point, ‖finalPlaneMap point‖ = 1 := by
    intro point
    exact planeMap.unit point point.prop
  have hfinalIncidence : ∀ index point,
      ∀ hpoint : point ∈ final.carrier index,
        |inner ℝ (family.tube index).direction
          (finalPlaneMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ delta := by
    intro index point hpoint
    exact planeMap.incidence index point hpoint
  let criticalScale : ℝ := 48 * rho.1 ^ 2
  let sourceConstant : ENNReal :=
    Kakeya.realRpowENN delta (-sourceADLoss)
  have hcriticalPos : 0 < criticalScale := by
    dsimp only [criticalScale]
    positivity
  have hcriticalOne : criticalScale ≤ 1 := by
    dsimp only [criticalScale]
    nlinarith [sq_nonneg (rho.1 : ℝ)]
  have hcritical : ∀ point : {point : Point3 // point ∈ final.union},
      PureWZ2PaperADSet1
        (scalarProjection (finalPlaneMap point)
          (final.union ∩ Metric.closedBall (point : Point3)
            (Real.sqrt criticalScale)))
        criticalScale (1 - sigma) sourceConstant := by
    intro point
    have hpointCommon : (point : Point3) ∈
        (ambientPropertyThreeCommonHull sticky propP.propertyThree).union := by
      rcases point.prop with ⟨index, hindex⟩
      exact ⟨index, hfinalSub index hindex⟩
    have hpullback : (point : Point3) ∈
        (propertyThreeFinePullbackShading
          sticky.cover sticky.refined propP.propertyThree).union := by
      rw [← ambientPropertyThreeCommonHull_union sticky propP.propertyThree]
      exact hpointCommon
    let S : Set Point3 := sticky.croppedCoarseShading.union ∩
      Metric.closedBall (point : Point3) (4 * tau)
    have hinvCube : Real.rpow rho.1 (-3 : ℝ) ≤
        Real.rpow delta (-sourceADLoss) :=
      aligned_scale_inv_cube_bound hdelta hdeltaOne hL_lower
        hstickyLoss_le_sourceAD
    have hAD :=
      propertyThreeFinePullback_high_local_ad_at_critical_scale_of_inv_cube_bound
        sticky.balanced epsilon₁ epsilon₃ propP
        (finalPlaneMap point) (hfinalUnit point) point hpullback
        S rfl
        (sticky.croppedCoarseShading.union_measurable.inter
          Metric.isClosed_closedBall.measurableSet)
        (by intro other hother; exact hother.2)
        htau_def htau_pos htau_le_20L hL_le_tau htau_sq htau_le_one
        hL_small hL_pos hL_half hsigma_pos hsigma_lt_one heps₁_pos
        heps₁_lt heps₃_pos heps₃_def heps_sum L₀_log hL_le_L0_log
        h_log_main h_propertyThree_full h_ax_condition hdelta hdeltaOne
        hsourceADLoss hL_bound hinvCube
    have hcommonAD := ambientPropertyThreeCommonHull_ad
      sticky propP.propertyThree (finalPlaneMap point) point
      sourceConstant hAD
    apply hcommonAD.mono_set
    rintro value ⟨other, hother, rfl⟩
    exact ⟨other, ⟨by
      rcases hother.1 with ⟨index, hindex⟩
      exact ⟨index, hfinalSub index hindex⟩, hother.2⟩, rfl⟩
  let localGrains : PureWZ2RelaxedLocalGrainData final sigma
      (Kakeya.realRpowENN delta (-targetLoss)) L := {
    planeMap := finalPlaneMap
    planeMap_lipschitz := hfinalLipschitz
    planeMap_unit := hfinalUnit
    planeMap_incidence := hfinalIncidence
    local_ad := local_projection_ad_all_scales_of_critical
      finalPlaneMap hfinalUnit hdelta hdeltaOne.le hsigma_pos
      hsigma_lt_one htargetLoss hcriticalPos hcriticalOne sourceConstant
      hcritical hsmallCost hlargeEndpoint
  }
  exact ⟨hfinalExtremal, hfinalCWA, ⟨localGrains⟩⟩

/-- Strict-Lipschitz compatibility wrapper for existing callers. -/
theorem propertyThree_subshading_every_scale_local_grain
    {delta sigma stickyLoss sourceADLoss targetLoss tau epsilon₁ epsilon₃ : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading final : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (planeMap : PaperWZ1WeakPlaneMapData final delta)
    (hplaneLipschitz : LipschitzWith 1
      (fun point : {point : Point3 // point ∈ final.union} =>
        planeMap.planeMap point))
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (hfinalSub : PaperIsSubshading final
      (ambientPropertyThreeCommonHull sticky propP.propertyThree))
    (hfinalCubical : WZ1PaperIsCubicalShading final)
    (scaleFactor : ℕ)
    (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * delta)
    (sourceExtremal :
      WZ2PaperCroppedIsExtremal
        sigma stickyLoss family sourceShading)
    (sourceCWA :
      WZ2PaperConvexWolffBound family
        (Kakeya.realRpowENN delta (-stickyLoss)))
    (massLoss : ENNReal)
    (hmassLossPos : 0 < massLoss)
    (hmassLossFinite : massLoss ≠ ⊤)
    (hmass : massLoss⁻¹ * sourceShading.mass ≤ final.mass)
    (hloss : stickyLoss ≤ targetLoss)
    (hslack : massLoss * Kakeya.realRpowENN delta targetLoss ≤
      Kakeya.realRpowENN delta stickyLoss)
    (hdelta : 0 < delta)
    (hdeltaOne : delta < 1)
    (htargetLoss : 0 < targetLoss)
    (hsourceADLoss : 0 < sourceADLoss)
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
    (h_log_main : 0 < epsilon₁ → ∀ L' : ℝ, 0 < L' → L' ≤ L₀_log →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / L' ^ 3 →
        Real.rpow L' epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (h_propertyThree_full :
      ∀ parent : Fin sticky.coarse.card, ∀ point : Point3,
        point ∈ propP.propertyThree.carrier parent →
          Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
              ENNReal.ofReal tau ≤
            volume (propP.propertyThree.carrier parent ∩
              Metric.closedBall point tau))
    (h_ax_condition :
      4 * (6 * rho.1) ^ 2 ≤
        (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2)
    (hL_lower : Real.rpow delta stickyLoss ≤ rho.1)
    (hL_bound : rho.1 ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
    (hstickyLoss_le_sourceAD : 3 * stickyLoss ≤ sourceADLoss)
    (hsmallCost :
      let criticalScale := 48 * rho.1 ^ 2
      let sourceConstant := Kakeya.realRpowENN delta (-sourceADLoss)
      10 * ((10 * sourceConstant) *
          ENNReal.ofReal (10 * criticalScale / delta)) ≤
        Kakeya.realRpowENN delta (-targetLoss))
    (hlargeEndpoint :
      let criticalScale := 48 * rho.1 ^ 2
      3 * (2 / Real.sqrt criticalScale) ^ sigma ≤
        delta ^ (-targetLoss)) :
    WZ2PaperCroppedIsExtremal sigma targetLoss family final ∧
      WZ2PaperConvexWolffBound family
        (Kakeya.realRpowENN delta (-targetLoss)) ∧
      Nonempty (PureWZ2LocalGrainData final sigma
        (Kakeya.realRpowENN delta (-targetLoss))) := by
  rcases propertyThree_subshading_every_scale_relaxed_local_grain
      planeMap hplaneLipschitz sticky propP hfinalSub hfinalCubical
      scaleFactor hscaleFactor hrhoAligned sourceExtremal sourceCWA
      massLoss hmassLossPos hmassLossFinite hmass hloss hslack hdelta
      hdeltaOne htargetLoss hsourceADLoss htau_def htau_pos htau_le_20L
      hL_le_tau htau_sq htau_le_one hL_small hL_pos hL_half hsigma_pos
      hsigma_lt_one heps₁_pos heps₁_lt heps₃_pos heps₃_def heps_sum
      L₀_log hL_le_L0_log h_log_main h_propertyThree_full h_ax_condition
      hL_lower hL_bound hstickyLoss_le_sourceAD hsmallCost hlargeEndpoint
    with ⟨hextremal, hcwa, ⟨localGrains⟩⟩
  exact ⟨hextremal, hcwa, ⟨localGrains.to_strict⟩⟩

end Kakeya.Assouad.PureWZ2

end
