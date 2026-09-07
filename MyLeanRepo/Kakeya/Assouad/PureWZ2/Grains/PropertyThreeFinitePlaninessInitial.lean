import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BalancedFinitePlaniness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFiniteLipschitzLocalGrain
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.NormalizedCardinalityFloor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RetainedZeroExtensionFinitePlaniness

/-!
# Paper-order initial finite planiness and graininess package

This module joins the two outputs used at the start of Proposition 6.3:
finite-Lipschitz planiness on a genuine refinement and every-scale local AD
on that same refinement.  It does not ask for a plane map on the complete
source shading.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

/-- The actual retained fraction from the sticky refinement followed by the
Property-Three common-spatial pullback. -/
def propertyThreeCommonHullRetainedFactor
    {delta sigma stickyLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent) : ENNReal :=
  (2 * stickyCoarseMultiplicityCap sticky *
      stickyCoarseMultiplicityCap sticky *
      stickyFiberMultiplicityCap sticky)⁻¹ *
    wz2PaperPureRefinementFraction delta logExponent

/-- A positive finite mass-loss constant dominating the reciprocal of the
actual common-hull retained fraction. -/
def propertyThreeCommonHullMassLoss
    {delta sigma stickyLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent) : ENNReal :=
  1 + (propertyThreeCommonHullRetainedFactor sticky)⁻¹

lemma propertyThreeCommonHullRetainedFactor_pos
    {delta sigma stickyLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (hdelta : 0 < delta)
    (hdeltaOne : delta < 1) :
    0 < propertyThreeCommonHullRetainedFactor sticky := by
  have hcapFinite :
      (2 * stickyCoarseMultiplicityCap sticky *
        stickyCoarseMultiplicityCap sticky *
        stickyFiberMultiplicityCap sticky : ENNReal) ≠ ⊤ := by
    have hcoarseFinite : stickyCoarseMultiplicityCap sticky ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · simp [Kakeya.realRpowENN]
      · simp [Kakeya.Streamlined.TubeFamily.enncard]
    have hfiberFinite : stickyFiberMultiplicityCap sticky ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · simp [Kakeya.realRpowENN]
      · simp [Kakeya.Streamlined.TubeFamily.enncard]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) hcoarseFinite)
        hcoarseFinite) hfiberFinite
  have hfraction :=
    pure_refinement_fraction_pos_ne_top hdelta hdeltaOne logExponent
  exact ENNReal.mul_pos
    (ENNReal.inv_pos.mpr hcapFinite).ne' hfraction.1.ne'

lemma propertyThreeCommonHullMassLoss_pos
    {delta sigma stickyLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent) :
    0 < propertyThreeCommonHullMassLoss sticky := by
  exact zero_lt_one.trans_le (le_add_right le_rfl)

lemma propertyThreeCommonHullMassLoss_ne_top
    {delta sigma stickyLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (hdelta : 0 < delta)
    (hdeltaOne : delta < 1) :
    propertyThreeCommonHullMassLoss sticky ≠ ⊤ := by
  rw [propertyThreeCommonHullMassLoss, ENNReal.add_ne_top]
  exact ⟨by norm_num, ENNReal.inv_ne_top.mpr
    (propertyThreeCommonHullRetainedFactor_pos
      sticky hdelta hdeltaOne).ne'⟩

lemma propertyThreeCommonHullMassLoss_inv_mul_source_mass_le
    {delta sigma stickyLoss tau epsilon₁ epsilon₃ : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (hdelta : 0 < delta) :
    (propertyThreeCommonHullMassLoss sticky)⁻¹ * sourceShading.mass ≤
      (ambientPropertyThreeCommonHull sticky propP.propertyThree).mass := by
  have hretained :
      propertyThreeCommonHullRetainedFactor sticky * sourceShading.mass ≤
        (ambientPropertyThreeCommonHull sticky propP.propertyThree).mass := by
    simpa [propertyThreeCommonHullRetainedFactor, mul_assoc] using
      ambientPropertyThreeCommonHull_source_mass_lower
        sticky propP.propertyThree hdelta
        (fun index => (propP.propertyThree_sub index).trans
          (propP.propertyOne_sub index))
        propP.propertyThree_cubical propP.propertyThree_mass
  have hinvLe : (propertyThreeCommonHullMassLoss sticky)⁻¹ ≤
      propertyThreeCommonHullRetainedFactor sticky := by
    rw [ENNReal.inv_le_iff_inv_le]
    exact le_add_left le_rfl
  exact (mul_le_mul_right' hinvLe sourceShading.mass).trans hretained

/-- Transfer cropped extremality to the honest common-spatial
Property-Three pullback, paying exactly the mass loss derived above. -/
theorem propertyThreeCommonHull_extremal
    {delta sigma stickyLoss targetLoss tau epsilon₁ epsilon₃ : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (hsourceCubical : WZ1PaperIsCubicalShading sourceShading)
    (scaleFactor : ℕ)
    (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * delta)
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma stickyLoss family sourceShading)
    (hdeltaOne : delta < 1)
    (hloss : stickyLoss ≤ targetLoss)
    (hslack : propertyThreeCommonHullMassLoss sticky *
        Kakeya.realRpowENN delta targetLoss ≤
      Kakeya.realRpowENN delta stickyLoss)
    (htargetLoss : 0 < targetLoss) :
    WZ2PaperCroppedIsExtremal sigma targetLoss family
      (ambientPropertyThreeCommonHull sticky propP.propertyThree) := by
  have hpullbackCubical : WZ1PaperIsCubicalShading
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propP.propertyThree) :=
    propertyThreeFinePullbackShading_cubical sticky.cover sticky.refined
      propP.propertyThree sticky.refined_cubical scaleFactor
      hscaleFactor hrhoAligned
  have hcommonCubical : WZ1PaperIsCubicalShading
      (ambientPropertyThreeCommonHull sticky propP.propertyThree) :=
    ambientPropertyThreeCommonHull_cubical sticky propP.propertyThree
      hsourceCubical hpullbackCubical
  exact transfer_cropped_extremal_to_subshading
    (propertyThreeCommonHullMassLoss sticky)
    (propertyThreeCommonHullMassLoss_pos sticky)
    (propertyThreeCommonHullMassLoss_ne_top sticky
      sourceExtremal.delta_pos hdeltaOne)
    sourceExtremal
    (ambientPropertyThreeCommonHull_subshading sticky propP.propertyThree)
    (propertyThreeCommonHullMassLoss_inv_mul_source_mass_le
      sticky propP sourceExtremal.delta_pos)
    hcommonCubical hloss hslack sourceExtremal.delta_pos
    sourceExtremal.delta_le_one htargetLoss

/-- Put a finite-planiness refinement of the Property-Three common hull into
the relaxed every-scale local-grain interface.  The two mass losses are
composed in the same order as the two paper refinements. -/
theorem propertyThree_finite_planiness_initial_local_grains
    {delta sigma stickyLoss sourceADLoss targetLoss tau epsilon₁ epsilon₃
      coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (bounded : BoundedBalancedFinitePlaninessData
      (coefficient := coefficient)
      (ambientPropertyThreeCommonHull sticky propP.propertyThree) delta)
    (scaleFactor : ℕ)
    (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * delta)
    (sourceExtremal :
      WZ2PaperCroppedIsExtremal
        sigma stickyLoss family sourceShading)
    (sourceCWA :
      WZ2PaperConvexWolffBound family
        (Kakeya.realRpowENN delta (-stickyLoss)))
    (hloss : stickyLoss ≤ targetLoss)
    (hslack :
      (propertyThreeCommonHullMassLoss sticky * bounded.data.massLoss) *
          Kakeya.realRpowENN delta targetLoss ≤
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
    WZ2PaperCroppedIsExtremal sigma targetLoss family
        bounded.data.refinement.shading ∧
      WZ2PaperConvexWolffBound family
        (Kakeya.realRpowENN delta (-targetLoss)) ∧
      Nonempty (PureWZ2RelaxedLocalGrainData
        bounded.data.refinement.shading sigma
        (Kakeya.realRpowENN delta (-targetLoss))
        (Real.toNNReal coefficient)) := by
  let final := bounded.data.refinement.shading
  let sourceMap := bounded.data.refinement.planeMap
  let planeMap : PaperWZ1WeakPlaneMapData final delta := {
    planeMap := sourceMap.planeMap
    measurable := sourceMap.measurable
    unit := sourceMap.unit
    incidence := by
      intro index point hpoint
      exact (sourceMap.incidence index point hpoint).trans
        bounded.incidence_le
  }
  have hplaneLipschitz : LipschitzWith (Real.toNNReal coefficient)
      (fun point : {point : Point3 // point ∈ final.union} =>
        planeMap.planeMap point) :=
    bounded.data.refinement.lipschitz
  let totalMassLoss : ENNReal :=
    propertyThreeCommonHullMassLoss sticky * bounded.data.massLoss
  have hcommonMassLossPos :
      0 < propertyThreeCommonHullMassLoss sticky :=
    propertyThreeCommonHullMassLoss_pos sticky
  have hcommonMassLossFinite :
      propertyThreeCommonHullMassLoss sticky ≠ ⊤ :=
    propertyThreeCommonHullMassLoss_ne_top sticky hdelta hdeltaOne
  have hcommonMass :
      (propertyThreeCommonHullMassLoss sticky)⁻¹ * sourceShading.mass ≤
        (ambientPropertyThreeCommonHull sticky propP.propertyThree).mass :=
    propertyThreeCommonHullMassLoss_inv_mul_source_mass_le
      sticky propP hdelta
  have htotalMassLossPos : 0 < totalMassLoss :=
    ENNReal.mul_pos hcommonMassLossPos.ne'
      bounded.data.massLoss_pos.ne'
  have htotalMassLossFinite : totalMassLoss ≠ ⊤ :=
    ENNReal.mul_ne_top hcommonMassLossFinite
      bounded.data.massLoss_ne_top
  have htotalMass : totalMassLoss⁻¹ * sourceShading.mass ≤ final.mass := by
    calc
      totalMassLoss⁻¹ * sourceShading.mass =
          bounded.data.massLoss⁻¹ *
            ((propertyThreeCommonHullMassLoss sticky)⁻¹ *
              sourceShading.mass) := by
        dsimp only [totalMassLoss]
        rw [ENNReal.mul_inv
          (Or.inl hcommonMassLossPos.ne')
          (Or.inl hcommonMassLossFinite)]
        ring
      _ ≤ bounded.data.massLoss⁻¹ *
          (ambientPropertyThreeCommonHull
            sticky propP.propertyThree).mass := by
        exact mul_le_mul_left' hcommonMass _
      _ ≤ final.mass :=
        bounded.data.massLoss_inv_mul_source_mass_le
  exact propertyThree_subshading_every_scale_relaxed_local_grain
    planeMap hplaneLipschitz sticky propP
    bounded.data.refinement.subshading bounded.data.refinement.cubical
    scaleFactor hscaleFactor hrhoAligned sourceExtremal sourceCWA
    totalMassLoss htotalMassLossPos htotalMassLossFinite htotalMass
    hloss (by simpa [totalMassLoss] using hslack) hdelta hdeltaOne
    htargetLoss hsourceADLoss htau_def htau_pos htau_le_20L hL_le_tau
    htau_sq htau_le_one hL_small hL_pos hL_half hsigma_pos
    hsigma_lt_one heps₁_pos heps₁_lt heps₃_pos heps₃_def heps_sum
    L₀_log hL_le_L0_log h_log_main h_propertyThree_full h_ax_condition
    hL_lower hL_bound hstickyLoss_le_sourceAD hsmallCost hlargeEndpoint

/-- Run the already-proved finite planiness dichotomy on the honest common
Property-Three hull, then attach local AD to its actual selected shading. -/
theorem propertyThree_run_finite_planiness_initial
    {delta sigma stickyLoss planinessLoss sourceADLoss targetLoss
      densityLoss kappa eta coefficient tau epsilon₁ epsilon₃ : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma stickyLoss family sourceShading)
    (sourceCWA : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-stickyLoss)))
    (commonExtremal : WZ2PaperCroppedIsExtremal
      sigma planinessLoss family
      (ambientPropertyThreeCommonHull sticky propP.propertyThree))
    (hline : WZ1PaperIsLineClass family)
    (schedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * planinessLoss)
    (hplaninessLoss : 0 < planinessLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hsmall : Kakeya.realRpowENN delta planinessLoss < 1 / 4)
    (hfixedAbsorb :
      (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * planinessLoss))
    (hsparsePackage : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa)
      (ambientPropertyThreeCommonHull sticky propP.propertyThree)
      (Kakeya.realRpowENN delta
        (2 - sigma + 3 * planinessLoss)),
        Nonempty (SparseRelativeBandCVPackage
          (ambientPropertyThreeCommonHull sticky propP.propertyThree)
          prepared))
    (hdenseIncidence : eta ≤ delta)
    (hsparseIncidence : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa)
      (ambientPropertyThreeCommonHull sticky propP.propertyThree)
      (Kakeya.realRpowENN delta
        (2 - sigma + 3 * planinessLoss)),
      ∀ package : SparseRelativeBandCVPackage
        (ambientPropertyThreeCommonHull sticky propP.propertyThree)
        prepared, package.tau / kappa ≤ delta)
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaPositive : 0 < kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (heta : 0 < eta)
    (hetaHalf : eta ≤ 1 / 2)
    (hcoefficient : 0 < coefficient)
    (hactualSmall : ∀ coordinate, coordinate < 1 →
      (commonExtremal.cwa_nearby_scales.chosenNearby
        (schedule.requested coordinate)).rho < 1 / 8)
    (hparentKappa : ∀ coordinate, coordinate < 1 →
      8 * (commonExtremal.cwa_nearby_scales.chosenNearby
        (schedule.requested coordinate)).rho < kappa)
    (scaleFactor : ℕ)
    (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * delta)
    (hstickyTarget : stickyLoss ≤ targetLoss)
    (htotalSlack : ∀ bounded : BoundedBalancedFinitePlaninessData
      (coefficient := coefficient)
      (ambientPropertyThreeCommonHull sticky propP.propertyThree) delta,
      (propertyThreeCommonHullMassLoss sticky * bounded.data.massLoss) *
          Kakeya.realRpowENN delta targetLoss ≤
        Kakeya.realRpowENN delta stickyLoss)
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
    ∃ bounded : BoundedBalancedFinitePlaninessData
        (coefficient := coefficient)
        (ambientPropertyThreeCommonHull sticky propP.propertyThree) delta,
      WZ2PaperCroppedIsExtremal sigma targetLoss family
          bounded.data.refinement.shading ∧
        WZ2PaperConvexWolffBound family
          (Kakeya.realRpowENN delta (-targetLoss)) ∧
        Nonempty (PureWZ2RelaxedLocalGrainData
          bounded.data.refinement.shading sigma
          (Kakeya.realRpowENN delta (-targetLoss))
          (Real.toNNReal coefficient)) := by
  rcases finite_planiness_of_extremal commonExtremal hline schedule
      hdensityLoss hplaninessLoss hdeltaSmall hsmall hfixedAbsorb
      hsparsePackage hdenseIncidence hsparseIncidence hkappaNonnegative
      hkappaPositive hkappaHalf heta hetaHalf hcoefficient hactualSmall
      hparentKappa with ⟨bounded⟩
  refine ⟨bounded, ?_⟩
  exact propertyThree_finite_planiness_initial_local_grains
    sticky propP bounded scaleFactor hscaleFactor hrhoAligned
    sourceExtremal sourceCWA hstickyTarget (htotalSlack bounded)
    commonExtremal.delta_pos hdeltaOne htargetLoss hsourceADLoss
    htau_def htau_pos htau_le_20L hL_le_tau htau_sq htau_le_one
    hL_small hL_pos hL_half hsigma_pos hsigma_lt_one heps₁_pos
    heps₁_lt heps₃_pos heps₃_def heps_sum L₀_log hL_le_L0_log
    h_log_main h_propertyThree_full h_ax_condition hL_lower hL_bound
    hstickyLoss_le_sourceAD hsmallCost hlargeEndpoint

end Kakeya.Assouad.PureWZ2

end
