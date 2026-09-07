import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeSelectedLocalGrain
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinitePlaninessInitial
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFiniteGridLocalGrain

/-!
# Preliminary local grains for Proposition 6.3

This module packages the one-sticky, one-Property-Three construction playing
the role of the preliminary Lemmas 4.8 and 4.12 in the paper. It ends on one
genuine subshading of the original normalized family and records both the
local-grain estimate and the extremal/CWA data needed for the first
ordinary-trace re-entry.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- The preliminary local-grain output before the first exact-power-scale
application of Proposition 6.2. -/
structure Proposition63PreliminaryLocalGrainData
    {delta sigma initialInputLoss normalizationLoss localLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent) where
  shading : WZ1PaperTubeShading initialNormalized.croppedFamily
  subshading : PaperIsSubshading shading initialNormalized.croppedRefined
  cubical : WZ1PaperIsCubicalShading shading
  extremal : WZ2PaperCroppedIsExtremal sigma reentryLoss
    initialNormalized.croppedFamily shading
  topLevelCWA : WZ2PaperConvexWolffBound initialNormalized.croppedFamily
    (Kakeya.realRpowENN delta (-reentryLoss))
  incidence : ℝ
  lipschitz : NNReal
  incidence_nonnegative : 0 ≤ incidence
  localGrains : Proposition63InitialWeakLocalGrainData
    (incidence := incidence) shading sigma
    (Kakeya.realRpowENN delta (-localLoss)) lipschitz

/-- Assemble the preliminary output from one Property-Three common hull and
one finite-planiness refinement on that same hull. -/
theorem proposition63_preliminary_local_grain_of_bounded
    {delta sigma initialInputLoss normalizationLoss preliminaryStickyLoss
      producerLoss localLoss reentryLoss sourceADLoss tau epsilon₁ epsilon₃
      coefficient : ℝ}
    {rho : WZ2PaperRequestedScale delta}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent logExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := preliminaryStickyLoss)
      initialNormalized.croppedRefined rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (bounded : BoundedBalancedFinitePlaninessData
      (coefficient := coefficient)
      (ambientPropertyThreeCommonHull sticky propP.propertyThree) delta)
    (hboundedMass : 0 < bounded.data.refinement.shading.mass)
    (scaleFactor : ℕ) (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * delta)
    (hnormalizationSticky : normalizationLoss ≤ preliminaryStickyLoss)
    (hstickyProducer : preliminaryStickyLoss ≤ producerLoss)
    (hproducerLocal : producerLoss ≤ localLoss)
    (hproducerReentry : producerLoss ≤ reentryLoss)
    (hslack :
      (propertyThreeCommonHullMassLoss sticky * bounded.data.massLoss) *
          Kakeya.realRpowENN delta producerLoss ≤
        Kakeya.realRpowENN delta preliminaryStickyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hproducerLoss : 0 < producerLoss)
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
            MeasureTheory.volume
              (propP.propertyThree.carrier parent ∩
                Metric.closedBall point tau))
    (h_ax_condition :
      4 * (6 * rho.1) ^ 2 ≤
        (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2)
    (hL_lower : Real.rpow delta preliminaryStickyLoss ≤ rho.1)
    (hL_bound : rho.1 ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
    (hstickyLoss_le_sourceAD : 3 * preliminaryStickyLoss ≤ sourceADLoss)
    (hsmallCost :
      let criticalScale := 48 * rho.1 ^ 2
      let sourceConstant := Kakeya.realRpowENN delta (-sourceADLoss)
      10 * ((10 * sourceConstant) *
          ENNReal.ofReal (10 * criticalScale / delta)) ≤
        Kakeya.realRpowENN delta (-producerLoss))
    (hlargeEndpoint :
      let criticalScale := 48 * rho.1 ^ 2
      3 * (2 / Real.sqrt criticalScale) ^ sigma ≤
        delta ^ (-producerLoss)) :
    Nonempty (Proposition63PreliminaryLocalGrainData
      (localLoss := localLoss) (reentryLoss := reentryLoss)
      initialNormalized) := by
  have hsourceExtremal : WZ2PaperCroppedIsExtremal
      sigma preliminaryStickyLoss initialNormalized.croppedFamily
        initialNormalized.croppedRefined :=
    initialNormalized.final_extremal.mono_loss hnormalizationSticky
  have hsourceCWA : WZ2PaperConvexWolffBound
      initialNormalized.croppedFamily
      (Kakeya.realRpowENN delta (-preliminaryStickyLoss)) := by
    apply weaken_convex_wolff_bound initialNormalized.cropped_top_level_cwa
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne.le
      (by linarith)
  rcases propertyThree_finite_planiness_initial_local_grains
      sticky propP bounded scaleFactor hscaleFactor hrhoAligned
      hsourceExtremal hsourceCWA hstickyProducer hslack hdelta hdeltaOne
      hproducerLoss hsourceADLoss htau_def htau_pos htau_le_20L hL_le_tau
      htau_sq htau_le_one hL_small hL_pos hL_half hsigma_pos
      hsigma_lt_one heps₁_pos heps₁_lt heps₃_pos heps₃_def heps_sum
      L₀_log hL_le_L0_log h_log_main h_propertyThree_full h_ax_condition
      hL_lower hL_bound hstickyLoss_le_sourceAD hsmallCost hlargeEndpoint
    with ⟨hfinalExtremal, hfinalCWA, ⟨localGrains⟩⟩
  have hsub : PaperIsSubshading bounded.data.refinement.shading
      initialNormalized.croppedRefined := fun index =>
    (bounded.data.refinement.subshading index).trans
      (ambientPropertyThreeCommonHull_subshading
        sticky propP.propertyThree index)
  let weak := Proposition63InitialWeakLocalGrainData.ofRelaxed localGrains
  let weakened := weak.weakenLoss hdelta hdeltaOne.le hproducerLocal
  exact ⟨{
    shading := bounded.data.refinement.shading
    subshading := hsub
    cubical := bounded.data.refinement.cubical
    extremal := hfinalExtremal.mono_loss hproducerReentry
    topLevelCWA := by
      apply weaken_convex_wolff_bound hfinalCWA
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne.le
        (by linarith)
    incidence := delta
    lipschitz := Real.toNNReal coefficient
    incidence_nonnegative := hdelta.le
    localGrains := weakened
  }⟩

/-- Paper-order preliminary Lemmas 4.8/4.12 assembler using one fixed
Property-(P) common hull and a finite grid of LOW/HIGH estimates.  Unlike the
compatibility theorem above, this does not extend a single critical-scale
estimate to all scales. -/
theorem proposition63_preliminary_local_grain_finite_grid_of_bounded
    {delta sigma initialInputLoss normalizationLoss preliminaryStickyLoss
      producerLoss gridLoss gridMidLoss localLoss reentryLoss tau epsilon₁
      epsilon₃ coefficient incidence : ℝ}
    {N kMin kMax : ℕ}
    {rho : WZ2PaperRequestedScale delta}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent logExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := preliminaryStickyLoss)
      initialNormalized.croppedRefined rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (bounded : BoundedBalancedFinitePlaninessData
      (coefficient := coefficient)
      (ambientPropertyThreeCommonHull sticky propP.propertyThree) incidence)
    (hboundedMass : 0 < bounded.data.refinement.shading.mass)
    (hincidenceNonnegative : 0 ≤ incidence)
    (hnormalizationSticky : normalizationLoss ≤ preliminaryStickyLoss)
    (hstickyProducer : preliminaryStickyLoss ≤ producerLoss)
    (hproducerLocal : producerLoss ≤ localLoss)
    (hproducerReentry : producerLoss ≤ reentryLoss)
    (hmassSlack :
      (propertyThreeCommonHullMassLoss sticky * bounded.data.massLoss) *
          Kakeya.realRpowENN delta producerLoss ≤
        Kakeya.realRpowENN delta preliminaryStickyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hproducerLoss : 0 < producerLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hcoarse : 0 < rho.1)
    (hcoarseSmall : rho.1 ≤ 1 / 10000)
    (hgridLoss : 0 < gridLoss)
    (hgridMidLoss : 0 < gridMidLoss)
    (hN : 0 < (N : ℝ))
    (hkMin : kMin = Nat.ceil ((N : ℝ) * gridMidLoss))
    (hkMinMax : kMin ≤ kMax)
    (hkMaxLower :
      (N : ℝ) * (1 - gridMidLoss) - 1 ≤ (kMax : ℝ))
    (hgridAdmissible : ∀ k, kMin ≤ k ∧ k ≤ kMax →
      delta ≤ finiteGridScaleVal delta N k ∧
        finiteGridScaleVal delta N k ≤ 1)
    (htauDef : tau = rho.1 * Real.sqrt 3)
    (htauPos : 0 < tau)
    (htauLe : tau ≤ 20 * rho.1)
    (hcoarseTau : rho.1 ≤ tau)
    (htauSq : tau ^ 2 ≤ 4 * rho.1)
    (htauOne : tau ≤ 1)
    (hepsilon₁ : 0 < epsilon₁)
    (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (L₀Log Vtotal : ℝ)
    (hcoarseLog : rho.1 ≤ L₀Log)
    (hlog : 0 < epsilon₁ → ∀ L' : ℝ, 0 < L' → L' ≤ L₀Log →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / L' ^ 3 →
        Real.rpow L' epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hpropertyThree :
      ∀ parent : Fin sticky.coarse.card, ∀ point : Point3,
        point ∈ propP.propertyThree.carrier parent →
          Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
              ENNReal.ofReal tau ≤
            MeasureTheory.volume
              (propP.propertyThree.carrier parent ∩
                Metric.closedBall point tau))
    (haxis :
      4 * (6 * rho.1) ^ 2 ≤
        (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2)
    (hVtotalPos : 0 < Vtotal)
    (hVtotal : MeasureTheory.volume sticky.croppedCoarseShading.union ≤
      ENNReal.ofReal Vtotal)
    (highConstant : ENNReal)
    (hhighOne : (1 : ENNReal) ≤ highConstant)
    (hhighTop : highConstant ≠ ⊤)
    (hhighArithmetic : ∀ queryScale : ℝ,
      0 < queryScale → queryScale < 5 * rho.1 ^ 2 →
      ENNReal.ofReal
        ((Vtotal /
            (Real.rpow rho.1 (1 + 7 * epsilon₁ + epsilon₃) *
              tau ^ 2 / 200)) *
          (2 * (2 * (40 * rho.1)) / queryScale + 2)) ≤
        highConstant)
    (hlowAbsorb : Kakeya.realRpowENN rho.1 (-1) ≤
      Kakeya.realRpowENN delta (-gridLoss))
    (hhighAbsorb : 10 * highConstant ≤
      Kakeya.realRpowENN delta (-gridLoss))
    (habsorbInterpolation :
      (100 : ℝ) * Real.rpow delta
          (-gridLoss - gridMidLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-localLoss))
    (habsorbFine :
      (100 : ℝ) * Real.rpow delta
          (-gridMidLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-localLoss)) :
    Nonempty (Proposition63PreliminaryLocalGrainData
      (localLoss := localLoss) (reentryLoss := reentryLoss)
      initialNormalized) := by
  let final := bounded.data.refinement.shading
  let sourceMap := bounded.data.refinement.planeMap
  let planeMap : PaperWZ1WeakPlaneMapData final incidence := {
    planeMap := sourceMap.planeMap
    measurable := sourceMap.measurable
    unit := sourceMap.unit
    incidence := by
      intro index point hpoint
      exact (sourceMap.incidence index point hpoint).trans
        bounded.incidence_le
  }
  have hlipschitz : LipschitzWith (Real.toNNReal coefficient)
      (fun point : {point : Point3 // point ∈ final.union} =>
        planeMap.planeMap point) :=
    bounded.data.refinement.lipschitz
  have hsourceExtremal : WZ2PaperCroppedIsExtremal
      sigma preliminaryStickyLoss initialNormalized.croppedFamily
        initialNormalized.croppedRefined :=
    initialNormalized.final_extremal.mono_loss hnormalizationSticky
  have hsourceCWA : WZ2PaperConvexWolffBound
      initialNormalized.croppedFamily
      (Kakeya.realRpowENN delta (-preliminaryStickyLoss)) := by
    apply weaken_convex_wolff_bound initialNormalized.cropped_top_level_cwa
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne.le
      (by linarith)
  let totalMassLoss : ENNReal :=
    propertyThreeCommonHullMassLoss sticky * bounded.data.massLoss
  have hcommonMassLossPos : 0 < propertyThreeCommonHullMassLoss sticky :=
    propertyThreeCommonHullMassLoss_pos sticky
  have hcommonMassLossTop : propertyThreeCommonHullMassLoss sticky ≠ ⊤ :=
    propertyThreeCommonHullMassLoss_ne_top sticky hdelta hdeltaOne
  have hcommonMass :
      (propertyThreeCommonHullMassLoss sticky)⁻¹ *
          initialNormalized.croppedRefined.mass ≤
        (ambientPropertyThreeCommonHull sticky propP.propertyThree).mass :=
    propertyThreeCommonHullMassLoss_inv_mul_source_mass_le
      sticky propP hdelta
  have htotalPos : 0 < totalMassLoss :=
    ENNReal.mul_pos hcommonMassLossPos.ne'
      bounded.data.massLoss_pos.ne'
  have htotalTop : totalMassLoss ≠ ⊤ :=
    ENNReal.mul_ne_top hcommonMassLossTop bounded.data.massLoss_ne_top
  have htotalMass : totalMassLoss⁻¹ *
        initialNormalized.croppedRefined.mass ≤ final.mass := by
    calc
      totalMassLoss⁻¹ * initialNormalized.croppedRefined.mass =
          bounded.data.massLoss⁻¹ *
            ((propertyThreeCommonHullMassLoss sticky)⁻¹ *
              initialNormalized.croppedRefined.mass) := by
        dsimp only [totalMassLoss]
        rw [ENNReal.mul_inv
          (Or.inl hcommonMassLossPos.ne')
          (Or.inl hcommonMassLossTop)]
        ring
      _ ≤ bounded.data.massLoss⁻¹ *
          (ambientPropertyThreeCommonHull sticky propP.propertyThree).mass :=
        mul_le_mul_left' hcommonMass _
      _ ≤ final.mass :=
        bounded.data.massLoss_inv_mul_source_mass_le
  have hfinalCommon : PaperIsSubshading final
      (ambientPropertyThreeCommonHull sticky propP.propertyThree) :=
    bounded.data.refinement.subshading
  have hfinalSub : PaperIsSubshading final
      initialNormalized.croppedRefined := fun index =>
    (hfinalCommon index).trans
      (ambientPropertyThreeCommonHull_subshading
        sticky propP.propertyThree index)
  have hproducerExtremal : WZ2PaperCroppedIsExtremal
      sigma producerLoss initialNormalized.croppedFamily final :=
    transfer_cropped_extremal_to_subshading totalMassLoss htotalPos
      htotalTop hsourceExtremal hfinalSub htotalMass
      bounded.data.refinement.cubical hstickyProducer
      (by simpa [totalMassLoss] using hmassSlack) hdelta hdeltaOne.le
      hproducerLoss
  have hproducerCWA : WZ2PaperConvexWolffBound
      initialNormalized.croppedFamily
      (Kakeya.realRpowENN delta (-producerLoss)) := by
    apply weaken_convex_wolff_bound hsourceCWA
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne.le
      (by linarith)
  let localAD := propertyThree_commonHull_finiteGrid_local_ad
    sticky propP planeMap hlipschitz hfinalCommon
    hdelta hdeltaOne.le hsigma hsigmaOne hcoarse hcoarseSmall hgridLoss
    hgridMidLoss hN hkMin hkMinMax hkMaxLower hgridAdmissible htauDef
    htauPos htauLe hcoarseTau htauSq htauOne hepsilon₁ hepsilon₃
    hepsilonSum L₀Log hcoarseLog hlog hpropertyThree haxis Vtotal
    hVtotalPos hVtotal highConstant hhighOne hhighTop hhighArithmetic
    hlowAbsorb hhighAbsorb habsorbInterpolation habsorbFine
  let weak : Proposition63InitialWeakLocalGrainData
      (incidence := incidence) final sigma
      (Kakeya.realRpowENN delta (-localLoss))
      (Real.toNNReal coefficient) := {
    planeMap := fun point => planeMap.planeMap point
    planeMap_lipschitz := hlipschitz
    planeMap_unit := by
      intro point
      exact planeMap.unit point point.prop
    planeMap_incidence := by
      intro index point hpoint
      exact planeMap.incidence index point hpoint
    local_ad := localAD
  }
  exact ⟨{
    shading := final
    subshading := hfinalSub
    cubical := bounded.data.refinement.cubical
    extremal := hproducerExtremal.mono_loss hproducerReentry
    topLevelCWA := by
      apply weaken_convex_wolff_bound hproducerCWA
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne.le
        (by linarith)
    incidence := incidence
    lipschitz := Real.toNNReal coefficient
    incidence_nonnegative := hincidenceNonnegative
    localGrains := weak
  }⟩

end Kakeya.Assouad.PureWZ2

end
