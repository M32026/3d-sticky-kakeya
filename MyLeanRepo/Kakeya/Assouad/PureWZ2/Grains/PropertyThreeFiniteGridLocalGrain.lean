import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSpatialPropertyThreePullback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinePullbackAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteGridEveryScaleLocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TransversePairPaper

/-!
# Finite-grid local grains on one Property-Three common hull

This is the geometric half of the preliminary Lemma 4.12 construction.  One
sticky witness and one Property-(P) common-spatial pullback are fixed once.
LOW grid scales use the diameter estimate; HIGH grid scales use the Córdoba
estimate on that same pullback.  No hereditary sticky call and no further
shading refinement occurs in the scale loop.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

attribute [local instance] Classical.propDecidable

/-- Prove every-scale local AD for a fixed finite-planiness refinement of a
single Property-(P) common hull.  This conclusion depends on the fixed unit
plane map but not on its incidence tolerance. -/
noncomputable def propertyThree_commonHull_finiteGrid_local_ad
    {delta sigma stickyLoss tau epsilon₁ epsilon₃ : ℝ}
    {gridLoss midLoss outputLoss : ℝ}
    {N kMin kMax : ℕ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading final : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {incidence coefficient : ℝ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (planeMap : PaperWZ1WeakPlaneMapData final incidence)
    (hlipschitz : LipschitzWith (Real.toNNReal coefficient)
      (fun point : {point : Point3 // point ∈ final.union} =>
        planeMap.planeMap point))
    (hfinalSub : PaperIsSubshading final
      (ambientPropertyThreeCommonHull sticky propP.propertyThree))
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hcoarse : 0 < rho.1)
    (hcoarseSmall : rho.1 ≤ 1 / 10000)
    (hgridLoss : 0 < gridLoss)
    (hmidLoss : 0 < midLoss)
    (hN : 0 < (N : ℝ))
    (hkMin : kMin = Nat.ceil ((N : ℝ) * midLoss))
    (hkMinMax : kMin ≤ kMax)
    (hkMaxLower : (N : ℝ) * (1 - midLoss) - 1 ≤ (kMax : ℝ))
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
    (L₀Log : ℝ)
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
            volume (propP.propertyThree.carrier parent ∩
              Metric.closedBall point tau))
    (haxis :
      4 * (6 * rho.1) ^ 2 ≤
        (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2)
    (Vtotal : ℝ)
    (hVtotalPos : 0 < Vtotal)
    (hVtotal : volume sticky.croppedCoarseShading.union ≤
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
          (-gridLoss - midLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-outputLoss))
    (habsorbFine :
      (100 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-outputLoss)) :
    ∀ queryScale : ℝ, delta ≤ queryScale → queryScale ≤ 1 →
      ∀ point : {point : Point3 // point ∈ final.union},
        PureWZ2PaperADSet1
          (scalarProjection (planeMap.planeMap point)
            (final.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt queryScale)))
          queryScale (1 - sigma)
          (Kakeya.realRpowENN delta (-outputLoss)) := by
  let finalPlaneMap : {point : Point3 // point ∈ final.union} → Point3 :=
    fun point => planeMap.planeMap point
  have hfinalUnit : ∀ point, ‖finalPlaneMap point‖ = 1 := by
    intro point
    exact planeMap.unit point point.prop
  apply finite_grid_low_high_every_scale_local_ad
    finalPlaneMap hlipschitz hfinalUnit hdelta hdeltaOne
    hsigma hsigmaOne hcoarse hcoarseSmall hgridLoss hmidLoss hN hkMin
    hkMinMax hkMaxLower hgridAdmissible highConstant
  · intro k hk hhigh point
    let queryScale := finiteGridScaleVal delta N k
    have hpointCommon : (point : Point3) ∈
        (ambientPropertyThreeCommonHull sticky propP.propertyThree).union := by
      rcases point.prop with ⟨index, hpoint⟩
      exact ⟨index, hfinalSub index hpoint⟩
    have hpointPullback : (point : Point3) ∈
        (propertyThreeFinePullbackShading
          sticky.cover sticky.refined propP.propertyThree).union := by
      rw [← ambientPropertyThreeCommonHull_union
        sticky propP.propertyThree]
      exact hpointCommon
    let S : Set Point3 := sticky.croppedCoarseShading.union ∩
      Metric.closedBall (point : Point3) (4 * tau)
    let W0 : ℝ := 40 * rho.1
    let Vmin : ℝ :=
      Real.rpow rho.1 (1 + 7 * epsilon₁ + epsilon₃) * tau ^ 2 / 200
    have hVmin : 0 < Vmin := by
      dsimp only [Vmin]
      exact div_pos
        (mul_pos (Real.rpow_pos_of_pos hcoarse _)
          (sq_pos_of_pos htauPos))
        (by norm_num)
    have hSVolume : volume S ≤ ENNReal.ofReal Vtotal := by
      calc
        volume S ≤ volume sticky.croppedCoarseShading.union :=
          measure_mono Set.inter_subset_left
        _ ≤ ENNReal.ofReal Vtotal := hVtotal
    have hquery : 0 < queryScale := Real.rpow_pos_of_pos hdelta _
    have hsqrt : Real.sqrt queryScale ≤ 4 * tau :=
      sqrt_rho_le_4tau hcoarse hquery.le htauDef (by linarith)
    have hpullback := propertyThreeFinePullback_high_local_ad
      sticky.balanced epsilon₁ epsilon₃ propP
      (finalPlaneMap point) (hfinalUnit point) (point : Point3)
      hpointPullback S rfl
      (sticky.croppedCoarseShading.union_measurable.inter
        Metric.isClosed_closedBall.measurableSet)
      (by intro other hother; exact hother.2)
      W0 Vmin Vtotal (by dsimp only [W0]; positivity) rfl
      hVmin rfl hVtotalPos hSVolume htauDef htauPos htauLe hcoarseTau
      htauSq htauOne (hcoarseSmall.trans (by norm_num)) hcoarse hsigma
      hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum L₀Log hcoarseLog hlog
      hpropertyThree haxis hsqrt hquery highConstant hhighOne hhighTop
      (by simpa [queryScale, W0, Vmin] using
        hhighArithmetic queryScale hquery hhigh)
    apply hpullback.mono_set
    rintro value ⟨other, hother, rfl⟩
    refine ⟨other, ⟨?_, hother.2⟩, rfl⟩
    have hotherCommon : other ∈
        (ambientPropertyThreeCommonHull sticky propP.propertyThree).union := by
      rcases hother.1 with ⟨index, hindex⟩
      exact ⟨index, hfinalSub index hindex⟩
    rw [ambientPropertyThreeCommonHull_union
      sticky propP.propertyThree] at hotherCommon
    exact hotherCommon
  · exact hlowAbsorb
  · exact hhighAbsorb
  · exact habsorbInterpolation
  · exact habsorbFine

/-- Compatibility wrapper for consumers that need the historical relaxed
package with fine-scale incidence. -/
noncomputable def propertyThree_commonHull_finiteGrid_local_grain
    {delta sigma stickyLoss tau epsilon₁ epsilon₃ : ℝ}
    {gridLoss midLoss outputLoss : ℝ}
    {N kMin kMax : ℕ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading final : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {incidence coefficient : ℝ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (planeMap : PaperWZ1WeakPlaneMapData final incidence)
    (hlipschitz : LipschitzWith (Real.toNNReal coefficient)
      (fun point : {point : Point3 // point ∈ final.union} =>
        planeMap.planeMap point))
    (hincidence : incidence ≤ delta)
    (hfinalSub : PaperIsSubshading final
      (ambientPropertyThreeCommonHull sticky propP.propertyThree))
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hcoarse : 0 < rho.1)
    (hcoarseSmall : rho.1 ≤ 1 / 10000)
    (hgridLoss : 0 < gridLoss)
    (hmidLoss : 0 < midLoss)
    (hN : 0 < (N : ℝ))
    (hkMin : kMin = Nat.ceil ((N : ℝ) * midLoss))
    (hkMinMax : kMin ≤ kMax)
    (hkMaxLower : (N : ℝ) * (1 - midLoss) - 1 ≤ (kMax : ℝ))
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
    (L₀Log : ℝ)
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
            volume (propP.propertyThree.carrier parent ∩
              Metric.closedBall point tau))
    (haxis :
      4 * (6 * rho.1) ^ 2 ≤
        (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2)
    (Vtotal : ℝ)
    (hVtotalPos : 0 < Vtotal)
    (hVtotal : volume sticky.croppedCoarseShading.union ≤
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
          (-gridLoss - midLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-outputLoss))
    (habsorbFine :
      (100 : ℝ) * Real.rpow delta (-midLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-outputLoss)) :
    PureWZ2RelaxedLocalGrainData final sigma
      (Kakeya.realRpowENN delta (-outputLoss))
      (Real.toNNReal coefficient) where
  planeMap := fun point => planeMap.planeMap point
  planeMap_lipschitz := hlipschitz
  planeMap_unit := by
    intro point
    exact planeMap.unit point point.prop
  planeMap_incidence := by
    intro index point hpoint
    exact (planeMap.incidence index point hpoint).trans hincidence
  local_ad := propertyThree_commonHull_finiteGrid_local_ad
    sticky propP planeMap hlipschitz hfinalSub hdelta hdeltaOne hsigma
    hsigmaOne hcoarse hcoarseSmall hgridLoss hmidLoss hN hkMin hkMinMax
    hkMaxLower hgridAdmissible htauDef htauPos htauLe hcoarseTau htauSq
    htauOne hepsilon₁ hepsilon₃ hepsilonSum L₀Log hcoarseLog hlog
    hpropertyThree haxis Vtotal hVtotalPos hVtotal highConstant hhighOne
    hhighTop hhighArithmetic hlowAbsorb hhighAbsorb habsorbInterpolation
    habsorbFine

end Kakeya.Assouad.PureWZ2

end
