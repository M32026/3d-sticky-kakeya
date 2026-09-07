import MyLeanRepo.Kakeya.Assouad.PureWZ2.FiniteAssertionDCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PullbackFactor

/-!
# Direct source-scale floor from one finite Assertion-D core

This module contains the final deterministic half of the literal full-fiber
route.  It applies Assertion D to a finite target core, uses the generalized
source-power inequality, and pulls the target union back through the centered
literal rescaling.
-/

noncomputable section

namespace Kakeya.Assouad

/--
One finite Assertion-D core at scale `delta / rho` gives the requested
source-scale volume floor once the scale-separation and fixed-constant
absorption inequalities are available.
-/
theorem pure_wz2_direct_assertionD_floor
    {delta rho outputEpsilon assertionEpsilon cardLoss c : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hrho : 0 < rho)
    (houtputEpsilon : 0 < outputEpsilon)
    (hassertionEpsilon : 0 < assertionEpsilon)
    (hassertionOutput :
      assertionEpsilon < outputEpsilon)
    (houtputSmall : outputEpsilon < 1)
    (hcardLoss : 0 ≤ cardLoss)
    (hexponent :
      0 <
        outputEpsilon - assertionEpsilon -
          cardLoss / 2)
    (hdenominator :
      0 <
        3 / 2 - assertionEpsilon -
          cardLoss / 2)
    (hc : 0 ≤ c)
    (hcBound :
      c <
        (outputEpsilon - assertionEpsilon -
            cardLoss / 2) /
          (3 / 2 - assertionEpsilon -
            cardLoss / 2))
    (hscale : Real.rpow delta c ≤ rho)
    {coreEta assertionEta kappa : ℝ}
    (hkappa : 0 < kappa)
    (hcoreEta : 0 < coreEta)
    (hcoreAssertionEta : coreEta ≤ assertionEta)
    (habsorb :
      Kakeya.realRpowENN delta
          ((outputEpsilon - assertionEpsilon -
              cardLoss / 2) -
            c * (3 / 2 - assertionEpsilon -
              cardLoss / 2)) ≤
        ENNReal.ofReal (1000000 * kappa))
    (hAssertionD :
      ∀ delta' : ℝ, 0 < delta' →
        ∀ family' : Kakeya.TubeFamily delta',
          family'.IsInUnitBall →
          family'.IsEssentiallyDistinct →
          ∀ shading' : Kakeya.Shading family',
            shading'.IsLambdaDense
                (Kakeya.realRpowENN delta' assertionEta) →
            Kakeya.KatzTaoConvexWolffBound family'
                (Real.rpow delta' (-assertionEta)) →
            Kakeya.FrostmanSlabWolffBound family'
                (Real.rpow delta' (-assertionEta)) →
            Kakeya.AssertionDLowerBound
              family' shading' kappa
              (1 / 2) 0 assertionEpsilon)
    {sourceFamily :
      Kakeya.Streamlined.TubeFamily delta}
    (sourceShading :
      Kakeya.Streamlined.TubeShading sourceFamily)
    {centeredFamily :
      Kakeya.Streamlined.TubeFamily (delta / rho)}
    (centeredShading :
      Kakeya.Streamlined.TubeShading centeredFamily)
    (core :
      PureWZ2FiniteAssertionDCore
        (assertionEta := coreEta)
        (requestedCardLoss := cardLoss)
        centeredFamily centeredShading)
    (anchor : Kakeya.DeltaTube rho)
    (hcoreUnion :
      core.targetShading.union ⊆
        wz2PaperCenteredLiteralRescalingAffineEquiv
            anchor hrho ''
          sourceShading.union) :
    Kakeya.realRpowENN delta
        (1 / 2 + outputEpsilon) ≤
      MeasureTheory.volume sourceShading.union := by
  let targetScale := delta / rho
  have htargetScale : 0 < targetScale :=
    div_pos hdelta hrho
  have htargetScaleOne : targetScale ≤ 1 := by
    have hdeltaRho : delta ≤ rho := by
      have hdeltaLePower : delta ≤ Real.rpow delta c := by
        by_cases hdeltaEq : delta = 1
        · subst hdeltaEq
          simp
        · have hdeltaLt : delta < 1 :=
            lt_of_le_of_ne hdeltaOne hdeltaEq
          have hcOne : c ≤ 1 := by
            have hratioPos :
                0 <
                  (outputEpsilon - assertionEpsilon -
                      cardLoss / 2) /
                    (3 / 2 - assertionEpsilon -
                      cardLoss / 2) := by positivity
            have hratioLtOne :
                (outputEpsilon - assertionEpsilon -
                      cardLoss / 2) /
                    (3 / 2 - assertionEpsilon -
                      cardLoss / 2) < 1 := by
              rw [div_lt_one hdenominator]
              linarith
            exact hcBound.le.trans hratioLtOne.le
          have hpow :=
            Real.rpow_le_rpow_of_exponent_ge
              hdelta hdeltaOne hcOne
          simpa using hpow
      exact hdeltaLePower.trans hscale
    exact (div_le_one hrho).mpr hdeltaRho
  have htargetVolumeZero :
      Kakeya.deltaTubeVolume targetScale ≠ 0 :=
    (tube_volume_scaling.2.1 targetScale
      htargetScale htargetScaleOne).1.ne'
  have htargetVolumeTop :
      Kakeya.deltaTubeVolume targetScale ≠ ⊤ :=
    (tube_volume_scaling.2.1 targetScale
      htargetScale htargetScaleOne).2
  have htargetCardZero :
      core.targetFamily.enncard ≠ 0 := by
    have hpowerPositive :
        0 <
          Kakeya.realRpowENN targetScale
            (-2 + cardLoss) :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos htargetScale _)
    exact
      (hpowerPositive.trans_le
        core.target_cardinality).ne'
  have htargetCardTop :
      core.targetFamily.enncard ≠ ⊤ := by
    change (core.targetFamily.card : ENNReal) ≠ ⊤
    simp
  have hAssertionLower :
      Kakeya.AssertionDLowerBound
        core.targetFamily core.targetShading
        kappa (1 / 2) 0 assertionEpsilon :=
    hAssertionD targetScale htargetScale
      core.targetFamily core.target_unit_ball
      core.target_distinct core.targetShading
      (by
        have hpower :
            Kakeya.realRpowENN targetScale assertionEta ≤
              Kakeya.realRpowENN targetScale coreEta :=
          pure_wz2_rpowENN_antitone
            htargetScale htargetScaleOne hcoreAssertionEta
        exact
          (mul_le_mul_right'
            hpower core.targetFamily.mass).trans
            core.target_dense)
      (by
        intro convexSet hconvex
        exact
          (core.target_katz_tao convexSet hconvex).trans (by
            gcongr
            exact
              Real.rpow_le_rpow_of_exponent_ge
                htargetScale htargetScaleOne
                (by linarith : -assertionEta ≤ -coreEta)))
      (by
        intro slab
        exact
          (core.target_frostman slab).trans (by
            gcongr
            exact
              Real.rpow_le_rpow_of_exponent_ge
                htargetScale htargetScaleOne
                (by linarith : -assertionEta ≤ -coreEta)))
  have hsourcePower :=
    source_power_generalized
      hdelta hdeltaOne hrho
      hassertionEpsilon hassertionOutput
      houtputEpsilon
      (by linarith : outputEpsilon < 3 / 2)
      hcardLoss hexponent hdenominator hkappa
      core.targetFamily.enncard
      (Kakeya.deltaTubeVolume targetScale)
      core.target_cardinality
      (by
        simpa [Kakeya.realRpowENN] using
          canonical_volume_lower htargetScale)
      htargetCardZero htargetCardTop
      htargetVolumeZero htargetVolumeTop
      c hc hcBound hscale habsorb
  have hAssertionInequality :
      ENNReal.ofReal kappa *
          Kakeya.realRpowENN targetScale assertionEpsilon *
          core.targetFamily.enncard *
          Kakeya.deltaTubeVolume targetScale *
          ENNReal.rpow
            (core.targetFamily.enncard *
              ENNReal.rpow
                (Kakeya.deltaTubeVolume targetScale) (1 / 2))
            (-(1 / 2 : ℝ)) ≤
        MeasureTheory.volume core.targetShading.union := by
    simpa [Kakeya.AssertionDLowerBound, mul_assoc] using
      hAssertionLower
  calc
    Kakeya.realRpowENN delta (1 / 2 + outputEpsilon) ≤
        pullbackFactor rho *
          (ENNReal.ofReal kappa *
            Kakeya.realRpowENN targetScale assertionEpsilon *
            core.targetFamily.enncard *
            Kakeya.deltaTubeVolume targetScale *
            ENNReal.rpow
              (core.targetFamily.enncard *
                ENNReal.rpow
                  (Kakeya.deltaTubeVolume targetScale) (1 / 2))
              (-(1 / 2 : ℝ))) := by
      simpa [pullbackFactor, targetScale, mul_assoc] using
        hsourcePower
    _ ≤ pullbackFactor rho *
          MeasureTheory.volume core.targetShading.union := by
      gcongr
    _ ≤ MeasureTheory.volume sourceShading.union :=
      centered_affine_equiv_pullback_volume
        anchor hrho hcoreUnion

end Kakeya.Assouad

end
