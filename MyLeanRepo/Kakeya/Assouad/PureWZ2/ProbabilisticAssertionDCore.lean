import MyLeanRepo.Kakeya.Assouad.PureWZ2.ProbabilisticAnalyticCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.FiniteAssertionDCore
import MyLeanRepo.Kakeya.Assouad.Targets.IndexedKatzTaoToAssertionD

/-!
# Finite Assertion-D core from probabilistic thinning

This module is the thin ABI between the UTS-free probabilistic analytic core
and the existing deterministic indexed-to-finite conversion.  It deliberately
does not assert a target-to-selected index bijection: the old deterministic
conversion does not expose one, and the direct Wolff-floor route does not need
one.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Bernoulli thinning, analytic essentially-distinct cleanup, and deterministic
conversion produce one finite Assertion-D core.

The three explicit weakening hypotheses are exactly the interfaces between
the probabilistic constants and the requested Assertion-D exponents:

* pointwise density is at least `delta ^ assertionEta`;
* the thinned Katz--Tao constant is at most `delta ^ (-ktEta)`;
* the explicit retained-cardinality coefficient reaches the requested
  `delta ^ (-2 + coreCardLoss)` floor.
-/
theorem pure_wz2_probabilistic_assertionD_core
    (requestedCardLoss coreCardLoss ktEta assertionEta : ℝ)
    (hrequestedCardLoss : 0 < requestedCardLoss)
    (hcoreCardLoss : 0 < coreCardLoss)
    (hcoreRequested : coreCardLoss ≤ requestedCardLoss)
    (hktEta : 0 < ktEta)
    (hassertionEta : 0 < assertionEta)
    (hstrict : ktEta + coreCardLoss < assertionEta) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ family : Kakeya.Streamlined.TubeFamily delta,
          family.Nonempty →
          family.IsInUnitBall →
          ∀ shading : Kakeya.Streamlined.TubeShading family,
            ∀ densityConstant D : ENNReal,
              ∀ thinningEta : ℝ,
                0 < densityConstant →
                D ≠ ⊤ →
                0 < thinningEta →
                family.toBodyFamily.deltaMax ≤ D →
                Kakeya.realRpowENN delta (-thinningEta) ≤ D →
                (∀ index,
                  densityConstant * (family.tube index).volume ≤
                    MeasureTheory.volume
                      (shading.carrier index)) →
                ∀ net :
                    Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet
                      delta,
                  Kakeya.deltaTubeVolume delta ≤
                    (Kakeya.realRpowENN delta
                        (-thinningEta) / D) *
                      shading.mass →
                  (net.testSets.card : ℝ) *
                        Real.exp (-(11 - Real.exp 1) *
                          (Kakeya.realRpowENN delta
                            (-thinningEta)).toReal) +
                      Real.exp (-(3 - Real.exp 1) *
                        ((Kakeya.realRpowENN delta
                          (-thinningEta)).toReal / D.toReal) *
                        (family.card : ℝ)) <
                    1 / 8 →
                  Kakeya.realRpowENN delta assertionEta ≤
                    densityConstant →
                  pureWZ2ThinnedDeltaMax net thinningEta ≤
                    Kakeya.realRpowENN delta (-ktEta) →
                  Kakeya.realRpowENN delta
                      (-2 + coreCardLoss) ≤
                    (((pureWZ2ThinnedAnalyticConflictBound
                          net thinningEta + 1)⁻¹ *
                        densityConstant) *
                      ((1 / 2 : ENNReal) *
                        (Kakeya.realRpowENN delta
                          (-thinningEta) / D) *
                        densityConstant)) *
                      family.enncard →
                  Nonempty
                    (PureWZ2FiniteAssertionDCore
                      (assertionEta := assertionEta)
                      (requestedCardLoss := requestedCardLoss)
                      family shading) := by
  rcases
      indexed_katz_tao_to_assertionD
        requestedCardLoss coreCardLoss ktEta assertionEta
        hrequestedCardLoss hcoreCardLoss hcoreRequested
        hktEta hassertionEta hstrict with
    ⟨conversionDelta₀, hconversionDelta₀,
      hconversionDelta₀One, hconvert⟩
  refine
    ⟨min conversionDelta₀ (1 / 24000),
      by positivity, ?_, ?_⟩
  · exact (min_le_left _ _).trans hconversionDelta₀One
  intro delta hdelta hdeltaBound family hfamilyNonempty
    hfamilyBall shading densityConstant D thinningEta
    hdensityPositive hDtop hthinningEta hdeltaMax hthin
    hperTube net hmu hunion hdensityWeak hktWeak
    hcardinality
  have hdeltaConversion : delta ≤ conversionDelta₀ :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaOne : delta ≤ 1 :=
    hdeltaConversion.trans hconversionDelta₀One
  have hscaleSmall : 3000 * delta ≤ 1 / 8 := by
    have hsmall : delta ≤ 1 / 24000 :=
      hdeltaBound.trans (min_le_right _ _)
    nlinarith
  rcases
      pure_wz2_probabilistic_analytic_core
        hdelta hdeltaOne hscaleSmall family hfamilyNonempty
        hfamilyBall shading densityConstant D thinningEta
        hdensityPositive hDtop hthinningEta hdeltaMax hthin
        hperTube net hmu hunion with
    ⟨final, hfinalNonempty, hfinalBall, hfinalDistinct,
      _hfinalUnion, hfinalDense, hfinalKatzTao,
      _hfinalMass, hfinalCardinality⟩
  have hfinalDenseWeak :
      (final.restrictShading shading).IsLambdaDense
        (Kakeya.realRpowENN delta assertionEta) := by
    exact
      (mul_le_mul_right'
        hdensityWeak
        final.family.toBodyFamily.mass).trans hfinalDense
  have hfinalKatzTaoWeak :
      final.family.toBodyFamily.IsCKatzTao
        (Kakeya.realRpowENN delta (-ktEta)) :=
    hfinalKatzTao.trans hktWeak
  have hfinalCardinalityWeak :
      Kakeya.realRpowENN delta (-2 + coreCardLoss) ≤
        final.family.enncard :=
    hcardinality.trans hfinalCardinality
  rcases
      hconvert delta hdelta hdeltaConversion family shading final
        hfinalNonempty hfinalBall hfinalDistinct hfinalDenseWeak
        hfinalKatzTaoWeak hfinalCardinalityWeak with
    ⟨targetFamily, source, targetShading, htargetUnitBall,
      htargetDistinct, htargetTube, htargetShading,
      htargetDense, htargetKatzTao, htargetFrostman,
      htargetCardinality⟩
  exact
    ⟨⟨targetFamily, source, targetShading, htargetUnitBall,
      htargetDistinct, htargetTube, htargetShading,
      htargetDense, htargetKatzTao, htargetFrostman,
      htargetCardinality⟩⟩

end Kakeya.Assouad

end
