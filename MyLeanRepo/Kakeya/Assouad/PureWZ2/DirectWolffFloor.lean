import MyLeanRepo.Kakeya.Assouad.PureWZ2.AssertionDOneHalfZero
import MyLeanRepo.Kakeya.Assouad.PureWZ2.BodyCWAProbabilisticAssertionDCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CenteredStrictFiberBounds
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Core
import MyLeanRepo.Kakeya.Assouad.PureWZ2.DirectAssertionDFloor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.DirectWolffFloorThresholds
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1OneScaleAbsorption
import MyLeanRepo.Kakeya.Assouad.Targets.ProbabilisticKatzTaoSubfamily

/-!
# Direct pure WZ2 Wolff floor

This is the complete race route from literal Definition 2.12 complete strict
full fibers to the pure Wolff volume floor.  It uses no assigned-fiber API and
no historical uniform tube structure.
-/

noncomputable section

open Kakeya.Streamlined
open Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Literal complete-full-fiber proof of the pure WZ2 Wolff floor for a
subunit loss exponent. -/
private theorem pure_wz2_direct_wolff_floor_small
    (outputEpsilon : ℝ)
    (houtputEpsilon : 0 < outputEpsilon)
    (houtputSmall : outputEpsilon < 1) :
    ∃ eta delta₀ : ℝ,
      0 < eta ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ family : Kakeya.Streamlined.TubeFamily delta,
          family.Nonempty →
          WZ2PaperPureCWAAtNearbyScales family
            (Kakeya.realRpowENN delta (-eta)) →
          ∀ shading : Kakeya.Streamlined.TubeShading family,
            shading.IsLambdaDense
              (Kakeya.realRpowENN delta eta) →
            Kakeya.realRpowENN delta
                (1 / 2 + outputEpsilon) ≤
              MeasureTheory.volume shading.union := by
  have hAssertionD : Kakeya.AssertionD (1 / 2) 0 :=
    assertionD_one_half_zero
  let assertionEpsilon : ℝ := outputEpsilon / 4
  have hassertionEpsilon : 0 < assertionEpsilon := by
    positivity
  rcases
      hAssertionD.2.2 assertionEpsilon hassertionEpsilon with
    ⟨kappa, assertionEta, hkappa, hassertionEta,
      hAssertionMain⟩
  let coreEta : ℝ :=
    min (assertionEta / 4) (min (outputEpsilon / 64) (1 / 64))
  let ktEta : ℝ := coreEta / 4
  let cardLoss : ℝ := coreEta / 4
  let thinningEta : ℝ := coreEta / 8
  let inputEta : ℝ := coreEta / 256
  let pruneEta : ℝ := coreEta / 128
  let c : ℝ := outputEpsilon / 16
  have hcoreEta : 0 < coreEta := by
    dsimp [coreEta]
    positivity
  have hcoreAssertionEta : coreEta ≤ assertionEta := by
    dsimp [coreEta]
    exact (min_le_left _ _).trans (by linarith)
  have hktEta : 0 < ktEta := by positivity
  have hcardLoss : 0 < cardLoss := by positivity
  have hthinningEta : 0 < thinningEta := by positivity
  have hinputEta : 0 < inputEta := by positivity
  have hpruneEta : 0 < pruneEta := by positivity
  have hinputC : inputEta ≤ c := by
    have hcoreOutput : coreEta ≤ outputEpsilon / 64 := by
      exact min_le_right _ _ |>.trans (min_le_left _ _)
    dsimp [inputEta, c]
    linarith
  have hcOne : c ≤ 1 := by
    dsimp [c]
    linarith
  have hcoreStrict : ktEta + cardLoss < coreEta := by
    dsimp [ktEta, cardLoss]
    linarith
  have hcardNonnegative : 0 ≤ cardLoss := hcardLoss.le
  have hassertionOutput :
      assertionEpsilon < outputEpsilon := by
    dsimp [assertionEpsilon]
    linarith
  rcases
      pure_wz2_body_cwa_probabilistic_assertionD_core
        cardLoss cardLoss ktEta coreEta
        hcardLoss hcardLoss le_rfl hktEta hcoreEta
        hcoreStrict with
    ⟨coreDelta₀, hcoreDelta₀, hcoreDelta₀One, hcore⟩

  let failureExponent : ℝ :=
    -(2 * (1 - c) - inputEta - pruneEta)
  have hfailureExponent : failureExponent < 0 := by
    dsimp [failureExponent, c, inputEta, pruneEta]
    have hcoreSmall : coreEta ≤ 1 / 64 := by
      exact min_le_right _ _ |>.trans (min_le_right _ _)
    nlinarith
  let cwaDensityGap : ℝ :=
    2 * (1 - c) - inputEta - 2 * pruneEta
  have hcwaDensityGap : 0 < cwaDensityGap := by
    dsimp [cwaDensityGap, c, inputEta, pruneEta]
    have hcoreSmall : coreEta ≤ 1 / 64 := by
      exact min_le_right _ _ |>.trans (min_le_right _ _)
    nlinarith
  let cardinalityGap : ℝ :=
    (1 - c) * (cardLoss - thinningEta) -
      inputEta - 3 * pruneEta
  have hcardinalityGap : 0 < cardinalityGap := by
    dsimp [cardinalityGap, c, cardLoss, thinningEta,
      inputEta, pruneEta]
    have hcoreOutput : coreEta ≤ outputEpsilon / 64 := by
      exact min_le_right _ _ |>.trans (min_le_left _ _)
    nlinarith
  let sourceGap : ℝ :=
    (outputEpsilon - assertionEpsilon - cardLoss / 2) -
      c * (3 / 2 - assertionEpsilon - cardLoss / 2)
  have hsourceGap : 0 < sourceGap := by
    dsimp [sourceGap, assertionEpsilon, cardLoss, c]
    have hcoreOutput : coreEta ≤ outputEpsilon / 64 := by
      exact min_le_right _ _ |>.trans (min_le_left _ _)
    nlinarith
  rcases
      pure_wz2_direct_wolff_floor_thresholds
        (coreDelta₀ := coreDelta₀)
        (c := c)
        (inputEta := inputEta)
        (pruneEta := pruneEta)
        (coreEta := coreEta)
        (ktEta := ktEta)
        (thinningEta := thinningEta)
        (cwaDensityGap := cwaDensityGap)
        (cardinalityGap := cardinalityGap)
        (sourceGap := sourceGap)
        (kappa := kappa)
        hcoreDelta₀ hcoreDelta₀One
        (by
          dsimp [c, inputEta]
          have hcoreOutput : coreEta ≤ outputEpsilon / 64 := by
            exact min_le_right _ _ |>.trans (min_le_left _ _)
          linarith)
        (by
          dsimp [c]
          linarith)
        (by
          dsimp [pruneEta, inputEta]
          linarith)
        (by
          dsimp [c, pruneEta]
          have hcoreOutput : coreEta ≤ outputEpsilon / 64 := by
            exact min_le_right _ _ |>.trans (min_le_left _ _)
          nlinarith)
        (by
          dsimp [c, ktEta, thinningEta]
          nlinarith)
        (by
          have hcLtOne : c < 1 := by
            dsimp [c]
            linarith
          positivity)
        hfailureExponent hcwaDensityGap hcardinalityGap
        hsourceGap hkappa with
    ⟨thresholds⟩
  refine
    ⟨inputEta, thresholds.delta₀, hinputEta,
      thresholds.delta₀_pos, thresholds.delta₀_le_one, ?_⟩
  intro delta hdelta hdeltaBound family hfamilyNonempty
    hCWA shading hdense
  have hdeltaOne : delta ≤ 1 :=
    hdeltaBound.trans thresholds.delta₀_le_one

  have hprune :
      Kakeya.realRpowENN delta pruneEta ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta inputEta := by
    exact pure_wz2_pruning_power_bound hdelta
      (thresholds.prune delta hdelta hdeltaBound)
  rcases
      pure_wz2_centered_strict_fiber_preparation
        hdelta hdeltaOne hfamilyNonempty shading
        hinputEta hinputC hcOne hdense hprune
        rfl hCWA
        (thresholds.rho delta hdelta hdeltaBound)
        (thresholds.target delta hdelta hdeltaBound) with
    ⟨prepared⟩
  let rho := prepared.nearby.rho
  let targetScale := delta / rho
  have hrho : 0 < rho := prepared.nearby.scaleData.rho_pos
  have htarget : 0 < targetScale := div_pos hdelta hrho
  have htargetOne : targetScale ≤ 1 :=
    prepared.target_scale_le_one
  have hdeltaTarget : delta ≤ targetScale := by
    have hrhoOne : rho ≤ 1 := prepared.rho_le_one
    change delta ≤ delta / rho
    exact (le_div_iff₀ hrho).2 (by
      nlinarith)
  have htargetUpper :
      targetScale ≤ Real.rpow delta (1 - c) := by
    calc
      targetScale = delta / rho := rfl
      _ ≤ delta / Real.rpow delta c := by
        exact div_le_div_of_nonneg_left
          hdelta.le
          (Real.rpow_pos_of_pos hdelta c)
          prepared.scale_lower
      _ = Real.rpow delta (1 - c) := by
        calc
          delta / Real.rpow delta c =
              Real.rpow delta 1 /
                Real.rpow delta c := by
            exact congrArg
              (fun value => value / Real.rpow delta c)
              (Real.rpow_one delta).symm
          _ = Real.rpow delta (1 - c) :=
            (Real.rpow_sub hdelta 1 c).symm
  have htargetCore : targetScale ≤ coreDelta₀ :=
    htargetUpper.trans
      (thresholds.coreScale delta hdelta hdeltaBound)
  have hrhoSmall' : rho ≤ 1 / 4 :=
    prepared.rho_upper.le.trans
      (thresholds.rho delta hdelta hdeltaBound)
  let centeredFamily :=
    wz2PaperCenteredSelectedFullFiberFamily
      family prepared.nearby.scaleData.coarse prepared.parent
      prepared.nearby.scaleData.rho_pos prepared.selected
  let centeredShading := prepared.centeredShading hrhoSmall'
  let densityConstant :=
    pureWZ2CenteredDensityConstant delta rho
      (Kakeya.realRpowENN delta pruneEta)
  let cwaConstant :=
    (Kakeya.realRpowENN delta pruneEta)⁻¹ *
      ((4000000 : ENNReal) *
        Kakeya.realRpowENN delta (-inputEta))
  have hdensityPositive : 0 < densityConstant := by
    exact pure_wz2_centeredDensityConstant_pos
      hdelta hrho htargetOne
      (Kakeya.realRpowENN delta pruneEta)
      (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hdelta pruneEta))
  have hcwaPosFinite :=
    pure_wz2_centeredCWA_constant_pos_finite
      (inputEta := inputEta) (pruneEta := pruneEta) hdelta
  have hcwaZero : cwaConstant ≠ 0 :=
    hcwaPosFinite.1.ne'
  have hcwaTop : cwaConstant ≠ ⊤ :=
    hcwaPosFinite.2
  have hperTube :=
    prepared.centeredShading_perTube hrhoSmall'
  have hdensityWeak :
      Kakeya.realRpowENN targetScale coreEta ≤
        densityConstant := by
    have hlower :=
      pure_wz2_centeredDensityConstant_lower
        hdelta hrho htargetOne
        (Kakeya.realRpowENN delta pruneEta)
    have habsorb :=
      thresholds.density delta hdelta hdeltaBound
    have hsource :
        Kakeya.realRpowENN delta ((1 - c) * coreEta) ≤
          ENNReal.ofReal (1 / 12000000 : ℝ) *
            Kakeya.realRpowENN delta pruneEta := by
      have hmain :=
        pure_wz2_density_power_from_absorption
          (sourceEta := (1 - c) * coreEta)
          (targetEta := pruneEta)
          (constant := 12000000)
          hdelta (by norm_num) habsorb
      have hinverse :
          ENNReal.ofReal (12000000 : ℝ)⁻¹ =
            ENNReal.ofReal (1 / 12000000 : ℝ) := by
        congr 1
        ring
      rw [hinverse] at hmain
      exact hmain
    have htargetSource :
        Kakeya.realRpowENN targetScale coreEta ≤
          Kakeya.realRpowENN delta ((1 - c) * coreEta) :=
      pure_wz2_target_power_upper
        hdelta htarget.le
        htargetUpper
        hcoreEta.le
    exact htargetSource.trans (hsource.trans hlower)
  have hcwa := prepared.centered_cwa
  have hCwaVolume :=
    pure_wz2_centeredCWA_volume_upper
      (inputEta := inputEta) (pruneEta := pruneEta)
      hdelta hrho htargetOne
  have hDensityLower :=
    pure_wz2_centeredDensityConstant_lower
      hdelta hrho htargetOne
      (Kakeya.realRpowENN delta pruneEta)

  rcases tube_density_test_net_explicit htarget htargetOne with
    ⟨net, hnetLoss, hnetCard⟩
  have hlowKatz :
      Kakeya.realRpowENN targetScale (-thinningEta) ≤
        Kakeya.realRpowENN targetScale (-ktEta) :=
    pure_wz2_rpowENN_antitone htarget htargetOne (by
      dsimp [thinningEta, ktEta]
      linarith : -ktEta ≤ -thinningEta)
  have hhighKatz :
      pureWZ2ThinnedDeltaMax net thinningEta ≤
        Kakeya.realRpowENN targetScale (-ktEta) := by
    calc
      pureWZ2ThinnedDeltaMax net thinningEta ≤
          ENNReal.ofReal (100000000 : ℝ) *
            Kakeya.realRpowENN targetScale (-thinningEta) := by
        dsimp [pureWZ2ThinnedDeltaMax]
        calc
          net.lossFactor * 10 *
              Kakeya.realRpowENN targetScale (-thinningEta) ≤
            (10^7 : ENNReal) * 10 *
              Kakeya.realRpowENN targetScale (-thinningEta) := by
                gcongr
          _ = ENNReal.ofReal (100000000 : ℝ) *
              Kakeya.realRpowENN targetScale (-thinningEta) := by
                norm_num
      _ ≤ Kakeya.realRpowENN targetScale (-ktEta) := by
        have habsorb :=
          thresholds.katzTao delta hdelta hdeltaBound
        exact
          pure_wz2_target_negative_power_absorption
            (s := 1 - c)
            (smaller := thinningEta)
            (larger := ktEta)
            (constant := 100000000)
            hdelta htarget
            htargetUpper
            (by
              dsimp [c]
              linarith)
            (by
              dsimp [ktEta, thinningEta]
              linarith)
            habsorb

  -- The remaining cardinality and probability bounds use the body-CWA
  -- lower bound in both branches.
  have hbaseCard :=
    pure_wz2_body_cwa_cardinality_lower
      htarget htargetOne prepared.centered_nonempty
      hcwaZero hcwaTop hcwa

  have hCenteredCV :
      cwaConstant * Kakeya.deltaTubeVolume targetScale ≤
        densityConstant := by
    exact
      pure_wz2_centered_cwa_volume_le_density
        hdelta htarget htargetOne
        hCwaVolume hDensityLower
        (by
          have habsorb :=
            thresholds.cwa delta hdelta hdeltaBound
          have htargetTwo :=
            pure_wz2_target_power_upper
              hdelta htarget.le htargetUpper
              (by norm_num : (0 : ℝ) ≤ 2)
          have hsourceExponent :
              (1 - c) * 2 =
                cwaDensityGap +
                  (inputEta + 2 * pruneEta) := by
            dsimp [cwaDensityGap]
            ring
          have hsourcePower :
              (576000000000000 : ENNReal) *
                  Kakeya.realRpowENN delta
                    (-(inputEta + 2 * pruneEta)) *
                  Kakeya.realRpowENN delta
                    ((1 - c) * 2) ≤
                1 := by
            rw [hsourceExponent]
            have hproduct :
              Kakeya.realRpowENN delta
                  (-(inputEta + 2 * pruneEta)) *
                  Kakeya.realRpowENN delta
                    (cwaDensityGap +
                      (inputEta + 2 * pruneEta)) =
                Kakeya.realRpowENN delta
                  cwaDensityGap := by
              rw [Subunit.realRpowENN_mul hdelta]
              congr 1
              ring
            calc
              (576000000000000 : ENNReal) *
                  Kakeya.realRpowENN delta
                    (-(inputEta + 2 * pruneEta)) *
                  Kakeya.realRpowENN delta
                    (cwaDensityGap +
                      (inputEta + 2 * pruneEta)) =
                (576000000000000 : ENNReal) *
                  (Kakeya.realRpowENN delta
                    (-(inputEta + 2 * pruneEta)) *
                  Kakeya.realRpowENN delta
                    (cwaDensityGap +
                      (inputEta + 2 * pruneEta))) := by ring
              _ = (576000000000000 : ENNReal) *
                  Kakeya.realRpowENN delta cwaDensityGap := by
                rw [hproduct]
              _ ≤ 1 := by
                simpa using habsorb
          exact
            (mul_le_mul_left'
              htargetTwo
              ((576000000000000 : ENNReal) *
                Kakeya.realRpowENN delta
                  (-(inputEta + 2 * pruneEta)))).trans
              (by simpa [mul_assoc] using hsourcePower))
  have hProbability :
      (net.testSets.card : ℝ) *
            Real.exp (-(11 - Real.exp 1) *
              (Kakeya.realRpowENN targetScale
                (-thinningEta)).toReal) +
          Real.exp (-(3 - Real.exp 1) *
            (cwaConstant *
              Kakeya.deltaTubeVolume targetScale).toReal⁻¹) <
        1 / 8 := by
    have htermOne :
        (net.testSets.card : ℝ) *
            Real.exp (-(11 - Real.exp 1) *
              (Kakeya.realRpowENN targetScale
                (-thinningEta)).toReal) <
          1 / 16 := by
      exact
        pure_wz2_density_net_failure_at_target
          hdelta hdeltaOne htarget hdeltaTarget
          htargetUpper
          (by
            dsimp [c]
            linarith)
          hthinningEta net hnetCard
          (thresholds.net delta hdelta hdeltaBound)
    have hinverseReal :
        (1 / 48000000 : ℝ) *
            Real.rpow delta (inputEta + pruneEta) *
            Real.rpow targetScale (-2) ≤
          (cwaConstant *
            Kakeya.deltaTubeVolume targetScale).toReal⁻¹ := by
      have hrightTop :
          (cwaConstant *
            Kakeya.deltaTubeVolume targetScale)⁻¹ ≠ ⊤ := by
        exact ENNReal.inv_ne_top.mpr
          (mul_ne_zero hcwaZero
            (tube_volume_scaling.2.1 targetScale
              htarget htargetOne).1.ne')
      exact
        pure_wz2_centeredCWA_volume_inv_lower_toReal
          hdelta htarget hCwaVolume hrightTop
    have hzLower :
        (1 / 48000000 : ℝ) *
            Real.rpow delta failureExponent ≤
          (cwaConstant *
            Kakeya.deltaTubeVolume targetScale).toReal⁻¹ := by
      have hexponent :
          failureExponent =
            inputEta + pruneEta - 2 * (1 - c) := by
        dsimp [failureExponent]
        ring
      rw [hexponent]
      exact
        pure_wz2_source_failure_inverse_lower
          hdelta htarget htargetUpper hinverseReal
    have htermTwo :
        Real.exp (-(3 - Real.exp 1) *
            (cwaConstant *
              Kakeya.deltaTubeVolume targetScale).toReal⁻¹) <
          1 / 16 := by
      exact
        pure_wz2_thinning_failure_of_count_lower
          (by linarith [Real.exp_one_lt_three])
          hzLower
          (by
            have h := thresholds.count delta hdelta hdeltaBound
            dsimp [failureExponent] at h ⊢
            exact h)
    calc
      (net.testSets.card : ℝ) *
            Real.exp (-(11 - Real.exp 1) *
              (Kakeya.realRpowENN targetScale
                (-thinningEta)).toReal) +
          Real.exp (-(3 - Real.exp 1) *
            (cwaConstant *
              Kakeya.deltaTubeVolume targetScale).toReal⁻¹) <
        1 / 16 + 1 / 16 :=
          add_lt_add htermOne htermTwo
      _ = 1 / 8 := by norm_num
  have hCardinality :
      Kakeya.realRpowENN targetScale (-2 + cardLoss) ≤
        (pureWZ2ThinnedAnalyticConflictBound
            net thinningEta + 1)⁻¹ *
          densityConstant *
          ((1 / 2 : ENNReal) *
            (cwaConstant *
              Kakeya.deltaTubeVolume targetScale)⁻¹ *
            densityConstant) := by
    have hcardGap :
        0 ≤ cardLoss - thinningEta := by
      dsimp [cardLoss, thinningEta]
      linarith
    have habsorb :=
      thresholds.cardinality delta hdelta hdeltaBound
    have habsorb' :
        ENNReal.ofReal
            (2 * 97200000000000001 *
              12000000 ^ 2 * 48000000 : ℝ) *
            Kakeya.realRpowENN delta
              ((1 - c) * (cardLoss - thinningEta) -
                inputEta - 3 * pruneEta) ≤
          1 := by
      dsimp [cardinalityGap] at habsorb
      exact habsorb
    exact
      pure_wz2_final_cardinality_from_centered_bounds
        (delta := delta)
        (targetScale := targetScale)
        (scaleExponent := 1 - c)
        (cardLoss := cardLoss)
        (thinningEta := thinningEta)
        (inputEta := inputEta)
        (pruneEta := pruneEta)
        hdelta htarget htargetOne htargetUpper
        hcardGap hthinningEta.le net hnetLoss
        densityConstant hDensityLower hCwaVolume
        habsorb'

  -- Continue through the explicit probabilistic core wrapper only after all
  -- dependent certificates have been closed.
  have hcoreWitness :
      Nonempty
        (PureWZ2FiniteAssertionDCore
          (assertionEta := coreEta)
          (requestedCardLoss := cardLoss)
          centeredFamily centeredShading) :=
    hcore targetScale htarget htargetCore
      centeredFamily prepared.centered_nonempty
      prepared.centered_ball centeredShading
      densityConstant cwaConstant thinningEta
      hdensityPositive hcwaZero hcwaTop hthinningEta
      hcwa hperTube hCenteredCV net hProbability
      hdensityWeak hhighKatz hCardinality

  rcases hcoreWitness with ⟨core⟩
  have hcoreUnion :
      core.targetShading.union ⊆
        wz2PaperCenteredLiteralRescalingAffineEquiv
            (prepared.nearby.scaleData.coarse.tube prepared.parent)
            prepared.nearby.scaleData.rho_pos ''
          shading.union :=
    core.target_union_subset.trans
      (prepared.centeredShading_union_subset hrhoSmall')
  have hsourceAbsorbRaw :=
    thresholds.source delta hdelta hdeltaBound
  have hsourceAbsorb' :
      Kakeya.realRpowENN delta sourceGap ≤
        ENNReal.ofReal (1000000 * kappa) := by
    exact
      pure_wz2_ofReal_inv_mul_le_one
        (mul_pos (by norm_num) hkappa) hsourceAbsorbRaw
  have hfloorExponent :
      0 <
        outputEpsilon - assertionEpsilon -
          cardLoss / 2 := by
    dsimp [assertionEpsilon, cardLoss]
    have hcoreOutput : coreEta ≤ outputEpsilon / 64 := by
      exact min_le_right _ _ |>.trans (min_le_left _ _)
    nlinarith
  have hfloorDenominator :
      0 <
        3 / 2 - assertionEpsilon -
          cardLoss / 2 := by
    dsimp [assertionEpsilon, cardLoss]
    have hcoreOutput : coreEta ≤ outputEpsilon / 64 := by
      exact min_le_right _ _ |>.trans (min_le_left _ _)
    nlinarith
  have hcNonnegative : 0 ≤ c := by
    dsimp [c]
    positivity
  have hcBound :
      c <
        (outputEpsilon - assertionEpsilon -
            cardLoss / 2) /
          (3 / 2 - assertionEpsilon -
            cardLoss / 2) := by
    rw [lt_div_iff₀ hfloorDenominator]
    dsimp [assertionEpsilon, cardLoss, c]
    have hcoreOutput : coreEta ≤ outputEpsilon / 64 := by
      exact min_le_right _ _ |>.trans (min_le_left _ _)
    nlinarith
  exact
    pure_wz2_direct_assertionD_floor
      hdelta hdeltaOne hrho houtputEpsilon
      hassertionEpsilon hassertionOutput
      houtputSmall
      hcardNonnegative
      hfloorExponent hfloorDenominator
      hcNonnegative hcBound
      prepared.scale_lower hkappa hcoreEta
      hcoreAssertionEta hsourceAbsorb'
      hAssertionMain shading centeredShading core
      (prepared.nearby.scaleData.coarse.tube prepared.parent)
      hcoreUnion

/-- Literal complete-full-fiber proof of the pure WZ2 Wolff floor. -/
theorem pure_wz2_direct_wolff_floor :
    PureWZ2WolffVolumeFloor := by
  intro outputEpsilon houtputEpsilon
  by_cases houtputSmall : outputEpsilon < 1
  · exact
      pure_wz2_direct_wolff_floor_small
        outputEpsilon houtputEpsilon houtputSmall
  · rcases
        pure_wz2_direct_wolff_floor_small
          (1 / 2) (by norm_num) (by norm_num) with
      ⟨eta, delta₀, heta, hdelta₀, hdelta₀One, hfloor⟩
    refine
      ⟨eta, delta₀, heta, hdelta₀, hdelta₀One, ?_⟩
    intro delta hdelta hdeltaBound family hfamilyNonempty
      hCWA shading hdense
    have hbase :=
      hfloor delta hdelta hdeltaBound family
        hfamilyNonempty hCWA shading hdense
    exact
      (pure_wz2_rpowENN_antitone
        hdelta
        (hdeltaBound.trans hdelta₀One)
        (by linarith : 1 / 2 + (1 / 2 : ℝ) ≤
          1 / 2 + outputEpsilon)).trans hbase

end Kakeya.Assouad

end
