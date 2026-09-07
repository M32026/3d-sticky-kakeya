import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Node6FixedSqrtAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Node6FixedScaleBudgets
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Node6FixedPreconditioningCap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Node6Lemma31ScaleInterface
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FrameNormalCompatibilityCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FaithfulConvexOverload
import MyLeanRepo.Kakeya.Assouad.PureWZ2.IntervalSlopeExtension

/-!
# Fixed-output WZ2 Lemma 31 power-scale assembly

This is the fixed-scale parallel replacement for the historical full-sticky
assembly.  Its public record keeps only the data consumed downstream.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

private def node6FixedPowerRequestedScale
    {delta power : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hpower : 0 < power) (hpowerOne : power ≤ 1) :
    WZ2PaperRequestedScale delta :=
  ⟨Real.rpow delta power, by
    constructor
    · simpa using
        (Real.rpow_le_rpow_of_exponent_ge
          hdelta hdeltaOne hpowerOne :
          Real.rpow delta 1 ≤ Real.rpow delta power)
    · exact Real.rpow_le_one hdelta.le hdeltaOne hpower.le⟩

@[simp] private theorem node6FixedPowerRequestedScale_value
    {delta power : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hpower : 0 < power) (hpowerOne : power ≤ 1) :
    (node6FixedPowerRequestedScale hdelta hdeltaOne
      hpower hpowerOne).1 = Real.rpow delta power := rfl

private theorem node6_fixed_power_scale_window
    {delta loss power : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hlossPower : loss ≤ power)
    (hpowerUpper : power ≤ 1 - loss) :
    Real.rpow delta (1 - loss) ≤ Real.rpow delta power ∧
      Real.rpow delta power ≤ Real.rpow delta loss := by
  constructor
  · exact Real.rpow_le_rpow_of_exponent_ge
      hdelta hdeltaOne hpowerUpper
  · exact Real.rpow_le_rpow_of_exponent_ge
      hdelta hdeltaOne hlossPower

private theorem exists_delta_node6_fixed_ratio_power_gap
    (power firstLoss secondLoss : ℝ)
    (hpower : 0 < power) (hloss : firstLoss < secondLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
        (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 *
            Kakeya.realRpowENN delta (power * secondLoss) ≤
          Kakeya.realRpowENN delta (power * firstLoss) := by
  have hgap : 0 < power * (secondLoss - firstLoss) := by positivity
  rcases exists_delta_C_pow_log_absorbed_ennreal
      (1 : ENNReal) (by norm_num) 2 (by norm_num)
      hgap (by norm_num : 0 < (10 : ℕ)) with
    ⟨delta₀, hdelta₀, hdelta₀One, habsorb⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaBound
  have hdeltaOne : delta ≤ 1 := hdeltaBound.trans hdelta₀One
  have hcount := node6_fixed_directionLevelCount_le_logEnvelope
    hdelta hdeltaOne
  have hcountPow :
      (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 ≤
        (2 * ENNReal.ofReal (1 + Real.log delta⁻¹)) ^ 10 :=
    pow_le_pow_left' hcount 10
  have hratio :
      (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 ≤
        Kakeya.realRpowENN delta
          (-(power * (secondLoss - firstLoss))) := by
    exact hcountPow.trans (by
      simpa [mul_comm] using habsorb delta hdelta hdeltaBound)
  calc
    (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 *
          Kakeya.realRpowENN delta (power * secondLoss) ≤
        Kakeya.realRpowENN delta
            (-(power * (secondLoss - firstLoss))) *
          Kakeya.realRpowENN delta (power * secondLoss) := by gcongr
    _ = Kakeya.realRpowENN delta (power * firstLoss) := by
      rw [← realRpowENN_add hdelta]
      congr 2
      ring

private theorem exists_delta_node6_fixed_lemma31_scalars
    (sourceLoss stickyLoss targetLoss power : ℝ)
    (hsourceTarget : sourceLoss < targetLoss)
    (hcellGap : power * stickyLoss < 2 * targetLoss - sourceLoss)
    (htarget : 0 < targetLoss)
    (logExponent : ℕ) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
        (ENNReal.ofReal Real.pi *
              (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 *
              Kakeya.realRpowENN delta targetLoss ≤
            wz2PaperPureRefinementFraction delta logExponent *
              Kakeya.realRpowENN delta sourceLoss) ∧
        (ENNReal.ofReal (4 * Real.pi) *
              Kakeya.realRpowENN delta
                (2 * targetLoss - sourceLoss) ≤
            wz2PaperPureRefinementFraction delta logExponent *
              Kakeya.realRpowENN delta (power * stickyLoss)) ∧
        ((16 : ENNReal) ≤
          Kakeya.realRpowENN delta (-targetLoss)) := by
  let middleLoss := (sourceLoss + targetLoss) / 2
  have hsourceMiddle : sourceLoss < middleLoss := by
    dsimp only [middleLoss]
    linarith
  have hmiddleTarget : middleLoss < targetLoss := by
    dsimp only [middleLoss]
    linarith
  rcases exists_delta_node6_fixed_ratio_refinement_absorption
      sourceLoss middleLoss hsourceMiddle logExponent with
    ⟨ratioMassScale, hratioMassScale, hratioMassScaleOne, hratioMass⟩
  rcases exists_delta_constant_mul_power_le_power
      (ENNReal.ofReal Real.pi) ENNReal.ofReal_ne_top
      middleLoss targetLoss hmiddleTarget with
    ⟨piScale, hpiScale, hpiScaleOne, hpi⟩
  rcases exists_delta_constant_mul_pure_refinement_fraction_absorbs
      (ENNReal.ofReal (4 * Real.pi)) ENNReal.ofReal_ne_top
      (power * stickyLoss) (2 * targetLoss - sourceLoss)
      hcellGap logExponent with
    ⟨cellScale, hcellScale, hcellScaleOne, hcell⟩
  rcases exists_delta_realRpowENN_bound
      (16 : ENNReal) (by norm_num) htarget with
    ⟨coverScale, hcoverScale, hcoverScaleOne, hcover⟩
  let delta₀ := min ratioMassScale
    (min piScale (min cellScale coverScale))
  refine ⟨delta₀, by dsimp only [delta₀]; positivity,
    (min_le_left _ _).trans hratioMassScaleOne, ?_⟩
  intro delta hdelta hdeltaBound
  have hdeltaRatioMass : delta ≤ ratioMassScale :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaPi : delta ≤ piScale :=
    hdeltaBound.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmass :
      ENNReal.ofReal Real.pi *
          (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 *
          Kakeya.realRpowENN delta targetLoss ≤
        wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta sourceLoss := by
    calc
      ENNReal.ofReal Real.pi *
            (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 *
            Kakeya.realRpowENN delta targetLoss =
          (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 *
            (ENNReal.ofReal Real.pi *
              Kakeya.realRpowENN delta targetLoss) := by ring
      _ ≤ (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 *
            Kakeya.realRpowENN delta middleLoss := by
        gcongr
        exact hpi hdelta hdeltaPi
      _ ≤ wz2PaperPureRefinementFraction delta logExponent *
            Kakeya.realRpowENN delta sourceLoss :=
        hratioMass hdelta hdeltaRatioMass
  exact
    ⟨hmass,
      hcell hdelta (hdeltaBound.trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _)))),
      hcover delta hdelta (hdeltaBound.trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _))))⟩

private def node6FixedLemma31SourceCap
    (sigma epsilon stickyLoss powerInputLoss : ℝ)
    {sourceLoss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta) : Prop :=
  sourceLoss ≤ powerInputLoss →
    ∀ point,
      (cfg.shading.pointMultiplicity point : ENNReal) ≤
        (Kakeya.realRpowENN delta
            (2 - sigma - stickyLoss) *
          Kakeya.realRpowENN (Real.rpow delta epsilon)
            (-stickyLoss)) *
          cfg.family.enncard

private theorem node6_fixed_lemma31_source_provider
    {logExponent : ℕ}
    (hc2grains : PureWZ2C2GrainsFromCriticalStatement)
    (certifiedProvider : PureWZ2Node6FixedScaleCriticalAt logExponent)
    (sigma : ℝ) (critical : PureWZ2CriticalPackage sigma)
    (epsilon stickyLoss powerInputLoss : ℝ)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hpowerInputHalf : powerInputLoss ≤ 1 / 2)
    (hpowerInputStickyHalf : powerInputLoss ≤ stickyLoss / 2) :
    ∀ sourceLoss localBound : ℝ,
      0 < sourceLoss → 0 < localBound →
        ∃ delta : ℝ, 0 < delta ∧ delta ≤ localBound ∧
          ∃ cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta,
            node6FixedLemma31SourceCap
              sigma epsilon stickyLoss powerInputLoss cfg := by
  intro sourceLoss localBound hsourceLoss hlocalBound
  by_cases hsourcePower : sourceLoss ≤ powerInputLoss
  · let preLoss := sourceLoss / 2
    have hpreLoss : 0 < preLoss := by
      dsimp only [preLoss]
      positivity
    have hpreLossOne : preLoss ≤ 1 := by
      dsimp only [preLoss]
      linarith [hpowerInputHalf]
    have hpreLossHalf : preLoss ≤ 1 / 2 := by
      dsimp only [preLoss]
      linarith [hpowerInputHalf]
    rcases certifiedProvider sigma critical preLoss hpreLoss
        hpreLossOne with
      ⟨preSourceLoss, preScale, hpreSource, hpreSourceLoss,
        hpreScale, hpreScaleOne, providePre⟩
    have hpreSourceTarget : preSourceLoss < sourceLoss := by
      exact hpreSourceLoss.trans_lt <| by
        dsimp only [preLoss]
        linarith
    rcases exists_delta_pure_refinement_fraction_absorbs
        preSourceLoss sourceLoss hpreSourceTarget logExponent with
      ⟨preDensityScale, hpreDensityScale, _hpreDensityScaleOne,
        preDensityAbsorb⟩
    let preBound := min localBound (min preScale preDensityScale)
    have hpreBound : 0 < preBound := by
      dsimp only [preBound]
      positivity
    rcases hc2grains sigma critical preSourceLoss preBound
        hpreSource hpreBound with
      ⟨delta, hdelta, hdeltaPreBound, ⟨preSourceCfg⟩⟩
    have hdeltaLocal : delta ≤ localBound :=
      hdeltaPreBound.trans (by simp [preBound])
    have hdeltaPreScale : delta ≤ preScale :=
      hdeltaPreBound.trans (by simp [preBound])
    have hdeltaPreDensity : delta ≤ preDensityScale :=
      hdeltaPreBound.trans (by simp [preBound])
    have hdeltaOne : delta ≤ 1 :=
      hdeltaPreScale.trans hpreScaleOne
    let preRho : WZ2PaperRequestedScale delta :=
      node6FixedPowerRequestedScale hdelta hdeltaOne
        hpreLoss hpreLossOne
    have hpreWindow := node6_fixed_power_scale_window
      (loss := preLoss) (power := preLoss)
      hdelta hdeltaOne le_rfl (by linarith [hpreLossHalf])
    rcases providePre delta hdelta hdeltaPreScale preSourceCfg preRho
        (by
          change Real.rpow delta (1 - preLoss) ≤
            Real.rpow delta preLoss
          exact hpreWindow.1)
        (by
          change Real.rpow delta preLoss ≤
            Real.rpow delta preLoss
          exact le_rfl) with
      ⟨preCertified⟩
    rcases preCertified.fixed.zeroExtendC2 preSourceCfg
        hsourceLoss.le hpreSourceTarget.le
        (by dsimp only [preLoss]; linarith)
        (preDensityAbsorb hdelta hdeltaPreDensity) with
      ⟨preZeroData⟩
    let preCfg := preZeroData.configuration
    refine ⟨delta, hdelta, hdeltaLocal, preCfg, ?_⟩
    intro _
    apply preCertified.fixed.pointMultiplicity_upper_preconditioned
      preCfg.shading rfl hdelta hdeltaOne hpreLoss hpreLossOne
    · intro point
      change
        (preZeroData.zeroExtension.ambientShading.pointMultiplicity
            point : ENNReal) ≤
          (preCertified.fixed.refined.pointMultiplicity point : ENNReal)
      exact_mod_cast le_of_eq
        (preZeroData.zeroExtension.node6_pointMultiplicity_eq point)
    · change preCertified.fixed.selected.family.enncard ≤
        preSourceCfg.family.enncard
      have hcard : preCertified.fixed.selected.family.card ≤
          preSourceCfg.family.card := by
        simpa using Fintype.card_le_of_injective
          preCertified.fixed.selected.embedding
          preCertified.fixed.selected.embedding.injective
      simp only [Kakeya.Streamlined.TubeFamily.enncard]
      exact_mod_cast hcard
    · dsimp only [preLoss]
      have hsourceStickyHalf : sourceLoss ≤ stickyLoss / 2 :=
        hsourcePower.trans hpowerInputStickyHalf
      have hstickyPos : 0 < stickyLoss := by
        linarith [hsourceLoss]
      have hthreeSigma : 0 ≤ 3 - sigma := by
        linarith [critical.sigma_lt_one]
      have hlinear :
          sourceLoss * (3 - sigma) ≤
            (stickyLoss / 2) * (3 - sigma) :=
        mul_le_mul_of_nonneg_right hsourceStickyHalf hthreeSigma
      have hepsilonSticky : 0 ≤ epsilon * stickyLoss :=
        mul_nonneg hepsilon.le hstickyPos.le
      nlinarith [sq_nonneg sourceLoss, critical.sigma_pos]
  · rcases hc2grains sigma critical sourceLoss localBound
        hsourceLoss hlocalBound with
      ⟨delta, hdelta, hdeltaLocal, ⟨cfg⟩⟩
    exact ⟨delta, hdelta, hdeltaLocal, cfg,
      fun h => (hsourcePower h).elim⟩

theorem pureWZ2_node6_fixed_lemma31_scale_assembly_with_eta
    {logExponent : ℕ}
    (hc2grains : PureWZ2C2GrainsFromCriticalStatement)
    (certifiedProvider : PureWZ2Node6FixedScaleCriticalAt logExponent)
    (sigma : ℝ) (critical : PureWZ2CriticalPackage sigma)
    (epsilon eta deltaBound : ℝ)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (heta : 0 < eta) (hetaBudget : 1000 * eta ≤ epsilon * sigma ^ 2)
    (hdeltaBound : 0 < deltaBound) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ deltaBound ∧
      ∃ data : PureWZ2Lemma31ScaleAssembly sigma epsilon delta,
        data.eta = eta := by
  let targetLoss := eta / 8
  let stickyLoss := eta / 4096
  let powerLoss := stickyLoss / 2
  have htarget : 0 < targetLoss := by
    dsimp only [targetLoss]
    positivity
  have hsticky : 0 < stickyLoss := by
    dsimp only [stickyLoss]
    positivity
  have hpowerLoss : 0 < powerLoss := by
    dsimp only [powerLoss]
    positivity
  have hsigmaSqOne : sigma ^ 2 < 1 := by
    nlinarith [mul_pos critical.sigma_pos
      (sub_pos.mpr critical.sigma_lt_one)]
  have hetaEpsilon : eta ≤ epsilon := by
    have hscaled : epsilon * sigma ^ 2 ≤ 1000 * epsilon := by
      nlinarith [hepsilon, hsigmaSqOne]
    nlinarith
  have hpowerLossOne : powerLoss ≤ 1 := by
    dsimp only [powerLoss, stickyLoss]
    linarith
  rcases certifiedProvider sigma critical powerLoss hpowerLoss
      hpowerLossOne with
    ⟨powerInputLoss, powerScale, hpowerInput,
      hpowerInputPower, hpowerScale, _hpowerScaleOne, providePower⟩
  have hpowerInputSticky : powerInputLoss ≤ stickyLoss := by
    exact hpowerInputPower.trans (by
      dsimp only [powerLoss]
      linarith [hsticky])
  have hpowerInputHalf : powerInputLoss ≤ 1 / 2 := by
    have hpowerLossHalf : powerLoss ≤ 1 / 2 := by
      dsimp only [powerLoss, stickyLoss]
      linarith
    exact hpowerInputPower.trans hpowerLossHalf
  have hetaSigma : eta < sigma := by
    have hsigmaSqLt : sigma ^ 2 < sigma := by
      nlinarith [mul_pos critical.sigma_pos
        (sub_pos.mpr critical.sigma_lt_one)]
    have hscaled : 1000 * eta < epsilon * sigma := by
      exact lt_of_le_of_lt hetaBudget <| by
        nlinarith [mul_pos hepsilon (sub_pos.mpr hsigmaSqLt)]
    nlinarith
  have hpowerInputSigma : 16 * powerInputLoss < sigma := by
    have hsourceSticky' : 16 * powerInputLoss ≤ 16 * stickyLoss := by
      gcongr
    have hstickyEta : 16 * stickyLoss < eta := by
      dsimp only [stickyLoss]
      linarith [heta]
    exact hsourceSticky'.trans_lt (hstickyEta.trans hetaSigma)
  have hpowerInputTarget : powerInputLoss < targetLoss := by
    exact hpowerInputPower.trans_lt <| by
      dsimp only [powerLoss, stickyLoss, targetLoss]
      linarith [heta]
  have hcellGap : epsilon * stickyLoss <
      2 * targetLoss - powerInputLoss := by
    have hraw : epsilon * stickyLoss <
        2 * targetLoss - stickyLoss := by
      dsimp only [stickyLoss, targetLoss]
      nlinarith [mul_pos heta (sub_pos.mpr (by linarith : epsilon < 7))]
    exact hraw.trans_le
      (sub_le_sub_left hpowerInputSticky (2 * targetLoss))
  rcases exists_delta_pure_refinement_fraction_absorbs
      powerInputLoss targetLoss hpowerInputTarget logExponent with
    ⟨densityScale, hdensityScale, _hdensityScaleOne, densityAbsorb⟩
  rcases exists_delta_node6_fixed_lemma31_scalars
      powerInputLoss stickyLoss targetLoss epsilon hpowerInputTarget hcellGap
      htarget logExponent with
    ⟨scalarScale, hscalarScale, _hscalarScaleOne, scalarAbsorb⟩
  rcases exists_delta_node6_fixed_ratio_power_gap epsilon powerLoss
      stickyLoss hepsilon (by
        dsimp only [powerLoss]
        linarith [hsticky]) with
    ⟨ratioScale, hratioScale, _hratioScaleOne, ratioAbsorb⟩
  have htargetEta : targetLoss ≤ eta := by
    dsimp only [targetLoss]
    linarith [heta]
  rcases large_slope_faithful_convex_overload
      epsilon sigma eta targetLoss hepsilon hepsilonHalf
      critical.sigma_pos critical.sigma_lt_one heta hetaEpsilon
      htargetEta hetaBudget with
    ⟨overloadScale, hoverloadScale, _hoverloadScaleOne, overload⟩
  let SourceCap : ∀ {sourceLoss delta : ℝ},
      PureWZ2C2GrainConfiguration sigma sourceLoss delta → Prop :=
    node6FixedLemma31SourceCap
      sigma epsilon stickyLoss powerInputLoss
  have hpowerInputStickyHalf :
      powerInputLoss ≤ stickyLoss / 2 := by
    simpa only [powerLoss] using hpowerInputPower
  let sourceProvider : ∀ sourceLoss localBound : ℝ,
      0 < sourceLoss → 0 < localBound →
        ∃ delta : ℝ, 0 < delta ∧ delta ≤ localBound ∧
          ∃ cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta,
            SourceCap cfg :=
    node6_fixed_lemma31_source_provider
      hc2grains certifiedProvider sigma critical
      epsilon stickyLoss powerInputLoss hepsilon hepsilonHalf
      hpowerInputHalf hpowerInputStickyHalf
  let sqrtBound := min deltaBound
    (min powerScale
      (min densityScale (min scalarScale
        (min ratioScale (min overloadScale (1 / 24))))))
  have hsqrtBound : 0 < sqrtBound := by
    dsimp only [sqrtBound]
    positivity
  rcases pureWZ2_node6_fixed_sqrt_assembly_with_source_property
      (P := SourceCap) sigma sourceProvider certifiedProvider critical
      powerInputLoss sqrtBound hpowerInput hpowerInputHalf
      hpowerInputSigma hsqrtBound with
    ⟨delta, hdelta, hdeltaSqrt, sqrtData, hsourceCap⟩
  have hsourcePowerInput : sqrtData.sourceLoss ≤ powerInputLoss :=
    sqrtData.sourceLoss_le_fixedLoss.trans
      sqrtData.fixedLoss_le_slabLoss
  have hsqrtSourceCap := hsourceCap hsourcePowerInput
  have hdeltaBound' : delta ≤ deltaBound :=
    hdeltaSqrt.trans (by simp [sqrtBound])
  have hdeltaProvider : delta ≤ powerScale :=
    hdeltaSqrt.trans (by simp [sqrtBound])
  have hdeltaDensity : delta ≤ densityScale :=
    hdeltaSqrt.trans (by simp [sqrtBound])
  have hdeltaScalar : delta ≤ scalarScale :=
    hdeltaSqrt.trans (by simp [sqrtBound])
  have hdeltaRatio : delta ≤ ratioScale :=
    hdeltaSqrt.trans (by simp [sqrtBound])
  have hdeltaOverload : delta ≤ overloadScale :=
    hdeltaSqrt.trans (by simp [sqrtBound])
  have hdeltaSmall : delta ≤ 1 / 24 :=
    hdeltaSqrt.trans (by simp [sqrtBound])
  let rho : WZ2PaperRequestedScale delta :=
    node6FixedPowerRequestedScale sqrtData.cfg.extremal.delta_pos
      sqrtData.cfg.extremal.delta_le_one hepsilon
      (hepsilonHalf.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have hstickyPower : powerLoss ≤ epsilon := by
    dsimp only [powerLoss, stickyLoss]
    linarith
  have hepsilonUpper : epsilon ≤ 1 - powerLoss := by
    linarith
  have hwindow := node6_fixed_power_scale_window
    hdelta sqrtData.cfg.extremal.delta_le_one
    hstickyPower hepsilonUpper
  rcases providePower delta hdelta hdeltaProvider sqrtData.cfg rho
      (by
        change Real.rpow delta (1 - powerLoss) ≤
          Real.rpow delta epsilon
        exact hwindow.1)
      (by
        change Real.rpow delta epsilon ≤
          Real.rpow delta powerLoss
        exact hwindow.2) with
    ⟨certified⟩
  have hsourceTarget : powerInputLoss ≤ targetLoss := by
    exact hpowerInputSticky.trans <| by
      dsimp only [stickyLoss, targetLoss]
      linarith [heta]
  have hpowerTarget : powerLoss ≤ targetLoss := by
    dsimp only [powerLoss, stickyLoss, targetLoss]
    linarith [heta]
  have hdensity :
      Kakeya.realRpowENN delta targetLoss ≤
        wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta powerInputLoss := by
    exact densityAbsorb hdelta hdeltaDensity
  rcases certified.fixed.zeroExtendC2 sqrtData.cfg htarget.le
      hsourceTarget hpowerTarget hdensity with
    ⟨zeroData⟩
  let fixed := certified.fixed
  let targetMass : ENNReal :=
    ENNReal.ofReal (Real.pi / 4) *
      Kakeya.realRpowENN delta (targetLoss + 2) *
      sqrtData.cfg.family.enncard * ENNReal.ofReal rho.1
  let coverBudget : ENNReal :=
    Kakeya.realRpowENN delta (-targetLoss) *
      Kakeya.realRpowENN rho.1 (-2 + sigma)
  have hscalars := scalarAbsorb hdelta hdeltaScalar
  have hratioGap := ratioAbsorb hdelta hdeltaRatio
  have hFourPiQuarter :
      (4 : ENNReal) * ENNReal.ofReal (Real.pi / 4) =
        ENNReal.ofReal Real.pi := by
    rw [show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) by norm_num]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    ring
  have htargetPower :
      Kakeya.realRpowENN delta (targetLoss + 2) =
        Kakeya.realRpowENN delta targetLoss *
          Kakeya.realRpowENN delta 2 := by
    rw [realRpowENN_add hdelta]
  have hglobalScalar :
      4 * fixed.cellIndexedMassRatio * targetMass ≤
        ENNReal.ofReal rho.1 *
          (wz2PaperPureRefinementFraction delta logExponent *
            (Kakeya.realRpowENN delta powerInputLoss *
              sqrtData.cfg.family.enncard *
              Kakeya.realRpowENN delta 2)) := by
    calc
      4 * fixed.cellIndexedMassRatio * targetMass =
          ((4 : ENNReal) * ENNReal.ofReal (Real.pi / 4)) *
            fixed.cellIndexedMassRatio *
            (Kakeya.realRpowENN delta targetLoss *
              Kakeya.realRpowENN delta 2) *
            sqrtData.cfg.family.enncard *
            ENNReal.ofReal rho.1 := by
        dsimp only [targetMass]
        rw [htargetPower]
        ring
      _ = ENNReal.ofReal rho.1 *
            ((ENNReal.ofReal Real.pi *
                fixed.cellIndexedMassRatio *
                Kakeya.realRpowENN delta targetLoss) *
              (sqrtData.cfg.family.enncard *
                Kakeya.realRpowENN delta 2)) := by
        rw [hFourPiQuarter]
        ring
      _ ≤ ENNReal.ofReal rho.1 *
            ((ENNReal.ofReal Real.pi *
                (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 *
                Kakeya.realRpowENN delta targetLoss) *
              (sqrtData.cfg.family.enncard *
                Kakeya.realRpowENN delta 2)) := by
        gcongr
        exact fixed.cellIndexedMassRatio_le_logarithmicLoss
      _ ≤ ENNReal.ofReal rho.1 *
            ((wz2PaperPureRefinementFraction delta logExponent *
                Kakeya.realRpowENN delta powerInputLoss) *
              (sqrtData.cfg.family.enncard *
                Kakeya.realRpowENN delta 2)) := by
        exact mul_le_mul_left'
          (mul_le_mul_right' hscalars.1
            (sqrtData.cfg.family.enncard *
              Kakeya.realRpowENN delta 2))
          (ENNReal.ofReal rho.1)
      _ = ENNReal.ofReal rho.1 *
            (wz2PaperPureRefinementFraction delta logExponent *
              (Kakeya.realRpowENN delta powerInputLoss *
                sqrtData.cfg.family.enncard *
                Kakeya.realRpowENN delta 2)) := by
        ring
  have hsourceMass :
      Kakeya.realRpowENN delta powerInputLoss *
          sqrtData.cfg.family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        sqrtData.cfg.shading.mass := by
    calc
      Kakeya.realRpowENN delta powerInputLoss *
            sqrtData.cfg.family.enncard *
            Kakeya.realRpowENN delta 2 =
          Kakeya.realRpowENN delta powerInputLoss *
            (sqrtData.cfg.family.enncard *
              Kakeya.realRpowENN delta 2) := by ring
      _ ≤ Kakeya.realRpowENN delta powerInputLoss *
          (wz1PaperBodyFamily sqrtData.cfg.family).mass := by
        gcongr
        exact pureWZ2_prop62_paper_body_mass_lower
          hdelta
          (hdeltaSmall.trans (by norm_num : (1 / 24 : ℝ) ≤ 1 / 12))
          sqrtData.cfg.line_class
      _ ≤ sqrtData.cfg.shading.mass := sqrtData.cfg.extremal.dense
  have hrefinedMass :
      wz2PaperPureRefinementFraction delta logExponent *
          (Kakeya.realRpowENN delta powerInputLoss *
            sqrtData.cfg.family.enncard *
            Kakeya.realRpowENN delta 2) ≤
        fixed.refined.mass := by
    calc
      _ ≤ wz2PaperPureRefinementFraction delta logExponent *
            sqrtData.cfg.shading.mass := by gcongr
      _ ≤ fixed.refined.mass := fixed.retained_mass
  have hactive : fixed.balanced.activeCells.Nonempty := by
    by_contra hempty
    have hcells : fixed.balanced.activeCells = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hrefinedZero : fixed.refined.mass = 0 := by
      rw [fixed.refined_mass_eq_sum_cellIndexedMass
        zeroData.zeroExtension, hcells]
      simp
    have hfamilyPos : 0 < sqrtData.cfg.family.enncard := by
      change (0 : ENNReal) < (sqrtData.cfg.family.card : ENNReal)
      exact_mod_cast
        (lt_of_lt_of_le Nat.zero_lt_one sqrtData.cfg.extremal.nonempty)
    have hrefinementPos :
        0 < wz2PaperPureRefinementFraction delta logExponent := by
      unfold wz2PaperPureRefinementFraction
      exact ENNReal.pow_pos
        (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top) logExponent
    have hsourcePowerPos :
        0 < Kakeya.realRpowENN delta powerInputLoss := by
      rw [Kakeya.realRpowENN]
      exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)
    have hvolumePowerPos :
        0 < Kakeya.realRpowENN delta 2 := by
      rw [Kakeya.realRpowENN]
      exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)
    have hleftPos :
        0 <
          wz2PaperPureRefinementFraction delta logExponent *
            (Kakeya.realRpowENN delta powerInputLoss *
              sqrtData.cfg.family.enncard *
              Kakeya.realRpowENN delta 2) := by
      exact ENNReal.mul_pos hrefinementPos.ne'
        (mul_ne_zero
          (mul_ne_zero hsourcePowerPos.ne' hfamilyPos.ne')
          hvolumePowerPos.ne')
    have hle :
        wz2PaperPureRefinementFraction delta logExponent *
            (Kakeya.realRpowENN delta powerInputLoss *
              sqrtData.cfg.family.enncard *
              Kakeya.realRpowENN delta 2) ≤ 0 := by
      simpa [hrefinedZero] using hrefinedMass
    exact (not_le_of_gt hleftPos) hle
  have hrefinedUpper :
      fixed.refined.mass ≤
        (fixed.balanced.activeCells.card : ENNReal) *
          (fixed.cellIndexedMassRatio *
            fixed.cellIndexedMassBase) := by
    rw [fixed.refined_mass_eq_sum_cellIndexedMass
      zeroData.zeroExtension]
    calc
      ∑ cell ∈ fixed.balanced.activeCells,
          fixed.cellIndexedMass cell ≤
        ∑ _cell ∈ fixed.balanced.activeCells,
          fixed.cellIndexedMassRatio *
            fixed.cellIndexedMassBase := by
          apply Finset.sum_le_sum
          intro cell hcell
          exact (fixed.cellIndexedMass_band cell hcell).2
      _ = (fixed.balanced.activeCells.card : ENNReal) *
          (fixed.cellIndexedMassRatio *
            fixed.cellIndexedMassBase) := by
        simp [Finset.sum_const]
  have hmassSupply :
      wz2PaperPureRefinementFraction delta logExponent *
          (Kakeya.realRpowENN delta powerInputLoss *
            sqrtData.cfg.family.enncard *
            Kakeya.realRpowENN delta 2) ≤
        (fixed.balanced.activeCells.card : ENNReal) *
          fixed.cellIndexedMassRatio *
          fixed.cellIndexedMassBase := by
    exact hrefinedMass.trans <| by
      simpa [mul_assoc] using hrefinedUpper
  have hcellRatio :
      ENNReal.ofReal (4 * Real.pi) *
          (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 *
          Kakeya.realRpowENN delta
            (2 * targetLoss - powerInputLoss) ≤
        wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta (epsilon * powerLoss) := by
    calc
      _ = (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 *
          (ENNReal.ofReal (4 * Real.pi) *
            Kakeya.realRpowENN delta
              (2 * targetLoss - powerInputLoss)) := by ring
      _ ≤ (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 *
          (wz2PaperPureRefinementFraction delta logExponent *
            Kakeya.realRpowENN delta
              (epsilon * stickyLoss)) := by
        exact mul_le_mul_left' hscalars.2.1
          ((pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10)
      _ = wz2PaperPureRefinementFraction delta logExponent *
          ((pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 *
            Kakeya.realRpowENN delta
              (epsilon * stickyLoss)) := by ring
      _ ≤ wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta (epsilon * powerLoss) := by
        gcongr
  have hrhoPower : ∀ exponent : ℝ,
      Kakeya.realRpowENN rho.1 exponent =
        Kakeya.realRpowENN delta (epsilon * exponent) := by
    intro exponent
    change Kakeya.realRpowENN (Real.rpow delta epsilon) exponent = _
    exact node6_fixed_preconditioning_realRpowENN_rpow
      hdelta epsilon exponent
  have hcoverBudgetPower :
      coverBudget =
        Kakeya.realRpowENN delta (-targetLoss) *
          Kakeya.realRpowENN delta (epsilon * (-2 + sigma)) := by
    dsimp only [coverBudget]
    rw [hrhoPower (-2 + sigma)]
  have hSixteenPiQuarter :
      (16 : ENNReal) * ENNReal.ofReal (Real.pi / 4) =
        ENNReal.ofReal (4 * Real.pi) := by
    rw [show (16 : ENNReal) = ENNReal.ofReal (16 : ℝ) by norm_num]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
    congr 1
    ring
  have hselectionDeltaPower :
      Kakeya.realRpowENN delta (targetLoss + 2) =
        Kakeya.realRpowENN delta
            (2 * targetLoss - powerInputLoss) *
          Kakeya.realRpowENN delta
            (powerInputLoss - targetLoss + 2) := by
    rw [← realRpowENN_add hdelta]
    congr 1
    ring
  have hrhoShift :
      ENNReal.ofReal rho.1 *
          Kakeya.realRpowENN rho.1
            (sigma - powerLoss - 3) =
        Kakeya.realRpowENN rho.1
          (sigma - powerLoss - 2) := by
    rw [show ENNReal.ofReal rho.1 =
        Kakeya.realRpowENN rho.1 1 by
      rw [Kakeya.realRpowENN]
      exact congrArg ENNReal.ofReal (Real.rpow_one _).symm]
    rw [← realRpowENN_add (hdelta.trans_le rho.2.1)]
    congr 1
    ring
  have hselectionScaled :
      16 *
          (targetMass *
            ((fixed.balanced.activeCells.card : ENNReal) *
              fixed.cellIndexedMassRatio)) ≤
        coverBudget *
          ((fixed.balanced.activeCells.card : ENNReal) *
            fixed.cellIndexedMassRatio *
            fixed.cellIndexedMassBase) := by
    calc
      16 *
            (targetMass *
              ((fixed.balanced.activeCells.card : ENNReal) *
                fixed.cellIndexedMassRatio)) ≤
          16 *
            (targetMass *
              (Kakeya.realRpowENN rho.1
                  (sigma - powerLoss - 3) *
                (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10)) := by
        gcongr
        · exact fixed.activeCells_card_upper
        · exact fixed.cellIndexedMassRatio_le_logarithmicLoss
      _ =
          (ENNReal.ofReal (4 * Real.pi) *
              (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 *
              Kakeya.realRpowENN delta
                (2 * targetLoss - powerInputLoss)) *
            (Kakeya.realRpowENN delta
                (powerInputLoss - targetLoss + 2) *
              sqrtData.cfg.family.enncard *
              Kakeya.realRpowENN rho.1
                (sigma - powerLoss - 2)) := by
        dsimp only [targetMass]
        calc
          16 *
                (ENNReal.ofReal (Real.pi / 4) *
                    Kakeya.realRpowENN delta (targetLoss + 2) *
                    sqrtData.cfg.family.enncard *
                    ENNReal.ofReal rho.1 *
                  (Kakeya.realRpowENN rho.1
                      (sigma - powerLoss - 3) *
                    (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10)) =
              ((16 : ENNReal) * ENNReal.ofReal (Real.pi / 4)) *
                (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 *
                Kakeya.realRpowENN delta (targetLoss + 2) *
                sqrtData.cfg.family.enncard *
                (ENNReal.ofReal rho.1 *
                  Kakeya.realRpowENN rho.1
                    (sigma - powerLoss - 3)) := by ring
          _ = ENNReal.ofReal (4 * Real.pi) *
                (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 *
                Kakeya.realRpowENN delta
                  (2 * targetLoss - powerInputLoss) *
                (Kakeya.realRpowENN delta
                    (powerInputLoss - targetLoss + 2) *
                  sqrtData.cfg.family.enncard *
                  Kakeya.realRpowENN rho.1
                    (sigma - powerLoss - 2)) := by
            rw [hSixteenPiQuarter, hselectionDeltaPower, hrhoShift]
            ring
      _ ≤
          (wz2PaperPureRefinementFraction delta logExponent *
              Kakeya.realRpowENN delta (epsilon * powerLoss)) *
            (Kakeya.realRpowENN delta
                (powerInputLoss - targetLoss + 2) *
              sqrtData.cfg.family.enncard *
              Kakeya.realRpowENN rho.1
                (sigma - powerLoss - 2)) := by
        gcongr
      _ =
          coverBudget *
            (wz2PaperPureRefinementFraction delta logExponent *
              (Kakeya.realRpowENN delta powerInputLoss *
                sqrtData.cfg.family.enncard *
                Kakeya.realRpowENN delta 2)) := by
        rw [hcoverBudgetPower, hrhoPower (sigma - powerLoss - 2)]
        have hpowerIdentity :
            Kakeya.realRpowENN delta (epsilon * powerLoss) *
                Kakeya.realRpowENN delta
                  (powerInputLoss - targetLoss + 2) *
                Kakeya.realRpowENN delta
                  (epsilon * (sigma - powerLoss - 2)) =
              Kakeya.realRpowENN delta (-targetLoss) *
                Kakeya.realRpowENN delta
                  (epsilon * (-2 + sigma)) *
                Kakeya.realRpowENN delta powerInputLoss *
                Kakeya.realRpowENN delta 2 := by
          repeat' rw [← realRpowENN_add hdelta]
          congr 1
          ring
        calc
          (wz2PaperPureRefinementFraction delta logExponent *
                Kakeya.realRpowENN delta (epsilon * powerLoss)) *
              (Kakeya.realRpowENN delta
                  (powerInputLoss - targetLoss + 2) *
                sqrtData.cfg.family.enncard *
                Kakeya.realRpowENN delta
                  (epsilon * (sigma - powerLoss - 2))) =
              wz2PaperPureRefinementFraction delta logExponent *
                sqrtData.cfg.family.enncard *
                (Kakeya.realRpowENN delta (epsilon * powerLoss) *
                  Kakeya.realRpowENN delta
                    (powerInputLoss - targetLoss + 2) *
                  Kakeya.realRpowENN delta
                    (epsilon * (sigma - powerLoss - 2))) := by ring
          _ = wz2PaperPureRefinementFraction delta logExponent *
                sqrtData.cfg.family.enncard *
                (Kakeya.realRpowENN delta (-targetLoss) *
                  Kakeya.realRpowENN delta (epsilon * (-2 + sigma)) *
                  Kakeya.realRpowENN delta powerInputLoss *
                  Kakeya.realRpowENN delta 2) := by rw [hpowerIdentity]
          _ = (Kakeya.realRpowENN delta (-targetLoss) *
                Kakeya.realRpowENN delta (epsilon * (-2 + sigma))) *
              (wz2PaperPureRefinementFraction delta logExponent *
                (Kakeya.realRpowENN delta powerInputLoss *
                  sqrtData.cfg.family.enncard *
                  Kakeya.realRpowENN delta 2)) := by ring
      _ ≤ coverBudget *
          ((fixed.balanced.activeCells.card : ENNReal) *
            fixed.cellIndexedMassRatio *
            fixed.cellIndexedMassBase) := by
        gcongr
  have hselectionScalar :
      targetMass *
          ((fixed.balanced.activeCells.card : ENNReal) *
            fixed.cellIndexedMassRatio) ≤
        (coverBudget / 16) *
          ((fixed.balanced.activeCells.card : ENNReal) *
            fixed.cellIndexedMassRatio *
            fixed.cellIndexedMassBase) := by
    have hdiv :
        targetMass *
            ((fixed.balanced.activeCells.card : ENNReal) *
              fixed.cellIndexedMassRatio) ≤
          (coverBudget *
            ((fixed.balanced.activeCells.card : ENNReal) *
              fixed.cellIndexedMassRatio *
              fixed.cellIndexedMassBase)) / 16 := by
      apply (ENNReal.le_div_iff_mul_le
        (Or.inl (by norm_num : (16 : ENNReal) ≠ 0))
        (Or.inl (by norm_num : (16 : ENNReal) ≠ ⊤))).2
      simpa only [mul_comm] using hselectionScaled
    calc
      _ ≤ (coverBudget *
          ((fixed.balanced.activeCells.card : ENNReal) *
            fixed.cellIndexedMassRatio *
            fixed.cellIndexedMassBase)) / 16 := hdiv
      _ = (coverBudget / 16) *
          ((fixed.balanced.activeCells.card : ENNReal) *
            fixed.cellIndexedMassRatio *
            fixed.cellIndexedMassBase) := by
        simp only [div_eq_mul_inv]
        calc
          (coverBudget *
                ((fixed.balanced.activeCells.card : ENNReal) *
                  fixed.cellIndexedMassRatio *
                  fixed.cellIndexedMassBase)) * (16 : ENNReal)⁻¹ =
              coverBudget *
                (((fixed.balanced.activeCells.card : ENNReal) *
                  fixed.cellIndexedMassRatio *
                  fixed.cellIndexedMassBase) * (16 : ENNReal)⁻¹) :=
            mul_assoc _ _ _
          _ = coverBudget *
                ((16 : ENNReal)⁻¹ *
                  ((fixed.balanced.activeCells.card : ENNReal) *
                    fixed.cellIndexedMassRatio *
                    fixed.cellIndexedMassBase)) := by
            rw [mul_comm
              ((fixed.balanced.activeCells.card : ENNReal) *
                fixed.cellIndexedMassRatio * fixed.cellIndexedMassBase)]
          _ = (coverBudget * (16 : ENNReal)⁻¹) *
                ((fixed.balanced.activeCells.card : ENNReal) *
                  fixed.cellIndexedMassRatio *
                  fixed.cellIndexedMassBase) :=
            (mul_assoc _ _ _).symm
  have hcoverPowerOne :
      (1 : ENNReal) ≤ Kakeya.realRpowENN rho.1 (-2 + sigma) := by
    rw [Kakeya.realRpowENN, ENNReal.one_le_ofReal]
    have hpow := Real.rpow_le_rpow_of_exponent_ge
      (hdelta.trans_le rho.2.1) rho.2.2
      (show -2 + sigma ≤ (0 : ℝ) by linarith [critical.sigma_lt_one])
    simpa using hpow
  have hcoverSixteen : (16 : ENNReal) ≤ coverBudget := by
    calc
      (16 : ENNReal) ≤ Kakeya.realRpowENN delta (-targetLoss) :=
        hscalars.2.2
      _ ≤ Kakeya.realRpowENN delta (-targetLoss) *
          Kakeya.realRpowENN rho.1 (-2 + sigma) := by
        simpa only [mul_one] using
          mul_le_mul_left' hcoverPowerOne
            (Kakeya.realRpowENN delta (-targetLoss))
      _ = coverBudget := rfl
  have hcoverScalar : (1 : ENNReal) ≤ coverBudget / 16 := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num : (16 : ENNReal) ≠ 0))
      (Or.inl (by norm_num : (16 : ENNReal) ≠ ⊤))).2
    simpa using hcoverSixteen
  rcases fixed.fixed_height_selection_of_scalars
      (source := sqrtData.cfg.family)
      sqrtData.cfg zeroData.zeroExtension rfl
      (hdeltaSmall.trans (by norm_num : (1 / 24 : ℝ) ≤ 1 / 12))
      (by linarith [critical.sigma_lt_one])
      hpowerInputPower hpowerTarget targetMass coverBudget rfl rfl
      hglobalScalar hactive hselectionScalar hcoverScalar with
    ⟨heightSelection⟩
  let outputCfg := zeroData.configuration
  have hcompatibility : PureWZ2FrameNormalCompatibility outputCfg :=
    zeroData.configuration_frameNormalCompatibility
      sqrtData.frameNormalCompatibility
  let globalizedSlopeData :
      PureWZ2GlobalizedPaperSlopeData
        outputCfg.globalGrains.slope :=
    Classical.choice outputCfg.globalGrains.globalizedSlope
  have houtputFamily : outputCfg.family = sqrtData.sourceCfg.family := by
    have hpowerFamily : outputCfg.family = sqrtData.cfg.family :=
      zeroData.configuration_family
    have hsqrtFamily : sqrtData.cfg.family = sqrtData.sourceCfg.family := by
      rw [sqrtData.cfg_eq]
      exact sqrtData.zeroData.configuration_family
    exact hpowerFamily.trans hsqrtFamily
  have hpoint : ∀ point,
      (heightSelection.scaleData.slabShading.pointMultiplicity point :
          ENNReal) ≤
        (Kakeya.realRpowENN delta
            (2 - sigma - stickyLoss) *
          Kakeya.realRpowENN rho.1 (-stickyLoss)) *
            outputCfg.family.enncard := by
    intro point
    have hslabPower :
        heightSelection.scaleData.slabShading.pointMultiplicity point ≤
          outputCfg.shading.pointMultiplicity point :=
      heightSelection.scaleData.pointMultiplicity_le_source point
    have hpowerSqrt :
        outputCfg.shading.pointMultiplicity point ≤
          sqrtData.cfg.shading.pointMultiplicity point :=
      zeroData.configuration_pointMultiplicity_le_source point
    have hsqrtSource :
        sqrtData.cfg.shading.pointMultiplicity point ≤
          sqrtData.sourceCfg.shading.pointMultiplicity point := by
      rw [sqrtData.cfg_eq]
      exact sqrtData.zeroData.configuration_pointMultiplicity_le_source point
    have hnat :
        heightSelection.scaleData.slabShading.pointMultiplicity point ≤
          sqrtData.sourceCfg.shading.pointMultiplicity point :=
      hslabPower.trans (hpowerSqrt.trans hsqrtSource)
    calc
      (heightSelection.scaleData.slabShading.pointMultiplicity point :
          ENNReal) ≤
          (sqrtData.sourceCfg.shading.pointMultiplicity point : ENNReal) := by
        exact_mod_cast hnat
      _ ≤
          (Kakeya.realRpowENN delta
              (2 - sigma - stickyLoss) *
            Kakeya.realRpowENN (Real.rpow delta epsilon)
              (-stickyLoss)) *
              sqrtData.sourceCfg.family.enncard :=
        hsqrtSourceCap point
      _ =
          (Kakeya.realRpowENN delta
              (2 - sigma - stickyLoss) *
            Kakeya.realRpowENN rho.1 (-stickyLoss)) *
              outputCfg.family.enncard := by
        rw [show rho.1 = Real.rpow delta epsilon by rfl, houtputFamily]
  exact ⟨delta, hdelta, hdeltaBound', ⟨{
    eta := eta
    eta_pos := heta
    eta_budget := hetaBudget
    targetLoss := targetLoss
    targetLoss_eq := rfl
    stickyLoss := stickyLoss
    stickyLoss_eq := rfl
    sourceLoss := powerInputLoss
    sourceLoss_pos := hpowerInput
    sourceLoss_le_stickyLoss := hpowerInputSticky
    cfg := outputCfg
    cfg_bounded_base := outputCfg.bounded_base
    rho := rho
    rho_eq_power := rfl
    globalSlope := globalizedSlopeData.slope
    globalSlope_eq_on := globalizedSlopeData.eq_on
    globalSlope_normalized := globalizedSlopeData.normalized
    scaleData := heightSelection.scaleData
    frameNormalCompatibility := hcompatibility
    faithful_overload :=
      overload delta hdelta hdeltaOverload outputCfg
    pointMultiplicity_upper := hpoint
  }, rfl⟩⟩

end Kakeya.Assouad

end
