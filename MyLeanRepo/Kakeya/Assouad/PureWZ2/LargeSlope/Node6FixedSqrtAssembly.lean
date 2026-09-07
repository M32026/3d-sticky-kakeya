import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4DirectNode6FixedScaleCertified
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Node6FixedFrameNormalCompatibility
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6Refinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6Absorption

/-!
# Certified fixed square-root assembly for Node 6

This is the fixed-output replacement for the historical Section-6
square-root assembly.  It applies the certified Proposition 6.2 provider to
the same C2 configuration produced by Node 5, retains the certified
balanced-cell floor, zero-extends that exact fixed output, and proves the
frame-normal compatibility used at every later power scale.

The only loss between the fixed output and the final configuration is a
strict scalar gap used to absorb the literal refinement fraction.  No
incidence-mass field from the retired cover adapter is used.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- The synchronized certified square-root output and its same-family
frame-normal-compatible C2 configuration. -/
structure PureWZ2Node6FixedSqrtAssembly
    (sigma slabLoss delta : ℝ) where
  sourceLoss : ℝ
  fixedLoss : ℝ
  sourceLoss_pos : 0 < sourceLoss
  sourceLoss_le_fixedLoss : sourceLoss ≤ fixedLoss
  fixedLoss_pos : 0 < fixedLoss
  fixedLoss_le_slabLoss : fixedLoss ≤ slabLoss
  logExponent : ℕ
  sourceCfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta
  rho : WZ2PaperRequestedScale delta
  rho_eq_sqrt : rho.1 = Real.sqrt delta
  certified : PureWZ2Node6FixedScaleCriticalOutput
    (sigma := sigma) (outputLoss := fixedLoss)
    sourceCfg.shading rho logExponent
  zeroData : PureWZ2Node6FixedC2ZeroExtensionData
    (targetLoss := slabLoss) sourceCfg certified.fixed
  cfg : PureWZ2C2GrainConfiguration sigma slabLoss delta
  cfg_eq : cfg = zeroData.configuration
  frameNormalCompatibility : PureWZ2FrameNormalCompatibility cfg

private theorem node6_fixed_two_c_le_three_delta_power
    {delta loss localEta : ℝ}
    (hdelta : 0 < delta)
    (hconstant : 2 * Kakeya.realRpowENN 3 localEta ≤
      Kakeya.realRpowENN delta (-(localEta - loss))) :
    2 * Kakeya.realRpowENN delta (-loss) ≤
      Kakeya.realRpowENN (3 * delta) (-localEta) := by
  rw [realRpowENN_mul (by norm_num) hdelta]
  have hthreeCancel : Kakeya.realRpowENN 3 localEta *
      Kakeya.realRpowENN 3 (-localEta) = 1 := by
    rw [← realRpowENN_add (by norm_num : (0 : ℝ) < 3)]
    simp [Kakeya.realRpowENN]
  have hdeltaSplit : Kakeya.realRpowENN delta (-(localEta - loss)) *
      Kakeya.realRpowENN delta (-loss) =
        Kakeya.realRpowENN delta (-localEta) := by
    rw [← realRpowENN_add hdelta]
    congr 1
    ring
  calc
    2 * Kakeya.realRpowENN delta (-loss) =
        (2 * Kakeya.realRpowENN 3 localEta) *
          (Kakeya.realRpowENN 3 (-localEta) *
            Kakeya.realRpowENN delta (-loss)) := by
      rw [show (2 * Kakeya.realRpowENN 3 localEta) *
            (Kakeya.realRpowENN 3 (-localEta) *
              Kakeya.realRpowENN delta (-loss)) =
          2 * (Kakeya.realRpowENN 3 localEta *
            Kakeya.realRpowENN 3 (-localEta)) *
              Kakeya.realRpowENN delta (-loss) by ring,
        hthreeCancel]
      simp
    _ ≤ Kakeya.realRpowENN delta (-(localEta - loss)) *
          (Kakeya.realRpowENN 3 (-localEta) *
            Kakeya.realRpowENN delta (-loss)) :=
      mul_le_mul_right' hconstant _
    _ = Kakeya.realRpowENN 3 (-localEta) *
        Kakeya.realRpowENN delta (-localEta) := by
      rw [← hdeltaSplit]
      ring

private theorem node6_fixed_three_delta_planar_small
    {delta localEta : ℝ}
    (hdelta : 0 < delta) (hlocalEta : 0 < localEta)
    (hlocalEtaOne : localEta ≤ 1)
    (hsmall : Real.rpow delta localEta ≤ 1 / 96) :
    32 * Real.rpow (3 * delta) localEta ≤ 1 := by
  rw [show Real.rpow (3 * delta) localEta =
      Real.rpow 3 localEta * Real.rpow delta localEta by
    exact Real.mul_rpow (by norm_num) hdelta.le]
  have hthree : Real.rpow 3 localEta ≤ 3 := by
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      hlocalEtaOne).trans_eq (Real.rpow_one 3)
  calc
    32 * (Real.rpow 3 localEta * Real.rpow delta localEta) ≤
        32 * (3 * (1 / 96 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hthree hsmall (Real.rpow_nonneg hdelta.le _)
          (by norm_num)) (by norm_num)
    _ = 1 := by norm_num

private theorem node6_fixed_twenty_sqrt_three_delta_le_one
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (htiny : delta ≤ 1 / 1000000000000) :
    20 * Real.sqrt (3 * delta) ≤ 1 := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hsqrtThree : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sqrt_nonneg 3,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hsqrtDeltaSq : Real.sqrt delta ^ 2 ≤ (1 / 1000 : ℝ) ^ 2 := by
    rw [Real.sq_sqrt hdelta]
    exact htiny.trans (by norm_num)
  have hsqrtDelta : Real.sqrt delta ≤ 1 / 1000 :=
    (sq_le_sq₀ (Real.sqrt_nonneg delta) (by norm_num)).mp hsqrtDeltaSq
  calc
    20 * (Real.sqrt 3 * Real.sqrt delta) ≤
        20 * (2 * (1 / 1000 : ℝ)) := by gcongr
    _ ≤ 1 := by norm_num

private theorem node6_fixed_three_delta_absorb
    {delta sigma localEta : ℝ}
    (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hlocalEta : 0 < localEta)
    (heighth : 8 * localEta < sigma)
    (hsmall : Real.rpow delta (1 / 2 - 4 * localEta / sigma) ≤
      1 / 28) :
    Real.rpow (3 * delta) (1 - 4 * localEta / sigma) ≤
      Real.sqrt (3 * delta) / 14 := by
  have hmulPower : Real.rpow (3 * delta)
      (1 - 4 * localEta / sigma) =
        Real.rpow 3 (1 - 4 * localEta / sigma) *
          Real.rpow delta (1 - 4 * localEta / sigma) :=
    Real.mul_rpow (by norm_num) hdelta.le
  have hsqrtMul : Real.sqrt (3 * delta) =
      Real.sqrt 3 * Real.sqrt delta :=
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3) delta
  have hquotNonneg : 0 ≤ 4 * localEta / sigma :=
    div_nonneg (mul_nonneg (by norm_num) hlocalEta.le) hsigma.le
  have hthreePower : Real.rpow 3 (1 - 4 * localEta / sigma) ≤ 3 :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (sub_le_self 1 hquotNonneg)).trans_eq (Real.rpow_one 3)
  have hdeltaSplit : Real.rpow delta (1 - 4 * localEta / sigma) =
      Real.sqrt delta *
        Real.rpow delta (1 / 2 - 4 * localEta / sigma) := by
    calc
      Real.rpow delta (1 - 4 * localEta / sigma) =
          Real.rpow delta
            ((1 / 2 : ℝ) + (1 / 2 - 4 * localEta / sigma)) := by
        congr 1
        ring
      _ = Real.rpow delta (1 / 2 : ℝ) *
          Real.rpow delta (1 / 2 - 4 * localEta / sigma) :=
        Real.rpow_add hdelta _ _
      _ = Real.sqrt delta *
          Real.rpow delta (1 / 2 - 4 * localEta / sigma) := by
        simp [Real.sqrt_eq_rpow]
  have hsqrtThree : (3 / 2 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg 3,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [hmulPower, hdeltaSplit, hsqrtMul]
  have hproduct : Real.rpow 3 (1 - 4 * localEta / sigma) *
      Real.rpow delta (1 / 2 - 4 * localEta / sigma) ≤
        3 * (1 / 28 : ℝ) :=
    mul_le_mul hthreePower hsmall
      (Real.rpow_nonneg hdelta.le _) (by norm_num)
  have hsqrtNonneg := Real.sqrt_nonneg delta
  calc
    Real.rpow 3 (1 - 4 * localEta / sigma) *
        (Real.sqrt delta *
          Real.rpow delta (1 / 2 - 4 * localEta / sigma)) =
      Real.sqrt delta *
        (Real.rpow 3 (1 - 4 * localEta / sigma) *
          Real.rpow delta (1 / 2 - 4 * localEta / sigma)) := by ring
    _ ≤ Real.sqrt delta * (3 * (1 / 28 : ℝ)) := by gcongr
    _ = 3 * (Real.sqrt delta / 28) := by ring
    _ ≤ Real.sqrt 3 * Real.sqrt delta / 14 := by nlinarith

/-- Produce certified square-root data from an arbitrary dependent source
producer, retaining a caller-specified property of that exact source.  This
is the compositional form used when an earlier Proposition-6.2 refinement
has already installed a global multiplicity cap. -/
theorem pureWZ2_node6_fixed_sqrt_assembly_with_source_property
    (sigma : ℝ)
    {P : ∀ {sourceLoss delta : ℝ},
      PureWZ2C2GrainConfiguration sigma sourceLoss delta → Prop}
    (sourceProvider : ∀ sourceLoss deltaBound : ℝ,
      0 < sourceLoss → 0 < deltaBound →
        ∃ delta : ℝ, 0 < delta ∧ delta ≤ deltaBound ∧
          ∃ cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta,
            P cfg)
    {logExponent : ℕ}
    (certifiedProvider : PureWZ2Node6FixedScaleCriticalAt logExponent)
    (critical : PureWZ2CriticalPackage sigma)
    (slabLoss deltaBound : ℝ)
    (hslabLoss : 0 < slabLoss)
    (hslabLossHalf : slabLoss ≤ 1 / 2)
    (hslabLossSigma : 16 * slabLoss < sigma)
    (hdeltaBound : 0 < deltaBound) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ deltaBound ∧
      ∃ data : PureWZ2Node6FixedSqrtAssembly sigma slabLoss delta,
        P data.sourceCfg := by
  let fixedLoss : ℝ :=
    min (slabLoss / 2) (min (sigma / 32) (1 / 4))
  have hfixedLoss : 0 < fixedLoss := by
    dsimp only [fixedLoss]
    exact lt_min (by positivity)
      (lt_min (by positivity [critical.sigma_pos]) (by norm_num))
  have hfixedLossSlabHalf : fixedLoss ≤ slabLoss / 2 := by
    exact min_le_left _ _
  have hfixedLossSigma : fixedLoss ≤ sigma / 32 := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hfixedLossQuarter : fixedLoss ≤ 1 / 4 := by
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hfixedLossOne : fixedLoss ≤ 1 := by linarith
  have hfixedLossHalf : fixedLoss ≤ 1 / 2 := by linarith
  have hfixedLossSlab : fixedLoss < slabLoss := by linarith
  let localEta : ℝ := 2 * slabLoss
  have hlocalEta : 0 < localEta := by
    dsimp only [localEta]
    positivity
  have hlocalEtaOne : localEta ≤ 1 := by
    dsimp only [localEta]
    linarith [hslabLossHalf]
  have hlocalEtaSlab : 0 < localEta - slabLoss := by
    dsimp only [localEta]
    linarith
  have hlocalEtaSigma : 4 * localEta < sigma := by
    dsimp only [localEta]
    linarith [hslabLossSigma]
  have heightLocalEtaSigma : 8 * localEta < sigma := by
    dsimp only [localEta]
    nlinarith [hslabLossSigma]
  have habsorbExponent : 0 < 1 / 2 - 4 * localEta / sigma := by
    rw [sub_pos, div_lt_iff₀ critical.sigma_pos]
    linarith [heightLocalEtaSigma]
  rcases certifiedProvider sigma critical fixedLoss hfixedLoss hfixedLossOne with
    ⟨sourceLoss, providerScale, hsourceLoss, hsourceFixed,
      hproviderScale, hproviderScaleOne, provide⟩
  have hsourceSlab : sourceLoss < slabLoss :=
    lt_of_le_of_lt hsourceFixed hfixedLossSlab
  rcases exists_delta_pure_refinement_fraction_absorbs
      sourceLoss slabLoss hsourceSlab logExponent with
    ⟨densityScale, hdensityScale, hdensityScaleOne, densityAbsorb⟩
  rcases exists_delta_constant_mul_power_le_power
      (Kakeya.realRpowENN 3
        (3 / 2 + sigma / 2 + localEta))
      (by simp [Kakeya.realRpowENN])
      (3 / 2 + sigma / 2 + fixedLoss)
      (3 / 2 + sigma / 2 + localEta)
      (by dsimp only [localEta]; linarith) with
    ⟨sourceScale, hsourceScale, hsourceScaleOne, sourceAbsorb⟩
  rcases exists_delta_realRpowENN_bound
      (2 * Kakeya.realRpowENN 3 localEta)
      (ENNReal.mul_ne_top (by norm_num)
        (by simp [Kakeya.realRpowENN]))
      hlocalEtaSlab with
    ⟨twoScale, htwoScale, htwoScaleOne, twoAbsorb⟩
  rcases exists_delta_rpow_le_single localEta (1 / 96) hlocalEta
      (by norm_num) (by norm_num) with
    ⟨planarScale, hplanarScale, hplanarScaleOne, planarAbsorb⟩
  rcases exists_delta_rpow_le_single
      (1 / 2 - 4 * localEta / sigma) (1 / 28)
      habsorbExponent (by norm_num) (by norm_num) with
    ⟨normalScale, hnormalScale, hnormalScaleOne, normalAbsorb⟩
  let inputScale : ℝ :=
    min deltaBound
      (min providerScale
        (min densityScale
          (min sourceScale
            (min twoScale
              (min planarScale
                (min normalScale (1 / 1000000000000)))))))
  have hinputScale : 0 < inputScale := by
    dsimp only [inputScale]
    positivity
  rcases sourceProvider sourceLoss inputScale hsourceLoss hinputScale with
    ⟨delta, hdelta, hdeltaInput, sourceCfg, hsourceProperty⟩
  have hdeltaBound' : delta ≤ deltaBound :=
    hdeltaInput.trans (by simp [inputScale])
  have hdeltaProvider : delta ≤ providerScale :=
    hdeltaInput.trans (by simp [inputScale])
  have hdeltaDensity : delta ≤ densityScale :=
    hdeltaInput.trans (by simp [inputScale])
  have hdeltaSource : delta ≤ sourceScale :=
    hdeltaInput.trans (by simp [inputScale])
  have hdeltaTwo : delta ≤ twoScale :=
    hdeltaInput.trans (by simp [inputScale])
  have hdeltaPlanar : delta ≤ planarScale :=
    hdeltaInput.trans (by simp [inputScale])
  have hdeltaNormal : delta ≤ normalScale :=
    hdeltaInput.trans (by simp [inputScale])
  have hdeltaTiny : delta ≤ 1 / 1000000000000 :=
    hdeltaInput.trans (by simp [inputScale])
  have hdeltaOne : delta ≤ 1 :=
    hdeltaProvider.trans hproviderScaleOne
  let rho : WZ2PaperRequestedScale delta :=
    pureWZ2SqrtRequestedScale hdelta hdeltaOne
  have hwindow := pureWZ2_sqrt_scale_window
    hdelta hdeltaOne hfixedLoss.le hfixedLossHalf
  rcases provide delta hdelta hdeltaProvider sourceCfg rho
      hwindow.1 hwindow.2 with
    ⟨certified⟩
  have hdensity := densityAbsorb hdelta hdeltaDensity
  rcases certified.fixed.zeroExtendC2 sourceCfg hslabLoss.le
      hsourceSlab.le hfixedLossSlab.le hdensity with
    ⟨zeroData⟩
  have hsourceFloor :
      Kakeya.realRpowENN (3 * delta)
          (3 / 2 + sigma / 2 + localEta) ≤
        certified.fixed.balanced.cellMass := by
    rw [realRpowENN_mul (by norm_num) hdelta]
    exact (sourceAbsorb hdelta hdeltaSource).trans
      (certified.balanced_cellMass_critical_lower_at_sqrt rfl)
  have hTwoCOne : 1 ≤
      2 * Kakeya.realRpowENN delta (-slabLoss) := by
    have hone : Kakeya.realRpowENN delta 0 ≤
        Kakeya.realRpowENN delta (-slabLoss) :=
      realRpowENN_antitone hdelta hdeltaOne (by linarith)
    calc
      1 = Kakeya.realRpowENN delta 0 := by simp [Kakeya.realRpowENN]
      _ ≤ Kakeya.realRpowENN delta (-slabLoss) := hone
      _ ≤ 2 * Kakeya.realRpowENN delta (-slabLoss) := by
        simpa using mul_le_mul_right' (by norm_num : (1 : ENNReal) ≤ 2)
          (Kakeya.realRpowENN delta (-slabLoss))
  have hTwoCPower :
      2 * Kakeya.realRpowENN delta (-slabLoss) ≤
        Kakeya.realRpowENN (3 * delta) (-localEta) :=
    node6_fixed_two_c_le_three_delta_power hdelta
      (twoAbsorb delta hdelta hdeltaTwo)
  have hPlanarSmall : 32 * Real.rpow (3 * delta) localEta ≤ 1 :=
    node6_fixed_three_delta_planar_small hdelta hlocalEta hlocalEtaOne
      (planarAbsorb delta hdelta hdeltaPlanar)
  have hrootSmall20 : 20 * Real.sqrt (3 * delta) ≤ 1 :=
    node6_fixed_twenty_sqrt_three_delta_le_one hdelta.le hdeltaTiny
  have habsorb : Real.rpow (3 * delta)
        (1 - 4 * localEta / sigma) ≤ Real.sqrt (3 * delta) / 14 :=
    node6_fixed_three_delta_absorb hdelta critical.sigma_pos hlocalEta
      heightLocalEtaSigma (normalAbsorb delta hdelta hdeltaNormal)
  have hcompatibility :
      PureWZ2FrameNormalCompatibility
        (zeroData.configuration (targetLoss := slabLoss)) :=
    certified.fixed.frameNormalCompatibility zeroData rfl hdeltaTiny
      hsourceFloor critical.sigma_pos critical.sigma_lt_one
      hlocalEta hlocalEtaSigma hTwoCOne hTwoCPower hPlanarSmall
      hrootSmall20 habsorb
  let result : PureWZ2Node6FixedSqrtAssembly sigma slabLoss delta := {
    sourceLoss := sourceLoss
    fixedLoss := fixedLoss
    sourceLoss_pos := hsourceLoss
    sourceLoss_le_fixedLoss := hsourceFixed
    fixedLoss_pos := hfixedLoss
    fixedLoss_le_slabLoss := hfixedLossSlab.le
    logExponent := logExponent
    sourceCfg := sourceCfg
    rho := rho
    rho_eq_sqrt := rfl
    certified := certified
    zeroData := zeroData
    cfg := zeroData.configuration
    cfg_eq := rfl
    frameNormalCompatibility := hcompatibility
  }
  exact ⟨delta, hdelta, hdeltaBound', result, hsourceProperty⟩

/-- Produce arbitrarily small certified square-root data with a fixed
frame-normal-compatible output configuration. -/
theorem pureWZ2_node6_fixed_sqrt_assembly
    (hc2grains : PureWZ2C2GrainsFromCriticalStatement)
    {logExponent : ℕ}
    (certifiedProvider : PureWZ2Node6FixedScaleCriticalAt logExponent)
    (sigma : ℝ) (critical : PureWZ2CriticalPackage sigma)
    (slabLoss deltaBound : ℝ)
    (hslabLoss : 0 < slabLoss)
    (hslabLossHalf : slabLoss ≤ 1 / 2)
    (hslabLossSigma : 16 * slabLoss < sigma)
    (hdeltaBound : 0 < deltaBound) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ deltaBound ∧
      Nonempty (PureWZ2Node6FixedSqrtAssembly sigma slabLoss delta) := by
  let sourceProvider : ∀ sourceLoss deltaBound : ℝ,
      0 < sourceLoss → 0 < deltaBound →
        ∃ delta : ℝ, 0 < delta ∧ delta ≤ deltaBound ∧
          ∃ _cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta, True := by
    intro sourceLoss deltaBound hsourceLoss hdeltaBound
    rcases hc2grains sigma critical sourceLoss deltaBound
        hsourceLoss hdeltaBound with
      ⟨delta, hdelta, hdeltaLe, ⟨cfg⟩⟩
    exact ⟨delta, hdelta, hdeltaLe, cfg, trivial⟩
  rcases pureWZ2_node6_fixed_sqrt_assembly_with_source_property
      (P := fun _ => True) sigma sourceProvider certifiedProvider critical
      slabLoss deltaBound hslabLoss hslabLossHalf hslabLossSigma
      hdeltaBound with
    ⟨delta, hdelta, hdeltaLe, data, _⟩
  exact ⟨delta, hdelta, hdeltaLe, ⟨data⟩⟩

end Kakeya.Assouad

end
