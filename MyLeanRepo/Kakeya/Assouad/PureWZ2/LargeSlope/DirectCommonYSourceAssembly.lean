import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ConfigurationWeakening
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectSection6SourceInterface
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FixedShearChartSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HalfOffsetHorizontalSource
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.MassPopularSubband
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CoupledIsotropicSlope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Node6FixedLemma31ScaleAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6Lemma31Uniform

/-!
# Common-y-aware source assembly for the direct Proposition 6.5 route

The direct affine backend needs a mass-popular interval, while the local-grain
argument needs the whole-label common-y provenance chosen before that
interval.  This file packages both on one source.  The quantitative loss is
weakened to the honest common-y band loss; no stronger mass estimate is
silently assigned to the restricted shading.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- The direct source package together with the common-y data from which its
mass-popular interval was selected. -/
structure PureWZ2DirectCommonYSourceAssembly
    (logExponent : ℕ)
    (sigma epsilon delta : ℝ) where
  lemma31 : PureWZ2Lemma31DerivativeAssembly sigma epsilon delta
  lemma31_eta_eq : lemma31.eta = epsilon * sigma ^ 2 / 2000
  commonBand : PureWZ2CoupledCommonYDerivativeBandData lemma31
  subband : PureWZ2MassPopularSubbandData commonBand.band
  /-- The direct pipeline after restricting to one of the two fixed shear
  charts.  The source shading and both grain records are the selected records,
  and the actual affine shear is the same selected constant. -/
  halfOffsetAssembly : PureWZ2DirectSection6SourceAssembly
    logExponent sigma epsilon delta
  halfOffsetAssembly_technicalLoss :
    halfOffsetAssembly.technicalLoss = commonBand.band.massLoss + epsilon / 2
  /-- The requested scale retained by the half-offset assembly is the
  hundredth derivative-band width, hence `delta ^ epsilon / 50`.  This
  provenance is needed by the final source-to-target power absorption. -/
  halfOffsetAssembly_rho_eq_power_div :
    halfOffsetAssembly.rho.1 = Real.rpow delta epsilon / 50
  /-- The half-offset replacement changes the constant shear and the public
  intercept, but not the ambient Node-5 slope used in the exact formula. -/
  halfOffsetAssembly_globalSlope :
    halfOffsetAssembly.globalSlope = commonBand.band.lemma31.data.globalSlope
  halfOffsetAssembly_cfg_cubical :
    WZ1PaperIsCubicalShading halfOffsetAssembly.cfg.shading
  /-- The half-offset source shading is still the selected hundredth-band
  subshading of the ambient configuration.  Finite-slice arguments need this
  literal carrier inclusion in addition to cubicality of the ambient shading. -/
  halfOffsetAssembly_source_subconfiguration : ∀ index,
    halfOffsetAssembly.horizontalSource.sourceShading.carrier index ⊆
      halfOffsetAssembly.cfg.shading.carrier index
  /-- The selected derivative interval and scale are unchanged by the
  half-offset replacement. -/
  halfOffsetAssembly_source_coordinates :
    halfOffsetAssembly.horizontalSource.c = subband.left ∧
      halfOffsetAssembly.horizontalSource.d = subband.right ∧
      halfOffsetAssembly.horizontalSource.m =
        (9 : ℝ) / 10 * commonBand.band.slopeScale
  /-- The geometry map is the selected fixed shear on the whole source
  interval; it is not inferred from a midpoint half-offset. -/
  halfOffsetAssembly_geometry_fixedShear : ∀ z,
    halfOffsetAssembly.horizontalSource.geometrySlope z =
      PureWZ2HalfOffsetHorizontalSourceData.offset
        halfOffsetAssembly.horizontalSource
  halfOffsetAssembly_compatibility :
    PureWZ2HalfOffsetHorizontalSourceData.FixedShearChart
      halfOffsetAssembly.horizontalSource

/-- The literal common-y mass loss contains the original target loss and the
fixed positive loss paid by the band selection, so it is at least epsilon.
This lower bound lets all later schedule depths be fixed from epsilon before
the runtime source is chosen. -/
theorem PureWZ2DirectCommonYSourceAssembly.epsilon_le_halfOffsetAssembly_technicalLoss
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta) :
    epsilon ≤ commonSource.halfOffsetAssembly.technicalLoss := by
  rw [show commonSource.halfOffsetAssembly.technicalLoss =
      commonSource.commonBand.band.massLoss + epsilon / 2 by
    exact commonSource.halfOffsetAssembly_technicalLoss,
    commonSource.commonBand.band_massLoss,
    commonSource.commonBand.common_loss]
  have htarget : 0 ≤ commonSource.lemma31.data.targetLoss := by
    rw [commonSource.lemma31.data.targetLoss_eq]
    positivity [commonSource.lemma31.data.eta_pos]
  nlinarith [htarget, commonSource.lemma31.eta_pos,
    commonSource.lemma31.epsilon_pos]

theorem PureWZ2DirectCommonYSourceAssembly.halfOffset_projectiveNormal_lipschitz
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta) :
    LipschitzWith 10100
      (fun point => pureWZ2OffsetShearProjectiveNormal
        (PureWZ2HalfOffsetHorizontalSourceData.offset
          assembly.halfOffsetAssembly.horizontalSource)
        (assembly.halfOffsetAssembly.horizontalSource.sourceLocalGrains.planeMap
          point)) := by
  exact PureWZ2HalfOffsetHorizontalSourceData.projectiveNormal_lipschitz_restrict
    assembly.halfOffsetAssembly.horizontalSource
      assembly.halfOffsetAssembly_compatibility

theorem PureWZ2DirectCommonYSourceAssembly.halfOffset_projectiveNormal_coord_one
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)
    (point : {point : Point3 //
      point ∈ assembly.halfOffsetAssembly.horizontalSource.sourceShading.union}) :
    pureWZ2OffsetShearProjectiveNormal
        (PureWZ2HalfOffsetHorizontalSourceData.offset
          assembly.halfOffsetAssembly.horizontalSource)
        (assembly.halfOffsetAssembly.horizontalSource.sourceLocalGrains.planeMap
          point) 1 = 1 := by
  exact PureWZ2HalfOffsetHorizontalSourceData.projectiveNormal_coord_one_restrict
    assembly.halfOffsetAssembly.horizontalSource
      assembly.halfOffsetAssembly_compatibility point

/-- Build the direct backend source from the paper-order chain
Lemma 31 -> common-y whole-label refinement -> derivative band ->
mass-popular hundredth. -/
theorem pureWZ2_direct_commonY_source_assembly
    (hc2grains : PureWZ2C2GrainsFromCriticalStatement)
    {logExponent : ℕ}
    (certifiedProvider : PureWZ2Node6FixedScaleCriticalAt logExponent)
    (sigma : ℝ) (critical : PureWZ2CriticalPackage sigma)
    (epsilon deltaBound : ℝ)
    (hepsilon : 0 < epsilon) (hepsilonSixtyFourth : epsilon ≤ 1 / 64)
    (hdeltaBound : 0 < deltaBound) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ deltaBound ∧
      Nonempty (PureWZ2DirectCommonYSourceAssembly
        logExponent sigma epsilon delta) := by
  rcases exists_delta_constant_mul_power_le_power (2 : ENNReal) (by norm_num)
      0 (epsilon / 2) (by linarith) with
    ⟨chartScale, hchartScale, _hchartScaleOne, hchartAbsorption⟩
  let directBound := min deltaBound chartScale
  have hdirectBound : 0 < directBound := by
    exact lt_min hdeltaBound hchartScale
  have fixedScaleProducer : ∀ eta requestedBound : ℝ,
      0 < eta → 1000 * eta ≤ epsilon * sigma ^ 2 →
      0 < requestedBound →
        ∃ delta : ℝ, 0 < delta ∧ delta ≤ requestedBound ∧
          ∃ data : PureWZ2Lemma31ScaleAssembly sigma epsilon delta,
            data.eta = eta := by
    intro eta requestedBound heta
    intro hbudget hrequestedBound
    exact pureWZ2_node6_fixed_lemma31_scale_assembly_with_eta
      hc2grains certifiedProvider sigma critical epsilon eta
      requestedBound hepsilon
      (hepsilonSixtyFourth.trans (by norm_num)) heta hbudget
      hrequestedBound
  rcases pureWZ2_lemma31_derivative_assembly_of_scale_producer
      sigma epsilon fixedScaleProducer
      critical directBound hepsilon
      (hepsilonSixtyFourth.trans (by norm_num)) hdirectBound with
    ⟨delta, hdelta, hdeltaBound', lemma31, hlemma31Eta⟩
  have hdeltaOriginalBound : delta ≤ deltaBound :=
    hdeltaBound'.trans (min_le_left _ _)
  have hdeltaChart : delta ≤ chartScale :=
    hdeltaBound'.trans (min_le_right _ _)
  rcases lemma31.toCoupledCommonYDerivativeBand with ⟨commonBand⟩
  rcases commonBand.band.massPopularSubband with ⟨subband⟩
  let directLemma31 := commonBand.band.lemma31
  let directRho : WZ2PaperRequestedScale delta :=
    ⟨commonBand.band.right - commonBand.band.left, by
      have hrhoPos : 0 < directLemma31.data.rho.1 :=
        directLemma31.data.cfg.extremal.delta_pos.trans_le
          directLemma31.data.rho.2.1
      have hwidth : commonBand.band.right - commonBand.band.left =
          directLemma31.data.rho.1 / 50 := commonBand.band.length_eq
      constructor
      · rw [hwidth]
        have hdeltaRho : delta ≤ directLemma31.data.rho.1 ^ 2 :=
          directLemma31.delta_le_rho_sq
        have hrhoTiny : directLemma31.data.rho.1 ≤ 1 / 2500 :=
          directLemma31.rho_tiny.trans (by norm_num)
        have hfactor : 0 ≤ directLemma31.data.rho.1 / 50 -
            directLemma31.data.rho.1 ^ 2 := by
          nlinarith [mul_nonneg hrhoPos.le
            (sub_nonneg.mpr hrhoTiny)]
        linarith
      · rw [hwidth]
        exact (div_le_self hrhoPos.le (by norm_num)).trans
          directLemma31.data.rho.2.2⟩
  have htargetBand : directLemma31.data.targetLoss ≤
      commonBand.band.massLoss := by
    have htarget : directLemma31.data.targetLoss =
        lemma31.data.targetLoss := by
      simp [directLemma31, commonBand.band_lemma31]
    calc
      directLemma31.data.targetLoss = lemma31.data.targetLoss := htarget
      _ ≤ lemma31.data.targetLoss + 4 * commonBand.common.badYLoss + epsilon := by
        nlinarith [commonBand.common.badYLoss_pos, hepsilon]
      _ = commonBand.band.massLoss := commonBand.band_massLoss.symm
  let cfg := directLemma31.data.cfg.mono_loss
    directLemma31.data.cfg.extremal.delta_pos
    directLemma31.data.cfg.extremal.delta_le_one
    (by
      have htarget : directLemma31.data.targetLoss =
          lemma31.data.targetLoss := by
        simp [directLemma31, commonBand.band_lemma31]
      rw [htarget, lemma31.data.targetLoss_eq]
      exact
      (div_pos lemma31.data.eta_pos (by norm_num)).le)
    htargetBand
  have hcfgFamily : cfg.family = directLemma31.data.cfg.family := rfl
  have hcfgSlope : cfg.globalGrains.slope =
      directLemma31.data.cfg.globalGrains.slope := rfl
  have htargetNonneg : 0 ≤ directLemma31.data.targetLoss := by
    have htarget : directLemma31.data.targetLoss =
        lemma31.data.targetLoss := by
      simp [directLemma31, commonBand.band_lemma31]
    rw [htarget, lemma31.data.targetLoss_eq]
    exact (div_pos lemma31.data.eta_pos (by norm_num)).le
  have hbandLossNonneg : 0 ≤ commonBand.band.massLoss :=
    htargetNonneg.trans htargetBand
  have hbandSourceSub : ∀ index, commonBand.band.sourceShading.carrier index ⊆
      cfg.shading.carrier index := by
    intro index
    change commonBand.band.sourceShading.carrier index ⊆
      directLemma31.data.cfg.shading.carrier index
    exact commonBand.band.source_subshading index
  have hconstantOne : 1 ≤
      Kakeya.realRpowENN delta (-commonBand.band.massLoss) := by
    calc
      1 = Kakeya.realRpowENN delta 0 := by
        simp [Kakeya.realRpowENN]
      _ ≤ Kakeya.realRpowENN delta (-commonBand.band.massLoss) :=
        realRpowENN_antitone directLemma31.data.cfg.extremal.delta_pos
          directLemma31.data.cfg.extremal.delta_le_one
          (by linarith [hbandLossNonneg])
  have hconstantTop :
      Kakeya.realRpowENN delta (-commonBand.band.massLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let refinedGlobalGrains : PureWZ2C2GlobalGrainData
      commonBand.band.sourceShading sigma
        (Kakeya.realRpowENN delta (-commonBand.band.massLoss)) :=
    cfg.globalGrains.restrict_same_constant hbandSourceSub
  let refinedLocalGrains : PureWZ2LocalGrainData
      commonBand.band.sourceShading sigma
        (Kakeya.realRpowENN delta (-commonBand.band.massLoss)) :=
    cfg.localGrains.restrict hbandSourceSub
  rcases exists_pureWZ2SubbandExactSlopeFunction subband with
    ⟨exactSlope, exactSlopeNonsingular, exactSlopeFormula⟩
  let shearOffset : ℝ :=
    (commonBand.band.lemma31.data.globalSlope subband.anchor -
      commonBand.frameSlope) /
        ((9 : ℝ) / 10 * commonBand.band.slopeScale *
          (subband.right - subband.left) / 2)
  let exactShearSlope : SlopeFunction := exactSlope.addConstant shearOffset
  have exactShearSlopeNonsingular : exactShearSlope.IsNonsingular :=
    SlopeFunction.addConstant_isNonsingular exactSlopeNonsingular shearOffset
  have hsourceSub : ∀ index, subband.shading.carrier index ⊆
      commonBand.band.sourceShading.carrier index := by
    intro index point hpoint
    rw [subband.carrier_eq] at hpoint
    exact hpoint.1
  let horizontalSource : PureWZ2HorizontalSourceData cfg := {
    c := subband.left
    d := subband.right
    m := (9 : ℝ) / 10 * commonBand.band.slopeScale
    left_mem := directLemma31.data.scaleData.slabLeft_mem.trans
      (commonBand.band.left_mem.trans subband.left_mem)
    ordered := subband.ordered
    right_mem := subband.right_mem.trans <|
      commonBand.band.right_mem.trans
        directLemma31.data.scaleData.slabRight_mem
    source_length := commonBand.band.right - commonBand.band.left
    length_eq := subband.length_eq
    slopeScale_pos := by
      exact mul_pos (by norm_num) commonBand.band.slopeScale_pos
    slopeScale_lower := by
      calc
        commonBand.band.right - commonBand.band.left =
            commonBand.band.lemma31.data.rho.1 / 50 :=
          commonBand.band.length_eq
        _ ≤ commonBand.band.slopeScale / 50 :=
          div_le_div_of_nonneg_right commonBand.band.slopeScale_lower
            (by norm_num)
        _ ≤ (9 : ℝ) / 10 * commonBand.band.slopeScale := by
          nlinarith [commonBand.band.slopeScale_pos]
    slopeScale_le_one := by
      nlinarith [commonBand.band.slopeScale_le_one]
    globalSlope := directLemma31.data.globalSlope
    globalSlope_eq_on := by
      intro z hz
      rw [directLemma31.data.globalSlope_eq_on z hz, hcfgSlope]
    globalSlope_normalized := directLemma31.data.globalSlope_normalized
    derivative_band := fun z hz => by
      have hband := commonBand.band.derivative_band z
        ⟨subband.left_mem.trans hz.1, hz.2.trans subband.right_mem⟩
      have htight := commonBand.band.derivative_tight_upper z
        ⟨subband.left_mem.trans hz.1, hz.2.trans subband.right_mem⟩
      constructor
      · nlinarith [hband.1, commonBand.band.slopeScale_pos]
      · have hrho : commonBand.band.lemma31.data.rho.1 ≤
            commonBand.band.slopeScale :=
          commonBand.band.slopeScale_lower
        have hrhoFiftieth : commonBand.band.lemma31.data.rho.1 / 50 ≤
            commonBand.band.slopeScale / 50 :=
          div_le_div_of_nonneg_right hrho (by norm_num)
        nlinarith [htight]
    sourceShading := subband.shading
    source_in_interval := fun index point hpoint => by
      rw [subband.carrier_eq] at hpoint
      exact hpoint.2
    source_mass_lower := by
      have hbandMass :
          Kakeya.realRpowENN delta (commonBand.band.massLoss + 3) *
              ENNReal.ofReal
                (commonBand.band.right - commonBand.band.left) ≤
            commonBand.band.literalBandShading.mass := by
        rw [commonBand.band.literalBandShading_mass]
        rw [commonBand.band.length_eq, ENNReal.ofReal_div_of_pos
          (by norm_num : (0 : ℝ) < 50), ENNReal.ofReal_ofNat]
        simpa only [div_eq_mul_inv, mul_assoc] using
          commonBand.band.shaded_mass
      calc
        Kakeya.realRpowENN delta (commonBand.band.massLoss + 3) *
              ENNReal.ofReal (subband.right - subband.left) =
            (Kakeya.realRpowENN delta (commonBand.band.massLoss + 3) *
              ENNReal.ofReal
                (commonBand.band.right - commonBand.band.left)) / 100 := by
              rw [subband.length_eq, ENNReal.ofReal_div_of_pos
                (by norm_num : (0 : ℝ) < 100), ENNReal.ofReal_ofNat]
              exact mul_div _ _ _
        _ ≤ commonBand.band.literalBandShading.mass / 100 :=
          ENNReal.div_le_div hbandMass (by norm_num)
        _ ≤ subband.shading.mass := subband.mass_lower
    source_mass_card := by
      have hbandCard : ENNReal.ofReal (Real.pi / 4) *
              Kakeya.realRpowENN delta
                (commonBand.band.massLoss + 2) *
              commonBand.band.lemma31.data.cfg.family.enncard *
              ENNReal.ofReal
                (commonBand.band.right - commonBand.band.left) ≤
            commonBand.band.literalBandShading.mass := by
        rw [commonBand.band.literalBandShading_mass]
        rw [commonBand.band.length_eq, ENNReal.ofReal_div_of_pos
          (by norm_num : (0 : ℝ) < 50), ENNReal.ofReal_ofNat]
        simpa only [div_eq_mul_inv, mul_assoc] using
          commonBand.band.shaded_mass_card
      have hcard : ENNReal.ofReal (Real.pi / 4) *
              Kakeya.realRpowENN delta
                (commonBand.band.massLoss + 2) *
              commonBand.band.lemma31.data.cfg.family.enncard *
              ENNReal.ofReal (subband.right - subband.left) ≤
            subband.shading.mass := by
        calc
          _ =
              (ENNReal.ofReal (Real.pi / 4) *
                  Kakeya.realRpowENN delta
                    (commonBand.band.massLoss + 2) *
                  commonBand.band.lemma31.data.cfg.family.enncard *
                  ENNReal.ofReal
                    (commonBand.band.right - commonBand.band.left)) / 100 := by
                    rw [subband.length_eq,
                      ENNReal.ofReal_div_of_pos
                        (by norm_num : (0 : ℝ) < 100),
                      ENNReal.ofReal_ofNat]
                    exact mul_div _ _ _
          _ ≤ commonBand.band.literalBandShading.mass / 100 :=
            ENNReal.div_le_div hbandCard (by norm_num)
          _ ≤ subband.shading.mass := subband.mass_lower
      change ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta (commonBand.band.massLoss + 2) *
          commonBand.band.lemma31.data.cfg.family.enncard *
          ENNReal.ofReal (subband.right - subband.left) ≤
        subband.shading.mass
      exact hcard
    sourceGlobalGrains :=
      refinedGlobalGrains.restrict_same_constant hsourceSub
    source_global_slope_eq := rfl
    sourceLocalGrains := refinedLocalGrains.restrict hsourceSub
    geometrySlope := {
      toFun := fun _ => commonBand.frameSlope
      contDiff := contDiff_const
    }
    geometrySlope_normalized := by
      intro z _hz
      exact ⟨commonBand.frame_abs, by simp, by simp⟩
    f := exactShearSlope.onUnitInterval
    f_nonsingular := exactShearSlope.nonsingular_onUnitInterval
      exactShearSlopeNonsingular
    f_formula := fun t => by
      change exactShearSlope t.1 = _
      rw [SlopeFunction.addConstant_apply]
      rw [exactSlopeFormula]
      simp only [anisotropicRescaledSlope,
        anisotropicRescaledSlopeWithShear, shearOffset]
      have hsourceHeight :
          subband.left + (subband.right - subband.left) / 2 * (t.1 + 1) ∈
            Set.Icc (-1 : ℝ) 1 := by
        have hsourceBand :
            subband.left + (subband.right - subband.left) / 2 * (t.1 + 1) ∈
              Set.Icc subband.left subband.right := by
          constructor
          · have ht : 0 ≤ t.1 + 1 := by linarith [t.2.1]
            have hwidth : 0 ≤ (subband.right - subband.left) / 2 := by
              linarith [subband.ordered]
            nlinarith
          · have ht : t.1 + 1 ≤ 2 := by linarith [t.2.2]
            have hwidth : 0 ≤ (subband.right - subband.left) / 2 := by
              linarith [subband.ordered]
            nlinarith
        exact ⟨directLemma31.data.scaleData.slabLeft_mem.trans
            (commonBand.band.left_mem.trans <|
              subband.left_mem.trans hsourceBand.1),
          (hsourceBand.2.trans subband.right_mem).trans <|
            commonBand.band.right_mem.trans
              directLemma31.data.scaleData.slabRight_mem⟩
      have hanchorHeight : subband.anchor ∈ Set.Icc (-1 : ℝ) 1 :=
        ⟨directLemma31.data.scaleData.slabLeft_mem.trans
            (commonBand.band.left_mem.trans subband.anchor_mem.1),
          subband.anchor_mem.2.trans <|
            commonBand.band.right_mem.trans
              directLemma31.data.scaleData.slabRight_mem⟩
      have hcenterEq :
          subband.left + (subband.right - subband.left) / 2 =
            subband.anchor := by
        rw [subband.anchor_eq]
        ring
      rw [directLemma31.data.globalSlope_eq_on _ hsourceHeight,
        hcenterEq, directLemma31.data.globalSlope_eq_on _ hanchorHeight]
      ring
  }
  rcases pureWZ2_fixedShear_source_selection horizontalSource
      directLemma31.delta_small with
    ⟨selection⟩
  let technicalLoss := commonBand.band.massLoss + epsilon / 2
  have hbandTechnical : commonBand.band.massLoss ≤ technicalLoss := by
    dsimp only [technicalLoss]
    linarith
  have htechnicalNonneg : 0 ≤ technicalLoss :=
    hbandLossNonneg.trans hbandTechnical
  let outputCfg := cfg.mono_loss
    directLemma31.data.cfg.extremal.delta_pos
    directLemma31.data.cfg.extremal.delta_le_one
    hbandLossNonneg hbandTechnical
  have hconstantLe :
      Kakeya.realRpowENN delta (-commonBand.band.massLoss) ≤
        Kakeya.realRpowENN delta (-technicalLoss) :=
    realRpowENN_antitone directLemma31.data.cfg.extremal.delta_pos
      directLemma31.data.cfg.extremal.delta_le_one (by linarith)
  have htechnicalConstantOne :
      1 ≤ Kakeya.realRpowENN delta (-technicalLoss) := by
    calc
      1 = Kakeya.realRpowENN delta 0 := by simp [Kakeya.realRpowENN]
      _ ≤ Kakeya.realRpowENN delta (-technicalLoss) :=
        realRpowENN_antitone directLemma31.data.cfg.extremal.delta_pos
          directLemma31.data.cfg.extremal.delta_le_one (by linarith)
  have htechnicalConstantTop :
      Kakeya.realRpowENN delta (-technicalLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let selectedGlobalGrains : PureWZ2C2GlobalGrainData
      selection.selectedShading sigma
        (Kakeya.realRpowENN delta (-technicalLoss)) :=
    (horizontalSource.sourceGlobalGrains.restrict_same_constant
      selection.selected_subshading).weaken_constant
        hconstantLe htechnicalConstantOne htechnicalConstantTop
  let selectedLocalGrains : PureWZ2LocalGrainData
      selection.selectedShading sigma
        (Kakeya.realRpowENN delta (-technicalLoss)) :=
    selection.selectedLocalGrains.weaken_constant
      hconstantLe htechnicalConstantTop
  have htwoPower (k : ℝ) :
      (2 : ENNReal) * Kakeya.realRpowENN delta
          (commonBand.band.massLoss + epsilon / 2 + k) ≤
        Kakeya.realRpowENN delta (commonBand.band.massLoss + k) := by
    have hgap :
        (2 : ENNReal) * Kakeya.realRpowENN delta (epsilon / 2) ≤ 1 := by
      simpa [Kakeya.realRpowENN] using
        hchartAbsorption hdelta hdeltaChart
    rw [show commonBand.band.massLoss + epsilon / 2 + k =
          epsilon / 2 + (commonBand.band.massLoss + k) by ring,
        realRpowENN_add hdelta]
    calc
      2 * (Kakeya.realRpowENN delta (epsilon / 2) *
            Kakeya.realRpowENN delta (commonBand.band.massLoss + k)) =
          (2 * Kakeya.realRpowENN delta (epsilon / 2)) *
            Kakeya.realRpowENN delta (commonBand.band.massLoss + k) := by ring
      _ ≤ 1 * Kakeya.realRpowENN delta
            (commonBand.band.massLoss + k) :=
        mul_le_mul_right' hgap _
      _ = Kakeya.realRpowENN delta (commonBand.band.massLoss + k) := one_mul _
  have hhalfPower (k : ℝ) :
      Kakeya.realRpowENN delta
          (commonBand.band.massLoss + epsilon / 2 + k) ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta (commonBand.band.massLoss + k) := by
    apply (ENNReal.mul_le_mul_iff_right
      (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)).mp
    calc
      2 * Kakeya.realRpowENN delta
            (commonBand.band.massLoss + epsilon / 2 + k) ≤
          Kakeya.realRpowENN delta (commonBand.band.massLoss + k) :=
        htwoPower k
      _ = 2 * ((1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta (commonBand.band.massLoss + k)) := by
        have hhalf : (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
          rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
        rw [show 2 * ((1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta (commonBand.band.massLoss + k)) =
          (2 * (1 / 2 : ENNReal)) *
            Kakeya.realRpowENN delta (commonBand.band.massLoss + k) by ring,
          hhalf, one_mul]
  let selectedSource : PureWZ2HorizontalSourceData outputCfg := {
    c := horizontalSource.c
    d := horizontalSource.d
    m := horizontalSource.m
    left_mem := horizontalSource.left_mem
    ordered := horizontalSource.ordered
    right_mem := horizontalSource.right_mem
    source_length := horizontalSource.source_length
    length_eq := horizontalSource.length_eq
    slopeScale_pos := horizontalSource.slopeScale_pos
    slopeScale_lower := horizontalSource.slopeScale_lower
    slopeScale_le_one := horizontalSource.slopeScale_le_one
    globalSlope := horizontalSource.globalSlope
    globalSlope_eq_on := horizontalSource.globalSlope_eq_on
    globalSlope_normalized := horizontalSource.globalSlope_normalized
    derivative_band := horizontalSource.derivative_band
    sourceShading := selection.selectedShading
    source_in_interval := by
      intro index point hpoint
      exact horizontalSource.source_in_interval index
        (selection.selected_subshading index hpoint)
    source_mass_lower := by
      calc
        Kakeya.realRpowENN delta (technicalLoss + 3) *
              ENNReal.ofReal (horizontalSource.d - horizontalSource.c) ≤
            ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta
                (commonBand.band.massLoss + 3)) *
              ENNReal.ofReal (horizontalSource.d - horizontalSource.c) := by
                exact mul_le_mul_right' (by
                  simpa [technicalLoss] using hhalfPower 3) _
        _ = (1 / 2 : ENNReal) *
              (Kakeya.realRpowENN delta (commonBand.band.massLoss + 3) *
                ENNReal.ofReal (horizontalSource.d - horizontalSource.c)) := by
              ring
        _ ≤ (1 / 2 : ENNReal) * horizontalSource.sourceShading.mass := by
              exact mul_le_mul_left' horizontalSource.source_mass_lower _
        _ ≤ selection.selectedShading.mass := selection.half_mass
    source_mass_card := by
      calc
        ENNReal.ofReal (Real.pi / 4) *
              Kakeya.realRpowENN delta (technicalLoss + 2) *
              outputCfg.family.enncard *
              ENNReal.ofReal (horizontalSource.d - horizontalSource.c) ≤
            ENNReal.ofReal (Real.pi / 4) *
              ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta
                (commonBand.band.massLoss + 2)) *
              outputCfg.family.enncard *
              ENNReal.ofReal (horizontalSource.d - horizontalSource.c) := by
                gcongr
                simpa [technicalLoss] using hhalfPower 2
        _ = (1 / 2 : ENNReal) *
              (ENNReal.ofReal (Real.pi / 4) *
                Kakeya.realRpowENN delta (commonBand.band.massLoss + 2) *
                cfg.family.enncard *
                ENNReal.ofReal (horizontalSource.d - horizontalSource.c)) := by
              dsimp only [outputCfg, PureWZ2C2GrainConfiguration.mono_loss]
              ring
        _ ≤ (1 / 2 : ENNReal) * horizontalSource.sourceShading.mass := by
              exact mul_le_mul_left' horizontalSource.source_mass_card _
        _ ≤ selection.selectedShading.mass := selection.half_mass
    sourceGlobalGrains := selectedGlobalGrains
    source_global_slope_eq := rfl
    sourceLocalGrains := selectedLocalGrains
    geometrySlope := horizontalSource.geometrySlope
    geometrySlope_normalized := horizontalSource.geometrySlope_normalized
    f := horizontalSource.f
    f_nonsingular := horizontalSource.f_nonsingular
    f_formula := horizontalSource.f_formula
  }
  have hshear : |selection.shear| ≤ 1 / 2 := by
    rw [selection.shear_eq]
    exact selection.shear_choice.shear_abs_le
  let fixedSource := PureWZ2HalfOffsetHorizontalSourceData.withFixedShear
    selectedSource selection.shear hshear
  have hselectedDenominator :
      ∀ point : {point : Point3 // point ∈ selectedSource.sourceShading.union},
        (1 / 50 : ℝ) ≤
          |pureWZ2OffsetShearNormal selection.shear
            (selectedSource.sourceLocalGrains.planeMap point) 1| := by
    intro point
    simpa [selectedSource, selectedLocalGrains,
      PureWZ2LocalGrainData.weaken_constant] using
        selection.denominator_lower point
  let halfOffsetAssembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta := {
    technicalLoss := technicalLoss
    technicalLoss_pos := by
      dsimp only [technicalLoss]
      rw [commonBand.band_massLoss, commonBand.common_loss,
        lemma31.data.targetLoss_eq, ← lemma31.eta_eq]
      nlinarith [lemma31.eta_pos, hepsilon]
    technicalLoss_nonneg := htechnicalNonneg
    technicalLoss_le_two_epsilon := by
      dsimp only [technicalLoss]
      rw [commonBand.band_massLoss, commonBand.common_loss,
        lemma31.data.targetLoss_eq, ← lemma31.eta_eq]
      have hetaScaled : 1000 * lemma31.eta ≤ epsilon := by
        calc
          1000 * lemma31.eta ≤ epsilon * sigma ^ 2 := lemma31.eta_budget
          _ ≤ epsilon := by
            have hsigmaSq : sigma ^ 2 ≤ 1 := by
              nlinarith [critical.sigma_pos, critical.sigma_lt_one]
            exact mul_le_of_le_one_right hepsilon.le hsigmaSq
      nlinarith [lemma31.eta_pos]
    cfg := outputCfg
    globalSlope := directLemma31.data.globalSlope
    globalSlope_eq_source := by
      intro z hz
      exact (directLemma31.data.globalSlope_eq_on z hz).trans
        (congrFun hcfgSlope.symm z)
    globalSlope_normalized := directLemma31.data.globalSlope_normalized
    rho := directRho
    delta_small := directLemma31.delta_small
    rho_tiny := by
      change commonBand.band.right - commonBand.band.left ≤ 1 / 6400
      rw [commonBand.band.length_eq]
      exact (div_le_self
        (directLemma31.data.cfg.extremal.delta_pos.trans_le
          directLemma31.data.rho.2.1).le (by norm_num)).trans
        (directLemma31.rho_tiny.trans (by norm_num))
    rho_final_tiny := by
      change commonBand.band.right - commonBand.band.left ≤ _
      rw [commonBand.band.length_eq]
      apply (div_le_self
        (directLemma31.data.cfg.extremal.delta_pos.trans_le
          directLemma31.data.rho.2.1).le (by norm_num)).trans
      exact directLemma31.rho_coupled_tiny.trans <| by
        unfold pureWZ2DirectFinalGeometryThreshold
          pureWZ2DirectFinalGeometryConstant pureWZ2CoupledConflictConstant
          pureWZ2CoupledScaleRequirement
        have hLPos : 0 < (lipschitzExtensionConstant Point3 : ℝ) :=
          lipschitzExtensionConstant_pos Point3
        apply one_div_le_one_div_of_le (by positivity)
        have hreqConstant : (15000 : ℝ) ≤
            max 15000 (1536 * (lipschitzExtensionConstant Point3 : ℝ)) :=
          le_max_left _ _
        have hreqSlope :
            1536 * (lipschitzExtensionConstant Point3 : ℝ) ≤
              max 15000
                (1536 * (lipschitzExtensionConstant Point3 : ℝ)) :=
          le_max_right _ _
        have hgeometry :
            max 1
                (max
                  (16 * (lipschitzExtensionConstant Point3 : ℝ) *
                    145440000)
                  1818000000) ≤
              75000000000 *
                max 15000
                  (1536 * (lipschitzExtensionConstant Point3 : ℝ)) := by
          apply max_le
          · nlinarith
          · apply max_le
            · nlinarith
            · nlinarith
        nlinarith
    delta_le_rho_sq := by
      change delta ≤ (commonBand.band.right - commonBand.band.left) ^ 2
      rw [commonBand.band.length_eq]
      have hpower := directLemma31.delta_le_rho_eight
      have hrhoNonneg : 0 ≤ directLemma31.data.rho.1 :=
        (directLemma31.data.cfg.extremal.delta_pos.trans_le
          directLemma31.data.rho.2.1).le
      have hrhoTiny : directLemma31.data.rho.1 ≤ 1 / 2500 :=
        directLemma31.rho_tiny.trans (by norm_num)
      have hfourth : directLemma31.data.rho.1 ^ 4 ≤
          directLemma31.data.rho.1 / 50 := by
        nlinarith [sq_nonneg directLemma31.data.rho.1,
          mul_nonneg hrhoNonneg (sub_nonneg.mpr hrhoTiny)]
      have hsquare := pow_le_pow_left₀ (pow_nonneg hrhoNonneg 4) hfourth 2
      nlinarith
    delta_le_rho_eight := by
      change delta ≤ (commonBand.band.right - commonBand.band.left) ^ 8
      rw [commonBand.band.length_eq]
      have hpower : delta ≤ directLemma31.data.rho.1 ^ 64 := by
        have hdeltaOne : delta ≤ 1 :=
          directLemma31.data.cfg.extremal.delta_le_one
        rw [directLemma31.data.rho_eq_power]
        have hmain : Real.rpow delta 1 ≤ Real.rpow delta (64 * epsilon) :=
          Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by
            have := mul_le_mul_of_nonneg_left hepsilonSixtyFourth
              (by norm_num : (0 : ℝ) ≤ 64)
            norm_num at this ⊢
            exact this)
        calc
          delta = Real.rpow delta 1 := (Real.rpow_one delta).symm
          _ ≤ Real.rpow delta (64 * epsilon) := hmain
          _ = (Real.rpow delta epsilon) ^ 64 := by
            exact (rpow_nat_pow hdelta epsilon 64).symm.trans <| by
              congr 1 <;> ring
      have hrhoNonneg : 0 ≤ directLemma31.data.rho.1 :=
        (directLemma31.data.cfg.extremal.delta_pos.trans_le
          directLemma31.data.rho.2.1).le
      have hrhoTiny : directLemma31.data.rho.1 ≤ 1 / 50 :=
        directLemma31.rho_tiny.trans (by norm_num)
      have hbase : directLemma31.data.rho.1 ^ 8 ≤
          directLemma31.data.rho.1 / 50 := by
        have hrhoOne : directLemma31.data.rho.1 ≤ 1 :=
          hrhoTiny.trans (by norm_num)
        have hseven : directLemma31.data.rho.1 ^ 7 ≤
            directLemma31.data.rho.1 := by
          calc
            directLemma31.data.rho.1 ^ 7 =
                directLemma31.data.rho.1 *
                  directLemma31.data.rho.1 ^ 6 := by ring
            _ ≤ directLemma31.data.rho.1 * 1 := by
              gcongr
              exact pow_le_one₀ hrhoNonneg hrhoOne
            _ = directLemma31.data.rho.1 := by ring
        calc
          directLemma31.data.rho.1 ^ 8 =
              directLemma31.data.rho.1 ^ 7 *
                directLemma31.data.rho.1 := by ring
          _ ≤ directLemma31.data.rho.1 *
                directLemma31.data.rho.1 := by gcongr
          _ ≤ directLemma31.data.rho.1 * (1 / 50) := by gcongr
          _ = directLemma31.data.rho.1 / 50 := by ring
      have heighth := pow_le_pow_left₀ (pow_nonneg hrhoNonneg 8) hbase 8
      nlinarith
    scaleData := {
      slabLeft := commonBand.band.left
      slabRight := commonBand.band.right
      slabLeft_mem := directLemma31.data.scaleData.slabLeft_mem.trans
        commonBand.band.left_mem
      slab_ordered := commonBand.band.ordered
      slabRight_mem := commonBand.band.right_mem.trans
        directLemma31.data.scaleData.slabRight_mem
      slab_width := rfl
    }
    horizontalSource := fixedSource
    globalSlope_eq_horizontalSource := rfl
    horizontalSource_scale := by
      dsimp only [fixedSource, selectedSource,
        PureWZ2HalfOffsetHorizontalSourceData.withFixedShear, directRho]
  }
  exact ⟨delta, hdelta, hdeltaOriginalBound, ⟨{
    lemma31 := lemma31
    lemma31_eta_eq := hlemma31Eta
    commonBand := commonBand
    subband := subband
    halfOffsetAssembly := halfOffsetAssembly
    halfOffsetAssembly_technicalLoss := rfl
    halfOffsetAssembly_rho_eq_power_div := by
      change commonBand.band.right - commonBand.band.left =
        Real.rpow delta epsilon / 50
      rw [commonBand.band.length_eq, commonBand.band_lemma31,
        lemma31.data.rho_eq_power]
    halfOffsetAssembly_globalSlope := rfl
    halfOffsetAssembly_cfg_cubical := outputCfg.cubical
    halfOffsetAssembly_source_subconfiguration := by
      intro index
      change selection.selectedShading.carrier index ⊆ cfg.shading.carrier index
      exact (selection.selected_subshading index).trans <|
        (hsourceSub index).trans (hbandSourceSub index)
    halfOffsetAssembly_source_coordinates := ⟨rfl, rfl, rfl⟩
    halfOffsetAssembly_geometry_fixedShear := by
      intro z
      simp [halfOffsetAssembly, fixedSource,
        PureWZ2HalfOffsetHorizontalSourceData.offset_withFixedShear]
    halfOffsetAssembly_compatibility := by
      change PureWZ2HalfOffsetHorizontalSourceData.FixedShearChart fixedSource
      exact PureWZ2HalfOffsetHorizontalSourceData.fixedShearChart_withFixedShear
        selectedSource selection.shear hshear hselectedDenominator
  }⟩⟩

end Kakeya.Assouad

end
