import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7AffineScalarBounds
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7AffineCleanupBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers

/-!
# Pre-runtime scalar schedule for the Node 7 affine configuration

All cutoffs in this file are selected before the runtime source, scale,
family, and shading.  The runtime methods merely specialize these frozen
certificates to the synchronized affine package.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

namespace PureWZ2Node7AffineDiagonalPreparationData

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}

/-- CWA absorption at the final radius. -/
theorem exists_delta_for_node7_ordinary_cwa
    (sigma epsilon coreLoss : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon < 1)
    (hgap : 10 * epsilon < (1 - epsilon) * coreLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {delta : ℝ}
        {commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta}
        (data : PureWZ2Node7AffineDiagonalPreparationData commonSource),
        0 < delta → delta ≤ delta₀ →
        WZ2PaperConvexWolffBound data.ordinaryFamily
          (Kakeya.realRpowENN data.finalRadius (-coreLoss)) := by
  rcases exists_delta_for_selectedSourceTopLevelConstant
      sigma epsilon hsigma hsigmaOne hepsilon with
    ⟨sourceScale, hsourceScale, hsourceScaleOne, hsource⟩
  rcases exists_delta_constant_mul_power_le_power
      (8957952000000000 : ENNReal) (by norm_num)
      (-10 * epsilon) (-9 * epsilon) (by linarith) with
    ⟨coefficientScale, hcoefficientScale, hcoefficientScaleOne,
      hcoefficient⟩
  rcases exists_scale_power_conversion
      (C := 60000) (p := 1 - epsilon)
      (a := 10 * epsilon) (b := coreLoss)
      (by norm_num) (by linarith) (by positivity) hgap with
    ⟨conversionScale, hconversionScale, hconversionScaleOne, hconversion⟩
  rcases exists_source_cutoff_for_finalRadius
      epsilon 1 hepsilon hepsilonOne (by norm_num) with
    ⟨radiusScale, hradiusScale, hradiusScaleOne, hradius⟩
  let delta₀ := min sourceScale <| min coefficientScale <|
    min conversionScale radiusScale
  refine ⟨delta₀, by dsimp only [delta₀]; positivity,
    (min_le_left _ _).trans hsourceScaleOne, ?_⟩
  intro logExponent delta commonSource data hdelta hdeltaSmall
  have hsourceSmall : delta ≤ sourceScale :=
    hdeltaSmall.trans (min_le_left _ _)
  have hcoefficientSmall : delta ≤ coefficientScale :=
    hdeltaSmall.trans <| (min_le_right _ _).trans (min_le_left _ _)
  have hconversionSmall : delta ≤ conversionScale :=
    hdeltaSmall.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have hradiusSmall : delta ≤ radiusScale :=
    hdeltaSmall.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_right _ _)
  have hsourceBound := hsource data hdelta hsourceSmall
  have hraw := data.selectedTopLevelConstant_le_source_power hsourceBound
  have hcoefficientBound := hcoefficient hdelta hcoefficientSmall
  have hsourcePower :
      data.selectedAffineTopLevelLoss * data.selectedSourceTopLevelConstant ≤
        Kakeya.realRpowENN delta (-10 * epsilon) :=
    hraw.trans hcoefficientBound
  have hfinalOne : data.finalRadius ≤ 1 :=
    hradius data hdelta hradiusSmall
  have hconverted : Kakeya.realRpowENN delta (-10 * epsilon) ≤
      Kakeya.realRpowENN data.finalRadius (-coreLoss) :=
    by
      simpa only [neg_mul] using
        hconversion delta data.finalRadius hdelta hconversionSmall
          data.finalRadius_pos hfinalOne data.finalRadius_le_source_power
  exact data.ordinaryFamily_top_level_cwa.weaken_constant
    (hsourcePower.trans hconverted)

/-- Density absorption at the final radius. -/
theorem exists_delta_for_node7_ordinary_density
    (epsilon coreLoss : ℝ)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon < 1 / 2)
    (hcore : 0 < coreLoss)
    (hgap : 2 + 4 * epsilon < (1 - 2 * epsilon) * (coreLoss + 2)) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {sigma delta : ℝ}
        {commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta}
        (data : PureWZ2Node7AffineDiagonalPreparationData commonSource),
        sigma < 1 → 0 < delta → delta ≤ delta₀ →
        data.ordinaryShading.IsLambdaDense
          (Kakeya.realRpowENN data.finalRadius coreLoss) := by
  rcases exists_delta_for_node7_density_budget epsilon coreLoss hepsilon
      hepsilonHalf hcore hgap with
    ⟨delta₀, hdelta₀, hdelta₀One, hbudget⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro logExponent sigma delta commonSource data hsigmaOne hdelta hdeltaSmall
  exact data.ordinaryShading_dense_of_budget _
    (hbudget data hsigmaOne hdelta hdeltaSmall)

/-- A source-scale cutoff making the literal derivative-band CWA constant
strictly larger than two, as required by the popular-source regularization. -/
theorem exists_delta_for_node7_sourceConstant_gt_two
    (sigma epsilon : ℝ) (hsigma : 0 < sigma) (hepsilon : 0 < epsilon) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        0 < delta → delta ≤ delta₀ →
        2 < commonSource.commonBand.band.sourceConstant := by
  have hexponent : 0 < epsilon * sigma ^ 2 / 16000 := by positivity
  rcases exists_delta_realRpowENN_bound
      (3 : ENNReal) (by norm_num) hexponent with
    ⟨delta₀, hdelta₀, hdelta₀One, hbound⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro logExponent delta commonSource hdelta hdeltaSmall
  have hthree : (3 : ENNReal) ≤
      Kakeya.realRpowENN delta (-(epsilon * sigma ^ 2 / 16000)) :=
    hbound delta hdelta hdeltaSmall
  have hsourceEq : commonSource.commonBand.band.sourceConstant =
      Kakeya.realRpowENN delta (-(epsilon * sigma ^ 2 / 16000)) := by
    unfold PureWZ2Lemma32DerivativeBandAssembly.sourceConstant
    rw [commonSource.commonBand.band_lemma31,
      commonSource.lemma31.data.targetLoss_eq,
      ← commonSource.lemma31.eta_eq, commonSource.lemma31_eta_eq]
    congr 1
    ring
  rw [hsourceEq]
  exact (by norm_num : (2 : ENNReal) < 3).trans_le hthree

/-- The raw cubical AD constant is a fixed multiple of the source constant. -/
theorem cubicalGlobalADConstant_le_source_power
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    data.Node7CubicalGlobalADConstant ≤
      (99144 : ENNReal) *
        Kakeya.realRpowENN delta
          (-commonSource.commonBand.band.lemma31.data.targetLoss) := by
  unfold Node7CubicalGlobalADConstant Node7CubicalGlobalADProjectionFactor
    PureWZ2Lemma32DerivativeBandAssembly.sourceConstant
  norm_num
  rw [← mul_assoc]
  norm_num

/-- Projection scalar budget at the affine target scale. -/
theorem exists_delta_for_node7_projection_scalar
    (sigma epsilon intermediateLoss : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon < 1 / 2)
    (hintermediate : 0 < intermediateLoss)
    (hgap : epsilon < (1 - 2 * epsilon) * intermediateLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {delta : ℝ}
        {commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta}
        (data : PureWZ2Node7AffineDiagonalPreparationData commonSource),
        0 < delta → delta ≤ delta₀ →
        Node7ProjectionScalarBudget data data.Node7CubicalGlobalADConstant
          intermediateLoss := by
  let finiteConstant : ENNReal :=
    16 * 99144 * Kakeya.realRpowENN 6 (1 - sigma)
  have hfiniteTop : finiteConstant ≠ ⊤ := by
    unfold finiteConstant
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (by norm_num))
      ENNReal.ofReal_ne_top
  rcases exists_delta_constant_mul_power_le_power
      finiteConstant hfiniteTop
      (-((1 - 2 * epsilon) * intermediateLoss)) (-epsilon)
      (by linarith) with
    ⟨absorbScale, habsorbScale, habsorbScaleOne, habsorb⟩
  rcases exists_delta_for_node7_finalRadius_power_upper epsilon hepsilon
      hepsilonHalf with ⟨radiusScale, hradiusScale, hradiusScaleOne, hradius⟩
  refine ⟨min absorbScale radiusScale, lt_min habsorbScale hradiusScale,
    (min_le_left _ _).trans habsorbScaleOne, ?_⟩
  intro logExponent delta commonSource data hdelta hdeltaSmall
  have hdeltaAbsorb := hdeltaSmall.trans (min_le_left _ _)
  have hdeltaRadius := hdeltaSmall.trans (min_le_right _ _)
  have hfinalUpper := hradius data hdelta hdeltaRadius
  have hdeltaOne := hdeltaSmall.trans <|
    (min_le_left _ _).trans habsorbScaleOne
  have htargetDeltaUpper : data.affineScale.targetDelta ≤
      Real.rpow delta (1 - 2 * epsilon) := by
    have hpositive := data.affineScale.targetDelta_pos
    have hfinalEq : data.finalRadius = 12 * data.affineScale.targetDelta := rfl
    rw [hfinalEq] at hfinalUpper
    linarith
  have htargetDeltaOne : data.affineScale.targetDelta ≤ 1 :=
    data.affineScale.targetDelta_le_one
  have hsourceAbsorb : finiteConstant *
        Kakeya.realRpowENN delta (-epsilon) ≤
      Kakeya.realRpowENN delta
        (-((1 - 2 * epsilon) * intermediateLoss)) :=
    habsorb hdelta hdeltaAbsorb
  have hsourceTarget : finiteConstant *
        Kakeya.realRpowENN delta (-epsilon) ≤
      Kakeya.realRpowENN data.affineScale.targetDelta
        (-intermediateLoss) :=
    hsourceAbsorb.trans <|
      pure_wz2_target_negative_power_lower hdelta
        data.affineScale.targetDelta_pos htargetDeltaUpper hintermediate.le
  have htargetLossLe :
      commonSource.commonBand.band.lemma31.data.targetLoss ≤ epsilon := by
    rw [commonSource.commonBand.band_lemma31,
      commonSource.lemma31.data.targetLoss_eq,
      ← commonSource.lemma31.eta_eq, commonSource.lemma31_eta_eq]
    have hsigmaSq : sigma ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg sigma, sq_nonneg (sigma - 1)]
    nlinarith [mul_le_mul_of_nonneg_left hsigmaSq hepsilon.le]
  have hconstant : data.Node7CubicalGlobalADConstant ≤
      (99144 : ENNReal) * Kakeya.realRpowENN delta (-epsilon) :=
    data.cubicalGlobalADConstant_le_source_power.trans <| by
      gcongr
      exact realRpowENN_antitone hdelta hdeltaOne
        (by linarith)
  unfold Node7ProjectionScalarBudget
  have hnormalize : 8 *
      (data.Node7CubicalGlobalADConstant *
        Kakeya.realRpowENN
          ((2 * (1 + (2 : ℝ))) / data.affineScale.targetDelta)
          (1 - sigma) *
        ENNReal.ofReal (2 * data.affineScale.targetDelta)) ≤
      finiteConstant * Kakeya.realRpowENN delta (-epsilon) *
          Kakeya.realRpowENN data.affineScale.targetDelta sigma := by
    have hscaleFactor : Kakeya.realRpowENN
          ((2 * (1 + (2 : ℝ))) / data.affineScale.targetDelta)
          (1 - sigma) ≤
        Kakeya.realRpowENN 6 (1 - sigma) *
          Kakeya.realRpowENN data.affineScale.targetDelta
            (-(1 - sigma)) := by
      have hbase : 0 < (6 : ℝ) := by norm_num
      have hinv : Kakeya.realRpowENN data.affineScale.targetDelta⁻¹
          (1 - sigma) =
        Kakeya.realRpowENN data.affineScale.targetDelta
          (-(1 - sigma)) := by
        exact congrArg ENNReal.ofReal <|
          (Real.inv_rpow data.affineScale.targetDelta_pos.le _).trans
            (Real.rpow_neg data.affineScale.targetDelta_pos.le _).symm
      rw [show ((2 * (1 + (2 : ℝ))) / data.affineScale.targetDelta) =
          6 * data.affineScale.targetDelta⁻¹ by ring,
        realRpowENN_mul hbase
          (inv_pos.mpr data.affineScale.targetDelta_pos), hinv]
    have htwo : ENNReal.ofReal (2 * data.affineScale.targetDelta) =
        2 * Kakeya.realRpowENN data.affineScale.targetDelta 1 := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      simp [Kakeya.realRpowENN]
    have htargetExponent : Kakeya.realRpowENN data.affineScale.targetDelta
          (-(1 - sigma)) *
          Kakeya.realRpowENN data.affineScale.targetDelta 1 =
        Kakeya.realRpowENN data.affineScale.targetDelta sigma := by
      rw [← realRpowENN_add data.affineScale.targetDelta_pos]
      congr 1
      ring
    calc
      _ ≤ 8 * (((99144 : ENNReal) *
            Kakeya.realRpowENN delta (-epsilon)) *
          (Kakeya.realRpowENN 6 (1 - sigma) *
            Kakeya.realRpowENN data.affineScale.targetDelta
              (-(1 - sigma))) *
          ENNReal.ofReal (2 * data.affineScale.targetDelta)) := by
        gcongr
      _ = 8 * (((99144 : ENNReal) *
            Kakeya.realRpowENN delta (-epsilon)) *
          (Kakeya.realRpowENN 6 (1 - sigma) *
            Kakeya.realRpowENN data.affineScale.targetDelta
              (-(1 - sigma))) *
          (2 * Kakeya.realRpowENN data.affineScale.targetDelta 1)) := by
        rw [htwo]
      _ = finiteConstant * Kakeya.realRpowENN delta (-epsilon) *
          Kakeya.realRpowENN data.affineScale.targetDelta sigma := by
        unfold finiteConstant
        calc
          _ = (16 * 99144 * Kakeya.realRpowENN 6 (1 - sigma)) *
              Kakeya.realRpowENN delta (-epsilon) *
              (Kakeya.realRpowENN data.affineScale.targetDelta
                  (-(1 - sigma)) *
                Kakeya.realRpowENN data.affineScale.targetDelta 1) := by ring
          _ = _ := by rw [htargetExponent]
      _ = _ := rfl
  exact hnormalize.trans <| by
    calc
      _ ≤ Kakeya.realRpowENN data.affineScale.targetDelta
            (-intermediateLoss) *
          Kakeya.realRpowENN data.affineScale.targetDelta sigma := by
        gcongr
      _ = Kakeya.realRpowENN data.affineScale.targetDelta
          (sigma - intermediateLoss) := by
        rw [← realRpowENN_add data.affineScale.targetDelta_pos]
        congr 1
        ring

/-- Passing from the affine target grid to the final radius `12 * Delta`
costs no further source-scale power when the final projection exponent is
nonnegative. -/
theorem final_projection_scale_comparison
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (intermediateLoss outputLoss : ℝ)
    (hintermediate : intermediateLoss ≤ outputLoss)
    (houtput : outputLoss ≤ sigma) :
    Kakeya.realRpowENN data.affineScale.targetDelta
        (sigma - intermediateLoss) ≤
      Kakeya.realRpowENN data.finalRadius (sigma - outputLoss) := by
  have hsameBase :
      Kakeya.realRpowENN data.affineScale.targetDelta
          (sigma - intermediateLoss) ≤
        Kakeya.realRpowENN data.affineScale.targetDelta
          (sigma - outputLoss) :=
    realRpowENN_mono_constant data.affineScale.targetDelta_pos
      data.affineScale.targetDelta_le_one (by linarith)
  have hbase : data.affineScale.targetDelta ≤ data.finalRadius := by
    unfold finalRadius
    nlinarith [data.affineScale.targetDelta_pos]
  apply hsameBase.trans
  apply ENNReal.ofReal_mono
  exact Real.rpow_le_rpow data.affineScale.targetDelta_pos.le hbase
    (by linarith)

/-- All scalar cutoffs needed by the direct affine Node-7 route, selected
before the runtime source and tied to one source-scale threshold. -/
structure PureWZ2Node7AffineScalarScheduleData
    (sigma analyticLoss finalCeiling : ℝ) where
  sourceDelta₀ : ℝ
  sourceDelta₀_pos : 0 < sourceDelta₀
  sourceDelta₀_le_one : sourceDelta₀ ≤ 1
  sourceConstant_gt_two :
    ∀ {logExponent : ℕ} {delta : ℝ}
      (commonSource : PureWZ2DirectCommonYSourceAssembly
        logExponent sigma (analyticLoss / 100000) delta),
      0 < delta → delta ≤ sourceDelta₀ →
      2 < commonSource.commonBand.band.sourceConstant
  finalRadius_le :
    ∀ {logExponent : ℕ} {delta : ℝ}
      {commonSource : PureWZ2DirectCommonYSourceAssembly
        logExponent sigma (analyticLoss / 100000) delta}
      (data : PureWZ2Node7AffineDiagonalPreparationData commonSource),
      0 < delta → delta ≤ sourceDelta₀ →
      data.finalRadius ≤ finalCeiling
  ordinary_cwa :
    ∀ {logExponent : ℕ} {delta : ℝ}
      {commonSource : PureWZ2DirectCommonYSourceAssembly
        logExponent sigma (analyticLoss / 100000) delta}
      (data : PureWZ2Node7AffineDiagonalPreparationData commonSource),
      0 < delta → delta ≤ sourceDelta₀ →
      WZ2PaperConvexWolffBound data.ordinaryFamily
        (Kakeya.realRpowENN data.finalRadius
          (-(analyticLoss / 100)))
  ordinary_dense :
    ∀ {logExponent : ℕ} {delta : ℝ}
      {commonSource : PureWZ2DirectCommonYSourceAssembly
        logExponent sigma (analyticLoss / 100000) delta}
      (data : PureWZ2Node7AffineDiagonalPreparationData commonSource),
      0 < delta → delta ≤ sourceDelta₀ →
      data.ordinaryShading.IsLambdaDense
        (Kakeya.realRpowENN data.finalRadius (analyticLoss / 100))
  final_projection_budget :
    ∀ {logExponent : ℕ} {delta : ℝ}
      {commonSource : PureWZ2DirectCommonYSourceAssembly
        logExponent sigma (analyticLoss / 100000) delta}
      (data : PureWZ2Node7AffineDiagonalPreparationData commonSource),
      0 < delta → delta ≤ sourceDelta₀ →
      Node7FinalProjectionScalarBudget data
        data.Node7CubicalGlobalADConstant (analyticLoss / 200) analyticLoss

/-- Freeze the complete affine scalar schedule for one requested analytic
loss and one final-radius ceiling. -/
theorem pure_wz2_node7_affine_scalar_schedule
    (sigma analyticLoss finalCeiling : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hloss : 0 < analyticLoss) (hlossSigma : analyticLoss < sigma)
    (hfinalCeiling : 0 < finalCeiling) :
    Nonempty (PureWZ2Node7AffineScalarScheduleData
      sigma analyticLoss finalCeiling) := by
  let epsilon : ℝ := analyticLoss / 100000
  let coreLoss : ℝ := analyticLoss / 100
  let intermediateLoss : ℝ := analyticLoss / 200
  have hepsilon : 0 < epsilon := by positivity
  have hepsilonOne : epsilon < 1 := by
    dsimp only [epsilon]
    linarith [hlossSigma, hsigmaOne]
  have hepsilonHalf : epsilon < 1 / 2 := by
    dsimp only [epsilon]
    linarith [hlossSigma, hsigmaOne]
  have hcore : 0 < coreLoss := by positivity
  have hintermediate : 0 < intermediateLoss := by positivity
  have hcwaGap : 10 * epsilon < (1 - epsilon) * coreLoss := by
    dsimp only [epsilon, coreLoss]
    nlinarith [hloss, hlossSigma, hsigmaOne]
  have hdensityGap :
      2 + 4 * epsilon < (1 - 2 * epsilon) * (coreLoss + 2) := by
    dsimp only [epsilon, coreLoss]
    nlinarith [hloss, hlossSigma, hsigmaOne]
  have hprojectionGap :
      epsilon < (1 - 2 * epsilon) * intermediateLoss := by
    dsimp only [epsilon, intermediateLoss]
    nlinarith [hloss, hlossSigma, hsigmaOne]
  rcases exists_delta_for_node7_sourceConstant_gt_two
      sigma epsilon hsigma hepsilon with
    ⟨sourceScale, hsourceScale, hsourceScaleOne, hsource⟩
  rcases exists_source_cutoff_for_finalRadius
      epsilon finalCeiling hepsilon hepsilonOne hfinalCeiling with
    ⟨radiusScale, hradiusScale, hradiusScaleOne, hradius⟩
  rcases exists_delta_for_node7_ordinary_cwa
      sigma epsilon coreLoss hsigma hsigmaOne hepsilon hepsilonOne
      hcwaGap with
    ⟨cwaScale, hcwaScale, hcwaScaleOne, hcwa⟩
  rcases exists_delta_for_node7_ordinary_density
      epsilon coreLoss hepsilon hepsilonHalf hcore hdensityGap with
    ⟨densityScale, hdensityScale, hdensityScaleOne, hdensity⟩
  rcases exists_delta_for_node7_projection_scalar
      sigma epsilon intermediateLoss hsigma hsigmaOne hepsilon hepsilonHalf
      hintermediate hprojectionGap with
    ⟨projectionScale, hprojectionScale, hprojectionScaleOne, hprojection⟩
  let sourceDelta₀ := min sourceScale <| min radiusScale <| min cwaScale <|
    min densityScale projectionScale
  refine ⟨{
    sourceDelta₀ := sourceDelta₀
    sourceDelta₀_pos := by dsimp only [sourceDelta₀]; positivity
    sourceDelta₀_le_one := by
      dsimp only [sourceDelta₀]
      exact (min_le_left _ _).trans hsourceScaleOne
    sourceConstant_gt_two := ?_
    finalRadius_le := ?_
    ordinary_cwa := ?_
    ordinary_dense := ?_
    final_projection_budget := ?_ }⟩
  · intro logExponent delta commonSource hdelta hdeltaSmall
    exact hsource commonSource hdelta
      (hdeltaSmall.trans (min_le_left _ _))
  · intro logExponent delta commonSource data hdelta hdeltaSmall
    exact hradius data hdelta <| hdeltaSmall.trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  · intro logExponent delta commonSource data hdelta hdeltaSmall
    exact hcwa data hdelta <| hdeltaSmall.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  · intro logExponent delta commonSource data hdelta hdeltaSmall
    exact hdensity data hsigmaOne hdelta <| hdeltaSmall.trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  · intro logExponent delta commonSource data hdelta hdeltaSmall
    refine ⟨hprojection data hdelta <| hdeltaSmall.trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _), ?_⟩
    exact data.final_projection_scale_comparison
      intermediateLoss analyticLoss (by
        dsimp only [intermediateLoss]
        linarith) hlossSigma.le

end PureWZ2Node7AffineDiagonalPreparationData

end Kakeya.Assouad

end
