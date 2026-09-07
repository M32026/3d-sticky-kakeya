import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalOuterScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalReadyGraph
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalAnalyticSchedule
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.ExponentArithmetic

/-!
# Uniform numerical schedule for the ordinary one-scale chain

This module contains the outer numerical bridges for the paper-order
ordinary Corollary-5.6 step.  The public scale is first replaced by the
internal scale `targetScale / 1280`; the two sticky decompositions and the
source-horizontal fixed-line graph are then built at that one internal
scale.

The first bridge below transports a source-scale negative power to the
actual Theorem-22 graph scale.  It uses only the upper scale relation stored
by `PureWZ2SourceHorizontalFlexibleOuterScaleData`; in particular, it does
not replace the source carrier or its slope by a coarse surrogate.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The ordinary ready-graph scale is bounded by the square root of the
public output scale. -/
theorem PureWZ2SourceHorizontalReadyGraph.deltaGraph_le_sqrt_targetScale
    {sigma inputLoss delta targetScale middleLoss stickyLoss finalLoss
      normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source
      (pureWZ2SourceHorizontalInternalScale targetScale) middleLoss
      stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    (ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp)
    (outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetScale stickyLoss finalLoss) :
    ready.ready.deltaGraph ≤ Real.sqrt targetScale := by
  rw [ready.ready.deltaGraph_eq, prep.graphScale_eq]
  have htarget : 0 < targetScale := by
    have hinternal := outer.internal_pos
    unfold pureWZ2SourceHorizontalInternalScale at hinternal
    linarith
  have hscaled :
      256 * pureWZ2SourceHorizontalInternalScale targetScale ≤ targetScale := by
    unfold pureWZ2SourceHorizontalInternalScale
    nlinarith
  have hroot :
      Real.sqrt (256 * pureWZ2SourceHorizontalInternalScale targetScale) ≤
        Real.sqrt targetScale := Real.sqrt_le_sqrt hscaled
  unfold wz1Lemma23Theorem22Scale
  have hdenom : 1 ≤ 5 * Real.sqrt 3 := by
    have hsqrtThree : 1 ≤ Real.sqrt 3 :=
      (Real.one_le_sqrt).2 (by norm_num)
    nlinarith
  exact (div_le_self (Real.sqrt_nonneg _) hdenom).trans hroot

/-- Choose one source-scale threshold which converts every loss below
`sourceLossCeiling` into the requested negative power of the actual ordinary
ready-graph scale. -/
theorem pureWZ2_sourceHorizontal_ready_sourceCost_schedule
    {finalLoss sourceLossCeiling sourceCostLoss : ℝ}
    (hfinal : 0 < finalLoss)
    (hsourceLossCeiling : 0 ≤ sourceLossCeiling)
    (hsourceCostLoss : 0 < sourceCostLoss)
    (hgap : sourceLossCeiling < (finalLoss / 2) * sourceCostLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sigma inputLoss delta targetScale middleLoss stickyLoss normalEta
          theoremEta : ℝ}
        {logExponent : ℕ}
        {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
        {twoScale : PureWZ2OneScaleTwoScaleStickyData source
          (pureWZ2SourceHorizontalInternalScale targetScale) middleLoss
          stickyLoss logExponent}
        {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
        {prepared : PureWZ2SourceCarrierPreparation pullback}
        {window : PureWZ2SourceCarrierWindow prepared}
        {line : PureWZ2SourceHorizontalFixedLineData window}
        {parents : PureWZ2SourceHorizontalParentData line}
        {selection : PureWZ2SourceHorizontalYSelection parents}
        {residue : PureWZ2SourceHorizontalYResidueData selection}
        {retained : PureWZ2SourceHorizontalResidueShadingData residue}
        {prep : PureWZ2SourceHorizontalResiduePreparation retained}
        {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
        {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
        (ready : PureWZ2SourceHorizontalReadyGraph
          (theoremEta := theoremEta) sharp),
        0 < inputLoss → inputLoss ≤ sourceLossCeiling →
        0 < delta → delta ≤ delta₀ →
        targetScale ≤ Real.rpow delta finalLoss →
        (outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
          delta targetScale stickyLoss finalLoss) →
        Kakeya.realRpowENN delta (-inputLoss) ≤
          Kakeya.realRpowENN ready.ready.deltaGraph (-sourceCostLoss) := by
  rcases exists_scale_power_conversion
      (C := 1) (p := finalLoss / 2)
      (a := sourceLossCeiling) (b := sourceCostLoss)
      (by norm_num) (by positivity) hsourceLossCeiling hgap with
    ⟨delta₀, hdelta₀, hdelta₀One, hconvert⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro sigma inputLoss delta targetScale middleLoss stickyLoss normalEta
    theoremEta logExponent source twoScale pullback prepared window line
    parents selection residue retained prep graph sharp ready
    hinput hinputCeiling hdelta hdeltaSmall htargetUpper outer
  have hdeltaOne : delta ≤ 1 := hdeltaSmall.trans hdelta₀One
  have htarget : 0 < targetScale := by
    have hinternal := outer.internal_pos
    unfold pureWZ2SourceHorizontalInternalScale at hinternal
    linarith
  have htargetOne : targetScale ≤ 1 := by
    exact htargetUpper.trans
      (Real.rpow_le_one hdelta.le hdeltaOne hfinal.le)
  have hgraph : 0 < ready.ready.deltaGraph := ready.ready.deltaGraph_pos
  have hgraphOne : ready.ready.deltaGraph ≤ 1 :=
    (ready.deltaGraph_le_sqrt_targetScale
      (normalEta := normalEta) outer).trans
      (Real.sqrt_le_one.mpr htargetOne)
  have hsqrtTarget :
      Real.sqrt targetScale ≤ Real.rpow delta (finalLoss / 2) := by
    rw [Real.sqrt_eq_rpow]
    calc
      Real.rpow targetScale (1 / 2 : ℝ) ≤
          Real.rpow (Real.rpow delta finalLoss) (1 / 2 : ℝ) :=
        Real.rpow_le_rpow htarget.le htargetUpper
          (by norm_num)
      _ = Real.rpow delta (finalLoss / 2) := by
        calc
          Real.rpow (Real.rpow delta finalLoss) (1 / 2 : ℝ) =
              Real.rpow delta (finalLoss * (1 / 2 : ℝ)) :=
            (Real.rpow_mul hdelta.le _ _).symm
          _ = Real.rpow delta (finalLoss / 2) := by
            congr 1
            ring
  have hgraphPower :
      ready.ready.deltaGraph ≤ 1 * Real.rpow delta (finalLoss / 2) := by
    simpa using (ready.deltaGraph_le_sqrt_targetScale
      (normalEta := normalEta) outer).trans hsqrtTarget
  have hceiling := hconvert delta ready.ready.deltaGraph hdelta hdeltaSmall
    hgraph hgraphOne hgraphPower
  have hinputMono :
      Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN delta (-sourceLossCeiling) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith)
  exact hinputMono.trans hceiling

/-- The same scale conversion with the absolute factor `10` required by the
ordinary ready-graph constant.  The factor is absorbed at the source scale
before the power is transported to the graph scale. -/
theorem pureWZ2_sourceHorizontal_ready_constant_schedule
    {finalLoss sourceLossCeiling constantLoss : ℝ}
    (hfinal : 0 < finalLoss)
    (hsourceLossCeiling : 0 ≤ sourceLossCeiling)
    (hconstantLoss : 0 < constantLoss)
    (hgap : sourceLossCeiling < (finalLoss / 2) * constantLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sigma inputLoss delta targetScale middleLoss stickyLoss normalEta
          theoremEta : ℝ}
        {logExponent : ℕ}
        {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
        {twoScale : PureWZ2OneScaleTwoScaleStickyData source
          (pureWZ2SourceHorizontalInternalScale targetScale) middleLoss
          stickyLoss logExponent}
        {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
        {prepared : PureWZ2SourceCarrierPreparation pullback}
        {window : PureWZ2SourceCarrierWindow prepared}
        {line : PureWZ2SourceHorizontalFixedLineData window}
        {parents : PureWZ2SourceHorizontalParentData line}
        {selection : PureWZ2SourceHorizontalYSelection parents}
        {residue : PureWZ2SourceHorizontalYResidueData selection}
        {retained : PureWZ2SourceHorizontalResidueShadingData residue}
        {prep : PureWZ2SourceHorizontalResiduePreparation retained}
        {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
        {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
        (ready : PureWZ2SourceHorizontalReadyGraph
          (theoremEta := theoremEta) sharp),
        0 < inputLoss → inputLoss ≤ sourceLossCeiling →
        0 < delta → delta ≤ delta₀ →
        targetScale ≤ Real.rpow delta finalLoss →
        (outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
          delta targetScale stickyLoss finalLoss) →
        (10 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
          Real.rpow ready.ready.deltaGraph (-constantLoss) := by
  let intermediateLoss :=
    (sourceLossCeiling + (finalLoss / 2) * constantLoss) / 2
  have hsourceIntermediate : sourceLossCeiling < intermediateLoss := by
    dsimp only [intermediateLoss]
    linarith
  have hintermediateNonneg : 0 ≤ intermediateLoss := by
    dsimp only [intermediateLoss]
    positivity
  have hintermediateGap :
      intermediateLoss < (finalLoss / 2) * constantLoss := by
    dsimp only [intermediateLoss]
    linarith
  rcases exists_scale_absorb_constant (10 : ENNReal) (by norm_num)
      hsourceLossCeiling hsourceIntermediate with
    ⟨constantDelta₀, hconstantDelta₀, hconstantDelta₀One, habsorb⟩
  rcases exists_scale_power_conversion
      (C := 1) (p := finalLoss / 2)
      (a := intermediateLoss) (b := constantLoss)
      (by norm_num) (by positivity) hintermediateNonneg hintermediateGap with
    ⟨transportDelta₀, htransportDelta₀, htransportDelta₀One, htransport⟩
  let delta₀ := min constantDelta₀ transportDelta₀
  refine ⟨delta₀, lt_min hconstantDelta₀ htransportDelta₀,
    (min_le_left _ _).trans hconstantDelta₀One, ?_⟩
  intro sigma inputLoss delta targetScale middleLoss stickyLoss normalEta
    theoremEta logExponent source twoScale pullback prepared window line
    parents selection residue retained prep graph sharp ready
    hinput hinputCeiling hdelta hdeltaSmall htargetUpper outer
  have hdeltaConstant : delta ≤ constantDelta₀ :=
    hdeltaSmall.trans (min_le_left _ _)
  have hdeltaTransport : delta ≤ transportDelta₀ :=
    hdeltaSmall.trans (min_le_right _ _)
  have hdeltaOne : delta ≤ 1 := hdeltaConstant.trans hconstantDelta₀One
  have htarget : 0 < targetScale := by
    have hinternal := outer.internal_pos
    unfold pureWZ2SourceHorizontalInternalScale at hinternal
    linarith
  have htargetOne : targetScale ≤ 1 :=
    htargetUpper.trans (Real.rpow_le_one hdelta.le hdeltaOne hfinal.le)
  have hgraph : 0 < ready.ready.deltaGraph := ready.ready.deltaGraph_pos
  have hgraphOne : ready.ready.deltaGraph ≤ 1 :=
    (ready.deltaGraph_le_sqrt_targetScale
      (normalEta := normalEta) outer).trans
      (Real.sqrt_le_one.mpr htargetOne)
  have hsqrtTarget :
      Real.sqrt targetScale ≤ Real.rpow delta (finalLoss / 2) := by
    rw [Real.sqrt_eq_rpow]
    calc
      Real.rpow targetScale (1 / 2 : ℝ) ≤
          Real.rpow (Real.rpow delta finalLoss) (1 / 2 : ℝ) :=
        Real.rpow_le_rpow htarget.le htargetUpper (by norm_num)
      _ = Real.rpow delta (finalLoss / 2) := by
        calc
          Real.rpow (Real.rpow delta finalLoss) (1 / 2 : ℝ) =
              Real.rpow delta (finalLoss * (1 / 2 : ℝ)) :=
            (Real.rpow_mul hdelta.le _ _).symm
          _ = Real.rpow delta (finalLoss / 2) := by
            congr 1
            ring
  have hgraphPower :
      ready.ready.deltaGraph ≤ 1 * Real.rpow delta (finalLoss / 2) := by
    simpa using (ready.deltaGraph_le_sqrt_targetScale
      (normalEta := normalEta) outer).trans hsqrtTarget
  have hinputMono :
      Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN delta (-sourceLossCeiling) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith)
  have hsourceAbsorb :
      10 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN delta (-intermediateLoss) :=
    (mul_le_mul_left' hinputMono 10).trans
      (habsorb delta hdelta hdeltaConstant)
  have hgraphAbsorb :
      Kakeya.realRpowENN delta (-intermediateLoss) ≤
        Kakeya.realRpowENN ready.ready.deltaGraph (-constantLoss) :=
    htransport delta ready.ready.deltaGraph hdelta hdeltaTransport
      hgraph hgraphOne hgraphPower
  have hENN := hsourceAbsorb.trans hgraphAbsorb
  have hrightTop :
      Kakeya.realRpowENN ready.ready.deltaGraph (-constantLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have hreal := ENNReal.toReal_mono hrightTop hENN
  simpa [Kakeya.realRpowENN,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hgraph.le _)] using hreal

/-- Uniform comparison between the source constant and the first-sticky
constant.  The only scale relation used is the scheduled upper bound
`rho ≤ delta^finalLoss`. -/
theorem pureWZ2_ordinary_local_constant_schedule
    {finalLoss sourceLossCeiling middleLoss : ℝ}
    (hfinalLoss : 0 < finalLoss)
    (hsourceLossCeiling : 0 ≤ sourceLossCeiling)
    (hmiddleLoss : 0 < middleLoss)
    (hgap : sourceLossCeiling < finalLoss * middleLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {inputLoss delta rho : ℝ},
        0 < inputLoss → inputLoss ≤ sourceLossCeiling →
        0 < delta → delta ≤ delta₀ →
        0 < rho → rho ≤ 1 → rho ≤ Real.rpow delta finalLoss →
          35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
            19 * (10 * Kakeya.realRpowENN rho (-middleLoss)) := by
  let intermediateLoss :=
    (sourceLossCeiling + finalLoss * middleLoss) / 2
  have hsourceIntermediate : sourceLossCeiling < intermediateLoss := by
    dsimp only [intermediateLoss]
    linarith
  have hintermediateNonneg : 0 ≤ intermediateLoss := by
    dsimp only [intermediateLoss]
    positivity
  have hintermediateGap : intermediateLoss < finalLoss * middleLoss := by
    dsimp only [intermediateLoss]
    linarith
  rcases exists_scale_absorb_constant (2 : ENNReal) (by norm_num)
      hsourceLossCeiling hsourceIntermediate with
    ⟨constantDelta₀, hconstantDelta₀, hconstantDelta₀One, habsorb⟩
  rcases exists_scale_power_conversion
      (C := 1) (p := finalLoss) (a := intermediateLoss)
      (b := middleLoss) (by norm_num) hfinalLoss hintermediateNonneg
      hintermediateGap with
    ⟨transportDelta₀, htransportDelta₀, htransportDelta₀One, htransport⟩
  let delta₀ := min constantDelta₀ transportDelta₀
  refine ⟨delta₀, lt_min hconstantDelta₀ htransportDelta₀,
    (min_le_left _ _).trans hconstantDelta₀One, ?_⟩
  intro inputLoss delta rho hinput hinputCeiling hdelta hdeltaSmall hrho
    hrhoOne hrhoUpper
  have hdeltaOne : delta ≤ 1 :=
    hdeltaSmall.trans ((min_le_left _ _).trans hconstantDelta₀One)
  have hinputMono : Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-sourceLossCeiling) :=
    by
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith)
  have hsource : 2 * Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-intermediateLoss) :=
    (mul_le_mul_left' hinputMono 2).trans
      (habsorb delta hdelta
        (hdeltaSmall.trans (min_le_left _ _)))
  have htarget := htransport delta rho hdelta
    (hdeltaSmall.trans (min_le_right _ _)) hrho hrhoOne (by simpa using hrhoUpper)
  have hsourceTarget :
      2 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN rho (-middleLoss) := hsource.trans htarget
  calc
    35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * (2 * Kakeya.realRpowENN delta (-inputLoss))) := by
      calc
        35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) =
            350 * Kakeya.realRpowENN delta (-inputLoss) := by ring
        _ ≤ 380 * Kakeya.realRpowENN delta (-inputLoss) :=
          mul_le_mul_right' (by norm_num : (350 : ENNReal) ≤ 380) _
        _ = 19 * (10 * (2 *
            Kakeya.realRpowENN delta (-inputLoss))) := by ring
    _ ≤ 19 * (10 * Kakeya.realRpowENN rho (-middleLoss)) := by
      exact mul_le_mul_left' (mul_le_mul_left' hsourceTarget 10) 19

/-- The power and logarithmic certificates used before the ordinary
source-horizontal graph is built.  The two scale variables are kept
separate: `delta` is the original source scale, while `rho` is the internal
sticky scale. -/
structure PureWZ2OrdinaryCoreThreshold
    (sigma sourceLossCeiling middleLossCeiling stickyLoss normalEta finalLoss : ℝ)
    (logExponent : ℕ) where
  secondEta : ℝ
  secondEta_eq : secondEta = normalEta / 16
  secondEta_pos : 0 < secondEta
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  rho₀ : ℝ
  rho₀_pos : 0 < rho₀
  rho₀_le_one : rho₀ ≤ 1
  source_floor :
    ∀ {rho middleLoss : ℝ},
      0 < rho → rho ≤ rho₀ →
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2)
  local_power :
    ∀ {inputLoss delta rho : ℝ},
      0 < inputLoss → inputLoss ≤ sourceLossCeiling →
      0 < delta → delta ≤ delta₀ →
      0 < rho → 4 * rho ≤ 1 → rho ≤ Real.rpow delta finalLoss →
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta)
  global_power :
    ∀ {middleLoss rho : ℝ},
      0 < middleLoss → middleLoss ≤ middleLossCeiling →
      0 < rho → rho ≤ rho₀ →
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta)
  height_absorb :
    ∀ {rho : ℝ}, 0 < rho → rho ≤ rho₀ →
      256 * rho + 2 * Real.sqrt rho ≤ 16 * Real.sqrt rho
  second_fraction :
    ∀ {rho : ℝ}, 0 < rho → rho ≤ rho₀ →
      Kakeya.realRpowENN rho secondEta ≤
        wz2PaperPureRefinementFraction rho logExponent

/-- Select the ordinary pre-graph losses in the paper order.  The source and
middle losses are already fixed by the two nested sticky calls; strict gaps
to `finalLoss * normalEta` and `normalEta` pay the two source-horizontal AD
constants. -/
theorem pureWZ2_ordinary_core_threshold
    {sigma sourceLossCeiling middleLossCeiling stickyLoss normalEta finalLoss : ℝ}
    (logExponent : ℕ)
    (hsigma : 0 < sigma)
    (hsourceLossCeiling : 0 ≤ sourceLossCeiling)
    (hmiddleLossCeiling : 0 ≤ middleLossCeiling)
    (hsticky : 0 < stickyLoss)
    (hnormalEta : 0 < normalEta)
    (hfinal : 0 < finalLoss)
    (hstickyNormal : 3 * stickyLoss / 2 < normalEta)
    (hmiddleNormal : middleLossCeiling < normalEta)
    (hsourceGap : sourceLossCeiling < finalLoss * normalEta) :
    Nonempty (PureWZ2OrdinaryCoreThreshold sigma sourceLossCeiling
      middleLossCeiling stickyLoss normalEta finalLoss logExponent) := by
  let sourceIntermediate :=
    (sourceLossCeiling + finalLoss * normalEta) / 2
  have hsourceIntermediate : sourceLossCeiling < sourceIntermediate := by
    dsimp only [sourceIntermediate]
    linarith
  have hsourceIntermediateNonneg : 0 ≤ sourceIntermediate := by
    dsimp only [sourceIntermediate]
    positivity
  have hsourceIntermediateGap :
      sourceIntermediate < finalLoss * normalEta := by
    dsimp only [sourceIntermediate]
    linarith
  rcases exists_scale_absorb_constant (160 : ENNReal) (by norm_num)
      hsourceLossCeiling hsourceIntermediate with
    ⟨sourceConstantDelta₀, hsourceConstantDelta₀,
      hsourceConstantDelta₀One, hsourceConstant⟩
  rcases exists_scale_power_conversion
      (C := 4) (p := finalLoss)
      (a := sourceIntermediate) (b := normalEta)
      (by norm_num) hfinal hsourceIntermediateNonneg hsourceIntermediateGap with
    ⟨sourceTransportDelta₀, hsourceTransportDelta₀,
      hsourceTransportDelta₀One, hsourceTransport⟩
  let middleIntermediate := (middleLossCeiling + normalEta) / 2
  have hmiddleIntermediate : middleLossCeiling < middleIntermediate := by
    dsimp only [middleIntermediate]
    linarith
  have hmiddleIntermediateNonneg : 0 ≤ middleIntermediate := by
    dsimp only [middleIntermediate]
    positivity
  have hmiddleIntermediateGap : middleIntermediate < normalEta := by
    dsimp only [middleIntermediate]
    linarith
  rcases exists_scale_absorb_constant (10 : ENNReal) (by norm_num)
      hmiddleLossCeiling hmiddleIntermediate with
    ⟨middleConstantRho₀, hmiddleConstantRho₀, hmiddleConstantRho₀One,
      hmiddleConstant⟩
  rcases exists_scale_power_conversion
      (C := 4) (p := 1)
      (a := middleIntermediate) (b := normalEta)
      (by norm_num) (by norm_num) hmiddleIntermediateNonneg
      (by simpa using hmiddleIntermediateGap) with
    ⟨middleTransportRho₀, hmiddleTransportRho₀, hmiddleTransportRho₀One,
      hmiddleTransport⟩
  let sourceExponent := 3 / 2 + sigma / 2 + normalEta
  let targetExponent := 3 / 2 + sigma / 2 + 3 * stickyLoss / 2
  have hsourceExponent : 0 < sourceExponent := by
    dsimp only [sourceExponent]
    positivity
  have hexponentGap : targetExponent < sourceExponent := by
    dsimp only [targetExponent, sourceExponent]
    linarith
  rcases exists_delta₀_const_mul_rpow_le
      (Real.rpow 4 sourceExponent)
      (Real.rpow_pos_of_pos (by norm_num) _ )
      targetExponent sourceExponent hexponentGap with
    ⟨floorRho₀, hfloorRho₀, hfloorRho₀One, hfloor⟩
  rcases exists_delta_rpow_le_single (1 / 2 : ℝ) (7 / 128 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) with
    ⟨heightRho₀, hheightRho₀, hheightRho₀One, hheight⟩
  let secondEta := normalEta / 16
  have hsecondEta : 0 < secondEta := by
    dsimp only [secondEta]
    positivity
  rcases pureWZ2_refinementFraction_power_schedule logExponent hsecondEta with
    ⟨fractionRho₀, hfractionRho₀, hfractionRho₀One, hfraction⟩
  let delta₀ := min sourceConstantDelta₀ sourceTransportDelta₀
  let rho₀ := min middleConstantRho₀
    (min middleTransportRho₀ (min floorRho₀ (min heightRho₀ fractionRho₀)))
  have hdelta₀ : 0 < delta₀ :=
    lt_min hsourceConstantDelta₀ hsourceTransportDelta₀
  have hrho₀ : 0 < rho₀ := by
    dsimp only [rho₀]
    exact lt_min hmiddleConstantRho₀
      (lt_min hmiddleTransportRho₀
        (lt_min hfloorRho₀ (lt_min hheightRho₀ hfractionRho₀)))
  refine ⟨{
    secondEta := secondEta
    secondEta_eq := rfl
    secondEta_pos := hsecondEta
    delta₀ := delta₀
    delta₀_pos := hdelta₀
    delta₀_le_one := (min_le_left _ _).trans hsourceConstantDelta₀One
    rho₀ := rho₀
    rho₀_pos := hrho₀
    rho₀_le_one := (min_le_left _ _).trans hmiddleConstantRho₀One
    source_floor := ?_
    local_power := ?_
    global_power := ?_
    height_absorb := ?_
    second_fraction := ?_ }⟩
  · intro rho middleLoss hrho hrhoSmall
    have hrhoFloor : rho ≤ floorRho₀ :=
      hrhoSmall.trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
    have hbase :
        ENNReal.ofReal (Real.rpow 4 sourceExponent) *
            Kakeya.realRpowENN rho sourceExponent ≤
          Kakeya.realRpowENN rho targetExponent :=
      hfloor rho hrho hrhoFloor
    have hfour :
        Kakeya.realRpowENN (4 * rho) sourceExponent =
          ENNReal.ofReal (Real.rpow 4 sourceExponent) *
            Kakeya.realRpowENN rho sourceExponent := by
      simpa [Kakeya.realRpowENN] using
        (realRpowENN_mul (x := (4 : ℝ)) (y := rho)
          (by norm_num) hrho sourceExponent)
    calc
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) =
          Kakeya.realRpowENN (4 * rho) sourceExponent := by
            rfl
      _ = ENNReal.ofReal (Real.rpow 4 sourceExponent) *
          Kakeya.realRpowENN rho sourceExponent := hfour
      _ ≤ Kakeya.realRpowENN rho targetExponent := hbase
      _ = Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) := by rfl
  · intro inputLoss delta rho hinput hinputCeiling hdelta hdeltaSmall
      hrho hfourRho hrhoUpper
    have hdeltaConstant : delta ≤ sourceConstantDelta₀ :=
      hdeltaSmall.trans (min_le_left _ _)
    have hdeltaTransport : delta ≤ sourceTransportDelta₀ :=
      hdeltaSmall.trans (min_le_right _ _)
    have hdeltaOne : delta ≤ 1 :=
      hdeltaConstant.trans hsourceConstantDelta₀One
    have hinputMono :
        Kakeya.realRpowENN delta (-inputLoss) ≤
          Kakeya.realRpowENN delta (-sourceLossCeiling) := by
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith)
    have hconstant :
        160 * Kakeya.realRpowENN delta (-inputLoss) ≤
          Kakeya.realRpowENN delta (-sourceIntermediate) :=
      (mul_le_mul_left' hinputMono 160).trans
        (hsourceConstant delta hdelta hdeltaConstant)
    exact hconstant.trans
      (hsourceTransport delta (4 * rho) hdelta hdeltaTransport
        (by positivity) hfourRho (by simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_left hrhoUpper (by norm_num : (0 : ℝ) ≤ 4))))
  · intro middleLoss rho hmiddle hmiddleCeiling hrho hrhoSmall
    have hrhoConstant : rho ≤ middleConstantRho₀ :=
      hrhoSmall.trans (min_le_left _ _)
    have hrhoTransport : rho ≤ middleTransportRho₀ :=
      hrhoSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hrhoOne : rho ≤ 1 :=
      hrhoConstant.trans hmiddleConstantRho₀One
    have hrhoHeight : rho ≤ heightRho₀ :=
      hrhoSmall.trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))
    have hsqrtBound : Real.sqrt rho ≤ 7 / 128 := by
      simpa [Real.sqrt_eq_rpow] using hheight rho hrho hrhoHeight
    have hsqrtSq : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt hrho.le
    have hfourRho : 4 * rho ≤ 1 := by
      nlinarith [Real.sqrt_nonneg rho]
    have hmiddleMono :
        Kakeya.realRpowENN rho (-middleLoss) ≤
          Kakeya.realRpowENN rho (-middleLossCeiling) := by
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge hrho hrhoOne (by linarith)
    exact ((mul_le_mul_left' hmiddleMono 10).trans
      (hmiddleConstant rho hrho hrhoConstant)).trans
      (hmiddleTransport rho (4 * rho) hrho hrhoTransport
        (by positivity) hfourRho (by simp [Real.rpow_one]))
  · intro rho hrho hrhoSmall
    have hrhoHeight : rho ≤ heightRho₀ :=
      hrhoSmall.trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))
    have hroot : Real.sqrt rho ≤ 7 / 128 := by
      simpa [Real.sqrt_eq_rpow] using hheight rho hrho hrhoHeight
    have hsqrt : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
    have hsqrtSq : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt hrho.le
    nlinarith
  · intro rho hrho hrhoSmall
    exact hfraction rho hrho
      (hrhoSmall.trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _)))))

end Kakeya.Assouad

end
