import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalProjectionSchedule
import MyLeanRepo.Kakeya.Assouad.WZ1.WellSeparatedProjectionUnion

/-!
# Uniform projection threshold for the source-horizontal graph

The source carrier and its loss are fixed before any local height block is
chosen.  This module selects the common-endpoint projection parameters once,
then supplies Alternative A uniformly for every dependent local pipeline.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2SourceHorizontalProjectionThreshold
    (sigma outputLoss : ℝ) where
  projectionEta : ℝ
  theoremEta : ℝ
  budgetFactor : ℝ
  reductionDelta₀ : ℝ
  projectionEta_pos : 0 < projectionEta
  theoremEta_pos : 0 < theoremEta
  theoremEta_small : theoremEta ≤ 1 / 100
  reductionDelta₀_pos : 0 < reductionDelta₀
  reductionDelta₀_le_half : reductionDelta₀ ≤ 1 / 2
  reduction :
    ∀ {rho : ℝ}
      {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
      {sourceH : Finset (Point2 × Point2 × Point2)}
      {unitBall : WZ1Lemma23UnitBallGraph
        rho sourceF sourceG₁ sourceG₂ sourceH}
      (ready : WZ1Lemma23Theorem22ReadyGraph
        rho theoremEta unitBall),
      ready.deltaGraph ≤ reductionDelta₀ →
      unitBall.G₂ = unitBall.G₁ →
        WZ1Proposition8_9AlternativeAUnion
            ready.deltaGraph outputLoss
            unitBall.F unitBall.G₁ unitBall.G₁ ∨
          Nonempty (PureWZ2CommonEndpointProjectionLongData
            (epsilon := outputLoss) ready budgetFactor projectionEta)
  sourceCostLossCeiling : ℝ
  sourceCostLossCeiling_pos : 0 < sourceCostLossCeiling
  gain : 10 * theoremEta + sourceCostLossCeiling <
    projectionEta * (sigma - outputLoss / 2)
  rho₀ : ℝ
  rho₀_pos : 0 < rho₀
  rho₀_le_one : rho₀ ≤ 1
  graph_small :
    ∀ rho, 0 < rho → rho ≤ rho₀ →
      wz1Lemma23Theorem22Scale (256 * rho) ≤ reductionDelta₀
  constant_small :
    ∀ rho, 0 < rho → rho ≤ rho₀ →
      (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale (256 * rho))
          (-(projectionEta * (sigma - outputLoss / 2) -
            (10 * theoremEta + sourceCostLossCeiling)) / 2)

theorem pureWZ2_sourceHorizontal_projection_threshold
    {sigma outputLoss : ℝ}
    (hsigma : 0 < sigma)
    (houtput : 0 < outputLoss)
    (houtputOne : outputLoss < 1)
    (houtputSigma : outputLoss / 2 < sigma) :
    Nonempty
      (PureWZ2SourceHorizontalProjectionThreshold sigma outputLoss) := by
  let sigmaGap := sigma - outputLoss / 2
  have hsigmaGap : 0 < sigmaGap := by
    dsimp only [sigmaGap]
    linarith
  let budgetFactor := max 100 (1000 / sigmaGap)
  have hbudgetFactor : 100 ≤ budgetFactor := le_max_left _ _
  have hbudgetFactorPos : 0 < budgetFactor :=
    lt_of_lt_of_le (by norm_num) hbudgetFactor
  have hbudgetGap : 1000 ≤ budgetFactor * sigmaGap := by
    have h := le_max_right (100 : ℝ) (1000 / sigmaGap)
    dsimp only [budgetFactor]
    calc
      1000 = (1000 / sigmaGap) * sigmaGap := by
        field_simp [hsigmaGap.ne']
      _ ≤ budgetFactor * sigmaGap := by gcongr
  rcases pureWZ2_common_endpoint_projection_reduction
      wz1_well_separated_projection_union budgetFactor outputLoss
      hbudgetFactor houtput houtputOne with
    ⟨projectionEta, theoremEta, reductionDelta₀,
      hprojectionEta, htheoremEta, htheoremEtaSmall, hsourceBudget,
      hreductionDelta₀, hreductionDelta₀Half, hreduction⟩
  let projectionGap := projectionEta * sigmaGap
  have hprojectionGap : 0 < projectionGap := by
    dsimp only [projectionGap]
    positivity
  have htheoremBudget : 1000 * theoremEta ≤ projectionGap := by
    calc
      1000 * theoremEta ≤ (budgetFactor * sigmaGap) * theoremEta := by
        gcongr
      _ = (budgetFactor * theoremEta) * sigmaGap := by ring
      _ ≤ projectionEta * sigmaGap := by gcongr
  let rawCap := (projectionGap - 10 * theoremEta) / 4
  have hrawCap : 0 < rawCap := by
    dsimp only [rawCap]
    nlinarith
  let sourceCostLossCeiling := min rawCap (projectionGap / 16)
  have hsourceCostLossCeiling : 0 < sourceCostLossCeiling := by
    dsimp only [sourceCostLossCeiling]
    positivity
  have hgain : 10 * theoremEta + sourceCostLossCeiling < projectionGap := by
    have hcap := min_le_left rawCap (projectionGap / 16)
    dsimp only [sourceCostLossCeiling]
    dsimp only [rawCap] at hcap
    nlinarith
  let gap := projectionGap -
    (10 * theoremEta + sourceCostLossCeiling)
  have hgap : 0 < gap := by dsimp only [gap]; linarith
  rcases exists_delta_realRpowENN_bound
      ((648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3))
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      (gamma := gap / 2) (by positivity) with
    ⟨graphDelta₀, hgraphDelta₀, hgraphDelta₀One, hconstant⟩
  let graphTarget := min reductionDelta₀ graphDelta₀
  let rootTarget := graphTarget / 2
  have hgraphTarget : 0 < graphTarget :=
    lt_min hreductionDelta₀ hgraphDelta₀
  have hrootTarget : 0 < rootTarget := by
    dsimp only [rootTarget]
    positivity
  have hrootTargetOne : rootTarget < 1 := by
    calc
      rootTarget < graphTarget := by
        dsimp only [rootTarget]
        linarith
      _ ≤ reductionDelta₀ := min_le_left _ _
      _ ≤ 1 / 2 := hreductionDelta₀Half
      _ < 1 := by norm_num
  rcases exists_delta_rpow_le_single (1 / 2 : ℝ) rootTarget
      (by norm_num) hrootTarget hrootTargetOne with
    ⟨rho₀, hrho₀, hrho₀One, hroot⟩
  have hgraphLeTwoRoot : ∀ rho, 0 < rho →
      wz1Lemma23Theorem22Scale (256 * rho) ≤ 2 * Real.sqrt rho := by
    intro rho hrho
    rw [wz1Lemma23Theorem22Scale, Real.sqrt_mul (by norm_num)]
    norm_num
    have hsqrtThree : 8 ≤ 5 * Real.sqrt 3 := by
      have hsqrtSq := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      have hsqrtNonneg := Real.sqrt_nonneg (3 : ℝ)
      nlinarith
    have hrootNonneg : 0 ≤ 16 * Real.sqrt rho := by positivity
    calc
      16 * Real.sqrt rho / (5 * Real.sqrt 3) ≤
          16 * Real.sqrt rho / 8 := by
        exact div_le_div_of_nonneg_left hrootNonneg (by norm_num) hsqrtThree
      _ = 2 * Real.sqrt rho := by ring
  refine ⟨{
    projectionEta := projectionEta
    theoremEta := theoremEta
    budgetFactor := budgetFactor
    reductionDelta₀ := reductionDelta₀
    projectionEta_pos := hprojectionEta
    theoremEta_pos := htheoremEta
    theoremEta_small := htheoremEtaSmall
    reductionDelta₀_pos := hreductionDelta₀
    reductionDelta₀_le_half := hreductionDelta₀Half
    reduction := hreduction
    sourceCostLossCeiling := sourceCostLossCeiling
    sourceCostLossCeiling_pos := hsourceCostLossCeiling
    gain := by simpa [projectionGap, sigmaGap] using hgain
    rho₀ := rho₀
    rho₀_pos := hrho₀
    rho₀_le_one := hrho₀One
    graph_small := ?_
    constant_small := ?_ }⟩
  · intro rho hrho hrhoSmall
    have hrootBound := hroot rho hrho hrhoSmall
    have hsqrtBound : Real.sqrt rho ≤ rootTarget := by
      simpa [Real.sqrt_eq_rpow] using hrootBound
    calc
      wz1Lemma23Theorem22Scale (256 * rho) ≤ 2 * Real.sqrt rho :=
        hgraphLeTwoRoot rho hrho
      _ ≤ 2 * rootTarget := by gcongr
      _ = graphTarget := by dsimp only [rootTarget]; ring
      _ ≤ reductionDelta₀ := min_le_left _ _
  · intro rho hrho hrhoSmall
    have hgraphPos : 0 < wz1Lemma23Theorem22Scale (256 * rho) := by
      dsimp only [wz1Lemma23Theorem22Scale]
      positivity
    have hgraphSmall :
        wz1Lemma23Theorem22Scale (256 * rho) ≤ graphDelta₀ := by
      have hrootBound := hroot rho hrho hrhoSmall
      have hsqrtBound : Real.sqrt rho ≤ rootTarget := by
        simpa [Real.sqrt_eq_rpow] using hrootBound
      calc
        wz1Lemma23Theorem22Scale (256 * rho) ≤ 2 * Real.sqrt rho :=
          hgraphLeTwoRoot rho hrho
        _ ≤ 2 * rootTarget := by gcongr
        _ = graphTarget := by dsimp only [rootTarget]; ring
        _ ≤ graphDelta₀ := min_le_right _ _
    have hbound := hconstant _ hgraphPos hgraphSmall
    convert hbound using 1 <;>
      simp only [gap, projectionGap, sigmaGap] <;> ring

theorem PureWZ2SourceHorizontalProjectionThreshold.alternativeA
    {sigma outputLoss inputLoss delta rho middleLoss stickyLoss
      normalEta : ℝ}
    (self : PureWZ2SourceHorizontalProjectionThreshold sigma outputLoss)
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (pipeline : PureWZ2SourceHorizontalPipelineData
      (normalEta := normalEta) twoScale)
    (data : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := self.theoremEta) pipeline.sharp)
    (houtput : 0 < outputLoss) (houtputOne : outputLoss < 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (houtputSigma : outputLoss / 2 < sigma)
    {sourceCostLoss : ℝ}
    (hsourceCost : Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN data.ready.deltaGraph (-sourceCostLoss))
    (hsourceCostLoss : 0 ≤ sourceCostLoss)
    (hsourceCostCeiling : sourceCostLoss ≤ self.sourceCostLossCeiling)
    (hrhoSmall : rho ≤ self.rho₀) :
    WZ1Proposition8_9AlternativeAUnion
      data.ready.deltaGraph outputLoss
      data.common.F data.common.G₁ data.common.G₁ := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hgraphSmall : data.ready.deltaGraph ≤ self.reductionDelta₀ := by
    rw [data.ready.deltaGraph_eq, pipeline.prep.graphScale_eq]
    exact self.graph_small rho hrho hrhoSmall
  have hgain : 10 * self.theoremEta + sourceCostLoss <
      self.projectionEta * (sigma - outputLoss / 2) := by
    calc
      10 * self.theoremEta + sourceCostLoss ≤
          10 * self.theoremEta + self.sourceCostLossCeiling := by gcongr
      _ < self.projectionEta * (sigma - outputLoss / 2) := self.gain
  have hgraphOne : data.ready.deltaGraph ≤ 1 :=
    hgraphSmall.trans (self.reductionDelta₀_le_half.trans (by norm_num))
  have hgraphStrict : data.ready.deltaGraph < 1 :=
    hgraphSmall.trans_lt (self.reductionDelta₀_le_half.trans_lt (by norm_num))
  have hconstantSmall :
      (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN data.ready.deltaGraph
          (-(self.projectionEta * (sigma - outputLoss / 2) -
            (10 * self.theoremEta + sourceCostLoss)) / 2) := by
    have hceiling := self.constant_small rho hrho hrhoSmall
    rw [data.ready.deltaGraph_eq, pipeline.prep.graphScale_eq]
    apply hceiling.trans
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow_of_exponent_ge
    · dsimp only [wz1Lemma23Theorem22Scale]
      positivity
    · exact (self.graph_small rho hrho hrhoSmall).trans
        (self.reductionDelta₀_le_half.trans (by norm_num))
    · have hactualGap :
          self.projectionEta * (sigma - outputLoss / 2) -
              (10 * self.theoremEta + sourceCostLoss) ≥
            self.projectionEta * (sigma - outputLoss / 2) -
              (10 * self.theoremEta + self.sourceCostLossCeiling) := by
        linarith
      nlinarith
  exact data.projection_alternative_a_strong
    houtput houtputOne hsigma hsigmaOne houtputSigma
    self.reduction hgraphSmall self.theoremEta_pos.le self.theoremEta_small
    hsourceCost hsourceCostLoss hgain hconstantSmall

end Kakeya.Assouad

end
