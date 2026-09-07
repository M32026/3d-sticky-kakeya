import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalExactReadySchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactRefinedProjection
import MyLeanRepo.Kakeya.Assouad.WZ1.WellSeparatedProjectionUnion

/-!
# Uniform projection schedule for the refined exact terminal graph
-/

noncomputable section

namespace Kakeya.Assouad

private theorem pureWZ2_terminal_refined_graph_le_root
    {sigma inputLoss delta stickyLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    {selection : PureWZ2TerminalParentYSelection parents}
    {residue : PureWZ2TerminalParentYResidueData selection}
    {retained : PureWZ2TerminalRetainedShadingData residue}
    {sources : PureWZ2TerminalSourceFamily retained}
    {band : PureWZ2TerminalFixedBandSelection sources}
    {phase : PureWZ2TerminalHeightPhaseSelection band}
    {anchored : PureWZ2TerminalAnchoredPieceData phase}
    {prep : PureWZ2TerminalExactGraphPreparation anchored}
    {graphParents : PureWZ2TerminalExactGraphParentData prep}
    {localCells : PureWZ2TerminalExactLocalCellData
      (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
    {first : PureWZ2TerminalExactReadyGraph
      (theoremEta := theoremEta) sharp}
    (data : PureWZ2TerminalExactRefinedReadyGraph first) :
    data.ready.deltaGraph ≤ Real.sqrt delta := by
  rw [data.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale]
  have hrefined : delta / 625 ≤ delta :=
    div_le_self source.extremal.delta_pos.le (by norm_num)
  have hroot : Real.sqrt (delta / 625) ≤ Real.sqrt delta :=
    Real.sqrt_le_sqrt hrefined
  have hdenom : 1 ≤ 5 * Real.sqrt 3 := by
    have hsqrtThree : 1 ≤ Real.sqrt 3 :=
      (Real.one_le_sqrt).2 (by norm_num)
    nlinarith
  exact (div_le_self (Real.sqrt_nonneg _) hdenom).trans hroot

theorem PureWZ2TerminalExactRefinedReadyGraph.source_cost
    {sigma inputLoss delta stickyLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    {residue : PureWZ2TerminalBinParentYResidueData selection}
    {retained : PureWZ2TerminalBinRetainedShadingData residue}
    {sources : PureWZ2TerminalBinSourceFamily retained}
    {band : PureWZ2TerminalBinFixedBandSelection sources}
    {phase : PureWZ2TerminalBinHeightPhaseSelection band}
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    {graphParents : PureWZ2TerminalExactGraphParentData prep}
    {localCells : PureWZ2TerminalExactLocalCellData
      (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
    {first : PureWZ2TerminalExactReadyGraph
      (theoremEta := theoremEta) sharp}
    (data : PureWZ2TerminalExactRefinedReadyGraph first)
    (hinputLoss : 0 ≤ inputLoss) :
    Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN data.ready.deltaGraph (-4 * inputLoss) := by
  apply ENNReal.ofReal_mono
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hdeltaOne : delta ≤ 1 := source.extremal.delta_le_one
  let root := Real.sqrt delta
  have hroot : 0 < root := Real.sqrt_pos.mpr hdelta
  have hrootOne : root ≤ 1 := Real.sqrt_le_one.mpr hdeltaOne
  have hgraph : 0 < data.ready.deltaGraph := data.ready.deltaGraph_pos
  have hgraphRoot : data.ready.deltaGraph ≤ root := by
    rw [data.deltaGraph_eq, first.ready.deltaGraph_eq,
      wz1Lemma23Theorem22Scale]
    have hdenom : 1 ≤ 5 * Real.sqrt 3 := by
      have hsqrtThree : 1 ≤ Real.sqrt 3 :=
        (Real.one_le_sqrt).2 (by norm_num)
      nlinarith
    exact (div_le_self (by positivity : 0 ≤ Real.sqrt delta /
      (5 * Real.sqrt 3)) (by norm_num : 1 ≤ (25 : ℝ))).trans
        (div_le_self (Real.sqrt_nonneg delta) hdenom)
  have hdeltaPower : Real.rpow delta (-inputLoss) =
      Real.rpow root (-2 * inputLoss) := by
    dsimp only [root]
    rw [Real.sqrt_eq_rpow]
    calc
      Real.rpow delta (-inputLoss) =
          Real.rpow delta ((1 / 2 : ℝ) * (-2 * inputLoss)) := by
        congr 1
        ring
      _ = (Real.rpow delta (1 / 2 : ℝ)).rpow (-2 * inputLoss) :=
        Real.rpow_mul hdelta.le _ _
  rw [hdeltaPower]
  calc
    Real.rpow root (-2 * inputLoss) ≤
        Real.rpow root (-4 * inputLoss) :=
      Real.rpow_le_rpow_of_exponent_ge hroot hrootOne (by linarith)
    _ ≤ Real.rpow data.ready.deltaGraph (-4 * inputLoss) :=
      Real.rpow_le_rpow_of_nonpos hgraph hgraphRoot (by linarith)

structure PureWZ2TerminalExactProjectionThreshold
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
  sourceLossCeiling : ℝ
  sourceLossCeiling_pos : 0 < sourceLossCeiling
  gain : 10 * theoremEta + 4 * sourceLossCeiling <
    projectionEta * (sigma - outputLoss / 2)
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  graph_small :
    ∀ delta, 0 < delta → delta ≤ delta₀ →
      wz1Lemma23Theorem22Scale (delta / 625) ≤ reductionDelta₀
  constant_small :
    ∀ delta, 0 < delta → delta ≤ delta₀ →
      (6480000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale (delta / 625))
          (-(projectionEta * (sigma - outputLoss / 2) -
            (10 * theoremEta + 4 * sourceLossCeiling)) / 2)
  popular_constant_small :
    ∀ delta, 0 < delta → delta ≤ delta₀ →
      (25920000000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale (delta / 625))
          (-(projectionEta * (sigma - outputLoss / 2) -
            (10 * theoremEta + 4 * sourceLossCeiling)) / 2)

theorem pureWZ2_terminalExact_projection_threshold
    {sigma outputLoss : ℝ}
    (hsigma : 0 < sigma)
    (houtput : 0 < outputLoss)
    (houtputOne : outputLoss < 1)
    (houtputSigma : outputLoss / 2 < sigma) :
    Nonempty (PureWZ2TerminalExactProjectionThreshold sigma outputLoss) := by
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
  let rawCap := (projectionGap - 10 * theoremEta) / 8
  have hrawCap : 0 < rawCap := by
    dsimp only [rawCap]
    nlinarith
  let sourceLossCeiling := min rawCap (projectionGap / 32)
  have hsourceLossCeiling : 0 < sourceLossCeiling := by
    dsimp only [sourceLossCeiling]
    positivity
  have hgain : 10 * theoremEta + 4 * sourceLossCeiling < projectionGap := by
    have hcap := min_le_left rawCap (projectionGap / 32)
    dsimp only [sourceLossCeiling]
    dsimp only [rawCap] at hcap
    nlinarith
  let gap := projectionGap -
    (10 * theoremEta + 4 * sourceLossCeiling)
  have hgap : 0 < gap := by dsimp only [gap]; linarith
  rcases exists_delta_realRpowENN_bound
      ((25920000000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3))
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      (gamma := gap / 2) (by positivity) with
    ⟨graphDelta₀, hgraphDelta₀, hgraphDelta₀One, hconstant⟩
  let rootTarget := min (1 / 2 : ℝ)
    (min reductionDelta₀ graphDelta₀ * (125 * Real.sqrt 3))
  have hrootTarget : 0 < rootTarget := by
    dsimp only [rootTarget]
    exact lt_min (by norm_num)
      (mul_pos (lt_min hreductionDelta₀ hgraphDelta₀) (by positivity))
  have hrootTargetOne : rootTarget < 1 :=
    (min_le_left _ _).trans_lt (by norm_num)
  rcases exists_delta_rpow_le_single (1 / 2 : ℝ) rootTarget
      (by norm_num)
      hrootTarget hrootTargetOne with
    ⟨delta₀, hdelta₀, hdelta₀One, hroot⟩
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
    sourceLossCeiling := sourceLossCeiling
    sourceLossCeiling_pos := hsourceLossCeiling
    gain := by simpa [projectionGap, sigmaGap] using hgain
    delta₀ := delta₀
    delta₀_pos := hdelta₀
    delta₀_le_one := hdelta₀One
    graph_small := ?_
    constant_small := ?_
    popular_constant_small := ?_ }⟩
  · intro delta hdelta hdeltaSmall
    have hrootBound := hroot delta hdelta hdeltaSmall
    have hpositive : 0 < 125 * Real.sqrt 3 := by positivity
    have hsqrtBound : Real.sqrt delta ≤ rootTarget := by
      simpa [Real.sqrt_eq_rpow] using hrootBound
    have hgraphEq : wz1Lemma23Theorem22Scale (delta / 625) =
        Real.sqrt delta / (125 * Real.sqrt 3) := by
      rw [wz1Lemma23Theorem22Scale, Real.sqrt_div hdelta.le]
      norm_num
      ring
    rw [hgraphEq]
    exact (div_le_iff₀ hpositive).2 (hsqrtBound.trans (by
      calc
        rootTarget ≤
            min reductionDelta₀ graphDelta₀ * (125 * Real.sqrt 3) :=
          min_le_right _ _
        min reductionDelta₀ graphDelta₀ * (125 * Real.sqrt 3) ≤
            reductionDelta₀ * (125 * Real.sqrt 3) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hpositive.le
        _ = _ := rfl))
  · intro delta hdelta hdeltaSmall
    have hgraphPos : 0 < wz1Lemma23Theorem22Scale (delta / 625) := by
      dsimp only [wz1Lemma23Theorem22Scale]
      positivity
    have hgraphSmall :
        wz1Lemma23Theorem22Scale (delta / 625) ≤ graphDelta₀ := by
      have hrootBound := hroot delta hdelta hdeltaSmall
      have hpositive : 0 < 125 * Real.sqrt 3 := by positivity
      have hsqrtBound : Real.sqrt delta ≤ rootTarget := by
        simpa [Real.sqrt_eq_rpow] using hrootBound
      have hgraphEq : wz1Lemma23Theorem22Scale (delta / 625) =
          Real.sqrt delta / (125 * Real.sqrt 3) := by
        rw [wz1Lemma23Theorem22Scale, Real.sqrt_div hdelta.le]
        norm_num
        ring
      rw [hgraphEq]
      exact (div_le_iff₀ hpositive).2 (hsqrtBound.trans (by
        calc
          rootTarget ≤
              min reductionDelta₀ graphDelta₀ * (125 * Real.sqrt 3) :=
            min_le_right _ _
          min reductionDelta₀ graphDelta₀ * (125 * Real.sqrt 3) ≤
              graphDelta₀ * (125 * Real.sqrt 3) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hpositive.le
          _ = _ := rfl))
    have hraw := hconstant _ hgraphPos hgraphSmall
    have hexponent : -(gap / 2) =
        -(projectionEta * (sigma - outputLoss / 2) -
          (10 * theoremEta + 4 * sourceLossCeiling)) / 2 := by
      dsimp only [gap, projectionGap, sigmaGap]
      ring
    rw [hexponent] at hraw
    exact (mul_le_mul_right'
      (by norm_num : (6480000000 : ENNReal) ≤ 25920000000000)
      (ENNReal.ofReal (Real.sqrt 3))).trans hraw
  · intro delta hdelta hdeltaSmall
    have hgraphPos : 0 < wz1Lemma23Theorem22Scale (delta / 625) := by
      dsimp only [wz1Lemma23Theorem22Scale]
      positivity
    have hgraphSmall :
        wz1Lemma23Theorem22Scale (delta / 625) ≤ graphDelta₀ := by
      have hrootBound := hroot delta hdelta hdeltaSmall
      have hpositive : 0 < 125 * Real.sqrt 3 := by positivity
      have hsqrtBound : Real.sqrt delta ≤ rootTarget := by
        simpa [Real.sqrt_eq_rpow] using hrootBound
      have hgraphEq : wz1Lemma23Theorem22Scale (delta / 625) =
          Real.sqrt delta / (125 * Real.sqrt 3) := by
        rw [wz1Lemma23Theorem22Scale, Real.sqrt_div hdelta.le]
        norm_num
        ring
      rw [hgraphEq]
      exact (div_le_iff₀ hpositive).2 (hsqrtBound.trans (by
        calc
          rootTarget ≤
              min reductionDelta₀ graphDelta₀ * (125 * Real.sqrt 3) :=
            min_le_right _ _
          min reductionDelta₀ graphDelta₀ * (125 * Real.sqrt 3) ≤
              graphDelta₀ * (125 * Real.sqrt 3) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hpositive.le
          _ = _ := rfl))
    have hraw := hconstant _ hgraphPos hgraphSmall
    have hexponent : -(gap / 2) =
        -(projectionEta * (sigma - outputLoss / 2) -
          (10 * theoremEta + 4 * sourceLossCeiling)) / 2 := by
      dsimp only [gap, projectionGap, sigmaGap]
      ring
    rwa [hexponent] at hraw

theorem PureWZ2CommonEndpointProjectionLongData.constant_absorb_ten
    {rho theoremEta epsilon budgetFactor projectionEta deltaAD
      sigma inputLoss sourceCostLoss delta : ℝ}
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {unitBall : WZ1Lemma23UnitBallGraph
      rho sourceF sourceG₁ sourceG₂ sourceH}
    {ready : WZ1Lemma23Theorem22ReadyGraph rho theoremEta unitBall}
    (data : PureWZ2CommonEndpointProjectionLongData
      (epsilon := epsilon) ready budgetFactor projectionEta)
    (hdeltaAD : deltaAD = ready.deltaGraph / 5)
    (htheoremEta : 0 ≤ theoremEta)
    (hdeltaGraphOne : ready.deltaGraph ≤ 1)
    (hsourceCost :
      Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN ready.deltaGraph (-sourceCostLoss))
    (hsourceCostLoss : 0 ≤ sourceCostLoss)
    (hgain : 10 * theoremEta + sourceCostLoss <
      projectionEta * (sigma - epsilon / 2))
    (hdeltaGraphStrict : ready.deltaGraph < 1)
    (hconstantSmall :
      (6480000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN ready.deltaGraph
          (-(projectionEta * (sigma - epsilon / 2) -
            (10 * theoremEta + sourceCostLoss)) / 2)) :
    let C : ENNReal := 10 *
      ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
        (10 * Kakeya.realRpowENN delta (-inputLoss)))
    ((5 * C) * ENNReal.ofReal
          (max 1 (10 * (data.long.affine.dotScale * deltaAD) /
            (ready.deltaGraph / 2)))) * 100 *
        Kakeya.realRpowENN (ready.deltaGraph / 2)
          (data.long.projectionEta * (sigma - epsilon / 2)) < 1 := by
  dsimp only
  have hmax := data.max_factor_bound hdeltaAD htheoremEta hdeltaGraphOne
  have hprojectionEq : data.long.projectionEta = projectionEta :=
    data.projectionEta_eq
  have hhalfPower :
      Kakeya.realRpowENN (ready.deltaGraph / 2)
          (data.long.projectionEta * (sigma - epsilon / 2)) ≤
        Kakeya.realRpowENN ready.deltaGraph
          (projectionEta * (sigma - epsilon / 2)) := by
    rw [hprojectionEq]
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow
    · exact (div_nonneg ready.deltaGraph_pos.le (by norm_num))
    · exact div_le_self ready.deltaGraph_pos.le (by norm_num)
    · have hprojection : 0 < projectionEta := by
        rw [← hprojectionEq]
        exact data.long.projectionEta_pos
      have hsigmaGap : 0 < sigma - epsilon / 2 := by
        by_contra hnot
        have hnonpos : projectionEta * (sigma - epsilon / 2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hprojection.le (le_of_not_gt hnot)
        have hleftNonneg : 0 ≤ 10 * theoremEta + sourceCostLoss := by
          positivity
        linarith
      positivity
  have hnegativeCombine :
      Kakeya.realRpowENN ready.deltaGraph (-sourceCostLoss) *
          Kakeya.realRpowENN ready.deltaGraph (-10 * theoremEta) =
        Kakeya.realRpowENN ready.deltaGraph
          (-(10 * theoremEta + sourceCostLoss)) := by
    rw [← realRpowENN_add ready.deltaGraph_pos]
    congr 1
    ring
  have htotalCombine :
      Kakeya.realRpowENN ready.deltaGraph
          (-(10 * theoremEta + sourceCostLoss)) *
        Kakeya.realRpowENN ready.deltaGraph
          (projectionEta * (sigma - epsilon / 2)) =
      Kakeya.realRpowENN ready.deltaGraph
        (projectionEta * (sigma - epsilon / 2) -
          (10 * theoremEta + sourceCostLoss)) := by
    rw [← realRpowENN_add ready.deltaGraph_pos]
    congr 1
    ring
  let gap := projectionEta * (sigma - epsilon / 2) -
    (10 * theoremEta + sourceCostLoss)
  have hgap : 0 < gap := by dsimp only [gap]; linarith
  have hhalfGap : 0 < gap / 2 := by positivity
  have hpowerLt : Kakeya.realRpowENN ready.deltaGraph (gap / 2) < 1 := by
    have h := realRpowENN_strict_antitone
      ready.deltaGraph_pos hdeltaGraphStrict hhalfGap
    simpa [Kakeya.realRpowENN] using h
  have hscaled :
      (5 * (10 * ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
          (10 * Kakeya.realRpowENN delta (-inputLoss)))) *
          ENNReal.ofReal
            (max 1 (10 * (data.long.affine.dotScale * deltaAD) /
              (ready.deltaGraph / 2)))) * 100 *
          Kakeya.realRpowENN (ready.deltaGraph / 2)
            (data.long.projectionEta * (sigma - epsilon / 2)) ≤
        (6480000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
          Kakeya.realRpowENN ready.deltaGraph
            (-(10 * theoremEta + sourceCostLoss)) *
          Kakeya.realRpowENN ready.deltaGraph
            (projectionEta * (sigma - epsilon / 2)) := by
    calc
      _ ≤ (5 * (10 * ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
            (10 * Kakeya.realRpowENN ready.deltaGraph (-sourceCostLoss))))) *
            (8 * Kakeya.realRpowENN ready.deltaGraph (-10 * theoremEta)) *
            100 * Kakeya.realRpowENN ready.deltaGraph
              (projectionEta * (sigma - epsilon / 2)) := by
        gcongr
      _ = (6480000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
            Kakeya.realRpowENN ready.deltaGraph
              (-(10 * theoremEta + sourceCostLoss)) *
            Kakeya.realRpowENN ready.deltaGraph
              (projectionEta * (sigma - epsilon / 2)) := by
        calc
          _ = (6480000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
              (Kakeya.realRpowENN ready.deltaGraph (-sourceCostLoss) *
                Kakeya.realRpowENN ready.deltaGraph (-10 * theoremEta)) *
              Kakeya.realRpowENN ready.deltaGraph
                (projectionEta * (sigma - epsilon / 2)) := by ring
          _ = _ := by rw [hnegativeCombine]
  have hupper :
      (6480000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
          Kakeya.realRpowENN ready.deltaGraph
            (-(10 * theoremEta + sourceCostLoss)) *
          Kakeya.realRpowENN ready.deltaGraph
            (projectionEta * (sigma - epsilon / 2)) ≤
        Kakeya.realRpowENN ready.deltaGraph (gap / 2) := by
    calc
      _ = (6480000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
          (Kakeya.realRpowENN ready.deltaGraph
              (-(10 * theoremEta + sourceCostLoss)) *
            Kakeya.realRpowENN ready.deltaGraph
              (projectionEta * (sigma - epsilon / 2))) := by ring
      _ = (6480000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
          Kakeya.realRpowENN ready.deltaGraph gap := by
        rw [htotalCombine]
      _ ≤ Kakeya.realRpowENN ready.deltaGraph (gap / 2) := by
        calc
          (6480000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
                Kakeya.realRpowENN ready.deltaGraph gap ≤
              Kakeya.realRpowENN ready.deltaGraph (-(gap / 2)) *
                Kakeya.realRpowENN ready.deltaGraph gap := by
            gcongr
            have hneg : -(gap / 2) = -gap / 2 := by ring
            rw [hneg]
            exact hconstantSmall
          _ = Kakeya.realRpowENN ready.deltaGraph (gap / 2) := by
            rw [← realRpowENN_add ready.deltaGraph_pos]
            congr 1
            ring
  exact hscaled.trans_lt (hupper.trans_lt hpowerLt)

theorem PureWZ2TerminalExactProjectionThreshold.alternativeA
    {sigma outputLoss inputLoss delta stickyLoss eta : ℝ}
    (self : PureWZ2TerminalExactProjectionThreshold sigma outputLoss)
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    {selection : PureWZ2TerminalParentYSelection parents}
    {residue : PureWZ2TerminalParentYResidueData selection}
    {retained : PureWZ2TerminalRetainedShadingData residue}
    {sources : PureWZ2TerminalSourceFamily retained}
    {band : PureWZ2TerminalFixedBandSelection sources}
    {phase : PureWZ2TerminalHeightPhaseSelection band}
    {anchored : PureWZ2TerminalAnchoredPieceData phase}
    {prep : PureWZ2TerminalExactGraphPreparation anchored}
    {graphParents : PureWZ2TerminalExactGraphParentData prep}
    {localCells : PureWZ2TerminalExactLocalCellData
      (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
    {first : PureWZ2TerminalExactReadyGraph
      (theoremEta := self.theoremEta) sharp}
    (data : PureWZ2TerminalExactRefinedReadyGraph first)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (houtput : 0 < outputLoss) (houtputSigma : outputLoss / 2 < sigma)
    (hinput : 0 ≤ inputLoss) (hinputCeiling : inputLoss ≤ self.sourceLossCeiling)
    (hdeltaSmall : delta ≤ self.delta₀) :
    WZ1Proposition8_9AlternativeAUnion
      data.ready.deltaGraph outputLoss
      data.common.F data.common.G₁ data.common.G₁ := by
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hgraphSmall : data.ready.deltaGraph ≤ self.reductionDelta₀ := by
    rw [data.ready.deltaGraph_eq]
    exact self.graph_small delta hdelta hdeltaSmall
  have hsourceCost := data.source_cost hinput
  have hsourceCostLoss : 0 ≤ 4 * inputLoss := by positivity
  have hgain : 10 * self.theoremEta + 4 * inputLoss <
      self.projectionEta * (sigma - outputLoss / 2) := by
    calc
      10 * self.theoremEta + 4 * inputLoss ≤
          10 * self.theoremEta + 4 * self.sourceLossCeiling := by
        gcongr
      _ < self.projectionEta * (sigma - outputLoss / 2) := self.gain
  have hgraphOne : data.ready.deltaGraph ≤ 1 := by
    rw [data.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale]
    have hrefinedOne : delta / 625 ≤ 1 := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 625)).2
      nlinarith [source.extremal.delta_le_one]
    have hroot := Real.sqrt_le_one.mpr hrefinedOne
    have hdenom : 1 ≤ 5 * Real.sqrt 3 := by
      have hsqrtThree : 1 ≤ Real.sqrt 3 :=
        (Real.one_le_sqrt).2 (by norm_num)
      nlinarith
    exact (div_le_self (Real.sqrt_nonneg _) hdenom).trans hroot
  have hgraphStrict : data.ready.deltaGraph < 1 := by
    rw [data.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale]
    have hrefinedPos : 0 < delta / 625 := by positivity
    have hrootPos : 0 < Real.sqrt (delta / 625) :=
      Real.sqrt_pos.mpr hrefinedPos
    have hdenom : 1 < 5 * Real.sqrt 3 := by
      have hsqrtThree : 1 ≤ Real.sqrt 3 :=
        (Real.one_le_sqrt).2 (by norm_num)
      nlinarith
    exact (div_lt_self hrootPos hdenom).trans_le
      (Real.sqrt_le_one.mpr (by
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 625)).2
        nlinarith [source.extremal.delta_le_one]))
  have hconstantSmall :
      (6480000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN data.ready.deltaGraph
          (-(self.projectionEta * (sigma - outputLoss / 2) -
            (10 * self.theoremEta + 4 * inputLoss)) / 2) := by
    have hceiling := self.constant_small delta hdelta hdeltaSmall
    have hscaleOne : wz1Lemma23Theorem22Scale (delta / 625) ≤ 1 := by
      rw [← data.ready.deltaGraph_eq]
      exact hgraphOne
    rw [data.ready.deltaGraph_eq]
    apply hceiling.trans
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow_of_exponent_ge
    · dsimp only [wz1Lemma23Theorem22Scale]
      positivity
    · exact hscaleOne
    · have hactualGap :
          self.projectionEta * (sigma - outputLoss / 2) -
              (10 * self.theoremEta + 4 * inputLoss) ≥
            self.projectionEta * (sigma - outputLoss / 2) -
              (10 * self.theoremEta + 4 * self.sourceLossCeiling) := by
        linarith
      nlinarith
  apply data.projection_alternative_a houtput hsigma hsigmaOne houtputSigma
      self.reduction hgraphSmall self.theoremEta_pos.le
      self.theoremEta_small
  intro strongLong
  have hsourceCost' :
      Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN data.ready.deltaGraph (-(4 * inputLoss)) := by
    simpa only [show -(4 * inputLoss) = -4 * inputLoss by ring] using hsourceCost
  exact strongLong.constant_absorb_ten rfl self.theoremEta_pos.le
    hgraphOne hsourceCost' hsourceCostLoss hgain hgraphStrict hconstantSmall

end Kakeya.Assouad

end
