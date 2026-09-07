import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleLossMonotonicity
import MyLeanRepo.Kakeya.Assouad.ExtremalHelpers

/-!
# Strong projection-loss schedule for the Pure C2 argument

The generic common-endpoint reduction records only the fixed budget
`100 * sourceEta ≤ projectionEta`.  The normalized dot map costs a power
depending on `sourceEta`, so the Pure C2 caller needs the same reduction with
an arbitrarily large budget factor selected before the ready graph is built.
-/

noncomputable section

namespace Kakeya.Assouad

/-- A long projection branch together with the stronger caller-selected loss
separation. -/
structure PureWZ2CommonEndpointProjectionLongData
    {rho sourceEta epsilon : ℝ}
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {unitBall :
      WZ1Lemma23UnitBallGraph rho sourceF sourceG₁ sourceG₂ sourceH}
    (ready : WZ1Lemma23Theorem22ReadyGraph rho sourceEta unitBall)
    (budgetFactor projectionEta : ℝ) where
  long : WZ1CommonEndpointProjectionLongData
    (epsilon := epsilon) ready
  projectionEta_eq : long.projectionEta = projectionEta
  factor_budget : budgetFactor * sourceEta ≤ long.projectionEta

/-- In the source-horizontal graph the transported dot-AD scale is exactly
one fifth of the ready graph scale. -/
theorem pureWZ2_sourceHorizontal_dotADScale_eq
    {graphScale theoremEta : ℝ}
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {unitBall : WZ1Lemma23UnitBallGraph
      graphScale sourceF sourceG₁ sourceG₂ sourceH}
    (ready : WZ1Lemma23Theorem22ReadyGraph
      graphScale theoremEta unitBall) :
    Real.sqrt graphScale / (25 * Real.sqrt 3) =
      ready.deltaGraph / 5 := by
  rw [ready.deltaGraph_eq, wz1Lemma23Theorem22Scale]
  field_simp [show Real.sqrt (3 : ℝ) ≠ 0 by positivity]
  ring

/-- The two common-endpoint similarities cost at most the tenth inverse
power of the ready graph scale. -/
theorem PureWZ2CommonEndpointProjectionLongData.dotScale_upper
    {rho sourceEta epsilon budgetFactor projectionEta : ℝ}
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {unitBall :
      WZ1Lemma23UnitBallGraph rho sourceF sourceG₁ sourceG₂ sourceH}
    {ready : WZ1Lemma23Theorem22ReadyGraph rho sourceEta unitBall}
    (data : PureWZ2CommonEndpointProjectionLongData
      (epsilon := epsilon) ready budgetFactor projectionEta) :
    data.long.affine.dotScale ≤
      2 * Real.rpow ready.deltaGraph (-10 * sourceEta) := by
  have hraw := data.long.affine.dotScale_upper
  rw [data.long.raw.threshold_eq] at hraw
  have hthreshold :
      (Real.rpow ready.deltaGraph (5 * sourceEta))⁻¹ ^ 2 =
        Real.rpow ready.deltaGraph (-10 * sourceEta) := by
    have hinverse :
        (Real.rpow ready.deltaGraph (5 * sourceEta))⁻¹ =
          Real.rpow ready.deltaGraph (-5 * sourceEta) := by
      change (ready.deltaGraph ^ (5 * sourceEta))⁻¹ =
        ready.deltaGraph ^ (-5 * sourceEta)
      rw [show -5 * sourceEta = -(5 * sourceEta) by ring]
      exact (Real.rpow_neg ready.deltaGraph_pos.le (5 * sourceEta)).symm
    rw [hinverse, pow_two]
    have hadd := Real.rpow_add ready.deltaGraph_pos
      (-5 * sourceEta) (-5 * sourceEta)
    rw [show -5 * sourceEta + -5 * sourceEta = -10 * sourceEta by ring] at hadd
    exact hadd.symm
  rwa [hthreshold] at hraw

/-- The normalized long-branch scale remains at most one. -/
theorem PureWZ2CommonEndpointProjectionLongData.scaled_dotAD_le_one
    {rho theoremEta epsilon budgetFactor projectionEta deltaAD : ℝ}
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {unitBall : WZ1Lemma23UnitBallGraph
      rho sourceF sourceG₁ sourceG₂ sourceH}
    {ready : WZ1Lemma23Theorem22ReadyGraph rho theoremEta unitBall}
    (data : PureWZ2CommonEndpointProjectionLongData
      (epsilon := epsilon) ready budgetFactor projectionEta)
    (hdeltaAD : deltaAD = ready.deltaGraph / 5)
    (htheoremEta : 0 ≤ theoremEta) (htheoremEtaSmall : theoremEta ≤ 1 / 100)
    (hdeltaGraphOne : ready.deltaGraph ≤ 1) :
    data.long.affine.dotScale * deltaAD ≤ 1 := by
  rw [hdeltaAD]
  have hpower :
      Real.rpow ready.deltaGraph (1 - 10 * theoremEta) ≤ 1 :=
    Real.rpow_le_one ready.deltaGraph_pos.le hdeltaGraphOne (by linarith)
  have hcombine :
      Real.rpow ready.deltaGraph (-10 * theoremEta) *
          ready.deltaGraph =
        Real.rpow ready.deltaGraph (1 - 10 * theoremEta) := by
    have hadd := Real.rpow_add ready.deltaGraph_pos
      (-10 * theoremEta) 1
    calc
      Real.rpow ready.deltaGraph (-10 * theoremEta) * ready.deltaGraph =
          Real.rpow ready.deltaGraph (-10 * theoremEta) *
            Real.rpow ready.deltaGraph 1 := by
        congr 1
        exact (Real.rpow_one _).symm
      _ = Real.rpow ready.deltaGraph (-10 * theoremEta + 1) := hadd.symm
      _ = Real.rpow ready.deltaGraph (1 - 10 * theoremEta) := by
        congr 1
        ring
  calc
    data.long.affine.dotScale * (ready.deltaGraph / 5) ≤
        (2 * Real.rpow ready.deltaGraph (-10 * theoremEta)) *
          (ready.deltaGraph / 5) := by
      exact mul_le_mul_of_nonneg_right data.dotScale_upper
        (div_nonneg ready.deltaGraph_pos.le (by norm_num))
    _ = (2 / 5) * Real.rpow ready.deltaGraph
          (1 - 10 * theoremEta) := by rw [← hcombine]; ring
    _ ≤ (2 / 5) * 1 := by gcongr
    _ ≤ 1 := by norm_num

/-- The max-factor in the transported AD constant loses at most the same
tenth inverse power, up to the absolute constant eight. -/
theorem PureWZ2CommonEndpointProjectionLongData.max_factor_bound
    {rho theoremEta epsilon budgetFactor projectionEta deltaAD : ℝ}
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {unitBall : WZ1Lemma23UnitBallGraph
      rho sourceF sourceG₁ sourceG₂ sourceH}
    {ready : WZ1Lemma23Theorem22ReadyGraph rho theoremEta unitBall}
    (data : PureWZ2CommonEndpointProjectionLongData
      (epsilon := epsilon) ready budgetFactor projectionEta)
    (hdeltaAD : deltaAD = ready.deltaGraph / 5)
    (htheoremEta : 0 ≤ theoremEta)
    (hdeltaGraphOne : ready.deltaGraph ≤ 1) :
    ENNReal.ofReal
        (max 1 (10 * (data.long.affine.dotScale *
          deltaAD) / (ready.deltaGraph / 2))) ≤
      8 * Kakeya.realRpowENN ready.deltaGraph (-10 * theoremEta) := by
  have hdeltaGraph : 0 < ready.deltaGraph := ready.deltaGraph_pos
  rw [hdeltaAD]
  have hratio :
      10 * (data.long.affine.dotScale * (ready.deltaGraph / 5)) /
          (ready.deltaGraph / 2) =
        4 * data.long.affine.dotScale := by
    field_simp [hdeltaGraph.ne']
    ring
  rw [hratio]
  have hpowerOne :
      1 ≤ Real.rpow ready.deltaGraph (-10 * theoremEta) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hdeltaGraph hdeltaGraphOne (by linarith)
  have hmax :
      max 1 (4 * data.long.affine.dotScale) ≤
        8 * Real.rpow ready.deltaGraph (-10 * theoremEta) := by
    apply max_le
    · nlinarith
    · calc
        4 * data.long.affine.dotScale ≤
            4 * (2 * Real.rpow ready.deltaGraph (-10 * theoremEta)) := by
          gcongr
          exact data.dotScale_upper
        _ = 8 * Real.rpow ready.deltaGraph (-10 * theoremEta) := by ring
  rw [Kakeya.realRpowENN]
  have hnonneg : 0 ≤ Real.rpow ready.deltaGraph (-10 * theoremEta) :=
    Real.rpow_nonneg hdeltaGraph.le _
  calc
    ENNReal.ofReal (max 1 (4 * data.long.affine.dotScale)) ≤
        ENNReal.ofReal
          (8 * Real.rpow ready.deltaGraph (-10 * theoremEta)) :=
      ENNReal.ofReal_mono hmax
    _ = 8 * ENNReal.ofReal
          (Real.rpow ready.deltaGraph (-10 * theoremEta)) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num

/-- After the strong loss separation, the normalized dot-AD constant is
absorbed by the projection gain.  The source loss is kept explicit because it
is selected only after the sticky and projection losses have been frozen. -/
theorem PureWZ2CommonEndpointProjectionLongData.constant_absorb
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
      (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN ready.deltaGraph
          (-(projectionEta * (sigma - epsilon / 2) -
            (10 * theoremEta + sourceCostLoss)) / 2)) :
    let C := (16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
      (10 * Kakeya.realRpowENN delta (-inputLoss))
    ((5 * C) * ENNReal.ofReal
          (max 1 (10 * (data.long.affine.dotScale * deltaAD) /
            (ready.deltaGraph / 2)))) * 100 *
        Kakeya.realRpowENN (ready.deltaGraph / 2)
          (data.long.projectionEta * (sigma - epsilon / 2)) < 1 := by
  dsimp only
  have hmax := data.max_factor_bound hdeltaAD htheoremEta hdeltaGraphOne
  have hprojectionEq : data.long.projectionEta = projectionEta :=
    data.projectionEta_eq
  have hbaseHalf : 0 < ready.deltaGraph / 2 :=
    div_pos ready.deltaGraph_pos (by norm_num)
  have hhalfPower :
      Kakeya.realRpowENN (ready.deltaGraph / 2)
          (data.long.projectionEta * (sigma - epsilon / 2)) ≤
        Kakeya.realRpowENN ready.deltaGraph
          (projectionEta * (sigma - epsilon / 2)) := by
    rw [hprojectionEq]
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow
    · positivity
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
  have hpowerLt : Kakeya.realRpowENN ready.deltaGraph (gap / 2) < 1 :=
    by
      have h := realRpowENN_strict_antitone
        ready.deltaGraph_pos hdeltaGraphStrict hhalfGap
      simpa [Kakeya.realRpowENN] using h
  have hscaled :
      (5 * ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
          (10 * Kakeya.realRpowENN delta (-inputLoss))) *
          ENNReal.ofReal
            (max 1 (10 * (data.long.affine.dotScale * deltaAD) /
              (ready.deltaGraph / 2)))) * 100 *
          Kakeya.realRpowENN (ready.deltaGraph / 2)
            (data.long.projectionEta * (sigma - epsilon / 2)) ≤
        (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
          Kakeya.realRpowENN ready.deltaGraph
            (-(10 * theoremEta + sourceCostLoss)) *
          Kakeya.realRpowENN ready.deltaGraph
            (projectionEta * (sigma - epsilon / 2)) := by
    calc
      _ ≤ (5 * ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
            (10 * Kakeya.realRpowENN ready.deltaGraph (-sourceCostLoss)))) *
            (8 * Kakeya.realRpowENN ready.deltaGraph (-10 * theoremEta)) *
            100 *
            Kakeya.realRpowENN ready.deltaGraph
              (projectionEta * (sigma - epsilon / 2)) := by
        gcongr
      _ = (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
            Kakeya.realRpowENN ready.deltaGraph
              (-(10 * theoremEta + sourceCostLoss)) *
            Kakeya.realRpowENN ready.deltaGraph
              (projectionEta * (sigma - epsilon / 2)) := by
        calc
          _ = (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
              (Kakeya.realRpowENN ready.deltaGraph (-sourceCostLoss) *
                Kakeya.realRpowENN ready.deltaGraph (-10 * theoremEta)) *
              Kakeya.realRpowENN ready.deltaGraph
                (projectionEta * (sigma - epsilon / 2)) := by ring
          _ = _ := by rw [hnegativeCombine]
  have hupper :
      (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
          Kakeya.realRpowENN ready.deltaGraph
            (-(10 * theoremEta + sourceCostLoss)) *
          Kakeya.realRpowENN ready.deltaGraph
            (projectionEta * (sigma - epsilon / 2)) ≤
        Kakeya.realRpowENN ready.deltaGraph (gap / 2) := by
    calc
      _ = (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
          (Kakeya.realRpowENN ready.deltaGraph
              (-(10 * theoremEta + sourceCostLoss)) *
            Kakeya.realRpowENN ready.deltaGraph
              (projectionEta * (sigma - epsilon / 2))) := by ring
      _ = (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
          Kakeya.realRpowENN ready.deltaGraph gap := by
        rw [htotalCombine]
      _ ≤ Kakeya.realRpowENN ready.deltaGraph (gap / 2) := by
        calc
          (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
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

/-- Common-endpoint projection reduction with an arbitrary loss-separation
factor.  This is the same geometric reduction as the closed WZ1 theorem; only
the outer choice of `sourceEta` is made smaller. -/
theorem pureWZ2_common_endpoint_projection_reduction
    (hWell : WZ1WellSeparatedProjectionUnionConclusion)
    (budgetFactor epsilon : ℝ)
    (hfactor : 100 ≤ budgetFactor)
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon < 1) :
    ∃ projectionEta sourceEta delta₀ : ℝ,
      0 < projectionEta ∧
      0 < sourceEta ∧ sourceEta ≤ 1 / 100 ∧
      budgetFactor * sourceEta ≤ projectionEta ∧
      0 < delta₀ ∧ delta₀ ≤ 1 / 2 ∧
      ∀ {rho : ℝ}
        {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
        {sourceH : Finset (Point2 × Point2 × Point2)}
        {unitBall :
          WZ1Lemma23UnitBallGraph rho sourceF sourceG₁ sourceG₂ sourceH}
        (ready : WZ1Lemma23Theorem22ReadyGraph rho sourceEta unitBall),
        ready.deltaGraph ≤ delta₀ →
        unitBall.G₂ = unitBall.G₁ →
          WZ1Proposition8_9AlternativeAUnion
              ready.deltaGraph epsilon
              unitBall.F unitBall.G₁ unitBall.G₁ ∨
            Nonempty
              (PureWZ2CommonEndpointProjectionLongData
                (epsilon := epsilon) ready budgetFactor projectionEta) := by
  have hfactorPos : 0 < budgetFactor := lt_of_lt_of_le (by norm_num) hfactor
  have hhalfEpsilon : 0 < epsilon / 2 := by linarith
  rcases hWell (epsilon / 2) hhalfEpsilon with
    ⟨projectionEta, projectionDelta₀, hprojectionEta,
      hprojectionDelta₀, hprojectionDelta₀One, hprojection⟩
  let sourceEta := min (projectionEta / budgetFactor) (1 / 100 : ℝ)
  have hsourceEta : 0 < sourceEta := by
    dsimp only [sourceEta]
    positivity
  have hsourceEtaSmall : sourceEta ≤ 1 / 100 := min_le_right _ _
  have hsourceBudget : budgetFactor * sourceEta ≤ projectionEta := by
    have h := min_le_left (projectionEta / budgetFactor) (1 / 100 : ℝ)
    dsimp only [sourceEta]
    calc
      budgetFactor * sourceEta ≤
          budgetFactor * (projectionEta / budgetFactor) := by gcongr
      _ = projectionEta := by field_simp [hfactorPos.ne']
  have hhundredBudget : 100 * sourceEta ≤ projectionEta := by
    exact (mul_le_mul_of_nonneg_right hfactor hsourceEta.le).trans hsourceBudget
  rcases exists_common_endpoint_parameter_budget sourceEta hsourceEta with
    ⟨budgetDelta₀, hbudgetDelta₀, hbudgetDelta₀Half, hbudget⟩
  let delta₀ := min budgetDelta₀ projectionDelta₀
  have hdelta₀ : 0 < delta₀ := by positivity
  have hdelta₀Half : delta₀ ≤ 1 / 2 :=
    (min_le_left _ _).trans hbudgetDelta₀Half
  refine ⟨projectionEta, sourceEta, delta₀, hprojectionEta,
    hsourceEta, hsourceEtaSmall, hsourceBudget,
    hdelta₀, hdelta₀Half, ?_⟩
  intro rho sourceF sourceG₁ sourceG₂ sourceH unitBall ready
    hdeltaSmall hcommon
  have hdeltaBudget : ready.deltaGraph ≤ budgetDelta₀ :=
    hdeltaSmall.trans (min_le_left _ _)
  have hdeltaProjection : ready.deltaGraph / 2 ≤ projectionDelta₀ := by
    calc
      ready.deltaGraph / 2 ≤ ready.deltaGraph := by
        linarith [ready.deltaGraph_pos]
      _ ≤ projectionDelta₀ := hdeltaSmall.trans (min_le_right _ _)
  rcases hbudget ready.deltaGraph ready.deltaGraph_pos hdeltaBudget with
    ⟨budget⟩
  have hsourceEtaFive : 5 * sourceEta ≤ 1 := by
    linarith [hsourceEtaSmall]
  rcases ready.toRawLocalization hsourceEta hsourceEtaFive hcommon budget with
    ⟨raw⟩
  rcases raw.toAffineNormalization hsourceEta budget with ⟨affine⟩
  rcases affine.toWellSeparatedInput hsourceEta budget with ⟨well⟩
  have hdelta' : 0 < ready.deltaGraph / 2 :=
    div_pos ready.deltaGraph_pos (by norm_num)
  have hdelta'One : ready.deltaGraph / 2 ≤ 1 := by
    exact (div_le_self ready.deltaGraph_pos.le (by norm_num)).trans
      (budget.delta_half.trans (by norm_num))
  have hconstant :
      Kakeya.realRpowENN (ready.deltaGraph / 2) (-budgetFactor * sourceEta) ≤
        Kakeya.realRpowENN (ready.deltaGraph / 2) (-projectionEta) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge
      hdelta' hdelta'One (by linarith [hsourceBudget])
  have hhundredConstant :
      Kakeya.realRpowENN (ready.deltaGraph / 2) (-100 * sourceEta) ≤
        Kakeya.realRpowENN (ready.deltaGraph / 2) (-projectionEta) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge
      hdelta' hdelta'One (by linarith [hhundredBudget])
  have hFfrost : affine.F.IsFrostman (ready.deltaGraph / 2) 1
      (Kakeya.realRpowENN (ready.deltaGraph / 2) (-projectionEta)) := by
    rw [← well.delta_eq]
    exact well.F_frostman.mono
      (by simpa [well.delta_eq] using hhundredConstant)
  have hG₁frost : affine.G₁.IsFrostman (ready.deltaGraph / 2) 1
      (Kakeya.realRpowENN (ready.deltaGraph / 2) (-projectionEta)) := by
    rw [← well.delta_eq]
    exact well.G₁_frostman.mono
      (by simpa [well.delta_eq] using hhundredConstant)
  have hG₂frost : affine.G₂.IsFrostman (ready.deltaGraph / 2) 1
      (Kakeya.realRpowENN (ready.deltaGraph / 2) (-projectionEta)) := by
    rw [← well.delta_eq]
    exact well.G₂_frostman.mono
      (by simpa [well.delta_eq] using hhundredConstant)
  have hdensity :
      Kakeya.realRpowENN (ready.deltaGraph / 2) projectionEta ≤
        Kakeya.realRpowENN (ready.deltaGraph / 2) (100 * sourceEta) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge
      hdelta' hdelta'One hhundredBudget
  have huniform := well.uniform.mono
    (by simpa [well.delta_eq] using hdensity)
  rcases hprojection (ready.deltaGraph / 2) hdelta' hdeltaProjection
      affine.F affine.G₁ affine.G₂
      affine.F_nonempty affine.G₁_nonempty affine.G₂_nonempty
      affine.F_unit affine.G₁_unit affine.G₂_unit
      affine.F_separated affine.G₁_separated affine.G₂_separated
      hFfrost hG₁frost hG₂frost affine.standardSeparation
      well.refinedH huniform with hA | hlong
  · exact Or.inl
      (affine.pullbackAlternativeA budget hepsilon hepsilonOne.le hA)
  · let long : WZ1CommonEndpointProjectionLongData
        (epsilon := epsilon) ready := {
      projectionEta := projectionEta
      projectionEta_pos := hprojectionEta
      sourceEta_budget := hhundredBudget
      raw := raw
      affine := affine
      wellSeparated := well
      long := hlong
    }
    exact Or.inr ⟨{
      long := long
      projectionEta_eq := rfl
      factor_budget := hsourceBudget
    }⟩

/--
Exclude the normalized long branch for the source-carrier graph using the
literal dot-difference AD certificate.  The source loss remains attached to
the original `delta`-scale carrier; no coarse-slope or assigned-fiber
surrogate is introduced.
-/
theorem PureWZ2SourceHorizontalReadyGraph.projection_alternative_a_strong
    {sigma inputLoss delta rho middleLoss stickyLoss outputLoss theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
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
    (data : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp)
    (hepsilon : 0 < outputLoss) (hepsilonOne : outputLoss < 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilonSigma : outputLoss / 2 < sigma)
    {budgetFactor projectionEta reductionDelta₀ sourceCostLoss : ℝ}
    (hreduction :
      ∀ {rho' : ℝ}
        {sourceF' sourceG₁' sourceG₂' : DiscreteSet 2}
        {sourceH' : Finset (Point2 × Point2 × Point2)}
        {unitBall' : WZ1Lemma23UnitBallGraph
          rho' sourceF' sourceG₁' sourceG₂' sourceH'}
        (ready' : WZ1Lemma23Theorem22ReadyGraph
          rho' theoremEta unitBall'),
        ready'.deltaGraph ≤ reductionDelta₀ →
        unitBall'.G₂ = unitBall'.G₁ →
          WZ1Proposition8_9AlternativeAUnion
              ready'.deltaGraph outputLoss
              unitBall'.F unitBall'.G₁ unitBall'.G₁ ∨
            Nonempty (PureWZ2CommonEndpointProjectionLongData
              (epsilon := outputLoss) ready' budgetFactor projectionEta))
    (hdeltaSmall : data.ready.deltaGraph ≤ reductionDelta₀)
    (htheoremEta : 0 ≤ theoremEta)
    (htheoremEtaSmall : theoremEta ≤ 1 / 100)
    (hsourceCost :
      Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN data.ready.deltaGraph (-sourceCostLoss))
    (hsourceCostLoss : 0 ≤ sourceCostLoss)
    (hgain : 10 * theoremEta + sourceCostLoss <
      projectionEta * (sigma - outputLoss / 2))
    (hconstantSmall :
      (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN data.ready.deltaGraph
          (-(projectionEta * (sigma - outputLoss / 2) -
            (10 * theoremEta + sourceCostLoss)) / 2)) :
    WZ1Proposition8_9AlternativeAUnion
      data.ready.deltaGraph outputLoss
      data.common.F data.common.G₁ data.common.G₁ := by
  have hcommon : data.common.G₂ = data.common.G₁ := by
    rw [data.common.G₂_eq, data.common.G₁_eq]
  rcases hreduction data.ready hdeltaSmall hcommon with hA | hB
  · exact hA
  · rcases hB with ⟨strongLong⟩
    exfalso
    let C : ENNReal :=
      (16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
        (10 * Kakeya.realRpowENN delta (-inputLoss))
    have hAD : IsADSet1 (wz1DotDifferenceSet data.common.H)
        (Real.sqrt prep.graphScale / (25 * Real.sqrt 3))
        (1 - sigma) C := by
      simpa [C] using data.dot_difference_ad hsigma hsigmaOne
    have hCtop : C ≠ ⊤ := by
      dsimp only [C]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        (ENNReal.mul_ne_top (by norm_num)
          (by simp [Kakeya.realRpowENN]))
    have hdeltaAD :
        Real.sqrt prep.graphScale / (25 * Real.sqrt 3) =
          data.ready.deltaGraph / 5 :=
      pureWZ2_sourceHorizontal_dotADScale_eq data.ready
    have hdeltaGraphOne : data.ready.deltaGraph ≤ 1 := by
      rw [data.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale]
      have hsqrt := Real.sqrt_le_one.mpr prep.graphScale_one
      have hdenom : 1 ≤ 5 * Real.sqrt 3 := by
        have hsqrt3 : 1 ≤ Real.sqrt 3 :=
          (Real.one_le_sqrt).2 (by norm_num)
        nlinarith
      exact (div_le_self (Real.sqrt_nonneg prep.graphScale) hdenom).trans
        hsqrt
    have hdeltaGraphStrict : data.ready.deltaGraph < 1 := by
      have hsqrt3 : 1 ≤ Real.sqrt 3 :=
        (Real.one_le_sqrt).2 (by norm_num)
      have hdenom : 1 < 5 * Real.sqrt 3 := by nlinarith
      rw [data.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale]
      have hsqrtPos : 0 < Real.sqrt prep.graphScale :=
        Real.sqrt_pos.mpr prep.graphScale_pos
      calc
        Real.sqrt prep.graphScale / (5 * Real.sqrt 3) <
            Real.sqrt prep.graphScale :=
          div_lt_self hsqrtPos hdenom
        _ ≤ 1 := Real.sqrt_le_one.mpr prep.graphScale_one
    have hscaledOne : strongLong.long.affine.dotScale *
        (Real.sqrt prep.graphScale / (25 * Real.sqrt 3)) ≤ 1 :=
      strongLong.scaled_dotAD_le_one hdeltaAD
        htheoremEta htheoremEtaSmall hdeltaGraphOne
    have hconstant := strongLong.constant_absorb hdeltaAD
      htheoremEta hdeltaGraphOne hsourceCost hsourceCostLoss hgain
      hdeltaGraphStrict hconstantSmall
    have htargetPos : 0 < data.ready.deltaGraph / 2 :=
      div_pos data.ready.deltaGraph_pos (by norm_num)
    have htargetOne : data.ready.deltaGraph / 2 ≤ 1 :=
      (div_le_self data.ready.deltaGraph_pos.le (by norm_num)).trans
        hdeltaGraphOne
    have htargetStrict : data.ready.deltaGraph / 2 < 1 := by
      calc
        data.ready.deltaGraph / 2 < data.ready.deltaGraph := by
          linarith [data.ready.deltaGraph_pos]
        _ < 1 := hdeltaGraphStrict
    exact strongLong.long.false_of_dot_ad hAD hCtop hsigma hsigmaOne
      (by positivity) hepsilonSigma hscaledOne
      htargetPos htargetOne htargetStrict hconstant

end Kakeya.Assouad
