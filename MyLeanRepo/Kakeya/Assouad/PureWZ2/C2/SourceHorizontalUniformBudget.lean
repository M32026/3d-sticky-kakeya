import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalAnalyticSchedule
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GeometricInput
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26DeltaBudget

/-!
# Uniform analytic budget for the pure source-horizontal route

The projection theorem first chooses `theoremEta`.  This module then spends
three equal small portions on the window-volume, AD-constant, and finite-log
losses and chooses one scale threshold valid for every dependent pipeline.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2SourceHorizontalAnalyticBudget
    (theoremEta : ℝ) where
  volumeLoss : ℝ
  constantLoss : ℝ
  extraLoss : ℝ
  volumeLoss_pos : 0 < volumeLoss
  constantLoss_pos : 0 < constantLoss
  extraLoss_pos : 0 < extraLoss
  edge_budget :
    8 * ((volumeLoss + extraLoss) + constantLoss) < theoremEta

/-- Equal allocation leaves a fixed positive margin in the edge exponent. -/
noncomputable def pureWZ2SourceHorizontalAnalyticBudget
    (theoremEta : ℝ) (htheoremEta : 0 < theoremEta) :
    PureWZ2SourceHorizontalAnalyticBudget theoremEta where
  volumeLoss := theoremEta / 64
  constantLoss := theoremEta / 64
  extraLoss := theoremEta / 64
  volumeLoss_pos := by positivity
  constantLoss_pos := by positivity
  extraLoss_pos := by positivity
  edge_budget := by linarith

structure PureWZ2SourceHorizontalAnalyticThreshold
    (theoremEta : ℝ) where
  budget : PureWZ2SourceHorizontalAnalyticBudget theoremEta
  rho0 : ℝ
  rho0_pos : 0 < rho0
  rho0_le_one : rho0 ≤ 1
  edge :
    ∀ rho : ℝ, 0 < rho → rho ≤ rho0 →
      Real.rpow (wz1Lemma23Theorem22Scale rho)
          (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow rho
            (-3 / 2 + 4 * budget.volumeLoss +
              4 * budget.constantLoss + 4 * budget.extraLoss)
  katzTao :
    ∀ rho : ℝ, 0 < rho → rho ≤ rho0 →
      (4 : ENNReal) ≤
        Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale rho) (-theoremEta)
  extraScalar :
    ∀ rho graphScale : ℝ, 0 < rho → rho ≤ rho0 →
      graphScale = 256 * rho →
      920 * (Real.log (1 / graphScale) + 1) ^ 2 ≤
        Real.rpow graphScale (-budget.extraLoss)
  extra :
    ∀ rho : ℝ, 0 < rho → rho ≤ rho0 →
      ∀ {sigma inputLoss delta middleLoss stickyLoss normalEta : ℝ}
        {logExponent : ℕ}
        {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
        (twoScale : PureWZ2OneScaleTwoScaleStickyData
          source rho middleLoss stickyLoss logExponent)
        (pipeline : PureWZ2SourceHorizontalPipelineData
          (normalEta := normalEta) twoScale),
        (pipeline.graph.residue.extraCost : ℝ) ≤
          Real.rpow pipeline.prep.graphScale (-budget.extraLoss)

/-- One threshold simultaneously supplies the edge, Katz--Tao, and finite-log
absorptions needed by every source-horizontal pipeline. -/
theorem pureWZ2_sourceHorizontal_analytic_threshold
    {theoremEta : ℝ} (htheoremEta : 0 < theoremEta) :
    Nonempty (PureWZ2SourceHorizontalAnalyticThreshold theoremEta) := by
  let budget :=
    pureWZ2SourceHorizontalAnalyticBudget theoremEta htheoremEta
  rcases wz1_lemma23_theorem22_absorption
      theoremEta (budget.volumeLoss + budget.extraLoss)
      budget.constantLoss htheoremEta budget.edge_budget with
    ⟨edgeRho0, hedgeRho0, hedgeRho0One, hedge⟩
  rcases pureWZ2_sourceHorizontal_extraCost_schedule
      budget.extraLoss_pos with
    ⟨extraRho0, hextraRho0, hextraRho0One, hextra⟩
  rcases pureWZ2_sourceHorizontal_extraCost_scalar_schedule
      budget.extraLoss_pos with
    ⟨scalarRho0, hscalarRho0, hscalarRho0One, hscalar⟩
  let rho0 := min edgeRho0 (min scalarRho0 extraRho0)
  refine ⟨{
    budget := budget
    rho0 := rho0
    rho0_pos := lt_min hedgeRho0 (lt_min hscalarRho0 hextraRho0)
    rho0_le_one := (min_le_left _ _).trans hedgeRho0One
    edge := ?_
    katzTao := ?_
    extraScalar := ?_
    extra := ?_ }⟩
  · intro rho hrho hrhoSmall
    have h := hedge rho hrho
      (hrhoSmall.trans (min_le_left _ _))
    simpa only [show
      -3 / 2 + 4 * (budget.volumeLoss + budget.extraLoss) +
          4 * budget.constantLoss =
        -3 / 2 + 4 * budget.volumeLoss +
          4 * budget.constantLoss + 4 * budget.extraLoss by ring]
      using h.edge
  · intro rho hrho hrhoSmall
    exact (hedge rho hrho
      (hrhoSmall.trans (min_le_left _ _))).katzTao
  · intro rho graphScale hrho hrhoSmall hgraphScale
    exact hscalar rho graphScale hrho
      (hrhoSmall.trans
        ((min_le_right _ _).trans (min_le_left _ _)))
      hgraphScale
  · intro rho hrho hrhoSmall sigma inputLoss delta middleLoss
      stickyLoss normalEta logExponent source twoScale pipeline
    exact hextra rho hrho
      (hrhoSmall.trans
        ((min_le_right _ _).trans (min_le_right _ _)))
      sigma inputLoss delta middleLoss stickyLoss normalEta theoremEta
      logExponent source twoScale pipeline

/-- Fixed-scale geometric inequalities used before the graph is constructed. -/
structure PureWZ2SourceHorizontalGeometricThreshold
    (sigma normalEta finalLoss : ℝ) where
  rho0 : ℝ
  rho0_pos : 0 < rho0
  rho0_le_one : rho0 ≤ 1
  certificate : ∀ rho, 0 < rho → rho ≤ rho0 → 4 * rho ≤ 1
  graph : ∀ rho, 0 < rho → rho ≤ rho0 → 256 * rho ≤ 1
  heightAbsorb : ∀ rho, 0 < rho → rho ≤ rho0 →
    256 * rho + 2 * Real.sqrt rho ≤ 16 * Real.sqrt rho
  scale : ∀ rho, 0 < rho → rho ≤ rho0 → 5 * (256 * rho) ≤ 1
  margin : ∀ rho, 0 < rho → rho ≤ rho0 → 4 * rho ≤ Real.sqrt rho
  planar : ∀ rho, 0 < rho → rho ≤ rho0 →
    32 * Real.rpow (4 * rho) normalEta ≤ 1
  root : ∀ rho, 0 < rho → rho ≤ rho0 →
    20 * Real.sqrt (4 * rho) ≤ 1
  localization : ∀ rho, 0 < rho → rho ≤ rho0 →
    Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
      Real.sqrt (4 * rho) / 14
  length : ∀ rho, 0 < rho → rho ≤ rho0 →
    Real.rpow (5 * (256 * rho)) (1 / 2 + finalLoss) ≤
      Real.sqrt rho

/-- All fixed-factor geometric losses are absorbed at one sufficiently small
internal sticky scale. -/
theorem pureWZ2_sourceHorizontal_geometric_threshold
    {sigma normalEta finalLoss : ℝ}
    (hsigma : 0 < sigma)
    (hnormalEta : 0 < normalEta)
    (hnormalEtaSigma : 8 * normalEta < sigma)
    (hfinal : 0 < finalLoss) :
    Nonempty
      (PureWZ2SourceHorizontalGeometricThreshold
        sigma normalEta finalLoss) := by
  let localExp : ℝ := 1 / 2 - 4 * normalEta / sigma
  have hlocalExp : 0 < localExp := by
    dsimp only [localExp]
    have hsigmaNe : sigma ≠ 0 := hsigma.ne'
    rw [sub_pos, div_lt_iff₀ hsigma]
    nlinarith
  rcases exists_delta_rpow_le_single normalEta (1 / 128)
      hnormalEta (by norm_num) (by norm_num) with
    ⟨planarScale0, hplanarScale0, hplanarScale0One, hplanar⟩
  rcases exists_delta_rpow_le_single (1 / 2 : ℝ) (1 / 40)
      (by norm_num) (by norm_num) (by norm_num) with
    ⟨rootScale0, hrootScale0, hrootScale0One, hroot⟩
  rcases exists_delta_rpow_le_single localExp (1 / 14)
      hlocalExp (by norm_num) (by norm_num) with
    ⟨localScale0, hlocalScale0, hlocalScale0One, hlocal⟩
  rcases exists_delta_rpow_le_single finalLoss (1 / 36)
      hfinal (by norm_num) (by norm_num) with
    ⟨lengthScale0, hlengthScale0, hlengthScale0One, hlength⟩
  let rho0 := min (1 / 5120 : ℝ)
    (min (planarScale0 / 4)
      (min (rootScale0 / 4)
        (min (localScale0 / 4) (lengthScale0 / 1280))))
  have hrho0 : 0 < rho0 := by
    dsimp only [rho0]
    positivity
  have hrho0One : rho0 ≤ 1 := by
    exact (min_le_left _ _).trans (by norm_num)
  refine ⟨{
    rho0 := rho0
    rho0_pos := hrho0
    rho0_le_one := hrho0One
    certificate := ?_
    graph := ?_
    heightAbsorb := ?_
    scale := ?_
    margin := ?_
    planar := ?_
    root := ?_
    localization := ?_
    length := ?_ }⟩
  · intro rho hrho hrhoSmall
    have hsmall : rho ≤ 1 / 5120 :=
      hrhoSmall.trans (min_le_left _ _)
    linarith
  · intro rho hrho hrhoSmall
    have hsmall : rho ≤ 1 / 5120 :=
      hrhoSmall.trans (min_le_left _ _)
    linarith
  · intro rho hrho hrhoSmall
    have hsmall : rho ≤ 1 / 5120 :=
      hrhoSmall.trans (min_le_left _ _)
    have hsqrtSq : (Real.sqrt rho) ^ 2 = rho :=
      Real.sq_sqrt hrho.le
    have hsqrt : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
    nlinarith
  · intro rho hrho hrhoSmall
    have hsmall : rho ≤ 1 / 5120 :=
      hrhoSmall.trans (min_le_left _ _)
    linarith
  · intro rho hrho hrhoSmall
    have hsmall : rho ≤ 1 / 5120 :=
      hrhoSmall.trans (min_le_left _ _)
    have hsqrtSq : (Real.sqrt rho) ^ 2 = rho :=
      Real.sq_sqrt hrho.le
    have hsqrt : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
    nlinarith
  · intro rho hrho hrhoSmall
    have hfour : 4 * rho ≤ planarScale0 := by
      have hsmall : rho ≤ planarScale0 / 4 :=
        hrhoSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
      linarith
    have hpow := hplanar (4 * rho) (by positivity) hfour
    nlinarith
  · intro rho hrho hrhoSmall
    have hfour : 4 * rho ≤ rootScale0 := by
      have hsmall : rho ≤ rootScale0 / 4 :=
        hrhoSmall.trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _)))
      linarith
    have hpow := hroot (4 * rho) (by positivity) hfour
    have hrpowHalf :
        Real.rpow (4 * rho) (1 / 2 : ℝ) = Real.sqrt (4 * rho) := by
      exact (Real.sqrt_eq_rpow (4 * rho)).symm
    have hsqrt : Real.sqrt (4 * rho) ≤ 1 / 40 := by
      rw [← hrpowHalf]
      exact hpow
    calc
      20 * Real.sqrt (4 * rho) ≤ 20 * (1 / 40 : ℝ) := by
        gcongr
      _ ≤ 1 := by norm_num
  · intro rho hrho hrhoSmall
    have hfour : 4 * rho ≤ localScale0 := by
      have hsmall : rho ≤ localScale0 / 4 :=
        hrhoSmall.trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_left _ _))))
      linarith
    have hpow := hlocal (4 * rho) (by positivity) hfour
    have hrpowHalf :
        Real.rpow (4 * rho) (1 / 2 : ℝ) = Real.sqrt (4 * rho) := by
      exact (Real.sqrt_eq_rpow (4 * rho)).symm
    have hsplit :
        Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) =
          Real.sqrt (4 * rho) *
            Real.rpow (4 * rho) localExp := by
      calc
        Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) =
            Real.rpow (4 * rho) ((1 / 2 : ℝ) + localExp) := by
          congr 1
          dsimp only [localExp]
          ring
        _ = Real.rpow (4 * rho) (1 / 2 : ℝ) *
            Real.rpow (4 * rho) localExp :=
          Real.rpow_add (by positivity) _ _
        _ = Real.sqrt (4 * rho) *
            Real.rpow (4 * rho) localExp := by
          rw [hrpowHalf]
    rw [hsplit]
    calc
      Real.sqrt (4 * rho) * Real.rpow (4 * rho) localExp ≤
          Real.sqrt (4 * rho) * (1 / 14) := by gcongr
      _ = Real.sqrt (4 * rho) / 14 := by ring
  · intro rho hrho hrhoSmall
    have hscaled : 1280 * rho ≤ lengthScale0 := by
      have hsmall : rho ≤ lengthScale0 / 1280 :=
        hrhoSmall.trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_right _ _))))
      linarith
    have hpow := hlength (1280 * rho) (by positivity) hscaled
    have hrpowHalf :
        Real.rpow (1280 * rho) (1 / 2 : ℝ) =
          Real.sqrt (1280 * rho) := by
      exact (Real.sqrt_eq_rpow (1280 * rho)).symm
    have hsplit :
        Real.rpow (1280 * rho) (1 / 2 + finalLoss) =
          Real.sqrt (1280 * rho) *
            Real.rpow (1280 * rho) finalLoss := by
      calc
        Real.rpow (1280 * rho) (1 / 2 + finalLoss) =
            Real.rpow (1280 * rho) (1 / 2 : ℝ) *
              Real.rpow (1280 * rho) finalLoss :=
          Real.rpow_add (by positivity) _ _
        _ = Real.sqrt (1280 * rho) *
            Real.rpow (1280 * rho) finalLoss := by
          rw [hrpowHalf]
    rw [show 5 * (256 * rho) = 1280 * rho by ring, hsplit]
    have hsqrtScale :
        Real.sqrt (1280 * rho) / 36 ≤ Real.sqrt rho := by
      have hsqrtRho : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
      have hsqrtScaled : 0 ≤ Real.sqrt (1280 * rho) :=
        Real.sqrt_nonneg _
      have hsquareRho : (Real.sqrt rho) ^ 2 = rho :=
        Real.sq_sqrt hrho.le
      have hsquareScaled : (Real.sqrt (1280 * rho)) ^ 2 =
          1280 * rho := Real.sq_sqrt (by positivity)
      nlinarith
    calc
      Real.sqrt (1280 * rho) *
            Real.rpow (1280 * rho) finalLoss ≤
          Real.sqrt (1280 * rho) * (1 / 36) := by gcongr
      _ = Real.sqrt (1280 * rho) / 36 := by ring
      _ ≤ Real.sqrt rho := hsqrtScale

end Kakeya.Assouad

end
