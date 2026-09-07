import MyLeanRepo.Kakeya.Assouad.WZ1.IntervalADHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedPreparedGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23PowerEdgeBound

/-!
# Theorem 22 edge threshold for the actual WZ1 Lemma 23 graph

The power-form edge lower bound is

`edgeConstant⁻¹ * rho^(-3/2 + 4*volumeLoss + 4*constantLoss)`.

The final unit-ball graph scale is

`deltaGraph = sqrt rho / (5 * sqrt 3)`.

If `8 * (volumeLoss + constantLoss) < theoremEta`, then after shrinking
`rho` the fixed constants are absorbed and the unit-ball edge set satisfies

`deltaGraph^(theoremEta - 3) <= #H`,

exactly the graph-cardinality premise of the final WZ1 Theorem 22 interface.
-/

namespace Kakeya.Assouad

noncomputable section

/-- The final graph scale after height normalization and common `/5` scaling. -/
def wz1Lemma23Theorem22Scale (rho : ℝ) : ℝ :=
  Real.sqrt rho / (5 * Real.sqrt 3)

/--
Small-scale threshold that absorbs all fixed constants between the power-form
edge lower bound and the final Theorem 22 graph scale.
-/
theorem wz1_lemma23_theorem22_threshold_absorption
    (theoremEta volumeLoss constantLoss : ℝ)
    (hbudget :
      8 * (volumeLoss + constantLoss) < theoremEta) :
    ∃ rho₀ : ℝ, 0 < rho₀ ∧ rho₀ ≤ 1 ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ rho₀ →
        Real.rpow (wz1Lemma23Theorem22Scale rho)
            (theoremEta - 3) ≤
          (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
            Real.rpow rho
              (-3 / 2 + 4 * volumeLoss + 4 * constantLoss) := by
  let sourceExponent :=
    3 / 2 - 4 * (volumeLoss + constantLoss)
  let targetExponent :=
    (3 - theoremEta) / 2
  have htargetSource : targetExponent < sourceExponent := by
    dsimp only [sourceExponent, targetExponent]
    linarith
  let K :=
    wz1Lemma23EdgeConstant *
      Real.rpow (5 * Real.sqrt 3) (3 - theoremEta)
  have hK : 0 < K := by
    exact mul_pos
      (by norm_num [wz1Lemma23EdgeConstant])
      (Real.rpow_pos_of_pos (by positivity) _)
  rcases absorb_rpow_const
      targetExponent sourceExponent K
      htargetSource hK with
    ⟨rho₀, hrho₀, hrho₀One, habsorb⟩
  refine ⟨rho₀, hrho₀, hrho₀One, ?_⟩
  intro rho hrho hrhoSmall
  have habs :=
    habsorb rho hrho hrhoSmall
  have hsqrt :
      Real.sqrt rho = Real.rpow rho (1 / 2 : ℝ) :=
    Real.sqrt_eq_rpow rho
  have hdenomPos : 0 < 5 * Real.sqrt 3 := by positivity
  have hscale :
      Real.rpow (wz1Lemma23Theorem22Scale rho)
          (theoremEta - 3) =
        Real.rpow (5 * Real.sqrt 3) (3 - theoremEta) *
          Real.rpow rho (-targetExponent) := by
    have hdiv :
        Real.rpow
            (Real.rpow rho (1 / 2 : ℝ) /
              (5 * Real.sqrt 3))
            (theoremEta - 3) =
          Real.rpow (Real.rpow rho (1 / 2 : ℝ))
              (theoremEta - 3) /
            Real.rpow (5 * Real.sqrt 3)
              (theoremEta - 3) :=
      Real.div_rpow
        (Real.rpow_nonneg hrho.le (1 / 2 : ℝ))
        hdenomPos.le (theoremEta - 3)
    have hnum :
        Real.rpow (Real.rpow rho (1 / 2 : ℝ))
            (theoremEta - 3) =
          Real.rpow rho ((1 / 2 : ℝ) * (theoremEta - 3)) := by
      exact
        (Real.rpow_mul hrho.le (1 / 2 : ℝ)
          (theoremEta - 3)).symm
    have hden :
        Real.rpow (5 * Real.sqrt 3) (theoremEta - 3) =
          (Real.rpow (5 * Real.sqrt 3)
            (3 - theoremEta))⁻¹ := by
      have hneg :
          theoremEta - 3 = -(3 - theoremEta) := by ring
      rw [hneg]
      exact Real.rpow_neg hdenomPos.le (3 - theoremEta)
    have hnumExp :
        (1 / 2 : ℝ) * (theoremEta - 3) =
          -targetExponent := by
      dsimp only [targetExponent]
      ring
    have hdenRpowPos :
        0 < Real.rpow (5 * Real.sqrt 3)
          (3 - theoremEta) :=
      Real.rpow_pos_of_pos hdenomPos _
    calc
      Real.rpow (wz1Lemma23Theorem22Scale rho)
            (theoremEta - 3)
          = Real.rpow
              (Real.rpow rho (1 / 2 : ℝ) /
                (5 * Real.sqrt 3))
              (theoremEta - 3) := by
            rw [wz1Lemma23Theorem22Scale, hsqrt]
      _ = Real.rpow (Real.rpow rho (1 / 2 : ℝ))
              (theoremEta - 3) /
            Real.rpow (5 * Real.sqrt 3)
              (theoremEta - 3) := hdiv
      _ = Real.rpow rho (-targetExponent) /
            (Real.rpow (5 * Real.sqrt 3)
              (3 - theoremEta))⁻¹ := by
            rw [hnum, hden, hnumExp]
      _ = Real.rpow (5 * Real.sqrt 3) (3 - theoremEta) *
            Real.rpow rho (-targetExponent) := by
          field_simp [hdenRpowPos.ne']
  have hsourceExp :
      -sourceExponent =
        -3 / 2 + 4 * volumeLoss + 4 * constantLoss := by
    dsimp only [sourceExponent]
    ring
  have hconstant :
      K =
        wz1Lemma23EdgeConstant *
          Real.rpow (5 * Real.sqrt 3)
            (3 - theoremEta) := rfl
  rw [hconstant] at habsorb
  have hedgeConstantPos :
      0 < wz1Lemma23EdgeConstant := by
    norm_num [wz1Lemma23EdgeConstant]
  have hdenRpowNonneg :
      0 ≤ Real.rpow (5 * Real.sqrt 3)
        (3 - theoremEta) := by
    exact Real.rpow_nonneg (by positivity) _
  have hrearranged :
      Real.rpow (5 * Real.sqrt 3) (3 - theoremEta) *
          Real.rpow rho (-targetExponent) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow rho
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss) := by
    have hscaled :=
      mul_le_mul_of_nonneg_left habs
        (show 0 ≤ (wz1Lemma23EdgeConstant : ℝ)⁻¹ by
          exact inv_nonneg.mpr
            (by norm_num [wz1Lemma23EdgeConstant]))
    calc
      Real.rpow (5 * Real.sqrt 3) (3 - theoremEta) *
            Real.rpow rho (-targetExponent)
          =
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          (K * Real.rpow rho (-targetExponent)) := by
            rw [hconstant]
            field_simp [hedgeConstantPos.ne']
      _ ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow rho (-sourceExponent) := hscaled
      _ = (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow rho
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss) := by
        rw [hsourceExp]
  rw [hscale]
  exact hrearranged

/--
The final unit-ball graph satisfies the exact edge-cardinality premise of
WZ1 Theorem 22.
-/
theorem WZ1Lemma23LocalizedPreparedGeometry.theorem22_edge_threshold
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C}
    {localized :
      WZ1Lemma23LocalizedGlobalBinPackage windowed.global}
    {residue :
      WZ1Lemma23YResiduePackage windowed.global}
    {localBins :
      WZ1Lemma23LocalBinPackage
        (rho := rho) (sigma := sigma) C windowed.global.cells}
    {prepared :
      WZ1Lemma23LocalizedPreparedPackage
        windowed localized residue localBins}
    (geometry :
      WZ1Lemma23LocalizedPreparedGeometry prepared)
    (theoremEta volumeLoss constantLoss extraLoss rho₀ : ℝ)
    (hrhoSmall : rho ≤ rho₀)
    (habsorb :
      ∀ scale : ℝ, 0 < scale → scale ≤ rho₀ →
        Real.rpow (wz1Lemma23Theorem22Scale scale)
            (theoremEta - 3) ≤
          (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
            Real.rpow scale
              (-3 / 2 + 4 * volumeLoss + 4 * constantLoss +
                4 * extraLoss))
    (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    (hC : 1 ≤ C) (hCtop : C ≠ ⊤)
    (hvolume :
      ENNReal.ofReal
          (Real.rpow rho
            (1 + sigma / 2 + volumeLoss)) ≤
        MeasureTheory.volume Y.union)
    (hCpower :
      C.toReal ≤ Real.rpow rho (-constantLoss))
    (hextraPower :
      (residue.extraCost : ℝ) ≤ Real.rpow rho (-extraLoss)) :
    Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale rho)
        (theoremEta - 3) ≤
      (geometry.unitBall.H.card : ENNReal) := by
  have hrho := windowed.global.rho_pos
  have hpower :=
    prepared.power_edge_bound
      hrho_one hsigma hsigma_one hball
      hC hCtop volumeLoss constantLoss
      extraLoss hvolume hCpower hextraPower
  have hthreshold := habsorb rho hrho hrhoSmall
  have hreal :
      Real.rpow (wz1Lemma23Theorem22Scale rho)
          (theoremEta - 3) ≤
        (prepared.normalized.H.card : ℝ) :=
    hthreshold.trans hpower
  have hscaleNonneg :
      0 ≤ wz1Lemma23Theorem22Scale rho := by
    dsimp only [wz1Lemma23Theorem22Scale]
    positivity
  have hrpowNonneg :
      0 ≤ Real.rpow (wz1Lemma23Theorem22Scale rho)
        (theoremEta - 3) :=
    Real.rpow_nonneg hscaleNonneg _
  have hENN :
      Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale rho)
          (theoremEta - 3) ≤
        (prepared.normalized.H.card : ENNReal) := by
    rw [Kakeya.realRpowENN]
    have hcast :
        (prepared.normalized.H.card : ENNReal) =
          ENNReal.ofReal
            (prepared.normalized.H.card : ℝ) := by
      norm_cast
    rw [hcast]
    exact ENNReal.ofReal_le_ofReal hreal
  rw [geometry.unitBall.edge_card]
  exact hENN

end

end Kakeya.Assouad
