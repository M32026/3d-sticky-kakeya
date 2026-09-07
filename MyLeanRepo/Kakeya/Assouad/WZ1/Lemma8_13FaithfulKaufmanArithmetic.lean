import MyLeanRepo.Kakeya.Assouad.WZ1.AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulSanity

/-!
# Kaufman-input arithmetic for the faithful PDF Lemma 8.13 freeze

This module verifies the three loss absorptions used after the actual
representative refinement:

* `delta^eta / 256` weakens to `delta^normalizedEta`;
* the Lemma 48 logarithmic Frostman loss is absorbed; and
* the cardinality-gated unit-circle Frostman constant is absorbed.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Exponent spent by the affine active-`F` Frostman estimate. -/
def wz1Lemma8_13FaithfulFineExponent (epsilon : ℝ) : ℝ :=
  2 * wz1Lemma8_13FaithfulEta epsilon +
    wz1Lemma8_13FaithfulEpsilonOne epsilon

/-- Exponent spent by the final radial-direction cardinality estimate. -/
def wz1Lemma8_13FaithfulDirectionExponent (epsilon : ℝ) : ℝ :=
  4 * wz1Lemma8_13FaithfulEta epsilon +
    2 * wz1Lemma8_13FaithfulEpsilonOne epsilon

/-- The Lemma 48 logarithmic loss has a positive remaining exponent budget. -/
lemma wz1Lemma8_13_fine_exponent_gap
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 <
      wz1Lemma8_13FaithfulNormalizedEta epsilon -
        wz1Lemma8_13FaithfulFineExponent epsilon := by
  dsimp only [wz1Lemma8_13FaithfulNormalizedEta,
    wz1Lemma8_13FaithfulFineExponent,
    wz1Lemma8_13FaithfulEta,
    wz1Lemma8_13FaithfulEpsilonOne]
  nlinarith [sq_pos_of_pos hepsilon]

/-- The radial-direction constant has a positive remaining exponent budget. -/
lemma wz1Lemma8_13_direction_exponent_gap
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 <
      wz1Lemma8_13FaithfulNormalizedEta epsilon -
        wz1Lemma8_13FaithfulDirectionExponent epsilon := by
  dsimp only [wz1Lemma8_13FaithfulNormalizedEta,
    wz1Lemma8_13FaithfulDirectionExponent,
    wz1Lemma8_13FaithfulEta,
    wz1Lemma8_13FaithfulEpsilonOne]
  nlinarith [sq_pos_of_pos hepsilon]

/-- The graph-density refinement also leaves a strict exponent gap. -/
lemma wz1Lemma8_13_graph_exponent_gap
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    wz1Lemma8_13FaithfulEta epsilon <
      wz1Lemma8_13FaithfulNormalizedEta epsilon := by
  dsimp only [wz1Lemma8_13FaithfulEta,
    wz1Lemma8_13FaithfulNormalizedEta]
  nlinarith [sq_pos_of_pos hepsilon]

/-- The pre-normalization separated-source scale is controlled by the
Kaufman angular scale with the exact `2 * epsilon₁` loss. -/
lemma wz1Lemma8_13_selectionScale_le_angular
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hdelta : 0 < delta)
    (haspect :
      wz1Lemma8_13FaithfulAspect input ≤
        3 * Real.rpow delta
          (-wz1Lemma8_13FaithfulEpsilonOne epsilon)) :
    wz1Lemma8_13FaithfulSelectionScale input ≤
      384 * Real.rpow delta
          (-2 * wz1Lemma8_13FaithfulEpsilonOne epsilon) *
        wz1Lemma8_13FaithfulAngularScale input := by
  have hactive :
      0 < wz1Lemma8_13FaithfulActiveWidth input := by
    exact hdelta.trans_le
      (wz1Lemma49_delta_le_activeCommonWidth
        input.density.1 input.base input.direction)
  have hpowerPos :
      0 <
        Real.rpow delta
          (-wz1Lemma8_13FaithfulEpsilonOne epsilon) :=
    Real.rpow_pos_of_pos hdelta _
  have hnormalization :
      0 < wz1Lemma8_13FaithfulNormalizationWidth input := by
    dsimp only [wz1Lemma8_13FaithfulNormalizationWidth]
    exact mul_pos hpowerPos hactive
  have hpower :
      Real.rpow delta
            (-wz1Lemma8_13FaithfulEpsilonOne epsilon) *
          Real.rpow delta
            (-wz1Lemma8_13FaithfulEpsilonOne epsilon) =
        Real.rpow delta
          (-2 * wz1Lemma8_13FaithfulEpsilonOne epsilon) := by
    calc
      Real.rpow delta
            (-wz1Lemma8_13FaithfulEpsilonOne epsilon) *
          Real.rpow delta
            (-wz1Lemma8_13FaithfulEpsilonOne epsilon) =
        Real.rpow delta
          (-wz1Lemma8_13FaithfulEpsilonOne epsilon +
            -wz1Lemma8_13FaithfulEpsilonOne epsilon) :=
          (Real.rpow_add hdelta _ _).symm
      _ =
        Real.rpow delta
          (-2 * wz1Lemma8_13FaithfulEpsilonOne epsilon) := by
            congr 1
            ring
  have hidentity :
      wz1Lemma8_13FaithfulSelectionScale input =
        128 * wz1Lemma8_13FaithfulAspect input *
          Real.rpow delta
            (-wz1Lemma8_13FaithfulEpsilonOne epsilon) *
          wz1Lemma8_13FaithfulAngularScale input := by
    dsimp only [wz1Lemma8_13FaithfulSelectionScale,
      wz1Lemma8_13FaithfulAngularScale,
      wz1Lemma8_13FaithfulNormalizationWidth,
      wz1Lemma8_13FaithfulActiveWidth]
    field_simp [hactive.ne', hpowerPos.ne']
  rw [hidentity]
  have hangularNonnegative :
      0 ≤ wz1Lemma8_13FaithfulAngularScale input :=
    (div_pos input.width_pos hnormalization).le
  have hfirstFactor :
      128 * wz1Lemma8_13FaithfulAspect input *
          Real.rpow delta
            (-wz1Lemma8_13FaithfulEpsilonOne epsilon) ≤
        128 *
          (3 * Real.rpow delta
            (-wz1Lemma8_13FaithfulEpsilonOne epsilon)) *
          Real.rpow delta
            (-wz1Lemma8_13FaithfulEpsilonOne epsilon) := by
    gcongr
  calc
    128 * wz1Lemma8_13FaithfulAspect input *
          Real.rpow delta
            (-wz1Lemma8_13FaithfulEpsilonOne epsilon) *
          wz1Lemma8_13FaithfulAngularScale input
        ≤
      128 *
          (3 * Real.rpow delta
            (-wz1Lemma8_13FaithfulEpsilonOne epsilon)) *
          Real.rpow delta
            (-wz1Lemma8_13FaithfulEpsilonOne epsilon) *
          wz1Lemma8_13FaithfulAngularScale input := by
            exact
              mul_le_mul_of_nonneg_right
                hfirstFactor hangularNonnegative
    _ =
      384 * Real.rpow delta
          (-2 * wz1Lemma8_13FaithfulEpsilonOne epsilon) *
        wz1Lemma8_13FaithfulAngularScale input := by
          rw [← hpower]
          ring

/-- The actual post-affine fine scale retains its full aspect-ratio loss.
This is the scale bridge needed before applying the Lemma 48 logarithmic
bound; in particular, the logarithm may not be evaluated at `delta`
directly. -/
lemma wz1Lemma8_13_fineScale_inv_le
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hdelta : 0 < delta)
    (haspect :
      wz1Lemma8_13FaithfulAspect input ≤
        3 * Real.rpow delta
          (-wz1Lemma8_13FaithfulEpsilonOne epsilon)) :
    (wz1Lemma8_13FaithfulFineScale input)⁻¹ ≤
      6 * Real.rpow delta
        (-(1 + wz1Lemma8_13FaithfulEpsilonOne epsilon)) := by
  let aspect := wz1Lemma8_13FaithfulAspect input
  let epsilonOne := wz1Lemma8_13FaithfulEpsilonOne epsilon
  have haspectOne : 1 ≤ aspect := by
    dsimp only [aspect, wz1Lemma8_13FaithfulAspect]
    exact le_max_left _ _
  have haspectPos : 0 < aspect :=
    zero_lt_one.trans_le haspectOne
  have hfineInv :
      (wz1Lemma8_13FaithfulFineScale input)⁻¹ =
        2 * aspect * delta⁻¹ := by
    dsimp only [wz1Lemma8_13FaithfulFineScale]
    field_simp [hdelta.ne', haspectPos.ne']
    ring
  have hpower :
      Real.rpow delta (-epsilonOne) * delta⁻¹ =
        Real.rpow delta (-(1 + epsilonOne)) := by
    have hinv : delta⁻¹ = Real.rpow delta (-1 : ℝ) :=
      (Real.rpow_neg_one delta).symm
    rw [hinv]
    calc
      Real.rpow delta (-epsilonOne) *
            Real.rpow delta (-1 : ℝ) =
          Real.rpow delta
            ((-epsilonOne) + (-1 : ℝ)) :=
        (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta (-(1 + epsilonOne)) := by
        congr 1
        ring
  rw [hfineInv]
  calc
    2 * aspect * delta⁻¹ ≤
        2 * (3 * Real.rpow delta (-epsilonOne)) *
          delta⁻¹ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (by simpa [aspect, epsilonOne] using haspect)
          (by norm_num))
        (inv_nonneg.mpr hdelta.le)
    _ = 6 * Real.rpow delta (-(1 + epsilonOne)) := by
      rw [← hpower]
      ring

/-- A Lemma 48 loss at the actual post-affine fine scale is at most six
copies of the original-scale logarithm.  The fixed factor `6` absorbs both
the aspect-ratio exponent and the absolute affine factor. -/
lemma wz1Lemma8_13_fineScale_logarithmic_bound
    {delta epsilon fineScale : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon < 1)
    (hfine : 0 < fineScale)
    (hfineInv :
      fineScale⁻¹ ≤
        6 * Real.rpow delta
          (-(1 + wz1Lemma8_13FaithfulEpsilonOne epsilon))) :
    1 + Real.log fineScale⁻¹ ≤
      6 * (1 + Real.log delta⁻¹) := by
  let epsilonOne := wz1Lemma8_13FaithfulEpsilonOne epsilon
  have hepsilonOneNonnegative : 0 ≤ epsilonOne := by
    dsimp only [epsilonOne,
      wz1Lemma8_13FaithfulEpsilonOne]
    positivity
  have hepsilonOneLe : epsilonOne ≤ 1 := by
    dsimp only [epsilonOne,
      wz1Lemma8_13FaithfulEpsilonOne]
    nlinarith [sq_pos_of_pos hepsilon]
  have hdeltaInvOne : 1 ≤ delta⁻¹ :=
    (one_le_inv₀ hdelta).2 hdeltaOne
  have hlogDeltaNonnegative :
      0 ≤ Real.log delta⁻¹ :=
    Real.log_nonneg hdeltaInvOne
  have hfineInvPos : 0 < fineScale⁻¹ :=
    inv_pos.mpr hfine
  have hmajorantPos :
      0 <
        6 * Real.rpow delta
          (-(1 + epsilonOne)) :=
    mul_pos (by norm_num)
      (Real.rpow_pos_of_pos hdelta _)
  have hlogMonotone :
      Real.log fineScale⁻¹ ≤
        Real.log
          (6 * Real.rpow delta
            (-(1 + epsilonOne))) := by
    exact
      Real.strictMonoOn_log.monotoneOn
        hfineInvPos hmajorantPos
        (by simpa [epsilonOne] using hfineInv)
  have hlogMajorant :
      Real.log
          (6 * Real.rpow delta
            (-(1 + epsilonOne))) =
        Real.log 6 +
          (1 + epsilonOne) * Real.log delta⁻¹ := by
    calc
      Real.log
            (6 * Real.rpow delta
              (-(1 + epsilonOne))) =
          Real.log 6 +
            Real.log
              (Real.rpow delta
                (-(1 + epsilonOne))) :=
        Real.log_mul (by norm_num)
          (Real.rpow_pos_of_pos hdelta _).ne'
      _ =
          Real.log 6 +
            (-(1 + epsilonOne)) * Real.log delta := by
        exact
          congrArg (fun value : ℝ => Real.log 6 + value)
            (Real.log_rpow hdelta
              (-(1 + epsilonOne)))
      _ =
          Real.log 6 +
            (1 + epsilonOne) * Real.log delta⁻¹ := by
        rw [Real.log_inv]
        ring
  have hlogSix : Real.log 6 ≤ 5 := by
    convert
      Real.log_le_sub_one_of_pos
        (by norm_num : (0 : ℝ) < 6) using 1 <;>
      norm_num
  rw [hlogMajorant] at hlogMonotone
  calc
    1 + Real.log fineScale⁻¹ ≤
        1 +
          (Real.log 6 +
            (1 + epsilonOne) * Real.log delta⁻¹) := by
      linarith
    _ ≤ 6 * (1 + Real.log delta⁻¹) := by
      nlinarith

/--
All second-stage fixed and logarithmic losses can be absorbed simultaneously.
-/
theorem wz1Lemma8_13_faithful_kaufman_budget :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
      ∃ delta₀ : ℝ,
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          (256 * Real.rpow delta
              (wz1Lemma8_13FaithfulNormalizedEta epsilon) ≤
            Real.rpow delta
              (wz1Lemma8_13FaithfulEta epsilon)) ∧
          (∀ fineScale logarithmicLoss fineConstant : ℝ,
            0 < fineScale →
            fineScale⁻¹ ≤
              6 * Real.rpow delta
                (-(1 +
                  wz1Lemma8_13FaithfulEpsilonOne epsilon)) →
            0 ≤ logarithmicLoss →
            logarithmicLoss ≤
              20 * (1 + Real.log fineScale⁻¹) →
            0 ≤ fineConstant →
            fineConstant ≤
              96 * Real.rpow delta
                (-wz1Lemma8_13FaithfulFineExponent epsilon) →
            16200 * logarithmicLoss * fineConstant ≤
              Real.rpow delta
                (-wz1Lemma8_13FaithfulNormalizedEta epsilon)) ∧
          (2 +
              (4 / Real.sqrt 3 + 1) /
                wz1Lemma8_13FaithfulDirectionKappa delta epsilon ≤
            Real.rpow delta
              (-wz1Lemma8_13FaithfulNormalizedEta epsilon)) := by
  intro epsilon hepsilon hepsilonOne
  let eta := wz1Lemma8_13FaithfulEta epsilon
  let normalizedEta :=
    wz1Lemma8_13FaithfulNormalizedEta epsilon
  let fineExponent :=
    wz1Lemma8_13FaithfulFineExponent epsilon
  let directionExponent :=
    wz1Lemma8_13FaithfulDirectionExponent epsilon
  let fineGap := normalizedEta - fineExponent
  let directionGap := normalizedEta - directionExponent
  have heta : 0 < eta := by
    dsimp only [eta, wz1Lemma8_13FaithfulEta]
    positivity
  have hnormalizedEta : 0 < normalizedEta := by
    dsimp only [normalizedEta,
      wz1Lemma8_13FaithfulNormalizedEta]
    positivity
  have hfineGap : 0 < fineGap := by
    dsimp only [fineGap, normalizedEta, fineExponent]
    exact wz1Lemma8_13_fine_exponent_gap hepsilon
  have hdirectionGap : 0 < directionGap := by
    dsimp only [directionGap, normalizedEta,
      directionExponent]
    exact wz1Lemma8_13_direction_exponent_gap hepsilon
  have hgraphGap : eta < normalizedEta := by
    dsimp only [eta, normalizedEta]
    exact wz1Lemma8_13_graph_exponent_gap hepsilon
  rcases
      exists_delta_mul_rpow_le_rpow
        256 (by norm_num)
        (alpha := normalizedEta) (beta := eta)
        hgraphGap with
    ⟨graphScale, hgraphScale, hgraphScaleOne,
      hgraph⟩
  let logarithmicConstant : ℝ :=
    16200 * 120 * 96
  have hlogarithmicConstant :
      0 < logarithmicConstant := by
    dsimp only [logarithmicConstant]
    norm_num
  rcases
      log_poly_decay_general
        logarithmicConstant fineGap
        hlogarithmicConstant hfineGap with
    ⟨logScale, hlogScale, hlogScaleOne, hlog⟩
  let circleConstant : ℝ :=
    2 + (4 / Real.sqrt 3 + 1) * 1572864
  have hcircleConstant : 0 < circleConstant := by
    dsimp only [circleConstant]
    have hsqrt : 0 < Real.sqrt 3 :=
      Real.sqrt_pos.mpr (by norm_num)
    positivity
  rcases
      exists_delta_mul_rpow_le_rpow
        circleConstant hcircleConstant.le
        (alpha := -directionExponent)
        (beta := -normalizedEta)
        (by linarith) with
    ⟨circleScale, hcircleScale, hcircleScaleOne,
      hcircle⟩
  let delta₀ :=
    min graphScale (min logScale circleScale)
  have hdelta₀ : 0 < delta₀ := by
    simp [delta₀, hgraphScale, hlogScale, hcircleScale]
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans hgraphScaleOne
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaSmall
  have hdeltaOne : delta ≤ 1 :=
    hdeltaSmall.trans hdelta₀One
  have hdeltaGraph : delta ≤ graphScale :=
    hdeltaSmall.trans (min_le_left _ _)
  have hdeltaLog : delta ≤ logScale :=
    hdeltaSmall.trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaCircle : delta ≤ circleScale :=
    hdeltaSmall.trans
      ((min_le_right _ _).trans (min_le_right _ _))
  have hgraphAt :=
    hgraph delta hdelta hdeltaGraph
  have hlogAt :=
    hlog delta hdelta hdeltaLog
  have hcircleAt :=
    hcircle delta hdelta hdeltaCircle
  refine ⟨hgraphAt, ?_, ?_⟩
  · intro fineScale logarithmicLoss fineConstant
      hfineScale hfineScaleInv
      hlogarithmicLoss hlogarithmicLossBound
      hfineConstant hfineConstantBound
    have hlogNonnegative :
        0 ≤ Real.log delta⁻¹ := by
      apply Real.log_nonneg
      exact (one_le_inv₀ hdelta).2 hdeltaOne
    have hfineLogBound :
        1 + Real.log fineScale⁻¹ ≤
          6 * (1 + Real.log delta⁻¹) :=
      wz1Lemma8_13_fineScale_logarithmic_bound
        hdelta hdeltaOne hepsilon hepsilonOne
        hfineScale hfineScaleInv
    have hlogarithmicLossDelta :
        logarithmicLoss ≤
          120 * (1 + Real.log delta⁻¹) := by
      calc
        logarithmicLoss ≤
            20 * (1 + Real.log fineScale⁻¹) :=
          hlogarithmicLossBound
        _ ≤
            20 * (6 * (1 + Real.log delta⁻¹)) := by
          exact mul_le_mul_of_nonneg_left
            hfineLogBound (by norm_num)
        _ = 120 * (1 + Real.log delta⁻¹) := by
          ring
    have hlogBound :
        logarithmicConstant *
            (Real.log delta⁻¹ + 1) ≤
          1 / Real.rpow delta fineGap := by
      simpa [logarithmicConstant, add_comm] using hlogAt
    have hconstantBound :
        16200 * logarithmicLoss * fineConstant ≤
          logarithmicConstant *
            (Real.log delta⁻¹ + 1) *
              Real.rpow delta (-fineExponent) := by
      calc
        16200 * logarithmicLoss * fineConstant
            ≤
          16200 *
              (120 * (1 + Real.log delta⁻¹)) *
                (96 * Real.rpow delta (-fineExponent)) := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left
                hlogarithmicLossDelta (by norm_num))
              hfineConstantBound
              hfineConstant
              (mul_nonneg (by norm_num)
                (by
                  have : 0 ≤ 1 + Real.log delta⁻¹ := by
                    linarith
                  positivity))
        _ =
          logarithmicConstant *
            (Real.log delta⁻¹ + 1) *
              Real.rpow delta (-fineExponent) := by
            dsimp only [logarithmicConstant]
            ring
    calc
      16200 * logarithmicLoss * fineConstant
          ≤
        logarithmicConstant *
          (Real.log delta⁻¹ + 1) *
            Real.rpow delta (-fineExponent) :=
        hconstantBound
      _ ≤
        (1 / Real.rpow delta fineGap) *
          Real.rpow delta (-fineExponent) := by
            exact mul_le_mul_of_nonneg_right hlogBound
              (Real.rpow_nonneg hdelta.le _)
      _ =
        Real.rpow delta (-normalizedEta) := by
          have hfineGapPower :
              1 / Real.rpow delta fineGap =
                Real.rpow delta (-fineGap) := by
            rw [one_div]
            exact (Real.rpow_neg hdelta.le fineGap).symm
          rw [hfineGapPower]
          calc
            Real.rpow delta (-fineGap) *
                  Real.rpow delta (-fineExponent) =
                Real.rpow delta
                  ((-fineGap) + (-fineExponent)) :=
              (Real.rpow_add hdelta _ _).symm
            _ = Real.rpow delta (-normalizedEta) := by
              congr 1
              dsimp only [fineGap]
              ring
  · have hdirectionPower :
        1 ≤ Real.rpow delta (-directionExponent) := by
      exact
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos
          hdelta hdeltaOne (by
            dsimp only [directionExponent,
              wz1Lemma8_13FaithfulDirectionExponent,
              wz1Lemma8_13FaithfulEta,
              wz1Lemma8_13FaithfulEpsilonOne]
            nlinarith [sq_pos_of_pos hepsilon])
    have hkappa :
        wz1Lemma8_13FaithfulDirectionKappa delta epsilon =
          Real.rpow delta directionExponent / 1572864 := by
      dsimp only [wz1Lemma8_13FaithfulDirectionKappa,
        directionExponent,
        wz1Lemma8_13FaithfulDirectionExponent]
    have hkappaPos :
        0 <
          wz1Lemma8_13FaithfulDirectionKappa
            delta epsilon :=
      wz1Lemma8_13_directionKappa_pos hdelta
    have hcircleRewrite :
        (4 / Real.sqrt 3 + 1) /
              wz1Lemma8_13FaithfulDirectionKappa delta epsilon =
          (4 / Real.sqrt 3 + 1) * 1572864 *
            Real.rpow delta (-directionExponent) := by
      rw [hkappa]
      have hpowerPos :
          0 < Real.rpow delta directionExponent :=
        Real.rpow_pos_of_pos hdelta _
      have hnegativePower :
          Real.rpow delta (-directionExponent) =
            (Real.rpow delta directionExponent)⁻¹ :=
        Real.rpow_neg hdelta.le directionExponent
      rw [hnegativePower]
      field_simp
        [hpowerPos.ne', hkappaPos.ne',
          (by norm_num : (1572864 : ℝ) ≠ 0)]
    rw [hcircleRewrite]
    calc
      2 +
          (4 / Real.sqrt 3 + 1) * 1572864 *
            Real.rpow delta (-directionExponent)
          ≤
        circleConstant *
          Real.rpow delta (-directionExponent) := by
            dsimp only [circleConstant]
            nlinarith
      _ ≤ Real.rpow delta (-normalizedEta) :=
        hcircleAt

end

end Kakeya.Assouad
